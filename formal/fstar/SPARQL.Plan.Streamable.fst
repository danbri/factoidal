module SPARQL.Plan.Streamable

// Parse-stream fast-path shape recognizer for the CLI query pipeline.
//
// docs/designissues/2026-07-05-disk-backed-db-perf-review.md, roadmap
// item "bound in-memory query memory": `factoidal --data gene.ttl`
// (888,949 triples) answering a one-row COUNT(*) peaked at 731 MiB RSS
// — the same cost as materialising the whole graph for a point lookup
// — because the CLI parses every `--data` file into a full in-memory
// term graph (`load_dataset`) *before* it looks at the query at all.
// The streaming `factoidal count` subcommand answers the same corpus
// in 44 MiB by never building that graph. This module is the pure F*
// decision that lets the CLI take the `count`-style streaming path for
// a query too, when (and only when) the query provably doesn't need
// the materialised graph to answer correctly.
//
// This is a sibling of SPARQL11.Store's existing "Aleph6" fast paths
// (`detect_streaming_count_star` / `detect_streaming_count_group_by_
// graph`) — but those run AFTER a `graph_backend` already exists
// (indexed in memory, or an on-disk COTTAS store); they save the
// second materialisation (BGP-eval + per-row aggregation), not the
// first (parse-to-graph). This module's decision runs BEFORE any
// backend exists at all: when it matches, bin/factoidal-cli/
// factoidal_cli.ml drives the query straight off the parsers'
// generic per-item fold entry points (Parser.Turtle.fold_turtle_
// triples, Parser.NTriples.fold_ntriples, Parser.NQuads.fold_nquads)
// and never calls `load_dataset` / `build_indexed` at all.
//
// What this module owns:
//   - `stream_domain` / `stream_goal` / `stream_plan` — the typed
//     decision output.
//   - `streamable_shape` — pure AST -> option stream_plan. Recognizes
//     exactly the four shapes the CLI slice targets:
//       (a) SELECT (COUNT(*) AS ?v) WHERE { ?s ?p ?o }
//       (b) SELECT (COUNT(*) AS ?v) WHERE { GRAPH ?g { ?s ?p ?o } }
//           (?g not projected/grouped — one total row over all named
//           graphs; the NQuads-input sibling of (a))
//       (c) ASK { ?s ?p ?o }
//       (d) (a)/(c) with any subject/predicate/object position bound
//           to a constant instead of a variable
//   - `stream_state` / `stream_init` / `stream_step` / `stream_stop` /
//     `stream_in_domain` — the per-triple fold, generic over source
//     format.
//   - `stream_count_result` / `stream_ask_result` — read the final
//     answer out of a `stream_state`.
//
// What it deliberately does NOT own:
//   - The parsers' document-walk loop (Parser.Turtle/NTriples/NQuads
//     `fold_*` functions) — those are generic (accumulator type +
//     step function), unaware of SPARQL; this module supplies the
//     step function, not the walk.
//   - Building the final `solution_sequence` / output row — the CLI
//     reuses SPARQL11.Store.count_star_solution + SPARQL11.Algebra.
//     slice_solutions for that (same builder, same slicing the
//     materialise path already uses), so JSON/CSV/table output is
//     byte-identical to the materialise path by construction rather
//     than by a second hand-written formatter.
//   - Anything the four shapes above don't cover: GROUP BY, HAVING,
//     FILTER, multi-pattern BGP, DISTINCT/REDUCED, ORDER BY, VALUES,
//     COTTAS/on-disk backends, `--named` graphs, entailment closure.
//     All of those fall through unchanged to the existing
//     materialise-then-evaluate path — `streamable_shape` returning
//     `None` is the fallthrough signal.
//
// Correctness note on shape (b): a plain `?s ?p ?o` (no GRAPH) only
// ever queries the DEFAULT graph (RDF 1.1 dataset semantics); `GRAPH
// ?g { ?s ?p ?o }` only ever queries the UNION of NAMED graphs. In
// N-Quads a line without a graph label is a default-graph triple and
// a line WITH one is a named-graph quad (Parser.NQuads.fst's
// `parse_nquad` already returns `(triple & option iri)` for exactly
// this reason) — so the two shapes must count disjoint subsets of the
// document, never "every line". `stream_domain` + `stream_in_domain`
// is what keeps that distinction honest in the fold.
//
// Pairwise-distinctness requirement on shape (b): mirrors
// SPARQL11.Store.detect_streaming_count_group_by_graph's own
// requirement and for the same reason (2026-05-01 reviewer note
// there) — if the graph variable also names one of tp's positions
// (`GRAPH ?g { ?g ?p ?o }`), or two of tp's positions are the same
// variable (`GRAPH ?g { ?s ?p ?s }`), the pattern carries an implicit
// equality constraint that a bound-only match (subject/predicate/
// object checked independently) does not honour, and the streamed
// count would silently over-count. Rejecting those shapes (returning
// `None`, falling through to the materialise path) is required for
// soundness, not just style.

open RDF.Graph.Executable
open SPARQL11.Algebra

// ----------------------------------------------------------------------
// Decision output
// ----------------------------------------------------------------------

// Which part of the dataset a stream_plan ranges over. Triple-only
// input formats (Turtle, N-Triples) only ever have a default graph, so
// SD_DefaultGraph is the only domain that ever applies there.
type stream_domain =
  | SD_DefaultGraph
  | SD_AnyNamedGraph

// What the query wants back: a COUNT(*) alias binding, or a boolean.
noeq type stream_goal =
  | SG_Count : var_name -> stream_goal
  | SG_Ask   : stream_goal

noeq type stream_plan = {
  sp_domain : stream_domain;
  sp_bound  : triple_pattern_bound;
  sp_goal   : stream_goal;
  sp_offset : option nat;
  sp_limit  : option nat;
}

// ----------------------------------------------------------------------
// Shape detectors
// ----------------------------------------------------------------------

// Extract the single triple pattern of a 1-tp BGP. Mirrors
// SPARQL11.Store.extract_single_tp_bgp; duplicated (not imported) so
// this module stays below SPARQL11.Store in the dependency order —
// it is consulted by the CLI directly, before any backend/store
// exists, and must not depend on the backend layer.
let extract_single_tp_bgp (p : group_graph_pattern) : option triple_pattern =
  match p with
  | GP_BGP [tp] -> Some tp
  | _ -> None

// Detect the COUNT(*) shape of a SELECT clause: exactly one projected
// item, `(COUNT(*) AS ?v)` or `(COUNT(true) AS ?v)`, not DISTINCT.
// Mirrors SPARQL11.Store.detect_count_star_select.
let detect_count_star_select (sel : select_clause) : option var_name =
  match sel with
  | Select_Vars [SI_Expr e v] ->
    (match e with
     | E_Aggregate Agg_Count distinct sub_e ->
       if distinct then None
       else
         (match sub_e with
          | E_Var "*" -> Some v
          | E_BoolLit true -> Some v
          | _ -> None)
     | _ -> None)
  | _ -> None

let pattern_bound_of_tp (tp : triple_pattern) : triple_pattern_bound =
  {
    bs = bound_subject_of_pattern tp.tp_s sm_empty;
    bp = bound_predicate_of_pattern tp.tp_p sm_empty;
    bo = bound_object_of_pattern tp.tp_o sm_empty;
  }

// Modifiers that rule out ANY streaming fast path regardless of shape:
// GROUP BY / HAVING / VALUES need row materialisation to evaluate;
// DISTINCT / REDUCED need materialisation to dedup. ORDER BY is a
// semantic no-op on a single-row COUNT(*)/ASK answer, but is rejected
// too for consistency with SPARQL11.Store.detect_streaming_count_star
// (same conservative call there).
let common_modifiers_ok (q : query) : bool =
  None? q.q_group_by &&
  None? q.q_having &&
  None? q.q_values &&
  not q.q_modifier.sm_distinct &&
  not q.q_modifier.sm_reduced &&
  None? q.q_modifier.sm_order_by

// Shape (a) / (d): SELECT (COUNT(*) AS ?v) WHERE { tp } — tp any
// single triple pattern (all-variable for (a), one or more constant
// positions for (d)). Default graph only.
let detect_count_default (q : query) : option stream_plan =
  match q.q_form with
  | QF_Select sel ->
    (match detect_count_star_select sel with
     | None -> None
     | Some alias ->
       if not (common_modifiers_ok q) then None
       else
         (match extract_single_tp_bgp q.q_pattern with
          | None -> None
          | Some tp ->
            Some ({
              sp_domain = SD_DefaultGraph;
              sp_bound  = pattern_bound_of_tp tp;
              sp_goal   = SG_Count alias;
              sp_offset = q.q_modifier.sm_offset;
              sp_limit  = q.q_modifier.sm_limit;
            })))
  | _ -> None

// Shape (b): SELECT (COUNT(*) AS ?v) WHERE { GRAPH ?g { ?s ?p ?o } } —
// ?g not projected, not grouped: one total row across all named
// graphs. Requires s/p/o/g pairwise-distinct variables (see banner).
let detect_count_any_named_graph (q : query) : option stream_plan =
  match q.q_form with
  | QF_Select sel ->
    (match detect_count_star_select sel with
     | None -> None
     | Some alias ->
       if not (common_modifiers_ok q) then None
       else
         (match q.q_pattern with
          | GP_Graph (PT_Var gv) inner ->
            (match extract_single_tp_bgp inner with
             | None -> None
             | Some tp ->
               (match tp.tp_s, tp.tp_p, tp.tp_o with
                | PS_Var sv, PT_Var pv, PT_Var ov ->
                  if sv = gv || pv = gv || ov = gv then None
                  else if sv = pv || sv = ov || pv = ov then None
                  else
                    Some ({
                      sp_domain = SD_AnyNamedGraph;
                      sp_bound  = { bs = None; bp = None; bo = None };
                      sp_goal   = SG_Count alias;
                      sp_offset = q.q_modifier.sm_offset;
                      sp_limit  = q.q_modifier.sm_limit;
                    })
                | _ -> None))
          | _ -> None))
  | _ -> None

// Shape (c) / (d): ASK { tp } — default graph, any single triple
// pattern (bound positions allowed: "does at least one X exist" is
// just as streamable as "is the graph nonempty").
let detect_ask_default (q : query) : option stream_plan =
  match q.q_form with
  | QF_Ask ->
    if Some? q.q_values then None
    else
      (match extract_single_tp_bgp q.q_pattern with
       | None -> None
       | Some tp ->
         Some ({
           sp_domain = SD_DefaultGraph;
           sp_bound  = pattern_bound_of_tp tp;
           sp_goal   = SG_Ask;
           sp_offset = None;
           sp_limit  = None;
         }))
  | _ -> None

// Top-level decision: try each detector in turn. At most one can ever
// match (they dispatch on disjoint (q_form, q_pattern) shapes), order
// is not semantically significant.
let streamable_shape (q : query) : option stream_plan =
  match detect_count_default q with
  | Some p -> Some p
  | None ->
    match detect_count_any_named_graph q with
    | Some p -> Some p
    | None -> detect_ask_default q

// ----------------------------------------------------------------------
// The per-triple fold — generic over source format. Callers wire this
// through Parser.Turtle/NTriples/NQuads' generic `fold_*` entry
// points, each of which takes a `triple -> 'a -> 'a` step function and
// an `'a -> bool` stop predicate and is otherwise unaware of SPARQL.
// ----------------------------------------------------------------------

noeq type stream_state = {
  ss_count : nat;
  ss_found : bool;
}

let stream_init : stream_state = { ss_count = 0; ss_found = false }

let triple_matches_stream_bound (b : triple_pattern_bound) (t : triple) : bool =
  (match b.bs with | None -> true | Some s -> subject_eq s t.s) &&
  (match b.bp with | None -> true | Some p -> p = t.p) &&
  (match b.bo with | None -> true | Some o -> rdf_term_eq o t.o)

// Whether a parsed item (triple plus its optional N-Quads graph label)
// falls within the plan's domain. Triple-only sources (Turtle, N-
// Triples) always pass `g = None` and only ever run SD_DefaultGraph
// plans, so this is always `true` for them. N-Quads sources pass the
// real graph label per quad; see the module banner for why this
// distinction is required for correctness on N-Quads input.
let stream_in_domain (plan : stream_plan) (g : option iri) : bool =
  match plan.sp_domain, g with
  | SD_DefaultGraph, None -> true
  | SD_AnyNamedGraph, Some _ -> true
  | _, _ -> false

// The per-triple fold. Only ever called (by the CLI wiring) on items
// already known to be in-domain via `stream_in_domain`.
let stream_step (plan : stream_plan) (t : triple) (st : stream_state) : stream_state =
  if triple_matches_stream_bound plan.sp_bound t then
    match plan.sp_goal with
    | SG_Count _ -> { st with ss_count = st.ss_count + 1 }
    | SG_Ask -> { st with ss_found = true }
  else st

// Early-stop predicate: once an ASK plan has found a match, further
// input can't change the answer. COUNT plans never stop early (every
// remaining triple could still match).
let stream_stop (plan : stream_plan) (st : stream_state) : bool =
  match plan.sp_goal with
  | SG_Ask -> st.ss_found
  | SG_Count _ -> false

let stream_count_result (st : stream_state) : nat = st.ss_count
let stream_ask_result (st : stream_state) : bool = st.ss_found
