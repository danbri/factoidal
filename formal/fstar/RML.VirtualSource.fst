module RML.VirtualSource

// Part B of docs/designissues/2026-07-06-virtual-sources-design.md
// ("virtual-sources-design" stage 5 of its own §5 staged-rollout
// table): a `store_caps` realisation (RDF.Store.Capabilities.fst)
// over an already-decoded RML mapping (RML.Mapping.fst) plus its
// source payloads (already-read, already-parsed JSON trees / raw CSV
// text — see `rml_source_data` below), answering bound SPARQL triple
// patterns WITHOUT ever calling RML.Eval.eval_triples_map's
// materializing path per query. Reuses RML.Mapping/RML.Sources/
// RML.Eval's existing functions VERBATIM wherever the design doc's
// §4 reuse table calls for it; the only net-new logic here is (a) the
// structural TriplesMap-narrowing predicates (§3.2's first sentence)
// and (b) the two small filtered-iterator wrappers (§3.2's last
// paragraph) that push a bound value into the row list BEFORE the
// per-row RML.Eval machinery runs.
//
// Pushdown model (design doc §3.2, implemented exactly):
//   1. Structural narrowing: `triples_map_could_match` rules out a
//      TriplesMap whose SUBJECT map is a `TMF_Constant` that doesn't
//      equal a bound `bs`, or whose every predicate (POM predicates +
//      the rdf:type-via-rml:class shortcut) is a `TMF_Constant` that
//      doesn't equal a bound `bp`. A `TMF_Reference`/`TMF_Template`
//      subject or predicate map ALWAYS stays a candidate (per the
//      doc: "evaluating it is the only way to know").
//   2. Row-level pushdown: within a surviving candidate, when `bs` is
//      bound and the subject map is NOT a plain constant (so
//      map-level narrowing couldn't resolve it), `json_iterate_filtered`/
//      `csv_iterate_filtered` evaluate ONLY the subject term map per
//      row (`eval_term_map MR_Subject`, reused verbatim — the
//      cheapest targeted evaluation available, since the subject map
//      is one term, not the whole predicate-object-map cross
//      product) and drop rows whose subject doesn't match `bs` BEFORE
//      `RML.Eval.eval_triples_map`'s full per-row machinery
//      (predicate-object maps, class triples, datatype/language
//      Cartesian products) ever runs on them.
//   3. `bo` (bound object) is NOT pushed down in v1 — every surviving
//      candidate map's rows all reach full evaluation regardless of
//      `bo`; the exact-match safety net (`triple_matches_bound`,
//      reused verbatim, SPARQL11.Algebra.fst) still filters the FINAL
//      triple list correctly. Documented deviation/fallback, disclosed
//      in the task report — the doc's own §3.2 illustrates narrowing
//      via predicate/subject shape only, and no rml-core stage-5
//      acceptance case needs bo pushdown.
//   4. Joins do NOT push down (doc §3.2, verbatim): `RML.Eval.
//      eval_triples_map` (the non-join evaluator) is the ONLY
//      function this module calls per candidate map, so `OB_Join`
//      object bindings contribute zero triples here, exactly as they
//      already do in every other eval_triples_map caller. A query
//      that needs RefObjectMap-equivalent data joins two triple
//      patterns over this SAME store_caps at the SPARQL level
//      (ordinary BGP join), never inside one sc_solve call.
//
// v1 scope, disclosed (design doc §3.1/§3.4 boundary): DEFAULT GRAPH
// ONLY. `solve_one_map` runs the evaluated placed-triples through
// `RML.Eval.place_into_dataset` (reused verbatim) and keeps only
// `ds_default` — any rml:graph/graphMap-routed triple is dropped
// rather than silently misrouted. `sc_flags.scf_supports_named_graphs
// = false` advertises this honestly. Extending to named-graph routing
// is a `dataset_caps`-shaped follow-up (RDF.Store.Capabilities.fst's
// own `dataset_caps` record already exists for exactly this shape),
// not attempted here per the commit-sized floor-preserving mandate.
//
// DAG position (design doc §4): sits above RML.Mapping/RML.Sources/
// RML.Eval, and — like RDF.Store.Capabilities.fst itself — opens
// SPARQL11.Algebra for `triple_pattern_bound`/`triple_matches_bound`
// and RDF.Store.Capabilities for the `store_caps` record it builds.
// No cycle: RDF.Store.Capabilities.fst does not import anything RML-
// or SPARQL11.Store-shaped, so this module can sit below SPARQL11.Store
// (which gets the new GB_VirtualRML arm) without inverting any edge.
//
// IRON RULES:
//   - F* is the source of truth (rule #1); all pushdown/narrowing
//     decision logic lives here, not in the OCaml CLI glue.
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open RML.Mapping
open RML.Sources
open RML.Eval
open Parser.JSON
open SPARQL11.Algebra
open RDF.Store.Capabilities

// ------------------------------------------------------------------
// 1. Source payloads. One entry per triples map (keyed by its own
//    `tm_id`), holding whatever the OCaml-side loader already read +
//    parsed ONE TIME at store-construction (design doc §3.1: "the
//    resulting closures ... are Tot over the already-read,
//    already-parsed in-memory value ... walked fresh on every
//    sc_solve call"). Mirrors the exact byte source `RML.Eval.fst`'s
//    own banner already documents for `eval_triples_map_json`/`_csv`
//    ("json_root is supplied by the (OCaml-side, rule #11) caller
//    that read + parsed the logical source's file") — this is the
//    SAME seam, just captured once per triples map instead of passed
//    fresh at every call site.
// ------------------------------------------------------------------

noeq type rml_source_data =
  | RSD_Json : json_val -> rml_source_data
  | RSD_Csv  : string -> rml_source_data
  | RSD_None : rml_source_data   // unresolvable: unread file, XPath/Stage-4-only
                                 // formulation, or no logical source at all

type rml_sources = list (node_ref & rml_source_data)

noeq type rml_virtual_source = {
  rvs_doc      : mapping_document;
  rvs_sources  : rml_sources;
  rvs_base_iri : option string;   // RML-Core's "execution environment" default base IRI
}

// ------------------------------------------------------------------
// 2. Filtered iterators (design doc §3.2's last paragraph): thin
//    wraps over RML.Sources' existing json_iterate/csv_iterate,
//    additive, not a fork — no new parsing, no new term-map logic.
// ------------------------------------------------------------------

let json_iterate_filtered (root : json_val) (iterator : string) (pred : source_row -> bool)
  : list source_row =
  List.Tot.filter pred (json_iterate root iterator)

let csv_iterate_filtered (csv_text : string) (null_values : list string) (pred : source_row -> bool)
  : list source_row =
  List.Tot.filter pred (csv_iterate csv_text null_values)

// ------------------------------------------------------------------
// 3. Structural narrowing (design doc §3.2, first sentence): does
//    this TriplesMap's SUBJECT/PREDICATE term-map SHAPE rule it out
//    for a bound (bs, bp), without evaluating a single row?
// ------------------------------------------------------------------

// A bound predicate `p` rules out a `TMF_Constant` predicate map that
// isn't `T_IRI p`; a reference/template/unknown predicate map always
// stays a candidate (evaluating it is the only way to know).
let single_pm_could_match (p : wf_iri) (pm : term_map) : bool =
  match pm.tmap_form with
  | TMF_Constant (T_IRI i) -> i = p
  | TMF_Constant _ -> false
  | _ -> true

let pom_predicate_could_match (p : wf_iri) (pom : predicate_object_map) : bool =
  List.Tot.existsb (single_pm_could_match p) pom.pom_predicates

// rml:class is a constant-predicate (rdf:type) shortcut at the
// subject-map level (RML.Mapping.decode_subject_map's sm_classes) —
// a nonempty class list only ever contributes rdf:type triples.
let classes_could_match_predicate (p : wf_iri) (classes : list wf_iri) : bool =
  match classes with
  | [] -> false
  | _ -> p = rdf_type

let bp_could_match (b_bp : option wf_iri) (sm_classes : list wf_iri) (poms : list predicate_object_map)
  : bool =
  match b_bp with
  | None -> true
  | Some p ->
    classes_could_match_predicate p sm_classes ||
    List.Tot.existsb (pom_predicate_could_match p) poms

// A bound subject `s` rules out a `TMF_Constant` subject map whose
// resolved term isn't (as a subject) equal to `s`; reference/template
// subject maps always stay structural candidates (row-level pushdown,
// §4 below, is where those get narrowed).
let sm_term_could_match_subject (b_bs : option subject) (sm_term : term_map) : bool =
  match b_bs with
  | None -> true
  | Some s ->
    (match sm_term.tmap_form with
     | TMF_Constant t ->
       (match subject_of_rdf_term t with
        | Some s' -> subject_eq s s'
        | None -> false)
     | _ -> true)

let triples_map_could_match (b : triple_pattern_bound) (tmap : triples_map) : bool =
  match tmap.tm_subject_map with
  | None -> false   // no subjectMap: never produces a triple (RML.Eval's own None branch)
  | Some sm ->
    sm_term_could_match_subject b.bs sm.sm_term &&
    bp_could_match b.bp sm.sm_classes tmap.tm_predicate_object_maps

// ------------------------------------------------------------------
// 4. Row-level subject pushdown (design doc §3.2, "a JSONPath sub-step
//    evaluated per row and compared before running the row through
//    RML.Eval's full term-map machinery"): the cheapest available
//    per-row probe is the subject term map ALONE, via RML.Eval's own
//    `eval_term_map` — reused verbatim, not forked — rather than the
//    whole triples map's predicate-object-map cross product. The
//    `row_seed` argument only matters for the corner case of a
//    `TMF_Unknown` subject map with `rml:termType rml:BlankNode` and
//    no expression at all (RML.Eval.eval_term_map's
//    fresh-per-row-blank-node fallback); using a constant placeholder
//    here can only make this PROBE over-inclusive (a row survives to
//    full evaluation that a real per-row seed would have excluded),
//    never under-inclusive, because `RML.Eval.eval_triples_map` still
//    computes the REAL per-row seed independently afterwards and
//    `triple_matches_bound` (§5) still applies the exact-match filter
//    to the final triple list — correctness holds either way; only
//    the pushdown's row-count savings narrows slightly less than a
//    real per-row seed would in that one corner case (not exercised
//    by any rml-core stage-5 fixture: none use a seedless BlankNode
//    subject map).
// ------------------------------------------------------------------

let row_matches_bound_subject
    (b_bs : option subject) (sm_term : term_map) (base_iri : option string) (row : source_row)
  : bool =
  match b_bs with
  | None -> true
  | Some s ->
    (match sm_term.tmap_form with
     | TMF_Constant _ -> true   // map-level narrowing (§3) already resolved this case
     | _ ->
       List.Tot.existsb
         (fun t -> match subject_of_rdf_term t with Some s' -> subject_eq s s' | None -> false)
         (eval_term_map MR_Subject sm_term row "#virtualsource_pushdown_probe" base_iri))

// Rows for ONE candidate triples map, with the subject-pushdown filter
// applied at the source-iteration level (json_iterate_filtered/
// csv_iterate_filtered — §2). Unresolvable logical sources (wrong
// reference formulation for the payload kind, or RSD_None) yield no
// rows, matching RML.Eval.eval_triples_map_json/_csv's own None arms.
let rows_for_map_pushed_down
    (b : triple_pattern_bound) (tmap : triples_map) (sm : subject_map_t) (data : rml_source_data)
    (default_base_iri : option string)
  : list source_row =
  let base_iri = (match tmap.tm_base_iri with Some x -> Some x | None -> default_base_iri) in
  let pred (row : source_row) : bool = row_matches_bound_subject b.bs sm.sm_term base_iri row in
  match tmap.tm_logical_source, data with
  | Some ls, RSD_Json root ->
    (match ls.ls_reference_formulation with
     | Some RF_JSONPath ->
       let iterator = (match ls.ls_iterator with Some it -> it | None -> "$") in
       json_iterate_filtered root iterator pred
     | _ -> [])
  | Some ls, RSD_Csv text ->
    (match ls.ls_reference_formulation with
     | Some RF_CSV -> csv_iterate_filtered text ls.ls_null_values pred
     | _ -> [])
  | _ -> []

// ------------------------------------------------------------------
// 5. Per-map solve (default graph only, §1's disclosed v1 scope) and
//    the whole-mapping sc_solve. `eval_triples_map` and
//    `place_into_dataset` are RML.Eval's existing functions, called
//    verbatim; `triple_matches_bound` is SPARQL11.Algebra's existing
//    exact-match filter, called verbatim as the final safety net (the
//    same role it plays in `ig_search`/`store_search`).
// ------------------------------------------------------------------

let solve_one_map
    (b : triple_pattern_bound) (tmap : triples_map) (sources : rml_sources)
    (default_base_iri : option string)
  : list triple =
  match tmap.tm_subject_map with
  | None -> []
  | Some sm ->
    (match List.Tot.assoc tmap.tm_id sources with
     | None -> []
     | Some data ->
       let rows = rows_for_map_pushed_down b tmap sm data default_base_iri in
       let placed = eval_triples_map tmap rows default_base_iri in
       (place_into_dataset empty_dataset placed).ds_default)

// An RDF graph is a SET of triples: a source with duplicate rows
// (e.g. RMLTC0012b-JSON's lives.json, where the Bob Smith row appears
// twice) generates the same triple more than once per evaluation, but
// the MATERIALIZED graph — and hence any query answered against it —
// carries it once. Dedupe with the same structural `triple_eq` check
// RDF.Graph's own `mem_triple` uses, order-preserving (first
// occurrence wins). O(n^2), acceptable at v1's "small/bounded source"
// scope (design doc §3.4) — without this, the stage-5 parity gate
// (virtual vs materialized byte-equal) fails on any fixture whose
// source contains duplicate rows.
let rec dedupe_triples_acc (ts : list triple) (acc_rev : list triple)
  : Tot (list triple) (decreases ts) =
  match ts with
  | [] -> List.Tot.rev acc_rev
  | t :: rest ->
    if List.Tot.existsb (fun u -> triple_eq u t) acc_rev
    then dedupe_triples_acc rest acc_rev
    else dedupe_triples_acc rest (t :: acc_rev)

let rml_solve
    (doc : mapping_document) (sources : rml_sources) (default_base_iri : option string)
    (b : triple_pattern_bound)
  : list triple =
  let candidates = List.Tot.filter (triples_map_could_match b) doc.md_triples_maps in
  let raw = List.Tot.concatMap (fun tm -> solve_one_map b tm sources default_base_iri) candidates in
  dedupe_triples_acc (triple_matches_bound b raw) []

// ------------------------------------------------------------------
// 6. Pushdown evidence (task acceptance requirement: "at least one
//    bound case demonstrably iterates fewer source rows than the
//    unbound scan"). Per candidate map (post structural narrowing),
//    the count of rows that survive row-level pushdown and would
//    enter RML.Eval's full per-row machinery — a deterministic,
//    computable number a test driver can print/compare directly
//    without runtime side-effect instrumentation, since every
//    function it calls is Tot.
// ------------------------------------------------------------------

let rows_considered_for_map
    (b : triple_pattern_bound) (tmap : triples_map) (sources : rml_sources)
    (default_base_iri : option string)
  : nat =
  match tmap.tm_subject_map with
  | None -> 0
  | Some sm ->
    (match List.Tot.assoc tmap.tm_id sources with
     | None -> 0
     | Some data -> List.Tot.length (rows_for_map_pushed_down b tmap sm data default_base_iri))

let rml_solve_trace
    (doc : mapping_document) (sources : rml_sources) (default_base_iri : option string)
    (b : triple_pattern_bound)
  : list (node_ref & nat) =
  List.Tot.map
    (fun (tm : triples_map) -> (tm.tm_id, rows_considered_for_map b tm sources default_base_iri))
    (List.Tot.filter (triples_map_could_match b) doc.md_triples_maps)

// ------------------------------------------------------------------
// 7. store_caps builder (design doc §3.1/§3.3). Local copy of
//    RDF.Store.Capabilities.caps_take_n (adjustment precedent that
//    module's own banner documents: this module sits at the same DAG
//    layer as RDF.Store.Capabilities, so it duplicates the tiny
//    truncation helper rather than importing "sideways").
//
//    sc_estimate/sc_count_exact (§3.3): v1's sc_solve walks an
//    already in-memory row list, so BOTH are genuinely exact full
//    scans — same shape as caps_of_indexed's
//    `sc_count_exact = sc_estimate` (RDF.Store.Capabilities.fst),
//    `scf_estimate_is_exact = true` is honest here, not a claim of
//    cheapness (§3.3: "exact but not cheap ... O(rows)").
// ------------------------------------------------------------------

let rec vs_take_n (#a:Type) (n : nat) (xs : list a) : Tot (list a) (decreases n) =
  if n = 0 then []
  else
    match xs with
    | [] -> []
    | hd :: tl -> hd :: vs_take_n (n - 1) tl

let caps_of_rml_source (rvs : rml_virtual_source) : Tot store_caps =
  {
    sc_flags = {
      scf_supports_named_graphs = false;   // v1 scope: default graph only (module banner §1)
      scf_supports_update = false;         // read-only virtual source, no write seam
      scf_streaming_shapes = true;
      scf_estimate_is_exact = true;        // §3.3: genuinely exact, not merely cheap
      scf_can_report_decode_fail = false;
    };
    sc_solve = (fun b -> rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b);
    sc_solve_limited =
      (fun b n -> vs_take_n n (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b));
    sc_estimate = (fun b -> List.Tot.length (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b));
    sc_count_exact = (fun b -> List.Tot.length (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri b));
    sc_predicate_present =
      (fun pred ->
        List.Tot.length
          (rml_solve rvs.rvs_doc rvs.rvs_sources rvs.rvs_base_iri ({ bs = None; bp = Some pred; bo = None }))
        > 0);
    sc_decode_failure = (fun () -> false);
  }
