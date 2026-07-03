module SPARQL11.Store

open RDF.Graph.Executable
open SPARQL11.Algebra
open Parser.BallyhooHDT
open Parser.BallyhooCOTTAS
open RDF.CottasStore

module Lh = RDF.List.Helpers

// Note: this module previously imported Util.Log for in-line debug
// tracing in choose_best_tp_backend. Removed because F* erases
// Tot-unit-discarded calls regardless of how they're wrapped. The
// OCaml-side dry-runner in factoidal_explain.ml is the right place
// for explain-mode logging — it calls F*'s choose_best_tp_backend
// directly and logs each decision via Util_Log_runtime. The F*
// planner is the runtime path; the logging is glue.

// Backend-neutral store layer for SPARQL evaluation.
// The algebra remains the semantic source of truth; this module only dispatches
// physical triple-pattern access to specific backends.

noeq type graph_backend =
  | GB_List : rdf_graph -> graph_backend
  | GB_Indexed : indexed_graph -> graph_backend
  | GB_HDT : hdt_graph_store -> graph_backend
  | GB_COTTAS : cottas_dataset_store -> option iri -> graph_backend
  | GB_CottasOnDisk : cottas_ondisk_store -> option iri -> graph_backend
  | GB_Union : list graph_backend -> graph_backend

noeq type named_graph_backend = {
  ngb_name : iri;
  ngb_graph : graph_backend;
}

noeq type dataset_backend = {
  dsb_default : graph_backend;
  dsb_named : list named_graph_backend;
}

(* list_graph_backend / list_dataset_backend wrappers were removed
   2026-05-16. All callers use the indexed_* variants below — same
   triples, faster lookup paths. *)

(* Wrap an rdf_graph as an indexed backend (issue #100 Phase 0). The
   index is built once at construction; subsequent backend_search calls
   on the same wrapper reuse the buckets. *)
let indexed_graph_backend (g : rdf_graph) : graph_backend =
  GB_Indexed (build_indexed g)

let indexed_dataset_backend (ds : rdf_dataset) : dataset_backend =
  {
    dsb_default = indexed_graph_backend ds.ds_default;
    dsb_named =
      List.Tot.map
        (fun (ng : named_graph) ->
          { ngb_name = ng.ng_name; ngb_graph = indexed_graph_backend ng.ng_graph })
        ds.ds_named
  }

(* Build a dataset_backend whose default + named graphs all dispatch to
   the same on-disk COTTAS store, with named-graph dispatch using the
   stored graph IRI as the bound. The default graph is the COTTAS rows
   whose graph column is unbound (DEFAULT) — modelled as `GB_CottasOnDisk
   _ None`. Each named graph is a separate `GB_CottasOnDisk` filtering
   on its IRI (issue #100 Phase 2). *)
let cottas_ondisk_dataset_backend (cods : cottas_ondisk_store) : dataset_backend =
  {
    dsb_default = GB_CottasOnDisk cods None;
    dsb_named =
      List.Tot.map
        (fun (g : (iri & cottas_graph_ref)) ->
          let (gname, _) = g in
          { ngb_name = gname; ngb_graph = GB_CottasOnDisk cods (Some gname) })
        (cottas_ondisk_named_graphs cods)
  }

// Tail-rec accumulator. The original used `backend_search member b @
// union_backend_search rest b` — both the recursion AND the `@` walk the
// LHS list (each search result, up to 3M triples) on every step. On a
// multi-graph dataset that overflows the macOS main-thread stack BEFORE
// Tav5's HTTP-level row cap (commit 4ff2321) can fire. Sin7 fix
// (2026-04-26): walk members tail-recursively, accumulating each
// member's results in reverse via `List.Tot.rev_acc`, then reverse once
// at the end. Order is preserved (semantics unchanged).
let rec union_backend_search_acc (members : list graph_backend)
  (b : triple_pattern_bound) (acc_rev : list triple)
  : Tot (list triple) (decreases members) =
  match members with
  | [] -> List.Tot.rev acc_rev
  | member :: rest ->
    let part = backend_search member b in
    union_backend_search_acc rest b (List.Tot.rev_acc part acc_rev)

and backend_search (gb : graph_backend) (b : triple_pattern_bound) : list triple =
  match gb with
  | GB_List g ->
    store_search (graph_to_store g) b
  | GB_Indexed ig ->
    ig_search ig b
  | GB_HDT hgs ->
    hdt_search_triples hgs b.bs b.bp b.bo
  | GB_COTTAS cds graph_name ->
    let rows = cottas_search cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name) in
    List.Tot.map fst (cottas_rows_to_quads cds rows)
  | GB_CottasOnDisk cods graph_name ->
    (* On-disk search: encode bounds → integer term-ids, walk per-row term-id
       arrays (no parsed terms), decode terms only for matched rows.
       If any bound term is absent from the dictionary the result is
       definitively empty without scanning.
       Sin7 (2026-04-26): use the fused tail-rec
       `cottas_ondisk_rows_to_triples` to avoid the non-tail-rec
       `List.Tot.map fst` walk on 3M-row results. *)
    (match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo graph_name with
     | None -> []
     | Some bound ->
       let rows = cottas_ondisk_search cods bound in
       cottas_ondisk_rows_to_triples cods rows)
  | GB_Union members ->
    union_backend_search_acc members b []

let union_backend_search (members : list graph_backend) (b : triple_pattern_bound)
  : Tot (list triple) =
  union_backend_search_acc members b []

// Aleph6 (issue #100, demo prep): LIMIT-pushdown variant of backend_search.
// The COTTAS-on-disk backend stops walking once `limit` matched rows are
// accumulated; non-disk backends fall back to a simple List.Tot.takeWhile-style
// truncation since their search is already in-memory and cheap.
let rec list_take_n (#a:Type) (n : nat) (xs : list a)
  : Tot (list a) (decreases n) =
  if n = 0 then []
  else
    match xs with
    | [] -> []
    | hd :: tl -> hd :: list_take_n (n - 1) tl

// Tail-rec accumulator for LIMIT-pushdown union search. Same hazard as
// `union_backend_search` (sin7 2026-04-26): the original used `part @
// more`, walking the LHS on every step. Even with LIMIT pushdown, a
// single member's pre-truncate result list could still be large; the
// per-member result is fed unchanged to `List.Tot.rev_acc`. Order
// preserved (rev at end, then take_n).
let rec union_backend_search_limited_acc (members : list graph_backend)
  (b : triple_pattern_bound) (limit : nat) (acc_rev : list triple)
  (acc_len : nat)
  : Tot (list triple) (decreases members) =
  if acc_len >= limit then acc_rev
  else
    match members with
    | [] -> acc_rev
    | member :: rest ->
      let need : nat = limit - acc_len in
      let part = backend_search_limited member b need in
      let part_len = List.Tot.length part in
      union_backend_search_limited_acc rest b limit
        (List.Tot.rev_acc part acc_rev) (acc_len + part_len)

and backend_search_limited (gb : graph_backend) (b : triple_pattern_bound)
  (limit : nat)
  : Tot (list triple) =
  match gb with
  | GB_CottasOnDisk cods graph_name ->
    (* COTTAS-on-disk: real LIMIT pushdown — walker stops at `limit` rows.
       Sin7 (2026-04-26): tail-rec rows->triples to avoid stack overflow
       even at LIMIT=50000 if pushdown returns more than expected. *)
    (match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo graph_name with
     | None -> []
     | Some bound ->
       let rows = cottas_ondisk_search_limited cods bound limit in
       cottas_ondisk_rows_to_triples cods rows)
  | GB_Union members ->
    if limit = 0 then []
    else
      let result_rev = union_backend_search_limited_acc members b limit [] 0 in
      list_take_n limit (List.Tot.rev result_rev)
  | _ ->
    (* Other backends: no pushdown, just truncate. Their search results
       are already in memory; LIMIT is a small post-step. *)
    list_take_n limit (backend_search gb b)

let rec union_backend_estimate (members : list graph_backend) (b : triple_pattern_bound)
  : Tot nat (decreases members) =
  match members with
  | [] -> 0
  | member :: rest ->
    backend_estimate member b + union_backend_estimate rest b

and backend_estimate (gb : graph_backend) (b : triple_pattern_bound) : nat =
  match gb with
  | GB_List g ->
    store_estimate (graph_to_store g) b
  | GB_Indexed ig ->
    ig_estimate ig b
  | GB_HDT hgs ->
    hdt_estimate hgs (hdt_build_bound_tp hgs b.bs b.bp b.bo)
  | GB_COTTAS cds graph_name ->
    cottas_estimate cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name)
  | GB_CottasOnDisk cods graph_name ->
    (match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo graph_name with
     | None -> 0
     | Some bound -> cottas_ondisk_estimate cods bound)
  | GB_Union members ->
    union_backend_estimate members b

// EXACT counting for result-producing callers (the Bet5 streaming
// GROUP BY ?g path and the Aleph6 COUNT-star path below).
// backend_estimate is the join-order-optimiser contract and may
// approximate (GB_CottasOnDisk's bounds-present branch does, by
// design); consuming it as a query RESULT returned wrong per-graph
// counts (E1 experiment, 2026-07-03). Every non-on-disk backend's
// estimate is already exact, so only GB_CottasOnDisk (and unions
// containing it) dispatch differently here.
let rec union_backend_count_exact (members : list graph_backend) (b : triple_pattern_bound)
  : Tot nat (decreases members) =
  match members with
  | [] -> 0
  | member :: rest ->
    backend_count_exact member b + union_backend_count_exact rest b

and backend_count_exact (gb : graph_backend) (b : triple_pattern_bound) : Tot nat (decreases gb) =
  match gb with
  | GB_CottasOnDisk cods graph_name ->
    (match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo graph_name with
     | None -> 0
     | Some bound -> cottas_ondisk_count_exact cods bound)
  | GB_Union members -> union_backend_count_exact members b
  | _ -> backend_estimate gb b

let rec union_backend_predicate_present (members : list graph_backend) (pred : wf_iri)
  : Tot bool (decreases members) =
  match members with
  | [] -> false
  | member :: rest ->
    if backend_predicate_present member pred then true
    else union_backend_predicate_present rest pred

and backend_predicate_present (gb : graph_backend) (pred : wf_iri)
  : Tot bool (decreases gb) =
  match gb with
  | GB_List g ->
    backend_estimate (GB_List g) {
      bs = None;
      bp = Some pred;
      bo = None;
    } > 0
  | GB_Indexed ig ->
    backend_estimate (GB_Indexed ig) {
      bs = None;
      bp = Some pred;
      bo = None;
    } > 0
  | GB_HDT hgs ->
    hdt_predicate_present hgs pred
  | GB_COTTAS cds graph_name ->
    backend_estimate (GB_COTTAS cds graph_name) {
      bs = None;
      bp = Some pred;
      bo = None;
    } > 0
  | GB_CottasOnDisk cods _ ->
    cottas_ondisk_predicate_present cods pred
  | GB_Union members ->
    union_backend_predicate_present members pred

let rec lookup_named_backend (name : iri) (named : list named_graph_backend)
  : Tot (option graph_backend) (decreases named) =
  match named with
  | [] -> None
  | ng :: rest ->
    if ng.ngb_name = name then Some ng.ngb_graph else lookup_named_backend name rest

let eval_single_tp_backend (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping)
  : solution_sequence =
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  } in
  let candidates = backend_search gb bound in
  list_filter_map (fun t -> tp_match tp t mu) candidates

// Compact bound-shape descriptor. Encodes which positions have a
let estimate_tp_backend_mu (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping) : nat =
  backend_estimate gb {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  }

// F* planner. Stays pure (Tot). Logging is the OCaml-side dry-runner's
// job (factoidal_explain.ml calls choose_best_tp_backend recursively
// and logs each decision via Util_Log_runtime). Earlier attempt to
// embed Util.Log calls IN this F* function was reverted: F* erases
// `Tot unit` returning calls in unused-result position, regardless of
// whether they're assume-val or `let`-bodied. The clean split:
// PLANNING in F*, LOGGING in OCaml glue.
let rec choose_best_tp_backend (patterns : bgp) (gb : graph_backend) (mu : solution_mapping)
  : Tot (option (triple_pattern * bgp)) (decreases patterns) =
  match patterns with
  | [] -> None
  | tp :: rest ->
    match choose_best_tp_backend rest gb mu with
    | None -> Some (tp, [])
    | Some (best, remaining) ->
      if estimate_tp_backend_mu tp gb mu <= estimate_tp_backend_mu best gb mu
      then Some (tp, rest)
      else Some (best, tp :: remaining)

let rec pattern_predicate_hint (p : group_graph_pattern)
  : Tot (option wf_iri) (decreases p) =
  match p with
  | GP_BGP [] -> None
  | GP_BGP (tp :: _) ->
    (match tp.tp_p with
     | PT_IRI pred -> Some pred
     | _ -> None)
  | GP_Filter _ p' -> pattern_predicate_hint p'
  | GP_Bind _ _ p' -> pattern_predicate_hint p'
  | GP_Graph _ p' -> pattern_predicate_hint p'
  | GP_Join p1 _ -> pattern_predicate_hint p1
  | GP_LeftJoin p1 _ _ -> pattern_predicate_hint p1
  | GP_Union p1 _ -> pattern_predicate_hint p1
  | GP_Minus p1 _ -> pattern_predicate_hint p1
  | GP_Empty -> None
  | GP_Values _ _ -> None
  | GP_Service _ _ _ -> None
  | GP_ServiceVar _ _ _ -> None
  | GP_SubSelect _ -> None
  | GP_PropertyPath _ _ _ -> None

let named_candidate_backends (named : list named_graph_backend) (predicate_hint : option wf_iri)
  : list named_graph_backend =
  match predicate_hint with
  | None -> named
  | Some pred ->
    List.Tot.filter (fun ngb -> backend_predicate_present ngb.ngb_graph pred) named

// Tail-rec concatMap helper. F* stdlib `List.Tot.concatMap` is non-tail-rec
// (recurses, then `append`s), so on a 3M-element solution list (e.g. first
// BGP pattern matching the entire COTTAS dataset) the outer recursion alone
// blows the macOS main-thread stack. Sin7 fix (2026-04-26): walk `next`
// tail-recursively, using `List.Tot.rev_acc` to splice each per-mu result
// list into a reversed accumulator. Order preserved (rev once at the end).
let rec eval_bgp_concatmap_acc
  (rest : bgp) (gb : graph_backend) (next : solution_sequence)
  (fuel : nat) (acc_rev : solution_sequence)
  : Tot solution_sequence (decreases %[fuel; 1; next]) =
  match next with
  | [] -> acc_rev
  | mu' :: more ->
    let part = eval_bgp_backend_from_mu_fuel rest gb mu' fuel in
    eval_bgp_concatmap_acc rest gb more fuel (List.Tot.rev_acc part acc_rev)

and eval_bgp_backend_from_mu_fuel
  (patterns : bgp) (gb : graph_backend) (mu : solution_mapping) (fuel : nat)
  : Tot solution_sequence (decreases %[fuel; 0; ([] <: solution_sequence)]) =
  if fuel = 0 then [mu]
  else
    match patterns with
    | [] -> [mu]
    | _ ->
      match choose_best_tp_backend patterns gb mu with
      | None -> [mu]
      | Some (tp, rest) ->
        let next = eval_single_tp_backend tp gb mu in
        List.Tot.rev (eval_bgp_concatmap_acc rest gb next (fuel - 1) [])

let eval_bgp_backend (patterns : bgp) (gb : graph_backend) : solution_sequence =
  eval_bgp_backend_from_mu_fuel patterns gb sm_empty (List.Tot.length patterns + 1)

// ----------------------------------------------------------------------
// Aleph6 (issue #100, demo prep): query-shape detectors and fast paths.
//
// These pattern-match the SPARQL AST for two demo-critical query shapes:
//
//   1. Streaming COUNT(*): SELECT (COUNT(*) AS ?n) WHERE { tp } with no
//      GROUP BY, no DISTINCT, no FILTER above the BGP. Calls
//      `backend_estimate` directly instead of materialising 3M+ rows
//      and counting them.
//
//   2. LIMIT pushdown: SELECT ?vars WHERE { tp } LIMIT k with no
//      DISTINCT/ORDER BY/aggregates/etc. Uses
//      `backend_search_limited` so the COTTAS-on-disk walker stops at
//      `k` rows.
//
// Both fast paths are SEMANTICS-PRESERVING: when the detector matches,
// the returned solution sequence equals what the materialise path
// would produce. Detectors are conservative — anything they don't
// recognise falls through to the existing materialise path.
// ----------------------------------------------------------------------

// Helper: extract the single triple pattern of a 1-tp BGP, modulo no
// FILTER/BIND/JOIN wrappers that change semantics. Returns None if the
// pattern isn't a single-tp BGP.
let extract_single_tp_bgp (p : group_graph_pattern) : option triple_pattern =
  match p with
  | GP_BGP [tp] -> Some tp
  | _ -> None

// Helper: detect the COUNT(*) shape of a SELECT clause.
// Matches SI_Expr (E_Aggregate Agg_Count false (E_Var "*" | E_BoolLit true)) v.
// COUNT(DISTINCT *) is NOT matched (distinct=false required) — it needs
// row materialisation for the dedup pass.
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

// Detect the streaming-COUNT(*) shape of a whole query and return the
// alias variable name plus the triple pattern. Conservative — bails
// out on any modifier that would change the count (DISTINCT, ORDER BY,
// HAVING, GROUP BY, VALUES, etc.).
let detect_streaming_count_star (q : query) : option (var_name & triple_pattern) =
  match q.q_form with
  | QF_Select sel ->
    (match detect_count_star_select sel with
     | None -> None
     | Some v ->
       if Some? q.q_group_by then None
       else if Some? q.q_having then None
       else if Some? q.q_values then None
       else if q.q_modifier.sm_distinct then None
       else if q.q_modifier.sm_reduced then None
       else if Some? q.q_modifier.sm_order_by then None
       else
         (match extract_single_tp_bgp q.q_pattern with
          | None -> None
          | Some tp -> Some (v, tp)))
  | _ -> None

// Build the one-row solution sequence for COUNT(*) = n.
let count_star_solution (alias : var_name) (n : nat) : solution_sequence =
  let lit_term : rdf_term = T_Literal {
    lexical_form = string_of_int n;
    datatype = xsd_integer;
    lang_tag = None;
  } in
  [ sm_bind alias lit_term sm_empty ]

// Detect:  SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } }
//          GROUP BY ?g  [ORDER BY ?...  LIMIT/OFFSET]
// Returns (graph_var, count_alias) when the shape matches.
//
// Allowed modifiers: ORDER BY (sorted post-aggregate via sort_solutions),
//   LIMIT/OFFSET (sliced via slice_solutions).
// Rejected modifiers: HAVING, VALUES, DISTINCT, REDUCED — any of these
//   requires row materialisation and the streaming count is unsound.
//
// The inner BGP must be a single triple pattern with all three terms
// being VARIABLES, all DISTINCT from each other, and all DISTINCT from
// the graph variable ?g. Without that distinctness check, queries like
//   GRAPH ?g { ?g ?p ?o }   -- ?g now also bound from subject column
//   GRAPH ?g { ?s ?p ?s }   -- ?s appears twice; equality constraint
// would still match, but the streaming estimate counts the whole graph
// without honouring those equality constraints, returning a wrong
// (over-)count. (Reviewer 2026-05-01.)
let detect_streaming_count_group_by_graph (q : query)
  : option (var_name & var_name) =
  match q.q_form with
  | QF_Select (Select_Vars items) ->
    if Some? q.q_having then None
    else if Some? q.q_values then None
    else if q.q_modifier.sm_distinct then None
    else if q.q_modifier.sm_reduced then None
    else
      // SELECT must be exactly: SI_Var ?g, SI_Expr (COUNT(*) AS ?n)
      (match items with
       | [SI_Var gv; SI_Expr count_e nv] ->
         (match count_e with
          | E_Aggregate Agg_Count false sub_e ->
            let count_ok = match sub_e with
              | E_Var "*" -> true
              | E_BoolLit true -> true
              | _ -> false in
            if not count_ok then None
            else
              // GROUP BY exactly [GC_Var gv]
              (match q.q_group_by with
               | Some [GC_Var gbv] ->
                 if gbv <> gv then None
                 else
                   // WHERE: GP_Graph (PT_Var gv) (GP_BGP [tp]) where tp is
                   // (PS_Var s, PT_Var p, PT_Var o), all PAIRWISE DISTINCT
                   // and all distinct from gv.
                   (match q.q_pattern with
                    | GP_Graph (PT_Var graph_v) inner ->
                      if graph_v <> gv then None
                      else
                        (match extract_single_tp_bgp inner with
                         | None -> None
                         | Some tp ->
                           (match tp.tp_s, tp.tp_p, tp.tp_o with
                            | PS_Var sv, PT_Var pv, PT_Var ov ->
                              // Pairwise-distinct check: rejects shapes like
                              // ?g/?p/?o or ?s/?p/?s that would carry an
                              // implicit equality constraint the estimate
                              // does not honour.
                              if sv = gv || pv = gv || ov = gv then None
                              else if sv = pv || sv = ov || pv = ov then None
                              else Some (gv, nv)
                            | _ -> None))
                    | _ -> None)
               | _ -> None)
          | _ -> None)
       | _ -> None)
  | _ -> None

// Build the per-graph solutions for the GROUP BY ?g COUNT(*) fast path.
// One row per named graph: ?g = graph IRI, ?count_alias = backend_estimate.
//
// Tail-recursive accumulator form (reviewer 2026-05-01): the prior
// straight-recursive shape blew JS's ~10K stack on lifesci-class
// datasets if a future caller passed in many named graphs. Same
// pattern as the bucket_replace tail-rec fix in #119.
let rec count_group_by_graph_solutions_acc
  (graph_var : var_name)
  (count_alias : var_name)
  (acc : solution_sequence)
  (named : list named_graph_backend)
  : Tot solution_sequence (decreases named) =
  match named with
  | [] -> List.Tot.rev acc
  | ngb :: rest ->
    let bound : triple_pattern_bound = { bs = None; bp = None; bo = None } in
    // Exact, not estimate: this count IS the query result (E1 bug).
    let cnt = backend_count_exact ngb.ngb_graph bound in
    let lit_term : rdf_term = T_Literal {
      lexical_form = string_of_int cnt;
      datatype = xsd_integer;
      lang_tag = None;
    } in
    let mu0 = sm_bind count_alias lit_term sm_empty in
    let mu = if is_iri ngb.ngb_name
             then sm_bind graph_var (T_IRI ngb.ngb_name) mu0
             else mu0 in
    count_group_by_graph_solutions_acc graph_var count_alias (mu :: acc) rest

let count_group_by_graph_solutions
  (graph_var : var_name)
  (count_alias : var_name)
  (named : list named_graph_backend)
  : solution_sequence =
  count_group_by_graph_solutions_acc graph_var count_alias [] named

// Detect the LIMIT-pushdown shape: SELECT ?vars WHERE { single tp }
// [LIMIT k]  with no DISTINCT / ORDER BY / OFFSET / GROUP BY / HAVING /
// VALUES / aggregates. Returns (triple_pattern, limit) when matched.
let detect_limit_single_tp (q : query) : option (triple_pattern & nat) =
  match q.q_form with
  | QF_Select sel ->
    if select_has_aggregates sel then None
    else if Some? q.q_group_by then None
    else if Some? q.q_having then None
    else if Some? q.q_values then None
    else if q.q_modifier.sm_distinct then None
    else if q.q_modifier.sm_reduced then None
    else if Some? q.q_modifier.sm_order_by then None
    else if Some? q.q_modifier.sm_offset then None
    else
      (match q.q_modifier.sm_limit with
       | None -> None
       | Some k ->
         (match extract_single_tp_bgp q.q_pattern with
          | None -> None
          | Some tp -> Some (tp, k)))
  | _ -> None

// Run the LIMIT-pushdown path. Builds a triple_pattern_bound (no mu),
// calls backend_search_limited, projects to the SELECT clause's vars.
let eval_limit_single_tp (sel : select_clause) (tp : triple_pattern)
  (gb : graph_backend) (limit : nat) : solution_sequence =
  let bound = {
    bs = bound_subject_of_pattern tp.tp_s sm_empty;
    bp = bound_predicate_of_pattern tp.tp_p sm_empty;
    bo = bound_object_of_pattern tp.tp_o sm_empty;
  } in
  let candidates = backend_search_limited gb bound limit in
  let omega = list_filter_map (fun t -> tp_match tp t sm_empty) candidates in
  let omega' = list_take_n limit omega in
  match sel with
  | Select_Vars items -> project_solutions (select_item_vars items) omega'
  | Select_All -> omega'

let rec eval_pattern_backend (base : option wf_iri) (p : group_graph_pattern) (gb : graph_backend) (dsb : dataset_backend)
  : Tot solution_sequence (decreases p) =
  match p with
  | GP_BGP bgp ->
    eval_bgp_backend bgp gb

  | GP_Join p1 p2 ->
    join (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb)

  | GP_LeftJoin p1 p2 filter_e ->
    left_join base (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb) filter_e

  | GP_Filter e p' ->
    filter_solutions_fwd base e (eval_pattern_backend base p' gb dsb)

  | GP_Union p1 p2 ->
    union (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb)

  | GP_Minus p1 p2 ->
    minus (eval_pattern_backend base p1 gb dsb) (eval_pattern_backend base p2 gb dsb)

  | GP_Empty ->
    [sm_empty]

  | GP_Bind e v p' ->
    let omega = eval_pattern_backend base p' gb dsb in
    List.Tot.map
      (fun mu ->
        match er_to_term (eval_expr_fwd base e mu) with
        | Some t ->
          (match sm_lookup v mu with
           | Some _ -> mu
           | None -> sm_bind v t mu)
        | None -> mu)
      omega

  | GP_Values vars rows ->
    eval_values vars rows

  | GP_Graph gt p' ->
    (match gt with
     | PT_IRI name ->
       (match lookup_named_backend name dsb.dsb_named with
        | Some ngb -> eval_pattern_backend base p' ngb dsb
        | None -> [])
     | PT_Var v ->
       let candidates = named_candidate_backends dsb.dsb_named (pattern_predicate_hint p') in
       Lh.concatMap_tr
         (fun (ngb : named_graph_backend) ->
           let ng_results = eval_pattern_backend base p' ngb.ngb_graph dsb in
           if is_iri ngb.ngb_name then
             List.Tot.map (fun mu -> sm_bind v (T_IRI ngb.ngb_name) mu) ng_results
           else ng_results)
         candidates
     | _ ->
       eval_pattern_backend base p' gb dsb)

  | GP_Service _ _ _ ->
    []

  | GP_ServiceVar _ _ _ ->
    (* Variable-endpoint federated query — backend evaluator does not currently
       implement service dispatch. Issue #57 Phase 3 (Tet): full per-solution
       handling lives in the in-memory eval_pattern_store path. *)
    []

  | GP_SubSelect q ->
    (match eval_select_query_backend_on_graph q gb dsb with
     | Some omega -> omega
     | None -> [])

  | GP_PropertyPath _ _ _ ->
    []

and eval_select_query_backend_bgp (q : query) (gb : graph_backend)
  : option solution_sequence =
  let base = q.q_base in
  match q.q_form, q.q_pattern with
  | QF_Select sel, GP_BGP bgp ->
    let omega0 = eval_bgp_backend bgp gb in
    let omega = match q.q_values with
      | None -> omega0
      | Some vals -> join omega0 vals in
    let needs_grouping = match q.q_group_by with
      | Some _ -> true
      | None -> select_has_aggregates sel in
    if needs_grouping then None
    else
      let omega' = match sel with
        | Select_Vars items -> eval_select_items base items omega []
        | Select_All -> omega in
      let ordered = match q.q_modifier.sm_order_by with
        | None -> omega'
        | Some o -> sort_solutions base o omega' in
      let projected = match sel with
        | Select_Vars items -> project_solutions (select_item_vars items) ordered
        | Select_All -> ordered in
      let deduped =
        if q.q_modifier.sm_distinct then distinct_solutions projected
        else if q.q_modifier.sm_reduced then reduced_solutions projected
        else projected in
      Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
  | _ -> None

and eval_select_query_backend_on_graph (q : query) (gb : graph_backend) (dsb : dataset_backend)
  : option solution_sequence =
  // Aleph6: streaming COUNT-star fast-path. Calls backend_estimate
  // directly (one walk, no per-row materialisation). Semantics-
  // preserving: equivalent to materialising and counting.
  match detect_streaming_count_star q with
  | Some (alias, tp) ->
    let bound = {
      bs = bound_subject_of_pattern tp.tp_s sm_empty;
      bp = bound_predicate_of_pattern tp.tp_p sm_empty;
      bo = bound_object_of_pattern tp.tp_o sm_empty;
    } in
    // Exact, not estimate: this count IS the query result (E1 bug).
    let n = backend_count_exact gb bound in
    let omega = count_star_solution alias n in
    Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit omega)
  | None ->
    // Aleph6: LIMIT-pushdown fast-path. SELECT vars WHERE single-tp LIMIT k.
    let limit_match : option (triple_pattern & nat) =
      match q.q_form with
      | QF_Select _ -> detect_limit_single_tp q
      | _ -> None in
    (match limit_match with
     | Some (tp, k) ->
       (match q.q_form with
        | QF_Select sel -> Some (eval_limit_single_tp sel tp gb k)
        | _ -> None)
     | None ->
    // Materialise path: original implementation, inlined here so that
    // F*'s totality checker can see the q.q_pattern structural decrease
    // for the recursive eval_pattern_backend call.
    match q.q_form with
    | QF_Select sel ->
      let base = q.q_base in
      let omega0 = eval_pattern_backend base q.q_pattern gb dsb in
      let omega = match q.q_values with
        | None -> omega0
        | Some vals -> join omega0 vals in
      let needs_grouping = match q.q_group_by with
        | Some _ -> true
        | None -> select_has_aggregates sel in
      if needs_grouping then
        let groups = match q.q_group_by with
          | Some conds -> group_by base conds omega
          | None -> implicit_group omega in
        let filtered_groups = match q.q_having with
          | Some conditions -> having_filter base conditions groups
          | None -> groups in
        let omega' = match sel with
          | Select_Vars items -> aggregate_groups base items filtered_groups
          | Select_All ->
            List.Tot.map (fun (grp : group) ->
              match grp.g_solutions with
              | mu :: _ -> mu
              | [] -> sm_empty) filtered_groups in
        let ordered = match q.q_modifier.sm_order_by with
          | None -> omega'
          | Some o -> sort_solutions base o omega' in
        let deduped =
          if q.q_modifier.sm_distinct then distinct_solutions ordered
          else if q.q_modifier.sm_reduced then reduced_solutions ordered
          else ordered in
        Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
      else
        let omega' = match sel with
          | Select_Vars items -> eval_select_items base items omega []
          | Select_All -> omega in
        let ordered = match q.q_modifier.sm_order_by with
          | None -> omega'
          | Some o -> sort_solutions base o omega' in
        let projected = match sel with
          | Select_Vars items -> project_solutions (select_item_vars items) ordered
          | Select_All -> ordered in
        let deduped =
          if q.q_modifier.sm_distinct then distinct_solutions projected
          else if q.q_modifier.sm_reduced then reduced_solutions projected
          else projected in
        Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
    | _ -> None)

and eval_select_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option solution_sequence =
  // Bet5: streaming COUNT(*) GROUP BY ?g over named graphs. One
  // backend_estimate call per named graph, no per-row materialisation.
  // Semantics-preserving for the matched shape: each named graph
  // contributes exactly one ?g=iri / ?n=count row.
  match detect_streaming_count_group_by_graph q with
  | Some (graph_var, count_alias) ->
    let omega = count_group_by_graph_solutions graph_var count_alias dsb.dsb_named in
    // Apply ORDER BY post-aggregation if present. The result set is
    // bounded by the number of named graphs (small, typically < 100),
    // so sorting cost is negligible compared to the saved BGP eval.
    let ordered = match q.q_modifier.sm_order_by with
      | None   -> omega
      | Some o -> sort_solutions q.q_base o omega in
    Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit ordered)
  | None ->
    eval_select_query_backend_on_graph q dsb.dsb_default dsb

and eval_ask_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option bool =
  match q.q_form with
  | QF_Ask ->
    let omega0 = eval_pattern_backend q.q_base q.q_pattern dsb.dsb_default dsb in
    let omega = match q.q_values with
      | None -> omega0
      | Some vals -> join omega0 vals in
    Some (match omega with | [] -> false | _ -> true)
  | _ -> None

// Priority 2c (Jena basic-probe regression): the algebra path rewrites
// blank-node pattern terms to variables at its entry
// (eval_select_query, SPARQL11.Algebra); the backend path never did,
// so bnode-pattern SELECT/ASK matched zero rows via the CLI's default
// route. The rewrite cannot live inside the mutually recursive group
// above — replacing q_pattern breaks its termination metric — so these
// top-level entries do it once and delegate. Consumers call these.
let run_select_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option solution_sequence =
  eval_select_query_backend_dataset
    ({ q with q_pattern = rewrite_query_bnodes_pattern q.q_pattern }) dsb

let run_ask_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option bool =
  eval_ask_query_backend_dataset
    ({ q with q_pattern = rewrite_query_bnodes_pattern q.q_pattern }) dsb
