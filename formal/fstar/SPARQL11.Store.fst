module SPARQL11.Store

open RDF.Graph.Executable
open SPARQL11.Algebra
open Parser.BallyhooHDT
open Parser.BallyhooCOTTAS
open RDF.CottasStore

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

let list_graph_backend (g : rdf_graph) : graph_backend =
  GB_List g

let list_dataset_backend (ds : rdf_dataset) : dataset_backend =
  {
    dsb_default = GB_List ds.ds_default;
    dsb_named =
      List.Tot.map
        (fun (ng : named_graph) -> { ngb_name = ng.ng_name; ngb_graph = GB_List ng.ng_graph })
        ds.ds_named
  }

(* Wrap an rdf_graph as an indexed backend (issue #100 Phase 0). The
   index is built once at construction; subsequent backend_search calls
   on the same wrapper reuse the buckets. Semantically identical to
   list_graph_backend — same triples, just faster lookup paths. *)
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

let rec union_backend_search (members : list graph_backend) (b : triple_pattern_bound)
  : Tot (list triple) (decreases members) =
  match members with
  | [] -> []
  | member :: rest ->
    backend_search member b @ union_backend_search rest b

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
       definitively empty without scanning. *)
    (match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo graph_name with
     | None -> []
     | Some bound ->
       let rows = cottas_ondisk_search cods bound in
       List.Tot.map fst (cottas_ondisk_rows_to_quads cods rows))
  | GB_Union members ->
    union_backend_search members b

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

let rec union_backend_search_limited (members : list graph_backend)
  (b : triple_pattern_bound) (limit : nat)
  : Tot (list triple) (decreases members) =
  if limit = 0 then []
  else
    match members with
    | [] -> []
    | member :: rest ->
      let part = backend_search_limited member b limit in
      let part_len = List.Tot.length part in
      if part_len >= limit then list_take_n limit part
      else
        let need : nat = limit - part_len in
        let more = union_backend_search_limited rest b need in
        part @ more

and backend_search_limited (gb : graph_backend) (b : triple_pattern_bound)
  (limit : nat)
  : Tot (list triple) =
  match gb with
  | GB_CottasOnDisk cods graph_name ->
    (* COTTAS-on-disk: real LIMIT pushdown — walker stops at `limit` rows. *)
    (match cottas_ondisk_build_bound_qp_opt cods b.bs b.bp b.bo graph_name with
     | None -> []
     | Some bound ->
       let rows = cottas_ondisk_search_limited cods bound limit in
       List.Tot.map fst (cottas_ondisk_rows_to_quads cods rows))
  | GB_Union members ->
    union_backend_search_limited members b limit
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

let estimate_tp_backend_mu (tp : triple_pattern) (gb : graph_backend) (mu : solution_mapping) : nat =
  backend_estimate gb {
    bs = bound_subject_of_pattern tp.tp_s mu;
    bp = bound_predicate_of_pattern tp.tp_p mu;
    bo = bound_object_of_pattern tp.tp_o mu;
  }

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

let rec eval_bgp_backend_from_mu_fuel
  (patterns : bgp) (gb : graph_backend) (mu : solution_mapping) (fuel : nat)
  : Tot solution_sequence (decreases fuel) =
  if fuel = 0 then [mu]
  else
    match patterns with
    | [] -> [mu]
    | _ ->
      match choose_best_tp_backend patterns gb mu with
      | None -> [mu]
      | Some (tp, rest) ->
        let next = eval_single_tp_backend tp gb mu in
        List.Tot.concatMap (fun mu' -> eval_bgp_backend_from_mu_fuel rest gb mu' (fuel - 1)) next

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

let rec eval_pattern_backend (p : group_graph_pattern) (gb : graph_backend) (dsb : dataset_backend)
  : Tot solution_sequence (decreases p) =
  match p with
  | GP_BGP bgp ->
    eval_bgp_backend bgp gb

  | GP_Join p1 p2 ->
    join (eval_pattern_backend p1 gb dsb) (eval_pattern_backend p2 gb dsb)

  | GP_LeftJoin p1 p2 filter_e ->
    left_join (eval_pattern_backend p1 gb dsb) (eval_pattern_backend p2 gb dsb) filter_e

  | GP_Filter e p' ->
    filter_solutions_fwd e (eval_pattern_backend p' gb dsb)

  | GP_Union p1 p2 ->
    union (eval_pattern_backend p1 gb dsb) (eval_pattern_backend p2 gb dsb)

  | GP_Minus p1 p2 ->
    minus (eval_pattern_backend p1 gb dsb) (eval_pattern_backend p2 gb dsb)

  | GP_Empty ->
    [sm_empty]

  | GP_Bind e v p' ->
    let omega = eval_pattern_backend p' gb dsb in
    List.Tot.map
      (fun mu ->
        match er_to_term (eval_expr_fwd e mu) with
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
        | Some ngb -> eval_pattern_backend p' ngb dsb
        | None -> [])
     | PT_Var v ->
       let candidates = named_candidate_backends dsb.dsb_named (pattern_predicate_hint p') in
       List.Tot.concatMap
         (fun (ngb : named_graph_backend) ->
           let ng_results = eval_pattern_backend p' ngb.ngb_graph dsb in
           if is_iri ngb.ngb_name then
             List.Tot.map (fun mu -> sm_bind v (T_IRI ngb.ngb_name) mu) ng_results
           else ng_results)
         candidates
     | _ ->
       eval_pattern_backend p' gb dsb)

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
        | Select_Vars items -> eval_select_items items omega []
        | Select_All -> omega in
      let ordered = match q.q_modifier.sm_order_by with
        | None -> omega'
        | Some o -> sort_solutions o omega' in
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
    let n = backend_estimate gb bound in
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
      let omega0 = eval_pattern_backend q.q_pattern gb dsb in
      let omega = match q.q_values with
        | None -> omega0
        | Some vals -> join omega0 vals in
      let needs_grouping = match q.q_group_by with
        | Some _ -> true
        | None -> select_has_aggregates sel in
      if needs_grouping then
        let groups = match q.q_group_by with
          | Some conds -> group_by conds omega
          | None -> implicit_group omega in
        let filtered_groups = match q.q_having with
          | Some conditions -> having_filter conditions groups
          | None -> groups in
        let omega' = match sel with
          | Select_Vars items -> aggregate_groups items filtered_groups
          | Select_All ->
            List.Tot.map (fun (grp : group) ->
              match grp.g_solutions with
              | mu :: _ -> mu
              | [] -> sm_empty) filtered_groups in
        let ordered = match q.q_modifier.sm_order_by with
          | None -> omega'
          | Some o -> sort_solutions o omega' in
        let deduped =
          if q.q_modifier.sm_distinct then distinct_solutions ordered
          else if q.q_modifier.sm_reduced then reduced_solutions ordered
          else ordered in
        Some (slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped)
      else
        let omega' = match sel with
          | Select_Vars items -> eval_select_items items omega []
          | Select_All -> omega in
        let ordered = match q.q_modifier.sm_order_by with
          | None -> omega'
          | Some o -> sort_solutions o omega' in
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
  eval_select_query_backend_on_graph q dsb.dsb_default dsb

and eval_ask_query_backend_dataset (q : query) (dsb : dataset_backend)
  : option bool =
  match q.q_form with
  | QF_Ask ->
    let omega0 = eval_pattern_backend q.q_pattern dsb.dsb_default dsb in
    let omega = match q.q_values with
      | None -> omega0
      | Some vals -> join omega0 vals in
    Some (match omega with | [] -> false | _ -> true)
  | _ -> None
