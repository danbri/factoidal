module SPARQL11.Store

open RDF.Graph.Executable
open SPARQL11.Algebra
open Parser.BallyhooHDT
open Parser.BallyhooCOTTAS

// Backend-neutral store layer for SPARQL evaluation.
// The algebra remains the semantic source of truth; this module only dispatches
// physical triple-pattern access to specific backends.

noeq type graph_backend =
  | GB_List : rdf_graph -> graph_backend
  | GB_HDT : hdt_graph_store -> graph_backend
  | GB_COTTAS : cottas_dataset_store -> option iri -> graph_backend
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
  | GB_HDT hgs ->
    hdt_search_triples hgs b.bs b.bp b.bo
  | GB_COTTAS cds graph_name ->
    let rows = cottas_search cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name) in
    List.Tot.map fst (cottas_rows_to_quads cds rows)
  | GB_Union members ->
    union_backend_search members b

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
  | GB_HDT hgs ->
    hdt_estimate hgs (hdt_build_bound_tp hgs b.bs b.bp b.bo)
  | GB_COTTAS cds graph_name ->
    cottas_estimate cds (cottas_build_bound_qp cds b.bs b.bp b.bo graph_name)
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
  | GB_HDT hgs ->
    hdt_predicate_present hgs pred
  | GB_COTTAS cds graph_name ->
    backend_estimate (GB_COTTAS cds graph_name) {
      bs = None;
      bp = Some pred;
      bo = None;
    } > 0
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
  | _ -> None

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
