open Prims
type graph_backend =
  | GB_List of RDF_Graph_Executable.rdf_graph 
  | GB_HDT of Parser_BallyhooHDT.hdt_graph_store 
  | GB_COTTAS of Parser_BallyhooCOTTAS.cottas_dataset_store *
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option 
  | GB_Union of graph_backend Prims.list 
let uu___is_GB_List (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_List _0 -> true | uu___ -> false
let __proj__GB_List__item___0 (projectee : graph_backend) :
  RDF_Graph_Executable.rdf_graph= match projectee with | GB_List _0 -> _0
let uu___is_GB_HDT (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_HDT _0 -> true | uu___ -> false
let __proj__GB_HDT__item___0 (projectee : graph_backend) :
  Parser_BallyhooHDT.hdt_graph_store= match projectee with | GB_HDT _0 -> _0
let uu___is_GB_COTTAS (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_COTTAS (_0, _1) -> true | uu___ -> false
let __proj__GB_COTTAS__item___0 (projectee : graph_backend) :
  Parser_BallyhooCOTTAS.cottas_dataset_store=
  match projectee with | GB_COTTAS (_0, _1) -> _0
let __proj__GB_COTTAS__item___1 (projectee : graph_backend) :
  RDF_Graph_Executable.iri FStar_Pervasives_Native.option=
  match projectee with | GB_COTTAS (_0, _1) -> _1
let uu___is_GB_Union (projectee : graph_backend) : Prims.bool=
  match projectee with | GB_Union _0 -> true | uu___ -> false
let __proj__GB_Union__item___0 (projectee : graph_backend) :
  graph_backend Prims.list= match projectee with | GB_Union _0 -> _0
type named_graph_backend =
  {
  ngb_name: RDF_Graph_Executable.iri ;
  ngb_graph: graph_backend }
let __proj__Mknamed_graph_backend__item__ngb_name
  (projectee : named_graph_backend) : RDF_Graph_Executable.iri=
  match projectee with | { ngb_name; ngb_graph;_} -> ngb_name
let __proj__Mknamed_graph_backend__item__ngb_graph
  (projectee : named_graph_backend) : graph_backend=
  match projectee with | { ngb_name; ngb_graph;_} -> ngb_graph
type dataset_backend =
  {
  dsb_default: graph_backend ;
  dsb_named: named_graph_backend Prims.list }
let __proj__Mkdataset_backend__item__dsb_default
  (projectee : dataset_backend) : graph_backend=
  match projectee with | { dsb_default; dsb_named;_} -> dsb_default
let __proj__Mkdataset_backend__item__dsb_named (projectee : dataset_backend)
  : named_graph_backend Prims.list=
  match projectee with | { dsb_default; dsb_named;_} -> dsb_named
let list_graph_backend (g : RDF_Graph_Executable.rdf_graph) : graph_backend=
  GB_List g
let list_dataset_backend (ds : RDF_Graph_Executable.rdf_dataset) :
  dataset_backend=
  {
    dsb_default = (GB_List (ds.RDF_Graph_Executable.ds_default));
    dsb_named =
      (FStar_List_Tot_Base.map
         (fun ng ->
            {
              ngb_name = (ng.RDF_Graph_Executable.ng_name);
              ngb_graph = (GB_List (ng.RDF_Graph_Executable.ng_graph))
            }) ds.RDF_Graph_Executable.ds_named)
  }
let rec union_backend_search (members : graph_backend Prims.list)
  (b : SPARQL11_Algebra.triple_pattern_bound) :
  RDF_Graph_Executable.triple Prims.list=
  match members with
  | [] -> []
  | member::rest ->
      FStar_List_Tot_Base.append (backend_search member b)
        (union_backend_search rest b)
and backend_search (gb : graph_backend)
  (b : SPARQL11_Algebra.triple_pattern_bound) :
  RDF_Graph_Executable.triple Prims.list=
  match gb with
  | GB_List g ->
      SPARQL11_Algebra.store_search (SPARQL11_Algebra.graph_to_store g) b
  | GB_HDT hgs ->
      Parser_BallyhooHDT.hdt_search_triples hgs b.SPARQL11_Algebra.bs
        b.SPARQL11_Algebra.bp b.SPARQL11_Algebra.bo
  | GB_COTTAS (cds, graph_name) ->
      let rows =
        Parser_BallyhooCOTTAS.cottas_search cds
          (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
             b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp
             b.SPARQL11_Algebra.bo graph_name) in
      FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
        (Parser_BallyhooCOTTAS.cottas_rows_to_quads cds rows)
  | GB_Union members -> union_backend_search members b
let rec union_backend_estimate (members : graph_backend Prims.list)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  match members with
  | [] -> Prims.int_zero
  | member::rest ->
      (backend_estimate member b) + (union_backend_estimate rest b)
and backend_estimate (gb : graph_backend)
  (b : SPARQL11_Algebra.triple_pattern_bound) : Prims.nat=
  match gb with
  | GB_List g ->
      SPARQL11_Algebra.store_estimate (SPARQL11_Algebra.graph_to_store g) b
  | GB_HDT hgs ->
      Parser_BallyhooHDT.hdt_estimate hgs
        (Parser_BallyhooHDT.hdt_build_bound_tp hgs b.SPARQL11_Algebra.bs
           b.SPARQL11_Algebra.bp b.SPARQL11_Algebra.bo)
  | GB_COTTAS (cds, graph_name) ->
      Parser_BallyhooCOTTAS.cottas_estimate cds
        (Parser_BallyhooCOTTAS.cottas_build_bound_qp cds
           b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp b.SPARQL11_Algebra.bo
           graph_name)
  | GB_Union members -> union_backend_estimate members b
let rec union_backend_predicate_present (members : graph_backend Prims.list)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  match members with
  | [] -> false
  | member::rest ->
      if backend_predicate_present member pred
      then true
      else union_backend_predicate_present rest pred
and backend_predicate_present (gb : graph_backend)
  (pred : RDF_Graph_Executable.wf_iri) : Prims.bool=
  match gb with
  | GB_List g ->
      (backend_estimate (GB_List g)
         {
           SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
           SPARQL11_Algebra.bp = (FStar_Pervasives_Native.Some pred);
           SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
         })
        > Prims.int_zero
  | GB_HDT hgs -> Parser_BallyhooHDT.hdt_predicate_present hgs pred
  | GB_COTTAS (cds, graph_name) ->
      (backend_estimate (GB_COTTAS (cds, graph_name))
         {
           SPARQL11_Algebra.bs = FStar_Pervasives_Native.None;
           SPARQL11_Algebra.bp = (FStar_Pervasives_Native.Some pred);
           SPARQL11_Algebra.bo = FStar_Pervasives_Native.None
         })
        > Prims.int_zero
  | GB_Union members -> union_backend_predicate_present members pred
let rec lookup_named_backend (name : RDF_Graph_Executable.iri)
  (named : named_graph_backend Prims.list) :
  graph_backend FStar_Pervasives_Native.option=
  match named with
  | [] -> FStar_Pervasives_Native.None
  | ng::rest ->
      if ng.ngb_name = name
      then FStar_Pervasives_Native.Some (ng.ngb_graph)
      else lookup_named_backend name rest
let eval_single_tp_backend (tp : SPARQL11_Algebra.triple_pattern)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping) :
  SPARQL11_Algebra.solution_sequence=
  let bound =
    {
      SPARQL11_Algebra.bs =
        (SPARQL11_Algebra.bound_subject_of_pattern tp.SPARQL11_Algebra.tp_s
           mu);
      SPARQL11_Algebra.bp =
        (SPARQL11_Algebra.bound_predicate_of_pattern tp.SPARQL11_Algebra.tp_p
           mu);
      SPARQL11_Algebra.bo =
        (SPARQL11_Algebra.bound_object_of_pattern tp.SPARQL11_Algebra.tp_o mu)
    } in
  let candidates = backend_search gb bound in
  SPARQL11_Algebra.list_filter_map
    (fun t -> SPARQL11_Algebra.tp_match tp t mu) candidates
let estimate_tp_backend_mu (tp : SPARQL11_Algebra.triple_pattern)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping) :
  Prims.nat=
  backend_estimate gb
    {
      SPARQL11_Algebra.bs =
        (SPARQL11_Algebra.bound_subject_of_pattern tp.SPARQL11_Algebra.tp_s
           mu);
      SPARQL11_Algebra.bp =
        (SPARQL11_Algebra.bound_predicate_of_pattern tp.SPARQL11_Algebra.tp_p
           mu);
      SPARQL11_Algebra.bo =
        (SPARQL11_Algebra.bound_object_of_pattern tp.SPARQL11_Algebra.tp_o mu)
    }
let rec choose_best_tp_backend (patterns : SPARQL11_Algebra.bgp)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping) :
  (SPARQL11_Algebra.triple_pattern * SPARQL11_Algebra.bgp)
    FStar_Pervasives_Native.option=
  match patterns with
  | [] -> FStar_Pervasives_Native.None
  | tp::rest ->
      (match choose_best_tp_backend rest gb mu with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (tp, [])
       | FStar_Pervasives_Native.Some (best, remaining) ->
           if
             (estimate_tp_backend_mu tp gb mu) <=
               (estimate_tp_backend_mu best gb mu)
           then FStar_Pervasives_Native.Some (tp, rest)
           else FStar_Pervasives_Native.Some (best, (tp :: remaining)))
let rec pattern_predicate_hint (p : SPARQL11_Algebra.group_graph_pattern) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match p with
  | SPARQL11_Algebra.GP_BGP [] -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_BGP (tp::uu___) ->
      (match tp.SPARQL11_Algebra.tp_p with
       | SPARQL11_Algebra.PT_IRI pred -> FStar_Pervasives_Native.Some pred
       | uu___1 -> FStar_Pervasives_Native.None)
  | SPARQL11_Algebra.GP_Filter (uu___, p') -> pattern_predicate_hint p'
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, p') -> pattern_predicate_hint p'
  | SPARQL11_Algebra.GP_Graph (uu___, p') -> pattern_predicate_hint p'
  | SPARQL11_Algebra.GP_Join (p1, uu___) -> pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_LeftJoin (p1, uu___, uu___1) ->
      pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_Union (p1, uu___) -> pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_Minus (p1, uu___) -> pattern_predicate_hint p1
  | SPARQL11_Algebra.GP_Empty -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_Service (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_SubSelect uu___ -> FStar_Pervasives_Native.None
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let named_candidate_backends (named : named_graph_backend Prims.list)
  (predicate_hint :
    RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  : named_graph_backend Prims.list=
  match predicate_hint with
  | FStar_Pervasives_Native.None -> named
  | FStar_Pervasives_Native.Some pred ->
      FStar_List_Tot_Base.filter
        (fun ngb -> backend_predicate_present ngb.ngb_graph pred) named
let rec eval_bgp_backend_from_mu_fuel (patterns : SPARQL11_Algebra.bgp)
  (gb : graph_backend) (mu : RDF_Graph_Executable.solution_mapping)
  (fuel : Prims.nat) : SPARQL11_Algebra.solution_sequence=
  if fuel = Prims.int_zero
  then [mu]
  else
    (match patterns with
     | [] -> [mu]
     | uu___1 ->
         (match choose_best_tp_backend patterns gb mu with
          | FStar_Pervasives_Native.None -> [mu]
          | FStar_Pervasives_Native.Some (tp, rest) ->
              let next = eval_single_tp_backend tp gb mu in
              FStar_List_Tot_Base.concatMap
                (fun mu' ->
                   eval_bgp_backend_from_mu_fuel rest gb mu'
                     (fuel - Prims.int_one)) next))
let eval_bgp_backend (patterns : SPARQL11_Algebra.bgp) (gb : graph_backend) :
  SPARQL11_Algebra.solution_sequence=
  eval_bgp_backend_from_mu_fuel patterns gb SPARQL11_Algebra.sm_empty
    ((FStar_List_Tot_Base.length patterns) + Prims.int_one)
let rec eval_pattern_backend (p : SPARQL11_Algebra.group_graph_pattern)
  (gb : graph_backend) (dsb : dataset_backend) :
  SPARQL11_Algebra.solution_sequence=
  match p with
  | SPARQL11_Algebra.GP_BGP bgp -> eval_bgp_backend bgp gb
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      SPARQL11_Algebra.join (eval_pattern_backend p1 gb dsb)
        (eval_pattern_backend p2 gb dsb)
  | SPARQL11_Algebra.GP_LeftJoin (p1, p2, filter_e) ->
      SPARQL11_Algebra.left_join (eval_pattern_backend p1 gb dsb)
        (eval_pattern_backend p2 gb dsb) filter_e
  | SPARQL11_Algebra.GP_Filter (e, p') ->
      SPARQL11_Algebra.filter_solutions_fwd e
        (eval_pattern_backend p' gb dsb)
  | SPARQL11_Algebra.GP_Union (p1, p2) ->
      SPARQL11_Algebra.union (eval_pattern_backend p1 gb dsb)
        (eval_pattern_backend p2 gb dsb)
  | SPARQL11_Algebra.GP_Minus (p1, p2) ->
      SPARQL11_Algebra.minus (eval_pattern_backend p1 gb dsb)
        (eval_pattern_backend p2 gb dsb)
  | SPARQL11_Algebra.GP_Empty -> [SPARQL11_Algebra.sm_empty]
  | SPARQL11_Algebra.GP_Bind (e, v, p') ->
      let omega = eval_pattern_backend p' gb dsb in
      FStar_List_Tot_Base.map
        (fun mu ->
           match SPARQL11_Algebra.er_to_term
                   (SPARQL11_Algebra.eval_expr_fwd e mu)
           with
           | FStar_Pervasives_Native.Some t ->
               (match SPARQL11_Algebra.sm_lookup v mu with
                | FStar_Pervasives_Native.Some uu___ -> mu
                | FStar_Pervasives_Native.None ->
                    SPARQL11_Algebra.sm_bind v t mu)
           | FStar_Pervasives_Native.None -> mu) omega
  | SPARQL11_Algebra.GP_Values (vars, rows) ->
      SPARQL11_Algebra.eval_values vars rows
  | SPARQL11_Algebra.GP_Graph (gt, p') ->
      (match gt with
       | SPARQL11_Algebra.PT_IRI name ->
           (match lookup_named_backend name dsb.dsb_named with
            | FStar_Pervasives_Native.Some ngb ->
                eval_pattern_backend p' ngb dsb
            | FStar_Pervasives_Native.None -> [])
       | SPARQL11_Algebra.PT_Var v ->
           let candidates =
             named_candidate_backends dsb.dsb_named
               (pattern_predicate_hint p') in
           FStar_List_Tot_Base.concatMap
             (fun ngb ->
                let ng_results = eval_pattern_backend p' ngb.ngb_graph dsb in
                if RDF_Graph_Executable.is_iri ngb.ngb_name
                then
                  FStar_List_Tot_Base.map
                    (fun mu ->
                       SPARQL11_Algebra.sm_bind v
                         (RDF_Graph_Executable.T_IRI (ngb.ngb_name)) mu)
                    ng_results
                else ng_results) candidates
       | uu___ -> eval_pattern_backend p' gb dsb)
  | SPARQL11_Algebra.GP_Service (uu___, uu___1, uu___2) -> []
  | SPARQL11_Algebra.GP_SubSelect q ->
      (match eval_select_query_backend_on_graph q gb dsb with
       | FStar_Pervasives_Native.Some omega -> omega
       | FStar_Pervasives_Native.None -> [])
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) -> []
and eval_select_query_backend_bgp (q : SPARQL11_Algebra.query)
  (gb : graph_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  match ((q.SPARQL11_Algebra.q_form), (q.SPARQL11_Algebra.q_pattern)) with
  | (SPARQL11_Algebra.QF_Select sel, SPARQL11_Algebra.GP_BGP bgp) ->
      let omega0 = eval_bgp_backend bgp gb in
      let omega =
        match q.SPARQL11_Algebra.q_values with
        | FStar_Pervasives_Native.None -> omega0
        | FStar_Pervasives_Native.Some vals ->
            SPARQL11_Algebra.join omega0 vals in
      let needs_grouping =
        match q.SPARQL11_Algebra.q_group_by with
        | FStar_Pervasives_Native.Some uu___ -> true
        | FStar_Pervasives_Native.None ->
            SPARQL11_Algebra.select_has_aggregates sel in
      if needs_grouping
      then FStar_Pervasives_Native.None
      else
        (let omega' =
           match sel with
           | SPARQL11_Algebra.Select_Vars items ->
               SPARQL11_Algebra.eval_select_items items omega []
           | SPARQL11_Algebra.Select_All -> omega in
         let ordered =
           match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
           with
           | FStar_Pervasives_Native.None -> omega'
           | FStar_Pervasives_Native.Some o ->
               SPARQL11_Algebra.sort_solutions o omega' in
         let projected =
           match sel with
           | SPARQL11_Algebra.Select_Vars items ->
               SPARQL11_Algebra.project_solutions
                 (SPARQL11_Algebra.select_item_vars items) ordered
           | SPARQL11_Algebra.Select_All -> ordered in
         let deduped =
           if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
           then SPARQL11_Algebra.distinct_solutions projected
           else
             if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
             then SPARQL11_Algebra.reduced_solutions projected
             else projected in
         FStar_Pervasives_Native.Some
           (SPARQL11_Algebra.slice_solutions
              (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
              (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
              deduped))
  | uu___ -> FStar_Pervasives_Native.None
and eval_select_query_backend_on_graph (q : SPARQL11_Algebra.query)
  (gb : graph_backend) (dsb : dataset_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Select sel ->
      let omega0 = eval_pattern_backend q.SPARQL11_Algebra.q_pattern gb dsb in
      let omega =
        match q.SPARQL11_Algebra.q_values with
        | FStar_Pervasives_Native.None -> omega0
        | FStar_Pervasives_Native.Some vals ->
            SPARQL11_Algebra.join omega0 vals in
      let needs_grouping =
        match q.SPARQL11_Algebra.q_group_by with
        | FStar_Pervasives_Native.Some uu___ -> true
        | FStar_Pervasives_Native.None ->
            SPARQL11_Algebra.select_has_aggregates sel in
      if needs_grouping
      then
        let groups =
          match q.SPARQL11_Algebra.q_group_by with
          | FStar_Pervasives_Native.Some conds ->
              SPARQL11_Algebra.group_by conds omega
          | FStar_Pervasives_Native.None ->
              SPARQL11_Algebra.implicit_group omega in
        let filtered_groups =
          match q.SPARQL11_Algebra.q_having with
          | FStar_Pervasives_Native.Some conditions ->
              SPARQL11_Algebra.having_filter conditions groups
          | FStar_Pervasives_Native.None -> groups in
        let omega' =
          match sel with
          | SPARQL11_Algebra.Select_Vars items ->
              SPARQL11_Algebra.aggregate_groups items filtered_groups
          | SPARQL11_Algebra.Select_All ->
              FStar_List_Tot_Base.map
                (fun grp ->
                   match grp.SPARQL11_Algebra.g_solutions with
                   | mu::uu___ -> mu
                   | [] -> SPARQL11_Algebra.sm_empty) filtered_groups in
        let ordered =
          match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
          with
          | FStar_Pervasives_Native.None -> omega'
          | FStar_Pervasives_Native.Some o ->
              SPARQL11_Algebra.sort_solutions o omega' in
        let deduped =
          if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
          then SPARQL11_Algebra.distinct_solutions ordered
          else
            if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
            then SPARQL11_Algebra.reduced_solutions ordered
            else ordered in
        FStar_Pervasives_Native.Some
          (SPARQL11_Algebra.slice_solutions
             (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
             (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
             deduped)
      else
        (let omega' =
           match sel with
           | SPARQL11_Algebra.Select_Vars items ->
               SPARQL11_Algebra.eval_select_items items omega []
           | SPARQL11_Algebra.Select_All -> omega in
         let ordered =
           match (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by
           with
           | FStar_Pervasives_Native.None -> omega'
           | FStar_Pervasives_Native.Some o ->
               SPARQL11_Algebra.sort_solutions o omega' in
         let projected =
           match sel with
           | SPARQL11_Algebra.Select_Vars items ->
               SPARQL11_Algebra.project_solutions
                 (SPARQL11_Algebra.select_item_vars items) ordered
           | SPARQL11_Algebra.Select_All -> ordered in
         let deduped =
           if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct
           then SPARQL11_Algebra.distinct_solutions projected
           else
             if (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_reduced
             then SPARQL11_Algebra.reduced_solutions projected
             else projected in
         FStar_Pervasives_Native.Some
           (SPARQL11_Algebra.slice_solutions
              (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset
              (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit
              deduped))
  | uu___ -> FStar_Pervasives_Native.None
and eval_select_query_backend_dataset (q : SPARQL11_Algebra.query)
  (dsb : dataset_backend) :
  SPARQL11_Algebra.solution_sequence FStar_Pervasives_Native.option=
  eval_select_query_backend_on_graph q dsb.dsb_default dsb
and eval_ask_query_backend_dataset (q : SPARQL11_Algebra.query)
  (dsb : dataset_backend) : Prims.bool FStar_Pervasives_Native.option=
  match q.SPARQL11_Algebra.q_form with
  | SPARQL11_Algebra.QF_Ask ->
      let omega0 =
        eval_pattern_backend q.SPARQL11_Algebra.q_pattern dsb.dsb_default dsb in
      let omega =
        match q.SPARQL11_Algebra.q_values with
        | FStar_Pervasives_Native.None -> omega0
        | FStar_Pervasives_Native.Some vals ->
            SPARQL11_Algebra.join omega0 vals in
      FStar_Pervasives_Native.Some
        ((match omega with | [] -> false | uu___ -> true))
  | uu___ -> FStar_Pervasives_Native.None
