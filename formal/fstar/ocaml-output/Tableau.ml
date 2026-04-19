open Prims
let owl_intersectionOf : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#intersectionOf"
let owl_unionOf : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#unionOf"
let owl_complementOf : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#complementOf"
let owl_Restriction : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#Restriction"
let owl_onProperty : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#onProperty"
let owl_someValuesFrom : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#someValuesFrom"
let owl_allValuesFrom : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#allValuesFrom"
let owl_hasValue : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2002/07/owl#hasValue"
let rdf_first : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
type class_expr =
  | CE_Named of RDF_Graph_Executable.wf_iri 
  | CE_SomeValuesFrom of RDF_Graph_Executable.wf_iri * class_expr 
  | CE_AllValuesFrom of RDF_Graph_Executable.wf_iri * class_expr 
  | CE_HasValue of RDF_Graph_Executable.wf_iri *
  RDF_Graph_Executable.rdf_term 
  | CE_IntersectionOf of class_expr Prims.list 
  | CE_UnionOf of class_expr Prims.list 
  | CE_ComplementOf of class_expr 
  | CE_Unknown 
let uu___is_CE_Named (projectee : class_expr) : Prims.bool=
  match projectee with | CE_Named _0 -> true | uu___ -> false
let __proj__CE_Named__item___0 (projectee : class_expr) :
  RDF_Graph_Executable.wf_iri= match projectee with | CE_Named _0 -> _0
let uu___is_CE_SomeValuesFrom (projectee : class_expr) : Prims.bool=
  match projectee with | CE_SomeValuesFrom (_0, _1) -> true | uu___ -> false
let __proj__CE_SomeValuesFrom__item___0 (projectee : class_expr) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | CE_SomeValuesFrom (_0, _1) -> _0
let __proj__CE_SomeValuesFrom__item___1 (projectee : class_expr) :
  class_expr= match projectee with | CE_SomeValuesFrom (_0, _1) -> _1
let uu___is_CE_AllValuesFrom (projectee : class_expr) : Prims.bool=
  match projectee with | CE_AllValuesFrom (_0, _1) -> true | uu___ -> false
let __proj__CE_AllValuesFrom__item___0 (projectee : class_expr) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | CE_AllValuesFrom (_0, _1) -> _0
let __proj__CE_AllValuesFrom__item___1 (projectee : class_expr) : class_expr=
  match projectee with | CE_AllValuesFrom (_0, _1) -> _1
let uu___is_CE_HasValue (projectee : class_expr) : Prims.bool=
  match projectee with | CE_HasValue (_0, _1) -> true | uu___ -> false
let __proj__CE_HasValue__item___0 (projectee : class_expr) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | CE_HasValue (_0, _1) -> _0
let __proj__CE_HasValue__item___1 (projectee : class_expr) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | CE_HasValue (_0, _1) -> _1
let uu___is_CE_IntersectionOf (projectee : class_expr) : Prims.bool=
  match projectee with | CE_IntersectionOf _0 -> true | uu___ -> false
let __proj__CE_IntersectionOf__item___0 (projectee : class_expr) :
  class_expr Prims.list= match projectee with | CE_IntersectionOf _0 -> _0
let uu___is_CE_UnionOf (projectee : class_expr) : Prims.bool=
  match projectee with | CE_UnionOf _0 -> true | uu___ -> false
let __proj__CE_UnionOf__item___0 (projectee : class_expr) :
  class_expr Prims.list= match projectee with | CE_UnionOf _0 -> _0
let uu___is_CE_ComplementOf (projectee : class_expr) : Prims.bool=
  match projectee with | CE_ComplementOf _0 -> true | uu___ -> false
let __proj__CE_ComplementOf__item___0 (projectee : class_expr) : class_expr=
  match projectee with | CE_ComplementOf _0 -> _0
let uu___is_CE_Unknown (projectee : class_expr) : Prims.bool=
  match projectee with | CE_Unknown -> true | uu___ -> false
let find_first_object (g : RDF_Graph_Executable.rdf_graph)
  (subj : RDF_Graph_Executable.subject) (pred : RDF_Graph_Executable.wf_iri)
  : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match RDF_Graph_Executable.find_objects g subj pred with
  | [] -> FStar_Pervasives_Native.None
  | h::uu___ -> FStar_Pervasives_Native.Some h
let term_as_subject (t : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.subject FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_IRI i ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_IRI i)
  | RDF_Graph_Executable.T_BNode b ->
      FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_BNode b)
  | uu___ -> FStar_Pervasives_Native.None
let rec walk_rdf_list (g : RDF_Graph_Executable.rdf_graph)
  (head : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | n ->
      (match head with
       | RDF_Graph_Executable.T_IRI i -> if i = rdf_nil then [] else []
       | RDF_Graph_Executable.T_BNode uu___ ->
           (match term_as_subject head with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some s ->
                let first = find_first_object g s rdf_first in
                let rest = find_first_object g s rdf_rest in
                (match (first, rest) with
                 | (FStar_Pervasives_Native.Some h,
                    FStar_Pervasives_Native.Some t) -> h ::
                     (walk_rdf_list g t (n - Prims.int_one))
                 | (uu___1, uu___2) -> []))
       | uu___ -> [])
let rec parse_class_expr (g : RDF_Graph_Executable.rdf_graph)
  (t : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) : class_expr=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> CE_Unknown
  | n ->
      (match t with
       | RDF_Graph_Executable.T_IRI i -> CE_Named i
       | RDF_Graph_Executable.T_BNode uu___ ->
           (match term_as_subject t with
            | FStar_Pervasives_Native.None -> CE_Unknown
            | FStar_Pervasives_Native.Some s ->
                (match find_first_object g s owl_intersectionOf with
                 | FStar_Pervasives_Native.Some list_head ->
                     let items = walk_rdf_list g list_head n in
                     CE_IntersectionOf
                       (parse_class_expr_list g items (n - Prims.int_one))
                 | FStar_Pervasives_Native.None ->
                     (match find_first_object g s owl_unionOf with
                      | FStar_Pervasives_Native.Some list_head ->
                          let items = walk_rdf_list g list_head n in
                          CE_UnionOf
                            (parse_class_expr_list g items
                               (n - Prims.int_one))
                      | FStar_Pervasives_Native.None ->
                          (match find_first_object g s owl_complementOf with
                           | FStar_Pervasives_Native.Some c ->
                               CE_ComplementOf
                                 (parse_class_expr g c (n - Prims.int_one))
                           | FStar_Pervasives_Native.None ->
                               (match find_first_object g s owl_onProperty
                                with
                                | FStar_Pervasives_Native.Some
                                    (RDF_Graph_Executable.T_IRI p) ->
                                    (match find_first_object g s
                                             owl_someValuesFrom
                                     with
                                     | FStar_Pervasives_Native.Some c ->
                                         CE_SomeValuesFrom
                                           (p,
                                             (parse_class_expr g c
                                                (n - Prims.int_one)))
                                     | FStar_Pervasives_Native.None ->
                                         (match find_first_object g s
                                                  owl_allValuesFrom
                                          with
                                          | FStar_Pervasives_Native.Some c ->
                                              CE_AllValuesFrom
                                                (p,
                                                  (parse_class_expr g c
                                                     (n - Prims.int_one)))
                                          | FStar_Pervasives_Native.None ->
                                              (match find_first_object g s
                                                       owl_hasValue
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   v -> CE_HasValue (p, v)
                                               | FStar_Pervasives_Native.None
                                                   -> CE_Unknown)))
                                | uu___1 -> CE_Unknown)))))
       | uu___ -> CE_Unknown)
and parse_class_expr_list (g : RDF_Graph_Executable.rdf_graph)
  (ts : RDF_Graph_Executable.rdf_term Prims.list) (fuel : Prims.nat) :
  class_expr Prims.list=
  match ts with
  | [] -> []
  | h::tl -> (parse_class_expr g h fuel) :: (parse_class_expr_list g tl fuel)
let has_type (g : RDF_Graph_Executable.rdf_graph)
  (i : RDF_Graph_Executable.subject) (c : RDF_Graph_Executable.wf_iri) :
  Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((t.RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type) &&
          (RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s i))
         &&
         (match t.RDF_Graph_Executable.o with
          | RDF_Graph_Executable.T_IRI o -> o = c
          | uu___ -> false)) g
let find_P_successors (g : RDF_Graph_Executable.rdf_graph)
  (i : RDF_Graph_Executable.subject) (p : RDF_Graph_Executable.wf_iri) :
  RDF_Graph_Executable.rdf_term Prims.list=
  RDF_Graph_Executable.find_objects g i p
let rec any_successor_sat (f : RDF_Graph_Executable.rdf_term -> Prims.bool)
  (xs : RDF_Graph_Executable.rdf_term Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | h::tl -> if f h then true else any_successor_sat f tl
let rec is_member (g : RDF_Graph_Executable.rdf_graph)
  (i : RDF_Graph_Executable.subject) (ce : class_expr) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> FStar_Pervasives_Native.None
  | n ->
      (match ce with
       | CE_Unknown -> FStar_Pervasives_Native.None
       | CE_Named c ->
           if has_type g i c
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_HasValue (p, v) ->
           let succs = find_P_successors g i p in
           if
             any_successor_sat
               (fun t -> RDF_Graph_Executable.rdf_term_eq t v) succs
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_SomeValuesFrom (p, c) ->
           let succs = find_P_successors g i p in
           any_is_member g succs c (n - Prims.int_one)
       | CE_AllValuesFrom (p, c) ->
           let succs = find_P_successors g i p in
           all_is_member g succs c (n - Prims.int_one)
       | CE_IntersectionOf ces ->
           is_intersection_member g i ces (n - Prims.int_one)
       | CE_UnionOf ces -> is_union_member g i ces (n - Prims.int_one)
       | CE_ComplementOf c ->
           (match is_member g i c (n - Prims.int_one) with
            | FStar_Pervasives_Native.Some b ->
                FStar_Pervasives_Native.Some (Prims.op_Negation b)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
and any_is_member (g : RDF_Graph_Executable.rdf_graph)
  (ys : RDF_Graph_Executable.rdf_term Prims.list) (c : class_expr)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  match ys with
  | [] -> FStar_Pervasives_Native.None
  | y::tl ->
      (match term_as_subject y with
       | FStar_Pervasives_Native.None -> any_is_member g tl c fuel
       | FStar_Pervasives_Native.Some ys_subj ->
           (match is_member g ys_subj c fuel with
            | FStar_Pervasives_Native.Some true ->
                FStar_Pervasives_Native.Some true
            | uu___ -> any_is_member g tl c fuel))
and all_is_member (g : RDF_Graph_Executable.rdf_graph)
  (ys : RDF_Graph_Executable.rdf_term Prims.list) (c : class_expr)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  match ys with
  | [] -> FStar_Pervasives_Native.Some true
  | y::tl ->
      (match term_as_subject y with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some false
       | FStar_Pervasives_Native.Some ys_subj ->
           (match is_member g ys_subj c fuel with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | FStar_Pervasives_Native.Some true -> all_is_member g tl c fuel
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
and is_intersection_member (g : RDF_Graph_Executable.rdf_graph)
  (i : RDF_Graph_Executable.subject) (ces : class_expr Prims.list)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  match ces with
  | [] -> FStar_Pervasives_Native.Some true
  | c::tl ->
      (match is_member g i c fuel with
       | FStar_Pervasives_Native.Some false ->
           FStar_Pervasives_Native.Some false
       | FStar_Pervasives_Native.Some true ->
           is_intersection_member g i tl fuel
       | FStar_Pervasives_Native.None ->
           (match is_intersection_member g i tl fuel with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | uu___ -> FStar_Pervasives_Native.None))
and is_union_member (g : RDF_Graph_Executable.rdf_graph)
  (i : RDF_Graph_Executable.subject) (ces : class_expr Prims.list)
  (fuel : Prims.nat) : Prims.bool FStar_Pervasives_Native.option=
  match ces with
  | [] -> FStar_Pervasives_Native.Some false
  | c::tl ->
      (match is_member g i c fuel with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | FStar_Pervasives_Native.Some false -> is_union_member g i tl fuel
       | FStar_Pervasives_Native.None ->
           (match is_union_member g i tl fuel with
            | FStar_Pervasives_Native.Some true ->
                FStar_Pervasives_Native.Some true
            | uu___ -> FStar_Pervasives_Native.None))
type tab_link =
  {
  tl_pred: RDF_Graph_Executable.wf_iri ;
  tl_obj: RDF_Graph_Executable.rdf_term }
let __proj__Mktab_link__item__tl_pred (projectee : tab_link) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | { tl_pred; tl_obj;_} -> tl_pred
let __proj__Mktab_link__item__tl_obj (projectee : tab_link) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | { tl_pred; tl_obj;_} -> tl_obj
type tab_individual =
  | TI_IRI of RDF_Graph_Executable.wf_iri 
  | TI_BNode of RDF_Graph_Executable.bnode_id 
  | TI_Skolem of Prims.nat 
let uu___is_TI_IRI (projectee : tab_individual) : Prims.bool=
  match projectee with | TI_IRI _0 -> true | uu___ -> false
let __proj__TI_IRI__item___0 (projectee : tab_individual) :
  RDF_Graph_Executable.wf_iri= match projectee with | TI_IRI _0 -> _0
let uu___is_TI_BNode (projectee : tab_individual) : Prims.bool=
  match projectee with | TI_BNode _0 -> true | uu___ -> false
let __proj__TI_BNode__item___0 (projectee : tab_individual) :
  RDF_Graph_Executable.bnode_id= match projectee with | TI_BNode _0 -> _0
let uu___is_TI_Skolem (projectee : tab_individual) : Prims.bool=
  match projectee with | TI_Skolem _0 -> true | uu___ -> false
let __proj__TI_Skolem__item___0 (projectee : tab_individual) : Prims.nat=
  match projectee with | TI_Skolem _0 -> _0
type tab_node =
  {
  tn_indiv: tab_individual ;
  tn_classes: RDF_Graph_Executable.wf_iri Prims.list ;
  tn_links: tab_link Prims.list ;
  tn_same_as: tab_individual Prims.list }
let __proj__Mktab_node__item__tn_indiv (projectee : tab_node) :
  tab_individual=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_indiv
let __proj__Mktab_node__item__tn_classes (projectee : tab_node) :
  RDF_Graph_Executable.wf_iri Prims.list=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_classes
let __proj__Mktab_node__item__tn_links (projectee : tab_node) :
  tab_link Prims.list=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_links
let __proj__Mktab_node__item__tn_same_as (projectee : tab_node) :
  tab_individual Prims.list=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_same_as
let make_iri_node (i : RDF_Graph_Executable.wf_iri) : tab_node=
  { tn_indiv = (TI_IRI i); tn_classes = []; tn_links = []; tn_same_as = [] }
type tab_status =
  | Open 
  | Closed 
  | Unknown 
let uu___is_Open (projectee : tab_status) : Prims.bool=
  match projectee with | Open -> true | uu___ -> false
let uu___is_Closed (projectee : tab_status) : Prims.bool=
  match projectee with | Closed -> true | uu___ -> false
let uu___is_Unknown (projectee : tab_status) : Prims.bool=
  match projectee with | Unknown -> true | uu___ -> false
type tab_branch = {
  tb_nodes: tab_node Prims.list ;
  tb_status: tab_status }
let __proj__Mktab_branch__item__tb_nodes (projectee : tab_branch) :
  tab_node Prims.list=
  match projectee with | { tb_nodes; tb_status;_} -> tb_nodes
let __proj__Mktab_branch__item__tb_status (projectee : tab_branch) :
  tab_status= match projectee with | { tb_nodes; tb_status;_} -> tb_status
let empty_branch : tab_branch= { tb_nodes = []; tb_status = Open }
type tab_obligation = {
  tob_owner: tab_individual ;
  tob_desc: Prims.string }
let __proj__Mktab_obligation__item__tob_owner (projectee : tab_obligation) :
  tab_individual=
  match projectee with | { tob_owner; tob_desc;_} -> tob_owner
let __proj__Mktab_obligation__item__tob_desc (projectee : tab_obligation) :
  Prims.string= match projectee with | { tob_owner; tob_desc;_} -> tob_desc
type tableau_state =
  {
  ts_branches: tab_branch Prims.list ;
  ts_obligations: tab_obligation Prims.list ;
  ts_una: Prims.bool ;
  ts_fuel_used: Prims.nat }
let __proj__Mktableau_state__item__ts_branches (projectee : tableau_state) :
  tab_branch Prims.list=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_branches
let __proj__Mktableau_state__item__ts_obligations (projectee : tableau_state)
  : tab_obligation Prims.list=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_obligations
let __proj__Mktableau_state__item__ts_una (projectee : tableau_state) :
  Prims.bool=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_una
let __proj__Mktableau_state__item__ts_fuel_used (projectee : tableau_state) :
  Prims.nat=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_fuel_used
let init_tableau_state (uu___ : unit) : tableau_state=
  {
    ts_branches = [empty_branch];
    ts_obligations = [];
    ts_una = false;
    ts_fuel_used = Prims.int_zero
  }
let rec triple_in_graph (goal : RDF_Graph_Executable.triple)
  (g : RDF_Graph_Executable.rdf_graph) : Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      if RDF_Graph_Executable.triple_eq t goal
      then true
      else triple_in_graph goal rest
let tableau_step (st : tableau_state) (fuel : Prims.nat) :
  (tableau_state * tab_status)=
  if fuel = Prims.int_zero
  then (st, Unknown)
  else
    (match st.ts_obligations with
     | [] -> (st, Unknown)
     | uu___1::uu___2 -> (st, Unknown))
let owl_tableau_entails (regime : Prims.string)
  (data : RDF_Graph_Executable.rdf_dataset)
  (schema : RDF_Graph_Executable.rdf_dataset)
  (goal : RDF_Graph_Executable.triple) :
  Prims.bool FStar_Pervasives_Native.option=
  let uu___ = regime in
  let uu___1 = schema in
  let g = data.RDF_Graph_Executable.ds_default in
  if triple_in_graph goal g
  then FStar_Pervasives_Native.Some true
  else
    if goal.RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type
    then
      (let ce =
         parse_class_expr g goal.RDF_Graph_Executable.o (Prims.of_int (32)) in
       match ce with
       | CE_Unknown -> FStar_Pervasives_Native.None
       | CE_Named uu___3 -> FStar_Pervasives_Native.None
       | uu___3 ->
           is_member g goal.RDF_Graph_Executable.s ce (Prims.of_int (64)))
    else FStar_Pervasives_Native.None
let owl_tableau_entails_graph (regime : Prims.string)
  (g : RDF_Graph_Executable.rdf_graph) (goal : RDF_Graph_Executable.triple) :
  Prims.bool FStar_Pervasives_Native.option=
  let ds =
    { RDF_Graph_Executable.ds_default = g; RDF_Graph_Executable.ds_named = []
    } in
  owl_tableau_entails regime ds RDF_Graph_Executable.empty_dataset goal
let is_class_expression_subject (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : Prims.bool=
  match s with
  | RDF_Graph_Executable.S_IRI uu___ -> false
  | RDF_Graph_Executable.S_BNode uu___ ->
      (((FStar_Pervasives_Native.uu___is_Some
           (find_first_object g s owl_intersectionOf))
          ||
          (FStar_Pervasives_Native.uu___is_Some
             (find_first_object g s owl_unionOf)))
         ||
         (FStar_Pervasives_Native.uu___is_Some
            (find_first_object g s owl_complementOf)))
        ||
        (FStar_Pervasives_Native.uu___is_Some
           (find_first_object g s owl_onProperty))
let rec collect_ce_bnodes (g : RDF_Graph_Executable.rdf_graph)
  (gfull : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.subject Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let rest = collect_ce_bnodes tl gfull in
      (match t.RDF_Graph_Executable.s with
       | RDF_Graph_Executable.S_BNode uu___ ->
           if
             (is_class_expression_subject gfull t.RDF_Graph_Executable.s) &&
               (Prims.op_Negation
                  (FStar_List_Tot_Base.existsb
                     (fun x ->
                        RDF_Graph_Executable.subject_eq x
                          t.RDF_Graph_Executable.s) rest))
           then (t.RDF_Graph_Executable.s) :: rest
           else rest
       | uu___ -> rest)
let rec collect_candidate_individuals (g : RDF_Graph_Executable.rdf_graph)
  (gfull : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.subject Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let rest = collect_candidate_individuals tl gfull in
      let is_ce = is_class_expression_subject gfull t.RDF_Graph_Executable.s in
      if is_ce
      then rest
      else
        if
          FStar_List_Tot_Base.existsb
            (fun x ->
               RDF_Graph_Executable.subject_eq x t.RDF_Graph_Executable.s)
            rest
        then rest
        else (t.RDF_Graph_Executable.s) :: rest
let materialise_for_pair (g : RDF_Graph_Executable.rdf_graph)
  (i : RDF_Graph_Executable.subject) (ce_s : RDF_Graph_Executable.subject)
  (ce : class_expr) : RDF_Graph_Executable.triple Prims.list=
  let existing =
    FStar_List_Tot_Base.existsb
      (fun t ->
         ((t.RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type) &&
            (RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s i))
           &&
           (match ((t.RDF_Graph_Executable.o), ce_s) with
            | (RDF_Graph_Executable.T_IRI o, RDF_Graph_Executable.S_IRI ci)
                -> o = ci
            | (RDF_Graph_Executable.T_BNode o, RDF_Graph_Executable.S_BNode
               cb) -> o = cb
            | (uu___, uu___1) -> false)) g in
  if existing
  then []
  else
    (match is_member g i ce (Prims.of_int (64)) with
     | FStar_Pervasives_Native.Some true ->
         let obj =
           match ce_s with
           | RDF_Graph_Executable.S_IRI ci -> RDF_Graph_Executable.T_IRI ci
           | RDF_Graph_Executable.S_BNode cb ->
               RDF_Graph_Executable.T_BNode cb in
         [{
            RDF_Graph_Executable.s = i;
            RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type;
            RDF_Graph_Executable.o = obj
          }]
     | uu___1 -> [])
let rec materialise_for_ce (g : RDF_Graph_Executable.rdf_graph)
  (candidates : RDF_Graph_Executable.subject Prims.list)
  (ce_s : RDF_Graph_Executable.subject) (ce : class_expr) :
  RDF_Graph_Executable.triple Prims.list=
  match candidates with
  | [] -> []
  | i::tl ->
      FStar_List_Tot_Base.op_At (materialise_for_pair g i ce_s ce)
        (materialise_for_ce g tl ce_s ce)
let rec materialise_all (g : RDF_Graph_Executable.rdf_graph)
  (candidates : RDF_Graph_Executable.subject Prims.list)
  (ces : RDF_Graph_Executable.subject Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match ces with
  | [] -> []
  | ce_s::tl ->
      let ce =
        parse_class_expr g
          (match ce_s with
           | RDF_Graph_Executable.S_IRI i -> RDF_Graph_Executable.T_IRI i
           | RDF_Graph_Executable.S_BNode b -> RDF_Graph_Executable.T_BNode b)
          (Prims.of_int (32)) in
      (match ce with
       | CE_Unknown -> materialise_all g candidates tl
       | uu___ ->
           FStar_List_Tot_Base.op_At
             (materialise_for_ce g candidates ce_s ce)
             (materialise_all g candidates tl))
let rec emit_intersection_subclasses_via_eqc
  (named_subj : RDF_Graph_Executable.subject)
  (items : RDF_Graph_Executable.rdf_term Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match items with
  | [] -> []
  | t::tl ->
      let tail = emit_intersection_subclasses_via_eqc named_subj tl in
      (match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.Some uu___ ->
           {
             RDF_Graph_Executable.s = named_subj;
             RDF_Graph_Executable.p = RDF_Graph_Executable.rdfs_subClassOf;
             RDF_Graph_Executable.o = t
           } :: tail
       | FStar_Pervasives_Native.None -> tail)
let rec emit_union_subclasses_via_eqc
  (named_subj : RDF_Graph_Executable.subject)
  (items : RDF_Graph_Executable.rdf_term Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match items with
  | [] -> []
  | t::tl ->
      let tail = emit_union_subclasses_via_eqc named_subj tl in
      (match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.Some t_subj ->
           {
             RDF_Graph_Executable.s = t_subj;
             RDF_Graph_Executable.p = RDF_Graph_Executable.rdfs_subClassOf;
             RDF_Graph_Executable.o =
               (RDF_Graph_Executable.subject_to_term named_subj)
           } :: tail
       | FStar_Pervasives_Native.None -> tail)
let rec materialise_eqc_expansion (g : RDF_Graph_Executable.rdf_graph)
  (all : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.triple Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let tail = materialise_eqc_expansion tl all in
      if t.RDF_Graph_Executable.p = RDF_Graph_Executable.owl_equivalentClass
      then
        (match RDF_Graph_Executable.term_to_subject t.RDF_Graph_Executable.o
         with
         | FStar_Pervasives_Native.Some ce_s ->
             (match find_first_object all ce_s owl_intersectionOf with
              | FStar_Pervasives_Native.Some list_head ->
                  let items = walk_rdf_list all list_head (Prims.of_int (64)) in
                  FStar_List_Tot_Base.op_At
                    (emit_intersection_subclasses_via_eqc
                       t.RDF_Graph_Executable.s items) tail
              | FStar_Pervasives_Native.None ->
                  (match find_first_object all ce_s owl_unionOf with
                   | FStar_Pervasives_Native.Some list_head ->
                       let items =
                         walk_rdf_list all list_head (Prims.of_int (64)) in
                       FStar_List_Tot_Base.op_At
                         (emit_union_subclasses_via_eqc
                            t.RDF_Graph_Executable.s items) tail
                   | FStar_Pervasives_Native.None -> tail))
         | FStar_Pervasives_Native.None -> tail)
      else tail
let tableau_materialise (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.rdf_graph=
  let ces = collect_ce_bnodes g g in
  let individuals = collect_candidate_individuals g g in
  let instance_triples = materialise_all g individuals ces in
  let structural_triples = materialise_eqc_expansion g g in
  RDF_Graph_Executable.add_triples_if_new
    (RDF_Graph_Executable.add_triples_if_new g structural_triples)
    instance_triples
