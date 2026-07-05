open Prims
type plan_node =
  | Plan_Bgp of SPARQL_Explain.tp_explain Prims.list 
  | Plan_Join of plan_node * plan_node 
  | Plan_LeftJoin of plan_node * plan_node 
  | Plan_Filter of plan_node 
  | Plan_Union of plan_node * plan_node 
  | Plan_Graph of Prims.string * plan_node 
  | Plan_Minus of plan_node * plan_node 
  | Plan_Bind of SPARQL11_Algebra.var_name * plan_node 
  | Plan_Values of SPARQL11_Algebra.var_name Prims.list 
  | Plan_Service of Prims.string * plan_node 
  | Plan_ServiceVar of SPARQL11_Algebra.var_name * plan_node 
  | Plan_SubSelect 
  | Plan_PropertyPath of Prims.string * Prims.string 
  | Plan_Empty 
let uu___is_Plan_Bgp (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Bgp _0 -> true | uu___ -> false
let __proj__Plan_Bgp__item___0 (projectee : plan_node) :
  SPARQL_Explain.tp_explain Prims.list=
  match projectee with | Plan_Bgp _0 -> _0
let uu___is_Plan_Join (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Join (_0, _1) -> true | uu___ -> false
let __proj__Plan_Join__item___0 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Join (_0, _1) -> _0
let __proj__Plan_Join__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Join (_0, _1) -> _1
let uu___is_Plan_LeftJoin (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_LeftJoin (_0, _1) -> true | uu___ -> false
let __proj__Plan_LeftJoin__item___0 (projectee : plan_node) : plan_node=
  match projectee with | Plan_LeftJoin (_0, _1) -> _0
let __proj__Plan_LeftJoin__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_LeftJoin (_0, _1) -> _1
let uu___is_Plan_Filter (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Filter _0 -> true | uu___ -> false
let __proj__Plan_Filter__item___0 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Filter _0 -> _0
let uu___is_Plan_Union (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Union (_0, _1) -> true | uu___ -> false
let __proj__Plan_Union__item___0 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Union (_0, _1) -> _0
let __proj__Plan_Union__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Union (_0, _1) -> _1
let uu___is_Plan_Graph (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Graph (_0, _1) -> true | uu___ -> false
let __proj__Plan_Graph__item___0 (projectee : plan_node) : Prims.string=
  match projectee with | Plan_Graph (_0, _1) -> _0
let __proj__Plan_Graph__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Graph (_0, _1) -> _1
let uu___is_Plan_Minus (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Minus (_0, _1) -> true | uu___ -> false
let __proj__Plan_Minus__item___0 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Minus (_0, _1) -> _0
let __proj__Plan_Minus__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Minus (_0, _1) -> _1
let uu___is_Plan_Bind (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Bind (_0, _1) -> true | uu___ -> false
let __proj__Plan_Bind__item___0 (projectee : plan_node) :
  SPARQL11_Algebra.var_name= match projectee with | Plan_Bind (_0, _1) -> _0
let __proj__Plan_Bind__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Bind (_0, _1) -> _1
let uu___is_Plan_Values (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Values _0 -> true | uu___ -> false
let __proj__Plan_Values__item___0 (projectee : plan_node) :
  SPARQL11_Algebra.var_name Prims.list=
  match projectee with | Plan_Values _0 -> _0
let uu___is_Plan_Service (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Service (_0, _1) -> true | uu___ -> false
let __proj__Plan_Service__item___0 (projectee : plan_node) : Prims.string=
  match projectee with | Plan_Service (_0, _1) -> _0
let __proj__Plan_Service__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_Service (_0, _1) -> _1
let uu___is_Plan_ServiceVar (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_ServiceVar (_0, _1) -> true | uu___ -> false
let __proj__Plan_ServiceVar__item___0 (projectee : plan_node) :
  SPARQL11_Algebra.var_name=
  match projectee with | Plan_ServiceVar (_0, _1) -> _0
let __proj__Plan_ServiceVar__item___1 (projectee : plan_node) : plan_node=
  match projectee with | Plan_ServiceVar (_0, _1) -> _1
let uu___is_Plan_SubSelect (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_SubSelect -> true | uu___ -> false
let uu___is_Plan_PropertyPath (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_PropertyPath (_0, _1) -> true | uu___ -> false
let __proj__Plan_PropertyPath__item___0 (projectee : plan_node) :
  Prims.string= match projectee with | Plan_PropertyPath (_0, _1) -> _0
let __proj__Plan_PropertyPath__item___1 (projectee : plan_node) :
  Prims.string= match projectee with | Plan_PropertyPath (_0, _1) -> _1
let uu___is_Plan_Empty (projectee : plan_node) : Prims.bool=
  match projectee with | Plan_Empty -> true | uu___ -> false
type plan_form =
  | PF_Select_Vars of SPARQL11_Algebra.var_name Prims.list 
  | PF_Select_All 
  | PF_Construct 
  | PF_Ask 
  | PF_Describe 
let uu___is_PF_Select_Vars (projectee : plan_form) : Prims.bool=
  match projectee with | PF_Select_Vars _0 -> true | uu___ -> false
let __proj__PF_Select_Vars__item___0 (projectee : plan_form) :
  SPARQL11_Algebra.var_name Prims.list=
  match projectee with | PF_Select_Vars _0 -> _0
let uu___is_PF_Select_All (projectee : plan_form) : Prims.bool=
  match projectee with | PF_Select_All -> true | uu___ -> false
let uu___is_PF_Construct (projectee : plan_form) : Prims.bool=
  match projectee with | PF_Construct -> true | uu___ -> false
let uu___is_PF_Ask (projectee : plan_form) : Prims.bool=
  match projectee with | PF_Ask -> true | uu___ -> false
let uu___is_PF_Describe (projectee : plan_form) : Prims.bool=
  match projectee with | PF_Describe -> true | uu___ -> false
type query_plan =
  {
  qp_form: plan_form ;
  qp_distinct: Prims.bool ;
  qp_offset: Prims.nat FStar_Pervasives_Native.option ;
  qp_limit: Prims.nat FStar_Pervasives_Native.option ;
  qp_order_by: Prims.bool ;
  qp_root: plan_node }
let __proj__Mkquery_plan__item__qp_form (projectee : query_plan) : plan_form=
  match projectee with
  | { qp_form; qp_distinct; qp_offset; qp_limit; qp_order_by; qp_root;_} ->
      qp_form
let __proj__Mkquery_plan__item__qp_distinct (projectee : query_plan) :
  Prims.bool=
  match projectee with
  | { qp_form; qp_distinct; qp_offset; qp_limit; qp_order_by; qp_root;_} ->
      qp_distinct
let __proj__Mkquery_plan__item__qp_offset (projectee : query_plan) :
  Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { qp_form; qp_distinct; qp_offset; qp_limit; qp_order_by; qp_root;_} ->
      qp_offset
let __proj__Mkquery_plan__item__qp_limit (projectee : query_plan) :
  Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { qp_form; qp_distinct; qp_offset; qp_limit; qp_order_by; qp_root;_} ->
      qp_limit
let __proj__Mkquery_plan__item__qp_order_by (projectee : query_plan) :
  Prims.bool=
  match projectee with
  | { qp_form; qp_distinct; qp_offset; qp_limit; qp_order_by; qp_root;_} ->
      qp_order_by
let __proj__Mkquery_plan__item__qp_root (projectee : query_plan) : plan_node=
  match projectee with
  | { qp_form; qp_distinct; qp_offset; qp_limit; qp_order_by; qp_root;_} ->
      qp_root
let synthetic_tp_explain (label : Prims.string)
  (tp : SPARQL11_Algebra.triple_pattern) : SPARQL_Explain.tp_explain=
  {
    SPARQL_Explain.tpx_label = label;
    SPARQL_Explain.tpx_tp = tp;
    SPARQL_Explain.tpx_s_status = (SPARQL_Explain.BS_Other "no-info");
    SPARQL_Explain.tpx_p_status = (SPARQL_Explain.BS_Other "no-info");
    SPARQL_Explain.tpx_o_status = (SPARQL_Explain.BS_Other "no-info");
    SPARQL_Explain.tpx_bound_built = false;
    SPARQL_Explain.tpx_pred_present = FStar_Pervasives_Native.None;
    SPARQL_Explain.tpx_estimate = Prims.int_zero
  }
let tp_eq (tp1 : SPARQL11_Algebra.triple_pattern)
  (tp2 : SPARQL11_Algebra.triple_pattern) : Prims.bool=
  ((SPARQL11_Algebra.pattern_subject_eq tp1.SPARQL11_Algebra.tp_s
      tp2.SPARQL11_Algebra.tp_s)
     &&
     (SPARQL11_Algebra.pattern_term_eq tp1.SPARQL11_Algebra.tp_p
        tp2.SPARQL11_Algebra.tp_p))
    &&
    (SPARQL11_Algebra.pattern_term_eq tp1.SPARQL11_Algebra.tp_o
       tp2.SPARQL11_Algebra.tp_o)
let rec find_tp_row (rows : SPARQL_Explain.tp_explain Prims.list)
  (tp : SPARQL11_Algebra.triple_pattern) :
  SPARQL_Explain.tp_explain FStar_Pervasives_Native.option=
  match rows with
  | [] -> FStar_Pervasives_Native.None
  | r::rest ->
      if tp_eq r.SPARQL_Explain.tpx_tp tp
      then FStar_Pervasives_Native.Some r
      else find_tp_row rest tp
let fresh_label (n : Prims.nat) : Prims.string=
  Prims.strcat "T" (Prims.string_of_int n)
let rec rows_for_bgp_aux (tps : SPARQL11_Algebra.triple_pattern Prims.list)
  (rows : SPARQL_Explain.tp_explain Prims.list) (idx : Prims.nat) :
  (SPARQL_Explain.tp_explain Prims.list * Prims.nat)=
  match tps with
  | [] -> ([], idx)
  | tp::rest ->
      let row =
        match find_tp_row rows tp with
        | FStar_Pervasives_Native.Some r -> r
        | FStar_Pervasives_Native.None ->
            synthetic_tp_explain (fresh_label idx) tp in
      let next_idx = idx + Prims.int_one in
      let uu___ = rows_for_bgp_aux rest rows next_idx in
      (match uu___ with | (rest_rows, idx') -> ((row :: rest_rows), idx'))
let rows_for_bgp (tps : SPARQL11_Algebra.triple_pattern Prims.list)
  (rows : SPARQL_Explain.tp_explain Prims.list) :
  SPARQL_Explain.tp_explain Prims.list=
  let uu___ = rows_for_bgp_aux tps rows Prims.int_one in
  match uu___ with | (out, uu___1) -> out
let rec build_plan (p : SPARQL11_Algebra.group_graph_pattern)
  (rows : SPARQL_Explain.tp_explain Prims.list) : plan_node=
  match p with
  | SPARQL11_Algebra.GP_BGP tps -> Plan_Bgp (rows_for_bgp tps rows)
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      Plan_Join ((build_plan p1 rows), (build_plan p2 rows))
  | SPARQL11_Algebra.GP_LeftJoin (p1, p2, uu___) ->
      Plan_LeftJoin ((build_plan p1 rows), (build_plan p2 rows))
  | SPARQL11_Algebra.GP_Filter (uu___, p1) ->
      Plan_Filter (build_plan p1 rows)
  | SPARQL11_Algebra.GP_Union (p1, p2) ->
      Plan_Union ((build_plan p1 rows), (build_plan p2 rows))
  | SPARQL11_Algebra.GP_Graph (gt, p1) ->
      Plan_Graph
        ((RDF_Pretty.pattern_term_short_explain gt), (build_plan p1 rows))
  | SPARQL11_Algebra.GP_Minus (p1, p2) ->
      Plan_Minus ((build_plan p1 rows), (build_plan p2 rows))
  | SPARQL11_Algebra.GP_Bind (uu___, v, p1) ->
      Plan_Bind (v, (build_plan p1 rows))
  | SPARQL11_Algebra.GP_Values (vars, uu___) -> Plan_Values vars
  | SPARQL11_Algebra.GP_Service (iri, p1, uu___) ->
      Plan_Service
        ((RDF_Pretty.term_short_explain (RDF_Graph_Executable.T_IRI iri)),
          (build_plan p1 rows))
  | SPARQL11_Algebra.GP_ServiceVar (v, p1, uu___) ->
      Plan_ServiceVar (v, (build_plan p1 rows))
  | SPARQL11_Algebra.GP_SubSelect uu___ -> Plan_SubSelect
  | SPARQL11_Algebra.GP_PropertyPath (s, uu___, o) ->
      Plan_PropertyPath
        ((RDF_Pretty.pattern_subject_short_explain s),
          (RDF_Pretty.pattern_term_short_explain o))
  | SPARQL11_Algebra.GP_Empty -> Plan_Empty
let plan_form_of_query_form (qf : SPARQL11_Algebra.query_form) : plan_form=
  match qf with
  | SPARQL11_Algebra.QF_Select (SPARQL11_Algebra.Select_Vars items) ->
      let vars =
        FStar_List_Tot_Base.map
          (fun it ->
             match it with
             | SPARQL11_Algebra.SI_Var v -> v
             | SPARQL11_Algebra.SI_Expr (uu___, v) -> v) items in
      PF_Select_Vars vars
  | SPARQL11_Algebra.QF_Select (SPARQL11_Algebra.Select_All) -> PF_Select_All
  | SPARQL11_Algebra.QF_Construct uu___ -> PF_Construct
  | SPARQL11_Algebra.QF_Ask -> PF_Ask
  | SPARQL11_Algebra.QF_Describe uu___ -> PF_Describe
let explain_query (q : SPARQL11_Algebra.query)
  (rows : SPARQL_Explain.tp_explain Prims.list) : query_plan=
  {
    qp_form = (plan_form_of_query_form q.SPARQL11_Algebra.q_form);
    qp_distinct =
      ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_distinct);
    qp_offset = ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_offset);
    qp_limit = ((q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_limit);
    qp_order_by =
      (FStar_Pervasives_Native.uu___is_Some
         (q.SPARQL11_Algebra.q_modifier).SPARQL11_Algebra.sm_order_by);
    qp_root = (build_plan q.SPARQL11_Algebra.q_pattern rows)
  }
let rec repeat_space (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then ""
  else Prims.strcat " " (repeat_space (n - Prims.int_one))
let indent_of (depth : Prims.nat) : Prims.string=
  repeat_space (depth + depth)
let nl : Prims.string= "\n"
let bound_built_suffix (b : Prims.bool) : Prims.string=
  if b then "" else "  <-- definitely empty (a bound term missing from dict)"
let pred_present_line (indent : Prims.string)
  (op : Prims.bool FStar_Pervasives_Native.option) : Prims.string=
  match op with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some true ->
      Prims.strcat indent
        (Prims.strcat "    predicate-presence: true (present in dictionary)"
           nl)
  | FStar_Pervasives_Native.Some false ->
      Prims.strcat indent
        (Prims.strcat
           "    predicate-presence: false (predicate ABSENT from corpus)" nl)
let tp_row_to_text (depth : Prims.nat) (r : SPARQL_Explain.tp_explain) :
  Prims.string=
  let ind = indent_of depth in
  Prims.strcat ind
    (Prims.strcat "["
       (Prims.strcat r.SPARQL_Explain.tpx_label
          (Prims.strcat "] "
             (Prims.strcat
                (RDF_Pretty.triple_pattern_short_explain
                   r.SPARQL_Explain.tpx_tp)
                (Prims.strcat nl
                   (Prims.strcat ind
                      (Prims.strcat "    s: "
                         (Prims.strcat
                            (SPARQL_Explain.bs_string
                               r.SPARQL_Explain.tpx_s_status)
                            (Prims.strcat nl
                               (Prims.strcat ind
                                  (Prims.strcat "    p: "
                                     (Prims.strcat
                                        (SPARQL_Explain.bs_string
                                           r.SPARQL_Explain.tpx_p_status)
                                        (Prims.strcat nl
                                           (Prims.strcat ind
                                              (Prims.strcat "    o: "
                                                 (Prims.strcat
                                                    (SPARQL_Explain.bs_string
                                                       r.SPARQL_Explain.tpx_o_status)
                                                    (Prims.strcat nl
                                                       (Prims.strcat ind
                                                          (Prims.strcat
                                                             "    bound built: "
                                                             (Prims.strcat
                                                                (if
                                                                   r.SPARQL_Explain.tpx_bound_built
                                                                 then "true"
                                                                 else "false")
                                                                (Prims.strcat
                                                                   (bound_built_suffix
                                                                    r.SPARQL_Explain.tpx_bound_built)
                                                                   (Prims.strcat
                                                                    nl
                                                                    (Prims.strcat
                                                                    (pred_present_line
                                                                    ind
                                                                    r.SPARQL_Explain.tpx_pred_present)
                                                                    (Prims.strcat
                                                                    ind
                                                                    (Prims.strcat
                                                                    "    estimate: "
                                                                    (Prims.strcat
                                                                    (Prims.string_of_int
                                                                    r.SPARQL_Explain.tpx_estimate)
                                                                    (Prims.strcat
                                                                    " row(s)"
                                                                    nl)))))))))))))))))))))))))))
let rec rows_to_text (depth : Prims.nat)
  (rs : SPARQL_Explain.tp_explain Prims.list) : Prims.string=
  match rs with
  | [] -> ""
  | r::rest ->
      Prims.strcat (tp_row_to_text depth r) (rows_to_text depth rest)
let rec plan_node_to_text (depth : Prims.nat) (n : plan_node) : Prims.string=
  let ind = indent_of depth in
  match n with
  | Plan_Bgp rs ->
      Prims.strcat ind
        (Prims.strcat "BGP" (Prims.strcat nl (rows_to_text depth rs)))
  | Plan_Join (p1, p2) ->
      Prims.strcat ind
        (Prims.strcat "Join"
           (Prims.strcat nl
              (Prims.strcat (plan_node_to_text (depth + Prims.int_one) p1)
                 (plan_node_to_text (depth + Prims.int_one) p2))))
  | Plan_LeftJoin (p1, p2) ->
      Prims.strcat ind
        (Prims.strcat "LeftJoin (OPTIONAL)"
           (Prims.strcat nl
              (Prims.strcat (plan_node_to_text (depth + Prims.int_one) p1)
                 (plan_node_to_text (depth + Prims.int_one) p2))))
  | Plan_Filter p1 ->
      Prims.strcat ind
        (Prims.strcat "Filter"
           (Prims.strcat nl (plan_node_to_text (depth + Prims.int_one) p1)))
  | Plan_Union (p1, p2) ->
      Prims.strcat ind
        (Prims.strcat "Union"
           (Prims.strcat nl
              (Prims.strcat (plan_node_to_text (depth + Prims.int_one) p1)
                 (plan_node_to_text (depth + Prims.int_one) p2))))
  | Plan_Graph (gt, p1) ->
      Prims.strcat ind
        (Prims.strcat "Graph "
           (Prims.strcat gt
              (Prims.strcat nl (plan_node_to_text (depth + Prims.int_one) p1))))
  | Plan_Minus (p1, p2) ->
      Prims.strcat ind
        (Prims.strcat "Minus"
           (Prims.strcat nl
              (Prims.strcat (plan_node_to_text (depth + Prims.int_one) p1)
                 (plan_node_to_text (depth + Prims.int_one) p2))))
  | Plan_Bind (v, p1) ->
      Prims.strcat ind
        (Prims.strcat "Bind ?"
           (Prims.strcat v
              (Prims.strcat nl (plan_node_to_text (depth + Prims.int_one) p1))))
  | Plan_Values vars ->
      Prims.strcat ind
        (Prims.strcat "Values ["
           (Prims.strcat (join_vars vars) (Prims.strcat "]" nl)))
  | Plan_Service (iri, p1) ->
      Prims.strcat ind
        (Prims.strcat "Service <"
           (Prims.strcat iri
              (Prims.strcat ">"
                 (Prims.strcat nl
                    (plan_node_to_text (depth + Prims.int_one) p1)))))
  | Plan_ServiceVar (v, p1) ->
      Prims.strcat ind
        (Prims.strcat "ServiceVar ?"
           (Prims.strcat v
              (Prims.strcat nl (plan_node_to_text (depth + Prims.int_one) p1))))
  | Plan_SubSelect -> Prims.strcat ind (Prims.strcat "SubSelect (...)" nl)
  | Plan_PropertyPath (s, o) ->
      Prims.strcat ind
        (Prims.strcat "PropertyPath "
           (Prims.strcat s (Prims.strcat " ... " (Prims.strcat o nl))))
  | Plan_Empty -> Prims.strcat ind (Prims.strcat "Empty" nl)
and join_vars (vars : SPARQL11_Algebra.var_name Prims.list) : Prims.string=
  match vars with
  | [] -> ""
  | v::[] -> Prims.strcat "?" v
  | v::tl ->
      Prims.strcat "?" (Prims.strcat v (Prims.strcat ", " (join_vars tl)))
let plan_form_to_text (pf : plan_form) : Prims.string=
  match pf with
  | PF_Select_Vars vars ->
      Prims.strcat "Project [" (Prims.strcat (join_vars vars) "]")
  | PF_Select_All -> "Project [*]"
  | PF_Construct -> "Construct"
  | PF_Ask -> "Ask"
  | PF_Describe -> "Describe"
let slice_line (offset : Prims.nat FStar_Pervasives_Native.option)
  (limit : Prims.nat FStar_Pervasives_Native.option) : Prims.string=
  match (offset, limit) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> ""
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some l) ->
      Prims.strcat "Slice limit=" (Prims.string_of_int l)
  | (FStar_Pervasives_Native.Some o, FStar_Pervasives_Native.None) ->
      Prims.strcat "Slice offset=" (Prims.string_of_int o)
  | (FStar_Pervasives_Native.Some o, FStar_Pervasives_Native.Some l) ->
      Prims.strcat "Slice offset="
        (Prims.strcat (Prims.string_of_int o)
           (Prims.strcat " limit=" (Prims.string_of_int l)))
let query_plan_to_text (qp : query_plan) : Prims.string=
  let header = Prims.strcat (plan_form_to_text qp.qp_form) nl in
  let depth0 = Prims.int_one in
  let ind0 = indent_of depth0 in
  let uu___ =
    if qp.qp_distinct
    then
      ((depth0 + Prims.int_one),
        (Prims.strcat ind0 (Prims.strcat "Distinct" nl)))
    else (depth0, "") in
  match uu___ with
  | (depth1, distinct_line) ->
      let ind1 = indent_of depth1 in
      let uu___1 =
        let sl = slice_line qp.qp_offset qp.qp_limit in
        if sl = ""
        then (depth1, "")
        else
          ((depth1 + Prims.int_one),
            (Prims.strcat ind1 (Prims.strcat sl nl))) in
      (match uu___1 with
       | (depth2, slice_text) ->
           let ind2 = indent_of depth2 in
           let uu___2 =
             if qp.qp_order_by
             then
               ((depth2 + Prims.int_one),
                 (Prims.strcat ind2 (Prims.strcat "OrderBy [...]" nl)))
             else (depth2, "") in
           (match uu___2 with
            | (depth3, order_text) ->
                Prims.strcat header
                  (Prims.strcat distinct_line
                     (Prims.strcat slice_text
                        (Prims.strcat order_text
                           (plan_node_to_text depth3 qp.qp_root))))))
let rec rows_to_json (rs : SPARQL_Explain.tp_explain Prims.list) :
  Prims.string=
  match rs with
  | [] -> ""
  | r::[] -> SPARQL_Explain.tpx_json r
  | r::rest ->
      Prims.strcat (SPARQL_Explain.tpx_json r)
        (Prims.strcat "," (rows_to_json rest))
let rec join_var_names_json (vars : SPARQL11_Algebra.var_name Prims.list) :
  Prims.string=
  match vars with
  | [] -> ""
  | v::[] ->
      Prims.strcat "\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape v) "\"")
  | v::tl ->
      Prims.strcat "\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape v)
           (Prims.strcat "\"," (join_var_names_json tl)))
let rec plan_node_to_json (n : plan_node) : Prims.string=
  match n with
  | Plan_Bgp rs ->
      Prims.strcat "{\"kind\":\"bgp\",\"patterns\":["
        (Prims.strcat (rows_to_json rs) "]}")
  | Plan_Join (p1, p2) ->
      Prims.strcat "{\"kind\":\"join\",\"left\":"
        (Prims.strcat (plan_node_to_json p1)
           (Prims.strcat ",\"right\":"
              (Prims.strcat (plan_node_to_json p2) "}")))
  | Plan_LeftJoin (p1, p2) ->
      Prims.strcat "{\"kind\":\"leftjoin\",\"left\":"
        (Prims.strcat (plan_node_to_json p1)
           (Prims.strcat ",\"right\":"
              (Prims.strcat (plan_node_to_json p2) "}")))
  | Plan_Filter p1 ->
      Prims.strcat "{\"kind\":\"filter\",\"inner\":"
        (Prims.strcat (plan_node_to_json p1) "}")
  | Plan_Union (p1, p2) ->
      Prims.strcat "{\"kind\":\"union\",\"left\":"
        (Prims.strcat (plan_node_to_json p1)
           (Prims.strcat ",\"right\":"
              (Prims.strcat (plan_node_to_json p2) "}")))
  | Plan_Graph (gt, p1) ->
      Prims.strcat "{\"kind\":\"graph\",\"term\":\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape gt)
           (Prims.strcat "\",\"inner\":"
              (Prims.strcat (plan_node_to_json p1) "}")))
  | Plan_Minus (p1, p2) ->
      Prims.strcat "{\"kind\":\"minus\",\"left\":"
        (Prims.strcat (plan_node_to_json p1)
           (Prims.strcat ",\"right\":"
              (Prims.strcat (plan_node_to_json p2) "}")))
  | Plan_Bind (v, p1) ->
      Prims.strcat "{\"kind\":\"bind\",\"var\":\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape v)
           (Prims.strcat "\",\"inner\":"
              (Prims.strcat (plan_node_to_json p1) "}")))
  | Plan_Values vars ->
      Prims.strcat "{\"kind\":\"values\",\"vars\":["
        (Prims.strcat (join_var_names_json vars) "]}")
  | Plan_Service (iri, p1) ->
      Prims.strcat "{\"kind\":\"service\",\"iri\":\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape iri)
           (Prims.strcat "\",\"inner\":"
              (Prims.strcat (plan_node_to_json p1) "}")))
  | Plan_ServiceVar (v, p1) ->
      Prims.strcat "{\"kind\":\"service_var\",\"var\":\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape v)
           (Prims.strcat "\",\"inner\":"
              (Prims.strcat (plan_node_to_json p1) "}")))
  | Plan_SubSelect -> "{\"kind\":\"subselect\"}"
  | Plan_PropertyPath (s, o) ->
      Prims.strcat "{\"kind\":\"property_path\",\"subject\":\""
        (Prims.strcat (SPARQL_JSON_Escape.json_escape s)
           (Prims.strcat "\",\"object\":\""
              (Prims.strcat (SPARQL_JSON_Escape.json_escape o) "\"}")))
  | Plan_Empty -> "{\"kind\":\"empty\"}"
let plan_form_to_json (pf : plan_form) : Prims.string=
  match pf with
  | PF_Select_Vars vars ->
      Prims.strcat "{\"kind\":\"select_vars\",\"vars\":["
        (Prims.strcat (join_var_names_json vars) "]}")
  | PF_Select_All -> "{\"kind\":\"select_all\"}"
  | PF_Construct -> "{\"kind\":\"construct\"}"
  | PF_Ask -> "{\"kind\":\"ask\"}"
  | PF_Describe -> "{\"kind\":\"describe\"}"
let opt_nat_json (on : Prims.nat FStar_Pervasives_Native.option) :
  Prims.string=
  match on with
  | FStar_Pervasives_Native.None -> "null"
  | FStar_Pervasives_Native.Some n -> Prims.string_of_int n
let query_plan_to_json (qp : query_plan) : Prims.string=
  Prims.strcat "{\"form\":"
    (Prims.strcat (plan_form_to_json qp.qp_form)
       (Prims.strcat ",\"distinct\":"
          (Prims.strcat (if qp.qp_distinct then "true" else "false")
             (Prims.strcat ",\"offset\":"
                (Prims.strcat (opt_nat_json qp.qp_offset)
                   (Prims.strcat ",\"limit\":"
                      (Prims.strcat (opt_nat_json qp.qp_limit)
                         (Prims.strcat ",\"order_by\":"
                            (Prims.strcat
                               (if qp.qp_order_by then "true" else "false")
                               (Prims.strcat ",\"root\":"
                                  (Prims.strcat
                                     (plan_node_to_json qp.qp_root) "}")))))))))))
let plan_node_well_formed (uu___ : plan_node) : Prims.bool= true
let query_plan_well_formed (uu___ : query_plan) : Prims.bool= true
