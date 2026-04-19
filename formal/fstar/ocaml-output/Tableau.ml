open Prims
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
  if triple_in_graph goal data.RDF_Graph_Executable.ds_default
  then FStar_Pervasives_Native.Some true
  else FStar_Pervasives_Native.None
let owl_tableau_entails_graph (regime : Prims.string)
  (g : RDF_Graph_Executable.rdf_graph) (goal : RDF_Graph_Executable.triple) :
  Prims.bool FStar_Pervasives_Native.option=
  let ds =
    { RDF_Graph_Executable.ds_default = g; RDF_Graph_Executable.ds_named = []
    } in
  owl_tableau_entails regime ds RDF_Graph_Executable.empty_dataset goal
