open Prims
let lit_lexical (l : RDF_Graph_Executable.wf_literal) : Prims.string=
  l.RDF_Graph_Executable.lexical_form
let lit_datatype (l : RDF_Graph_Executable.wf_literal) :
  RDF_Graph_Executable.wf_iri= l.RDF_Graph_Executable.datatype
let lit_lang (l : RDF_Graph_Executable.wf_literal) :
  Prims.string FStar_Pervasives_Native.option=
  l.RDF_Graph_Executable.lang_tag
let iri_to_string (i : RDF_Graph_Executable.wf_iri) : Prims.string= i
let string_to_iri (s : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri s
  then FStar_Pervasives_Native.Some s
  else FStar_Pervasives_Native.None
let rdf_langString : RDF_Graph_Executable.wf_iri=
  RDF_Graph_Executable.rdf_lang_string
let xsd_float : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#float"
let xsd_dateTime : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#dateTime"
let xsd_date : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#date"
let xsd_time : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#time"
let xsd_duration : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#duration"
let xsd_dayTimeDuration : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#dayTimeDuration"
let xsd_yearMonthDuration : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/2001/XMLSchema#yearMonthDuration"
let sm_empty : RDF_Graph_Executable.solution_mapping= []
let sm_lookup (v : Prims.string) (mu : RDF_Graph_Executable.solution_mapping)
  : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  FStar_List_Tot_Base.assoc v mu
let sm_bind (v : Prims.string) (t : RDF_Graph_Executable.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping= (v, t) :: mu
let sm_domain (mu : RDF_Graph_Executable.solution_mapping) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.map FStar_Pervasives_Native.fst mu
let rec sm_compatible (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  match mu1 with
  | [] -> true
  | (v, t)::rest ->
      (match FStar_List_Tot_Base.assoc v mu2 with
       | FStar_Pervasives_Native.None -> sm_compatible rest mu2
       | FStar_Pervasives_Native.Some t2 ->
           (RDF_Graph_Executable.rdf_term_eq t t2) &&
             (sm_compatible rest mu2))
let rec sm_merge_aux (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  match mu2 with
  | [] -> mu1
  | (v, t)::rest ->
      if
        FStar_Pervasives_Native.uu___is_Some
          (FStar_List_Tot_Base.assoc v mu1)
      then sm_merge_aux mu1 rest
      else sm_merge_aux ((v, t) :: mu1) rest
let sm_merge (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping= sm_merge_aux mu1 mu2
let graph_triples (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.triple Prims.list= g
let triple_subject (t : RDF_Graph_Executable.triple) :
  RDF_Graph_Executable.subject= t.RDF_Graph_Executable.s
let triple_predicate (t : RDF_Graph_Executable.triple) :
  RDF_Graph_Executable.wf_iri= t.RDF_Graph_Executable.p
let triple_object (t : RDF_Graph_Executable.triple) :
  RDF_Graph_Executable.rdf_term= t.RDF_Graph_Executable.o
type var_name = Prims.string
type pattern_term =
  | PT_Var of var_name 
  | PT_IRI of RDF_Graph_Executable.wf_iri 
  | PT_BNode of RDF_Graph_Executable.bnode_id 
  | PT_Literal of RDF_Graph_Executable.wf_literal 
let uu___is_PT_Var (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Var _0 -> true | uu___ -> false
let __proj__PT_Var__item___0 (projectee : pattern_term) : var_name=
  match projectee with | PT_Var _0 -> _0
let uu___is_PT_IRI (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_IRI _0 -> true | uu___ -> false
let __proj__PT_IRI__item___0 (projectee : pattern_term) :
  RDF_Graph_Executable.wf_iri= match projectee with | PT_IRI _0 -> _0
let uu___is_PT_BNode (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_BNode _0 -> true | uu___ -> false
let __proj__PT_BNode__item___0 (projectee : pattern_term) :
  RDF_Graph_Executable.bnode_id= match projectee with | PT_BNode _0 -> _0
let uu___is_PT_Literal (projectee : pattern_term) : Prims.bool=
  match projectee with | PT_Literal _0 -> true | uu___ -> false
let __proj__PT_Literal__item___0 (projectee : pattern_term) :
  RDF_Graph_Executable.wf_literal= match projectee with | PT_Literal _0 -> _0
type pattern_subject =
  | PS_Var of var_name 
  | PS_IRI of RDF_Graph_Executable.wf_iri 
  | PS_BNode of RDF_Graph_Executable.bnode_id 
let uu___is_PS_Var (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_Var _0 -> true | uu___ -> false
let __proj__PS_Var__item___0 (projectee : pattern_subject) : var_name=
  match projectee with | PS_Var _0 -> _0
let uu___is_PS_IRI (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_IRI _0 -> true | uu___ -> false
let __proj__PS_IRI__item___0 (projectee : pattern_subject) :
  RDF_Graph_Executable.wf_iri= match projectee with | PS_IRI _0 -> _0
let uu___is_PS_BNode (projectee : pattern_subject) : Prims.bool=
  match projectee with | PS_BNode _0 -> true | uu___ -> false
let __proj__PS_BNode__item___0 (projectee : pattern_subject) :
  RDF_Graph_Executable.bnode_id= match projectee with | PS_BNode _0 -> _0
type triple_pattern =
  {
  tp_s: pattern_subject ;
  tp_p: pattern_term ;
  tp_o: pattern_term }
let __proj__Mktriple_pattern__item__tp_s (projectee : triple_pattern) :
  pattern_subject= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_s
let __proj__Mktriple_pattern__item__tp_p (projectee : triple_pattern) :
  pattern_term= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_p
let __proj__Mktriple_pattern__item__tp_o (projectee : triple_pattern) :
  pattern_term= match projectee with | { tp_s; tp_p; tp_o;_} -> tp_o
type bgp = triple_pattern Prims.list
type comp_op =
  | CmpEq 
  | CmpNe 
  | CmpLt 
  | CmpGt 
  | CmpLe 
  | CmpGe 
let uu___is_CmpEq (projectee : comp_op) : Prims.bool=
  match projectee with | CmpEq -> true | uu___ -> false
let uu___is_CmpNe (projectee : comp_op) : Prims.bool=
  match projectee with | CmpNe -> true | uu___ -> false
let uu___is_CmpLt (projectee : comp_op) : Prims.bool=
  match projectee with | CmpLt -> true | uu___ -> false
let uu___is_CmpGt (projectee : comp_op) : Prims.bool=
  match projectee with | CmpGt -> true | uu___ -> false
let uu___is_CmpLe (projectee : comp_op) : Prims.bool=
  match projectee with | CmpLe -> true | uu___ -> false
let uu___is_CmpGe (projectee : comp_op) : Prims.bool=
  match projectee with | CmpGe -> true | uu___ -> false
type arith_op =
  | Add 
  | Sub 
  | Mul 
  | Div 
let uu___is_Add (projectee : arith_op) : Prims.bool=
  match projectee with | Add -> true | uu___ -> false
let uu___is_Sub (projectee : arith_op) : Prims.bool=
  match projectee with | Sub -> true | uu___ -> false
let uu___is_Mul (projectee : arith_op) : Prims.bool=
  match projectee with | Mul -> true | uu___ -> false
let uu___is_Div (projectee : arith_op) : Prims.bool=
  match projectee with | Div -> true | uu___ -> false
type aggregate_fn =
  | Agg_Count 
  | Agg_Sum 
  | Agg_Min 
  | Agg_Max 
  | Agg_Avg 
  | Agg_GroupConcat of Prims.string FStar_Pervasives_Native.option 
  | Agg_Sample 
let uu___is_Agg_Count (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Count -> true | uu___ -> false
let uu___is_Agg_Sum (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Sum -> true | uu___ -> false
let uu___is_Agg_Min (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Min -> true | uu___ -> false
let uu___is_Agg_Max (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Max -> true | uu___ -> false
let uu___is_Agg_Avg (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Avg -> true | uu___ -> false
let uu___is_Agg_GroupConcat (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_GroupConcat _0 -> true | uu___ -> false
let __proj__Agg_GroupConcat__item___0 (projectee : aggregate_fn) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | Agg_GroupConcat _0 -> _0
let uu___is_Agg_Sample (projectee : aggregate_fn) : Prims.bool=
  match projectee with | Agg_Sample -> true | uu___ -> false
type expr =
  | E_Var of var_name 
  | E_IRI of RDF_Graph_Executable.wf_iri 
  | E_Literal of RDF_Graph_Executable.wf_literal 
  | E_BoolLit of Prims.bool 
  | E_NumericLit of Prims.int 
  | E_DecimalLit of Prims.string 
  | E_DoubleLit of Prims.string 
  | E_Arith of arith_op * expr * expr 
  | E_UnaryMinus of expr 
  | E_UnaryPlus of expr 
  | E_Compare of comp_op * expr * expr 
  | E_And of expr * expr 
  | E_Or of expr * expr 
  | E_Not of expr 
  | E_IsIRI of expr 
  | E_IsBlank of expr 
  | E_IsLiteral of expr 
  | E_IsNumeric of expr 
  | E_Str of expr 
  | E_Lang of expr 
  | E_Datatype of expr 
  | E_IRI_fn of expr 
  | E_StrDt of expr * expr 
  | E_StrLang of expr * expr 
  | E_Bound of var_name 
  | E_If of expr * expr * expr 
  | E_Coalesce of expr Prims.list 
  | E_In of expr * expr Prims.list 
  | E_NotIn of expr * expr Prims.list 
  | E_StrLen of expr 
  | E_Substr of expr * expr * expr FStar_Pervasives_Native.option 
  | E_UCase of expr 
  | E_LCase of expr 
  | E_StrStarts of expr * expr 
  | E_StrEnds of expr * expr 
  | E_Contains of expr * expr 
  | E_StrBefore of expr * expr 
  | E_StrAfter of expr * expr 
  | E_Concat of expr Prims.list 
  | E_EncodeForUri of expr 
  | E_Replace of expr * expr * expr * expr FStar_Pervasives_Native.option 
  | E_Regex of expr * expr * expr FStar_Pervasives_Native.option 
  | E_Abs of expr 
  | E_Round of expr 
  | E_Ceil of expr 
  | E_Floor of expr 
  | E_MD5 of expr 
  | E_SHA1 of expr 
  | E_SHA256 of expr 
  | E_SHA384 of expr 
  | E_SHA512 of expr 
  | E_Now 
  | E_Year of expr 
  | E_Month of expr 
  | E_Day of expr 
  | E_Hours of expr 
  | E_Minutes of expr 
  | E_Seconds of expr 
  | E_Timezone of expr 
  | E_Tz of expr 
  | E_SameTerm of expr * expr 
  | E_Exists of group_graph_pattern 
  | E_NotExists of group_graph_pattern 
  | E_Aggregate of aggregate_fn * Prims.bool * expr 
  | E_FunctionCall of RDF_Graph_Executable.wf_iri * expr Prims.list 
and property_path =
  | PP_IRI of RDF_Graph_Executable.wf_iri 
  | PP_Inverse of property_path 
  | PP_Sequence of property_path * property_path 
  | PP_Alternative of property_path * property_path 
  | PP_ZeroOrMore of property_path 
  | PP_OneOrMore of property_path 
  | PP_ZeroOrOne of property_path 
  | PP_NegatedSet of property_path Prims.list 
and group_graph_pattern =
  | GP_BGP of bgp 
  | GP_Join of group_graph_pattern * group_graph_pattern 
  | GP_LeftJoin of group_graph_pattern * group_graph_pattern * expr 
  | GP_Filter of expr * group_graph_pattern 
  | GP_Union of group_graph_pattern * group_graph_pattern 
  | GP_Graph of pattern_term * group_graph_pattern 
  | GP_Minus of group_graph_pattern * group_graph_pattern 
  | GP_Bind of expr * var_name * group_graph_pattern 
  | GP_Values of var_name Prims.list * RDF_Graph_Executable.rdf_term
  FStar_Pervasives_Native.option Prims.list Prims.list 
  | GP_Service of RDF_Graph_Executable.wf_iri * group_graph_pattern *
  Prims.bool 
  | GP_SubSelect of query 
  | GP_PropertyPath of pattern_subject * property_path * pattern_term 
  | GP_Empty 
and order_condition =
  | OC_Asc of expr 
  | OC_Desc of expr 
and solution_modifier =
  {
  sm_order_by: order_condition Prims.list FStar_Pervasives_Native.option ;
  sm_distinct: Prims.bool ;
  sm_reduced: Prims.bool ;
  sm_offset: Prims.nat FStar_Pervasives_Native.option ;
  sm_limit: Prims.nat FStar_Pervasives_Native.option }
and select_item =
  | SI_Var of var_name 
  | SI_Expr of expr * var_name 
and select_clause =
  | Select_Vars of select_item Prims.list 
  | Select_All 
and group_condition =
  | GC_Var of var_name 
  | GC_Expr of expr * var_name FStar_Pervasives_Native.option 
  | GC_BuiltIn of expr 
and query_form =
  | QF_Select of select_clause 
  | QF_Construct of triple_pattern Prims.list 
  | QF_Ask 
  | QF_Describe of pattern_term Prims.list 
and dataset_clause =
  | DC_Default of RDF_Graph_Executable.wf_iri 
  | DC_Named of RDF_Graph_Executable.wf_iri 
and query =
  {
  q_base: RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ;
  q_prefixes: (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list ;
  q_form: query_form ;
  q_dataset: dataset_clause Prims.list ;
  q_pattern: group_graph_pattern ;
  q_group_by: group_condition Prims.list FStar_Pervasives_Native.option ;
  q_having: expr Prims.list FStar_Pervasives_Native.option ;
  q_modifier: solution_modifier }
let uu___is_E_Var (projectee : expr) : Prims.bool=
  match projectee with | E_Var _0 -> true | uu___ -> false
let __proj__E_Var__item___0 (projectee : expr) : var_name=
  match projectee with | E_Var _0 -> _0
let uu___is_E_IRI (projectee : expr) : Prims.bool=
  match projectee with | E_IRI _0 -> true | uu___ -> false
let __proj__E_IRI__item___0 (projectee : expr) : RDF_Graph_Executable.wf_iri=
  match projectee with | E_IRI _0 -> _0
let uu___is_E_Literal (projectee : expr) : Prims.bool=
  match projectee with | E_Literal _0 -> true | uu___ -> false
let __proj__E_Literal__item___0 (projectee : expr) :
  RDF_Graph_Executable.wf_literal= match projectee with | E_Literal _0 -> _0
let uu___is_E_BoolLit (projectee : expr) : Prims.bool=
  match projectee with | E_BoolLit _0 -> true | uu___ -> false
let __proj__E_BoolLit__item___0 (projectee : expr) : Prims.bool=
  match projectee with | E_BoolLit _0 -> _0
let uu___is_E_NumericLit (projectee : expr) : Prims.bool=
  match projectee with | E_NumericLit _0 -> true | uu___ -> false
let __proj__E_NumericLit__item___0 (projectee : expr) : Prims.int=
  match projectee with | E_NumericLit _0 -> _0
let uu___is_E_DecimalLit (projectee : expr) : Prims.bool=
  match projectee with | E_DecimalLit _0 -> true | uu___ -> false
let __proj__E_DecimalLit__item___0 (projectee : expr) : Prims.string=
  match projectee with | E_DecimalLit _0 -> _0
let uu___is_E_DoubleLit (projectee : expr) : Prims.bool=
  match projectee with | E_DoubleLit _0 -> true | uu___ -> false
let __proj__E_DoubleLit__item___0 (projectee : expr) : Prims.string=
  match projectee with | E_DoubleLit _0 -> _0
let uu___is_E_Arith (projectee : expr) : Prims.bool=
  match projectee with | E_Arith (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Arith__item___0 (projectee : expr) : arith_op=
  match projectee with | E_Arith (_0, _1, _2) -> _0
let __proj__E_Arith__item___1 (projectee : expr) : expr=
  match projectee with | E_Arith (_0, _1, _2) -> _1
let __proj__E_Arith__item___2 (projectee : expr) : expr=
  match projectee with | E_Arith (_0, _1, _2) -> _2
let uu___is_E_UnaryMinus (projectee : expr) : Prims.bool=
  match projectee with | E_UnaryMinus _0 -> true | uu___ -> false
let __proj__E_UnaryMinus__item___0 (projectee : expr) : expr=
  match projectee with | E_UnaryMinus _0 -> _0
let uu___is_E_UnaryPlus (projectee : expr) : Prims.bool=
  match projectee with | E_UnaryPlus _0 -> true | uu___ -> false
let __proj__E_UnaryPlus__item___0 (projectee : expr) : expr=
  match projectee with | E_UnaryPlus _0 -> _0
let uu___is_E_Compare (projectee : expr) : Prims.bool=
  match projectee with | E_Compare (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Compare__item___0 (projectee : expr) : comp_op=
  match projectee with | E_Compare (_0, _1, _2) -> _0
let __proj__E_Compare__item___1 (projectee : expr) : expr=
  match projectee with | E_Compare (_0, _1, _2) -> _1
let __proj__E_Compare__item___2 (projectee : expr) : expr=
  match projectee with | E_Compare (_0, _1, _2) -> _2
let uu___is_E_And (projectee : expr) : Prims.bool=
  match projectee with | E_And (_0, _1) -> true | uu___ -> false
let __proj__E_And__item___0 (projectee : expr) : expr=
  match projectee with | E_And (_0, _1) -> _0
let __proj__E_And__item___1 (projectee : expr) : expr=
  match projectee with | E_And (_0, _1) -> _1
let uu___is_E_Or (projectee : expr) : Prims.bool=
  match projectee with | E_Or (_0, _1) -> true | uu___ -> false
let __proj__E_Or__item___0 (projectee : expr) : expr=
  match projectee with | E_Or (_0, _1) -> _0
let __proj__E_Or__item___1 (projectee : expr) : expr=
  match projectee with | E_Or (_0, _1) -> _1
let uu___is_E_Not (projectee : expr) : Prims.bool=
  match projectee with | E_Not _0 -> true | uu___ -> false
let __proj__E_Not__item___0 (projectee : expr) : expr=
  match projectee with | E_Not _0 -> _0
let uu___is_E_IsIRI (projectee : expr) : Prims.bool=
  match projectee with | E_IsIRI _0 -> true | uu___ -> false
let __proj__E_IsIRI__item___0 (projectee : expr) : expr=
  match projectee with | E_IsIRI _0 -> _0
let uu___is_E_IsBlank (projectee : expr) : Prims.bool=
  match projectee with | E_IsBlank _0 -> true | uu___ -> false
let __proj__E_IsBlank__item___0 (projectee : expr) : expr=
  match projectee with | E_IsBlank _0 -> _0
let uu___is_E_IsLiteral (projectee : expr) : Prims.bool=
  match projectee with | E_IsLiteral _0 -> true | uu___ -> false
let __proj__E_IsLiteral__item___0 (projectee : expr) : expr=
  match projectee with | E_IsLiteral _0 -> _0
let uu___is_E_IsNumeric (projectee : expr) : Prims.bool=
  match projectee with | E_IsNumeric _0 -> true | uu___ -> false
let __proj__E_IsNumeric__item___0 (projectee : expr) : expr=
  match projectee with | E_IsNumeric _0 -> _0
let uu___is_E_Str (projectee : expr) : Prims.bool=
  match projectee with | E_Str _0 -> true | uu___ -> false
let __proj__E_Str__item___0 (projectee : expr) : expr=
  match projectee with | E_Str _0 -> _0
let uu___is_E_Lang (projectee : expr) : Prims.bool=
  match projectee with | E_Lang _0 -> true | uu___ -> false
let __proj__E_Lang__item___0 (projectee : expr) : expr=
  match projectee with | E_Lang _0 -> _0
let uu___is_E_Datatype (projectee : expr) : Prims.bool=
  match projectee with | E_Datatype _0 -> true | uu___ -> false
let __proj__E_Datatype__item___0 (projectee : expr) : expr=
  match projectee with | E_Datatype _0 -> _0
let uu___is_E_IRI_fn (projectee : expr) : Prims.bool=
  match projectee with | E_IRI_fn _0 -> true | uu___ -> false
let __proj__E_IRI_fn__item___0 (projectee : expr) : expr=
  match projectee with | E_IRI_fn _0 -> _0
let uu___is_E_StrDt (projectee : expr) : Prims.bool=
  match projectee with | E_StrDt (_0, _1) -> true | uu___ -> false
let __proj__E_StrDt__item___0 (projectee : expr) : expr=
  match projectee with | E_StrDt (_0, _1) -> _0
let __proj__E_StrDt__item___1 (projectee : expr) : expr=
  match projectee with | E_StrDt (_0, _1) -> _1
let uu___is_E_StrLang (projectee : expr) : Prims.bool=
  match projectee with | E_StrLang (_0, _1) -> true | uu___ -> false
let __proj__E_StrLang__item___0 (projectee : expr) : expr=
  match projectee with | E_StrLang (_0, _1) -> _0
let __proj__E_StrLang__item___1 (projectee : expr) : expr=
  match projectee with | E_StrLang (_0, _1) -> _1
let uu___is_E_Bound (projectee : expr) : Prims.bool=
  match projectee with | E_Bound _0 -> true | uu___ -> false
let __proj__E_Bound__item___0 (projectee : expr) : var_name=
  match projectee with | E_Bound _0 -> _0
let uu___is_E_If (projectee : expr) : Prims.bool=
  match projectee with | E_If (_0, _1, _2) -> true | uu___ -> false
let __proj__E_If__item___0 (projectee : expr) : expr=
  match projectee with | E_If (_0, _1, _2) -> _0
let __proj__E_If__item___1 (projectee : expr) : expr=
  match projectee with | E_If (_0, _1, _2) -> _1
let __proj__E_If__item___2 (projectee : expr) : expr=
  match projectee with | E_If (_0, _1, _2) -> _2
let uu___is_E_Coalesce (projectee : expr) : Prims.bool=
  match projectee with | E_Coalesce _0 -> true | uu___ -> false
let __proj__E_Coalesce__item___0 (projectee : expr) : expr Prims.list=
  match projectee with | E_Coalesce _0 -> _0
let uu___is_E_In (projectee : expr) : Prims.bool=
  match projectee with | E_In (_0, _1) -> true | uu___ -> false
let __proj__E_In__item___0 (projectee : expr) : expr=
  match projectee with | E_In (_0, _1) -> _0
let __proj__E_In__item___1 (projectee : expr) : expr Prims.list=
  match projectee with | E_In (_0, _1) -> _1
let uu___is_E_NotIn (projectee : expr) : Prims.bool=
  match projectee with | E_NotIn (_0, _1) -> true | uu___ -> false
let __proj__E_NotIn__item___0 (projectee : expr) : expr=
  match projectee with | E_NotIn (_0, _1) -> _0
let __proj__E_NotIn__item___1 (projectee : expr) : expr Prims.list=
  match projectee with | E_NotIn (_0, _1) -> _1
let uu___is_E_StrLen (projectee : expr) : Prims.bool=
  match projectee with | E_StrLen _0 -> true | uu___ -> false
let __proj__E_StrLen__item___0 (projectee : expr) : expr=
  match projectee with | E_StrLen _0 -> _0
let uu___is_E_Substr (projectee : expr) : Prims.bool=
  match projectee with | E_Substr (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Substr__item___0 (projectee : expr) : expr=
  match projectee with | E_Substr (_0, _1, _2) -> _0
let __proj__E_Substr__item___1 (projectee : expr) : expr=
  match projectee with | E_Substr (_0, _1, _2) -> _1
let __proj__E_Substr__item___2 (projectee : expr) :
  expr FStar_Pervasives_Native.option=
  match projectee with | E_Substr (_0, _1, _2) -> _2
let uu___is_E_UCase (projectee : expr) : Prims.bool=
  match projectee with | E_UCase _0 -> true | uu___ -> false
let __proj__E_UCase__item___0 (projectee : expr) : expr=
  match projectee with | E_UCase _0 -> _0
let uu___is_E_LCase (projectee : expr) : Prims.bool=
  match projectee with | E_LCase _0 -> true | uu___ -> false
let __proj__E_LCase__item___0 (projectee : expr) : expr=
  match projectee with | E_LCase _0 -> _0
let uu___is_E_StrStarts (projectee : expr) : Prims.bool=
  match projectee with | E_StrStarts (_0, _1) -> true | uu___ -> false
let __proj__E_StrStarts__item___0 (projectee : expr) : expr=
  match projectee with | E_StrStarts (_0, _1) -> _0
let __proj__E_StrStarts__item___1 (projectee : expr) : expr=
  match projectee with | E_StrStarts (_0, _1) -> _1
let uu___is_E_StrEnds (projectee : expr) : Prims.bool=
  match projectee with | E_StrEnds (_0, _1) -> true | uu___ -> false
let __proj__E_StrEnds__item___0 (projectee : expr) : expr=
  match projectee with | E_StrEnds (_0, _1) -> _0
let __proj__E_StrEnds__item___1 (projectee : expr) : expr=
  match projectee with | E_StrEnds (_0, _1) -> _1
let uu___is_E_Contains (projectee : expr) : Prims.bool=
  match projectee with | E_Contains (_0, _1) -> true | uu___ -> false
let __proj__E_Contains__item___0 (projectee : expr) : expr=
  match projectee with | E_Contains (_0, _1) -> _0
let __proj__E_Contains__item___1 (projectee : expr) : expr=
  match projectee with | E_Contains (_0, _1) -> _1
let uu___is_E_StrBefore (projectee : expr) : Prims.bool=
  match projectee with | E_StrBefore (_0, _1) -> true | uu___ -> false
let __proj__E_StrBefore__item___0 (projectee : expr) : expr=
  match projectee with | E_StrBefore (_0, _1) -> _0
let __proj__E_StrBefore__item___1 (projectee : expr) : expr=
  match projectee with | E_StrBefore (_0, _1) -> _1
let uu___is_E_StrAfter (projectee : expr) : Prims.bool=
  match projectee with | E_StrAfter (_0, _1) -> true | uu___ -> false
let __proj__E_StrAfter__item___0 (projectee : expr) : expr=
  match projectee with | E_StrAfter (_0, _1) -> _0
let __proj__E_StrAfter__item___1 (projectee : expr) : expr=
  match projectee with | E_StrAfter (_0, _1) -> _1
let uu___is_E_Concat (projectee : expr) : Prims.bool=
  match projectee with | E_Concat _0 -> true | uu___ -> false
let __proj__E_Concat__item___0 (projectee : expr) : expr Prims.list=
  match projectee with | E_Concat _0 -> _0
let uu___is_E_EncodeForUri (projectee : expr) : Prims.bool=
  match projectee with | E_EncodeForUri _0 -> true | uu___ -> false
let __proj__E_EncodeForUri__item___0 (projectee : expr) : expr=
  match projectee with | E_EncodeForUri _0 -> _0
let uu___is_E_Replace (projectee : expr) : Prims.bool=
  match projectee with | E_Replace (_0, _1, _2, _3) -> true | uu___ -> false
let __proj__E_Replace__item___0 (projectee : expr) : expr=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _0
let __proj__E_Replace__item___1 (projectee : expr) : expr=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _1
let __proj__E_Replace__item___2 (projectee : expr) : expr=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _2
let __proj__E_Replace__item___3 (projectee : expr) :
  expr FStar_Pervasives_Native.option=
  match projectee with | E_Replace (_0, _1, _2, _3) -> _3
let uu___is_E_Regex (projectee : expr) : Prims.bool=
  match projectee with | E_Regex (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Regex__item___0 (projectee : expr) : expr=
  match projectee with | E_Regex (_0, _1, _2) -> _0
let __proj__E_Regex__item___1 (projectee : expr) : expr=
  match projectee with | E_Regex (_0, _1, _2) -> _1
let __proj__E_Regex__item___2 (projectee : expr) :
  expr FStar_Pervasives_Native.option=
  match projectee with | E_Regex (_0, _1, _2) -> _2
let uu___is_E_Abs (projectee : expr) : Prims.bool=
  match projectee with | E_Abs _0 -> true | uu___ -> false
let __proj__E_Abs__item___0 (projectee : expr) : expr=
  match projectee with | E_Abs _0 -> _0
let uu___is_E_Round (projectee : expr) : Prims.bool=
  match projectee with | E_Round _0 -> true | uu___ -> false
let __proj__E_Round__item___0 (projectee : expr) : expr=
  match projectee with | E_Round _0 -> _0
let uu___is_E_Ceil (projectee : expr) : Prims.bool=
  match projectee with | E_Ceil _0 -> true | uu___ -> false
let __proj__E_Ceil__item___0 (projectee : expr) : expr=
  match projectee with | E_Ceil _0 -> _0
let uu___is_E_Floor (projectee : expr) : Prims.bool=
  match projectee with | E_Floor _0 -> true | uu___ -> false
let __proj__E_Floor__item___0 (projectee : expr) : expr=
  match projectee with | E_Floor _0 -> _0
let uu___is_E_MD5 (projectee : expr) : Prims.bool=
  match projectee with | E_MD5 _0 -> true | uu___ -> false
let __proj__E_MD5__item___0 (projectee : expr) : expr=
  match projectee with | E_MD5 _0 -> _0
let uu___is_E_SHA1 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA1 _0 -> true | uu___ -> false
let __proj__E_SHA1__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA1 _0 -> _0
let uu___is_E_SHA256 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA256 _0 -> true | uu___ -> false
let __proj__E_SHA256__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA256 _0 -> _0
let uu___is_E_SHA384 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA384 _0 -> true | uu___ -> false
let __proj__E_SHA384__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA384 _0 -> _0
let uu___is_E_SHA512 (projectee : expr) : Prims.bool=
  match projectee with | E_SHA512 _0 -> true | uu___ -> false
let __proj__E_SHA512__item___0 (projectee : expr) : expr=
  match projectee with | E_SHA512 _0 -> _0
let uu___is_E_Now (projectee : expr) : Prims.bool=
  match projectee with | E_Now -> true | uu___ -> false
let uu___is_E_Year (projectee : expr) : Prims.bool=
  match projectee with | E_Year _0 -> true | uu___ -> false
let __proj__E_Year__item___0 (projectee : expr) : expr=
  match projectee with | E_Year _0 -> _0
let uu___is_E_Month (projectee : expr) : Prims.bool=
  match projectee with | E_Month _0 -> true | uu___ -> false
let __proj__E_Month__item___0 (projectee : expr) : expr=
  match projectee with | E_Month _0 -> _0
let uu___is_E_Day (projectee : expr) : Prims.bool=
  match projectee with | E_Day _0 -> true | uu___ -> false
let __proj__E_Day__item___0 (projectee : expr) : expr=
  match projectee with | E_Day _0 -> _0
let uu___is_E_Hours (projectee : expr) : Prims.bool=
  match projectee with | E_Hours _0 -> true | uu___ -> false
let __proj__E_Hours__item___0 (projectee : expr) : expr=
  match projectee with | E_Hours _0 -> _0
let uu___is_E_Minutes (projectee : expr) : Prims.bool=
  match projectee with | E_Minutes _0 -> true | uu___ -> false
let __proj__E_Minutes__item___0 (projectee : expr) : expr=
  match projectee with | E_Minutes _0 -> _0
let uu___is_E_Seconds (projectee : expr) : Prims.bool=
  match projectee with | E_Seconds _0 -> true | uu___ -> false
let __proj__E_Seconds__item___0 (projectee : expr) : expr=
  match projectee with | E_Seconds _0 -> _0
let uu___is_E_Timezone (projectee : expr) : Prims.bool=
  match projectee with | E_Timezone _0 -> true | uu___ -> false
let __proj__E_Timezone__item___0 (projectee : expr) : expr=
  match projectee with | E_Timezone _0 -> _0
let uu___is_E_Tz (projectee : expr) : Prims.bool=
  match projectee with | E_Tz _0 -> true | uu___ -> false
let __proj__E_Tz__item___0 (projectee : expr) : expr=
  match projectee with | E_Tz _0 -> _0
let uu___is_E_SameTerm (projectee : expr) : Prims.bool=
  match projectee with | E_SameTerm (_0, _1) -> true | uu___ -> false
let __proj__E_SameTerm__item___0 (projectee : expr) : expr=
  match projectee with | E_SameTerm (_0, _1) -> _0
let __proj__E_SameTerm__item___1 (projectee : expr) : expr=
  match projectee with | E_SameTerm (_0, _1) -> _1
let uu___is_E_Exists (projectee : expr) : Prims.bool=
  match projectee with | E_Exists _0 -> true | uu___ -> false
let __proj__E_Exists__item___0 (projectee : expr) : group_graph_pattern=
  match projectee with | E_Exists _0 -> _0
let uu___is_E_NotExists (projectee : expr) : Prims.bool=
  match projectee with | E_NotExists _0 -> true | uu___ -> false
let __proj__E_NotExists__item___0 (projectee : expr) : group_graph_pattern=
  match projectee with | E_NotExists _0 -> _0
let uu___is_E_Aggregate (projectee : expr) : Prims.bool=
  match projectee with | E_Aggregate (_0, _1, _2) -> true | uu___ -> false
let __proj__E_Aggregate__item___0 (projectee : expr) : aggregate_fn=
  match projectee with | E_Aggregate (_0, _1, _2) -> _0
let __proj__E_Aggregate__item___1 (projectee : expr) : Prims.bool=
  match projectee with | E_Aggregate (_0, _1, _2) -> _1
let __proj__E_Aggregate__item___2 (projectee : expr) : expr=
  match projectee with | E_Aggregate (_0, _1, _2) -> _2
let uu___is_E_FunctionCall (projectee : expr) : Prims.bool=
  match projectee with | E_FunctionCall (_0, _1) -> true | uu___ -> false
let __proj__E_FunctionCall__item___0 (projectee : expr) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | E_FunctionCall (_0, _1) -> _0
let __proj__E_FunctionCall__item___1 (projectee : expr) : expr Prims.list=
  match projectee with | E_FunctionCall (_0, _1) -> _1
let uu___is_PP_IRI (projectee : property_path) : Prims.bool=
  match projectee with | PP_IRI _0 -> true | uu___ -> false
let __proj__PP_IRI__item___0 (projectee : property_path) :
  RDF_Graph_Executable.wf_iri= match projectee with | PP_IRI _0 -> _0
let uu___is_PP_Inverse (projectee : property_path) : Prims.bool=
  match projectee with | PP_Inverse _0 -> true | uu___ -> false
let __proj__PP_Inverse__item___0 (projectee : property_path) : property_path=
  match projectee with | PP_Inverse _0 -> _0
let uu___is_PP_Sequence (projectee : property_path) : Prims.bool=
  match projectee with | PP_Sequence (_0, _1) -> true | uu___ -> false
let __proj__PP_Sequence__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_Sequence (_0, _1) -> _0
let __proj__PP_Sequence__item___1 (projectee : property_path) :
  property_path= match projectee with | PP_Sequence (_0, _1) -> _1
let uu___is_PP_Alternative (projectee : property_path) : Prims.bool=
  match projectee with | PP_Alternative (_0, _1) -> true | uu___ -> false
let __proj__PP_Alternative__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_Alternative (_0, _1) -> _0
let __proj__PP_Alternative__item___1 (projectee : property_path) :
  property_path= match projectee with | PP_Alternative (_0, _1) -> _1
let uu___is_PP_ZeroOrMore (projectee : property_path) : Prims.bool=
  match projectee with | PP_ZeroOrMore _0 -> true | uu___ -> false
let __proj__PP_ZeroOrMore__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_ZeroOrMore _0 -> _0
let uu___is_PP_OneOrMore (projectee : property_path) : Prims.bool=
  match projectee with | PP_OneOrMore _0 -> true | uu___ -> false
let __proj__PP_OneOrMore__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_OneOrMore _0 -> _0
let uu___is_PP_ZeroOrOne (projectee : property_path) : Prims.bool=
  match projectee with | PP_ZeroOrOne _0 -> true | uu___ -> false
let __proj__PP_ZeroOrOne__item___0 (projectee : property_path) :
  property_path= match projectee with | PP_ZeroOrOne _0 -> _0
let uu___is_PP_NegatedSet (projectee : property_path) : Prims.bool=
  match projectee with | PP_NegatedSet _0 -> true | uu___ -> false
let __proj__PP_NegatedSet__item___0 (projectee : property_path) :
  property_path Prims.list= match projectee with | PP_NegatedSet _0 -> _0
let uu___is_GP_BGP (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_BGP _0 -> true | uu___ -> false
let __proj__GP_BGP__item___0 (projectee : group_graph_pattern) : bgp=
  match projectee with | GP_BGP _0 -> _0
let uu___is_GP_Join (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Join (_0, _1) -> true | uu___ -> false
let __proj__GP_Join__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Join (_0, _1) -> _0
let __proj__GP_Join__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Join (_0, _1) -> _1
let uu___is_GP_LeftJoin (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_LeftJoin (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_LeftJoin__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_LeftJoin (_0, _1, _2) -> _0
let __proj__GP_LeftJoin__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_LeftJoin (_0, _1, _2) -> _1
let __proj__GP_LeftJoin__item___2 (projectee : group_graph_pattern) : 
  expr= match projectee with | GP_LeftJoin (_0, _1, _2) -> _2
let uu___is_GP_Filter (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Filter (_0, _1) -> true | uu___ -> false
let __proj__GP_Filter__item___0 (projectee : group_graph_pattern) : expr=
  match projectee with | GP_Filter (_0, _1) -> _0
let __proj__GP_Filter__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Filter (_0, _1) -> _1
let uu___is_GP_Union (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Union (_0, _1) -> true | uu___ -> false
let __proj__GP_Union__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Union (_0, _1) -> _0
let __proj__GP_Union__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Union (_0, _1) -> _1
let uu___is_GP_Graph (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Graph (_0, _1) -> true | uu___ -> false
let __proj__GP_Graph__item___0 (projectee : group_graph_pattern) :
  pattern_term= match projectee with | GP_Graph (_0, _1) -> _0
let __proj__GP_Graph__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Graph (_0, _1) -> _1
let uu___is_GP_Minus (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Minus (_0, _1) -> true | uu___ -> false
let __proj__GP_Minus__item___0 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Minus (_0, _1) -> _0
let __proj__GP_Minus__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Minus (_0, _1) -> _1
let uu___is_GP_Bind (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Bind (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_Bind__item___0 (projectee : group_graph_pattern) : expr=
  match projectee with | GP_Bind (_0, _1, _2) -> _0
let __proj__GP_Bind__item___1 (projectee : group_graph_pattern) : var_name=
  match projectee with | GP_Bind (_0, _1, _2) -> _1
let __proj__GP_Bind__item___2 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Bind (_0, _1, _2) -> _2
let uu___is_GP_Values (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Values (_0, _1) -> true | uu___ -> false
let __proj__GP_Values__item___0 (projectee : group_graph_pattern) :
  var_name Prims.list= match projectee with | GP_Values (_0, _1) -> _0
let __proj__GP_Values__item___1 (projectee : group_graph_pattern) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
    Prims.list=
  match projectee with | GP_Values (_0, _1) -> _1
let uu___is_GP_Service (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Service (_0, _1, _2) -> true | uu___ -> false
let __proj__GP_Service__item___0 (projectee : group_graph_pattern) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | GP_Service (_0, _1, _2) -> _0
let __proj__GP_Service__item___1 (projectee : group_graph_pattern) :
  group_graph_pattern= match projectee with | GP_Service (_0, _1, _2) -> _1
let __proj__GP_Service__item___2 (projectee : group_graph_pattern) :
  Prims.bool= match projectee with | GP_Service (_0, _1, _2) -> _2
let uu___is_GP_SubSelect (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_SubSelect _0 -> true | uu___ -> false
let __proj__GP_SubSelect__item___0 (projectee : group_graph_pattern) : 
  query= match projectee with | GP_SubSelect _0 -> _0
let uu___is_GP_PropertyPath (projectee : group_graph_pattern) : Prims.bool=
  match projectee with
  | GP_PropertyPath (_0, _1, _2) -> true
  | uu___ -> false
let __proj__GP_PropertyPath__item___0 (projectee : group_graph_pattern) :
  pattern_subject= match projectee with | GP_PropertyPath (_0, _1, _2) -> _0
let __proj__GP_PropertyPath__item___1 (projectee : group_graph_pattern) :
  property_path= match projectee with | GP_PropertyPath (_0, _1, _2) -> _1
let __proj__GP_PropertyPath__item___2 (projectee : group_graph_pattern) :
  pattern_term= match projectee with | GP_PropertyPath (_0, _1, _2) -> _2
let uu___is_GP_Empty (projectee : group_graph_pattern) : Prims.bool=
  match projectee with | GP_Empty -> true | uu___ -> false
let uu___is_OC_Asc (projectee : order_condition) : Prims.bool=
  match projectee with | OC_Asc _0 -> true | uu___ -> false
let __proj__OC_Asc__item___0 (projectee : order_condition) : expr=
  match projectee with | OC_Asc _0 -> _0
let uu___is_OC_Desc (projectee : order_condition) : Prims.bool=
  match projectee with | OC_Desc _0 -> true | uu___ -> false
let __proj__OC_Desc__item___0 (projectee : order_condition) : expr=
  match projectee with | OC_Desc _0 -> _0
let __proj__Mksolution_modifier__item__sm_order_by
  (projectee : solution_modifier) :
  order_condition Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_order_by
let __proj__Mksolution_modifier__item__sm_distinct
  (projectee : solution_modifier) : Prims.bool=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_distinct
let __proj__Mksolution_modifier__item__sm_reduced
  (projectee : solution_modifier) : Prims.bool=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_reduced
let __proj__Mksolution_modifier__item__sm_offset
  (projectee : solution_modifier) : Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_offset
let __proj__Mksolution_modifier__item__sm_limit
  (projectee : solution_modifier) : Prims.nat FStar_Pervasives_Native.option=
  match projectee with
  | { sm_order_by; sm_distinct; sm_reduced; sm_offset; sm_limit;_} ->
      sm_limit
let uu___is_SI_Var (projectee : select_item) : Prims.bool=
  match projectee with | SI_Var _0 -> true | uu___ -> false
let __proj__SI_Var__item___0 (projectee : select_item) : var_name=
  match projectee with | SI_Var _0 -> _0
let uu___is_SI_Expr (projectee : select_item) : Prims.bool=
  match projectee with | SI_Expr (_0, _1) -> true | uu___ -> false
let __proj__SI_Expr__item___0 (projectee : select_item) : expr=
  match projectee with | SI_Expr (_0, _1) -> _0
let __proj__SI_Expr__item___1 (projectee : select_item) : var_name=
  match projectee with | SI_Expr (_0, _1) -> _1
let uu___is_Select_Vars (projectee : select_clause) : Prims.bool=
  match projectee with | Select_Vars _0 -> true | uu___ -> false
let __proj__Select_Vars__item___0 (projectee : select_clause) :
  select_item Prims.list= match projectee with | Select_Vars _0 -> _0
let uu___is_Select_All (projectee : select_clause) : Prims.bool=
  match projectee with | Select_All -> true | uu___ -> false
let uu___is_GC_Var (projectee : group_condition) : Prims.bool=
  match projectee with | GC_Var _0 -> true | uu___ -> false
let __proj__GC_Var__item___0 (projectee : group_condition) : var_name=
  match projectee with | GC_Var _0 -> _0
let uu___is_GC_Expr (projectee : group_condition) : Prims.bool=
  match projectee with | GC_Expr (_0, _1) -> true | uu___ -> false
let __proj__GC_Expr__item___0 (projectee : group_condition) : expr=
  match projectee with | GC_Expr (_0, _1) -> _0
let __proj__GC_Expr__item___1 (projectee : group_condition) :
  var_name FStar_Pervasives_Native.option=
  match projectee with | GC_Expr (_0, _1) -> _1
let uu___is_GC_BuiltIn (projectee : group_condition) : Prims.bool=
  match projectee with | GC_BuiltIn _0 -> true | uu___ -> false
let __proj__GC_BuiltIn__item___0 (projectee : group_condition) : expr=
  match projectee with | GC_BuiltIn _0 -> _0
let uu___is_QF_Select (projectee : query_form) : Prims.bool=
  match projectee with | QF_Select _0 -> true | uu___ -> false
let __proj__QF_Select__item___0 (projectee : query_form) : select_clause=
  match projectee with | QF_Select _0 -> _0
let uu___is_QF_Construct (projectee : query_form) : Prims.bool=
  match projectee with | QF_Construct _0 -> true | uu___ -> false
let __proj__QF_Construct__item___0 (projectee : query_form) :
  triple_pattern Prims.list= match projectee with | QF_Construct _0 -> _0
let uu___is_QF_Ask (projectee : query_form) : Prims.bool=
  match projectee with | QF_Ask -> true | uu___ -> false
let uu___is_QF_Describe (projectee : query_form) : Prims.bool=
  match projectee with | QF_Describe _0 -> true | uu___ -> false
let __proj__QF_Describe__item___0 (projectee : query_form) :
  pattern_term Prims.list= match projectee with | QF_Describe _0 -> _0
let uu___is_DC_Default (projectee : dataset_clause) : Prims.bool=
  match projectee with | DC_Default _0 -> true | uu___ -> false
let __proj__DC_Default__item___0 (projectee : dataset_clause) :
  RDF_Graph_Executable.wf_iri= match projectee with | DC_Default _0 -> _0
let uu___is_DC_Named (projectee : dataset_clause) : Prims.bool=
  match projectee with | DC_Named _0 -> true | uu___ -> false
let __proj__DC_Named__item___0 (projectee : dataset_clause) :
  RDF_Graph_Executable.wf_iri= match projectee with | DC_Named _0 -> _0
let __proj__Mkquery__item__q_base (projectee : query) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_base
let __proj__Mkquery__item__q_prefixes (projectee : query) :
  (Prims.string * RDF_Graph_Executable.wf_iri) Prims.list=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_prefixes
let __proj__Mkquery__item__q_form (projectee : query) : query_form=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_form
let __proj__Mkquery__item__q_dataset (projectee : query) :
  dataset_clause Prims.list=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_dataset
let __proj__Mkquery__item__q_pattern (projectee : query) :
  group_graph_pattern=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_pattern
let __proj__Mkquery__item__q_group_by (projectee : query) :
  group_condition Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_group_by
let __proj__Mkquery__item__q_having (projectee : query) :
  expr Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_having
let __proj__Mkquery__item__q_modifier (projectee : query) :
  solution_modifier=
  match projectee with
  | { q_base; q_prefixes; q_form; q_dataset; q_pattern; q_group_by; q_having;
      q_modifier;_} -> q_modifier
type having_condition = expr
let rec list_filter_map :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  =
  fun f l ->
    match l with
    | [] -> []
    | x::xs ->
        (match f x with
         | FStar_Pervasives_Native.Some y -> y :: (list_filter_map f xs)
         | FStar_Pervasives_Native.None -> list_filter_map f xs)
let rec list_is_prefix : 'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun prefix lst ->
    match (prefix, lst) with
    | ([], uu___) -> true
    | (uu___, []) -> false
    | (x::xs, y::ys) -> (x = y) && (list_is_prefix xs ys)
let rec list_contains_sublist :
  'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun needle haystack ->
    match haystack with
    | [] -> Prims.uu___is_Nil needle
    | uu___::rest ->
        (list_is_prefix needle haystack) ||
          (list_contains_sublist needle rest)
let rec list_drop : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then l
    else
      (match l with
       | [] -> []
       | uu___1::tl -> list_drop (n - Prims.int_one) tl)
let rec list_take : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then []
    else
      (match l with
       | [] -> []
       | hd::tl -> hd :: (list_take (n - Prims.int_one) tl))
let string_contains (s : Prims.string) (sub : Prims.string) : Prims.bool=
  list_contains_sublist (FStar_String.list_of_string sub)
    (FStar_String.list_of_string s)
let string_starts_with (s : Prims.string) (prefix : Prims.string) :
  Prims.bool=
  list_is_prefix (FStar_String.list_of_string prefix)
    (FStar_String.list_of_string s)
let string_ends_with (s : Prims.string) (suffix : Prims.string) : Prims.bool=
  list_is_prefix
    (FStar_List_Tot_Base.rev (FStar_String.list_of_string suffix))
    (FStar_List_Tot_Base.rev (FStar_String.list_of_string s))
let string_length (s : Prims.string) : Prims.nat= FStar_String.strlen s
let string_substring (s : Prims.string) (start : Prims.nat)
  (len : Prims.nat FStar_Pervasives_Native.option) : Prims.string=
  let slen = FStar_String.strlen s in
  let start' = if start >= slen then slen else start in
  let actual_len =
    match len with
    | FStar_Pervasives_Native.Some l ->
        if (start' + l) > slen then slen - start' else l
    | FStar_Pervasives_Native.None -> slen - start' in
  if (actual_len = Prims.int_zero) || (start' >= slen)
  then ""
  else FStar_String.sub s start' actual_len
let string_upper (s : Prims.string) : Prims.string= FStar_String.uppercase s
let string_lower (s : Prims.string) : Prims.string= FStar_String.lowercase s
let is_numeric_datatype (dt : RDF_Graph_Executable.wf_iri) : Prims.bool=
  (((dt = RDF_Graph_Executable.xsd_integer) ||
      (dt = RDF_Graph_Executable.xsd_decimal))
     || (dt = RDF_Graph_Executable.xsd_double))
    || (dt = xsd_float)
let mk_plain_literal (s : Prims.string) : RDF_Graph_Executable.wf_literal=
  {
    RDF_Graph_Executable.lexical_form = s;
    RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string;
    RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
  }
type eval_result =
  | ER_Term of RDF_Graph_Executable.rdf_term 
  | ER_Bool of Prims.bool 
  | ER_Num of Prims.int 
  | ER_Dec of Prims.string 
  | ER_Dbl of Prims.string 
  | ER_Error 
let uu___is_ER_Term (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Term _0 -> true | uu___ -> false
let __proj__ER_Term__item___0 (projectee : eval_result) :
  RDF_Graph_Executable.rdf_term= match projectee with | ER_Term _0 -> _0
let uu___is_ER_Bool (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Bool _0 -> true | uu___ -> false
let __proj__ER_Bool__item___0 (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Bool _0 -> _0
let uu___is_ER_Num (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Num _0 -> true | uu___ -> false
let __proj__ER_Num__item___0 (projectee : eval_result) : Prims.int=
  match projectee with | ER_Num _0 -> _0
let uu___is_ER_Dec (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Dec _0 -> true | uu___ -> false
let __proj__ER_Dec__item___0 (projectee : eval_result) : Prims.string=
  match projectee with | ER_Dec _0 -> _0
let uu___is_ER_Dbl (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Dbl _0 -> true | uu___ -> false
let __proj__ER_Dbl__item___0 (projectee : eval_result) : Prims.string=
  match projectee with | ER_Dbl _0 -> _0
let uu___is_ER_Error (projectee : eval_result) : Prims.bool=
  match projectee with | ER_Error -> true | uu___ -> false
let ebv (v : eval_result) : Prims.bool=
  match v with
  | ER_Bool b -> b
  | ER_Num n -> n <> Prims.int_zero
  | ER_Dec s -> ((s <> "0") && (s <> "0.0")) && (s <> "")
  | ER_Dbl s -> (((s <> "0") && (s <> "0.0")) && (s <> "NaN")) && (s <> "")
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
      then ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
      else
        if (lit_datatype l) = RDF_Graph_Executable.xsd_string
        then (FStar_String.strlen (lit_lexical l)) > Prims.int_zero
        else
          if (lit_datatype l) = rdf_langString
          then (FStar_String.strlen (lit_lexical l)) > Prims.int_zero
          else
            if is_numeric_datatype (lit_datatype l)
            then
              (((lit_lexical l) <> "0") && ((lit_lexical l) <> "0.0")) &&
                ((lit_lexical l) <> "")
            else false
  | ER_Term uu___ -> false
  | ER_Error -> false
let er_to_term (v : eval_result) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match v with
  | ER_Term t -> FStar_Pervasives_Native.Some t
  | ER_Bool true ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal (mk_plain_literal "true"))
  | ER_Bool false ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal (mk_plain_literal "false"))
  | ER_Num n ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal
           {
             RDF_Graph_Executable.lexical_form = (Prims.string_of_int n);
             RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer;
             RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
           })
  | ER_Dec s ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal
           {
             RDF_Graph_Executable.lexical_form = s;
             RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_decimal;
             RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
           })
  | ER_Dbl s ->
      FStar_Pervasives_Native.Some
        (RDF_Graph_Executable.T_Literal
           {
             RDF_Graph_Executable.lexical_form = s;
             RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_double;
             RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
           })
  | ER_Error -> FStar_Pervasives_Native.None
let er_to_string (v : eval_result) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      FStar_Pervasives_Native.Some (lit_lexical l)
  | ER_Term (RDF_Graph_Executable.T_IRI i) ->
      FStar_Pervasives_Native.Some (iri_to_string i)
  | uu___ -> FStar_Pervasives_Native.None
let er_string (s : Prims.string) : eval_result=
  ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal s))
let eval_arith_int (op : arith_op) (a : Prims.int) (b : Prims.int) :
  eval_result=
  match op with
  | Add -> ER_Num (a + b)
  | Sub -> ER_Num (a - b)
  | Mul -> ER_Num (a * b)
  | Div -> if b = Prims.int_zero then ER_Error else ER_Num (a / b)
let er_to_datetime_lex (v : eval_result) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      if (lit_datatype l) = xsd_dateTime
      then FStar_Pervasives_Native.Some (lit_lexical l)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec zip_bindings (vars : var_name Prims.list)
  (terms :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list)
  (acc : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  match (vars, terms) with
  | (v::vs, (FStar_Pervasives_Native.Some t)::ts) ->
      zip_bindings vs ts (sm_bind v t acc)
  | (uu___::vs, uu___1::ts) -> zip_bindings vs ts acc
  | (uu___, uu___1) -> acc
let eval_values (vars : var_name Prims.list)
  (rows :
    RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option Prims.list
      Prims.list)
  : RDF_Graph_Executable.solution_mapping Prims.list=
  FStar_List_Tot_Base.map (fun row -> zip_bindings vars row sm_empty) rows
let apply_comp_op (cmp : Prims.int) (op : comp_op) : Prims.bool=
  match op with
  | CmpEq -> cmp = Prims.int_zero
  | CmpNe -> cmp <> Prims.int_zero
  | CmpLt -> cmp < Prims.int_zero
  | CmpGt -> cmp > Prims.int_zero
  | CmpLe -> cmp <= Prims.int_zero
  | CmpGe -> cmp >= Prims.int_zero
let int_compare (a : Prims.int) (b : Prims.int) : Prims.int=
  if a < b
  then (Prims.of_int (-1))
  else if a = b then Prims.int_zero else Prims.int_one
let has_timezone (s : Prims.string) : Prims.bool=
  let len = FStar_String.strlen s in
  if len < Prims.int_one
  then false
  else
    if (FStar_String.sub s (len - Prims.int_one) Prims.int_one) = "Z"
    then true
    else
      if len >= (Prims.of_int (6))
      then
        (let suffix =
           FStar_String.sub s (len - (Prims.of_int (6))) (Prims.of_int (6)) in
         let c0 = FStar_String.sub suffix Prims.int_zero Prims.int_one in
         ((c0 = "+") || (c0 = "-")) &&
           ((FStar_String.sub suffix (Prims.of_int (3)) Prims.int_one) = ":"))
      else false
let date_part (s : Prims.string) : Prims.string=
  if (FStar_String.strlen s) >= (Prims.of_int (10))
  then FStar_String.sub s Prims.int_zero (Prims.of_int (10))
  else s
let value_compare (v1 : eval_result) (v2 : eval_result) (op : comp_op) :
  Prims.bool FStar_Pervasives_Native.option=
  match (v1, v2) with
  | (ER_Num a, ER_Num b) ->
      FStar_Pervasives_Native.Some (apply_comp_op (int_compare a b) op)
  | (ER_Bool a, ER_Bool b) ->
      let ia = if a then Prims.int_one else Prims.int_zero in
      let ib = if b then Prims.int_one else Prims.int_zero in
      FStar_Pervasives_Native.Some (apply_comp_op (int_compare ia ib) op)
  | (ER_Dec a, ER_Dec b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare a b) op)
  | (ER_Dbl a, ER_Dbl b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare a b) op)
  | (ER_Num a, ER_Dec b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare (Prims.string_of_int a) b) op)
  | (ER_Dec a, ER_Num b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare a (Prims.string_of_int b)) op)
  | (ER_Num a, ER_Dbl b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare (Prims.string_of_int a) b) op)
  | (ER_Dbl a, ER_Num b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare a (Prims.string_of_int b)) op)
  | (ER_Dec a, ER_Dbl b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare a b) op)
  | (ER_Dbl a, ER_Dec b) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op (FStar_String.compare a b) op)
  | (ER_Term (RDF_Graph_Executable.T_IRI i1), ER_Term
     (RDF_Graph_Executable.T_IRI i2)) ->
      FStar_Pervasives_Native.Some
        (apply_comp_op
           (FStar_String.compare (iri_to_string i1) (iri_to_string i2)) op)
  | (ER_Term (RDF_Graph_Executable.T_Literal l1), ER_Term
     (RDF_Graph_Executable.T_Literal l2)) ->
      if (lit_datatype l1) = (lit_datatype l2)
      then
        let dt = lit_datatype l1 in
        let is_known =
          ((((((((dt = RDF_Graph_Executable.xsd_string) ||
                   (dt =
                      "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"))
                  || (dt = RDF_Graph_Executable.xsd_integer))
                 || (dt = RDF_Graph_Executable.xsd_decimal))
                || (dt = RDF_Graph_Executable.xsd_double))
               || (dt = RDF_Graph_Executable.xsd_boolean))
              || (dt = "http://www.w3.org/2001/XMLSchema#float"))
             || (dt = "http://www.w3.org/2001/XMLSchema#date"))
            || (dt = "http://www.w3.org/2001/XMLSchema#dateTime") in
        (if is_known
         then
           let is_numeric_dt =
             (((dt = RDF_Graph_Executable.xsd_integer) ||
                 (dt = RDF_Graph_Executable.xsd_decimal))
                || (dt = RDF_Graph_Executable.xsd_double))
               || (dt = "http://www.w3.org/2001/XMLSchema#float") in
           (if is_numeric_dt
            then
              (if
                 ((lit_lexical l1) = (lit_lexical l2)) &&
                   ((lit_lang l1) = (lit_lang l2))
               then
                 match op with
                 | CmpEq -> FStar_Pervasives_Native.Some true
                 | CmpNe -> FStar_Pervasives_Native.Some false
                 | uu___ -> FStar_Pervasives_Native.None
               else FStar_Pervasives_Native.None)
            else
              (let lang_match =
                 match ((lit_lang l1), (lit_lang l2)) with
                 | (FStar_Pervasives_Native.Some t1,
                    FStar_Pervasives_Native.Some t2) ->
                     (string_lower t1) = (string_lower t2)
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> true
                 | (uu___1, uu___2) -> false in
               if lang_match
               then
                 (if dt = xsd_date
                  then
                    let s1 = lit_lexical l1 in
                    let s2 = lit_lexical l2 in
                    let tz1 = has_timezone s1 in
                    let tz2 = has_timezone s2 in
                    (if tz1 = tz2
                     then
                       FStar_Pervasives_Native.Some
                         (apply_comp_op (FStar_String.compare s1 s2) op)
                     else
                       (let dp1 = date_part s1 in
                        let dp2 = date_part s2 in
                        if dp1 = dp2
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            (apply_comp_op (FStar_String.compare dp1 dp2) op)))
                  else
                    FStar_Pervasives_Native.Some
                      (apply_comp_op
                         (FStar_String.compare (lit_lexical l1)
                            (lit_lexical l2)) op))
               else
                 (match op with
                  | CmpEq -> FStar_Pervasives_Native.Some false
                  | CmpNe -> FStar_Pervasives_Native.Some true
                  | uu___2 -> FStar_Pervasives_Native.None)))
         else
           if
             ((lit_lexical l1) = (lit_lexical l2)) &&
               ((lit_lang l1) = (lit_lang l2))
           then
             (match op with
              | CmpEq -> FStar_Pervasives_Native.Some true
              | CmpNe -> FStar_Pervasives_Native.Some false
              | uu___1 -> FStar_Pervasives_Native.None)
           else FStar_Pervasives_Native.None)
      else
        (let d1 = lit_datatype l1 in
         let d2 = lit_datatype l2 in
         if
           ((d1 = xsd_dateTime) && (d2 = xsd_date)) ||
             ((d1 = xsd_date) && (d2 = xsd_dateTime))
         then
           match op with
           | CmpEq -> FStar_Pervasives_Native.Some false
           | CmpNe -> FStar_Pervasives_Native.Some true
           | uu___1 -> FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.None)
  | (ER_Error, uu___) -> FStar_Pervasives_Native.None
  | (uu___, ER_Error) -> FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let fn_isIRI (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Graph_Executable.T_IRI uu___) -> ER_Bool true
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_isBlank (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Graph_Executable.T_BNode uu___) -> ER_Bool true
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_isLiteral (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Graph_Executable.T_Literal uu___) -> ER_Bool true
  | ER_Num uu___ -> ER_Bool true
  | ER_Dec uu___ -> ER_Bool true
  | ER_Dbl uu___ -> ER_Bool true
  | ER_Bool uu___ -> ER_Bool true
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_isNumeric (v : eval_result) : eval_result=
  match v with
  | ER_Num uu___ -> ER_Bool true
  | ER_Dec uu___ -> ER_Bool true
  | ER_Dbl uu___ -> ER_Bool true
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      ER_Bool (is_numeric_datatype (lit_datatype l))
  | ER_Error -> ER_Error
  | uu___ -> ER_Bool false
let fn_str (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Graph_Executable.T_IRI i) ->
      ER_Term
        (RDF_Graph_Executable.T_Literal (mk_plain_literal (iri_to_string i)))
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      ER_Term
        (RDF_Graph_Executable.T_Literal (mk_plain_literal (lit_lexical l)))
  | ER_Term (RDF_Graph_Executable.T_BNode b) ->
      ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal b))
  | ER_Num n ->
      ER_Term
        (RDF_Graph_Executable.T_Literal
           (mk_plain_literal (Prims.string_of_int n)))
  | ER_Dec s -> ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal s))
  | ER_Dbl s -> ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal s))
  | ER_Bool b ->
      ER_Term
        (RDF_Graph_Executable.T_Literal
           (mk_plain_literal (if b then "true" else "false")))
  | ER_Error -> ER_Error
let fn_lang (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      (match lit_lang l with
       | FStar_Pervasives_Native.Some tag ->
           ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal tag))
       | FStar_Pervasives_Native.None ->
           ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal "")))
  | ER_Num uu___ ->
      ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal ""))
  | ER_Dec uu___ ->
      ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal ""))
  | ER_Dbl uu___ ->
      ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal ""))
  | ER_Bool uu___ ->
      ER_Term (RDF_Graph_Executable.T_Literal (mk_plain_literal ""))
  | uu___ -> ER_Error
let fn_datatype (v : eval_result) : eval_result=
  match v with
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      ER_Term (RDF_Graph_Executable.T_IRI (lit_datatype l))
  | ER_Num uu___ ->
      ER_Term (RDF_Graph_Executable.T_IRI RDF_Graph_Executable.xsd_integer)
  | ER_Dec uu___ ->
      ER_Term (RDF_Graph_Executable.T_IRI RDF_Graph_Executable.xsd_decimal)
  | ER_Dbl uu___ ->
      ER_Term (RDF_Graph_Executable.T_IRI RDF_Graph_Executable.xsd_double)
  | ER_Bool uu___ ->
      ER_Term (RDF_Graph_Executable.T_IRI RDF_Graph_Executable.xsd_boolean)
  | uu___ -> ER_Error
let rec find_substring_pos_aux :
  'a .
    'a Prims.list ->
      'a Prims.list -> Prims.nat -> Prims.nat FStar_Pervasives_Native.option
  =
  fun needle haystack pos ->
    match haystack with
    | [] ->
        if Prims.uu___is_Nil needle
        then FStar_Pervasives_Native.Some pos
        else FStar_Pervasives_Native.None
    | uu___::rest ->
        if list_is_prefix needle haystack
        then FStar_Pervasives_Native.Some pos
        else find_substring_pos_aux needle rest (pos + Prims.int_one)
let find_substring_pos (needle : FStar_String.char Prims.list)
  (haystack : FStar_String.char Prims.list) :
  Prims.nat FStar_Pervasives_Native.option=
  find_substring_pos_aux needle haystack Prims.int_zero
let string_before (s : Prims.string) (arg : Prims.string) : Prims.string=
  if (FStar_String.strlen arg) = Prims.int_zero
  then ""
  else
    (let s_chars = FStar_String.list_of_string s in
     let arg_chars = FStar_String.list_of_string arg in
     match find_substring_pos arg_chars s_chars with
     | FStar_Pervasives_Native.None -> ""
     | FStar_Pervasives_Native.Some pos ->
         if pos = Prims.int_zero
         then ""
         else
           FStar_String.string_of_list
             (FStar_Pervasives_Native.fst
                (FStar_List_Tot_Base.splitAt pos s_chars)))
let string_after (s : Prims.string) (arg : Prims.string) : Prims.string=
  if (FStar_String.strlen arg) = Prims.int_zero
  then s
  else
    (let s_chars = FStar_String.list_of_string s in
     let arg_chars = FStar_String.list_of_string arg in
     let arg_len = FStar_List_Tot_Base.length arg_chars in
     match find_substring_pos arg_chars s_chars with
     | FStar_Pervasives_Native.None -> ""
     | FStar_Pervasives_Native.Some pos ->
         FStar_String.string_of_list
           (FStar_Pervasives_Native.snd
              (FStar_List_Tot_Base.splitAt (pos + arg_len) s_chars)))
let string_concat (args : Prims.string Prims.list) : Prims.string=
  FStar_String.concat "" args
let nibble_to_hex (n : Prims.nat) : FStar_Char.char=
  if n < (Prims.of_int (10))
  then FStar_Char.char_of_int (n + (Prims.of_int (48)))
  else
    FStar_Char.char_of_int ((n - (Prims.of_int (10))) + (Prims.of_int (65)))
let is_uri_unreserved (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((code >= (Prims.of_int (65))) && (code <= (Prims.of_int (90)))) ||
         ((code >= (Prims.of_int (97))) && (code <= (Prims.of_int (122)))))
        || ((code >= (Prims.of_int (48))) && (code <= (Prims.of_int (57)))))
       || (code = (Prims.of_int (45))))
      || (code = (Prims.of_int (95))))
     || (code = (Prims.of_int (46))))
    || (code = (Prims.of_int (126)))
let percent_encode_char (c : FStar_Char.char) : FStar_Char.char Prims.list=
  let code = FStar_Char.int_of_char c in
  if (code >= Prims.int_zero) && (code < (Prims.of_int (128)))
  then
    let hi = code / (Prims.of_int (16)) in
    let lo = (mod) code (Prims.of_int (16)) in
    [FStar_Char.char_of_int (Prims.of_int (37));
    nibble_to_hex hi;
    nibble_to_hex lo]
  else [c]
let rec encode_uri_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if is_uri_unreserved c
      then c :: (encode_uri_chars rest)
      else
        FStar_List_Tot_Base.op_At (percent_encode_char c)
          (encode_uri_chars rest)
let string_encode_uri (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (encode_uri_chars (FStar_String.list_of_string s))
let rec replace_first (haystack : FStar_Char.char Prims.list)
  (pattern : FStar_Char.char Prims.list)
  (replacement : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match haystack with
  | [] -> []
  | hd::tl ->
      if list_is_prefix pattern haystack
      then
        FStar_List_Tot_Base.op_At replacement
          (list_drop (FStar_List_Tot_Base.length pattern) haystack)
      else hd :: (replace_first tl pattern replacement)
let rec replace_all_chars_fuel (haystack : FStar_Char.char Prims.list)
  (pattern : FStar_Char.char Prims.list)
  (replacement : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  FStar_Char.char Prims.list=
  if fuel = Prims.int_zero
  then haystack
  else
    if list_contains_sublist pattern haystack
    then
      replace_all_chars_fuel (replace_first haystack pattern replacement)
        pattern replacement (fuel - Prims.int_one)
    else haystack
let replace_all_chars (haystack : FStar_Char.char Prims.list)
  (pattern : FStar_Char.char Prims.list)
  (replacement : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  if Prims.uu___is_Nil pattern
  then haystack
  else
    replace_all_chars_fuel haystack pattern replacement
      (FStar_List_Tot_Base.length haystack)
let string_replace (s : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (_flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  if (FStar_String.strlen pattern) = Prims.int_zero
  then s
  else
    FStar_String.string_of_list
      (replace_all_chars (FStar_String.list_of_string s)
         (FStar_String.list_of_string pattern)
         (FStar_String.list_of_string replacement))
let regex_match (text : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let re = if case_insensitive
      then Str.regexp_case_fold pattern
      else Str.regexp pattern in
    (try let _ = Str.search_forward re text 0 in true
     with Not_found -> false)
  with _ -> false
let fn_strlen_spec (s : Prims.string) : Prims.nat= string_length s
let fn_substr_spec (s : Prims.string) (start : Prims.nat)
  (len : Prims.nat FStar_Pervasives_Native.option) : Prims.string=
  let idx =
    if start > Prims.int_zero then start - Prims.int_one else Prims.int_zero in
  string_substring s idx len
let fn_ucase_spec (s : Prims.string) : Prims.string= string_upper s
let fn_lcase_spec (s : Prims.string) : Prims.string= string_lower s
let fn_strstarts_spec (s : Prims.string) (arg : Prims.string) : Prims.bool=
  string_starts_with s arg
let fn_strends_spec (s : Prims.string) (arg : Prims.string) : Prims.bool=
  string_ends_with s arg
let fn_strbefore_spec (s : Prims.string) (arg : Prims.string) : Prims.string=
  string_before s arg
let fn_strafter_spec (s : Prims.string) (arg : Prims.string) : Prims.string=
  string_after s arg
let fn_concat_spec (args : Prims.string Prims.list) : Prims.string=
  string_concat args
let fn_encode_for_uri_spec (s : Prims.string) : Prims.string=
  string_encode_uri s
let fn_strdt (lex : Prims.string) (dt : RDF_Graph_Executable.wf_iri) :
  RDF_Graph_Executable.rdf_term=
  if dt = RDF_Graph_Executable.rdf_lang_string
  then
    RDF_Graph_Executable.T_Literal
      {
        RDF_Graph_Executable.lexical_form = lex;
        RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string;
        RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
      }
  else
    RDF_Graph_Executable.T_Literal
      {
        RDF_Graph_Executable.lexical_form = lex;
        RDF_Graph_Executable.datatype = dt;
        RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
      }
let fn_strlang (lex : Prims.string) (lang : Prims.string) :
  RDF_Graph_Executable.rdf_term=
  RDF_Graph_Executable.T_Literal
    {
      RDF_Graph_Executable.lexical_form = lex;
      RDF_Graph_Executable.datatype = RDF_Graph_Executable.rdf_lang_string;
      RDF_Graph_Executable.lang_tag = (FStar_Pervasives_Native.Some lang)
    }
let same_term (t1 : RDF_Graph_Executable.rdf_term)
  (t2 : RDF_Graph_Executable.rdf_term) : Prims.bool=
  RDF_Graph_Executable.rdf_term_eq t1 t2
let fn_langMatches_spec (tag : Prims.string) (range : Prims.string) :
  Prims.bool=
  if range = "*"
  then (FStar_String.strlen tag) > Prims.int_zero
  else
    (let ltag = string_lower tag in
     let lrange = string_lower range in
     (ltag = lrange) || (string_starts_with ltag (Prims.strcat lrange "-")))
let hash_md5 (s : Prims.string) : Prims.string=
  Digestif.MD5.digest_string s |> Digestif.MD5.to_hex
let hash_sha1 (s : Prims.string) : Prims.string=
  Digestif.SHA1.digest_string s |> Digestif.SHA1.to_hex
let hash_sha256 (s : Prims.string) : Prims.string=
  Digestif.SHA256.digest_string s |> Digestif.SHA256.to_hex
let hash_sha384 (s : Prims.string) : Prims.string=
  Digestif.SHA384.digest_string s |> Digestif.SHA384.to_hex
let hash_sha512 (s : Prims.string) : Prims.string=
  Digestif.SHA512.digest_string s |> Digestif.SHA512.to_hex
let int_abs (n : Prims.int) : Prims.int=
  if n >= Prims.int_zero then n else Prims.int_zero - n
let fn_abs_spec (n : Prims.int) : Prims.int= int_abs n
let char_to_digit (c : FStar_Char.char) :
  Prims.int FStar_Pervasives_Native.option=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (n - (Prims.of_int (48)))
  else FStar_Pervasives_Native.None
let rec parse_int_chars (chars : FStar_Char.char Prims.list)
  (acc : Prims.int) : Prims.int FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      (match char_to_digit c with
       | FStar_Pervasives_Native.Some d ->
           parse_int_chars rest ((acc * (Prims.of_int (10))) + d)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let parse_int_string (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | [] -> FStar_Pervasives_Native.None
  | chars ->
      if
        (FStar_List_Tot_Base.hd chars) =
          (FStar_Char.char_of_int (Prims.of_int (45)))
      then
        (match parse_int_chars (FStar_List_Tot_Base.tl chars) Prims.int_zero
         with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (Prims.int_zero - n)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else parse_int_chars chars Prims.int_zero
let rec all_zeros (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::rest ->
      ((FStar_Char.int_of_char c) = (Prims.of_int (48))) && (all_zeros rest)
let rec list_take_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then x :: (list_take_while f xs) else []
let rec list_drop_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then list_drop_while f xs else x :: xs
let split_decimal (s : Prims.string) :
  (Prims.int FStar_Pervasives_Native.option * FStar_Char.char Prims.list *
    Prims.bool)=
  let chars = FStar_String.list_of_string s in
  let dot = FStar_Char.char_of_int (Prims.of_int (46)) in
  let before = list_take_while (fun c -> c <> dot) chars in
  let after_with_dot = list_drop_while (fun c -> c <> dot) chars in
  let has_dot = Prims.op_Negation (Prims.uu___is_Nil after_with_dot) in
  let frac = if has_dot then FStar_List_Tot_Base.tl after_with_dot else [] in
  let int_part = parse_int_string (FStar_String.string_of_list before) in
  (int_part, frac, has_dot)
let int_floor (s : Prims.string) : Prims.int=
  let uu___ = split_decimal s in
  match uu___ with
  | (int_part, frac, has_dot) ->
      (match int_part with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some n ->
           if (Prims.op_Negation has_dot) || (all_zeros frac)
           then n
           else if n >= Prims.int_zero then n else n - Prims.int_one)
let int_ceil (s : Prims.string) : Prims.int=
  let uu___ = split_decimal s in
  match uu___ with
  | (int_part, frac, has_dot) ->
      (match int_part with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some n ->
           if (Prims.op_Negation has_dot) || (all_zeros frac)
           then n
           else if n >= Prims.int_zero then n + Prims.int_one else n)
let int_round (s : Prims.string) : Prims.int=
  let uu___ = split_decimal s in
  match uu___ with
  | (int_part, frac, has_dot) ->
      (match int_part with
       | FStar_Pervasives_Native.None -> Prims.int_zero
       | FStar_Pervasives_Native.Some n ->
           if
             ((Prims.op_Negation has_dot) || (Prims.uu___is_Nil frac)) ||
               (all_zeros frac)
           then n
           else
             (let first_digit_code =
                FStar_Char.int_of_char (FStar_List_Tot_Base.hd frac) in
              if first_digit_code >= (Prims.of_int (53))
              then
                (if n >= Prims.int_zero
                 then n + Prims.int_one
                 else n - Prims.int_one)
              else n))
let dt_year (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (4))
  then FStar_Pervasives_Native.None
  else
    parse_int_string (FStar_String.sub s Prims.int_zero (Prims.of_int (4)))
let dt_month (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (7))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (5)) (Prims.of_int (2)))
let dt_day (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (10))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (8)) (Prims.of_int (2)))
let dt_hours (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (13))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (11)) (Prims.of_int (2)))
let dt_minutes (s : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (16))
  then FStar_Pervasives_Native.None
  else
    parse_int_string
      (FStar_String.sub s (Prims.of_int (14)) (Prims.of_int (2)))
let dt_seconds (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (let chars = FStar_String.list_of_string s in
     let after_17 = list_drop (Prims.of_int (17)) chars in
     let rec find_end cs count =
       match cs with
       | [] -> count
       | c::rest ->
           let ci = FStar_Char.int_of_char c in
           if
             ((ci = (Prims.of_int (90))) || (ci = (Prims.of_int (43)))) ||
               (ci = (Prims.of_int (45)))
           then count
           else find_end rest (count + Prims.int_one) in
     let sec_len = find_end after_17 Prims.int_zero in
     if sec_len = Prims.int_zero
     then FStar_Pervasives_Native.None
     else
       if ((Prims.of_int (17)) + sec_len) <= (FStar_String.strlen s)
       then
         FStar_Pervasives_Native.Some
           (FStar_String.sub s (Prims.of_int (17)) sec_len)
       else FStar_Pervasives_Native.None)
let dt_timezone (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (let last_char = FStar_String.index s (len - Prims.int_one) in
     if (FStar_Char.int_of_char last_char) = (Prims.of_int (90))
     then FStar_Pervasives_Native.Some "PT0S"
     else
       (let chars = FStar_String.list_of_string s in
        let rec find_tz cs pos =
          match cs with
          | [] -> FStar_Pervasives_Native.None
          | c::rest ->
              let ci = FStar_Char.int_of_char c in
              if
                (pos >= (Prims.of_int (19))) &&
                  ((ci = (Prims.of_int (43))) || (ci = (Prims.of_int (45))))
              then FStar_Pervasives_Native.Some pos
              else find_tz rest (pos + Prims.int_one) in
        match find_tz chars Prims.int_zero with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ""
        | FStar_Pervasives_Native.Some pos ->
            if len >= (pos + (Prims.of_int (6)))
            then
              let sign = FStar_String.index s pos in
              let sign_str =
                if (FStar_Char.int_of_char sign) = (Prims.of_int (45))
                then "-"
                else "" in
              let h_str =
                FStar_String.sub s (pos + Prims.int_one) (Prims.of_int (2)) in
              let m_str =
                FStar_String.sub s (pos + (Prims.of_int (4)))
                  (Prims.of_int (2)) in
              (match ((parse_int_string h_str), (parse_int_string m_str))
               with
               | (FStar_Pervasives_Native.Some h,
                  FStar_Pervasives_Native.Some m) ->
                   if m = Prims.int_zero
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat sign_str
                          (Prims.strcat "PT"
                             (Prims.strcat (Prims.string_of_int h) "H")))
                   else
                     FStar_Pervasives_Native.Some
                       (Prims.strcat sign_str
                          (Prims.strcat "PT"
                             (Prims.strcat (Prims.string_of_int h)
                                (Prims.strcat "H"
                                   (Prims.strcat (Prims.string_of_int m) "M")))))
               | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None))
let dt_tz (s : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (let last_char = FStar_String.index s (len - Prims.int_one) in
     if (FStar_Char.int_of_char last_char) = (Prims.of_int (90))
     then FStar_Pervasives_Native.Some "Z"
     else
       (let chars = FStar_String.list_of_string s in
        let rec find_tz_pos cs pos =
          match cs with
          | [] -> FStar_Pervasives_Native.None
          | c::rest ->
              let ci = FStar_Char.int_of_char c in
              if
                (pos >= (Prims.of_int (19))) &&
                  ((ci = (Prims.of_int (43))) || (ci = (Prims.of_int (45))))
              then FStar_Pervasives_Native.Some pos
              else find_tz_pos rest (pos + Prims.int_one) in
        match find_tz_pos chars Prims.int_zero with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ""
        | FStar_Pervasives_Native.Some pos ->
            if pos < len
            then
              FStar_Pervasives_Native.Some
                (FStar_String.sub s pos (len - pos))
            else FStar_Pervasives_Native.None))
let rec find_scheme_end (cs : FStar_String.char Prims.list) (pos : Prims.nat)
  : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | c1::c2::c3::rest ->
      if
        ((c1 = (FStar_Char.char_of_int (Prims.of_int (58)))) &&
           (c2 = (FStar_Char.char_of_int (Prims.of_int (47)))))
          && (c3 = (FStar_Char.char_of_int (Prims.of_int (47))))
      then FStar_Pervasives_Native.Some (pos + (Prims.of_int (3)))
      else find_scheme_end (c2 :: c3 :: rest) (pos + Prims.int_one)
  | uu___ -> FStar_Pervasives_Native.None
let rec find_slash_from (cs : FStar_String.char Prims.list) (pos : Prims.nat)
  (cur : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (cur >= pos) && (c = (FStar_Char.char_of_int (Prims.of_int (47))))
      then FStar_Pervasives_Native.Some cur
      else find_slash_from rest pos (cur + Prims.int_one)
let rec find_last_slash (cs : FStar_String.char Prims.list) (cur : Prims.nat)
  (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if c = (FStar_Char.char_of_int (Prims.of_int (47)))
      then
        find_last_slash rest (cur + Prims.int_one)
          (FStar_Pervasives_Native.Some cur)
      else find_last_slash rest (cur + Prims.int_one) last
let rec take_chars (n : Prims.nat) (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  if n = Prims.int_zero
  then []
  else
    (match cs with
     | [] -> []
     | c::rest -> c :: (take_chars (n - Prims.int_one) rest))
let rec remove_fragment (cs : FStar_String.char Prims.list)
  (last_hash : Prims.nat FStar_Pervasives_Native.option) (cur : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last_hash
  | c::rest ->
      if c = (FStar_Char.char_of_int (Prims.of_int (35)))
      then
        remove_fragment rest (FStar_Pervasives_Native.Some cur)
          (cur + Prims.int_one)
      else remove_fragment rest last_hash (cur + Prims.int_one)
let resolve_iri (base : RDF_Graph_Executable.wf_iri)
  (relative : Prims.string) : RDF_Graph_Executable.wf_iri=
  let base_chars = FStar_String.list_of_string base in
  let rel_chars = FStar_String.list_of_string relative in
  if string_contains relative "://"
  then base
  else
    if (FStar_String.strlen relative) = Prims.int_zero
    then base
    else
      (let result_chars =
         let first_char = FStar_List_Tot_Base.hd rel_chars in
         if first_char = (FStar_Char.char_of_int (Prims.of_int (35)))
         then
           match remove_fragment base_chars FStar_Pervasives_Native.None
                   Prims.int_zero
           with
           | FStar_Pervasives_Native.Some hash_pos ->
               FStar_List_Tot_Base.op_At (take_chars hash_pos base_chars)
                 rel_chars
           | FStar_Pervasives_Native.None ->
               FStar_List_Tot_Base.op_At base_chars rel_chars
         else
           if first_char = (FStar_Char.char_of_int (Prims.of_int (47)))
           then
             (match find_scheme_end base_chars Prims.int_zero with
              | FStar_Pervasives_Native.Some after_scheme ->
                  (match find_slash_from base_chars after_scheme
                           Prims.int_zero
                   with
                   | FStar_Pervasives_Native.Some auth_end ->
                       FStar_List_Tot_Base.op_At
                         (take_chars auth_end base_chars) rel_chars
                   | FStar_Pervasives_Native.None ->
                       FStar_List_Tot_Base.op_At base_chars rel_chars)
              | FStar_Pervasives_Native.None ->
                  FStar_List_Tot_Base.op_At base_chars rel_chars)
           else
             (match find_last_slash base_chars Prims.int_zero
                      FStar_Pervasives_Native.None
              with
              | FStar_Pervasives_Native.Some slash_pos ->
                  FStar_List_Tot_Base.op_At
                    (take_chars (slash_pos + Prims.int_one) base_chars)
                    rel_chars
              | FStar_Pervasives_Native.None ->
                  FStar_List_Tot_Base.op_At base_chars
                    (FStar_List_Tot_Base.op_At
                       [FStar_Char.char_of_int (Prims.of_int (47))] rel_chars)) in
       let result = FStar_String.string_of_list result_chars in
       if RDF_Graph_Executable.is_iri result then result else base)
let resolve_query_iri
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (rel : Prims.string) :
  RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option=
  match base with
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some (resolve_iri b rel)
  | FStar_Pervasives_Native.None -> string_to_iri rel
let rec unescape_chars (cs : FStar_String.char Prims.list) :
  FStar_String.char Prims.list=
  match cs with
  | [] -> []
  | c1::rest ->
      if c1 = (FStar_Char.char_of_int (Prims.of_int (92)))
      then
        (match rest with
         | [] -> [c1]
         | c2::rest' ->
             let code = FStar_Char.int_of_char c2 in
             if code = (Prims.of_int (92))
             then (FStar_Char.char_of_int (Prims.of_int (92))) ::
               (unescape_chars rest')
             else
               if code = (Prims.of_int (110))
               then (FStar_Char.char_of_int (Prims.of_int (10))) ::
                 (unescape_chars rest')
               else
                 if code = (Prims.of_int (114))
                 then (FStar_Char.char_of_int (Prims.of_int (13))) ::
                   (unescape_chars rest')
                 else
                   if code = (Prims.of_int (116))
                   then (FStar_Char.char_of_int (Prims.of_int (9))) ::
                     (unescape_chars rest')
                   else
                     if code = (Prims.of_int (34))
                     then (FStar_Char.char_of_int (Prims.of_int (34))) ::
                       (unescape_chars rest')
                     else
                       if code = (Prims.of_int (39))
                       then (FStar_Char.char_of_int (Prims.of_int (39))) ::
                         (unescape_chars rest')
                       else c1 :: c2 :: (unescape_chars rest'))
      else c1 :: (unescape_chars rest)
let unescape_sparql_string (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (unescape_chars (FStar_String.list_of_string s))
let fn_regex_spec (s : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  regex_match s (unescape_sparql_string pattern) flags
type solution_sequence = RDF_Graph_Executable.solution_mapping Prims.list
let subject_to_term (s : RDF_Graph_Executable.subject) :
  RDF_Graph_Executable.rdf_term=
  match s with
  | RDF_Graph_Executable.S_IRI i -> RDF_Graph_Executable.T_IRI i
  | RDF_Graph_Executable.S_BNode b -> RDF_Graph_Executable.T_BNode b
let try_bind_subject (ps : pattern_subject)
  (s : RDF_Graph_Executable.subject)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match ps with
  | PS_IRI i ->
      (match s with
       | RDF_Graph_Executable.S_IRI i' ->
           if i = i'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PS_BNode b ->
      (match s with
       | RDF_Graph_Executable.S_BNode b' ->
           if b = b'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PS_Var v ->
      let term = subject_to_term s in
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some existing ->
           if RDF_Graph_Executable.rdf_term_eq existing term
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (sm_bind v term mu))
let literal_eq_ci_lang (l1 : RDF_Graph_Executable.literal)
  (l2 : RDF_Graph_Executable.literal) : Prims.bool=
  ((l1.RDF_Graph_Executable.lexical_form =
      l2.RDF_Graph_Executable.lexical_form)
     && (l1.RDF_Graph_Executable.datatype = l2.RDF_Graph_Executable.datatype))
    &&
    (match ((l1.RDF_Graph_Executable.lang_tag),
             (l2.RDF_Graph_Executable.lang_tag))
     with
     | (FStar_Pervasives_Native.Some t1, FStar_Pervasives_Native.Some t2) ->
         (string_lower t1) = (string_lower t2)
     | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
     | (uu___, uu___1) -> false)
let try_bind_term (pt : pattern_term) (t : RDF_Graph_Executable.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match pt with
  | PT_IRI i ->
      (match t with
       | RDF_Graph_Executable.T_IRI i' ->
           if i = i'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_BNode b ->
      (match t with
       | RDF_Graph_Executable.T_BNode b' ->
           if b = b'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_Literal l ->
      (match t with
       | RDF_Graph_Executable.T_Literal l' ->
           if literal_eq_ci_lang l l'
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some existing ->
           if RDF_Graph_Executable.rdf_term_eq existing t
           then FStar_Pervasives_Native.Some mu
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (sm_bind v t mu))
let pattern_term_matches (pt : pattern_term)
  (t : RDF_Graph_Executable.rdf_term)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (try_bind_term pt t mu)
let pattern_subject_matches (ps : pattern_subject)
  (s : RDF_Graph_Executable.subject)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (try_bind_subject ps s mu)
let tp_match (tp : triple_pattern) (t : RDF_Graph_Executable.triple)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping FStar_Pervasives_Native.option=
  match try_bind_subject tp.tp_s t.RDF_Graph_Executable.s mu with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some mu1 ->
      (match try_bind_term tp.tp_p
               (RDF_Graph_Executable.T_IRI (t.RDF_Graph_Executable.p)) mu1
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some mu2 ->
           try_bind_term tp.tp_o t.RDF_Graph_Executable.o mu2)
let eval_single_tp (tp : triple_pattern) (g : RDF_Graph_Executable.rdf_graph)
  (mu : RDF_Graph_Executable.solution_mapping) : solution_sequence=
  list_filter_map (fun t -> tp_match tp t mu) g
let rec eval_bgp (patterns : bgp) (g : RDF_Graph_Executable.rdf_graph) :
  solution_sequence=
  match patterns with
  | [] -> [sm_empty]
  | tp::rest ->
      let sub_results = eval_bgp rest g in
      FStar_List_Tot_Base.concatMap (fun mu -> eval_single_tp tp g mu)
        sub_results
let join (omega1 : solution_sequence) (omega2 : solution_sequence) :
  solution_sequence=
  FStar_List_Tot_Base.concatMap
    (fun mu1 ->
       list_filter_map
         (fun mu2 ->
            if sm_compatible mu1 mu2
            then FStar_Pervasives_Native.Some (sm_merge mu1 mu2)
            else FStar_Pervasives_Native.None) omega2) omega1
let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =
  ref (fun _ _ -> failwith "eval_expr_ebv not yet wired")
let eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =
  ref (fun _ _ -> failwith "eval_expr_fwd not yet wired")
let eval_exists_fwd_ref : (group_graph_pattern -> RDF_Graph_Executable.solution_mapping -> RDF_Graph_Executable.rdf_graph -> Prims.bool) ref =
  ref (fun _ _ _ -> failwith "eval_exists_fwd not yet wired")
let eval_select_query_fwd_ref : (query -> RDF_Graph_Executable.rdf_graph -> solution_sequence) ref =
  ref (fun _ _ -> failwith "eval_select_query_fwd not yet wired")
let eval_expr_ebv (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  !eval_expr_ebv_ref e mu
let eval_expr_fwd (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  !eval_expr_fwd_ref e mu
let eval_exists_fwd (p : group_graph_pattern)
  (mu : RDF_Graph_Executable.solution_mapping)
  (g : RDF_Graph_Executable.rdf_graph) : Prims.bool=
  !eval_exists_fwd_ref p mu g
let eval_select_query_fwd (q : query)
  (g : RDF_Graph_Executable.rdf_graph) : solution_sequence=
  !eval_select_query_fwd_ref q g
let rec eval_filter_with_graph (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping)
  (g : RDF_Graph_Executable.rdf_graph) : eval_result=
  match e with
  | E_Exists sub_p -> ER_Bool (eval_exists_fwd sub_p mu g)
  | E_NotExists sub_p ->
      ER_Bool (Prims.op_Negation (eval_exists_fwd sub_p mu g))
  | E_And (e1, e2) ->
      ER_Bool
        ((ebv (eval_filter_with_graph e1 mu g)) &&
           (ebv (eval_filter_with_graph e2 mu g)))
  | E_Or (e1, e2) ->
      ER_Bool
        ((ebv (eval_filter_with_graph e1 mu g)) ||
           (ebv (eval_filter_with_graph e2 mu g)))
  | E_Not e1 ->
      ER_Bool (Prims.op_Negation (ebv (eval_filter_with_graph e1 mu g)))
  | uu___ -> eval_expr_fwd e mu
let left_join (omega1 : solution_sequence) (omega2 : solution_sequence)
  (filter_expr : expr) : solution_sequence=
  FStar_List_Tot_Base.concatMap
    (fun mu1 ->
       let joins =
         list_filter_map
           (fun mu2 ->
              if sm_compatible mu1 mu2
              then
                let merged = sm_merge mu1 mu2 in
                (if eval_expr_ebv filter_expr merged
                 then FStar_Pervasives_Native.Some merged
                 else FStar_Pervasives_Native.None)
              else FStar_Pervasives_Native.None) omega2 in
       if (FStar_List_Tot_Base.length joins) > Prims.int_zero
       then joins
       else [mu1]) omega1
let filter_solutions_fwd (e : expr) (omega : solution_sequence) :
  solution_sequence= FStar_List_Tot_Base.filter (eval_expr_ebv e) omega
let union (omega1 : solution_sequence) (omega2 : solution_sequence) :
  solution_sequence= FStar_List_Tot_Base.op_At omega1 omega2
let rec domains_disjoint (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  match mu1 with
  | [] -> true
  | (v, uu___)::rest ->
      (Prims.op_Negation
         (FStar_Pervasives_Native.uu___is_Some
            (FStar_List_Tot_Base.assoc v mu2)))
        && (domains_disjoint rest mu2)
let minus (omega1 : solution_sequence) (omega2 : solution_sequence) :
  solution_sequence=
  FStar_List_Tot_Base.filter
    (fun mu1 ->
       Prims.op_Negation
         (FStar_List_Tot_Base.existsb
            (fun mu2 ->
               (sm_compatible mu1 mu2) &&
                 (Prims.op_Negation (domains_disjoint mu1 mu2))) omega2))
    omega1
let rec eval_pattern (p : group_graph_pattern)
  (g : RDF_Graph_Executable.rdf_graph) : solution_sequence=
  match p with
  | GP_BGP bgp1 -> eval_bgp bgp1 g
  | GP_Join (p1, p2) -> join (eval_pattern p1 g) (eval_pattern p2 g)
  | GP_LeftJoin (p1, p2, filter_e) ->
      left_join (eval_pattern p1 g) (eval_pattern p2 g) filter_e
  | GP_Filter (e, p') ->
      let omega = eval_pattern p' g in
      FStar_List_Tot_Base.filter
        (fun mu -> ebv (eval_filter_with_graph e mu g)) omega
  | GP_Union (p1, p2) -> union (eval_pattern p1 g) (eval_pattern p2 g)
  | GP_Minus (p1, p2) -> minus (eval_pattern p1 g) (eval_pattern p2 g)
  | GP_Empty -> [sm_empty]
  | GP_Bind (e, v, p') ->
      let omega = eval_pattern p' g in
      FStar_List_Tot_Base.map
        (fun mu ->
           match er_to_term (eval_expr_fwd e mu) with
           | FStar_Pervasives_Native.Some t ->
               (match sm_lookup v mu with
                | FStar_Pervasives_Native.Some uu___ -> mu
                | FStar_Pervasives_Native.None -> sm_bind v t mu)
           | FStar_Pervasives_Native.None -> mu) omega
  | GP_Values (vars, rows) -> eval_values vars rows
  | GP_Graph (uu___, p') -> eval_pattern p' g
  | GP_Service (uu___, uu___1, uu___2) -> []
  | GP_SubSelect q -> eval_select_query_fwd q g
  | GP_PropertyPath (uu___, uu___1, uu___2) -> []
let rec eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result=
  match e with
  | E_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal l) ->
           if (lit_datatype l) = RDF_Graph_Executable.xsd_integer
           then
             (match parse_int_string (lit_lexical l) with
              | FStar_Pervasives_Native.Some n -> ER_Num n
              | FStar_Pervasives_Native.None ->
                  ER_Term (RDF_Graph_Executable.T_Literal l))
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_decimal
             then ER_Dec (lit_lexical l)
             else
               if
                 ((lit_datatype l) = RDF_Graph_Executable.xsd_double) ||
                   ((lit_datatype l) = xsd_float)
               then ER_Dbl (lit_lexical l)
               else
                 if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
                 then
                   ER_Bool
                     (((lit_lexical l) = "true") || ((lit_lexical l) = "1"))
                 else ER_Term (RDF_Graph_Executable.T_Literal l)
       | FStar_Pervasives_Native.Some t -> ER_Term t
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_IRI i -> ER_Term (RDF_Graph_Executable.T_IRI i)
  | E_Literal l -> ER_Term (RDF_Graph_Executable.T_Literal l)
  | E_BoolLit b -> ER_Bool b
  | E_NumericLit n -> ER_Num n
  | E_DecimalLit s -> ER_Dec s
  | E_DoubleLit s -> ER_Dbl s
  | E_Arith (op, e1, e2) ->
      (match ((eval_expr e1 mu), (eval_expr e2 mu)) with
       | (ER_Num a, ER_Num b) -> eval_arith_int op a b
       | (uu___, uu___1) -> ER_Error)
  | E_UnaryMinus e1 ->
      (match eval_expr e1 mu with
       | ER_Num n -> ER_Num (Prims.int_zero - n)
       | uu___ -> ER_Error)
  | E_UnaryPlus e1 -> eval_expr e1 mu
  | E_Compare (op, e1, e2) ->
      let v1 = eval_expr e1 mu in
      let v2 = eval_expr e2 mu in
      if (uu___is_ER_Error v1) || (uu___is_ER_Error v2)
      then ER_Error
      else
        (match value_compare v1 v2 op with
         | FStar_Pervasives_Native.Some b -> ER_Bool b
         | FStar_Pervasives_Native.None ->
             (match (v1, v2) with
              | (ER_Term (RDF_Graph_Executable.T_IRI i1), ER_Term
                 (RDF_Graph_Executable.T_IRI i2)) ->
                  (match op with
                   | CmpEq -> ER_Bool (i1 = i2)
                   | CmpNe -> ER_Bool (i1 <> i2)
                   | uu___1 -> ER_Error)
              | (ER_Term (RDF_Graph_Executable.T_BNode b1), ER_Term
                 (RDF_Graph_Executable.T_BNode b2)) ->
                  (match op with
                   | CmpEq -> ER_Bool (b1 = b2)
                   | CmpNe -> ER_Bool (b1 <> b2)
                   | uu___1 -> ER_Error)
              | (ER_Term (RDF_Graph_Executable.T_Literal l1), ER_Term
                 (RDF_Graph_Executable.T_Literal l2)) ->
                  if (lit_datatype l1) = (lit_datatype l2)
                  then
                    let dt = lit_datatype l1 in
                    let is_known_dt =
                      ((((((((dt = RDF_Graph_Executable.xsd_string) ||
                               (dt =
                                  "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"))
                              || (dt = RDF_Graph_Executable.xsd_integer))
                             || (dt = RDF_Graph_Executable.xsd_decimal))
                            || (dt = RDF_Graph_Executable.xsd_double))
                           || (dt = RDF_Graph_Executable.xsd_boolean))
                          || (dt = "http://www.w3.org/2001/XMLSchema#float"))
                         || (dt = "http://www.w3.org/2001/XMLSchema#date"))
                        || (dt = "http://www.w3.org/2001/XMLSchema#dateTime") in
                    (if is_known_dt
                     then
                       let is_numeric =
                         (((dt = RDF_Graph_Executable.xsd_integer) ||
                             (dt = RDF_Graph_Executable.xsd_decimal))
                            || (dt = RDF_Graph_Executable.xsd_double))
                           || (dt = "http://www.w3.org/2001/XMLSchema#float") in
                       (if is_numeric
                        then
                          (if
                             ((lit_lexical l1) = (lit_lexical l2)) &&
                               ((lit_lang l1) = (lit_lang l2))
                           then
                             match op with
                             | CmpEq -> ER_Bool true
                             | CmpNe -> ER_Bool false
                             | uu___1 -> ER_Error
                           else ER_Error)
                        else
                          if dt = xsd_date
                          then
                            (let s1 = lit_lexical l1 in
                             let s2 = lit_lexical l2 in
                             let tz1 = has_timezone s1 in
                             let tz2 = has_timezone s2 in
                             if tz1 = tz2
                             then
                               match op with
                               | CmpEq -> ER_Bool (s1 = s2)
                               | CmpNe -> ER_Bool (s1 <> s2)
                               | uu___2 -> ER_Error
                             else
                               (let dp1 = date_part s1 in
                                let dp2 = date_part s2 in
                                if dp1 = dp2
                                then ER_Error
                                else
                                  (match op with
                                   | CmpEq -> ER_Bool false
                                   | CmpNe -> ER_Bool true
                                   | uu___4 -> ER_Error)))
                          else
                            (match op with
                             | CmpEq ->
                                 ER_Bool
                                   (((lit_lexical l1) = (lit_lexical l2)) &&
                                      ((match ((lit_lang l1), (lit_lang l2))
                                        with
                                        | (FStar_Pervasives_Native.Some t1,
                                           FStar_Pervasives_Native.Some t2)
                                            ->
                                            (string_lower t1) =
                                              (string_lower t2)
                                        | (FStar_Pervasives_Native.None,
                                           FStar_Pervasives_Native.None) ->
                                            true
                                        | (uu___3, uu___4) -> false)))
                             | CmpNe ->
                                 ER_Bool
                                   (((lit_lexical l1) <> (lit_lexical l2)) ||
                                      ((match ((lit_lang l1), (lit_lang l2))
                                        with
                                        | (FStar_Pervasives_Native.Some t1,
                                           FStar_Pervasives_Native.Some t2)
                                            ->
                                            (string_lower t1) <>
                                              (string_lower t2)
                                        | (FStar_Pervasives_Native.None,
                                           FStar_Pervasives_Native.None) ->
                                            false
                                        | (uu___3, uu___4) -> true)))
                             | uu___3 -> ER_Error))
                     else
                       (match op with
                        | CmpEq ->
                            ER_Bool
                              (((lit_lexical l1) = (lit_lexical l2)) &&
                                 ((lit_lang l1) = (lit_lang l2)))
                        | CmpNe ->
                            if
                              ((lit_lexical l1) = (lit_lexical l2)) &&
                                ((lit_lang l1) = (lit_lang l2))
                            then ER_Bool false
                            else ER_Error
                        | uu___2 -> ER_Error))
                  else
                    (let dt1 = lit_datatype l1 in
                     let dt2 = lit_datatype l2 in
                     let rdf_langString1 =
                       "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString" in
                     if (dt1 = rdf_langString1) || (dt2 = rdf_langString1)
                     then
                       match op with
                       | CmpEq -> ER_Bool false
                       | CmpNe -> ER_Bool true
                       | uu___2 -> ER_Error
                     else
                       if
                         ((dt1 = xsd_dateTime) && (dt2 = xsd_date)) ||
                           ((dt1 = xsd_date) && (dt2 = xsd_dateTime))
                       then
                         (match op with
                          | CmpEq -> ER_Bool false
                          | CmpNe -> ER_Bool true
                          | uu___3 -> ER_Error)
                       else ER_Error)
              | (ER_Term uu___1, ER_Term uu___2) ->
                  (match op with
                   | CmpEq -> ER_Bool false
                   | CmpNe -> ER_Bool true
                   | uu___3 -> ER_Error)
              | (uu___1, uu___2) -> ER_Error))
  | E_And (e1, e2) ->
      ER_Bool ((ebv (eval_expr e1 mu)) && (ebv (eval_expr e2 mu)))
  | E_Or (e1, e2) ->
      ER_Bool ((ebv (eval_expr e1 mu)) || (ebv (eval_expr e2 mu)))
  | E_Not e1 -> ER_Bool (Prims.op_Negation (ebv (eval_expr e1 mu)))
  | E_IsIRI e1 -> fn_isIRI (eval_expr e1 mu)
  | E_IsBlank e1 -> fn_isBlank (eval_expr e1 mu)
  | E_IsLiteral e1 -> fn_isLiteral (eval_expr e1 mu)
  | E_IsNumeric e1 -> fn_isNumeric (eval_expr e1 mu)
  | E_Str e1 -> fn_str (eval_expr e1 mu)
  | E_Lang e1 -> fn_lang (eval_expr e1 mu)
  | E_Datatype e1 -> fn_datatype (eval_expr e1 mu)
  | E_IRI_fn e1 ->
      (match eval_expr e1 mu with
       | ER_Term (RDF_Graph_Executable.T_IRI i) ->
           ER_Term (RDF_Graph_Executable.T_IRI i)
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           (match string_to_iri (lit_lexical l) with
            | FStar_Pervasives_Native.Some i ->
                ER_Term (RDF_Graph_Executable.T_IRI i)
            | FStar_Pervasives_Native.None -> ER_Error)
       | uu___ -> ER_Error)
  | E_StrDt (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)), (eval_expr e2 mu)) with
       | (FStar_Pervasives_Native.Some s, ER_Term (RDF_Graph_Executable.T_IRI
          dt)) -> ER_Term (fn_strdt s dt)
       | (uu___, uu___1) -> ER_Error)
  | E_StrLang (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some lang)
           -> ER_Term (fn_strlang s lang)
       | (uu___, uu___1) -> ER_Error)
  | E_Bound v ->
      ER_Bool (FStar_Pervasives_Native.uu___is_Some (sm_lookup v mu))
  | E_If (cond, then_e, else_e) ->
      if ebv (eval_expr cond mu)
      then eval_expr then_e mu
      else eval_expr else_e mu
  | E_Coalesce es -> eval_coalesce es mu
  | E_In (ev, es) -> let v = eval_expr ev mu in eval_in v es mu
  | E_NotIn (ev, es) ->
      let v = eval_expr ev mu in
      (match eval_in v es mu with
       | ER_Bool b -> ER_Bool (Prims.op_Negation b)
       | other -> other)
  | E_StrLen e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> ER_Num (string_length s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Substr (e1, e2, e3_opt) ->
      (match ((er_to_string (eval_expr e1 mu)), (eval_expr e2 mu)) with
       | (FStar_Pervasives_Native.Some s, ER_Num start) ->
           if start < Prims.int_zero
           then ER_Error
           else
             (let len_opt =
                match e3_opt with
                | FStar_Pervasives_Native.Some e3 ->
                    (match eval_expr e3 mu with
                     | ER_Num n ->
                         if n >= Prims.int_zero
                         then FStar_Pervasives_Native.Some n
                         else FStar_Pervasives_Native.None
                     | uu___1 -> FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None in
              er_string (fn_substr_spec s start len_opt))
       | (uu___, uu___1) -> ER_Error)
  | E_UCase e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (string_upper s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_LCase e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (string_lower s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_StrStarts (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some
          prefix) -> ER_Bool (string_starts_with s prefix)
       | (uu___, uu___1) -> ER_Error)
  | E_StrEnds (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some
          suffix) -> ER_Bool (string_ends_with s suffix)
       | (uu___, uu___1) -> ER_Error)
  | E_Contains (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some sub)
           -> ER_Bool (string_contains s sub)
       | (uu___, uu___1) -> ER_Error)
  | E_StrBefore (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some arg)
           -> er_string (string_before s arg)
       | (uu___, uu___1) -> ER_Error)
  | E_StrAfter (e1, e2) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some arg)
           -> er_string (string_after s arg)
       | (uu___, uu___1) -> ER_Error)
  | E_Concat es -> eval_concat es mu
  | E_EncodeForUri e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (string_encode_uri s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Replace (e1, e2, e3, e4_opt) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)),
               (er_to_string (eval_expr e3 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some pat,
          FStar_Pervasives_Native.Some rep) ->
           let flags =
             match e4_opt with
             | FStar_Pervasives_Native.Some e4 ->
                 er_to_string (eval_expr e4 mu)
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
           er_string (string_replace s pat rep flags)
       | (uu___, uu___1, uu___2) -> ER_Error)
  | E_Regex (e1, e2, e3_opt) ->
      (match ((er_to_string (eval_expr e1 mu)),
               (er_to_string (eval_expr e2 mu)))
       with
       | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some pat)
           ->
           let flags =
             match e3_opt with
             | FStar_Pervasives_Native.Some e3 ->
                 er_to_string (eval_expr e3 mu)
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
           ER_Bool (fn_regex_spec s pat flags)
       | (uu___, uu___1) -> ER_Error)
  | E_Abs e1 ->
      (match eval_expr e1 mu with
       | ER_Num n -> ER_Num (int_abs n)
       | ER_Dec s ->
           if
             ((FStar_String.strlen s) > Prims.int_zero) &&
               ((FStar_String.sub s Prims.int_zero Prims.int_one) = "-")
           then
             ER_Dec
               (FStar_String.sub s Prims.int_one
                  ((FStar_String.strlen s) - Prims.int_one))
           else ER_Dec s
       | ER_Dbl s ->
           if
             ((FStar_String.strlen s) > Prims.int_zero) &&
               ((FStar_String.sub s Prims.int_zero Prims.int_one) = "-")
           then
             ER_Dbl
               (FStar_String.sub s Prims.int_one
                  ((FStar_String.strlen s) - Prims.int_one))
           else ER_Dbl s
       | uu___ -> ER_Error)
  | E_Round e1 ->
      (match eval_expr e1 mu with
       | ER_Num n -> ER_Num n
       | ER_Dec s -> ER_Num (int_round s)
       | uu___ -> ER_Error)
  | E_Ceil e1 ->
      (match eval_expr e1 mu with
       | ER_Num n -> ER_Num n
       | ER_Dec s -> ER_Num (int_ceil s)
       | uu___ -> ER_Error)
  | E_Floor e1 ->
      (match eval_expr e1 mu with
       | ER_Num n -> ER_Num n
       | ER_Dec s -> ER_Num (int_floor s)
       | uu___ -> ER_Error)
  | E_MD5 e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_md5 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA1 e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha1 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA256 e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha256 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA384 e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha384 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SHA512 e1 ->
      (match er_to_string (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s -> er_string (hash_sha512 s)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Now -> ER_Error
  | E_Year e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_year s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Month e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_month s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Day e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_day s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Hours e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_hours s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Minutes e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_minutes s with
            | FStar_Pervasives_Native.Some n -> ER_Num n
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Seconds e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_seconds s with
            | FStar_Pervasives_Native.Some ds -> ER_Dec ds
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Timezone e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_timezone s with
            | FStar_Pervasives_Native.Some tz -> er_string tz
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_Tz e1 ->
      (match er_to_datetime_lex (eval_expr e1 mu) with
       | FStar_Pervasives_Native.Some s ->
           (match dt_tz s with
            | FStar_Pervasives_Native.Some tz -> er_string tz
            | FStar_Pervasives_Native.None -> ER_Error)
       | FStar_Pervasives_Native.None -> ER_Error)
  | E_SameTerm (e1, e2) ->
      (match ((eval_expr e1 mu), (eval_expr e2 mu)) with
       | (ER_Term t1, ER_Term t2) -> ER_Bool (same_term t1 t2)
       | (uu___, uu___1) -> ER_Error)
  | E_Exists uu___ -> ER_Error
  | E_NotExists uu___ -> ER_Error
  | E_Aggregate (uu___, uu___1, uu___2) -> ER_Error
  | E_FunctionCall (iri, args) ->
      if iri = "sparql:langMatches"
      then
        (match args with
         | e1::e2::[] ->
             let r1 = eval_expr e1 mu in
             let r2 = eval_expr e2 mu in
             let get_str r =
               match r with
               | ER_Term (RDF_Graph_Executable.T_Literal l) ->
                   FStar_Pervasives_Native.Some (lit_lexical l)
               | uu___ -> FStar_Pervasives_Native.None in
             (match ((get_str r1), (get_str r2)) with
              | (FStar_Pervasives_Native.Some s1,
                 FStar_Pervasives_Native.Some s2) ->
                  let tag = FStar_String.lowercase s1 in
                  let range = FStar_String.lowercase s2 in
                  if range = "*"
                  then ER_Bool ((FStar_String.strlen tag) > Prims.int_zero)
                  else ER_Bool (string_starts_with tag range)
              | (uu___, uu___1) -> ER_Error)
         | uu___ -> ER_Error)
      else ER_Error
and eval_coalesce (es : expr Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match es with
  | [] -> ER_Error
  | e::rest ->
      (match eval_expr e mu with | ER_Error -> eval_coalesce rest mu | v -> v)
and eval_in (v : eval_result) (es : expr Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match es with
  | [] -> ER_Bool false
  | e::rest ->
      (match value_compare v (eval_expr e mu) CmpEq with
       | FStar_Pervasives_Native.Some true -> ER_Bool true
       | uu___ -> eval_in v rest mu)
and eval_concat (es : expr Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match es with
  | [] -> er_string ""
  | e::rest ->
      (match ((er_to_string (eval_expr e mu)), (eval_concat rest mu)) with
       | (FStar_Pervasives_Native.Some s, ER_Term
          (RDF_Graph_Executable.T_Literal l)) ->
           er_string (Prims.strcat s (lit_lexical l))
       | (uu___, uu___1) -> ER_Error)
let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)
type group = {
  g_key: eval_result Prims.list ;
  g_solutions: solution_sequence }
let __proj__Mkgroup__item__g_key (projectee : group) :
  eval_result Prims.list=
  match projectee with | { g_key; g_solutions;_} -> g_key
let __proj__Mkgroup__item__g_solutions (projectee : group) :
  solution_sequence=
  match projectee with | { g_key; g_solutions;_} -> g_solutions
let eval_group_condition (gc : group_condition)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match gc with
  | GC_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some t -> ER_Term t
       | FStar_Pervasives_Native.None -> ER_Error)
  | GC_Expr (e, uu___) -> eval_expr e mu
  | GC_BuiltIn e -> eval_expr e mu
let eval_group_key (conds : group_condition Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result Prims.list=
  FStar_List_Tot_Base.map (fun gc -> eval_group_condition gc mu) conds
let er_rank (v : eval_result) : Prims.int=
  match v with
  | ER_Error -> Prims.int_zero
  | ER_Term (RDF_Graph_Executable.T_BNode uu___) -> Prims.int_one
  | ER_Term (RDF_Graph_Executable.T_IRI uu___) -> (Prims.of_int (2))
  | ER_Bool uu___ -> (Prims.of_int (3))
  | ER_Num uu___ -> (Prims.of_int (4))
  | ER_Dec uu___ -> (Prims.of_int (5))
  | ER_Dbl uu___ -> (Prims.of_int (6))
  | ER_Term (RDF_Graph_Executable.T_Literal uu___) -> (Prims.of_int (7))
let sparql_order (a : eval_result) (b : eval_result) : Prims.int=
  let ra = er_rank a in
  let rb = er_rank b in
  if ra < rb
  then (Prims.of_int (-1))
  else
    if ra > rb
    then Prims.int_one
    else
      (match (a, b) with
       | (ER_Error, ER_Error) -> Prims.int_zero
       | (ER_Term (RDF_Graph_Executable.T_BNode x), ER_Term
          (RDF_Graph_Executable.T_BNode y)) -> FStar_String.compare x y
       | (ER_Term (RDF_Graph_Executable.T_IRI x), ER_Term
          (RDF_Graph_Executable.T_IRI y)) ->
           FStar_String.compare (iri_to_string x) (iri_to_string y)
       | (ER_Bool x, ER_Bool y) ->
           int_compare (if x then Prims.int_one else Prims.int_zero)
             (if y then Prims.int_one else Prims.int_zero)
       | (ER_Num x, ER_Num y) -> int_compare x y
       | (ER_Dec x, ER_Dec y) -> FStar_String.compare x y
       | (ER_Dbl x, ER_Dbl y) -> FStar_String.compare x y
       | (ER_Term (RDF_Graph_Executable.T_Literal l1), ER_Term
          (RDF_Graph_Executable.T_Literal l2)) ->
           let dc = FStar_String.compare (lit_datatype l1) (lit_datatype l2) in
           if dc <> Prims.int_zero
           then dc
           else
             (let lc = FStar_String.compare (lit_lexical l1) (lit_lexical l2) in
              if lc <> Prims.int_zero
              then lc
              else
                (match ((lit_lang l1), (lit_lang l2)) with
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> Prims.int_zero
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.Some uu___4) ->
                     (Prims.of_int (-1))
                 | (FStar_Pervasives_Native.Some uu___4,
                    FStar_Pervasives_Native.None) -> Prims.int_one
                 | (FStar_Pervasives_Native.Some t1,
                    FStar_Pervasives_Native.Some t2) ->
                     FStar_String.compare t1 t2))
       | (uu___2, uu___3) -> Prims.int_zero)
let er_equal (a : eval_result) (b : eval_result) : Prims.bool=
  (sparql_order a b) = Prims.int_zero
let rec keys_equal (k1 : eval_result Prims.list)
  (k2 : eval_result Prims.list) : Prims.bool=
  match (k1, k2) with
  | ([], []) -> true
  | (a::rest1, b::rest2) -> (er_equal a b) && (keys_equal rest1 rest2)
  | (uu___, uu___1) -> false
let rec find_group (key : eval_result Prims.list) (groups : group Prims.list)
  :
  (group Prims.list * group * group Prims.list)
    FStar_Pervasives_Native.option=
  match groups with
  | [] -> FStar_Pervasives_Native.None
  | g::rest ->
      if keys_equal key g.g_key
      then FStar_Pervasives_Native.Some ([], g, rest)
      else
        (match find_group key rest with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (before, found, after) ->
             FStar_Pervasives_Native.Some ((g :: before), found, after))
let add_to_groups (key : eval_result Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) (groups : group Prims.list) :
  group Prims.list=
  match find_group key groups with
  | FStar_Pervasives_Native.Some (before, g, after) ->
      FStar_List_Tot_Base.op_At before
        (FStar_List_Tot_Base.op_At
           [{
              g_key = (g.g_key);
              g_solutions = (FStar_List_Tot_Base.op_At g.g_solutions [mu])
            }] after)
  | FStar_Pervasives_Native.None ->
      FStar_List_Tot_Base.op_At groups [{ g_key = key; g_solutions = [mu] }]
let group_by (conds : group_condition Prims.list) (omega : solution_sequence)
  : group Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun groups mu ->
       let key = eval_group_key conds mu in add_to_groups key mu groups) []
    omega
let implicit_group (omega : solution_sequence) : group Prims.list=
  [{ g_key = []; g_solutions = omega }]
let eval_over_group (e : expr) (g : group) : eval_result Prims.list=
  FStar_List_Tot_Base.map (fun mu -> eval_expr e mu) g.g_solutions
let filter_non_error (vals : eval_result Prims.list) :
  eval_result Prims.list=
  FStar_List_Tot_Base.filter
    (fun v -> Prims.op_Negation (uu___is_ER_Error v)) vals
let rec dedup_er (vals : eval_result Prims.list) : eval_result Prims.list=
  match vals with
  | [] -> []
  | v::rest ->
      if FStar_List_Tot_Base.existsb (fun x -> er_equal v x) rest
      then dedup_er rest
      else v :: (dedup_er rest)
let rec sum_nums (vals : eval_result Prims.list) : Prims.int=
  match vals with
  | [] -> Prims.int_zero
  | (ER_Num n)::rest -> n + (sum_nums rest)
  | uu___::rest -> sum_nums rest
let rec count_nums (vals : eval_result Prims.list) : Prims.int=
  match vals with
  | [] -> Prims.int_zero
  | (ER_Num uu___)::rest -> Prims.int_one + (count_nums rest)
  | uu___::rest -> count_nums rest
let rec find_min (vals : eval_result Prims.list) : eval_result=
  match vals with
  | [] -> ER_Error
  | v::[] -> v
  | v::rest ->
      let m = find_min rest in
      if (sparql_order v m) <= Prims.int_zero then v else m
let rec find_max (vals : eval_result Prims.list) : eval_result=
  match vals with
  | [] -> ER_Error
  | v::[] -> v
  | v::rest ->
      let m = find_max rest in
      if (sparql_order v m) >= Prims.int_zero then v else m
let rec collect_strings (vals : eval_result Prims.list) :
  Prims.string Prims.list=
  match vals with
  | [] -> []
  | v::rest ->
      (match er_to_string v with
       | FStar_Pervasives_Native.Some s -> s :: (collect_strings rest)
       | FStar_Pervasives_Native.None -> collect_strings rest)
let rec first_non_error (vals : eval_result Prims.list) : eval_result=
  match vals with
  | [] -> ER_Error
  | v::rest -> if uu___is_ER_Error v then first_non_error rest else v
let eval_aggregate (fn : aggregate_fn) (distinct : Prims.bool) (e : expr)
  (g : group) : eval_result=
  match fn with
  | Agg_Count ->
      (match e with
       | E_Var "*" -> ER_Num (FStar_List_Tot_Base.length g.g_solutions)
       | uu___ ->
           let vals = filter_non_error (eval_over_group e g) in
           let vals1 = if distinct then dedup_er vals else vals in
           ER_Num (FStar_List_Tot_Base.length vals1))
  | Agg_Sum ->
      let vals = filter_non_error (eval_over_group e g) in
      let vals1 = if distinct then dedup_er vals else vals in
      ER_Num (sum_nums vals1)
  | Agg_Avg ->
      let vals = filter_non_error (eval_over_group e g) in
      let vals1 = if distinct then dedup_er vals else vals in
      let s = sum_nums vals1 in
      let c = count_nums vals1 in
      if c > Prims.int_zero
      then
        ER_Dec
          (Prims.strcat (Prims.string_of_int (s / c))
             (Prims.strcat "."
                (Prims.string_of_int
                   (int_abs
                      (((s - ((s / c) * c)) * (Prims.of_int (1000))) / c)))))
      else ER_Num Prims.int_zero
  | Agg_Min ->
      let vals = filter_non_error (eval_over_group e g) in
      let vals1 = if distinct then dedup_er vals else vals in find_min vals1
  | Agg_Max ->
      let vals = filter_non_error (eval_over_group e g) in
      let vals1 = if distinct then dedup_er vals else vals in find_max vals1
  | Agg_GroupConcat sep_opt ->
      let vals = filter_non_error (eval_over_group e g) in
      let vals1 = if distinct then dedup_er vals else vals in
      let sep =
        match sep_opt with
        | FStar_Pervasives_Native.Some s -> s
        | FStar_Pervasives_Native.None -> " " in
      let strs = collect_strings vals1 in
      ER_Term
        (RDF_Graph_Executable.T_Literal
           (mk_plain_literal (FStar_String.concat sep strs)))
  | Agg_Sample -> let vals = eval_over_group e g in first_non_error vals
let rec eval_expr_group (e : expr) (grp : group)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  match e with
  | E_Aggregate (fn, distinct, inner_e) ->
      eval_aggregate fn distinct inner_e grp
  | E_Arith (op, e1, e2) ->
      let r1 = eval_expr_group e1 grp mu in
      let r2 = eval_expr_group e2 grp mu in
      (match (r1, r2) with
       | (ER_Num a, ER_Num b) -> eval_arith_int op a b
       | (uu___, uu___1) -> ER_Error)
  | E_And (e1, e2) ->
      ER_Bool
        ((ebv (eval_expr_group e1 grp mu)) &&
           (ebv (eval_expr_group e2 grp mu)))
  | E_Or (e1, e2) ->
      ER_Bool
        ((ebv (eval_expr_group e1 grp mu)) ||
           (ebv (eval_expr_group e2 grp mu)))
  | E_Not e1 -> ER_Bool (Prims.op_Negation (ebv (eval_expr_group e1 grp mu)))
  | E_Compare (op, e1, e2) ->
      (match value_compare (eval_expr_group e1 grp mu)
               (eval_expr_group e2 grp mu) op
       with
       | FStar_Pervasives_Native.Some b -> ER_Bool b
       | FStar_Pervasives_Native.None ->
           (match op with
            | CmpEq -> ER_Bool false
            | CmpNe -> ER_Bool true
            | uu___ -> ER_Error))
  | uu___ -> eval_expr e mu
let having_filter (conditions : having_condition Prims.list)
  (groups : group Prims.list) : group Prims.list=
  FStar_List_Tot_Base.filter
    (fun g ->
       let mu = match g.g_solutions with | m::uu___ -> m | [] -> sm_empty in
       FStar_List_Tot_Base.for_all
         (fun cond -> ebv (eval_expr_group cond g mu)) conditions) groups
let compare_on_condition (c : order_condition)
  (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.int=
  match c with
  | OC_Asc e -> sparql_order (eval_expr e mu1) (eval_expr e mu2)
  | OC_Desc e -> sparql_order (eval_expr e mu2) (eval_expr e mu1)
let rec compare_on_conditions (conds : order_condition Prims.list)
  (mu1 : RDF_Graph_Executable.solution_mapping)
  (mu2 : RDF_Graph_Executable.solution_mapping) : Prims.int=
  match conds with
  | [] -> Prims.int_zero
  | c::rest ->
      let r = compare_on_condition c mu1 mu2 in
      if r <> Prims.int_zero then r else compare_on_conditions rest mu1 mu2
let sort_solutions (conds : order_condition Prims.list)
  (omega : solution_sequence) : solution_sequence=
  FStar_List_Tot_Base.sortWith (compare_on_conditions conds) omega
let rec sm_equal (m1 : RDF_Graph_Executable.solution_mapping)
  (m2 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  match (m1, m2) with
  | ([], []) -> true
  | ((v1, t1)::r1, (v2, t2)::r2) ->
      ((v1 = v2) && (RDF_Graph_Executable.rdf_term_eq t1 t2)) &&
        (sm_equal r1 r2)
  | (uu___, uu___1) -> false
let rec sm_mem (mu : RDF_Graph_Executable.solution_mapping)
  (l : RDF_Graph_Executable.solution_mapping Prims.list) : Prims.bool=
  match l with | [] -> false | hd::tl -> (sm_equal mu hd) || (sm_mem mu tl)
let rec list_deduplicate_sm
  (l : RDF_Graph_Executable.solution_mapping Prims.list) :
  RDF_Graph_Executable.solution_mapping Prims.list=
  match l with
  | [] -> []
  | x::xs ->
      if sm_mem x xs
      then list_deduplicate_sm xs
      else x :: (list_deduplicate_sm xs)
let distinct_solutions (omega : solution_sequence) : solution_sequence=
  list_deduplicate_sm omega
let reduced_solutions (omega : solution_sequence) : solution_sequence= omega
let slice_solutions (offset : Prims.nat FStar_Pervasives_Native.option)
  (limit : Prims.nat FStar_Pervasives_Native.option)
  (omega : solution_sequence) : solution_sequence=
  let after_offset =
    match offset with
    | FStar_Pervasives_Native.None -> omega
    | FStar_Pervasives_Native.Some n -> list_drop n omega in
  match limit with
  | FStar_Pervasives_Native.None -> after_offset
  | FStar_Pervasives_Native.Some n -> list_take n after_offset
let rec project (vars : var_name Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) :
  RDF_Graph_Executable.solution_mapping=
  match mu with
  | [] -> []
  | (v, t)::rest ->
      if FStar_List_Tot_Base.mem v vars
      then (v, t) :: (project vars rest)
      else project vars rest
let project_solutions (vars : var_name Prims.list)
  (omega : solution_sequence) : solution_sequence=
  FStar_List_Tot_Base.map (project vars) omega
let eval_select_item (item : select_item)
  (mu : RDF_Graph_Executable.solution_mapping)
  (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.solution_mapping=
  match item with
  | SI_Var uu___ -> mu
  | SI_Expr (e, v) ->
      let r = eval_expr e mu in
      (match er_to_term r with
       | FStar_Pervasives_Native.Some t -> sm_bind v t mu
       | FStar_Pervasives_Native.None -> mu)
let eval_select_items (items : select_item Prims.list)
  (omega : solution_sequence) (g : RDF_Graph_Executable.rdf_graph) :
  solution_sequence=
  FStar_List_Tot_Base.map
    (fun mu ->
       FStar_List_Tot_Base.fold_left
         (fun acc item -> eval_select_item item acc g) mu items) omega
let rec expr_has_aggregate (e : expr) : Prims.bool=
  match e with
  | E_Aggregate (uu___, uu___1, uu___2) -> true
  | E_Arith (uu___, e1, e2) ->
      (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_Compare (uu___, e1, e2) ->
      (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_And (e1, e2) -> (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_Or (e1, e2) -> (expr_has_aggregate e1) || (expr_has_aggregate e2)
  | E_Not e1 -> expr_has_aggregate e1
  | uu___ -> false
let select_has_aggregates (items : select_item Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun item ->
       match item with
       | SI_Expr (e, uu___) -> expr_has_aggregate e
       | SI_Var uu___ -> false) items
let eval_group_select (items : select_item Prims.list)
  (conds : group_condition Prims.list FStar_Pervasives_Native.option)
  (grp : group) : RDF_Graph_Executable.solution_mapping=
  let base_mu = match grp.g_solutions with | mu::uu___ -> mu | [] -> sm_empty in
  let base_mu1 =
    match conds with
    | FStar_Pervasives_Native.None -> base_mu
    | FStar_Pervasives_Native.Some gc_list ->
        FStar_List_Tot_Base.fold_left
          (fun mu gc ->
             match gc with
             | GC_Expr (e, FStar_Pervasives_Native.Some v) ->
                 let r = eval_expr e mu in
                 (match er_to_term r with
                  | FStar_Pervasives_Native.Some t -> sm_bind v t mu
                  | FStar_Pervasives_Native.None -> mu)
             | uu___ -> mu) base_mu gc_list in
  FStar_List_Tot_Base.fold_left
    (fun mu item ->
       match item with
       | SI_Var v -> mu
       | SI_Expr (e, v) ->
           let r = eval_expr_group e grp mu in
           (match er_to_term r with
            | FStar_Pervasives_Native.Some t -> sm_bind v t mu
            | FStar_Pervasives_Native.None -> mu)) base_mu1 items
let eval_aggregate_query (items : select_item Prims.list)
  (conds : group_condition Prims.list FStar_Pervasives_Native.option)
  (groups : group Prims.list) : solution_sequence=
  FStar_List_Tot_Base.map (fun grp -> eval_group_select items conds grp)
    groups
let select_item_vars (items : select_item Prims.list) : var_name Prims.list=
  FStar_List_Tot_Base.map
    (fun item -> match item with | SI_Var v -> v | SI_Expr (uu___, v) -> v)
    items
let eval_select_query (q : query) (g : RDF_Graph_Executable.rdf_graph) :
  solution_sequence=
  match q.q_form with
  | QF_Select sel ->
      let omega = eval_pattern q.q_pattern g in
      let omega' =
        match sel with
        | Select_Vars items ->
            if
              (select_has_aggregates items) ||
                (FStar_Pervasives_Native.uu___is_Some q.q_group_by)
            then
              let groups =
                match q.q_group_by with
                | FStar_Pervasives_Native.None -> implicit_group omega
                | FStar_Pervasives_Native.Some gc -> group_by gc omega in
              let groups1 =
                match q.q_having with
                | FStar_Pervasives_Native.None -> groups
                | FStar_Pervasives_Native.Some conds ->
                    having_filter conds groups in
              eval_aggregate_query items q.q_group_by groups1
            else eval_select_items items omega g
        | Select_All -> omega in
      let ordered =
        match (q.q_modifier).sm_order_by with
        | FStar_Pervasives_Native.None -> omega'
        | FStar_Pervasives_Native.Some o -> sort_solutions o omega' in
      let projected =
        match sel with
        | Select_Vars items ->
            project_solutions (select_item_vars items) ordered
        | Select_All -> ordered in
      let deduped =
        if (q.q_modifier).sm_distinct
        then distinct_solutions projected
        else
          if (q.q_modifier).sm_reduced
          then reduced_solutions projected
          else projected in
      slice_solutions (q.q_modifier).sm_offset (q.q_modifier).sm_limit
        deduped
  | QF_Construct uu___ -> []
  | QF_Ask -> []
  | QF_Describe uu___ -> []
type path_result =
  (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list
let () = eval_select_query_fwd_ref := (fun q g -> eval_select_query q g)
let is_not_literal (t : RDF_Graph_Executable.rdf_term) : Prims.bool=
  match t with
  | RDF_Graph_Executable.T_Literal uu___ -> false
  | uu___ -> true
let path_pair_eq
  (p1 : (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term))
  (p2 : (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term)) :
  Prims.bool=
  let uu___ = p1 in
  match uu___ with
  | (a1, b1) ->
      let uu___1 = p2 in
      (match uu___1 with
       | (a2, b2) ->
           (RDF_Graph_Executable.rdf_term_eq a1 a2) &&
             (RDF_Graph_Executable.rdf_term_eq b1 b2))
let rec list_dedup_by :
  'a . ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun eq l ->
    match l with
    | [] -> []
    | x::xs ->
        if FStar_List_Tot_Base.existsb (eq x) xs
        then list_dedup_by eq xs
        else x :: (list_dedup_by eq xs)
let dedup_path (pairs : path_result) : path_result=
  list_dedup_by path_pair_eq pairs
let rec negated_iris (ps : property_path Prims.list) :
  RDF_Graph_Executable.wf_iri Prims.list=
  match ps with
  | [] -> []
  | (PP_IRI i)::rest -> i :: (negated_iris rest)
  | (PP_Inverse (PP_IRI i))::rest -> i :: (negated_iris rest)
  | uu___::rest -> negated_iris rest
let rec iri_in_list (iri : RDF_Graph_Executable.wf_iri)
  (iris : RDF_Graph_Executable.wf_iri Prims.list) : Prims.bool=
  match iris with
  | [] -> false
  | hd::tl -> if hd = iri then true else iri_in_list iri tl
let graph_nodes (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.rdf_term Prims.list=
  let subj_nodes =
    FStar_List_Tot_Base.map
      (fun t -> subject_to_term t.RDF_Graph_Executable.s) g in
  let obj_nodes =
    FStar_List_Tot_Base.map (fun t -> t.RDF_Graph_Executable.o) g in
  let pairs =
    dedup_path
      (FStar_List_Tot_Base.map (fun n -> (n, n))
         (FStar_List_Tot_Base.op_At subj_nodes obj_nodes)) in
  FStar_List_Tot_Base.map FStar_Pervasives_Native.fst pairs
let rec eval_property_path (p : property_path)
  (g : RDF_Graph_Executable.rdf_graph) : path_result=
  match p with
  | PP_IRI iri ->
      FStar_List_Tot_Base.concatMap
        (fun t ->
           if t.RDF_Graph_Executable.p = iri
           then
             [((subject_to_term t.RDF_Graph_Executable.s),
                (t.RDF_Graph_Executable.o))]
           else []) g
  | PP_Inverse pp ->
      let pairs = eval_property_path pp g in
      FStar_List_Tot_Base.concatMap
        (fun pair ->
           let uu___ = pair in
           match uu___ with
           | (s, o) -> if is_not_literal o then [(o, s)] else []) pairs
  | PP_Sequence (p1, p2) ->
      let r1 = eval_property_path p1 g in
      let r2 = eval_property_path p2 g in
      dedup_path
        (FStar_List_Tot_Base.concatMap
           (fun pair1 ->
              let uu___ = pair1 in
              match uu___ with
              | (s, mid1) ->
                  FStar_List_Tot_Base.concatMap
                    (fun pair2 ->
                       let uu___1 = pair2 in
                       match uu___1 with
                       | (mid2, o) ->
                           if RDF_Graph_Executable.rdf_term_eq mid1 mid2
                           then [(s, o)]
                           else []) r2) r1)
  | PP_Alternative (p1, p2) ->
      dedup_path
        (FStar_List_Tot_Base.op_At (eval_property_path p1 g)
           (eval_property_path p2 g))
  | PP_ZeroOrOne pp ->
      let reflexive =
        FStar_List_Tot_Base.map (fun n -> (n, n)) (graph_nodes g) in
      let step = eval_property_path pp g in
      dedup_path (FStar_List_Tot_Base.op_At reflexive step)
  | PP_ZeroOrMore pp ->
      let reflexive =
        FStar_List_Tot_Base.map (fun n -> (n, n)) (graph_nodes g) in
      let step = eval_property_path pp g in
      dedup_path (FStar_List_Tot_Base.op_At reflexive step)
  | PP_OneOrMore pp -> eval_property_path pp g
  | PP_NegatedSet ps ->
      let excluded = negated_iris ps in
      FStar_List_Tot_Base.concatMap
        (fun t ->
           if iri_in_list t.RDF_Graph_Executable.p excluded
           then []
           else
             [((subject_to_term t.RDF_Graph_Executable.s),
                (t.RDF_Graph_Executable.o))]) g
type numeric_precision =
  | NP_Integer 
  | NP_Decimal 
  | NP_Float 
  | NP_Double 
let uu___is_NP_Integer (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Integer -> true | uu___ -> false
let uu___is_NP_Decimal (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Decimal -> true | uu___ -> false
let uu___is_NP_Float (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Float -> true | uu___ -> false
let uu___is_NP_Double (projectee : numeric_precision) : Prims.bool=
  match projectee with | NP_Double -> true | uu___ -> false
let numeric_precision_of (dt : RDF_Graph_Executable.wf_iri) :
  numeric_precision FStar_Pervasives_Native.option=
  if dt = RDF_Graph_Executable.xsd_integer
  then FStar_Pervasives_Native.Some NP_Integer
  else
    if dt = RDF_Graph_Executable.xsd_decimal
    then FStar_Pervasives_Native.Some NP_Decimal
    else
      if dt = xsd_float
      then FStar_Pervasives_Native.Some NP_Float
      else
        if dt = RDF_Graph_Executable.xsd_double
        then FStar_Pervasives_Native.Some NP_Double
        else FStar_Pervasives_Native.None
let promote_numeric (a : numeric_precision) (b : numeric_precision) :
  numeric_precision=
  match (a, b) with
  | (NP_Double, uu___) -> NP_Double
  | (uu___, NP_Double) -> NP_Double
  | (NP_Float, uu___) -> NP_Float
  | (uu___, NP_Float) -> NP_Float
  | (NP_Decimal, uu___) -> NP_Decimal
  | (uu___, NP_Decimal) -> NP_Decimal
  | (NP_Integer, NP_Integer) -> NP_Integer
let promoted_datatype (p : numeric_precision) : RDF_Graph_Executable.wf_iri=
  match p with
  | NP_Integer -> RDF_Graph_Executable.xsd_integer
  | NP_Decimal -> RDF_Graph_Executable.xsd_decimal
  | NP_Float -> xsd_float
  | NP_Double -> RDF_Graph_Executable.xsd_double
type cast_target =
  | Cast_Integer 
  | Cast_Decimal 
  | Cast_Float 
  | Cast_Double 
  | Cast_String 
  | Cast_Boolean 
  | Cast_DateTime 
let uu___is_Cast_Integer (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Integer -> true | uu___ -> false
let uu___is_Cast_Decimal (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Decimal -> true | uu___ -> false
let uu___is_Cast_Float (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Float -> true | uu___ -> false
let uu___is_Cast_Double (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Double -> true | uu___ -> false
let uu___is_Cast_String (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_String -> true | uu___ -> false
let uu___is_Cast_Boolean (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_Boolean -> true | uu___ -> false
let uu___is_Cast_DateTime (projectee : cast_target) : Prims.bool=
  match projectee with | Cast_DateTime -> true | uu___ -> false
let er_to_lexical (v : eval_result) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | ER_Term (RDF_Graph_Executable.T_Literal l) ->
      FStar_Pervasives_Native.Some (lit_lexical l)
  | ER_Term (RDF_Graph_Executable.T_IRI i) ->
      FStar_Pervasives_Native.Some (iri_to_string i)
  | ER_Term (RDF_Graph_Executable.T_BNode b) ->
      FStar_Pervasives_Native.Some b
  | ER_Num n -> FStar_Pervasives_Native.Some (Prims.string_of_int n)
  | ER_Dec s -> FStar_Pervasives_Native.Some s
  | ER_Dbl s -> FStar_Pervasives_Native.Some s
  | ER_Bool true -> FStar_Pervasives_Native.Some "true"
  | ER_Bool false -> FStar_Pervasives_Native.Some "false"
  | ER_Error -> FStar_Pervasives_Native.None
let is_decimal_string (s : Prims.string) : Prims.bool=
  (FStar_String.strlen s) > Prims.int_zero
let xsd_cast (v : eval_result) (target : cast_target) :
  eval_result FStar_Pervasives_Native.option=
  match target with
  | Cast_Integer ->
      (match v with
       | ER_Num uu___ -> FStar_Pervasives_Native.Some v
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Num Prims.int_one)
       | ER_Bool false ->
           FStar_Pervasives_Native.Some (ER_Num Prims.int_zero)
       | ER_Dec s ->
           (match parse_int_string s with
            | FStar_Pervasives_Native.Some n ->
                FStar_Pervasives_Native.Some (ER_Num n)
            | FStar_Pervasives_Native.None ->
                let chars = FStar_String.list_of_string s in
                let before_dot =
                  list_take_while
                    (fun c ->
                       c <> (FStar_Char.char_of_int (Prims.of_int (46))))
                    chars in
                (match parse_int_string
                         (FStar_String.string_of_list before_dot)
                 with
                 | FStar_Pervasives_Native.Some n ->
                     FStar_Pervasives_Native.Some (ER_Num n)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | ER_Dbl s ->
           (match parse_int_string s with
            | FStar_Pervasives_Native.Some n ->
                FStar_Pervasives_Native.Some (ER_Num n)
            | FStar_Pervasives_Native.None ->
                let chars = FStar_String.list_of_string s in
                let before_dot =
                  list_take_while
                    (fun c ->
                       c <> (FStar_Char.char_of_int (Prims.of_int (46))))
                    chars in
                (match parse_int_string
                         (FStar_String.string_of_list before_dot)
                 with
                 | FStar_Pervasives_Native.Some n ->
                     FStar_Pervasives_Native.Some (ER_Num n)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           if
             ((lit_datatype l) = RDF_Graph_Executable.xsd_integer) ||
               ((lit_datatype l) = RDF_Graph_Executable.xsd_string)
           then
             (match parse_int_string (lit_lexical l) with
              | FStar_Pervasives_Native.Some n ->
                  FStar_Pervasives_Native.Some (ER_Num n)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
             then
               (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                then FStar_Pervasives_Native.Some (ER_Num Prims.int_one)
                else
                  if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                  then FStar_Pervasives_Native.Some (ER_Num Prims.int_zero)
                  else FStar_Pervasives_Native.None)
             else
               if
                 (((lit_datatype l) = RDF_Graph_Executable.xsd_decimal) ||
                    ((lit_datatype l) = RDF_Graph_Executable.xsd_double))
                   || ((lit_datatype l) = xsd_float)
               then
                 (let chars = FStar_String.list_of_string (lit_lexical l) in
                  let before_dot =
                    list_take_while
                      (fun c ->
                         c <> (FStar_Char.char_of_int (Prims.of_int (46))))
                      chars in
                  match parse_int_string
                          (FStar_String.string_of_list before_dot)
                  with
                  | FStar_Pervasives_Native.Some n ->
                      FStar_Pervasives_Native.Some (ER_Num n)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_Decimal ->
      (match v with
       | ER_Dec uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some
             (ER_Dec (Prims.strcat (Prims.string_of_int n) ".0"))
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Dec "1.0")
       | ER_Bool false -> FStar_Pervasives_Native.Some (ER_Dec "0.0")
       | ER_Dbl s -> FStar_Pervasives_Native.Some (ER_Dec s)
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           if
             ((lit_datatype l) = RDF_Graph_Executable.xsd_decimal) ||
               ((lit_datatype l) = RDF_Graph_Executable.xsd_string)
           then FStar_Pervasives_Native.Some (ER_Dec (lit_lexical l))
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_integer
             then
               (match parse_int_string (lit_lexical l) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some
                      (ER_Dec (Prims.strcat (Prims.string_of_int n) ".0"))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
               then
                 (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                  then FStar_Pervasives_Native.Some (ER_Dec "1.0")
                  else
                    if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                    then FStar_Pervasives_Native.Some (ER_Dec "0.0")
                    else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_Double ->
      (match v with
       | ER_Dbl uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some
             (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
       | ER_Dec s -> FStar_Pervasives_Native.Some (ER_Dbl s)
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
       | ER_Bool false -> FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           if
             ((((lit_datatype l) = RDF_Graph_Executable.xsd_double) ||
                 ((lit_datatype l) = xsd_float))
                || ((lit_datatype l) = RDF_Graph_Executable.xsd_decimal))
               || ((lit_datatype l) = RDF_Graph_Executable.xsd_string)
           then FStar_Pervasives_Native.Some (ER_Dbl (lit_lexical l))
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_integer
             then
               (match parse_int_string (lit_lexical l) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some
                      (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
               then
                 (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                  then FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
                  else
                    if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                    then FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
                    else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_Float ->
      (match v with
       | ER_Dbl uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some
             (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
       | ER_Dec s -> FStar_Pervasives_Native.Some (ER_Dbl s)
       | ER_Bool true -> FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
       | ER_Bool false -> FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           if
             ((((lit_datatype l) = RDF_Graph_Executable.xsd_double) ||
                 ((lit_datatype l) = xsd_float))
                || ((lit_datatype l) = RDF_Graph_Executable.xsd_decimal))
               || ((lit_datatype l) = RDF_Graph_Executable.xsd_string)
           then FStar_Pervasives_Native.Some (ER_Dbl (lit_lexical l))
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_integer
             then
               (match parse_int_string (lit_lexical l) with
                | FStar_Pervasives_Native.Some n ->
                    FStar_Pervasives_Native.Some
                      (ER_Dbl (Prims.strcat (Prims.string_of_int n) ".0E0"))
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
               then
                 (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                  then FStar_Pervasives_Native.Some (ER_Dbl "1.0E0")
                  else
                    if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                    then FStar_Pervasives_Native.Some (ER_Dbl "0.0E0")
                    else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_String ->
      (match v with
       | ER_Num n ->
           FStar_Pervasives_Native.Some (er_string (Prims.string_of_int n))
       | ER_Dec s -> FStar_Pervasives_Native.Some (er_string s)
       | ER_Dbl s -> FStar_Pervasives_Native.Some (er_string s)
       | ER_Bool true -> FStar_Pervasives_Native.Some (er_string "true")
       | ER_Bool false -> FStar_Pervasives_Native.Some (er_string "false")
       | ER_Term (RDF_Graph_Executable.T_IRI i) ->
           FStar_Pervasives_Native.Some (er_string (iri_to_string i))
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           FStar_Pervasives_Native.Some (er_string (lit_lexical l))
       | ER_Term (RDF_Graph_Executable.T_BNode uu___) ->
           FStar_Pervasives_Native.None
       | ER_Error -> FStar_Pervasives_Native.None)
  | Cast_Boolean ->
      (match v with
       | ER_Bool uu___ -> FStar_Pervasives_Native.Some v
       | ER_Num n ->
           FStar_Pervasives_Native.Some (ER_Bool (n <> Prims.int_zero))
       | ER_Dec s ->
           FStar_Pervasives_Native.Some
             (ER_Bool ((s <> "0") && (s <> "0.0")))
       | ER_Dbl s ->
           FStar_Pervasives_Native.Some
             (ER_Bool (((s <> "0") && (s <> "0.0")) && (s <> "0.0E0")))
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           if (lit_datatype l) = RDF_Graph_Executable.xsd_boolean
           then
             (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
              then FStar_Pervasives_Native.Some (ER_Bool true)
              else
                if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                then FStar_Pervasives_Native.Some (ER_Bool false)
                else FStar_Pervasives_Native.None)
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_string
             then
               (if ((lit_lexical l) = "true") || ((lit_lexical l) = "1")
                then FStar_Pervasives_Native.Some (ER_Bool true)
                else
                  if ((lit_lexical l) = "false") || ((lit_lexical l) = "0")
                  then FStar_Pervasives_Native.Some (ER_Bool false)
                  else FStar_Pervasives_Native.None)
             else
               if (lit_datatype l) = RDF_Graph_Executable.xsd_integer
               then
                 (match parse_int_string (lit_lexical l) with
                  | FStar_Pervasives_Native.Some n ->
                      FStar_Pervasives_Native.Some
                        (ER_Bool (n <> Prims.int_zero))
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | Cast_DateTime ->
      (match v with
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           if (lit_datatype l) = xsd_dateTime
           then FStar_Pervasives_Native.Some v
           else
             if (lit_datatype l) = RDF_Graph_Executable.xsd_string
             then
               FStar_Pervasives_Native.Some
                 (ER_Term
                    (RDF_Graph_Executable.T_Literal
                       {
                         RDF_Graph_Executable.lexical_form = (lit_lexical l);
                         RDF_Graph_Executable.datatype = xsd_dateTime;
                         RDF_Graph_Executable.lang_tag =
                           FStar_Pervasives_Native.None
                       }))
             else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
let substitute_pattern_term (mu : RDF_Graph_Executable.solution_mapping)
  (pt : pattern_term) : pattern_term=
  match pt with
  | PT_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI i) ->
           PT_IRI i
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_BNode b) ->
           PT_BNode b
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal l) ->
           PT_Literal l
       | FStar_Pervasives_Native.None -> PT_Var v)
  | uu___ -> pt
let substitute_pattern_subject (mu : RDF_Graph_Executable.solution_mapping)
  (ps : pattern_subject) : pattern_subject=
  match ps with
  | PS_Var v ->
      (match sm_lookup v mu with
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI i) ->
           PS_IRI i
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_BNode b) ->
           PS_BNode b
       | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal uu___)
           -> PS_Var v
       | FStar_Pervasives_Native.None -> PS_Var v)
  | uu___ -> ps
let substitute_triple_pattern (mu : RDF_Graph_Executable.solution_mapping)
  (tp : triple_pattern) : triple_pattern=
  {
    tp_s = (substitute_pattern_subject mu tp.tp_s);
    tp_p = (substitute_pattern_term mu tp.tp_p);
    tp_o = (substitute_pattern_term mu tp.tp_o)
  }
let substitute_bgp (mu : RDF_Graph_Executable.solution_mapping) (b : bgp) :
  bgp= FStar_List_Tot_Base.map (substitute_triple_pattern mu) b
let rec substitute_pattern (mu : RDF_Graph_Executable.solution_mapping)
  (p : group_graph_pattern) : group_graph_pattern=
  match p with
  | GP_BGP b -> GP_BGP (substitute_bgp mu b)
  | GP_Join (p1, p2) ->
      GP_Join ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_LeftJoin (p1, p2, e) ->
      GP_LeftJoin ((substitute_pattern mu p1), (substitute_pattern mu p2), e)
  | GP_Filter (e, p1) -> GP_Filter (e, (substitute_pattern mu p1))
  | GP_Union (p1, p2) ->
      GP_Union ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_Graph (gt, p1) ->
      GP_Graph ((substitute_pattern_term mu gt), (substitute_pattern mu p1))
  | GP_Minus (p1, p2) ->
      GP_Minus ((substitute_pattern mu p1), (substitute_pattern mu p2))
  | GP_Bind (e, v, p1) -> GP_Bind (e, v, (substitute_pattern mu p1))
  | GP_Values (vars, rows) -> GP_Values (vars, rows)
  | GP_Service (iri, p1, silent) -> GP_Service (iri, p1, silent)
  | GP_SubSelect q -> GP_SubSelect q
  | GP_PropertyPath (ps, pp, pt) ->
      GP_PropertyPath
        ((substitute_pattern_subject mu ps), pp,
          (substitute_pattern_term mu pt))
  | GP_Empty -> GP_Empty
let eval_exists (pattern : group_graph_pattern)
  (mu : RDF_Graph_Executable.solution_mapping)
  (graph : RDF_Graph_Executable.rdf_graph) : Prims.bool=
  let substituted = substitute_pattern mu pattern in
  (FStar_List_Tot_Base.length (eval_pattern substituted graph)) >
    Prims.int_zero
let eval_not_exists (pattern : group_graph_pattern)
  (mu : RDF_Graph_Executable.solution_mapping)
  (graph : RDF_Graph_Executable.rdf_graph) : Prims.bool=
  Prims.op_Negation (eval_exists pattern mu graph)
let () = eval_exists_fwd_ref := (fun p mu g -> eval_exists p mu g)
let filter_solutions (e : expr) (omega : solution_sequence) :
  solution_sequence= FStar_List_Tot_Base.filter (eval_expr_ebv e) omega
