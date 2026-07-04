open Prims
(* SHACL sh:sparql dispatch acknowledgement -- issue #181.
   `validate` and `parse_shape_from_graph` are real F-star
   (Phase 2 / slice 1 landed 2026-07-04) -- only
   `eval_sparql_target_select` is still extracted as a
   `failwith` stub, and it is unreachable this slice (T_Sparql
   targets and CC_Sparql constraints both evaluate to "no
   result" in pure F-star). See
     formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
     181_shacl_validate_stub.sh
   for the wiring plan. *)
let sh_NodeShape : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#NodeShape"
let sh_PropertyShape : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#PropertyShape"
let sh_targetClass : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#targetClass"
let sh_targetNode : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#targetNode"
let sh_targetSubjectsOf : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#targetSubjectsOf"
let sh_targetObjectsOf : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#targetObjectsOf"
let sh_path : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#path"
let sh_select : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#select"
let sh_Violation : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#Violation"
type severity =
  | Sev_Info 
  | Sev_Warning 
  | Sev_Violation 
let uu___is_Sev_Info (projectee : severity) : Prims.bool=
  match projectee with | Sev_Info -> true | uu___ -> false
let uu___is_Sev_Warning (projectee : severity) : Prims.bool=
  match projectee with | Sev_Warning -> true | uu___ -> false
let uu___is_Sev_Violation (projectee : severity) : Prims.bool=
  match projectee with | Sev_Violation -> true | uu___ -> false
type node_kind =
  | NK_BlankNode 
  | NK_IRI 
  | NK_Literal 
  | NK_BlankNodeOrIRI 
  | NK_BlankNodeOrLiteral 
  | NK_IRIOrLiteral 
let uu___is_NK_BlankNode (projectee : node_kind) : Prims.bool=
  match projectee with | NK_BlankNode -> true | uu___ -> false
let uu___is_NK_IRI (projectee : node_kind) : Prims.bool=
  match projectee with | NK_IRI -> true | uu___ -> false
let uu___is_NK_Literal (projectee : node_kind) : Prims.bool=
  match projectee with | NK_Literal -> true | uu___ -> false
let uu___is_NK_BlankNodeOrIRI (projectee : node_kind) : Prims.bool=
  match projectee with | NK_BlankNodeOrIRI -> true | uu___ -> false
let uu___is_NK_BlankNodeOrLiteral (projectee : node_kind) : Prims.bool=
  match projectee with | NK_BlankNodeOrLiteral -> true | uu___ -> false
let uu___is_NK_IRIOrLiteral (projectee : node_kind) : Prims.bool=
  match projectee with | NK_IRIOrLiteral -> true | uu___ -> false
type path =
  | P_Predicate of RDF_Graph_Executable.wf_iri 
  | P_Inverse of path 
  | P_Sequence of path Prims.list 
  | P_Alternative of path Prims.list 
  | P_ZeroOrMore of path 
  | P_OneOrMore of path 
  | P_ZeroOrOne of path 
let uu___is_P_Predicate (projectee : path) : Prims.bool=
  match projectee with | P_Predicate _0 -> true | uu___ -> false
let __proj__P_Predicate__item___0 (projectee : path) :
  RDF_Graph_Executable.wf_iri= match projectee with | P_Predicate _0 -> _0
let uu___is_P_Inverse (projectee : path) : Prims.bool=
  match projectee with | P_Inverse _0 -> true | uu___ -> false
let __proj__P_Inverse__item___0 (projectee : path) : path=
  match projectee with | P_Inverse _0 -> _0
let uu___is_P_Sequence (projectee : path) : Prims.bool=
  match projectee with | P_Sequence _0 -> true | uu___ -> false
let __proj__P_Sequence__item___0 (projectee : path) : path Prims.list=
  match projectee with | P_Sequence _0 -> _0
let uu___is_P_Alternative (projectee : path) : Prims.bool=
  match projectee with | P_Alternative _0 -> true | uu___ -> false
let __proj__P_Alternative__item___0 (projectee : path) : path Prims.list=
  match projectee with | P_Alternative _0 -> _0
let uu___is_P_ZeroOrMore (projectee : path) : Prims.bool=
  match projectee with | P_ZeroOrMore _0 -> true | uu___ -> false
let __proj__P_ZeroOrMore__item___0 (projectee : path) : path=
  match projectee with | P_ZeroOrMore _0 -> _0
let uu___is_P_OneOrMore (projectee : path) : Prims.bool=
  match projectee with | P_OneOrMore _0 -> true | uu___ -> false
let __proj__P_OneOrMore__item___0 (projectee : path) : path=
  match projectee with | P_OneOrMore _0 -> _0
let uu___is_P_ZeroOrOne (projectee : path) : Prims.bool=
  match projectee with | P_ZeroOrOne _0 -> true | uu___ -> false
let __proj__P_ZeroOrOne__item___0 (projectee : path) : path=
  match projectee with | P_ZeroOrOne _0 -> _0
type target =
  | T_Class of RDF_Graph_Executable.wf_iri 
  | T_Node of RDF_Graph_Executable.rdf_term 
  | T_SubjectsOf of RDF_Graph_Executable.wf_iri 
  | T_ObjectsOf of RDF_Graph_Executable.wf_iri 
  | T_ImplicitClass of RDF_Graph_Executable.wf_iri 
  | T_Sparql of Prims.string 
let uu___is_T_Class (projectee : target) : Prims.bool=
  match projectee with | T_Class _0 -> true | uu___ -> false
let __proj__T_Class__item___0 (projectee : target) :
  RDF_Graph_Executable.wf_iri= match projectee with | T_Class _0 -> _0
let uu___is_T_Node (projectee : target) : Prims.bool=
  match projectee with | T_Node _0 -> true | uu___ -> false
let __proj__T_Node__item___0 (projectee : target) :
  RDF_Graph_Executable.rdf_term= match projectee with | T_Node _0 -> _0
let uu___is_T_SubjectsOf (projectee : target) : Prims.bool=
  match projectee with | T_SubjectsOf _0 -> true | uu___ -> false
let __proj__T_SubjectsOf__item___0 (projectee : target) :
  RDF_Graph_Executable.wf_iri= match projectee with | T_SubjectsOf _0 -> _0
let uu___is_T_ObjectsOf (projectee : target) : Prims.bool=
  match projectee with | T_ObjectsOf _0 -> true | uu___ -> false
let __proj__T_ObjectsOf__item___0 (projectee : target) :
  RDF_Graph_Executable.wf_iri= match projectee with | T_ObjectsOf _0 -> _0
let uu___is_T_ImplicitClass (projectee : target) : Prims.bool=
  match projectee with | T_ImplicitClass _0 -> true | uu___ -> false
let __proj__T_ImplicitClass__item___0 (projectee : target) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | T_ImplicitClass _0 -> _0
let uu___is_T_Sparql (projectee : target) : Prims.bool=
  match projectee with | T_Sparql _0 -> true | uu___ -> false
let __proj__T_Sparql__item___0 (projectee : target) : Prims.string=
  match projectee with | T_Sparql _0 -> _0
type shape_ref = Prims.string
type constraint_component =
  | CC_MinCount of Prims.nat 
  | CC_MaxCount of Prims.nat 
  | CC_Datatype of RDF_Graph_Executable.wf_iri 
  | CC_NodeKind of node_kind 
  | CC_Class of RDF_Graph_Executable.wf_iri 
  | CC_In of RDF_Graph_Executable.rdf_term Prims.list 
  | CC_HasValue of RDF_Graph_Executable.rdf_term 
  | CC_Pattern of Prims.string * Prims.string 
  | CC_MinLength of Prims.nat 
  | CC_MaxLength of Prims.nat 
  | CC_LanguageIn of Prims.string Prims.list 
  | CC_UniqueLang of Prims.bool 
  | CC_MinInclusive of RDF_Graph_Executable.rdf_term 
  | CC_MaxInclusive of RDF_Graph_Executable.rdf_term 
  | CC_MinExclusive of RDF_Graph_Executable.rdf_term 
  | CC_MaxExclusive of RDF_Graph_Executable.rdf_term 
  | CC_Not of shape_ref 
  | CC_And of shape_ref Prims.list 
  | CC_Or of shape_ref Prims.list 
  | CC_Xone of shape_ref Prims.list 
  | CC_Node of shape_ref 
  | CC_Equals of RDF_Graph_Executable.wf_iri 
  | CC_Disjoint of RDF_Graph_Executable.wf_iri 
  | CC_LessThan of RDF_Graph_Executable.wf_iri 
  | CC_LessThanOrEq of RDF_Graph_Executable.wf_iri 
  | CC_Closed of RDF_Graph_Executable.wf_iri Prims.list 
  | CC_Sparql of Prims.string 
let uu___is_CC_MinCount (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MinCount _0 -> true | uu___ -> false
let __proj__CC_MinCount__item___0 (projectee : constraint_component) :
  Prims.nat= match projectee with | CC_MinCount _0 -> _0
let uu___is_CC_MaxCount (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxCount _0 -> true | uu___ -> false
let __proj__CC_MaxCount__item___0 (projectee : constraint_component) :
  Prims.nat= match projectee with | CC_MaxCount _0 -> _0
let uu___is_CC_Datatype (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Datatype _0 -> true | uu___ -> false
let __proj__CC_Datatype__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri= match projectee with | CC_Datatype _0 -> _0
let uu___is_CC_NodeKind (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_NodeKind _0 -> true | uu___ -> false
let __proj__CC_NodeKind__item___0 (projectee : constraint_component) :
  node_kind= match projectee with | CC_NodeKind _0 -> _0
let uu___is_CC_Class (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Class _0 -> true | uu___ -> false
let __proj__CC_Class__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri= match projectee with | CC_Class _0 -> _0
let uu___is_CC_In (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_In _0 -> true | uu___ -> false
let __proj__CC_In__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match projectee with | CC_In _0 -> _0
let uu___is_CC_HasValue (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_HasValue _0 -> true | uu___ -> false
let __proj__CC_HasValue__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.rdf_term= match projectee with | CC_HasValue _0 -> _0
let uu___is_CC_Pattern (projectee : constraint_component) : Prims.bool=
  match projectee with
  | CC_Pattern (pattern_re, flags) -> true
  | uu___ -> false
let __proj__CC_Pattern__item__pattern_re (projectee : constraint_component) :
  Prims.string=
  match projectee with | CC_Pattern (pattern_re, flags) -> pattern_re
let __proj__CC_Pattern__item__flags (projectee : constraint_component) :
  Prims.string=
  match projectee with | CC_Pattern (pattern_re, flags) -> flags
let uu___is_CC_MinLength (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MinLength _0 -> true | uu___ -> false
let __proj__CC_MinLength__item___0 (projectee : constraint_component) :
  Prims.nat= match projectee with | CC_MinLength _0 -> _0
let uu___is_CC_MaxLength (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxLength _0 -> true | uu___ -> false
let __proj__CC_MaxLength__item___0 (projectee : constraint_component) :
  Prims.nat= match projectee with | CC_MaxLength _0 -> _0
let uu___is_CC_LanguageIn (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_LanguageIn _0 -> true | uu___ -> false
let __proj__CC_LanguageIn__item___0 (projectee : constraint_component) :
  Prims.string Prims.list= match projectee with | CC_LanguageIn _0 -> _0
let uu___is_CC_UniqueLang (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_UniqueLang _0 -> true | uu___ -> false
let __proj__CC_UniqueLang__item___0 (projectee : constraint_component) :
  Prims.bool= match projectee with | CC_UniqueLang _0 -> _0
let uu___is_CC_MinInclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MinInclusive _0 -> true | uu___ -> false
let __proj__CC_MinInclusive__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | CC_MinInclusive _0 -> _0
let uu___is_CC_MaxInclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxInclusive _0 -> true | uu___ -> false
let __proj__CC_MaxInclusive__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | CC_MaxInclusive _0 -> _0
let uu___is_CC_MinExclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MinExclusive _0 -> true | uu___ -> false
let __proj__CC_MinExclusive__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | CC_MinExclusive _0 -> _0
let uu___is_CC_MaxExclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxExclusive _0 -> true | uu___ -> false
let __proj__CC_MaxExclusive__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.rdf_term=
  match projectee with | CC_MaxExclusive _0 -> _0
let uu___is_CC_Not (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Not _0 -> true | uu___ -> false
let __proj__CC_Not__item___0 (projectee : constraint_component) : shape_ref=
  match projectee with | CC_Not _0 -> _0
let uu___is_CC_And (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_And _0 -> true | uu___ -> false
let __proj__CC_And__item___0 (projectee : constraint_component) :
  shape_ref Prims.list= match projectee with | CC_And _0 -> _0
let uu___is_CC_Or (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Or _0 -> true | uu___ -> false
let __proj__CC_Or__item___0 (projectee : constraint_component) :
  shape_ref Prims.list= match projectee with | CC_Or _0 -> _0
let uu___is_CC_Xone (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Xone _0 -> true | uu___ -> false
let __proj__CC_Xone__item___0 (projectee : constraint_component) :
  shape_ref Prims.list= match projectee with | CC_Xone _0 -> _0
let uu___is_CC_Node (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Node _0 -> true | uu___ -> false
let __proj__CC_Node__item___0 (projectee : constraint_component) : shape_ref=
  match projectee with | CC_Node _0 -> _0
let uu___is_CC_Equals (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Equals _0 -> true | uu___ -> false
let __proj__CC_Equals__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri= match projectee with | CC_Equals _0 -> _0
let uu___is_CC_Disjoint (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Disjoint _0 -> true | uu___ -> false
let __proj__CC_Disjoint__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri= match projectee with | CC_Disjoint _0 -> _0
let uu___is_CC_LessThan (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_LessThan _0 -> true | uu___ -> false
let __proj__CC_LessThan__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri= match projectee with | CC_LessThan _0 -> _0
let uu___is_CC_LessThanOrEq (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_LessThanOrEq _0 -> true | uu___ -> false
let __proj__CC_LessThanOrEq__item___0 (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri=
  match projectee with | CC_LessThanOrEq _0 -> _0
let uu___is_CC_Closed (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Closed ignored -> true | uu___ -> false
let __proj__CC_Closed__item__ignored (projectee : constraint_component) :
  RDF_Graph_Executable.wf_iri Prims.list=
  match projectee with | CC_Closed ignored -> ignored
let uu___is_CC_Sparql (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Sparql _0 -> true | uu___ -> false
let __proj__CC_Sparql__item___0 (projectee : constraint_component) :
  Prims.string= match projectee with | CC_Sparql _0 -> _0
type shape =
  {
  shape_id: shape_ref ;
  is_property: Prims.bool ;
  shape_path: path FStar_Pervasives_Native.option ;
  targets: target Prims.list ;
  shape_sev: severity ;
  message: Prims.string FStar_Pervasives_Native.option ;
  constraints: constraint_component Prims.list ;
  property_refs: shape_ref Prims.list }
let __proj__Mkshape__item__shape_id (projectee : shape) : shape_ref=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> shape_id
let __proj__Mkshape__item__is_property (projectee : shape) : Prims.bool=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> is_property
let __proj__Mkshape__item__shape_path (projectee : shape) :
  path FStar_Pervasives_Native.option=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> shape_path
let __proj__Mkshape__item__targets (projectee : shape) : target Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> targets
let __proj__Mkshape__item__shape_sev (projectee : shape) : severity=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> shape_sev
let __proj__Mkshape__item__message (projectee : shape) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> message
let __proj__Mkshape__item__constraints (projectee : shape) :
  constraint_component Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> constraints
let __proj__Mkshape__item__property_refs (projectee : shape) :
  shape_ref Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; property_refs;_} -> property_refs
type shapes_graph = {
  shapes: shape Prims.list }
let __proj__Mkshapes_graph__item__shapes (projectee : shapes_graph) :
  shape Prims.list= match projectee with | { shapes;_} -> shapes
let empty_shapes_graph : shapes_graph= { shapes = [] }
type violation =
  {
  v_focus_node: RDF_Graph_Executable.rdf_term ;
  v_path: path FStar_Pervasives_Native.option ;
  v_value: RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option ;
  v_source_shape: shape_ref ;
  v_constraint: constraint_component ;
  v_severity: severity ;
  v_message: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkviolation__item__v_focus_node (projectee : violation) :
  RDF_Graph_Executable.rdf_term=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_focus_node
let __proj__Mkviolation__item__v_path (projectee : violation) :
  path FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_path
let __proj__Mkviolation__item__v_value (projectee : violation) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_value
let __proj__Mkviolation__item__v_source_shape (projectee : violation) :
  shape_ref=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_source_shape
let __proj__Mkviolation__item__v_constraint (projectee : violation) :
  constraint_component=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_constraint
let __proj__Mkviolation__item__v_severity (projectee : violation) : severity=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_severity
let __proj__Mkviolation__item__v_message (projectee : violation) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message;_} -> v_message
type validation_report =
  {
  conforms: Prims.bool ;
  results: violation Prims.list }
let __proj__Mkvalidation_report__item__conforms
  (projectee : validation_report) : Prims.bool=
  match projectee with | { conforms; results;_} -> conforms
let __proj__Mkvalidation_report__item__results
  (projectee : validation_report) : violation Prims.list=
  match projectee with | { conforms; results;_} -> results
let conforming_report : validation_report= { conforms = true; results = [] }
let mk_shape_node (id_ : shape_ref) (ts : target Prims.list)
  (cs : constraint_component Prims.list) : shape=
  {
    shape_id = id_;
    is_property = false;
    shape_path = FStar_Pervasives_Native.None;
    targets = ts;
    shape_sev = Sev_Violation;
    message = FStar_Pervasives_Native.None;
    constraints = cs;
    property_refs = []
  }
let mk_shape_property (id_ : shape_ref) (p : path) (ts : target Prims.list)
  (cs : constraint_component Prims.list) : shape=
  {
    shape_id = id_;
    is_property = true;
    shape_path = (FStar_Pervasives_Native.Some p);
    targets = ts;
    shape_sev = Sev_Violation;
    message = FStar_Pervasives_Native.None;
    constraints = cs;
    property_refs = []
  }
let shapes_graph_of_list (ss : shape Prims.list) : shapes_graph=
  { shapes = ss }
let rec lookup_shape (id_ : shape_ref) (sg : shape Prims.list) :
  shape FStar_Pervasives_Native.option=
  match sg with
  | [] -> FStar_Pervasives_Native.None
  | s::rest ->
      if s.shape_id = id_
      then FStar_Pervasives_Native.Some s
      else lookup_shape id_ rest
let shape_well_formed (s : shape) : Prims.bool=
  if s.is_property
  then FStar_Pervasives_Native.uu___is_Some s.shape_path
  else FStar_Pervasives_Native.uu___is_None s.shape_path
let rec shapes_well_formed (ss : shape Prims.list) : Prims.bool=
  match ss with
  | [] -> true
  | s::rest -> (shape_well_formed s) && (shapes_well_formed rest)
let rec rdf_list_terms (g : RDF_Graph_Executable.rdf_graph)
  (head : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | n ->
      (match head with
       | RDF_Graph_Executable.T_BNode uu___ ->
           (match RDF_Graph_Executable.term_to_subject head with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some s ->
                (match ((RDF_Graph_Executable.find_objects g s
                           RDF_Graph_Executable.rdf_first),
                         (RDF_Graph_Executable.find_objects g s
                            RDF_Graph_Executable.rdf_rest))
                 with
                 | (h::uu___1, r::uu___2) -> h ::
                     (rdf_list_terms g r (n - Prims.int_one))
                 | (uu___1, uu___2) -> []))
       | uu___ -> [])
let rec distinct_subjects_acc (g : RDF_Graph_Executable.rdf_graph)
  (acc : RDF_Graph_Executable.subject Prims.list) :
  RDF_Graph_Executable.subject Prims.list=
  match g with
  | [] -> acc
  | t::rest ->
      if
        FStar_List_Tot_Base.existsb
          (RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s) acc
      then distinct_subjects_acc rest acc
      else distinct_subjects_acc rest ((t.RDF_Graph_Executable.s) :: acc)
let distinct_subjects (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.subject Prims.list= distinct_subjects_acc g []
let dedup_terms_acc (acc : RDF_Graph_Executable.rdf_term Prims.list)
  (t : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.rdf_term Prims.list=
  if FStar_List_Tot_Base.existsb (RDF_Graph_Executable.rdf_term_eq t) acc
  then acc
  else FStar_List_Tot_Base.op_At acc [t]
let dedup_terms (l : RDF_Graph_Executable.rdf_term Prims.list) :
  RDF_Graph_Executable.rdf_term Prims.list=
  FStar_List_Tot_Base.fold_left dedup_terms_acc [] l
let term_to_shape_ref (t : RDF_Graph_Executable.rdf_term) :
  shape_ref FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_IRI i -> FStar_Pervasives_Native.Some i
  | RDF_Graph_Executable.T_BNode b ->
      FStar_Pervasives_Native.Some (Prims.strcat "_:" b)
  | RDF_Graph_Executable.T_Literal uu___ -> FStar_Pervasives_Native.None
let subject_to_shape_ref (s : RDF_Graph_Executable.subject) : shape_ref=
  match s with
  | RDF_Graph_Executable.S_IRI i -> i
  | RDF_Graph_Executable.S_BNode b -> Prims.strcat "_:" b
let term_lexical (t : RDF_Graph_Executable.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match t with
  | RDF_Graph_Executable.T_Literal l ->
      FStar_Pervasives_Native.Some (l.RDF_Graph_Executable.lexical_form)
  | RDF_Graph_Executable.T_IRI i -> FStar_Pervasives_Native.Some i
  | RDF_Graph_Executable.T_BNode uu___ -> FStar_Pervasives_Native.None
let first_int (l : RDF_Graph_Executable.rdf_term Prims.list) :
  Prims.nat FStar_Pervasives_Native.option=
  match l with
  | (RDF_Graph_Executable.T_Literal lit)::uu___ ->
      (match SPARQL11_Algebra.parse_int_string
               lit.RDF_Graph_Executable.lexical_form
       with
       | FStar_Pervasives_Native.Some n ->
           if n >= Prims.int_zero
           then FStar_Pervasives_Native.Some n
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let first_bool (l : RDF_Graph_Executable.rdf_term Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  match l with
  | (RDF_Graph_Executable.T_Literal lit)::uu___ ->
      FStar_Pervasives_Native.Some
        (lit.RDF_Graph_Executable.lexical_form = "true")
  | uu___ -> FStar_Pervasives_Native.None
let sh_property : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#property"
let sh_node : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#node"
let sh_minCount : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#minCount"
let sh_maxCount : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#maxCount"
let sh_datatype : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#datatype"
let sh_nodeKind : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#nodeKind"
let sh_class : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#class"
let sh_in : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#in"
let sh_hasValue : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#hasValue"
let sh_pattern : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#pattern"
let sh_flags : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#flags"
let sh_minLength : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#minLength"
let sh_maxLength : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#maxLength"
let sh_languageIn : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#languageIn"
let sh_uniqueLang : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#uniqueLang"
let sh_minInclusive : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#minInclusive"
let sh_maxInclusive : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#maxInclusive"
let sh_minExclusive : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#minExclusive"
let sh_maxExclusive : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#maxExclusive"
let sh_not : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#not"
let sh_and : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#and"
let sh_or : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#or"
let sh_xone : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#xone"
let sh_equals : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#equals"
let sh_disjoint : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#disjoint"
let sh_lessThan : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#lessThan"
let sh_lessThanOrEquals : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#lessThanOrEquals"
let sh_closed : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#closed"
let sh_ignoredProperties : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#ignoredProperties"
let sh_severity : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#severity"
let sh_message : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#message"
let sh_deactivated : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#deactivated"
let sh_Info : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#Info"
let sh_Warning : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#Warning"
let sh_inversePath : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#inversePath"
let sh_alternativePath : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#alternativePath"
let sh_zeroOrMorePath : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#zeroOrMorePath"
let sh_oneOrMorePath : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#oneOrMorePath"
let sh_zeroOrOnePath : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#zeroOrOnePath"
let sh_nk_BlankNode : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#BlankNode"
let sh_nk_IRI : RDF_Graph_Executable.wf_iri= "http://www.w3.org/ns/shacl#IRI"
let sh_nk_Literal : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#Literal"
let sh_nk_BlankNodeOrIRI : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#BlankNodeOrIRI"
let sh_nk_BlankNodeOrLiteral : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#BlankNodeOrLiteral"
let sh_nk_IRIOrLiteral : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/ns/shacl#IRIOrLiteral"
let node_kind_of_iri (i : RDF_Graph_Executable.wf_iri) :
  node_kind FStar_Pervasives_Native.option=
  if i = sh_nk_BlankNode
  then FStar_Pervasives_Native.Some NK_BlankNode
  else
    if i = sh_nk_IRI
    then FStar_Pervasives_Native.Some NK_IRI
    else
      if i = sh_nk_Literal
      then FStar_Pervasives_Native.Some NK_Literal
      else
        if i = sh_nk_BlankNodeOrIRI
        then FStar_Pervasives_Native.Some NK_BlankNodeOrIRI
        else
          if i = sh_nk_BlankNodeOrLiteral
          then FStar_Pervasives_Native.Some NK_BlankNodeOrLiteral
          else
            if i = sh_nk_IRIOrLiteral
            then FStar_Pervasives_Native.Some NK_IRIOrLiteral
            else FStar_Pervasives_Native.None
let node_kind_ok (t : RDF_Graph_Executable.rdf_term) (nk : node_kind) :
  Prims.bool=
  match (nk, t) with
  | (NK_BlankNode, RDF_Graph_Executable.T_BNode uu___) -> true
  | (NK_IRI, RDF_Graph_Executable.T_IRI uu___) -> true
  | (NK_Literal, RDF_Graph_Executable.T_Literal uu___) -> true
  | (NK_BlankNodeOrIRI, RDF_Graph_Executable.T_BNode uu___) -> true
  | (NK_BlankNodeOrIRI, RDF_Graph_Executable.T_IRI uu___) -> true
  | (NK_BlankNodeOrLiteral, RDF_Graph_Executable.T_BNode uu___) -> true
  | (NK_BlankNodeOrLiteral, RDF_Graph_Executable.T_Literal uu___) -> true
  | (NK_IRIOrLiteral, RDF_Graph_Executable.T_IRI uu___) -> true
  | (NK_IRIOrLiteral, RDF_Graph_Executable.T_Literal uu___) -> true
  | (uu___, uu___1) -> false
let severity_of_iri (i : RDF_Graph_Executable.wf_iri) : severity=
  if i = sh_Warning
  then Sev_Warning
  else if i = sh_Info then Sev_Info else Sev_Violation
let path_term_to_predicate_path (t : RDF_Graph_Executable.rdf_term) : 
  path=
  match t with
  | RDF_Graph_Executable.T_IRI i -> P_Predicate i
  | uu___ -> P_Sequence []
let parse_path (g : RDF_Graph_Executable.rdf_graph)
  (t : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) : path=
  match t with
  | RDF_Graph_Executable.T_IRI i -> P_Predicate i
  | RDF_Graph_Executable.T_Literal uu___ -> P_Sequence []
  | RDF_Graph_Executable.T_BNode uu___ ->
      (match RDF_Graph_Executable.term_to_subject t with
       | FStar_Pervasives_Native.None -> P_Sequence []
       | FStar_Pervasives_Native.Some s ->
           (match RDF_Graph_Executable.find_objects g s sh_inversePath with
            | (RDF_Graph_Executable.T_IRI ip)::[] ->
                P_Inverse (P_Predicate ip)
            | uu___1 ->
                (match RDF_Graph_Executable.find_objects g s
                         sh_alternativePath
                 with
                 | alt_head::uu___2 ->
                     P_Alternative
                       (FStar_List_Tot_Base.map path_term_to_predicate_path
                          (rdf_list_terms g alt_head fuel))
                 | [] ->
                     (match RDF_Graph_Executable.find_objects g s
                              sh_zeroOrMorePath
                      with
                      | (RDF_Graph_Executable.T_IRI zp)::[] ->
                          P_ZeroOrMore (P_Predicate zp)
                      | uu___2 ->
                          (match RDF_Graph_Executable.find_objects g s
                                   sh_oneOrMorePath
                           with
                           | (RDF_Graph_Executable.T_IRI op)::[] ->
                               P_OneOrMore (P_Predicate op)
                           | uu___3 ->
                               (match RDF_Graph_Executable.find_objects g s
                                        sh_zeroOrOnePath
                                with
                                | (RDF_Graph_Executable.T_IRI zop)::[] ->
                                    P_ZeroOrOne (P_Predicate zop)
                                | uu___4 ->
                                    (match RDF_Graph_Executable.find_objects
                                             g s
                                             RDF_Graph_Executable.rdf_first
                                     with
                                     | uu___5::uu___6 ->
                                         P_Sequence
                                           (FStar_List_Tot_Base.map
                                              path_term_to_predicate_path
                                              (rdf_list_terms g t fuel))
                                     | [] -> P_Sequence [])))))))
let eval_path (g : RDF_Graph_Executable.rdf_graph)
  (start : RDF_Graph_Executable.rdf_term) (p : path) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match p with
  | P_Predicate pred ->
      (match RDF_Graph_Executable.term_to_subject start with
       | FStar_Pervasives_Native.Some s ->
           RDF_Graph_Executable.find_objects g s pred
       | FStar_Pervasives_Native.None -> [])
  | P_Inverse (P_Predicate pred) ->
      FStar_List_Tot_Base.map RDF_Graph_Executable.subject_to_term
        (RDF_Graph_Executable.find_subjects g pred start)
  | uu___ -> []
let shacl_class_closure_step (g : RDF_Graph_Executable.rdf_graph) :
  RDF_Graph_Executable.rdf_graph=
  let ig = RDF_Graph_Executable.build_indexed g in
  let g1 = RDF_Graph_Executable.rdfs_rule_subClassOf_trans g ig in
  let ig1 = RDF_Graph_Executable.build_indexed g1 in
  let g2 = RDF_Graph_Executable.rdfs_rule_subClassOf g1 ig1 in
  RDF_Graph_Executable.graph_dedup_sort g2
let rec shacl_class_closure (g : RDF_Graph_Executable.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph_Executable.rdf_graph=
  if fuel = Prims.int_zero
  then g
  else
    (let fuel' = fuel - Prims.int_one in
     let g' = shacl_class_closure_step g in
     if
       (RDF_Graph_Executable.graph_len g') =
         (RDF_Graph_Executable.graph_len g)
     then g
     else shacl_class_closure g' fuel')
let is_shacl_instance (closed_g : RDF_Graph_Executable.rdf_graph)
  (v : RDF_Graph_Executable.rdf_term) (c : RDF_Graph_Executable.wf_iri) :
  Prims.bool=
  match RDF_Graph_Executable.term_to_subject v with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some s ->
      RDF_Graph_Executable.mem_triple
        {
          RDF_Graph_Executable.s = s;
          RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type;
          RDF_Graph_Executable.o = (RDF_Graph_Executable.T_IRI c)
        } closed_g
let eval_target_class (closed_g : RDF_Graph_Executable.rdf_graph)
  (all_subjects : RDF_Graph_Executable.subject Prims.list)
  (c : RDF_Graph_Executable.wf_iri) :
  RDF_Graph_Executable.rdf_term Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun s ->
       if
         is_shacl_instance closed_g (RDF_Graph_Executable.subject_to_term s)
           c
       then [RDF_Graph_Executable.subject_to_term s]
       else []) all_subjects
let eval_target (data : RDF_Graph_Executable.rdf_graph)
  (closed_g : RDF_Graph_Executable.rdf_graph)
  (all_subjects : RDF_Graph_Executable.subject Prims.list) (t : target) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match t with
  | T_Class c -> eval_target_class closed_g all_subjects c
  | T_ImplicitClass c -> eval_target_class closed_g all_subjects c
  | T_Node n -> [n]
  | T_SubjectsOf p ->
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun tr ->
              if tr.RDF_Graph_Executable.p = p
              then
                [RDF_Graph_Executable.subject_to_term
                   tr.RDF_Graph_Executable.s]
              else []) data)
  | T_ObjectsOf p ->
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun tr ->
              if tr.RDF_Graph_Executable.p = p
              then [tr.RDF_Graph_Executable.o]
              else []) data)
  | T_Sparql uu___ -> []
let sh_ns_prefix : Prims.string= "http://www.w3.org/ns/shacl#"
let has_shacl_ns_prefix (p : Prims.string) : Prims.bool=
  let n = FStar_String.strlen sh_ns_prefix in
  ((FStar_String.strlen p) >= n) &&
    ((FStar_String.sub p Prims.int_zero n) = sh_ns_prefix)
let is_shape_trigger_triple (t : RDF_Graph_Executable.triple) : Prims.bool=
  (has_shacl_ns_prefix t.RDF_Graph_Executable.p) ||
    ((t.RDF_Graph_Executable.p = RDF_Graph_Executable.rdf_type) &&
       ((RDF_Graph_Executable.rdf_term_eq t.RDF_Graph_Executable.o
           (RDF_Graph_Executable.T_IRI sh_NodeShape))
          ||
          (RDF_Graph_Executable.rdf_term_eq t.RDF_Graph_Executable.o
             (RDF_Graph_Executable.T_IRI sh_PropertyShape))))
let is_deactivated (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : Prims.bool=
  match first_bool (RDF_Graph_Executable.find_objects g s sh_deactivated)
  with
  | FStar_Pervasives_Native.Some true -> true
  | uu___ -> false
let is_shape_establishing (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : Prims.bool=
  (FStar_List_Tot_Base.existsb
     (fun t ->
        (RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s s) &&
          (is_shape_trigger_triple t)) g)
    && (Prims.op_Negation (is_deactivated g s))
let build_targets (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : target Prims.list=
  let via_class =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [T_Class i]
         | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_targetClass) in
  let via_node =
    FStar_List_Tot_Base.map (fun t -> T_Node t)
      (RDF_Graph_Executable.find_objects g s sh_targetNode) in
  let via_subj_of =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [T_SubjectsOf i]
         | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_targetSubjectsOf) in
  let via_obj_of =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [T_ObjectsOf i]
         | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_targetObjectsOf) in
  let implicit =
    match s with
    | RDF_Graph_Executable.S_IRI i ->
        let is_class =
          FStar_List_Tot_Base.existsb
            (fun t ->
               (RDF_Graph_Executable.rdf_term_eq t
                  (RDF_Graph_Executable.T_IRI RDF_Graph_Executable.rdfs_Class))
                 ||
                 (RDF_Graph_Executable.rdf_term_eq t
                    (RDF_Graph_Executable.T_IRI
                       RDF_Graph_Executable.owl_Class)))
            (RDF_Graph_Executable.find_objects g s
               RDF_Graph_Executable.rdf_type) in
        let is_nodeshape =
          FStar_List_Tot_Base.existsb
            (fun t ->
               RDF_Graph_Executable.rdf_term_eq t
                 (RDF_Graph_Executable.T_IRI sh_NodeShape))
            (RDF_Graph_Executable.find_objects g s
               RDF_Graph_Executable.rdf_type) in
        if is_class && is_nodeshape then [T_ImplicitClass i] else []
    | RDF_Graph_Executable.S_BNode uu___ -> [] in
  FStar_List_Tot_Base.op_At via_class
    (FStar_List_Tot_Base.op_At via_node
       (FStar_List_Tot_Base.op_At via_subj_of
          (FStar_List_Tot_Base.op_At via_obj_of implicit)))
let collect_shape_ref_list (g : RDF_Graph_Executable.rdf_graph)
  (head : RDF_Graph_Executable.rdf_term) (fuel : Prims.nat) :
  shape_ref Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match term_to_shape_ref t with
       | FStar_Pervasives_Native.Some r -> [r]
       | FStar_Pervasives_Native.None -> []) (rdf_list_terms g head fuel)
let build_constraints (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : constraint_component Prims.list=
  let fuel = (RDF_Graph_Executable.graph_len g) + Prims.int_one in
  let mincount =
    match first_int (RDF_Graph_Executable.find_objects g s sh_minCount) with
    | FStar_Pervasives_Native.Some n -> [CC_MinCount n]
    | FStar_Pervasives_Native.None -> [] in
  let maxcount =
    match first_int (RDF_Graph_Executable.find_objects g s sh_maxCount) with
    | FStar_Pervasives_Native.Some n -> [CC_MaxCount n]
    | FStar_Pervasives_Native.None -> [] in
  let datatype =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [CC_Datatype i]
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_datatype) in
  let nodekind =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i ->
             (match node_kind_of_iri i with
              | FStar_Pervasives_Native.Some nk -> [CC_NodeKind nk]
              | FStar_Pervasives_Native.None -> [])
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_nodeKind) in
  let cls =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [CC_Class i]
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_class) in
  let in_ =
    match RDF_Graph_Executable.find_objects g s sh_in with
    | head::uu___ -> [CC_In (rdf_list_terms g head fuel)]
    | [] -> [] in
  let hasvalue =
    FStar_List_Tot_Base.map (fun t -> CC_HasValue t)
      (RDF_Graph_Executable.find_objects g s sh_hasValue) in
  let pattern =
    match RDF_Graph_Executable.find_objects g s sh_pattern with
    | (RDF_Graph_Executable.T_Literal l)::uu___ ->
        let flags =
          match RDF_Graph_Executable.find_objects g s sh_flags with
          | (RDF_Graph_Executable.T_Literal fl)::uu___1 ->
              fl.RDF_Graph_Executable.lexical_form
          | uu___1 -> "" in
        [CC_Pattern ((l.RDF_Graph_Executable.lexical_form), flags)]
    | uu___ -> [] in
  let minlen =
    match first_int (RDF_Graph_Executable.find_objects g s sh_minLength) with
    | FStar_Pervasives_Native.Some n -> [CC_MinLength n]
    | FStar_Pervasives_Native.None -> [] in
  let maxlen =
    match first_int (RDF_Graph_Executable.find_objects g s sh_maxLength) with
    | FStar_Pervasives_Native.Some n -> [CC_MaxLength n]
    | FStar_Pervasives_Native.None -> [] in
  let langin =
    match RDF_Graph_Executable.find_objects g s sh_languageIn with
    | head::uu___ ->
        let terms = rdf_list_terms g head fuel in
        [CC_LanguageIn
           (FStar_List_Tot_Base.concatMap
              (fun t ->
                 match t with
                 | RDF_Graph_Executable.T_Literal l ->
                     [l.RDF_Graph_Executable.lexical_form]
                 | uu___1 -> []) terms)]
    | [] -> [] in
  let uniquelang =
    match first_bool (RDF_Graph_Executable.find_objects g s sh_uniqueLang)
    with
    | FStar_Pervasives_Native.Some b -> [CC_UniqueLang b]
    | FStar_Pervasives_Native.None -> [] in
  let mininc =
    FStar_List_Tot_Base.map (fun uu___ -> CC_MinInclusive uu___)
      (RDF_Graph_Executable.find_objects g s sh_minInclusive) in
  let maxinc =
    FStar_List_Tot_Base.map (fun uu___ -> CC_MaxInclusive uu___)
      (RDF_Graph_Executable.find_objects g s sh_maxInclusive) in
  let minexc =
    FStar_List_Tot_Base.map (fun uu___ -> CC_MinExclusive uu___)
      (RDF_Graph_Executable.find_objects g s sh_minExclusive) in
  let maxexc =
    FStar_List_Tot_Base.map (fun uu___ -> CC_MaxExclusive uu___)
      (RDF_Graph_Executable.find_objects g s sh_maxExclusive) in
  let nots =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match term_to_shape_ref t with
         | FStar_Pervasives_Native.Some r -> [CC_Not r]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s sh_not) in
  let ands =
    match RDF_Graph_Executable.find_objects g s sh_and with
    | head::uu___ -> [CC_And (collect_shape_ref_list g head fuel)]
    | [] -> [] in
  let ors =
    match RDF_Graph_Executable.find_objects g s sh_or with
    | head::uu___ -> [CC_Or (collect_shape_ref_list g head fuel)]
    | [] -> [] in
  let xones =
    match RDF_Graph_Executable.find_objects g s sh_xone with
    | head::uu___ -> [CC_Xone (collect_shape_ref_list g head fuel)]
    | [] -> [] in
  let nodes =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match term_to_shape_ref t with
         | FStar_Pervasives_Native.Some r -> [CC_Node r]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s sh_node) in
  let equals =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [CC_Equals i]
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_equals) in
  let disjoint =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [CC_Disjoint i]
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_disjoint) in
  let lessthan =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [CC_LessThan i]
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_lessThan) in
  let lessthaneq =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_IRI i -> [CC_LessThanOrEq i]
         | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_lessThanOrEquals) in
  let closed_ =
    match first_bool (RDF_Graph_Executable.find_objects g s sh_closed) with
    | FStar_Pervasives_Native.Some true ->
        let ign =
          match RDF_Graph_Executable.find_objects g s sh_ignoredProperties
          with
          | head::uu___ ->
              FStar_List_Tot_Base.concatMap
                (fun t ->
                   match t with
                   | RDF_Graph_Executable.T_IRI i -> [i]
                   | uu___1 -> []) (rdf_list_terms g head fuel)
          | [] -> [] in
        [CC_Closed ign]
    | uu___ -> [] in
  FStar_List_Tot_Base.op_At mincount
    (FStar_List_Tot_Base.op_At maxcount
       (FStar_List_Tot_Base.op_At datatype
          (FStar_List_Tot_Base.op_At nodekind
             (FStar_List_Tot_Base.op_At cls
                (FStar_List_Tot_Base.op_At in_
                   (FStar_List_Tot_Base.op_At hasvalue
                      (FStar_List_Tot_Base.op_At pattern
                         (FStar_List_Tot_Base.op_At minlen
                            (FStar_List_Tot_Base.op_At maxlen
                               (FStar_List_Tot_Base.op_At langin
                                  (FStar_List_Tot_Base.op_At uniquelang
                                     (FStar_List_Tot_Base.op_At mininc
                                        (FStar_List_Tot_Base.op_At maxinc
                                           (FStar_List_Tot_Base.op_At minexc
                                              (FStar_List_Tot_Base.op_At
                                                 maxexc
                                                 (FStar_List_Tot_Base.op_At
                                                    nots
                                                    (FStar_List_Tot_Base.op_At
                                                       ands
                                                       (FStar_List_Tot_Base.op_At
                                                          ors
                                                          (FStar_List_Tot_Base.op_At
                                                             xones
                                                             (FStar_List_Tot_Base.op_At
                                                                nodes
                                                                (FStar_List_Tot_Base.op_At
                                                                   equals
                                                                   (FStar_List_Tot_Base.op_At
                                                                    disjoint
                                                                    (FStar_List_Tot_Base.op_At
                                                                    lessthan
                                                                    (FStar_List_Tot_Base.op_At
                                                                    lessthaneq
                                                                    closed_))))))))))))))))))))))))
let build_shape (g : RDF_Graph_Executable.rdf_graph)
  (s : RDF_Graph_Executable.subject) : shape=
  let path_objs = RDF_Graph_Executable.find_objects g s sh_path in
  let is_prop = Prims.uu___is_Cons path_objs in
  let path_opt =
    match path_objs with
    | head::uu___ ->
        FStar_Pervasives_Native.Some
          (parse_path g head
             ((RDF_Graph_Executable.graph_len g) + Prims.int_one))
    | [] -> FStar_Pervasives_Native.None in
  let sev =
    match RDF_Graph_Executable.find_objects g s sh_severity with
    | (RDF_Graph_Executable.T_IRI i)::uu___ -> severity_of_iri i
    | uu___ -> Sev_Violation in
  let msg =
    match RDF_Graph_Executable.find_objects g s sh_message with
    | (RDF_Graph_Executable.T_Literal l)::uu___ ->
        FStar_Pervasives_Native.Some (l.RDF_Graph_Executable.lexical_form)
    | uu___ -> FStar_Pervasives_Native.None in
  let prefs =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match term_to_shape_ref t with
         | FStar_Pervasives_Native.Some r -> [r]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s sh_property) in
  {
    shape_id = (subject_to_shape_ref s);
    is_property = is_prop;
    shape_path = path_opt;
    targets = (build_targets g s);
    shape_sev = sev;
    message = msg;
    constraints = (build_constraints g s);
    property_refs = prefs
  }
let parse_shape_from_graph_pure (g : RDF_Graph_Executable.rdf_graph) :
  shapes_graph=
  let subs = distinct_subjects g in
  let shape_subs = FStar_List_Tot_Base.filter (is_shape_establishing g) subs in
  { shapes = (FStar_List_Tot_Base.map (build_shape g) shape_subs) }
let literal_to_scaled (l : RDF_Graph_Executable.literal) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_double
  then
    SPARQL11_Algebra.parse_double_to_scaled
      l.RDF_Graph_Executable.lexical_form
  else
    if
      (l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer) ||
        (l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_decimal)
    then SPARQL11_Algebra.parse_to_scaled l.RDF_Graph_Executable.lexical_form
    else FStar_Pervasives_Native.None
let scaled_cmp (a : (Prims.int * Prims.nat)) (b : (Prims.int * Prims.nat)) :
  Prims.int=
  let uu___ = a in
  match uu___ with
  | (am, asc) ->
      let uu___1 = b in
      (match uu___1 with
       | (bm, bsc) ->
           if asc = bsc
           then
             (if am < bm
              then (Prims.of_int (-1))
              else if am > bm then Prims.int_one else Prims.int_zero)
           else
             if asc < bsc
             then
               (let am' = am * (SPARQL11_Algebra.pow10 (bsc - asc)) in
                if am' < bm
                then (Prims.of_int (-1))
                else if am' > bm then Prims.int_one else Prims.int_zero)
             else
               (let bm' = bm * (SPARQL11_Algebra.pow10 (asc - bsc)) in
                if am < bm'
                then (Prims.of_int (-1))
                else if am > bm' then Prims.int_one else Prims.int_zero))
let numeric_cmp_le (a : RDF_Graph_Executable.literal)
  (b : RDF_Graph_Executable.literal) :
  Prims.bool FStar_Pervasives_Native.option=
  match ((literal_to_scaled a), (literal_to_scaled b)) with
  | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
      FStar_Pervasives_Native.Some ((scaled_cmp sa sb) <= Prims.int_zero)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let numeric_cmp_lt (a : RDF_Graph_Executable.literal)
  (b : RDF_Graph_Executable.literal) :
  Prims.bool FStar_Pervasives_Native.option=
  match ((literal_to_scaled a), (literal_to_scaled b)) with
  | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
      FStar_Pervasives_Native.Some ((scaled_cmp sa sb) < Prims.int_zero)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let term_lt (a : RDF_Graph_Executable.rdf_term)
  (b : RDF_Graph_Executable.rdf_term) : Prims.bool=
  match (a, b) with
  | (RDF_Graph_Executable.T_Literal la, RDF_Graph_Executable.T_Literal lb) ->
      (match ((literal_to_scaled la), (literal_to_scaled lb)) with
       | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb)
           -> (scaled_cmp sa sb) < Prims.int_zero
       | (uu___, uu___1) ->
           if
             la.RDF_Graph_Executable.datatype =
               lb.RDF_Graph_Executable.datatype
           then
             RDF_Graph_Executable.string_lt
               la.RDF_Graph_Executable.lexical_form
               lb.RDF_Graph_Executable.lexical_form
           else false)
  | (uu___, uu___1) -> false
let term_le (a : RDF_Graph_Executable.rdf_term)
  (b : RDF_Graph_Executable.rdf_term) : Prims.bool=
  (term_lt a b) || (RDF_Graph_Executable.rdf_term_eq a b)
let list_diff (a : RDF_Graph_Executable.rdf_term Prims.list)
  (b : RDF_Graph_Executable.rdf_term Prims.list) :
  RDF_Graph_Executable.rdf_term Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun x ->
       if FStar_List_Tot_Base.existsb (RDF_Graph_Executable.rdf_term_eq x) b
       then []
       else [x]) a
let list_set_eq (a : RDF_Graph_Executable.rdf_term Prims.list)
  (b : RDF_Graph_Executable.rdf_term Prims.list) : Prims.bool=
  (Prims.uu___is_Nil (list_diff a b)) && (Prims.uu___is_Nil (list_diff b a))
let list_disjoint (a : RDF_Graph_Executable.rdf_term Prims.list)
  (b : RDF_Graph_Executable.rdf_term Prims.list) : Prims.bool=
  Prims.uu___is_Nil
    (FStar_List_Tot_Base.concatMap
       (fun x ->
          if
            FStar_List_Tot_Base.existsb (RDF_Graph_Executable.rdf_term_eq x)
              b
          then [x]
          else []) a)
let other_property_values (data : RDF_Graph_Executable.rdf_graph)
  (focus : RDF_Graph_Executable.rdf_term) (p : RDF_Graph_Executable.wf_iri) :
  RDF_Graph_Executable.rdf_term Prims.list=
  match RDF_Graph_Executable.term_to_subject focus with
  | FStar_Pervasives_Native.Some s ->
      RDF_Graph_Executable.find_objects data s p
  | FStar_Pervasives_Native.None -> []
let path_predicates_of_shape (sg : shape Prims.list) (s : shape) :
  RDF_Graph_Executable.wf_iri Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun r ->
       match lookup_shape r sg with
       | FStar_Pervasives_Native.Some ps ->
           (match ps.shape_path with
            | FStar_Pervasives_Native.Some (P_Predicate p) -> [p]
            | uu___ -> [])
       | FStar_Pervasives_Native.None -> []) s.property_refs
let closed_ok (data : RDF_Graph_Executable.rdf_graph) (sg : shape Prims.list)
  (focus : RDF_Graph_Executable.rdf_term) (s : shape)
  (ignored : RDF_Graph_Executable.wf_iri Prims.list) : Prims.bool=
  match RDF_Graph_Executable.term_to_subject focus with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some subj ->
      let allowed =
        FStar_List_Tot_Base.op_At (path_predicates_of_shape sg s) ignored in
      FStar_List_Tot_Base.for_all
        (fun t ->
           (Prims.op_Negation
              (RDF_Graph_Executable.subject_eq t.RDF_Graph_Executable.s subj))
             ||
             (FStar_List_Tot_Base.existsb
                (fun p -> p = t.RDF_Graph_Executable.p) allowed)) data
let unique_lang_violates (values : RDF_Graph_Executable.rdf_term Prims.list)
  : Prims.bool=
  let langs =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Graph_Executable.T_Literal l ->
             (match l.RDF_Graph_Executable.lang_tag with
              | FStar_Pervasives_Native.Some lt -> [lt]
              | FStar_Pervasives_Native.None -> [])
         | uu___ -> []) values in
  let rec has_dup seen xs =
    match xs with
    | [] -> false
    | x::rest ->
        if
          FStar_List_Tot_Base.existsb (RDF_Graph_Executable.lang_tag_eq x)
            seen
        then true
        else has_dup (x :: seen) rest in
  has_dup [] langs
let value_violation (focus : RDF_Graph_Executable.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (cc : constraint_component) (sev : severity)
  (msg : Prims.string FStar_Pervasives_Native.option)
  (v : RDF_Graph_Executable.rdf_term) : violation=
  {
    v_focus_node = focus;
    v_path = path_opt;
    v_value = (FStar_Pervasives_Native.Some v);
    v_source_shape = source;
    v_constraint = cc;
    v_severity = sev;
    v_message = msg
  }
let focus_violation (focus : RDF_Graph_Executable.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (cc : constraint_component) (sev : severity)
  (msg : Prims.string FStar_Pervasives_Native.option) : violation=
  {
    v_focus_node = focus;
    v_path = path_opt;
    v_value = FStar_Pervasives_Native.None;
    v_source_shape = source;
    v_constraint = cc;
    v_severity = sev;
    v_message = msg
  }
let eval_aggregate_constraints (data : RDF_Graph_Executable.rdf_graph)
  (sg : shape Prims.list) (focus : RDF_Graph_Executable.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (sev : severity) (msg : Prims.string FStar_Pervasives_Native.option)
  (values : RDF_Graph_Executable.rdf_term Prims.list) (s : shape) :
  violation Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun cc ->
       match cc with
       | CC_MinCount n ->
           if (FStar_List_Tot_Base.length values) < n
           then [focus_violation focus path_opt source cc sev msg]
           else []
       | CC_MaxCount n ->
           if (FStar_List_Tot_Base.length values) > n
           then [focus_violation focus path_opt source cc sev msg]
           else []
       | CC_HasValue t ->
           if
             FStar_List_Tot_Base.existsb (RDF_Graph_Executable.rdf_term_eq t)
               values
           then []
           else [focus_violation focus path_opt source cc sev msg]
       | CC_UniqueLang b ->
           if b && (unique_lang_violates values)
           then [focus_violation focus path_opt source cc sev msg]
           else []
       | CC_Closed ign ->
           if closed_ok data sg focus s ign
           then []
           else [focus_violation focus path_opt source cc sev msg]
       | CC_Equals p ->
           if list_set_eq values (other_property_values data focus p)
           then []
           else [focus_violation focus path_opt source cc sev msg]
       | CC_Disjoint p ->
           if list_disjoint values (other_property_values data focus p)
           then []
           else [focus_violation focus path_opt source cc sev msg]
       | CC_LessThan p ->
           let others = other_property_values data focus p in
           if
             FStar_List_Tot_Base.for_all
               (fun v ->
                  FStar_List_Tot_Base.for_all (fun w -> term_lt v w) others)
               values
           then []
           else [focus_violation focus path_opt source cc sev msg]
       | CC_LessThanOrEq p ->
           let others = other_property_values data focus p in
           if
             FStar_List_Tot_Base.for_all
               (fun v ->
                  FStar_List_Tot_Base.for_all (fun w -> term_le v w) others)
               values
           then []
           else [focus_violation focus path_opt source cc sev msg]
       | uu___ -> []) s.constraints
let rec collect_shape_violations (data : RDF_Graph_Executable.rdf_graph)
  (sg : shape Prims.list) (closed_cls : RDF_Graph_Executable.rdf_graph)
  (node : RDF_Graph_Executable.rdf_term) (s : shape) (fuel : Prims.nat) :
  violation Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      let path_opt = s.shape_path in
      let values =
        if s.is_property
        then
          match path_opt with
          | FStar_Pervasives_Native.Some p -> eval_path data node p
          | FStar_Pervasives_Native.None -> []
        else [node] in
      let per_value =
        FStar_List_Tot_Base.concatMap
          (fun v ->
             FStar_List_Tot_Base.concatMap
               (fun cc ->
                  eval_one_constraint data sg closed_cls node path_opt
                    s.shape_id s.shape_sev s.message v cc fuel')
               s.constraints) values in
      let agg =
        eval_aggregate_constraints data sg node path_opt s.shape_id
          s.shape_sev s.message values s in
      let nested_props =
        FStar_List_Tot_Base.concatMap
          (fun v ->
             FStar_List_Tot_Base.concatMap
               (fun pref ->
                  match lookup_shape pref sg with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some ps ->
                      collect_shape_violations data sg closed_cls v ps fuel')
               s.property_refs) values in
      FStar_List_Tot_Base.op_At per_value
        (FStar_List_Tot_Base.op_At agg nested_props)
and eval_one_constraint (data : RDF_Graph_Executable.rdf_graph)
  (sg : shape Prims.list) (closed_cls : RDF_Graph_Executable.rdf_graph)
  (focus : RDF_Graph_Executable.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (sev : severity) (msg : Prims.string FStar_Pervasives_Native.option)
  (v : RDF_Graph_Executable.rdf_term) (cc : constraint_component)
  (fuel : Prims.nat) : violation Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      let viol uu___1 = [value_violation focus path_opt source cc sev msg v] in
      (match cc with
       | CC_Not r ->
           (match lookup_shape r sg with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some rs ->
                if
                  Prims.uu___is_Nil
                    (collect_shape_violations data sg closed_cls v rs fuel')
                then viol ()
                else [])
       | CC_And rs ->
           if
             FStar_List_Tot_Base.for_all
               (fun r ->
                  match lookup_shape r sg with
                  | FStar_Pervasives_Native.None -> true
                  | FStar_Pervasives_Native.Some s2 ->
                      Prims.uu___is_Nil
                        (collect_shape_violations data sg closed_cls v s2
                           fuel')) rs
           then []
           else viol ()
       | CC_Or rs ->
           if
             FStar_List_Tot_Base.existsb
               (fun r ->
                  match lookup_shape r sg with
                  | FStar_Pervasives_Native.None -> false
                  | FStar_Pervasives_Native.Some s2 ->
                      Prims.uu___is_Nil
                        (collect_shape_violations data sg closed_cls v s2
                           fuel')) rs
           then []
           else viol ()
       | CC_Xone rs ->
           let matches =
             FStar_List_Tot_Base.filter
               (fun r ->
                  match lookup_shape r sg with
                  | FStar_Pervasives_Native.None -> false
                  | FStar_Pervasives_Native.Some s2 ->
                      Prims.uu___is_Nil
                        (collect_shape_violations data sg closed_cls v s2
                           fuel')) rs in
           if (FStar_List_Tot_Base.length matches) = Prims.int_one
           then []
           else viol ()
       | CC_Node r ->
           (match lookup_shape r sg with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some s2 ->
                if
                  Prims.uu___is_Nil
                    (collect_shape_violations data sg closed_cls v s2 fuel')
                then []
                else viol ())
       | CC_Datatype dt ->
           (match v with
            | RDF_Graph_Executable.T_Literal l ->
                if l.RDF_Graph_Executable.datatype = dt then [] else viol ()
            | uu___1 -> viol ())
       | CC_NodeKind nk -> if node_kind_ok v nk then [] else viol ()
       | CC_Class c ->
           (match RDF_Graph_Executable.term_to_subject v with
            | FStar_Pervasives_Native.None -> viol ()
            | FStar_Pervasives_Native.Some subj ->
                if
                  is_shacl_instance closed_cls
                    (RDF_Graph_Executable.subject_to_term subj) c
                then []
                else viol ())
       | CC_In items ->
           if
             FStar_List_Tot_Base.existsb (RDF_Graph_Executable.rdf_term_eq v)
               items
           then []
           else viol ()
       | CC_HasValue uu___1 -> []
       | CC_Pattern (re, flags) ->
           (match term_lexical v with
            | FStar_Pervasives_Native.None -> viol ()
            | FStar_Pervasives_Native.Some lex ->
                if
                  SPARQL11_Algebra.regex_match lex re
                    (if flags = ""
                     then FStar_Pervasives_Native.None
                     else FStar_Pervasives_Native.Some flags)
                then []
                else viol ())
       | CC_MinLength n ->
           (match term_lexical v with
            | FStar_Pervasives_Native.Some lex ->
                if (FStar_String.strlen lex) >= n then [] else viol ()
            | FStar_Pervasives_Native.None -> viol ())
       | CC_MaxLength n ->
           (match term_lexical v with
            | FStar_Pervasives_Native.Some lex ->
                if (FStar_String.strlen lex) <= n then [] else viol ()
            | FStar_Pervasives_Native.None -> viol ())
       | CC_LanguageIn langs ->
           (match v with
            | RDF_Graph_Executable.T_Literal l ->
                (match l.RDF_Graph_Executable.lang_tag with
                 | FStar_Pervasives_Native.Some lt ->
                     if
                       FStar_List_Tot_Base.existsb
                         (RDF_Graph_Executable.lang_tag_eq lt) langs
                     then []
                     else viol ()
                 | FStar_Pervasives_Native.None -> viol ())
            | uu___1 -> viol ())
       | CC_UniqueLang uu___1 -> []
       | CC_MinInclusive t ->
           (match (v, t) with
            | (RDF_Graph_Executable.T_Literal lv,
               RDF_Graph_Executable.T_Literal lt) ->
                (match numeric_cmp_le lt lv with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MaxInclusive t ->
           (match (v, t) with
            | (RDF_Graph_Executable.T_Literal lv,
               RDF_Graph_Executable.T_Literal lt) ->
                (match numeric_cmp_le lv lt with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MinExclusive t ->
           (match (v, t) with
            | (RDF_Graph_Executable.T_Literal lv,
               RDF_Graph_Executable.T_Literal lt) ->
                (match numeric_cmp_lt lt lv with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MaxExclusive t ->
           (match (v, t) with
            | (RDF_Graph_Executable.T_Literal lv,
               RDF_Graph_Executable.T_Literal lt) ->
                (match numeric_cmp_lt lv lt with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MinCount uu___1 -> []
       | CC_MaxCount uu___1 -> []
       | CC_Equals uu___1 -> []
       | CC_Disjoint uu___1 -> []
       | CC_LessThan uu___1 -> []
       | CC_LessThanOrEq uu___1 -> []
       | CC_Closed uu___1 -> []
       | CC_Sparql uu___1 -> [])
let parse_shape_from_graph (g : RDF_Graph_Executable.rdf_graph) :
  shapes_graph= parse_shape_from_graph_pure g
let validate (data : RDF_Graph_Executable.rdf_graph) (shapes : shapes_graph)
  : validation_report=
  let sg = shapes.shapes in
  let closed_cls =
    shacl_class_closure data
      ((RDF_Graph_Executable.graph_len data) + (Prims.of_int (20))) in
  let all_subjects = distinct_subjects data in
  let fuel0 =
    ((FStar_List_Tot_Base.length sg) * (Prims.of_int (4))) +
      (Prims.of_int (50)) in
  let root_shapes =
    FStar_List_Tot_Base.filter (fun s -> Prims.uu___is_Cons s.targets) sg in
  let per_shape_violations =
    FStar_List_Tot_Base.concatMap
      (fun s ->
         let focus_nodes =
           dedup_terms
             (FStar_List_Tot_Base.concatMap
                (fun tgt -> eval_target data closed_cls all_subjects tgt)
                s.targets) in
         FStar_List_Tot_Base.concatMap
           (fun fn -> collect_shape_violations data sg closed_cls fn s fuel0)
           focus_nodes) root_shapes in
  {
    conforms = (Prims.uu___is_Nil per_shape_violations);
    results = per_shape_violations
  }
let eval_sparql_target_select (data : RDF_Graph_Executable.rdf_graph)
  (query : Prims.string) : violation Prims.list=
  failwith "Not yet implemented: SHACL.Validation.eval_sparql_target_select"
