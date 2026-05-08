open Prims
(* SHACL phase-1 stub acknowledgement -- issue #181.
   `validate`, `parse_shape_from_graph`, and
   `eval_sparql_target_select` are extracted as `failwith`
   stubs by design. Phase 2 replaces the first two with pure
   F-star and rewires this patch to realise only the SPARQL
   target call-out. See
     formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
     181_shacl_validate_stub.sh
   for the migration plan. *)
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
let validate (data : RDF_Graph_Executable.rdf_graph) (shapes : shapes_graph)
  : validation_report=
  failwith "Not yet implemented: SHACL.Validation.validate"
let parse_shape_from_graph (g : RDF_Graph_Executable.rdf_graph) :
  shapes_graph=
  failwith "Not yet implemented: SHACL.Validation.parse_shape_from_graph"
let eval_sparql_target_select (data : RDF_Graph_Executable.rdf_graph)
  (query : Prims.string) : violation Prims.list=
  failwith "Not yet implemented: SHACL.Validation.eval_sparql_target_select"
