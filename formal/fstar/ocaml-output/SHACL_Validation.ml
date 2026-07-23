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
let sh_NodeShape : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#NodeShape"
let sh_ShapeClass : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#ShapeClass"
let sh_PropertyShape : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#PropertyShape"
let sh_targetClass : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#targetClass"
let sh_targetNode : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#targetNode"
let sh_targetSubjectsOf : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#targetSubjectsOf"
let sh_targetObjectsOf : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#targetObjectsOf"
let sh_path : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#path"
let sh_select : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#select"
let sh_values : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#values"
let sh_sparqlExpr : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#sparqlExpr"
let sh_Violation : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#Violation"
let sh_ValidationReport : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ValidationReport"
let sh_ValidationResult : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ValidationResult"
let sh_result : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#result"
let sh_detail : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#detail"
let sh_conforms_pred : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#conforms"
let sh_focusNode : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#focusNode"
let sh_resultPath : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#resultPath"
let sh_resultSeverity : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#resultSeverity"
let sh_resultMessage : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#resultMessage"
let sh_sourceConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#sourceConstraintComponent"
let sh_sourceShape : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#sourceShape"
let sh_sourceConstraint : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#sourceConstraint"
let sh_value_pred : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#value"
let sh_MinCountConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MinCountConstraintComponent"
let sh_MaxCountConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MaxCountConstraintComponent"
let sh_DatatypeConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#DatatypeConstraintComponent"
let sh_NodeKindConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#NodeKindConstraintComponent"
let sh_ClassConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ClassConstraintComponent"
let sh_InConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#InConstraintComponent"
let sh_HasValueConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#HasValueConstraintComponent"
let sh_PatternConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#PatternConstraintComponent"
let sh_MinLengthConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MinLengthConstraintComponent"
let sh_MaxLengthConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MaxLengthConstraintComponent"
let sh_SingleLineConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#SingleLineConstraintComponent"
let sh_MinListLengthConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MinListLengthConstraintComponent"
let sh_MaxListLengthConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MaxListLengthConstraintComponent"
let sh_RootClassConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#RootClassConstraintComponent"
let sh_SomeValueConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#SomeValueConstraintComponent"
let sh_UniqueMembersConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#UniqueMembersConstraintComponent"
let sh_MemberShapeConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MemberShapeConstraintComponent"
let sh_UniqueValuesForConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#UniqueValuesForConstraintComponent"
let sh_SubsetOfConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#SubsetOfConstraintComponent"
let sh_ReifierShapeConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ReifierShapeConstraintComponent"
let sh_NodeByExpressionConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#NodeByExpressionConstraintComponent"
let sh_ExpressionConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ExpressionConstraintComponent"
let shv_rdf_reifies : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies"
let sh_LanguageInConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#LanguageInConstraintComponent"
let sh_UniqueLangConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#UniqueLangConstraintComponent"
let sh_MinInclusiveConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MinInclusiveConstraintComponent"
let sh_MaxInclusiveConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MaxInclusiveConstraintComponent"
let sh_MinExclusiveConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MinExclusiveConstraintComponent"
let sh_MaxExclusiveConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#MaxExclusiveConstraintComponent"
let sh_NotConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#NotConstraintComponent"
let sh_AndConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#AndConstraintComponent"
let sh_OrConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#OrConstraintComponent"
let sh_XoneConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#XoneConstraintComponent"
let sh_NodeConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#NodeConstraintComponent"
let sh_QualifiedMinCountConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#QualifiedMinCountConstraintComponent"
let sh_QualifiedMaxCountConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#QualifiedMaxCountConstraintComponent"
let sh_EqualsConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#EqualsConstraintComponent"
let sh_DisjointConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#DisjointConstraintComponent"
let sh_LessThanConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#LessThanConstraintComponent"
let sh_LessThanOrEqualsConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#LessThanOrEqualsConstraintComponent"
let sh_ClosedConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ClosedConstraintComponent"
let sh_SPARQLConstraintComponent : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#SPARQLConstraintComponent"
let sh_sparql : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#sparql"
let sh_prefixes : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#prefixes"
let sh_declare : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#declare"
let sh_ShapesGraph : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ShapesGraph"
let sh_decl_prefix : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#prefix"
let sh_decl_namespace : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#namespace"
let owl_imports_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#imports"
let sh_parameter : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#parameter"
let sh_validator : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#validator"
let sh_nodeValidator : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#nodeValidator"
let sh_propertyValidator : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#propertyValidator"
let sh_ask : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#ask"
let sh_optional : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#optional"
type severity =
  | Sev_Info 
  | Sev_Warning 
  | Sev_Violation 
  | Sev_Custom of RDF_Term.wf_iri 
let uu___is_Sev_Info (projectee : severity) : Prims.bool=
  match projectee with | Sev_Info -> true | uu___ -> false
let uu___is_Sev_Warning (projectee : severity) : Prims.bool=
  match projectee with | Sev_Warning -> true | uu___ -> false
let uu___is_Sev_Violation (projectee : severity) : Prims.bool=
  match projectee with | Sev_Violation -> true | uu___ -> false
let uu___is_Sev_Custom (projectee : severity) : Prims.bool=
  match projectee with | Sev_Custom _0 -> true | uu___ -> false
let __proj__Sev_Custom__item___0 (projectee : severity) : RDF_Term.wf_iri=
  match projectee with | Sev_Custom _0 -> _0
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
  | P_Predicate of RDF_Term.wf_iri 
  | P_Inverse of path 
  | P_Sequence of path Prims.list 
  | P_Alternative of path Prims.list 
  | P_ZeroOrMore of path 
  | P_OneOrMore of path 
  | P_ZeroOrOne of path 
let uu___is_P_Predicate (projectee : path) : Prims.bool=
  match projectee with | P_Predicate _0 -> true | uu___ -> false
let __proj__P_Predicate__item___0 (projectee : path) : RDF_Term.wf_iri=
  match projectee with | P_Predicate _0 -> _0
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
  | T_Class of RDF_Term.wf_iri 
  | T_Node of RDF_Term.rdf_term 
  | T_SubjectsOf of RDF_Term.wf_iri 
  | T_ObjectsOf of RDF_Term.wf_iri 
  | T_ImplicitClass of RDF_Term.wf_iri 
  | T_Sparql of Prims.string 
  | T_DataShape of RDF_Term.wf_iri 
let uu___is_T_Class (projectee : target) : Prims.bool=
  match projectee with | T_Class _0 -> true | uu___ -> false
let __proj__T_Class__item___0 (projectee : target) : RDF_Term.wf_iri=
  match projectee with | T_Class _0 -> _0
let uu___is_T_Node (projectee : target) : Prims.bool=
  match projectee with | T_Node _0 -> true | uu___ -> false
let __proj__T_Node__item___0 (projectee : target) : RDF_Term.rdf_term=
  match projectee with | T_Node _0 -> _0
let uu___is_T_SubjectsOf (projectee : target) : Prims.bool=
  match projectee with | T_SubjectsOf _0 -> true | uu___ -> false
let __proj__T_SubjectsOf__item___0 (projectee : target) : RDF_Term.wf_iri=
  match projectee with | T_SubjectsOf _0 -> _0
let uu___is_T_ObjectsOf (projectee : target) : Prims.bool=
  match projectee with | T_ObjectsOf _0 -> true | uu___ -> false
let __proj__T_ObjectsOf__item___0 (projectee : target) : RDF_Term.wf_iri=
  match projectee with | T_ObjectsOf _0 -> _0
let uu___is_T_ImplicitClass (projectee : target) : Prims.bool=
  match projectee with | T_ImplicitClass _0 -> true | uu___ -> false
let __proj__T_ImplicitClass__item___0 (projectee : target) : RDF_Term.wf_iri=
  match projectee with | T_ImplicitClass _0 -> _0
let uu___is_T_Sparql (projectee : target) : Prims.bool=
  match projectee with | T_Sparql _0 -> true | uu___ -> false
let __proj__T_Sparql__item___0 (projectee : target) : Prims.string=
  match projectee with | T_Sparql _0 -> _0
let uu___is_T_DataShape (projectee : target) : Prims.bool=
  match projectee with | T_DataShape _0 -> true | uu___ -> false
let __proj__T_DataShape__item___0 (projectee : target) : RDF_Term.wf_iri=
  match projectee with | T_DataShape _0 -> _0
type shape_ref = Prims.string
type constraint_component =
  | CC_MinCount of Prims.nat 
  | CC_MaxCount of Prims.nat 
  | CC_Datatype of RDF_Term.wf_iri 
  | CC_NodeKind of node_kind 
  | CC_Class of RDF_Term.wf_iri 
  | CC_DatatypeIn of RDF_Term.wf_iri Prims.list 
  | CC_NodeKindOneOf of node_kind Prims.list 
  | CC_ClassOneOf of RDF_Term.wf_iri Prims.list 
  | CC_In of RDF_Term.rdf_term Prims.list 
  | CC_HasValue of RDF_Term.rdf_term 
  | CC_Pattern of Prims.string * Prims.string 
  | CC_MinLength of Prims.nat 
  | CC_MaxLength of Prims.nat 
  | CC_SingleLine 
  | CC_MinListLength of Prims.nat 
  | CC_MaxListLength of Prims.nat 
  | CC_RootClass of RDF_Term.wf_iri 
  | CC_SomeValue of shape_ref 
  | CC_UniqueMembers 
  | CC_MemberShape of shape_ref 
  | CC_UniqueValuesFor of RDF_Term.wf_iri Prims.list 
  | CC_LanguageIn of Prims.string Prims.list 
  | CC_UniqueLang of Prims.bool 
  | CC_MinInclusive of RDF_Term.rdf_term 
  | CC_MaxInclusive of RDF_Term.rdf_term 
  | CC_MinExclusive of RDF_Term.rdf_term 
  | CC_MaxExclusive of RDF_Term.rdf_term 
  | CC_Not of shape_ref 
  | CC_And of shape_ref Prims.list 
  | CC_Or of shape_ref Prims.list 
  | CC_Xone of shape_ref Prims.list 
  | CC_Node of shape_ref 
  | CC_QualifiedMinCount of shape_ref * Prims.nat * Prims.bool 
  | CC_QualifiedMaxCount of shape_ref * Prims.nat * Prims.bool 
  | CC_Equals of path 
  | CC_Disjoint of path 
  | CC_LessThan of path 
  | CC_LessThanOrEq of path 
  | CC_SubsetOf of path 
  | CC_ReifierShape of shape_ref * Prims.bool 
  | CC_Closed of RDF_Term.wf_iri Prims.list 
  | CC_ClosedByTypes of RDF_Term.wf_iri Prims.list 
  | CC_NodeByExpression of shape_ref 
  | CC_Expression of RDF_Term.rdf_term 
  | CC_Sparql of shape_ref * Prims.string * RDF_Term.wf_literal
  FStar_Pervasives_Native.option 
  | CC_Custom of RDF_Term.wf_iri * Prims.bool * Prims.string * (Prims.string
  * RDF_Term.rdf_term) Prims.list * Prims.string
  FStar_Pervasives_Native.option 
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
  RDF_Term.wf_iri= match projectee with | CC_Datatype _0 -> _0
let uu___is_CC_NodeKind (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_NodeKind _0 -> true | uu___ -> false
let __proj__CC_NodeKind__item___0 (projectee : constraint_component) :
  node_kind= match projectee with | CC_NodeKind _0 -> _0
let uu___is_CC_Class (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Class _0 -> true | uu___ -> false
let __proj__CC_Class__item___0 (projectee : constraint_component) :
  RDF_Term.wf_iri= match projectee with | CC_Class _0 -> _0
let uu___is_CC_DatatypeIn (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_DatatypeIn _0 -> true | uu___ -> false
let __proj__CC_DatatypeIn__item___0 (projectee : constraint_component) :
  RDF_Term.wf_iri Prims.list= match projectee with | CC_DatatypeIn _0 -> _0
let uu___is_CC_NodeKindOneOf (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_NodeKindOneOf _0 -> true | uu___ -> false
let __proj__CC_NodeKindOneOf__item___0 (projectee : constraint_component) :
  node_kind Prims.list= match projectee with | CC_NodeKindOneOf _0 -> _0
let uu___is_CC_ClassOneOf (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_ClassOneOf _0 -> true | uu___ -> false
let __proj__CC_ClassOneOf__item___0 (projectee : constraint_component) :
  RDF_Term.wf_iri Prims.list= match projectee with | CC_ClassOneOf _0 -> _0
let uu___is_CC_In (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_In _0 -> true | uu___ -> false
let __proj__CC_In__item___0 (projectee : constraint_component) :
  RDF_Term.rdf_term Prims.list= match projectee with | CC_In _0 -> _0
let uu___is_CC_HasValue (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_HasValue _0 -> true | uu___ -> false
let __proj__CC_HasValue__item___0 (projectee : constraint_component) :
  RDF_Term.rdf_term= match projectee with | CC_HasValue _0 -> _0
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
let uu___is_CC_SingleLine (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_SingleLine -> true | uu___ -> false
let uu___is_CC_MinListLength (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MinListLength _0 -> true | uu___ -> false
let __proj__CC_MinListLength__item___0 (projectee : constraint_component) :
  Prims.nat= match projectee with | CC_MinListLength _0 -> _0
let uu___is_CC_MaxListLength (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxListLength _0 -> true | uu___ -> false
let __proj__CC_MaxListLength__item___0 (projectee : constraint_component) :
  Prims.nat= match projectee with | CC_MaxListLength _0 -> _0
let uu___is_CC_RootClass (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_RootClass _0 -> true | uu___ -> false
let __proj__CC_RootClass__item___0 (projectee : constraint_component) :
  RDF_Term.wf_iri= match projectee with | CC_RootClass _0 -> _0
let uu___is_CC_SomeValue (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_SomeValue _0 -> true | uu___ -> false
let __proj__CC_SomeValue__item___0 (projectee : constraint_component) :
  shape_ref= match projectee with | CC_SomeValue _0 -> _0
let uu___is_CC_UniqueMembers (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_UniqueMembers -> true | uu___ -> false
let uu___is_CC_MemberShape (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MemberShape _0 -> true | uu___ -> false
let __proj__CC_MemberShape__item___0 (projectee : constraint_component) :
  shape_ref= match projectee with | CC_MemberShape _0 -> _0
let uu___is_CC_UniqueValuesFor (projectee : constraint_component) :
  Prims.bool=
  match projectee with | CC_UniqueValuesFor _0 -> true | uu___ -> false
let __proj__CC_UniqueValuesFor__item___0 (projectee : constraint_component) :
  RDF_Term.wf_iri Prims.list=
  match projectee with | CC_UniqueValuesFor _0 -> _0
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
  RDF_Term.rdf_term= match projectee with | CC_MinInclusive _0 -> _0
let uu___is_CC_MaxInclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxInclusive _0 -> true | uu___ -> false
let __proj__CC_MaxInclusive__item___0 (projectee : constraint_component) :
  RDF_Term.rdf_term= match projectee with | CC_MaxInclusive _0 -> _0
let uu___is_CC_MinExclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MinExclusive _0 -> true | uu___ -> false
let __proj__CC_MinExclusive__item___0 (projectee : constraint_component) :
  RDF_Term.rdf_term= match projectee with | CC_MinExclusive _0 -> _0
let uu___is_CC_MaxExclusive (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_MaxExclusive _0 -> true | uu___ -> false
let __proj__CC_MaxExclusive__item___0 (projectee : constraint_component) :
  RDF_Term.rdf_term= match projectee with | CC_MaxExclusive _0 -> _0
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
let uu___is_CC_QualifiedMinCount (projectee : constraint_component) :
  Prims.bool=
  match projectee with
  | CC_QualifiedMinCount (_0, _1, _2) -> true
  | uu___ -> false
let __proj__CC_QualifiedMinCount__item___0 (projectee : constraint_component)
  : shape_ref= match projectee with | CC_QualifiedMinCount (_0, _1, _2) -> _0
let __proj__CC_QualifiedMinCount__item___1 (projectee : constraint_component)
  : Prims.nat= match projectee with | CC_QualifiedMinCount (_0, _1, _2) -> _1
let __proj__CC_QualifiedMinCount__item___2 (projectee : constraint_component)
  : Prims.bool=
  match projectee with | CC_QualifiedMinCount (_0, _1, _2) -> _2
let uu___is_CC_QualifiedMaxCount (projectee : constraint_component) :
  Prims.bool=
  match projectee with
  | CC_QualifiedMaxCount (_0, _1, _2) -> true
  | uu___ -> false
let __proj__CC_QualifiedMaxCount__item___0 (projectee : constraint_component)
  : shape_ref= match projectee with | CC_QualifiedMaxCount (_0, _1, _2) -> _0
let __proj__CC_QualifiedMaxCount__item___1 (projectee : constraint_component)
  : Prims.nat= match projectee with | CC_QualifiedMaxCount (_0, _1, _2) -> _1
let __proj__CC_QualifiedMaxCount__item___2 (projectee : constraint_component)
  : Prims.bool=
  match projectee with | CC_QualifiedMaxCount (_0, _1, _2) -> _2
let uu___is_CC_Equals (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Equals _0 -> true | uu___ -> false
let __proj__CC_Equals__item___0 (projectee : constraint_component) : 
  path= match projectee with | CC_Equals _0 -> _0
let uu___is_CC_Disjoint (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Disjoint _0 -> true | uu___ -> false
let __proj__CC_Disjoint__item___0 (projectee : constraint_component) : 
  path= match projectee with | CC_Disjoint _0 -> _0
let uu___is_CC_LessThan (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_LessThan _0 -> true | uu___ -> false
let __proj__CC_LessThan__item___0 (projectee : constraint_component) : 
  path= match projectee with | CC_LessThan _0 -> _0
let uu___is_CC_LessThanOrEq (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_LessThanOrEq _0 -> true | uu___ -> false
let __proj__CC_LessThanOrEq__item___0 (projectee : constraint_component) :
  path= match projectee with | CC_LessThanOrEq _0 -> _0
let uu___is_CC_SubsetOf (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_SubsetOf _0 -> true | uu___ -> false
let __proj__CC_SubsetOf__item___0 (projectee : constraint_component) : 
  path= match projectee with | CC_SubsetOf _0 -> _0
let uu___is_CC_ReifierShape (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_ReifierShape (_0, _1) -> true | uu___ -> false
let __proj__CC_ReifierShape__item___0 (projectee : constraint_component) :
  shape_ref= match projectee with | CC_ReifierShape (_0, _1) -> _0
let __proj__CC_ReifierShape__item___1 (projectee : constraint_component) :
  Prims.bool= match projectee with | CC_ReifierShape (_0, _1) -> _1
let uu___is_CC_Closed (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Closed ignored -> true | uu___ -> false
let __proj__CC_Closed__item__ignored (projectee : constraint_component) :
  RDF_Term.wf_iri Prims.list=
  match projectee with | CC_Closed ignored -> ignored
let uu___is_CC_ClosedByTypes (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_ClosedByTypes ignored -> true | uu___ -> false
let __proj__CC_ClosedByTypes__item__ignored
  (projectee : constraint_component) : RDF_Term.wf_iri Prims.list=
  match projectee with | CC_ClosedByTypes ignored -> ignored
let uu___is_CC_NodeByExpression (projectee : constraint_component) :
  Prims.bool=
  match projectee with | CC_NodeByExpression _0 -> true | uu___ -> false
let __proj__CC_NodeByExpression__item___0 (projectee : constraint_component)
  : shape_ref= match projectee with | CC_NodeByExpression _0 -> _0
let uu___is_CC_Expression (projectee : constraint_component) : Prims.bool=
  match projectee with | CC_Expression _0 -> true | uu___ -> false
let __proj__CC_Expression__item___0 (projectee : constraint_component) :
  RDF_Term.rdf_term= match projectee with | CC_Expression _0 -> _0
let uu___is_CC_Sparql (projectee : constraint_component) : Prims.bool=
  match projectee with
  | CC_Sparql (constraint_node, query, message) -> true
  | uu___ -> false
let __proj__CC_Sparql__item__constraint_node
  (projectee : constraint_component) : shape_ref=
  match projectee with
  | CC_Sparql (constraint_node, query, message) -> constraint_node
let __proj__CC_Sparql__item__query (projectee : constraint_component) :
  Prims.string=
  match projectee with | CC_Sparql (constraint_node, query, message) -> query
let __proj__CC_Sparql__item__message (projectee : constraint_component) :
  RDF_Term.wf_literal FStar_Pervasives_Native.option=
  match projectee with
  | CC_Sparql (constraint_node, query, message) -> message
let uu___is_CC_Custom (projectee : constraint_component) : Prims.bool=
  match projectee with
  | CC_Custom (component, is_ask, query, params, msg_tmpl) -> true
  | uu___ -> false
let __proj__CC_Custom__item__component (projectee : constraint_component) :
  RDF_Term.wf_iri=
  match projectee with
  | CC_Custom (component, is_ask, query, params, msg_tmpl) -> component
let __proj__CC_Custom__item__is_ask (projectee : constraint_component) :
  Prims.bool=
  match projectee with
  | CC_Custom (component, is_ask, query, params, msg_tmpl) -> is_ask
let __proj__CC_Custom__item__query (projectee : constraint_component) :
  Prims.string=
  match projectee with
  | CC_Custom (component, is_ask, query, params, msg_tmpl) -> query
let __proj__CC_Custom__item__params (projectee : constraint_component) :
  (Prims.string * RDF_Term.rdf_term) Prims.list=
  match projectee with
  | CC_Custom (component, is_ask, query, params, msg_tmpl) -> params
let __proj__CC_Custom__item__msg_tmpl (projectee : constraint_component) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CC_Custom (component, is_ask, query, params, msg_tmpl) -> msg_tmpl
type shape =
  {
  shape_id: shape_ref ;
  is_property: Prims.bool ;
  shape_path: path FStar_Pervasives_Native.option ;
  targets: target Prims.list ;
  shape_sev: severity ;
  message: RDF_Term.wf_literal FStar_Pervasives_Native.option ;
  constraints: constraint_component Prims.list ;
  constraint_meta:
    (RDF_Term.wf_iri * RDF_Term.rdf_term * severity
      FStar_Pervasives_Native.option * RDF_Term.wf_literal
      FStar_Pervasives_Native.option) Prims.list
    ;
  property_refs: shape_ref Prims.list ;
  target_where: shape_ref Prims.list ;
  values_query: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkshape__item__shape_id (projectee : shape) : shape_ref=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> shape_id
let __proj__Mkshape__item__is_property (projectee : shape) : Prims.bool=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> is_property
let __proj__Mkshape__item__shape_path (projectee : shape) :
  path FStar_Pervasives_Native.option=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> shape_path
let __proj__Mkshape__item__targets (projectee : shape) : target Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> targets
let __proj__Mkshape__item__shape_sev (projectee : shape) : severity=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> shape_sev
let __proj__Mkshape__item__message (projectee : shape) :
  RDF_Term.wf_literal FStar_Pervasives_Native.option=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> message
let __proj__Mkshape__item__constraints (projectee : shape) :
  constraint_component Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> constraints
let __proj__Mkshape__item__constraint_meta (projectee : shape) :
  (RDF_Term.wf_iri * RDF_Term.rdf_term * severity
    FStar_Pervasives_Native.option * RDF_Term.wf_literal
    FStar_Pervasives_Native.option) Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> constraint_meta
let __proj__Mkshape__item__property_refs (projectee : shape) :
  shape_ref Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> property_refs
let __proj__Mkshape__item__target_where (projectee : shape) :
  shape_ref Prims.list=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> target_where
let __proj__Mkshape__item__values_query (projectee : shape) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { shape_id; is_property; shape_path; targets; shape_sev; message;
      constraints; constraint_meta; property_refs; target_where;
      values_query;_} -> values_query
type shapes_graph = {
  shapes: shape Prims.list }
let __proj__Mkshapes_graph__item__shapes (projectee : shapes_graph) :
  shape Prims.list= match projectee with | { shapes;_} -> shapes
let empty_shapes_graph : shapes_graph= { shapes = [] }
type violation =
  {
  v_focus_node: RDF_Term.rdf_term ;
  v_path: path FStar_Pervasives_Native.option ;
  v_value: RDF_Term.rdf_term FStar_Pervasives_Native.option ;
  v_source_shape: shape_ref ;
  v_constraint: constraint_component ;
  v_severity: severity ;
  v_message: RDF_Term.wf_literal FStar_Pervasives_Native.option ;
  v_source_constraint: RDF_Term.rdf_term FStar_Pervasives_Native.option ;
  v_detail: violation Prims.list }
let __proj__Mkviolation__item__v_focus_node (projectee : violation) :
  RDF_Term.rdf_term=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_focus_node
let __proj__Mkviolation__item__v_path (projectee : violation) :
  path FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_path
let __proj__Mkviolation__item__v_value (projectee : violation) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_value
let __proj__Mkviolation__item__v_source_shape (projectee : violation) :
  shape_ref=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} ->
      v_source_shape
let __proj__Mkviolation__item__v_constraint (projectee : violation) :
  constraint_component=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_constraint
let __proj__Mkviolation__item__v_severity (projectee : violation) : severity=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_severity
let __proj__Mkviolation__item__v_message (projectee : violation) :
  RDF_Term.wf_literal FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_message
let __proj__Mkviolation__item__v_source_constraint (projectee : violation) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} ->
      v_source_constraint
let __proj__Mkviolation__item__v_detail (projectee : violation) :
  violation Prims.list=
  match projectee with
  | { v_focus_node; v_path; v_value; v_source_shape; v_constraint;
      v_severity; v_message; v_source_constraint; v_detail;_} -> v_detail
type validation_report =
  {
  conforms: Prims.bool ;
  results: violation Prims.list ;
  report_failure: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkvalidation_report__item__conforms
  (projectee : validation_report) : Prims.bool=
  match projectee with | { conforms; results; report_failure;_} -> conforms
let __proj__Mkvalidation_report__item__results
  (projectee : validation_report) : violation Prims.list=
  match projectee with | { conforms; results; report_failure;_} -> results
let __proj__Mkvalidation_report__item__report_failure
  (projectee : validation_report) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { conforms; results; report_failure;_} -> report_failure
let conforming_report : validation_report=
  {
    conforms = true;
    results = [];
    report_failure = FStar_Pervasives_Native.None
  }
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
    constraint_meta = [];
    property_refs = [];
    target_where = [];
    values_query = FStar_Pervasives_Native.None
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
    constraint_meta = [];
    property_refs = [];
    target_where = [];
    values_query = FStar_Pervasives_Native.None
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
let rec rdf_list_terms (g : RDF_Graph.rdf_graph) (head : RDF_Term.rdf_term)
  (fuel : Prims.nat) : RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | n ->
      (match head with
       | RDF_Term.T_BNode uu___ ->
           (match RDF_Graph.term_to_subject head with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some s ->
                (match ((RDF_Graph_Executable.find_objects g s
                           OWL_Closure.rdf_first),
                         (RDF_Graph_Executable.find_objects g s
                            OWL_Closure.rdf_rest))
                 with
                 | (h::uu___1, r::uu___2) -> h ::
                     (rdf_list_terms g r (n - Prims.int_one))
                 | (uu___1, uu___2) -> []))
       | uu___ -> [])
let rec rdf_list_opt (g : RDF_Graph.rdf_graph) (head : RDF_Term.rdf_term)
  (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list FStar_Pervasives_Native.option=
  if RDF_Term.rdf_term_eq head (RDF_Term.T_IRI OWL_Closure.rdf_nil_iri)
  then FStar_Pervasives_Native.Some []
  else
    (match fuel with
     | uu___1 when uu___1 = Prims.int_zero -> FStar_Pervasives_Native.None
     | n ->
         (match RDF_Graph.term_to_subject head with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some s ->
              (match ((RDF_Graph_Executable.find_objects g s
                         OWL_Closure.rdf_first),
                       (RDF_Graph_Executable.find_objects g s
                          OWL_Closure.rdf_rest))
               with
               | (h::uu___1, r::uu___2) ->
                   (match rdf_list_opt g r (n - Prims.int_one) with
                    | FStar_Pervasives_Native.Some tl ->
                        FStar_Pervasives_Native.Some (h :: tl)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | (uu___1, uu___2) -> FStar_Pervasives_Native.None)))
let has_line_break (str : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun c ->
       let i = FStar_Char.int_of_char c in
       (((i = (Prims.of_int (0x0A))) || (i = (Prims.of_int (0x0B)))) ||
          (i = (Prims.of_int (0x0C))))
         || (i = (Prims.of_int (0x0D)))) (FStar_String.list_of_string str)
let rdf_term_duplicates (xs : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  let rec go seen rest =
    match rest with
    | [] -> []
    | x::tl ->
        if FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq x) seen
        then go seen tl
        else
          if FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq x) tl
          then x :: (go (x :: seen) tl)
          else go (x :: seen) tl in
  go [] xs
let find_reifiers (g : RDF_Graph.rdf_graph) (tt : RDF_Term.rdf_term) :
  RDF_Term.subject Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       if
         (t.RDF_Triple.p = shv_rdf_reifies) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o tt)
       then [t.RDF_Triple.s]
       else []) g
let rec distinct_subjects_acc (g : RDF_Graph.rdf_graph)
  (acc : RDF_Term.subject Prims.list) : RDF_Term.subject Prims.list=
  match g with
  | [] -> acc
  | t::rest ->
      if FStar_List_Tot_Base.existsb (RDF_Term.subject_eq t.RDF_Triple.s) acc
      then distinct_subjects_acc rest acc
      else distinct_subjects_acc rest ((t.RDF_Triple.s) :: acc)
let distinct_subjects (g : RDF_Graph.rdf_graph) :
  RDF_Term.subject Prims.list= distinct_subjects_acc g []
let dedup_terms_acc (acc : RDF_Term.rdf_term Prims.list)
  (t : RDF_Term.rdf_term) : RDF_Term.rdf_term Prims.list=
  if FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq t) acc
  then acc
  else FStar_List_Tot_Base.op_At acc [t]
let dedup_terms (l : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  FStar_List_Tot_Base.fold_left dedup_terms_acc [] l
let term_to_shape_ref (t : RDF_Term.rdf_term) :
  shape_ref FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some i
  | RDF_Term.T_BNode b -> FStar_Pervasives_Native.Some (Prims.strcat "_:" b)
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let subject_to_shape_ref (s : RDF_Term.subject) : shape_ref=
  match s with
  | RDF_Term.S_IRI i -> i
  | RDF_Term.S_BNode b -> Prims.strcat "_:" b
let shape_ref_to_term (r : shape_ref) : RDF_Term.rdf_term=
  if
    ((FStar_String.strlen r) >= (Prims.of_int (2))) &&
      ((FStar_String.sub r Prims.int_zero (Prims.of_int (2))) = "_:")
  then
    RDF_Term.T_BNode
      (FStar_String.sub r (Prims.of_int (2))
         ((FStar_String.strlen r) - (Prims.of_int (2))))
  else if RDF_Term.is_iri r then RDF_Term.T_IRI r else RDF_Term.T_BNode r
let term_lexical (t : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some i
  | RDF_Term.T_BNode uu___ -> FStar_Pervasives_Native.None
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let first_int (l : RDF_Term.rdf_term Prims.list) :
  Prims.nat FStar_Pervasives_Native.option=
  match l with
  | (RDF_Term.T_Literal lit)::uu___ ->
      (match SPARQL11_Algebra.parse_int_string lit.RDF_Term.lexical_form with
       | FStar_Pervasives_Native.Some n ->
           if n >= Prims.int_zero
           then FStar_Pervasives_Native.Some n
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let first_bool (l : RDF_Term.rdf_term Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  match l with
  | (RDF_Term.T_Literal lit)::uu___ ->
      FStar_Pervasives_Native.Some (lit.RDF_Term.lexical_form = "true")
  | uu___ -> FStar_Pervasives_Native.None
let sh_property : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#property"
let sh_node : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#node"
let sh_minCount : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#minCount"
let sh_maxCount : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#maxCount"
let sh_datatype : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#datatype"
let sh_nodeKind : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#nodeKind"
let sh_class : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#class"
let sh_in : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#in"
let sh_hasValue : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#hasValue"
let sh_pattern : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#pattern"
let sh_flags : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#flags"
let sh_minLength : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#minLength"
let sh_maxLength : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#maxLength"
let sh_singleLine : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#singleLine"
let sh_minListLength : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#minListLength"
let sh_maxListLength : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#maxListLength"
let sh_rootClass : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#rootClass"
let sh_someValue : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#someValue"
let sh_uniqueMembers : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#uniqueMembers"
let sh_memberShape : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#memberShape"
let sh_uniqueValuesFor : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#uniqueValuesFor"
let sh_subsetOf : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#subsetOf"
let sh_reifierShape : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#reifierShape"
let sh_reificationRequired : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#reificationRequired"
let sh_ByTypes : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#ByTypes"
let sh_nodeByExpression : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#nodeByExpression"
let sh_expression : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#expression"
let sh_shape_pred : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#shape"
let sh_targetWhere : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#targetWhere"
let sh_languageIn : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#languageIn"
let sh_uniqueLang : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#uniqueLang"
let sh_minInclusive : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#minInclusive"
let sh_maxInclusive : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#maxInclusive"
let sh_minExclusive : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#minExclusive"
let sh_maxExclusive : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#maxExclusive"
let sh_not : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#not"
let sh_and : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#and"
let sh_or : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#or"
let sh_xone : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#xone"
let sh_equals : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#equals"
let sh_disjoint : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#disjoint"
let sh_lessThan : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#lessThan"
let sh_lessThanOrEquals : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#lessThanOrEquals"
let sh_closed : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#closed"
let sh_ignoredProperties : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#ignoredProperties"
let sh_severity : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#severity"
let sh_message : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#message"
let sh_deactivated : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#deactivated"
let sh_Info : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#Info"
let sh_Warning : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#Warning"
let sh_Debug : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#Debug"
let sh_Trace : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#Trace"
let severity_breaks_conformance (sev : severity) : Prims.bool=
  match sev with
  | Sev_Custom i -> Prims.op_Negation ((i = sh_Debug) || (i = sh_Trace))
  | uu___ -> true
let sh_inversePath : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#inversePath"
let sh_alternativePath : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#alternativePath"
let sh_zeroOrMorePath : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#zeroOrMorePath"
let sh_oneOrMorePath : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#oneOrMorePath"
let sh_zeroOrOnePath : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#zeroOrOnePath"
let sh_qualifiedValueShape : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#qualifiedValueShape"
let sh_qualifiedMinCount : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#qualifiedMinCount"
let sh_qualifiedMaxCount : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#qualifiedMaxCount"
let sh_qualifiedValueShapesDisjoint : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#qualifiedValueShapesDisjoint"
let sh_nk_BlankNode : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#BlankNode"
let sh_nk_IRI : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#IRI"
let sh_nk_Literal : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl#Literal"
let sh_nk_BlankNodeOrIRI : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#BlankNodeOrIRI"
let sh_nk_BlankNodeOrLiteral : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#BlankNodeOrLiteral"
let sh_nk_IRIOrLiteral : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl#IRIOrLiteral"
let node_kind_of_iri (i : RDF_Term.wf_iri) :
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
let node_kind_ok (t : RDF_Term.rdf_term) (nk : node_kind) : Prims.bool=
  match (nk, t) with
  | (NK_BlankNode, RDF_Term.T_BNode uu___) -> true
  | (NK_IRI, RDF_Term.T_IRI uu___) -> true
  | (NK_Literal, RDF_Term.T_Literal uu___) -> true
  | (NK_BlankNodeOrIRI, RDF_Term.T_BNode uu___) -> true
  | (NK_BlankNodeOrIRI, RDF_Term.T_IRI uu___) -> true
  | (NK_BlankNodeOrLiteral, RDF_Term.T_BNode uu___) -> true
  | (NK_BlankNodeOrLiteral, RDF_Term.T_Literal uu___) -> true
  | (NK_IRIOrLiteral, RDF_Term.T_IRI uu___) -> true
  | (NK_IRIOrLiteral, RDF_Term.T_Literal uu___) -> true
  | (uu___, uu___1) -> false
let severity_of_iri (i : RDF_Term.wf_iri) : severity=
  if i = sh_Warning
  then Sev_Warning
  else
    if i = sh_Info
    then Sev_Info
    else if i = sh_Violation then Sev_Violation else Sev_Custom i
let rec parse_path (g : RDF_Graph.rdf_graph) (t : RDF_Term.rdf_term)
  (fuel : Prims.nat) : path=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> P_Sequence []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      (match t with
       | RDF_Term.T_IRI i -> P_Predicate i
       | RDF_Term.T_Literal uu___1 -> P_Sequence []
       | RDF_Term.T_TripleTerm (uu___1, uu___2, uu___3) -> P_Sequence []
       | RDF_Term.T_BNode uu___1 ->
           (match RDF_Graph.term_to_subject t with
            | FStar_Pervasives_Native.None -> P_Sequence []
            | FStar_Pervasives_Native.Some s ->
                (match RDF_Graph_Executable.find_objects g s
                         OWL_Closure.rdf_first
                 with
                 | uu___2::uu___3 ->
                     P_Sequence
                       (parse_path_list g (rdf_list_terms g t fuel') fuel')
                 | [] ->
                     (match RDF_Graph_Executable.find_objects g s
                              sh_inversePath
                      with
                      | (RDF_Term.T_IRI ip)::[] -> P_Inverse (P_Predicate ip)
                      | uu___2 ->
                          (match RDF_Graph_Executable.find_objects g s
                                   sh_alternativePath
                           with
                           | alt_head::uu___3 ->
                               P_Alternative
                                 (parse_path_list g
                                    (rdf_list_terms g alt_head fuel') fuel')
                           | [] ->
                               (match RDF_Graph_Executable.find_objects g s
                                        sh_zeroOrMorePath
                                with
                                | zp_term::uu___3 ->
                                    P_ZeroOrMore (parse_path g zp_term fuel')
                                | [] ->
                                    (match RDF_Graph_Executable.find_objects
                                             g s sh_oneOrMorePath
                                     with
                                     | op_term::uu___3 ->
                                         P_OneOrMore
                                           (parse_path g op_term fuel')
                                     | [] ->
                                         (match RDF_Graph_Executable.find_objects
                                                  g s sh_zeroOrOnePath
                                          with
                                          | zop_term::uu___3 ->
                                              P_ZeroOrOne
                                                (parse_path g zop_term fuel')
                                          | [] -> P_Sequence []))))))))
and parse_path_list (g : RDF_Graph.rdf_graph)
  (ts : RDF_Term.rdf_term Prims.list) (fuel : Prims.nat) : path Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      (match ts with
       | [] -> []
       | t::rest -> (parse_path g t fuel') :: (parse_path_list g rest fuel'))
let rec path_invert (p : path) : path=
  match p with
  | P_Predicate i -> P_Inverse (P_Predicate i)
  | P_Inverse p' -> p'
  | P_Sequence ps ->
      P_Sequence (FStar_List_Tot_Base.rev (path_invert_list ps))
  | P_Alternative ps -> P_Alternative (path_invert_list ps)
  | P_ZeroOrMore p' -> P_ZeroOrMore (path_invert p')
  | P_OneOrMore p' -> P_OneOrMore (path_invert p')
  | P_ZeroOrOne p' -> P_ZeroOrOne (path_invert p')
and path_invert_list (ps : path Prims.list) : path Prims.list=
  match ps with
  | [] -> []
  | p::rest -> (path_invert p) :: (path_invert_list rest)
let rec eval_path_fuel (g : RDF_Graph.rdf_graph) (start : RDF_Term.rdf_term)
  (p : path) (fuel : Prims.nat) : RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      (match p with
       | P_Predicate pred ->
           (match RDF_Graph.term_to_subject start with
            | FStar_Pervasives_Native.Some s ->
                RDF_Graph_Executable.find_objects g s pred
            | FStar_Pervasives_Native.None -> [])
       | P_Inverse (P_Predicate pred) ->
           FStar_List_Tot_Base.map RDF_Graph.subject_to_term
             (RDF_Graph_Executable.find_subjects g pred start)
       | P_Inverse p' -> eval_path_fuel g start (path_invert p') fuel'
       | P_Sequence ps -> eval_seq_fuel g [start] ps fuel'
       | P_Alternative ps -> eval_alt_fuel g start ps fuel'
       | P_ZeroOrMore p' ->
           dedup_terms (start ::
             (eval_plus_fuel g (eval_path_fuel g start p' fuel') p' fuel'))
       | P_OneOrMore p' ->
           dedup_terms
             (eval_plus_fuel g (eval_path_fuel g start p' fuel') p' fuel')
       | P_ZeroOrOne p' ->
           dedup_terms (start :: (eval_path_fuel g start p' fuel')))
and eval_seq_fuel (g : RDF_Graph.rdf_graph)
  (starts : RDF_Term.rdf_term Prims.list) (ps : path Prims.list)
  (fuel : Prims.nat) : RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      (match ps with
       | [] -> dedup_terms starts
       | p::rest ->
           let nexts =
             dedup_terms
               (FStar_List_Tot_Base.concatMap
                  (fun s -> eval_path_fuel g s p fuel') starts) in
           eval_seq_fuel g nexts rest fuel')
and eval_alt_fuel (g : RDF_Graph.rdf_graph) (start : RDF_Term.rdf_term)
  (ps : path Prims.list) (fuel : Prims.nat) : RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun p -> eval_path_fuel g start p fuel') ps)
and eval_plus_fuel (g : RDF_Graph.rdf_graph)
  (frontier : RDF_Term.rdf_term Prims.list) (p : path) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> dedup_terms frontier
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      let nexts =
        dedup_terms
          (FStar_List_Tot_Base.concatMap
             (fun s -> eval_path_fuel g s p fuel') frontier) in
      let combined = dedup_terms (FStar_List_Tot_Base.op_At frontier nexts) in
      if
        (FStar_List_Tot_Base.length combined) <=
          (FStar_List_Tot_Base.length frontier)
      then frontier
      else eval_plus_fuel g combined p fuel'
let eval_path (g : RDF_Graph.rdf_graph) (start : RDF_Term.rdf_term)
  (p : path) : RDF_Term.rdf_term Prims.list=
  eval_path_fuel g start p ((RDF_Graph.graph_len g) + (Prims.of_int (50)))
let rec path_to_sparql_expr (p : path) : Prims.string=
  match p with
  | P_Predicate i -> Prims.strcat "<" (Prims.strcat i ">")
  | P_Inverse p' -> Prims.strcat "^" (path_to_sparql_atom p')
  | P_Sequence ps -> path_list_to_sparql "/" ps
  | P_Alternative ps -> path_list_to_sparql "|" ps
  | P_ZeroOrMore p' -> Prims.strcat (path_to_sparql_atom p') "*"
  | P_OneOrMore p' -> Prims.strcat (path_to_sparql_atom p') "+"
  | P_ZeroOrOne p' -> Prims.strcat (path_to_sparql_atom p') "?"
and path_to_sparql_atom (p : path) : Prims.string=
  match p with
  | P_Predicate i -> Prims.strcat "<" (Prims.strcat i ">")
  | P_Inverse p' ->
      Prims.strcat "(^" (Prims.strcat (path_to_sparql_atom p') ")")
  | P_Sequence ps ->
      Prims.strcat "(" (Prims.strcat (path_list_to_sparql "/" ps) ")")
  | P_Alternative ps ->
      Prims.strcat "(" (Prims.strcat (path_list_to_sparql "|" ps) ")")
  | P_ZeroOrMore p' ->
      Prims.strcat "(" (Prims.strcat (path_to_sparql_atom p') "*)")
  | P_OneOrMore p' ->
      Prims.strcat "(" (Prims.strcat (path_to_sparql_atom p') "+)")
  | P_ZeroOrOne p' ->
      Prims.strcat "(" (Prims.strcat (path_to_sparql_atom p') "?)")
and path_list_to_sparql (sep : Prims.string) (ps : path Prims.list) :
  Prims.string=
  match ps with
  | [] -> ""
  | p::[] -> path_to_sparql_atom p
  | p::rest ->
      Prims.strcat (path_to_sparql_atom p)
        (Prims.strcat sep (path_list_to_sparql sep rest))
let shacl_class_closure_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let ig = RDF_Indexed.build_indexed g in
  let g1 = RDFS_Closure.rdfs_rule_subClassOf_trans g ig in
  let ig1 = RDF_Indexed.build_indexed g1 in
  let g2 = RDFS_Closure.rdfs_rule_subClassOf g1 ig1 in
  RDF_Graph.graph_dedup_sort g2
let rec shacl_class_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  if fuel = Prims.int_zero
  then g
  else
    (let fuel' = fuel - Prims.int_one in
     let g' = shacl_class_closure_step g in
     if (RDF_Graph.graph_len g') = (RDF_Graph.graph_len g)
     then g
     else shacl_class_closure g' fuel')
let is_shacl_instance (closed_g : RDF_Graph.rdf_graph)
  (v : RDF_Term.rdf_term) (c : RDF_Term.wf_iri) : Prims.bool=
  match RDF_Graph.term_to_subject v with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some s ->
      RDF_Graph.mem_triple
        {
          RDF_Triple.s = s;
          RDF_Triple.p = RDFS_Closure.rdf_type;
          RDF_Triple.o = (RDF_Term.T_IRI c)
        } closed_g
let eval_target_class (closed_g : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (c : RDF_Term.wf_iri) :
  RDF_Term.rdf_term Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun s ->
       if is_shacl_instance closed_g (RDF_Graph.subject_to_term s) c
       then [RDF_Graph.subject_to_term s]
       else []) all_subjects
let eval_target (data : RDF_Graph.rdf_graph) (closed_g : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (t : target) :
  RDF_Term.rdf_term Prims.list=
  match t with
  | T_Class c -> eval_target_class closed_g all_subjects c
  | T_ImplicitClass c -> eval_target_class closed_g all_subjects c
  | T_Node n -> [n]
  | T_SubjectsOf p ->
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun tr ->
              if tr.RDF_Triple.p = p
              then [RDF_Graph.subject_to_term tr.RDF_Triple.s]
              else []) data)
  | T_ObjectsOf p ->
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun tr -> if tr.RDF_Triple.p = p then [tr.RDF_Triple.o] else [])
           data)
  | T_Sparql q ->
      (match SPARQL11_Parser.parse_sparql q with
       | SPARQL11_Parser.ParseOk (pq, uu___) ->
           let ds = { RDF_Graph.ds_default = data; RDF_Graph.ds_named = [] } in
           let rows = SPARQL11_Algebra.eval_select_query pq data ds in
           dedup_terms
             (FStar_List_Tot_Base.concatMap
                (fun mu ->
                   FStar_List_Tot_Base.concatMap
                     (fun var ->
                        match SPARQL11_Algebra.sm_lookup var mu with
                        | FStar_Pervasives_Native.Some t1 -> [t1]
                        | FStar_Pervasives_Native.None -> [])
                     (SPARQL11_Algebra.sm_domain mu)) rows)
       | uu___ -> [])
  | T_DataShape i ->
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun tr ->
              if
                (tr.RDF_Triple.p = sh_shape_pred) &&
                  (RDF_Term.rdf_term_eq tr.RDF_Triple.o (RDF_Term.T_IRI i))
              then [RDF_Graph.subject_to_term tr.RDF_Triple.s]
              else []) data)
let term_to_sparql_token (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> FStar_String.concat "" ["<"; i; ">"]
  | RDF_Term.T_BNode b -> FStar_String.concat "" ["_:"; b]
  | RDF_Term.T_Literal l ->
      let base = FStar_String.concat "" ["\""; l.RDF_Term.lexical_form; "\""] in
      (match l.RDF_Term.lang_tag with
       | FStar_Pervasives_Native.Some lt ->
           FStar_String.concat "" [base; "@"; lt]
       | FStar_Pervasives_Native.None ->
           FStar_String.concat "" [base; "^^<"; l.RDF_Term.datatype; ">"])
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> "UNDEF"
let rec replace_this_chars (cs : FStar_String.char Prims.list)
  (repl : FStar_String.char Prims.list) : FStar_String.char Prims.list=
  match cs with
  | 36::116::104::105::115::rest ->
      FStar_List_Tot_Base.op_At repl (replace_this_chars rest repl)
  | c::rest -> c :: (replace_this_chars rest repl)
  | [] -> []
let subst_this_text (q : Prims.string) (focus : RDF_Term.rdf_term) :
  Prims.string=
  FStar_String.string_of_list
    (replace_this_chars (FStar_String.list_of_string q)
       (FStar_String.list_of_string (term_to_sparql_token focus)))
let eval_values_query (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (q : Prims.string) :
  RDF_Term.rdf_term Prims.list=
  match SPARQL11_Parser.parse_sparql (subst_this_text q focus) with
  | SPARQL11_Parser.ParseOk (pq, uu___) ->
      let ds = { RDF_Graph.ds_default = data; RDF_Graph.ds_named = [] } in
      let rows = SPARQL11_Algebra.eval_select_query pq data ds in
      dedup_terms
        (FStar_List_Tot_Base.concatMap
           (fun mu ->
              FStar_List_Tot_Base.concatMap
                (fun var ->
                   match SPARQL11_Algebra.sm_lookup var mu with
                   | FStar_Pervasives_Native.Some t -> [t]
                   | FStar_Pervasives_Native.None -> [])
                (SPARQL11_Algebra.sm_domain mu)) rows)
  | uu___ -> []
let sh_ns_prefix : Prims.string= "http://www.w3.org/ns/shacl#"
let has_shacl_ns_prefix (p : Prims.string) : Prims.bool=
  let n = FStar_String.strlen sh_ns_prefix in
  ((FStar_String.strlen p) >= n) &&
    ((FStar_String.sub p Prims.int_zero n) = sh_ns_prefix)
let is_shape_trigger_triple (t : RDF_Triple.triple) : Prims.bool=
  (has_shacl_ns_prefix t.RDF_Triple.p) ||
    ((t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
       ((RDF_Term.rdf_term_eq t.RDF_Triple.o (RDF_Term.T_IRI sh_NodeShape))
          ||
          (RDF_Term.rdf_term_eq t.RDF_Triple.o
             (RDF_Term.T_IRI sh_PropertyShape))))
let is_deactivated (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  Prims.bool=
  match first_bool (RDF_Graph_Executable.find_objects g s sh_deactivated)
  with
  | FStar_Pervasives_Native.Some true -> true
  | uu___ -> false
let is_shape_establishing (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  Prims.bool=
  (FStar_List_Tot_Base.existsb
     (fun t ->
        (RDF_Term.subject_eq t.RDF_Triple.s s) && (is_shape_trigger_triple t))
     g)
    && (Prims.op_Negation (is_deactivated g s))
let build_targets (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  target Prims.list=
  let via_class =
    FStar_List_Tot_Base.concatMap
      (fun t -> match t with | RDF_Term.T_IRI i -> [T_Class i] | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_targetClass) in
  let via_node =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match RDF_Graph.term_to_subject t with
         | FStar_Pervasives_Native.Some ts ->
             (match RDF_Graph_Executable.find_objects g ts sh_select with
              | (RDF_Term.T_Literal l)::uu___ ->
                  [T_Sparql (l.RDF_Term.lexical_form)]
              | uu___ -> [T_Node t])
         | FStar_Pervasives_Native.None -> [T_Node t])
      (RDF_Graph_Executable.find_objects g s sh_targetNode) in
  let via_subj_of =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with | RDF_Term.T_IRI i -> [T_SubjectsOf i] | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_targetSubjectsOf) in
  let via_obj_of =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with | RDF_Term.T_IRI i -> [T_ObjectsOf i] | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_targetObjectsOf) in
  let implicit =
    match s with
    | RDF_Term.S_IRI i ->
        let is_class =
          FStar_List_Tot_Base.existsb
            (fun t ->
               (RDF_Term.rdf_term_eq t
                  (RDF_Term.T_IRI RDFS_Closure.rdfs_Class))
                 ||
                 (RDF_Term.rdf_term_eq t
                    (RDF_Term.T_IRI RDFS_Closure.owl_Class)))
            (RDF_Graph_Executable.find_objects g s RDFS_Closure.rdf_type) in
        let is_nodeshape =
          FStar_List_Tot_Base.existsb
            (fun t -> RDF_Term.rdf_term_eq t (RDF_Term.T_IRI sh_NodeShape))
            (RDF_Graph_Executable.find_objects g s RDFS_Closure.rdf_type) in
        let is_shapeclass =
          FStar_List_Tot_Base.existsb
            (fun t -> RDF_Term.rdf_term_eq t (RDF_Term.T_IRI sh_ShapeClass))
            (RDF_Graph_Executable.find_objects g s RDFS_Closure.rdf_type) in
        if (is_class && is_nodeshape) || is_shapeclass
        then [T_ImplicitClass i]
        else []
    | RDF_Term.S_BNode uu___ -> [] in
  let data_shape =
    match s with
    | RDF_Term.S_IRI i -> [T_DataShape i]
    | RDF_Term.S_BNode uu___ -> [] in
  FStar_List_Tot_Base.op_At via_class
    (FStar_List_Tot_Base.op_At via_node
       (FStar_List_Tot_Base.op_At via_subj_of
          (FStar_List_Tot_Base.op_At via_obj_of
             (FStar_List_Tot_Base.op_At implicit data_shape))))
let collect_shape_ref_list (g : RDF_Graph.rdf_graph)
  (head : RDF_Term.rdf_term) (fuel : Prims.nat) : shape_ref Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match term_to_shape_ref t with
       | FStar_Pervasives_Native.Some r -> [r]
       | FStar_Pervasives_Native.None -> []) (rdf_list_terms g head fuel)
let build_qualified_constraints (g : RDF_Graph.rdf_graph)
  (s : RDF_Term.subject) : constraint_component Prims.list=
  match RDF_Graph_Executable.find_objects g s sh_qualifiedValueShape with
  | qvs_term::uu___ ->
      (match term_to_shape_ref qvs_term with
       | FStar_Pervasives_Native.Some qref ->
           let qdisjoint =
             match first_bool
                     (RDF_Graph_Executable.find_objects g s
                        sh_qualifiedValueShapesDisjoint)
             with
             | FStar_Pervasives_Native.Some b -> b
             | FStar_Pervasives_Native.None -> false in
           let qmin_cc =
             match first_int
                     (RDF_Graph_Executable.find_objects g s
                        sh_qualifiedMinCount)
             with
             | FStar_Pervasives_Native.Some n ->
                 [CC_QualifiedMinCount (qref, n, qdisjoint)]
             | FStar_Pervasives_Native.None -> [] in
           let qmax_cc =
             match first_int
                     (RDF_Graph_Executable.find_objects g s
                        sh_qualifiedMaxCount)
             with
             | FStar_Pervasives_Native.Some n ->
                 [CC_QualifiedMaxCount (qref, n, qdisjoint)]
             | FStar_Pervasives_Native.None -> [] in
           FStar_List_Tot_Base.op_At qmin_cc qmax_cc
       | FStar_Pervasives_Native.None -> [])
  | [] -> []
let rec declares_to_header (g : RDF_Graph.rdf_graph)
  (decls : RDF_Term.rdf_term Prims.list) : Prims.string=
  match decls with
  | [] -> ""
  | d::rest ->
      (match RDF_Graph.term_to_subject d with
       | FStar_Pervasives_Native.None -> declares_to_header g rest
       | FStar_Pervasives_Native.Some ds ->
           let pfx =
             match RDF_Graph_Executable.find_objects g ds sh_decl_prefix with
             | (RDF_Term.T_Literal l)::uu___ ->
                 FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
             | uu___ -> FStar_Pervasives_Native.None in
           let ns =
             match RDF_Graph_Executable.find_objects g ds sh_decl_namespace
             with
             | (RDF_Term.T_Literal l)::uu___ ->
                 FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
             | uu___ -> FStar_Pervasives_Native.None in
           (match (pfx, ns) with
            | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.Some
               n) ->
                FStar_String.concat ""
                  ["PREFIX "; p; ": <"; n; ">\n"; declares_to_header g rest]
            | (uu___, uu___1) -> declares_to_header g rest))
let rec collect_declares (g : RDF_Graph.rdf_graph)
  (frontier : RDF_Term.rdf_term Prims.list)
  (visited : RDF_Term.rdf_term Prims.list) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      (match frontier with
       | [] -> []
       | n::rest ->
           if FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq n) visited
           then collect_declares g rest visited (fuel - Prims.int_one)
           else
             (match RDF_Graph.term_to_subject n with
              | FStar_Pervasives_Native.None ->
                  collect_declares g rest (n :: visited)
                    (fuel - Prims.int_one)
              | FStar_Pervasives_Native.Some ns ->
                  let ds = RDF_Graph_Executable.find_objects g ns sh_declare in
                  let imps =
                    RDF_Graph_Executable.find_objects g ns owl_imports_iri in
                  FStar_List_Tot_Base.op_At ds
                    (collect_declares g (FStar_List_Tot_Base.op_At imps rest)
                       (n :: visited) (fuel - Prims.int_one))))
let prefix_header_for (g : RDF_Graph.rdf_graph)
  (constraint_subj : RDF_Term.subject) : Prims.string=
  let via_nodes =
    RDF_Graph_Executable.find_objects g constraint_subj sh_prefixes in
  let prefix_nodes =
    if Prims.uu___is_Cons via_nodes
    then via_nodes
    else
      FStar_List_Tot_Base.map RDF_Graph.subject_to_term
        (RDF_Graph_Executable.find_subjects g RDFS_Closure.rdf_type
           (RDF_Term.T_IRI sh_ShapesGraph)) in
  let all_declares =
    collect_declares g prefix_nodes []
      ((RDF_Graph.graph_len g) + (Prims.of_int (10))) in
  declares_to_header g all_declares
let build_sparql_constraints (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject)
  : constraint_component Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match RDF_Graph.term_to_subject t with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some cs ->
           let cref = subject_to_shape_ref cs in
           (match RDF_Graph_Executable.find_objects g cs sh_select with
            | (RDF_Term.T_Literal l)::uu___ ->
                let cmsg =
                  match RDF_Graph_Executable.find_objects g cs sh_message
                  with
                  | (RDF_Term.T_Literal ml)::uu___1 ->
                      FStar_Pervasives_Native.Some ml
                  | uu___1 -> FStar_Pervasives_Native.None in
                let hdr = prefix_header_for g cs in
                [CC_Sparql
                   (cref, (Prims.strcat hdr l.RDF_Term.lexical_form), cmsg)]
            | uu___ -> [])) (RDF_Graph_Executable.find_objects g s sh_sparql)
let values_query_for (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  Prims.string FStar_Pervasives_Native.option=
  match RDF_Graph_Executable.find_objects g s sh_values with
  | ve::uu___ ->
      (match RDF_Graph.term_to_subject ve with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some vs ->
           let hdr = prefix_header_for g vs in
           (match RDF_Graph_Executable.find_objects g vs sh_select with
            | (RDF_Term.T_Literal l)::uu___1 ->
                FStar_Pervasives_Native.Some
                  (Prims.strcat hdr l.RDF_Term.lexical_form)
            | uu___1 ->
                (match RDF_Graph_Executable.find_objects g vs sh_sparqlExpr
                 with
                 | (RDF_Term.T_Literal l)::uu___2 ->
                     FStar_Pervasives_Native.Some
                       (FStar_String.concat ""
                          [hdr;
                          "SELECT (";
                          l.RDF_Term.lexical_form;
                          " AS ?value) WHERE {}"])
                 | uu___2 -> FStar_Pervasives_Native.None)))
  | [] -> FStar_Pervasives_Native.None
let rec find_last_name_sep (cs : FStar_Char.char Prims.list)
  (idx : Prims.nat) (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      let ci = FStar_Char.int_of_char c in
      if (ci = (Prims.of_int (35))) || (ci = (Prims.of_int (47)))
      then
        find_last_name_sep rest (idx + Prims.int_one)
          (FStar_Pervasives_Native.Some idx)
      else find_last_name_sep rest (idx + Prims.int_one) last
let local_name_of_iri (iri : Prims.string) : Prims.string=
  match find_last_name_sep (FStar_String.list_of_string iri) Prims.int_zero
          FStar_Pervasives_Native.None
  with
  | FStar_Pervasives_Native.None -> iri
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen iri in
      if (pos + Prims.int_one) >= len
      then ""
      else
        FStar_String.sub iri (pos + Prims.int_one)
          ((len - pos) - Prims.int_one)
let is_custom_component_def (g : RDF_Graph.rdf_graph)
  (subj : RDF_Term.subject) : Prims.bool=
  (Prims.uu___is_Cons (RDF_Graph_Executable.find_objects g subj sh_parameter))
    &&
    (((Prims.uu___is_Cons
         (RDF_Graph_Executable.find_objects g subj sh_validator))
        ||
        (Prims.uu___is_Cons
           (RDF_Graph_Executable.find_objects g subj sh_nodeValidator)))
       ||
       (Prims.uu___is_Cons
          (RDF_Graph_Executable.find_objects g subj sh_propertyValidator)))
type custom_param =
  {
  cp_path: RDF_Term.wf_iri ;
  cp_name: Prims.string ;
  cp_optional: Prims.bool }
let __proj__Mkcustom_param__item__cp_path (projectee : custom_param) :
  RDF_Term.wf_iri=
  match projectee with | { cp_path; cp_name; cp_optional;_} -> cp_path
let __proj__Mkcustom_param__item__cp_name (projectee : custom_param) :
  Prims.string=
  match projectee with | { cp_path; cp_name; cp_optional;_} -> cp_name
let __proj__Mkcustom_param__item__cp_optional (projectee : custom_param) :
  Prims.bool=
  match projectee with | { cp_path; cp_name; cp_optional;_} -> cp_optional
let parse_custom_param (g : RDF_Graph.rdf_graph) (t : RDF_Term.rdf_term) :
  custom_param FStar_Pervasives_Native.option=
  match RDF_Graph.term_to_subject t with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ps ->
      (match RDF_Graph_Executable.find_objects g ps sh_path with
       | (RDF_Term.T_IRI p)::uu___ ->
           let opt =
             match first_bool
                     (RDF_Graph_Executable.find_objects g ps sh_optional)
             with
             | FStar_Pervasives_Native.Some b -> b
             | FStar_Pervasives_Native.None -> false in
           FStar_Pervasives_Native.Some
             {
               cp_path = p;
               cp_name = (local_name_of_iri p);
               cp_optional = opt
             }
       | uu___ -> FStar_Pervasives_Native.None)
let build_custom_params (g : RDF_Graph.rdf_graph)
  (comp_subj : RDF_Term.subject) : custom_param Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       match parse_custom_param g t with
       | FStar_Pervasives_Native.Some cp -> [cp]
       | FStar_Pervasives_Native.None -> [])
    (RDF_Graph_Executable.find_objects g comp_subj sh_parameter)
let rec custom_params_applicable (g : RDF_Graph.rdf_graph)
  (s : RDF_Term.subject) (ps : custom_param Prims.list)
  (any_bound : Prims.bool) :
  ((Prims.string * RDF_Term.rdf_term) Prims.list * Prims.bool)
    FStar_Pervasives_Native.option=
  match ps with
  | [] -> FStar_Pervasives_Native.Some ([], any_bound)
  | p::rest ->
      (match RDF_Graph_Executable.find_objects g s p.cp_path with
       | v::uu___ ->
           (match custom_params_applicable g s rest true with
            | FStar_Pervasives_Native.Some (acc, ab) ->
                FStar_Pervasives_Native.Some ((((p.cp_name), v) :: acc), ab)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | [] ->
           if p.cp_optional
           then custom_params_applicable g s rest any_bound
           else FStar_Pervasives_Native.None)
let component_applies_and_params (g : RDF_Graph.rdf_graph)
  (s : RDF_Term.subject) (params : custom_param Prims.list) :
  (Prims.string * RDF_Term.rdf_term) Prims.list
    FStar_Pervasives_Native.option=
  match custom_params_applicable g s params false with
  | FStar_Pervasives_Native.Some (bindings, true) ->
      FStar_Pervasives_Native.Some bindings
  | uu___ -> FStar_Pervasives_Native.None
let validator_query_of (g : RDF_Graph.rdf_graph)
  (val_term : RDF_Term.rdf_term) :
  (Prims.bool * Prims.string * Prims.string FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  match RDF_Graph.term_to_subject val_term with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some vs ->
      let mtmpl =
        match RDF_Graph_Executable.find_objects g vs sh_message with
        | (RDF_Term.T_Literal l)::uu___ ->
            FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
        | uu___ -> FStar_Pervasives_Native.None in
      (match RDF_Graph_Executable.find_objects g vs sh_ask with
       | (RDF_Term.T_Literal l)::uu___ ->
           FStar_Pervasives_Native.Some
             (true,
               (Prims.strcat (prefix_header_for g vs) l.RDF_Term.lexical_form),
               mtmpl)
       | uu___ ->
           (match RDF_Graph_Executable.find_objects g vs sh_select with
            | (RDF_Term.T_Literal l)::uu___1 ->
                FStar_Pervasives_Native.Some
                  (false,
                    (Prims.strcat (prefix_header_for g vs)
                       l.RDF_Term.lexical_form), mtmpl)
            | uu___1 -> FStar_Pervasives_Native.None))
let choose_validator (g : RDF_Graph.rdf_graph) (comp_subj : RDF_Term.subject)
  (is_property : Prims.bool) :
  (Prims.bool * Prims.string * Prims.string FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  let generic uu___ =
    match RDF_Graph_Executable.find_objects g comp_subj sh_validator with
    | v::uu___1 -> validator_query_of g v
    | [] -> FStar_Pervasives_Native.None in
  let specific =
    if is_property
    then RDF_Graph_Executable.find_objects g comp_subj sh_propertyValidator
    else RDF_Graph_Executable.find_objects g comp_subj sh_nodeValidator in
  match specific with
  | v::uu___ ->
      (match validator_query_of g v with
       | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
       | FStar_Pervasives_Native.None -> generic ())
  | [] -> generic ()
let build_custom_constraints (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject)
  (is_prop : Prims.bool) : constraint_component Prims.list=
  let comp_subjs =
    FStar_List_Tot_Base.filter (is_custom_component_def g)
      (distinct_subjects g) in
  FStar_List_Tot_Base.concatMap
    (fun comp_subj ->
       let params = build_custom_params g comp_subj in
       if Prims.uu___is_Nil params
       then []
       else
         (match component_applies_and_params g s params with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some bindings ->
              (match choose_validator g comp_subj is_prop with
               | FStar_Pervasives_Native.None -> []
               | FStar_Pervasives_Native.Some (is_ask, query_text, mtmpl) ->
                   (match comp_subj with
                    | RDF_Term.S_IRI ci ->
                        [CC_Custom (ci, is_ask, query_text, bindings, mtmpl)]
                    | RDF_Term.S_BNode uu___1 -> [])))) comp_subjs
let reifier_deactivated (g : RDF_Graph.rdf_graph) (tt : RDF_Term.rdf_term) :
  Prims.bool=
  match find_reifiers g tt with
  | [] -> false
  | r::uu___ ->
      (match first_bool
               (RDF_Graph_Executable.find_objects g r sh_deactivated)
       with
       | FStar_Pervasives_Native.Some b -> b
       | FStar_Pervasives_Native.None -> false)
let cc_source_tt (s_subj : RDF_Term.subject) (cc : constraint_component) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match cc with
  | CC_Datatype i ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_TripleTerm (s_subj, sh_datatype, (RDF_Term.T_IRI i)))
  | CC_Class i ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_TripleTerm (s_subj, sh_class, (RDF_Term.T_IRI i)))
  | CC_HasValue t ->
      FStar_Pervasives_Native.Some
        (RDF_Term.T_TripleTerm (s_subj, sh_hasValue, t))
  | uu___ -> FStar_Pervasives_Native.None
let filter_active_constraints (g : RDF_Graph.rdf_graph)
  (s : RDF_Term.subject) (ccs : constraint_component Prims.list) :
  constraint_component Prims.list=
  FStar_List_Tot_Base.filter
    (fun cc ->
       match cc_source_tt s cc with
       | FStar_Pervasives_Native.Some tt ->
           Prims.op_Negation (reifier_deactivated g tt)
       | FStar_Pervasives_Native.None -> true) ccs
let build_constraint_meta (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  (RDF_Term.wf_iri * RDF_Term.rdf_term * severity
    FStar_Pervasives_Native.option * RDF_Term.wf_literal
    FStar_Pervasives_Native.option) Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       if t.RDF_Triple.p = shv_rdf_reifies
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_TripleTerm (ts, tp, to1) ->
             (if RDF_Term.subject_eq ts s
              then
                let sev =
                  match RDF_Graph_Executable.find_objects g t.RDF_Triple.s
                          sh_severity
                  with
                  | (RDF_Term.T_IRI i)::uu___ ->
                      FStar_Pervasives_Native.Some (severity_of_iri i)
                  | uu___ -> FStar_Pervasives_Native.None in
                let msg =
                  match RDF_Graph_Executable.find_objects g t.RDF_Triple.s
                          sh_message
                  with
                  | (RDF_Term.T_Literal l)::uu___ ->
                      FStar_Pervasives_Native.Some l
                  | uu___ -> FStar_Pervasives_Native.None in
                match (sev, msg) with
                | (FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None) -> []
                | (uu___, uu___1) -> [(tp, to1, sev, msg)]
              else [])
         | uu___ -> []
       else []) g
let cc_source_pred_obj (cc : constraint_component) :
  (RDF_Term.wf_iri * RDF_Term.rdf_term) FStar_Pervasives_Native.option=
  match cc with
  | CC_Datatype i ->
      FStar_Pervasives_Native.Some (sh_datatype, (RDF_Term.T_IRI i))
  | CC_Class i -> FStar_Pervasives_Native.Some (sh_class, (RDF_Term.T_IRI i))
  | CC_HasValue t -> FStar_Pervasives_Native.Some (sh_hasValue, t)
  | uu___ -> FStar_Pervasives_Native.None
let constraint_override
  (meta :
    (RDF_Term.wf_iri * RDF_Term.rdf_term * severity
      FStar_Pervasives_Native.option * RDF_Term.wf_literal
      FStar_Pervasives_Native.option) Prims.list)
  (cc : constraint_component) (dsev : severity)
  (dmsg : RDF_Term.wf_literal FStar_Pervasives_Native.option) :
  (severity * RDF_Term.wf_literal FStar_Pervasives_Native.option)=
  match cc_source_pred_obj cc with
  | FStar_Pervasives_Native.None -> (dsev, dmsg)
  | FStar_Pervasives_Native.Some (p, o) ->
      (match FStar_List_Tot_Base.find
               (fun uu___ ->
                  match uu___ with
                  | (mp, mo, uu___1, uu___2) ->
                      (mp = p) && (RDF_Term.rdf_term_eq mo o)) meta
       with
       | FStar_Pervasives_Native.Some (uu___, uu___1, msev, mmsg) ->
           (((match msev with
              | FStar_Pervasives_Native.Some x -> x
              | FStar_Pervasives_Native.None -> dsev)),
             ((match mmsg with
               | FStar_Pervasives_Native.Some x ->
                   FStar_Pervasives_Native.Some x
               | FStar_Pervasives_Native.None -> dmsg)))
       | FStar_Pervasives_Native.None -> (dsev, dmsg))
let build_reifier_constraints (g : RDF_Graph.rdf_graph)
  (s : RDF_Term.subject) : constraint_component Prims.list=
  match RDF_Graph_Executable.find_objects g s sh_reifierShape with
  | t::uu___ ->
      (match term_to_shape_ref t with
       | FStar_Pervasives_Native.Some r ->
           let req =
             match first_bool
                     (RDF_Graph_Executable.find_objects g s
                        sh_reificationRequired)
             with
             | FStar_Pervasives_Native.Some b -> b
             | FStar_Pervasives_Native.None -> false in
           [CC_ReifierShape (r, req)]
       | FStar_Pervasives_Native.None -> [])
  | [] -> []
let build_constraints (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  constraint_component Prims.list=
  let fuel = (RDF_Graph.graph_len g) + Prims.int_one in
  let mincount =
    match first_int (RDF_Graph_Executable.find_objects g s sh_minCount) with
    | FStar_Pervasives_Native.Some n -> [CC_MinCount n]
    | FStar_Pervasives_Native.None -> [] in
  let maxcount =
    match first_int (RDF_Graph_Executable.find_objects g s sh_maxCount) with
    | FStar_Pervasives_Native.Some n -> [CC_MaxCount n]
    | FStar_Pervasives_Native.None -> [] in
  let iris_of_list t =
    FStar_List_Tot_Base.concatMap
      (fun x -> match x with | RDF_Term.T_IRI i -> [i] | uu___ -> [])
      (rdf_list_terms g t fuel) in
  let datatype =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Term.T_IRI i -> [CC_Datatype i]
         | RDF_Term.T_BNode uu___ ->
             (match iris_of_list t with
              | [] -> []
              | dts -> [CC_DatatypeIn dts])
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_datatype) in
  let nodekind =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Term.T_IRI i ->
             (match node_kind_of_iri i with
              | FStar_Pervasives_Native.Some nk -> [CC_NodeKind nk]
              | FStar_Pervasives_Native.None -> [])
         | RDF_Term.T_BNode uu___ ->
             let nks =
               FStar_List_Tot_Base.concatMap
                 (fun x ->
                    match x with
                    | RDF_Term.T_IRI i ->
                        (match node_kind_of_iri i with
                         | FStar_Pervasives_Native.Some nk -> [nk]
                         | FStar_Pervasives_Native.None -> [])
                    | uu___1 -> []) (rdf_list_terms g t fuel) in
             (match nks with | [] -> [] | uu___1 -> [CC_NodeKindOneOf nks])
         | uu___ -> []) (RDF_Graph_Executable.find_objects g s sh_nodeKind) in
  let cls =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Term.T_IRI i -> [CC_Class i]
         | RDF_Term.T_BNode uu___ ->
             (match iris_of_list t with | [] -> [] | cs -> [CC_ClassOneOf cs])
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
    | (RDF_Term.T_Literal l)::uu___ ->
        let flags =
          match RDF_Graph_Executable.find_objects g s sh_flags with
          | (RDF_Term.T_Literal fl)::uu___1 -> fl.RDF_Term.lexical_form
          | uu___1 -> "" in
        [CC_Pattern ((l.RDF_Term.lexical_form), flags)]
    | uu___ -> [] in
  let minlen =
    match first_int (RDF_Graph_Executable.find_objects g s sh_minLength) with
    | FStar_Pervasives_Native.Some n -> [CC_MinLength n]
    | FStar_Pervasives_Native.None -> [] in
  let maxlen =
    match first_int (RDF_Graph_Executable.find_objects g s sh_maxLength) with
    | FStar_Pervasives_Native.Some n -> [CC_MaxLength n]
    | FStar_Pervasives_Native.None -> [] in
  let singleline =
    match first_bool (RDF_Graph_Executable.find_objects g s sh_singleLine)
    with
    | FStar_Pervasives_Native.Some true -> [CC_SingleLine]
    | uu___ -> [] in
  let minlistlen =
    match first_int (RDF_Graph_Executable.find_objects g s sh_minListLength)
    with
    | FStar_Pervasives_Native.Some n -> [CC_MinListLength n]
    | FStar_Pervasives_Native.None -> [] in
  let maxlistlen =
    match first_int (RDF_Graph_Executable.find_objects g s sh_maxListLength)
    with
    | FStar_Pervasives_Native.Some n -> [CC_MaxListLength n]
    | FStar_Pervasives_Native.None -> [] in
  let rootcls =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with | RDF_Term.T_IRI i -> [CC_RootClass i] | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_rootClass) in
  let somevalue =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match term_to_shape_ref t with
         | FStar_Pervasives_Native.Some r -> [CC_SomeValue r]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s sh_someValue) in
  let uniquemembers =
    match first_bool (RDF_Graph_Executable.find_objects g s sh_uniqueMembers)
    with
    | FStar_Pervasives_Native.Some true -> [CC_UniqueMembers]
    | uu___ -> [] in
  let membershape =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match term_to_shape_ref t with
         | FStar_Pervasives_Native.Some r -> [CC_MemberShape r]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s sh_memberShape) in
  let uvf =
    match RDF_Graph_Executable.find_objects g s sh_uniqueValuesFor with
    | [] -> []
    | (RDF_Term.T_IRI i)::uu___ -> [CC_UniqueValuesFor [i]]
    | head::uu___ ->
        (match iris_of_list head with
         | [] -> []
         | ps -> [CC_UniqueValuesFor ps]) in
  let langin =
    match RDF_Graph_Executable.find_objects g s sh_languageIn with
    | head::uu___ ->
        let terms = rdf_list_terms g head fuel in
        [CC_LanguageIn
           (FStar_List_Tot_Base.concatMap
              (fun t ->
                 match t with
                 | RDF_Term.T_Literal l -> [l.RDF_Term.lexical_form]
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
  let qualified = build_qualified_constraints g s in
  let equals =
    FStar_List_Tot_Base.map (fun t -> CC_Equals (parse_path g t fuel))
      (RDF_Graph_Executable.find_objects g s sh_equals) in
  let disjoint =
    FStar_List_Tot_Base.map (fun t -> CC_Disjoint (parse_path g t fuel))
      (RDF_Graph_Executable.find_objects g s sh_disjoint) in
  let lessthan =
    FStar_List_Tot_Base.map (fun t -> CC_LessThan (parse_path g t fuel))
      (RDF_Graph_Executable.find_objects g s sh_lessThan) in
  let lessthaneq =
    FStar_List_Tot_Base.map (fun t -> CC_LessThanOrEq (parse_path g t fuel))
      (RDF_Graph_Executable.find_objects g s sh_lessThanOrEquals) in
  let subsetof =
    FStar_List_Tot_Base.map (fun t -> CC_SubsetOf (parse_path g t fuel))
      (RDF_Graph_Executable.find_objects g s sh_subsetOf) in
  let reifiershape = build_reifier_constraints g s in
  let nodebyexpr =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Term.T_IRI i -> [CC_NodeByExpression i]
         | uu___ -> [])
      (RDF_Graph_Executable.find_objects g s sh_nodeByExpression) in
  let expression =
    FStar_List_Tot_Base.map (fun t -> CC_Expression t)
      (RDF_Graph_Executable.find_objects g s sh_expression) in
  let closed_ =
    let ign =
      match RDF_Graph_Executable.find_objects g s sh_ignoredProperties with
      | head::uu___ ->
          FStar_List_Tot_Base.concatMap
            (fun t -> match t with | RDF_Term.T_IRI i -> [i] | uu___1 -> [])
            (rdf_list_terms g head fuel)
      | [] -> [] in
    match RDF_Graph_Executable.find_objects g s sh_closed with
    | (RDF_Term.T_IRI i)::uu___ ->
        if i = sh_ByTypes then [CC_ClosedByTypes ign] else []
    | objs ->
        (match first_bool objs with
         | FStar_Pervasives_Native.Some true -> [CC_Closed ign]
         | uu___ -> []) in
  let sparqls = build_sparql_constraints g s in
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
                               (FStar_List_Tot_Base.op_At singleline
                                  (FStar_List_Tot_Base.op_At minlistlen
                                     (FStar_List_Tot_Base.op_At maxlistlen
                                        (FStar_List_Tot_Base.op_At rootcls
                                           (FStar_List_Tot_Base.op_At
                                              somevalue
                                              (FStar_List_Tot_Base.op_At
                                                 uniquemembers
                                                 (FStar_List_Tot_Base.op_At
                                                    membershape
                                                    (FStar_List_Tot_Base.op_At
                                                       uvf
                                                       (FStar_List_Tot_Base.op_At
                                                          expression
                                                          (FStar_List_Tot_Base.op_At
                                                             langin
                                                             (FStar_List_Tot_Base.op_At
                                                                uniquelang
                                                                (FStar_List_Tot_Base.op_At
                                                                   mininc
                                                                   (FStar_List_Tot_Base.op_At
                                                                    maxinc
                                                                    (FStar_List_Tot_Base.op_At
                                                                    minexc
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
                                                                    qualified
                                                                    (FStar_List_Tot_Base.op_At
                                                                    equals
                                                                    (FStar_List_Tot_Base.op_At
                                                                    disjoint
                                                                    (FStar_List_Tot_Base.op_At
                                                                    lessthan
                                                                    (FStar_List_Tot_Base.op_At
                                                                    lessthaneq
                                                                    (FStar_List_Tot_Base.op_At
                                                                    subsetof
                                                                    (FStar_List_Tot_Base.op_At
                                                                    reifiershape
                                                                    (FStar_List_Tot_Base.op_At
                                                                    nodebyexpr
                                                                    (FStar_List_Tot_Base.op_At
                                                                    closed_
                                                                    sparqls))))))))))))))))))))))))))))))))))))))
let build_shape (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) : shape=
  let path_objs = RDF_Graph_Executable.find_objects g s sh_path in
  let is_prop = Prims.uu___is_Cons path_objs in
  let path_opt =
    match path_objs with
    | head::uu___ ->
        FStar_Pervasives_Native.Some
          (parse_path g head ((RDF_Graph.graph_len g) + Prims.int_one))
    | [] -> FStar_Pervasives_Native.None in
  let sev =
    match RDF_Graph_Executable.find_objects g s sh_severity with
    | (RDF_Term.T_IRI i)::uu___ -> severity_of_iri i
    | uu___ -> Sev_Violation in
  let msg =
    match RDF_Graph_Executable.find_objects g s sh_message with
    | (RDF_Term.T_Literal l)::uu___ -> FStar_Pervasives_Native.Some l
    | uu___ -> FStar_Pervasives_Native.None in
  let prefs =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match term_to_shape_ref t with
         | FStar_Pervasives_Native.Some r ->
             if
               reifier_deactivated g
                 (RDF_Term.T_TripleTerm (s, sh_property, t))
             then []
             else [r]
         | FStar_Pervasives_Native.None -> [])
      (RDF_Graph_Executable.find_objects g s sh_property) in
  {
    shape_id = (subject_to_shape_ref s);
    is_property = is_prop;
    shape_path = path_opt;
    targets = (build_targets g s);
    shape_sev = sev;
    message = msg;
    constraints =
      (filter_active_constraints g s
         (FStar_List_Tot_Base.op_At (build_constraints g s)
            (build_custom_constraints g s is_prop)));
    constraint_meta = (build_constraint_meta g s);
    property_refs = prefs;
    target_where =
      (FStar_List_Tot_Base.concatMap
         (fun t ->
            match term_to_shape_ref t with
            | FStar_Pervasives_Native.Some r -> [r]
            | FStar_Pervasives_Native.None -> [])
         (RDF_Graph_Executable.find_objects g s sh_targetWhere));
    values_query = (values_query_for g s)
  }
let parse_shape_from_graph_pure (g : RDF_Graph.rdf_graph) : shapes_graph=
  let subs = distinct_subjects g in
  let shape_subs = FStar_List_Tot_Base.filter (is_shape_establishing g) subs in
  { shapes = (FStar_List_Tot_Base.map (build_shape g) shape_subs) }
let literal_to_scaled :
  RDF_Term.literal -> (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  XSD_Datatypes.literal_to_scaled
let scaled_cmp :
  (Prims.int * Prims.nat) -> (Prims.int * Prims.nat) -> Prims.int=
  XSD_Datatypes.scaled_cmp
let numeric_cmp_le :
  RDF_Term.literal ->
    RDF_Term.literal -> Prims.bool FStar_Pervasives_Native.option=
  XSD_Datatypes.numeric_cmp_le
let numeric_cmp_lt :
  RDF_Term.literal ->
    RDF_Term.literal -> Prims.bool FStar_Pervasives_Native.option=
  XSD_Datatypes.numeric_cmp_lt
let literal_ill_formed : RDF_Term.wf_iri -> Prims.string -> Prims.bool=
  XSD_Datatypes.literal_ill_formed
let term_lt (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.bool=
  match (a, b) with
  | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
      (match ((literal_to_scaled la), (literal_to_scaled lb)) with
       | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb)
           -> (scaled_cmp sa sb) < Prims.int_zero
       | (uu___, uu___1) ->
           if la.RDF_Term.datatype = lb.RDF_Term.datatype
           then
             RDF_Graph_Executable.string_lt la.RDF_Term.lexical_form
               lb.RDF_Term.lexical_form
           else false)
  | (uu___, uu___1) -> false
let term_le (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.bool=
  (term_lt a b) || (RDF_Term.rdf_term_eq a b)
let other_property_values (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (p : RDF_Term.wf_iri) :
  RDF_Term.rdf_term Prims.list=
  match RDF_Graph.term_to_subject focus with
  | FStar_Pervasives_Native.Some s ->
      RDF_Graph_Executable.find_objects data s p
  | FStar_Pervasives_Native.None -> []
let qualified_shape_ref_of (cc : constraint_component) :
  shape_ref FStar_Pervasives_Native.option=
  match cc with
  | CC_QualifiedMinCount (r, uu___, uu___1) -> FStar_Pervasives_Native.Some r
  | CC_QualifiedMaxCount (r, uu___, uu___1) -> FStar_Pervasives_Native.Some r
  | uu___ -> FStar_Pervasives_Native.None
let sibling_shape_refs (sg : shape Prims.list) (self_id : shape_ref) :
  shape_ref Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun parent ->
       if
         FStar_List_Tot_Base.existsb (fun r -> r = self_id)
           parent.property_refs
       then
         FStar_List_Tot_Base.filter
           (fun r -> Prims.op_Negation (r = self_id)) parent.property_refs
       else []) sg
let path_predicates_of_shape (sg : shape Prims.list) (s : shape) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun r ->
       match lookup_shape r sg with
       | FStar_Pervasives_Native.Some ps ->
           (match ps.shape_path with
            | FStar_Pervasives_Native.Some (P_Predicate p) -> [p]
            | uu___ -> [])
       | FStar_Pervasives_Native.None -> []) s.property_refs
let shape_closed_by_types (s : shape) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun cc ->
       match cc with | CC_ClosedByTypes uu___ -> true | uu___ -> false)
    s.constraints
let rec shape_and_node_paths (sg : shape Prims.list) (s : shape)
  (fuel : Prims.nat) : RDF_Term.wf_iri Prims.list=
  if fuel = Prims.int_zero
  then path_predicates_of_shape sg s
  else
    (let own = path_predicates_of_shape sg s in
     let node_refs =
       FStar_List_Tot_Base.concatMap
         (fun cc -> match cc with | CC_Node r -> [r] | uu___1 -> [])
         s.constraints in
     let nested =
       FStar_List_Tot_Base.concatMap
         (fun r ->
            match lookup_shape r sg with
            | FStar_Pervasives_Native.Some ns ->
                shape_and_node_paths sg ns (fuel - Prims.int_one)
            | FStar_Pervasives_Native.None -> []) node_refs in
     FStar_List_Tot_Base.op_At own nested)
let shape_applies_to_types (types : RDF_Term.wf_iri Prims.list) (sh : shape)
  : Prims.bool=
  (FStar_List_Tot_Base.existsb (fun ty -> ty = sh.shape_id) types) ||
    (FStar_List_Tot_Base.existsb
       (fun tgt ->
          match tgt with
          | T_Class c -> FStar_List_Tot_Base.existsb (fun ty -> ty = c) types
          | T_ImplicitClass c ->
              FStar_List_Tot_Base.existsb (fun ty -> ty = c) types
          | uu___ -> false) sh.targets)
let duplicated_lang_tags (values : RDF_Term.rdf_term Prims.list) :
  Prims.string Prims.list=
  let langs =
    FStar_List_Tot_Base.concatMap
      (fun t ->
         match t with
         | RDF_Term.T_Literal l ->
             (match l.RDF_Term.lang_tag with
              | FStar_Pervasives_Native.Some lt ->
                  [FStar_String.concat ""
                     [lt;
                     (match l.RDF_Term.direction with
                      | FStar_Pervasives_Native.Some (RDF_Term.Dir_LTR) ->
                          "--ltr"
                      | FStar_Pervasives_Native.Some (RDF_Term.Dir_RTL) ->
                          "--rtl"
                      | FStar_Pervasives_Native.None -> "")]]
              | FStar_Pervasives_Native.None -> [])
         | uu___ -> []) values in
  let count x =
    FStar_List_Tot_Base.length
      (FStar_List_Tot_Base.filter (RDF_Term.lang_tag_eq x) langs) in
  let rec distinct_dups seen xs =
    match xs with
    | [] -> []
    | x::rest ->
        if FStar_List_Tot_Base.existsb (RDF_Term.lang_tag_eq x) seen
        then distinct_dups seen rest
        else
          if (count x) >= (Prims.of_int (2))
          then x :: (distinct_dups (x :: seen) rest)
          else distinct_dups (x :: seen) rest in
  distinct_dups [] langs
let lang_matches_range (tag : Prims.string) (range : Prims.string) :
  Prims.bool=
  let t = FStar_String.lowercase tag in
  let r = FStar_String.lowercase range in
  let tl = FStar_String.strlen t in
  let rl = FStar_String.strlen r in
  (t = r) ||
    (((tl > rl) && ((FStar_String.sub t Prims.int_zero rl) = r)) &&
       ((FStar_String.sub t rl Prims.int_one) = "-"))
let value_violation (focus : RDF_Term.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (cc : constraint_component) (sev : severity)
  (msg : RDF_Term.wf_literal FStar_Pervasives_Native.option)
  (v : RDF_Term.rdf_term) : violation=
  {
    v_focus_node = focus;
    v_path = path_opt;
    v_value = (FStar_Pervasives_Native.Some v);
    v_source_shape = source;
    v_constraint = cc;
    v_severity = sev;
    v_message = msg;
    v_source_constraint = FStar_Pervasives_Native.None;
    v_detail = []
  }
let focus_violation (focus : RDF_Term.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (cc : constraint_component) (sev : severity)
  (msg : RDF_Term.wf_literal FStar_Pervasives_Native.option) : violation=
  {
    v_focus_node = focus;
    v_path = path_opt;
    v_value = FStar_Pervasives_Native.None;
    v_source_shape = source;
    v_constraint = cc;
    v_severity = sev;
    v_message = msg;
    v_source_constraint = FStar_Pervasives_Native.None;
    v_detail = []
  }
let rec collect_shape_violations (data : RDF_Graph.rdf_graph)
  (sg : shape Prims.list) (closed_cls : RDF_Graph.rdf_graph)
  (node : RDF_Term.rdf_term) (s : shape) (fuel : Prims.nat) :
  violation Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      let path_opt = s.shape_path in
      let values =
        if s.is_property
        then
          match s.values_query with
          | FStar_Pervasives_Native.Some q -> eval_values_query data node q
          | FStar_Pervasives_Native.None ->
              (match path_opt with
               | FStar_Pervasives_Native.Some p -> eval_path data node p
               | FStar_Pervasives_Native.None -> [])
        else [node] in
      let per_value =
        FStar_List_Tot_Base.concatMap
          (fun v ->
             FStar_List_Tot_Base.concatMap
               (fun cc ->
                  let uu___1 =
                    constraint_override s.constraint_meta cc s.shape_sev
                      s.message in
                  match uu___1 with
                  | (esev, emsg) ->
                      eval_one_constraint data sg closed_cls node path_opt
                        s.shape_id esev emsg v cc fuel') s.constraints)
          values in
      let agg =
        eval_aggregate_constraints data sg closed_cls node path_opt
          s.shape_id s.shape_sev s.message values s fuel' in
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
and eval_one_constraint (data : RDF_Graph.rdf_graph) (sg : shape Prims.list)
  (closed_cls : RDF_Graph.rdf_graph) (focus : RDF_Term.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (sev : severity) (msg : RDF_Term.wf_literal FStar_Pervasives_Native.option)
  (v : RDF_Term.rdf_term) (cc : constraint_component) (fuel : Prims.nat) :
  violation Prims.list=
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
       | CC_NodeByExpression r ->
           (match lookup_shape r sg with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some s2 ->
                if
                  Prims.uu___is_Nil
                    (collect_shape_violations data sg closed_cls v s2 fuel')
                then []
                else
                  [(let uu___2 =
                      value_violation focus path_opt source cc sev msg v in
                    {
                      v_focus_node = (uu___2.v_focus_node);
                      v_path = (uu___2.v_path);
                      v_value = (uu___2.v_value);
                      v_source_shape = (uu___2.v_source_shape);
                      v_constraint = (uu___2.v_constraint);
                      v_severity = (uu___2.v_severity);
                      v_message = (uu___2.v_message);
                      v_source_constraint =
                        (FStar_Pervasives_Native.Some (shape_ref_to_term r));
                      v_detail = (uu___2.v_detail)
                    })])
       | CC_Expression e ->
           (match e with
            | RDF_Term.T_Literal l ->
                if
                  (l.RDF_Term.datatype = RDF_Term.xsd_boolean) &&
                    (l.RDF_Term.lexical_form = "true")
                then []
                else
                  [(let uu___2 =
                      value_violation focus path_opt source cc sev msg v in
                    {
                      v_focus_node = (uu___2.v_focus_node);
                      v_path = (uu___2.v_path);
                      v_value = (uu___2.v_value);
                      v_source_shape = (uu___2.v_source_shape);
                      v_constraint = (uu___2.v_constraint);
                      v_severity = (uu___2.v_severity);
                      v_message = (uu___2.v_message);
                      v_source_constraint = (FStar_Pervasives_Native.Some e);
                      v_detail = (uu___2.v_detail)
                    })]
            | uu___1 -> [])
       | CC_Datatype dt ->
           (match v with
            | RDF_Term.T_Literal l ->
                if
                  (l.RDF_Term.datatype = dt) &&
                    (Prims.op_Negation
                       (literal_ill_formed dt l.RDF_Term.lexical_form))
                then []
                else viol ()
            | uu___1 -> viol ())
       | CC_NodeKind nk -> if node_kind_ok v nk then [] else viol ()
       | CC_Class c ->
           (match RDF_Graph.term_to_subject v with
            | FStar_Pervasives_Native.None -> viol ()
            | FStar_Pervasives_Native.Some subj ->
                if
                  is_shacl_instance closed_cls
                    (RDF_Graph.subject_to_term subj) c
                then []
                else viol ())
       | CC_DatatypeIn dts ->
           (match v with
            | RDF_Term.T_Literal l ->
                if
                  (FStar_List_Tot_Base.existsb
                     (fun dt -> l.RDF_Term.datatype = dt) dts)
                    &&
                    (Prims.op_Negation
                       (literal_ill_formed l.RDF_Term.datatype
                          l.RDF_Term.lexical_form))
                then []
                else viol ()
            | uu___1 -> viol ())
       | CC_NodeKindOneOf nks ->
           if FStar_List_Tot_Base.existsb (node_kind_ok v) nks
           then []
           else viol ()
       | CC_ClassOneOf cs ->
           (match RDF_Graph.term_to_subject v with
            | FStar_Pervasives_Native.None -> viol ()
            | FStar_Pervasives_Native.Some subj ->
                if
                  FStar_List_Tot_Base.existsb
                    (fun c ->
                       is_shacl_instance closed_cls
                         (RDF_Graph.subject_to_term subj) c) cs
                then []
                else viol ())
       | CC_In items ->
           if FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq v) items
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
       | CC_SingleLine ->
           (match term_lexical v with
            | FStar_Pervasives_Native.Some lex ->
                if has_line_break lex then viol () else []
            | FStar_Pervasives_Native.None -> [])
       | CC_MinListLength n ->
           (match rdf_list_opt data v
                    ((RDF_Graph.graph_len data) + Prims.int_one)
            with
            | FStar_Pervasives_Native.Some terms ->
                if (FStar_List_Tot_Base.length terms) >= n
                then []
                else viol ()
            | FStar_Pervasives_Native.None -> viol ())
       | CC_MaxListLength n ->
           (match rdf_list_opt data v
                    ((RDF_Graph.graph_len data) + Prims.int_one)
            with
            | FStar_Pervasives_Native.Some terms ->
                if (FStar_List_Tot_Base.length terms) <= n
                then []
                else viol ()
            | FStar_Pervasives_Native.None -> viol ())
       | CC_RootClass rc ->
           if RDF_Term.rdf_term_eq v (RDF_Term.T_IRI rc)
           then []
           else
             (match RDF_Graph.term_to_subject v with
              | FStar_Pervasives_Native.Some vs ->
                  if
                    RDF_Graph.mem_triple
                      {
                        RDF_Triple.s = vs;
                        RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                        RDF_Triple.o = (RDF_Term.T_IRI rc)
                      } closed_cls
                  then []
                  else viol ()
              | FStar_Pervasives_Native.None -> viol ())
       | CC_UniqueMembers ->
           (match rdf_list_opt data v
                    ((RDF_Graph.graph_len data) + Prims.int_one)
            with
            | FStar_Pervasives_Native.None -> viol ()
            | FStar_Pervasives_Native.Some terms ->
                (match rdf_term_duplicates terms with
                 | [] -> []
                 | dups ->
                     let details =
                       FStar_List_Tot_Base.map
                         (fun d ->
                            value_violation focus path_opt source cc sev msg
                              d) dups in
                     [(let uu___1 =
                         value_violation focus path_opt source cc sev msg v in
                       {
                         v_focus_node = (uu___1.v_focus_node);
                         v_path = (uu___1.v_path);
                         v_value = (uu___1.v_value);
                         v_source_shape = (uu___1.v_source_shape);
                         v_constraint = (uu___1.v_constraint);
                         v_severity = (uu___1.v_severity);
                         v_message = (uu___1.v_message);
                         v_source_constraint = (uu___1.v_source_constraint);
                         v_detail = details
                       })]))
       | CC_MemberShape r ->
           (match rdf_list_opt data v
                    ((RDF_Graph.graph_len data) + Prims.int_one)
            with
            | FStar_Pervasives_Native.None -> viol ()
            | FStar_Pervasives_Native.Some members ->
                (match lookup_shape r sg with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some ms ->
                     let inner =
                       FStar_List_Tot_Base.concatMap
                         (fun m ->
                            collect_shape_violations data sg closed_cls m ms
                              fuel') members in
                     if Prims.uu___is_Nil inner
                     then []
                     else
                       [(let uu___2 =
                           value_violation focus path_opt source cc sev msg v in
                         {
                           v_focus_node = (uu___2.v_focus_node);
                           v_path = (uu___2.v_path);
                           v_value = (uu___2.v_value);
                           v_source_shape = (uu___2.v_source_shape);
                           v_constraint = (uu___2.v_constraint);
                           v_severity = (uu___2.v_severity);
                           v_message = (uu___2.v_message);
                           v_source_constraint = (uu___2.v_source_constraint);
                           v_detail = inner
                         })]))
       | CC_SomeValue uu___1 -> []
       | CC_UniqueValuesFor uu___1 -> []
       | CC_ReifierShape (r, req) ->
           (match (path_opt, (RDF_Graph.term_to_subject focus)) with
            | (FStar_Pervasives_Native.Some (P_Predicate pp),
               FStar_Pervasives_Native.Some fsubj) ->
                let tt = RDF_Term.T_TripleTerm (fsubj, pp, v) in
                (match find_reifiers data tt with
                 | [] -> if req then viol () else []
                 | reifiers ->
                     (match lookup_shape r sg with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some rs ->
                          if
                            FStar_List_Tot_Base.existsb
                              (fun rf ->
                                 Prims.op_Negation
                                   (Prims.uu___is_Nil
                                      (collect_shape_violations data sg
                                         closed_cls
                                         (RDF_Graph.subject_to_term rf) rs
                                         fuel'))) reifiers
                          then viol ()
                          else []))
            | (uu___1, uu___2) -> [])
       | CC_LanguageIn langs ->
           (match v with
            | RDF_Term.T_Literal l ->
                (match l.RDF_Term.lang_tag with
                 | FStar_Pervasives_Native.Some lt ->
                     if
                       FStar_List_Tot_Base.existsb (lang_matches_range lt)
                         langs
                     then []
                     else viol ()
                 | FStar_Pervasives_Native.None -> viol ())
            | uu___1 -> viol ())
       | CC_UniqueLang uu___1 -> []
       | CC_MinInclusive t ->
           (match (v, t) with
            | (RDF_Term.T_Literal lv, RDF_Term.T_Literal lt) ->
                (match numeric_cmp_le lt lv with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MaxInclusive t ->
           (match (v, t) with
            | (RDF_Term.T_Literal lv, RDF_Term.T_Literal lt) ->
                (match numeric_cmp_le lv lt with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MinExclusive t ->
           (match (v, t) with
            | (RDF_Term.T_Literal lv, RDF_Term.T_Literal lt) ->
                (match numeric_cmp_lt lt lv with
                 | FStar_Pervasives_Native.Some true -> []
                 | uu___1 -> viol ())
            | (uu___1, uu___2) -> viol ())
       | CC_MaxExclusive t ->
           (match (v, t) with
            | (RDF_Term.T_Literal lv, RDF_Term.T_Literal lt) ->
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
       | CC_SubsetOf uu___1 -> []
       | CC_Closed uu___1 -> []
       | CC_ClosedByTypes uu___1 -> []
       | CC_QualifiedMinCount (uu___1, uu___2, uu___3) -> []
       | CC_QualifiedMaxCount (uu___1, uu___2, uu___3) -> []
       | CC_Sparql (uu___1, uu___2, uu___3) -> []
       | CC_Custom (uu___1, uu___2, uu___3, uu___4, uu___5) -> [])
and eval_aggregate_constraints (data : RDF_Graph.rdf_graph)
  (sg : shape Prims.list) (closed_cls : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term)
  (path_opt : path FStar_Pervasives_Native.option) (source : shape_ref)
  (sev : severity) (msg : RDF_Term.wf_literal FStar_Pervasives_Native.option)
  (values : RDF_Term.rdf_term Prims.list) (s : shape) (fuel : Prims.nat) :
  violation Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      let qualifying_count qref qdisjoint =
        match lookup_shape qref sg with
        | FStar_Pervasives_Native.None -> Prims.int_zero
        | FStar_Pervasives_Native.Some qs ->
            let sibling_refs = sibling_shape_refs sg source in
            let sibling_qrefs =
              FStar_List_Tot_Base.concatMap
                (fun r ->
                   match lookup_shape r sg with
                   | FStar_Pervasives_Native.Some sib ->
                       FStar_List_Tot_Base.concatMap
                         (fun cc2 ->
                            match qualified_shape_ref_of cc2 with
                            | FStar_Pervasives_Native.Some sr -> [sr]
                            | FStar_Pervasives_Native.None -> [])
                         sib.constraints
                   | FStar_Pervasives_Native.None -> []) sibling_refs in
            let conforms_q v =
              Prims.uu___is_Nil
                (collect_shape_violations data sg closed_cls v qs fuel') in
            let excluded v =
              qdisjoint &&
                (FStar_List_Tot_Base.existsb
                   (fun sr ->
                      match lookup_shape sr sg with
                      | FStar_Pervasives_Native.Some sqs ->
                          Prims.uu___is_Nil
                            (collect_shape_violations data sg closed_cls v
                               sqs fuel')
                      | FStar_Pervasives_Native.None -> false) sibling_qrefs) in
            FStar_List_Tot_Base.length
              (FStar_List_Tot_Base.filter
                 (fun v -> (conforms_q v) && (Prims.op_Negation (excluded v)))
                 values) in
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
               if FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq t) values
               then []
               else [focus_violation focus path_opt source cc sev msg]
           | CC_UniqueLang b ->
               if b
               then
                 FStar_List_Tot_Base.map
                   (fun _lt ->
                      focus_violation focus path_opt source cc sev msg)
                   (duplicated_lang_tags values)
               else []
           | CC_Closed ign ->
               (match RDF_Graph.term_to_subject focus with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some subj ->
                    let allowed =
                      FStar_List_Tot_Base.op_At
                        (path_predicates_of_shape sg s) ign in
                    FStar_List_Tot_Base.concatMap
                      (fun t ->
                         if
                           (RDF_Term.subject_eq t.RDF_Triple.s subj) &&
                             (Prims.op_Negation
                                (FStar_List_Tot_Base.existsb
                                   (fun p -> p = t.RDF_Triple.p) allowed))
                         then
                           [{
                              v_focus_node = focus;
                              v_path =
                                (FStar_Pervasives_Native.Some
                                   (P_Predicate (t.RDF_Triple.p)));
                              v_value =
                                (FStar_Pervasives_Native.Some
                                   (t.RDF_Triple.o));
                              v_source_shape = source;
                              v_constraint = cc;
                              v_severity = sev;
                              v_message = msg;
                              v_source_constraint =
                                FStar_Pervasives_Native.None;
                              v_detail = []
                            }]
                         else []) data)
           | CC_ClosedByTypes ign ->
               (match RDF_Graph.term_to_subject focus with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some subj ->
                    let types =
                      FStar_List_Tot_Base.concatMap
                        (fun t ->
                           if
                             (RDF_Term.subject_eq t.RDF_Triple.s subj) &&
                               (t.RDF_Triple.p = RDFS_Closure.rdf_type)
                           then
                             match t.RDF_Triple.o with
                             | RDF_Term.T_IRI c -> [c]
                             | uu___1 -> []
                           else []) closed_cls in
                    let allowed = RDFS_Closure.rdf_type ::
                      (FStar_List_Tot_Base.op_At ign
                         (FStar_List_Tot_Base.concatMap
                            (fun sh ->
                               if shape_applies_to_types types sh
                               then
                                 shape_and_node_paths sg sh
                                   ((FStar_List_Tot_Base.length sg) +
                                      Prims.int_one)
                               else []) sg)) in
                    FStar_List_Tot_Base.concatMap
                      (fun t ->
                         if
                           (RDF_Term.subject_eq t.RDF_Triple.s subj) &&
                             (Prims.op_Negation
                                (FStar_List_Tot_Base.existsb
                                   (fun p -> p = t.RDF_Triple.p) allowed))
                         then
                           [{
                              v_focus_node = focus;
                              v_path =
                                (FStar_Pervasives_Native.Some
                                   (P_Predicate (t.RDF_Triple.p)));
                              v_value =
                                (FStar_Pervasives_Native.Some
                                   (t.RDF_Triple.o));
                              v_source_shape = source;
                              v_constraint = cc;
                              v_severity = sev;
                              v_message = msg;
                              v_source_constraint =
                                FStar_Pervasives_Native.None;
                              v_detail = []
                            }]
                         else []) data)
           | CC_Equals p ->
               let others = eval_path data focus p in
               FStar_List_Tot_Base.op_At
                 (FStar_List_Tot_Base.concatMap
                    (fun v ->
                       if
                         FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq v)
                           others
                       then []
                       else
                         [value_violation focus path_opt source cc sev msg v])
                    values)
                 (FStar_List_Tot_Base.concatMap
                    (fun o ->
                       if
                         FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq o)
                           values
                       then []
                       else
                         [value_violation focus path_opt source cc sev msg o])
                    others)
           | CC_Disjoint p ->
               let others = eval_path data focus p in
               FStar_List_Tot_Base.concatMap
                 (fun v ->
                    if
                      FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq v)
                        others
                    then [value_violation focus path_opt source cc sev msg v]
                    else []) values
           | CC_LessThan p ->
               let others = eval_path data focus p in
               FStar_List_Tot_Base.concatMap
                 (fun v ->
                    FStar_List_Tot_Base.concatMap
                      (fun w ->
                         if term_lt v w
                         then []
                         else
                           [value_violation focus path_opt source cc sev msg
                              v]) others) values
           | CC_LessThanOrEq p ->
               let others = eval_path data focus p in
               FStar_List_Tot_Base.concatMap
                 (fun v ->
                    FStar_List_Tot_Base.concatMap
                      (fun w ->
                         if term_le v w
                         then []
                         else
                           [value_violation focus path_opt source cc sev msg
                              v]) others) values
           | CC_SubsetOf p ->
               let others = eval_path data focus p in
               FStar_List_Tot_Base.concatMap
                 (fun v ->
                    if
                      FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq v)
                        others
                    then []
                    else [value_violation focus path_opt source cc sev msg v])
                 values
           | CC_QualifiedMinCount (qref, qmin, qdisjoint) ->
               if (qualifying_count qref qdisjoint) >= qmin
               then []
               else [focus_violation focus path_opt source cc sev msg]
           | CC_QualifiedMaxCount (qref, qmax, qdisjoint) ->
               if (qualifying_count qref qdisjoint) <= qmax
               then []
               else [focus_violation focus path_opt source cc sev msg]
           | CC_SomeValue r ->
               if
                 FStar_List_Tot_Base.existsb
                   (fun v ->
                      match lookup_shape r sg with
                      | FStar_Pervasives_Native.None -> false
                      | FStar_Pervasives_Native.Some s2 ->
                          Prims.uu___is_Nil
                            (collect_shape_violations data sg closed_cls v s2
                               fuel')) values
               then []
               else [focus_violation focus path_opt source cc sev msg]
           | uu___1 -> []) s.constraints
let shape_focus_nodes (data : RDF_Graph.rdf_graph) (sg : shape Prims.list)
  (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (s : shape) :
  RDF_Term.rdf_term Prims.list=
  let via_targets =
    FStar_List_Tot_Base.concatMap
      (fun tgt -> eval_target data closed_cls all_subjects tgt) s.targets in
  let via_where =
    FStar_List_Tot_Base.concatMap
      (fun wref ->
         match lookup_shape wref sg with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some ws ->
             FStar_List_Tot_Base.concatMap
               (fun subj ->
                  let n = RDF_Graph.subject_to_term subj in
                  if
                    Prims.uu___is_Nil
                      (collect_shape_violations data sg closed_cls n ws
                         ((RDF_Graph.graph_len data) + (Prims.of_int (20))))
                  then [n]
                  else []) all_subjects) s.target_where in
  dedup_terms (FStar_List_Tot_Base.op_At via_targets via_where)
let sparql_constraints_of (s : shape) :
  (shape_ref * Prims.string * RDF_Term.wf_literal
    FStar_Pervasives_Native.option) Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun cc ->
       match cc with | CC_Sparql (cref, q, m) -> [(cref, q, m)] | uu___ -> [])
    s.constraints
let substitute_path (q : Prims.string)
  (path_opt : path FStar_Pervasives_Native.option) : Prims.string=
  match path_opt with
  | FStar_Pervasives_Native.Some p ->
      SPARQL11_Algebra.string_replace_literal q "$PATH"
        (path_to_sparql_expr p) FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> q
let subst_var_ps (name : Prims.string) (t : RDF_Term.rdf_term)
  (ps : SPARQL11_Algebra.pattern_subject) : SPARQL11_Algebra.pattern_subject=
  match ps with
  | SPARQL11_Algebra.PS_Var v ->
      if v = name
      then
        (match t with
         | RDF_Term.T_IRI i -> SPARQL11_Algebra.PS_IRI i
         | RDF_Term.T_BNode b -> SPARQL11_Algebra.PS_BNode b
         | RDF_Term.T_Literal uu___ -> ps
         | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> ps)
      else ps
  | uu___ -> ps
let subst_var_pt (name : Prims.string) (t : RDF_Term.rdf_term)
  (pt : SPARQL11_Algebra.pattern_term) : SPARQL11_Algebra.pattern_term=
  match pt with
  | SPARQL11_Algebra.PT_Var v ->
      if v = name
      then
        (match t with
         | RDF_Term.T_IRI i -> SPARQL11_Algebra.PT_IRI i
         | RDF_Term.T_BNode b -> SPARQL11_Algebra.PT_BNode b
         | RDF_Term.T_Literal l -> SPARQL11_Algebra.PT_Literal l
         | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> pt)
      else pt
  | uu___ -> pt
let subst_var_tp (name : Prims.string) (t : RDF_Term.rdf_term)
  (tp : SPARQL11_Algebra.triple_pattern) : SPARQL11_Algebra.triple_pattern=
  {
    SPARQL11_Algebra.tp_s =
      (subst_var_ps name t
         (SPARQL11_Algebra.__proj__Mktriple_pattern__item__tp_s tp));
    SPARQL11_Algebra.tp_p =
      (subst_var_pt name t
         (SPARQL11_Algebra.__proj__Mktriple_pattern__item__tp_p tp));
    SPARQL11_Algebra.tp_o =
      (subst_var_pt name t
         (SPARQL11_Algebra.__proj__Mktriple_pattern__item__tp_o tp))
  }
let term_to_expr_opt (t : RDF_Term.rdf_term) :
  SPARQL11_Algebra.expr FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_IRI i ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IRI i)
  | RDF_Term.T_Literal l ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Literal l)
  | RDF_Term.T_BNode uu___ -> FStar_Pervasives_Native.None
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let rec subst_var_expr (name : Prims.string) (t : RDF_Term.rdf_term)
  (e : SPARQL11_Algebra.expr) : SPARQL11_Algebra.expr=
  match e with
  | SPARQL11_Algebra.E_Var v ->
      if v = name
      then
        (match term_to_expr_opt t with
         | FStar_Pervasives_Native.Some e' -> e'
         | FStar_Pervasives_Native.None -> e)
      else e
  | SPARQL11_Algebra.E_Bound v ->
      if v = name then SPARQL11_Algebra.E_BoolLit true else e
  | SPARQL11_Algebra.E_Arith (op, a, b) ->
      SPARQL11_Algebra.E_Arith
        (op, (subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_UnaryMinus a ->
      SPARQL11_Algebra.E_UnaryMinus (subst_var_expr name t a)
  | SPARQL11_Algebra.E_UnaryPlus a ->
      SPARQL11_Algebra.E_UnaryPlus (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Compare (op, a, b) ->
      SPARQL11_Algebra.E_Compare
        (op, (subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_And (a, b) ->
      SPARQL11_Algebra.E_And
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_Or (a, b) ->
      SPARQL11_Algebra.E_Or
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_Not a ->
      SPARQL11_Algebra.E_Not (subst_var_expr name t a)
  | SPARQL11_Algebra.E_IsIRI a ->
      SPARQL11_Algebra.E_IsIRI (subst_var_expr name t a)
  | SPARQL11_Algebra.E_IsBlank a ->
      SPARQL11_Algebra.E_IsBlank (subst_var_expr name t a)
  | SPARQL11_Algebra.E_IsLiteral a ->
      SPARQL11_Algebra.E_IsLiteral (subst_var_expr name t a)
  | SPARQL11_Algebra.E_IsNumeric a ->
      SPARQL11_Algebra.E_IsNumeric (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Str a ->
      SPARQL11_Algebra.E_Str (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Lang a ->
      SPARQL11_Algebra.E_Lang (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Datatype a ->
      SPARQL11_Algebra.E_Datatype (subst_var_expr name t a)
  | SPARQL11_Algebra.E_IRI_fn a ->
      SPARQL11_Algebra.E_IRI_fn (subst_var_expr name t a)
  | SPARQL11_Algebra.E_HasLang a ->
      SPARQL11_Algebra.E_HasLang (subst_var_expr name t a)
  | SPARQL11_Algebra.E_HasLangDir a ->
      SPARQL11_Algebra.E_HasLangDir (subst_var_expr name t a)
  | SPARQL11_Algebra.E_LangDir a ->
      SPARQL11_Algebra.E_LangDir (subst_var_expr name t a)
  | SPARQL11_Algebra.E_StrDt (a, b) ->
      SPARQL11_Algebra.E_StrDt
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_StrLang (a, b) ->
      SPARQL11_Algebra.E_StrLang
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_StrLangDir (a, b, c) ->
      SPARQL11_Algebra.E_StrLangDir
        ((subst_var_expr name t a), (subst_var_expr name t b),
          (subst_var_expr name t c))
  | SPARQL11_Algebra.E_If (a, b, c) ->
      SPARQL11_Algebra.E_If
        ((subst_var_expr name t a), (subst_var_expr name t b),
          (subst_var_expr name t c))
  | SPARQL11_Algebra.E_Coalesce es ->
      SPARQL11_Algebra.E_Coalesce (subst_var_exprs name t es)
  | SPARQL11_Algebra.E_In (a, es) ->
      SPARQL11_Algebra.E_In
        ((subst_var_expr name t a), (subst_var_exprs name t es))
  | SPARQL11_Algebra.E_NotIn (a, es) ->
      SPARQL11_Algebra.E_NotIn
        ((subst_var_expr name t a), (subst_var_exprs name t es))
  | SPARQL11_Algebra.E_StrLen a ->
      SPARQL11_Algebra.E_StrLen (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Substr (a, b, c) ->
      SPARQL11_Algebra.E_Substr
        ((subst_var_expr name t a), (subst_var_expr name t b),
          ((match c with
            | FStar_Pervasives_Native.Some x ->
                FStar_Pervasives_Native.Some (subst_var_expr name t x)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)))
  | SPARQL11_Algebra.E_UCase a ->
      SPARQL11_Algebra.E_UCase (subst_var_expr name t a)
  | SPARQL11_Algebra.E_LCase a ->
      SPARQL11_Algebra.E_LCase (subst_var_expr name t a)
  | SPARQL11_Algebra.E_StrStarts (a, b) ->
      SPARQL11_Algebra.E_StrStarts
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_StrEnds (a, b) ->
      SPARQL11_Algebra.E_StrEnds
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_Contains (a, b) ->
      SPARQL11_Algebra.E_Contains
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_StrBefore (a, b) ->
      SPARQL11_Algebra.E_StrBefore
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_StrAfter (a, b) ->
      SPARQL11_Algebra.E_StrAfter
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_Concat es ->
      SPARQL11_Algebra.E_Concat (subst_var_exprs name t es)
  | SPARQL11_Algebra.E_EncodeForUri a ->
      SPARQL11_Algebra.E_EncodeForUri (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Replace (a, b, c, fl) ->
      SPARQL11_Algebra.E_Replace
        ((subst_var_expr name t a), (subst_var_expr name t b),
          (subst_var_expr name t c),
          ((match fl with
            | FStar_Pervasives_Native.Some x ->
                FStar_Pervasives_Native.Some (subst_var_expr name t x)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)))
  | SPARQL11_Algebra.E_Regex (a, b, fl) ->
      SPARQL11_Algebra.E_Regex
        ((subst_var_expr name t a), (subst_var_expr name t b),
          ((match fl with
            | FStar_Pervasives_Native.Some x ->
                FStar_Pervasives_Native.Some (subst_var_expr name t x)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)))
  | SPARQL11_Algebra.E_Abs a ->
      SPARQL11_Algebra.E_Abs (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Round a ->
      SPARQL11_Algebra.E_Round (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Ceil a ->
      SPARQL11_Algebra.E_Ceil (subst_var_expr name t a)
  | SPARQL11_Algebra.E_Floor a ->
      SPARQL11_Algebra.E_Floor (subst_var_expr name t a)
  | SPARQL11_Algebra.E_SameTerm (a, b) ->
      SPARQL11_Algebra.E_SameTerm
        ((subst_var_expr name t a), (subst_var_expr name t b))
  | SPARQL11_Algebra.E_Exists p ->
      SPARQL11_Algebra.E_Exists (subst_var_gp name t p)
  | SPARQL11_Algebra.E_NotExists p ->
      SPARQL11_Algebra.E_NotExists (subst_var_gp name t p)
  | SPARQL11_Algebra.E_FunctionCall (f, es) ->
      SPARQL11_Algebra.E_FunctionCall (f, (subst_var_exprs name t es))
  | uu___ -> e
and subst_var_exprs (name : Prims.string) (t : RDF_Term.rdf_term)
  (es : SPARQL11_Algebra.expr Prims.list) : SPARQL11_Algebra.expr Prims.list=
  match es with
  | [] -> []
  | e::rest -> (subst_var_expr name t e) :: (subst_var_exprs name t rest)
and subst_var_bgp (name : Prims.string) (t : RDF_Term.rdf_term)
  (bgp : SPARQL11_Algebra.triple_pattern Prims.list) :
  SPARQL11_Algebra.triple_pattern Prims.list=
  match bgp with
  | [] -> []
  | tp::rest -> (subst_var_tp name t tp) :: (subst_var_bgp name t rest)
and subst_var_gp (name : Prims.string) (t : RDF_Term.rdf_term)
  (p : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match p with
  | SPARQL11_Algebra.GP_BGP bgp ->
      SPARQL11_Algebra.GP_BGP (subst_var_bgp name t bgp)
  | SPARQL11_Algebra.GP_Join (a, b) ->
      SPARQL11_Algebra.GP_Join
        ((subst_var_gp name t a), (subst_var_gp name t b))
  | SPARQL11_Algebra.GP_LeftJoin (a, b, e) ->
      SPARQL11_Algebra.GP_LeftJoin
        ((subst_var_gp name t a), (subst_var_gp name t b),
          (subst_var_expr name t e))
  | SPARQL11_Algebra.GP_Filter (e, a) ->
      SPARQL11_Algebra.GP_Filter
        ((subst_var_expr name t e), (subst_var_gp name t a))
  | SPARQL11_Algebra.GP_Union (a, b) ->
      SPARQL11_Algebra.GP_Union
        ((subst_var_gp name t a), (subst_var_gp name t b))
  | SPARQL11_Algebra.GP_Graph (pt, a) ->
      SPARQL11_Algebra.GP_Graph
        ((subst_var_pt name t pt), (subst_var_gp name t a))
  | SPARQL11_Algebra.GP_Minus (a, b) ->
      SPARQL11_Algebra.GP_Minus
        ((subst_var_gp name t a), (subst_var_gp name t b))
  | SPARQL11_Algebra.GP_Bind (e, v, a) ->
      SPARQL11_Algebra.GP_Bind
        ((subst_var_expr name t e), v, (subst_var_gp name t a))
  | SPARQL11_Algebra.GP_SubSelect q ->
      SPARQL11_Algebra.GP_SubSelect
        (SPARQL11_Algebra.query_with_pattern q
           (subst_var_gp name t
              (SPARQL11_Algebra.__proj__Mkquery__item__q_pattern q)))
  | SPARQL11_Algebra.GP_PropertyPath (ps, pp, pt) ->
      SPARQL11_Algebra.GP_PropertyPath
        ((subst_var_ps name t ps), pp, (subst_var_pt name t pt))
  | uu___ -> p
let subst_this_gp (t : RDF_Term.rdf_term)
  (p : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern= subst_var_gp "this" t p
let rec subst_vars_gp (binds : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (p : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.group_graph_pattern=
  match binds with
  | [] -> p
  | (name, t)::rest -> subst_vars_gp rest (subst_var_gp name t p)
let si_projects_this (si : SPARQL11_Algebra.select_item) : Prims.bool=
  match si with | SPARQL11_Algebra.SI_Var v -> v = "this" | uu___ -> false
let si_assigns_prebound (si : SPARQL11_Algebra.select_item) : Prims.bool=
  match si with
  | SPARQL11_Algebra.SI_Expr (uu___, v) ->
      ((v = "this") || (v = "value")) || (v = "path")
  | uu___ -> false
let rec prebinding_unsupported (p : SPARQL11_Algebra.group_graph_pattern) :
  Prims.string FStar_Pervasives_Native.option=
  match p with
  | SPARQL11_Algebra.GP_Minus (uu___, uu___1) ->
      FStar_Pervasives_Native.Some
        "MINUS is not supported with pre-bound variables"
  | SPARQL11_Algebra.GP_Lateral (uu___, uu___1) ->
      FStar_Pervasives_Native.Some
        "LATERAL is not supported with pre-bound variables"
  | SPARQL11_Algebra.GP_Service (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.Some
        "SERVICE is not supported with pre-bound variables"
  | SPARQL11_Algebra.GP_ServiceVar (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.Some
        "SERVICE is not supported with pre-bound variables"
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) ->
      FStar_Pervasives_Native.Some
        "VALUES is not supported with pre-bound variables"
  | SPARQL11_Algebra.GP_Bind (uu___, v, p') ->
      if ((v = "this") || (v = "value")) || (v = "path")
      then FStar_Pervasives_Native.Some "assignment to a pre-bound variable"
      else prebinding_unsupported p'
  | SPARQL11_Algebra.GP_SubSelect q ->
      (match SPARQL11_Algebra.__proj__Mkquery__item__q_form q with
       | SPARQL11_Algebra.QF_Select (SPARQL11_Algebra.Select_Vars sis) ->
           if FStar_List_Tot_Base.existsb si_assigns_prebound sis
           then
             FStar_Pervasives_Native.Some
               "assignment to a pre-bound variable in a nested SELECT"
           else
             if FStar_List_Tot_Base.existsb si_projects_this sis
             then
               prebinding_unsupported
                 (SPARQL11_Algebra.__proj__Mkquery__item__q_pattern q)
             else
               FStar_Pervasives_Native.Some
                 "nested SELECT does not project $this"
       | uu___ ->
           FStar_Pervasives_Native.Some
             "nested SELECT does not project $this")
  | SPARQL11_Algebra.GP_Join (a, b) ->
      (match prebinding_unsupported a with
       | FStar_Pervasives_Native.Some m -> FStar_Pervasives_Native.Some m
       | FStar_Pervasives_Native.None -> prebinding_unsupported b)
  | SPARQL11_Algebra.GP_LeftJoin (a, b, uu___) ->
      (match prebinding_unsupported a with
       | FStar_Pervasives_Native.Some m -> FStar_Pervasives_Native.Some m
       | FStar_Pervasives_Native.None -> prebinding_unsupported b)
  | SPARQL11_Algebra.GP_Union (a, b) ->
      (match prebinding_unsupported a with
       | FStar_Pervasives_Native.Some m -> FStar_Pervasives_Native.Some m
       | FStar_Pervasives_Native.None -> prebinding_unsupported b)
  | SPARQL11_Algebra.GP_Filter (uu___, a) -> prebinding_unsupported a
  | SPARQL11_Algebra.GP_Graph (uu___, a) -> prebinding_unsupported a
  | uu___ -> FStar_Pervasives_Native.None
let shacl_internal_shapes_graph_iri : RDF_Term.wf_iri=
  "http://factoidal.example/shacl-internal#shapesGraph"
let sparql_constraint_severity (shapes_raw : RDF_Graph.rdf_graph)
  (cref : shape_ref) (dsev : severity) : severity=
  match RDF_Graph.term_to_subject (shape_ref_to_term cref) with
  | FStar_Pervasives_Native.Some cs ->
      (match RDF_Graph_Executable.find_objects shapes_raw cs sh_severity with
       | (RDF_Term.T_IRI i)::uu___ -> severity_of_iri i
       | uu___ -> dsev)
  | FStar_Pervasives_Native.None -> dsev
let sparql_violations_for_focus (data : RDF_Graph.rdf_graph)
  (shapes_raw : RDF_Graph.rdf_graph) (focus : RDF_Term.rdf_term) (s : shape)
  (cref : shape_ref) (query_text : Prims.string)
  (cmsg : RDF_Term.wf_literal FStar_Pervasives_Native.option) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  let substituted = substitute_path query_text s.shape_path in
  match SPARQL11_Parser.parse_sparql substituted with
  | SPARQL11_Parser.ParseErr msg ->
      ([],
        (FStar_Pervasives_Native.Some
           (FStar_String.concat ""
              ["sh:sparql query parse error ("; cref; "): "; msg])))
  | SPARQL11_Parser.ParseOk (q, uu___) ->
      (match if
               FStar_Pervasives_Native.uu___is_Some
                 (SPARQL11_Algebra.query_values_of q)
             then
               FStar_Pervasives_Native.Some
                 "VALUES is not supported with pre-bound variables"
             else
               prebinding_unsupported (SPARQL11_Algebra.query_pattern_of q)
       with
       | FStar_Pervasives_Native.Some why ->
           ([],
             (FStar_Pervasives_Native.Some
                (FStar_String.concat ""
                   ["sh:sparql unsupported query ("; cref; "): "; why])))
       | FStar_Pervasives_Native.None ->
           let binds =
             [("this", focus);
             ("shapesGraph",
               (RDF_Term.T_IRI shacl_internal_shapes_graph_iri));
             ("currentShape", (shape_ref_to_term s.shape_id))] in
           let q_subst =
             SPARQL11_Algebra.query_with_pattern q
               (subst_vars_gp binds (SPARQL11_Algebra.query_pattern_of q)) in
           let q' =
             SPARQL11_Algebra.query_with_prebound_values q_subst [binds] in
           let ds =
             {
               RDF_Graph.ds_default = data;
               RDF_Graph.ds_named =
                 [{
                    RDF_Graph.ng_name = shacl_internal_shapes_graph_iri;
                    RDF_Graph.ng_graph = shapes_raw
                  }]
             } in
           let rows = SPARQL11_Algebra.eval_select_query q' data ds in
           let csev = sparql_constraint_severity shapes_raw cref s.shape_sev in
           let mk_violation mu =
             let value =
               match SPARQL11_Algebra.sm_lookup "value" mu with
               | FStar_Pervasives_Native.Some v -> v
               | FStar_Pervasives_Native.None -> focus in
             let path_result =
               match SPARQL11_Algebra.sm_lookup "path" mu with
               | FStar_Pervasives_Native.Some (RDF_Term.T_IRI p) ->
                   FStar_Pervasives_Native.Some (P_Predicate p)
               | uu___1 -> s.shape_path in
             let row_msg =
               match SPARQL11_Algebra.sm_lookup "message" mu with
               | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
                   FStar_Pervasives_Native.Some l
               | uu___1 ->
                   (match cmsg with
                    | FStar_Pervasives_Native.Some uu___2 -> cmsg
                    | FStar_Pervasives_Native.None -> s.message) in
             {
               v_focus_node = focus;
               v_path = path_result;
               v_value = (FStar_Pervasives_Native.Some value);
               v_source_shape = (s.shape_id);
               v_constraint = (CC_Sparql (cref, query_text, cmsg));
               v_severity = csev;
               v_message = row_msg;
               v_source_constraint =
                 (FStar_Pervasives_Native.Some (shape_ref_to_term cref));
               v_detail = []
             } in
           ((FStar_List_Tot_Base.map mk_violation rows),
             FStar_Pervasives_Native.None))
let rec sparql_violations_for_focus_all (data : RDF_Graph.rdf_graph)
  (shapes_raw : RDF_Graph.rdf_graph) (focus : RDF_Term.rdf_term) (s : shape)
  (ccs :
    (shape_ref * Prims.string * RDF_Term.wf_literal
      FStar_Pervasives_Native.option) Prims.list)
  : (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match ccs with
  | [] -> ([], FStar_Pervasives_Native.None)
  | (cref, qt, m)::rest ->
      let uu___ =
        sparql_violations_for_focus data shapes_raw focus s cref qt m in
      (match uu___ with
       | (vs1, f1) ->
           let uu___1 =
             sparql_violations_for_focus_all data shapes_raw focus s rest in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At vs1 vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let rec sparql_violations_for_foci (data : RDF_Graph.rdf_graph)
  (shapes_raw : RDF_Graph.rdf_graph) (foci : RDF_Term.rdf_term Prims.list)
  (s : shape)
  (ccs :
    (shape_ref * Prims.string * RDF_Term.wf_literal
      FStar_Pervasives_Native.option) Prims.list)
  : (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match foci with
  | [] -> ([], FStar_Pervasives_Native.None)
  | fn::rest ->
      let uu___ = sparql_violations_for_focus_all data shapes_raw fn s ccs in
      (match uu___ with
       | (vs1, f1) ->
           let uu___1 = sparql_violations_for_foci data shapes_raw rest s ccs in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At vs1 vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let sparql_violations_for_shape (data : RDF_Graph.rdf_graph)
  (shapes_raw : RDF_Graph.rdf_graph) (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (s : shape) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  let ccs = sparql_constraints_of s in
  if Prims.uu___is_Nil ccs
  then ([], FStar_Pervasives_Native.None)
  else
    (let focus_nodes =
       dedup_terms
         (FStar_List_Tot_Base.concatMap
            (fun tgt -> eval_target data closed_cls all_subjects tgt)
            s.targets) in
     sparql_violations_for_foci data shapes_raw focus_nodes s ccs)
let rec sparql_violations_for_shapes (data : RDF_Graph.rdf_graph)
  (shapes_raw : RDF_Graph.rdf_graph) (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (ss : shape Prims.list) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match ss with
  | [] -> ([], FStar_Pervasives_Native.None)
  | s::rest ->
      let uu___ =
        sparql_violations_for_shape data shapes_raw closed_cls all_subjects s in
      (match uu___ with
       | (vs1, f1) ->
           let uu___1 =
             sparql_violations_for_shapes data shapes_raw closed_cls
               all_subjects rest in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At vs1 vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let eval_custom_component_ask (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (v : RDF_Term.rdf_term) (s : shape)
  (cc : constraint_component) (query_text : Prims.string)
  (params : (Prims.string * RDF_Term.rdf_term) Prims.list) :
  (violation FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)=
  let substituted = substitute_path query_text s.shape_path in
  match SPARQL11_Parser.parse_sparql substituted with
  | SPARQL11_Parser.ParseErr msg ->
      (FStar_Pervasives_Native.None,
        (FStar_Pervasives_Native.Some
           (FStar_String.concat ""
              ["custom constraint component query parse error: "; msg])))
  | SPARQL11_Parser.ParseOk (q, uu___) ->
      (match if
               FStar_Pervasives_Native.uu___is_Some
                 (SPARQL11_Algebra.query_values_of q)
             then
               FStar_Pervasives_Native.Some
                 "VALUES is not supported with pre-bound variables"
             else
               prebinding_unsupported (SPARQL11_Algebra.query_pattern_of q)
       with
       | FStar_Pervasives_Native.Some why ->
           (FStar_Pervasives_Native.None,
             (FStar_Pervasives_Native.Some
                (FStar_String.concat ""
                   ["custom constraint component unsupported query: "; why])))
       | FStar_Pervasives_Native.None ->
           let binds =
             FStar_List_Tot_Base.op_At [("this", focus); ("value", v)] params in
           let q_subst =
             SPARQL11_Algebra.query_with_pattern q
               (subst_vars_gp binds (SPARQL11_Algebra.query_pattern_of q)) in
           let q' =
             SPARQL11_Algebra.query_with_prebound_values q_subst [binds] in
           let ds =
             {
               RDF_Graph.ds_default = data;
               RDF_Graph.ds_named =
                 (RDF_Graph.empty_dataset.RDF_Graph.ds_named)
             } in
           let ok = SPARQL11_Algebra.eval_ask_query q' data ds in
           if ok
           then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
           else
             ((FStar_Pervasives_Native.Some
                 {
                   v_focus_node = focus;
                   v_path = (s.shape_path);
                   v_value = (FStar_Pervasives_Native.Some v);
                   v_source_shape = (s.shape_id);
                   v_constraint = cc;
                   v_severity = (s.shape_sev);
                   v_message = (s.message);
                   v_source_constraint = FStar_Pervasives_Native.None;
                   v_detail = []
                 }), FStar_Pervasives_Native.None))
let rec eval_custom_component_ask_values (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (s : shape) (cc : constraint_component)
  (query_text : Prims.string)
  (params : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (values : RDF_Term.rdf_term Prims.list) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match values with
  | [] -> ([], FStar_Pervasives_Native.None)
  | v::rest ->
      let uu___ =
        eval_custom_component_ask data focus v s cc query_text params in
      (match uu___ with
       | (vo, f1) ->
           let uu___1 =
             eval_custom_component_ask_values data focus s cc query_text
               params rest in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At
                    (match vo with
                     | FStar_Pervasives_Native.Some vv -> [vv]
                     | FStar_Pervasives_Native.None -> []) vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let term_to_plain_string (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> i
  | RDF_Term.T_BNode b -> FStar_String.concat "" ["_:"; b]
  | RDF_Term.T_Literal l -> l.RDF_Term.lexical_form
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> ""
let rec split_at_close_brace (cs : FStar_String.char Prims.list) :
  (FStar_String.char Prims.list * FStar_String.char Prims.list)
    FStar_Pervasives_Native.option=
  match cs with
  | 125::rest -> FStar_Pervasives_Native.Some ([], rest)
  | c::rest ->
      (match split_at_close_brace rest with
       | FStar_Pervasives_Native.Some (nm, r) ->
           FStar_Pervasives_Native.Some ((c :: nm), r)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | [] -> FStar_Pervasives_Native.None
let rec fill_tmpl_chars (fuel : Prims.nat)
  (cs : FStar_String.char Prims.list)
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option) :
  FStar_String.char Prims.list=
  if fuel = Prims.int_zero
  then cs
  else
    (match cs with
     | 123::63::rest ->
         (match split_at_close_brace rest with
          | FStar_Pervasives_Native.Some (nm, after) ->
              let repl =
                match lookup (FStar_String.string_of_list nm) with
                | FStar_Pervasives_Native.Some v ->
                    FStar_String.list_of_string v
                | FStar_Pervasives_Native.None -> [] in
              FStar_List_Tot_Base.op_At repl
                (fill_tmpl_chars (fuel - Prims.int_one) after lookup)
          | FStar_Pervasives_Native.None -> 123 ::
              (fill_tmpl_chars (fuel - Prims.int_one)
                 (FStar_List_Tot_Base.tl cs) lookup))
     | 123::36::rest ->
         (match split_at_close_brace rest with
          | FStar_Pervasives_Native.Some (nm, after) ->
              let repl =
                match lookup (FStar_String.string_of_list nm) with
                | FStar_Pervasives_Native.Some v ->
                    FStar_String.list_of_string v
                | FStar_Pervasives_Native.None -> [] in
              FStar_List_Tot_Base.op_At repl
                (fill_tmpl_chars (fuel - Prims.int_one) after lookup)
          | FStar_Pervasives_Native.None -> 123 ::
              (fill_tmpl_chars (fuel - Prims.int_one)
                 (FStar_List_Tot_Base.tl cs) lookup))
     | c::rest -> c :: (fill_tmpl_chars (fuel - Prims.int_one) rest lookup)
     | [] -> [])
let fill_message_template (tmpl : Prims.string)
  (params : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (mu : RDF_Graph_Executable.solution_mapping) : RDF_Term.wf_literal=
  let lookup name =
    match FStar_List_Tot_Base.find
            (fun uu___ -> match uu___ with | (n, uu___1) -> n = name) params
    with
    | FStar_Pervasives_Native.Some (uu___, t) ->
        FStar_Pervasives_Native.Some (term_to_plain_string t)
    | FStar_Pervasives_Native.None ->
        (match SPARQL11_Algebra.sm_lookup name mu with
         | FStar_Pervasives_Native.Some t ->
             FStar_Pervasives_Native.Some (term_to_plain_string t)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None) in
  let cs = FStar_String.list_of_string tmpl in
  let filled =
    FStar_String.string_of_list
      (fill_tmpl_chars ((FStar_List_Tot_Base.length cs) + Prims.int_one) cs
         lookup) in
  {
    RDF_Term.lexical_form = filled;
    RDF_Term.datatype = RDF_Term.xsd_string;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None;
    RDF_Term.direction = FStar_Pervasives_Native.None
  }
let eval_custom_component_select (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (s : shape) (cc : constraint_component)
  (query_text : Prims.string)
  (params : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (msg_tmpl : Prims.string FStar_Pervasives_Native.option) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  let substituted = substitute_path query_text s.shape_path in
  match SPARQL11_Parser.parse_sparql substituted with
  | SPARQL11_Parser.ParseErr msg ->
      ([],
        (FStar_Pervasives_Native.Some
           (FStar_String.concat ""
              ["custom constraint component query parse error: "; msg])))
  | SPARQL11_Parser.ParseOk (q, uu___) ->
      (match if
               FStar_Pervasives_Native.uu___is_Some
                 (SPARQL11_Algebra.query_values_of q)
             then
               FStar_Pervasives_Native.Some
                 "VALUES is not supported with pre-bound variables"
             else
               prebinding_unsupported (SPARQL11_Algebra.query_pattern_of q)
       with
       | FStar_Pervasives_Native.Some why ->
           ([],
             (FStar_Pervasives_Native.Some
                (FStar_String.concat ""
                   ["custom constraint component unsupported query: "; why])))
       | FStar_Pervasives_Native.None ->
           let binds = ("this", focus) :: params in
           let q_subst =
             SPARQL11_Algebra.query_with_pattern q
               (subst_vars_gp binds (SPARQL11_Algebra.query_pattern_of q)) in
           let q' =
             SPARQL11_Algebra.query_with_prebound_values q_subst [binds] in
           let ds =
             {
               RDF_Graph.ds_default = data;
               RDF_Graph.ds_named =
                 (RDF_Graph.empty_dataset.RDF_Graph.ds_named)
             } in
           let rows = SPARQL11_Algebra.eval_select_query q' data ds in
           let mk_violation mu =
             let value =
               match SPARQL11_Algebra.sm_lookup "value" mu with
               | FStar_Pervasives_Native.Some vv -> vv
               | FStar_Pervasives_Native.None -> focus in
             let path_result =
               match SPARQL11_Algebra.sm_lookup "path" mu with
               | FStar_Pervasives_Native.Some (RDF_Term.T_IRI p) ->
                   FStar_Pervasives_Native.Some (P_Predicate p)
               | uu___1 -> s.shape_path in
             let row_msg =
               match msg_tmpl with
               | FStar_Pervasives_Native.Some tmpl ->
                   FStar_Pervasives_Native.Some
                     (fill_message_template tmpl params mu)
               | FStar_Pervasives_Native.None ->
                   (match SPARQL11_Algebra.sm_lookup "message" mu with
                    | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
                        FStar_Pervasives_Native.Some l
                    | uu___1 -> s.message) in
             {
               v_focus_node = focus;
               v_path = path_result;
               v_value = (FStar_Pervasives_Native.Some value);
               v_source_shape = (s.shape_id);
               v_constraint = cc;
               v_severity = (s.shape_sev);
               v_message = row_msg;
               v_source_constraint = FStar_Pervasives_Native.None;
               v_detail = []
             } in
           ((FStar_List_Tot_Base.map mk_violation rows),
             FStar_Pervasives_Native.None))
let eval_one_custom_component (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (s : shape)
  (values : RDF_Term.rdf_term Prims.list) (cc : constraint_component) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match cc with
  | CC_Custom (uu___, is_ask, query_text, params, msg_tmpl) ->
      if is_ask
      then
        eval_custom_component_ask_values data focus s cc query_text params
          values
      else
        eval_custom_component_select data focus s cc query_text params
          msg_tmpl
  | uu___ -> ([], FStar_Pervasives_Native.None)
let rec eval_custom_components (data : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term) (s : shape)
  (values : RDF_Term.rdf_term Prims.list)
  (ccs : constraint_component Prims.list) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match ccs with
  | [] -> ([], FStar_Pervasives_Native.None)
  | cc::rest ->
      let uu___ = eval_one_custom_component data focus s values cc in
      (match uu___ with
       | (vs1, f1) ->
           let uu___1 = eval_custom_components data focus s values rest in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At vs1 vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let rec custom_violations_for_occurrence (data : RDF_Graph.rdf_graph)
  (sg : shape Prims.list) (node : RDF_Term.rdf_term) (s : shape)
  (fuel : Prims.nat) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> ([], FStar_Pervasives_Native.None)
  | uu___ ->
      let fuel' = fuel - Prims.int_one in
      let values =
        if s.is_property
        then
          match s.shape_path with
          | FStar_Pervasives_Native.Some p -> eval_path data node p
          | FStar_Pervasives_Native.None -> []
        else [node] in
      let customs =
        FStar_List_Tot_Base.concatMap
          (fun cc ->
             match cc with
             | CC_Custom (uu___1, uu___2, uu___3, uu___4, uu___5) -> [cc]
             | uu___1 -> []) s.constraints in
      let uu___1 =
        if Prims.uu___is_Nil customs
        then ([], FStar_Pervasives_Native.None)
        else eval_custom_components data node s values customs in
      (match uu___1 with
       | (own_vs, own_f) ->
           let nested_pairs =
             FStar_List_Tot_Base.concatMap
               (fun v ->
                  FStar_List_Tot_Base.concatMap
                    (fun pref ->
                       match lookup_shape pref sg with
                       | FStar_Pervasives_Native.None -> []
                       | FStar_Pervasives_Native.Some ps ->
                           [custom_violations_for_occurrence data sg v ps
                              fuel']) s.property_refs) values in
           let nested_vs =
             FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.fst
               nested_pairs in
           let nested_f =
             FStar_List_Tot_Base.fold_left
               (fun acc p ->
                  match acc with
                  | FStar_Pervasives_Native.Some uu___2 -> acc
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.snd p)
               FStar_Pervasives_Native.None nested_pairs in
           ((FStar_List_Tot_Base.op_At own_vs nested_vs),
             ((match own_f with
               | FStar_Pervasives_Native.Some uu___2 -> own_f
               | FStar_Pervasives_Native.None -> nested_f))))
let rec custom_violations_for_foci (data : RDF_Graph.rdf_graph)
  (sg : shape Prims.list) (foci : RDF_Term.rdf_term Prims.list) (s : shape)
  (fuel : Prims.nat) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match foci with
  | [] -> ([], FStar_Pervasives_Native.None)
  | fn::rest ->
      let uu___ = custom_violations_for_occurrence data sg fn s fuel in
      (match uu___ with
       | (vs1, f1) ->
           let uu___1 = custom_violations_for_foci data sg rest s fuel in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At vs1 vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let custom_violations_for_shape (data : RDF_Graph.rdf_graph)
  (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (sg : shape Prims.list)
  (s : shape) (fuel : Prims.nat) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  let focus_nodes =
    dedup_terms
      (FStar_List_Tot_Base.concatMap
         (fun tgt -> eval_target data closed_cls all_subjects tgt) s.targets) in
  custom_violations_for_foci data sg focus_nodes s fuel
let rec custom_violations_for_shapes (data : RDF_Graph.rdf_graph)
  (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (sg : shape Prims.list)
  (ss : shape Prims.list) (fuel : Prims.nat) :
  (violation Prims.list * Prims.string FStar_Pervasives_Native.option)=
  match ss with
  | [] -> ([], FStar_Pervasives_Native.None)
  | s::rest ->
      let uu___ =
        custom_violations_for_shape data closed_cls all_subjects sg s fuel in
      (match uu___ with
       | (vs1, f1) ->
           let uu___1 =
             custom_violations_for_shapes data closed_cls all_subjects sg
               rest fuel in
           (match uu___1 with
            | (vs2, f2) ->
                ((FStar_List_Tot_Base.op_At vs1 vs2),
                  ((match f1 with
                    | FStar_Pervasives_Native.Some uu___2 -> f1
                    | FStar_Pervasives_Native.None -> f2)))))
let objects_of_focus (data : RDF_Graph.rdf_graph) (fn : RDF_Term.rdf_term)
  (p : RDF_Term.wf_iri) : RDF_Term.rdf_term Prims.list=
  match RDF_Graph.term_to_subject fn with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some s ->
      RDF_Graph_Executable.find_objects data s p
let rec uvf_key (data : RDF_Graph.rdf_graph) (fn : RDF_Term.rdf_term)
  (props : RDF_Term.wf_iri Prims.list) :
  RDF_Term.rdf_term Prims.list Prims.list FStar_Pervasives_Native.option=
  match props with
  | [] -> FStar_Pervasives_Native.Some []
  | p::rest ->
      (match objects_of_focus data fn p with
       | [] -> FStar_Pervasives_Native.None
       | objs ->
           (match uvf_key data fn rest with
            | FStar_Pervasives_Native.Some tl ->
                FStar_Pervasives_Native.Some (objs :: tl)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let term_list_set_eq (a : RDF_Term.rdf_term Prims.list)
  (b : RDF_Term.rdf_term Prims.list) : Prims.bool=
  (((FStar_List_Tot_Base.length a) = (FStar_List_Tot_Base.length b)) &&
     (FStar_List_Tot_Base.for_all
        (fun x -> FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq x) b) a))
    &&
    (FStar_List_Tot_Base.for_all
       (fun x -> FStar_List_Tot_Base.existsb (RDF_Term.rdf_term_eq x) a) b)
let rec key_eq (a : RDF_Term.rdf_term Prims.list Prims.list)
  (b : RDF_Term.rdf_term Prims.list Prims.list) : Prims.bool=
  match (a, b) with
  | ([], []) -> true
  | (x::xr, y::yr) -> (term_list_set_eq x y) && (key_eq xr yr)
  | (uu___, uu___1) -> false
let uvf_props_of_shape (s : shape) : RDF_Term.wf_iri Prims.list Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun cc -> match cc with | CC_UniqueValuesFor ps -> [ps] | uu___ -> [])
    s.constraints
let uvf_violations_for_shape (data : RDF_Graph.rdf_graph)
  (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (s : shape) :
  violation Prims.list=
  let foci =
    dedup_terms
      (FStar_List_Tot_Base.concatMap
         (fun tgt -> eval_target data closed_cls all_subjects tgt) s.targets) in
  FStar_List_Tot_Base.concatMap
    (fun props ->
       let keyed =
         FStar_List_Tot_Base.map (fun fn -> (fn, (uvf_key data fn props)))
           foci in
       FStar_List_Tot_Base.concatMap
         (fun fk ->
            let uu___ = fk in
            match uu___ with
            | (fn, ko) ->
                (match ko with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some k ->
                     if
                       FStar_List_Tot_Base.existsb
                         (fun gk ->
                            let uu___1 = gk in
                            match uu___1 with
                            | (gn, ko2) ->
                                (Prims.op_Negation
                                   (RDF_Term.rdf_term_eq gn fn))
                                  &&
                                  ((match ko2 with
                                    | FStar_Pervasives_Native.Some k2 ->
                                        key_eq k k2
                                    | FStar_Pervasives_Native.None -> false)))
                         keyed
                     then
                       [focus_violation fn FStar_Pervasives_Native.None
                          s.shape_id (CC_UniqueValuesFor props) s.shape_sev
                          s.message]
                     else [])) keyed) (uvf_props_of_shape s)
let rec uvf_violations_for_shapes (data : RDF_Graph.rdf_graph)
  (closed_cls : RDF_Graph.rdf_graph)
  (all_subjects : RDF_Term.subject Prims.list) (ss : shape Prims.list) :
  violation Prims.list=
  match ss with
  | [] -> []
  | s::rest ->
      FStar_List_Tot_Base.op_At
        (uvf_violations_for_shape data closed_cls all_subjects s)
        (uvf_violations_for_shapes data closed_cls all_subjects rest)
let parse_shape_from_graph (g : RDF_Graph.rdf_graph) : shapes_graph=
  parse_shape_from_graph_pure g
let validate (data : RDF_Graph.rdf_graph) (shapes_raw : RDF_Graph.rdf_graph)
  (shapes : shapes_graph) : validation_report=
  let sg = shapes.shapes in
  let closed_cls =
    shacl_class_closure data
      ((RDF_Graph.graph_len data) + (Prims.of_int (20))) in
  let all_subjects = distinct_subjects data in
  let fuel0 =
    ((FStar_List_Tot_Base.length sg) * (Prims.of_int (4))) +
      (Prims.of_int (50)) in
  let root_shapes =
    FStar_List_Tot_Base.filter
      (fun s ->
         (Prims.uu___is_Cons s.targets) ||
           (Prims.uu___is_Cons s.target_where)) sg in
  let per_shape_violations =
    FStar_List_Tot_Base.concatMap
      (fun s ->
         let focus_nodes =
           shape_focus_nodes data sg closed_cls all_subjects s in
         FStar_List_Tot_Base.concatMap
           (fun fn -> collect_shape_violations data sg closed_cls fn s fuel0)
           focus_nodes) root_shapes in
  let uu___ =
    sparql_violations_for_shapes data shapes_raw closed_cls all_subjects
      root_shapes in
  match uu___ with
  | (sparql_violations, sparql_failure) ->
      let uu___1 =
        custom_violations_for_shapes data closed_cls all_subjects sg
          root_shapes fuel0 in
      (match uu___1 with
       | (custom_violations, custom_failure) ->
           let uvf_violations =
             uvf_violations_for_shapes data closed_cls all_subjects
               root_shapes in
           let all_results =
             FStar_List_Tot_Base.op_At per_shape_violations
               (FStar_List_Tot_Base.op_At sparql_violations
                  (FStar_List_Tot_Base.op_At custom_violations uvf_violations)) in
           {
             conforms =
               (Prims.op_Negation
                  (FStar_List_Tot_Base.existsb
                     (fun v -> severity_breaks_conformance v.v_severity)
                     all_results));
             results = all_results;
             report_failure =
               ((match sparql_failure with
                 | FStar_Pervasives_Native.Some uu___2 -> sparql_failure
                 | FStar_Pervasives_Native.None -> custom_failure))
           })
let eval_sparql_target_select (data : RDF_Graph.rdf_graph)
  (query : Prims.string) : violation Prims.list=
  failwith "Not yet implemented: SHACL.Validation.eval_sparql_target_select"
let fresh_report_bnode (prefix : Prims.string) (ctr : Prims.nat) :
  (RDF_Term.bnode_id * Prims.nat)=
  ((FStar_String.concat "" [prefix; Prims.string_of_int ctr]),
    (ctr + Prims.int_one))
let constraint_component_iri (cc : constraint_component) : RDF_Term.wf_iri=
  match cc with
  | CC_MinCount uu___ -> sh_MinCountConstraintComponent
  | CC_MaxCount uu___ -> sh_MaxCountConstraintComponent
  | CC_Datatype uu___ -> sh_DatatypeConstraintComponent
  | CC_NodeKind uu___ -> sh_NodeKindConstraintComponent
  | CC_Class uu___ -> sh_ClassConstraintComponent
  | CC_DatatypeIn uu___ -> sh_DatatypeConstraintComponent
  | CC_NodeKindOneOf uu___ -> sh_NodeKindConstraintComponent
  | CC_ClassOneOf uu___ -> sh_ClassConstraintComponent
  | CC_In uu___ -> sh_InConstraintComponent
  | CC_HasValue uu___ -> sh_HasValueConstraintComponent
  | CC_Pattern (uu___, uu___1) -> sh_PatternConstraintComponent
  | CC_MinLength uu___ -> sh_MinLengthConstraintComponent
  | CC_MaxLength uu___ -> sh_MaxLengthConstraintComponent
  | CC_SingleLine -> sh_SingleLineConstraintComponent
  | CC_MinListLength uu___ -> sh_MinListLengthConstraintComponent
  | CC_MaxListLength uu___ -> sh_MaxListLengthConstraintComponent
  | CC_RootClass uu___ -> sh_RootClassConstraintComponent
  | CC_SomeValue uu___ -> sh_SomeValueConstraintComponent
  | CC_UniqueMembers -> sh_UniqueMembersConstraintComponent
  | CC_MemberShape uu___ -> sh_MemberShapeConstraintComponent
  | CC_UniqueValuesFor uu___ -> sh_UniqueValuesForConstraintComponent
  | CC_LanguageIn uu___ -> sh_LanguageInConstraintComponent
  | CC_UniqueLang uu___ -> sh_UniqueLangConstraintComponent
  | CC_MinInclusive uu___ -> sh_MinInclusiveConstraintComponent
  | CC_MaxInclusive uu___ -> sh_MaxInclusiveConstraintComponent
  | CC_MinExclusive uu___ -> sh_MinExclusiveConstraintComponent
  | CC_MaxExclusive uu___ -> sh_MaxExclusiveConstraintComponent
  | CC_Not uu___ -> sh_NotConstraintComponent
  | CC_And uu___ -> sh_AndConstraintComponent
  | CC_Or uu___ -> sh_OrConstraintComponent
  | CC_Xone uu___ -> sh_XoneConstraintComponent
  | CC_Node uu___ -> sh_NodeConstraintComponent
  | CC_QualifiedMinCount (uu___, uu___1, uu___2) ->
      sh_QualifiedMinCountConstraintComponent
  | CC_QualifiedMaxCount (uu___, uu___1, uu___2) ->
      sh_QualifiedMaxCountConstraintComponent
  | CC_Equals uu___ -> sh_EqualsConstraintComponent
  | CC_Disjoint uu___ -> sh_DisjointConstraintComponent
  | CC_LessThan uu___ -> sh_LessThanConstraintComponent
  | CC_LessThanOrEq uu___ -> sh_LessThanOrEqualsConstraintComponent
  | CC_SubsetOf uu___ -> sh_SubsetOfConstraintComponent
  | CC_ReifierShape (uu___, uu___1) -> sh_ReifierShapeConstraintComponent
  | CC_Closed uu___ -> sh_ClosedConstraintComponent
  | CC_ClosedByTypes uu___ -> sh_ClosedConstraintComponent
  | CC_NodeByExpression uu___ -> sh_NodeByExpressionConstraintComponent
  | CC_Expression uu___ -> sh_ExpressionConstraintComponent
  | CC_Sparql (uu___, uu___1, uu___2) -> sh_SPARQLConstraintComponent
  | CC_Custom (comp, uu___, uu___1, uu___2, uu___3) -> comp
let severity_to_iri (s : severity) : RDF_Term.wf_iri=
  match s with
  | Sev_Info -> sh_Info
  | Sev_Warning -> sh_Warning
  | Sev_Violation -> sh_Violation
  | Sev_Custom i -> i
let rec path_list_to_rdf (ps : path Prims.list) (ctr : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat)=
  match ps with
  | [] -> ((RDF_Term.T_IRI OWL_Closure.rdf_nil_iri), [], ctr)
  | p::rest ->
      let uu___ = path_to_rdf p ctr in
      (match uu___ with
       | (p_term, p_ts, ctr1) ->
           let uu___1 = path_list_to_rdf rest ctr1 in
           (match uu___1 with
            | (rest_term, rest_ts, ctr2) ->
                let uu___2 = fresh_report_bnode "_shacl_rpl" ctr2 in
                (match uu___2 with
                 | (bid, ctr3) ->
                     let subj = RDF_Term.S_BNode bid in
                     ((RDF_Term.T_BNode bid),
                       ({
                          RDF_Triple.s = subj;
                          RDF_Triple.p = OWL_Closure.rdf_first;
                          RDF_Triple.o = p_term
                        } ::
                       {
                         RDF_Triple.s = subj;
                         RDF_Triple.p = OWL_Closure.rdf_rest;
                         RDF_Triple.o = rest_term
                       } :: (FStar_List_Tot_Base.op_At p_ts rest_ts)), ctr3))))
and path_to_rdf (p : path) (ctr : Prims.nat) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list * Prims.nat)=
  match p with
  | P_Predicate i -> ((RDF_Term.T_IRI i), [], ctr)
  | P_Inverse p' ->
      let uu___ = path_to_rdf p' ctr in
      (match uu___ with
       | (inner, its, ctr1) ->
           let uu___1 = fresh_report_bnode "_shacl_rpi" ctr1 in
           (match uu___1 with
            | (bid, ctr2) ->
                ((RDF_Term.T_BNode bid),
                  ({
                     RDF_Triple.s = (RDF_Term.S_BNode bid);
                     RDF_Triple.p = sh_inversePath;
                     RDF_Triple.o = inner
                   } :: its), ctr2)))
  | P_Sequence ps -> path_list_to_rdf ps ctr
  | P_Alternative ps ->
      let uu___ = path_list_to_rdf ps ctr in
      (match uu___ with
       | (list_term, list_ts, ctr1) ->
           let uu___1 = fresh_report_bnode "_shacl_rpa" ctr1 in
           (match uu___1 with
            | (bid, ctr2) ->
                ((RDF_Term.T_BNode bid),
                  ({
                     RDF_Triple.s = (RDF_Term.S_BNode bid);
                     RDF_Triple.p = sh_alternativePath;
                     RDF_Triple.o = list_term
                   } :: list_ts), ctr2)))
  | P_ZeroOrMore p' ->
      let uu___ = path_to_rdf p' ctr in
      (match uu___ with
       | (inner, its, ctr1) ->
           let uu___1 = fresh_report_bnode "_shacl_rpzm" ctr1 in
           (match uu___1 with
            | (bid, ctr2) ->
                ((RDF_Term.T_BNode bid),
                  ({
                     RDF_Triple.s = (RDF_Term.S_BNode bid);
                     RDF_Triple.p = sh_zeroOrMorePath;
                     RDF_Triple.o = inner
                   } :: its), ctr2)))
  | P_OneOrMore p' ->
      let uu___ = path_to_rdf p' ctr in
      (match uu___ with
       | (inner, its, ctr1) ->
           let uu___1 = fresh_report_bnode "_shacl_rpom" ctr1 in
           (match uu___1 with
            | (bid, ctr2) ->
                ((RDF_Term.T_BNode bid),
                  ({
                     RDF_Triple.s = (RDF_Term.S_BNode bid);
                     RDF_Triple.p = sh_oneOrMorePath;
                     RDF_Triple.o = inner
                   } :: its), ctr2)))
  | P_ZeroOrOne p' ->
      let uu___ = path_to_rdf p' ctr in
      (match uu___ with
       | (inner, its, ctr1) ->
           let uu___1 = fresh_report_bnode "_shacl_rpzo" ctr1 in
           (match uu___1 with
            | (bid, ctr2) ->
                ((RDF_Term.T_BNode bid),
                  ({
                     RDF_Triple.s = (RDF_Term.S_BNode bid);
                     RDF_Triple.p = sh_zeroOrOnePath;
                     RDF_Triple.o = inner
                   } :: its), ctr2)))
let rec result_to_triples (parent_subj : RDF_Term.subject)
  (link_pred : RDF_Term.wf_iri) (v : violation) (ctr : Prims.nat) :
  (RDF_Triple.triple Prims.list * Prims.nat)=
  let uu___ = fresh_report_bnode "_shacl_result" ctr in
  match uu___ with
  | (bid, ctr1) ->
      let rsubj = RDF_Term.S_BNode bid in
      let base =
        [{
           RDF_Triple.s = rsubj;
           RDF_Triple.p = RDFS_Closure.rdf_type;
           RDF_Triple.o = (RDF_Term.T_IRI sh_ValidationResult)
         };
        {
          RDF_Triple.s = parent_subj;
          RDF_Triple.p = link_pred;
          RDF_Triple.o = (RDF_Term.T_BNode bid)
        };
        {
          RDF_Triple.s = rsubj;
          RDF_Triple.p = sh_focusNode;
          RDF_Triple.o = (v.v_focus_node)
        };
        {
          RDF_Triple.s = rsubj;
          RDF_Triple.p = sh_resultSeverity;
          RDF_Triple.o = (RDF_Term.T_IRI (severity_to_iri v.v_severity))
        };
        {
          RDF_Triple.s = rsubj;
          RDF_Triple.p = sh_sourceConstraintComponent;
          RDF_Triple.o =
            (RDF_Term.T_IRI (constraint_component_iri v.v_constraint))
        };
        {
          RDF_Triple.s = rsubj;
          RDF_Triple.p = sh_sourceShape;
          RDF_Triple.o = (shape_ref_to_term v.v_source_shape)
        }] in
      let uu___1 =
        match v.v_path with
        | FStar_Pervasives_Native.None -> ([], ctr1)
        | FStar_Pervasives_Native.Some p ->
            let uu___2 = path_to_rdf p ctr1 in
            (match uu___2 with
             | (pterm, pts, ctr2') ->
                 (({
                     RDF_Triple.s = rsubj;
                     RDF_Triple.p = sh_resultPath;
                     RDF_Triple.o = pterm
                   } :: pts), ctr2')) in
      (match uu___1 with
       | (path_ts, ctr2) ->
           let value_ts =
             match v.v_value with
             | FStar_Pervasives_Native.Some vv ->
                 [{
                    RDF_Triple.s = rsubj;
                    RDF_Triple.p = sh_value_pred;
                    RDF_Triple.o = vv
                  }]
             | FStar_Pervasives_Native.None -> [] in
           let msg_ts =
             match v.v_message with
             | FStar_Pervasives_Native.Some m ->
                 [{
                    RDF_Triple.s = rsubj;
                    RDF_Triple.p = sh_resultMessage;
                    RDF_Triple.o = (RDF_Term.T_Literal m)
                  }]
             | FStar_Pervasives_Native.None -> [] in
           let sc_ts =
             match v.v_source_constraint with
             | FStar_Pervasives_Native.Some sc ->
                 [{
                    RDF_Triple.s = rsubj;
                    RDF_Triple.p = sh_sourceConstraint;
                    RDF_Triple.o = sc
                  }]
             | FStar_Pervasives_Native.None -> [] in
           let uu___2 = results_to_triples rsubj sh_detail v.v_detail ctr2 in
           (match uu___2 with
            | (detail_ts, ctr3) ->
                ((FStar_List_Tot_Base.op_At base
                    (FStar_List_Tot_Base.op_At path_ts
                       (FStar_List_Tot_Base.op_At value_ts
                          (FStar_List_Tot_Base.op_At msg_ts
                             (FStar_List_Tot_Base.op_At sc_ts detail_ts))))),
                  ctr3)))
and results_to_triples (parent_subj : RDF_Term.subject)
  (link_pred : RDF_Term.wf_iri) (vs : violation Prims.list) (ctr : Prims.nat)
  : (RDF_Triple.triple Prims.list * Prims.nat)=
  match vs with
  | [] -> ([], ctr)
  | v::rest ->
      let uu___ = result_to_triples parent_subj link_pred v ctr in
      (match uu___ with
       | (ts, ctr1) ->
           let uu___1 = results_to_triples parent_subj link_pred rest ctr1 in
           (match uu___1 with
            | (rest_ts, ctr2) ->
                ((FStar_List_Tot_Base.op_At ts rest_ts), ctr2)))
let validation_report_to_graph (r : validation_report) : RDF_Graph.rdf_graph=
  let report_subj = RDF_Term.S_BNode "_shacl_report0" in
  let header =
    [{
       RDF_Triple.s = report_subj;
       RDF_Triple.p = RDFS_Closure.rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI sh_ValidationReport)
     };
    {
      RDF_Triple.s = report_subj;
      RDF_Triple.p = sh_conforms_pred;
      RDF_Triple.o =
        (RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = (if r.conforms then "true" else "false");
             RDF_Term.datatype = RDF_Term.xsd_boolean;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
    }] in
  FStar_List_Tot_Base.op_At header
    (FStar_Pervasives_Native.fst
       (results_to_triples report_subj sh_result r.results Prims.int_zero))
