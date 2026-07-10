module OWL2.SyntaxDL

// OWL 2 DL species checker for the W3C OWL 2 Test Cases "species"
// facet (http://www.w3.org/2007/OWL/testOntology#species): given the
// RDF graphs of a test case's ontology documents, decide whether the
// case is within OWL 2 DL (species test:DL) or only OWL 2 Full
// (species test:FULL). Purely syntax-directed over parsed triples —
// no reasoning, no closure; every function is Tot.
//
// Scope note (measured, not aspirational): the species facet in the
// W3C corpus mixes two judging eras — the OWL 1 WebOnt species
// classification and the OWL 2 WG's re-annotation (rdfbased-sem-*
// cases are species-FULL as a matter of test provenance). The checks
// below are the subset of the OWL 2 Mapping-to-RDF-Graphs reverse
// mapping + Structural Specification global restrictions that the
// corpus actually discriminates on, validated check-by-check against
// all 489 species-annotated cases in third_party/testing/owl/all.rdf
// (323 species-DL, 166 species-FULL-only). Two graph-identical
// premise pairs with opposite species verdicts exist in the corpus
// (WebOnt-I5.5-005 vs WebOnt-I5.5-006 premises), so the species
// facet also covers the CONCLUSION document — hence the two-graph
// interface of `species_is_dl` below. Residual mis-verdicts are
// enumerated in ocaml-output/owl_syntax_dl_results.log.
//
// Checks realised (spec anchor in parens):
//   1. ontology header discipline — a document with no owl:Ontology
//      header is not the RDF image of an OWL 2 DL ontology document
//      (Mapping to RDF Graphs sec 3.1) unless it consists solely of
//      entity-typing triples over non-reserved subjects; a document
//      with more than one non-imported header has no unique root.
//   2. typed-entity discipline — an IRI used as an assertion
//      predicate or as owl:onProperty filler must be declared as an
//      object/data/annotation property, be a built-in, carry
//      rdfs:domain/rdfs:range disambiguation alongside a property-
//      characteristic typing, or take part in owl:inverseOf
//      (Mapping sec 3.2.1 declaration-driven parsing); an IRI used
//      as an rdf:type class filler must be a declared class,
//      datatype or built-in.
//   3. reserved-vocabulary discipline — rdf:/rdfs:/owl:/xsd: IRIs as
//      triple subjects (redefinition) or in entity positions are
//      OWL Full, minus the built-in entities OWL 2 DL admits
//      (owl:Thing, owl:Nothing, top/bottom properties, datatype map,
//      built-in annotation properties; Structural Spec sec 5).
//   4. illegal punning — the same IRI declared as class and datatype,
//      as object and data property, or as object/data and annotation
//      property (Structural Spec sec 5.8.1); class+individual punning
//      stays DL.
//   5. structural well-formedness of the RDF mapping — literals in
//      class position, undefined bnode class expressions, malformed
//      rdf lists (a list node needs exactly one rdf:first and one
//      rdf:rest), user datatypes without a definition, object
//      properties with literal objects.
//   6. global restrictions (Structural Spec sec 11) where the corpus
//      exercises them — non-simple (transitive or chain-defined)
//      properties under cardinality restrictions, and a property
//      occurring strictly inside its own owl:propertyChainAxiom
//      (violates the regular-order requirement on role chains).

open FStar.List.Tot
open RDF.Term
open RDF.Triple

module S = FStar.String

(* ------------------------------------------------------------------ *)
(* Vocabulary                                                          *)
(* ------------------------------------------------------------------ *)

let ns_owl  : string = "http://www.w3.org/2002/07/owl#"
let ns_rdf  : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let ns_rdfs : string = "http://www.w3.org/2000/01/rdf-schema#"
let ns_xsd  : string = "http://www.w3.org/2001/XMLSchema#"

let starts_with (prefix s: string) : Tot bool =
  let pl = S.length prefix in
  let sl = S.length s in
  if sl < pl then false
  else S.sub s 0 pl = prefix

let iri_reserved (i: string) : Tot bool =
  starts_with ns_owl i || starts_with ns_rdf i ||
  starts_with ns_rdfs i || starts_with ns_xsd i

let rdf_type_p        : string = ns_rdf ^ "type"
let rdf_first_p       : string = ns_rdf ^ "first"
let rdf_rest_p        : string = ns_rdf ^ "rest"
let rdf_nil_i         : string = ns_rdf ^ "nil"

let owl_ontology_c    : string = ns_owl ^ "Ontology"
let owl_class_c       : string = ns_owl ^ "Class"
let owl_restriction_c : string = ns_owl ^ "Restriction"
let owl_objprop_c     : string = ns_owl ^ "ObjectProperty"
let owl_dataprop_c    : string = ns_owl ^ "DatatypeProperty"
let owl_annprop_c     : string = ns_owl ^ "AnnotationProperty"
let owl_ontprop_c     : string = ns_owl ^ "OntologyProperty"
let owl_datarange_c   : string = ns_owl ^ "DataRange"
let rdfs_datatype_c   : string = ns_rdfs ^ "Datatype"

let owl_imports_p       : string = ns_owl ^ "imports"
let owl_priorversion_p  : string = ns_owl ^ "priorVersion"
let owl_onproperty_p    : string = ns_owl ^ "onProperty"
let owl_inverseof_p     : string = ns_owl ^ "inverseOf"
let owl_intersectionof_p: string = ns_owl ^ "intersectionOf"
let owl_unionof_p       : string = ns_owl ^ "unionOf"
let owl_complementof_p  : string = ns_owl ^ "complementOf"
let owl_oneof_p         : string = ns_owl ^ "oneOf"
let owl_equivclass_p    : string = ns_owl ^ "equivalentClass"
let owl_ondatatype_p    : string = ns_owl ^ "onDatatype"
let owl_chain_p         : string = ns_owl ^ "propertyChainAxiom"
let rdfs_domain_p       : string = ns_rdfs ^ "domain"
let rdfs_range_p        : string = ns_rdfs ^ "range"

/// Property-characteristic classes whose members are object
/// properties in the OWL 2 RDF mapping.
let obj_characteristics : list string = [
  ns_owl ^ "SymmetricProperty";
  ns_owl ^ "TransitiveProperty";
  ns_owl ^ "InverseFunctionalProperty";
  ns_owl ^ "AsymmetricProperty";
  ns_owl ^ "ReflexiveProperty";
  ns_owl ^ "IrreflexiveProperty"
]

let owl_functionalprop_c : string = ns_owl ^ "FunctionalProperty"

/// The OWL 2 datatype map (Structural Spec sec 4) plus rdfs:Literal,
/// rdf:XMLLiteral, rdf:PlainLiteral, rdf:langString — datatype IRIs a
/// DL document may use without defining them.
let builtin_datatypes : list string = [
  ns_rdfs ^ "Literal";
  ns_rdf ^ "XMLLiteral"; ns_rdf ^ "PlainLiteral"; ns_rdf ^ "langString";
  ns_owl ^ "real"; ns_owl ^ "rational";
  ns_xsd ^ "string"; ns_xsd ^ "boolean"; ns_xsd ^ "decimal";
  ns_xsd ^ "integer"; ns_xsd ^ "double"; ns_xsd ^ "float";
  ns_xsd ^ "date"; ns_xsd ^ "time"; ns_xsd ^ "dateTime";
  ns_xsd ^ "dateTimeStamp"; ns_xsd ^ "gYear"; ns_xsd ^ "gMonth";
  ns_xsd ^ "gDay"; ns_xsd ^ "gYearMonth"; ns_xsd ^ "gMonthDay";
  ns_xsd ^ "duration"; ns_xsd ^ "yearMonthDuration";
  ns_xsd ^ "dayTimeDuration";
  ns_xsd ^ "byte"; ns_xsd ^ "short"; ns_xsd ^ "int"; ns_xsd ^ "long";
  ns_xsd ^ "unsignedByte"; ns_xsd ^ "unsignedShort";
  ns_xsd ^ "unsignedInt"; ns_xsd ^ "unsignedLong";
  ns_xsd ^ "negativeInteger"; ns_xsd ^ "nonNegativeInteger";
  ns_xsd ^ "nonPositiveInteger"; ns_xsd ^ "positiveInteger";
  ns_xsd ^ "hexBinary"; ns_xsd ^ "base64Binary"; ns_xsd ^ "anyURI";
  ns_xsd ^ "language"; ns_xsd ^ "normalizedString"; ns_xsd ^ "token";
  ns_xsd ^ "NMTOKEN"; ns_xsd ^ "Name"; ns_xsd ^ "NCName"
]

/// Built-in annotation properties (Structural Spec sec 5.5).
let builtin_annprops : list string = [
  ns_rdfs ^ "label"; ns_rdfs ^ "comment"; ns_rdfs ^ "seeAlso";
  ns_rdfs ^ "isDefinedBy";
  ns_owl ^ "versionInfo"; ns_owl ^ "deprecated";
  ns_owl ^ "backwardCompatibleWith"; ns_owl ^ "incompatibleWith";
  ns_owl ^ "priorVersion"
]

/// Built-in top/bottom properties (Structural Spec sec 5.3/5.4).
let builtin_props : list string = [
  ns_owl ^ "topObjectProperty"; ns_owl ^ "bottomObjectProperty";
  ns_owl ^ "topDataProperty"; ns_owl ^ "bottomDataProperty"
]

/// Declaration-typing classes: rdf:type objects that declare an
/// entity rather than assert class membership.
let declaration_types : list string = [
  ns_owl ^ "Class"; ns_owl ^ "ObjectProperty"; ns_owl ^ "DatatypeProperty";
  ns_owl ^ "AnnotationProperty"; ns_rdfs ^ "Datatype";
  ns_owl ^ "NamedIndividual"; ns_owl ^ "Ontology";
  ns_owl ^ "DeprecatedClass"; ns_owl ^ "DeprecatedProperty";
  ns_owl ^ "OntologyProperty"; ns_owl ^ "DataRange"
]

/// Reserved IRIs acceptable as an rdf:type object in a DL document:
/// declarations, property characteristics, built-in classes, the
/// mapping's own structural classes, and the legacy typings the
/// corpus's species-DL cases use (rdfs:Class, rdf:List,
/// rdf:Property).
let type_object_whitelist : list string =
  declaration_types @ obj_characteristics @ builtin_datatypes @ [
    owl_functionalprop_c; ns_owl ^ "Restriction";
    ns_owl ^ "Thing"; ns_owl ^ "Nothing";
    ns_owl ^ "AllDifferent"; ns_owl ^ "AllDisjointClasses";
    ns_owl ^ "AllDisjointProperties"; ns_owl ^ "Axiom";
    ns_owl ^ "Annotation"; ns_owl ^ "NegativePropertyAssertion";
    ns_rdfs ^ "Class"; ns_rdf ^ "List"; ns_rdf ^ "Property"
  ]

/// Reserved IRIs acceptable as a triple SUBJECT in a DL document:
/// the built-in entities OWL 2 DL lets an ontology talk about.
let subject_whitelist : list string =
  [ns_owl ^ "Thing"; ns_owl ^ "Nothing"]
  @ builtin_datatypes @ builtin_props

/// rdf:type objects acceptable inside a header-less typing-only
/// document (see doc_header_violations): declarations plus owl:Thing.
/// Narrower than type_object_whitelist on purpose — a header-less
/// document typing entities with owl:Nothing, rdfs:Class etc. is
/// species-FULL throughout the corpus.
let headerless_type_whitelist : list string =
  declaration_types @ [ns_owl ^ "Thing"]

let cardinality_preds : list string = [
  ns_owl ^ "cardinality"; ns_owl ^ "minCardinality";
  ns_owl ^ "maxCardinality"; ns_owl ^ "qualifiedCardinality";
  ns_owl ^ "minQualifiedCardinality"; ns_owl ^ "maxQualifiedCardinality"
]

(* ------------------------------------------------------------------ *)
(* Graph accessors (entity keys: "I" ^ iri for IRIs, "B" ^ id for     *)
(* blank nodes, so one string set covers both node kinds)              *)
(* ------------------------------------------------------------------ *)

let subj_key (s: subject) : Tot string =
  match s with
  | S_IRI i -> "I" ^ i
  | S_BNode b -> "B" ^ b

let term_key (o: rdf_term) : Tot (option string) =
  match o with
  | T_IRI i -> Some ("I" ^ i)
  | T_BNode b -> Some ("B" ^ b)
  | T_Literal _ -> None

let term_is_iri (o: rdf_term) (i: string) : Tot bool =
  match o with
  | T_IRI x -> x = i
  | _ -> false

/// Subject keys of triples `?s rdf:type <ty>`.
let rec subjects_typed (g: list triple) (ty: string) : Tot (list string) =
  match g with
  | [] -> []
  | t :: rest ->
    if t.p = rdf_type_p && term_is_iri t.o ty
    then subj_key t.s :: subjects_typed rest ty
    else subjects_typed rest ty

/// Subject keys of triples with predicate p.
let rec subjects_of (g: list triple) (p: string) : Tot (list string) =
  match g with
  | [] -> []
  | t :: rest ->
    if t.p = p then subj_key t.s :: subjects_of rest p
    else subjects_of rest p

/// Node keys of non-literal objects of triples with predicate p.
let rec object_keys_of (g: list triple) (p: string) : Tot (list string) =
  match g with
  | [] -> []
  | t :: rest ->
    if t.p = p then
      (match term_key t.o with
       | Some k -> k :: object_keys_of rest p
       | None -> object_keys_of rest p)
    else object_keys_of rest p

/// Objects (terms) of triples with predicate p.
let rec objects_of (g: list triple) (p: string) : Tot (list rdf_term) =
  match g with
  | [] -> []
  | t :: rest ->
    if t.p = p then t.o :: objects_of rest p
    else objects_of rest p

/// Does the graph contain a triple with subject key sk and predicate p?
let rec has_triple_sp (g: list triple) (sk: string) (p: string) : Tot bool =
  match g with
  | [] -> false
  | t :: rest ->
    (t.p = p && subj_key t.s = sk) || has_triple_sp rest sk p

/// First object of (sk, p, ?o), if any.
let rec find_object (g: list triple) (sk: string) (p: string)
  : Tot (option rdf_term) =
  match g with
  | [] -> None
  | t :: rest ->
    if t.p = p && subj_key t.s = sk then Some t.o
    else find_object rest sk p

/// Number of triples (sk, p, ?o).
let rec count_sp (g: list triple) (sk: string) (p: string) : Tot nat =
  match g with
  | [] -> 0
  | t :: rest ->
    if t.p = p && subj_key t.s = sk
    then 1 + count_sp rest sk p
    else count_sp rest sk p

let rec dedup (l: list string) : Tot (list string) =
  match l with
  | [] -> []
  | x :: rest -> if mem x rest then dedup rest else x :: dedup rest

/// Members of an RDF collection starting at `node`, fuel-bounded by
/// the graph size (each step consumes one rdf:rest link).
let rec collection_members (g: list triple) (node: rdf_term) (fuel: nat)
  : Tot (list rdf_term) (decreases fuel) =
  if fuel = 0 then []
  else
    match term_key node with
    | None -> []
    | Some nk ->
      if term_is_iri node rdf_nil_i then []
      else
        match find_object g nk rdf_first_p with
        | None -> []
        | Some first ->
          match find_object g nk rdf_rest_p with
          | None -> [first]
          | Some rest -> first :: collection_members g rest (fuel - 1)

(* ------------------------------------------------------------------ *)
(* Precomputed declaration index                                       *)
(* ------------------------------------------------------------------ *)

noeq type decl_index = {
  d_class    : list string;   (* keys typed owl:Class / owl:DeprecatedClass *)
  d_restr    : list string;   (* keys typed owl:Restriction *)
  d_datatype : list string;   (* keys typed rdfs:Datatype / owl:DataRange *)
  d_objprop  : list string;   (* keys typed owl:ObjectProperty *)
  d_dataprop : list string;   (* keys typed owl:DatatypeProperty *)
  d_annprop  : list string;   (* keys typed owl:AnnotationProperty / owl:OntologyProperty *)
  d_charprop : list string;   (* keys typed with an object characteristic or owl:FunctionalProperty *)
  d_hasdr    : list string;   (* keys with rdfs:domain or rdfs:range *)
  d_inv      : list string;   (* keys taking part in owl:inverseOf (either side) *)
  d_annsubj  : list string;   (* keys typed owl:Ontology / owl:Axiom / owl:Annotation *)
}

let rec subjects_typed_any (g: list triple) (tys: list string)
  : Tot (list string) (decreases tys) =
  match tys with
  | [] -> []
  | ty :: rest -> subjects_typed g ty @ subjects_typed_any g rest

let build_decl_index (g: list triple) : Tot decl_index = {
  d_class    = subjects_typed_any g [owl_class_c; ns_owl ^ "DeprecatedClass"];
  d_restr    = subjects_typed g owl_restriction_c;
  d_datatype = subjects_typed_any g [rdfs_datatype_c; owl_datarange_c];
  d_objprop  = subjects_typed g owl_objprop_c;
  d_dataprop = subjects_typed g owl_dataprop_c;
  d_annprop  = subjects_typed_any g [owl_annprop_c; owl_ontprop_c];
  d_charprop = subjects_typed_any g (owl_functionalprop_c :: obj_characteristics);
  d_hasdr    = subjects_of g rdfs_domain_p @ subjects_of g rdfs_range_p;
  d_inv      = subjects_of g owl_inverseof_p @ object_keys_of g owl_inverseof_p;
  d_annsubj  = subjects_typed_any g [owl_ontology_c; ns_owl ^ "Axiom"; ns_owl ^ "Annotation"];
}

/// Is key k acceptable wherever the RDF mapping demands a property?
/// Declared object/data/annotation property; built-in; a property-
/// characteristic typing disambiguated by rdfs:domain/rdfs:range; or
/// participation in owl:inverseOf.
let prop_evidence (d: decl_index) (k: string) : Tot bool =
  mem k d.d_objprop || mem k d.d_dataprop || mem k d.d_annprop ||
  mem k d.d_inv ||
  (mem k d.d_charprop && (mem k d.d_hasdr || mem k d.d_inv))

/// Is key k defined as a class expression? Declared class, datatype
/// or restriction, or a bnode carrying class-expression structure.
let class_evidence (g: list triple) (d: decl_index) (k: string) : Tot bool =
  mem k d.d_class || mem k d.d_datatype || mem k d.d_restr ||
  has_triple_sp g k owl_intersectionof_p ||
  has_triple_sp g k owl_unionof_p ||
  has_triple_sp g k owl_complementof_p ||
  has_triple_sp g k owl_oneof_p ||
  has_triple_sp g k owl_onproperty_p

/// Is datatype IRI dt usable in a DL data range position? Built-in,
/// declared as a class (legacy corpus shape), or carrying a datatype
/// definition (owl:equivalentClass / owl:onDatatype / owl:oneOf).
let datatype_evidence (g: list triple) (d: decl_index) (dt: string) : Tot bool =
  mem dt builtin_datatypes ||
  mem ("I" ^ dt) d.d_class ||
  has_triple_sp g ("I" ^ dt) owl_equivclass_p ||
  has_triple_sp g ("I" ^ dt) owl_ondatatype_p ||
  has_triple_sp g ("I" ^ dt) owl_oneof_p

(* ------------------------------------------------------------------ *)
(* Header discipline (checked per document, before imports merge)      *)
(* ------------------------------------------------------------------ *)

/// Is triple t acceptable in a header-less document? Only entity
/// typings whose subject is a blank node or non-reserved IRI and
/// whose object is a declaration class, owl:Thing, a blank node, or
/// a non-reserved IRI.
let typing_only_triple (t: triple) : Tot bool =
  t.p = rdf_type_p &&
  (match t.s with
   | S_BNode _ -> true
   | S_IRI i -> not (iri_reserved i)) &&
  (match t.o with
   | T_BNode _ -> true
   | T_Literal _ -> false
   | T_IRI o -> mem o headerless_type_whitelist || not (iri_reserved o))

let rec all_typing_only (g: list triple) : Tot bool =
  match g with
  | [] -> true
  | t :: rest -> typing_only_triple t && all_typing_only rest

/// Header violations for one ontology DOCUMENT (unmerged): either no
/// owl:Ontology header (unless the document is typing-only), or more
/// than one header that is not the object of owl:imports /
/// owl:priorVersion (no unique root ontology node).
let doc_header_violations (g: list triple) : Tot (list string) =
  let headers = dedup (subjects_typed g owl_ontology_c) in
  let nonroot = object_keys_of g owl_imports_p
              @ object_keys_of g owl_priorversion_p in
  let roots = filter (fun h -> not (mem h nonroot)) headers in
  match headers with
  | [] -> if all_typing_only g then [] else ["no-ontology-header"]
  | _ -> if length roots > 1 then ["multiple-root-ontology-headers"] else []

(* ------------------------------------------------------------------ *)
(* Body checks (on the merged graph)                                   *)
(* ------------------------------------------------------------------ *)

/// All elements of l except the last (strict interior helper for the
/// role-chain regularity check).
let rec drop_last_term (l: list rdf_term) : Tot (list rdf_term) =
  match l with
  | [] -> []
  | [_] -> []
  | x :: rest -> x :: drop_last_term rest

/// Violations contributed by a single triple, given the declaration
/// index of the whole graph.
let triple_violations (g: list triple) (d: decl_index) (t: triple)
  : Tot (list string) =
  let v1 =
    (* reserved-vocabulary subject = redefinition of built-ins *)
    match t.s with
    | S_IRI i ->
      if iri_reserved i && not (mem i subject_whitelist)
      then ["reserved-vocabulary-subject: " ^ i]
      else []
    | _ -> [] in
  let v2 =
    (* untyped / undeclared assertion predicate *)
    if iri_reserved t.p then []
    else if mem t.p builtin_annprops || mem t.p builtin_props then []
    else if prop_evidence d ("I" ^ t.p) then []
    else if mem (subj_key t.s) d.d_annsubj then []
    else ["untyped-predicate: " ^ t.p] in
  let v3 =
    (* rdf:type object discipline *)
    if t.p <> rdf_type_p then []
    else
      match t.o with
      | T_Literal _ -> ["literal-as-type-object"]
      | T_BNode b ->
        if class_evidence g d ("B" ^ b) then []
        else ["undefined-bnode-class-expression"]
      | T_IRI o ->
        if iri_reserved o then
          (if mem o type_object_whitelist then []
           else ["reserved-vocabulary-as-class: " ^ o])
        else if class_evidence g d ("I" ^ o) then []
        else ["untyped-class: " ^ o] in
  let v4 =
    (* owl:onProperty filler must be a property *)
    if t.p <> owl_onproperty_p then []
    else
      match t.o with
      | T_Literal _ -> ["literal-as-onProperty"]
      | T_BNode b ->
        if mem ("B" ^ b) d.d_inv then [] else ["undefined-bnode-onProperty"]
      | T_IRI o ->
        if mem o builtin_props then []
        else if iri_reserved o then ["reserved-vocabulary-as-onProperty: " ^ o]
        else if prop_evidence d ("I" ^ o) then []
        else ["untyped-onProperty: " ^ o] in
  let v5 =
    (* object property with a literal object *)
    match t.o with
    | T_Literal _ ->
      if mem ("I" ^ t.p) d.d_objprop
      then ["object-property-with-literal-object: " ^ t.p]
      else []
    | _ -> [] in
  let v6 =
    (* literal datatype must be usable in DL *)
    match t.o with
    | T_Literal l ->
      let dt : string = l.datatype in
      if datatype_evidence g d dt then []
      else if iri_reserved dt then ["reserved-vocabulary-as-datatype: " ^ dt]
      else ["undefined-datatype: " ^ dt]
    | _ -> [] in
  let v7 =
    (* data-property rdfs:range and owl:onDatatype fillers *)
    if (t.p = rdfs_range_p && mem (subj_key t.s) d.d_dataprop)
       || t.p = owl_ondatatype_p then
      match t.o with
      | T_IRI o ->
        if datatype_evidence g d o then []
        else if iri_reserved o then ["reserved-vocabulary-as-datatype: " ^ o]
        else ["undefined-datatype: " ^ o]
      | _ -> []
    else [] in
  let v8 =
    (* rdf list node discipline: exactly one rdf:first + one rdf:rest *)
    if t.p = rdf_first_p || t.p = rdf_rest_p then
      let sk = subj_key t.s in
      if count_sp g sk rdf_first_p = 1 && count_sp g sk rdf_rest_p = 1
      then []
      else ["malformed-rdf-list-node"]
    else [] in
  let v9 =
    (* global restriction: property strictly inside its own chain *)
    if t.p = owl_chain_p then
      let members = collection_members g t.o (length g) in
      let interior =
        (match members with
         | [] -> []
         | _ :: tl -> drop_last_term tl) in
      let self = subj_key t.s in
      if existsb
           (fun (m: rdf_term) ->
              match term_key m with
              | Some k -> k = self
              | None -> false)
           interior
      then ["property-inside-own-chain: " ^ self]
      else []
    else [] in
  v1 @ v2 @ v3 @ v4 @ v5 @ v6 @ v7 @ v8 @ v9

let rec triples_violations (g: list triple) (d: decl_index) (ts: list triple)
  : Tot (list string) (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> triple_violations g d t @ triples_violations g d rest

/// Illegal punning: same IRI as class+datatype, object+data property,
/// or object/data+annotation property (blank-node keys are skipped —
/// a bnode typed both owl:Class and owl:Restriction is fine).
let rec punning_violations_keys (d: decl_index) (keys: list string)
  : Tot (list string) (decreases keys) =
  match keys with
  | [] -> []
  | k :: rest ->
    let here =
      if not (starts_with "I" k) then []
      else
        (if mem k d.d_class && mem k d.d_datatype
         then ["illegal-punning-class-datatype: " ^ k] else [])
        @ (if mem k d.d_objprop && mem k d.d_dataprop
           then ["illegal-punning-object-data-property: " ^ k] else [])
        @ (if mem k d.d_objprop && mem k d.d_annprop
           then ["illegal-punning-object-annotation-property: " ^ k] else [])
        @ (if mem k d.d_dataprop && mem k d.d_annprop
           then ["illegal-punning-data-annotation-property: " ^ k] else []) in
    here @ punning_violations_keys d rest

let punning_violations (d: decl_index) : Tot (list string) =
  punning_violations_keys d
    (dedup (d.d_class @ d.d_objprop @ d.d_dataprop))

/// Global restriction sec 11: non-simple (transitive or chain-
/// defined) property under a cardinality restriction.
let rec nonsimple_cardinality_violations
    (g: list triple) (nonsimple: list string) (restrs: list string)
  : Tot (list string) (decreases restrs) =
  match restrs with
  | [] -> []
  | r :: rest ->
    let here =
      if existsb (fun (cp: string) -> has_triple_sp g r cp) cardinality_preds
      then
        match find_object g r owl_onproperty_p with
        | Some o ->
          (match term_key o with
           | Some k ->
             if mem k nonsimple
             then ["non-simple-property-in-cardinality: " ^ k]
             else []
           | None -> [])
        | None -> []
      else [] in
    here @ nonsimple_cardinality_violations g nonsimple rest

/// All body violations of a (merged) graph.
let graph_body_violations (g: list triple) : Tot (list string) =
  let d = build_decl_index g in
  let per_triple = triples_violations g d g in
  let punning = punning_violations d in
  let nonsimple =
    dedup (subjects_typed g (ns_owl ^ "TransitiveProperty")
           @ subjects_of g owl_chain_p) in
  let restrs = dedup (subjects_of g owl_onproperty_p) in
  per_triple @ punning
  @ nonsimple_cardinality_violations g nonsimple restrs

(* ------------------------------------------------------------------ *)
(* Species verdict                                                     *)
(* ------------------------------------------------------------------ *)

/// Full species check for one test case.
///   p_doc     — the premise/input document alone (no imports merged)
///   p_merged  — the premise with its owl:imports closure merged in
///   has_conclusion — whether the case carries a conclusion document
///   c_doc     — the conclusion document alone
///   u_merged  — premise + conclusion + imports closure, merged
/// The conclusion's entity typing is checked against the union
/// (the corpus convention lets conclusions use premise vocabulary),
/// but its header discipline is its own document's.
let species_violations
    (p_doc: list triple) (p_merged: list triple)
    (has_conclusion: bool)
    (c_doc: list triple) (u_merged: list triple)
  : Tot (list string) =
  map (fun v -> "premise: " ^ v) (doc_header_violations p_doc)
  @ map (fun v -> "premise: " ^ v) (graph_body_violations p_merged)
  @ (if has_conclusion then
       map (fun v -> "conclusion: " ^ v) (doc_header_violations c_doc)
       @ map (fun v -> "conclusion: " ^ v) (graph_body_violations u_merged)
     else [])

/// True iff every document of the case is within OWL 2 DL.
let species_is_dl
    (p_doc: list triple) (p_merged: list triple)
    (has_conclusion: bool)
    (c_doc: list triple) (u_merged: list triple)
  : Tot bool =
  Nil? (species_violations p_doc p_merged has_conclusion c_doc u_merged)

/// Species check for graphs obtained from OWL 2 Functional Syntax
/// (test:normativeSyntax FUNCTIONAL): a successful FS parse proves the
/// Ontology(...) header syntactically, so only the body checks apply.
let species_violations_functional
    (p: list triple) (has_conclusion: bool) (u: list triple)
  : Tot (list string) =
  map (fun v -> "premise: " ^ v) (graph_body_violations p)
  @ (if has_conclusion
     then map (fun v -> "conclusion: " ^ v) (graph_body_violations u)
     else [])

let species_is_dl_functional
    (p: list triple) (has_conclusion: bool) (u: list triple)
  : Tot bool =
  Nil? (species_violations_functional p has_conclusion u)
