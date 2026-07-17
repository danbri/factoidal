open Prims
let ns_owl : Prims.string= "http://www.w3.org/2002/07/owl#"
let ns_rdf : Prims.string= "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let ns_rdfs : Prims.string= "http://www.w3.org/2000/01/rdf-schema#"
let ns_xsd : Prims.string= "http://www.w3.org/2001/XMLSchema#"
let starts_with (prefix : Prims.string) (s : Prims.string) : Prims.bool=
  let pl = FStar_String.strlen prefix in
  let sl = FStar_String.strlen s in
  if sl < pl then false else (FStar_String.sub s Prims.int_zero pl) = prefix
let iri_reserved (i : Prims.string) : Prims.bool=
  (((starts_with ns_owl i) || (starts_with ns_rdf i)) ||
     (starts_with ns_rdfs i))
    || (starts_with ns_xsd i)
let rdf_type_p : Prims.string= Prims.strcat ns_rdf "type"
let rdf_first_p : Prims.string= Prims.strcat ns_rdf "first"
let rdf_rest_p : Prims.string= Prims.strcat ns_rdf "rest"
let rdf_nil_i : Prims.string= Prims.strcat ns_rdf "nil"
let owl_ontology_c : Prims.string= Prims.strcat ns_owl "Ontology"
let owl_class_c : Prims.string= Prims.strcat ns_owl "Class"
let owl_restriction_c : Prims.string= Prims.strcat ns_owl "Restriction"
let owl_objprop_c : Prims.string= Prims.strcat ns_owl "ObjectProperty"
let owl_dataprop_c : Prims.string= Prims.strcat ns_owl "DatatypeProperty"
let owl_annprop_c : Prims.string= Prims.strcat ns_owl "AnnotationProperty"
let owl_ontprop_c : Prims.string= Prims.strcat ns_owl "OntologyProperty"
let owl_datarange_c : Prims.string= Prims.strcat ns_owl "DataRange"
let rdfs_datatype_c : Prims.string= Prims.strcat ns_rdfs "Datatype"
let owl_imports_p : Prims.string= Prims.strcat ns_owl "imports"
let owl_priorversion_p : Prims.string= Prims.strcat ns_owl "priorVersion"
let owl_onproperty_p : Prims.string= Prims.strcat ns_owl "onProperty"
let owl_inverseof_p : Prims.string= Prims.strcat ns_owl "inverseOf"
let owl_intersectionof_p : Prims.string= Prims.strcat ns_owl "intersectionOf"
let owl_unionof_p : Prims.string= Prims.strcat ns_owl "unionOf"
let owl_complementof_p : Prims.string= Prims.strcat ns_owl "complementOf"
let owl_oneof_p : Prims.string= Prims.strcat ns_owl "oneOf"
let owl_equivclass_p : Prims.string= Prims.strcat ns_owl "equivalentClass"
let owl_ondatatype_p : Prims.string= Prims.strcat ns_owl "onDatatype"
let owl_chain_p : Prims.string= Prims.strcat ns_owl "propertyChainAxiom"
let rdfs_domain_p : Prims.string= Prims.strcat ns_rdfs "domain"
let rdfs_range_p : Prims.string= Prims.strcat ns_rdfs "range"
let obj_characteristics : Prims.string Prims.list=
  [Prims.strcat ns_owl "SymmetricProperty";
  Prims.strcat ns_owl "TransitiveProperty";
  Prims.strcat ns_owl "InverseFunctionalProperty";
  Prims.strcat ns_owl "AsymmetricProperty";
  Prims.strcat ns_owl "ReflexiveProperty";
  Prims.strcat ns_owl "IrreflexiveProperty"]
let owl_functionalprop_c : Prims.string=
  Prims.strcat ns_owl "FunctionalProperty"
let builtin_datatypes : Prims.string Prims.list=
  [Prims.strcat ns_rdfs "Literal";
  Prims.strcat ns_rdf "XMLLiteral";
  Prims.strcat ns_rdf "PlainLiteral";
  Prims.strcat ns_rdf "langString";
  Prims.strcat ns_owl "real";
  Prims.strcat ns_owl "rational";
  Prims.strcat ns_xsd "string";
  Prims.strcat ns_xsd "boolean";
  Prims.strcat ns_xsd "decimal";
  Prims.strcat ns_xsd "integer";
  Prims.strcat ns_xsd "double";
  Prims.strcat ns_xsd "float";
  Prims.strcat ns_xsd "date";
  Prims.strcat ns_xsd "time";
  Prims.strcat ns_xsd "dateTime";
  Prims.strcat ns_xsd "dateTimeStamp";
  Prims.strcat ns_xsd "gYear";
  Prims.strcat ns_xsd "gMonth";
  Prims.strcat ns_xsd "gDay";
  Prims.strcat ns_xsd "gYearMonth";
  Prims.strcat ns_xsd "gMonthDay";
  Prims.strcat ns_xsd "duration";
  Prims.strcat ns_xsd "yearMonthDuration";
  Prims.strcat ns_xsd "dayTimeDuration";
  Prims.strcat ns_xsd "byte";
  Prims.strcat ns_xsd "short";
  Prims.strcat ns_xsd "int";
  Prims.strcat ns_xsd "long";
  Prims.strcat ns_xsd "unsignedByte";
  Prims.strcat ns_xsd "unsignedShort";
  Prims.strcat ns_xsd "unsignedInt";
  Prims.strcat ns_xsd "unsignedLong";
  Prims.strcat ns_xsd "negativeInteger";
  Prims.strcat ns_xsd "nonNegativeInteger";
  Prims.strcat ns_xsd "nonPositiveInteger";
  Prims.strcat ns_xsd "positiveInteger";
  Prims.strcat ns_xsd "hexBinary";
  Prims.strcat ns_xsd "base64Binary";
  Prims.strcat ns_xsd "anyURI";
  Prims.strcat ns_xsd "language";
  Prims.strcat ns_xsd "normalizedString";
  Prims.strcat ns_xsd "token";
  Prims.strcat ns_xsd "NMTOKEN";
  Prims.strcat ns_xsd "Name";
  Prims.strcat ns_xsd "NCName"]
let builtin_annprops : Prims.string Prims.list=
  [Prims.strcat ns_rdfs "label";
  Prims.strcat ns_rdfs "comment";
  Prims.strcat ns_rdfs "seeAlso";
  Prims.strcat ns_rdfs "isDefinedBy";
  Prims.strcat ns_owl "versionInfo";
  Prims.strcat ns_owl "deprecated";
  Prims.strcat ns_owl "backwardCompatibleWith";
  Prims.strcat ns_owl "incompatibleWith";
  Prims.strcat ns_owl "priorVersion"]
let builtin_props : Prims.string Prims.list=
  [Prims.strcat ns_owl "topObjectProperty";
  Prims.strcat ns_owl "bottomObjectProperty";
  Prims.strcat ns_owl "topDataProperty";
  Prims.strcat ns_owl "bottomDataProperty"]
let declaration_types : Prims.string Prims.list=
  [Prims.strcat ns_owl "Class";
  Prims.strcat ns_owl "ObjectProperty";
  Prims.strcat ns_owl "DatatypeProperty";
  Prims.strcat ns_owl "AnnotationProperty";
  Prims.strcat ns_rdfs "Datatype";
  Prims.strcat ns_owl "NamedIndividual";
  Prims.strcat ns_owl "Ontology";
  Prims.strcat ns_owl "DeprecatedClass";
  Prims.strcat ns_owl "DeprecatedProperty";
  Prims.strcat ns_owl "OntologyProperty";
  Prims.strcat ns_owl "DataRange"]
let type_object_whitelist : Prims.string Prims.list=
  FStar_List_Tot_Base.op_At declaration_types
    (FStar_List_Tot_Base.op_At obj_characteristics
       (FStar_List_Tot_Base.op_At builtin_datatypes
          [owl_functionalprop_c;
          Prims.strcat ns_owl "Restriction";
          Prims.strcat ns_owl "Thing";
          Prims.strcat ns_owl "Nothing";
          Prims.strcat ns_owl "AllDifferent";
          Prims.strcat ns_owl "AllDisjointClasses";
          Prims.strcat ns_owl "AllDisjointProperties";
          Prims.strcat ns_owl "Axiom";
          Prims.strcat ns_owl "Annotation";
          Prims.strcat ns_owl "NegativePropertyAssertion";
          Prims.strcat ns_rdfs "Class";
          Prims.strcat ns_rdf "List";
          Prims.strcat ns_rdf "Property"]))
let subject_whitelist : Prims.string Prims.list=
  FStar_List_Tot_Base.op_At
    [Prims.strcat ns_owl "Thing"; Prims.strcat ns_owl "Nothing"]
    (FStar_List_Tot_Base.op_At builtin_datatypes builtin_props)
let headerless_type_whitelist : Prims.string Prims.list=
  FStar_List_Tot_Base.op_At declaration_types [Prims.strcat ns_owl "Thing"]
let cardinality_preds : Prims.string Prims.list=
  [Prims.strcat ns_owl "cardinality";
  Prims.strcat ns_owl "minCardinality";
  Prims.strcat ns_owl "maxCardinality";
  Prims.strcat ns_owl "qualifiedCardinality";
  Prims.strcat ns_owl "minQualifiedCardinality";
  Prims.strcat ns_owl "maxQualifiedCardinality"]
let subj_key (s : RDF_Term.subject) : Prims.string=
  match s with
  | RDF_Term.S_IRI i -> Prims.strcat "I" i
  | RDF_Term.S_BNode b -> Prims.strcat "B" b
let term_key (o : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match o with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (Prims.strcat "I" i)
  | RDF_Term.T_BNode b -> FStar_Pervasives_Native.Some (Prims.strcat "B" b)
  | RDF_Term.T_Literal uu___ -> FStar_Pervasives_Native.None
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
      FStar_Pervasives_Native.None
let term_is_iri (o : RDF_Term.rdf_term) (i : Prims.string) : Prims.bool=
  match o with | RDF_Term.T_IRI x -> x = i | uu___ -> false
let rec subjects_typed (g : RDF_Triple.triple Prims.list) (ty : Prims.string)
  : Prims.string Prims.list=
  match g with
  | [] -> []
  | t::rest ->
      if (t.RDF_Triple.p = rdf_type_p) && (term_is_iri t.RDF_Triple.o ty)
      then (subj_key t.RDF_Triple.s) :: (subjects_typed rest ty)
      else subjects_typed rest ty
let rec subjects_of (g : RDF_Triple.triple Prims.list) (p : Prims.string) :
  Prims.string Prims.list=
  match g with
  | [] -> []
  | t::rest ->
      if t.RDF_Triple.p = p
      then (subj_key t.RDF_Triple.s) :: (subjects_of rest p)
      else subjects_of rest p
let rec object_keys_of (g : RDF_Triple.triple Prims.list) (p : Prims.string)
  : Prims.string Prims.list=
  match g with
  | [] -> []
  | t::rest ->
      if t.RDF_Triple.p = p
      then
        (match term_key t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some k -> k :: (object_keys_of rest p)
         | FStar_Pervasives_Native.None -> object_keys_of rest p)
      else object_keys_of rest p
let rec objects_of (g : RDF_Triple.triple Prims.list) (p : Prims.string) :
  RDF_Term.rdf_term Prims.list=
  match g with
  | [] -> []
  | t::rest ->
      if t.RDF_Triple.p = p
      then (t.RDF_Triple.o) :: (objects_of rest p)
      else objects_of rest p
let rec has_triple_sp (g : RDF_Triple.triple Prims.list) (sk : Prims.string)
  (p : Prims.string) : Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      ((t.RDF_Triple.p = p) && ((subj_key t.RDF_Triple.s) = sk)) ||
        (has_triple_sp rest sk p)
let rec find_object (g : RDF_Triple.triple Prims.list) (sk : Prims.string)
  (p : Prims.string) : RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match g with
  | [] -> FStar_Pervasives_Native.None
  | t::rest ->
      if (t.RDF_Triple.p = p) && ((subj_key t.RDF_Triple.s) = sk)
      then FStar_Pervasives_Native.Some (t.RDF_Triple.o)
      else find_object rest sk p
let rec count_sp (g : RDF_Triple.triple Prims.list) (sk : Prims.string)
  (p : Prims.string) : Prims.nat=
  match g with
  | [] -> Prims.int_zero
  | t::rest ->
      if (t.RDF_Triple.p = p) && ((subj_key t.RDF_Triple.s) = sk)
      then Prims.int_one + (count_sp rest sk p)
      else count_sp rest sk p
let rec dedup (l : Prims.string Prims.list) : Prims.string Prims.list=
  match l with
  | [] -> []
  | x::rest ->
      if FStar_List_Tot_Base.mem x rest
      then dedup rest
      else x :: (dedup rest)
let rec collection_members (g : RDF_Triple.triple Prims.list)
  (node : RDF_Term.rdf_term) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match term_key node with
     | FStar_Pervasives_Native.None -> []
     | FStar_Pervasives_Native.Some nk ->
         if term_is_iri node rdf_nil_i
         then []
         else
           (match find_object g nk rdf_first_p with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some first ->
                (match find_object g nk rdf_rest_p with
                 | FStar_Pervasives_Native.None -> [first]
                 | FStar_Pervasives_Native.Some rest -> first ::
                     (collection_members g rest (fuel - Prims.int_one)))))
type decl_index =
  {
  d_class: Prims.string Prims.list ;
  d_restr: Prims.string Prims.list ;
  d_datatype: Prims.string Prims.list ;
  d_objprop: Prims.string Prims.list ;
  d_dataprop: Prims.string Prims.list ;
  d_annprop: Prims.string Prims.list ;
  d_charprop: Prims.string Prims.list ;
  d_hasdr: Prims.string Prims.list ;
  d_inv: Prims.string Prims.list ;
  d_annsubj: Prims.string Prims.list }
let __proj__Mkdecl_index__item__d_class (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_class
let __proj__Mkdecl_index__item__d_restr (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_restr
let __proj__Mkdecl_index__item__d_datatype (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_datatype
let __proj__Mkdecl_index__item__d_objprop (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_objprop
let __proj__Mkdecl_index__item__d_dataprop (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_dataprop
let __proj__Mkdecl_index__item__d_annprop (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_annprop
let __proj__Mkdecl_index__item__d_charprop (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_charprop
let __proj__Mkdecl_index__item__d_hasdr (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_hasdr
let __proj__Mkdecl_index__item__d_inv (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_inv
let __proj__Mkdecl_index__item__d_annsubj (projectee : decl_index) :
  Prims.string Prims.list=
  match projectee with
  | { d_class; d_restr; d_datatype; d_objprop; d_dataprop; d_annprop;
      d_charprop; d_hasdr; d_inv; d_annsubj;_} -> d_annsubj
let rec subjects_typed_any (g : RDF_Triple.triple Prims.list)
  (tys : Prims.string Prims.list) : Prims.string Prims.list=
  match tys with
  | [] -> []
  | ty::rest ->
      FStar_List_Tot_Base.op_At (subjects_typed g ty)
        (subjects_typed_any g rest)
let build_decl_index (g : RDF_Triple.triple Prims.list) : decl_index=
  {
    d_class =
      (subjects_typed_any g
         [owl_class_c; Prims.strcat ns_owl "DeprecatedClass"]);
    d_restr = (subjects_typed g owl_restriction_c);
    d_datatype = (subjects_typed_any g [rdfs_datatype_c; owl_datarange_c]);
    d_objprop = (subjects_typed g owl_objprop_c);
    d_dataprop = (subjects_typed g owl_dataprop_c);
    d_annprop = (subjects_typed_any g [owl_annprop_c; owl_ontprop_c]);
    d_charprop =
      (subjects_typed_any g (owl_functionalprop_c :: obj_characteristics));
    d_hasdr =
      (FStar_List_Tot_Base.op_At (subjects_of g rdfs_domain_p)
         (subjects_of g rdfs_range_p));
    d_inv =
      (FStar_List_Tot_Base.op_At (subjects_of g owl_inverseof_p)
         (object_keys_of g owl_inverseof_p));
    d_annsubj =
      (subjects_typed_any g
         [owl_ontology_c;
         Prims.strcat ns_owl "Axiom";
         Prims.strcat ns_owl "Annotation"])
  }
let prop_evidence (d : decl_index) (k : Prims.string) : Prims.bool=
  ((((FStar_List_Tot_Base.mem k d.d_objprop) ||
       (FStar_List_Tot_Base.mem k d.d_dataprop))
      || (FStar_List_Tot_Base.mem k d.d_annprop))
     || (FStar_List_Tot_Base.mem k d.d_inv))
    ||
    ((FStar_List_Tot_Base.mem k d.d_charprop) &&
       ((FStar_List_Tot_Base.mem k d.d_hasdr) ||
          (FStar_List_Tot_Base.mem k d.d_inv)))
let class_evidence (g : RDF_Triple.triple Prims.list) (d : decl_index)
  (k : Prims.string) : Prims.bool=
  (((((((FStar_List_Tot_Base.mem k d.d_class) ||
          (FStar_List_Tot_Base.mem k d.d_datatype))
         || (FStar_List_Tot_Base.mem k d.d_restr))
        || (has_triple_sp g k owl_intersectionof_p))
       || (has_triple_sp g k owl_unionof_p))
      || (has_triple_sp g k owl_complementof_p))
     || (has_triple_sp g k owl_oneof_p))
    || (has_triple_sp g k owl_onproperty_p)
let datatype_evidence (g : RDF_Triple.triple Prims.list) (d : decl_index)
  (dt : Prims.string) : Prims.bool=
  ((((FStar_List_Tot_Base.mem dt builtin_datatypes) ||
       (FStar_List_Tot_Base.mem (Prims.strcat "I" dt) d.d_class))
      || (has_triple_sp g (Prims.strcat "I" dt) owl_equivclass_p))
     || (has_triple_sp g (Prims.strcat "I" dt) owl_ondatatype_p))
    || (has_triple_sp g (Prims.strcat "I" dt) owl_oneof_p)
let typing_only_triple (t : RDF_Triple.triple) : Prims.bool=
  ((t.RDF_Triple.p = rdf_type_p) &&
     (match t.RDF_Triple.s with
      | RDF_Term.S_BNode uu___ -> true
      | RDF_Term.S_IRI i -> Prims.op_Negation (iri_reserved i)))
    &&
    (match t.RDF_Triple.o with
     | RDF_Term.T_BNode uu___ -> true
     | RDF_Term.T_Literal uu___ -> false
     | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> false
     | RDF_Term.T_IRI o ->
         (FStar_List_Tot_Base.mem o headerless_type_whitelist) ||
           (Prims.op_Negation (iri_reserved o)))
let rec all_typing_only (g : RDF_Triple.triple Prims.list) : Prims.bool=
  match g with
  | [] -> true
  | t::rest -> (typing_only_triple t) && (all_typing_only rest)
let doc_header_violations (g : RDF_Triple.triple Prims.list) :
  Prims.string Prims.list=
  let headers = dedup (subjects_typed g owl_ontology_c) in
  let nonroot =
    FStar_List_Tot_Base.op_At (object_keys_of g owl_imports_p)
      (object_keys_of g owl_priorversion_p) in
  let roots =
    FStar_List_Tot_Base.filter
      (fun h -> Prims.op_Negation (FStar_List_Tot_Base.mem h nonroot))
      headers in
  match headers with
  | [] -> if all_typing_only g then [] else ["no-ontology-header"]
  | uu___ ->
      if (FStar_List_Tot_Base.length roots) > Prims.int_one
      then ["multiple-root-ontology-headers"]
      else []
let rec drop_last_term (l : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match l with
  | [] -> []
  | uu___::[] -> []
  | x::rest -> x :: (drop_last_term rest)
let triple_violations (g : RDF_Triple.triple Prims.list) (d : decl_index)
  (t : RDF_Triple.triple) : Prims.string Prims.list=
  let v1 =
    match t.RDF_Triple.s with
    | RDF_Term.S_IRI i ->
        if
          (iri_reserved i) &&
            (Prims.op_Negation (FStar_List_Tot_Base.mem i subject_whitelist))
        then [Prims.strcat "reserved-vocabulary-subject: " i]
        else []
    | uu___ -> [] in
  let v2 =
    if iri_reserved t.RDF_Triple.p
    then []
    else
      if
        (FStar_List_Tot_Base.mem t.RDF_Triple.p builtin_annprops) ||
          (FStar_List_Tot_Base.mem t.RDF_Triple.p builtin_props)
      then []
      else
        if prop_evidence d (Prims.strcat "I" t.RDF_Triple.p)
        then []
        else
          if FStar_List_Tot_Base.mem (subj_key t.RDF_Triple.s) d.d_annsubj
          then []
          else [Prims.strcat "untyped-predicate: " t.RDF_Triple.p] in
  let v3 =
    if t.RDF_Triple.p <> rdf_type_p
    then []
    else
      (match t.RDF_Triple.o with
       | RDF_Term.T_Literal uu___1 -> ["literal-as-type-object"]
       | RDF_Term.T_TripleTerm (uu___1, uu___2, uu___3) ->
           ["triple-term-as-type-object"]
       | RDF_Term.T_BNode b ->
           if class_evidence g d (Prims.strcat "B" b)
           then []
           else ["undefined-bnode-class-expression"]
       | RDF_Term.T_IRI o ->
           if iri_reserved o
           then
             (if FStar_List_Tot_Base.mem o type_object_whitelist
              then []
              else [Prims.strcat "reserved-vocabulary-as-class: " o])
           else
             if class_evidence g d (Prims.strcat "I" o)
             then []
             else [Prims.strcat "untyped-class: " o]) in
  let v4 =
    if t.RDF_Triple.p <> owl_onproperty_p
    then []
    else
      (match t.RDF_Triple.o with
       | RDF_Term.T_Literal uu___1 -> ["literal-as-onProperty"]
       | RDF_Term.T_TripleTerm (uu___1, uu___2, uu___3) ->
           ["triple-term-as-onProperty"]
       | RDF_Term.T_BNode b ->
           if FStar_List_Tot_Base.mem (Prims.strcat "B" b) d.d_inv
           then []
           else ["undefined-bnode-onProperty"]
       | RDF_Term.T_IRI o ->
           if FStar_List_Tot_Base.mem o builtin_props
           then []
           else
             if iri_reserved o
             then [Prims.strcat "reserved-vocabulary-as-onProperty: " o]
             else
               if prop_evidence d (Prims.strcat "I" o)
               then []
               else [Prims.strcat "untyped-onProperty: " o]) in
  let v5 =
    match t.RDF_Triple.o with
    | RDF_Term.T_Literal uu___ ->
        if
          FStar_List_Tot_Base.mem (Prims.strcat "I" t.RDF_Triple.p)
            d.d_objprop
        then
          [Prims.strcat "object-property-with-literal-object: "
             t.RDF_Triple.p]
        else []
    | uu___ -> [] in
  let v6 =
    match t.RDF_Triple.o with
    | RDF_Term.T_Literal l ->
        let dt = l.RDF_Term.datatype in
        if datatype_evidence g d dt
        then []
        else
          if iri_reserved dt
          then [Prims.strcat "reserved-vocabulary-as-datatype: " dt]
          else [Prims.strcat "undefined-datatype: " dt]
    | uu___ -> [] in
  let v7 =
    if
      ((t.RDF_Triple.p = rdfs_range_p) &&
         (FStar_List_Tot_Base.mem (subj_key t.RDF_Triple.s) d.d_dataprop))
        || (t.RDF_Triple.p = owl_ondatatype_p)
    then
      match t.RDF_Triple.o with
      | RDF_Term.T_IRI o ->
          (if datatype_evidence g d o
           then []
           else
             if iri_reserved o
             then [Prims.strcat "reserved-vocabulary-as-datatype: " o]
             else [Prims.strcat "undefined-datatype: " o])
      | uu___ -> []
    else [] in
  let v8 =
    if (t.RDF_Triple.p = rdf_first_p) || (t.RDF_Triple.p = rdf_rest_p)
    then
      let sk = subj_key t.RDF_Triple.s in
      (if
         ((count_sp g sk rdf_first_p) = Prims.int_one) &&
           ((count_sp g sk rdf_rest_p) = Prims.int_one)
       then []
       else ["malformed-rdf-list-node"])
    else [] in
  let v9 =
    if t.RDF_Triple.p = owl_chain_p
    then
      let members =
        collection_members g t.RDF_Triple.o (FStar_List_Tot_Base.length g) in
      let interior =
        match members with | [] -> [] | uu___::tl -> drop_last_term tl in
      let self = subj_key t.RDF_Triple.s in
      (if
         FStar_List_Tot_Base.existsb
           (fun m ->
              match term_key m with
              | FStar_Pervasives_Native.Some k -> k = self
              | FStar_Pervasives_Native.None -> false) interior
       then [Prims.strcat "property-inside-own-chain: " self]
       else [])
    else [] in
  FStar_List_Tot_Base.op_At v1
    (FStar_List_Tot_Base.op_At v2
       (FStar_List_Tot_Base.op_At v3
          (FStar_List_Tot_Base.op_At v4
             (FStar_List_Tot_Base.op_At v5
                (FStar_List_Tot_Base.op_At v6
                   (FStar_List_Tot_Base.op_At v7
                      (FStar_List_Tot_Base.op_At v8 v9)))))))
let rec triples_violations (g : RDF_Triple.triple Prims.list)
  (d : decl_index) (ts : RDF_Triple.triple Prims.list) :
  Prims.string Prims.list=
  match ts with
  | [] -> []
  | t::rest ->
      FStar_List_Tot_Base.op_At (triple_violations g d t)
        (triples_violations g d rest)
let rec punning_violations_keys (d : decl_index)
  (keys : Prims.string Prims.list) : Prims.string Prims.list=
  match keys with
  | [] -> []
  | k::rest ->
      let here =
        if Prims.op_Negation (starts_with "I" k)
        then []
        else
          FStar_List_Tot_Base.op_At
            (if
               (FStar_List_Tot_Base.mem k d.d_class) &&
                 (FStar_List_Tot_Base.mem k d.d_datatype)
             then [Prims.strcat "illegal-punning-class-datatype: " k]
             else [])
            (FStar_List_Tot_Base.op_At
               (if
                  (FStar_List_Tot_Base.mem k d.d_objprop) &&
                    (FStar_List_Tot_Base.mem k d.d_dataprop)
                then
                  [Prims.strcat "illegal-punning-object-data-property: " k]
                else [])
               (FStar_List_Tot_Base.op_At
                  (if
                     (FStar_List_Tot_Base.mem k d.d_objprop) &&
                       (FStar_List_Tot_Base.mem k d.d_annprop)
                   then
                     [Prims.strcat
                        "illegal-punning-object-annotation-property: " k]
                   else [])
                  (if
                     (FStar_List_Tot_Base.mem k d.d_dataprop) &&
                       (FStar_List_Tot_Base.mem k d.d_annprop)
                   then
                     [Prims.strcat
                        "illegal-punning-data-annotation-property: " k]
                   else []))) in
      FStar_List_Tot_Base.op_At here (punning_violations_keys d rest)
let punning_violations (d : decl_index) : Prims.string Prims.list=
  punning_violations_keys d
    (dedup
       (FStar_List_Tot_Base.op_At d.d_class
          (FStar_List_Tot_Base.op_At d.d_objprop d.d_dataprop)))
let rec nonsimple_cardinality_violations (g : RDF_Triple.triple Prims.list)
  (nonsimple : Prims.string Prims.list) (restrs : Prims.string Prims.list) :
  Prims.string Prims.list=
  match restrs with
  | [] -> []
  | r::rest ->
      let here =
        if
          FStar_List_Tot_Base.existsb (fun cp -> has_triple_sp g r cp)
            cardinality_preds
        then
          match find_object g r owl_onproperty_p with
          | FStar_Pervasives_Native.Some o ->
              (match term_key o with
               | FStar_Pervasives_Native.Some k ->
                   if FStar_List_Tot_Base.mem k nonsimple
                   then
                     [Prims.strcat "non-simple-property-in-cardinality: " k]
                   else []
               | FStar_Pervasives_Native.None -> [])
          | FStar_Pervasives_Native.None -> []
        else [] in
      FStar_List_Tot_Base.op_At here
        (nonsimple_cardinality_violations g nonsimple rest)
let graph_body_violations (g : RDF_Triple.triple Prims.list) :
  Prims.string Prims.list=
  let d = build_decl_index g in
  let per_triple = triples_violations g d g in
  let punning = punning_violations d in
  let nonsimple =
    dedup
      (FStar_List_Tot_Base.op_At
         (subjects_typed g (Prims.strcat ns_owl "TransitiveProperty"))
         (subjects_of g owl_chain_p)) in
  let restrs = dedup (subjects_of g owl_onproperty_p) in
  FStar_List_Tot_Base.op_At per_triple
    (FStar_List_Tot_Base.op_At punning
       (nonsimple_cardinality_violations g nonsimple restrs))
let species_violations (p_doc : RDF_Triple.triple Prims.list)
  (p_merged : RDF_Triple.triple Prims.list) (has_conclusion : Prims.bool)
  (c_doc : RDF_Triple.triple Prims.list)
  (u_merged : RDF_Triple.triple Prims.list) : Prims.string Prims.list=
  FStar_List_Tot_Base.op_At
    (FStar_List_Tot_Base.map (fun v -> Prims.strcat "premise: " v)
       (doc_header_violations p_doc))
    (FStar_List_Tot_Base.op_At
       (FStar_List_Tot_Base.map (fun v -> Prims.strcat "premise: " v)
          (graph_body_violations p_merged))
       (if has_conclusion
        then
          FStar_List_Tot_Base.op_At
            (FStar_List_Tot_Base.map (fun v -> Prims.strcat "conclusion: " v)
               (doc_header_violations c_doc))
            (FStar_List_Tot_Base.map (fun v -> Prims.strcat "conclusion: " v)
               (graph_body_violations u_merged))
        else []))
let species_is_dl (p_doc : RDF_Triple.triple Prims.list)
  (p_merged : RDF_Triple.triple Prims.list) (has_conclusion : Prims.bool)
  (c_doc : RDF_Triple.triple Prims.list)
  (u_merged : RDF_Triple.triple Prims.list) : Prims.bool=
  Prims.uu___is_Nil
    (species_violations p_doc p_merged has_conclusion c_doc u_merged)
let species_violations_functional (p : RDF_Triple.triple Prims.list)
  (has_conclusion : Prims.bool) (u : RDF_Triple.triple Prims.list) :
  Prims.string Prims.list=
  FStar_List_Tot_Base.op_At
    (FStar_List_Tot_Base.map (fun v -> Prims.strcat "premise: " v)
       (graph_body_violations p))
    (if has_conclusion
     then
       FStar_List_Tot_Base.map (fun v -> Prims.strcat "conclusion: " v)
         (graph_body_violations u)
     else [])
let species_is_dl_functional (p : RDF_Triple.triple Prims.list)
  (has_conclusion : Prims.bool) (u : RDF_Triple.triple Prims.list) :
  Prims.bool=
  Prims.uu___is_Nil (species_violations_functional p has_conclusion u)
