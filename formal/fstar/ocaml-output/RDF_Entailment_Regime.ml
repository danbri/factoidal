open Prims
let rdf_type_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_reifies_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies"
let rdfs_proposition_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#Proposition"
let owl_sameas_iri : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#sameAs"
let is_exact_scaled_dt (dt : RDF_Term.wf_iri) : Prims.bool=
  (dt = RDF_Term.xsd_integer) || (dt = RDF_Term.xsd_decimal)
let dt_value_leq (l1 : RDF_Term.literal) (l2 : RDF_Term.literal) :
  Prims.bool=
  if
    (is_exact_scaled_dt l1.RDF_Term.datatype) &&
      (is_exact_scaled_dt l2.RDF_Term.datatype)
  then
    match ((XSD_Datatypes.literal_to_scaled l1),
            (XSD_Datatypes.literal_to_scaled l2))
    with
    | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some s2) ->
        (l1.RDF_Term.datatype = l2.RDF_Term.datatype) &&
          ((XSD_Datatypes.scaled_cmp s1 s2) = Prims.int_zero)
    | (uu___, uu___1) -> RDF_Term.literal_eq l1 l2
  else RDF_Term.literal_eq l1 l2
let reifies_prop_triples (t : RDF_Triple.triple) :
  RDF_Triple.triple Prims.list=
  if t.RDF_Triple.p = rdf_reifies_iri
  then
    match t.RDF_Triple.o with
    | RDF_Term.T_IRI i ->
        [{
           RDF_Triple.s = (RDF_Term.S_IRI i);
           RDF_Triple.p = rdf_type_iri;
           RDF_Triple.o = (RDF_Term.T_IRI rdfs_proposition_iri)
         }]
    | RDF_Term.T_BNode b ->
        [{
           RDF_Triple.s = (RDF_Term.S_BNode b);
           RDF_Triple.p = rdf_type_iri;
           RDF_Triple.o = (RDF_Term.T_IRI rdfs_proposition_iri)
         }]
    | uu___ -> []
  else []
let rdfs_closure (ts : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.op_At ts
    (FStar_List_Tot_Base.collect reifies_prop_triples ts)
let subst_subj (x : RDF_Term.wf_iri) (y : RDF_Term.wf_iri)
  (s : RDF_Term.subject) : RDF_Term.subject=
  match s with
  | RDF_Term.S_IRI i -> if i = x then RDF_Term.S_IRI y else RDF_Term.S_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.S_BNode b
let rec subst_term (x : RDF_Term.wf_iri) (y : RDF_Term.wf_iri)
  (t : RDF_Term.rdf_term) : RDF_Term.rdf_term=
  match t with
  | RDF_Term.T_IRI i -> if i = x then RDF_Term.T_IRI y else RDF_Term.T_IRI i
  | RDF_Term.T_BNode b -> RDF_Term.T_BNode b
  | RDF_Term.T_Literal l -> RDF_Term.T_Literal l
  | RDF_Term.T_TripleTerm (s, p, o) ->
      RDF_Term.T_TripleTerm
        ((subst_subj x y s), (if p = x then y else p), (subst_term x y o))
let subst_triple (x : RDF_Term.wf_iri) (y : RDF_Term.wf_iri)
  (t : RDF_Triple.triple) : RDF_Triple.triple=
  {
    RDF_Triple.s = (subst_subj x y t.RDF_Triple.s);
    RDF_Triple.p = (if t.RDF_Triple.p = x then y else t.RDF_Triple.p);
    RDF_Triple.o = (subst_term x y t.RDF_Triple.o)
  }
let sameas_pairs (ts : RDF_Triple.triple Prims.list) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  FStar_List_Tot_Base.collect
    (fun t ->
       if t.RDF_Triple.p = owl_sameas_iri
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI a, RDF_Term.T_IRI b) -> [(a, b)]
         | (uu___, uu___1) -> []
       else []) ts
let apply_sameas_pair (acc : RDF_Triple.triple Prims.list)
  (p : (RDF_Term.wf_iri * RDF_Term.wf_iri)) : RDF_Triple.triple Prims.list=
  let uu___ = p in
  match uu___ with
  | (a, b) ->
      FStar_List_Tot_Base.op_At acc
        (FStar_List_Tot_Base.op_At
           (FStar_List_Tot_Base.map (subst_triple b a) acc)
           (FStar_List_Tot_Base.map (subst_triple a b) acc))
let owl_closure (ts : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.fold_left apply_sameas_pair ts (sameas_pairs ts)
let entails_rdf (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  RDF_Entailment_Simple.entails_with dt_value_leq a b
let entails_rdfs (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  RDF_Entailment_Simple.entails_with dt_value_leq (rdfs_closure a) b
let entails_rdfs_plus (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  RDF_Entailment_Simple.entails_with dt_value_leq
    (owl_closure (rdfs_closure a)) b
