open Prims
let rdf_type_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_reifies_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies"
let rdfs_proposition_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#Proposition"
let owl_sameas_iri : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#sameAs"
let rdf_json_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"
let rec json_value_eq (fuel : Prims.nat) (v1 : Parser_JSON.json_val)
  (v2 : Parser_JSON.json_val) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (v1, v2) with
     | (Parser_JSON.JNull, Parser_JSON.JNull) -> true
     | (Parser_JSON.JBool a, Parser_JSON.JBool b) -> a = b
     | (Parser_JSON.JString a, Parser_JSON.JString b) -> a = b
     | (Parser_JSON.JNumber a, Parser_JSON.JNumber b) ->
         XSD_IEEE754.json_number_eq a b
     | (Parser_JSON.JArray xs, Parser_JSON.JArray ys) ->
         json_arr_eq (fuel - Prims.int_one) xs ys
     | (Parser_JSON.JObject fs, Parser_JSON.JObject gs) ->
         ((FStar_List_Tot_Base.length fs) = (FStar_List_Tot_Base.length gs))
           && (json_obj_eq (fuel - Prims.int_one) fs gs)
     | (uu___1, uu___2) -> false)
and json_arr_eq (fuel : Prims.nat) (xs : Parser_JSON.json_val Prims.list)
  (ys : Parser_JSON.json_val Prims.list) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match (xs, ys) with
     | ([], []) -> true
     | (x::xr, y::yr) ->
         (json_value_eq (fuel - Prims.int_one) x y) &&
           (json_arr_eq (fuel - Prims.int_one) xr yr)
     | (uu___1, uu___2) -> false)
and json_obj_eq (fuel : Prims.nat)
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list)
  (gs : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match fs with
     | [] -> true
     | (k, v)::rest ->
         (match FStar_List_Tot_Base.assoc k gs with
          | FStar_Pervasives_Native.Some v' ->
              (json_value_eq (fuel - Prims.int_one) v v') &&
                (json_obj_eq (fuel - Prims.int_one) rest gs)
          | FStar_Pervasives_Native.None -> false))
let rdf_json_value_eq (lex1 : Prims.string) (lex2 : Prims.string) :
  Prims.bool=
  match ((Parser_JSON.parse_json lex1), (Parser_JSON.parse_json lex2)) with
  | (FStar_Pervasives_Native.Some v1, FStar_Pervasives_Native.Some v2) ->
      json_value_eq
        (((Parser_JSON.json_size v1) + (Parser_JSON.json_size v2)) +
           Prims.int_one) v1 v2
  | (uu___, uu___1) -> lex1 = lex2
let is_exact_scaled_dt (dt : RDF_Term.wf_iri) : Prims.bool=
  (dt = RDF_Term.xsd_integer) || (dt = RDF_Term.xsd_decimal)
let lit_opaque_eq (l1 : RDF_Term.literal) (l2 : RDF_Term.literal) :
  Prims.bool=
  (((l1.RDF_Term.lexical_form = l2.RDF_Term.lexical_form) &&
      (l1.RDF_Term.datatype = l2.RDF_Term.datatype))
     && (l1.RDF_Term.lang_tag = l2.RDF_Term.lang_tag))
    && (l1.RDF_Term.direction = l2.RDF_Term.direction)
let dt_value_leq (inside_tt : Prims.bool) (l1 : RDF_Term.literal)
  (l2 : RDF_Term.literal) : Prims.bool=
  if
    (inside_tt &&
       (FStar_Pervasives_Native.uu___is_Some l1.RDF_Term.direction))
      && (FStar_Pervasives_Native.uu___is_Some l2.RDF_Term.direction)
  then lit_opaque_eq l1 l2
  else
    if
      (l1.RDF_Term.datatype = RDF_Term.xsd_double) &&
        (l2.RDF_Term.datatype = RDF_Term.xsd_double)
    then
      XSD_IEEE754.double_value_eq l1.RDF_Term.lexical_form
        l2.RDF_Term.lexical_form
    else
      if
        (l1.RDF_Term.datatype = XSD_Datatypes.xsd_float) &&
          (l2.RDF_Term.datatype = XSD_Datatypes.xsd_float)
      then
        XSD_IEEE754.float_value_eq l1.RDF_Term.lexical_form
          l2.RDF_Term.lexical_form
      else
        if
          (l1.RDF_Term.datatype = rdf_json_iri) &&
            (l2.RDF_Term.datatype = rdf_json_iri)
        then
          rdf_json_value_eq l1.RDF_Term.lexical_form l2.RDF_Term.lexical_form
        else
          if
            (is_exact_scaled_dt l1.RDF_Term.datatype) &&
              (is_exact_scaled_dt l2.RDF_Term.datatype)
          then
            (match ((XSD_Datatypes.literal_to_scaled l1),
                     (XSD_Datatypes.literal_to_scaled l2))
             with
             | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some
                s2) ->
                 (l1.RDF_Term.datatype = l2.RDF_Term.datatype) &&
                   ((XSD_Datatypes.scaled_cmp s1 s2) = Prims.int_zero)
             | (uu___4, uu___5) -> RDF_Term.literal_eq l1 l2)
          else RDF_Term.literal_eq l1 l2
let bnd_rdf (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l ->
      Prims.op_Negation
        (XSD_Datatypes.literal_ill_formed l.RDF_Term.datatype
           l.RDF_Term.lexical_form)
  | uu___ -> true
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
let rdf12_reifies_closure (ts : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.op_At ts
    (FStar_List_Tot_Base.collect reifies_prop_triples ts)
let rdfs_regime_fuel : Prims.nat= (Prims.of_int (100))
let rdf12_vocabulary_axioms : RDF_Triple.triple Prims.list=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI rdf_reifies_iri);
     RDF_Triple.p = RDFS_Closure.rdfs_range;
     RDF_Triple.o = (RDF_Term.T_IRI rdfs_proposition_iri)
   }]
let rdfs_regime_closure (ts : RDF_Triple.triple Prims.list) :
  RDF_Triple.triple Prims.list=
  RDFS_Closure.rdfs_closure
    (FStar_List_Tot_Base.op_At rdf12_vocabulary_axioms
       (rdf12_reifies_closure ts)) rdfs_regime_fuel
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
type gtriple =
  {
  gs: RDF_Term.rdf_term ;
  gp: RDF_Term.wf_iri ;
  go: RDF_Term.rdf_term }
let __proj__Mkgtriple__item__gs (projectee : gtriple) : RDF_Term.rdf_term=
  match projectee with | { gs; gp; go;_} -> gs
let __proj__Mkgtriple__item__gp (projectee : gtriple) : RDF_Term.wf_iri=
  match projectee with | { gs; gp; go;_} -> gp
let __proj__Mkgtriple__item__go (projectee : gtriple) : RDF_Term.rdf_term=
  match projectee with | { gs; gp; go;_} -> go
let gtriple_of_triple (t : RDF_Triple.triple) : gtriple=
  {
    gs = (RDF_Entailment_Simple.subj_as_term t.RDF_Triple.s);
    gp = (t.RDF_Triple.p);
    go = (t.RDF_Triple.o)
  }
let match_subj_g (bnd : RDF_Term.rdf_term -> Prims.bool)
  (b : RDF_Entailment_Simple.binding) (ps : RDF_Term.subject)
  (gs : RDF_Term.rdf_term) :
  RDF_Entailment_Simple.binding FStar_Pervasives_Native.option=
  match ps with
  | RDF_Term.S_BNode lbl ->
      (match FStar_List_Tot_Base.assoc lbl b with
       | FStar_Pervasives_Native.Some t ->
           if RDF_Term.rdf_term_eq t gs
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None ->
           if bnd gs
           then FStar_Pervasives_Native.Some ((lbl, gs) :: b)
           else FStar_Pervasives_Native.None)
  | RDF_Term.S_IRI i ->
      (match gs with
       | RDF_Term.T_IRI j ->
           if i = j
           then FStar_Pervasives_Native.Some b
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
let match_gtriple
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (b : RDF_Entailment_Simple.binding)
  (tb : RDF_Triple.triple) (ta : gtriple) :
  RDF_Entailment_Simple.binding FStar_Pervasives_Native.option=
  if tb.RDF_Triple.p = ta.gp
  then
    match match_subj_g bnd b tb.RDF_Triple.s ta.gs with
    | FStar_Pervasives_Native.Some b1 ->
        RDF_Entailment_Simple.match_term leq bnd false b1 tb.RDF_Triple.o
          ta.go
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.None
let rec try_match_g
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (bs : RDF_Triple.triple Prims.list)
  (b : RDF_Entailment_Simple.binding) (a : gtriple Prims.list) : Prims.bool=
  match bs with
  | [] -> true
  | tb::rest -> try_alts_g leq bnd bs tb rest b a a
and try_alts_g
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (bs : RDF_Triple.triple Prims.list)
  (tb : RDF_Triple.triple) (rest : RDF_Triple.triple Prims.list)
  (b : RDF_Entailment_Simple.binding) (a : gtriple Prims.list)
  (cand : gtriple Prims.list) : Prims.bool=
  match cand with
  | [] -> false
  | ta::more ->
      (match match_gtriple leq bnd b tb ta with
       | FStar_Pervasives_Native.Some b1 ->
           if try_match_g leq bnd rest b1 a
           then true
           else try_alts_g leq bnd bs tb rest b a more
       | FStar_Pervasives_Native.None ->
           try_alts_g leq bnd bs tb rest b a more)
let entails_g
  (leq : Prims.bool -> RDF_Term.literal -> RDF_Term.literal -> Prims.bool)
  (bnd : RDF_Term.rdf_term -> Prims.bool) (a : gtriple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool= try_match_g leq bnd b [] a
let rec tt_occurrences (t : RDF_Term.rdf_term) :
  RDF_Term.rdf_term Prims.list=
  match t with
  | RDF_Term.T_TripleTerm (uu___, uu___1, o) -> t :: (tt_occurrences o)
  | uu___ -> []
let graph_tt_occurrences (ts : RDF_Triple.triple Prims.list) :
  RDF_Term.rdf_term Prims.list=
  FStar_List_Tot_Base.collect (fun t -> tt_occurrences t.RDF_Triple.o) ts
let proposition_gtriples (ts : RDF_Triple.triple Prims.list) :
  gtriple Prims.list=
  FStar_List_Tot_Base.map
    (fun tt ->
       {
         gs = tt;
         gp = rdf_type_iri;
         go = (RDF_Term.T_IRI rdfs_proposition_iri)
       }) (graph_tt_occurrences ts)
let is_recognized_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  ((((dt = RDF_Term.xsd_boolean) || (dt = XSD_Datatypes.xsd_dateTime)) ||
      (dt = XSD_Datatypes.xsd_float))
     || (dt = RDF_Term.xsd_double))
    || (XSD_Datatypes.is_decimal_derived_datatype dt)
let literal_type_gtriples (ts : RDF_Triple.triple Prims.list) :
  gtriple Prims.list=
  FStar_List_Tot_Base.collect
    (fun t ->
       match t.RDF_Triple.o with
       | RDF_Term.T_Literal l ->
           if
             (is_recognized_datatype l.RDF_Term.datatype) &&
               (Prims.op_Negation
                  (XSD_Datatypes.literal_ill_formed l.RDF_Term.datatype
                     l.RDF_Term.lexical_form))
           then
             [{
                gs = (RDF_Term.T_Literal l);
                gp = rdf_type_iri;
                go = (RDF_Term.T_IRI (l.RDF_Term.datatype))
              }]
           else []
       | uu___ -> []) ts
let rdf_regime_gclosure (ts : RDF_Triple.triple Prims.list) :
  gtriple Prims.list=
  FStar_List_Tot_Base.op_At (FStar_List_Tot_Base.map gtriple_of_triple ts)
    (FStar_List_Tot_Base.op_At (literal_type_gtriples ts)
       (proposition_gtriples ts))
let subclass_targets (closed : RDF_Triple.triple Prims.list)
  (c : RDF_Term.wf_iri) : RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.collect
    (fun t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI a, RDF_Term.T_IRI b) ->
             (if a = c then [b] else [])
         | (uu___, uu___1) -> []
       else []) closed
let rdfs9_over_gtriples (closed : RDF_Triple.triple Prims.list)
  (gts : gtriple Prims.list) : gtriple Prims.list=
  FStar_List_Tot_Base.collect
    (fun g ->
       if g.gp = rdf_type_iri
       then
         match g.go with
         | RDF_Term.T_IRI c ->
             FStar_List_Tot_Base.map
               (fun d ->
                  { gs = (g.gs); gp = rdf_type_iri; go = (RDF_Term.T_IRI d) })
               (subclass_targets closed c)
         | uu___ -> []
       else []) gts
let range_targets (closed : RDF_Triple.triple Prims.list)
  (p : RDF_Term.wf_iri) : RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.collect
    (fun t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_range
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI a, RDF_Term.T_IRI b) ->
             (if a = p then [b] else [])
         | (uu___, uu___1) -> []
       else []) closed
let rdfs3_over_gtriples (closed : RDF_Triple.triple Prims.list) :
  gtriple Prims.list=
  FStar_List_Tot_Base.collect
    (fun t ->
       match t.RDF_Triple.o with
       | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) ->
           FStar_List_Tot_Base.map
             (fun d ->
                {
                  gs = (t.RDF_Triple.o);
                  gp = rdf_type_iri;
                  go = (RDF_Term.T_IRI d)
                }) (range_targets closed t.RDF_Triple.p)
       | RDF_Term.T_Literal uu___ ->
           FStar_List_Tot_Base.map
             (fun d ->
                {
                  gs = (t.RDF_Triple.o);
                  gp = rdf_type_iri;
                  go = (RDF_Term.T_IRI d)
                }) (range_targets closed t.RDF_Triple.p)
       | uu___ -> []) closed
let rdfs_regime_gclosure (ts : RDF_Triple.triple Prims.list) :
  gtriple Prims.list=
  let closed = rdfs_regime_closure ts in
  let base =
    FStar_List_Tot_Base.op_At (rdf_regime_gclosure closed)
      (rdfs3_over_gtriples closed) in
  FStar_List_Tot_Base.op_At base (rdfs9_over_gtriples closed base)
let rec term_ill_formed (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l ->
      XSD_Datatypes.literal_ill_formed l.RDF_Term.datatype
        l.RDF_Term.lexical_form
  | RDF_Term.T_TripleTerm (uu___, uu___1, o) -> term_ill_formed o
  | uu___ -> false
let rdf_inconsistent (ts : RDF_Triple.triple Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb (fun t -> term_ill_formed t.RDF_Triple.o) ts
let entails_rdf (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  entails_g dt_value_leq bnd_rdf (rdf_regime_gclosure a) b
let entails_rdfs (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  entails_g dt_value_leq bnd_rdf (rdfs_regime_gclosure a) b
let entails_rdfs_plus (a : RDF_Triple.triple Prims.list)
  (b : RDF_Triple.triple Prims.list) : Prims.bool=
  let closed = owl_closure (rdfs_regime_closure a) in
  entails_g dt_value_leq bnd_rdf (rdf_regime_gclosure closed) b
