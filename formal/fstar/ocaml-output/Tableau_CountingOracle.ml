open Prims
type z3_verdict =
  | Z3_Sat 
  | Z3_Unsat 
  | Z3_Unknown 
  | Z3_Timeout 
let uu___is_Z3_Sat (projectee : z3_verdict) : Prims.bool=
  match projectee with | Z3_Sat -> true | uu___ -> false
let uu___is_Z3_Unsat (projectee : z3_verdict) : Prims.bool=
  match projectee with | Z3_Unsat -> true | uu___ -> false
let uu___is_Z3_Unknown (projectee : z3_verdict) : Prims.bool=
  match projectee with | Z3_Unknown -> true | uu___ -> false
let uu___is_Z3_Timeout (projectee : z3_verdict) : Prims.bool=
  match projectee with | Z3_Timeout -> true | uu___ -> false
let ico_rdf_type : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let ico_owl_onProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onProperty"
let ico_owl_onClass : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onClass"
let ico_owl_minCardinality : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#minCardinality"
let ico_owl_maxCardinality : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#maxCardinality"
let ico_owl_cardinality : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#cardinality"
let ico_owl_minQualifiedCardinality : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"
let ico_owl_maxQualifiedCardinality : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"
let ico_owl_qualifiedCardinality : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"
let ico_owl_FunctionalProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#FunctionalProperty"
let ico_owl_InverseFunctionalProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"
let ico_owl_differentFrom : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#differentFrom"
let ico_owl_complementOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#complementOf"
let ico_owl_datatypeComplementOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#datatypeComplementOf"
let ico_owl_onDatatype : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onDatatype"
let ico_owl_withRestrictions : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#withRestrictions"
let ico_owl_onDataRange : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onDataRange"
let ico_owl_DatatypeProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#DatatypeProperty"
let ico_xsd_minInclusive : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minInclusive"
let ico_xsd_maxInclusive : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxInclusive"
let ico_xsd_minExclusive : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minExclusive"
let ico_xsd_maxExclusive : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxExclusive"
let ico_xsd_pattern : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#pattern"
let ico_xsd_length : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#length"
let ico_xsd_minLength : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minLength"
let ico_xsd_maxLength : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxLength"
type card_bound =
  | CB_Min of Prims.nat 
  | CB_Max of Prims.nat 
  | CB_Exact of Prims.nat 
let uu___is_CB_Min (projectee : card_bound) : Prims.bool=
  match projectee with | CB_Min _0 -> true | uu___ -> false
let __proj__CB_Min__item___0 (projectee : card_bound) : Prims.nat=
  match projectee with | CB_Min _0 -> _0
let uu___is_CB_Max (projectee : card_bound) : Prims.bool=
  match projectee with | CB_Max _0 -> true | uu___ -> false
let __proj__CB_Max__item___0 (projectee : card_bound) : Prims.nat=
  match projectee with | CB_Max _0 -> _0
let uu___is_CB_Exact (projectee : card_bound) : Prims.bool=
  match projectee with | CB_Exact _0 -> true | uu___ -> false
let __proj__CB_Exact__item___0 (projectee : card_bound) : Prims.nat=
  match projectee with | CB_Exact _0 -> _0
type count_axiom =
  {
  ca_subj: RDF_Term.rdf_term ;
  ca_role: RDF_Term.wf_iri ;
  ca_filler: RDF_Term.wf_iri FStar_Pervasives_Native.option ;
  ca_bound: card_bound }
let __proj__Mkcount_axiom__item__ca_subj (projectee : count_axiom) :
  RDF_Term.rdf_term=
  match projectee with
  | { ca_subj; ca_role; ca_filler; ca_bound;_} -> ca_subj
let __proj__Mkcount_axiom__item__ca_role (projectee : count_axiom) :
  RDF_Term.wf_iri=
  match projectee with
  | { ca_subj; ca_role; ca_filler; ca_bound;_} -> ca_role
let __proj__Mkcount_axiom__item__ca_filler (projectee : count_axiom) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with
  | { ca_subj; ca_role; ca_filler; ca_bound;_} -> ca_filler
let __proj__Mkcount_axiom__item__ca_bound (projectee : count_axiom) :
  card_bound=
  match projectee with
  | { ca_subj; ca_role; ca_filler; ca_bound;_} -> ca_bound
type counting_ast =
  {
  cx_individuals: RDF_Term.rdf_term Prims.list ;
  cx_axioms: count_axiom Prims.list ;
  cx_distinct: (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list }
let __proj__Mkcounting_ast__item__cx_individuals (projectee : counting_ast) :
  RDF_Term.rdf_term Prims.list=
  match projectee with
  | { cx_individuals; cx_axioms; cx_distinct;_} -> cx_individuals
let __proj__Mkcounting_ast__item__cx_axioms (projectee : counting_ast) :
  count_axiom Prims.list=
  match projectee with
  | { cx_individuals; cx_axioms; cx_distinct;_} -> cx_axioms
let __proj__Mkcounting_ast__item__cx_distinct (projectee : counting_ast) :
  (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list=
  match projectee with
  | { cx_individuals; cx_axioms; cx_distinct;_} -> cx_distinct
let ico_is_card_pred (p : RDF_Term.wf_iri) : Prims.bool=
  (((((p = ico_owl_minCardinality) || (p = ico_owl_maxCardinality)) ||
       (p = ico_owl_cardinality))
      || (p = ico_owl_minQualifiedCardinality))
     || (p = ico_owl_maxQualifiedCardinality))
    || (p = ico_owl_qualifiedCardinality)
let ico_bound_of (p : RDF_Term.wf_iri) (k : Prims.nat) :
  card_bound FStar_Pervasives_Native.option=
  if (p = ico_owl_minCardinality) || (p = ico_owl_minQualifiedCardinality)
  then FStar_Pervasives_Native.Some (CB_Min k)
  else
    if (p = ico_owl_maxCardinality) || (p = ico_owl_maxQualifiedCardinality)
    then FStar_Pervasives_Native.Some (CB_Max k)
    else
      if (p = ico_owl_cardinality) || (p = ico_owl_qualifiedCardinality)
      then FStar_Pervasives_Native.Some (CB_Exact k)
      else FStar_Pervasives_Native.None
let ico_axiom_of (g : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) :
  count_axiom FStar_Pervasives_Native.option=
  if Prims.op_Negation (ico_is_card_pred t.RDF_Triple.p)
  then FStar_Pervasives_Native.None
  else
    (match t.RDF_Triple.o with
     | RDF_Term.T_Literal l ->
         (match Tableau.cardinality_literal_to_nat l.RDF_Term.lexical_form
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some k ->
              (match ico_bound_of t.RDF_Triple.p k with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some b ->
                   (match Tableau.find_first_object g t.RDF_Triple.s
                            ico_owl_onProperty
                    with
                    | FStar_Pervasives_Native.Some (RDF_Term.T_IRI role) ->
                        let filler =
                          match Tableau.find_first_object g t.RDF_Triple.s
                                  ico_owl_onClass
                          with
                          | FStar_Pervasives_Native.Some (RDF_Term.T_IRI c)
                              -> FStar_Pervasives_Native.Some c
                          | uu___1 -> FStar_Pervasives_Native.None in
                        FStar_Pervasives_Native.Some
                          {
                            ca_subj =
                              (RDF_Graph.subject_to_term t.RDF_Triple.s);
                            ca_role = role;
                            ca_filler = filler;
                            ca_bound = b
                          }
                    | uu___1 -> FStar_Pervasives_Native.None)))
     | uu___1 -> FStar_Pervasives_Native.None)
let rec ico_axioms (g : RDF_Graph.rdf_graph)
  (ts : RDF_Triple.triple Prims.list) : count_axiom Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      FStar_List_Tot_Base.op_At
        (match ico_axiom_of g t with
         | FStar_Pervasives_Native.Some a -> [a]
         | FStar_Pervasives_Native.None -> []) (ico_axioms g tl)
let rec ico_distinct_pairs (ts : RDF_Triple.triple Prims.list) :
  (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      FStar_List_Tot_Base.op_At
        (if t.RDF_Triple.p = ico_owl_differentFrom
         then
           [((RDF_Graph.subject_to_term t.RDF_Triple.s), (t.RDF_Triple.o))]
         else []) (ico_distinct_pairs tl)
let rec ico_mem_term (t : RDF_Term.rdf_term)
  (xs : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | h::tl -> (RDF_Term.rdf_term_eq h t) || (ico_mem_term t tl)
let rec ico_dedup (xs : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match xs with
  | [] -> []
  | h::tl -> if ico_mem_term h tl then ico_dedup tl else h :: (ico_dedup tl)
let ico_axiom_subj (a : count_axiom) : RDF_Term.rdf_term= a.ca_subj
let ico_fst (p : (RDF_Term.rdf_term * RDF_Term.rdf_term)) :
  RDF_Term.rdf_term= FStar_Pervasives_Native.fst p
let ico_snd (p : (RDF_Term.rdf_term * RDF_Term.rdf_term)) :
  RDF_Term.rdf_term= FStar_Pervasives_Native.snd p
let extract_counting_fragment (g : RDF_Graph.rdf_graph) : counting_ast=
  let axs = ico_axioms g g in
  let dis = ico_distinct_pairs g in
  let inds =
    ico_dedup
      (FStar_List_Tot_Base.op_At (FStar_List_Tot_Base.map ico_fst dis)
         (FStar_List_Tot_Base.op_At (FStar_List_Tot_Base.map ico_snd dis)
            (FStar_List_Tot_Base.map ico_axiom_subj axs))) in
  { cx_individuals = inds; cx_axioms = axs; cx_distinct = dis }
let ico_is_facet_pred (p : RDF_Term.wf_iri) : Prims.bool=
  (((((((p = ico_xsd_minInclusive) || (p = ico_xsd_maxInclusive)) ||
         (p = ico_xsd_minExclusive))
        || (p = ico_xsd_maxExclusive))
       || (p = ico_xsd_pattern))
      || (p = ico_xsd_length))
     || (p = ico_xsd_minLength))
    || (p = ico_xsd_maxLength)
let ico_authored_complement (t : RDF_Triple.triple) : Prims.bool=
  (t.RDF_Triple.p = ico_owl_complementOf) &&
    (match t.RDF_Triple.s with
     | RDF_Term.S_BNode b ->
         Prims.op_Negation (OWL_Closure.bnode_is_rl_canonical b)
     | RDF_Term.S_IRI uu___ -> true)
let ico_reject_triple (t : RDF_Triple.triple) : Prims.bool=
  ((((((t.RDF_Triple.p = ico_owl_onDatatype) ||
         (t.RDF_Triple.p = ico_owl_withRestrictions))
        || (t.RDF_Triple.p = ico_owl_datatypeComplementOf))
       || (t.RDF_Triple.p = ico_owl_onDataRange))
      || (ico_authored_complement t))
     || (ico_is_facet_pred t.RDF_Triple.p))
    ||
    ((t.RDF_Triple.p = ico_rdf_type) &&
       (match t.RDF_Triple.o with
        | RDF_Term.T_IRI i -> i = ico_owl_DatatypeProperty
        | uu___ -> false))
let ico_has_reject (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb ico_reject_triple g
let ico_counting_triple (t : RDF_Triple.triple) : Prims.bool=
  (ico_is_card_pred t.RDF_Triple.p) ||
    ((t.RDF_Triple.p = ico_rdf_type) &&
       (match t.RDF_Triple.o with
        | RDF_Term.T_IRI i ->
            (i = ico_owl_FunctionalProperty) ||
              (i = ico_owl_InverseFunctionalProperty)
        | uu___ -> false))
let ico_has_counting (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb ico_counting_triple g
let in_counting_fragment (g : RDF_Graph.rdf_graph) : Prims.bool=
  (Prims.op_Negation (ico_has_reject g)) && (ico_has_counting g)
let rec ico_index_of (xs : RDF_Term.rdf_term Prims.list)
  (t : RDF_Term.rdf_term) (i : Prims.nat) : Prims.nat=
  match xs with
  | [] -> i
  | h::tl ->
      if RDF_Term.rdf_term_eq h t
      then i
      else ico_index_of tl t (i + Prims.int_one)
let rec ico_iri_index (xs : RDF_Term.wf_iri Prims.list) (x : RDF_Term.wf_iri)
  (i : Prims.nat) : Prims.nat=
  match xs with
  | [] -> i
  | h::tl -> if h = x then i else ico_iri_index tl x (i + Prims.int_one)
let rec ico_mem_iri (x : RDF_Term.wf_iri) (xs : RDF_Term.wf_iri Prims.list) :
  Prims.bool=
  match xs with | [] -> false | h::tl -> (h = x) || (ico_mem_iri x tl)
let rec ico_dedup_iri (xs : RDF_Term.wf_iri Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match xs with
  | [] -> []
  | h::tl ->
      if ico_mem_iri h tl then ico_dedup_iri tl else h :: (ico_dedup_iri tl)
let ico_axiom_role (a : count_axiom) : RDF_Term.wf_iri= a.ca_role
let rec ico_filler_iris (axs : count_axiom Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match axs with
  | [] -> []
  | a::tl ->
      FStar_List_Tot_Base.op_At
        (match a.ca_filler with
         | FStar_Pervasives_Native.Some c -> [c]
         | FStar_Pervasives_Native.None -> []) (ico_filler_iris tl)
let ico_var_name (inds : RDF_Term.rdf_term Prims.list)
  (roles : RDF_Term.wf_iri Prims.list) (fillers : RDF_Term.wf_iri Prims.list)
  (a : count_axiom) : Prims.string=
  Prims.strcat "n_s"
    (Prims.strcat
       (Prims.string_of_int (ico_index_of inds a.ca_subj Prims.int_zero))
       (Prims.strcat "_r"
          (Prims.strcat
             (Prims.string_of_int
                (ico_iri_index roles a.ca_role Prims.int_zero))
             (Prims.strcat "_c"
                (match a.ca_filler with
                 | FStar_Pervasives_Native.Some c ->
                     Prims.string_of_int
                       (ico_iri_index fillers c Prims.int_zero)
                 | FStar_Pervasives_Native.None -> "u")))))
let ico_bound_assert (name : Prims.string) (b : card_bound) : Prims.string=
  match b with
  | CB_Min k ->
      Prims.strcat "(assert (>= "
        (Prims.strcat name
           (Prims.strcat " " (Prims.strcat (Prims.string_of_int k) "))\n")))
  | CB_Max k ->
      Prims.strcat "(assert (<= "
        (Prims.strcat name
           (Prims.strcat " " (Prims.strcat (Prims.string_of_int k) "))\n")))
  | CB_Exact k ->
      Prims.strcat "(assert (= "
        (Prims.strcat name
           (Prims.strcat " " (Prims.strcat (Prims.string_of_int k) "))\n")))
let rec ico_str_mem (s : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with | [] -> false | h::tl -> (h = s) || (ico_str_mem s tl)
let rec ico_str_dedup (xs : Prims.string Prims.list) :
  Prims.string Prims.list=
  match xs with
  | [] -> []
  | h::tl ->
      if ico_str_mem h tl then ico_str_dedup tl else h :: (ico_str_dedup tl)
let rec ico_decls (names : Prims.string Prims.list) : Prims.string=
  match names with
  | [] -> ""
  | h::tl ->
      Prims.strcat "(declare-const "
        (Prims.strcat h
           (Prims.strcat " Int)\n(assert (>= "
              (Prims.strcat h (Prims.strcat " 0))\n" (ico_decls tl)))))
let rec ico_bound_asserts (inds : RDF_Term.rdf_term Prims.list)
  (roles : RDF_Term.wf_iri Prims.list) (fillers : RDF_Term.wf_iri Prims.list)
  (axs : count_axiom Prims.list) : Prims.string=
  match axs with
  | [] -> ""
  | a::tl ->
      Prims.strcat
        (ico_bound_assert (ico_var_name inds roles fillers a) a.ca_bound)
        (ico_bound_asserts inds roles fillers tl)
let rec ico_id_decls (inds : RDF_Term.rdf_term Prims.list) (i : Prims.nat) :
  Prims.string=
  match inds with
  | [] -> ""
  | uu___::tl ->
      Prims.strcat "(declare-const id_"
        (Prims.strcat (Prims.string_of_int i)
           (Prims.strcat " Int)\n" (ico_id_decls tl (i + Prims.int_one))))
let rec ico_distinct_asserts (inds : RDF_Term.rdf_term Prims.list)
  (pairs : (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list) :
  Prims.string=
  match pairs with
  | [] -> ""
  | (a, b)::tl ->
      let ia = ico_index_of inds a Prims.int_zero in
      let ib = ico_index_of inds b Prims.int_zero in
      let n = FStar_List_Tot_Base.length inds in
      Prims.strcat
        (if ((ia < n) && (ib < n)) && (ia <> ib)
         then
           Prims.strcat "(assert (not (= id_"
             (Prims.strcat (Prims.string_of_int ia)
                (Prims.strcat " id_"
                   (Prims.strcat (Prims.string_of_int ib) ")))\n")))
         else "") (ico_distinct_asserts inds tl)
let rec ico_var_names (inds : RDF_Term.rdf_term Prims.list)
  (roles : RDF_Term.wf_iri Prims.list) (fillers : RDF_Term.wf_iri Prims.list)
  (axs : count_axiom Prims.list) : Prims.string Prims.list=
  match axs with
  | [] -> []
  | a::tl -> (ico_var_name inds roles fillers a) ::
      (ico_var_names inds roles fillers tl)
let encode_counting_fragment (ast : counting_ast) : Prims.string=
  let inds = ast.cx_individuals in
  let axs = ast.cx_axioms in
  let roles = ico_dedup_iri (FStar_List_Tot_Base.map ico_axiom_role axs) in
  let fillers = ico_dedup_iri (ico_filler_iris axs) in
  let names = ico_str_dedup (ico_var_names inds roles fillers axs) in
  Prims.strcat "(set-logic QF_LIA)\n"
    (Prims.strcat "; Z33kr counting-fragment encoding (Phase 0 skeleton)\n"
       (Prims.strcat (ico_id_decls inds Prims.int_zero)
          (Prims.strcat (ico_distinct_asserts inds ast.cx_distinct)
             (Prims.strcat (ico_decls names)
                (Prims.strcat (ico_bound_asserts inds roles fillers axs)
                   "(check-sat)\n")))))
let ico_rdfs_subClassOf : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let ico_owl_equivalentClass : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#equivalentClass"
let ico_owl_someValuesFrom : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#someValuesFrom"
let ico_owl_inverseOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#inverseOf"
let ico_owl_unionOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#unionOf"
let ico_owl_oneOf2 : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#oneOf"
let ico_owl_disjointWith : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#disjointWith"
let ico_rdfs_domain : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#domain"
let ico_rdfs_range : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#range"
let ico_owl_Thing2 : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Thing"
let ico_digit (c : FStar_Char.char) :
  Prims.nat FStar_Pervasives_Native.option=
  if c = 48
  then FStar_Pervasives_Native.Some Prims.int_zero
  else
    if c = 49
    then FStar_Pervasives_Native.Some Prims.int_one
    else
      if c = 50
      then FStar_Pervasives_Native.Some (Prims.of_int (2))
      else
        if c = 51
        then FStar_Pervasives_Native.Some (Prims.of_int (3))
        else
          if c = 52
          then FStar_Pervasives_Native.Some (Prims.of_int (4))
          else
            if c = 53
            then FStar_Pervasives_Native.Some (Prims.of_int (5))
            else
              if c = 54
              then FStar_Pervasives_Native.Some (Prims.of_int (6))
              else
                if c = 55
                then FStar_Pervasives_Native.Some (Prims.of_int (7))
                else
                  if c = 56
                  then FStar_Pervasives_Native.Some (Prims.of_int (8))
                  else
                    if c = 57
                    then FStar_Pervasives_Native.Some (Prims.of_int (9))
                    else FStar_Pervasives_Native.None
let rec ico_digits (acc : Prims.nat) (cs : FStar_Char.char Prims.list) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::tl ->
      (match ico_digit c with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some d ->
           ico_digits ((acc * (Prims.of_int (10))) + d) tl)
let ico_parse_nat (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | [] -> FStar_Pervasives_Native.None
  | cs -> ico_digits Prims.int_zero cs
let rec ico_all_iris (ts : RDF_Triple.triple Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      FStar_List_Tot_Base.op_At
        (match t.RDF_Triple.s with | RDF_Term.S_IRI i -> [i] | uu___ -> [])
        (FStar_List_Tot_Base.op_At
           (match t.RDF_Triple.o with | RDF_Term.T_IRI i -> [i] | uu___ -> [])
           (ico_all_iris tl))
let ico_cvar (classes : RDF_Term.wf_iri Prims.list) (c : RDF_Term.wf_iri) :
  Prims.string=
  Prims.strcat "c"
    (Prims.string_of_int (ico_iri_index classes c Prims.int_zero))
let rec ico_props_typed (ts : RDF_Triple.triple Prims.list)
  (cls : RDF_Term.wf_iri) : RDF_Term.wf_iri Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      FStar_List_Tot_Base.op_At
        (if
           (t.RDF_Triple.p = ico_rdf_type) &&
             (match t.RDF_Triple.o with
              | RDF_Term.T_IRI i -> i = cls
              | uu___ -> false)
         then
           match t.RDF_Triple.s with | RDF_Term.S_IRI i -> [i] | uu___ -> []
         else []) (ico_props_typed tl cls)
let rec ico_find_dom (ts : RDF_Triple.triple Prims.list)
  (p : RDF_Term.wf_iri) : RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.None
  | t::tl ->
      if
        (t.RDF_Triple.p = ico_rdfs_domain) &&
          ((match t.RDF_Triple.s with
            | RDF_Term.S_IRI i -> i = p
            | uu___ -> false))
      then
        (match t.RDF_Triple.o with
         | RDF_Term.T_IRI i ->
             if i = ico_owl_Thing2
             then ico_find_dom tl p
             else FStar_Pervasives_Native.Some i
         | uu___ -> ico_find_dom tl p)
      else ico_find_dom tl p
let rec ico_find_inv (ts : RDF_Triple.triple Prims.list)
  (p : RDF_Term.wf_iri) : RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.None
  | t::tl ->
      if t.RDF_Triple.p = ico_owl_inverseOf
      then
        (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI a, RDF_Term.T_IRI b) ->
             if a = p
             then FStar_Pervasives_Native.Some b
             else
               if b = p
               then FStar_Pervasives_Native.Some a
               else ico_find_inv tl p
         | uu___ -> ico_find_inv tl p)
      else ico_find_inv tl p
let rec ico_disjoint (ts : RDF_Triple.triple Prims.list)
  (a : RDF_Term.wf_iri) (b : RDF_Term.wf_iri) : Prims.bool=
  match ts with
  | [] -> false
  | t::tl ->
      ((t.RDF_Triple.p = ico_owl_disjointWith) &&
         (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
          | (RDF_Term.S_IRI x, RDF_Term.T_IRI y) ->
              ((x = a) && (y = b)) || ((x = b) && (y = a))
          | uu___ -> false))
        || (ico_disjoint tl a b)
let rec ico_svf_via (g : RDF_Graph.rdf_graph)
  (bs : RDF_Term.rdf_term Prims.list) (p : RDF_Term.wf_iri) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match bs with
  | [] -> FStar_Pervasives_Native.None
  | b::tl ->
      (match Tableau.term_as_subject b with
       | FStar_Pervasives_Native.Some s ->
           (match Tableau.find_first_object g s ico_owl_onProperty with
            | FStar_Pervasives_Native.Some (RDF_Term.T_IRI pp) ->
                if pp = p
                then
                  (match Tableau.find_first_object g s ico_owl_someValuesFrom
                   with
                   | FStar_Pervasives_Native.Some (RDF_Term.T_IRI x) ->
                       FStar_Pervasives_Native.Some x
                   | uu___ -> ico_svf_via g tl p)
                else ico_svf_via g tl p
            | uu___ -> ico_svf_via g tl p)
       | FStar_Pervasives_Native.None -> ico_svf_via g tl p)
let rec ico_exactcard_via (g : RDF_Graph.rdf_graph)
  (bs : RDF_Term.rdf_term Prims.list) (invp : RDF_Term.wf_iri) :
  Prims.nat FStar_Pervasives_Native.option=
  match bs with
  | [] -> FStar_Pervasives_Native.None
  | b::tl ->
      (match Tableau.term_as_subject b with
       | FStar_Pervasives_Native.Some s ->
           (match Tableau.find_first_object g s ico_owl_onProperty with
            | FStar_Pervasives_Native.Some (RDF_Term.T_IRI pp) ->
                if pp = invp
                then
                  (match Tableau.find_first_object g s ico_owl_cardinality
                   with
                   | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
                       (match ico_parse_nat l.RDF_Term.lexical_form with
                        | FStar_Pervasives_Native.Some k ->
                            FStar_Pervasives_Native.Some k
                        | FStar_Pervasives_Native.None ->
                            ico_exactcard_via g tl invp)
                   | uu___ -> ico_exactcard_via g tl invp)
                else ico_exactcard_via g tl invp
            | uu___ -> ico_exactcard_via g tl invp)
       | FStar_Pervasives_Native.None -> ico_exactcard_via g tl invp)
let ico_restr_of (g : RDF_Graph.rdf_graph) (c : RDF_Term.wf_iri) :
  RDF_Term.rdf_term Prims.list=
  FStar_List_Tot_Base.op_At
    (RDF_Graph_Executable.find_objects g (RDF_Term.S_IRI c)
       ico_rdfs_subClassOf)
    (RDF_Graph_Executable.find_objects g (RDF_Term.S_IRI c)
       ico_owl_equivalentClass)
let ico_fiber_of (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (p : RDF_Term.wf_iri) :
  Prims.string=
  match ((ico_find_dom g p), (ico_find_inv g p)) with
  | (FStar_Pervasives_Native.Some d, FStar_Pervasives_Native.Some ip) ->
      (match ico_svf_via g (ico_restr_of g d) p with
       | FStar_Pervasives_Native.Some x ->
           (match ico_exactcard_via g (ico_restr_of g x) ip with
            | FStar_Pervasives_Native.Some k ->
                Prims.strcat "(assert (= "
                  (Prims.strcat (ico_cvar classes d)
                     (Prims.strcat " (* "
                        (Prims.strcat (Prims.string_of_int k)
                           (Prims.strcat " "
                              (Prims.strcat (ico_cvar classes x) ")))\n")))))
            | FStar_Pervasives_Native.None -> "")
       | FStar_Pervasives_Native.None -> "")
  | uu___ -> ""
let rec ico_fiber_asserts (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (ps : RDF_Term.wf_iri Prims.list) :
  Prims.string=
  match ps with
  | [] -> ""
  | p::tl ->
      Prims.strcat (ico_fiber_of g classes p)
        (ico_fiber_asserts g classes tl)
let rec ico_bij_for_prop (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (p : RDF_Term.wf_iri)
  (ip : RDF_Term.wf_iri) (cs : RDF_Term.wf_iri Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | d::tl ->
      let this =
        match ico_svf_via g (ico_restr_of g d) p with
        | FStar_Pervasives_Native.Some y ->
            (match ico_svf_via g (ico_restr_of g y) ip with
             | FStar_Pervasives_Native.Some dback ->
                 if dback = d
                 then
                   Prims.strcat "(assert (= "
                     (Prims.strcat (ico_cvar classes d)
                        (Prims.strcat " "
                           (Prims.strcat (ico_cvar classes y) "))\n")))
                 else ""
             | FStar_Pervasives_Native.None -> "")
        | FStar_Pervasives_Native.None -> "" in
      Prims.strcat this (ico_bij_for_prop g classes p ip tl)
let rec ico_bij_asserts (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (ps : RDF_Term.wf_iri Prims.list) :
  Prims.string=
  match ps with
  | [] -> ""
  | p::tl ->
      Prims.strcat
        (match ico_find_inv g p with
         | FStar_Pervasives_Native.Some ip ->
             ico_bij_for_prop g classes p ip classes
         | FStar_Pervasives_Native.None -> "") (ico_bij_asserts g classes tl)
let ico_union_of_triple (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (t : RDF_Triple.triple) :
  Prims.string=
  if t.RDF_Triple.p = ico_owl_equivalentClass
  then
    match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
    | (RDF_Term.S_IRI z, RDF_Term.T_BNode uu___) ->
        (match Tableau.term_as_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some bs ->
             (match Tableau.find_first_object g bs ico_owl_unionOf with
              | FStar_Pervasives_Native.Some lterm ->
                  (match Tableau.walk_rdf_list g lterm
                           (FStar_List_Tot_Base.length g)
                   with
                   | (RDF_Term.T_IRI m1)::(RDF_Term.T_IRI m2)::[] ->
                       if ico_disjoint g m1 m2
                       then
                         Prims.strcat "(assert (= "
                           (Prims.strcat (ico_cvar classes z)
                              (Prims.strcat " (+ "
                                 (Prims.strcat (ico_cvar classes m1)
                                    (Prims.strcat " "
                                       (Prims.strcat (ico_cvar classes m2)
                                          ")))\n")))))
                       else ""
                   | uu___1 -> "")
              | FStar_Pervasives_Native.None -> "")
         | FStar_Pervasives_Native.None -> "")
    | uu___ -> ""
  else ""
let rec ico_union_asserts (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (ts : RDF_Triple.triple Prims.list)
  : Prims.string=
  match ts with
  | [] -> ""
  | t::tl ->
      Prims.strcat (ico_union_of_triple g classes t)
        (ico_union_asserts g classes tl)
let ico_list_nonempty (g : RDF_Graph.rdf_graph) (head : RDF_Term.rdf_term) :
  Prims.bool=
  match Tableau.term_as_subject head with
  | FStar_Pervasives_Native.Some s ->
      (match Tableau.find_first_object g s OWL_Closure.rdf_first with
       | FStar_Pervasives_Native.Some uu___ -> true
       | FStar_Pervasives_Native.None -> false)
  | FStar_Pervasives_Native.None -> false
let rec ico_any_equiv_oneof (g : RDF_Graph.rdf_graph)
  (bs : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match bs with
  | [] -> false
  | b::tl ->
      (match Tableau.term_as_subject b with
       | FStar_Pervasives_Native.Some s ->
           (match Tableau.find_first_object g s ico_owl_oneOf2 with
            | FStar_Pervasives_Native.Some l -> ico_list_nonempty g l
            | FStar_Pervasives_Native.None -> false)
       | FStar_Pervasives_Native.None -> false) || (ico_any_equiv_oneof g tl)
let ico_class_has_oneof (g : RDF_Graph.rdf_graph) (c : RDF_Term.wf_iri) :
  Prims.bool=
  (match Tableau.find_first_object g (RDF_Term.S_IRI c) ico_owl_oneOf2 with
   | FStar_Pervasives_Native.Some l -> ico_list_nonempty g l
   | FStar_Pervasives_Native.None -> false) ||
    (ico_any_equiv_oneof g
       (RDF_Graph_Executable.find_objects g (RDF_Term.S_IRI c)
          ico_owl_equivalentClass))
let rec ico_oneof_asserts (g : RDF_Graph.rdf_graph)
  (classes : RDF_Term.wf_iri Prims.list) (cs : RDF_Term.wf_iri Prims.list) :
  Prims.string=
  match cs with
  | [] -> ""
  | c::tl ->
      Prims.strcat
        (if ico_class_has_oneof g c
         then
           Prims.strcat "(assert (>= "
             (Prims.strcat (ico_cvar classes c) " 1))\n")
         else "") (ico_oneof_asserts g classes tl)
let rec ico_class_decls (classes : RDF_Term.wf_iri Prims.list)
  (cs : RDF_Term.wf_iri Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::tl ->
      Prims.strcat "(declare-const "
        (Prims.strcat (ico_cvar classes c)
           (Prims.strcat " Int)\n"
              (Prims.strcat "(assert (>= "
                 (Prims.strcat (ico_cvar classes c)
                    (Prims.strcat " 0))\n" (ico_class_decls classes tl))))))
let rec ico_iri_inter (xs : RDF_Term.wf_iri Prims.list)
  (ys : RDF_Term.wf_iri Prims.list) : RDF_Term.wf_iri Prims.list=
  match xs with
  | [] -> []
  | h::tl ->
      FStar_List_Tot_Base.op_At (if ico_mem_iri h ys then [h] else [])
        (ico_iri_inter tl ys)
let encode_counting_smt (g : RDF_Graph.rdf_graph) : Prims.string=
  let classes = ico_dedup_iri (ico_all_iris g) in
  let fprops = ico_props_typed g ico_owl_FunctionalProperty in
  let ifprops = ico_props_typed g ico_owl_InverseFunctionalProperty in
  let bprops = ico_iri_inter fprops ifprops in
  Prims.strcat "(set-logic QF_LIA)\n"
    (Prims.strcat "; Z33kr counting-fragment class-size encoding (Phase 1)\n"
       (Prims.strcat (ico_class_decls classes classes)
          (Prims.strcat (ico_fiber_asserts g classes fprops)
             (Prims.strcat (ico_bij_asserts g classes bprops)
                (Prims.strcat (ico_union_asserts g classes g)
                   (Prims.strcat (ico_oneof_asserts g classes classes)
                      "(check-sat)\n"))))))
let z3_check_sat smtlib rlimit =
  (* Issue #296: Phase-1 native z3 spawn (ASSUME-HOST + ASSUME-IO).
     Realisation ONLY -- satisfiability is z3's semantics; the counting
     encoding is the verified F* Tot function encode_counting_smt. Any
     failure => Z3_Unknown, NEVER a fabricated verdict. See
     minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with _ -> ());
  (try
     let z3bin = (try Sys.getenv "FACTOIDAL_Z3_BIN" with Not_found -> "z3") in
     (* NB: the extracted module opens Prims, so a bare `>` / `*` are the
        Z.t operators. Use Z.gt / Z.zero explicitly and keep rl as a
        Stdlib int only for Printf's %d. *)
     let rl = (try Z.to_int rlimit with _ -> 0) in
     let use_rlimit = (try Z.gt rlimit Z.zero with _ -> false) in
     let smt =
       (if use_rlimit then Printf.sprintf "(set-option :rlimit %d)\n" rl else "")
       ^ smtlib in
     (* child stdout -> parent reads r_out; parent writes w_in -> child stdin *)
     (* cloexec on BOTH pipes: create_process dup2s r_in/w_out onto the
        child's fd0/fd1 (clearing cloexec on those dups), then exec closes
        every remaining cloexec fd -- so the child does NOT inherit the
        parent's write-end of its stdin (w_in). Without this the child
        keeps w_in open, its stdin never reaches EOF, z3 blocks forever,
        and the read below deadlocks (the wall-clock cap then reports it
        as Unknown). *)
     let (r_out, w_out) = Unix.pipe ~cloexec:true () in
     let (r_in, w_in) = Unix.pipe ~cloexec:true () in
     let pid =
       Unix.create_process z3bin [| z3bin; "-in"; "-smt2" |] r_in w_out Unix.stderr in
     Unix.close r_in; Unix.close w_out;
     let oc = Unix.out_channel_of_descr w_in in
     (try output_string oc smt; flush oc with _ -> ());
     (try close_out oc with _ -> ());
     let ic = Unix.in_channel_of_descr r_out in
     let rec read_lines acc =
       match (try Some (input_line ic) with End_of_file -> None) with
       | Some l -> read_lines (l :: acc)
       | None -> List.rev acc in
     let lines = read_lines [] in
     (try close_in ic with _ -> ());
     (try ignore (Unix.waitpid [] pid) with _ -> ());
     let rec first = function
       | [] -> Z3_Unknown
       | l :: tl ->
         (match String.trim l with
          | "unsat" -> Z3_Unsat
          | "sat" -> Z3_Sat
          | "unknown" -> Z3_Unknown
          | _ -> first tl) in
     first lines
   with _ -> Z3_Unknown)
