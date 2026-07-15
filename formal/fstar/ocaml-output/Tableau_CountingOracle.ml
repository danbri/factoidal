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
let z3_check_sat (smtlib : Prims.string) (rlimit : Prims.nat) : z3_verdict=
    (* Issue #296: Phase-0 Z3_Unknown -- z3 NOT consulted yet; never
     fabricate Z3_Unsat/Z3_Sat. See
     minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh *)
  Z3_Unknown
