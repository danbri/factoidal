open Prims
type class_expr =
  | CE_Named of RDF_Term.wf_iri 
  | CE_SomeValuesFrom of RDF_Term.wf_iri * class_expr 
  | CE_AllValuesFrom of RDF_Term.wf_iri * class_expr 
  | CE_HasValue of RDF_Term.wf_iri * RDF_Term.rdf_term 
  | CE_IntersectionOf of class_expr Prims.list 
  | CE_UnionOf of class_expr Prims.list 
  | CE_ComplementOf of class_expr 
  | CE_MinCard of Prims.nat * RDF_Term.wf_iri 
  | CE_MaxCard of Prims.nat * RDF_Term.wf_iri 
  | CE_ExactCard of Prims.nat * RDF_Term.wf_iri 
  | CE_MinQualCard of Prims.nat * RDF_Term.wf_iri * class_expr 
  | CE_MaxQualCard of Prims.nat * RDF_Term.wf_iri * class_expr 
  | CE_ExactQualCard of Prims.nat * RDF_Term.wf_iri * class_expr 
  | CE_Unknown 
let uu___is_CE_Named (projectee : class_expr) : Prims.bool=
  match projectee with | CE_Named _0 -> true | uu___ -> false
let __proj__CE_Named__item___0 (projectee : class_expr) : RDF_Term.wf_iri=
  match projectee with | CE_Named _0 -> _0
let uu___is_CE_SomeValuesFrom (projectee : class_expr) : Prims.bool=
  match projectee with | CE_SomeValuesFrom (_0, _1) -> true | uu___ -> false
let __proj__CE_SomeValuesFrom__item___0 (projectee : class_expr) :
  RDF_Term.wf_iri= match projectee with | CE_SomeValuesFrom (_0, _1) -> _0
let __proj__CE_SomeValuesFrom__item___1 (projectee : class_expr) :
  class_expr= match projectee with | CE_SomeValuesFrom (_0, _1) -> _1
let uu___is_CE_AllValuesFrom (projectee : class_expr) : Prims.bool=
  match projectee with | CE_AllValuesFrom (_0, _1) -> true | uu___ -> false
let __proj__CE_AllValuesFrom__item___0 (projectee : class_expr) :
  RDF_Term.wf_iri= match projectee with | CE_AllValuesFrom (_0, _1) -> _0
let __proj__CE_AllValuesFrom__item___1 (projectee : class_expr) : class_expr=
  match projectee with | CE_AllValuesFrom (_0, _1) -> _1
let uu___is_CE_HasValue (projectee : class_expr) : Prims.bool=
  match projectee with | CE_HasValue (_0, _1) -> true | uu___ -> false
let __proj__CE_HasValue__item___0 (projectee : class_expr) : RDF_Term.wf_iri=
  match projectee with | CE_HasValue (_0, _1) -> _0
let __proj__CE_HasValue__item___1 (projectee : class_expr) :
  RDF_Term.rdf_term= match projectee with | CE_HasValue (_0, _1) -> _1
let uu___is_CE_IntersectionOf (projectee : class_expr) : Prims.bool=
  match projectee with | CE_IntersectionOf _0 -> true | uu___ -> false
let __proj__CE_IntersectionOf__item___0 (projectee : class_expr) :
  class_expr Prims.list= match projectee with | CE_IntersectionOf _0 -> _0
let uu___is_CE_UnionOf (projectee : class_expr) : Prims.bool=
  match projectee with | CE_UnionOf _0 -> true | uu___ -> false
let __proj__CE_UnionOf__item___0 (projectee : class_expr) :
  class_expr Prims.list= match projectee with | CE_UnionOf _0 -> _0
let uu___is_CE_ComplementOf (projectee : class_expr) : Prims.bool=
  match projectee with | CE_ComplementOf _0 -> true | uu___ -> false
let __proj__CE_ComplementOf__item___0 (projectee : class_expr) : class_expr=
  match projectee with | CE_ComplementOf _0 -> _0
let uu___is_CE_MinCard (projectee : class_expr) : Prims.bool=
  match projectee with | CE_MinCard (_0, _1) -> true | uu___ -> false
let __proj__CE_MinCard__item___0 (projectee : class_expr) : Prims.nat=
  match projectee with | CE_MinCard (_0, _1) -> _0
let __proj__CE_MinCard__item___1 (projectee : class_expr) : RDF_Term.wf_iri=
  match projectee with | CE_MinCard (_0, _1) -> _1
let uu___is_CE_MaxCard (projectee : class_expr) : Prims.bool=
  match projectee with | CE_MaxCard (_0, _1) -> true | uu___ -> false
let __proj__CE_MaxCard__item___0 (projectee : class_expr) : Prims.nat=
  match projectee with | CE_MaxCard (_0, _1) -> _0
let __proj__CE_MaxCard__item___1 (projectee : class_expr) : RDF_Term.wf_iri=
  match projectee with | CE_MaxCard (_0, _1) -> _1
let uu___is_CE_ExactCard (projectee : class_expr) : Prims.bool=
  match projectee with | CE_ExactCard (_0, _1) -> true | uu___ -> false
let __proj__CE_ExactCard__item___0 (projectee : class_expr) : Prims.nat=
  match projectee with | CE_ExactCard (_0, _1) -> _0
let __proj__CE_ExactCard__item___1 (projectee : class_expr) :
  RDF_Term.wf_iri= match projectee with | CE_ExactCard (_0, _1) -> _1
let uu___is_CE_MinQualCard (projectee : class_expr) : Prims.bool=
  match projectee with | CE_MinQualCard (_0, _1, _2) -> true | uu___ -> false
let __proj__CE_MinQualCard__item___0 (projectee : class_expr) : Prims.nat=
  match projectee with | CE_MinQualCard (_0, _1, _2) -> _0
let __proj__CE_MinQualCard__item___1 (projectee : class_expr) :
  RDF_Term.wf_iri= match projectee with | CE_MinQualCard (_0, _1, _2) -> _1
let __proj__CE_MinQualCard__item___2 (projectee : class_expr) : class_expr=
  match projectee with | CE_MinQualCard (_0, _1, _2) -> _2
let uu___is_CE_MaxQualCard (projectee : class_expr) : Prims.bool=
  match projectee with | CE_MaxQualCard (_0, _1, _2) -> true | uu___ -> false
let __proj__CE_MaxQualCard__item___0 (projectee : class_expr) : Prims.nat=
  match projectee with | CE_MaxQualCard (_0, _1, _2) -> _0
let __proj__CE_MaxQualCard__item___1 (projectee : class_expr) :
  RDF_Term.wf_iri= match projectee with | CE_MaxQualCard (_0, _1, _2) -> _1
let __proj__CE_MaxQualCard__item___2 (projectee : class_expr) : class_expr=
  match projectee with | CE_MaxQualCard (_0, _1, _2) -> _2
let uu___is_CE_ExactQualCard (projectee : class_expr) : Prims.bool=
  match projectee with
  | CE_ExactQualCard (_0, _1, _2) -> true
  | uu___ -> false
let __proj__CE_ExactQualCard__item___0 (projectee : class_expr) : Prims.nat=
  match projectee with | CE_ExactQualCard (_0, _1, _2) -> _0
let __proj__CE_ExactQualCard__item___1 (projectee : class_expr) :
  RDF_Term.wf_iri= match projectee with | CE_ExactQualCard (_0, _1, _2) -> _1
let __proj__CE_ExactQualCard__item___2 (projectee : class_expr) : class_expr=
  match projectee with | CE_ExactQualCard (_0, _1, _2) -> _2
let uu___is_CE_Unknown (projectee : class_expr) : Prims.bool=
  match projectee with | CE_Unknown -> true | uu___ -> false
let find_first_object (g : RDF_Graph.rdf_graph) (subj : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match RDF_Graph_Executable.find_objects g subj pred with
  | [] -> FStar_Pervasives_Native.None
  | h::uu___ -> FStar_Pervasives_Native.Some h
let term_as_subject (t : RDF_Term.rdf_term) :
  RDF_Term.subject FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_IRI i -> FStar_Pervasives_Native.Some (RDF_Term.S_IRI i)
  | RDF_Term.T_BNode b -> FStar_Pervasives_Native.Some (RDF_Term.S_BNode b)
  | uu___ -> FStar_Pervasives_Native.None
let rec walk_rdf_list (g : RDF_Graph.rdf_graph) (head : RDF_Term.rdf_term)
  (fuel : Prims.nat) : RDF_Term.rdf_term Prims.list=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> []
  | n ->
      (match head with
       | RDF_Term.T_IRI i -> if i = OWL_Vocabulary.rdf_nil then [] else []
       | RDF_Term.T_BNode uu___ ->
           (match term_as_subject head with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some s ->
                let first = find_first_object g s OWL_Vocabulary.rdf_first in
                let rest = find_first_object g s OWL_Vocabulary.rdf_rest in
                (match (first, rest) with
                 | (FStar_Pervasives_Native.Some h,
                    FStar_Pervasives_Native.Some t) -> h ::
                     (walk_rdf_list g t (n - Prims.int_one))
                 | (uu___1, uu___2) -> []))
       | uu___ -> [])
let cardinality_literal_to_nat (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  if s = "0"
  then FStar_Pervasives_Native.Some Prims.int_zero
  else
    if s = "1"
    then FStar_Pervasives_Native.Some Prims.int_one
    else
      if s = "2"
      then FStar_Pervasives_Native.Some (Prims.of_int (2))
      else
        if s = "3"
        then FStar_Pervasives_Native.Some (Prims.of_int (3))
        else
          if s = "4"
          then FStar_Pervasives_Native.Some (Prims.of_int (4))
          else
            if s = "5"
            then FStar_Pervasives_Native.Some (Prims.of_int (5))
            else
              if s = "6"
              then FStar_Pervasives_Native.Some (Prims.of_int (6))
              else
                if s = "7"
                then FStar_Pervasives_Native.Some (Prims.of_int (7))
                else
                  if s = "8"
                  then FStar_Pervasives_Native.Some (Prims.of_int (8))
                  else
                    if s = "9"
                    then FStar_Pervasives_Native.Some (Prims.of_int (9))
                    else FStar_Pervasives_Native.None
let cardinality_value (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject)
  (pred : RDF_Term.wf_iri) : Prims.nat FStar_Pervasives_Native.option=
  match find_first_object g s pred with
  | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
      cardinality_literal_to_nat l.RDF_Term.lexical_form
  | uu___ -> FStar_Pervasives_Native.None
let rec parse_class_expr (g : RDF_Graph.rdf_graph) (t : RDF_Term.rdf_term)
  (fuel : Prims.nat) : class_expr=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> CE_Unknown
  | n ->
      (match t with
       | RDF_Term.T_IRI i -> CE_Named i
       | RDF_Term.T_BNode uu___ ->
           (match term_as_subject t with
            | FStar_Pervasives_Native.None -> CE_Unknown
            | FStar_Pervasives_Native.Some s ->
                (match find_first_object g s
                         OWL_Vocabulary.owl_intersectionOf
                 with
                 | FStar_Pervasives_Native.Some list_head ->
                     let items = walk_rdf_list g list_head n in
                     CE_IntersectionOf
                       (parse_class_expr_list g items (n - Prims.int_one))
                 | FStar_Pervasives_Native.None ->
                     (match find_first_object g s OWL_Vocabulary.owl_unionOf
                      with
                      | FStar_Pervasives_Native.Some list_head ->
                          let items = walk_rdf_list g list_head n in
                          CE_UnionOf
                            (parse_class_expr_list g items
                               (n - Prims.int_one))
                      | FStar_Pervasives_Native.None ->
                          (match find_first_object g s
                                   OWL_Vocabulary.owl_complementOf
                           with
                           | FStar_Pervasives_Native.Some c ->
                               CE_ComplementOf
                                 (parse_class_expr g c (n - Prims.int_one))
                           | FStar_Pervasives_Native.None ->
                               (match find_first_object g s
                                        OWL_Vocabulary.owl_onProperty
                                with
                                | FStar_Pervasives_Native.Some
                                    (RDF_Term.T_IRI p) ->
                                    (match find_first_object g s
                                             OWL_Vocabulary.owl_someValuesFrom
                                     with
                                     | FStar_Pervasives_Native.Some c ->
                                         CE_SomeValuesFrom
                                           (p,
                                             (parse_class_expr g c
                                                (n - Prims.int_one)))
                                     | FStar_Pervasives_Native.None ->
                                         (match find_first_object g s
                                                  OWL_Vocabulary.owl_allValuesFrom
                                          with
                                          | FStar_Pervasives_Native.Some c ->
                                              CE_AllValuesFrom
                                                (p,
                                                  (parse_class_expr g c
                                                     (n - Prims.int_one)))
                                          | FStar_Pervasives_Native.None ->
                                              (match find_first_object g s
                                                       OWL_Vocabulary.owl_hasValue
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   v -> CE_HasValue (p, v)
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (match cardinality_value g
                                                            s
                                                            OWL_Vocabulary.owl_minQualifiedCardinality
                                                    with
                                                    | FStar_Pervasives_Native.Some
                                                        k ->
                                                        (match find_first_object
                                                                 g s
                                                                 OWL_Vocabulary.owl_onClass
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             c ->
                                                             CE_MinQualCard
                                                               (k, p,
                                                                 (parse_class_expr
                                                                    g c
                                                                    (
                                                                    n -
                                                                    Prims.int_one)))
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             CE_MinCard
                                                               (k, p))
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        (match cardinality_value
                                                                 g s
                                                                 OWL_Vocabulary.owl_maxQualifiedCardinality
                                                         with
                                                         | FStar_Pervasives_Native.Some
                                                             k ->
                                                             (match find_first_object
                                                                    g s
                                                                    OWL_Vocabulary.owl_onClass
                                                              with
                                                              | FStar_Pervasives_Native.Some
                                                                  c ->
                                                                  CE_MaxQualCard
                                                                    (k, p,
                                                                    (parse_class_expr
                                                                    g c
                                                                    (n -
                                                                    Prims.int_one)))
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  CE_MaxCard
                                                                    (k, p))
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             (match cardinality_value
                                                                    g s
                                                                    OWL_Vocabulary.owl_qualifiedCardinality
                                                              with
                                                              | FStar_Pervasives_Native.Some
                                                                  k ->
                                                                  (match 
                                                                    find_first_object
                                                                    g s
                                                                    OWL_Vocabulary.owl_onClass
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    c ->
                                                                    CE_ExactQualCard
                                                                    (k, p,
                                                                    (parse_class_expr
                                                                    g c
                                                                    (n -
                                                                    Prims.int_one)))
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
                                                                    CE_ExactCard
                                                                    (k, p))
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  (match 
                                                                    cardinality_value
                                                                    g s
                                                                    OWL_Vocabulary.owl_minCardinality
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    k ->
                                                                    CE_MinCard
                                                                    (k, p)
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    cardinality_value
                                                                    g s
                                                                    OWL_Vocabulary.owl_maxCardinality
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    k ->
                                                                    CE_MaxCard
                                                                    (k, p)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    cardinality_value
                                                                    g s
                                                                    OWL_Vocabulary.owl_cardinality
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    k ->
                                                                    CE_ExactCard
                                                                    (k, p)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    CE_Unknown)))))))))
                                | uu___1 -> CE_Unknown)))))
       | uu___ -> CE_Unknown)
and parse_class_expr_list (g : RDF_Graph.rdf_graph)
  (ts : RDF_Term.rdf_term Prims.list) (fuel : Prims.nat) :
  class_expr Prims.list=
  match ts with
  | [] -> []
  | h::tl -> (parse_class_expr g h fuel) :: (parse_class_expr_list g tl fuel)
let has_type (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (c : RDF_Term.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
          (RDF_Term.subject_eq t.RDF_Triple.s i))
         &&
         (match t.RDF_Triple.o with
          | RDF_Term.T_IRI o -> o = c
          | uu___ -> false)) g
let find_P_successors (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (p : RDF_Term.wf_iri) : RDF_Term.rdf_term Prims.list=
  RDF_Graph_Executable.find_objects g i p
let rec any_successor_sat (f : RDF_Term.rdf_term -> Prims.bool)
  (xs : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | h::tl -> if f h then true else any_successor_sat f tl
let rec any_disjoint_witness_in (g : RDF_Graph.rdf_graph)
  (i : RDF_Term.subject) (ds : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match ds with
  | [] -> false
  | h::tl ->
      (match h with
       | RDF_Term.T_IRI d_iri ->
           if has_type g i d_iri
           then true
           else any_disjoint_witness_in g i tl
       | uu___ -> any_disjoint_witness_in g i tl)
let rec any_disjoint_witness_sym (g : RDF_Graph.rdf_graph)
  (i : RDF_Term.subject) (c_iri : RDF_Term.wf_iri)
  (subjs : RDF_Term.subject Prims.list) : Prims.bool=
  match subjs with
  | [] -> false
  | h::tl ->
      (match h with
       | RDF_Term.S_IRI d_iri ->
           if has_type g i d_iri
           then true
           else any_disjoint_witness_sym g i c_iri tl
       | uu___ -> any_disjoint_witness_sym g i c_iri tl)
let has_disjoint_witness (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (c_iri : RDF_Term.wf_iri) : Prims.bool=
  let forward =
    RDF_Graph_Executable.find_objects g (RDF_Term.S_IRI c_iri)
      OWL_Vocabulary.owl_disjointWith in
  if any_disjoint_witness_in g i forward
  then true
  else
    (let reverse =
       RDF_Graph_Executable.find_subjects g OWL_Vocabulary.owl_disjointWith
         (RDF_Term.T_IRI c_iri) in
     any_disjoint_witness_sym g i c_iri reverse)
let rec is_member (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (ce : class_expr) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> FStar_Pervasives_Native.None
  | n ->
      (match ce with
       | CE_Unknown -> FStar_Pervasives_Native.None
       | CE_Named c ->
           if has_type g i c
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_HasValue (p, v) ->
           let succs = find_P_successors g i p in
           if any_successor_sat (fun t -> RDF_Term.rdf_term_eq t v) succs
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_SomeValuesFrom (p, c) ->
           let succs = find_P_successors g i p in
           any_is_member g succs c (n - Prims.int_one)
       | CE_AllValuesFrom (p, c) ->
           let succs = find_P_successors g i p in
           all_is_member g succs c (n - Prims.int_one)
       | CE_IntersectionOf ces ->
           is_intersection_member g i ces (n - Prims.int_one)
       | CE_UnionOf ces -> is_union_member g i ces (n - Prims.int_one)
       | CE_ComplementOf c ->
           (match c with
            | CE_Named c_iri ->
                if has_disjoint_witness g i c_iri
                then FStar_Pervasives_Native.Some true
                else
                  (match is_member g i c (n - Prims.int_one) with
                   | FStar_Pervasives_Native.Some b ->
                       FStar_Pervasives_Native.Some (Prims.op_Negation b)
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None)
            | uu___ ->
                (match is_member g i c (n - Prims.int_one) with
                 | FStar_Pervasives_Native.Some b ->
                     FStar_Pervasives_Native.Some (Prims.op_Negation b)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | CE_MinCard (k, p) ->
           let succs = find_P_successors g i p in
           if (FStar_List_Tot_Base.length succs) >= k
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_MaxCard (k, p) ->
           let succs = find_P_successors g i p in
           if
             (k = Prims.int_zero) &&
               ((FStar_List_Tot_Base.length succs) = Prims.int_zero)
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_ExactCard (k, p) ->
           let succs = find_P_successors g i p in
           if
             (k = Prims.int_zero) &&
               ((FStar_List_Tot_Base.length succs) = Prims.int_zero)
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_MinQualCard (k, p, c) ->
           let succs = find_P_successors g i p in
           let matched = count_qual_successors g succs c (n - Prims.int_one) in
           if matched >= k
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_MaxQualCard (k, p, c) ->
           let succs = find_P_successors g i p in
           let matched = count_qual_successors g succs c (n - Prims.int_one) in
           if (k = Prims.int_zero) && (matched = Prims.int_zero)
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None
       | CE_ExactQualCard (k, p, c) ->
           let succs = find_P_successors g i p in
           let matched = count_qual_successors g succs c (n - Prims.int_one) in
           if (k = Prims.int_zero) && (matched = Prims.int_zero)
           then FStar_Pervasives_Native.Some true
           else FStar_Pervasives_Native.None)
and any_is_member (g : RDF_Graph.rdf_graph)
  (ys : RDF_Term.rdf_term Prims.list) (c : class_expr) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  match ys with
  | [] -> FStar_Pervasives_Native.None
  | y::tl ->
      (match term_as_subject y with
       | FStar_Pervasives_Native.None -> any_is_member g tl c fuel
       | FStar_Pervasives_Native.Some ys_subj ->
           (match is_member g ys_subj c fuel with
            | FStar_Pervasives_Native.Some true ->
                FStar_Pervasives_Native.Some true
            | uu___ -> any_is_member g tl c fuel))
and all_is_member (g : RDF_Graph.rdf_graph)
  (ys : RDF_Term.rdf_term Prims.list) (c : class_expr) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  match ys with
  | [] -> FStar_Pervasives_Native.Some true
  | y::tl ->
      (match term_as_subject y with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some false
       | FStar_Pervasives_Native.Some ys_subj ->
           (match is_member g ys_subj c fuel with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | FStar_Pervasives_Native.Some true -> all_is_member g tl c fuel
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
and is_intersection_member (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (ces : class_expr Prims.list) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  match ces with
  | [] -> FStar_Pervasives_Native.Some true
  | c::tl ->
      (match is_member g i c fuel with
       | FStar_Pervasives_Native.Some false ->
           FStar_Pervasives_Native.Some false
       | FStar_Pervasives_Native.Some true ->
           is_intersection_member g i tl fuel
       | FStar_Pervasives_Native.None ->
           (match is_intersection_member g i tl fuel with
            | FStar_Pervasives_Native.Some false ->
                FStar_Pervasives_Native.Some false
            | uu___ -> FStar_Pervasives_Native.None))
and is_union_member (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (ces : class_expr Prims.list) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  match ces with
  | [] -> FStar_Pervasives_Native.Some false
  | c::tl ->
      (match is_member g i c fuel with
       | FStar_Pervasives_Native.Some true ->
           FStar_Pervasives_Native.Some true
       | FStar_Pervasives_Native.Some false -> is_union_member g i tl fuel
       | FStar_Pervasives_Native.None ->
           (match is_union_member g i tl fuel with
            | FStar_Pervasives_Native.Some true ->
                FStar_Pervasives_Native.Some true
            | uu___ -> FStar_Pervasives_Native.None))
and count_qual_successors (g : RDF_Graph.rdf_graph)
  (ys : RDF_Term.rdf_term Prims.list) (c : class_expr) (fuel : Prims.nat) :
  Prims.nat=
  match ys with
  | [] -> Prims.int_zero
  | y::tl ->
      let rest = count_qual_successors g tl c fuel in
      (match term_as_subject y with
       | FStar_Pervasives_Native.None -> rest
       | FStar_Pervasives_Native.Some ys_subj ->
           (match is_member g ys_subj c fuel with
            | FStar_Pervasives_Native.Some true -> rest + Prims.int_one
            | uu___ -> rest))
type tab_link = {
  tl_pred: RDF_Term.wf_iri ;
  tl_obj: RDF_Term.rdf_term }
let __proj__Mktab_link__item__tl_pred (projectee : tab_link) :
  RDF_Term.wf_iri= match projectee with | { tl_pred; tl_obj;_} -> tl_pred
let __proj__Mktab_link__item__tl_obj (projectee : tab_link) :
  RDF_Term.rdf_term= match projectee with | { tl_pred; tl_obj;_} -> tl_obj
type tab_individual =
  | TI_IRI of RDF_Term.wf_iri 
  | TI_BNode of RDF_Term.bnode_id 
  | TI_Skolem of Prims.nat 
let uu___is_TI_IRI (projectee : tab_individual) : Prims.bool=
  match projectee with | TI_IRI _0 -> true | uu___ -> false
let __proj__TI_IRI__item___0 (projectee : tab_individual) : RDF_Term.wf_iri=
  match projectee with | TI_IRI _0 -> _0
let uu___is_TI_BNode (projectee : tab_individual) : Prims.bool=
  match projectee with | TI_BNode _0 -> true | uu___ -> false
let __proj__TI_BNode__item___0 (projectee : tab_individual) :
  RDF_Term.bnode_id= match projectee with | TI_BNode _0 -> _0
let uu___is_TI_Skolem (projectee : tab_individual) : Prims.bool=
  match projectee with | TI_Skolem _0 -> true | uu___ -> false
let __proj__TI_Skolem__item___0 (projectee : tab_individual) : Prims.nat=
  match projectee with | TI_Skolem _0 -> _0
type tab_node =
  {
  tn_indiv: tab_individual ;
  tn_classes: RDF_Term.wf_iri Prims.list ;
  tn_links: tab_link Prims.list ;
  tn_same_as: tab_individual Prims.list }
let __proj__Mktab_node__item__tn_indiv (projectee : tab_node) :
  tab_individual=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_indiv
let __proj__Mktab_node__item__tn_classes (projectee : tab_node) :
  RDF_Term.wf_iri Prims.list=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_classes
let __proj__Mktab_node__item__tn_links (projectee : tab_node) :
  tab_link Prims.list=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_links
let __proj__Mktab_node__item__tn_same_as (projectee : tab_node) :
  tab_individual Prims.list=
  match projectee with
  | { tn_indiv; tn_classes; tn_links; tn_same_as;_} -> tn_same_as
let make_iri_node (i : RDF_Term.wf_iri) : tab_node=
  { tn_indiv = (TI_IRI i); tn_classes = []; tn_links = []; tn_same_as = [] }
type tab_status =
  | Open 
  | Closed 
  | Unknown 
let uu___is_Open (projectee : tab_status) : Prims.bool=
  match projectee with | Open -> true | uu___ -> false
let uu___is_Closed (projectee : tab_status) : Prims.bool=
  match projectee with | Closed -> true | uu___ -> false
let uu___is_Unknown (projectee : tab_status) : Prims.bool=
  match projectee with | Unknown -> true | uu___ -> false
type tab_branch = {
  tb_nodes: tab_node Prims.list ;
  tb_status: tab_status }
let __proj__Mktab_branch__item__tb_nodes (projectee : tab_branch) :
  tab_node Prims.list=
  match projectee with | { tb_nodes; tb_status;_} -> tb_nodes
let __proj__Mktab_branch__item__tb_status (projectee : tab_branch) :
  tab_status= match projectee with | { tb_nodes; tb_status;_} -> tb_status
let empty_branch : tab_branch= { tb_nodes = []; tb_status = Open }
type tab_obligation = {
  tob_owner: tab_individual ;
  tob_desc: Prims.string }
let __proj__Mktab_obligation__item__tob_owner (projectee : tab_obligation) :
  tab_individual=
  match projectee with | { tob_owner; tob_desc;_} -> tob_owner
let __proj__Mktab_obligation__item__tob_desc (projectee : tab_obligation) :
  Prims.string= match projectee with | { tob_owner; tob_desc;_} -> tob_desc
type tableau_state =
  {
  ts_branches: tab_branch Prims.list ;
  ts_obligations: tab_obligation Prims.list ;
  ts_una: Prims.bool ;
  ts_fuel_used: Prims.nat }
let __proj__Mktableau_state__item__ts_branches (projectee : tableau_state) :
  tab_branch Prims.list=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_branches
let __proj__Mktableau_state__item__ts_obligations (projectee : tableau_state)
  : tab_obligation Prims.list=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_obligations
let __proj__Mktableau_state__item__ts_una (projectee : tableau_state) :
  Prims.bool=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_una
let __proj__Mktableau_state__item__ts_fuel_used (projectee : tableau_state) :
  Prims.nat=
  match projectee with
  | { ts_branches; ts_obligations; ts_una; ts_fuel_used;_} -> ts_fuel_used
let init_tableau_state (uu___ : unit) : tableau_state=
  {
    ts_branches = [empty_branch];
    ts_obligations = [];
    ts_una = false;
    ts_fuel_used = Prims.int_zero
  }
let rec triple_in_graph (goal : RDF_Triple.triple) (g : RDF_Graph.rdf_graph)
  : Prims.bool=
  match g with
  | [] -> false
  | t::rest ->
      if RDF_Triple.triple_eq t goal then true else triple_in_graph goal rest
let tableau_step (st : tableau_state) (fuel : Prims.nat) :
  (tableau_state * tab_status)=
  if fuel = Prims.int_zero
  then (st, Unknown)
  else
    (match st.ts_obligations with
     | [] -> (st, Unknown)
     | uu___1::uu___2 -> (st, Unknown))
let owl_tableau_entails (regime : Prims.string)
  (data : RDF_Graph.rdf_dataset) (schema : RDF_Graph.rdf_dataset)
  (goal : RDF_Triple.triple) : Prims.bool FStar_Pervasives_Native.option=
  let uu___ = regime in
  let uu___1 = schema in
  let g = data.RDF_Graph.ds_default in
  if triple_in_graph goal g
  then FStar_Pervasives_Native.Some true
  else
    if goal.RDF_Triple.p = RDFS_Closure.rdf_type
    then
      (let ce = parse_class_expr g goal.RDF_Triple.o (Prims.of_int (32)) in
       match ce with
       | CE_Unknown -> FStar_Pervasives_Native.None
       | CE_Named uu___3 -> FStar_Pervasives_Native.None
       | uu___3 -> is_member g goal.RDF_Triple.s ce (Prims.of_int (64)))
    else FStar_Pervasives_Native.None
let owl_tableau_entails_graph (regime : Prims.string)
  (g : RDF_Graph.rdf_graph) (goal : RDF_Triple.triple) :
  Prims.bool FStar_Pervasives_Native.option=
  let ds = { RDF_Graph.ds_default = g; RDF_Graph.ds_named = [] } in
  owl_tableau_entails regime ds RDF_Graph.empty_dataset goal
let is_class_expression_subject (g : RDF_Graph.rdf_graph)
  (s : RDF_Term.subject) : Prims.bool=
  match s with
  | RDF_Term.S_IRI uu___ -> false
  | RDF_Term.S_BNode uu___ ->
      (((FStar_Pervasives_Native.uu___is_Some
           (find_first_object g s OWL_Vocabulary.owl_intersectionOf))
          ||
          (FStar_Pervasives_Native.uu___is_Some
             (find_first_object g s OWL_Vocabulary.owl_unionOf)))
         ||
         (FStar_Pervasives_Native.uu___is_Some
            (find_first_object g s OWL_Vocabulary.owl_complementOf)))
        ||
        (FStar_Pervasives_Native.uu___is_Some
           (find_first_object g s OWL_Vocabulary.owl_onProperty))
let rec collect_ce_bnodes (g : RDF_Graph.rdf_graph)
  (gfull : RDF_Graph.rdf_graph) : RDF_Term.subject Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let rest = collect_ce_bnodes tl gfull in
      (match t.RDF_Triple.s with
       | RDF_Term.S_BNode uu___ ->
           if
             (is_class_expression_subject gfull t.RDF_Triple.s) &&
               (Prims.op_Negation
                  (FStar_List_Tot_Base.existsb
                     (fun x -> RDF_Term.subject_eq x t.RDF_Triple.s) rest))
           then (t.RDF_Triple.s) :: rest
           else rest
       | uu___ -> rest)
let rec collect_candidate_individuals (g : RDF_Graph.rdf_graph)
  (gfull : RDF_Graph.rdf_graph) : RDF_Term.subject Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let rest = collect_candidate_individuals tl gfull in
      let is_ce = is_class_expression_subject gfull t.RDF_Triple.s in
      if is_ce
      then rest
      else
        if
          FStar_List_Tot_Base.existsb
            (fun x -> RDF_Term.subject_eq x t.RDF_Triple.s) rest
        then rest
        else (t.RDF_Triple.s) :: rest
let materialise_for_pair (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (ce_s : RDF_Term.subject) (ce : class_expr) : RDF_Triple.triple Prims.list=
  let existing =
    FStar_List_Tot_Base.existsb
      (fun t ->
         ((t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
            (RDF_Term.subject_eq t.RDF_Triple.s i))
           &&
           (match ((t.RDF_Triple.o), ce_s) with
            | (RDF_Term.T_IRI o, RDF_Term.S_IRI ci) -> o = ci
            | (RDF_Term.T_BNode o, RDF_Term.S_BNode cb) -> o = cb
            | (uu___, uu___1) -> false)) g in
  if existing
  then []
  else
    (match is_member g i ce (Prims.of_int (64)) with
     | FStar_Pervasives_Native.Some true ->
         let obj =
           match ce_s with
           | RDF_Term.S_IRI ci -> RDF_Term.T_IRI ci
           | RDF_Term.S_BNode cb -> RDF_Term.T_BNode cb in
         [{
            RDF_Triple.s = i;
            RDF_Triple.p = RDFS_Closure.rdf_type;
            RDF_Triple.o = obj
          }]
     | uu___1 -> [])
let rec materialise_for_ce (g : RDF_Graph.rdf_graph)
  (candidates : RDF_Term.subject Prims.list) (ce_s : RDF_Term.subject)
  (ce : class_expr) : RDF_Triple.triple Prims.list=
  match candidates with
  | [] -> []
  | i::tl ->
      FStar_List_Tot_Base.op_At (materialise_for_pair g i ce_s ce)
        (materialise_for_ce g tl ce_s ce)
let rec materialise_all (g : RDF_Graph.rdf_graph)
  (candidates : RDF_Term.subject Prims.list)
  (ces : RDF_Term.subject Prims.list) : RDF_Triple.triple Prims.list=
  match ces with
  | [] -> []
  | ce_s::tl ->
      let ce =
        parse_class_expr g
          (match ce_s with
           | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
           | RDF_Term.S_BNode b -> RDF_Term.T_BNode b) (Prims.of_int (32)) in
      (match ce with
       | CE_Unknown -> materialise_all g candidates tl
       | uu___ ->
           FStar_List_Tot_Base.op_At
             (materialise_for_ce g candidates ce_s ce)
             (materialise_all g candidates tl))
let rec emit_intersection_subclasses_via_eqc (named_subj : RDF_Term.subject)
  (items : RDF_Term.rdf_term Prims.list) : RDF_Triple.triple Prims.list=
  match items with
  | [] -> []
  | t::tl ->
      let tail = emit_intersection_subclasses_via_eqc named_subj tl in
      (match RDF_Graph.term_to_subject t with
       | FStar_Pervasives_Native.Some uu___ ->
           {
             RDF_Triple.s = named_subj;
             RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
             RDF_Triple.o = t
           } :: tail
       | FStar_Pervasives_Native.None -> tail)
let rec emit_union_subclasses_via_eqc (named_subj : RDF_Term.subject)
  (items : RDF_Term.rdf_term Prims.list) : RDF_Triple.triple Prims.list=
  match items with
  | [] -> []
  | t::tl ->
      let tail = emit_union_subclasses_via_eqc named_subj tl in
      (match RDF_Graph.term_to_subject t with
       | FStar_Pervasives_Native.Some t_subj ->
           {
             RDF_Triple.s = t_subj;
             RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
             RDF_Triple.o = (RDF_Graph.subject_to_term named_subj)
           } :: tail
       | FStar_Pervasives_Native.None -> tail)
let rec materialise_eqc_expansion (g : RDF_Graph.rdf_graph)
  (all : RDF_Graph.rdf_graph) : RDF_Triple.triple Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let tail = materialise_eqc_expansion tl all in
      if t.RDF_Triple.p = OWL_Closure.owl_equivalentClass
      then
        (match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some ce_s ->
             (match find_first_object all ce_s
                      OWL_Vocabulary.owl_intersectionOf
              with
              | FStar_Pervasives_Native.Some list_head ->
                  let items = walk_rdf_list all list_head (Prims.of_int (64)) in
                  FStar_List_Tot_Base.op_At
                    (emit_intersection_subclasses_via_eqc t.RDF_Triple.s
                       items) tail
              | FStar_Pervasives_Native.None ->
                  (match find_first_object all ce_s
                           OWL_Vocabulary.owl_unionOf
                   with
                   | FStar_Pervasives_Native.Some list_head ->
                       let items =
                         walk_rdf_list all list_head (Prims.of_int (64)) in
                       FStar_List_Tot_Base.op_At
                         (emit_union_subclasses_via_eqc t.RDF_Triple.s items)
                         tail
                   | FStar_Pervasives_Native.None -> tail))
         | FStar_Pervasives_Native.None -> tail)
      else tail
let existential_obligation (ce : class_expr) :
  (RDF_Term.wf_iri * class_expr) FStar_Pervasives_Native.option=
  match ce with
  | CE_SomeValuesFrom (p, c) -> FStar_Pervasives_Native.Some (p, c)
  | CE_MinCard (k, p) ->
      if k = Prims.int_one
      then FStar_Pervasives_Native.Some (p, CE_Unknown)
      else FStar_Pervasives_Native.None
  | CE_MinQualCard (k, p, c) ->
      if k = Prims.int_one
      then FStar_Pervasives_Native.Some (p, c)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let witness_bnode_id (i : RDF_Term.subject) (p : RDF_Term.wf_iri) :
  RDF_Term.bnode_id=
  let i_str = match i with | RDF_Term.S_IRI s -> s | RDF_Term.S_BNode b -> b in
  FStar_String.concat "" ["_:bw_"; i_str; "__"; p]
let already_has_witness (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (p : RDF_Term.wf_iri) (c : class_expr) : Prims.bool=
  let succs = find_P_successors g i p in
  match c with
  | CE_Unknown -> Prims.op_Negation (Prims.uu___is_Nil succs)
  | uu___ ->
      (match any_is_member g succs c (Prims.of_int (32)) with
       | FStar_Pervasives_Native.Some true -> true
       | uu___1 -> false)
let witnesses_for_ce_bnode (g : RDF_Graph.rdf_graph)
  (ce_s : RDF_Term.subject) (ce : class_expr) : RDF_Triple.triple Prims.list=
  match existential_obligation ce with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some (p, c) ->
      let ce_term = RDF_Graph.subject_to_term ce_s in
      let typed_individuals =
        RDF_Graph_Executable.find_subjects g RDFS_Closure.rdf_type ce_term in
      FStar_List_Tot_Base.fold_left
        (fun acc i ->
           if already_has_witness g i p c
           then acc
           else
             (let bw_id = witness_bnode_id i p in
              let bw_term = RDF_Term.T_BNode bw_id in
              let edge =
                { RDF_Triple.s = i; RDF_Triple.p = p; RDF_Triple.o = bw_term
                } in
              let acc1 = edge :: acc in
              match c with
              | CE_Named c_iri ->
                  let type_t =
                    {
                      RDF_Triple.s = (RDF_Term.S_BNode bw_id);
                      RDF_Triple.p = RDFS_Closure.rdf_type;
                      RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                    } in
                  type_t :: acc1
              | uu___1 -> acc1)) [] typed_individuals
let rec witnesses_for_all (g : RDF_Graph.rdf_graph)
  (ces : RDF_Term.subject Prims.list) : RDF_Triple.triple Prims.list=
  match ces with
  | [] -> []
  | ce_s::tl ->
      let ce =
        parse_class_expr g (RDF_Graph.subject_to_term ce_s)
          (Prims.of_int (32)) in
      (match ce with
       | CE_Unknown -> witnesses_for_all g tl
       | uu___ ->
           FStar_List_Tot_Base.op_At (witnesses_for_ce_bnode g ce_s ce)
             (witnesses_for_all g tl))
let tableau_introduce_witnesses (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  let ces = collect_ce_bnodes g g in
  let extras = witnesses_for_all g ces in
  RDF_Graph.add_triples_if_new g extras
let rec materialise_direct_boolean_subclasses (g : RDF_Graph.rdf_graph)
  (all : RDF_Graph.rdf_graph) : RDF_Triple.triple Prims.list=
  match g with
  | [] -> []
  | t::tl ->
      let tail = materialise_direct_boolean_subclasses tl all in
      (match t.RDF_Triple.s with
       | RDF_Term.S_IRI uu___ ->
           if t.RDF_Triple.p = OWL_Vocabulary.owl_unionOf
           then
             let items = walk_rdf_list all t.RDF_Triple.o (Prims.of_int (64)) in
             FStar_List_Tot_Base.op_At
               (emit_union_subclasses_via_eqc t.RDF_Triple.s items) tail
           else
             if t.RDF_Triple.p = OWL_Vocabulary.owl_intersectionOf
             then
               (let items =
                  walk_rdf_list all t.RDF_Triple.o (Prims.of_int (64)) in
                FStar_List_Tot_Base.op_At
                  (emit_intersection_subclasses_via_eqc t.RDF_Triple.s items)
                  tail)
             else tail
       | uu___ -> tail)
let tableau_materialise (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let g1 = tableau_introduce_witnesses g in
  let ces = collect_ce_bnodes g1 g1 in
  let individuals = collect_candidate_individuals g1 g1 in
  let instance_triples = materialise_all g1 individuals ces in
  let structural_triples = materialise_eqc_expansion g1 g1 in
  let bool_subclasses = materialise_direct_boolean_subclasses g1 g1 in
  RDF_Graph.add_triples_if_new
    (RDF_Graph.add_triples_if_new
       (RDF_Graph.add_triples_if_new g1 structural_triples) bool_subclasses)
    instance_triples
