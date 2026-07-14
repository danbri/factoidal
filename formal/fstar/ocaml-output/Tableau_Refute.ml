open Prims
let owl_bottomObjectProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#bottomObjectProperty"
let owl_bottomDataProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#bottomDataProperty"
let owl_topObjectProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#topObjectProperty"
let owl_inverseOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#inverseOf"
let owl_distinctMembers : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#distinctMembers"
let xsd_string_dt : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#string"
let xsd_boolean_dt : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#boolean"
let is_bottom_prop (p : RDF_Term.wf_iri) : Prims.bool=
  (p = owl_bottomObjectProperty) || (p = owl_bottomDataProperty)
let rec term_list_eq (xs : RDF_Term.rdf_term Prims.list)
  (ys : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match (xs, ys) with
  | ([], []) -> true
  | (x::xtl, y::ytl) -> (RDF_Term.rdf_term_eq x y) && (term_list_eq xtl ytl)
  | (uu___, uu___1) -> false
let rec facet_pairs_eq
  (xs : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list)
  (ys : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list) : Prims.bool=
  match (xs, ys) with
  | ([], []) -> true
  | ((fi, fv)::xtl, (gi, gv)::ytl) ->
      ((fi = gi) && (RDF_Term.rdf_term_eq fv gv)) && (facet_pairs_eq xtl ytl)
  | (uu___, uu___1) -> false
let rec ce_eq (a : Tableau.class_expr) (b : Tableau.class_expr) : Prims.bool=
  match (a, b) with
  | (Tableau.CE_Named x, Tableau.CE_Named y) -> x = y
  | (Tableau.CE_OneOf xs, Tableau.CE_OneOf ys) -> term_list_eq xs ys
  | (Tableau.CE_SomeValuesFrom (p, c), Tableau.CE_SomeValuesFrom (q, d)) ->
      (p = q) && (ce_eq c d)
  | (Tableau.CE_AllValuesFrom (p, c), Tableau.CE_AllValuesFrom (q, d)) ->
      (p = q) && (ce_eq c d)
  | (Tableau.CE_HasValue (p, v), Tableau.CE_HasValue (q, w)) ->
      (p = q) && (RDF_Term.rdf_term_eq v w)
  | (Tableau.CE_IntersectionOf xs, Tableau.CE_IntersectionOf ys) ->
      ce_list_eq xs ys
  | (Tableau.CE_UnionOf xs, Tableau.CE_UnionOf ys) -> ce_list_eq xs ys
  | (Tableau.CE_ComplementOf c, Tableau.CE_ComplementOf d) -> ce_eq c d
  | (Tableau.CE_MinCard (k, p), Tableau.CE_MinCard (j, q)) ->
      (k = j) && (p = q)
  | (Tableau.CE_MaxCard (k, p), Tableau.CE_MaxCard (j, q)) ->
      (k = j) && (p = q)
  | (Tableau.CE_ExactCard (k, p), Tableau.CE_ExactCard (j, q)) ->
      (k = j) && (p = q)
  | (Tableau.CE_MinQualCard (k, p, c), Tableau.CE_MinQualCard (j, q, d)) ->
      ((k = j) && (p = q)) && (ce_eq c d)
  | (Tableau.CE_MaxQualCard (k, p, c), Tableau.CE_MaxQualCard (j, q, d)) ->
      ((k = j) && (p = q)) && (ce_eq c d)
  | (Tableau.CE_ExactQualCard (k, p, c), Tableau.CE_ExactQualCard (j, q, d))
      -> ((k = j) && (p = q)) && (ce_eq c d)
  | (Tableau.CE_DataRestriction (dt, fs), Tableau.CE_DataRestriction
     (dt', fs')) -> (dt = dt') && (facet_pairs_eq fs fs')
  | (uu___, uu___1) -> false
and ce_list_eq (xs : Tableau.class_expr Prims.list)
  (ys : Tableau.class_expr Prims.list) : Prims.bool=
  match (xs, ys) with
  | ([], []) -> true
  | (x::xtl, y::ytl) -> (ce_eq x y) && (ce_list_eq xtl ytl)
  | (uu___, uu___1) -> false
let rec ce_eq_syn (a : Tableau.class_expr) (b : Tableau.class_expr) :
  Prims.bool=
  match (a, b) with
  | (Tableau.CE_Unknown, Tableau.CE_Unknown) -> true
  | (Tableau.CE_Named x, Tableau.CE_Named y) -> x = y
  | (Tableau.CE_OneOf xs, Tableau.CE_OneOf ys) -> term_list_eq xs ys
  | (Tableau.CE_SomeValuesFrom (p, c), Tableau.CE_SomeValuesFrom (q, d)) ->
      (p = q) && (ce_eq_syn c d)
  | (Tableau.CE_AllValuesFrom (p, c), Tableau.CE_AllValuesFrom (q, d)) ->
      (p = q) && (ce_eq_syn c d)
  | (Tableau.CE_HasValue (p, v), Tableau.CE_HasValue (q, w)) ->
      (p = q) && (RDF_Term.rdf_term_eq v w)
  | (Tableau.CE_IntersectionOf xs, Tableau.CE_IntersectionOf ys) ->
      ce_list_eq_syn xs ys
  | (Tableau.CE_UnionOf xs, Tableau.CE_UnionOf ys) -> ce_list_eq_syn xs ys
  | (Tableau.CE_ComplementOf c, Tableau.CE_ComplementOf d) -> ce_eq_syn c d
  | (Tableau.CE_MinCard (k, p), Tableau.CE_MinCard (j, q)) ->
      (k = j) && (p = q)
  | (Tableau.CE_MaxCard (k, p), Tableau.CE_MaxCard (j, q)) ->
      (k = j) && (p = q)
  | (Tableau.CE_ExactCard (k, p), Tableau.CE_ExactCard (j, q)) ->
      (k = j) && (p = q)
  | (Tableau.CE_MinQualCard (k, p, c), Tableau.CE_MinQualCard (j, q, d)) ->
      ((k = j) && (p = q)) && (ce_eq_syn c d)
  | (Tableau.CE_MaxQualCard (k, p, c), Tableau.CE_MaxQualCard (j, q, d)) ->
      ((k = j) && (p = q)) && (ce_eq_syn c d)
  | (Tableau.CE_ExactQualCard (k, p, c), Tableau.CE_ExactQualCard (j, q, d))
      -> ((k = j) && (p = q)) && (ce_eq_syn c d)
  | (Tableau.CE_DataRestriction (dt, fs), Tableau.CE_DataRestriction
     (dt', fs')) -> (dt = dt') && (facet_pairs_eq fs fs')
  | (uu___, uu___1) -> false
and ce_list_eq_syn (xs : Tableau.class_expr Prims.list)
  (ys : Tableau.class_expr Prims.list) : Prims.bool=
  match (xs, ys) with
  | ([], []) -> true
  | (x::xtl, y::ytl) -> (ce_eq_syn x y) && (ce_list_eq_syn xtl ytl)
  | (uu___, uu___1) -> false
let rec ce_definite (c : Tableau.class_expr) : Prims.bool=
  match c with
  | Tableau.CE_Unknown -> false
  | Tableau.CE_Named uu___ -> true
  | Tableau.CE_HasValue (uu___, uu___1) -> true
  | Tableau.CE_MinCard (uu___, uu___1) -> true
  | Tableau.CE_MaxCard (uu___, uu___1) -> true
  | Tableau.CE_ExactCard (uu___, uu___1) -> true
  | Tableau.CE_OneOf uu___ -> true
  | Tableau.CE_DataRestriction (uu___, uu___1) -> true
  | Tableau.CE_SomeValuesFrom (uu___, d) -> ce_definite d
  | Tableau.CE_AllValuesFrom (uu___, d) -> ce_definite d
  | Tableau.CE_ComplementOf d -> ce_definite d
  | Tableau.CE_MinQualCard (uu___, uu___1, d) -> ce_definite d
  | Tableau.CE_MaxQualCard (uu___, uu___1, d) -> ce_definite d
  | Tableau.CE_ExactQualCard (uu___, uu___1, d) -> ce_definite d
  | Tableau.CE_IntersectionOf ds -> ce_list_definite ds
  | Tableau.CE_UnionOf ds -> ce_list_definite ds
and ce_list_definite (cs : Tableau.class_expr Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | c::tl -> (ce_definite c) && (ce_list_definite tl)
let rec nnf (c : Tableau.class_expr) : Tableau.class_expr=
  match c with
  | Tableau.CE_ComplementOf d -> nnf_neg d
  | Tableau.CE_IntersectionOf cs -> Tableau.CE_IntersectionOf (nnf_list cs)
  | Tableau.CE_UnionOf cs -> Tableau.CE_UnionOf (nnf_list cs)
  | Tableau.CE_SomeValuesFrom (p, d) ->
      Tableau.CE_SomeValuesFrom (p, (nnf d))
  | Tableau.CE_AllValuesFrom (p, d) -> Tableau.CE_AllValuesFrom (p, (nnf d))
  | Tableau.CE_MinQualCard (k, p, d) ->
      Tableau.CE_MinQualCard (k, p, (nnf d))
  | Tableau.CE_MaxQualCard (k, p, d) ->
      Tableau.CE_MaxQualCard (k, p, (nnf d))
  | Tableau.CE_ExactCard (k, p) ->
      Tableau.CE_IntersectionOf
        [Tableau.CE_MinCard (k, p); Tableau.CE_MaxCard (k, p)]
  | Tableau.CE_ExactQualCard (k, p, d) ->
      let d' = nnf d in
      Tableau.CE_IntersectionOf
        [Tableau.CE_MinQualCard (k, p, d');
        Tableau.CE_MaxQualCard (k, p, d')]
  | uu___ -> c
and nnf_neg (c : Tableau.class_expr) : Tableau.class_expr=
  match c with
  | Tableau.CE_Named x ->
      if x = RDFS_Closure.owl_Thing
      then Tableau.CE_Named RDFS_Closure.owl_Nothing
      else
        if x = RDFS_Closure.owl_Nothing
        then Tableau.CE_Named RDFS_Closure.owl_Thing
        else Tableau.CE_ComplementOf (Tableau.CE_Named x)
  | Tableau.CE_ComplementOf d -> nnf d
  | Tableau.CE_IntersectionOf cs -> Tableau.CE_UnionOf (nnf_neg_list cs)
  | Tableau.CE_UnionOf cs -> Tableau.CE_IntersectionOf (nnf_neg_list cs)
  | Tableau.CE_SomeValuesFrom (p, d) ->
      Tableau.CE_AllValuesFrom (p, (nnf_neg d))
  | Tableau.CE_AllValuesFrom (p, d) ->
      Tableau.CE_SomeValuesFrom (p, (nnf_neg d))
  | Tableau.CE_HasValue (p, v) ->
      Tableau.CE_ComplementOf (Tableau.CE_HasValue (p, v))
  | Tableau.CE_MinCard (k, p) ->
      if k = Prims.int_zero
      then Tableau.CE_Named RDFS_Closure.owl_Nothing
      else Tableau.CE_MaxCard ((k - Prims.int_one), p)
  | Tableau.CE_MaxCard (k, p) -> Tableau.CE_MinCard ((k + Prims.int_one), p)
  | Tableau.CE_ExactCard (k, p) ->
      if k = Prims.int_zero
      then Tableau.CE_MinCard (Prims.int_one, p)
      else
        Tableau.CE_UnionOf
          [Tableau.CE_MaxCard ((k - Prims.int_one), p);
          Tableau.CE_MinCard ((k + Prims.int_one), p)]
  | Tableau.CE_MinQualCard (k, p, d) ->
      if k = Prims.int_zero
      then Tableau.CE_Named RDFS_Closure.owl_Nothing
      else Tableau.CE_MaxQualCard ((k - Prims.int_one), p, (nnf d))
  | Tableau.CE_MaxQualCard (k, p, d) ->
      Tableau.CE_MinQualCard ((k + Prims.int_one), p, (nnf d))
  | Tableau.CE_ExactQualCard (k, p, d) ->
      let d' = nnf d in
      if k = Prims.int_zero
      then Tableau.CE_MinQualCard (Prims.int_one, p, d')
      else
        Tableau.CE_UnionOf
          [Tableau.CE_MaxQualCard ((k - Prims.int_one), p, d');
          Tableau.CE_MinQualCard ((k + Prims.int_one), p, d')]
  | Tableau.CE_OneOf members ->
      Tableau.CE_ComplementOf (Tableau.CE_OneOf members)
  | Tableau.CE_DataRestriction (dt, facets) ->
      Tableau.CE_ComplementOf (Tableau.CE_DataRestriction (dt, facets))
  | Tableau.CE_Unknown -> Tableau.CE_Unknown
and nnf_list (cs : Tableau.class_expr Prims.list) :
  Tableau.class_expr Prims.list=
  match cs with | [] -> [] | c::tl -> (nnf c) :: (nnf_list tl)
and nnf_neg_list (cs : Tableau.class_expr Prims.list) :
  Tableau.class_expr Prims.list=
  match cs with | [] -> [] | c::tl -> (nnf_neg c) :: (nnf_neg_list tl)
type rnode =
  {
  rn_id: RDF_Term.subject ;
  rn_labels: Tableau.class_expr Prims.list }
let __proj__Mkrnode__item__rn_id (projectee : rnode) : RDF_Term.subject=
  match projectee with | { rn_id; rn_labels;_} -> rn_id
let __proj__Mkrnode__item__rn_labels (projectee : rnode) :
  Tableau.class_expr Prims.list=
  match projectee with | { rn_id; rn_labels;_} -> rn_labels
type redge =
  {
  re_s: RDF_Term.subject ;
  re_p: RDF_Term.wf_iri ;
  re_o: RDF_Term.rdf_term ;
  re_count: Prims.bool }
let __proj__Mkredge__item__re_s (projectee : redge) : RDF_Term.subject=
  match projectee with | { re_s; re_p; re_o; re_count;_} -> re_s
let __proj__Mkredge__item__re_p (projectee : redge) : RDF_Term.wf_iri=
  match projectee with | { re_s; re_p; re_o; re_count;_} -> re_p
let __proj__Mkredge__item__re_o (projectee : redge) : RDF_Term.rdf_term=
  match projectee with | { re_s; re_p; re_o; re_count;_} -> re_o
let __proj__Mkredge__item__re_count (projectee : redge) : Prims.bool=
  match projectee with | { re_s; re_p; re_o; re_count;_} -> re_count
type rstate =
  {
  rs_nodes: rnode Prims.list ;
  rs_extra: redge Prims.list ;
  rs_fresh: Prims.nat ;
  rs_wdepth: (RDF_Term.bnode_id * Prims.nat) Prims.list ;
  rs_inv: (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list ;
  rs_gendistinct: RDF_Term.rdf_term Prims.list Prims.list }
let __proj__Mkrstate__item__rs_nodes (projectee : rstate) : rnode Prims.list=
  match projectee with
  | { rs_nodes; rs_extra; rs_fresh; rs_wdepth; rs_inv; rs_gendistinct;_} ->
      rs_nodes
let __proj__Mkrstate__item__rs_extra (projectee : rstate) : redge Prims.list=
  match projectee with
  | { rs_nodes; rs_extra; rs_fresh; rs_wdepth; rs_inv; rs_gendistinct;_} ->
      rs_extra
let __proj__Mkrstate__item__rs_fresh (projectee : rstate) : Prims.nat=
  match projectee with
  | { rs_nodes; rs_extra; rs_fresh; rs_wdepth; rs_inv; rs_gendistinct;_} ->
      rs_fresh
let __proj__Mkrstate__item__rs_wdepth (projectee : rstate) :
  (RDF_Term.bnode_id * Prims.nat) Prims.list=
  match projectee with
  | { rs_nodes; rs_extra; rs_fresh; rs_wdepth; rs_inv; rs_gendistinct;_} ->
      rs_wdepth
let __proj__Mkrstate__item__rs_inv (projectee : rstate) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  match projectee with
  | { rs_nodes; rs_extra; rs_fresh; rs_wdepth; rs_inv; rs_gendistinct;_} ->
      rs_inv
let __proj__Mkrstate__item__rs_gendistinct (projectee : rstate) :
  RDF_Term.rdf_term Prims.list Prims.list=
  match projectee with
  | { rs_nodes; rs_extra; rs_fresh; rs_wdepth; rs_inv; rs_gendistinct;_} ->
      rs_gendistinct
let rec collect_inverse_pairs (ts : RDF_Graph.rdf_graph) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      let rest = collect_inverse_pairs tl in
      if t.RDF_Triple.p = owl_inverseOf
      then
        (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p, RDF_Term.T_IRI q) -> (p, q) :: rest
         | uu___ -> rest)
      else rest
let rec inverses_of (pairs : (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list)
  (p : RDF_Term.wf_iri) : RDF_Term.wf_iri Prims.list=
  match pairs with
  | [] -> []
  | (a, b)::tl ->
      let rest = inverses_of tl p in
      if a = p then b :: rest else if b = p then a :: rest else rest
let max_witness_depth : Prims.nat= (Prims.of_int (3))
let rec witness_depth_of (ds : (RDF_Term.bnode_id * Prims.nat) Prims.list)
  (i : RDF_Term.subject) : Prims.nat=
  match i with
  | RDF_Term.S_IRI uu___ -> Prims.int_zero
  | RDF_Term.S_BNode b ->
      (match ds with
       | [] -> Prims.int_zero
       | (w, d)::tl -> if w = b then d else witness_depth_of tl i)
let rec mem_ce (c : Tableau.class_expr) (ls : Tableau.class_expr Prims.list)
  : Prims.bool=
  match ls with
  | [] -> false
  | l::tl -> if ce_eq c l then true else mem_ce c tl
let rec mem_ce_syn (c : Tableau.class_expr)
  (ls : Tableau.class_expr Prims.list) : Prims.bool=
  match ls with
  | [] -> false
  | l::tl -> if ce_eq_syn c l then true else mem_ce_syn c tl
let rec labels_of_nodes (ns : rnode Prims.list) (i : RDF_Term.subject) :
  Tableau.class_expr Prims.list=
  match ns with
  | [] -> []
  | n::tl ->
      if RDF_Term.subject_eq n.rn_id i
      then n.rn_labels
      else labels_of_nodes tl i
let labels_of (st : rstate) (i : RDF_Term.subject) :
  Tableau.class_expr Prims.list= labels_of_nodes st.rs_nodes i
let rec add_label_nodes (ns : rnode Prims.list) (i : RDF_Term.subject)
  (c : Tableau.class_expr) : (rnode Prims.list * Prims.bool)=
  match ns with
  | [] -> ([{ rn_id = i; rn_labels = [c] }], true)
  | n::tl ->
      if RDF_Term.subject_eq n.rn_id i
      then
        (if mem_ce_syn c n.rn_labels
         then ((n :: tl), false)
         else
           (({ rn_id = (n.rn_id); rn_labels = (c :: (n.rn_labels)) } :: tl),
             true))
      else
        (let uu___1 = add_label_nodes tl i c in
         match uu___1 with | (tl', ch) -> ((n :: tl'), ch))
let add_label (st : rstate) (i : RDF_Term.subject) (c : Tableau.class_expr) :
  (rstate * Prims.bool)=
  match c with
  | Tableau.CE_Unknown -> (st, false)
  | uu___ ->
      let uu___1 = add_label_nodes st.rs_nodes i c in
      (match uu___1 with
       | (ns, ch) ->
           ({
              rs_nodes = ns;
              rs_extra = (st.rs_extra);
              rs_fresh = (st.rs_fresh);
              rs_wdepth = (st.rs_wdepth);
              rs_inv = (st.rs_inv);
              rs_gendistinct = (st.rs_gendistinct)
            }, ch))
let rec add_labels_all (st : rstate) (i : RDF_Term.subject)
  (cs : Tableau.class_expr Prims.list) : (rstate * Prims.bool)=
  match cs with
  | [] -> (st, false)
  | c::tl ->
      let uu___ = add_label st i c in
      (match uu___ with
       | (st1, c1) ->
           let uu___1 = add_labels_all st1 i tl in
           (match uu___1 with | (st2, c2) -> (st2, (c1 || c2))))
let rec extra_objects (es : redge Prims.list) (i : RDF_Term.subject)
  (p : RDF_Term.wf_iri) (count_only : Prims.bool) :
  RDF_Term.rdf_term Prims.list=
  match es with
  | [] -> []
  | e::tl ->
      let rest = extra_objects tl i p count_only in
      if
        ((RDF_Term.subject_eq e.re_s i) && (e.re_p = p)) &&
          (e.re_count || (Prims.op_Negation count_only))
      then (e.re_o) :: rest
      else rest
let rec dedup_terms (ts : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      let rest = dedup_terms tl in
      if FStar_List_Tot_Base.existsb (fun o -> RDF_Term.rdf_term_eq t o) rest
      then rest
      else t :: rest
let rec base_reverse_objects (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (invs : RDF_Term.wf_iri Prims.list) : RDF_Term.rdf_term Prims.list=
  match invs with
  | [] -> []
  | q::tl ->
      FStar_List_Tot_Base.op_At
        (FStar_List_Tot_Base.map RDF_Graph.subject_to_term
           (RDF_Graph_Executable.find_subjects g q
              (RDF_Graph.subject_to_term i))) (base_reverse_objects g i tl)
let rec extra_reverse_objects (es : redge Prims.list)
  (i_term : RDF_Term.rdf_term) (q : RDF_Term.wf_iri)
  (count_only : Prims.bool) : RDF_Term.rdf_term Prims.list=
  match es with
  | [] -> []
  | e::tl ->
      let rest = extra_reverse_objects tl i_term q count_only in
      if
        ((e.re_p = q) && (RDF_Term.rdf_term_eq e.re_o i_term)) &&
          (e.re_count || (Prims.op_Negation count_only))
      then (RDF_Graph.subject_to_term e.re_s) :: rest
      else rest
let rec extra_reverse_objects_all (es : redge Prims.list)
  (i_term : RDF_Term.rdf_term) (invs : RDF_Term.wf_iri Prims.list)
  (count_only : Prims.bool) : RDF_Term.rdf_term Prims.list=
  match invs with
  | [] -> []
  | q::tl ->
      FStar_List_Tot_Base.op_At
        (extra_reverse_objects es i_term q count_only)
        (extra_reverse_objects_all es i_term tl count_only)
let countable_successors (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (p : RDF_Term.wf_iri) :
  RDF_Term.rdf_term Prims.list=
  let invs = inverses_of st.rs_inv p in
  dedup_terms
    (FStar_List_Tot_Base.op_At (RDF_Graph_Executable.find_objects g i p)
       (FStar_List_Tot_Base.op_At (extra_objects st.rs_extra i p true)
          (FStar_List_Tot_Base.op_At (base_reverse_objects g i invs)
             (extra_reverse_objects_all st.rs_extra
                (RDF_Graph.subject_to_term i) invs true))))
let all_successors (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (p : RDF_Term.wf_iri) :
  RDF_Term.rdf_term Prims.list=
  let invs = inverses_of st.rs_inv p in
  dedup_terms
    (FStar_List_Tot_Base.op_At (RDF_Graph_Executable.find_objects g i p)
       (FStar_List_Tot_Base.op_At (extra_objects st.rs_extra i p false)
          (FStar_List_Tot_Base.op_At (base_reverse_objects g i invs)
             (extra_reverse_objects_all st.rs_extra
                (RDF_Graph.subject_to_term i) invs false))))
let rec extra_edge_present (es : redge Prims.list) (i : RDF_Term.subject)
  (p : RDF_Term.wf_iri) (o : RDF_Term.rdf_term) : Prims.bool=
  match es with
  | [] -> false
  | e::tl ->
      (((RDF_Term.subject_eq e.re_s i) && (e.re_p = p)) &&
         (RDF_Term.rdf_term_eq e.re_o o))
        || (extra_edge_present tl i p o)
let graph_edge_present (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (p : RDF_Term.wf_iri) (o : RDF_Term.rdf_term) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((RDF_Term.subject_eq t.RDF_Triple.s i) && (t.RDF_Triple.p = p)) &&
         (RDF_Term.rdf_term_eq t.RDF_Triple.o o)) g
let add_countable_edge (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (p : RDF_Term.wf_iri) (v : RDF_Term.rdf_term) :
  (rstate * Prims.bool)=
  if (graph_edge_present g i p v) || (extra_edge_present st.rs_extra i p v)
  then (st, false)
  else
    ({
       rs_nodes = (st.rs_nodes);
       rs_extra = ({ re_s = i; re_p = p; re_o = v; re_count = true } ::
         (st.rs_extra));
       rs_fresh = (st.rs_fresh);
       rs_wdepth = (st.rs_wdepth);
       rs_inv = (st.rs_inv);
       rs_gendistinct = (st.rs_gendistinct)
     }, true)
let comparable_datatype (d : RDF_Term.wf_iri) : Prims.bool=
  (((d = RDF_Term.xsd_integer) || (d = RDF_Term.xsd_decimal)) ||
     (d = xsd_string_dt))
    || (d = xsd_boolean_dt)
let group_says_distinct (grp : RDF_Term.rdf_term Prims.list)
  (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.bool=
  ((Prims.op_Negation (RDF_Term.rdf_term_eq a b)) &&
     (FStar_List_Tot_Base.existsb (fun x -> RDF_Term.rdf_term_eq x a) grp))
    && (FStar_List_Tot_Base.existsb (fun x -> RDF_Term.rdf_term_eq x b) grp)
let rec gen_distinct (groups : RDF_Term.rdf_term Prims.list Prims.list)
  (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.bool=
  match groups with
  | [] -> false
  | grp::tl -> (group_says_distinct grp a b) || (gen_distinct tl a b)
let provably_distinct (g : RDF_Graph.rdf_graph)
  (gd : RDF_Term.rdf_term Prims.list Prims.list) (a : RDF_Term.rdf_term)
  (b : RDF_Term.rdf_term) : Prims.bool=
  (((OWL_Closure.differentFrom_in_graph g a b) ||
      (OWL_Closure.differentFrom_in_graph g b a))
     || (gen_distinct gd a b))
    ||
    (match (a, b) with
     | (RDF_Term.T_Literal l1, RDF_Term.T_Literal l2) ->
         ((l1.RDF_Term.datatype = l2.RDF_Term.datatype) &&
            (comparable_datatype l1.RDF_Term.datatype))
           && (Prims.op_Negation (OWL_Closure.datatype_value_eq l1 l2))
     | (uu___, uu___1) -> false)
let rec filter_distinct_from (g : RDF_Graph.rdf_graph)
  (gd : RDF_Term.rdf_term Prims.list Prims.list) (h : RDF_Term.rdf_term)
  (ts : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      let rest = filter_distinct_from g gd h tl in
      if provably_distinct g gd h t then t :: rest else rest
let rec all_provably_distinct (g : RDF_Graph.rdf_graph)
  (gd : RDF_Term.rdf_term Prims.list Prims.list) (x : RDF_Term.rdf_term)
  (ms : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match ms with
  | [] -> true
  | m::tl ->
      (provably_distinct g gd x m) && (all_provably_distinct g gd x tl)
let rec exists_distinct_subset (g : RDF_Graph.rdf_graph)
  (gd : RDF_Term.rdf_term Prims.list Prims.list)
  (cands : RDF_Term.rdf_term Prims.list) (need : Prims.nat) : Prims.bool=
  if need = Prims.int_zero
  then true
  else
    (match cands with
     | [] -> false
     | h::tl ->
         (exists_distinct_subset g gd (filter_distinct_from g gd h tl)
            (need - Prims.int_one))
           || (exists_distinct_subset g gd tl need))
let rec fold_datatype_constraint (acc : XSD_Facets.value_set)
  (ce : Tableau.class_expr) : XSD_Facets.value_set=
  match ce with
  | Tableau.CE_DataRestriction (dt, facets) ->
      if XSD_Facets.is_integer_family_datatype dt
      then
        XSD_Facets.value_set_intersect acc
          (XSD_Facets.VS_Interval
             (XSD_Facets.facets_to_interval dt facets
                XSD_Facets.full_interval))
      else acc
  | Tableau.CE_OneOf members ->
      if
        (Prims.uu___is_Cons members) &&
          (XSD_Facets.all_literal_terms members)
      then XSD_Facets.value_set_intersect acc (XSD_Facets.VS_Enum members)
      else acc
  | Tableau.CE_Named dt ->
      (match XSD_Facets.classify_family dt with
       | FStar_Pervasives_Native.Some (XSD_Facets.Fam_Numeric) ->
           XSD_Facets.value_set_intersect acc
             (XSD_Facets.VS_Interval (XSD_Facets.base_interval_for dt))
       | FStar_Pervasives_Native.Some f ->
           XSD_Facets.value_set_intersect acc (XSD_Facets.VS_Family f)
       | FStar_Pervasives_Native.None -> acc)
  | Tableau.CE_ComplementOf inner ->
      let inner_vs =
        fold_datatype_constraint XSD_Facets.VS_Unconstrained inner in
      XSD_Facets.value_set_subtract acc inner_vs
  | uu___ -> acc
let rec universal_for_property (p : RDF_Term.wf_iri)
  (ls : Tableau.class_expr Prims.list) (acc : XSD_Facets.value_set) :
  XSD_Facets.value_set=
  match ls with
  | [] -> acc
  | (Tableau.CE_AllValuesFrom (q, d))::tl ->
      universal_for_property p tl
        (if q = p then fold_datatype_constraint acc d else acc)
  | uu___::tl -> universal_for_property p tl acc
let rec exists_unsatisfiable_witness (p : RDF_Term.wf_iri)
  (ls : Tableau.class_expr Prims.list) (universal : XSD_Facets.value_set) :
  Prims.bool=
  match ls with
  | [] -> false
  | (Tableau.CE_SomeValuesFrom (q, d))::tl ->
      if
        (q = p) &&
          (XSD_Facets.value_set_is_empty
             (fold_datatype_constraint universal d))
      then true
      else exists_unsatisfiable_witness p tl universal
  | (Tableau.CE_HasValue (q, v))::tl ->
      if q = p
      then
        (match v with
         | RDF_Term.T_Literal uu___ ->
             if
               XSD_Facets.value_set_is_empty
                 (XSD_Facets.value_set_intersect universal
                    (XSD_Facets.VS_Enum [v]))
             then true
             else exists_unsatisfiable_witness p tl universal
         | uu___ -> exists_unsatisfiable_witness p tl universal)
      else exists_unsatisfiable_witness p tl universal
  | uu___::tl -> exists_unsatisfiable_witness p tl universal
let property_datatype_clash (p : RDF_Term.wf_iri)
  (ls_all : Tableau.class_expr Prims.list) : Prims.bool=
  let universal = universal_for_property p ls_all XSD_Facets.VS_Unconstrained in
  exists_unsatisfiable_witness p ls_all universal
let rec collect_dt_properties (ls : Tableau.class_expr Prims.list) :
  RDF_Term.wf_iri Prims.list=
  match ls with
  | [] -> []
  | (Tableau.CE_SomeValuesFrom (p, uu___))::tl -> p ::
      (collect_dt_properties tl)
  | (Tableau.CE_AllValuesFrom (p, uu___))::tl -> p ::
      (collect_dt_properties tl)
  | (Tableau.CE_HasValue (p, uu___))::tl -> p :: (collect_dt_properties tl)
  | uu___::tl -> collect_dt_properties tl
let rec any_property_datatype_clash (ps : RDF_Term.wf_iri Prims.list)
  (ls_all : Tableau.class_expr Prims.list) : Prims.bool=
  match ps with
  | [] -> false
  | p::tl ->
      (property_datatype_clash p ls_all) ||
        (any_property_datatype_clash tl ls_all)
let datatype_range_clash (ls_all : Tableau.class_expr Prims.list) :
  Prims.bool=
  any_property_datatype_clash (collect_dt_properties ls_all) ls_all
let exists_max_lt (k : Prims.nat) (p : RDF_Term.wf_iri)
  (ls : Tableau.class_expr Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun l ->
       match l with
       | Tableau.CE_MaxCard (k', p') -> (p' = p) && (k' < k)
       | uu___ -> false) ls
let exists_maxqual_lt (k : Prims.nat) (p : RDF_Term.wf_iri)
  (c : Tableau.class_expr) (ls : Tableau.class_expr Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun l ->
       match l with
       | Tableau.CE_MaxQualCard (k', p', c') ->
           ((p' = p) && (k' < k)) && (ce_eq c c')
       | uu___ -> false) ls
let rec filter_in_filler (st : rstate) (c : Tableau.class_expr)
  (ts : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      let rest = filter_in_filler st c tl in
      (match RDF_Graph.term_to_subject t with
       | FStar_Pervasives_Native.Some j ->
           if mem_ce c (labels_of st j) then t :: rest else rest
       | FStar_Pervasives_Native.None -> rest)
let clash_for_label (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (ls_all : Tableau.class_expr Prims.list)
  (l : Tableau.class_expr) : Prims.bool=
  match l with
  | Tableau.CE_Named x -> x = RDFS_Closure.owl_Nothing
  | Tableau.CE_ComplementOf c ->
      (mem_ce c ls_all) ||
        ((match c with
          | Tableau.CE_Named x -> x = RDFS_Closure.owl_Thing
          | uu___ -> false))
  | Tableau.CE_MinCard (k, p) ->
      (k >= Prims.int_one) &&
        ((is_bottom_prop p) || (exists_max_lt k p ls_all))
  | Tableau.CE_SomeValuesFrom (p, c) ->
      ((is_bottom_prop p) || (exists_max_lt Prims.int_one p ls_all)) ||
        (exists_maxqual_lt Prims.int_one p c ls_all)
  | Tableau.CE_HasValue (p, uu___) ->
      (is_bottom_prop p) || (exists_max_lt Prims.int_one p ls_all)
  | Tableau.CE_MinQualCard (k, p, c) ->
      (k >= Prims.int_one) &&
        ((((is_bottom_prop p) || (exists_max_lt k p ls_all)) ||
            (exists_maxqual_lt k p c ls_all))
           ||
           ((match c with
             | Tableau.CE_OneOf members ->
                 k > (FStar_List_Tot_Base.length members)
             | uu___ -> false)))
  | Tableau.CE_OneOf members ->
      all_provably_distinct g st.rs_gendistinct (RDF_Graph.subject_to_term i)
        members
  | Tableau.CE_MaxCard (k, p) ->
      let succs = countable_successors g st i p in
      if k = Prims.int_zero
      then Prims.uu___is_Cons succs
      else
        exists_distinct_subset g st.rs_gendistinct succs (k + Prims.int_one)
  | Tableau.CE_MaxQualCard (k, p, c) ->
      let succs = filter_in_filler st c (countable_successors g st i p) in
      if k = Prims.int_zero
      then Prims.uu___is_Cons succs
      else
        exists_distinct_subset g st.rs_gendistinct succs (k + Prims.int_one)
  | uu___ -> false
let rec clash_labels (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (ls_all : Tableau.class_expr Prims.list)
  (ls_iter : Tableau.class_expr Prims.list) : Prims.bool=
  match ls_iter with
  | [] -> false
  | l::tl ->
      (clash_for_label g st i ls_all l) || (clash_labels g st i ls_all tl)
let rec clash_nodes (g : RDF_Graph.rdf_graph) (st : rstate)
  (ns : rnode Prims.list) : Prims.bool=
  match ns with
  | [] -> false
  | n::tl ->
      ((clash_labels g st n.rn_id n.rn_labels n.rn_labels) ||
         (datatype_range_clash n.rn_labels))
        || (clash_nodes g st tl)
let has_clash (g : RDF_Graph.rdf_graph) (st : rstate) : Prims.bool=
  clash_nodes g st st.rs_nodes
let is_scaffold_bnode (b : RDF_Term.bnode_id) : Prims.bool=
  ((FStar_String.strlen b) >= (Prims.of_int (5))) &&
    ((FStar_String.sub b Prims.int_zero (Prims.of_int (5))) = "__rl_")
let parse_nnf (g : RDF_Graph.rdf_graph) (t : RDF_Term.rdf_term) :
  Tableau.class_expr=
  match t with
  | RDF_Term.T_BNode b ->
      if is_scaffold_bnode b
      then Tableau.CE_Unknown
      else nnf (Tableau.parse_class_expr g t (Prims.of_int (32)))
  | uu___ -> nnf (Tableau.parse_class_expr g t (Prims.of_int (32)))
let parse_nnf_subject (g : RDF_Graph.rdf_graph) (s : RDF_Term.subject) :
  Tableau.class_expr=
  match s with
  | RDF_Term.S_BNode b ->
      if is_scaffold_bnode b
      then Tableau.CE_Unknown
      else parse_nnf g (RDF_Graph.subject_to_term s)
  | uu___ -> parse_nnf g (RDF_Graph.subject_to_term s)
let rec collect_axioms_aux (gfull : RDF_Graph.rdf_graph)
  (ts : RDF_Graph.rdf_graph) :
  (Tableau.class_expr * Tableau.class_expr) Prims.list=
  match ts with
  | [] -> []
  | t::tl ->
      let rest = collect_axioms_aux gfull tl in
      if t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf
      then
        ((parse_nnf_subject gfull t.RDF_Triple.s),
          (parse_nnf gfull t.RDF_Triple.o))
        :: rest
      else
        if t.RDF_Triple.p = OWL_Closure.owl_equivalentClass
        then
          (let a = parse_nnf_subject gfull t.RDF_Triple.s in
           let b = parse_nnf gfull t.RDF_Triple.o in (a, b) :: (b, a) :: rest)
        else
          if
            (t.RDF_Triple.p = OWL_Vocabulary.owl_disjointWith) ||
              (t.RDF_Triple.p = OWL_Vocabulary.owl_complementOf)
          then
            (let a = parse_nnf_subject gfull t.RDF_Triple.s in
             let b = parse_nnf gfull t.RDF_Triple.o in
             let na =
               nnf
                 (Tableau.CE_ComplementOf
                    (Tableau.parse_class_expr gfull
                       (RDF_Graph.subject_to_term t.RDF_Triple.s)
                       (Prims.of_int (32)))) in
             let nb =
               nnf
                 (Tableau.CE_ComplementOf
                    (Tableau.parse_class_expr gfull t.RDF_Triple.o
                       (Prims.of_int (32)))) in
             (a, nb) :: (b, na) :: rest)
          else
            if
              (((t.RDF_Triple.p = OWL_Vocabulary.owl_onProperty) ||
                  (t.RDF_Triple.p = OWL_Vocabulary.owl_intersectionOf))
                 || (t.RDF_Triple.p = OWL_Vocabulary.owl_unionOf))
                && (RDF_Term.uu___is_S_IRI t.RDF_Triple.s)
            then
              (match t.RDF_Triple.s with
               | RDF_Term.S_IRI z ->
                   let ce =
                     nnf (Tableau.parse_ce_of_subject gfull t.RDF_Triple.s) in
                   ((Tableau.CE_Named z), ce) :: (ce, (Tableau.CE_Named z))
                     :: rest
               | uu___3 -> rest)
            else rest
let collect_axioms (g : RDF_Graph.rdf_graph) :
  (Tableau.class_expr * Tableau.class_expr) Prims.list=
  collect_axioms_aux g g
let rec apply_axioms
  (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list) (st : rstate)
  (i : RDF_Term.subject) (l : Tableau.class_expr) : (rstate * Prims.bool)=
  match tb with
  | [] -> (st, false)
  | (a, d)::tl ->
      let uu___ = if ce_eq a l then add_label st i d else (st, false) in
      (match uu___ with
       | (st1, c1) ->
           let uu___1 = apply_axioms tl st1 i l in
           (match uu___1 with | (st2, c2) -> (st2, (c1 || c2))))
let edge_entails_membership (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (a : Tableau.class_expr) : Prims.bool=
  match a with
  | Tableau.CE_MinCard (k, p) ->
      if k = Prims.int_zero
      then false
      else
        if k = Prims.int_one
        then Prims.uu___is_Cons (countable_successors g st i p)
        else
          exists_distinct_subset g st.rs_gendistinct
            (countable_successors g st i p) k
  | Tableau.CE_SomeValuesFrom (p, c) ->
      (ce_definite c) &&
        (FStar_List_Tot_Base.existsb
           (fun o ->
              match RDF_Graph.term_to_subject o with
              | FStar_Pervasives_Native.Some j -> mem_ce c (labels_of st j)
              | FStar_Pervasives_Native.None -> false)
           (countable_successors g st i p))
  | Tableau.CE_HasValue (p, v) ->
      FStar_List_Tot_Base.existsb (fun o -> RDF_Term.rdf_term_eq o v)
        (countable_successors g st i p)
  | Tableau.CE_MinQualCard (k, p, c) ->
      if (k = Prims.int_zero) || (Prims.op_Negation (ce_definite c))
      then false
      else
        (let cs = filter_in_filler st c (countable_successors g st i p) in
         if k = Prims.int_one
         then Prims.uu___is_Cons cs
         else exists_distinct_subset g st.rs_gendistinct cs k)
  | uu___ -> false
let rec apply_axioms_edges
  (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (st : rstate) (i : RDF_Term.subject) :
  (rstate * Prims.bool)=
  match tb with
  | [] -> (st, false)
  | (a, d)::tl ->
      let uu___ =
        if
          (Prims.op_Negation (mem_ce_syn a (labels_of st i))) &&
            (edge_entails_membership g st i a)
        then
          let uu___1 = add_label st i a in
          match uu___1 with
          | (sta, ca) ->
              let uu___2 = add_label sta i d in
              (match uu___2 with | (stb, cb) -> (stb, (ca || cb)))
        else (st, false) in
      (match uu___ with
       | (st1, c1) ->
           let uu___1 = apply_axioms_edges tl g st1 i in
           (match uu___1 with | (st2, c2) -> (st2, (c1 || c2))))
let rec forall_prop (st : rstate) (c : Tableau.class_expr)
  (succs : RDF_Term.rdf_term Prims.list) : (rstate * Prims.bool)=
  match succs with
  | [] -> (st, false)
  | o::tl ->
      let uu___ =
        match RDF_Graph.term_to_subject o with
        | FStar_Pervasives_Native.Some j -> add_label st j c
        | FStar_Pervasives_Native.None -> (st, false) in
      (match uu___ with
       | (st1, c1) ->
           let uu___1 = forall_prop st1 c tl in
           (match uu___1 with | (st2, c2) -> (st2, (c1 || c2))))
let witness_id (n : Prims.nat) : RDF_Term.bnode_id=
  FStar_String.concat "" [" rw_"; Prims.string_of_int n]
let ensure_witness (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (p : RDF_Term.wf_iri)
  (filler : Tableau.class_expr FStar_Pervasives_Native.option) :
  (rstate * Prims.bool)=
  let filler1 =
    match filler with
    | FStar_Pervasives_Native.Some c ->
        if ce_definite c
        then FStar_Pervasives_Native.Some c
        else FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let succs = all_successors g st i p in
  let satisfied =
    match filler1 with
    | FStar_Pervasives_Native.None -> Prims.uu___is_Cons succs
    | FStar_Pervasives_Native.Some c ->
        FStar_List_Tot_Base.existsb
          (fun o ->
             match RDF_Graph.term_to_subject o with
             | FStar_Pervasives_Native.Some j -> mem_ce c (labels_of st j)
             | FStar_Pervasives_Native.None -> false) succs in
  if satisfied
  then (st, false)
  else
    (let d = witness_depth_of st.rs_wdepth i in
     if d >= max_witness_depth
     then (st, false)
     else
       (let w = witness_id st.rs_fresh in
        let ws = RDF_Term.S_BNode w in
        let edge =
          { re_s = i; re_p = p; re_o = (RDF_Term.T_BNode w); re_count = false
          } in
        let st1 =
          {
            rs_nodes = (st.rs_nodes);
            rs_extra = (edge :: (st.rs_extra));
            rs_fresh = (st.rs_fresh + Prims.int_one);
            rs_wdepth = ((w, (d + Prims.int_one)) :: (st.rs_wdepth));
            rs_inv = (st.rs_inv);
            rs_gendistinct = (st.rs_gendistinct)
          } in
        let uu___2 =
          match filler1 with
          | FStar_Pervasives_Native.Some c -> add_label st1 ws c
          | FStar_Pervasives_Native.None -> (st1, false) in
        match uu___2 with | (st2, uu___3) -> (st2, true)))
let ensure_existential (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (p : RDF_Term.wf_iri) (c : Tableau.class_expr) :
  (rstate * Prims.bool)=
  match c with
  | Tableau.CE_OneOf (a::[]) -> add_countable_edge g st i p a
  | uu___ -> ensure_witness g st i p (FStar_Pervasives_Native.Some c)
let max_generated_witnesses : Prims.nat= (Prims.of_int (12))
let rec mint_witness_group (base : Prims.nat) (n : Prims.nat) :
  RDF_Term.bnode_id Prims.list=
  if n = Prims.int_zero
  then []
  else (witness_id ((base + n) - Prims.int_one)) ::
    (mint_witness_group base (n - Prims.int_one))
let rec min_witness_parts (i : RDF_Term.subject) (p : RDF_Term.wf_iri)
  (d : Prims.nat) (bids : RDF_Term.bnode_id Prims.list) :
  (redge Prims.list * rnode Prims.list * (RDF_Term.bnode_id * Prims.nat)
    Prims.list * RDF_Term.rdf_term Prims.list)=
  match bids with
  | [] -> ([], [], [], [])
  | b::tl ->
      let uu___ = min_witness_parts i p d tl in
      (match uu___ with
       | (es, ns, ds, ts) ->
           let wt = RDF_Term.T_BNode b in
           (({ re_s = i; re_p = p; re_o = wt; re_count = true } :: es),
             ({ rn_id = (RDF_Term.S_BNode b); rn_labels = [] } :: ns),
             ((b, (d + Prims.int_one)) :: ds), (wt :: ts)))
let ensure_min_witnesses (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (p : RDF_Term.wf_iri) (k : Prims.nat) :
  (rstate * Prims.bool)=
  if k < (Prims.of_int (2))
  then ensure_witness g st i p FStar_Pervasives_Native.None
  else
    (let kk =
       if k > max_generated_witnesses then max_generated_witnesses else k in
     let succs = all_successors g st i p in
     if exists_distinct_subset g st.rs_gendistinct succs kk
     then (st, false)
     else
       (let d = witness_depth_of st.rs_wdepth i in
        if d >= max_witness_depth
        then (st, false)
        else
          (let bids = mint_witness_group st.rs_fresh kk in
           let uu___3 = min_witness_parts i p d bids in
           match uu___3 with
           | (es, ns, ds, ts) ->
               let st1 =
                 {
                   rs_nodes = (FStar_List_Tot_Base.op_At st.rs_nodes ns);
                   rs_extra = (FStar_List_Tot_Base.op_At es st.rs_extra);
                   rs_fresh = (st.rs_fresh + kk);
                   rs_wdepth = (FStar_List_Tot_Base.op_At ds st.rs_wdepth);
                   rs_inv = (st.rs_inv);
                   rs_gendistinct = (ts :: (st.rs_gendistinct))
                 } in
               (st1, true))))
let apply_label_rules (g : RDF_Graph.rdf_graph) (st : rstate)
  (i : RDF_Term.subject) (l : Tableau.class_expr) : (rstate * Prims.bool)=
  match l with
  | Tableau.CE_IntersectionOf cs -> add_labels_all st i cs
  | Tableau.CE_AllValuesFrom (p, c) ->
      let succs = all_successors g st i p in
      let uu___ = forall_prop st c succs in
      (match uu___ with
       | (st1, c1) ->
           if p = owl_topObjectProperty
           then
             let uu___1 = add_label st1 i c in
             (match uu___1 with | (st2, c2) -> (st2, (c1 || c2)))
           else (st1, c1))
  | Tableau.CE_HasValue (p, v) -> add_countable_edge g st i p v
  | Tableau.CE_SomeValuesFrom (p, c) ->
      if is_bottom_prop p then (st, false) else ensure_existential g st i p c
  | Tableau.CE_MinQualCard (k, p, c) ->
      if (k >= Prims.int_one) && (Prims.op_Negation (is_bottom_prop p))
      then ensure_existential g st i p c
      else (st, false)
  | Tableau.CE_MinCard (k, p) ->
      if (k >= Prims.int_one) && (Prims.op_Negation (is_bottom_prop p))
      then ensure_min_witnesses g st i p k
      else (st, false)
  | uu___ -> (st, false)
let step_label (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (st : rstate) (i : RDF_Term.subject)
  (l : Tableau.class_expr) : (rstate * Prims.bool)=
  let uu___ = apply_axioms tb st i l in
  match uu___ with
  | (st1, c1) ->
      let uu___1 = apply_label_rules g st1 i l in
      (match uu___1 with | (st2, c2) -> (st2, (c1 || c2)))
let rec pass_labels
  (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (st : rstate) (i : RDF_Term.subject)
  (ls : Tableau.class_expr Prims.list) : (rstate * Prims.bool)=
  match ls with
  | [] -> (st, false)
  | l::tl ->
      let uu___ = step_label tb g st i l in
      (match uu___ with
       | (st1, c1) ->
           let uu___1 = pass_labels tb g st1 i tl in
           (match uu___1 with | (st2, c2) -> (st2, (c1 || c2))))
let rec pass_nodes
  (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (st : rstate) (ns : rnode Prims.list) :
  (rstate * Prims.bool)=
  match ns with
  | [] -> (st, false)
  | n::tl ->
      let uu___ =
        step_label tb g st n.rn_id (Tableau.CE_Named RDFS_Closure.owl_Thing) in
      (match uu___ with
       | (st0, c0) ->
           let uu___1 = pass_labels tb g st0 n.rn_id n.rn_labels in
           (match uu___1 with
            | (st1, c1) ->
                let uu___2 = apply_axioms_edges tb g st1 n.rn_id in
                (match uu___2 with
                 | (st1b, c1b) ->
                     let uu___3 = pass_nodes tb g st1b tl in
                     (match uu___3 with
                      | (st2, c2) -> (st2, (((c0 || c1) || c1b) || c2))))))
let pass (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (st : rstate) : (rstate * Prims.bool)=
  pass_nodes tb g st st.rs_nodes
type tri =
  | TClash 
  | TOpen 
  | TOut 
let uu___is_TClash (projectee : tri) : Prims.bool=
  match projectee with | TClash -> true | uu___ -> false
let uu___is_TOpen (projectee : tri) : Prims.bool=
  match projectee with | TOpen -> true | uu___ -> false
let uu___is_TOut (projectee : tri) : Prims.bool=
  match projectee with | TOut -> true | uu___ -> false
let branchable_union (ls_all : Tableau.class_expr Prims.list)
  (l : Tableau.class_expr) :
  Tableau.class_expr Prims.list FStar_Pervasives_Native.option=
  match l with
  | Tableau.CE_UnionOf cs ->
      if
        (ce_list_definite cs) &&
          (Prims.op_Negation
             (FStar_List_Tot_Base.existsb (fun d -> mem_ce d ls_all) cs))
      then FStar_Pervasives_Native.Some cs
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec find_union_labels (ls_all : Tableau.class_expr Prims.list)
  (ls_iter : Tableau.class_expr Prims.list) :
  Tableau.class_expr Prims.list FStar_Pervasives_Native.option=
  match ls_iter with
  | [] -> FStar_Pervasives_Native.None
  | l::tl ->
      (match branchable_union ls_all l with
       | FStar_Pervasives_Native.Some cs -> FStar_Pervasives_Native.Some cs
       | FStar_Pervasives_Native.None -> find_union_labels ls_all tl)
let rec find_union_nodes (ns : rnode Prims.list) :
  (RDF_Term.subject * Tableau.class_expr Prims.list)
    FStar_Pervasives_Native.option=
  match ns with
  | [] -> FStar_Pervasives_Native.None
  | n::tl ->
      (match find_union_labels n.rn_labels n.rn_labels with
       | FStar_Pervasives_Native.Some cs ->
           FStar_Pervasives_Native.Some ((n.rn_id), cs)
       | FStar_Pervasives_Native.None -> find_union_nodes tl)
let rec check (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (st : rstate) (b : Prims.nat) :
  (tri * Prims.nat)=
  if b = Prims.int_zero
  then (TOut, Prims.int_zero)
  else
    if has_clash g st
    then (TClash, (b - Prims.int_one))
    else
      (let uu___2 = pass tb g st in
       match uu___2 with
       | (st', changed) ->
           if changed
           then
             let uu___3 = check tb g st' (b - Prims.int_one) in
             (match uu___3 with | (r, b') -> (r, b'))
           else
             (match find_union_nodes st'.rs_nodes with
              | FStar_Pervasives_Native.None -> (TOpen, (b - Prims.int_one))
              | FStar_Pervasives_Native.Some (i, ds) ->
                  let uu___4 = branch tb g i ds st' (b - Prims.int_one) in
                  (match uu___4 with | (r, b') -> (r, b'))))
and branch (tb : (Tableau.class_expr * Tableau.class_expr) Prims.list)
  (g : RDF_Graph.rdf_graph) (i : RDF_Term.subject)
  (ds : Tableau.class_expr Prims.list) (st : rstate) (b : Prims.nat) :
  (tri * Prims.nat)=
  match ds with
  | [] -> (TClash, b)
  | d::tl ->
      if b = Prims.int_zero
      then (TOut, Prims.int_zero)
      else
        (let uu___1 = add_label st i d in
         match uu___1 with
         | (st1, uu___2) ->
             let uu___3 = check tb g st1 (b - Prims.int_one) in
             (match uu___3 with
              | (r1, b1) ->
                  (match r1 with
                   | TOpen -> (TOpen, b1)
                   | uu___4 ->
                       let uu___5 = branch tb g i tl st b1 in
                       (match uu___5 with
                        | (r2, b2) ->
                            (match (r1, r2) with
                             | (TClash, x) -> (x, b2)
                             | (TOut, TOpen) -> (TOpen, b2)
                             | (TOut, uu___6) -> (TOut, b2))))))
let sameAs_linked (g : RDF_Graph.rdf_graph) (a : RDF_Term.rdf_term)
  (b : RDF_Term.rdf_term) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (t.RDF_Triple.p = OWL_Closure.owl_sameAs) &&
         (((RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s) a)
             && (RDF_Term.rdf_term_eq t.RDF_Triple.o b))
            ||
            ((RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s)
                b)
               && (RDF_Term.rdf_term_eq t.RDF_Triple.o a)))) g
let rec alldiff_pair_violation (g : RDF_Graph.rdf_graph)
  (ms : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match ms with
  | [] -> false
  | h::tl ->
      (FStar_List_Tot_Base.existsb
         (fun o -> (RDF_Term.rdf_term_eq h o) || (sameAs_linked g h o)) tl)
        || (alldiff_pair_violation g tl)
let rec alldiff_lists_violation (g : RDF_Graph.rdf_graph)
  (heads : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match heads with
  | [] -> false
  | h::tl ->
      (alldiff_pair_violation g
         (Tableau.walk_rdf_list g h (Prims.of_int (64))))
        || (alldiff_lists_violation g tl)
let alldifferent_violation (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
          (RDF_Term.rdf_term_eq t.RDF_Triple.o
             (RDF_Term.T_IRI OWL_Closure.owl_AllDifferent_iri)))
         &&
         ((alldiff_lists_violation g
             (RDF_Graph_Executable.find_objects g t.RDF_Triple.s
                OWL_Closure.owl_members_iri))
            ||
            (alldiff_lists_violation g
               (RDF_Graph_Executable.find_objects g t.RDF_Triple.s
                  owl_distinctMembers)))) g
let bottom_property_assertion (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb (fun t -> is_bottom_prop t.RDF_Triple.p) g
let self_disjoint_property_in_use (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((t.RDF_Triple.p = OWL_Closure.owl_propertyDisjointWith) &&
          (RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s)
             t.RDF_Triple.o))
         &&
         (match t.RDF_Triple.s with
          | RDF_Term.S_IRI p ->
              FStar_List_Tot_Base.existsb (fun u -> u.RDF_Triple.p = p) g
          | uu___ -> false)) g
let nil_structure_violation (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       ((t.RDF_Triple.p = OWL_Vocabulary.rdf_first) ||
          (t.RDF_Triple.p = OWL_Vocabulary.rdf_rest))
         &&
         (match t.RDF_Triple.s with
          | RDF_Term.S_IRI i -> i = OWL_Vocabulary.rdf_nil
          | uu___ -> false)) g
let owl_hasSelf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#hasSelf"
let is_hasself_restriction (g : RDF_Graph.rdf_graph) (r : RDF_Term.subject) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match Tableau.find_first_object g r OWL_Vocabulary.owl_onProperty with
  | FStar_Pervasives_Native.Some (RDF_Term.T_IRI p) ->
      (match Tableau.find_first_object g r owl_hasSelf_iri with
       | FStar_Pervasives_Native.Some (RDF_Term.T_Literal l) ->
           if
             (l.RDF_Term.lexical_form = "true") ||
               (l.RDF_Term.lexical_form = "1")
           then FStar_Pervasives_Native.Some p
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let hasself_disjoint_violation_for (g : RDF_Graph.rdf_graph)
  (c : RDF_Term.wf_iri) (r : RDF_Term.subject) : Prims.bool=
  match is_hasself_restriction g r with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some p ->
      FStar_List_Tot_Base.existsb
        (fun t ->
           ((t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
              (RDF_Term.rdf_term_eq t.RDF_Triple.o (RDF_Term.T_IRI c)))
             &&
             (FStar_List_Tot_Base.existsb
                (fun u ->
                   ((u.RDF_Triple.p = p) &&
                      (RDF_Term.subject_eq u.RDF_Triple.s t.RDF_Triple.s))
                     &&
                     (RDF_Term.rdf_term_eq u.RDF_Triple.o
                        (RDF_Graph.subject_to_term t.RDF_Triple.s))) g)) g
let hasself_disjoint_violation (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (t.RDF_Triple.p = OWL_Vocabulary.owl_disjointWith) &&
         (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
          | (RDF_Term.S_IRI c, RDF_Term.T_BNode b) ->
              hasself_disjoint_violation_for g c (RDF_Term.S_BNode b)
          | (RDF_Term.S_BNode b, RDF_Term.T_IRI c) ->
              hasself_disjoint_violation_for g c (RDF_Term.S_BNode b)
          | (RDF_Term.S_IRI c, RDF_Term.T_IRI r) ->
              hasself_disjoint_violation_for g c (RDF_Term.S_IRI r)
          | (uu___, uu___1) -> false)) g
let immediate_inconsistency (g : RDF_Graph.rdf_graph) : Prims.bool=
  ((((alldifferent_violation g) || (bottom_property_assertion g)) ||
      (self_disjoint_property_in_use g))
     || (nil_structure_violation g))
    || (hasself_disjoint_violation g)
let rec init_nodes_aux (gfull : RDF_Graph.rdf_graph)
  (ts : RDF_Graph.rdf_graph) (st : rstate) : rstate=
  match ts with
  | [] -> st
  | t::tl ->
      let st' =
        if t.RDF_Triple.p = RDFS_Closure.rdf_type
        then
          let uu___ =
            add_label st t.RDF_Triple.s (parse_nnf gfull t.RDF_Triple.o) in
          match uu___ with | (st1, uu___1) -> st1
        else st in
      init_nodes_aux gfull tl st'
let init_state (g : RDF_Graph.rdf_graph) : rstate=
  init_nodes_aux g g
    {
      rs_nodes = [];
      rs_extra = [];
      rs_fresh = Prims.int_zero;
      rs_wdepth = [];
      rs_inv = (collect_inverse_pairs g);
      rs_gendistinct = []
    }
let tableau_consistent (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  Prims.bool FStar_Pervasives_Native.option=
  if immediate_inconsistency g
  then FStar_Pervasives_Native.Some false
  else
    (let tb = collect_axioms g in
     let st0 = init_state g in
     match check tb g st0 fuel with
     | (TClash, uu___1) -> FStar_Pervasives_Native.Some false
     | (TOpen, uu___1) -> FStar_Pervasives_Native.Some true
     | (TOut, uu___1) -> FStar_Pervasives_Native.None)
