open Prims
let is_control_iri (i : RDF_Term.wf_iri) : Prims.bool=
  ((((i = RDFS_Closure.rdfs_subClassOf) ||
       (i = RDFS_Closure.rdfs_subPropertyOf))
      || (i = RDFS_Closure.rdfs_domain))
     || (i = RDFS_Closure.rdfs_range))
    || (i = RDFS_Closure.rdf_type)
let is_schema_class_iri (i : RDF_Term.wf_iri) : Prims.bool=
  ((i = RDFS_Closure.rdfs_Class) || (i = RDFS_Closure.rdfs_Datatype)) ||
    (i = RDFS_Closure.rdf_Property)
let obj_not_control (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_IRI i -> Prims.op_Negation (is_control_iri i)
  | uu___ -> true
let obj_not_schema_class (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_IRI i -> Prims.op_Negation (is_schema_class_iri i)
  | uu___ -> true
let no_control_aliasing_triple (t : RDF_Triple.triple) : Prims.bool=
  if t.RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf
  then obj_not_control t.RDF_Triple.o
  else true
let no_meta_domain_range_triple (t : RDF_Triple.triple) : Prims.bool=
  if
    (t.RDF_Triple.p = RDFS_Closure.rdfs_domain) ||
      (t.RDF_Triple.p = RDFS_Closure.rdfs_range)
  then obj_not_schema_class t.RDF_Triple.o
  else true
let no_meta_superclass_triple (t : RDF_Triple.triple) : Prims.bool=
  if t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf
  then obj_not_schema_class t.RDF_Triple.o
  else true
let schema_stable_triple (t : RDF_Triple.triple) : Prims.bool=
  ((no_control_aliasing_triple t) && (no_meta_domain_range_triple t)) &&
    (no_meta_superclass_triple t)
type 'g schema_stable = unit
let rec schema_stable_check (g : RDF_Graph.rdf_graph) : Prims.bool=
  match g with
  | [] -> true
  | t::rest -> (schema_stable_triple t) && (schema_stable_check rest)
let schema_seed_base (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let ig = RDF_Indexed.build_indexed g in
  let a1 = RDFS_Closure.rdfs_rule_container_membership g ig in
  let a2 = RDFS_Closure.rdfs_rule_recognized_datatypes a1 ig in
  let a3 = RDFS_Closure.rdfs_rule_class_subclass_resource a2 ig in
  let a4 = RDFS_Closure.rdfs_rule_datatype_subclass_literal a3 ig in
  RDF_Graph.graph_dedup_sort a4
let succ_step (acc : (RDF_Term.subject Prims.list * Prims.string Prims.list))
  (o : RDF_Term.rdf_term) :
  (RDF_Term.subject Prims.list * Prims.string Prims.list)=
  let uu___ = acc in
  match uu___ with
  | (xs, ks) ->
      (match RDF_Graph.term_to_subject o with
       | FStar_Pervasives_Native.Some sj ->
           let k = RDF_Indexed.subject_to_key sj in
           if FStar_List_Tot_Base.mem k ks
           then (xs, ks)
           else ((sj :: xs), (k :: ks))
       | FStar_Pervasives_Native.None -> (xs, ks))
let succ_subjects (ig : RDF_Indexed.indexed_graph) (rel : RDF_Term.wf_iri)
  (s : RDF_Term.subject) : RDF_Term.subject Prims.list=
  let uu___ =
    FStar_List_Tot_Base.fold_left succ_step ([], [])
      (RDF_Indexed.find_objects_indexed ig s rel) in
  match uu___ with | (xs, uu___1) -> xs
let fresh_step
  (acc : (RDF_Term.subject Prims.list * Prims.string Prims.list))
  (sj : RDF_Term.subject) :
  (RDF_Term.subject Prims.list * Prims.string Prims.list)=
  let uu___ = acc in
  match uu___ with
  | (xs, ks) ->
      let k = RDF_Indexed.subject_to_key sj in
      if FStar_List_Tot_Base.mem k ks
      then (xs, ks)
      else ((sj :: xs), (k :: ks))
let rec sc_bfs (ig : RDF_Indexed.indexed_graph) (rel : RDF_Term.wf_iri)
  (fuel : Prims.nat) (frontier : RDF_Term.subject Prims.list)
  (visited : RDF_Term.subject Prims.list)
  (visited_keys : Prims.string Prims.list) :
  (RDF_Term.subject Prims.list * Prims.bool)=
  match frontier with
  | [] -> (visited, true)
  | s::rest ->
      if fuel = Prims.int_zero
      then (visited, false)
      else
        (let succs = succ_subjects ig rel s in
         let uu___1 =
           FStar_List_Tot_Base.fold_left fresh_step ([], visited_keys) succs in
         match uu___1 with
         | (fresh, keys') ->
             sc_bfs ig rel (fuel - Prims.int_one)
               (FStar_List_Tot_Base.append rest fresh)
               (FStar_List_Tot_Base.append fresh visited) keys')
let sc_reach (ig : RDF_Indexed.indexed_graph) (rel : RDF_Term.wf_iri)
  (fuel : Prims.nat) (a : RDF_Term.subject) :
  (RDF_Term.subject Prims.list * Prims.bool)=
  let start = succ_subjects ig rel a in
  let start_keys = FStar_List_Tot_Base.map RDF_Indexed.subject_to_key start in
  sc_bfs ig rel fuel start start start_keys
let emit_edge (a : RDF_Term.subject) (rel : RDF_Term.wf_iri)
  (acc : RDF_Graph.rdf_graph) (o : RDF_Term.rdf_term) : RDF_Graph.rdf_graph=
  RDF_Graph.add_triple_unchecked acc
    { RDF_Triple.s = a; RDF_Triple.p = rel; RDF_Triple.o = o }
let emit_from_node (ig : RDF_Indexed.indexed_graph) (rel : RDF_Term.wf_iri)
  (a : RDF_Term.subject) (acc : RDF_Graph.rdf_graph) (x : RDF_Term.subject) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (emit_edge a rel) acc
    (RDF_Indexed.find_objects_indexed ig x rel)
let sc_edges_for (ig : RDF_Indexed.indexed_graph) (rel : RDF_Term.wf_iri)
  (fuel : Prims.nat) (acc : (RDF_Graph.rdf_graph * Prims.bool))
  (a : RDF_Term.subject) : (RDF_Graph.rdf_graph * Prims.bool)=
  let uu___ = acc in
  match uu___ with
  | (g0, ok0) ->
      let uu___1 = sc_reach ig rel fuel a in
      (match uu___1 with
       | (reached, ok) ->
           ((FStar_List_Tot_Base.fold_left (emit_from_node ig rel a) g0
               reached), (ok0 && ok)))
let rel_subject_step (rel : RDF_Term.wf_iri)
  (acc : (RDF_Term.subject Prims.list * Prims.string Prims.list))
  (t : RDF_Triple.triple) :
  (RDF_Term.subject Prims.list * Prims.string Prims.list)=
  let uu___ = acc in
  match uu___ with
  | (xs, ks) ->
      if t.RDF_Triple.p = rel
      then
        let k = RDF_Indexed.subject_to_key t.RDF_Triple.s in
        (if FStar_List_Tot_Base.mem k ks
         then (xs, ks)
         else (((t.RDF_Triple.s) :: xs), (k :: ks)))
      else (xs, ks)
let rel_subjects (g : RDF_Graph.rdf_graph) (rel : RDF_Term.wf_iri) :
  RDF_Term.subject Prims.list=
  let uu___ = FStar_List_Tot_Base.fold_left (rel_subject_step rel) ([], []) g in
  match uu___ with | (xs, uu___1) -> xs
let is_schema_edge (t : RDF_Triple.triple) : Prims.bool=
  (t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf) ||
    (t.RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf)
let schema_dense (base : RDF_Graph.rdf_graph) : Prims.bool=
  let edges =
    FStar_List_Tot_Base.length
      (FStar_List_Tot_Base.filter is_schema_edge base) in
  let srcs =
    (FStar_List_Tot_Base.length
       (rel_subjects base RDFS_Closure.rdfs_subClassOf))
      +
      (FStar_List_Tot_Base.length
         (rel_subjects base RDFS_Closure.rdfs_subPropertyOf)) in
  edges > (((Prims.of_int (8)) * srcs) + (Prims.of_int (64)))
let schema_closed_edges (base : RDF_Graph.rdf_graph) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  let ig = RDF_Indexed.build_indexed base in
  let fuel = (RDF_Graph.graph_len base) + (Prims.of_int (2)) in
  let acc0 = ([], true) in
  let acc1 =
    FStar_List_Tot_Base.fold_left
      (sc_edges_for ig RDFS_Closure.rdfs_subClassOf fuel) acc0
      (rel_subjects base RDFS_Closure.rdfs_subClassOf) in
  FStar_List_Tot_Base.fold_left
    (sc_edges_for ig RDFS_Closure.rdfs_subPropertyOf fuel) acc1
    (rel_subjects base RDFS_Closure.rdfs_subPropertyOf)
let rdfs_closure_step_no_trans (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  let ig = RDF_Indexed.build_indexed g in
  let g1 = RDFS_Closure.rdfs_rule_subPropertyOf g ig in
  let g2 = RDFS_Closure.rdfs_rule_domain g1 ig in
  let g3 = RDFS_Closure.rdfs_rule_range g2 ig in
  let g4 = RDFS_Closure.rdfs_rule_subClassOf g3 ig in
  let g5 = RDFS_Closure.rdfs_rule_container_membership g4 ig in
  let g8 = RDFS_Closure.rdfs_rule_recognized_datatypes g5 ig in
  let g9 = RDFS_Closure.rdfs_rule_class_subclass_resource g8 ig in
  let g10 = RDFS_Closure.rdfs_rule_datatype_subclass_literal g9 ig in
  let g11 = RDFS_Closure.rdfs_rule_resource_subject g10 ig in
  let g12 = RDFS_Closure.rdfs_rule_resource_object g11 ig in
  RDF_Graph.graph_dedup_sort g12
let rec rdfs_closure_no_trans (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let g' = rdfs_closure_step_no_trans g in
      if (RDF_Graph.graph_len g') = (RDF_Graph.graph_len g)
      then g
      else rdfs_closure_no_trans g' (n - Prims.int_one)
let count_schema_edges (g : RDF_Graph.rdf_graph) : Prims.nat=
  FStar_List_Tot_Base.length (FStar_List_Tot_Base.filter is_schema_edge g)
let semi_naive_round_no_trans (full : RDF_Graph.rdf_graph)
  (delta : RDF_Graph.rdf_graph) (ig_full : RDF_Indexed.indexed_graph)
  (ig_delta : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let a1 = RDFS_Closure_SemiNaive.sn_rdfs7 full ig_delta ig_full in
  let a2 = RDFS_Closure_SemiNaive.sn_rdfs7 a1 ig_full ig_delta in
  let a3 = RDFS_Closure_SemiNaive.sn_rdfs2 a2 ig_delta ig_full in
  let a4 = RDFS_Closure_SemiNaive.sn_rdfs2 a3 ig_full ig_delta in
  let a5 = RDFS_Closure_SemiNaive.sn_rdfs3 a4 ig_delta ig_full in
  let a6 = RDFS_Closure_SemiNaive.sn_rdfs3 a5 ig_full ig_delta in
  let a7 = RDFS_Closure_SemiNaive.sn_rdfs9 a6 ig_full delta in
  let a8 = RDFS_Closure_SemiNaive.sn_rdfs9 a7 ig_delta full in
  let a9 = RDFS_Closure_SemiNaive.sn_rdfs8 a8 ig_full delta in
  let a10 = RDFS_Closure_SemiNaive.sn_rdfs13 a9 ig_full delta in
  let a11 = RDFS_Closure_SemiNaive.sn_rdfs4a a10 ig_full delta in
  let a12 = RDFS_Closure_SemiNaive.sn_rdfs4b a11 ig_full delta in
  RDF_Graph.graph_dedup_sort a12
let rec semi_naive_loop_no_trans (full : RDF_Graph.rdf_graph)
  (delta : RDF_Graph.rdf_graph) (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> full
  | n ->
      if Prims.uu___is_Nil delta
      then full
      else
        (let ig_full = RDF_Indexed.build_indexed full in
         let ig_delta = RDF_Indexed.build_indexed delta in
         let next = semi_naive_round_no_trans full delta ig_full ig_delta in
         if (RDF_Graph.graph_len next) = (RDF_Graph.graph_len full)
         then full
         else
           semi_naive_loop_no_trans next (RDF_Graph.sorted_diff next full)
             (n - Prims.int_one))
let rdfs_closure_no_trans_semi_naive (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let remaining =
        if n > Prims.int_zero then n - Prims.int_one else Prims.int_zero in
      let first = rdfs_closure_step_no_trans g in
      if (RDF_Graph.graph_len first) = (RDF_Graph.graph_len g)
      then first
      else
        semi_naive_loop_no_trans first
          (RDF_Graph.sorted_diff first (RDF_Graph.graph_dedup_sort g))
          remaining
let rdfs_closure_no_trans_checked (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  let fast = rdfs_closure_no_trans_semi_naive g fuel in
  let probe = rdfs_closure_step_no_trans fast in
  if (RDF_Graph.graph_len probe) = (RDF_Graph.graph_len fast)
  then fast
  else rdfs_closure_no_trans g fuel
let fast_pass (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  let before = count_schema_edges g in
  let r = rdfs_closure_no_trans g fuel in
  (r, ((count_schema_edges r) = before))
let rdfs_closure_with_reflexivity_fast (base : RDF_Graph.rdf_graph)
  (extra : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  (RDF_Graph.rdf_graph * Prims.bool)=
  let seeded =
    RDF_Graph.graph_dedup_sort (FStar_List_Tot_Base.append extra base) in
  let uu___ = fast_pass seeded fuel in
  match uu___ with
  | (closed, ok1) ->
      if Prims.op_Negation ok1
      then (closed, false)
      else
        (let refl_axioms = RDFS_Closure.rdfs_reflexivity_axioms closed in
         let with_refl = RDF_Graph.add_triples_if_new_bulk closed refl_axioms in
         fast_pass with_refl fuel)
let rdfs_closure_with_reflexivity_dispatch (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  let base = schema_seed_base g in
  if schema_dense base
  then RDFS_Closure_SemiNaive.rdfs_closure_with_reflexivity_checked g fuel
  else
    (let uu___1 = schema_closed_edges base in
     match uu___1 with
     | (extra, ok) ->
         if Prims.op_Negation ok
         then
           RDFS_Closure_SemiNaive.rdfs_closure_with_reflexivity_checked g
             fuel
         else
           (let uu___3 = rdfs_closure_with_reflexivity_fast base extra fuel in
            match uu___3 with
            | (r, ok_fast) ->
                if ok_fast
                then r
                else
                  RDFS_Closure_SemiNaive.rdfs_closure_with_reflexivity_checked
                    g fuel))
let ex_A : RDF_Term.wf_iri= "http://example.org/A"
let ex_B : RDF_Term.wf_iri= "http://example.org/B"
let ex_C : RDF_Term.wf_iri= "http://example.org/C"
let ex_p : RDF_Term.wf_iri= "http://example.org/p"
let ex_i : RDF_Term.wf_iri= "http://example.org/i"
let witness_stable : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI ex_A);
     RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
     RDF_Triple.o = (RDF_Term.T_IRI ex_B)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI ex_B);
    RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
    RDF_Triple.o = (RDF_Term.T_IRI ex_C)
  };
  {
    RDF_Triple.s = (RDF_Term.S_IRI ex_A);
    RDF_Triple.p = RDFS_Closure.rdf_type;
    RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdfs_Class)
  };
  {
    RDF_Triple.s = (RDF_Term.S_IRI ex_i);
    RDF_Triple.p = RDFS_Closure.rdf_type;
    RDF_Triple.o = (RDF_Term.T_IRI ex_A)
  };
  {
    RDF_Triple.s = (RDF_Term.S_IRI ex_p);
    RDF_Triple.p = RDFS_Closure.rdfs_domain;
    RDF_Triple.o = (RDF_Term.T_IRI ex_A)
  }]
let witness_reflective : RDF_Graph.rdf_graph=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI ex_p);
     RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf;
     RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdfs_subClassOf)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI ex_A);
    RDF_Triple.p = ex_p;
    RDF_Triple.o = (RDF_Term.T_IRI ex_B)
  }]
