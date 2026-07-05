open Prims
let rdfs_subClassOf : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_subClassOf
let rdfs_subPropertyOf : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_subPropertyOf
let rdfs_domain : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_domain
let rdfs_range : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_range
let rdf_type : RDF_Term.wf_iri= RDF_Vocabulary.rdf_type
let rdfs_Class : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Class
let rdf_Property : RDF_Term.wf_iri= RDF_Vocabulary.rdf_Property
let rdfs_Resource : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Resource
let rdfs_Literal : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Literal
let rdfs_ContainerMembershipProperty : RDF_Term.wf_iri=
  RDF_Vocabulary.rdfs_ContainerMembershipProperty
let rdfs_member : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_member
let rdfs_Datatype : RDF_Term.wf_iri= RDF_Vocabulary.rdfs_Datatype
let rdf_1 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_1
let rdf_2 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_2
let rdf_3 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_3
let rdf_4 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_4
let rdf_5 : RDF_Term.wf_iri= RDF_Vocabulary.rdf_5
let container_membership_properties : RDF_Term.wf_iri Prims.list=
  [rdf_1; rdf_2; rdf_3; rdf_4; rdf_5]
let rdfs_rule_subPropertyOf (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let decls =
    RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred rdfs_subPropertyOf in
  FStar_List_Tot_Base.fold_left
    (fun acc decl ->
       match ((decl.RDF_Triple.s), (decl.RDF_Triple.o)) with
       | (RDF_Term.S_IRI p, RDF_Term.T_IRI q) ->
           let matching = RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                let new_t =
                  {
                    RDF_Triple.s = (t.RDF_Triple.s);
                    RDF_Triple.p = q;
                    RDF_Triple.o = (t.RDF_Triple.o)
                  } in
                RDF_Graph.add_triple_unchecked acc2 new_t) acc matching
       | (uu___, uu___1) -> acc) g decls
let rdfs_rule_domain (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let decls = RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred rdfs_domain in
  FStar_List_Tot_Base.fold_left
    (fun acc decl ->
       match decl.RDF_Triple.s with
       | RDF_Term.S_IRI p ->
           let matching = RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                let new_t =
                  {
                    RDF_Triple.s = (t.RDF_Triple.s);
                    RDF_Triple.p = rdf_type;
                    RDF_Triple.o = (decl.RDF_Triple.o)
                  } in
                RDF_Graph.add_triple_unchecked acc2 new_t) acc matching
       | uu___ -> acc) g decls
let rdfs_rule_range (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let decls = RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred rdfs_range in
  FStar_List_Tot_Base.fold_left
    (fun acc decl ->
       match decl.RDF_Triple.s with
       | RDF_Term.S_IRI p ->
           let matching = RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                match RDF_Graph.term_to_subject t.RDF_Triple.o with
                | FStar_Pervasives_Native.Some b_subj ->
                    let new_t =
                      {
                        RDF_Triple.s = b_subj;
                        RDF_Triple.p = rdf_type;
                        RDF_Triple.o = (decl.RDF_Triple.o)
                      } in
                    RDF_Graph.add_triple_unchecked acc2 new_t
                | FStar_Pervasives_Native.None -> acc2) acc matching
       | uu___ -> acc) g decls
let rdfs_rule_subClassOf (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdf_type
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI class_iri ->
             let super_classes =
               RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI class_iri)
                 rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 b_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = rdf_type;
                      RDF_Triple.o = b_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc
               super_classes
         | uu___ -> acc
       else acc) g g
let rdfs_rule_subClassOf_trans (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_subClassOf
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some b_subj ->
             let supers =
               RDF_Indexed.find_objects_indexed ig b_subj rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = rdfs_subClassOf;
                      RDF_Triple.o = c_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc supers
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let rdfs_rule_subPropertyOf_trans (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = rdfs_subPropertyOf
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some q_subj ->
             let supers =
               RDF_Indexed.find_objects_indexed ig q_subj rdfs_subPropertyOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 r_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = rdfs_subPropertyOf;
                      RDF_Triple.o = r_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc supers
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let rdfs_rule_container_membership (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc cmp ->
       let t1 =
         {
           RDF_Triple.s = (RDF_Term.S_IRI cmp);
           RDF_Triple.p = rdfs_subPropertyOf;
           RDF_Triple.o = (RDF_Term.T_IRI rdfs_member)
         } in
       let t2 =
         {
           RDF_Triple.s = (RDF_Term.S_IRI cmp);
           RDF_Triple.p = rdf_type;
           RDF_Triple.o = (RDF_Term.T_IRI rdfs_ContainerMembershipProperty)
         } in
       RDF_Graph.add_triple_unchecked (RDF_Graph.add_triple_unchecked acc t1)
         t2) g container_membership_properties
let rdfs_closure_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let ig = RDF_Indexed.build_indexed g in
  let g1 = rdfs_rule_subPropertyOf g ig in
  let g2 = rdfs_rule_domain g1 ig in
  let g3 = rdfs_rule_range g2 ig in
  let g4 = rdfs_rule_subClassOf g3 ig in
  let g5 = rdfs_rule_container_membership g4 ig in
  let g6 = rdfs_rule_subClassOf_trans g5 ig in
  let g7 = rdfs_rule_subPropertyOf_trans g6 ig in
  RDF_Graph.graph_dedup_sort g7
let rec rdfs_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let g' = rdfs_closure_step g in
      if (RDF_Graph.graph_len g') = (RDF_Graph.graph_len g)
      then g
      else rdfs_closure g' (n - Prims.int_one)
let owl_Class : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Class"
let owl_ObjectProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#ObjectProperty"
let owl_DatatypeProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#DatatypeProperty"
let owl_Thing : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Thing"
let owl_Nothing : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#Nothing"
let owl_NamedIndividual : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#NamedIndividual"
let cons_if_new_iri (i : RDF_Term.wf_iri) (acc : RDF_Term.wf_iri Prims.list)
  : RDF_Term.wf_iri Prims.list=
  if FStar_List_Tot_Base.mem i acc then acc else i :: acc
let cons_subject_iri_if_new (s : RDF_Term.subject)
  (acc : RDF_Term.wf_iri Prims.list) : RDF_Term.wf_iri Prims.list=
  match s with
  | RDF_Term.S_IRI i -> cons_if_new_iri i acc
  | RDF_Term.S_BNode uu___ -> acc
let cons_term_iri_if_new (t : RDF_Term.rdf_term)
  (acc : RDF_Term.wf_iri Prims.list) : RDF_Term.wf_iri Prims.list=
  match t with | RDF_Term.T_IRI i -> cons_if_new_iri i acc | uu___ -> acc
let is_class_type_object (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_IRI c -> (c = rdfs_Class) || (c = owl_Class)
  | uu___ -> false
let is_property_type_object (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_IRI c ->
      ((c = rdf_Property) || (c = owl_ObjectProperty)) ||
        (c = owl_DatatypeProperty)
  | uu___ -> false
let collect_classes (g : RDF_Graph.rdf_graph) : RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 =
         if t.RDF_Triple.p = rdfs_subClassOf
         then
           cons_term_iri_if_new t.RDF_Triple.o
             (cons_subject_iri_if_new t.RDF_Triple.s acc)
         else acc in
       if
         (t.RDF_Triple.p = rdf_type) && (is_class_type_object t.RDF_Triple.o)
       then cons_subject_iri_if_new t.RDF_Triple.s acc1
       else acc1) [] g
let collect_properties (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 =
         if t.RDF_Triple.p = rdfs_subPropertyOf
         then
           cons_term_iri_if_new t.RDF_Triple.o
             (cons_subject_iri_if_new t.RDF_Triple.s acc)
         else acc in
       if
         (t.RDF_Triple.p = rdf_type) &&
           (is_property_type_object t.RDF_Triple.o)
       then cons_subject_iri_if_new t.RDF_Triple.s acc1
       else acc1) [] g
let rdfs_reflexivity_axioms (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let classes = collect_classes g in
  let properties = collect_properties g in
  let class_triples =
    FStar_List_Tot_Base.map
      (fun c ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI c);
           RDF_Triple.p = rdfs_subClassOf;
           RDF_Triple.o = (RDF_Term.T_IRI c)
         }) classes in
  let property_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = rdfs_subPropertyOf;
           RDF_Triple.o = (RDF_Term.T_IRI p)
         }) properties in
  FStar_List_Tot_Base.op_At class_triples property_triples
let rdfs_closure_with_reflexivity (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  let closed = rdfs_closure g fuel in
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = RDF_Graph.add_triples_if_new closed refl_axioms in
  rdfs_closure with_refl fuel
