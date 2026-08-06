open Prims
let owl_sameAs : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#sameAs"
let owl_SymmetricProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#SymmetricProperty"
let owl_TransitiveProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#TransitiveProperty"
let owl_InverseFunctionalProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"
let owl_FunctionalProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#FunctionalProperty"
let owl_AsymmetricProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AsymmetricProperty"
let owl_IrreflexiveProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#IrreflexiveProperty"
let owl_inverseOf : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#inverseOf"
let owl_equivalentClass : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#equivalentClass"
let owl_equivalentProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#equivalentProperty"
let owl_differentFrom : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#differentFrom"
let owl_propertyDisjointWith : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#propertyDisjointWith"
let owl_sourceIndividual : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#sourceIndividual"
let owl_assertionProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#assertionProperty"
let owl_targetIndividual : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#targetIndividual"
let owl_targetValue : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#targetValue"
let is_owl_metapredicate (p : RDF_Term.wf_iri) : Prims.bool=
  (((p = owl_sameAs) || (p = owl_inverseOf)) || (p = owl_equivalentClass)) ||
    (p = owl_equivalentProperty)
let owl_rule_equivalent_class (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_equivalentClass
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some d_subj ->
             let t1 =
               {
                 RDF_Triple.s = (t.RDF_Triple.s);
                 RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                 RDF_Triple.o = (RDF_Graph.subject_to_term d_subj)
               } in
             let t2 =
               {
                 RDF_Triple.s = d_subj;
                 RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                 RDF_Triple.o = (RDF_Graph.subject_to_term t.RDF_Triple.s)
               } in
             (match ((t.RDF_Triple.s), d_subj) with
              | (RDF_Term.S_IRI uu___, RDF_Term.S_IRI uu___1) ->
                  RDF_Graph.add_triple_unchecked
                    (RDF_Graph.add_triple_unchecked acc t1) t2
              | (RDF_Term.S_IRI uu___, RDF_Term.S_BNode uu___1) ->
                  RDF_Graph.add_triple_unchecked acc t1
              | (RDF_Term.S_BNode uu___, RDF_Term.S_IRI uu___1) ->
                  RDF_Graph.add_triple_unchecked acc t2
              | (RDF_Term.S_BNode uu___, RDF_Term.S_BNode uu___1) -> acc)
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_equivalent_property (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_equivalentProperty
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p_iri, RDF_Term.T_IRI q_iri) ->
             let t1 =
               {
                 RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                 RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf;
                 RDF_Triple.o = (RDF_Term.T_IRI q_iri)
               } in
             let t2 =
               {
                 RDF_Triple.s = (RDF_Term.S_IRI q_iri);
                 RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf;
                 RDF_Triple.o = (RDF_Term.T_IRI p_iri)
               } in
             RDF_Graph.add_triple_unchecked
               (RDF_Graph.add_triple_unchecked acc t1) t2
         | (uu___, uu___1) -> acc
       else acc) g g
let term_is_iri (i : RDF_Term.wf_iri) (x : RDF_Term.rdf_term) : Prims.bool=
  RDF_Term.rdf_term_eq x (RDF_Term.T_IRI i)
let owl_rule_scm_eqc2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
             (if
                (c_iri <> d_iri) &&
                  (FStar_List_Tot_Base.existsb (term_is_iri c_iri)
                     (RDF_Indexed.find_objects_indexed ig
                        (RDF_Term.S_IRI d_iri) RDFS_Closure.rdfs_subClassOf))
              then
                let new_t =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                    RDF_Triple.p = owl_equivalentClass;
                    RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                  } in
                RDF_Graph.add_triple_unchecked acc new_t
              else acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_rule_scm_eqp2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p_iri, RDF_Term.T_IRI q_iri) ->
             (if
                (p_iri <> q_iri) &&
                  (FStar_List_Tot_Base.existsb (term_is_iri p_iri)
                     (RDF_Indexed.find_objects_indexed ig
                        (RDF_Term.S_IRI q_iri)
                        RDFS_Closure.rdfs_subPropertyOf))
              then
                let new_t =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                    RDF_Triple.p = owl_equivalentProperty;
                    RDF_Triple.o = (RDF_Term.T_IRI q_iri)
                  } in
                RDF_Graph.add_triple_unchecked acc new_t
              else acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_rule_symmetric_property (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let sym_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_SymmetricProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> RDFS_Closure.cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if FStar_List_Tot_Base.mem t.RDF_Triple.p sym_props
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some new_subj ->
             let new_t =
               {
                 RDF_Triple.s = new_subj;
                 RDF_Triple.p = (t.RDF_Triple.p);
                 RDF_Triple.o = (RDF_Graph.subject_to_term t.RDF_Triple.s)
               } in
             RDF_Graph.add_triple_unchecked acc new_t
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_transitive_property (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let trans_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_TransitiveProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> RDFS_Closure.cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if FStar_List_Tot_Base.mem t.RDF_Triple.p trans_props
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some y_subj ->
             let zs =
               RDF_Indexed.find_objects_indexed ig y_subj t.RDF_Triple.p in
             FStar_List_Tot_Base.fold_left
               (fun acc2 z_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = (t.RDF_Triple.p);
                      RDF_Triple.o = z_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc zs
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let owl_rule_inverseOf_domain_range_flip (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc inv_t ->
       if inv_t.RDF_Triple.p = owl_inverseOf
       then
         match ((inv_t.RDF_Triple.s), (inv_t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) ->
             FStar_List_Tot_Base.fold_left
               (fun acc2 t ->
                  let add_flip target_p target_pred acc3 =
                    match t.RDF_Triple.o with
                    | RDF_Term.T_IRI c ->
                        RDF_Graph.add_triple_unchecked acc3
                          {
                            RDF_Triple.s = (RDF_Term.S_IRI target_p);
                            RDF_Triple.p = target_pred;
                            RDF_Triple.o = (RDF_Term.T_IRI c)
                          }
                    | uu___ -> acc3 in
                  match t.RDF_Triple.s with
                  | RDF_Term.S_IRI src_p ->
                      if
                        (src_p = p1) &&
                          (t.RDF_Triple.p = RDFS_Closure.rdfs_domain)
                      then add_flip p2 RDFS_Closure.rdfs_range acc2
                      else
                        if
                          (src_p = p1) &&
                            (t.RDF_Triple.p = RDFS_Closure.rdfs_range)
                        then add_flip p2 RDFS_Closure.rdfs_domain acc2
                        else
                          if
                            (src_p = p2) &&
                              (t.RDF_Triple.p = RDFS_Closure.rdfs_domain)
                          then add_flip p1 RDFS_Closure.rdfs_range acc2
                          else
                            if
                              (src_p = p2) &&
                                (t.RDF_Triple.p = RDFS_Closure.rdfs_range)
                            then add_flip p1 RDFS_Closure.rdfs_domain acc2
                            else acc2
                  | uu___ -> acc2) acc g
         | (uu___, uu___1) -> acc
       else acc) g g
let inverse_of_emit (p1_iri : RDF_Term.wf_iri) (p2_iri : RDF_Term.wf_iri)
  (acc2 : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  let add_inverse target_p acc3 =
    match RDF_Graph.term_to_subject t.RDF_Triple.o with
    | FStar_Pervasives_Native.Some new_subj ->
        let new_t =
          {
            RDF_Triple.s = new_subj;
            RDF_Triple.p = target_p;
            RDF_Triple.o = (RDF_Graph.subject_to_term t.RDF_Triple.s)
          } in
        RDF_Graph.add_triple_unchecked acc3 new_t
    | FStar_Pervasives_Native.None -> acc3 in
  if t.RDF_Triple.p = p1_iri
  then add_inverse p2_iri acc2
  else if t.RDF_Triple.p = p2_iri then add_inverse p1_iri acc2 else acc2
let owl_rule_inverse_of (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc inv_t ->
       if inv_t.RDF_Triple.p = owl_inverseOf
       then
         match ((inv_t.RDF_Triple.s), (inv_t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p1_iri, RDF_Term.T_IRI p2_iri) ->
             FStar_List_Tot_Base.fold_left (inverse_of_emit p1_iri p2_iri)
               acc g
         | (uu___, uu___1) -> acc
       else acc) g g
let collect_iri_or_bnode_terms (g : RDF_Graph.rdf_graph) :
  RDF_Term.subject Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 =
         if
           FStar_List_Tot_Base.existsb
             (fun x -> RDF_Term.subject_eq x t.RDF_Triple.s) acc
         then acc
         else (t.RDF_Triple.s) :: acc in
       match t.RDF_Triple.o with
       | RDF_Term.T_IRI i ->
           let ox = RDF_Term.S_IRI i in
           if
             FStar_List_Tot_Base.existsb (fun x -> RDF_Term.subject_eq x ox)
               acc1
           then acc1
           else ox :: acc1
       | RDF_Term.T_BNode b ->
           let ox = RDF_Term.S_BNode b in
           if
             FStar_List_Tot_Base.existsb (fun x -> RDF_Term.subject_eq x ox)
               acc1
           then acc1
           else ox :: acc1
       | RDF_Term.T_Literal uu___ -> acc1
       | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> acc1) [] g
let owl_rule_sameAs_reflexivity (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let nodes = collect_iri_or_bnode_terms g in
  FStar_List_Tot_Base.fold_left
    (fun acc n ->
       let new_t =
         {
           RDF_Triple.s = n;
           RDF_Triple.p = owl_sameAs;
           RDF_Triple.o = (RDF_Graph.subject_to_term n)
         } in
       RDF_Graph.add_triple_unchecked acc new_t) g nodes
let sameas_pair_key (xy : (RDF_Term.subject * RDF_Term.subject)) :
  Prims.string=
  let uu___ = xy in
  match uu___ with
  | (x, y) ->
      FStar_String.concat ""
        [RDF_Indexed.subject_to_key x;
        RDF_Indexed.unit_sep;
        RDF_Indexed.subject_to_key y]
let sameas_pair_cmp (a : (RDF_Term.subject * RDF_Term.subject))
  (b : (RDF_Term.subject * RDF_Term.subject)) : Prims.int=
  FStar_String.compare (sameas_pair_key a) (sameas_pair_key b)
let rec dedup_pairs_sorted_aux
  (prev_key : Prims.string FStar_Pervasives_Native.option)
  (ps : (RDF_Term.subject * RDF_Term.subject) Prims.list)
  (acc : (RDF_Term.subject * RDF_Term.subject) Prims.list) :
  (RDF_Term.subject * RDF_Term.subject) Prims.list=
  match ps with
  | [] -> FStar_List_Tot_Base.rev acc
  | p::rest ->
      let k = sameas_pair_key p in
      let dup =
        match prev_key with
        | FStar_Pervasives_Native.Some q -> q = k
        | FStar_Pervasives_Native.None -> false in
      if dup
      then dedup_pairs_sorted_aux prev_key rest acc
      else
        dedup_pairs_sorted_aux (FStar_Pervasives_Native.Some k) rest (p ::
          acc)
let sameas_pairs (ig : RDF_Indexed.indexed_graph) :
  (RDF_Term.subject * RDF_Term.subject) Prims.list=
  let raw =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_sameAs
         then
           match RDF_Graph.term_to_subject t.RDF_Triple.o with
           | FStar_Pervasives_Native.Some y ->
               (if RDF_Term.subject_eq t.RDF_Triple.s y
                then acc
                else ((t.RDF_Triple.s), y) :: acc)
           | FStar_Pervasives_Native.None -> acc
         else acc) [] ig.RDF_Indexed.ig_triples in
  let sorted = FStar_List_Tot_Base.sortWith sameas_pair_cmp raw in
  dedup_pairs_sorted_aux FStar_Pervasives_Native.None sorted []
let owl_rule_sameAs_symmetry (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let new_t =
             {
               RDF_Triple.s = y;
               RDF_Triple.p = owl_sameAs;
               RDF_Triple.o = (RDF_Graph.subject_to_term x)
             } in
           RDF_Graph.add_triple_unchecked acc new_t) g (sameas_pairs ig)
let owl_rule_differentFrom_symmetry (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_differentFrom
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some new_subj ->
             let new_t =
               {
                 RDF_Triple.s = new_subj;
                 RDF_Triple.p = owl_differentFrom;
                 RDF_Triple.o = (RDF_Graph.subject_to_term t.RDF_Triple.s)
               } in
             RDF_Graph.add_triple_unchecked acc new_t
         | FStar_Pervasives_Native.None -> acc
       else acc) g g
let sameas_trans_emit (x : RDF_Term.subject) (acc2 : RDF_Graph.rdf_graph)
  (z_term : RDF_Term.rdf_term) : RDF_Graph.rdf_graph=
  let new_t =
    { RDF_Triple.s = x; RDF_Triple.p = owl_sameAs; RDF_Triple.o = z_term } in
  RDF_Graph.add_triple_unchecked acc2 new_t
let owl_rule_sameAs_transitivity (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let zs = RDF_Indexed.find_objects_indexed ig y owl_sameAs in
           FStar_List_Tot_Base.fold_left (sameas_trans_emit x) acc zs) g
    (sameas_pairs ig)
let sameas_rep_subj_emit (y : RDF_Term.subject) (acc2 : RDF_Graph.rdf_graph)
  (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if t.RDF_Triple.p <> owl_sameAs
  then
    let new_t =
      {
        RDF_Triple.s = y;
        RDF_Triple.p = (t.RDF_Triple.p);
        RDF_Triple.o = (t.RDF_Triple.o)
      } in
    RDF_Graph.add_triple_unchecked acc2 new_t
  else acc2
let owl_rule_sameAs_replace_subject (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, s_prime) ->
           let srcs =
             RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_subj
               (RDF_Indexed.subject_to_key x) in
           FStar_List_Tot_Base.fold_left (sameas_rep_subj_emit s_prime) acc
             srcs) g (sameas_pairs ig)
let sameas_rep_obj_emit (y_term : RDF_Term.rdf_term)
  (acc2 : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if t.RDF_Triple.p <> owl_sameAs
  then
    let new_t =
      {
        RDF_Triple.s = (t.RDF_Triple.s);
        RDF_Triple.p = (t.RDF_Triple.p);
        RDF_Triple.o = y_term
      } in
    RDF_Graph.add_triple_unchecked acc2 new_t
  else acc2
let owl_rule_sameAs_replace_object (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let y_term = RDF_Graph.subject_to_term y in
           let srcs =
             RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_obj
               (RDF_Indexed.subject_to_key x) in
           FStar_List_Tot_Base.fold_left (sameas_rep_obj_emit y_term) acc
             srcs) g (sameas_pairs ig)
let sameas_rep_pred_emit (p_prime_iri : RDF_Term.wf_iri)
  (acc2 : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  let new_t =
    {
      RDF_Triple.s = (t.RDF_Triple.s);
      RDF_Triple.p = p_prime_iri;
      RDF_Triple.o = (t.RDF_Triple.o)
    } in
  RDF_Graph.add_triple_unchecked acc2 new_t
let owl_rule_sameAs_replace_predicate (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       match xy with
       | (RDF_Term.S_IRI p_iri, RDF_Term.S_IRI p_prime_iri) ->
           if is_owl_metapredicate p_iri
           then acc
           else
             (let srcs =
                RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred p_iri in
              FStar_List_Tot_Base.fold_left
                (sameas_rep_pred_emit p_prime_iri) acc srcs)
       | uu___ -> acc) g (sameas_pairs ig)
let is_list_cell_functional_property (p : RDF_Term.wf_iri) : Prims.bool=
  (p = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first") ||
    (p = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest")
let owl_prp_fp_collect_step (acc : RDF_Term.wf_iri Prims.list)
  (t : RDF_Triple.triple) : RDF_Term.wf_iri Prims.list=
  if
    (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
      (RDF_Term.rdf_term_eq t.RDF_Triple.o
         (RDF_Term.T_IRI owl_FunctionalProperty))
  then
    match t.RDF_Triple.s with
    | RDF_Term.S_IRI p_iri ->
        (if is_list_cell_functional_property p_iri
         then acc
         else RDFS_Closure.cons_if_new_iri p_iri acc)
    | uu___ -> acc
  else acc
let owl_prp_fp_emit (y_subj : RDF_Term.subject) (t1_o : RDF_Term.rdf_term)
  (acc2 : RDF_Graph.rdf_graph) (z : RDF_Term.rdf_term) : RDF_Graph.rdf_graph=
  if RDF_Term.rdf_term_eq z t1_o
  then acc2
  else
    RDF_Graph.add_triple_unchecked acc2
      { RDF_Triple.s = y_subj; RDF_Triple.p = owl_sameAs; RDF_Triple.o = z }
let owl_prp_fp_step (ig : RDF_Indexed.indexed_graph)
  (fp_props : RDF_Term.wf_iri Prims.list) (acc : RDF_Graph.rdf_graph)
  (t1 : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if FStar_List_Tot_Base.mem t1.RDF_Triple.p fp_props
  then
    match RDF_Graph.term_to_subject t1.RDF_Triple.o with
    | FStar_Pervasives_Native.None -> acc
    | FStar_Pervasives_Native.Some y_subj ->
        let zs =
          RDF_Indexed.find_objects_indexed ig t1.RDF_Triple.s t1.RDF_Triple.p in
        FStar_List_Tot_Base.fold_left
          (owl_prp_fp_emit y_subj t1.RDF_Triple.o) acc zs
  else acc
let owl_rule_functional (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fp_props = FStar_List_Tot_Base.fold_left owl_prp_fp_collect_step [] g in
  FStar_List_Tot_Base.fold_left (owl_prp_fp_step ig fp_props) g g
let owl_prp_ifp_collect_step (acc : RDF_Term.wf_iri Prims.list)
  (t : RDF_Triple.triple) : RDF_Term.wf_iri Prims.list=
  if
    (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
      (RDF_Term.rdf_term_eq t.RDF_Triple.o
         (RDF_Term.T_IRI owl_InverseFunctionalProperty))
  then
    match t.RDF_Triple.s with
    | RDF_Term.S_IRI p_iri -> RDFS_Closure.cons_if_new_iri p_iri acc
    | uu___ -> acc
  else acc
let owl_prp_ifp_emit (t1_s : RDF_Term.subject) (acc2 : RDF_Graph.rdf_graph)
  (z : RDF_Term.subject) : RDF_Graph.rdf_graph=
  if RDF_Term.subject_eq z t1_s
  then acc2
  else
    RDF_Graph.add_triple_unchecked acc2
      {
        RDF_Triple.s = t1_s;
        RDF_Triple.p = owl_sameAs;
        RDF_Triple.o = (RDF_Graph.subject_to_term z)
      }
let owl_prp_ifp_step (ig : RDF_Indexed.indexed_graph)
  (ifp_props : RDF_Term.wf_iri Prims.list) (acc : RDF_Graph.rdf_graph)
  (t1 : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if FStar_List_Tot_Base.mem t1.RDF_Triple.p ifp_props
  then
    let zs =
      RDF_Indexed.find_subjects_indexed ig t1.RDF_Triple.p t1.RDF_Triple.o in
    FStar_List_Tot_Base.fold_left (owl_prp_ifp_emit t1.RDF_Triple.s) acc zs
  else acc
let owl_rule_inverse_functional (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let ifp_props = FStar_List_Tot_Base.fold_left owl_prp_ifp_collect_step [] g in
  FStar_List_Tot_Base.fold_left (owl_prp_ifp_step ig ifp_props) g g
let differentFrom_in_graph (g : RDF_Graph.rdf_graph) (a : RDF_Term.rdf_term)
  (b : RDF_Term.rdf_term) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (t.RDF_Triple.p = owl_differentFrom) &&
         (((RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s) a)
             && (RDF_Term.rdf_term_eq t.RDF_Triple.o b))
            ||
            ((RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s)
                b)
               && (RDF_Term.rdf_term_eq t.RDF_Triple.o a)))) g
let owl_rule_pdw_to_differentFrom (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let pdw_pairs =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_propertyDisjointWith
         then
           match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
           | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) -> (p1, p2) :: acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc pair ->
       let uu___ = pair in
       match uu___ with
       | (p1, p2) ->
           FStar_List_Tot_Base.fold_left
             (fun acc1 t1 ->
                if t1.RDF_Triple.p = p1
                then
                  match RDF_Graph.term_to_subject t1.RDF_Triple.o with
                  | FStar_Pervasives_Native.None -> acc1
                  | FStar_Pervasives_Native.Some o1_subj ->
                      let o2_terms =
                        RDF_Indexed.find_objects_indexed ig t1.RDF_Triple.s
                          p2 in
                      FStar_List_Tot_Base.fold_left
                        (fun acc2 o2_term ->
                           if RDF_Term.rdf_term_eq t1.RDF_Triple.o o2_term
                           then acc2
                           else
                             (match RDF_Graph.term_to_subject o2_term with
                              | FStar_Pervasives_Native.None -> acc2
                              | FStar_Pervasives_Native.Some uu___2 ->
                                  let new_t =
                                    {
                                      RDF_Triple.s = o1_subj;
                                      RDF_Triple.p = owl_differentFrom;
                                      RDF_Triple.o = o2_term
                                    } in
                                  RDF_Graph.add_triple_unchecked acc2 new_t))
                        acc1 o2_terms
                else acc1) acc g) g pdw_pairs
let owl_rule_pdw_shared_value_to_differentFrom (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let pdw_pairs =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_propertyDisjointWith
         then
           match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
           | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) -> (p1, p2) :: acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc pair ->
       let uu___ = pair in
       match uu___ with
       | (p1, p2) ->
           FStar_List_Tot_Base.fold_left
             (fun acc1 t1 ->
                if t1.RDF_Triple.p = p1
                then
                  let ys =
                    RDF_Indexed.find_subjects_indexed ig p2 t1.RDF_Triple.o in
                  FStar_List_Tot_Base.fold_left
                    (fun acc2 y ->
                       if RDF_Term.subject_eq y t1.RDF_Triple.s
                       then acc2
                       else
                         (let new_t =
                            {
                              RDF_Triple.s = (t1.RDF_Triple.s);
                              RDF_Triple.p = owl_differentFrom;
                              RDF_Triple.o = (RDF_Graph.subject_to_term y)
                            } in
                          RDF_Graph.add_triple_unchecked acc2 new_t)) acc1 ys
                else acc1) acc g) g pdw_pairs
let owl_rule_fp_diff_to_diff (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fp_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_FunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri ->
               (if is_list_cell_functional_property p_iri
                then acc
                else RDFS_Closure.cons_if_new_iri p_iri acc)
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t1 ->
       if FStar_List_Tot_Base.mem t1.RDF_Triple.p fp_props
       then
         FStar_List_Tot_Base.fold_left
           (fun acc2 t2 ->
              if
                ((t2.RDF_Triple.p = t1.RDF_Triple.p) &&
                   (Prims.op_Negation
                      (RDF_Term.subject_eq t2.RDF_Triple.s t1.RDF_Triple.s)))
                  &&
                  (differentFrom_in_graph g t1.RDF_Triple.o t2.RDF_Triple.o)
              then
                let new_t =
                  {
                    RDF_Triple.s = (t1.RDF_Triple.s);
                    RDF_Triple.p = owl_differentFrom;
                    RDF_Triple.o =
                      (RDF_Graph.subject_to_term t2.RDF_Triple.s)
                  } in
                RDF_Graph.add_triple_unchecked acc2 new_t
              else acc2) acc g
       else acc) g g
let owl_rule_ifp_diff_to_diff (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let ifp_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_InverseFunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> RDFS_Closure.cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc t1 ->
       if FStar_List_Tot_Base.mem t1.RDF_Triple.p ifp_props
       then
         FStar_List_Tot_Base.fold_left
           (fun acc2 t2 ->
              if
                ((t2.RDF_Triple.p = t1.RDF_Triple.p) &&
                   (Prims.op_Negation
                      (RDF_Term.subject_eq t2.RDF_Triple.s t1.RDF_Triple.s)))
                  &&
                  (differentFrom_in_graph g
                     (RDF_Graph.subject_to_term t1.RDF_Triple.s)
                     (RDF_Graph.subject_to_term t2.RDF_Triple.s))
              then
                match RDF_Graph.term_to_subject t1.RDF_Triple.o with
                | FStar_Pervasives_Native.None -> acc2
                | FStar_Pervasives_Native.Some y1_subj ->
                    let new_t =
                      {
                        RDF_Triple.s = y1_subj;
                        RDF_Triple.p = owl_differentFrom;
                        RDF_Triple.o = (t2.RDF_Triple.o)
                      } in
                    RDF_Graph.add_triple_unchecked acc2 new_t
              else acc2) acc g
       else acc) g g
let owl_Restriction_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#Restriction"
let owl_onProperty_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onProperty"
let owl_someValuesFrom_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#someValuesFrom"
let owl_allValuesFrom_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#allValuesFrom"
let owl_minCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#minCardinality"
let owl_minQualifiedCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"
let owl_maxCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#maxCardinality"
let owl_maxQualifiedCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"
let owl_qualifiedCardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"
let owl_cardinality_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#cardinality"
let owl_onClass_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#onClass"
let owl_hasValue_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#hasValue"
let owl_hasSelf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#hasSelf"
let owl_oneOf_iri : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#oneOf"
let owl_intersectionOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#intersectionOf"
let owl_unionOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#unionOf"
let owl_complementOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#complementOf"
let owl_disjointWith_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#disjointWith"
let is_schema_metapredicate (p : RDF_Term.wf_iri) : Prims.bool=
  ((((((((((((((((((((((((((is_owl_metapredicate p) ||
                             (p =
                                "http://www.w3.org/2002/07/owl#differentFrom"))
                            || (p = RDFS_Closure.rdfs_subClassOf))
                           || (p = RDFS_Closure.rdfs_subPropertyOf))
                          || (p = RDFS_Closure.rdfs_domain))
                         || (p = RDFS_Closure.rdfs_range))
                        || (p = owl_onProperty_iri))
                       || (p = owl_onClass_iri))
                      || (p = owl_someValuesFrom_iri))
                     || (p = owl_allValuesFrom_iri))
                    || (p = owl_hasValue_iri))
                   || (p = owl_hasSelf_iri))
                  || (p = owl_minCardinality_iri))
                 || (p = owl_maxCardinality_iri))
                || (p = owl_cardinality_iri))
               || (p = owl_minQualifiedCardinality_iri))
              || (p = owl_maxQualifiedCardinality_iri))
             || (p = owl_qualifiedCardinality_iri))
            || (p = owl_oneOf_iri))
           || (p = owl_intersectionOf_iri))
          || (p = owl_unionOf_iri))
         || (p = owl_complementOf_iri))
        || (p = owl_disjointWith_iri))
       || (p = "http://www.w3.org/2002/07/owl#propertyChainAxiom"))
      || (p = "http://www.w3.org/2002/07/owl#distinctMembers"))
     || (p = "http://www.w3.org/2002/07/owl#members"))
    || (p = "http://www.w3.org/2002/07/owl#disjointUnionOf")
let xsd_nonNegativeInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#nonNegativeInteger"
let one_nonNegInteger_literal : RDF_Term.wf_literal=
  let l =
    {
      RDF_Term.lexical_form = "1";
      RDF_Term.datatype = xsd_nonNegativeInteger;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    } in
  l
let true_xsd_boolean_literal : RDF_Term.wf_literal=
  let l =
    {
      RDF_Term.lexical_form = "true";
      RDF_Term.datatype = RDF_Term.xsd_boolean;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    } in
  l
let literal_is_true_boolean (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l ->
      (l.RDF_Term.datatype = RDF_Term.xsd_boolean) &&
        ((l.RDF_Term.lexical_form = "true") ||
           (l.RDF_Term.lexical_form = "1"))
  | uu___ -> false
let canonical_svf_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_svf_"; p; "__on__"; c]
let canonical_minqc1_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_minqc1_"; p; "__on__"; c]
let canonical_maxqc1_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_maxqc1_"; p; "__on__"; c]
let canonical_exactqc1_restriction_bnode (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_exactqc1_"; p; "__on__"; c]
let owl_rule_disjoint_with_propagation (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_disjointWith_iri
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
             let new_t =
               {
                 RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                 RDF_Triple.p = owl_disjointWith_iri;
                 RDF_Triple.o = (RDF_Term.T_IRI c_iri)
               } in
             RDF_Graph.add_triple_unchecked acc new_t
         | (uu___, uu___1) -> acc
       else
         if t.RDF_Triple.p = owl_complementOf_iri
         then
           (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
            | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
                let t1 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                    RDF_Triple.p = owl_disjointWith_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                  } in
                let t2 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                    RDF_Triple.p = owl_disjointWith_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                  } in
                RDF_Graph.add_triple_unchecked
                  (RDF_Graph.add_triple_unchecked acc t1) t2
            | (uu___1, uu___2) -> acc)
         else acc) g g
let canonical_complement_bnode (c : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_comp__"; c]
let owl_rule_disjoint_to_complement (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_disjointWith_iri
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c1, RDF_Term.T_IRI c2) ->
             (if
                (c2 = RDFS_Closure.owl_Thing) ||
                  (c2 = RDFS_Closure.owl_Nothing)
              then acc
              else
                (let cb = RDF_Term.S_BNode (canonical_complement_bnode c2) in
                 let shape1 =
                   {
                     RDF_Triple.s = cb;
                     RDF_Triple.p = owl_complementOf_iri;
                     RDF_Triple.o = (RDF_Term.T_IRI c2)
                   } in
                 let shape2 =
                   {
                     RDF_Triple.s = cb;
                     RDF_Triple.p = RDFS_Closure.rdf_type;
                     RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
                   } in
                 let acc1 =
                   RDF_Graph.add_triple_unchecked
                     (RDF_Graph.add_triple_unchecked acc shape1) shape2 in
                 let members =
                   RDF_Indexed.find_subjects_indexed ig RDFS_Closure.rdf_type
                     (RDF_Term.T_IRI c1) in
                 FStar_List_Tot_Base.fold_left
                   (fun acc2 x ->
                      let memb =
                        {
                          RDF_Triple.s = x;
                          RDF_Triple.p = RDFS_Closure.rdf_type;
                          RDF_Triple.o =
                            (RDF_Term.T_BNode (canonical_complement_bnode c2))
                        } in
                      RDF_Graph.add_triple_unchecked acc2 memb) acc1 members))
         | (uu___, uu___1) -> acc
       else acc) g g
let svf2_max_witness_depth : Prims.nat= (Prims.of_int (3))
let svf2_witness_marker : Prims.string= "__rl_svf2w_d"
let svf2_depth_char (d : Prims.nat) : Prims.string=
  if d = Prims.int_zero
  then "0"
  else
    if d = Prims.int_one
    then "1"
    else if d = (Prims.of_int (2)) then "2" else "3"
let subject_svf2_depth (x : RDF_Term.subject) : Prims.nat=
  match x with
  | RDF_Term.S_IRI uu___ -> Prims.int_zero
  | RDF_Term.S_BNode b ->
      let plen = FStar_String.strlen svf2_witness_marker in
      let blen = FStar_String.strlen b in
      if blen <= plen
      then Prims.int_zero
      else
        if (FStar_String.sub b Prims.int_zero plen) = svf2_witness_marker
        then
          (let dc = FStar_String.sub b plen Prims.int_one in
           if dc = "0"
           then Prims.int_zero
           else
             if dc = "1"
             then Prims.int_one
             else if dc = "2" then (Prims.of_int (2)) else (Prims.of_int (3)))
        else Prims.int_zero
let canonical_svf2_witness_bnode (depth : Prims.nat) (p : RDF_Term.wf_iri)
  (c : RDF_Term.wf_iri) (x : RDF_Term.subject) : RDF_Term.bnode_id=
  FStar_String.concat ""
    [svf2_witness_marker;
    svf2_depth_char depth;
    "__on__";
    p;
    "__filler__";
    c;
    "__from__";
    RDF_Indexed.subject_to_key x]
let owl_rule_svf2_existential_witness (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc svf_t ->
       if svf_t.RDF_Triple.p = owl_someValuesFrom_iri
       then
         match svf_t.RDF_Triple.o with
         | RDF_Term.T_IRI c ->
             (if c = RDFS_Closure.owl_Thing
              then acc
              else
                (let r_subj = svf_t.RDF_Triple.s in
                 let onprops =
                   RDF_Indexed.find_objects_indexed ig r_subj
                     owl_onProperty_iri in
                 FStar_List_Tot_Base.fold_left
                   (fun acc2 op_term ->
                      match op_term with
                      | RDF_Term.T_IRI p ->
                          let r_term = RDF_Graph.subject_to_term r_subj in
                          let ancestors =
                            RDF_Indexed.find_subjects_indexed ig
                              RDFS_Closure.rdfs_subClassOf r_term in
                          FStar_List_Tot_Base.fold_left
                            (fun acc3 cls_subj ->
                               match cls_subj with
                               | RDF_Term.S_IRI cls_iri ->
                                   let members =
                                     RDF_Indexed.find_subjects_indexed ig
                                       RDFS_Closure.rdf_type
                                       (RDF_Term.T_IRI cls_iri) in
                                   FStar_List_Tot_Base.fold_left
                                     (fun acc4 x ->
                                        let d = subject_svf2_depth x in
                                        if d >= svf2_max_witness_depth
                                        then acc4
                                        else
                                          (let w_id =
                                             canonical_svf2_witness_bnode
                                               (d + Prims.int_one) p c x in
                                           let edge_t =
                                             {
                                               RDF_Triple.s = x;
                                               RDF_Triple.p = p;
                                               RDF_Triple.o =
                                                 (RDF_Term.T_BNode w_id)
                                             } in
                                           let type_t =
                                             {
                                               RDF_Triple.s =
                                                 (RDF_Term.S_BNode w_id);
                                               RDF_Triple.p =
                                                 RDFS_Closure.rdf_type;
                                               RDF_Triple.o =
                                                 (RDF_Term.T_IRI c)
                                             } in
                                           RDF_Graph.add_triple_unchecked
                                             (RDF_Graph.add_triple_unchecked
                                                acc4 edge_t) type_t)) acc3
                                     members
                               | uu___1 -> acc3) acc2 ancestors
                      | uu___1 -> acc2) acc onprops))
         | uu___ -> acc
       else acc) g g
let owl_rule_minc1_bridge (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_someValuesFrom_iri) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI RDFS_Closure.owl_Thing))
       then
         let onprops =
           RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
             owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI uu___ ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = owl_minCardinality_iri;
                      RDF_Triple.o =
                        (RDF_Term.T_Literal one_nonNegInteger_literal)
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t
              | uu___ -> acc2) acc onprops
       else acc) g g
let owl_rule_cls_hv1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc hv_t ->
       if hv_t.RDF_Triple.p = owl_hasValue_iri
       then
         let r_subj = hv_t.RDF_Triple.s in
         let v = hv_t.RDF_Triple.o in
         let onprops =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI p ->
                  let members =
                    RDF_Indexed.find_subjects_indexed ig
                      RDFS_Closure.rdf_type
                      (RDF_Graph.subject_to_term r_subj) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       RDF_Graph.add_triple_unchecked acc3
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = p;
                           RDF_Triple.o = v
                         }) acc2 members
              | uu___ -> acc2) acc onprops
       else acc) g g
let owl_rule_cls_hv2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc hv_t ->
       if hv_t.RDF_Triple.p = owl_hasValue_iri
       then
         let r_subj = hv_t.RDF_Triple.s in
         let v = hv_t.RDF_Triple.o in
         let onprops =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI p ->
                  let holders = RDF_Indexed.find_subjects_indexed ig p v in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       RDF_Graph.add_triple_unchecked acc3
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = RDFS_Closure.rdf_type;
                           RDF_Triple.o = (RDF_Graph.subject_to_term r_subj)
                         }) acc2 holders
              | uu___ -> acc2) acc onprops
       else acc) g g
let rl_canonical_bnode_prefix : Prims.string= "__rl_"
let bnode_is_rl_canonical (b : RDF_Term.bnode_id) : Prims.bool=
  let plen = FStar_String.strlen rl_canonical_bnode_prefix in
  let blen = FStar_String.strlen b in
  if blen < plen
  then false
  else (FStar_String.sub b Prims.int_zero plen) = rl_canonical_bnode_prefix
let is_owl_or_rdfs_metaclass (i : RDF_Term.wf_iri) : Prims.bool=
  ((((((((((((((((((((((((i = RDFS_Closure.owl_Class) ||
                           (i = owl_Restriction_iri))
                          || (i = RDFS_Closure.owl_NamedIndividual))
                         || (i = RDFS_Closure.owl_Thing))
                        || (i = RDFS_Closure.owl_Nothing))
                       || (i = owl_FunctionalProperty))
                      || (i = owl_InverseFunctionalProperty))
                     || (i = owl_TransitiveProperty))
                    || (i = owl_SymmetricProperty))
                   ||
                   (i = "http://www.w3.org/2002/07/owl#AsymmetricProperty"))
                  || (i = "http://www.w3.org/2002/07/owl#ReflexiveProperty"))
                 || (i = "http://www.w3.org/2002/07/owl#IrreflexiveProperty"))
                || (i = RDFS_Closure.owl_ObjectProperty))
               || (i = RDFS_Closure.owl_DatatypeProperty))
              || (i = "http://www.w3.org/2002/07/owl#AnnotationProperty"))
             || (i = "http://www.w3.org/2002/07/owl#OntologyProperty"))
            || (i = "http://www.w3.org/2002/07/owl#Ontology"))
           || (i = RDFS_Closure.rdfs_Class))
          || (i = RDFS_Closure.rdfs_Resource))
         || (i = RDFS_Closure.rdfs_Datatype))
        || (i = RDFS_Closure.rdfs_Literal))
       || (i = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property"))
      || (i = "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"))
     || (i = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement"))
    ||
    (let xsd_prefix = "http://www.w3.org/2001/XMLSchema#" in
     let plen = FStar_String.strlen xsd_prefix in
     let ilen = FStar_String.strlen i in
     if ilen < plen
     then false
     else (FStar_String.sub i Prims.int_zero plen) = xsd_prefix)
let edge_subject_is_safe (e : RDF_Triple.triple) : Prims.bool=
  match e.RDF_Triple.s with
  | RDF_Term.S_IRI i ->
      (Prims.op_Negation (is_schema_metapredicate i)) &&
        (Prims.op_Negation (is_owl_or_rdfs_metaclass i))
  | RDF_Term.S_BNode b -> Prims.op_Negation (bnode_is_rl_canonical b)
let owl_rule_cls_svf2_qualified (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = RDFS_Closure.rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match RDF_Graph.term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes =
                  RDF_Indexed.find_objects_indexed ig y_subj
                    RDFS_Closure.rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = RDFS_Closure.owl_Thing
                         then acc2
                         else
                           (let rb = canonical_svf_restriction_bnode p c in
                            let rb_subj = RDF_Term.S_BNode rb in
                            let rb_term = RDF_Term.T_BNode rb in
                            let shape1 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI owl_Restriction_iri)
                              } in
                            let shape2 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onProperty_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI p)
                              } in
                            let shape3 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_someValuesFrom_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI c)
                              } in
                            let memb =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o = rb_term
                              } in
                            RDF_Graph.add_triple_unchecked
                              (RDF_Graph.add_triple_unchecked
                                 (RDF_Graph.add_triple_unchecked
                                    (RDF_Graph.add_triple_unchecked acc2
                                       shape1) shape2) shape3) memb)
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_minc_qual1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = RDFS_Closure.rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match RDF_Graph.term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes =
                  RDF_Indexed.find_objects_indexed ig y_subj
                    RDFS_Closure.rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = RDFS_Closure.owl_Thing
                         then acc2
                         else
                           (let rb = canonical_minqc1_restriction_bnode p c in
                            let rb_subj = RDF_Term.S_BNode rb in
                            let rb_term = RDF_Term.T_BNode rb in
                            let shape1 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI owl_Restriction_iri)
                              } in
                            let shape2 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onProperty_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI p)
                              } in
                            let shape3 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p =
                                  owl_minQualifiedCardinality_iri;
                                RDF_Triple.o =
                                  (RDF_Term.T_Literal
                                     one_nonNegInteger_literal)
                              } in
                            let shape4 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onClass_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI c)
                              } in
                            let memb =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o = rb_term
                              } in
                            RDF_Graph.add_triple_unchecked
                              (RDF_Graph.add_triple_unchecked
                                 (RDF_Graph.add_triple_unchecked
                                    (RDF_Graph.add_triple_unchecked
                                       (RDF_Graph.add_triple_unchecked acc2
                                          shape1) shape2) shape3) shape4)
                              memb)
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_hasself1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc hs_t ->
       if
         (hs_t.RDF_Triple.p = owl_hasSelf_iri) &&
           (literal_is_true_boolean hs_t.RDF_Triple.o)
       then
         let r_subj = hs_t.RDF_Triple.s in
         let onprops =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI p ->
                  let members =
                    RDF_Indexed.find_subjects_indexed ig
                      RDFS_Closure.rdf_type
                      (RDF_Graph.subject_to_term r_subj) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       RDF_Graph.add_triple_unchecked acc3
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = p;
                           RDF_Triple.o = (RDF_Graph.subject_to_term x)
                         }) acc2 members
              | uu___ -> acc2) acc onprops
       else acc) g g
let canonical_hasself_restriction_bnode (p : RDF_Term.wf_iri) :
  RDF_Term.bnode_id= FStar_String.concat "" ["__rl_hasself_"; p]
let owl_rule_cls_hasself2_synth (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let uu___ = ig in
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = RDFS_Closure.rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           if
             RDF_Term.rdf_term_eq
               (RDF_Graph.subject_to_term edge.RDF_Triple.s)
               edge.RDF_Triple.o
           then
             (let p = edge.RDF_Triple.p in
              let x = edge.RDF_Triple.s in
              let rb = canonical_hasself_restriction_bnode p in
              let rb_subj = RDF_Term.S_BNode rb in
              let rb_term = RDF_Term.T_BNode rb in
              let shape1 =
                {
                  RDF_Triple.s = rb_subj;
                  RDF_Triple.p = RDFS_Closure.rdf_type;
                  RDF_Triple.o = (RDF_Term.T_IRI owl_Restriction_iri)
                } in
              let shape2 =
                {
                  RDF_Triple.s = rb_subj;
                  RDF_Triple.p = owl_onProperty_iri;
                  RDF_Triple.o = (RDF_Term.T_IRI p)
                } in
              let shape3 =
                {
                  RDF_Triple.s = rb_subj;
                  RDF_Triple.p = owl_hasSelf_iri;
                  RDF_Triple.o =
                    (RDF_Term.T_Literal true_xsd_boolean_literal)
                } in
              let memb =
                {
                  RDF_Triple.s = x;
                  RDF_Triple.p = RDFS_Closure.rdf_type;
                  RDF_Triple.o = rb_term
                } in
              RDF_Graph.add_triple_unchecked
                (RDF_Graph.add_triple_unchecked
                   (RDF_Graph.add_triple_unchecked
                      (RDF_Graph.add_triple_unchecked acc shape1) shape2)
                   shape3) memb)
           else acc) g g
let canonical_svf_thing_restriction_bnode (p : RDF_Term.wf_iri) :
  RDF_Term.bnode_id= FStar_String.concat "" ["__rl_svfthing_"; p]
let owl_rule_cls_svf_thing_materialize (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let uu___ = ig in
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = RDFS_Closure.rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match RDF_Graph.term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some uu___3 ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let rb = canonical_svf_thing_restriction_bnode p in
                let rb_subj = RDF_Term.S_BNode rb in
                let rb_term = RDF_Term.T_BNode rb in
                let shape1 =
                  {
                    RDF_Triple.s = rb_subj;
                    RDF_Triple.p = RDFS_Closure.rdf_type;
                    RDF_Triple.o = (RDF_Term.T_IRI owl_Restriction_iri)
                  } in
                let shape2 =
                  {
                    RDF_Triple.s = rb_subj;
                    RDF_Triple.p = owl_onProperty_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI p)
                  } in
                let shape3 =
                  {
                    RDF_Triple.s = rb_subj;
                    RDF_Triple.p = owl_someValuesFrom_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
                  } in
                let memb =
                  {
                    RDF_Triple.s = x;
                    RDF_Triple.p = RDFS_Closure.rdf_type;
                    RDF_Triple.o = rb_term
                  } in
                RDF_Graph.add_triple_unchecked
                  (RDF_Graph.add_triple_unchecked
                     (RDF_Graph.add_triple_unchecked
                        (RDF_Graph.add_triple_unchecked acc shape1) shape2)
                     shape3) memb)) g g
let canonical_svf_thing_witness_bnode (p : RDF_Term.wf_iri)
  (x : RDF_Term.subject) : RDF_Term.bnode_id=
  FStar_String.concat ""
    ["__rl_svfthingw__on__"; p; "__from__"; RDF_Indexed.subject_to_key x]
let owl_rule_cls_svf_thing_witness (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc svf_t ->
       if
         (svf_t.RDF_Triple.p = owl_someValuesFrom_iri) &&
           (RDF_Term.rdf_term_eq svf_t.RDF_Triple.o
              (RDF_Term.T_IRI RDFS_Closure.owl_Thing))
       then
         let onprops =
           RDF_Indexed.find_objects_indexed ig svf_t.RDF_Triple.s
             owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 op_term ->
              match op_term with
              | RDF_Term.T_IRI p ->
                  let members =
                    RDF_Indexed.find_subjects_indexed ig
                      RDFS_Closure.rdf_type
                      (RDF_Graph.subject_to_term svf_t.RDF_Triple.s) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       let w_id = canonical_svf_thing_witness_bnode p x in
                       let edge_t =
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = p;
                           RDF_Triple.o = (RDF_Term.T_BNode w_id)
                         } in
                       RDF_Graph.add_triple_unchecked acc3 edge_t) acc2
                    members
              | uu___ -> acc2) acc onprops
       else acc) g g
let owl_rule_cax_dw_to_differentFrom (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let dw_pairs =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_disjointWith_iri
         then
           match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
           | (RDF_Term.S_IRI c1, RDF_Term.T_IRI c2) -> (c1, c2) :: acc
           | uu___ -> acc
         else acc) [] g in
  FStar_List_Tot_Base.fold_left
    (fun acc pair ->
       let uu___ = pair in
       match uu___ with
       | (c1, c2) ->
           let xs =
             RDF_Indexed.find_subjects_indexed ig RDFS_Closure.rdf_type
               (RDF_Term.T_IRI c1) in
           let ys =
             RDF_Indexed.find_subjects_indexed ig RDFS_Closure.rdf_type
               (RDF_Term.T_IRI c2) in
           FStar_List_Tot_Base.fold_left
             (fun acc1 x ->
                FStar_List_Tot_Base.fold_left
                  (fun acc2 y ->
                     if RDF_Term.subject_eq x y
                     then acc2
                     else
                       RDF_Graph.add_triple_unchecked acc2
                         {
                           RDF_Triple.s = x;
                           RDF_Triple.p = owl_differentFrom;
                           RDF_Triple.o = (RDF_Graph.subject_to_term y)
                         }) acc1 ys) acc xs) g dw_pairs
let count_p_successors_typed_c (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (x : RDF_Term.subject)
  (p : RDF_Term.wf_iri) (c : RDF_Term.wf_iri) : Prims.nat=
  let succs = RDF_Indexed.find_objects_indexed ig x p in
  let typed =
    FStar_List_Tot_Base.filter
      (fun y ->
         match RDF_Graph.term_to_subject y with
         | FStar_Pervasives_Native.None -> false
         | FStar_Pervasives_Native.Some y_subj ->
             let ts =
               RDF_Indexed.find_objects_indexed ig y_subj
                 RDFS_Closure.rdf_type in
             FStar_List_Tot_Base.existsb
               (fun t -> RDF_Term.rdf_term_eq t (RDF_Term.T_IRI c)) ts) succs in
  FStar_List_Tot_Base.length typed
let owl_rule_cls_maxqc1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = RDFS_Closure.rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match RDF_Graph.term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes =
                  RDF_Indexed.find_objects_indexed ig y_subj
                    RDFS_Closure.rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = RDFS_Closure.owl_Thing
                         then acc2
                         else
                           (let n = count_p_successors_typed_c g ig x p c in
                            if n > Prims.int_one
                            then acc2
                            else
                              (let rb =
                                 canonical_maxqc1_restriction_bnode p c in
                               let rb_subj = RDF_Term.S_BNode rb in
                               let rb_term = RDF_Term.T_BNode rb in
                               let shape1 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p = RDFS_Closure.rdf_type;
                                   RDF_Triple.o =
                                     (RDF_Term.T_IRI owl_Restriction_iri)
                                 } in
                               let shape2 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p = owl_onProperty_iri;
                                   RDF_Triple.o = (RDF_Term.T_IRI p)
                                 } in
                               let shape3 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p =
                                     owl_maxQualifiedCardinality_iri;
                                   RDF_Triple.o =
                                     (RDF_Term.T_Literal
                                        one_nonNegInteger_literal)
                                 } in
                               let shape4 =
                                 {
                                   RDF_Triple.s = rb_subj;
                                   RDF_Triple.p = owl_onClass_iri;
                                   RDF_Triple.o = (RDF_Term.T_IRI c)
                                 } in
                               let memb =
                                 {
                                   RDF_Triple.s = x;
                                   RDF_Triple.p = RDFS_Closure.rdf_type;
                                   RDF_Triple.o = rb_term
                                 } in
                               RDF_Graph.add_triple_unchecked
                                 (RDF_Graph.add_triple_unchecked
                                    (RDF_Graph.add_triple_unchecked
                                       (RDF_Graph.add_triple_unchecked
                                          (RDF_Graph.add_triple_unchecked
                                             acc2 shape1) shape2) shape3)
                                    shape4) memb))
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_exactqc1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc edge ->
       if
         (edge.RDF_Triple.p = RDFS_Closure.rdf_type) ||
           (is_schema_metapredicate edge.RDF_Triple.p)
       then acc
       else
         if Prims.op_Negation (edge_subject_is_safe edge)
         then acc
         else
           (match RDF_Graph.term_to_subject edge.RDF_Triple.o with
            | FStar_Pervasives_Native.None -> acc
            | FStar_Pervasives_Native.Some y_subj ->
                let p = edge.RDF_Triple.p in
                let x = edge.RDF_Triple.s in
                let ytypes =
                  RDF_Indexed.find_objects_indexed ig y_subj
                    RDFS_Closure.rdf_type in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 ty ->
                     match ty with
                     | RDF_Term.T_IRI c ->
                         if c = RDFS_Closure.owl_Thing
                         then acc2
                         else
                           (let rb = canonical_exactqc1_restriction_bnode p c in
                            let rb_subj = RDF_Term.S_BNode rb in
                            let rb_term = RDF_Term.T_BNode rb in
                            let shape1 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI owl_Restriction_iri)
                              } in
                            let shape2 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onProperty_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI p)
                              } in
                            let shape3 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_qualifiedCardinality_iri;
                                RDF_Triple.o =
                                  (RDF_Term.T_Literal
                                     one_nonNegInteger_literal)
                              } in
                            let shape4 =
                              {
                                RDF_Triple.s = rb_subj;
                                RDF_Triple.p = owl_onClass_iri;
                                RDF_Triple.o = (RDF_Term.T_IRI c)
                              } in
                            let memb =
                              {
                                RDF_Triple.s = x;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o = rb_term
                              } in
                            RDF_Graph.add_triple_unchecked
                              (RDF_Graph.add_triple_unchecked
                                 (RDF_Graph.add_triple_unchecked
                                    (RDF_Graph.add_triple_unchecked
                                       (RDF_Graph.add_triple_unchecked acc2
                                          shape1) shape2) shape3) shape4)
                              memb)
                     | uu___2 -> acc2) acc ytypes)) g g
let owl_rule_cls_maxc2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_maxCardinality_iri) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_Literal one_nonNegInteger_literal))
       then
         let r_subj = t.RDF_Triple.s in
         let props =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 p_term ->
              match p_term with
              | RDF_Term.T_IRI p ->
                  let members =
                    RDF_Indexed.find_subjects_indexed ig
                      RDFS_Closure.rdf_type
                      (RDF_Graph.subject_to_term r_subj) in
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 x ->
                       let ys = RDF_Indexed.find_objects_indexed ig x p in
                       FStar_List_Tot_Base.fold_left
                         (fun acc4 y1 ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc5 y2 ->
                                 if RDF_Term.rdf_term_eq y1 y2
                                 then acc5
                                 else
                                   (match RDF_Graph.term_to_subject y1 with
                                    | FStar_Pervasives_Native.None -> acc5
                                    | FStar_Pervasives_Native.Some y1_subj ->
                                        let new_t =
                                          {
                                            RDF_Triple.s = y1_subj;
                                            RDF_Triple.p = owl_sameAs;
                                            RDF_Triple.o = y2
                                          } in
                                        RDF_Graph.add_triple_unchecked acc5
                                          new_t)) acc4 ys) acc3 ys) acc2
                    members
              | uu___ -> acc2) acc props
       else acc) g g
let object_has_type (ig : RDF_Indexed.indexed_graph) (y : RDF_Term.rdf_term)
  (c : RDF_Term.wf_iri) : Prims.bool=
  match RDF_Graph.term_to_subject y with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some y_subj ->
      let ts =
        RDF_Indexed.find_objects_indexed ig y_subj RDFS_Closure.rdf_type in
      FStar_List_Tot_Base.existsb
        (fun ty -> RDF_Term.rdf_term_eq ty (RDF_Term.T_IRI c)) ts
let owl_rule_cls_maxqc_comp (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_maxQualifiedCardinality_iri) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_Literal one_nonNegInteger_literal))
       then
         let r_subj = t.RDF_Triple.s in
         let props =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
         let classes =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onClass_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 p_term ->
              match p_term with
              | RDF_Term.T_IRI p ->
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 c_term ->
                       match c_term with
                       | RDF_Term.T_IRI c ->
                           if
                             (c = RDFS_Closure.owl_Thing) ||
                               (c = RDFS_Closure.owl_Nothing)
                           then acc3
                           else
                             (let members =
                                RDF_Indexed.find_subjects_indexed ig
                                  RDFS_Closure.rdf_type
                                  (RDF_Graph.subject_to_term r_subj) in
                              FStar_List_Tot_Base.fold_left
                                (fun acc4 x ->
                                   let ys =
                                     RDF_Indexed.find_objects_indexed ig x p in
                                   FStar_List_Tot_Base.fold_left
                                     (fun acc5 y1 ->
                                        if object_has_type ig y1 c
                                        then
                                          FStar_List_Tot_Base.fold_left
                                            (fun acc6 y2 ->
                                               if RDF_Term.rdf_term_eq y1 y2
                                               then acc6
                                               else
                                                 if
                                                   Prims.op_Negation
                                                     (differentFrom_in_graph
                                                        g y1 y2)
                                                 then acc6
                                                 else
                                                   (match RDF_Graph.term_to_subject
                                                            y2
                                                    with
                                                    | FStar_Pervasives_Native.None
                                                        -> acc6
                                                    | FStar_Pervasives_Native.Some
                                                        y2_subj ->
                                                        let cb =
                                                          RDF_Term.S_BNode
                                                            (canonical_complement_bnode
                                                               c) in
                                                        let shape1 =
                                                          {
                                                            RDF_Triple.s = cb;
                                                            RDF_Triple.p =
                                                              owl_complementOf_iri;
                                                            RDF_Triple.o =
                                                              (RDF_Term.T_IRI
                                                                 c)
                                                          } in
                                                        let shape2 =
                                                          {
                                                            RDF_Triple.s = cb;
                                                            RDF_Triple.p =
                                                              RDFS_Closure.rdf_type;
                                                            RDF_Triple.o =
                                                              (RDF_Term.T_IRI
                                                                 RDFS_Closure.owl_Class)
                                                          } in
                                                        let memb =
                                                          {
                                                            RDF_Triple.s =
                                                              y2_subj;
                                                            RDF_Triple.p =
                                                              RDFS_Closure.rdf_type;
                                                            RDF_Triple.o =
                                                              (RDF_Term.T_BNode
                                                                 (canonical_complement_bnode
                                                                    c))
                                                          } in
                                                        RDF_Graph.add_triple_unchecked
                                                          (RDF_Graph.add_triple_unchecked
                                                             (RDF_Graph.add_triple_unchecked
                                                                acc6 shape1)
                                                             shape2) memb))
                                            acc5 ys
                                        else acc5) acc4 ys) acc3 members)
                       | uu___ -> acc3) acc2 classes
              | uu___ -> acc2) acc props
       else acc) g g
let owl_rule_cls_avf1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t_avf ->
       if t_avf.RDF_Triple.p = owl_allValuesFrom_iri
       then
         match t_avf.RDF_Triple.o with
         | RDF_Term.T_IRI d ->
             let r_subj = t_avf.RDF_Triple.s in
             let props =
               RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
             FStar_List_Tot_Base.fold_left
               (fun acc2 p_term ->
                  match p_term with
                  | RDF_Term.T_IRI p ->
                      let members =
                        RDF_Indexed.find_subjects_indexed ig
                          RDFS_Closure.rdf_type
                          (RDF_Graph.subject_to_term r_subj) in
                      FStar_List_Tot_Base.fold_left
                        (fun acc3 x ->
                           let ys = RDF_Indexed.find_objects_indexed ig x p in
                           FStar_List_Tot_Base.fold_left
                             (fun acc4 y ->
                                match RDF_Graph.term_to_subject y with
                                | FStar_Pervasives_Native.None -> acc4
                                | FStar_Pervasives_Native.Some y_subj ->
                                    let new_t =
                                      {
                                        RDF_Triple.s = y_subj;
                                        RDF_Triple.p = RDFS_Closure.rdf_type;
                                        RDF_Triple.o = (RDF_Term.T_IRI d)
                                      } in
                                    RDF_Graph.add_triple_unchecked acc4 new_t)
                             acc3 ys) acc2 members
                  | uu___ -> acc2) acc props
         | uu___ -> acc
       else acc) g g
let owl_ReflexiveProperty : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#ReflexiveProperty"
let prp_rfl_individuals (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 = RDFS_Closure.cons_subject_iri_if_new t.RDF_Triple.s acc in
       RDFS_Closure.cons_term_iri_if_new t.RDF_Triple.o acc1) [] g
let owl_rule_reflexive_property (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let refl_props =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_ReflexiveProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p_iri -> RDFS_Closure.cons_if_new_iri p_iri acc
           | uu___ -> acc
         else acc) [] g in
  match refl_props with
  | [] -> g
  | uu___ ->
      let indivs = prp_rfl_individuals g in
      FStar_List_Tot_Base.fold_left
        (fun acc p_iri ->
           FStar_List_Tot_Base.fold_left
             (fun acc2 x ->
                let new_t =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI x);
                    RDF_Triple.p = p_iri;
                    RDF_Triple.o = (RDF_Term.T_IRI x)
                  } in
                RDF_Graph.add_triple_unchecked acc2 new_t) acc indivs) g
        refl_props
let owl_rule_scm_cls_restriction (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_Restriction_iri))
       then
         let new_t =
           {
             RDF_Triple.s = (t.RDF_Triple.s);
             RDF_Triple.p = RDFS_Closure.rdf_type;
             RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
           } in
         RDF_Graph.add_triple_unchecked acc new_t
       else acc) g g
let rdf_first : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let owl_propertyChainAxiom : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#propertyChainAxiom"
let owl_hasKey : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#hasKey"
let decode_chain_pair (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (head_subj : RDF_Term.subject) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) FStar_Pervasives_Native.option=
  let firsts1 = RDF_Indexed.find_objects_indexed ig head_subj rdf_first in
  let rests1 = RDF_Indexed.find_objects_indexed ig head_subj rdf_rest in
  match (firsts1, rests1) with
  | ((RDF_Term.T_IRI p1)::uu___, tail_term::uu___1) ->
      (match RDF_Graph.term_to_subject tail_term with
       | FStar_Pervasives_Native.Some tail_subj ->
           let firsts2 =
             RDF_Indexed.find_objects_indexed ig tail_subj rdf_first in
           let rests2 =
             RDF_Indexed.find_objects_indexed ig tail_subj rdf_rest in
           (match (firsts2, rests2) with
            | ((RDF_Term.T_IRI p2)::uu___2, (RDF_Term.T_IRI nil_iri)::uu___3)
                ->
                if nil_iri = rdf_nil_iri
                then FStar_Pervasives_Native.Some (p1, p2)
                else FStar_Pervasives_Native.None
            | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let owl_rule_property_chain_2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc chain_t ->
       if chain_t.RDF_Triple.p = owl_propertyChainAxiom
       then
         match ((chain_t.RDF_Triple.s),
                 (RDF_Graph.term_to_subject chain_t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI p_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_chain_pair g ig list_subj with
              | FStar_Pervasives_Native.Some (p1, p2) ->
                  FStar_List_Tot_Base.fold_left
                    (fun acc2 t1 ->
                       if t1.RDF_Triple.p = p1
                       then
                         match RDF_Graph.term_to_subject t1.RDF_Triple.o with
                         | FStar_Pervasives_Native.Some y_subj ->
                             let zs =
                               RDF_Indexed.find_objects_indexed ig y_subj p2 in
                             FStar_List_Tot_Base.fold_left
                               (fun acc3 z_term ->
                                  let new_t =
                                    {
                                      RDF_Triple.s = (t1.RDF_Triple.s);
                                      RDF_Triple.p = p_iri;
                                      RDF_Triple.o = z_term
                                    } in
                                  RDF_Graph.add_triple_unchecked acc3 new_t)
                               acc2 zs
                         | FStar_Pervasives_Native.None -> acc2
                       else acc2) acc g
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let rec decode_chain_list_fuel (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (head_subj : RDF_Term.subject)
  (fuel : Prims.nat) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let is_nil =
    match head_subj with
    | RDF_Term.S_IRI i -> i = rdf_nil_iri
    | uu___ -> false in
  if is_nil
  then FStar_Pervasives_Native.Some []
  else
    if fuel = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (let firsts = RDF_Indexed.find_objects_indexed ig head_subj rdf_first in
       let rests = RDF_Indexed.find_objects_indexed ig head_subj rdf_rest in
       match (firsts, rests) with
       | ((RDF_Term.T_IRI p1)::uu___2, tail_term::uu___3) ->
           (match RDF_Graph.term_to_subject tail_term with
            | FStar_Pervasives_Native.Some tail_subj ->
                (match decode_chain_list_fuel g ig tail_subj
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.Some tail_props ->
                     FStar_Pervasives_Native.Some (p1 :: tail_props)
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
let decode_chain_list (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (head_subj : RDF_Term.subject) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let fuel = (RDF_Graph.graph_len g) + Prims.int_one in
  match decode_chain_list_fuel g ig head_subj fuel with
  | FStar_Pervasives_Native.Some [] -> FStar_Pervasives_Native.None
  | x -> x
let rec find_chain_endpoints (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (chain : RDF_Term.wf_iri Prims.list)
  (x : RDF_Term.subject) : RDF_Term.rdf_term Prims.list=
  match chain with
  | [] -> [RDF_Graph.subject_to_term x]
  | p::rest ->
      let next_terms = RDF_Indexed.find_objects_indexed ig x p in
      FStar_List_Tot_Base.fold_left
        (fun acc y_term ->
           match RDF_Graph.term_to_subject y_term with
           | FStar_Pervasives_Native.Some y_subj ->
               FStar_List_Tot_Base.append acc
                 (find_chain_endpoints g ig rest y_subj)
           | FStar_Pervasives_Native.None -> acc) [] next_terms
let owl_rule_property_chain_n (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let chain_decls =
    RDF_Indexed.bucket_lookup ig.RDF_Indexed.ig_pred owl_propertyChainAxiom in
  match chain_decls with
  | [] -> g
  | uu___ ->
      let starting_subjects =
        FStar_List_Tot_Base.fold_left
          (fun acc t ->
             if
               FStar_List_Tot_Base.existsb
                 (fun s -> RDF_Term.subject_eq s t.RDF_Triple.s) acc
             then acc
             else (t.RDF_Triple.s) :: acc) [] g in
      FStar_List_Tot_Base.fold_left
        (fun acc chain_t ->
           if chain_t.RDF_Triple.p = owl_propertyChainAxiom
           then
             match ((chain_t.RDF_Triple.s),
                     (RDF_Graph.term_to_subject chain_t.RDF_Triple.o))
             with
             | (RDF_Term.S_IRI p_iri, FStar_Pervasives_Native.Some list_subj)
                 ->
                 (match decode_chain_list g ig list_subj with
                  | FStar_Pervasives_Native.Some chain ->
                      if
                        (FStar_List_Tot_Base.length chain) >=
                          (Prims.of_int (2))
                      then
                        FStar_List_Tot_Base.fold_left
                          (fun acc1 x ->
                             let zs = find_chain_endpoints g ig chain x in
                             FStar_List_Tot_Base.fold_left
                               (fun acc2 z_term ->
                                  let new_t =
                                    {
                                      RDF_Triple.s = x;
                                      RDF_Triple.p = p_iri;
                                      RDF_Triple.o = z_term
                                    } in
                                  RDF_Graph.add_triple_unchecked acc2 new_t)
                               acc1 zs) acc starting_subjects
                      else acc
                  | FStar_Pervasives_Native.None -> acc)
             | (uu___1, uu___2) -> acc
           else acc) g g
let owl_rule_chain_to_transitive (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc chain_t ->
       if chain_t.RDF_Triple.p = owl_propertyChainAxiom
       then
         match ((chain_t.RDF_Triple.s),
                 (RDF_Graph.term_to_subject chain_t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI p_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_chain_pair g ig list_subj with
              | FStar_Pervasives_Native.Some (q1, q2) ->
                  if (q1 = p_iri) && (q2 = p_iri)
                  then
                    let new_t =
                      {
                        RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                        RDF_Triple.p = RDFS_Closure.rdf_type;
                        RDF_Triple.o =
                          (RDF_Term.T_IRI owl_TransitiveProperty)
                      } in
                    RDF_Graph.add_triple_unchecked acc new_t
                  else acc
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let canonical_chainl1_bnode (p : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_chainl1__"; p]
let canonical_chainl2_bnode (p : RDF_Term.wf_iri) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_chainl2__"; p]
let owl_rule_transitive_to_chain (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_TransitiveProperty))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI p_iri ->
             let l1 = canonical_chainl1_bnode p_iri in
             let l2 = canonical_chainl2_bnode p_iri in
             RDF_Graph.add_triples_if_new acc
               [{
                  RDF_Triple.s = (RDF_Term.S_IRI p_iri);
                  RDF_Triple.p = owl_propertyChainAxiom;
                  RDF_Triple.o = (RDF_Term.T_BNode l1)
                };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l1);
                 RDF_Triple.p = rdf_first;
                 RDF_Triple.o = (RDF_Term.T_IRI p_iri)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l1);
                 RDF_Triple.p = rdf_rest;
                 RDF_Triple.o = (RDF_Term.T_BNode l2)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l2);
                 RDF_Triple.p = rdf_first;
                 RDF_Triple.o = (RDF_Term.T_IRI p_iri)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_BNode l2);
                 RDF_Triple.p = rdf_rest;
                 RDF_Triple.o = (RDF_Term.T_IRI rdf_nil_iri)
               }]
         | uu___ -> acc
       else acc) g g
let owl_rule_named_sameAs_to_equivClass (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let is_class i =
    let types =
      RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI i)
        RDFS_Closure.rdf_type in
    FStar_List_Tot_Base.existsb
      (fun x ->
         RDF_Term.rdf_term_eq x (RDF_Term.T_IRI RDFS_Closure.owl_Class))
      types in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_sameAs
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
             (if ((c_iri <> d_iri) && (is_class c_iri)) && (is_class d_iri)
              then
                let t1 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                    RDF_Triple.p = owl_equivalentClass;
                    RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                  } in
                let t2 =
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                    RDF_Triple.p = owl_equivalentClass;
                    RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                  } in
                RDF_Graph.add_triple_unchecked
                  (RDF_Graph.add_triple_unchecked acc t1) t2
              else acc)
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_semantics_direct : Prims.string= "DIRECT"
let owl_semantics_rdf_based : Prims.string= "RDF-BASED"
let owl_semantics_rdf_based_full : Prims.string= "RDF-BASED-FULL"
let owl_rule_named_equivClass_to_sameAs_mode (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (mode : Prims.string) :
  RDF_Graph.rdf_graph=
  if
    (mode = owl_semantics_rdf_based) || (mode = owl_semantics_rdf_based_full)
  then g
  else
    (let is_class i =
       let types =
         RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI i)
           RDFS_Closure.rdf_type in
       FStar_List_Tot_Base.existsb
         (fun x ->
            RDF_Term.rdf_term_eq x (RDF_Term.T_IRI RDFS_Closure.owl_Class))
         types in
     let has_extra_property i =
       FStar_List_Tot_Base.existsb
         (fun t ->
            match t.RDF_Triple.s with
            | RDF_Term.S_IRI si ->
                ((((si = i) && (t.RDF_Triple.p <> RDFS_Closure.rdf_type)) &&
                    (t.RDF_Triple.p <> owl_equivalentClass))
                   && (t.RDF_Triple.p <> RDFS_Closure.rdfs_subClassOf))
                  && (t.RDF_Triple.p <> owl_sameAs)
            | RDF_Term.S_BNode uu___1 -> false) g in
     FStar_List_Tot_Base.fold_left
       (fun acc t ->
          if t.RDF_Triple.p = owl_equivalentClass
          then
            match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
            | (RDF_Term.S_IRI c_iri, RDF_Term.T_IRI d_iri) ->
                (if
                   (((c_iri <> d_iri) && (is_class c_iri)) &&
                      (is_class d_iri))
                     &&
                     ((has_extra_property c_iri) ||
                        (has_extra_property d_iri))
                 then
                   let t1 =
                     {
                       RDF_Triple.s = (RDF_Term.S_IRI c_iri);
                       RDF_Triple.p = owl_sameAs;
                       RDF_Triple.o = (RDF_Term.T_IRI d_iri)
                     } in
                   let t2 =
                     {
                       RDF_Triple.s = (RDF_Term.S_IRI d_iri);
                       RDF_Triple.p = owl_sameAs;
                       RDF_Triple.o = (RDF_Term.T_IRI c_iri)
                     } in
                   RDF_Graph.add_triple_unchecked
                     (RDF_Graph.add_triple_unchecked acc t1) t2
                 else acc)
            | (uu___1, uu___2) -> acc
          else acc) g g)
let owl_rule_named_equivClass_to_sameAs (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  owl_rule_named_equivClass_to_sameAs_mode g ig owl_semantics_direct
let rec decode_iri_list (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (head_subj : RDF_Term.subject)
  (fuel : Prims.nat) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  let is_nil_head =
    match head_subj with
    | RDF_Term.S_IRI i -> i = rdf_nil_iri
    | uu___ -> false in
  if is_nil_head
  then FStar_Pervasives_Native.Some []
  else
    if fuel = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (let firsts = RDF_Indexed.find_objects_indexed ig head_subj rdf_first in
       let rests = RDF_Indexed.find_objects_indexed ig head_subj rdf_rest in
       match (firsts, rests) with
       | ((RDF_Term.T_IRI p_iri)::uu___2, tail_term::uu___3) ->
           (match RDF_Graph.term_to_subject tail_term with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some tail_subj ->
                (match decode_iri_list g ig tail_subj (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some rest_props ->
                     FStar_Pervasives_Native.Some (p_iri :: rest_props)))
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
let collect_haskey_axioms (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_hasKey
       then
         match ((t.RDF_Triple.s), (RDF_Graph.term_to_subject t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI c_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_iri_list g ig list_subj fuel with
              | FStar_Pervasives_Native.Some props -> (c_iri, props) :: acc
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) [] g
let owl_cls_int1_emit (x : RDF_Term.subject) (acc2 : RDF_Graph.rdf_graph)
  (ci : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  RDF_Graph.add_triple_unchecked acc2
    {
      RDF_Triple.s = x;
      RDF_Triple.p = RDFS_Closure.rdf_type;
      RDF_Triple.o = (RDF_Term.T_IRI ci)
    }
let owl_cls_int1_x_step (members : RDF_Term.wf_iri Prims.list)
  (acc1 : RDF_Graph.rdf_graph) (x : RDF_Term.subject) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (owl_cls_int1_emit x) acc1 members
let owl_cls_int1_step (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (fuel : Prims.nat)
  (acc : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if t.RDF_Triple.p = owl_intersectionOf_iri
  then
    match RDF_Graph.term_to_subject t.RDF_Triple.o with
    | FStar_Pervasives_Native.None -> acc
    | FStar_Pervasives_Native.Some list_subj ->
        (match decode_iri_list g ig list_subj fuel with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some members ->
             let xs =
               RDF_Indexed.find_subjects_indexed ig RDFS_Closure.rdf_type
                 (RDF_Graph.subject_to_term t.RDF_Triple.s) in
             FStar_List_Tot_Base.fold_left (owl_cls_int1_x_step members) acc
               xs)
  else acc
let owl_rule_cls_int1 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left (owl_cls_int1_step g ig fuel) g g
let owl_disjointUnionOf_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#disjointUnionOf"
let owl_cls_oneof_emit (c_iri : RDF_Term.wf_iri) (acc1 : RDF_Graph.rdf_graph)
  (i : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  RDF_Graph.add_triple_unchecked acc1
    {
      RDF_Triple.s = (RDF_Term.S_IRI i);
      RDF_Triple.p = RDFS_Closure.rdf_type;
      RDF_Triple.o = (RDF_Term.T_IRI c_iri)
    }
let owl_cls_oneof_step (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (fuel : Prims.nat)
  (acc : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if t.RDF_Triple.p = owl_oneOf_iri
  then
    match ((t.RDF_Triple.s), (RDF_Graph.term_to_subject t.RDF_Triple.o)) with
    | (RDF_Term.S_IRI c_iri, FStar_Pervasives_Native.Some list_subj) ->
        (match decode_iri_list g ig list_subj fuel with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some members ->
             FStar_List_Tot_Base.fold_left (owl_cls_oneof_emit c_iri) acc
               members)
    | (uu___, uu___1) -> acc
  else acc
let owl_rule_cls_oneof (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left (owl_cls_oneof_step g ig fuel) g g
let owl_cls_uni_decode_axiom (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (fuel : Prims.nat) (t : RDF_Triple.triple)
  :
  (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list)
    FStar_Pervasives_Native.option=
  match ((t.RDF_Triple.s), (RDF_Graph.term_to_subject t.RDF_Triple.o)) with
  | (RDF_Term.S_IRI c_iri, FStar_Pervasives_Native.Some list_subj) ->
      (match decode_iri_list g ig list_subj fuel with
       | FStar_Pervasives_Native.Some members ->
           FStar_Pervasives_Native.Some (c_iri, members)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let owl_cls_uni_sub_emit (c_iri : RDF_Term.wf_iri)
  (acc1 : RDF_Graph.rdf_graph) (ci : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  RDF_Graph.add_triple_unchecked acc1
    {
      RDF_Triple.s = (RDF_Term.S_IRI ci);
      RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
      RDF_Triple.o = (RDF_Term.T_IRI c_iri)
    }
let owl_cls_uni_disjoint_inner (c1 : RDF_Term.wf_iri)
  (acc3 : RDF_Graph.rdf_graph) (c2 : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  if c1 = c2
  then acc3
  else
    RDF_Graph.add_triple_unchecked acc3
      {
        RDF_Triple.s = (RDF_Term.S_IRI c1);
        RDF_Triple.p = owl_disjointWith_iri;
        RDF_Triple.o = (RDF_Term.T_IRI c2)
      }
let owl_cls_uni_disjoint_outer (members : RDF_Term.wf_iri Prims.list)
  (acc2 : RDF_Graph.rdf_graph) (c1 : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (owl_cls_uni_disjoint_inner c1) acc2 members
let owl_cls_uni_step (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (fuel : Prims.nat)
  (acc : RDF_Graph.rdf_graph) (t : RDF_Triple.triple) : RDF_Graph.rdf_graph=
  if
    (t.RDF_Triple.p = owl_unionOf_iri) ||
      (t.RDF_Triple.p = owl_disjointUnionOf_iri)
  then
    match owl_cls_uni_decode_axiom g ig fuel t with
    | FStar_Pervasives_Native.None -> acc
    | FStar_Pervasives_Native.Some (c_iri, members) ->
        let acc_sub =
          FStar_List_Tot_Base.fold_left (owl_cls_uni_sub_emit c_iri) acc
            members in
        (if t.RDF_Triple.p = owl_disjointUnionOf_iri
         then
           let acc_u =
             RDF_Graph.add_triple_unchecked acc_sub
               {
                 RDF_Triple.s = (t.RDF_Triple.s);
                 RDF_Triple.p = owl_unionOf_iri;
                 RDF_Triple.o = (t.RDF_Triple.o)
               } in
           FStar_List_Tot_Base.fold_left (owl_cls_uni_disjoint_outer members)
             acc_u members
         else acc_sub)
  else acc
let owl_rule_cls_uni (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left (owl_cls_uni_step g ig fuel) g g
let known_not_member (ig : RDF_Indexed.indexed_graph) (x : RDF_Term.subject)
  (c : RDF_Term.wf_iri) : Prims.bool=
  let types = RDF_Indexed.find_objects_indexed ig x RDFS_Closure.rdf_type in
  let c_excl =
    FStar_List_Tot_Base.append
      (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI c)
         owl_complementOf_iri)
      (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI c)
         owl_disjointWith_iri) in
  FStar_List_Tot_Base.existsb
    (fun d ->
       (FStar_List_Tot_Base.existsb (fun z -> RDF_Term.rdf_term_eq z d)
          c_excl)
         ||
         (match RDF_Graph.term_to_subject d with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some d_subj ->
              let d_excl =
                FStar_List_Tot_Base.append
                  (RDF_Indexed.find_objects_indexed ig d_subj
                     owl_complementOf_iri)
                  (RDF_Indexed.find_objects_indexed ig d_subj
                     owl_disjointWith_iri) in
              FStar_List_Tot_Base.existsb
                (fun z -> RDF_Term.rdf_term_eq z (RDF_Term.T_IRI c)) d_excl))
    types
let owl_rule_cls_uni_elim (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = owl_unionOf_iri) ||
           (t.RDF_Triple.p = owl_disjointUnionOf_iri)
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some list_subj ->
             (match decode_iri_list g ig list_subj fuel with
              | FStar_Pervasives_Native.None -> acc
              | FStar_Pervasives_Native.Some members ->
                  if
                    (FStar_List_Tot_Base.length members) < (Prims.of_int (2))
                  then acc
                  else
                    (let xs =
                       RDF_Indexed.find_subjects_indexed ig
                         RDFS_Closure.rdf_type
                         (RDF_Graph.subject_to_term t.RDF_Triple.s) in
                     FStar_List_Tot_Base.fold_left
                       (fun acc1 x ->
                          let remaining =
                            FStar_List_Tot_Base.filter
                              (fun ci ->
                                 Prims.op_Negation (known_not_member ig x ci))
                              members in
                          match remaining with
                          | ck::[] ->
                              RDF_Graph.add_triple_unchecked acc1
                                {
                                  RDF_Triple.s = x;
                                  RDF_Triple.p = RDFS_Closure.rdf_type;
                                  RDF_Triple.o = (RDF_Term.T_IRI ck)
                                }
                          | uu___1 -> acc1) acc xs))
       else acc) g g
let iri_list_subset (a : RDF_Term.wf_iri Prims.list)
  (b : RDF_Term.wf_iri Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all (fun i -> FStar_List_Tot_Base.mem i b) a
let iri_list_set_eq (a : RDF_Term.wf_iri Prims.list)
  (b : RDF_Term.wf_iri Prims.list) : Prims.bool=
  (iri_list_subset a b) && (iri_list_subset b a)
let collect_oneof_axioms (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_oneOf_iri
       then
         match ((t.RDF_Triple.s), (RDF_Graph.term_to_subject t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI c_iri, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_iri_list g ig list_subj fuel with
              | FStar_Pervasives_Native.Some members -> (c_iri, members) ::
                  acc
              | FStar_Pervasives_Native.None -> acc)
         | (uu___, uu___1) -> acc
       else acc) [] g
let owl_rule_oneof_set_equivalence (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let axioms = collect_oneof_axioms g ig in
  FStar_List_Tot_Base.fold_left
    (fun acc a1 ->
       let uu___ = a1 in
       match uu___ with
       | (c1, m1) ->
           (match m1 with
            | [] -> acc
            | uu___1 ->
                FStar_List_Tot_Base.fold_left
                  (fun acc2 a2 ->
                     let uu___2 = a2 in
                     match uu___2 with
                     | (c2, m2) ->
                         if c1 = c2
                         then acc2
                         else
                           if iri_list_set_eq m1 m2
                           then
                             RDF_Graph.add_triple_unchecked acc2
                               {
                                 RDF_Triple.s = (RDF_Term.S_IRI c1);
                                 RDF_Triple.p = owl_equivalentClass;
                                 RDF_Triple.o = (RDF_Term.T_IRI c2)
                               }
                           else acc2) acc axioms)) g axioms
let members_of_class (g : RDF_Graph.rdf_graph) (cls : RDF_Term.wf_iri) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o (RDF_Term.T_IRI cls))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI x_iri ->
             (if FStar_List_Tot_Base.mem x_iri acc then acc else x_iri :: acc)
         | uu___ -> acc
       else acc) [] g
let agree_on_property (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (x : RDF_Term.wf_iri)
  (y : RDF_Term.wf_iri) (p : RDF_Term.wf_iri) : Prims.bool=
  let xs_objs = RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI x) p in
  let ys_objs = RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI y) p in
  FStar_List_Tot_Base.existsb
    (fun xv ->
       FStar_List_Tot_Base.existsb (fun yv -> RDF_Term.rdf_term_eq xv yv)
         ys_objs) xs_objs
let rec all_keys_match (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (x : RDF_Term.wf_iri)
  (y : RDF_Term.wf_iri) (props : RDF_Term.wf_iri Prims.list) : Prims.bool=
  match props with
  | [] -> true
  | p::rest ->
      if agree_on_property g ig x y p
      then all_keys_match g ig x y rest
      else false
let owl_prp_key_y_step (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (props : RDF_Term.wf_iri Prims.list)
  (x : RDF_Term.wf_iri) (acc2 : RDF_Graph.rdf_graph) (y : RDF_Term.wf_iri) :
  RDF_Graph.rdf_graph=
  if (x <> y) && (all_keys_match g ig x y props)
  then
    RDF_Graph.add_triple_unchecked acc2
      {
        RDF_Triple.s = (RDF_Term.S_IRI x);
        RDF_Triple.p = owl_sameAs;
        RDF_Triple.o = (RDF_Term.T_IRI y)
      }
  else acc2
let owl_prp_key_x_step (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (props : RDF_Term.wf_iri Prims.list)
  (members : RDF_Term.wf_iri Prims.list) (acc1 : RDF_Graph.rdf_graph)
  (x : RDF_Term.wf_iri) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (owl_prp_key_y_step g ig props x) acc1
    members
let owl_prp_key_axiom_step (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (acc : RDF_Graph.rdf_graph)
  (axiom : (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list)) :
  RDF_Graph.rdf_graph=
  let uu___ = axiom in
  match uu___ with
  | (c_iri, props) ->
      (match props with
       | [] -> acc
       | uu___1 ->
           let members = members_of_class g c_iri in
           FStar_List_Tot_Base.fold_left
             (owl_prp_key_x_step g ig props members) acc members)
let owl_rule_prp_key (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let axioms = collect_haskey_axioms g ig in
  FStar_List_Tot_Base.fold_left (owl_prp_key_axiom_step g ig) g axioms
let xsd_long : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#long"
let xsd_int : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#int"
let xsd_short : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#short"
let xsd_byte : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#byte"
let xsd_positiveInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#positiveInteger"
let xsd_unsignedLong : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedLong"
let xsd_unsignedInt : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedInt"
let xsd_unsignedShort : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedShort"
let xsd_unsignedByte : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#unsignedByte"
let xsd_nonPositiveInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#nonPositiveInteger"
let xsd_negativeInteger : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#negativeInteger"
let xsd_ns_prefix : Prims.string= "http://www.w3.org/2001/XMLSchema#"
let iri_in_xsd_ns (i : RDF_Term.wf_iri) : Prims.bool=
  let plen = FStar_String.strlen xsd_ns_prefix in
  let ilen = FStar_String.strlen i in
  if ilen < plen
  then false
  else (FStar_String.sub i Prims.int_zero plen) = xsd_ns_prefix
let term_in_xsd_ns (t : RDF_Term.rdf_term) : Prims.bool=
  match t with | RDF_Term.T_IRI i -> iri_in_xsd_ns i | uu___ -> false
let subject_in_xsd_ns (s : RDF_Term.subject) : Prims.bool=
  match s with | RDF_Term.S_IRI i -> iri_in_xsd_ns i | uu___ -> false
let triple_mentions_xsd (t : RDF_Triple.triple) : Prims.bool=
  ((subject_in_xsd_ns t.RDF_Triple.s) || (iri_in_xsd_ns t.RDF_Triple.p)) ||
    (term_in_xsd_ns t.RDF_Triple.o)
let graph_mentions_xsd_iri (g : RDF_Graph.rdf_graph) : Prims.bool=
  FStar_List_Tot_Base.existsb triple_mentions_xsd g
let xsd_hierarchy_edges : (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  [(xsd_byte, xsd_short);
  (xsd_short, xsd_int);
  (xsd_int, xsd_long);
  (xsd_long, RDF_Term.xsd_integer);
  (xsd_positiveInteger, xsd_nonNegativeInteger);
  (xsd_unsignedByte, xsd_unsignedShort);
  (xsd_unsignedShort, xsd_unsignedInt);
  (xsd_unsignedInt, xsd_unsignedLong);
  (xsd_unsignedLong, xsd_nonNegativeInteger);
  (xsd_nonNegativeInteger, RDF_Term.xsd_integer);
  (xsd_negativeInteger, xsd_nonPositiveInteger);
  (xsd_nonPositiveInteger, RDF_Term.xsd_integer);
  (RDF_Term.xsd_integer, RDF_Term.xsd_decimal);
  (RDF_Term.xsd_decimal, RDF_Term.xsd_double)]
let xsd_all_datatypes : RDF_Term.wf_iri Prims.list=
  [RDF_Term.xsd_string;
  RDF_Term.xsd_boolean;
  RDF_Term.xsd_double;
  RDF_Term.xsd_decimal;
  RDF_Term.xsd_integer;
  xsd_long;
  xsd_int;
  xsd_short;
  xsd_byte;
  xsd_nonNegativeInteger;
  xsd_positiveInteger;
  xsd_unsignedLong;
  xsd_unsignedInt;
  xsd_unsignedShort;
  xsd_unsignedByte;
  xsd_nonPositiveInteger;
  xsd_negativeInteger]
let owl_rule_xsd_datatype_axioms (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  if Prims.op_Negation (graph_mentions_xsd_iri g)
  then g
  else
    (let sub_triples =
       FStar_List_Tot_Base.map
         (fun pair ->
            let uu___1 = pair in
            match uu___1 with
            | (sub_i, sup_i) ->
                {
                  RDF_Triple.s = (RDF_Term.S_IRI sub_i);
                  RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                  RDF_Triple.o = (RDF_Term.T_IRI sup_i)
                }) xsd_hierarchy_edges in
     let dt_triples =
       FStar_List_Tot_Base.map
         (fun i ->
            {
              RDF_Triple.s = (RDF_Term.S_IRI i);
              RDF_Triple.p = RDFS_Closure.rdf_type;
              RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdfs_Datatype)
            }) xsd_all_datatypes in
     RDF_Graph.add_triples_if_new
       (RDF_Graph.add_triples_if_new g sub_triples) dt_triples)
let xsd_range_intersections :
  (RDF_Term.wf_iri * RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list=
  [(xsd_short, xsd_unsignedInt, [xsd_unsignedShort]);
  (xsd_short, xsd_unsignedLong, [xsd_unsignedShort]);
  (xsd_byte, xsd_unsignedInt, [xsd_unsignedByte]);
  (xsd_nonNegativeInteger, xsd_nonPositiveInteger,
    [xsd_byte; xsd_unsignedByte])]
let owl_rule_dt_range_intersect (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_range
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI d1 ->
             let others =
               RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
                 RDFS_Closure.rdfs_range in
             FStar_List_Tot_Base.fold_left
               (fun acc1 d2_term ->
                  match d2_term with
                  | RDF_Term.T_IRI d2 ->
                      FStar_List_Tot_Base.fold_left
                        (fun acc2 entry ->
                           let uu___ = entry in
                           match uu___ with
                           | (e1, e2, outs) ->
                               if
                                 ((e1 = d1) && (e2 = d2)) ||
                                   ((e1 = d2) && (e2 = d1))
                               then
                                 FStar_List_Tot_Base.fold_left
                                   (fun acc3 d3 ->
                                      RDF_Graph.add_triple_unchecked acc3
                                        {
                                          RDF_Triple.s = (t.RDF_Triple.s);
                                          RDF_Triple.p =
                                            RDFS_Closure.rdfs_range;
                                          RDF_Triple.o = (RDF_Term.T_IRI d3)
                                        }) acc2 outs
                               else acc2) acc1 xsd_range_intersections
                  | uu___ -> acc1) acc others
         | uu___ -> acc
       else acc) g g
let owl_rule_scm_dom2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_domain
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI c1_iri ->
             let supers =
               RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI c1_iri)
                 RDFS_Closure.rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c2_term ->
                  match c2_term with
                  | RDF_Term.T_IRI uu___ ->
                      let new_t =
                        {
                          RDF_Triple.s = (t.RDF_Triple.s);
                          RDF_Triple.p = RDFS_Closure.rdfs_domain;
                          RDF_Triple.o = c2_term
                        } in
                      RDF_Graph.add_triple_unchecked acc2 new_t
                  | uu___ -> acc2) acc supers
         | uu___ -> acc
       else acc) g g
let owl_rule_scm_rng2 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_range
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI c1_iri ->
             let supers =
               RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI c1_iri)
                 RDFS_Closure.rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c2_term ->
                  match c2_term with
                  | RDF_Term.T_IRI uu___ ->
                      let new_t =
                        {
                          RDF_Triple.s = (t.RDF_Triple.s);
                          RDF_Triple.p = RDFS_Closure.rdfs_range;
                          RDF_Triple.o = c2_term
                        } in
                      RDF_Graph.add_triple_unchecked acc2 new_t
                  | uu___ -> acc2) acc supers
         | uu___ -> acc
       else acc) g g
let owl_rule_subprop_domain_range (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some p2 ->
             let doms =
               RDF_Indexed.find_objects_indexed ig p2
                 RDFS_Closure.rdfs_domain in
             let rngs =
               RDF_Indexed.find_objects_indexed ig p2 RDFS_Closure.rdfs_range in
             let acc_d =
               FStar_List_Tot_Base.fold_left
                 (fun acc1 c ->
                    match c with
                    | RDF_Term.T_IRI uu___ ->
                        RDF_Graph.add_triple_unchecked acc1
                          {
                            RDF_Triple.s = (t.RDF_Triple.s);
                            RDF_Triple.p = RDFS_Closure.rdfs_domain;
                            RDF_Triple.o = c
                          }
                    | uu___ -> acc1) acc doms in
             FStar_List_Tot_Base.fold_left
               (fun acc1 c ->
                  match c with
                  | RDF_Term.T_IRI uu___ ->
                      RDF_Graph.add_triple_unchecked acc1
                        {
                          RDF_Triple.s = (t.RDF_Triple.s);
                          RDF_Triple.p = RDFS_Closure.rdfs_range;
                          RDF_Triple.o = c
                        }
                  | uu___ -> acc1) acc_d rngs
       else acc) g g
let owl_symmetric_metapredicates : RDF_Term.wf_iri Prims.list=
  [owl_complementOf_iri;
  owl_disjointWith_iri;
  owl_propertyDisjointWith;
  owl_inverseOf;
  owl_equivalentClass;
  owl_equivalentProperty]
let is_owl_symmetric_metapredicate (p : RDF_Term.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.mem p owl_symmetric_metapredicates
let owl_rule_symmetric_metapredicates (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if is_owl_symmetric_metapredicate t.RDF_Triple.p
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI a, RDF_Term.T_IRI b) ->
             (if a = b
              then acc
              else
                RDF_Graph.add_triple_unchecked acc
                  {
                    RDF_Triple.s = (RDF_Term.S_IRI b);
                    RDF_Triple.p = (t.RDF_Triple.p);
                    RDF_Triple.o = (RDF_Term.T_IRI a)
                  })
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_inverse_characteristic_transfer :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  [(owl_FunctionalProperty, owl_InverseFunctionalProperty);
  (owl_InverseFunctionalProperty, owl_FunctionalProperty);
  (owl_SymmetricProperty, owl_SymmetricProperty);
  (owl_TransitiveProperty, owl_TransitiveProperty);
  (owl_ReflexiveProperty, owl_ReflexiveProperty);
  (owl_IrreflexiveProperty, owl_IrreflexiveProperty);
  (owl_AsymmetricProperty, owl_AsymmetricProperty)]
let transfer_property_characteristics (ig : RDF_Indexed.indexed_graph)
  (table : (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list)
  (from_p : RDF_Term.wf_iri) (to_p : RDF_Term.wf_iri)
  (acc : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let from_types =
    RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI from_p)
      RDFS_Closure.rdf_type in
  FStar_List_Tot_Base.fold_left
    (fun a entry ->
       let src = FStar_Pervasives_Native.fst entry in
       let dst = FStar_Pervasives_Native.snd entry in
       if
         FStar_List_Tot_Base.existsb
           (fun ty -> RDF_Term.rdf_term_eq ty (RDF_Term.T_IRI src))
           from_types
       then
         RDF_Graph.add_triple_unchecked a
           {
             RDF_Triple.s = (RDF_Term.S_IRI to_p);
             RDF_Triple.p = RDFS_Closure.rdf_type;
             RDF_Triple.o = (RDF_Term.T_IRI dst)
           }
       else a) acc table
let owl_rule_inverse_characteristics (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_inverseOf
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) ->
             (if p1 = p2
              then acc
              else
                (let acc1 =
                   transfer_property_characteristics ig
                     owl_inverse_characteristic_transfer p1 p2 acc in
                 transfer_property_characteristics ig
                   owl_inverse_characteristic_transfer p2 p1 acc1))
         | (uu___, uu___1) -> acc
       else acc) g g
let owl_equivalent_characteristic_transfer :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  [(owl_FunctionalProperty, owl_FunctionalProperty);
  (owl_InverseFunctionalProperty, owl_InverseFunctionalProperty);
  (owl_SymmetricProperty, owl_SymmetricProperty);
  (owl_TransitiveProperty, owl_TransitiveProperty);
  (owl_ReflexiveProperty, owl_ReflexiveProperty);
  (owl_IrreflexiveProperty, owl_IrreflexiveProperty);
  (owl_AsymmetricProperty, owl_AsymmetricProperty)]
let owl_rule_equivalent_property_characteristics (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_equivalentProperty
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p1, RDF_Term.T_IRI p2) ->
             (if p1 = p2
              then acc
              else
                (let acc1 =
                   transfer_property_characteristics ig
                     owl_equivalent_characteristic_transfer p1 p2 acc in
                 transfer_property_characteristics ig
                   owl_equivalent_characteristic_transfer p2 p1 acc1))
         | (uu___, uu___1) -> acc
       else acc) g g
let canonical_min_card_bnode (p : RDF_Term.wf_iri) (n : Prims.string) :
  RDF_Term.bnode_id= FStar_String.concat "" ["__rl_mincard__"; p; "__n__"; n]
let canonical_max_card_bnode (p : RDF_Term.wf_iri) (n : Prims.string) :
  RDF_Term.bnode_id= FStar_String.concat "" ["__rl_maxcard__"; p; "__n__"; n]
let canonical_min_qcard_bnode (p : RDF_Term.wf_iri) (c : RDF_Term.wf_iri)
  (n : Prims.string) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_minqcard__"; p; "__on__"; c; "__n__"; n]
let canonical_max_qcard_bnode (p : RDF_Term.wf_iri) (c : RDF_Term.wf_iri)
  (n : Prims.string) : RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_maxqcard__"; p; "__on__"; c; "__n__"; n]
let restriction_node_is_asserted (r : RDF_Term.subject) : Prims.bool=
  match r with
  | RDF_Term.S_IRI uu___ -> true
  | RDF_Term.S_BNode b -> Prims.op_Negation (bnode_is_rl_canonical b)
let emit_bound_restriction (r : RDF_Term.subject) (b : RDF_Term.bnode_id)
  (p : RDF_Term.wf_iri) (bound_pred : RDF_Term.wf_iri)
  (card_lit : RDF_Term.wf_literal)
  (on_class : RDF_Term.wf_iri FStar_Pervasives_Native.option)
  (acc : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let b_subj = RDF_Term.S_BNode b in
  let base =
    [{
       RDF_Triple.s = b_subj;
       RDF_Triple.p = RDFS_Closure.rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI owl_Restriction_iri)
     };
    {
      RDF_Triple.s = b_subj;
      RDF_Triple.p = owl_onProperty_iri;
      RDF_Triple.o = (RDF_Term.T_IRI p)
    };
    {
      RDF_Triple.s = b_subj;
      RDF_Triple.p = bound_pred;
      RDF_Triple.o = (RDF_Term.T_Literal card_lit)
    };
    {
      RDF_Triple.s = r;
      RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
      RDF_Triple.o = (RDF_Term.T_BNode b)
    }] in
  let all_t =
    match on_class with
    | FStar_Pervasives_Native.None -> base
    | FStar_Pervasives_Native.Some c ->
        {
          RDF_Triple.s = b_subj;
          RDF_Triple.p = owl_onClass_iri;
          RDF_Triple.o = (RDF_Term.T_IRI c)
        } :: base in
  FStar_List_Tot_Base.fold_left RDF_Graph.add_triple_unchecked acc all_t
let owl_rule_cardinality_to_min_max (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if Prims.op_Negation (restriction_node_is_asserted t.RDF_Triple.s)
       then acc
       else
         if t.RDF_Triple.p = owl_cardinality_iri
         then
           (match t.RDF_Triple.o with
            | RDF_Term.T_Literal lit ->
                let props =
                  RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
                    owl_onProperty_iri in
                FStar_List_Tot_Base.fold_left
                  (fun a pt ->
                     match pt with
                     | RDF_Term.T_IRI p ->
                         let n = lit.RDF_Term.lexical_form in
                         let a1 =
                           emit_bound_restriction t.RDF_Triple.s
                             (canonical_min_card_bnode p n) p
                             owl_minCardinality_iri lit
                             FStar_Pervasives_Native.None a in
                         emit_bound_restriction t.RDF_Triple.s
                           (canonical_max_card_bnode p n) p
                           owl_maxCardinality_iri lit
                           FStar_Pervasives_Native.None a1
                     | uu___1 -> a) acc props
            | uu___1 -> acc)
         else
           if t.RDF_Triple.p = owl_qualifiedCardinality_iri
           then
             (match t.RDF_Triple.o with
              | RDF_Term.T_Literal lit ->
                  let props =
                    RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
                      owl_onProperty_iri in
                  let classes =
                    RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
                      owl_onClass_iri in
                  FStar_List_Tot_Base.fold_left
                    (fun a pt ->
                       match pt with
                       | RDF_Term.T_IRI p ->
                           FStar_List_Tot_Base.fold_left
                             (fun a1 ct ->
                                match ct with
                                | RDF_Term.T_IRI c ->
                                    let n = lit.RDF_Term.lexical_form in
                                    let a2 =
                                      emit_bound_restriction t.RDF_Triple.s
                                        (canonical_min_qcard_bnode p c n) p
                                        owl_minQualifiedCardinality_iri lit
                                        (FStar_Pervasives_Native.Some c) a1 in
                                    emit_bound_restriction t.RDF_Triple.s
                                      (canonical_max_qcard_bnode p c n) p
                                      owl_maxQualifiedCardinality_iri lit
                                      (FStar_Pervasives_Native.Some c) a2
                                | uu___2 -> a1) a classes
                       | uu___2 -> a) acc props
              | uu___2 -> acc)
           else acc) g g
let owl_rule_cls_maxqc34 (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         ((t.RDF_Triple.p = owl_maxQualifiedCardinality_iri) &&
            (RDF_Term.rdf_term_eq t.RDF_Triple.o
               (RDF_Term.T_Literal one_nonNegInteger_literal)))
           && (restriction_node_is_asserted t.RDF_Triple.s)
       then
         let r_subj = t.RDF_Triple.s in
         let props =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
         let classes =
           RDF_Indexed.find_objects_indexed ig r_subj owl_onClass_iri in
         FStar_List_Tot_Base.fold_left
           (fun acc2 p_term ->
              match p_term with
              | RDF_Term.T_IRI p ->
                  FStar_List_Tot_Base.fold_left
                    (fun acc3 c_term ->
                       match c_term with
                       | RDF_Term.T_IRI c ->
                           let unqualified = c = RDFS_Closure.owl_Thing in
                           let members =
                             RDF_Indexed.find_subjects_indexed ig
                               RDFS_Closure.rdf_type
                               (RDF_Graph.subject_to_term r_subj) in
                           FStar_List_Tot_Base.fold_left
                             (fun acc4 u ->
                                let ys =
                                  RDF_Indexed.find_objects_indexed ig u p in
                                let ws =
                                  if unqualified
                                  then ys
                                  else
                                    FStar_List_Tot_Base.filter
                                      (fun y -> object_has_type ig y c) ys in
                                FStar_List_Tot_Base.fold_left
                                  (fun acc5 y1 ->
                                     FStar_List_Tot_Base.fold_left
                                       (fun acc6 y2 ->
                                          if RDF_Term.rdf_term_eq y1 y2
                                          then acc6
                                          else
                                            (match RDF_Graph.term_to_subject
                                                     y1
                                             with
                                             | FStar_Pervasives_Native.None
                                                 -> acc6
                                             | FStar_Pervasives_Native.Some
                                                 y1_subj ->
                                                 RDF_Graph.add_triple_unchecked
                                                   acc6
                                                   {
                                                     RDF_Triple.s = y1_subj;
                                                     RDF_Triple.p =
                                                       owl_sameAs;
                                                     RDF_Triple.o = y2
                                                   })) acc5 ws) acc4 ws) acc3
                             members
                       | uu___ -> acc3) acc2 classes
              | uu___ -> acc2) acc props
       else acc) g g
let hasvalue_restriction_candidates (ig : RDF_Indexed.indexed_graph)
  (d : RDF_Term.subject) : RDF_Term.subject Prims.list=
  let sups =
    RDF_Indexed.find_objects_indexed ig d RDFS_Closure.rdfs_subClassOf in
  FStar_List_Tot_Base.fold_left
    (fun acc s ->
       match RDF_Graph.term_to_subject s with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some x ->
           if
             Prims.uu___is_Cons
               (RDF_Indexed.find_objects_indexed ig x owl_hasValue_iri)
           then x :: acc
           else acc)
    (if
       Prims.uu___is_Cons
         (RDF_Indexed.find_objects_indexed ig d owl_hasValue_iri)
     then [d]
     else []) sups
let restriction_pins (ig : RDF_Indexed.indexed_graph) (r : RDF_Term.subject)
  (q : RDF_Term.wf_iri) (v : RDF_Term.rdf_term) : Prims.bool=
  (FStar_List_Tot_Base.existsb
     (fun pt -> RDF_Term.rdf_term_eq pt (RDF_Term.T_IRI q))
     (RDF_Indexed.find_objects_indexed ig r owl_onProperty_iri))
    &&
    (FStar_List_Tot_Base.existsb (fun vt -> RDF_Term.rdf_term_eq vt v)
       (RDF_Indexed.find_objects_indexed ig r owl_hasValue_iri))
let owl_rule_fp_pinned_subproperty (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_FunctionalProperty))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI p ->
             let doms =
               RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
                 RDFS_Closure.rdfs_domain in
             FStar_List_Tot_Base.fold_left
               (fun a d_term ->
                  match RDF_Graph.term_to_subject d_term with
                  | FStar_Pervasives_Native.None -> a
                  | FStar_Pervasives_Native.Some d ->
                      let cands = hasvalue_restriction_candidates ig d in
                      FStar_List_Tot_Base.fold_left
                        (fun a1 r1 ->
                           let p_on =
                             FStar_List_Tot_Base.existsb
                               (fun pt ->
                                  RDF_Term.rdf_term_eq pt (RDF_Term.T_IRI p))
                               (RDF_Indexed.find_objects_indexed ig r1
                                  owl_onProperty_iri) in
                           if Prims.op_Negation p_on
                           then a1
                           else
                             FStar_List_Tot_Base.fold_left
                               (fun a2 v ->
                                  FStar_List_Tot_Base.fold_left
                                    (fun a3 r2 ->
                                       FStar_List_Tot_Base.fold_left
                                         (fun a4 qt ->
                                            match qt with
                                            | RDF_Term.T_IRI q ->
                                                if q = p
                                                then a4
                                                else
                                                  if
                                                    restriction_pins ig r2 q
                                                      v
                                                  then
                                                    RDF_Graph.add_triple_unchecked
                                                      a4
                                                      {
                                                        RDF_Triple.s =
                                                          (RDF_Term.S_IRI p);
                                                        RDF_Triple.p =
                                                          RDFS_Closure.rdfs_subPropertyOf;
                                                        RDF_Triple.o =
                                                          (RDF_Term.T_IRI q)
                                                      }
                                                  else a4
                                            | uu___1 -> a4) a3
                                         (RDF_Indexed.find_objects_indexed ig
                                            r2 owl_onProperty_iri)) a2 cands)
                               a1
                               (RDF_Indexed.find_objects_indexed ig r1
                                  owl_hasValue_iri)) a cands) acc doms
         | uu___ -> acc
       else acc) g g
let subject_is_rdf_nil (s : RDF_Term.subject) : Prims.bool=
  match s with
  | RDF_Term.S_IRI i -> i = rdf_nil_iri
  | RDF_Term.S_BNode uu___ -> false
let rec rdf_list_length_fuel (ig : RDF_Indexed.indexed_graph)
  (head : RDF_Term.subject) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if subject_is_rdf_nil head
  then FStar_Pervasives_Native.Some Prims.int_zero
  else
    (match fuel with
     | uu___1 when uu___1 = Prims.int_zero -> FStar_Pervasives_Native.None
     | uu___1 ->
         let firsts = RDF_Indexed.find_objects_indexed ig head rdf_first in
         let rests = RDF_Indexed.find_objects_indexed ig head rdf_rest in
         if Prims.uu___is_Nil firsts
         then FStar_Pervasives_Native.None
         else
           (match rests with
            | r::[] ->
                (match RDF_Graph.term_to_subject r with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some rs ->
                     (match rdf_list_length_fuel ig rs (fuel - Prims.int_one)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some n ->
                          FStar_Pervasives_Native.Some (n + Prims.int_one)))
            | uu___3 -> FStar_Pervasives_Native.None))
let owl_rule_singleton_nominal_functionality (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_oneOf_iri
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some list_subj ->
             (match rdf_list_length_fuel ig list_subj fuel with
              | FStar_Pervasives_Native.Some uu___ when uu___ = Prims.int_one
                  ->
                  let c_term = RDF_Graph.subject_to_term t.RDF_Triple.s in
                  let ranged =
                    RDF_Indexed.find_subjects_indexed ig
                      RDFS_Closure.rdfs_range c_term in
                  let domained =
                    RDF_Indexed.find_subjects_indexed ig
                      RDFS_Closure.rdfs_domain c_term in
                  let acc1 =
                    FStar_List_Tot_Base.fold_left
                      (fun a p ->
                         RDF_Graph.add_triple_unchecked a
                           {
                             RDF_Triple.s = p;
                             RDF_Triple.p = RDFS_Closure.rdf_type;
                             RDF_Triple.o =
                               (RDF_Term.T_IRI owl_FunctionalProperty)
                           }) acc ranged in
                  FStar_List_Tot_Base.fold_left
                    (fun a p ->
                       RDF_Graph.add_triple_unchecked a
                         {
                           RDF_Triple.s = p;
                           RDF_Triple.p = RDFS_Closure.rdf_type;
                           RDF_Triple.o =
                             (RDF_Term.T_IRI owl_InverseFunctionalProperty)
                         }) acc1 domained
              | uu___ -> acc)
       else acc) g g
let literal_values_provably_distinct (l1 : RDF_Term.wf_literal)
  (l2 : RDF_Term.wf_literal) : Prims.bool=
  ((((l1.RDF_Term.datatype = RDF_Term.xsd_string) &&
       (l2.RDF_Term.datatype = RDF_Term.xsd_string))
      && (FStar_Pervasives_Native.uu___is_None l1.RDF_Term.lang_tag))
     && (FStar_Pervasives_Native.uu___is_None l2.RDF_Term.lang_tag))
    && (l1.RDF_Term.lexical_form <> l2.RDF_Term.lexical_form)
let terms_provably_distinct (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  match (a, b) with
  | (RDF_Term.T_Literal l1, RDF_Term.T_Literal l2) ->
      literal_values_provably_distinct l1 l2
  | (uu___, uu___1) -> false
let cardinality_literal_is_one (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l -> l.RDF_Term.lexical_form = "1"
  | uu___ -> false
let class_pins_at_most_one (ig : RDF_Indexed.indexed_graph)
  (c : RDF_Term.subject) (p : RDF_Term.wf_iri) : Prims.bool=
  (FStar_List_Tot_Base.existsb
     (fun ty ->
        RDF_Term.rdf_term_eq ty (RDF_Term.T_IRI owl_FunctionalProperty))
     (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
        RDFS_Closure.rdf_type))
    ||
    (FStar_List_Tot_Base.existsb
       (fun s ->
          match RDF_Graph.term_to_subject s with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some m ->
              (FStar_List_Tot_Base.existsb
                 (fun pt -> RDF_Term.rdf_term_eq pt (RDF_Term.T_IRI p))
                 (RDF_Indexed.find_objects_indexed ig m owl_onProperty_iri))
                &&
                ((FStar_List_Tot_Base.existsb cardinality_literal_is_one
                    (RDF_Indexed.find_objects_indexed ig m
                       owl_maxCardinality_iri))
                   ||
                   (FStar_List_Tot_Base.existsb cardinality_literal_is_one
                      (RDF_Indexed.find_objects_indexed ig m
                         owl_cardinality_iri))))
       (RDF_Indexed.find_objects_indexed ig c RDFS_Closure.rdfs_subClassOf))
let collect_hasvalue_pins (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) :
  (RDF_Term.subject * RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI uu___ ->
             (match RDF_Graph.term_to_subject t.RDF_Triple.o with
              | FStar_Pervasives_Native.None -> acc
              | FStar_Pervasives_Native.Some r ->
                  let vs =
                    RDF_Indexed.find_objects_indexed ig r owl_hasValue_iri in
                  if Prims.uu___is_Nil vs
                  then acc
                  else
                    FStar_List_Tot_Base.fold_left
                      (fun a1 pt ->
                         match pt with
                         | RDF_Term.T_IRI p ->
                             FStar_List_Tot_Base.fold_left
                               (fun a2 v -> ((t.RDF_Triple.s), p, v) :: a2)
                               a1 vs
                         | uu___2 -> a1) acc
                      (RDF_Indexed.find_objects_indexed ig r
                         owl_onProperty_iri))
         | uu___ -> acc
       else acc) [] g
let owl_rule_hasvalue_card_disjoint (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let pins = collect_hasvalue_pins g ig in
  FStar_List_Tot_Base.fold_left
    (fun acc e1 ->
       let uu___ = e1 in
       match uu___ with
       | (c1, p1, v1) ->
           if Prims.op_Negation (class_pins_at_most_one ig c1 p1)
           then acc
           else
             FStar_List_Tot_Base.fold_left
               (fun a e2 ->
                  let uu___2 = e2 in
                  match uu___2 with
                  | (c2, p2, v2) ->
                      if
                        ((p1 = p2) &&
                           (Prims.op_Negation (RDF_Term.subject_eq c1 c2)))
                          && (terms_provably_distinct v1 v2)
                      then
                        RDF_Graph.add_triple_unchecked a
                          {
                            RDF_Triple.s = c1;
                            RDF_Triple.p = owl_disjointWith_iri;
                            RDF_Triple.o = (RDF_Graph.subject_to_term c2)
                          }
                      else a) acc pins) g pins
let owl_rule_avf_thing_to_range (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let subj_is_thing =
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI i -> i = RDFS_Closure.owl_Thing
         | RDF_Term.S_BNode uu___ -> false in
       if (t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf) && subj_is_thing
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some r_subj ->
             let props =
               RDF_Indexed.find_objects_indexed ig r_subj owl_onProperty_iri in
             let fillers =
               RDF_Indexed.find_objects_indexed ig r_subj
                 owl_allValuesFrom_iri in
             FStar_List_Tot_Base.fold_left
               (fun acc2 p_term ->
                  match p_term with
                  | RDF_Term.T_IRI p ->
                      FStar_List_Tot_Base.fold_left
                        (fun acc3 c_term ->
                           match c_term with
                           | RDF_Term.T_IRI uu___ ->
                               RDF_Graph.add_triple_unchecked acc3
                                 {
                                   RDF_Triple.s = (RDF_Term.S_IRI p);
                                   RDF_Triple.p = RDFS_Closure.rdfs_range;
                                   RDF_Triple.o = c_term
                                 }
                           | uu___ -> acc3) acc2 fillers
                  | uu___ -> acc2) acc props
       else acc) g g
let rec collect_pinned_edges (ts : RDF_Triple.triple Prims.list)
  (p : RDF_Term.wf_iri) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list
    FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.Some []
  | t::rest ->
      if t.RDF_Triple.p = p
      then
        (match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI s_iri, RDF_Term.T_IRI o_iri) ->
             (match collect_pinned_edges rest p with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some es ->
                  FStar_Pervasives_Native.Some ((s_iri, o_iri) :: es))
         | (uu___, uu___1) -> FStar_Pervasives_Native.None)
      else collect_pinned_edges rest p
let edge_set_is_symmetric
  (es : (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun e ->
       let uu___ = e in
       match uu___ with
       | (x, y) ->
           FStar_List_Tot_Base.existsb
             (fun f ->
                let uu___1 = f in
                match uu___1 with | (u, v) -> (u = y) && (v = x)) es) es
let edges_cover_members (es : (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list)
  (ms : RDF_Term.wf_iri Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun m ->
       FStar_List_Tot_Base.existsb
         (fun e -> let uu___ = e in match uu___ with | (uu___1, y) -> y = m)
         es) ms
let oneof_range_member_lists (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (p : RDF_Term.wf_iri) :
  RDF_Term.wf_iri Prims.list Prims.list=
  let fuel = FStar_List_Tot_Base.length g in
  FStar_List_Tot_Base.fold_left
    (fun acc r ->
       match RDF_Graph.term_to_subject r with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some r_subj ->
           FStar_List_Tot_Base.fold_left
             (fun acc2 o ->
                match RDF_Graph.term_to_subject o with
                | FStar_Pervasives_Native.None -> acc2
                | FStar_Pervasives_Native.Some l_subj ->
                    (match decode_iri_list g ig l_subj fuel with
                     | FStar_Pervasives_Native.None -> acc2
                     | FStar_Pervasives_Native.Some ms -> ms :: acc2)) acc
             (RDF_Indexed.find_objects_indexed ig r_subj owl_oneOf_iri)) []
    (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
       RDFS_Closure.rdfs_range)
let pinned_property_extension (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (p : RDF_Term.wf_iri) :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list
    FStar_Pervasives_Native.option=
  let is_ifp =
    FStar_List_Tot_Base.existsb
      (fun t ->
         RDF_Term.rdf_term_eq t
           (RDF_Term.T_IRI owl_InverseFunctionalProperty))
      (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
         RDFS_Closure.rdf_type) in
  if Prims.op_Negation is_ifp
  then FStar_Pervasives_Native.None
  else
    (match collect_pinned_edges g p with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some es ->
         if
           FStar_List_Tot_Base.existsb
             (fun ms ->
                (Prims.uu___is_Cons ms) && (edges_cover_members es ms))
             (oneof_range_member_lists g ig p)
         then FStar_Pervasives_Native.Some es
         else FStar_Pervasives_Native.None)
let owl_rule_extensional_symmetry (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_InverseFunctionalProperty))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI p ->
             (match pinned_property_extension g ig p with
              | FStar_Pervasives_Native.None -> acc
              | FStar_Pervasives_Native.Some es ->
                  if edge_set_is_symmetric es
                  then
                    RDF_Graph.add_triple_unchecked acc
                      {
                        RDF_Triple.s = (RDF_Term.S_IRI p);
                        RDF_Triple.p = RDFS_Closure.rdf_type;
                        RDF_Triple.o = (RDF_Term.T_IRI owl_SymmetricProperty)
                      }
                  else acc)
         | uu___ -> acc
       else acc) g g
let owl_xsd_core_datatype_axioms : RDF_Triple.triple Prims.list=
  [{
     RDF_Triple.s = (RDF_Term.S_IRI RDF_Term.xsd_integer);
     RDF_Triple.p = RDFS_Closure.rdf_type;
     RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdfs_Datatype)
   };
  {
    RDF_Triple.s = (RDF_Term.S_IRI RDF_Term.xsd_string);
    RDF_Triple.p = RDFS_Closure.rdf_type;
    RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdfs_Datatype)
  }]
let owl_rule_xsd_core_datatype_axioms (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  RDF_Graph.add_triples_if_new g owl_xsd_core_datatype_axioms
let owl_AnnotationProperty_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AnnotationProperty"
let owl_Ontology_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#Ontology"
let owl_imports_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#imports"
let rdfs_label_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#label"
let rdfs_comment_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#comment"
let rdfs_seeAlso_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#seeAlso"
let rdfs_isDefinedBy_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2000/01/rdf-schema#isDefinedBy"
let owl_deprecated_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#deprecated"
let owl_versionInfo_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#versionInfo"
let owl_backwardCompatibleWith_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#backwardCompatibleWith"
let owl_incompatibleWith_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#incompatibleWith"
let owl_priorVersion_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#priorVersion"
let owl_builtin_annotation_properties : RDF_Term.wf_iri Prims.list=
  [rdfs_label_iri;
  rdfs_comment_iri;
  rdfs_seeAlso_iri;
  rdfs_isDefinedBy_iri;
  owl_deprecated_iri;
  owl_versionInfo_iri;
  owl_backwardCompatibleWith_iri;
  owl_incompatibleWith_iri;
  owl_priorVersion_iri]
let owl_builtin_vocabulary_axioms : RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.append
    (FStar_List_Tot_Base.map
       (fun i ->
          {
            RDF_Triple.s = (RDF_Term.S_IRI i);
            RDF_Triple.p = RDFS_Closure.rdf_type;
            RDF_Triple.o = (RDF_Term.T_IRI owl_AnnotationProperty_iri)
          }) owl_builtin_annotation_properties)
    [{
       RDF_Triple.s = (RDF_Term.S_IRI owl_imports_iri);
       RDF_Triple.p = RDFS_Closure.rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.rdf_Property)
     };
    {
      RDF_Triple.s = (RDF_Term.S_IRI owl_imports_iri);
      RDF_Triple.p = RDFS_Closure.rdfs_domain;
      RDF_Triple.o = (RDF_Term.T_IRI owl_Ontology_iri)
    };
    {
      RDF_Triple.s = (RDF_Term.S_IRI owl_imports_iri);
      RDF_Triple.p = RDFS_Closure.rdfs_range;
      RDF_Triple.o = (RDF_Term.T_IRI owl_Ontology_iri)
    };
    {
      RDF_Triple.s = (RDF_Term.S_IRI rdf_first);
      RDF_Triple.p = RDFS_Closure.rdf_type;
      RDF_Triple.o = (RDF_Term.T_IRI owl_FunctionalProperty)
    };
    {
      RDF_Triple.s = (RDF_Term.S_IRI rdf_rest);
      RDF_Triple.p = RDFS_Closure.rdf_type;
      RDF_Triple.o = (RDF_Term.T_IRI owl_FunctionalProperty)
    }]
let owl_rule_builtin_vocabulary_axioms (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  RDF_Graph.add_triples_if_new g owl_builtin_vocabulary_axioms
let owl_AllDisjointClasses_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AllDisjointClasses"
let owl_members_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#members"
let owl_rule_all_disjoint_classes (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_AllDisjointClasses_iri))
       then
         FStar_List_Tot_Base.fold_left
           (fun acc1 l_term ->
              match RDF_Graph.term_to_subject l_term with
              | FStar_Pervasives_Native.None -> acc1
              | FStar_Pervasives_Native.Some l_subj ->
                  (match decode_chain_list g ig l_subj with
                   | FStar_Pervasives_Native.Some cs ->
                       FStar_List_Tot_Base.fold_left
                         (fun acc2 c1 ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc3 c2 ->
                                 if c1 = c2
                                 then acc3
                                 else
                                   RDF_Graph.add_triple_unchecked acc3
                                     {
                                       RDF_Triple.s = (RDF_Term.S_IRI c1);
                                       RDF_Triple.p = owl_disjointWith_iri;
                                       RDF_Triple.o = (RDF_Term.T_IRI c2)
                                     }) acc2 cs) acc1 cs
                   | FStar_Pervasives_Native.None -> acc1)) acc
           (RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
              owl_members_iri)
       else acc) g g
let owl_AllDisjointProperties_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AllDisjointProperties"
let owl_AllDifferent_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#AllDifferent"
let owl_rule_all_disjoint_properties (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_AllDisjointProperties_iri))
       then
         FStar_List_Tot_Base.fold_left
           (fun acc1 l_term ->
              match RDF_Graph.term_to_subject l_term with
              | FStar_Pervasives_Native.None -> acc1
              | FStar_Pervasives_Native.Some l_subj ->
                  (match decode_chain_list g ig l_subj with
                   | FStar_Pervasives_Native.Some ps ->
                       FStar_List_Tot_Base.fold_left
                         (fun acc2 p1 ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc3 p2 ->
                                 if p1 = p2
                                 then acc3
                                 else
                                   RDF_Graph.add_triple_unchecked acc3
                                     {
                                       RDF_Triple.s = (RDF_Term.S_IRI p1);
                                       RDF_Triple.p =
                                         owl_propertyDisjointWith;
                                       RDF_Triple.o = (RDF_Term.T_IRI p2)
                                     }) acc2 ps) acc1 ps
                   | FStar_Pervasives_Native.None -> acc1)) acc
           (RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
              owl_members_iri)
       else acc) g g
let differentFrom_canonical_pairs (ig : RDF_Indexed.indexed_graph) :
  (RDF_Term.subject * RDF_Term.subject) Prims.list=
  let raw =
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if t.RDF_Triple.p = owl_differentFrom
         then
           match RDF_Graph.term_to_subject t.RDF_Triple.o with
           | FStar_Pervasives_Native.Some y ->
               (if RDF_Term.subject_eq t.RDF_Triple.s y
                then acc
                else
                  if
                    (FStar_String.compare
                       (RDF_Indexed.subject_to_key t.RDF_Triple.s)
                       (RDF_Indexed.subject_to_key y))
                      < Prims.int_zero
                  then ((t.RDF_Triple.s), y) :: acc
                  else acc)
           | FStar_Pervasives_Native.None -> acc
         else acc) [] ig.RDF_Indexed.ig_triples in
  let sorted = FStar_List_Tot_Base.sortWith sameas_pair_cmp raw in
  dedup_pairs_sorted_aux FStar_Pervasives_Native.None sorted []
let canonical_adf_bnode (k1 : Prims.string) (k2 : Prims.string) :
  RDF_Term.bnode_id= FStar_String.concat "" ["__rl_adf__"; k1; "__vs__"; k2]
let canonical_adfl1_bnode (k1 : Prims.string) (k2 : Prims.string) :
  RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_adfl1__"; k1; "__vs__"; k2]
let canonical_adfl2_bnode (k1 : Prims.string) (k2 : Prims.string) :
  RDF_Term.bnode_id=
  FStar_String.concat "" ["__rl_adfl2__"; k1; "__vs__"; k2]
let owl_distinctMembers_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#distinctMembers"
let owl_rule_allDifferent_to_differentFrom (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI owl_AllDifferent_iri))
       then
         let lists =
           FStar_List_Tot_Base.append
             (RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
                owl_distinctMembers_iri)
             (RDF_Indexed.find_objects_indexed ig t.RDF_Triple.s
                owl_members_iri) in
         FStar_List_Tot_Base.fold_left
           (fun acc1 l_term ->
              match RDF_Graph.term_to_subject l_term with
              | FStar_Pervasives_Native.None -> acc1
              | FStar_Pervasives_Native.Some l_subj ->
                  (match decode_chain_list g ig l_subj with
                   | FStar_Pervasives_Native.None -> acc1
                   | FStar_Pervasives_Native.Some ms ->
                       FStar_List_Tot_Base.fold_left
                         (fun acc2 x ->
                            FStar_List_Tot_Base.fold_left
                              (fun acc3 y ->
                                 if x = y
                                 then acc3
                                 else
                                   RDF_Graph.add_triple_unchecked acc3
                                     {
                                       RDF_Triple.s = (RDF_Term.S_IRI x);
                                       RDF_Triple.p = owl_differentFrom;
                                       RDF_Triple.o = (RDF_Term.T_IRI y)
                                     }) acc2 ms) acc1 ms)) acc lists
       else acc) g g
let owl_rule_differentFrom_to_allDifferent (g : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc xy ->
       let uu___ = xy in
       match uu___ with
       | (x, y) ->
           let k1 = RDF_Indexed.subject_to_key x in
           let k2 = RDF_Indexed.subject_to_key y in
           let adf = RDF_Term.S_BNode (canonical_adf_bnode k1 k2) in
           let l1 = canonical_adfl1_bnode k1 k2 in
           let l2 = canonical_adfl2_bnode k1 k2 in
           RDF_Graph.add_triples_if_new acc
             [{
                RDF_Triple.s = adf;
                RDF_Triple.p = RDFS_Closure.rdf_type;
                RDF_Triple.o = (RDF_Term.T_IRI owl_AllDifferent_iri)
              };
             {
               RDF_Triple.s = adf;
               RDF_Triple.p = owl_members_iri;
               RDF_Triple.o = (RDF_Term.T_BNode l1)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l1);
               RDF_Triple.p = rdf_first;
               RDF_Triple.o = (RDF_Graph.subject_to_term x)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l1);
               RDF_Triple.p = rdf_rest;
               RDF_Triple.o = (RDF_Term.T_BNode l2)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l2);
               RDF_Triple.p = rdf_first;
               RDF_Triple.o = (RDF_Graph.subject_to_term y)
             };
             {
               RDF_Triple.s = (RDF_Term.S_BNode l2);
               RDF_Triple.p = rdf_rest;
               RDF_Triple.o = (RDF_Term.T_IRI rdf_nil_iri)
             }]) g (differentFrom_canonical_pairs ig)
let owl_DataRange_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#DataRange"
let rdf_based_full_meta_class_pairs :
  (RDF_Term.wf_iri * RDF_Term.wf_iri) Prims.list=
  [(RDFS_Closure.owl_Class, RDFS_Closure.rdfs_Class);
  (RDFS_Closure.owl_Thing, RDFS_Closure.rdfs_Resource);
  (owl_DataRange_iri, RDFS_Closure.rdfs_Datatype);
  (RDFS_Closure.owl_ObjectProperty, RDFS_Closure.rdf_Property)]
let owl_rule_rdf_based_full_meta_axioms_mode (g : RDF_Graph.rdf_graph)
  (mode : Prims.string) : RDF_Graph.rdf_graph=
  if mode <> owl_semantics_rdf_based_full
  then g
  else
    FStar_List_Tot_Base.fold_left
      (fun acc pr ->
         let uu___1 = pr in
         match uu___1 with
         | (a, b) ->
             RDF_Graph.add_triples_if_new acc
               [{
                  RDF_Triple.s = (RDF_Term.S_IRI a);
                  RDF_Triple.p = owl_equivalentClass;
                  RDF_Triple.o = (RDF_Term.T_IRI b)
                };
               {
                 RDF_Triple.s = (RDF_Term.S_IRI b);
                 RDF_Triple.p = owl_equivalentClass;
                 RDF_Triple.o = (RDF_Term.T_IRI a)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_IRI a);
                 RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                 RDF_Triple.o = (RDF_Term.T_IRI b)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_IRI b);
                 RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                 RDF_Triple.o = (RDF_Term.T_IRI a)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_IRI a);
                 RDF_Triple.p = RDFS_Closure.rdf_type;
                 RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
               };
               {
                 RDF_Triple.s = (RDF_Term.S_IRI b);
                 RDF_Triple.p = RDFS_Closure.rdf_type;
                 RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
               }]) g rdf_based_full_meta_class_pairs
let owl_rl_closure_step_mode (g : RDF_Graph.rdf_graph) (mode : Prims.string)
  : RDF_Graph.rdf_graph=
  let ig = RDF_Indexed.build_indexed g in
  let g1 = owl_rule_equivalent_class g ig in
  let g2 = owl_rule_equivalent_property g1 ig in
  let g2a = owl_rule_scm_eqc2 g2 ig in
  let g2b = owl_rule_scm_eqp2 g2a ig in
  let g3 = owl_rule_inverse_of g2b ig in
  let g3_adc = owl_rule_all_disjoint_classes g3 ig in
  let g3_disj = owl_rule_disjoint_with_propagation g3_adc ig in
  let g3_comp = owl_rule_disjoint_to_complement g3_disj ig in
  let g3a = owl_rule_inverseOf_domain_range_flip g3_comp ig in
  let g4 = owl_rule_symmetric_property g3a ig in
  let g5 = owl_rule_transitive_property g4 ig in
  let g5a = owl_rule_named_equivClass_to_sameAs_mode g5 ig mode in
  let g6 = owl_rule_sameAs_reflexivity g5a ig in
  let g7 = owl_rule_sameAs_symmetry g6 ig in
  let g7a = owl_rule_differentFrom_symmetry g7 ig in
  let g8 = owl_rule_sameAs_transitivity g7a ig in
  let g9 = owl_rule_sameAs_replace_subject g8 ig in
  let g10 = owl_rule_sameAs_replace_object g9 ig in
  let g11 = owl_rule_sameAs_replace_predicate g10 ig in
  let g11a = owl_rule_functional g11 ig in
  let g12 = owl_rule_inverse_functional g11a ig in
  let g12_adp = owl_rule_all_disjoint_properties g12 ig in
  let g12a = owl_rule_pdw_to_differentFrom g12_adp ig in
  let g12a1 = owl_rule_pdw_shared_value_to_differentFrom g12a ig in
  let g12b = owl_rule_fp_diff_to_diff g12a1 ig in
  let g12c = owl_rule_ifp_diff_to_diff g12b ig in
  let g12c1 = owl_rule_allDifferent_to_differentFrom g12c ig in
  let g12d = owl_rule_differentFrom_to_allDifferent g12c1 ig in
  let g13 = owl_rule_minc1_bridge g12d ig in
  let g13a = owl_rule_svf2_existential_witness g13 ig in
  let g14 = owl_rule_cls_svf2_qualified g13a ig in
  let g15 = owl_rule_cls_minc_qual1 g14 ig in
  let g16 = owl_rule_cls_maxqc1 g15 ig in
  let g17 = owl_rule_cls_exactqc1 g16 ig in
  let g18 = owl_rule_cls_maxc2 g17 ig in
  let g18a = owl_rule_cls_maxqc_comp g18 ig in
  let g19 = owl_rule_cls_avf1 g18a ig in
  let g19a = owl_rule_cls_hv1 g19 ig in
  let g19b = owl_rule_cls_hv2 g19a ig in
  let g19c = owl_rule_cls_hasself1 g19b ig in
  let g19g = owl_rule_cax_dw_to_differentFrom g19c ig in
  let g20 = owl_rule_reflexive_property g19g ig in
  let g21 = owl_rule_scm_cls_restriction g20 ig in
  let g21a = owl_rule_cls_int1 g21 ig in
  let g21b = owl_rule_cls_oneof g21a ig in
  let g21c = owl_rule_cls_uni g21b ig in
  let g21d = owl_rule_oneof_set_equivalence g21c ig in
  let g21e = owl_rule_cls_uni_elim g21d ig in
  let g22 = owl_rule_property_chain_2 g21e ig in
  let g22a = owl_rule_property_chain_n g22 ig in
  let g23 = owl_rule_chain_to_transitive g22a ig in
  let g23a = owl_rule_transitive_to_chain g23 ig in
  let g24 = owl_rule_named_sameAs_to_equivClass g23a ig in
  let g24a = owl_rule_prp_key g24 ig in
  let g25 = owl_rule_xsd_datatype_axioms g24a ig in
  let g25a = owl_rule_dt_range_intersect g25 ig in
  let g26 = owl_rule_xsd_core_datatype_axioms g25a ig in
  let g26a = owl_rule_builtin_vocabulary_axioms g26 ig in
  let g26b = owl_rule_rdf_based_full_meta_axioms_mode g26a mode in
  let g27 = owl_rule_scm_dom2 g26b ig in
  let g28 = owl_rule_scm_rng2 g27 ig in
  let g28a = owl_rule_subprop_domain_range g28 ig in
  let g28b = owl_rule_symmetric_metapredicates g28a ig in
  let g28c = owl_rule_inverse_characteristics g28b ig in
  let g28d = owl_rule_equivalent_property_characteristics g28c ig in
  let g28e = owl_rule_cardinality_to_min_max g28d ig in
  let g28f = owl_rule_cls_maxqc34 g28e ig in
  let g28g = owl_rule_fp_pinned_subproperty g28f ig in
  let g28h = owl_rule_singleton_nominal_functionality g28g ig in
  let g28i = owl_rule_hasvalue_card_disjoint g28h ig in
  let g28j = owl_rule_avf_thing_to_range g28i ig in
  let g28k = owl_rule_extensional_symmetry g28j ig in
  RDF_Graph.graph_dedup_sort g28k
let owl_rl_closure_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  owl_rl_closure_step_mode g owl_semantics_direct
let rec owl_rl_closure_mode (g : RDF_Graph.rdf_graph) (fuel : Prims.nat)
  (mode : Prims.string) : RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | uu___ ->
      let next_fuel = fuel - Prims.int_one in
      let g_owl = owl_rl_closure_step_mode g mode in
      let g_rdfs = RDFS_Closure.rdfs_closure_step g_owl in
      if (RDF_Graph.graph_len g_rdfs) = (RDF_Graph.graph_len g)
      then g
      else owl_rl_closure_mode g_rdfs next_fuel mode
let owl_rl_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph= owl_rl_closure_mode g fuel owl_semantics_direct
let owl_thing_subject_iris (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       let acc1 = RDFS_Closure.cons_subject_iri_if_new t.RDF_Triple.s acc in
       RDFS_Closure.cons_term_iri_if_new t.RDF_Triple.o acc1) [] g
let owl_thing_predicates (g : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t -> RDFS_Closure.cons_if_new_iri t.RDF_Triple.p acc) [] g
let owl_thing_axioms (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let classes = RDFS_Closure.collect_classes g in
  let properties = RDFS_Closure.collect_properties g in
  let indivs = owl_thing_subject_iris g in
  let predicates = owl_thing_predicates g in
  let top_class_triples =
    FStar_List_Tot_Base.map
      (fun c ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI c);
           RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
           RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
         }) classes in
  let bottom_class_triples =
    FStar_List_Tot_Base.map
      (fun c ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI RDFS_Closure.owl_Nothing);
           RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
           RDF_Triple.o = (RDF_Term.T_IRI c)
         }) classes in
  let property_domain_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = RDFS_Closure.rdfs_domain;
           RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
         }) properties in
  let property_range_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = RDFS_Closure.rdfs_range;
           RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
         }) properties in
  let predicate_domain_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = RDFS_Closure.rdfs_domain;
           RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
         }) predicates in
  let predicate_range_triples =
    FStar_List_Tot_Base.map
      (fun p ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI p);
           RDF_Triple.p = RDFS_Closure.rdfs_range;
           RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
         }) predicates in
  let individual_triples =
    FStar_List_Tot_Base.map
      (fun i ->
         {
           RDF_Triple.s = (RDF_Term.S_IRI i);
           RDF_Triple.p = RDFS_Closure.rdf_type;
           RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
         }) indivs in
  let self_axioms =
    [{
       RDF_Triple.s = (RDF_Term.S_IRI RDFS_Closure.owl_Thing);
       RDF_Triple.p = RDFS_Closure.rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
     };
    {
      RDF_Triple.s = (RDF_Term.S_IRI RDFS_Closure.owl_Nothing);
      RDF_Triple.p = RDFS_Closure.rdf_type;
      RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
    };
    {
      RDF_Triple.s = (RDF_Term.S_IRI RDFS_Closure.owl_Nothing);
      RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
      RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Thing)
    }] in
  FStar_List_Tot_Base.op_At top_class_triples
    (FStar_List_Tot_Base.op_At bottom_class_triples
       (FStar_List_Tot_Base.op_At property_domain_triples
          (FStar_List_Tot_Base.op_At property_range_triples
             (FStar_List_Tot_Base.op_At predicate_domain_triples
                (FStar_List_Tot_Base.op_At predicate_range_triples
                   (FStar_List_Tot_Base.op_At individual_triples self_axioms))))))
let owl_rl_closure_with_reflexivity_mode (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) (mode : Prims.string) : RDF_Graph.rdf_graph=
  let rdfs_closed = RDFS_Closure.owl_rdfs_closure_with_reflexivity g fuel in
  let thing_axioms = owl_thing_axioms rdfs_closed in
  let with_thing = RDF_Graph.add_triples_if_new rdfs_closed thing_axioms in
  owl_rl_closure_mode with_thing fuel mode
let owl_rl_closure_with_reflexivity (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  owl_rl_closure_with_reflexivity_mode g fuel owl_semantics_direct
let is_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let rec strip_leading_zeros (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> [FStar_Char.char_of_int (Prims.of_int (0x30))]
  | c::[] -> [c]
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x30))
      then strip_leading_zeros rest
      else cs
let normalize_integer_lexical (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  match chars with
  | [] -> "0"
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      if code = (Prims.of_int (0x2D))
      then
        let normalized = strip_leading_zeros rest in
        (match normalized with
         | z::[] ->
             if (FStar_Char.int_of_char z) = (Prims.of_int (0x30))
             then "0"
             else
               FStar_String.concat ""
                 ["-"; FStar_String.string_of_list normalized]
         | uu___ ->
             FStar_String.concat ""
               ["-"; FStar_String.string_of_list normalized])
      else
        if code = (Prims.of_int (0x2B))
        then FStar_String.string_of_list (strip_leading_zeros rest)
        else FStar_String.string_of_list (strip_leading_zeros chars)
let strip_trailing_zeros (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> [FStar_Char.char_of_int (Prims.of_int (0x30))]
  | uu___ ->
      let rev = FStar_List_Tot_Base.rev cs in
      let rec drop_zeros l =
        match l with
        | [] -> [FStar_Char.char_of_int (Prims.of_int (0x30))]
        | c::rest ->
            if (FStar_Char.int_of_char c) = (Prims.of_int (0x30))
            then drop_zeros rest
            else FStar_List_Tot_Base.rev l in
      drop_zeros rev
let rec split_at_dot (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), FStar_Pervasives_Native.None)
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x2E))
      then
        ((FStar_List_Tot_Base.rev acc), (FStar_Pervasives_Native.Some rest))
      else split_at_dot rest (c :: acc)
let normalize_decimal_lexical (s : Prims.string) : Prims.string=
  let chars = FStar_String.list_of_string s in
  let uu___ =
    match chars with
    | [] -> ("", chars)
    | c::rest ->
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x2D))
        then ("-", rest)
        else if code = (Prims.of_int (0x2B)) then ("", rest) else ("", chars) in
  match uu___ with
  | (sign, digits) ->
      let uu___1 = split_at_dot digits [] in
      (match uu___1 with
       | (int_part, frac_opt) ->
           let norm_int = strip_leading_zeros int_part in
           (match frac_opt with
            | FStar_Pervasives_Native.None ->
                let result =
                  FStar_String.concat ""
                    [sign; FStar_String.string_of_list norm_int] in
                if (sign = "-") && (result = "-0") then "0" else result
            | FStar_Pervasives_Native.Some frac_digits ->
                let norm_frac = strip_trailing_zeros frac_digits in
                let int_str = FStar_String.string_of_list norm_int in
                let frac_str = FStar_String.string_of_list norm_frac in
                let result =
                  FStar_String.concat "" [sign; int_str; "."; frac_str] in
                if ((sign = "-") && (int_str = "0")) && (frac_str = "0")
                then "0.0"
                else result))
let datatype_value_eq (l1 : RDF_Term.literal) (l2 : RDF_Term.literal) :
  Prims.bool=
  if l1.RDF_Term.datatype = l2.RDF_Term.datatype
  then
    (if l1.RDF_Term.datatype = RDF_Term.xsd_integer
     then
       ((normalize_integer_lexical l1.RDF_Term.lexical_form) =
          (normalize_integer_lexical l2.RDF_Term.lexical_form))
         &&
         (RDF_Term.lang_tag_option_eq l1.RDF_Term.lang_tag
            l2.RDF_Term.lang_tag)
     else
       if l1.RDF_Term.datatype = RDF_Term.xsd_decimal
       then
         ((normalize_decimal_lexical l1.RDF_Term.lexical_form) =
            (normalize_decimal_lexical l2.RDF_Term.lexical_form))
           &&
           (RDF_Term.lang_tag_option_eq l1.RDF_Term.lang_tag
              l2.RDF_Term.lang_tag)
       else RDF_Term.literal_eq l1 l2)
  else false
let rdf_List_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"
let one_xsd_int_literal : RDF_Term.wf_literal=
  let l =
    {
      RDF_Term.lexical_form = "1";
      RDF_Term.datatype = xsd_int;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    } in
  l
let rec comp_list_cells (prefix : Prims.string)
  (elems : RDF_Term.wf_iri Prims.list) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list)=
  match elems with
  | [] -> ((RDF_Term.T_IRI rdf_nil_iri), [])
  | e::rest ->
      let tail = comp_list_cells prefix rest in
      let uu___ = tail in
      (match uu___ with
       | (tail_term, tail_ts) ->
           let cell_id = FStar_String.concat "" [prefix; "__cell__"; e] in
           let cs = RDF_Term.S_BNode cell_id in
           ((RDF_Term.T_BNode cell_id),
             ({
                RDF_Triple.s = cs;
                RDF_Triple.p = RDFS_Closure.rdf_type;
                RDF_Triple.o = (RDF_Term.T_IRI rdf_List_iri)
              } ::
             {
               RDF_Triple.s = cs;
               RDF_Triple.p = rdf_first;
               RDF_Triple.o = (RDF_Term.T_IRI e)
             } ::
             {
               RDF_Triple.s = cs;
               RDF_Triple.p = rdf_rest;
               RDF_Triple.o = tail_term
             } :: tail_ts)))
let owl_rule_comp_singleton_union (base : RDF_Graph.rdf_graph)
  (acc0 : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI RDFS_Closure.owl_Class))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI c ->
             let u_id = FStar_String.concat "" ["__rl_compw_uni1__"; c] in
             let spine =
               comp_list_cells
                 (FStar_String.concat "" ["__rl_compw_uni1l__"; c]) [c] in
             let uu___ = spine in
             (match uu___ with
              | (head_term, cell_ts) ->
                  let u_subj = RDF_Term.S_BNode u_id in
                  RDF_Graph.add_triples_if_new acc
                    ({
                       RDF_Triple.s = u_subj;
                       RDF_Triple.p = RDFS_Closure.rdf_type;
                       RDF_Triple.o = (RDF_Term.T_IRI RDFS_Closure.owl_Class)
                     } ::
                    {
                      RDF_Triple.s = u_subj;
                      RDF_Triple.p = owl_unionOf_iri;
                      RDF_Triple.o = head_term
                    } :: cell_ts))
         | uu___ -> acc
       else acc) acc0 base
let owl_rule_comp_min1_restriction (base : RDF_Graph.rdf_graph)
  (acc0 : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           ((RDF_Term.rdf_term_eq t.RDF_Triple.o
               (RDF_Term.T_IRI RDFS_Closure.owl_ObjectProperty))
              ||
              (RDF_Term.rdf_term_eq t.RDF_Triple.o
                 (RDF_Term.T_IRI RDFS_Closure.owl_DatatypeProperty)))
       then
         match t.RDF_Triple.s with
         | RDF_Term.S_IRI p ->
             let r_id = FStar_String.concat "" ["__rl_compw_minc1__"; p] in
             let r_subj = RDF_Term.S_BNode r_id in
             RDF_Graph.add_triples_if_new acc
               [{
                  RDF_Triple.s = r_subj;
                  RDF_Triple.p = RDFS_Closure.rdf_type;
                  RDF_Triple.o = (RDF_Term.T_IRI owl_Restriction_iri)
                };
               {
                 RDF_Triple.s = r_subj;
                 RDF_Triple.p = owl_onProperty_iri;
                 RDF_Triple.o = (RDF_Term.T_IRI p)
               };
               {
                 RDF_Triple.s = r_subj;
                 RDF_Triple.p = owl_minCardinality_iri;
                 RDF_Triple.o = (RDF_Term.T_Literal one_xsd_int_literal)
               }]
         | uu___ -> acc
       else acc) acc0 base
let owl_rule_comp_oneof_union (base : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (acc0 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  let axioms = collect_oneof_axioms base ig in
  FStar_List_Tot_Base.fold_left
    (fun acc_a a3 ->
       let uu___ = a3 in
       match uu___ with
       | (c3, m3) ->
           FStar_List_Tot_Base.fold_left
             (fun acc_b a1 ->
                let uu___1 = a1 in
                match uu___1 with
                | (c1, m1) ->
                    FStar_List_Tot_Base.fold_left
                      (fun acc_c a2 ->
                         let uu___2 = a2 in
                         match uu___2 with
                         | (c2, m2) ->
                             if
                               (((c1 <> c2) && (c3 <> c1)) && (c3 <> c2)) &&
                                 (iri_list_set_eq m3
                                    (FStar_List_Tot_Base.append m1 m2))
                             then
                               let prefix =
                                 FStar_String.concat ""
                                   ["__rl_compw_uoo3__";
                                   c3;
                                   "__of__";
                                   c1;
                                   "__and__";
                                   c2] in
                               let spine = comp_list_cells prefix [c1; c2] in
                               let uu___3 = spine in
                               (match uu___3 with
                                | (head_term, cell_ts) ->
                                    RDF_Graph.add_triples_if_new acc_c
                                      ({
                                         RDF_Triple.s = (RDF_Term.S_IRI c3);
                                         RDF_Triple.p = owl_unionOf_iri;
                                         RDF_Triple.o = head_term
                                       } :: cell_ts))
                             else acc_c) acc_b axioms) acc_a axioms) acc0
    axioms
let rec oneof_members_for
  (axioms : (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list)
  (c : RDF_Term.wf_iri) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  match axioms with
  | [] -> FStar_Pervasives_Native.None
  | a::rest ->
      let uu___ = a in
      (match uu___ with
       | (c', m) ->
           if c' = c
           then FStar_Pervasives_Native.Some m
           else oneof_members_for rest c)
let rec all_oneof_members
  (axioms : (RDF_Term.wf_iri * RDF_Term.wf_iri Prims.list) Prims.list)
  (cs : RDF_Term.wf_iri Prims.list) :
  RDF_Term.wf_iri Prims.list FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some []
  | c::rest ->
      (match oneof_members_for axioms c with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some m ->
           (match all_oneof_members axioms rest with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ms ->
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.append m ms)))
let rec iri_dedup_acc (seen : RDF_Term.wf_iri Prims.list)
  (l : RDF_Term.wf_iri Prims.list) : RDF_Term.wf_iri Prims.list=
  match l with
  | [] -> []
  | x::rest ->
      if FStar_List_Tot_Base.mem x seen
      then iri_dedup_acc seen rest
      else x :: (iri_dedup_acc (x :: seen) rest)
let owl_rule_comp_union_oneof (base : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (acc0 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  let fuel = FStar_List_Tot_Base.length base in
  let axioms = collect_oneof_axioms base ig in
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = owl_unionOf_iri
       then
         match ((t.RDF_Triple.s), (RDF_Graph.term_to_subject t.RDF_Triple.o))
         with
         | (RDF_Term.S_IRI c, FStar_Pervasives_Native.Some list_subj) ->
             (match decode_iri_list base ig list_subj fuel with
              | FStar_Pervasives_Native.None -> acc
              | FStar_Pervasives_Native.Some members ->
                  (match all_oneof_members axioms members with
                   | FStar_Pervasives_Native.None -> acc
                   | FStar_Pervasives_Native.Some indivs ->
                       (match iri_dedup_acc [] indivs with
                        | [] -> acc
                        | u ->
                            let prefix =
                              FStar_String.concat "" ["__rl_compw_uof__"; c] in
                            let spine = comp_list_cells prefix u in
                            let uu___ = spine in
                            (match uu___ with
                             | (head_term, cell_ts) ->
                                 RDF_Graph.add_triples_if_new acc
                                   ({
                                      RDF_Triple.s = (RDF_Term.S_IRI c);
                                      RDF_Triple.p = owl_oneOf_iri;
                                      RDF_Triple.o = head_term
                                    } :: cell_ts)))))
         | (uu___, uu___1) -> acc
       else acc) acc0 base
let rec decode_literal_list (ig : RDF_Indexed.indexed_graph)
  (head_subj : RDF_Term.subject) (fuel : Prims.nat) :
  RDF_Term.wf_literal Prims.list FStar_Pervasives_Native.option=
  let is_nil_head =
    match head_subj with
    | RDF_Term.S_IRI i -> i = rdf_nil_iri
    | uu___ -> false in
  if is_nil_head
  then FStar_Pervasives_Native.Some []
  else
    if fuel = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (let firsts = RDF_Indexed.find_objects_indexed ig head_subj rdf_first in
       let rests = RDF_Indexed.find_objects_indexed ig head_subj rdf_rest in
       match (firsts, rests) with
       | ((RDF_Term.T_Literal l)::uu___2, tail_term::uu___3) ->
           (match RDF_Graph.term_to_subject tail_term with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some tail_subj ->
                (match decode_literal_list ig tail_subj
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some rest_lits ->
                     FStar_Pervasives_Native.Some (l :: rest_lits)))
       | (uu___2, uu___3) -> FStar_Pervasives_Native.None)
let lexical_is_positive_int (s : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string s in
  (match cs with
   | [] -> false
   | uu___ -> FStar_List_Tot_Base.for_all is_digit cs) &&
    ((normalize_integer_lexical s) <> "0")
let term_is_positive_int_literal (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l -> lexical_is_positive_int l.RDF_Term.lexical_form
  | uu___ -> false
let restriction_forces_value (ig : RDF_Indexed.indexed_graph)
  (r_subj : RDF_Term.subject) : Prims.bool=
  let mins =
    RDF_Indexed.find_objects_indexed ig r_subj owl_minCardinality_iri in
  let cards = RDF_Indexed.find_objects_indexed ig r_subj owl_cardinality_iri in
  let svfs =
    RDF_Indexed.find_objects_indexed ig r_subj owl_someValuesFrom_iri in
  ((FStar_List_Tot_Base.existsb term_is_positive_int_literal mins) ||
     (FStar_List_Tot_Base.existsb term_is_positive_int_literal cards))
    || (Prims.uu___is_Cons svfs)
let enumerated_range_lists (base : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (p : RDF_Term.wf_iri) :
  RDF_Term.wf_literal Prims.list Prims.list=
  let fuel = FStar_List_Tot_Base.length base in
  let ranges =
    RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
      RDFS_Closure.rdfs_range in
  FStar_List_Tot_Base.fold_left
    (fun acc r ->
       match RDF_Graph.term_to_subject r with
       | FStar_Pervasives_Native.None -> acc
       | FStar_Pervasives_Native.Some r_subj ->
           let oneofs =
             RDF_Indexed.find_objects_indexed ig r_subj owl_oneOf_iri in
           FStar_List_Tot_Base.fold_left
             (fun acc2 o ->
                match RDF_Graph.term_to_subject o with
                | FStar_Pervasives_Native.None -> acc2
                | FStar_Pervasives_Native.Some list_subj ->
                    (match decode_literal_list ig list_subj fuel with
                     | FStar_Pervasives_Native.None -> acc2
                     | FStar_Pervasives_Native.Some lits -> lits :: acc2))
             acc oneofs) [] ranges
let literal_in_list_by_value (l : RDF_Term.wf_literal)
  (ls : RDF_Term.wf_literal Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb (fun x -> datatype_value_eq x l) ls
let literals_in_all_lists (lists : RDF_Term.wf_literal Prims.list Prims.list)
  : RDF_Term.wf_literal Prims.list=
  match lists with
  | [] -> []
  | uu___ ->
      let pool =
        FStar_List_Tot_Base.fold_left
          (fun acc ls -> FStar_List_Tot_Base.append acc ls) [] lists in
      FStar_List_Tot_Base.filter
        (fun l ->
           FStar_List_Tot_Base.for_all
             (fun ls -> literal_in_list_by_value l ls) lists) pool
let all_value_equal (ls : RDF_Term.wf_literal Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun a -> FStar_List_Tot_Base.for_all (fun b -> datatype_value_eq a b) ls)
    ls
let owl_rule_comp_enum_range_value (base : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (acc0 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdf_type
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.None -> acc
         | FStar_Pervasives_Native.Some r_subj ->
             (if restriction_forces_value ig r_subj
              then
                let onprops =
                  RDF_Indexed.find_objects_indexed ig r_subj
                    owl_onProperty_iri in
                FStar_List_Tot_Base.fold_left
                  (fun acc2 op ->
                     match op with
                     | RDF_Term.T_IRI p ->
                         (match enumerated_range_lists base ig p with
                          | [] -> acc2
                          | lists ->
                              (match literals_in_all_lists lists with
                               | [] -> acc2
                               | inter ->
                                   if all_value_equal inter
                                   then
                                     FStar_List_Tot_Base.fold_left
                                       (fun acc3 v ->
                                          RDF_Graph.add_triple_unchecked acc3
                                            {
                                              RDF_Triple.s = (t.RDF_Triple.s);
                                              RDF_Triple.p = p;
                                              RDF_Triple.o =
                                                (RDF_Term.T_Literal v)
                                            }) acc2 inter
                                   else acc2))
                     | uu___ -> acc2) acc onprops
              else acc)
       else acc) acc0 base
let is_declared_owl_property (ig : RDF_Indexed.indexed_graph)
  (p : RDF_Term.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (RDF_Term.rdf_term_eq t
          (RDF_Term.T_IRI RDFS_Closure.owl_ObjectProperty))
         ||
         (RDF_Term.rdf_term_eq t
            (RDF_Term.T_IRI RDFS_Closure.owl_DatatypeProperty)))
    (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
       RDFS_Closure.rdf_type)
let owl_rule_comp_range_avf (base : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (acc0 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_range
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p, RDF_Term.T_IRI c) ->
             (if
                (c = RDFS_Closure.owl_Thing) ||
                  (Prims.op_Negation (is_declared_owl_property ig p))
              then acc
              else
                (let r_id =
                   FStar_String.concat "" ["__rl_compw_rngavf__"; p; "__"; c] in
                 let r_subj = RDF_Term.S_BNode r_id in
                 RDF_Graph.add_triples_if_new acc
                   [{
                      RDF_Triple.s = r_subj;
                      RDF_Triple.p = RDFS_Closure.rdf_type;
                      RDF_Triple.o = (RDF_Term.T_IRI owl_Restriction_iri)
                    };
                   {
                     RDF_Triple.s = r_subj;
                     RDF_Triple.p = owl_onProperty_iri;
                     RDF_Triple.o = (RDF_Term.T_IRI p)
                   };
                   {
                     RDF_Triple.s = r_subj;
                     RDF_Triple.p = owl_allValuesFrom_iri;
                     RDF_Triple.o = (RDF_Term.T_IRI c)
                   };
                   {
                     RDF_Triple.s = (RDF_Term.S_IRI RDFS_Closure.owl_Thing);
                     RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                     RDF_Triple.o = (RDF_Term.T_BNode r_id)
                   }]))
         | (uu___, uu___1) -> acc
       else acc) acc0 base
let iri_subclass_of (ig : RDF_Indexed.indexed_graph) (a : RDF_Term.wf_iri)
  (b : RDF_Term.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t -> RDF_Term.rdf_term_eq t (RDF_Term.T_IRI b))
    (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI a)
       RDFS_Closure.rdfs_subClassOf)
let minimal_named_ranges (ig : RDF_Indexed.indexed_graph)
  (p : RDF_Term.wf_iri) : RDF_Term.wf_iri Prims.list=
  let all_ranges =
    FStar_List_Tot_Base.fold_left
      (fun acc r ->
         match r with
         | RDF_Term.T_IRI c ->
             if c = RDFS_Closure.owl_Thing
             then acc
             else RDFS_Closure.cons_if_new_iri c acc
         | uu___ -> acc) []
      (RDF_Indexed.find_objects_indexed ig (RDF_Term.S_IRI p)
         RDFS_Closure.rdfs_range) in
  FStar_List_Tot_Base.filter
    (fun c ->
       Prims.op_Negation
         (FStar_List_Tot_Base.existsb
            (fun c2 ->
               ((c2 <> c) && (iri_subclass_of ig c2 c)) &&
                 (Prims.op_Negation (iri_subclass_of ig c c2))) all_ranges))
    all_ranges
let range_subject_properties (base : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.fold_left
    (fun acc t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_range
       then
         match ((t.RDF_Triple.s), (t.RDF_Triple.o)) with
         | (RDF_Term.S_IRI p, RDF_Term.T_IRI uu___) ->
             RDFS_Closure.cons_if_new_iri p acc
         | (uu___, uu___1) -> acc
       else acc) [] base
let owl_rule_comp_range_intersection (base : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) (acc0 : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc p ->
       let rs = minimal_named_ranges ig p in
       FStar_List_Tot_Base.fold_left
         (fun acc1 c1 ->
            FStar_List_Tot_Base.fold_left
              (fun acc2 c2 ->
                 if c1 = c2
                 then acc2
                 else
                   (let key =
                      FStar_String.concat "" [p; "__"; c1; "__and__"; c2] in
                    let i_id =
                      FStar_String.concat "" ["__rl_compw_rngint__"; key] in
                    let spine =
                      comp_list_cells
                        (FStar_String.concat "" ["__rl_compw_rngintl__"; key])
                        [c1; c2] in
                    let uu___1 = spine in
                    match uu___1 with
                    | (head_term, cell_ts) ->
                        let i_subj = RDF_Term.S_BNode i_id in
                        RDF_Graph.add_triples_if_new acc2
                          ({
                             RDF_Triple.s = i_subj;
                             RDF_Triple.p = RDFS_Closure.rdf_type;
                             RDF_Triple.o =
                               (RDF_Term.T_IRI RDFS_Closure.owl_Class)
                           } ::
                          {
                            RDF_Triple.s = i_subj;
                            RDF_Triple.p = owl_intersectionOf_iri;
                            RDF_Triple.o = head_term
                          } ::
                          {
                            RDF_Triple.s = (RDF_Term.S_IRI p);
                            RDF_Triple.p = RDFS_Closure.rdfs_range;
                            RDF_Triple.o = (RDF_Term.T_BNode i_id)
                          } :: cell_ts))) acc1 rs) acc rs) acc0
    (range_subject_properties base)
let asserted_thing_individuals (g0 : RDF_Graph.rdf_graph) :
  RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.rev
    (FStar_List_Tot_Base.fold_left
       (fun acc t ->
          if
            (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
              (RDF_Term.rdf_term_eq t.RDF_Triple.o
                 (RDF_Term.T_IRI RDFS_Closure.owl_Thing))
          then
            match t.RDF_Triple.s with
            | RDF_Term.S_IRI i -> RDFS_Closure.cons_if_new_iri i acc
            | RDF_Term.S_BNode uu___ -> acc
          else acc) [] g0)
let owl_rule_comp_pinned_domain_enum (g0 : RDF_Graph.rdf_graph)
  (base : RDF_Graph.rdf_graph) (ig : RDF_Indexed.indexed_graph)
  (acc0 : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let indivs = asserted_thing_individuals g0 in
  if Prims.uu___is_Nil indivs
  then acc0
  else
    FStar_List_Tot_Base.fold_left
      (fun acc t ->
         if
           (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
             (RDF_Term.rdf_term_eq t.RDF_Triple.o
                (RDF_Term.T_IRI owl_InverseFunctionalProperty))
         then
           match t.RDF_Triple.s with
           | RDF_Term.S_IRI p ->
               (match pinned_property_extension base ig p with
                | FStar_Pervasives_Native.None -> acc
                | FStar_Pervasives_Native.Some es ->
                    if
                      FStar_List_Tot_Base.for_all
                        (fun e ->
                           let uu___1 = e in
                           match uu___1 with
                           | (x, uu___2) -> FStar_List_Tot_Base.mem x indivs)
                        es
                    then
                      let e_id =
                        FStar_String.concat "" ["__rl_compw_pindom__"; p] in
                      let spine =
                        comp_list_cells
                          (FStar_String.concat "" ["__rl_compw_pindoml__"; p])
                          indivs in
                      let uu___1 = spine in
                      (match uu___1 with
                       | (head_term, cell_ts) ->
                           let e_subj = RDF_Term.S_BNode e_id in
                           RDF_Graph.add_triples_if_new acc
                             ({
                                RDF_Triple.s = e_subj;
                                RDF_Triple.p = RDFS_Closure.rdf_type;
                                RDF_Triple.o =
                                  (RDF_Term.T_IRI RDFS_Closure.owl_Class)
                              } ::
                             {
                               RDF_Triple.s = e_subj;
                               RDF_Triple.p = owl_oneOf_iri;
                               RDF_Triple.o = head_term
                             } ::
                             {
                               RDF_Triple.s = (RDF_Term.S_IRI p);
                               RDF_Triple.p = RDFS_Closure.rdfs_domain;
                               RDF_Triple.o = (RDF_Term.T_BNode e_id)
                             } :: cell_ts))
                    else acc)
           | uu___1 -> acc
         else acc) acc0 base
let owl_rl_closure_with_reflexivity_and_witnesses_mode
  (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) (mode : Prims.string) :
  RDF_Graph.rdf_graph=
  let base = owl_rl_closure_with_reflexivity_mode g fuel mode in
  let ig1 = RDF_Indexed.build_indexed base in
  let w1 = owl_rule_cls_hasself2_synth base ig1 in
  let ig2 = RDF_Indexed.build_indexed w1 in
  let w2 = owl_rule_cls_svf_thing_materialize w1 ig2 in
  let ig3 = RDF_Indexed.build_indexed w2 in
  let w3 = owl_rule_cls_svf_thing_witness w2 ig3 in
  let c1 = owl_rule_comp_singleton_union base w3 in
  let c2 = owl_rule_comp_min1_restriction base c1 in
  let c3 = owl_rule_comp_oneof_union base ig1 c2 in
  let c4 = owl_rule_comp_union_oneof base ig1 c3 in
  let c5 = owl_rule_comp_enum_range_value base ig1 c4 in
  let c6 = owl_rule_comp_range_avf base ig1 c5 in
  let c7 = owl_rule_comp_range_intersection base ig1 c6 in
  let c8 = owl_rule_comp_pinned_domain_enum g base ig1 c7 in
  owl_rl_closure_with_reflexivity_mode c8 fuel mode
let owl_rl_closure_with_reflexivity_and_witnesses (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  owl_rl_closure_with_reflexivity_and_witnesses_mode g fuel
    owl_semantics_direct
let has_disjoint_with (g : RDF_Graph.rdf_graph) (c1 : RDF_Term.rdf_term)
  (c2 : RDF_Term.rdf_term) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun t ->
       (t.RDF_Triple.p = owl_disjointWith_iri) &&
         (((RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s)
              c1)
             && (RDF_Term.rdf_term_eq t.RDF_Triple.o c2))
            ||
            ((RDF_Term.rdf_term_eq (RDF_Graph.subject_to_term t.RDF_Triple.s)
                c2)
               && (RDF_Term.rdf_term_eq t.RDF_Triple.o c1)))) g
let rec xsd_is_subtype_fuel (d1 : RDF_Term.wf_iri) (d2 : RDF_Term.wf_iri)
  (fuel : Prims.nat) : Prims.bool=
  if d1 = d2
  then true
  else
    if fuel = Prims.int_zero
    then false
    else
      FStar_List_Tot_Base.existsb
        (fun edge ->
           let uu___2 = edge in
           match uu___2 with
           | (sub_i, sup_i) ->
               (sub_i = d1) &&
                 (xsd_is_subtype_fuel sup_i d2 (fuel - Prims.int_one)))
        xsd_hierarchy_edges
let xsd_is_subtype (d1 : RDF_Term.wf_iri) (d2 : RDF_Term.wf_iri) :
  Prims.bool=
  xsd_is_subtype_fuel d1 d2
    ((FStar_List_Tot_Base.length xsd_hierarchy_edges) + Prims.int_one)
let owl_bottomObjectProperty_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#bottomObjectProperty"
let owl_bottomDataProperty_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2002/07/owl#bottomDataProperty"
let is_inconsistent (g : RDF_Graph.rdf_graph) : Prims.bool=
  let has_nothing =
    FStar_List_Tot_Base.existsb
      (fun t ->
         (t.RDF_Triple.p = RDFS_Closure.rdf_type) &&
           (RDF_Term.rdf_term_eq t.RDF_Triple.o
              (RDF_Term.T_IRI RDFS_Closure.owl_Nothing))) g in
  if has_nothing
  then true
  else
    (let has_sameAs_diff_clash =
       FStar_List_Tot_Base.existsb
         (fun t ->
            (t.RDF_Triple.p = owl_sameAs) &&
              (differentFrom_in_graph g
                 (RDF_Graph.subject_to_term t.RDF_Triple.s) t.RDF_Triple.o))
         g in
     if has_sameAs_diff_clash
     then true
     else
       (let has_disjoint_class_clash =
          FStar_List_Tot_Base.existsb
            (fun t1 ->
               (t1.RDF_Triple.p = RDFS_Closure.rdf_type) &&
                 (FStar_List_Tot_Base.existsb
                    (fun t2 ->
                       (((t2.RDF_Triple.p = RDFS_Closure.rdf_type) &&
                           (RDF_Term.subject_eq t1.RDF_Triple.s
                              t2.RDF_Triple.s))
                          &&
                          (Prims.op_Negation
                             (RDF_Term.rdf_term_eq t1.RDF_Triple.o
                                t2.RDF_Triple.o)))
                         &&
                         (has_disjoint_with g t1.RDF_Triple.o t2.RDF_Triple.o))
                    g)) g in
        if has_disjoint_class_clash
        then true
        else
          (let has_irreflexive_violation =
             FStar_List_Tot_Base.existsb
               (fun decl ->
                  ((decl.RDF_Triple.p = RDFS_Closure.rdf_type) &&
                     (RDF_Term.rdf_term_eq decl.RDF_Triple.o
                        (RDF_Term.T_IRI owl_IrreflexiveProperty)))
                    &&
                    (match decl.RDF_Triple.s with
                     | RDF_Term.S_IRI prop_iri ->
                         FStar_List_Tot_Base.existsb
                           (fun use ->
                              (use.RDF_Triple.p = prop_iri) &&
                                (RDF_Term.rdf_term_eq
                                   (RDF_Graph.subject_to_term
                                      use.RDF_Triple.s) use.RDF_Triple.o)) g
                     | uu___3 -> false)) g in
           if has_irreflexive_violation
           then true
           else
             (let has_asymmetric_violation =
                FStar_List_Tot_Base.existsb
                  (fun decl ->
                     ((decl.RDF_Triple.p = RDFS_Closure.rdf_type) &&
                        (RDF_Term.rdf_term_eq decl.RDF_Triple.o
                           (RDF_Term.T_IRI owl_AsymmetricProperty)))
                       &&
                       (match decl.RDF_Triple.s with
                        | RDF_Term.S_IRI prop_iri ->
                            FStar_List_Tot_Base.existsb
                              (fun t1 ->
                                 (t1.RDF_Triple.p = prop_iri) &&
                                   (FStar_List_Tot_Base.existsb
                                      (fun t2 ->
                                         ((t2.RDF_Triple.p = prop_iri) &&
                                            (RDF_Term.rdf_term_eq
                                               (RDF_Graph.subject_to_term
                                                  t1.RDF_Triple.s)
                                               t2.RDF_Triple.o))
                                           &&
                                           (RDF_Term.rdf_term_eq
                                              t1.RDF_Triple.o
                                              (RDF_Graph.subject_to_term
                                                 t2.RDF_Triple.s))) g)) g
                        | uu___4 -> false)) g in
              if has_asymmetric_violation
              then true
              else
                (let is_pdw_pair p1 p2 =
                   FStar_List_Tot_Base.existsb
                     (fun pdw ->
                        (pdw.RDF_Triple.p = owl_propertyDisjointWith) &&
                          (match ((pdw.RDF_Triple.s), (pdw.RDF_Triple.o))
                           with
                           | (RDF_Term.S_IRI ps, RDF_Term.T_IRI po) ->
                               ((ps = p1) && (po = p2)) ||
                                 ((ps = p2) && (po = p1))
                           | uu___5 -> false)) g in
                 let has_pdw_direct_clash =
                   FStar_List_Tot_Base.existsb
                     (fun t1 ->
                        FStar_List_Tot_Base.existsb
                          (fun t2 ->
                             (((t1.RDF_Triple.p <> t2.RDF_Triple.p) &&
                                 (RDF_Term.subject_eq t1.RDF_Triple.s
                                    t2.RDF_Triple.s))
                                &&
                                (RDF_Term.rdf_term_eq t1.RDF_Triple.o
                                   t2.RDF_Triple.o))
                               &&
                               (is_pdw_pair t1.RDF_Triple.p t2.RDF_Triple.p))
                          g) g in
                 if has_pdw_direct_clash
                 then true
                 else
                   (let has_fp_literal_clash =
                      FStar_List_Tot_Base.existsb
                        (fun decl ->
                           ((decl.RDF_Triple.p = RDFS_Closure.rdf_type) &&
                              (RDF_Term.rdf_term_eq decl.RDF_Triple.o
                                 (RDF_Term.T_IRI owl_FunctionalProperty)))
                             &&
                             (match decl.RDF_Triple.s with
                              | RDF_Term.S_IRI prop_iri ->
                                  (Prims.op_Negation
                                     (is_list_cell_functional_property
                                        prop_iri))
                                    &&
                                    (FStar_List_Tot_Base.existsb
                                       (fun t1 ->
                                          (t1.RDF_Triple.p = prop_iri) &&
                                            (match t1.RDF_Triple.o with
                                             | RDF_Term.T_Literal l1 ->
                                                 FStar_List_Tot_Base.existsb
                                                   (fun t2 ->
                                                      ((t2.RDF_Triple.p =
                                                          prop_iri)
                                                         &&
                                                         (RDF_Term.subject_eq
                                                            t1.RDF_Triple.s
                                                            t2.RDF_Triple.s))
                                                        &&
                                                        (match t2.RDF_Triple.o
                                                         with
                                                         | RDF_Term.T_Literal
                                                             l2 ->
                                                             Prims.op_Negation
                                                               (datatype_value_eq
                                                                  l1 l2)
                                                         | uu___6 -> false))
                                                   g
                                             | uu___6 -> false)) g)
                              | uu___6 -> false)) g in
                    if has_fp_literal_clash
                    then true
                    else
                      (let has_npa_clash =
                         FStar_List_Tot_Base.existsb
                           (fun npa ->
                              (npa.RDF_Triple.p = owl_sourceIndividual) &&
                                (match RDF_Graph.term_to_subject
                                         npa.RDF_Triple.o
                                 with
                                 | FStar_Pervasives_Native.None -> false
                                 | FStar_Pervasives_Native.Some i1 ->
                                     FStar_List_Tot_Base.existsb
                                       (fun ap ->
                                          ((RDF_Term.subject_eq
                                              ap.RDF_Triple.s
                                              npa.RDF_Triple.s)
                                             &&
                                             (ap.RDF_Triple.p =
                                                owl_assertionProperty))
                                            &&
                                            (match ap.RDF_Triple.o with
                                             | RDF_Term.T_IRI p ->
                                                 FStar_List_Tot_Base.existsb
                                                   (fun tgt ->
                                                      ((RDF_Term.subject_eq
                                                          tgt.RDF_Triple.s
                                                          npa.RDF_Triple.s)
                                                         &&
                                                         ((tgt.RDF_Triple.p =
                                                             owl_targetIndividual)
                                                            ||
                                                            (tgt.RDF_Triple.p
                                                               =
                                                               owl_targetValue)))
                                                        &&
                                                        (FStar_List_Tot_Base.existsb
                                                           (fun pos ->
                                                              ((pos.RDF_Triple.p
                                                                  = p)
                                                                 &&
                                                                 (RDF_Term.subject_eq
                                                                    pos.RDF_Triple.s
                                                                    i1))
                                                                &&
                                                                (RDF_Term.rdf_term_eq
                                                                   pos.RDF_Triple.o
                                                                   tgt.RDF_Triple.o))
                                                           g)) g
                                             | uu___7 -> false)) g)) g in
                       if has_npa_clash
                       then true
                       else
                         (let has_cls_com_clash =
                            FStar_List_Tot_Base.existsb
                              (fun comp ->
                                 (comp.RDF_Triple.p = owl_complementOf_iri)
                                   &&
                                   (FStar_List_Tot_Base.existsb
                                      (fun t1 ->
                                         ((t1.RDF_Triple.p =
                                             RDFS_Closure.rdf_type)
                                            &&
                                            (RDF_Term.rdf_term_eq
                                               t1.RDF_Triple.o
                                               (RDF_Graph.subject_to_term
                                                  comp.RDF_Triple.s)))
                                           &&
                                           (FStar_List_Tot_Base.existsb
                                              (fun t2 ->
                                                 ((t2.RDF_Triple.p =
                                                     RDFS_Closure.rdf_type)
                                                    &&
                                                    (RDF_Term.subject_eq
                                                       t1.RDF_Triple.s
                                                       t2.RDF_Triple.s))
                                                   &&
                                                   (RDF_Term.rdf_term_eq
                                                      t2.RDF_Triple.o
                                                      comp.RDF_Triple.o)) g))
                                      g)) g in
                          if has_cls_com_clash
                          then true
                          else
                            (let has_dt_range_clash =
                               FStar_List_Tot_Base.existsb
                                 (fun rng ->
                                    (rng.RDF_Triple.p =
                                       RDFS_Closure.rdfs_range)
                                      &&
                                      (match ((rng.RDF_Triple.s),
                                               (rng.RDF_Triple.o))
                                       with
                                       | (RDF_Term.S_IRI p, RDF_Term.T_IRI
                                          d_range) ->
                                           (FStar_List_Tot_Base.mem d_range
                                              xsd_all_datatypes)
                                             &&
                                             (FStar_List_Tot_Base.existsb
                                                (fun t ->
                                                   (t.RDF_Triple.p = p) &&
                                                     (match t.RDF_Triple.o
                                                      with
                                                      | RDF_Term.T_Literal
                                                          lit ->
                                                          ((FStar_List_Tot_Base.mem
                                                              lit.RDF_Term.datatype
                                                              xsd_all_datatypes)
                                                             &&
                                                             (Prims.op_Negation
                                                                (lit.RDF_Term.datatype
                                                                   = d_range)))
                                                            &&
                                                            (Prims.op_Negation
                                                               (xsd_is_subtype
                                                                  lit.RDF_Term.datatype
                                                                  d_range))
                                                      | uu___9 -> false)) g)
                                       | (uu___9, uu___10) -> false)) g in
                             if has_dt_range_clash
                             then true
                             else
                               (let is_bottom_property p =
                                  (p = owl_bottomObjectProperty_iri) ||
                                    (p = owl_bottomDataProperty_iri) in
                                let is_existential_obligation t r =
                                  (RDF_Term.subject_eq t.RDF_Triple.s r) &&
                                    (((t.RDF_Triple.p =
                                         owl_someValuesFrom_iri)
                                        ||
                                        (t.RDF_Triple.p = owl_hasValue_iri))
                                       ||
                                       (((((t.RDF_Triple.p =
                                              owl_minCardinality_iri)
                                             ||
                                             (t.RDF_Triple.p =
                                                owl_minQualifiedCardinality_iri))
                                            ||
                                            (t.RDF_Triple.p =
                                               owl_cardinality_iri))
                                           ||
                                           (t.RDF_Triple.p =
                                              owl_qualifiedCardinality_iri))
                                          &&
                                          (match t.RDF_Triple.o with
                                           | RDF_Term.T_Literal l ->
                                               (normalize_integer_lexical
                                                  l.RDF_Term.lexical_form)
                                                 <> "0"
                                           | uu___10 -> false))) in
                                let has_bottom_property_clash =
                                  FStar_List_Tot_Base.existsb
                                    (fun op ->
                                       (((op.RDF_Triple.p =
                                            owl_onProperty_iri)
                                           &&
                                           (match op.RDF_Triple.o with
                                            | RDF_Term.T_IRI p ->
                                                is_bottom_property p
                                            | uu___10 -> false))
                                          &&
                                          (FStar_List_Tot_Base.existsb
                                             (fun t ->
                                                is_existential_obligation t
                                                  op.RDF_Triple.s) g))
                                         &&
                                         (FStar_List_Tot_Base.existsb
                                            (fun mem ->
                                               (mem.RDF_Triple.p =
                                                  RDFS_Closure.rdf_type)
                                                 &&
                                                 (RDF_Term.rdf_term_eq
                                                    mem.RDF_Triple.o
                                                    (RDF_Graph.subject_to_term
                                                       op.RDF_Triple.s))) g))
                                    g in
                                if has_bottom_property_clash
                                then true
                                else
                                  FStar_List_Tot_Base.existsb
                                    (fun svf ->
                                       ((svf.RDF_Triple.p =
                                           owl_someValuesFrom_iri)
                                          &&
                                          (RDF_Term.rdf_term_eq
                                             svf.RDF_Triple.o
                                             (RDF_Term.T_IRI
                                                RDFS_Closure.owl_Nothing)))
                                         &&
                                         (FStar_List_Tot_Base.existsb
                                            (fun mem ->
                                               (mem.RDF_Triple.p =
                                                  RDFS_Closure.rdf_type)
                                                 &&
                                                 (RDF_Term.rdf_term_eq
                                                    mem.RDF_Triple.o
                                                    (RDF_Graph.subject_to_term
                                                       svf.RDF_Triple.s))) g))
                                    g))))))))))
let regime_rdf : Prims.string= "RDF"
let regime_rdfs : Prims.string= "RDFS"
let regime_owl_rl : Prims.string= "OWL-RL"
let regime_owl_direct : Prims.string= "OWL-Direct"
let is_witness_bnode_label (b : RDF_Term.bnode_id) : Prims.bool=
  let lp = FStar_String.strlen "__rl_" in
  ((FStar_String.strlen b) >= lp) &&
    ((FStar_String.sub b Prims.int_zero lp) = "__rl_")
let subject_is_witness (s : RDF_Term.subject) : Prims.bool=
  match s with
  | RDF_Term.S_BNode b -> is_witness_bnode_label b
  | RDF_Term.S_IRI uu___ -> false
let term_is_witness (o : RDF_Term.rdf_term) : Prims.bool=
  match o with
  | RDF_Term.T_BNode b -> is_witness_bnode_label b
  | uu___ -> false
let triple_mentions_witness (t : RDF_Triple.triple) : Prims.bool=
  (subject_is_witness t.RDF_Triple.s) || (term_is_witness t.RDF_Triple.o)
let strip_comprehension_witnesses (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.filter
    (fun t -> Prims.op_Negation (triple_mentions_witness t)) g
let entailment_closure (regime : Prims.string) (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  if regime = regime_owl_rl
  then owl_rl_closure_with_reflexivity g fuel
  else
    if regime = regime_owl_direct
    then owl_rl_closure_with_reflexivity g fuel
    else
      if regime = regime_rdfs
      then RDFS_SchemaSplit.rdfs_closure_with_reflexivity_dispatch g fuel
      else
        if regime = regime_rdf then RDFS_Closure.rdfs_closure g fuel else g
let entailment_closure_for_query (regime : Prims.string)
  (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  strip_comprehension_witnesses (entailment_closure regime g fuel)
