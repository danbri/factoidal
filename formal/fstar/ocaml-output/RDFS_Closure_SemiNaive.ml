open Prims
let sn_rdfs4a (acc : RDF_Graph.rdf_graph) (ig : RDF_Indexed.indexed_graph)
  (delta : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (RDFS_Closure.rdfs4a_step ig) acc delta
let sn_rdfs4b (acc : RDF_Graph.rdf_graph) (ig : RDF_Indexed.indexed_graph)
  (delta : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (RDFS_Closure.rdfs4b_step ig) acc delta
let sn_rdfs8 (acc : RDF_Graph.rdf_graph) (ig : RDF_Indexed.indexed_graph)
  (delta : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (RDFS_Closure.rdfs8_step ig) acc delta
let sn_rdfs13 (acc : RDF_Graph.rdf_graph) (ig : RDF_Indexed.indexed_graph)
  (delta : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left (RDFS_Closure.rdfs13_step ig) acc delta
let sn_axiom_rows (acc : RDF_Graph.rdf_graph)
  (ig : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let a1 = RDFS_Closure.rdfs_rule_recognized_datatypes acc ig in
  RDFS_Closure.rdfs_rule_container_membership a1 ig
let sn_rdfs9 (acc : RDF_Graph.rdf_graph)
  (ig_probe : RDF_Indexed.indexed_graph) (driver : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc1 t ->
       if t.RDF_Triple.p = RDFS_Closure.rdf_type
       then
         match t.RDF_Triple.o with
         | RDF_Term.T_IRI class_iri ->
             let super_classes =
               RDF_Indexed.find_objects_indexed ig_probe
                 (RDF_Term.S_IRI class_iri) RDFS_Closure.rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 b_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = RDFS_Closure.rdf_type;
                      RDF_Triple.o = b_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc1
               super_classes
         | uu___ -> acc1
       else acc1) acc driver
let sn_rdfs11 (acc : RDF_Graph.rdf_graph)
  (ig_probe : RDF_Indexed.indexed_graph) (driver : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc1 t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subClassOf
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some b_subj ->
             let supers =
               RDF_Indexed.find_objects_indexed ig_probe b_subj
                 RDFS_Closure.rdfs_subClassOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 c_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = RDFS_Closure.rdfs_subClassOf;
                      RDF_Triple.o = c_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc1 supers
         | FStar_Pervasives_Native.None -> acc1
       else acc1) acc driver
let sn_rdfs5 (acc : RDF_Graph.rdf_graph)
  (ig_probe : RDF_Indexed.indexed_graph) (driver : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  FStar_List_Tot_Base.fold_left
    (fun acc1 t ->
       if t.RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf
       then
         match RDF_Graph.term_to_subject t.RDF_Triple.o with
         | FStar_Pervasives_Native.Some q_subj ->
             let supers =
               RDF_Indexed.find_objects_indexed ig_probe q_subj
                 RDFS_Closure.rdfs_subPropertyOf in
             FStar_List_Tot_Base.fold_left
               (fun acc2 r_term ->
                  let new_t =
                    {
                      RDF_Triple.s = (t.RDF_Triple.s);
                      RDF_Triple.p = RDFS_Closure.rdfs_subPropertyOf;
                      RDF_Triple.o = r_term
                    } in
                  RDF_Graph.add_triple_unchecked acc2 new_t) acc1 supers
         | FStar_Pervasives_Native.None -> acc1
       else acc1) acc driver
let sn_rdfs7 (acc : RDF_Graph.rdf_graph)
  (ig_decls : RDF_Indexed.indexed_graph)
  (ig_data : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let decls =
    RDF_Indexed.bucket_lookup ig_decls.RDF_Indexed.ig_pred
      RDFS_Closure.rdfs_subPropertyOf in
  FStar_List_Tot_Base.fold_left
    (fun acc1 decl ->
       match ((decl.RDF_Triple.s), (decl.RDF_Triple.o)) with
       | (RDF_Term.S_IRI p, RDF_Term.T_IRI q) ->
           let matching =
             RDF_Indexed.bucket_lookup ig_data.RDF_Indexed.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                let new_t =
                  {
                    RDF_Triple.s = (t.RDF_Triple.s);
                    RDF_Triple.p = q;
                    RDF_Triple.o = (t.RDF_Triple.o)
                  } in
                RDF_Graph.add_triple_unchecked acc2 new_t) acc1 matching
       | (uu___, uu___1) -> acc1) acc decls
let sn_rdfs2 (acc : RDF_Graph.rdf_graph)
  (ig_decls : RDF_Indexed.indexed_graph)
  (ig_data : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let decls =
    RDF_Indexed.bucket_lookup ig_decls.RDF_Indexed.ig_pred
      RDFS_Closure.rdfs_domain in
  FStar_List_Tot_Base.fold_left
    (fun acc1 decl ->
       match decl.RDF_Triple.s with
       | RDF_Term.S_IRI p ->
           let matching =
             RDF_Indexed.bucket_lookup ig_data.RDF_Indexed.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                let new_t =
                  {
                    RDF_Triple.s = (t.RDF_Triple.s);
                    RDF_Triple.p = RDFS_Closure.rdf_type;
                    RDF_Triple.o = (decl.RDF_Triple.o)
                  } in
                RDF_Graph.add_triple_unchecked acc2 new_t) acc1 matching
       | uu___ -> acc1) acc decls
let sn_rdfs3 (acc : RDF_Graph.rdf_graph)
  (ig_decls : RDF_Indexed.indexed_graph)
  (ig_data : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let decls =
    RDF_Indexed.bucket_lookup ig_decls.RDF_Indexed.ig_pred
      RDFS_Closure.rdfs_range in
  FStar_List_Tot_Base.fold_left
    (fun acc1 decl ->
       match decl.RDF_Triple.s with
       | RDF_Term.S_IRI p ->
           let matching =
             RDF_Indexed.bucket_lookup ig_data.RDF_Indexed.ig_pred p in
           FStar_List_Tot_Base.fold_left
             (fun acc2 t ->
                match RDF_Graph.term_to_subject t.RDF_Triple.o with
                | FStar_Pervasives_Native.Some b_subj ->
                    let new_t =
                      {
                        RDF_Triple.s = b_subj;
                        RDF_Triple.p = RDFS_Closure.rdf_type;
                        RDF_Triple.o = (decl.RDF_Triple.o)
                      } in
                    RDF_Graph.add_triple_unchecked acc2 new_t
                | FStar_Pervasives_Native.None -> acc2) acc1 matching
       | uu___ -> acc1) acc decls
let semi_naive_round (full : RDF_Graph.rdf_graph)
  (delta : RDF_Graph.rdf_graph) (ig_full : RDF_Indexed.indexed_graph)
  (ig_delta : RDF_Indexed.indexed_graph) : RDF_Graph.rdf_graph=
  let a1 = sn_rdfs7 full ig_delta ig_full in
  let a2 = sn_rdfs7 a1 ig_full ig_delta in
  let a3 = sn_rdfs2 a2 ig_delta ig_full in
  let a4 = sn_rdfs2 a3 ig_full ig_delta in
  let a5 = sn_rdfs3 a4 ig_delta ig_full in
  let a6 = sn_rdfs3 a5 ig_full ig_delta in
  let a7 = sn_rdfs9 a6 ig_full delta in
  let a8 = sn_rdfs9 a7 ig_delta full in
  let a9 = sn_rdfs11 a8 ig_full delta in
  let a10 = sn_rdfs11 a9 ig_delta full in
  let a11 = sn_rdfs5 a10 ig_full delta in
  let a12 = sn_rdfs5 a11 ig_delta full in
  let a13 = sn_rdfs8 a12 ig_full delta in
  let a14 = sn_rdfs13 a13 ig_full delta in
  let a15 = sn_rdfs4a a14 ig_full delta in
  let a16 = sn_rdfs4b a15 ig_full delta in RDF_Graph.graph_dedup_sort a16
let rec semi_naive_loop (full : RDF_Graph.rdf_graph)
  (delta : RDF_Graph.rdf_graph) (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> full
  | n ->
      if Prims.uu___is_Nil delta
      then full
      else
        (let ig_full = RDF_Indexed.build_indexed full in
         let ig_delta = RDF_Indexed.build_indexed delta in
         let next = semi_naive_round full delta ig_full ig_delta in
         if (RDF_Graph.graph_len next) = (RDF_Graph.graph_len full)
         then full
         else
           semi_naive_loop next (RDF_Graph.sorted_diff next full)
             (n - Prims.int_one))
let rdfs_closure_semi_naive (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let remaining =
        if n > Prims.int_zero then n - Prims.int_one else Prims.int_zero in
      let ig0 = RDF_Indexed.build_indexed g in
      let seeded = RDF_Graph.graph_dedup_sort (sn_axiom_rows g ig0) in
      let first = RDFS_Closure.rdfs_closure_step seeded in
      if (RDF_Graph.graph_len first) = (RDF_Graph.graph_len seeded)
      then first
      else
        semi_naive_loop first (RDF_Graph.sorted_diff first seeded) remaining
let rdfs_closure_checked (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  let fast = rdfs_closure_semi_naive g fuel in
  let probe = RDFS_Closure.rdfs_closure_step fast in
  if (RDF_Graph.graph_len probe) = (RDF_Graph.graph_len fast)
  then fast
  else RDFS_Closure.rdfs_closure g fuel
let rdfs_closure_with_reflexivity_checked (g : RDF_Graph.rdf_graph)
  (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  let closed = rdfs_closure_checked g fuel in
  let refl_axioms = RDFS_Closure.rdfs_reflexivity_axioms closed in
  let with_refl = RDF_Graph.add_triples_if_new_bulk closed refl_axioms in
  rdfs_closure_checked with_refl fuel
