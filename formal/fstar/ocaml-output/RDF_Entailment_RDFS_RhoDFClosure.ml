open Prims
let rho_df_closure_step_pre_dedup (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph=
  let ig = RDF_Indexed.build_indexed g in
  let g1 = RDFS_Closure.rdfs_rule_subPropertyOf g ig in
  let g2 = RDFS_Closure.rdfs_rule_domain g1 ig in
  let g3 = RDFS_Closure.rdfs_rule_range g2 ig in
  let g4 = RDFS_Closure.rdfs_rule_subClassOf g3 ig in
  let g5 = RDFS_Closure.rdfs_rule_subClassOf_trans g4 ig in
  RDFS_Closure.rdfs_rule_subPropertyOf_trans g5 ig
let rho_df_closure_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  RDF_Graph.graph_dedup_sort (rho_df_closure_step_pre_dedup g)
let rec rho_df_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let g' = rho_df_closure_step g in
      if (RDF_Graph.graph_len g') = (RDF_Graph.graph_len g)
      then g
      else rho_df_closure g' (n - Prims.int_one)
let rec rho_df_closure_iter (g : RDF_Graph.rdf_graph) (n : Prims.nat) :
  RDF_Graph.rdf_graph=
  if n = Prims.int_zero
  then g
  else rho_df_closure_iter (rho_df_closure_step g) (n - Prims.int_one)
type 'g rho_df_chain_canonical = unit
type 'g rho_df_chain_wf = unit
type 'g rdfs7_reaches_fact = unit
let f1_decl_triple (p : RDF_Term.wf_iri) : RDF_Triple.triple=
  {
    RDF_Triple.s = (RDF_Term.S_IRI p);
    RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_subPropertyOf;
    RDF_Triple.o =
      (RDF_Term.T_IRI RDF_Vocabulary_Axioms.i_rdfs_subPropertyOf)
  }
let f1_data_triple (p : RDF_Term.wf_iri) (a : RDF_Term.wf_iri) :
  RDF_Triple.triple=
  {
    RDF_Triple.s = (RDF_Term.S_IRI a);
    RDF_Triple.p = p;
    RDF_Triple.o = (RDF_Term.T_BNode "b1")
  }
let f1_witness (p : RDF_Term.wf_iri) (a : RDF_Term.wf_iri) :
  RDF_Graph.rdf_graph= [f1_decl_triple p; f1_data_triple p a]
let f1_bad_triple (a : RDF_Term.wf_iri) : RDF_Triple.triple=
  {
    RDF_Triple.s = (RDF_Term.S_IRI a);
    RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_subPropertyOf;
    RDF_Triple.o = (RDF_Term.T_BNode "b1")
  }
type 'c rho_df_step_saturated = unit
type 'c rho_df_subclass_subjects_iri = unit
let is_rho_df_object_ok (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_IRI uu___ -> true
  | RDF_Term.T_BNode uu___ -> true
  | uu___ -> false
let is_rho_df_frag_triple (t : RDF_Triple.triple) : Prims.bool=
  (is_rho_df_object_ok t.RDF_Triple.o) &&
    (if t.RDF_Triple.p = RDF_Vocabulary_Axioms.i_rdfs_subPropertyOf
     then RDF_Term.uu___is_T_IRI t.RDF_Triple.o
     else true)
let rec is_rho_df_frag (g : RDF_Graph.rdf_graph) : Prims.bool=
  match g with
  | [] -> true
  | t::tl -> (is_rho_df_frag_triple t) && (is_rho_df_frag tl)
