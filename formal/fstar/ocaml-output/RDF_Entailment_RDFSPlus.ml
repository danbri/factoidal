open Prims
let rdfs_plus_step_pre_dedup (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  let g0 = RDFS_Closure.rdfs_closure_step g in
  let ig = RDF_Indexed.build_indexed g0 in
  let g1 = OWL_Closure.owl_rule_equivalent_class g0 ig in
  let g2 = OWL_Closure.owl_rule_equivalent_property g1 ig in
  let g3 = OWL_Closure.owl_rule_symmetric_property g2 ig in
  let g4 = OWL_Closure.owl_rule_transitive_property g3 ig in
  let g5 = OWL_Closure.owl_rule_inverse_of g4 ig in
  let g6 = OWL_Closure.owl_rule_inverseOf_domain_range_flip g5 ig in
  let g7 = OWL_Closure.owl_rule_functional g6 ig in
  let g8 = OWL_Closure.owl_rule_inverse_functional g7 ig in
  let g9 = OWL_Closure.owl_rule_sameAs_symmetry g8 ig in
  let g10 = OWL_Closure.owl_rule_sameAs_transitivity g9 ig in
  let g11 = OWL_Closure.owl_rule_sameAs_replace_subject g10 ig in
  let g12 = OWL_Closure.owl_rule_sameAs_replace_object g11 ig in
  OWL_Closure.owl_rule_sameAs_replace_predicate g12 ig
let rdfs_plus_step (g : RDF_Graph.rdf_graph) : RDF_Graph.rdf_graph=
  RDF_Graph.graph_dedup_sort (rdfs_plus_step_pre_dedup g)
let rec rdfs_plus_closure (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) :
  RDF_Graph.rdf_graph=
  match fuel with
  | uu___ when uu___ = Prims.int_zero -> g
  | n ->
      let g' = rdfs_plus_step g in
      if (RDF_Graph.graph_len g') = (RDF_Graph.graph_len g)
      then g
      else rdfs_plus_closure g' (n - Prims.int_one)
