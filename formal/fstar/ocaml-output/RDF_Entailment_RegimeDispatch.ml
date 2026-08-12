open Prims
let regime_x_rdfscore : Prims.string= "x-rdfscore"
let regime_x_rdfsplus : Prims.string= "x-rdfsplus"
let entailment_closure_for_query_ext (regime : Prims.string)
  (g : RDF_Graph.rdf_graph) (fuel : Prims.nat) : RDF_Graph.rdf_graph=
  if regime = regime_x_rdfscore
  then RDF_Entailment_RDFS_RhoDFClosure.rho_df_closure g fuel
  else
    if regime = regime_x_rdfsplus
    then RDF_Entailment_RDFSPlus.rdfs_plus_closure g fuel
    else OWL_Closure.entailment_closure_for_query regime g fuel
