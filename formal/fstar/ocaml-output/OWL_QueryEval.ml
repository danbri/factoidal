open Prims
let eval_select_query_owl (q : SPARQL11_Algebra.query)
  (g : RDF_Graph.rdf_graph) (ds : RDF_Graph.rdf_dataset) :
  SPARQL11_Algebra.solution_sequence=
  SPARQL11_Algebra.strip_rewrite_internal_vars
    (SPARQL11_Algebra.eval_select_query (OWL_QueryRewrite.rewrite_query q) g
       ds)
let eval_ask_query_owl (q : SPARQL11_Algebra.query) (g : RDF_Graph.rdf_graph)
  (ds : RDF_Graph.rdf_dataset) : Prims.bool=
  SPARQL11_Algebra.eval_ask_query (OWL_QueryRewrite.rewrite_query q) g ds
let eval_construct_query_owl (q : SPARQL11_Algebra.query)
  (g : RDF_Graph.rdf_graph) (ds : RDF_Graph.rdf_dataset) :
  RDF_Triple.triple Prims.list=
  SPARQL11_Algebra.eval_construct_query (OWL_QueryRewrite.rewrite_query q) g
    ds
