open Prims
let eval_select_query_owl (q : SPARQL11_Algebra.query)
  (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) :
  SPARQL11_Algebra.solution_sequence=
  SPARQL11_Algebra.eval_select_query (OWL_QueryRewrite.rewrite_query q) g ds
let eval_ask_query_owl (q : SPARQL11_Algebra.query)
  (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : Prims.bool=
  SPARQL11_Algebra.eval_ask_query (OWL_QueryRewrite.rewrite_query q) g ds
let eval_construct_query_owl (q : SPARQL11_Algebra.query)
  (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) :
  RDF_Graph_Executable.triple Prims.list=
  SPARQL11_Algebra.eval_construct_query (OWL_QueryRewrite.rewrite_query q) g
    ds
