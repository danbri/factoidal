open Prims
type graph_ref = RDF_Term.iri
let graphs (ds : RDF_Graph.rdf_dataset) :
  (graph_ref * RDF_Graph.rdf_graph) Prims.list=
  FStar_List_Tot_Base.map
    (fun ng -> ((ng.RDF_Graph.ng_name), (ng.RDF_Graph.ng_graph)))
    ds.RDF_Graph.ds_named
let component_of (ds : RDF_Graph.rdf_dataset) (name : graph_ref) :
  RDF_Graph.rdf_graph FStar_Pervasives_Native.option=
  RDF_Graph.lookup_named_graph name ds.RDF_Graph.ds_named
