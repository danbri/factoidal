open Prims
type graph_ref = RDF_Graph_Executable.iri
let graphs (ds : RDF_Graph_Executable.rdf_dataset) :
  (graph_ref * RDF_Graph_Executable.rdf_graph) Prims.list=
  FStar_List_Tot_Base.map
    (fun ng ->
       ((ng.RDF_Graph_Executable.ng_name),
         (ng.RDF_Graph_Executable.ng_graph)))
    ds.RDF_Graph_Executable.ds_named
let component_of (ds : RDF_Graph_Executable.rdf_dataset) (name : graph_ref) :
  RDF_Graph_Executable.rdf_graph FStar_Pervasives_Native.option=
  RDF_Graph_Executable.lookup_named_graph name
    ds.RDF_Graph_Executable.ds_named
