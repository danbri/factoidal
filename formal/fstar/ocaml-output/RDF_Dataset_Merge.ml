open Prims
let rename_bnode_label (prefix : Prims.string) (b : Prims.string) :
  Prims.string= FStar_String.concat "" [prefix; b]
let rename_subject (prefix : Prims.string) (s : RDF_Graph_Executable.subject)
  : RDF_Graph_Executable.subject=
  match s with
  | RDF_Graph_Executable.S_BNode b ->
      RDF_Graph_Executable.S_BNode (rename_bnode_label prefix b)
  | uu___ -> s
let rename_term (prefix : Prims.string) (t : RDF_Graph_Executable.rdf_term) :
  RDF_Graph_Executable.rdf_term=
  match t with
  | RDF_Graph_Executable.T_BNode b ->
      RDF_Graph_Executable.T_BNode (rename_bnode_label prefix b)
  | uu___ -> t
let rename_triple (prefix : Prims.string) (t : RDF_Graph_Executable.triple) :
  RDF_Graph_Executable.triple=
  {
    RDF_Graph_Executable.s = (rename_subject prefix t.RDF_Graph_Executable.s);
    RDF_Graph_Executable.p = (t.RDF_Graph_Executable.p);
    RDF_Graph_Executable.o = (rename_term prefix t.RDF_Graph_Executable.o)
  }
let rename_graph_bnodes (prefix : Prims.string)
  (g : RDF_Graph_Executable.rdf_graph) : RDF_Graph_Executable.rdf_graph=
  FStar_List_Tot_Base.map (rename_triple prefix) g
let rename_graph_name (prefix : Prims.string)
  (name : RDF_Graph_Executable.iri) : RDF_Graph_Executable.iri=
  if (FStar_String.strlen name) >= (Prims.of_int (2))
  then
    (if (FStar_String.sub name Prims.int_zero (Prims.of_int (2))) = "_:"
     then
       FStar_String.concat ""
         ["_:";
         prefix;
         FStar_String.sub name (Prims.of_int (2))
           ((FStar_String.strlen name) - (Prims.of_int (2)))]
     else name)
  else name
let rename_named_graph (prefix : Prims.string)
  (ng : RDF_Graph_Executable.named_graph) : RDF_Graph_Executable.named_graph=
  {
    RDF_Graph_Executable.ng_name =
      (rename_graph_name prefix ng.RDF_Graph_Executable.ng_name);
    RDF_Graph_Executable.ng_graph =
      (rename_graph_bnodes prefix ng.RDF_Graph_Executable.ng_graph)
  }
let rename_dataset_bnodes (prefix : Prims.string)
  (ds : RDF_Graph_Executable.rdf_dataset) : RDF_Graph_Executable.rdf_dataset=
  {
    RDF_Graph_Executable.ds_default =
      (rename_graph_bnodes prefix ds.RDF_Graph_Executable.ds_default);
    RDF_Graph_Executable.ds_named =
      (FStar_List_Tot_Base.map (rename_named_graph prefix)
         ds.RDF_Graph_Executable.ds_named)
  }
