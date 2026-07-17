open Prims
let rename_bnode_label (prefix : Prims.string) (b : Prims.string) :
  Prims.string= FStar_String.concat "" [prefix; b]
let rename_subject (prefix : Prims.string) (s : RDF_Term.subject) :
  RDF_Term.subject=
  match s with
  | RDF_Term.S_BNode b -> RDF_Term.S_BNode (rename_bnode_label prefix b)
  | uu___ -> s
let rename_term (prefix : Prims.string) (t : RDF_Term.rdf_term) :
  RDF_Term.rdf_term=
  match t with
  | RDF_Term.T_BNode b -> RDF_Term.T_BNode (rename_bnode_label prefix b)
  | uu___ -> t
let rename_triple (prefix : Prims.string) (t : RDF_Triple.triple) :
  RDF_Triple.triple=
  {
    RDF_Triple.s = (rename_subject prefix t.RDF_Triple.s);
    RDF_Triple.p = (t.RDF_Triple.p);
    RDF_Triple.o = (rename_term prefix t.RDF_Triple.o)
  }
let rename_graph_bnodes (prefix : Prims.string) (g : RDF_Graph.rdf_graph) :
  RDF_Graph.rdf_graph= FStar_List_Tot_Base.map (rename_triple prefix) g
let rename_graph_name (prefix : Prims.string) (name : RDF_Term.iri) :
  RDF_Term.iri=
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
let rename_named_graph (prefix : Prims.string) (ng : RDF_Graph.named_graph) :
  RDF_Graph.named_graph=
  {
    RDF_Graph.ng_name = (rename_graph_name prefix ng.RDF_Graph.ng_name);
    RDF_Graph.ng_graph = (rename_graph_bnodes prefix ng.RDF_Graph.ng_graph)
  }
let rename_dataset_bnodes (prefix : Prims.string)
  (ds : RDF_Graph.rdf_dataset) : RDF_Graph.rdf_dataset=
  {
    RDF_Graph.ds_default =
      (rename_graph_bnodes prefix ds.RDF_Graph.ds_default);
    RDF_Graph.ds_named =
      (FStar_List_Tot_Base.map (rename_named_graph prefix)
         ds.RDF_Graph.ds_named)
  }
