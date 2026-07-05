open Prims
let rec extend_backend_bucket (iri_name : RDF_Graph_Executable.iri)
  (g : SPARQL11_Store.graph_backend)
  (acc : SPARQL11_Store.named_graph_backend Prims.list) :
  SPARQL11_Store.named_graph_backend Prims.list=
  match acc with
  | [] ->
      [{ SPARQL11_Store.ngb_name = iri_name; SPARQL11_Store.ngb_graph = g }]
  | ng::rest ->
      if ng.SPARQL11_Store.ngb_name = iri_name
      then
        let new_graph =
          match ng.SPARQL11_Store.ngb_graph with
          | SPARQL11_Store.GB_Union members ->
              SPARQL11_Store.GB_Union
                (FStar_List_Tot_Base.append members [g])
          | single -> SPARQL11_Store.GB_Union [single; g] in
        {
          SPARQL11_Store.ngb_name = (ng.SPARQL11_Store.ngb_name);
          SPARQL11_Store.ngb_graph = new_graph
        } :: rest
      else ng :: (extend_backend_bucket iri_name g rest)
let rec extend_backend_buckets
  (acc : SPARQL11_Store.named_graph_backend Prims.list)
  (incoming : SPARQL11_Store.named_graph_backend Prims.list) :
  SPARQL11_Store.named_graph_backend Prims.list=
  match incoming with
  | [] -> acc
  | ngb::rest ->
      extend_backend_buckets
        (extend_backend_bucket ngb.SPARQL11_Store.ngb_name
           ngb.SPARQL11_Store.ngb_graph acc) rest
let combine_dataset_backends
  (backends : SPARQL11_Store.dataset_backend Prims.list) :
  SPARQL11_Store.dataset_backend=
  match backends with
  | [] ->
      {
        SPARQL11_Store.dsb_default = (SPARQL11_Store.GB_Union []);
        SPARQL11_Store.dsb_named = []
      }
  | b::[] -> b
  | uu___ ->
      let dsb_default =
        SPARQL11_Store.GB_Union
          (FStar_List_Tot_Base.map (fun b -> b.SPARQL11_Store.dsb_default)
             backends) in
      let dsb_named =
        FStar_List_Tot_Base.fold_left
          (fun acc b -> extend_backend_buckets acc b.SPARQL11_Store.dsb_named)
          [] backends in
      {
        SPARQL11_Store.dsb_default = dsb_default;
        SPARQL11_Store.dsb_named = dsb_named
      }
