open Prims
let merge_pair (acc : RDF_Graph_Executable.rdf_dataset)
  (extra : RDF_Graph_Executable.rdf_dataset) :
  RDF_Graph_Executable.rdf_dataset=
  {
    RDF_Graph_Executable.ds_default =
      (RDF_List_Helpers.append_tr acc.RDF_Graph_Executable.ds_default
         extra.RDF_Graph_Executable.ds_default);
    RDF_Graph_Executable.ds_named =
      (RDF_List_Helpers.append_tr acc.RDF_Graph_Executable.ds_named
         extra.RDF_Graph_Executable.ds_named)
  }
let merge_datasets (base : RDF_Graph_Executable.rdf_dataset)
  (extras : RDF_Graph_Executable.rdf_dataset Prims.list) :
  RDF_Graph_Executable.rdf_dataset=
  FStar_List_Tot_Base.fold_left merge_pair base extras
type resolved_quad =
  {
  rq_triple: RDF_Graph_Executable.triple ;
  rq_graph: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkresolved_quad__item__rq_triple (projectee : resolved_quad) :
  RDF_Graph_Executable.triple=
  match projectee with | { rq_triple; rq_graph;_} -> rq_triple
let __proj__Mkresolved_quad__item__rq_graph (projectee : resolved_quad) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { rq_triple; rq_graph;_} -> rq_graph
let rec extend_named_bucket (iri : Prims.string)
  (t : RDF_Graph_Executable.triple)
  (acc : RDF_Graph_Executable.named_graph Prims.list) :
  RDF_Graph_Executable.named_graph Prims.list=
  match acc with
  | [] ->
      [{
         RDF_Graph_Executable.ng_name = iri;
         RDF_Graph_Executable.ng_graph = [t]
       }]
  | ng::rest ->
      if ng.RDF_Graph_Executable.ng_name = iri
      then
        {
          RDF_Graph_Executable.ng_name = (ng.RDF_Graph_Executable.ng_name);
          RDF_Graph_Executable.ng_graph = (t ::
            (ng.RDF_Graph_Executable.ng_graph))
        } :: rest
      else ng :: (extend_named_bucket iri t rest)
let rec bucket_quads_acc
  (default_acc : RDF_Graph_Executable.triple Prims.list)
  (named_acc : RDF_Graph_Executable.named_graph Prims.list)
  (quads : resolved_quad Prims.list) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list)=
  match quads with
  | [] -> (default_acc, named_acc)
  | q::rest ->
      let t = q.rq_triple in
      (match q.rq_graph with
       | FStar_Pervasives_Native.None ->
           bucket_quads_acc (t :: default_acc) named_acc rest
       | FStar_Pervasives_Native.Some g_iri ->
           bucket_quads_acc default_acc
             (extend_named_bucket g_iri t named_acc) rest)
let reverse_named_graph (ng : RDF_Graph_Executable.named_graph) :
  RDF_Graph_Executable.named_graph=
  {
    RDF_Graph_Executable.ng_name = (ng.RDF_Graph_Executable.ng_name);
    RDF_Graph_Executable.ng_graph =
      (FStar_List_Tot_Base.rev ng.RDF_Graph_Executable.ng_graph)
  }
let bucket_quads (quads : resolved_quad Prims.list) :
  RDF_Graph_Executable.rdf_dataset=
  let uu___ = bucket_quads_acc [] [] quads in
  match uu___ with
  | (default_rev, named_rev) ->
      let default_g = FStar_List_Tot_Base.rev default_rev in
      let named_gs = FStar_List_Tot_Base.map reverse_named_graph named_rev in
      {
        RDF_Graph_Executable.ds_default = default_g;
        RDF_Graph_Executable.ds_named = named_gs
      }
