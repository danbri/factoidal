open Prims
(* __ONDISK_RUNTIME_REALISED__ *)
let ondisk_decode_subject_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (id : Prims.nat)
  : RDF_Graph_Executable.subject FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  try
    FStar_Pervasives_Native.Some
      (RDF_CottasStore.Cottas_ondisk_runtime.decode_subject_fast h id)
  with _ -> FStar_Pervasives_Native.None
let ondisk_decode_predicate_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (id : Prims.nat)
  : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  try
    FStar_Pervasives_Native.Some
      (RDF_CottasStore.Cottas_ondisk_runtime.decode_predicate_fast h id)
  with _ -> FStar_Pervasives_Native.None
let ondisk_decode_object_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (id : Prims.nat)
  : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  try
    FStar_Pervasives_Native.Some
      (RDF_CottasStore.Cottas_ondisk_runtime.decode_object_fast h id)
  with _ -> FStar_Pervasives_Native.None
let ondisk_decode_graph_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (id : Prims.nat)
  : RDF_Graph_Executable.iri FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  try
    FStar_Pervasives_Native.Some
      (RDF_CottasStore.Cottas_ondisk_runtime.decode_graph_fast h id)
  with _ -> FStar_Pervasives_Native.None
let ondisk_encode_subject_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (v : RDF_Graph_Executable.subject)
  : Prims.nat FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  RDF_CottasStore.Cottas_ondisk_runtime.encode_subject_fast h v
let ondisk_encode_predicate_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (v : RDF_Graph_Executable.wf_iri)
  : Prims.nat FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  RDF_CottasStore.Cottas_ondisk_runtime.encode_predicate_fast h v
let ondisk_encode_object_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (v : RDF_Graph_Executable.rdf_term)
  : Prims.nat FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  RDF_CottasStore.Cottas_ondisk_runtime.encode_object_fast h v
let ondisk_encode_graph_indexed (ds : RDF_CottasStore.cottas_ondisk_store)
  (v : RDF_Graph_Executable.iri)
  : Prims.nat FStar_Pervasives_Native.option =
  let h = ds.RDF_CottasStore.cods_handle in
  RDF_CottasStore.Cottas_ondisk_runtime.encode_graph_fast h v
let ondisk_decode_subject_via_registry (path : Prims.string) (id : Prims.nat)
  : RDF_Graph_Executable.subject FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_subjects_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.decode_by_id d id
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ondisk_decode_predicate_via_registry (path : Prims.string) (id : Prims.nat)
  : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_predicates_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.decode_by_id d id
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ondisk_decode_object_via_registry (path : Prims.string) (id : Prims.nat)
  : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_objects_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.decode_by_id d id
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ondisk_decode_graph_via_registry (path : Prims.string) (id : Prims.nat)
  : Prims.string FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_graphs_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.decode_by_id d id
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ondisk_encode_subject_via_registry (path : Prims.string) (v : RDF_Graph_Executable.subject)
  : Prims.nat FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_subjects_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.encode_by_key d (RDF_CottasStore.subject_to_revmap_key v)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ondisk_encode_predicate_via_registry (path : Prims.string) (v : RDF_Graph_Executable.wf_iri)
  : Prims.nat FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_predicates_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.encode_by_key d (RDF_CottasStore.iri_to_revmap_key v)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ondisk_encode_object_via_registry (path : Prims.string) (v : RDF_Graph_Executable.rdf_term)
  : Prims.nat FStar_Pervasives_Native.option =
  match RDF_CottasStore_LazyDictRegistry.get_objects_lazy path with
  | FStar_Pervasives_Native.Some d ->
    RDF_CottasStore_LazyDict.encode_by_key d (RDF_CottasStore.object_to_revmap_key v)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
