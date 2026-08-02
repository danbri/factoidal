open Prims
(* __LAZY_DICT_REGISTRY_RUNTIME_APPLIED__ *)
type registry_entry = {
  re_subjects   : RDF_Graph_Executable.subject RDF_CottasStore_LazyDict.lazy_dict;
  re_predicates : RDF_Graph_Executable.wf_iri  RDF_CottasStore_LazyDict.lazy_dict;
  re_objects    : RDF_Graph_Executable.rdf_term RDF_CottasStore_LazyDict.lazy_dict;
  re_graphs     : Prims.string RDF_CottasStore_LazyDict.lazy_dict;
}

let registry : (Prims.string, registry_entry) Stdlib.Hashtbl.t =
  Stdlib.Hashtbl.create 17

(* Called by the cottas_ondisk_runtime realisation when a fresh
   handle is opened. Populate thunks here just wrap the already-
   built eager dicts — true lazy-on-disk parquet population is a
   future-commit upgrade once the consumer migration validates the
   shape. *)
let register_for_path
  (p : Prims.string)
  (subj_pop : unit -> (Z.t * RDF_Graph_Executable.subject * Prims.string) Prims.list)
  (pred_pop : unit -> (Z.t * RDF_Graph_Executable.wf_iri * Prims.string) Prims.list)
  (obj_pop  : unit -> (Z.t * RDF_Graph_Executable.rdf_term * Prims.string) Prims.list)
  (graph_pop : unit -> (Z.t * Prims.string * Prims.string) Prims.list)
  (subj_key : RDF_Graph_Executable.subject -> Prims.string)
  (pred_key : RDF_Graph_Executable.wf_iri -> Prims.string)
  (obj_key  : RDF_Graph_Executable.rdf_term -> Prims.string)
  (graph_key : Prims.string -> Prims.string)
  : unit =
  let entry = {
    re_subjects   = RDF_CottasStore_LazyDict.mk_lazy_dict subj_pop  subj_key;
    re_predicates = RDF_CottasStore_LazyDict.mk_lazy_dict pred_pop  pred_key;
    re_objects    = RDF_CottasStore_LazyDict.mk_lazy_dict obj_pop   obj_key;
    re_graphs     = RDF_CottasStore_LazyDict.mk_lazy_dict graph_pop graph_key;
  } in
  Stdlib.Hashtbl.replace registry p entry
let get_subjects_lazy (p : Prims.string) : RDF_Graph_Executable.subject RDF_CottasStore_LazyDict.lazy_dict FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_subjects
  | None       -> FStar_Pervasives_Native.None
let get_predicates_lazy (p : Prims.string) : RDF_Graph_Executable.wf_iri RDF_CottasStore_LazyDict.lazy_dict FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_predicates
  | None       -> FStar_Pervasives_Native.None
let get_objects_lazy (p : Prims.string) : RDF_Graph_Executable.rdf_term RDF_CottasStore_LazyDict.lazy_dict FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_objects
  | None       -> FStar_Pervasives_Native.None
let get_graphs_lazy (p : Prims.string) : Prims.string RDF_CottasStore_LazyDict.lazy_dict FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_graphs
  | None       -> FStar_Pervasives_Native.None
let is_registered (p : Prims.string) : Prims.bool =
  Stdlib.Hashtbl.mem registry p
