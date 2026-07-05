open Prims
(* __HDT_TERM_CACHE_REGISTRY_RUNTIME_APPLIED__ *)
type registry_entry = {
  re_subjects   : RDF_Graph_Executable.subject RDF_Store_LazyTermCache.lazy_term_cache;
  re_predicates : RDF_Graph_Executable.wf_iri  RDF_Store_LazyTermCache.lazy_term_cache;
  re_objects    : RDF_Graph_Executable.rdf_term RDF_Store_LazyTermCache.lazy_term_cache;
}

let registry : (Prims.string, registry_entry) Stdlib.Hashtbl.t =
  Stdlib.Hashtbl.create 17

(* Called by the HDT runtime realisation when a fresh handle is
   opened. Populate thunks wrap the already-built dicts. *)
let register_for_path
  (p : Prims.string)
  (subj_pop : unit -> (Z.t * RDF_Graph_Executable.subject) Prims.list)
  (pred_pop : unit -> (Z.t * RDF_Graph_Executable.wf_iri) Prims.list)
  (obj_pop  : unit -> (Z.t * RDF_Graph_Executable.rdf_term) Prims.list)
  (subj_key : RDF_Graph_Executable.subject -> Prims.string)
  (pred_key : RDF_Graph_Executable.wf_iri -> Prims.string)
  (obj_key  : RDF_Graph_Executable.rdf_term -> Prims.string)
  : unit =
  let entry = {
    re_subjects   = RDF_Store_LazyTermCache.mk_lazy_term_cache subj_pop subj_key;
    re_predicates = RDF_Store_LazyTermCache.mk_lazy_term_cache pred_pop pred_key;
    re_objects    = RDF_Store_LazyTermCache.mk_lazy_term_cache obj_pop  obj_key;
  } in
  Stdlib.Hashtbl.replace registry p entry
let get_subjects_cache (p : Prims.string) : RDF_Graph_Executable.subject RDF_Store_LazyTermCache.lazy_term_cache FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_subjects
  | None       -> FStar_Pervasives_Native.None
let get_predicates_cache (p : Prims.string) : RDF_Graph_Executable.wf_iri RDF_Store_LazyTermCache.lazy_term_cache FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_predicates
  | None       -> FStar_Pervasives_Native.None
let get_objects_cache (p : Prims.string) : RDF_Graph_Executable.rdf_term RDF_Store_LazyTermCache.lazy_term_cache FStar_Pervasives_Native.option =
  match Stdlib.Hashtbl.find_opt registry p with
  | Some entry -> FStar_Pervasives_Native.Some entry.re_objects
  | None       -> FStar_Pervasives_Native.None
let is_registered (p : Prims.string) : Prims.bool =
  Stdlib.Hashtbl.mem registry p
