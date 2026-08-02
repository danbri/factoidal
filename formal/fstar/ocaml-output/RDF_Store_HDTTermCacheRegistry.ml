open Prims
let get_subjects_cache (path : Prims.string) :
  RDF_Term.subject RDF_Store_LazyTermCache.lazy_term_cache
    FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.Store.HDTTermCacheRegistry.get_subjects_cache"
let get_predicates_cache (path : Prims.string) :
  RDF_Term.wf_iri RDF_Store_LazyTermCache.lazy_term_cache
    FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.Store.HDTTermCacheRegistry.get_predicates_cache"
let get_objects_cache (path : Prims.string) :
  RDF_Term.rdf_term RDF_Store_LazyTermCache.lazy_term_cache
    FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.Store.HDTTermCacheRegistry.get_objects_cache"
let is_registered (path : Prims.string) : Prims.bool=
  failwith
    "Not yet implemented: RDF.Store.HDTTermCacheRegistry.is_registered"
