module RDF.CottasStore.LazyDictRegistry

open FStar.All
open RDF.Graph.Executable
open RDF.CottasStore.LazyDict

// Path-keyed registry of per-cottas-handle LazyDicts.
//
// Background: #254 Commit 2a attempted to put four `lazy_dict T`
// fields directly on `cottas_ondisk_handle`. That cascaded a
// universe-polymorphism constraint through SPARQL11.Store's
// mutually-recursive `eval_*_backend` definitions, manifesting as
//   Error 89: incompatible universe sets for eval_pattern_backend
//   and eval_select_query_backend_bgp
// — see commit f442c13 (revert).
//
// The fix per #254 plan risk register: expose the lazy_dicts via
// path-keyed lookup `assume val`s instead of record fields. The
// abstract type `lazy_dict T` appears only in return-position of
// `assume val`s, not as a field of a noeq record — so its universe
// parameters never propagate into a record's structural-equality
// type-class inference, and SPARQL11.Store's mutual block stays
// universe-monomorphic.
//
// The registry lives entirely in OCaml as a `(string, _) Hashtbl.t`
// indexed by the handle's `coh_path`. The realisation patch
// (cottas_lazy_dict_registry_runtime.sh) populates the registry
// when `cottas_ondisk_open` builds a new handle, and queries it
// from the per-direction `get_*_lazy` functions below.

// Get the lazy subjects dict for a given cottas handle's path.
// Returns None if no handle is open at that path (e.g. before
// `cottas_ondisk_open` has been called for it).
assume val get_subjects_lazy
  (path : string) : ML (option (lazy_dict subject))

// Predicates lazy_dict.
assume val get_predicates_lazy
  (path : string) : ML (option (lazy_dict wf_iri))

// Objects lazy_dict.
assume val get_objects_lazy
  (path : string) : ML (option (lazy_dict rdf_term))

// Graphs lazy_dict.
assume val get_graphs_lazy
  (path : string) : ML (option (lazy_dict iri))

// Has the registry been populated for this path? Cheap check used
// by consumers to decide whether to populate-from-scratch or use
// the cached lazy_dicts.
assume val is_registered (path : string) : ML bool
