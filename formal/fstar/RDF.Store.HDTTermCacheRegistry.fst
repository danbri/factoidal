module RDF.Store.HDTTermCacheRegistry

open FStar.All
open RDF.Graph.Executable
open RDF.Store.LazyTermCache

// Path-keyed registry of per-HDT-handle LazyTermCaches.
//
// Mirrors `RDF.CottasStore.LazyDictRegistry` (#254 Commit 2b) for
// the HDT runtime side per the #253 retirement plan:
//
//   docs/designissues/2026-05-13-issue-253-hdt-runtime-retirement-plan.md
//
// The HDT-specific abstraction is `lazy_term_cache` (2 directions:
// id <-> typed value) rather than `lazy_dict` (4 directions). The
// Front-Coded HDT dictionary IS the canonical form; there is no
// separate raw column-token view to track.
//
// Registry storage is OCaml-side: a `(string, _) Hashtbl.t` indexed
// by HDT artifact path. Realisation patch
// (hdt_term_cache_registry_runtime.sh) populates the registry when
// the OCaml-side `Ballyhoo_hdt_runtime.hdt_open_graph_store` builds
// a fresh handle, and queries it from the per-direction `get_*_cache`
// `assume val`s below.
//
// Universe safety: `lazy_term_cache T` appears only in return-position
// of `assume val`s here, never as a record field. Same protection as
// LazyDictRegistry against the SPARQL11.Store mutual-recursion
// universe cascade.

// Get the lazy subjects term-cache for a given HDT handle's path.
// Returns None if no handle is open at that path.
assume val get_subjects_cache
  (path : string) : ML (option (lazy_term_cache subject))

// Predicates term-cache.
assume val get_predicates_cache
  (path : string) : ML (option (lazy_term_cache wf_iri))

// Objects term-cache.
assume val get_objects_cache
  (path : string) : ML (option (lazy_term_cache rdf_term))

// Has the registry been populated for this path?
assume val is_registered (path : string) : ML bool
