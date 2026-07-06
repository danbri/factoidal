module RDF.Store.LazyTermCache

open FStar.All

// A lazy-populate term-ID cache for HDT-style backends.
//
// Bundles two indexed views over a backend's term inventory:
//   id  -> typed value   (subject / wf_iri / rdf_term)
//   typed value -> id    (reverse direction, requires eqtype)
//
// All entries populate together on the first lookup of any kind.
// Realised in OCaml as two Hashtbl.t + a populate thunk + a loaded
// flag + a mutex.
//
// Issue #253 (ballyhoo_hdt_runtime retirement) — originally scoped
// to replace the 555-line ballyhoo_hdt_runtime.sh patch's
// hand-written term-ID allocator + Hashtbl pair with an F*-spec'd
// populate-on-demand cache. Design plan:
//   docs/designissues/2026-05-13-issue-253-hdt-runtime-retirement-plan.md
//
// 2026-07-06 (HDT program stage 4): #253 closed a different way —
// ballyhoo_hdt_runtime.sh is deleted and Parser.BallyhooHDT calls
// the verified HDT.Container/HDT.Dictionary/HDT.Triples readers
// directly, with no cache in the path. This module is currently
// UNUSED by the HDT backend; it remains as a candidate memoization
// seam for the stage-5 perf pass (or removal if that pass finds it
// unneeded).
//
// Distinction from RDF.CottasStore.LazyDict (#254):
//   - LazyDict has 4 directions (typed/raw forward + canonical/raw
//     reverse) because the cottas-ondisk runtime needs raw column
//     tokens for parquet I/O alongside typed values for SPARQL eval.
//   - LazyTermCache has 2 directions (typed forward + typed reverse)
//     which is sufficient for HDT — the Front-Coded dictionary IS
//     the canonical form; there's no separate raw view.
//
// Effect: ML throughout. Populate touches state, lookups consult
// state, the rest of the HDT runtime already runs in ML.

// Each entry: (id, typed_value). The populate thunk returns the
// full list, typically in id order.
type entries (a : Type) = list (nat & a)

// The abstract container. Realised as a 4-field OCaml record.
assume new type lazy_term_cache (a : Type) : Type

// Build a fresh lazy_term_cache from a populate thunk + a
// canonical-key function. The thunk is held (not called); the
// cache starts in the "not populated" state. The key_of function
// canonicalises values for reverse-lookup — sidesteps the eqtype
// constraint so values can be `noeq` (e.g. RDF.Graph.Executable's
// `subject` type).
assume val mk_lazy_term_cache
  (#a : Type)
  (populate : unit -> ML (entries a))
  (key_of   : a -> string)
  : ML (lazy_term_cache a)

// Look up the typed value by id. Triggers populate on first call
// across any of the lookup_* functions. Returns None if the id is
// absent (id out of range).
assume val lookup_by_id
  (#a : Type) (c : lazy_term_cache a) (i : nat) : ML (option a)

// Reverse-lookup by canonical key (produced by the key_of
// function the cache was constructed with). Returns None if the
// canonical key is absent from this corpus.
assume val lookup_by_key
  (#a : Type) (c : lazy_term_cache a) (k : string) : ML (option nat)

// Has this cache been populated yet? Pure observation; used by
// diagnostics.
assume val is_populated
  (#a : Type) (c : lazy_term_cache a) : ML bool

// Number of entries. 0 before populate; fixed positive nat after.
assume val size
  (#a : Type) (c : lazy_term_cache a) : ML nat

// Materialise the full id-ordered list of typed values. Triggers
// populate.
assume val to_list
  (#a : Type) (c : lazy_term_cache a) : ML (list a)
