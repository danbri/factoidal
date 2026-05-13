module RDF.CottasStore.LazyDict

open FStar.All

// A lazy-populate cottas-column dictionary.
//
// Bundles four indexed views over a single column's distinct tokens:
//   id           -> typed term  (subject / wf_iri / rdf_term)
//   id           -> raw column-token string
//   canonical-key (string)      -> id
//   raw-token  (string)         -> id
//
// All four populate together on the first lookup of any kind.
// Realised in OCaml as four Hashtbl.t + a populate thunk + a loaded
// flag + a mutex. The mutex is the strict improvement called out in
// the retirement plan's risk register (cottas_ondisk_z_lazy_open.sh
// today is not cross-thread safe).
//
// Issue #254 (Bet7) — replaces cottas_ondisk_z_lazy_open.sh's
// `Cottas_ondisk_lazy` module with an F*-spec'd populate-on-demand
// dictionary. Design plan:
//   docs/designissues/2026-05-13-issue-254-bet7-retirement-plan.md
//
// Effect: ML throughout. Populate touches state, lookups consult
// state, the rest of the cottas runtime already runs in ML. The
// pure-vs-ML split called out in the plan's risk register lives on
// the consumer side (callers that want Tot purity take an already-
// populated `list (nat & a & string)` instead of a `lazy_dict a`).

// Each entry: (id, typed_value, raw_token_string). The populate
// thunk returns the full list, in id order.
type populate_result (a : Type) = list (nat & a & string)

// The abstract container. Realised as a 5-field OCaml record.
assume new type lazy_dict (a : Type) : Type

// Build a fresh lazy_dict from a populate thunk and a
// canonical-key function. The thunk is held (not called); the
// dict starts in the "not populated" state. The key_of function
// is used to canonicalise typed values for reverse-lookup.
assume val mk_lazy_dict
  (#a : Type)
  (populate : unit -> ML (populate_result a))
  (key_of   : a -> string)
  : ML (lazy_dict a)

// Look up the typed value by id. Triggers populate on first call
// across any of the lookup_* / encode_* / to_*_list functions.
// Returns None if the id is absent (id out of range).
assume val decode_by_id
  (#a : Type) (d : lazy_dict a) (i : nat) : ML (option a)

// Look up the raw column-token string by id. Same populate
// trigger as decode_by_id.
assume val decode_raw_by_id
  (#a : Type) (d : lazy_dict a) (i : nat) : ML (option string)

// Reverse-lookup by canonical key (produced by the key_of
// function the dict was constructed with). Returns None if the
// canonical key is absent from this corpus.
assume val encode_by_key
  (#a : Type) (d : lazy_dict a) (k : string) : ML (option nat)

// Reverse-lookup by raw column-token. Used by the fast-prune
// cascade to convert a row-group raw token back to its id
// without re-parsing the typed term.
assume val encode_by_raw_token
  (#a : Type) (d : lazy_dict a) (t : string) : ML (option nat)

// Has this dict been populated yet? Pure observation; used by
// diagnostics and the bet7-trace log lines.
assume val is_populated (#a : Type) (d : lazy_dict a) : ML bool

// Number of distinct entries. 0 before populate; fixed positive
// nat after. Used by cardinality estimation on the cottas-ondisk
// fast path (cottas_ondisk_estimate).
assume val size (#a : Type) (d : lazy_dict a) : ML nat

// Materialise the full id-to-typed list, in id order. Used by
// CONSTRUCT and DESCRIBE that need the whole column. Triggers
// populate.
assume val to_typed_list (#a : Type) (d : lazy_dict a)
  : ML (list a)

// Materialise the full id-to-raw list, in id order. Same
// populate trigger.
assume val to_raw_list (#a : Type) (d : lazy_dict a)
  : ML (list string)
