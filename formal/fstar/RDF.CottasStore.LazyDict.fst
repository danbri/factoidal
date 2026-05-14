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
// flag + a mutex.
//
// Issue #254 (Bet7) — replaces cottas_ondisk_z_lazy_open.sh's
// `Cottas_ondisk_lazy` module with an F*-spec'd populate-on-demand
// dictionary. Design plan:
//   docs/designissues/2026-05-13-issue-254-bet7-retirement-plan.md

// Each entry: (id, typed_value, raw_token_string). The populate
// thunk returns the full list, in id order.
type populate_result (a : Type0) = list (nat & a & string)

// The abstract container. Realised as a 5-field OCaml record.
// Pinned to Type0 to avoid universe-polymorphism propagation
// into mutually recursive definitions downstream (SPARQL11.Store
// eval_* / RDF.Store.Combine), which fails F* unification with
// "Error 89: incompatible universe sets" in mutual recursion blocks.
assume new type lazy_dict (a : Type0) : Type0

// Build a fresh lazy_dict from a populate thunk and a canonical-key
// function.
assume val mk_lazy_dict
  (#a : Type0)
  (populate : unit -> ML (populate_result a))
  (key_of   : a -> string)
  : ML (lazy_dict a)

assume val decode_by_id
  (#a : Type0) (d : lazy_dict a) (i : nat) : ML (option a)

assume val decode_raw_by_id
  (#a : Type0) (d : lazy_dict a) (i : nat) : ML (option string)

assume val encode_by_key
  (#a : Type0) (d : lazy_dict a) (k : string) : ML (option nat)

assume val encode_by_raw_token
  (#a : Type0) (d : lazy_dict a) (t : string) : ML (option nat)

assume val is_populated (#a : Type0) (d : lazy_dict a) : ML bool

assume val size (#a : Type0) (d : lazy_dict a) : ML nat

assume val to_typed_list (#a : Type0) (d : lazy_dict a)
  : ML (list a)

assume val to_raw_list (#a : Type0) (d : lazy_dict a)
  : ML (list string)

// Pure-Tot helpers — sidestep the ML-effect cascade for callers
// that need to preserve `Tot` purity (e.g. the SPARQL evaluator's
// filter_zipped_rows / walk_row_groups_search paths). They take
// already-materialised entry lists and perform the lookup at the
// F*-pure level. Caller is responsible for getting the lists via
// `to_typed_list` / `to_raw_list` from the ML primitives ONCE per
// query, then threading them through Tot consumers.

let rec lookup_id_in_list (#a : Type0)
  (entries : list (nat & a)) (id : nat)
  : Tot (option a) (decreases entries) =
  match entries with
  | [] -> None
  | (id', v) :: rest -> if id = id' then Some v else lookup_id_in_list rest id

let rec lookup_key_in_list (#a : Type0)
  (entries : list (string & a)) (key : string)
  : Tot (option a) (decreases entries) =
  match entries with
  | [] -> None
  | (k, v) :: rest -> if k = key then Some v else lookup_key_in_list rest key
