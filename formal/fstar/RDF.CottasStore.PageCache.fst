module RDF.CottasStore.PageCache

open RDF.CottasStore.ColumnSeq

// Mim2 (issue #100 Phase C): F*-internal page cache for the on-disk
// COTTAS backend.
//
// The cache is keyed by `(rg_index, col_index)` and stores the decoded
// `list (option string)` produced by
// `Parquet.Footer.probe_parquet_column_decode_in_row_group`.
//
// Why an F*-internal cache when the OCaml byte cache already memoises
// file reads + zstd decompression?
//
// 1. The byte cache makes `parquet_read_*` cheap, but the column-decode
//    path (DLBA / RLE_DICTIONARY) still walks the (now-cached) hex
//    payload byte-by-byte. Caching the decoded `list (option string)`
//    skips that walk for repeated row-group probes.
//
// 2. The cache is the canonical place for Phase D's column-prune
//    planner to look up per-column decoded data without re-deriving it.
//
// 3. The user's brief asked for an F*-verified cache as the
//    architectural anchor — `pcache_get` / `pcache_put` with explicit
//    LRU. This module provides exactly that.
//
// Implementation: assoc-list with monotonically-increasing age stamps.
// On `pcache_put` past capacity, the entry with the smallest age is
// evicted. Lookups bump the matched entry's age. Pure F*. The list
// is small (cap=64 covers parliament's 26x4 surface) so the linear
// scan is fine.

// Page-cache key: (row-group index, column index)
type pcache_key = nat & nat

// Page-cache entry: key + decoded payload + age stamp.
//
// Phase 2.5c (issue #118): pce_value is now `cottas_column` (an
// abstract type extracted to OCaml `string option array`) instead of
// `list (option string)`. This eliminates the per-cell list cons
// cost on column walks. Cache integrity (LRU + clock) unchanged;
// only the stored value's shape differs.
noeq type pcache_entry = {
  pce_key : pcache_key;
  pce_value : cottas_column;
  pce_age : nat;
}

noeq type page_cache = {
  pc_entries : list pcache_entry;
  pc_clock : nat;     // Monotonically increasing; assigned on put / get.
  pc_capacity : nat;  // Max number of entries. 0 = disabled.
}

// Empty cache with the given capacity.
let pcache_empty (capacity : nat) : page_cache = {
  pc_entries = [];
  pc_clock = 0;
  pc_capacity = capacity;
}

// Key equality.
let key_eq (k1 k2 : pcache_key) : bool =
  let (a1, b1) = k1 in
  let (a2, b2) = k2 in
  a1 = a2 && b1 = b2

// Linear lookup. Returns the entry's value if present.
let rec lookup_entry (entries : list pcache_entry) (k : pcache_key)
  : Tot (option pcache_entry) (decreases entries) =
  match entries with
  | [] -> None
  | e :: rest ->
    if key_eq e.pce_key k then Some e
    else lookup_entry rest k

// Replace the entry at key k (assumes it's present); returns new list.
let rec replace_entry (entries : list pcache_entry) (k : pcache_key)
  (new_e : pcache_entry)
  : Tot (list pcache_entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if key_eq e.pce_key k then new_e :: rest
    else e :: replace_entry rest k new_e

// Drop the entry with key k from the list. If absent, returns the list
// unchanged.
let rec drop_entry (entries : list pcache_entry) (k : pcache_key)
  : Tot (list pcache_entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if key_eq e.pce_key k then rest
    else e :: drop_entry rest k

// pcache_get: returns the decoded list if present + the cache with the
// matched entry's age bumped. (Threading the cache through is required
// because F* is pure-by-default; callers chain calls explicitly.)
let pcache_get (cache : page_cache) (k : pcache_key)
  : Tot (option cottas_column & page_cache) =
  match lookup_entry cache.pc_entries k with
  | None -> (None, cache)
  | Some entry ->
    let new_clock = cache.pc_clock + 1 in
    let bumped = { entry with pce_age = new_clock; } in
    let updated = {
      cache with
        pc_entries = replace_entry cache.pc_entries k bumped;
        pc_clock = new_clock;
    } in
    (Some entry.pce_value, updated)

// Find the LRU victim's key, scanning the entries. Returns None for an
// empty list. Uses (best_key, best_age, found) as the running winner;
// returning best_key when found.
let rec find_oldest_aux
  (entries : list pcache_entry)
  (best_key : pcache_key) (best_age : nat) (found : bool)
  : Tot (option pcache_key) (decreases entries) =
  match entries with
  | [] -> if found then Some best_key else None
  | e :: rest ->
    if not found then
      find_oldest_aux rest e.pce_key e.pce_age true
    else if e.pce_age < best_age then
      find_oldest_aux rest e.pce_key e.pce_age true
    else
      find_oldest_aux rest best_key best_age true

let find_oldest (entries : list pcache_entry) : Tot (option pcache_key) =
  find_oldest_aux entries (0, 0) 0 false

// List length.
let rec list_len (#a:Type) (xs : list a) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | _ :: rest -> 1 + list_len rest

// Put an entry. If the key is already present, replace in-place
// (bumping age). Otherwise prepend. If the resulting list exceeds
// capacity, evict the oldest entry.
let pcache_put
  (cache : page_cache) (k : pcache_key) (v : cottas_column)
  (capacity : nat)
  : Tot page_cache =
  if capacity = 0 then cache
  else
    let new_clock = cache.pc_clock + 1 in
    let new_entry = { pce_key = k; pce_value = v; pce_age = new_clock; } in
    let entries_after =
      match lookup_entry cache.pc_entries k with
      | Some _ -> replace_entry cache.pc_entries k new_entry
      | None -> new_entry :: cache.pc_entries in
    let entries_capped =
      if list_len entries_after > capacity then
        match find_oldest entries_after with
        | None -> entries_after  // unreachable when len > 0
        | Some victim_key -> drop_entry entries_after victim_key
      else entries_after in
    {
      pc_entries = entries_capped;
      pc_clock = new_clock;
      pc_capacity = capacity;
    }

// ----------------------------------------------------------------------
// Convenience: probe through the cache. Tries the cache first; on miss,
// calls the underlying decoder, inserts, and returns. Callers thread
// the cache explicitly:
//   let (col, cache) = pcache_decode_in_row_group cache path rg col cap in
// ----------------------------------------------------------------------

let pcache_decode_in_row_group
  (cache : page_cache) (path : string)
  (rg_index : nat) (col_index : nat) (capacity : nat)
  : Tot (option cottas_column & page_cache) =
  let key = (rg_index, col_index) in
  match pcache_get cache key with
  | (Some v, c1) -> (Some v, c1)
  | (None, c1) ->
    match probe_parquet_column_decode_in_row_group_seq path rg_index col_index with
    | None -> (None, c1)
    | Some v ->
      let c2 = pcache_put c1 key v capacity in
      (Some v, c2)
