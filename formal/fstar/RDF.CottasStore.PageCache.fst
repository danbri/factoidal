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

// Phase 2.5e (issue #118): cross-call cached decoder. The decision
// of WHEN to memoise (LRU eviction, monotone clock, key match) lives
// in the pure F* `pcache_*` functions above and is verified by the
// usual F* totality and Tot-purity. The CROSS-CALL STORAGE CELL —
// a process-level mutable ref holding the current `page_cache` —
// lives in OCaml because F* is pure-by-default, and threading the
// cache through every call chain (cottas_ondisk_search →
// walk_row_groups → ...) is both noisy and cannot survive multiple
// HTTP requests anyway.
//
// Realisation: see
//   experimental_ocaml_glue/cottas_pagecache_global_runtime.sh
// for the OCaml-side stateful ref + realisation. Rule #11(c) thin
// dispatch shim — no semantic decisions, only state plumbing.
//
// Callers (cottas_ondisk_search, cottas_ondisk_estimate,
// cottas_ondisk_search_limited) use this `_global` decoder so they
// inherit cross-query warm-cache hits without threading `page_cache`
// through their walk arguments.
assume val pcache_decode_in_row_group_global :
  (path : string) -> (rg_index : nat) -> (col_index : nat) ->
  Tot (option cottas_column)

// Table-threaded sibling of `pcache_decode_in_row_group` (issue
// #98/Mim3 follow-up, 2026-07-05): same LRU semantics, but a cache
// MISS decodes through the row-group-offset-table decoder
// (`probe_parquet_column_decode_in_row_group_seq_from_table`) instead
// of the per-call footer re-walk. The table is
// `Parquet.Footer.probe_parquet_row_group_offset_table`'s output,
// built ONCE per query by the RDF.CottasStore public entry points and
// threaded down through the row-group walks -- offsets are F*
// semantics, computed in Parquet.Footer, never cached OCaml-side.
let pcache_decode_in_row_group_from_table
  (cache : page_cache)
  (table : Parquet.Footer.parquet_row_group_offset_table)
  (path : string)
  (rg_index : nat) (col_index : nat) (capacity : nat)
  : Tot (option cottas_column & page_cache) =
  let key = (rg_index, col_index) in
  match pcache_get cache key with
  | (Some v, c1) -> (Some v, c1)
  | (None, c1) ->
    match probe_parquet_column_decode_in_row_group_seq_from_table
            table path rg_index col_index with
    | None -> (None, c1)
    | Some v ->
      let c2 = pcache_put c1 key v capacity in
      (Some v, c2)

// Global (cross-call storage cell) variant of the table-threaded
// decoder. Same rule-#11(c) shape as `pcache_decode_in_row_group_global`
// above: the OCaml realisation only forwards the F*-computed table and
// threads the mutable page_cache ref through
// `pcache_decode_in_row_group_from_table` -- no semantic decisions.
// Realisation lives alongside the existing one in
// experimental_ocaml_glue/cottas_pagecache_global_runtime.sh.
assume val pcache_decode_in_row_group_global_from_table :
  (table : Parquet.Footer.parquet_row_group_offset_table) ->
  (path : string) -> (rg_index : nat) -> (col_index : nat) ->
  Tot (option cottas_column)

// ----------------------------------------------------------------------
// Tsade2 Phase E (issue #100 followup, 2026-07-06): cross-query DICTIONARY
// cache.
//
// The two caches above memoise DATA-page decode (`cottas_column`, the
// actual row values). Query PLANNING (RDF.CottasStore.fst's
// `populate_dict_cache_for_column`, called once per `plan_candidate_rgs`,
// itself called once per public query entry point) needs a DIFFERENT
// artifact per (row-group, column): the column's DICTIONARY (`list
// string`, the distinct values a RLE_DICTIONARY-encoded column can take
// in that row group), used only to decide which row groups can possibly
// contain a bound term. That planner rebuilds its dict cache from `[]`
// on every single query (see the module banner at
// `RDF.CottasStore.dict_cache`), so
// `Parquet.Footer.probe_parquet_column_dictionary_in_row_group[_from_table]`
// -- dictionary-page decompress + plain-dictionary decode -- reruns on
// every query for every (row-group, bound-column) pair, even though the
// dictionary is invariant for the lifetime of a read-only store handle.
// This is the measured residual cost behind the post-offset-table 44-vs-
// 8-row-group ratio (2026-07-05 perf review, roadmap item 2): the
// per-locate O(row_groups^2) walk is gone, but this per-query O(row_groups)
// redecode remains and is what makes 44 groups still ~4x an 8-group query
// instead of the ~5.5x-row-group-ratio-bound linear cost alone would give.
//
// Cache shape mirrors `page_cache`/`pcache_*` above EXACTLY (same
// assoc-list-with-age-stamps LRU, same key shape) -- only the stored
// value type differs (`list string` dictionaries vs `cottas_column` data).
// Kept as a separate small type instead of parameterizing `page_cache`
// over a type variable, to avoid touching every existing `page_cache`-
// typed call site for an unrelated change. The duplication below is of
// LRU BOOKKEEPING only (rule #15 concerns decode logic, not cache
// scaffolding) -- the actual dictionary decompress/decode stays solely
// in `Parquet.Footer`, called exactly once per (rg, col) per PROCESS
// instead of once per (rg, col) per QUERY.
// ----------------------------------------------------------------------

noeq type dict_pcache_entry = {
  dpce_key : pcache_key;
  dpce_value : list string;
  dpce_age : nat;
}

noeq type dict_page_cache = {
  dpc_entries : list dict_pcache_entry;
  dpc_clock : nat;
  dpc_capacity : nat;  // 0 = disabled (every call is a miss, no growth).
}

let dpcache_empty (capacity : nat) : dict_page_cache = {
  dpc_entries = [];
  dpc_clock = 0;
  dpc_capacity = capacity;
}

let rec dpc_lookup_entry (entries : list dict_pcache_entry) (k : pcache_key)
  : Tot (option dict_pcache_entry) (decreases entries) =
  match entries with
  | [] -> None
  | e :: rest -> if key_eq e.dpce_key k then Some e else dpc_lookup_entry rest k

let rec dpc_replace_entry (entries : list dict_pcache_entry) (k : pcache_key)
  (new_e : dict_pcache_entry)
  : Tot (list dict_pcache_entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    if key_eq e.dpce_key k then new_e :: rest
    else e :: dpc_replace_entry rest k new_e

let rec dpc_drop_entry (entries : list dict_pcache_entry) (k : pcache_key)
  : Tot (list dict_pcache_entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest -> if key_eq e.dpce_key k then rest else e :: dpc_drop_entry rest k

// Cache lookup. Returns the cached dictionary if present + cache with
// the matched entry's age bumped.
let dpcache_get (cache : dict_page_cache) (k : pcache_key)
  : Tot (option (list string) & dict_page_cache) =
  match dpc_lookup_entry cache.dpc_entries k with
  | None -> (None, cache)
  | Some entry ->
    let new_clock = cache.dpc_clock + 1 in
    let bumped = { entry with dpce_age = new_clock; } in
    let updated = {
      cache with
        dpc_entries = dpc_replace_entry cache.dpc_entries k bumped;
        dpc_clock = new_clock;
    } in
    (Some entry.dpce_value, updated)

let rec dpc_find_oldest_aux
  (entries : list dict_pcache_entry)
  (best_key : pcache_key) (best_age : nat) (found : bool)
  : Tot (option pcache_key) (decreases entries) =
  match entries with
  | [] -> if found then Some best_key else None
  | e :: rest ->
    if not found then dpc_find_oldest_aux rest e.dpce_key e.dpce_age true
    else if e.dpce_age < best_age then dpc_find_oldest_aux rest e.dpce_key e.dpce_age true
    else dpc_find_oldest_aux rest best_key best_age true

let dpc_find_oldest (entries : list dict_pcache_entry) : Tot (option pcache_key) =
  dpc_find_oldest_aux entries (0, 0) 0 false

// Put an entry, evicting the LRU victim past capacity. Same policy as
// `pcache_put`.
let dpcache_put
  (cache : dict_page_cache) (k : pcache_key) (v : list string)
  (capacity : nat)
  : Tot dict_page_cache =
  if capacity = 0 then cache
  else
    let new_clock = cache.dpc_clock + 1 in
    let new_entry = { dpce_key = k; dpce_value = v; dpce_age = new_clock; } in
    let entries_after =
      match dpc_lookup_entry cache.dpc_entries k with
      | Some _ -> dpc_replace_entry cache.dpc_entries k new_entry
      | None -> new_entry :: cache.dpc_entries in
    let entries_capped =
      if list_len entries_after > capacity then
        match dpc_find_oldest entries_after with
        | None -> entries_after  // unreachable when len > 0
        | Some victim_key -> dpc_drop_entry entries_after victim_key
      else entries_after in
    {
      dpc_entries = entries_capped;
      dpc_clock = new_clock;
      dpc_capacity = capacity;
    }

// Cache-wrapped dictionary probe (table-threaded). A cache miss decodes
// through `Parquet.Footer.probe_parquet_column_dictionary_in_row_group_from_table`
// -- the exact call the planner makes on every query today -- and stores
// the result for the next caller.
let dpcache_probe_dict_in_row_group_from_table
  (cache : dict_page_cache)
  (table : Parquet.Footer.parquet_row_group_offset_table)
  (path : string)
  (rg_index : nat) (col_index : nat) (capacity : nat)
  : Tot (option (list string) & dict_page_cache) =
  let key = (rg_index, col_index) in
  match dpcache_get cache key with
  | (Some v, c1) -> (Some v, c1)
  | (None, c1) ->
    match Parquet.Footer.probe_parquet_column_dictionary_in_row_group_from_table
            table path rg_index col_index with
    | None -> (None, c1)
    | Some v ->
      let c2 = dpcache_put c1 key v capacity in
      (Some v, c2)

// Global (cross-call storage cell) variant. Same rule-#11(c) shape as
// `pcache_decode_in_row_group_global_from_table`: the OCaml realisation
// only forwards the F*-computed table and threads a mutable
// `dict_page_cache ref` across calls -- no semantic decisions, no
// OCaml-side dictionary decode. This is the function
// `RDF.CottasStore.populate_dict_cache_loop` calls instead of the raw
// per-call probe, so the planner's per-query cache populate becomes a
// process-lifetime cache populate. Realisation: the same
// experimental_ocaml_glue/cottas_pagecache_global_runtime.sh file (the
// existing OCaml page-cache glue layer already has the storage-cell +
// env-kill-switch plumbing this needs; extended, not duplicated).
assume val dpcache_probe_dict_in_row_group_global_from_table :
  (table : Parquet.Footer.parquet_row_group_offset_table) ->
  (path : string) -> (rg_index : nat) -> (col_index : nat) ->
  Tot (option (list string))
