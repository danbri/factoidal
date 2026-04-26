module RDF.CottasStore.PageCache.Bounds

// Mim4 (issue #100, methodology demonstration). Structural bounds proofs
// for the F*-pure page cache in RDF.CottasStore.PageCache and the
// LIMIT-pushdown walker in RDF.CottasStore.
//
// See docs/designissues/2026-04-26-mem4-pagecache-bounds-proof.md for the
// methodology argument behind this module.
//
// Lemmas:
//
//   1. pcache_put_capacity_bound — pcache_put preserves
//      length entries <= capacity.
//   2. pcache_get_length          — pcache_get preserves length exactly.
//   3. pcache_decode_capacity_bound — convenience wrapper preserves the
//      bound.
//   4. walk_candidate_rgs_search_limited_bound — the materialised
//      acc_rev from walk_candidate_rgs_search_limited never exceeds
//      limit. (Catches the "future regression where someone optimises
//      by removing the limit check" scenario.)
//
// What this DOES prove:
//   - The F*-modeled "resident set" of decoded column pages is bounded
//     by `cap` entries, regardless of how many row-groups the dataset
//     has. Combined with a max-bytes-per-page bound (future work),
//     gives a parametric statement: "resident bytes <= cap *
//     max_page_bytes". With cap=64 and max_page_bytes=1MB, that is
//     64MB regardless of dataset size — the "10% of working set"
//     story for the F*-pure layer.
//   - The materialised result list from the LIMIT-pushdown walker
//     never exceeds the user's LIMIT clause. A future optimisation
//     that removes a bound check would surface as a verification error
//     at `make verify` time, not as a production memory spike.
//
// What this does NOT prove:
//   - OCaml-extracted heap RSS. The Hashtbls in
//     experimental_ocaml_glue/cottas_ondisk_runtime.sh (200+ MB at
//     parliament scale) live outside F*'s model. Their size is
//     empirical, not proven.
//   - Kernel mmap residency. The OS pages are at the kernel's
//     discretion; F* only proves we don't *touch* more than the
//     candidate row-groups.
//   - Lazy-thunk closure retention in OCaml's runtime.
//   - Per-entry byte size. The list (option string) decoded from a
//     column is bounded only by the parquet column-page size, which
//     is an external (not-yet-modelled) parameter.
//
// Methodology shift: pc_capacity is currently a runtime knob; if a
// future edit to pcache_put accidentally leaks (say, a typo dropping
// the eviction step), the regression would surface as RSS bloat in
// production. With these lemmas in place, that same edit becomes a
// *verification error* at `make verify` time. Same code; stronger
// contract.

open RDF.CottasStore.PageCache
open RDF.CottasStore
open Parser.BallyhooCOTTAS
open Parquet.Footer
module L = FStar.List.Tot

// ------------------------------------------------------------
// Helper specs over the assoc-list operations.
// ------------------------------------------------------------

// `replace_entry` preserves length: replacing an entry doesn't change
// list length whether the key is present or not.
val replace_entry_length :
  entries:list pcache_entry -> k:pcache_key -> new_e:pcache_entry ->
  Lemma (ensures L.length (replace_entry entries k new_e) = L.length entries)
        (decreases entries)
let rec replace_entry_length entries k new_e =
  match entries with
  | [] -> ()
  | _ :: rest -> replace_entry_length rest k new_e

// `drop_entry` reduces length by at most 1. If the key is present
// exactly once, length decreases by 1; if absent, length is preserved.
val drop_entry_length :
  entries:list pcache_entry -> k:pcache_key ->
  Lemma (ensures
    L.length (drop_entry entries k) <= L.length entries /\
    L.length (drop_entry entries k) >= (if L.length entries > 0 then L.length entries - 1 else 0))
    (decreases entries)
let rec drop_entry_length entries k =
  match entries with
  | [] -> ()
  | _ :: rest -> drop_entry_length rest k

// "Key k is present in entries" — there's an entry whose key equals k.
let rec key_present (entries : list pcache_entry) (k : pcache_key) : Tot bool =
  match entries with
  | [] -> false
  | e :: rest -> if key_eq e.pce_key k then true else key_present rest k

// drop_entry strictly reduces length when the key is present.
val drop_entry_length_present :
  entries:list pcache_entry -> k:pcache_key ->
  Lemma
    (requires key_present entries k)
    (ensures L.length (drop_entry entries k) = L.length entries - 1)
    (decreases entries)
let rec drop_entry_length_present entries k =
  match entries with
  | [] -> ()
  | e :: rest ->
    if key_eq e.pce_key k then ()
    else drop_entry_length_present rest k

// list_len = List.length (the module redefines list_len structurally
// for `decreases` discipline; they're extensionally equal).
val list_len_eq_length :
  #a:Type -> xs:list a ->
  Lemma (ensures list_len xs = L.length xs) (decreases xs)
let rec list_len_eq_length #a xs =
  match xs with
  | [] -> ()
  | _ :: rest -> list_len_eq_length rest

// find_oldest_aux: once `found` becomes true, the result is Some.
val find_oldest_aux_found_some :
  entries:list pcache_entry -> best_key:pcache_key -> best_age:nat ->
  Lemma
    (ensures Some? (find_oldest_aux entries best_key best_age true))
    (decreases entries)
let rec find_oldest_aux_found_some entries best_key best_age =
  match entries with
  | [] -> ()
  | e :: rest ->
    if e.pce_age < best_age then
      find_oldest_aux_found_some rest e.pce_key e.pce_age
    else
      find_oldest_aux_found_some rest best_key best_age

// find_oldest of a non-empty list is Some.
val find_oldest_nonempty :
  entries:list pcache_entry ->
  Lemma
    (requires Cons? entries)
    (ensures Some? (find_oldest entries))
let find_oldest_nonempty entries =
  match entries with
  | [] -> ()
  | e :: rest ->
    find_oldest_aux_found_some rest e.pce_key e.pce_age

// key_present is monotone: if a key is in the running winner OR in the
// remaining entries, find_oldest_aux returns a key in (winner :: entries).
//
// More precisely: if found = true and best_key is present in
// `(known_seen @ entries)`, the result is Some k with k present in
// the same combined list. We use a simpler-to-prove form: best_key
// either gets returned, or some entry in `entries` is.
val find_oldest_aux_returns_present :
  entries:list pcache_entry -> best_key:pcache_key -> best_age:nat ->
  Lemma
    (ensures
      (match find_oldest_aux entries best_key best_age true with
       | None -> False
       | Some k ->
         key_eq k best_key \/ key_present entries k))
    (decreases entries)
let rec find_oldest_aux_returns_present entries best_key best_age =
  match entries with
  | [] -> ()
  | e :: rest ->
    if e.pce_age < best_age then begin
      find_oldest_aux_returns_present rest e.pce_key e.pce_age;
      // Result is either e.pce_key (present here) or in rest.
      ()
    end
    else begin
      find_oldest_aux_returns_present rest best_key best_age;
      // Result is either best_key or in rest. If in rest, also in
      // (e :: rest).
      ()
    end

// find_oldest of a non-empty list returns a key that is present.
val find_oldest_present :
  entries:list pcache_entry ->
  Lemma
    (requires Cons? entries)
    (ensures
      (match find_oldest entries with
       | None -> False
       | Some k -> key_present entries k))
let find_oldest_present entries =
  match entries with
  | [] -> ()
  | e :: rest ->
    // find_oldest entries = find_oldest_aux rest e.pce_key e.pce_age true.
    // After find_oldest_aux_returns_present, Some k where k = e.pce_key
    // (present at head) or k in rest (present in tail of e :: rest).
    find_oldest_aux_returns_present rest e.pce_key e.pce_age;
    find_oldest_aux_found_some rest e.pce_key e.pce_age
    // The Some k case: either key_eq k e.pce_key (so key_present (e::rest) k
    // by head match) or key_present rest k (so key_present (e::rest) k
    // by recursive case).

// ------------------------------------------------------------
// Lemma 1: pcache_put preserves the capacity bound.
// ------------------------------------------------------------
//
// Statement: if the input list has length <= capacity, the output
// list does too. The eviction step kicks in exactly when the
// "after-replace-or-prepend" list would exceed capacity, dropping
// one entry to bring it back to capacity.

val pcache_put_capacity_bound :
  cache:page_cache -> k:pcache_key -> v:list (option string) -> capacity:nat ->
  Lemma
    (requires L.length cache.pc_entries <= capacity \/ capacity = 0)
    (ensures
      capacity = 0 \/
      L.length (pcache_put cache k v capacity).pc_entries <= capacity)
// Helper lemma: bound on the entries_after intermediate.
val entries_after_bound :
  cache:page_cache -> k:pcache_key -> new_entry:pcache_entry ->
  capacity:nat ->
  Lemma
    (requires L.length cache.pc_entries <= capacity)
    (ensures
      (let entries_after =
         match lookup_entry cache.pc_entries k with
         | Some _ -> replace_entry cache.pc_entries k new_entry
         | None -> new_entry :: cache.pc_entries in
       L.length entries_after <= capacity + 1))
let entries_after_bound cache k new_entry capacity =
  match lookup_entry cache.pc_entries k with
  | Some _ -> replace_entry_length cache.pc_entries k new_entry
  | None -> ()

// Helper lemma: bound on entries_capped given entries_after length.
//
// Restated in terms of `L.length` (rather than the structural `list_len`)
// so the ensures clause uses properties SMT can match on. The `pos`
// refinement is needed so the precondition L.length <= capacity + 1
// admits the "could be 0" case for length cleanly.
val entries_capped_bound :
  entries_after:list pcache_entry -> capacity:pos ->
  Lemma
    (requires L.length entries_after <= capacity + 1)
    (ensures
      (if L.length entries_after > capacity then
         (Cons? entries_after /\ Some? (find_oldest entries_after) /\
          (let v = Some?.v (find_oldest entries_after) in
           L.length (drop_entry entries_after v) <= capacity))
       else
         L.length entries_after <= capacity))
let entries_capped_bound entries_after capacity =
  if L.length entries_after > capacity then begin
    // L.length > capacity >= 1 forces non-empty.
    find_oldest_nonempty entries_after;
    find_oldest_present entries_after;
    let v = Some?.v (find_oldest entries_after) in
    // v is present, so drop_entry strictly reduces length.
    drop_entry_length_present entries_after v
    // L.length (drop_entry entries_after v) = L.length entries_after - 1.
    // L.length entries_after <= capacity + 1 (precond), so result <= capacity.
  end
  else ()

#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
let pcache_put_capacity_bound cache k v capacity =
  if capacity = 0 then ()
  else begin
    let new_clock = cache.pc_clock + 1 in
    let new_entry = { pce_key = k; pce_value = v; pce_age = new_clock; } in
    entries_after_bound cache k new_entry capacity;
    let entries_after =
      match lookup_entry cache.pc_entries k with
      | Some _ -> replace_entry cache.pc_entries k new_entry
      | None -> new_entry :: cache.pc_entries in
    list_len_eq_length entries_after;
    entries_capped_bound entries_after capacity
  end
#pop-options

// ------------------------------------------------------------
// Lemma 2: pcache_get preserves length exactly.
// ------------------------------------------------------------

val pcache_get_length :
  cache:page_cache -> k:pcache_key ->
  Lemma (ensures
    L.length (snd (pcache_get cache k)).pc_entries = L.length cache.pc_entries)
let pcache_get_length cache k =
  match lookup_entry cache.pc_entries k with
  | None -> ()
  | Some entry ->
    let new_clock = cache.pc_clock + 1 in
    let bumped = { entry with pce_age = new_clock; } in
    replace_entry_length cache.pc_entries k bumped

// ------------------------------------------------------------
// Lemma 3: pcache_decode_in_row_group preserves the capacity bound.
// ------------------------------------------------------------
//
// Note: this depends on `probe_parquet_column_decode_in_row_group`
// being a `Tot` function (which it is, in the Mim2 design). On a
// cache hit, length is preserved (lemma 2). On a miss + decoder hit,
// pcache_put applies (lemma 1). On a decoder miss, length unchanged.

val pcache_decode_capacity_bound :
  cache:page_cache -> path:string -> rg_index:nat -> col_index:nat ->
  capacity:nat ->
  Lemma
    (requires L.length cache.pc_entries <= capacity \/ capacity = 0)
    (ensures
      capacity = 0 \/
      L.length (snd (pcache_decode_in_row_group cache path rg_index col_index capacity)).pc_entries
        <= capacity)
let pcache_decode_capacity_bound cache path rg_index col_index capacity =
  if capacity = 0 then ()
  else begin
    let key = (rg_index, col_index) in
    pcache_get_length cache key;
    match pcache_get cache key with
    | (Some _, _) -> ()
    | (None, c1) ->
      match probe_parquet_column_decode_in_row_group path rg_index col_index with
      | None -> ()
      | Some v ->
        pcache_put_capacity_bound c1 key v capacity
  end

// ------------------------------------------------------------
// Lemma 4 (NEW): materialisation bound for Aleph6's
// walk_candidate_rgs_search_limited.
// ------------------------------------------------------------
//
// Statement: the result list returned by walk_candidate_rgs_search_limited
// never exceeds `limit` rows.
//
// The proof goes via an invariant that links the running count
// (`acc_count`) to the running list length (`L.length acc_rev`). Both
// are incremented in lockstep by `filter_zipped_rows_limited`, so the
// invariant `acc_count = L.length acc_rev /\ acc_count <= limit`
// suffices to give a final `L.length acc_rev <= limit`.
//
// We need a helper lemma over `filter_zipped_rows_limited` first.

// Helper 4a: filter_zipped_rows_limited preserves the
// "acc_count = length acc_rev /\ acc_count <= limit" invariant.
//
// On match: acc_rev grows by 1, acc_count grows by 1. Equality preserved.
// No-match step: both unchanged. Equality preserved.
// Short-circuit: returns immediately, both unchanged, invariant preserved.
//
// The result tuple is (list cottas_qp_row & nat & bool); we constrain
// the first two components.
val filter_zipped_rows_limited_bound :
  h:cottas_ondisk_handle ->
  bound_s:option string -> bound_p:option string ->
  bound_o:option string -> bound_g:option string ->
  s_col:list (option string) -> p_col:list (option string) ->
  o_col:list (option string) -> g_col:list (option string) ->
  acc_rev:list cottas_qp_row -> acc_count:nat -> limit:nat ->
  Lemma
    (requires acc_count = L.length acc_rev /\ acc_count <= limit)
    (ensures
      (let (acc_rev', acc_count', _) =
         filter_zipped_rows_limited h bound_s bound_p bound_o bound_g
           s_col p_col o_col g_col acc_rev acc_count limit in
       acc_count' = L.length acc_rev' /\ acc_count' <= limit))
    (decreases s_col)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec filter_zipped_rows_limited_bound
  h bound_s bound_p bound_o bound_g
  s_col p_col o_col g_col acc_rev acc_count limit
  =
  if acc_count >= limit then ()
  else
    match s_col, p_col, o_col, g_col with
    | s_hd :: s_tl, p_hd :: p_tl, o_hd :: o_tl, g_hd :: g_tl ->
      let (acc_rev', acc_count') =
        match s_hd, p_hd, o_hd, g_hd with
        | Some s_tok, Some p_tok, Some o_tok, Some g_tok ->
          if cell_match bound_s s_tok &&
             cell_match bound_p p_tok &&
             cell_match bound_o o_tok &&
             graph_cell_match bound_g g_tok
          then (build_qp_row h s_tok p_tok o_tok g_tok :: acc_rev,
                acc_count + 1)
          else (acc_rev, acc_count)
        | _ -> (acc_rev, acc_count) in
      // Invariant maintained: either both grew by 1 (match path) or
      // both unchanged (no-match path).
      filter_zipped_rows_limited_bound h bound_s bound_p bound_o bound_g
        s_tl p_tl o_tl g_tl acc_rev' acc_count' limit
    | _ -> ()
#pop-options

// Lemma 4: walk_candidate_rgs_search_limited preserves
// L.length acc_rev <= limit.
//
// We strengthen to maintain acc_count = L.length acc_rev (otherwise the
// walker recursion can't see the invariant on the helper's output).
val walk_candidate_rgs_search_limited_bound :
  h:cottas_ondisk_handle ->
  bound_s:option string -> bound_p:option string ->
  bound_o:option string -> bound_g:option string ->
  candidates:list nat ->
  acc_rev:list cottas_qp_row -> acc_count:nat -> limit:nat ->
  cache:page_cache ->
  Lemma
    (requires acc_count = L.length acc_rev /\ acc_count <= limit)
    (ensures
      L.length (fst (walk_candidate_rgs_search_limited h bound_s bound_p bound_o bound_g
                      candidates acc_rev acc_count limit cache)) <= limit)
    (decreases candidates)
let rec walk_candidate_rgs_search_limited_bound
  h bound_s bound_p bound_o bound_g candidates acc_rev acc_count limit cache
  =
  if acc_count >= limit then ()
  else
    match candidates with
    | [] -> ()
    | rg_index :: rest ->
      let cap = cache.pc_capacity in
      let (s_col, c1) = pcache_decode_in_row_group cache  h.coh_path rg_index 0 cap in
      let (p_col, c2) = pcache_decode_in_row_group c1     h.coh_path rg_index 1 cap in
      let (o_col, c3) = pcache_decode_in_row_group c2     h.coh_path rg_index 2 cap in
      let (g_col, c4) = pcache_decode_in_row_group c3     h.coh_path rg_index 3 cap in
      // Compute the filter result with the same shape as the walker.
      (match s_col, p_col, o_col, g_col with
       | Some sc, Some pc, Some oc, Some gc ->
         filter_zipped_rows_limited_bound h bound_s bound_p bound_o bound_g
           sc pc oc gc acc_rev acc_count limit
       | _ -> ());
      let (acc_rev', acc_count', hit) =
        match s_col, p_col, o_col, g_col with
        | Some sc, Some pc, Some oc, Some gc ->
          filter_zipped_rows_limited h bound_s bound_p bound_o bound_g
            sc pc oc gc acc_rev acc_count limit
        | _ -> (acc_rev, acc_count, false) in
      // Either we hit (return acc_rev' which already satisfies bound)
      // or recurse with the invariant preserved.
      if hit then ()
      else
        walk_candidate_rgs_search_limited_bound h bound_s bound_p bound_o bound_g
          rest acc_rev' acc_count' limit c4
