open Prims
type pcache_key = (Prims.nat * Prims.nat)
type pcache_entry =
  {
  pce_key: pcache_key ;
  pce_value: RDF_CottasStore_ColumnSeq.cottas_column ;
  pce_age: Prims.nat }
let __proj__Mkpcache_entry__item__pce_key (projectee : pcache_entry) :
  pcache_key=
  match projectee with | { pce_key; pce_value; pce_age;_} -> pce_key
let __proj__Mkpcache_entry__item__pce_value (projectee : pcache_entry) :
  RDF_CottasStore_ColumnSeq.cottas_column=
  match projectee with | { pce_key; pce_value; pce_age;_} -> pce_value
let __proj__Mkpcache_entry__item__pce_age (projectee : pcache_entry) :
  Prims.nat=
  match projectee with | { pce_key; pce_value; pce_age;_} -> pce_age
type page_cache =
  {
  pc_entries: pcache_entry Prims.list ;
  pc_clock: Prims.nat ;
  pc_capacity: Prims.nat }
let __proj__Mkpage_cache__item__pc_entries (projectee : page_cache) :
  pcache_entry Prims.list=
  match projectee with | { pc_entries; pc_clock; pc_capacity;_} -> pc_entries
let __proj__Mkpage_cache__item__pc_clock (projectee : page_cache) :
  Prims.nat=
  match projectee with | { pc_entries; pc_clock; pc_capacity;_} -> pc_clock
let __proj__Mkpage_cache__item__pc_capacity (projectee : page_cache) :
  Prims.nat=
  match projectee with
  | { pc_entries; pc_clock; pc_capacity;_} -> pc_capacity
let pcache_empty (capacity : Prims.nat) : page_cache=
  { pc_entries = []; pc_clock = Prims.int_zero; pc_capacity = capacity }
let key_eq (k1 : pcache_key) (k2 : pcache_key) : Prims.bool=
  let uu___ = k1 in
  match uu___ with
  | (a1, b1) ->
      let uu___1 = k2 in
      (match uu___1 with | (a2, b2) -> (a1 = a2) && (b1 = b2))
let rec lookup_entry (entries : pcache_entry Prims.list) (k : pcache_key) :
  pcache_entry FStar_Pervasives_Native.option=
  match entries with
  | [] -> FStar_Pervasives_Native.None
  | e::rest ->
      if key_eq e.pce_key k
      then FStar_Pervasives_Native.Some e
      else lookup_entry rest k
let rec replace_entry (entries : pcache_entry Prims.list) (k : pcache_key)
  (new_e : pcache_entry) : pcache_entry Prims.list=
  match entries with
  | [] -> []
  | e::rest ->
      if key_eq e.pce_key k
      then new_e :: rest
      else e :: (replace_entry rest k new_e)
let rec drop_entry (entries : pcache_entry Prims.list) (k : pcache_key) :
  pcache_entry Prims.list=
  match entries with
  | [] -> []
  | e::rest -> if key_eq e.pce_key k then rest else e :: (drop_entry rest k)
let pcache_get (cache : page_cache) (k : pcache_key) :
  (RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option *
    page_cache)=
  match lookup_entry cache.pc_entries k with
  | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, cache)
  | FStar_Pervasives_Native.Some entry ->
      let new_clock = cache.pc_clock + Prims.int_one in
      let bumped =
        {
          pce_key = (entry.pce_key);
          pce_value = (entry.pce_value);
          pce_age = new_clock
        } in
      let updated =
        {
          pc_entries = (replace_entry cache.pc_entries k bumped);
          pc_clock = new_clock;
          pc_capacity = (cache.pc_capacity)
        } in
      ((FStar_Pervasives_Native.Some (entry.pce_value)), updated)
let rec find_oldest_aux (entries : pcache_entry Prims.list)
  (best_key : pcache_key) (best_age : Prims.nat) (found : Prims.bool) :
  pcache_key FStar_Pervasives_Native.option=
  match entries with
  | [] ->
      if found
      then FStar_Pervasives_Native.Some best_key
      else FStar_Pervasives_Native.None
  | e::rest ->
      if Prims.op_Negation found
      then find_oldest_aux rest e.pce_key e.pce_age true
      else
        if e.pce_age < best_age
        then find_oldest_aux rest e.pce_key e.pce_age true
        else find_oldest_aux rest best_key best_age true
let find_oldest (entries : pcache_entry Prims.list) :
  pcache_key FStar_Pervasives_Native.option=
  find_oldest_aux entries (Prims.int_zero, Prims.int_zero) Prims.int_zero
    false
let rec list_len : 'a . 'a Prims.list -> Prims.nat =
  fun xs ->
    match xs with
    | [] -> Prims.int_zero
    | uu___::rest -> Prims.int_one + (list_len rest)
let pcache_put (cache : page_cache) (k : pcache_key)
  (v : RDF_CottasStore_ColumnSeq.cottas_column) (capacity : Prims.nat) :
  page_cache=
  if capacity = Prims.int_zero
  then cache
  else
    (let new_clock = cache.pc_clock + Prims.int_one in
     let new_entry = { pce_key = k; pce_value = v; pce_age = new_clock } in
     let entries_after =
       match lookup_entry cache.pc_entries k with
       | FStar_Pervasives_Native.Some uu___1 ->
           replace_entry cache.pc_entries k new_entry
       | FStar_Pervasives_Native.None -> new_entry :: (cache.pc_entries) in
     let entries_capped =
       if (list_len entries_after) > capacity
       then
         match find_oldest entries_after with
         | FStar_Pervasives_Native.None -> entries_after
         | FStar_Pervasives_Native.Some victim_key ->
             drop_entry entries_after victim_key
       else entries_after in
     {
       pc_entries = entries_capped;
       pc_clock = new_clock;
       pc_capacity = capacity
     })
let pcache_decode_in_row_group (cache : page_cache) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) (capacity : Prims.nat) :
  (RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option *
    page_cache)=
  let key = (rg_index, col_index) in
  match pcache_get cache key with
  | (FStar_Pervasives_Native.Some v, c1) ->
      ((FStar_Pervasives_Native.Some v), c1)
  | (FStar_Pervasives_Native.None, c1) ->
      (match RDF_CottasStore_ColumnSeq.probe_parquet_column_decode_in_row_group_seq
               path rg_index col_index
       with
       | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, c1)
       | FStar_Pervasives_Native.Some v ->
           let c2 = pcache_put c1 key v capacity in
           ((FStar_Pervasives_Native.Some v), c2))
(* Phase 2.5e (issue #118): cross-call cache storage cell + realisation
   of the F*-pure `pcache_decode_in_row_group_global` assume val.

   The cache logic (LRU eviction, monotone clock, key match) lives in
   the F*-verified `pcache_get` / `pcache_put` / `pcache_decode_in_row_group`
   functions above. This shim only threads the mutable storage ref
   across calls. Rule #11(c). __PAGECACHE_GLOBAL_APPLIED__ *)
let pcache_global_capacity : Z.t = Z.of_int 256

let pcache_global_ref : page_cache ref =
  ref (pcache_empty pcache_global_capacity)

(* Stdlib.Int.t-typed counters; `open Prims` shadows `int` to `Z.t`
   in this file, so qualify with Stdlib explicitly. *)
let pcache_global_n_hits   : Stdlib.Int.t ref = Stdlib.ref 0
let pcache_global_n_misses : Stdlib.Int.t ref = Stdlib.ref 0

let pcache_decode_in_row_group_global (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat)
  : RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option =
  let cap = (!pcache_global_ref).pc_capacity in
  let key_present =
    let (v, _) = pcache_get !pcache_global_ref (rg_index, col_index) in
    match v with FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let (result, c') =
    pcache_decode_in_row_group !pcache_global_ref path rg_index col_index cap in
  pcache_global_ref := c';
  (if key_present then Stdlib.incr pcache_global_n_hits
   else Stdlib.incr pcache_global_n_misses);
  let total : Stdlib.Int.t = Stdlib.(!pcache_global_n_hits + !pcache_global_n_misses) in
  (if Stdlib.(total mod 32 = 0) then
    Printf.eprintf "[pagecache-global-trace] hits=%d misses=%d entries=%d cap=%d
%!"
      !pcache_global_n_hits !pcache_global_n_misses
      (Stdlib.List.length (!pcache_global_ref).pc_entries)
      (Z.to_int cap));
  result
let pcache_decode_in_row_group_from_table (cache : page_cache)
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  (capacity : Prims.nat) :
  (RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option *
    page_cache)=
  let key = (rg_index, col_index) in
  match pcache_get cache key with
  | (FStar_Pervasives_Native.Some v, c1) ->
      ((FStar_Pervasives_Native.Some v), c1)
  | (FStar_Pervasives_Native.None, c1) ->
      (match RDF_CottasStore_ColumnSeq.probe_parquet_column_decode_in_row_group_seq_from_table
               table path rg_index col_index
       with
       | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, c1)
       | FStar_Pervasives_Native.Some v ->
           let c2 = pcache_put c1 key v capacity in
           ((FStar_Pervasives_Native.Some v), c2))
(* Issue #98/Mim3 follow-up (2026-07-05): table-threaded sibling of
   pcache_decode_in_row_group_global above. Same cross-call storage
   cell (pcache_global_ref), same LRU logic in F*-pure
   pcache_decode_in_row_group_from_table; this shim only forwards the
   F*-computed row-group-offset table and threads the mutable ref.
   Rule #11(c). *)
let pcache_decode_in_row_group_global_from_table
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat)
  : RDF_CottasStore_ColumnSeq.cottas_column FStar_Pervasives_Native.option =
  let cap = (!pcache_global_ref).pc_capacity in
  let key_present =
    let (v, _) = pcache_get !pcache_global_ref (rg_index, col_index) in
    match v with FStar_Pervasives_Native.Some _ -> true | _ -> false in
  let (result, c') =
    pcache_decode_in_row_group_from_table !pcache_global_ref table path rg_index col_index cap in
  pcache_global_ref := c';
  (if key_present then Stdlib.incr pcache_global_n_hits
   else Stdlib.incr pcache_global_n_misses);
  let total : Stdlib.Int.t = Stdlib.(!pcache_global_n_hits + !pcache_global_n_misses) in
  (if Stdlib.(total mod 32 = 0) then
    Printf.eprintf "[pagecache-global-trace] hits=%d misses=%d entries=%d cap=%d
%!"
      !pcache_global_n_hits !pcache_global_n_misses
      (Stdlib.List.length (!pcache_global_ref).pc_entries)
      (Z.to_int cap));
  result
(* OPTIONAL/FILTER row-index-selective decode design (stage 2, issue
   #295 tracks the acknowledged RLE_DICTIONARY-fast-path gap):
   realisation of the F*-pure `pcache_decode_column_at_indices_global_
   from_table` assume val. Fallback-only: decodes the full column via
   the SAME table-threaded decoder every other `_from_table` caller
   already uses, then filters to the requested indices. Correct for
   every Parquet encoding; not yet accelerated for RLE_DICTIONARY (see
   this file's own header comment and issue #295).
   __PAGECACHE_INDEXED_APPLIED__ *)
let pcache_decode_column_at_indices_global_from_table
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  (indices : Prims.nat Prims.list)
  : (Prims.nat * Prims.string) Prims.list FStar_Pervasives_Native.option =
  match Parquet_Footer.probe_parquet_column_decode_in_row_group_from_table
          table path rg_index col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some lst ->
    let arr = Array.of_list lst in
    let len = Array.length arr in
    let pick (i : Prims.nat) : (Prims.nat * Prims.string) option =
      (* Z-domain comparisons: >=/< in this module scope may be
      rebound over Z.t (Prims), so avoid bare int operators entirely. *)
      if Z.geq i Z.zero && Z.lt i (Z.of_int len) then
        (let iv = Z.to_int i in
         match arr.(iv) with
         | FStar_Pervasives_Native.Some tok -> Some (i, tok)
         | FStar_Pervasives_Native.None -> None)
      else None
    in
    FStar_Pervasives_Native.Some (List.filter_map pick indices)
let rec indexed_decode_lookup (pairs : (Prims.nat * Prims.string) Prims.list)
  (i : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match pairs with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      if k = i
      then FStar_Pervasives_Native.Some v
      else indexed_decode_lookup rest i
type dict_pcache_entry =
  {
  dpce_key: pcache_key ;
  dpce_value: Prims.string Prims.list ;
  dpce_age: Prims.nat }
let __proj__Mkdict_pcache_entry__item__dpce_key
  (projectee : dict_pcache_entry) : pcache_key=
  match projectee with | { dpce_key; dpce_value; dpce_age;_} -> dpce_key
let __proj__Mkdict_pcache_entry__item__dpce_value
  (projectee : dict_pcache_entry) : Prims.string Prims.list=
  match projectee with | { dpce_key; dpce_value; dpce_age;_} -> dpce_value
let __proj__Mkdict_pcache_entry__item__dpce_age
  (projectee : dict_pcache_entry) : Prims.nat=
  match projectee with | { dpce_key; dpce_value; dpce_age;_} -> dpce_age
type dict_page_cache =
  {
  dpc_entries: dict_pcache_entry Prims.list ;
  dpc_clock: Prims.nat ;
  dpc_capacity: Prims.nat }
let __proj__Mkdict_page_cache__item__dpc_entries
  (projectee : dict_page_cache) : dict_pcache_entry Prims.list=
  match projectee with
  | { dpc_entries; dpc_clock; dpc_capacity;_} -> dpc_entries
let __proj__Mkdict_page_cache__item__dpc_clock (projectee : dict_page_cache)
  : Prims.nat=
  match projectee with
  | { dpc_entries; dpc_clock; dpc_capacity;_} -> dpc_clock
let __proj__Mkdict_page_cache__item__dpc_capacity
  (projectee : dict_page_cache) : Prims.nat=
  match projectee with
  | { dpc_entries; dpc_clock; dpc_capacity;_} -> dpc_capacity
let dpcache_empty (capacity : Prims.nat) : dict_page_cache=
  { dpc_entries = []; dpc_clock = Prims.int_zero; dpc_capacity = capacity }
let rec dpc_lookup_entry (entries : dict_pcache_entry Prims.list)
  (k : pcache_key) : dict_pcache_entry FStar_Pervasives_Native.option=
  match entries with
  | [] -> FStar_Pervasives_Native.None
  | e::rest ->
      if key_eq e.dpce_key k
      then FStar_Pervasives_Native.Some e
      else dpc_lookup_entry rest k
let rec dpc_replace_entry (entries : dict_pcache_entry Prims.list)
  (k : pcache_key) (new_e : dict_pcache_entry) :
  dict_pcache_entry Prims.list=
  match entries with
  | [] -> []
  | e::rest ->
      if key_eq e.dpce_key k
      then new_e :: rest
      else e :: (dpc_replace_entry rest k new_e)
let rec dpc_drop_entry (entries : dict_pcache_entry Prims.list)
  (k : pcache_key) : dict_pcache_entry Prims.list=
  match entries with
  | [] -> []
  | e::rest ->
      if key_eq e.dpce_key k then rest else e :: (dpc_drop_entry rest k)
let dpcache_get (cache : dict_page_cache) (k : pcache_key) :
  (Prims.string Prims.list FStar_Pervasives_Native.option * dict_page_cache)=
  match dpc_lookup_entry cache.dpc_entries k with
  | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, cache)
  | FStar_Pervasives_Native.Some entry ->
      let new_clock = cache.dpc_clock + Prims.int_one in
      let bumped =
        {
          dpce_key = (entry.dpce_key);
          dpce_value = (entry.dpce_value);
          dpce_age = new_clock
        } in
      let updated =
        {
          dpc_entries = (dpc_replace_entry cache.dpc_entries k bumped);
          dpc_clock = new_clock;
          dpc_capacity = (cache.dpc_capacity)
        } in
      ((FStar_Pervasives_Native.Some (entry.dpce_value)), updated)
let rec dpc_find_oldest_aux (entries : dict_pcache_entry Prims.list)
  (best_key : pcache_key) (best_age : Prims.nat) (found : Prims.bool) :
  pcache_key FStar_Pervasives_Native.option=
  match entries with
  | [] ->
      if found
      then FStar_Pervasives_Native.Some best_key
      else FStar_Pervasives_Native.None
  | e::rest ->
      if Prims.op_Negation found
      then dpc_find_oldest_aux rest e.dpce_key e.dpce_age true
      else
        if e.dpce_age < best_age
        then dpc_find_oldest_aux rest e.dpce_key e.dpce_age true
        else dpc_find_oldest_aux rest best_key best_age true
let dpc_find_oldest (entries : dict_pcache_entry Prims.list) :
  pcache_key FStar_Pervasives_Native.option=
  dpc_find_oldest_aux entries (Prims.int_zero, Prims.int_zero) Prims.int_zero
    false
let dpcache_put (cache : dict_page_cache) (k : pcache_key)
  (v : Prims.string Prims.list) (capacity : Prims.nat) : dict_page_cache=
  if capacity = Prims.int_zero
  then cache
  else
    (let new_clock = cache.dpc_clock + Prims.int_one in
     let new_entry = { dpce_key = k; dpce_value = v; dpce_age = new_clock } in
     let entries_after =
       match dpc_lookup_entry cache.dpc_entries k with
       | FStar_Pervasives_Native.Some uu___1 ->
           dpc_replace_entry cache.dpc_entries k new_entry
       | FStar_Pervasives_Native.None -> new_entry :: (cache.dpc_entries) in
     let entries_capped =
       if (list_len entries_after) > capacity
       then
         match dpc_find_oldest entries_after with
         | FStar_Pervasives_Native.None -> entries_after
         | FStar_Pervasives_Native.Some victim_key ->
             dpc_drop_entry entries_after victim_key
       else entries_after in
     {
       dpc_entries = entries_capped;
       dpc_clock = new_clock;
       dpc_capacity = capacity
     })
let dpcache_probe_dict_in_row_group_from_table (cache : dict_page_cache)
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat)
  (capacity : Prims.nat) :
  (Prims.string Prims.list FStar_Pervasives_Native.option * dict_page_cache)=
  let key = (rg_index, col_index) in
  match dpcache_get cache key with
  | (FStar_Pervasives_Native.Some v, c1) ->
      ((FStar_Pervasives_Native.Some v), c1)
  | (FStar_Pervasives_Native.None, c1) ->
      (match Parquet_Footer.probe_parquet_column_dictionary_in_row_group_from_table
               table path rg_index col_index
       with
       | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, c1)
       | FStar_Pervasives_Native.Some v ->
           let c2 = dpcache_put c1 key v capacity in
           ((FStar_Pervasives_Native.Some v), c2))
(* Tsade2 Phase E (issue #100 followup, 2026-07-06): cross-query
   DICTIONARY cache storage cell + realisation of the F*-pure
   `dpcache_probe_dict_in_row_group_global_from_table` assume val.

   LRU eviction, monotone clock, key match all live in the F*-verified
   `dpcache_get` / `dpcache_put` / `dpcache_probe_dict_in_row_group_from_table`
   functions above (mirrors `pcache_*` exactly, different value type).
   This shim only threads the mutable storage ref across calls and
   honours the FACTOIDAL_DISABLE_DICT_GLOBAL_CACHE kill switch. Rule
   #11(c): no semantic decisions, no dictionary decode logic here --
   that stays in Parquet_Footer. __PAGECACHE_GLOBAL_APPLIED__ *)
let dpcache_global_capacity : Z.t = Z.of_int 1024

let dpcache_global_ref : dict_page_cache ref =
  ref (dpcache_empty dpcache_global_capacity)

let dpcache_global_n_hits   : Stdlib.Int.t ref = Stdlib.ref 0
let dpcache_global_n_misses : Stdlib.Int.t ref = Stdlib.ref 0

let dpcache_global_disabled : bool =
  match Stdlib.Sys.getenv_opt "FACTOIDAL_DISABLE_DICT_GLOBAL_CACHE" with
  | Some "1" -> true
  | _ -> false

let dpcache_probe_dict_in_row_group_global_from_table
  (table : Parquet_Footer.parquet_row_group_offset_table)
  (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat)
  : Prims.string Prims.list FStar_Pervasives_Native.option =
  if dpcache_global_disabled then
    Parquet_Footer.probe_parquet_column_dictionary_in_row_group_from_table
      table path rg_index col_index
  else begin
    let cap = (!dpcache_global_ref).dpc_capacity in
    let key_present =
      let (v, _) = dpcache_get !dpcache_global_ref (rg_index, col_index) in
      match v with FStar_Pervasives_Native.Some _ -> true | _ -> false in
    let (result, c') =
      dpcache_probe_dict_in_row_group_from_table !dpcache_global_ref table path rg_index col_index cap in
    dpcache_global_ref := c';
    (if key_present then Stdlib.incr dpcache_global_n_hits
     else Stdlib.incr dpcache_global_n_misses);
    let total : Stdlib.Int.t = Stdlib.(!dpcache_global_n_hits + !dpcache_global_n_misses) in
    (if Stdlib.(total mod 32 = 0) then
      Printf.eprintf "[dictcache-global-trace] hits=%d misses=%d entries=%d cap=%d
%!"
        !dpcache_global_n_hits !dpcache_global_n_misses
        (Stdlib.List.length (!dpcache_global_ref).dpc_entries)
        (Z.to_int cap));
    result
  end
