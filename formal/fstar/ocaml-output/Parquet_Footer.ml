open Prims

(* __PARQUET_ASCII_STRING_FAST_PATH__
   Patched by 103_parquet_ascii_string_fast_path.sh.
   See the patch file for the safety argument: every Parquet_Footer
   call site that reaches one of these helpers passes an ASCII-only
   hex string, so codepoint ops collapse onto byte ops. *)
module FStar_String = struct
  include FStar_String
  (* The enclosing file does `open Prims`, which shadows OCaml's `int`
     and `string` to Prims aliases (Z.t and Stdlib.String.t). All the
     stdlib references below have to be fully qualified to escape that. *)
  let index (s : Stdlib.String.t) (i : Z.t) : Stdlib.Int.t =
    Stdlib.Char.code (Stdlib.String.unsafe_get s (Z.to_int i))
  let strlen (s : Stdlib.String.t) : Z.t =
    Z.of_int (Stdlib.String.length s)
  let length = strlen
  let sub (s : Stdlib.String.t) (i : Z.t) (j : Z.t) : Stdlib.String.t =
    Stdlib.String.sub s (Z.to_int i) (Z.to_int j)
  (* string_of_list: ASCII fast-path. Original walks the list O(n^2)
     via BatUTF8.init+List.at; we materialise once into a Bytes.
     The fstar.lib runtime declares `type char = FStar_Char.char =
     int`, so the list is a list of codepoint ints. Safe iff every
     codepoint fits in one byte, which is true for the
     ascii_string_of_hex_slice path (chars come from byte_at_hex
     and are always in [0,255]). *)
  let string_of_list (l : FStar_Char.char list) : Stdlib.String.t =
    let n = Stdlib.List.length l in
    let b = Stdlib.Bytes.create n in
    Stdlib.List.iteri (fun i c ->
      Stdlib.Bytes.unsafe_set b i
        (Stdlib.Char.unsafe_chr (c land 0xff))) l;
    Stdlib.Bytes.unsafe_to_string b
end

type parquet_footer =
  {
  pf_metadata_len: Prims.nat ;
  pf_footer_len: Prims.nat ;
  pf_magic: Prims.string }
let __proj__Mkparquet_footer__item__pf_metadata_len
  (projectee : parquet_footer) : Prims.nat=
  match projectee with
  | { pf_metadata_len; pf_footer_len; pf_magic;_} -> pf_metadata_len
let __proj__Mkparquet_footer__item__pf_footer_len
  (projectee : parquet_footer) : Prims.nat=
  match projectee with
  | { pf_metadata_len; pf_footer_len; pf_magic;_} -> pf_footer_len
let __proj__Mkparquet_footer__item__pf_magic (projectee : parquet_footer) :
  Prims.string=
  match projectee with
  | { pf_metadata_len; pf_footer_len; pf_magic;_} -> pf_magic
type compact_field =
  {
  cf_id: Prims.nat ;
  cf_type: Prims.nat ;
  cf_value_start: Prims.nat ;
  cf_next: Prims.nat }
let __proj__Mkcompact_field__item__cf_id (projectee : compact_field) :
  Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_id
let __proj__Mkcompact_field__item__cf_type (projectee : compact_field) :
  Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_type
let __proj__Mkcompact_field__item__cf_value_start (projectee : compact_field)
  : Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_value_start
let __proj__Mkcompact_field__item__cf_next (projectee : compact_field) :
  Prims.nat=
  match projectee with
  | { cf_id; cf_type; cf_value_start; cf_next;_} -> cf_next
type compact_list_info =
  {
  cli_count: Prims.nat ;
  cli_etype: Prims.nat ;
  cli_payload_start: Prims.nat }
let __proj__Mkcompact_list_info__item__cli_count
  (projectee : compact_list_info) : Prims.nat=
  match projectee with
  | { cli_count; cli_etype; cli_payload_start;_} -> cli_count
let __proj__Mkcompact_list_info__item__cli_etype
  (projectee : compact_list_info) : Prims.nat=
  match projectee with
  | { cli_count; cli_etype; cli_payload_start;_} -> cli_etype
let __proj__Mkcompact_list_info__item__cli_payload_start
  (projectee : compact_list_info) : Prims.nat=
  match projectee with
  | { cli_count; cli_etype; cli_payload_start;_} -> cli_payload_start
let parquet_magic : Prims.string= "PAR1"
let parquet_magic_hex : Prims.string= "50415231"
(* ---- Mim2 (issue #100 Phases B+C) ---------------------------------
   Process-wide path-keyed byte cache. The first call to parquet_read_*
   for a given path slurps the entire file into a single OCaml string
   (immutable, GC-tracked). Subsequent calls return slices in O(count).
   This is the in-process equivalent of mmap'ing the parquet file: at
   the F* abstraction layer, the path IS the region handle, the cache
   IS the mapped pages, and slicing IS a pointer dereference. We use
   really_input_string instead of Unix.map_file because parliament is
   66MB; for >1GB corpora a swap to Unix.map_file is one-line.

   Without this cache, every probe_parquet_* call (and the column-
   decode path inside it) reopens the file via open_in_bin, re-seeks,
   and reads. The footer alone is read on every probe (the metadata
   ASCII strings, num-rows, row-group-count, column descriptors, etc.).
   For the parliament corpus that's hundreds of file-opens per SELECT
   and hundreds of zstd decompressions; the daemon hangs.

   This block (tail_impl) is inserted at the location of the original
   parquet_read_tail_hex stub — earlier in the file than the
   parquet_read_range_hex stub. So we define the byte cache + the raw
   helpers + parquet_read_tail / parquet_read_range here, and the
   range_impl block (inserted later) only adds parquet_read_range_hex. *)

let __mim2_file_bytes_cache : (string, string) Hashtbl.t = Hashtbl.create 7

(* In-memory bytes store, stage 1 (docs/designissues/2026-07-06-
   inmemory-bytes-store.md). Seed the SAME process-wide cache
   `__mim2_load_file_bytes`/`parquet_read_*` already consult, under a
   synthetic handle that names no real file. Every later
   `parquet_read_tail_hex`/`parquet_read_range_hex` call for `handle`
   is served straight out of this cache -- the `Sys.file_exists`
   fallback in `__mim2_load_file_bytes` is never reached for a handle
   registered here, because the cache lookup happens first.

   Last-registration-wins (`Hashtbl.replace`, not `Hashtbl.add`):
   re-registering the same handle with new bytes is well-defined and
   intentional (lets a caller rebind a synthetic handle to fresh bytes
   without restarting the process), matching how a real file's cache
   entry would need an explicit invalidation to pick up an on-disk
   change too -- this backend is no less consistent than the file
   backend it shares a cache with. *)
let register_memory_buffer (handle : Prims.string) (raw_bytes : Prims.string) : unit =
  Hashtbl.replace __mim2_file_bytes_cache handle raw_bytes

let __mim2_load_file_bytes path =
  match Hashtbl.find_opt __mim2_file_bytes_cache path with
  | Some s -> Some s
  | None ->
    if not (Sys.file_exists path) then None
    else
      let ic = open_in_bin path in
      let module S = Stdlib in
      Fun.protect
        ~finally:(fun () -> close_in_noerr ic)
        (fun () ->
           let file_len = in_channel_length ic in
           let s = really_input_string ic file_len in
           Hashtbl.add __mim2_file_bytes_cache path s;
           Some s)

let parquet_read_range (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  let module S = Stdlib in
  match __mim2_load_file_bytes path with
  | None -> FStar_Pervasives_Native.None
  | Some buf ->
    let file_len = String.length buf in
    let offset = Z.to_int start in
    let want = Z.to_int count in
    if S.(offset < 0 || want < 0 || offset > file_len || offset + want > file_len)
    then FStar_Pervasives_Native.None
    else FStar_Pervasives_Native.Some (String.sub buf offset want)

let parquet_read_tail (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  let module S = Stdlib in
  match __mim2_load_file_bytes path with
  | None -> FStar_Pervasives_Native.None
  | Some buf ->
    let file_len = String.length buf in
    let want = Z.to_int count in
    if S.(file_len < want) then FStar_Pervasives_Native.None
    else
      let start = S.(file_len - want) in
      FStar_Pervasives_Native.Some (String.sub buf start want)

(* Precomputed two-hex-char string per byte value (0x00 .. 0xFF).
   `Printf.sprintf "%02X"` re-parses its format string on every call;
   in the per-byte `String.iter` loop below that cost dominates for
   footer-sized (KB) buffers called repeatedly. Table lookup is the
   same output, just without the per-byte format-string overhead. *)
let __mim2_hex_byte_table : string array =
  Array.init 256 (fun i -> Printf.sprintf "%02X" i)

(* Hex-encode a raw string. Buffer-once so the ~250MB row-group
   payloads don't trigger O(N^2) string concat. *)
let __mim2_hex_encode raw =
  let module S = Stdlib in
  let b = Buffer.create S.(2 * String.length raw) in
  String.iter
    (fun ch -> Buffer.add_string b __mim2_hex_byte_table.(Char.code ch))
    raw;
  Buffer.contents b

(* Mim3 (2026-07-05, docs/designissues/2026-07-05-disk-backed-db-perf-review.md):
   memoize the hex-encoded TAIL (the Parquet footer, in practice) per
   (path, count). `footer.pf_footer_len` is the same value for the whole
   life of a (write-once) COTTAS artifact, so every one of the ~15
   `probe_parquet_*` call sites in this module that re-derives a
   row-group/column-chunk locator from scratch — once per (row_group,
   column) pair walked, e.g. by `probe_parquet_column_decode_all_row_groups`
   or an unpruned per-row-group search — was re-reading AND re-hex-
   encoding the entire footer from scratch on every single call. Because
   the footer's metadata length itself grows roughly linearly with
   row-group count (more row groups = more column-chunk stat structs),
   and the number of per-row-group probe calls during an unpruned column
   walk also grows linearly with row-group count, the unmemoized cost
   was quadratic-ish in row-group count for a fixed corpus size (measured:
   50,000-quad fixture, 2 vs 25 row groups, same clustered content, only
   ROW_GROUP_SIZE changed: 0.60s -> 10.3s, ~17x; gene corpus 8 vs 44
   groups: 73ms -> 1,877ms, ~24-25x). This cache turns every probe after
   the first for a given (path, count) into an O(1) hashtable hit instead
   of an O(footer_size) re-encode. Pure memoization of a deterministic,
   already-cached-bytes (Mim2) computation — no new decode/interpretation
   logic; the returned hex strings are byte-identical to the unmemoized
   path. Rule #11(c)/#15 compliant. *)
(* `open Prims` (top of this file) shadows `int` to mean `Prims.int`
   (= Z.t); the cache keys need plain OCaml machine ints (what
   `Z.to_int` returns), so qualify explicitly with `Stdlib.Int.t`
   (same pattern as `Cottas_ondisk_runtime.pint` in
   experimental_ocaml_glue/cottas_ondisk_runtime.sh). *)
let __mim2_tail_hex_cache : (string * Stdlib.Int.t, string) Hashtbl.t = Hashtbl.create 17
let __mim2_range_hex_cache : (string * Stdlib.Int.t * Stdlib.Int.t, string) Hashtbl.t = Hashtbl.create 257

let parquet_read_tail_hex (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  let key = (path, Z.to_int count) in
  match Hashtbl.find_opt __mim2_tail_hex_cache key with
  | Some hex -> FStar_Pervasives_Native.Some hex
  | None ->
    match parquet_read_tail path count with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some raw ->
      let hex = __mim2_hex_encode raw in
      Hashtbl.add __mim2_tail_hex_cache key hex;
      FStar_Pervasives_Native.Some hex
(* parquet_read_range_hex: depends on helpers defined earlier in
   the tail_impl block (Mim2 byte cache for issue #100 Phases B+C).

   Mim3 (2026-07-05, docs/designissues/2026-07-05-disk-backed-db-perf-review.md
   roadmap item "characterise and fix the on-disk reader's per-row-group
   cost"): memoize the *hex-encoded* result per (path, start, count), not
   just the raw bytes. `Parquet.Footer.probe_parquet_column_chunk_in_row_group_locator`
   re-derives a column chunk's byte offsets from the footer on every single
   (row_group, column) probe, and every higher-level per-row-group probe
   (page header size/offset/num_values/etc.) re-reads its own small range
   at the same offset independently. Without this cache, a query that
   walks every row group of a column (e.g. no presence-bitmap pruning
   because the bound predicate is present in every group) re-hex-encodes
   the SAME parquet-page byte ranges once per sibling probe function. *)

let parquet_read_range_hex (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  let key = (path, Z.to_int start, Z.to_int count) in
  match Hashtbl.find_opt __mim2_range_hex_cache key with
  | Some hex -> FStar_Pervasives_Native.Some hex
  | None ->
    match parquet_read_range path start count with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some raw ->
      let hex = __mim2_hex_encode raw in
      Hashtbl.add __mim2_range_hex_cache key hex;
      FStar_Pervasives_Native.Some hex

external parquet_zstd_decompress_hex_runtime :
  Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option
  = "caml_parquet_zstd_decompress_hex"

let parquet_zstd_decompress_hex (compressed_hex : Prims.string) (expected_size : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  parquet_zstd_decompress_hex_runtime compressed_hex (Prims.string_of_int expected_size)
let hex_nibble (c : FStar_Char.char) :
  Prims.nat FStar_Pervasives_Native.option=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (48))) && (code <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (code - (Prims.of_int (48)))
  else
    if (code >= (Prims.of_int (65))) && (code <= (Prims.of_int (70)))
    then
      FStar_Pervasives_Native.Some
        ((code - (Prims.of_int (65))) + (Prims.of_int (10)))
    else
      if (code >= (Prims.of_int (97))) && (code <= (Prims.of_int (102)))
      then
        FStar_Pervasives_Native.Some
          ((code - (Prims.of_int (97))) + (Prims.of_int (10)))
      else FStar_Pervasives_Native.None
let byte_at_hex (s : Prims.string) (i : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((hex_nibble (FStar_String.index s i)),
          (hex_nibble (FStar_String.index s (i + Prims.int_one))))
  with
  | (FStar_Pervasives_Native.Some hi, FStar_Pervasives_Native.Some lo) ->
      let value =
        (((((((((((((((hi + hi) + hi) + hi) + hi) + hi) + hi) + hi) + hi) +
                 hi)
                + hi)
               + hi)
              + hi)
             + hi)
            + hi)
           + hi)
          + lo in
      FStar_Pervasives_Native.Some value
  | uu___ -> FStar_Pervasives_Native.None
let le_u32_at_hex (s : Prims.string) (start : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((byte_at_hex s start), (byte_at_hex s (start + (Prims.of_int (2)))),
          (byte_at_hex s (start + (Prims.of_int (4)))),
          (byte_at_hex s (start + (Prims.of_int (6)))))
  with
  | (FStar_Pervasives_Native.Some n0, FStar_Pervasives_Native.Some n1,
     FStar_Pervasives_Native.Some n2, FStar_Pervasives_Native.Some n3) ->
      let b0 = FStar_UInt32.uint_to_t n0 in
      let b1 =
        FStar_UInt32.shift_left (FStar_UInt32.uint_to_t n1)
          (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
      let b2 =
        FStar_UInt32.shift_left (FStar_UInt32.uint_to_t n2)
          (FStar_UInt32.uint_to_t (Prims.of_int (16))) in
      let b3 =
        FStar_UInt32.shift_left (FStar_UInt32.uint_to_t n3)
          (FStar_UInt32.uint_to_t (Prims.of_int (24))) in
      FStar_Pervasives_Native.Some
        (FStar_UInt32.v
           (FStar_UInt32.logor b0
              (FStar_UInt32.logor b1 (FStar_UInt32.logor b2 b3))))
  | uu___ -> FStar_Pervasives_Native.None
let parse_parquet_footer_tail_hex (tail : Prims.string) :
  parquet_footer FStar_Pervasives_Native.option=
  let len = FStar_String.strlen tail in
  if len < (Prims.of_int (16))
  then FStar_Pervasives_Native.None
  else
    (let magic =
       FStar_String.sub tail (len - (Prims.of_int (8))) (Prims.of_int (8)) in
     if magic <> parquet_magic_hex
     then FStar_Pervasives_Native.None
     else
       (let footer_start = len - (Prims.of_int (16)) in
        match le_u32_at_hex tail footer_start with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some meta_len ->
            FStar_Pervasives_Native.Some
              {
                pf_metadata_len = meta_len;
                pf_footer_len = (meta_len + (Prims.of_int (8)));
                pf_magic = parquet_magic
              }))
let is_printable_byte (b : Prims.nat) : Prims.bool=
  (b >= (Prims.of_int (32))) && (b <= (Prims.of_int (126)))
let finish_ascii_run (current : FStar_Char.char Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  if (FStar_List_Tot_Base.length current) = Prims.int_zero
  then acc
  else (FStar_String.string_of_list (FStar_List_Tot_Base.rev current)) :: acc
let rec extract_ascii_strings_hex (hex : Prims.string) (pos : Prims.nat)
  (current : FStar_Char.char Prims.list) (acc : Prims.string Prims.list) :
  Prims.string Prims.list=
  if (pos + Prims.int_one) >= (FStar_String.strlen hex)
  then FStar_List_Tot_Base.rev (finish_ascii_run current acc)
  else
    (match byte_at_hex hex pos with
     | FStar_Pervasives_Native.None ->
         FStar_List_Tot_Base.rev (finish_ascii_run current acc)
     | FStar_Pervasives_Native.Some b ->
         if is_printable_byte b
         then
           extract_ascii_strings_hex hex (pos + (Prims.of_int (2)))
             ((FStar_Char.char_of_int b) :: current) acc
         else
           extract_ascii_strings_hex hex (pos + (Prims.of_int (2))) []
             (finish_ascii_run current acc))
let probe_parquet_footer (path : Prims.string) :
  parquet_footer FStar_Pervasives_Native.option=
  match parquet_read_tail_hex path (Prims.of_int (8)) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some tail -> parse_parquet_footer_tail_hex tail
let probe_parquet_metadata_strings (path : Prims.string) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             FStar_Pervasives_Native.Some
               (extract_ascii_strings_hex
                  (FStar_String.sub footer_hex Prims.int_zero meta_hex_len)
                  Prims.int_zero [] [])
           else FStar_Pervasives_Native.None)
let compact_t_stop : Prims.nat= Prims.int_zero
let compact_t_bool_true : Prims.nat= Prims.int_one
let compact_t_bool_false : Prims.nat= (Prims.of_int (2))
let compact_t_byte : Prims.nat= (Prims.of_int (3))
let compact_t_i16 : Prims.nat= (Prims.of_int (4))
let compact_t_i32 : Prims.nat= (Prims.of_int (5))
let compact_t_i64 : Prims.nat= (Prims.of_int (6))
let compact_t_double : Prims.nat= (Prims.of_int (7))
let compact_t_binary : Prims.nat= (Prims.of_int (8))
let compact_t_list : Prims.nat= (Prims.of_int (9))
let compact_t_set : Prims.nat= (Prims.of_int (10))
let compact_t_map : Prims.nat= (Prims.of_int (11))
let compact_t_struct : Prims.nat= (Prims.of_int (12))
let high_nibble (b : Prims.nat) : Prims.nat=
  FStar_UInt32.v
    (FStar_UInt32.shift_right (FStar_UInt32.uint_to_t b)
       (FStar_UInt32.uint_to_t (Prims.of_int (4))))
let low_nibble (b : Prims.nat) : Prims.nat=
  FStar_UInt32.v
    (FStar_UInt32.logand (FStar_UInt32.uint_to_t b)
       (FStar_UInt32.uint_to_t (Prims.of_int (15))))
let low_7_bits (b : Prims.nat) : Prims.nat=
  FStar_UInt32.v
    (FStar_UInt32.logand (FStar_UInt32.uint_to_t b)
       (FStar_UInt32.uint_to_t (Prims.of_int (127))))
let rec scale_pow2 (x : Prims.nat) (shift : Prims.nat) : Prims.nat=
  if shift = Prims.int_zero
  then x
  else scale_pow2 (x + x) (shift - Prims.int_one)
let rec mul_nat (x : Prims.nat) (y : Prims.nat) : Prims.nat=
  if y = Prims.int_zero
  then Prims.int_zero
  else x + (mul_nat x (y - Prims.int_one))
let pred_nat (n : Prims.nat) : Prims.nat= n - Prims.int_one
let succ_nat (n : Prims.nat) : Prims.nat= n + Prims.int_one
let div_nat_pos (x : Prims.nat) (y : Prims.nat) : Prims.nat= x / y
let le_u24_at_hex (s : Prims.string) (start : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((byte_at_hex s start), (byte_at_hex s (start + (Prims.of_int (2)))),
          (byte_at_hex s (start + (Prims.of_int (4)))))
  with
  | (FStar_Pervasives_Native.Some n0, FStar_Pervasives_Native.Some n1,
     FStar_Pervasives_Native.Some n2) ->
      FStar_Pervasives_Native.Some
        ((n0 + (scale_pow2 n1 (Prims.of_int (8)))) +
           (scale_pow2 n2 (Prims.of_int (16))))
  | uu___ -> FStar_Pervasives_Native.None
let rec skip_varint_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           let next = pos + (Prims.of_int (2)) in
           if b < (Prims.of_int (128))
           then FStar_Pervasives_Native.Some next
           else skip_varint_hex hex next (fuel - Prims.int_one))
let rec skip_n_values_hex (hex : Prims.string) (etype : Prims.nat)
  (count : Prims.nat) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if count = Prims.int_zero
    then FStar_Pervasives_Native.Some pos
    else
      (match skip_compact_value_hex hex etype pos (fuel - Prims.int_one) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some next ->
           skip_n_values_hex hex etype (count - Prims.int_one) next
             (fuel - Prims.int_one))
and skip_struct_fields_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some header ->
           if header = compact_t_stop
           then FStar_Pervasives_Native.Some (pos + (Prims.of_int (2)))
           else
             (let ftype = low_nibble header in
              let delta = high_nibble header in
              let value_pos =
                if delta = Prims.int_zero
                then
                  match skip_varint_hex hex (pos + (Prims.of_int (2)))
                          (fuel - Prims.int_one)
                  with
                  | FStar_Pervasives_Native.Some p -> p
                  | FStar_Pervasives_Native.None -> pos + (Prims.of_int (2))
                else pos + (Prims.of_int (2)) in
              if
                (delta = Prims.int_zero) &&
                  (value_pos = (pos + (Prims.of_int (2))))
              then FStar_Pervasives_Native.None
              else
                (match skip_compact_value_hex hex ftype value_pos
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some next ->
                     skip_struct_fields_hex hex next (fuel - Prims.int_one))))
and skip_compact_value_hex (hex : Prims.string) (ftype : Prims.nat)
  (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (ftype = compact_t_bool_true) || (ftype = compact_t_bool_false)
    then FStar_Pervasives_Native.Some pos
    else
      if ftype = compact_t_byte
      then
        (if (pos + Prims.int_one) < (FStar_String.strlen hex)
         then FStar_Pervasives_Native.Some (pos + (Prims.of_int (2)))
         else FStar_Pervasives_Native.None)
      else
        if
          ((ftype = compact_t_i16) || (ftype = compact_t_i32)) ||
            (ftype = compact_t_i64)
        then skip_varint_hex hex pos (fuel - Prims.int_one)
        else
          if ftype = compact_t_double
          then
            (if (pos + (Prims.of_int (15))) < (FStar_String.strlen hex)
             then FStar_Pervasives_Native.Some (pos + (Prims.of_int (16)))
             else FStar_Pervasives_Native.None)
          else
            if ftype = compact_t_binary
            then
              (match skip_varint_hex hex pos (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some len_end ->
                   let rec decode_varint_hex p shift acc fuel2 =
                     if fuel2 = Prims.int_zero
                     then FStar_Pervasives_Native.None
                     else
                       if (p + Prims.int_one) >= (FStar_String.strlen hex)
                       then FStar_Pervasives_Native.None
                       else
                         (match byte_at_hex hex p with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let payload = low_7_bits b in
                              let acc' = acc + (scale_pow2 payload shift) in
                              if b < (Prims.of_int (128))
                              then FStar_Pervasives_Native.Some acc'
                              else
                                decode_varint_hex (p + (Prims.of_int (2)))
                                  (shift + (Prims.of_int (7))) acc'
                                  (fuel2 - Prims.int_one)) in
                   (match decode_varint_hex pos Prims.int_zero Prims.int_zero
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some blen ->
                        let data_end = len_end + (blen + blen) in
                        if data_end <= (FStar_String.strlen hex)
                        then FStar_Pervasives_Native.Some data_end
                        else FStar_Pervasives_Native.None))
            else
              if (ftype = compact_t_list) || (ftype = compact_t_set)
              then
                (if (pos + Prims.int_one) >= (FStar_String.strlen hex)
                 then FStar_Pervasives_Native.None
                 else
                   (match byte_at_hex hex pos with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some header ->
                        let size_nibble = high_nibble header in
                        let etype = low_nibble header in
                        if size_nibble < (Prims.of_int (15))
                        then
                          skip_n_values_hex hex etype size_nibble
                            (pos + (Prims.of_int (2))) (fuel - Prims.int_one)
                        else
                          (let rec decode_varint_hex p shift acc fuel2 =
                             if fuel2 = Prims.int_zero
                             then FStar_Pervasives_Native.None
                             else
                               if
                                 (p + Prims.int_one) >=
                                   (FStar_String.strlen hex)
                               then FStar_Pervasives_Native.None
                               else
                                 (match byte_at_hex hex p with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some b ->
                                      let payload = low_7_bits b in
                                      let acc' =
                                        acc + (scale_pow2 payload shift) in
                                      if b < (Prims.of_int (128))
                                      then
                                        FStar_Pervasives_Native.Some
                                          (acc', (p + (Prims.of_int (2))))
                                      else
                                        decode_varint_hex
                                          (p + (Prims.of_int (2)))
                                          (shift + (Prims.of_int (7))) acc'
                                          (fuel2 - Prims.int_one)) in
                           match decode_varint_hex (pos + (Prims.of_int (2)))
                                   Prims.int_zero Prims.int_zero
                                   (fuel - Prims.int_one)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some
                               (count, after_count) ->
                               skip_n_values_hex hex etype count after_count
                                 (fuel - Prims.int_one))))
              else
                if ftype = compact_t_struct
                then skip_struct_fields_hex hex pos (fuel - Prims.int_one)
                else
                  if ftype = compact_t_map
                  then FStar_Pervasives_Native.None
                  else FStar_Pervasives_Native.None
let zigzag_decode_nat (n : Prims.nat) : Prims.nat= n / (Prims.of_int (2))
let zigzag_decode_int (n : Prims.nat) : Prims.int=
  if ((mod) n (Prims.of_int (2))) = Prims.int_zero
  then n / (Prims.of_int (2))
  else Prims.int_zero - ((n / (Prims.of_int (2))) + Prims.int_one)
let rec decode_varint_value_with_end_hex (hex : Prims.string) (p : Prims.nat)
  (shift : Prims.nat) (acc : Prims.nat) (fuel : Prims.nat) :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (p + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex p with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           let payload = low_7_bits b in
           let acc' = acc + (scale_pow2 payload shift) in
           if b < (Prims.of_int (128))
           then FStar_Pervasives_Native.Some (acc', (p + (Prims.of_int (2))))
           else
             decode_varint_value_with_end_hex hex (p + (Prims.of_int (2)))
               (shift + (Prims.of_int (7))) acc' (fuel - Prims.int_one))
let rec decode_varint_value_hex (hex : Prims.string) (p : Prims.nat)
  (shift : Prims.nat) (acc : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match decode_varint_value_with_end_hex hex p shift acc fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (n, uu___) -> FStar_Pervasives_Native.Some n
let decode_compact_list_info_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : compact_list_info FStar_Pervasives_Native.option=
  if (pos + Prims.int_one) >= (FStar_String.strlen hex)
  then FStar_Pervasives_Native.None
  else
    (match byte_at_hex hex pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some header ->
         let count_nibble = high_nibble header in
         let etype = low_nibble header in
         if count_nibble < (Prims.of_int (15))
         then
           FStar_Pervasives_Native.Some
             {
               cli_count = count_nibble;
               cli_etype = etype;
               cli_payload_start = (pos + (Prims.of_int (2)))
             }
         else
           (match decode_varint_value_with_end_hex hex
                    (pos + (Prims.of_int (2))) Prims.int_zero Prims.int_zero
                    fuel
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (count, payload_start) ->
                FStar_Pervasives_Native.Some
                  {
                    cli_count = count;
                    cli_etype = etype;
                    cli_payload_start = payload_start
                  }))
let decode_compact_list_count_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match decode_compact_list_info_hex hex pos fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some info ->
      FStar_Pervasives_Native.Some (info.cli_count)
let decode_compact_binary_hex (hex : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match decode_varint_value_with_end_hex hex pos Prims.int_zero
          Prims.int_zero fuel
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (blen, payload_start) ->
      let chars_hex_len = blen + blen in
      let payload_end = payload_start + chars_hex_len in
      if payload_end > (FStar_String.strlen hex)
      then FStar_Pervasives_Native.None
      else
        (let rec build_chars p remaining acc =
           if remaining = Prims.int_zero
           then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
           else
             if (p + Prims.int_one) >= payload_end
             then FStar_Pervasives_Native.None
             else
               (match byte_at_hex hex p with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some b ->
                    build_chars (p + (Prims.of_int (2)))
                      (remaining - Prims.int_one) ((FStar_Char.char_of_int b)
                      :: acc)) in
         match build_chars payload_start blen [] with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some chars ->
             FStar_Pervasives_Native.Some (FStar_String.string_of_list chars))
let nth_compact_list_element_start_hex (hex : Prims.string)
  (list_pos : Prims.nat) (index : Prims.nat) (fuel : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match decode_compact_list_info_hex hex list_pos fuel with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some info ->
      if index >= info.cli_count
      then FStar_Pervasives_Native.None
      else
        (let rec loop remaining p fuel2 =
           if fuel2 = Prims.int_zero
           then FStar_Pervasives_Native.None
           else
             if remaining = Prims.int_zero
             then FStar_Pervasives_Native.Some p
             else
               (match skip_compact_value_hex hex info.cli_etype p
                        (fuel2 - Prims.int_one)
                with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some next ->
                    loop (remaining - Prims.int_one) next
                      (fuel2 - Prims.int_one)) in
         loop index info.cli_payload_start fuel)
let rec nth_field_hex (hex : Prims.string) (target_id : Prims.nat)
  (pos : Prims.nat) (prev_id : Prims.nat) (fuel : Prims.nat) :
  compact_field FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some header ->
           if header = compact_t_stop
           then FStar_Pervasives_Native.None
           else
             (let ftype = low_nibble header in
              let delta = high_nibble header in
              let rec decode_varint_hex p shift acc fuel2 =
                if fuel2 = Prims.int_zero
                then FStar_Pervasives_Native.None
                else
                  if (p + Prims.int_one) >= (FStar_String.strlen hex)
                  then FStar_Pervasives_Native.None
                  else
                    (match byte_at_hex hex p with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some b ->
                         let payload = low_7_bits b in
                         let acc' = acc + (scale_pow2 payload shift) in
                         if b < (Prims.of_int (128))
                         then
                           FStar_Pervasives_Native.Some
                             (acc', (p + (Prims.of_int (2))))
                         else
                           decode_varint_hex (p + (Prims.of_int (2)))
                             (shift + (Prims.of_int (7))) acc'
                             (fuel2 - Prims.int_one)) in
              let id_and_value_pos =
                if delta = Prims.int_zero
                then
                  match decode_varint_hex (pos + (Prims.of_int (2)))
                          Prims.int_zero Prims.int_zero
                          (fuel - Prims.int_one)
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (raw, p) ->
                      FStar_Pervasives_Native.Some
                        ((zigzag_decode_nat raw), p)
                else
                  FStar_Pervasives_Native.Some
                    ((prev_id + delta), (pos + (Prims.of_int (2)))) in
              match id_and_value_pos with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (field_id, value_pos) ->
                  (match skip_compact_value_hex hex ftype value_pos
                           (fuel - Prims.int_one)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some next ->
                       if field_id = target_id
                       then
                         FStar_Pervasives_Native.Some
                           {
                             cf_id = field_id;
                             cf_type = ftype;
                             cf_value_start = value_pos;
                             cf_next = next
                           }
                       else
                         nth_field_hex hex target_id next field_id
                           (fuel - Prims.int_one))))
let probe_parquet_num_rows (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (3)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_i64
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_varint_value_hex meta_hex
                             field.cf_value_start Prims.int_zero
                             Prims.int_zero meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some raw ->
                         FStar_Pervasives_Native.Some (zigzag_decode_nat raw)))
           else FStar_Pervasives_Native.None)
let cottas_format_version : Prims.nat= (Prims.of_int (445))
let parse_file_metadata_version_hex (meta_hex : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match nth_field_hex meta_hex Prims.int_one Prims.int_zero Prims.int_zero
          (FStar_String.strlen meta_hex)
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some field ->
      if field.cf_type <> compact_t_i32
      then FStar_Pervasives_Native.None
      else
        (match decode_varint_value_hex meta_hex field.cf_value_start
                 Prims.int_zero Prims.int_zero (FStar_String.strlen meta_hex)
         with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some raw ->
             FStar_Pervasives_Native.Some (zigzag_decode_nat raw))
let probe_parquet_file_metadata_version (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             parse_file_metadata_version_hex
               (FStar_String.sub footer_hex Prims.int_zero meta_hex_len)
           else FStar_Pervasives_Native.None)
let probe_parquet_row_group_count (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    decode_compact_list_count_hex meta_hex
                      field.cf_value_start meta_hex_len)
           else FStar_Pervasives_Native.None)
let probe_parquet_first_row_group_num_rows (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some info ->
                         if
                           (info.cli_count = Prims.int_zero) ||
                             (info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex (Prims.of_int (3))
                                    info.cli_payload_start Prims.int_zero
                                    meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some row_group_field ->
                                if row_group_field.cf_type <> compact_t_i64
                                then FStar_Pervasives_Native.None
                                else
                                  (match decode_varint_value_hex meta_hex
                                           row_group_field.cf_value_start
                                           Prims.int_zero Prims.int_zero
                                           meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some raw ->
                                       FStar_Pervasives_Native.Some
                                         (zigzag_decode_nat raw)))))
           else FStar_Pervasives_Native.None)
let probe_parquet_first_row_group_column_count (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some field ->
                  if field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some info ->
                         if
                           (info.cli_count = Prims.int_zero) ||
                             (info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    info.cli_payload_start Prims.int_zero
                                    meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some row_group_field ->
                                if row_group_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  decode_compact_list_count_hex meta_hex
                                    row_group_field.cf_value_start
                                    meta_hex_len)))
           else FStar_Pervasives_Native.None)
let probe_parquet_first_column_name (path : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           Prims.int_zero meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (3))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   path_field ->
                                                   if
                                                     path_field.cf_type <>
                                                       compact_t_list
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match nth_compact_list_element_start_hex
                                                              meta_hex
                                                              path_field.cf_value_start
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          path_start ->
                                                          decode_compact_binary_hex
                                                            meta_hex
                                                            path_start
                                                            meta_hex_len)))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_first_column_data_page_offset (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           Prims.int_zero meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (9))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   offset_field ->
                                                   if
                                                     offset_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              offset_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_name (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (3))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   path_field ->
                                                   if
                                                     path_field.cf_type <>
                                                       compact_t_list
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match nth_compact_list_element_start_hex
                                                              meta_hex
                                                              path_field.cf_value_start
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          path_start ->
                                                          decode_compact_binary_hex
                                                            meta_hex
                                                            path_start
                                                            meta_hex_len)))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_num_values (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (5))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   num_values_field ->
                                                   if
                                                     num_values_field.cf_type
                                                       <> compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              num_values_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_total_compressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (7))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   size_field ->
                                                   if
                                                     size_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              size_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_total_uncompressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (6))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   size_field ->
                                                   if
                                                     size_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              size_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let parquet_compression_codec_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "UNCOMPRESSED"
  else
    if n = Prims.int_one
    then "SNAPPY"
    else
      if n = (Prims.of_int (2))
      then "GZIP"
      else
        if n = (Prims.of_int (3))
        then "LZO"
        else
          if n = (Prims.of_int (4))
          then "BROTLI"
          else
            if n = (Prims.of_int (5))
            then "LZ4"
            else
              if n = (Prims.of_int (6))
              then "ZSTD"
              else if n = (Prims.of_int (7)) then "LZ4_RAW" else "UNKNOWN"
let probe_parquet_column_compression_codec (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (4))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   codec_field ->
                                                   if
                                                     codec_field.cf_type <>
                                                       compact_t_i32
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              codec_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (parquet_compression_codec_name
                                                               (zigzag_decode_nat
                                                                  raw)))))))))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_data_page_offset (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (9))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   offset_field ->
                                                   if
                                                     offset_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              offset_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let parquet_page_type_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "DATA_PAGE"
  else
    if n = Prims.int_one
    then "INDEX_PAGE"
    else
      if n = (Prims.of_int (2))
      then "DICTIONARY_PAGE"
      else if n = (Prims.of_int (3)) then "DATA_PAGE_V2" else "UNKNOWN"
let parquet_encoding_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "PLAIN"
  else
    if n = Prims.int_one
    then "GROUP_VAR_INT"
    else
      if n = (Prims.of_int (2))
      then "PLAIN_DICTIONARY"
      else
        if n = (Prims.of_int (3))
        then "RLE"
        else
          if n = (Prims.of_int (4))
          then "BIT_PACKED"
          else
            if n = (Prims.of_int (5))
            then "DELTA_BINARY_PACKED"
            else
              if n = (Prims.of_int (6))
              then "DELTA_LENGTH_BYTE_ARRAY"
              else
                if n = (Prims.of_int (7))
                then "DELTA_BYTE_ARRAY"
                else
                  if n = (Prims.of_int (8))
                  then "RLE_DICTIONARY"
                  else
                    if n = (Prims.of_int (9))
                    then "BYTE_STREAM_SPLIT"
                    else "UNKNOWN"
let rec nat_mod (x : Prims.nat) (y : Prims.nat) : Prims.nat=
  if x < y then x else nat_mod (x - y) y
let zstd_block_type_name (n : Prims.nat) : Prims.string=
  if n = Prims.int_zero
  then "RAW"
  else
    if n = Prims.int_one
    then "RLE"
    else
      if n = (Prims.of_int (2))
      then "COMPRESSED"
      else if n = (Prims.of_int (3)) then "RESERVED" else "UNKNOWN"
let zstd_frame_content_size_field_bytes (descriptor : Prims.nat) : Prims.nat=
  let fcs_flag = descriptor / (Prims.of_int (64)) in
  let single_segment =
    nat_mod (descriptor / (Prims.of_int (32))) (Prims.of_int (2)) in
  if fcs_flag = Prims.int_zero
  then
    (if single_segment = Prims.int_one then Prims.int_one else Prims.int_zero)
  else
    if fcs_flag = Prims.int_one
    then (Prims.of_int (2))
    else
      if fcs_flag = (Prims.of_int (2))
      then (Prims.of_int (4))
      else (Prims.of_int (8))
let zstd_dictionary_id_field_bytes (descriptor : Prims.nat) : Prims.nat=
  let did_flag = nat_mod descriptor (Prims.of_int (4)) in
  if did_flag = Prims.int_zero
  then Prims.int_zero
  else
    if did_flag = Prims.int_one
    then Prims.int_one
    else
      if did_flag = (Prims.of_int (2))
      then (Prims.of_int (2))
      else (Prims.of_int (4))
let zstd_window_descriptor_bytes (descriptor : Prims.nat) : Prims.nat=
  let single_segment =
    nat_mod (descriptor / (Prims.of_int (32))) (Prims.of_int (2)) in
  if single_segment = Prims.int_one then Prims.int_zero else Prims.int_one
let probe_parquet_column_page_header_type (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex Prims.int_one Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some type_field ->
                if type_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex page_hex
                           type_field.cf_value_start Prims.int_zero
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some
                         (parquet_page_type_name (zigzag_decode_nat raw)))))
let probe_parquet_column_page_header_uncompressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (2)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some size_field ->
                if size_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex page_hex
                           size_field.cf_value_start Prims.int_zero
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_page_header_compressed_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (3)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some size_field ->
                if size_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex page_hex
                           size_field.cf_value_start Prims.int_zero
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_page_header_num_values (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex Prims.int_one
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some num_values_field ->
                       if num_values_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  num_values_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (zigzag_decode_nat raw)))))
let probe_parquet_column_page_header_length (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match skip_struct_fields_hex page_hex Prims.int_zero
                    (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some end_hex ->
                FStar_Pervasives_Native.Some (end_hex / (Prims.of_int (2)))))
let probe_parquet_column_page_payload_offset (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_data_page_offset path col_index),
          (probe_parquet_column_page_header_length path col_index))
  with
  | (FStar_Pervasives_Native.Some page_offset, FStar_Pervasives_Native.Some
     header_len) -> FStar_Pervasives_Native.Some (page_offset + header_len)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_page_header_data_encoding (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (2))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_page_header_definition_level_encoding
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (3))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_page_header_repetition_level_encoding
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (4))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_page_payload_magic_hex (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match parquet_read_range_hex path payload_offset (Prims.of_int (4))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some payload_hex ->
           if (FStar_String.strlen payload_hex) >= (Prims.of_int (8))
           then
             FStar_Pervasives_Native.Some
               (FStar_String.sub payload_hex Prims.int_zero
                  (Prims.of_int (8)))
           else FStar_Pervasives_Native.None)
let probe_parquet_column_zstd_frame_header_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match parquet_read_range_hex path payload_offset (Prims.of_int (18))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some payload_hex ->
           if (FStar_String.strlen payload_hex) < (Prims.of_int (10))
           then FStar_Pervasives_Native.None
           else
             (match byte_at_hex payload_hex (Prims.of_int (8)) with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some descriptor ->
                  FStar_Pervasives_Native.Some
                    ((((Prims.of_int (5)) +
                         (zstd_window_descriptor_bytes descriptor))
                        + (zstd_dictionary_id_field_bytes descriptor))
                       + (zstd_frame_content_size_field_bytes descriptor))))
let probe_parquet_column_zstd_first_block_type (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_zstd_frame_header_size path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some frame_header_size ->
           (match parquet_read_range_hex path
                    (payload_offset + frame_header_size) (Prims.of_int (3))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some block_hex ->
                if (FStar_String.strlen block_hex) < (Prims.of_int (6))
                then FStar_Pervasives_Native.None
                else
                  (match le_u24_at_hex block_hex Prims.int_zero with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some block_header ->
                       let block_type =
                         nat_mod (block_header / (Prims.of_int (2)))
                           (Prims.of_int (4)) in
                       FStar_Pervasives_Native.Some
                         (zstd_block_type_name block_type))))
let probe_parquet_column_zstd_first_block_last_flag (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_zstd_frame_header_size path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some frame_header_size ->
           (match parquet_read_range_hex path
                    (payload_offset + frame_header_size) (Prims.of_int (3))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some block_hex ->
                if (FStar_String.strlen block_hex) < (Prims.of_int (6))
                then FStar_Pervasives_Native.None
                else
                  (match le_u24_at_hex block_hex Prims.int_zero with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some block_header ->
                       FStar_Pervasives_Native.Some
                         (nat_mod block_header (Prims.of_int (2))))))
let probe_parquet_column_zstd_first_block_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_zstd_frame_header_size path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some frame_header_size ->
           (match parquet_read_range_hex path
                    (payload_offset + frame_header_size) (Prims.of_int (3))
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some block_hex ->
                if (FStar_String.strlen block_hex) < (Prims.of_int (6))
                then FStar_Pervasives_Native.None
                else
                  (match le_u24_at_hex block_hex Prims.int_zero with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some block_header ->
                       FStar_Pervasives_Native.Some
                         (block_header / (Prims.of_int (8))))))
let probe_parquet_column_zstd_first_block_header_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_zstd_first_block_type path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some uu___ ->
      FStar_Pervasives_Native.Some (Prims.of_int (3))
let probe_parquet_column_zstd_first_block_payload_offset
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_page_payload_offset path col_index),
          (probe_parquet_column_zstd_frame_header_size path col_index),
          (probe_parquet_column_zstd_first_block_header_size path col_index))
  with
  | (FStar_Pervasives_Native.Some payload_offset,
     FStar_Pervasives_Native.Some frame_header_size,
     FStar_Pervasives_Native.Some block_header_size) ->
      FStar_Pervasives_Native.Some
        ((payload_offset + frame_header_size) + block_header_size)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_zstd_frame_accounted_size (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_zstd_frame_header_size path col_index),
          (probe_parquet_column_zstd_first_block_header_size path col_index),
          (probe_parquet_column_zstd_first_block_size path col_index))
  with
  | (FStar_Pervasives_Native.Some frame_header_size,
     FStar_Pervasives_Native.Some block_header_size,
     FStar_Pervasives_Native.Some block_size) ->
      FStar_Pervasives_Native.Some
        ((frame_header_size + block_header_size) + block_size)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_zstd_frame_size_matches_page (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_page_header_compressed_size path col_index),
          (probe_parquet_column_zstd_frame_accounted_size path col_index))
  with
  | (FStar_Pervasives_Native.Some page_compressed_size,
     FStar_Pervasives_Native.Some accounted) ->
      if page_compressed_size = accounted
      then FStar_Pervasives_Native.Some Prims.int_one
      else FStar_Pervasives_Native.Some Prims.int_zero
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_decompressed_payload_hex (path : Prims.string)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_page_payload_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_offset ->
      (match probe_parquet_column_page_header_compressed_size path col_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some compressed_size ->
           (match probe_parquet_column_page_header_uncompressed_size path
                    col_index
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some uncompressed_size ->
                (match parquet_read_range_hex path payload_offset
                         compressed_size
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some compressed_hex ->
                     (match probe_parquet_column_compression_codec path
                              col_index
                      with
                      | FStar_Pervasives_Native.Some "UNCOMPRESSED" ->
                          FStar_Pervasives_Native.Some compressed_hex
                      | uu___ ->
                          parquet_zstd_decompress_hex compressed_hex
                            uncompressed_size))))
let probe_parquet_column_decompressed_payload_prefix_hex
  (path : Prims.string) (col_index : Prims.nat) (prefix_bytes : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      let want = prefix_bytes + prefix_bytes in
      if want <= (FStar_String.strlen payload_hex)
      then
        FStar_Pervasives_Native.Some
          (FStar_String.sub payload_hex Prims.int_zero want)
      else FStar_Pervasives_Native.Some payload_hex
let probe_parquet_column_decompressed_payload_hex_length
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      FStar_Pervasives_Native.Some
        ((FStar_String.strlen payload_hex) / (Prims.of_int (2)))
let probe_parquet_column_first_level_section_length (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      if (FStar_String.strlen payload_hex) < (Prims.of_int (8))
      then FStar_Pervasives_Native.None
      else le_u32_at_hex payload_hex Prims.int_zero
let probe_parquet_column_delta_length_byte_array_values_offset
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_first_level_section_length path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some section_len ->
      FStar_Pervasives_Native.Some ((Prims.of_int (4)) + section_len)
let probe_parquet_column_delta_length_byte_array_values_prefix_hex
  (path : Prims.string) (col_index : Prims.nat) (prefix_bytes : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     value_offset) ->
      let start = value_offset + value_offset in
      if start > (FStar_String.strlen payload_hex)
      then FStar_Pervasives_Native.None
      else
        (let remaining = (FStar_String.strlen payload_hex) - start in
         let want = prefix_bytes + prefix_bytes in
         let take = if want <= remaining then want else remaining in
         FStar_Pervasives_Native.Some
           (FStar_String.sub payload_hex start take))
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_delta_length_byte_array_block_size
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (n, uu___) ->
           FStar_Pervasives_Native.Some n)
let probe_parquet_column_delta_length_byte_array_miniblock_count
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (n, uu___1) ->
                FStar_Pervasives_Native.Some n))
let probe_parquet_column_delta_length_byte_array_value_count
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (n, uu___2) ->
                     FStar_Pervasives_Native.Some n)))
let probe_parquet_column_delta_length_byte_array_first_length
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (32))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (raw, uu___3) ->
                          FStar_Pervasives_Native.Some
                            (zigzag_decode_nat raw)))))
let probe_parquet_column_delta_length_byte_array_first_min_delta
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.int FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (64))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (uu___3, p4) ->
                          (match decode_varint_value_with_end_hex values_hex
                                   p4 Prims.int_zero Prims.int_zero
                                   (FStar_String.strlen values_hex)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (raw, uu___4) ->
                               FStar_Pervasives_Native.Some
                                 (zigzag_decode_int raw))))))
let probe_parquet_column_delta_length_byte_array_first_bit_width
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (64))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (uu___3, p4) ->
                          (match decode_varint_value_with_end_hex values_hex
                                   p4 Prims.int_zero Prims.int_zero
                                   (FStar_String.strlen values_hex)
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uu___4, p5) ->
                               if
                                 (p5 + Prims.int_one) >=
                                   (FStar_String.strlen values_hex)
                               then FStar_Pervasives_Native.None
                               else
                                 (match byte_at_hex values_hex p5 with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some width ->
                                      FStar_Pervasives_Native.Some width))))))
let rec packed_lsb_value_hex (hex : Prims.string) (byte_start : Prims.nat)
  (start_bit : Prims.nat) (remaining : Prims.nat) (out_shift : Prims.nat)
  (acc : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (let absolute_bit = start_bit + out_shift in
     let byte_index =
       byte_start +
         (mul_nat (absolute_bit / (Prims.of_int (8))) (Prims.of_int (2))) in
     if (byte_index + Prims.int_one) >= (FStar_String.strlen hex)
     then FStar_Pervasives_Native.None
     else
       (match byte_at_hex hex byte_index with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some b ->
            let bit_in_byte = (mod) absolute_bit (Prims.of_int (8)) in
            let bit =
              (mod) (b / (scale_pow2 Prims.int_one bit_in_byte))
                (Prims.of_int (2)) in
            let acc' =
              if bit = Prims.int_zero
              then acc
              else acc + (scale_pow2 Prims.int_one out_shift) in
            packed_lsb_value_hex hex byte_start start_bit
              (remaining - Prims.int_one) (out_shift + Prims.int_one) acc'))
let probe_parquet_column_delta_length_byte_array_length_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.int FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_values_prefix_hex path
          col_index (Prims.of_int (96))
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some values_hex ->
      (match decode_varint_value_with_end_hex values_hex Prims.int_zero
               Prims.int_zero Prims.int_zero (FStar_String.strlen values_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (uu___, p1) ->
           (match decode_varint_value_with_end_hex values_hex p1
                    Prims.int_zero Prims.int_zero
                    (FStar_String.strlen values_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___1, p2) ->
                (match decode_varint_value_with_end_hex values_hex p2
                         Prims.int_zero Prims.int_zero
                         (FStar_String.strlen values_hex)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___2, p3) ->
                     (match decode_varint_value_with_end_hex values_hex p3
                              Prims.int_zero Prims.int_zero
                              (FStar_String.strlen values_hex)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (first_raw, p4) ->
                          let first_len = zigzag_decode_int first_raw in
                          if value_index = Prims.int_zero
                          then FStar_Pervasives_Native.Some first_len
                          else
                            (match decode_varint_value_with_end_hex
                                     values_hex p4 Prims.int_zero
                                     Prims.int_zero
                                     (FStar_String.strlen values_hex)
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some
                                 (min_delta_raw, p5) ->
                                 let min_delta =
                                   zigzag_decode_int min_delta_raw in
                                 if
                                   (p5 + Prims.int_one) >=
                                     (FStar_String.strlen values_hex)
                                 then FStar_Pervasives_Native.None
                                 else
                                   (match byte_at_hex values_hex p5 with
                                    | FStar_Pervasives_Native.None ->
                                        FStar_Pervasives_Native.None
                                    | FStar_Pervasives_Native.Some width ->
                                        let packed_start =
                                          p5 + (Prims.of_int (16)) in
                                        let rec accumulate_lengths
                                          delta_index current =
                                          if delta_index >= value_index
                                          then
                                            FStar_Pervasives_Native.Some
                                              current
                                          else
                                            (let start_bit =
                                               mul_nat delta_index width in
                                             match packed_lsb_value_hex
                                                     values_hex packed_start
                                                     start_bit width
                                                     Prims.int_zero
                                                     Prims.int_zero
                                             with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some
                                                 adjusted ->
                                                 let next =
                                                   (current + min_delta) +
                                                     adjusted in
                                                 let delta_index' =
                                                   succ_nat delta_index in
                                                 accumulate_lengths
                                                   delta_index' next) in
                                        accumulate_lengths Prims.int_zero
                                          first_len))))))
let rec count_used_miniblocks (remaining : Prims.nat)
  (values_per_miniblock : Prims.nat) : Prims.nat=
  if remaining = Prims.int_zero
  then Prims.int_zero
  else
    if remaining <= values_per_miniblock
    then Prims.int_one
    else
      succ_nat
        (count_used_miniblocks (remaining - values_per_miniblock)
           values_per_miniblock)
let probe_parquet_column_delta_length_byte_array_length_nat_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_length_at path col_index
          value_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some n ->
      if n < Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some n
let probe_parquet_column_delta_length_byte_array_total_value_bytes
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_value_count path
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some value_count ->
      let rec loop remaining idx acc =
        if remaining = Prims.int_zero
        then FStar_Pervasives_Native.Some acc
        else
          (match probe_parquet_column_delta_length_byte_array_length_nat_at
                   path col_index idx
           with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some len ->
               loop (pred_nat remaining) (succ_nat idx) (acc + len)) in
      loop value_count Prims.int_zero Prims.int_zero
let probe_parquet_column_delta_length_byte_array_value_data_offset
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex_length path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index),
          (probe_parquet_column_delta_length_byte_array_total_value_bytes
             path col_index))
  with
  | (FStar_Pervasives_Native.Some payload_len, FStar_Pervasives_Native.Some
     values_offset, FStar_Pervasives_Native.Some total_value_bytes) ->
      if values_offset > payload_len
      then FStar_Pervasives_Native.None
      else
        (let values_stream_len = payload_len - values_offset in
         if total_value_bytes > values_stream_len
         then FStar_Pervasives_Native.None
         else
           FStar_Pervasives_Native.Some
             (values_stream_len - total_value_bytes))
  | uu___ -> FStar_Pervasives_Native.None
let rec ascii_string_of_hex_slice (hex : Prims.string) (pos : Prims.nat)
  (remaining : Prims.nat) (acc : FStar_Char.char Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then
    FStar_Pervasives_Native.Some
      (FStar_String.string_of_list (FStar_List_Tot_Base.rev acc))
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           ascii_string_of_hex_slice hex (pos + (Prims.of_int (2)))
             (remaining - Prims.int_one) ((FStar_Char.char_of_int b) :: acc))
let probe_parquet_column_delta_length_byte_array_value_hex_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index),
          (probe_parquet_column_delta_length_byte_array_value_data_offset
             path col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     values_offset, FStar_Pervasives_Native.Some value_data_offset) ->
      let values_start = values_offset + value_data_offset in
      let rec sum_previous_lengths remaining idx acc =
        if remaining = Prims.int_zero
        then FStar_Pervasives_Native.Some acc
        else
          (match probe_parquet_column_delta_length_byte_array_length_nat_at
                   path col_index idx
           with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some len ->
               sum_previous_lengths (pred_nat remaining) (succ_nat idx)
                 (acc + len)) in
      (match ((sum_previous_lengths value_index Prims.int_zero Prims.int_zero),
               (probe_parquet_column_delta_length_byte_array_length_nat_at
                  path col_index value_index))
       with
       | (FStar_Pervasives_Native.Some prior_len,
          FStar_Pervasives_Native.Some value_len) ->
           let start_byte = values_start + prior_len in
           let start = mul_nat start_byte (Prims.of_int (2)) in
           let want = mul_nat value_len (Prims.of_int (2)) in
           if (start + want) <= (FStar_String.strlen payload_hex)
           then
             FStar_Pervasives_Native.Some
               (FStar_String.sub payload_hex start want)
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_delta_length_byte_array_value_string_at
  (path : Prims.string) (col_index : Prims.nat) (value_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_value_hex_at path
          col_index value_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some value_hex ->
      ascii_string_of_hex_slice value_hex Prims.int_zero
        ((FStar_String.strlen value_hex) / (Prims.of_int (2))) []
type dlba_page_cache =
  {
  dpc_payload_hex: Prims.string ;
  dpc_values_offset: Prims.nat ;
  dpc_value_count: Prims.nat ;
  dpc_first_length: Prims.nat ;
  dpc_min_delta: Prims.int ;
  dpc_bit_width: Prims.nat ;
  dpc_packed_start: Prims.nat ;
  dpc_value_data_offset: Prims.nat ;
  dpc_lengths: Prims.nat Prims.list ;
  dpc_value_starts: Prims.nat Prims.list }
let __proj__Mkdlba_page_cache__item__dpc_payload_hex
  (projectee : dlba_page_cache) : Prims.string=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_payload_hex
let __proj__Mkdlba_page_cache__item__dpc_values_offset
  (projectee : dlba_page_cache) : Prims.nat=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_values_offset
let __proj__Mkdlba_page_cache__item__dpc_value_count
  (projectee : dlba_page_cache) : Prims.nat=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_value_count
let __proj__Mkdlba_page_cache__item__dpc_first_length
  (projectee : dlba_page_cache) : Prims.nat=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_first_length
let __proj__Mkdlba_page_cache__item__dpc_min_delta
  (projectee : dlba_page_cache) : Prims.int=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_min_delta
let __proj__Mkdlba_page_cache__item__dpc_bit_width
  (projectee : dlba_page_cache) : Prims.nat=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_bit_width
let __proj__Mkdlba_page_cache__item__dpc_packed_start
  (projectee : dlba_page_cache) : Prims.nat=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_packed_start
let __proj__Mkdlba_page_cache__item__dpc_value_data_offset
  (projectee : dlba_page_cache) : Prims.nat=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_value_data_offset
let __proj__Mkdlba_page_cache__item__dpc_lengths
  (projectee : dlba_page_cache) : Prims.nat Prims.list=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_lengths
let __proj__Mkdlba_page_cache__item__dpc_value_starts
  (projectee : dlba_page_cache) : Prims.nat Prims.list=
  match projectee with
  | { dpc_payload_hex; dpc_values_offset; dpc_value_count; dpc_first_length;
      dpc_min_delta; dpc_bit_width; dpc_packed_start; dpc_value_data_offset;
      dpc_lengths; dpc_value_starts;_} -> dpc_value_starts
let decode_one_dlba_delta (values_hex : Prims.string)
  (packed_start : Prims.nat) (bit_width : Prims.nat) (min_delta : Prims.int)
  (delta_index : Prims.nat) (current_len : Prims.int) :
  Prims.int FStar_Pervasives_Native.option=
  let start_bit = mul_nat delta_index bit_width in
  match packed_lsb_value_hex values_hex packed_start start_bit bit_width
          Prims.int_zero Prims.int_zero
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some adjusted ->
      FStar_Pervasives_Native.Some ((current_len + min_delta) + adjusted)
let decode_one_dlba_delta_at_miniblock (values_hex : Prims.string)
  (mb_packed_start : Prims.nat) (bit_width : Prims.nat)
  (min_delta : Prims.int) (mb_pos : Prims.nat) (current_len : Prims.int) :
  Prims.int FStar_Pervasives_Native.option=
  let start_bit = mul_nat mb_pos bit_width in
  match packed_lsb_value_hex values_hex mb_packed_start start_bit bit_width
          Prims.int_zero Prims.int_zero
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some adjusted ->
      FStar_Pervasives_Native.Some ((current_len + min_delta) + adjusted)
let miniblock_hex_size (values_per_miniblock : Prims.nat)
  (bit_width : Prims.nat) : Prims.nat=
  (mul_nat values_per_miniblock bit_width) / (Prims.of_int (4))
let widths_byte_at (values_hex : Prims.string) (widths_offset : Prims.nat)
  (idx : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  let p = widths_offset + (mul_nat idx (Prims.of_int (2))) in
  if (p + Prims.int_one) >= (FStar_String.strlen values_hex)
  then FStar_Pervasives_Native.None
  else
    (match byte_at_hex values_hex p with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some b ->
         let n = b in FStar_Pervasives_Native.Some n)
let rec build_dlba_length_list (values_hex : Prims.string)
  (vh_len : Prims.nat) (block_size : Prims.nat) (miniblocks : Prims.nat)
  (values_per_miniblock : Prims.nat) (min_delta : Prims.int)
  (widths_offset : Prims.nat) (mb_packed_start : Prims.nat)
  (bit_width : Prims.nat) (mb_idx : Prims.nat) (mb_pos : Prims.nat)
  (remaining : Prims.nat) (current_len : Prims.int)
  (acc : Prims.nat Prims.list) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
  else
    if current_len < Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      if values_per_miniblock = Prims.int_zero
      then FStar_Pervasives_Native.None
      else
        (let safe_len = current_len in
         let acc' = safe_len :: acc in
         if remaining = Prims.int_one
         then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc')
         else
           (let mb_pos' = mb_pos + Prims.int_one in
            if mb_pos' < values_per_miniblock
            then
              match decode_one_dlba_delta_at_miniblock values_hex
                      mb_packed_start bit_width min_delta mb_pos current_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some next_len ->
                  build_dlba_length_list values_hex vh_len block_size
                    miniblocks values_per_miniblock min_delta widths_offset
                    mb_packed_start bit_width mb_idx mb_pos'
                    (remaining - Prims.int_one) next_len acc'
            else
              (match decode_one_dlba_delta_at_miniblock values_hex
                       mb_packed_start bit_width min_delta mb_pos current_len
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some next_len ->
                   let next_mb_packed_start =
                     mb_packed_start +
                       (miniblock_hex_size values_per_miniblock bit_width) in
                   let mb_idx' = mb_idx + Prims.int_one in
                   if mb_idx' < miniblocks
                   then
                     (match widths_byte_at values_hex widths_offset mb_idx'
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some next_bw ->
                          build_dlba_length_list values_hex vh_len block_size
                            miniblocks values_per_miniblock min_delta
                            widths_offset next_mb_packed_start next_bw
                            mb_idx' Prims.int_zero
                            (remaining - Prims.int_one) next_len acc')
                   else
                     (match decode_varint_value_with_end_hex values_hex
                              next_mb_packed_start Prims.int_zero
                              Prims.int_zero vh_len
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (md_raw, after_md) ->
                          let new_min_delta = zigzag_decode_int md_raw in
                          let new_widths_offset = after_md in
                          let new_packed_start =
                            new_widths_offset +
                              (mul_nat miniblocks (Prims.of_int (2))) in
                          if
                            (new_widths_offset + Prims.int_one) >=
                              (FStar_String.strlen values_hex)
                          then FStar_Pervasives_Native.None
                          else
                            (match byte_at_hex values_hex new_widths_offset
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some new_bw ->
                                 let new_bw_nat = new_bw in
                                 build_dlba_length_list values_hex vh_len
                                   block_size miniblocks values_per_miniblock
                                   new_min_delta new_widths_offset
                                   new_packed_start new_bw_nat Prims.int_zero
                                   Prims.int_zero (remaining - Prims.int_one)
                                   next_len acc')))))
let rec prefix_sums (lengths : Prims.nat Prims.list) (running : Prims.nat)
  (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  match lengths with
  | [] -> FStar_List_Tot_Base.rev acc
  | hd::tl -> prefix_sums tl (running + hd) (running :: acc)
let rec sum_nat_list_aux (xs : Prims.nat Prims.list) (acc : Prims.nat) :
  Prims.nat=
  match xs with | [] -> acc | hd::tl -> sum_nat_list_aux tl (acc + hd)
let sum_nat_list (xs : Prims.nat Prims.list) : Prims.nat=
  sum_nat_list_aux xs Prims.int_zero
let probe_parquet_column_delta_length_byte_array_page_cache
  (path : Prims.string) (col_index : Prims.nat) :
  dlba_page_cache FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex path col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset path
             col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     values_offset) ->
      let payload_len_hex = FStar_String.strlen payload_hex in
      let values_start_hex = mul_nat values_offset (Prims.of_int (2)) in
      if values_start_hex > payload_len_hex
      then FStar_Pervasives_Native.None
      else
        (let values_hex =
           FStar_String.sub payload_hex values_start_hex
             (payload_len_hex - values_start_hex) in
         let vh_len = FStar_String.strlen values_hex in
         match decode_varint_value_with_end_hex values_hex Prims.int_zero
                 Prims.int_zero Prims.int_zero vh_len
         with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (block_size, p1) ->
             (match decode_varint_value_with_end_hex values_hex p1
                      Prims.int_zero Prims.int_zero vh_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (miniblocks, p2) ->
                  if miniblocks = Prims.int_zero
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_varint_value_with_end_hex values_hex p2
                             Prims.int_zero Prims.int_zero vh_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (value_count, p3) ->
                         (match decode_varint_value_with_end_hex values_hex
                                  p3 Prims.int_zero Prims.int_zero vh_len
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (first_raw, p4) ->
                              let first_length = zigzag_decode_nat first_raw in
                              (match decode_varint_value_with_end_hex
                                       values_hex p4 Prims.int_zero
                                       Prims.int_zero vh_len
                               with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some
                                   (min_delta_raw, p5) ->
                                   let min_delta =
                                     zigzag_decode_int min_delta_raw in
                                   if (p5 + Prims.int_one) >= vh_len
                                   then FStar_Pervasives_Native.None
                                   else
                                     (match byte_at_hex values_hex p5 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          bit_width ->
                                          let widths_offset = p5 in
                                          let packed_start =
                                            p5 +
                                              (mul_nat miniblocks
                                                 (Prims.of_int (2))) in
                                          let values_per_miniblock =
                                            if miniblocks > Prims.int_zero
                                            then
                                              div_nat_pos block_size
                                                miniblocks
                                            else Prims.int_zero in
                                          (match build_dlba_length_list
                                                   values_hex vh_len
                                                   block_size miniblocks
                                                   values_per_miniblock
                                                   min_delta widths_offset
                                                   packed_start bit_width
                                                   Prims.int_zero
                                                   Prims.int_zero value_count
                                                   first_length []
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some
                                               lengths ->
                                               let total_value_bytes =
                                                 sum_nat_list lengths in
                                               let payload_byte_len =
                                                 payload_len_hex /
                                                   (Prims.of_int (2)) in
                                               if
                                                 values_offset >
                                                   payload_byte_len
                                               then
                                                 FStar_Pervasives_Native.None
                                               else
                                                 (let values_stream_len =
                                                    payload_byte_len -
                                                      values_offset in
                                                  if
                                                    total_value_bytes >
                                                      values_stream_len
                                                  then
                                                    FStar_Pervasives_Native.None
                                                  else
                                                    (let value_data_offset =
                                                       values_stream_len -
                                                         total_value_bytes in
                                                     let starts =
                                                       prefix_sums lengths
                                                         Prims.int_zero [] in
                                                     FStar_Pervasives_Native.Some
                                                       {
                                                         dpc_payload_hex =
                                                           payload_hex;
                                                         dpc_values_offset =
                                                           values_offset;
                                                         dpc_value_count =
                                                           value_count;
                                                         dpc_first_length =
                                                           first_length;
                                                         dpc_min_delta =
                                                           min_delta;
                                                         dpc_bit_width =
                                                           bit_width;
                                                         dpc_packed_start =
                                                           packed_start;
                                                         dpc_value_data_offset
                                                           =
                                                           value_data_offset;
                                                         dpc_lengths =
                                                           lengths;
                                                         dpc_value_starts =
                                                           starts
                                                       })))))))))
  | uu___ -> FStar_Pervasives_Native.None
let rec slice_all_dlba_values (payload_hex : Prims.string)
  (values_start_byte : Prims.nat) (lengths : Prims.nat Prims.list)
  (starts : Prims.nat Prims.list)
  (acc : Prims.string FStar_Pervasives_Native.option Prims.list) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  match (lengths, starts) with
  | ([], uu___) -> FStar_List_Tot_Base.rev acc
  | (uu___, []) -> FStar_List_Tot_Base.rev acc
  | (len::lts, st::sts) ->
      let start_byte = values_start_byte + st in
      let start = mul_nat start_byte (Prims.of_int (2)) in
      let want = mul_nat len (Prims.of_int (2)) in
      let slice =
        if (start + want) <= (FStar_String.strlen payload_hex)
        then
          FStar_Pervasives_Native.Some
            (FStar_String.sub payload_hex start want)
        else FStar_Pervasives_Native.None in
      slice_all_dlba_values payload_hex values_start_byte lts sts (slice ::
        acc)
let dlba_page_decode_all_value_hex (cache : dlba_page_cache) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  let values_start_byte =
    cache.dpc_values_offset + cache.dpc_value_data_offset in
  slice_all_dlba_values cache.dpc_payload_hex values_start_byte
    cache.dpc_lengths cache.dpc_value_starts []
let rec ascii_strings_of_hex_slices
  (slices : Prims.string FStar_Pervasives_Native.option Prims.list)
  (acc : Prims.string FStar_Pervasives_Native.option Prims.list) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  match slices with
  | [] -> FStar_List_Tot_Base.rev acc
  | (FStar_Pervasives_Native.None)::tl ->
      ascii_strings_of_hex_slices tl (FStar_Pervasives_Native.None :: acc)
  | (FStar_Pervasives_Native.Some hx)::tl ->
      let s =
        ascii_string_of_hex_slice hx Prims.int_zero
          ((FStar_String.strlen hx) / (Prims.of_int (2))) [] in
      ascii_strings_of_hex_slices tl (s :: acc)
let dlba_page_decode_all_strings (cache : dlba_page_cache) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  ascii_strings_of_hex_slices (dlba_page_decode_all_value_hex cache) []
let probe_parquet_column_delta_length_byte_array_decode_all
  (path : Prims.string) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_page_cache path
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some cache ->
      FStar_Pervasives_Native.Some (dlba_page_decode_all_strings cache)
let probe_parquet_column_dictionary_page_offset (path : Prims.string)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (row_groups_info.cli_count = Prims.int_zero) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_field_hex meta_hex Prims.int_one
                                    row_groups_info.cli_payload_start
                                    Prims.int_zero meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some columns_field ->
                                if columns_field.cf_type <> compact_t_list
                                then FStar_Pervasives_Native.None
                                else
                                  (match nth_compact_list_element_start_hex
                                           meta_hex
                                           columns_field.cf_value_start
                                           col_index meta_hex_len
                                   with
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                                   | FStar_Pervasives_Native.Some
                                       column_chunk_start ->
                                       (match nth_field_hex meta_hex
                                                (Prims.of_int (3))
                                                column_chunk_start
                                                Prims.int_zero meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            metadata_field ->
                                            if
                                              metadata_field.cf_type <>
                                                compact_t_struct
                                            then FStar_Pervasives_Native.None
                                            else
                                              (match nth_field_hex meta_hex
                                                       (Prims.of_int (11))
                                                       metadata_field.cf_value_start
                                                       Prims.int_zero
                                                       meta_hex_len
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   offset_field ->
                                                   if
                                                     offset_field.cf_type <>
                                                       compact_t_i64
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match decode_varint_value_hex
                                                              meta_hex
                                                              offset_field.cf_value_start
                                                              Prims.int_zero
                                                              Prims.int_zero
                                                              meta_hex_len
                                                      with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.Some
                                                          raw ->
                                                          FStar_Pervasives_Native.Some
                                                            (zigzag_decode_nat
                                                               raw))))))))
           else FStar_Pervasives_Native.None)
let parquet_page_header_uncompressed_size_at (path : Prims.string)
  (page_offset : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match parquet_read_range_hex path page_offset (Prims.of_int (128)) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_hex ->
      (match nth_field_hex page_hex (Prims.of_int (2)) Prims.int_zero
               Prims.int_zero (FStar_String.strlen page_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some size_field ->
           if size_field.cf_type <> compact_t_i32
           then FStar_Pervasives_Native.None
           else
             (match decode_varint_value_hex page_hex
                      size_field.cf_value_start Prims.int_zero Prims.int_zero
                      (FStar_String.strlen page_hex)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some raw ->
                  FStar_Pervasives_Native.Some (zigzag_decode_nat raw)))
let parquet_page_header_compressed_size_at (path : Prims.string)
  (page_offset : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match parquet_read_range_hex path page_offset (Prims.of_int (128)) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_hex ->
      (match nth_field_hex page_hex (Prims.of_int (3)) Prims.int_zero
               Prims.int_zero (FStar_String.strlen page_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some size_field ->
           if size_field.cf_type <> compact_t_i32
           then FStar_Pervasives_Native.None
           else
             (match decode_varint_value_hex page_hex
                      size_field.cf_value_start Prims.int_zero Prims.int_zero
                      (FStar_String.strlen page_hex)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some raw ->
                  FStar_Pervasives_Native.Some (zigzag_decode_nat raw)))
let parquet_page_header_length_at (path : Prims.string)
  (page_offset : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match parquet_read_range_hex path page_offset (Prims.of_int (128)) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_hex ->
      (match skip_struct_fields_hex page_hex Prims.int_zero
               (FStar_String.strlen page_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some end_hex ->
           FStar_Pervasives_Native.Some (end_hex / (Prims.of_int (2))))
let parquet_dictionary_page_num_values_at (path : Prims.string)
  (page_offset : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match parquet_read_range_hex path page_offset (Prims.of_int (128)) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_hex ->
      (match nth_field_hex page_hex (Prims.of_int (7)) Prims.int_zero
               Prims.int_zero (FStar_String.strlen page_hex)
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some dict_header_field ->
           if dict_header_field.cf_type <> compact_t_struct
           then FStar_Pervasives_Native.None
           else
             (match nth_field_hex page_hex Prims.int_one
                      dict_header_field.cf_value_start Prims.int_zero
                      (FStar_String.strlen page_hex)
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some nv_field ->
                  if nv_field.cf_type <> compact_t_i32
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_varint_value_hex page_hex
                             nv_field.cf_value_start Prims.int_zero
                             Prims.int_zero (FStar_String.strlen page_hex)
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some raw ->
                         FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let parquet_decompressed_page_at (path : Prims.string)
  (page_offset : Prims.nat) (codec : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_page_header_length_at path page_offset with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some header_len ->
      let payload_offset = page_offset + header_len in
      (match parquet_page_header_compressed_size_at path page_offset with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some compressed_size ->
           (match parquet_page_header_uncompressed_size_at path page_offset
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some uncompressed_size ->
                (match parquet_read_range_hex path payload_offset
                         compressed_size
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some compressed_hex ->
                     if codec = "UNCOMPRESSED"
                     then FStar_Pervasives_Native.Some compressed_hex
                     else
                       parquet_zstd_decompress_hex compressed_hex
                         uncompressed_size)))
let decode_one_plain_dictionary_entry (payload_hex : Prims.string)
  (pos : Prims.nat) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  if (pos + (Prims.of_int (7))) >= (FStar_String.strlen payload_hex)
  then FStar_Pervasives_Native.None
  else
    (match le_u32_at_hex payload_hex pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some entry_len ->
         let value_start = pos + (Prims.of_int (8)) in
         let value_hex_len = entry_len + entry_len in
         let value_end = value_start + value_hex_len in
         if value_end > (FStar_String.strlen payload_hex)
         then FStar_Pervasives_Native.None
         else
           (let value_hex =
              FStar_String.sub payload_hex value_start value_hex_len in
            let s =
              ascii_string_of_hex_slice value_hex Prims.int_zero entry_len [] in
            match s with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some str ->
                FStar_Pervasives_Native.Some (str, value_end)))
let rec decode_plain_dictionary_entries (payload_hex : Prims.string)
  (pos : Prims.nat) (remaining : Prims.nat) (acc : Prims.string Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
  else
    (match decode_one_plain_dictionary_entry payload_hex pos with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some (s, next_pos) ->
         decode_plain_dictionary_entries payload_hex next_pos
           (remaining - Prims.int_one) (s :: acc))
let decode_plain_dictionary (payload_hex : Prims.string)
  (num_values : Prims.nat) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  decode_plain_dictionary_entries payload_hex Prims.int_zero num_values []
let read_lsb_packed_value (hex : Prims.string) (byte_start : Prims.nat)
  (start_bit : Prims.nat) (bit_width : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  packed_lsb_value_hex hex byte_start start_bit bit_width Prims.int_zero
    Prims.int_zero
let rle_run_body_hex_size (bit_width : Prims.nat) : Prims.nat=
  let bytes = (bit_width + (Prims.of_int (7))) / (Prims.of_int (8)) in
  mul_nat bytes (Prims.of_int (2))
let rec read_le_uint_bytes (hex : Prims.string) (pos : Prims.nat)
  (remaining_bytes : Prims.nat) (shift : Prims.nat) (acc : Prims.nat) :
  (Prims.nat * Prims.nat) FStar_Pervasives_Native.option=
  if remaining_bytes = Prims.int_zero
  then FStar_Pervasives_Native.Some (acc, pos)
  else
    if (pos + Prims.int_one) >= (FStar_String.strlen hex)
    then FStar_Pervasives_Native.None
    else
      (match byte_at_hex hex pos with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some b ->
           let acc' = acc + (scale_pow2 b shift) in
           read_le_uint_bytes hex (pos + (Prims.of_int (2)))
             (remaining_bytes - Prims.int_one) (shift + (Prims.of_int (8)))
             acc')
let rec repeat_append (value : Prims.nat) (count : Prims.nat)
  (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  if count = Prims.int_zero
  then acc
  else repeat_append value (count - Prims.int_one) (value :: acc)
let rec decode_bit_packed_indices (values_hex : Prims.string)
  (byte_start : Prims.nat) (bit_width : Prims.nat) (count : Prims.nat)
  (mb_pos : Prims.nat) (acc : Prims.nat Prims.list) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if count = Prims.int_zero
  then FStar_Pervasives_Native.Some acc
  else
    (let start_bit = mul_nat mb_pos bit_width in
     match read_lsb_packed_value values_hex byte_start start_bit bit_width
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some v ->
         decode_bit_packed_indices values_hex byte_start bit_width
           (count - Prims.int_one) (mb_pos + Prims.int_one) (v :: acc))
let rec decode_hybrid_rle_runs (values_hex : Prims.string)
  (vh_len : Prims.nat) (pos : Prims.nat) (bit_width : Prims.nat)
  (remaining : Prims.nat) (acc : Prims.nat Prims.list) (fuel : Prims.nat) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if remaining = Prims.int_zero
  then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
  else
    if fuel = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (match decode_varint_value_with_end_hex values_hex pos Prims.int_zero
               Prims.int_zero vh_len
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (header_value, body_pos) ->
           let mode = (mod) header_value (Prims.of_int (2)) in
           let run_length = header_value / (Prims.of_int (2)) in
           if mode = Prims.int_zero
           then
             let body_bytes =
               (bit_width + (Prims.of_int (7))) / (Prims.of_int (8)) in
             (match read_le_uint_bytes values_hex body_pos body_bytes
                      Prims.int_zero Prims.int_zero
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (value, next_pos) ->
                  let take =
                    if run_length <= remaining then run_length else remaining in
                  let acc' = repeat_append value take acc in
                  decode_hybrid_rle_runs values_hex vh_len next_pos bit_width
                    (remaining - take) acc' (fuel - Prims.int_one))
           else
             (let total_values = mul_nat run_length (Prims.of_int (8)) in
              let body_bytes = mul_nat run_length bit_width in
              let body_hex_len = mul_nat body_bytes (Prims.of_int (2)) in
              if (body_pos + body_hex_len) > vh_len
              then FStar_Pervasives_Native.None
              else
                (let take =
                   if total_values <= remaining
                   then total_values
                   else remaining in
                 match decode_bit_packed_indices values_hex body_pos
                         bit_width take Prims.int_zero acc
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some acc' ->
                     decode_hybrid_rle_runs values_hex vh_len
                       (body_pos + body_hex_len) bit_width (remaining - take)
                       acc' (fuel - Prims.int_one))))
let decode_rle_dictionary_data_page (payload_hex : Prims.string)
  (value_count : Prims.nat) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if (FStar_String.strlen payload_hex) < (Prims.of_int (2))
  then FStar_Pervasives_Native.None
  else
    (match byte_at_hex payload_hex Prims.int_zero with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some bit_width ->
         let fuel =
           (value_count +
              ((FStar_String.strlen payload_hex) / (Prims.of_int (2))))
             + Prims.int_one in
         decode_hybrid_rle_runs payload_hex (FStar_String.strlen payload_hex)
           (Prims.of_int (2)) bit_width value_count [] fuel)
type dict_index_tree =
  | DIT_Leaf 
  | DIT_Node of (dict_index_tree * Prims.nat * Prims.string *
  dict_index_tree) 
let uu___is_DIT_Leaf (projectee : dict_index_tree) : Prims.bool=
  match projectee with | DIT_Leaf -> true | uu___ -> false
let uu___is_DIT_Node (projectee : dict_index_tree) : Prims.bool=
  match projectee with | DIT_Node _0 -> true | uu___ -> false
let __proj__DIT_Node__item___0 (projectee : dict_index_tree) :
  (dict_index_tree * Prims.nat * Prims.string * dict_index_tree)=
  match projectee with | DIT_Node _0 -> _0
let rec split_pos_dict_acc (n : Prims.nat) (xs : Prims.string Prims.list)
  (acc : Prims.string Prims.list) :
  (Prims.string Prims.list * Prims.string Prims.list)=
  match xs with
  | [] -> ((FStar_List_Tot_Base.rev acc), [])
  | hd::tl ->
      if n = Prims.int_zero
      then ((FStar_List_Tot_Base.rev acc), xs)
      else split_pos_dict_acc (n - Prims.int_one) tl (hd :: acc)
let rec build_dict_index_tree (xs : Prims.string Prims.list) (n : Prims.nat)
  : dict_index_tree=
  if n = Prims.int_zero
  then DIT_Leaf
  else
    (let mid = n / (Prims.of_int (2)) in
     let uu___1 = split_pos_dict_acc mid xs [] in
     match uu___1 with
     | (left, rest) ->
         (match rest with
          | [] -> DIT_Leaf
          | v::right ->
              DIT_Node
                ((build_dict_index_tree left mid), mid, v,
                  (build_dict_index_tree right ((n - mid) - Prims.int_one)))))
let rec dict_index_tree_find (idx : Prims.nat) (t : dict_index_tree) :
  Prims.string FStar_Pervasives_Native.option=
  match t with
  | DIT_Leaf -> FStar_Pervasives_Native.None
  | DIT_Node (l, left_size, v, r) ->
      if idx < left_size
      then dict_index_tree_find idx l
      else
        if idx = left_size
        then FStar_Pervasives_Native.Some v
        else dict_index_tree_find ((idx - left_size) - Prims.int_one) r
let rec map_indices_to_dict_via_tree (indices : Prims.nat Prims.list)
  (t : dict_index_tree)
  (acc : Prims.string FStar_Pervasives_Native.option Prims.list) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  match indices with
  | [] -> FStar_List_Tot_Base.rev acc
  | i::rest ->
      map_indices_to_dict_via_tree rest t ((dict_index_tree_find i t) :: acc)
let map_indices_to_dict (indices : Prims.nat Prims.list)
  (dict : Prims.string Prims.list)
  (acc : Prims.string FStar_Pervasives_Native.option Prims.list) :
  Prims.string FStar_Pervasives_Native.option Prims.list=
  map_indices_to_dict_via_tree indices
    (build_dict_index_tree dict (FStar_List_Tot_Base.length dict)) acc
let skip_first_level_section_hex (payload_hex : Prims.string)
  (section_len : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  let skip_bytes = (Prims.of_int (4)) + section_len in
  let skip_hex = mul_nat skip_bytes (Prims.of_int (2)) in
  let payload_len_hex = FStar_String.strlen payload_hex in
  if skip_hex > payload_len_hex
  then FStar_Pervasives_Native.None
  else
    FStar_Pervasives_Native.Some
      (FStar_String.sub payload_hex skip_hex (payload_len_hex - skip_hex))
let probe_parquet_column_rle_dictionary_decode_all (path : Prims.string)
  (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_dictionary_page_offset path col_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dict_offset ->
      (match probe_parquet_column_compression_codec path col_index with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some codec ->
           (match parquet_decompressed_page_at path dict_offset codec with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some dict_payload_hex ->
                (match parquet_dictionary_page_num_values_at path dict_offset
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some dict_num_values ->
                     (match decode_plain_dictionary dict_payload_hex
                              dict_num_values
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some dict ->
                          (match probe_parquet_column_decompressed_payload_hex
                                   path col_index
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some data_payload_hex ->
                               (match probe_parquet_column_page_header_num_values
                                        path col_index
                                with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some value_count ->
                                    (match probe_parquet_column_first_level_section_length
                                             path col_index
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         section_len ->
                                         (match skip_first_level_section_hex
                                                  data_payload_hex
                                                  section_len
                                          with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some
                                              values_hex ->
                                              (match decode_rle_dictionary_data_page
                                                       values_hex value_count
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   indices ->
                                                   FStar_Pervasives_Native.Some
                                                     (map_indices_to_dict
                                                        indices dict []))))))))))
let probe_parquet_column_decode_all (path : Prims.string)
  (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_page_header_data_encoding path col_index with
  | FStar_Pervasives_Native.Some "DELTA_LENGTH_BYTE_ARRAY" ->
      probe_parquet_column_delta_length_byte_array_decode_all path col_index
  | FStar_Pervasives_Native.Some "RLE_DICTIONARY" ->
      probe_parquet_column_rle_dictionary_decode_all path col_index
  | uu___ -> FStar_Pervasives_Native.None
type meta_column_chunk_locator =
  {
  mcc_meta_hex: Prims.string ;
  mcc_meta_hex_len: Prims.nat ;
  mcc_column_chunk_start: Prims.nat }
let __proj__Mkmeta_column_chunk_locator__item__mcc_meta_hex
  (projectee : meta_column_chunk_locator) : Prims.string=
  match projectee with
  | { mcc_meta_hex; mcc_meta_hex_len; mcc_column_chunk_start;_} ->
      mcc_meta_hex
let __proj__Mkmeta_column_chunk_locator__item__mcc_meta_hex_len
  (projectee : meta_column_chunk_locator) : Prims.nat=
  match projectee with
  | { mcc_meta_hex; mcc_meta_hex_len; mcc_column_chunk_start;_} ->
      mcc_meta_hex_len
let __proj__Mkmeta_column_chunk_locator__item__mcc_column_chunk_start
  (projectee : meta_column_chunk_locator) : Prims.nat=
  match projectee with
  | { mcc_meta_hex; mcc_meta_hex_len; mcc_column_chunk_start;_} ->
      mcc_column_chunk_start
let probe_parquet_column_chunk_in_row_group_locator (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  meta_column_chunk_locator FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if
                           (rg_index >= row_groups_info.cli_count) ||
                             (row_groups_info.cli_etype <> compact_t_struct)
                         then FStar_Pervasives_Native.None
                         else
                           (match nth_compact_list_element_start_hex meta_hex
                                    row_groups_field.cf_value_start rg_index
                                    meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some rg_start ->
                                (match nth_field_hex meta_hex Prims.int_one
                                         rg_start Prims.int_zero meta_hex_len
                                 with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some columns_field
                                     ->
                                     if
                                       columns_field.cf_type <>
                                         compact_t_list
                                     then FStar_Pervasives_Native.None
                                     else
                                       (match nth_compact_list_element_start_hex
                                                meta_hex
                                                columns_field.cf_value_start
                                                col_index meta_hex_len
                                        with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some
                                            column_chunk_start ->
                                            FStar_Pervasives_Native.Some
                                              {
                                                mcc_meta_hex = meta_hex;
                                                mcc_meta_hex_len =
                                                  meta_hex_len;
                                                mcc_column_chunk_start =
                                                  column_chunk_start
                                              })))))
           else FStar_Pervasives_Native.None)
let column_metadata_start_of (loc : meta_column_chunk_locator) :
  Prims.nat FStar_Pervasives_Native.option=
  match nth_field_hex loc.mcc_meta_hex (Prims.of_int (3))
          loc.mcc_column_chunk_start Prims.int_zero loc.mcc_meta_hex_len
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some metadata_field ->
      if metadata_field.cf_type <> compact_t_struct
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (metadata_field.cf_value_start)
let probe_parquet_column_data_page_offset_in_row_group (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_chunk_in_row_group_locator path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some loc ->
      (match column_metadata_start_of loc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some md_start ->
           (match nth_field_hex loc.mcc_meta_hex (Prims.of_int (9)) md_start
                    Prims.int_zero loc.mcc_meta_hex_len
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some offset_field ->
                if offset_field.cf_type <> compact_t_i64
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex loc.mcc_meta_hex
                           offset_field.cf_value_start Prims.int_zero
                           Prims.int_zero loc.mcc_meta_hex_len
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_dictionary_page_offset_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_chunk_in_row_group_locator path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some loc ->
      (match column_metadata_start_of loc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some md_start ->
           (match nth_field_hex loc.mcc_meta_hex (Prims.of_int (11)) md_start
                    Prims.int_zero loc.mcc_meta_hex_len
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some offset_field ->
                if offset_field.cf_type <> compact_t_i64
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex loc.mcc_meta_hex
                           offset_field.cf_value_start Prims.int_zero
                           Prims.int_zero loc.mcc_meta_hex_len
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_page_header_compressed_size_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      parquet_page_header_compressed_size_at path page_offset
let probe_parquet_column_page_header_uncompressed_size_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      parquet_page_header_uncompressed_size_at path page_offset
let probe_parquet_column_page_header_length_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      parquet_page_header_length_at path page_offset
let probe_parquet_column_page_header_num_values_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex Prims.int_one
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some num_values_field ->
                       if num_values_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  num_values_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (zigzag_decode_nat raw)))))
let probe_parquet_column_compression_codec_in_row_group (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_chunk_in_row_group_locator path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some loc ->
      (match column_metadata_start_of loc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some md_start ->
           (match nth_field_hex loc.mcc_meta_hex (Prims.of_int (4)) md_start
                    Prims.int_zero loc.mcc_meta_hex_len
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some codec_field ->
                if codec_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex loc.mcc_meta_hex
                           codec_field.cf_value_start Prims.int_zero
                           Prims.int_zero loc.mcc_meta_hex_len
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some
                         (parquet_compression_codec_name
                            (zigzag_decode_nat raw)))))
let probe_parquet_column_decompressed_payload_hex_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match ((probe_parquet_column_data_page_offset_in_row_group path rg_index
            col_index),
          (probe_parquet_column_page_header_length_in_row_group path rg_index
             col_index),
          (probe_parquet_column_page_header_compressed_size_in_row_group path
             rg_index col_index),
          (probe_parquet_column_page_header_uncompressed_size_in_row_group
             path rg_index col_index))
  with
  | (FStar_Pervasives_Native.Some page_offset, FStar_Pervasives_Native.Some
     header_len, FStar_Pervasives_Native.Some compressed_size,
     FStar_Pervasives_Native.Some uncompressed_size) ->
      let payload_offset = page_offset + header_len in
      (match parquet_read_range_hex path payload_offset compressed_size with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some compressed_hex ->
           (match probe_parquet_column_compression_codec_in_row_group path
                    rg_index col_index
            with
            | FStar_Pervasives_Native.Some "UNCOMPRESSED" ->
                FStar_Pervasives_Native.Some compressed_hex
            | uu___ ->
                parquet_zstd_decompress_hex compressed_hex uncompressed_size))
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_first_level_section_length_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex_in_row_group path
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      if (FStar_String.strlen payload_hex) < (Prims.of_int (8))
      then FStar_Pervasives_Native.None
      else le_u32_at_hex payload_hex Prims.int_zero
let probe_parquet_column_delta_length_byte_array_values_offset_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_first_level_section_length_in_row_group path
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some section_len ->
      FStar_Pervasives_Native.Some ((Prims.of_int (4)) + section_len)
let probe_parquet_column_delta_length_byte_array_page_cache_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  dlba_page_cache FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex_in_row_group path
            rg_index col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset_in_row_group
             path rg_index col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     values_offset) ->
      let payload_len_hex = FStar_String.strlen payload_hex in
      let values_start_hex = mul_nat values_offset (Prims.of_int (2)) in
      if values_start_hex > payload_len_hex
      then FStar_Pervasives_Native.None
      else
        (let values_hex =
           FStar_String.sub payload_hex values_start_hex
             (payload_len_hex - values_start_hex) in
         let vh_len = FStar_String.strlen values_hex in
         match decode_varint_value_with_end_hex values_hex Prims.int_zero
                 Prims.int_zero Prims.int_zero vh_len
         with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (block_size, p1) ->
             (match decode_varint_value_with_end_hex values_hex p1
                      Prims.int_zero Prims.int_zero vh_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (miniblocks, p2) ->
                  if miniblocks = Prims.int_zero
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_varint_value_with_end_hex values_hex p2
                             Prims.int_zero Prims.int_zero vh_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (value_count, p3) ->
                         (match decode_varint_value_with_end_hex values_hex
                                  p3 Prims.int_zero Prims.int_zero vh_len
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (first_raw, p4) ->
                              let first_length = zigzag_decode_nat first_raw in
                              (match decode_varint_value_with_end_hex
                                       values_hex p4 Prims.int_zero
                                       Prims.int_zero vh_len
                               with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some
                                   (min_delta_raw, p5) ->
                                   let min_delta =
                                     zigzag_decode_int min_delta_raw in
                                   if (p5 + Prims.int_one) >= vh_len
                                   then FStar_Pervasives_Native.None
                                   else
                                     (match byte_at_hex values_hex p5 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          bit_width ->
                                          let widths_offset = p5 in
                                          let packed_start =
                                            p5 +
                                              (mul_nat miniblocks
                                                 (Prims.of_int (2))) in
                                          let values_per_miniblock =
                                            if miniblocks > Prims.int_zero
                                            then
                                              div_nat_pos block_size
                                                miniblocks
                                            else Prims.int_zero in
                                          (match build_dlba_length_list
                                                   values_hex vh_len
                                                   block_size miniblocks
                                                   values_per_miniblock
                                                   min_delta widths_offset
                                                   packed_start bit_width
                                                   Prims.int_zero
                                                   Prims.int_zero value_count
                                                   first_length []
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some
                                               lengths ->
                                               let total_value_bytes =
                                                 sum_nat_list lengths in
                                               let payload_byte_len =
                                                 payload_len_hex /
                                                   (Prims.of_int (2)) in
                                               if
                                                 values_offset >
                                                   payload_byte_len
                                               then
                                                 FStar_Pervasives_Native.None
                                               else
                                                 (let values_stream_len =
                                                    payload_byte_len -
                                                      values_offset in
                                                  if
                                                    total_value_bytes >
                                                      values_stream_len
                                                  then
                                                    FStar_Pervasives_Native.None
                                                  else
                                                    (let value_data_offset =
                                                       values_stream_len -
                                                         total_value_bytes in
                                                     let starts =
                                                       prefix_sums lengths
                                                         Prims.int_zero [] in
                                                     FStar_Pervasives_Native.Some
                                                       {
                                                         dpc_payload_hex =
                                                           payload_hex;
                                                         dpc_values_offset =
                                                           values_offset;
                                                         dpc_value_count =
                                                           value_count;
                                                         dpc_first_length =
                                                           first_length;
                                                         dpc_min_delta =
                                                           min_delta;
                                                         dpc_bit_width =
                                                           bit_width;
                                                         dpc_packed_start =
                                                           packed_start;
                                                         dpc_value_data_offset
                                                           =
                                                           value_data_offset;
                                                         dpc_lengths =
                                                           lengths;
                                                         dpc_value_starts =
                                                           starts
                                                       })))))))))
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_delta_length_byte_array_decode_all_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_page_cache_in_row_group
          path rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some cache ->
      FStar_Pervasives_Native.Some (dlba_page_decode_all_strings cache)
let probe_parquet_column_rle_dictionary_decode_all_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_dictionary_page_offset_in_row_group path
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dict_offset ->
      (match probe_parquet_column_compression_codec_in_row_group path
               rg_index col_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some codec ->
           (match parquet_decompressed_page_at path dict_offset codec with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some dict_payload_hex ->
                (match parquet_dictionary_page_num_values_at path dict_offset
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some dict_num_values ->
                     (match decode_plain_dictionary dict_payload_hex
                              dict_num_values
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some dict ->
                          (match probe_parquet_column_decompressed_payload_hex_in_row_group
                                   path rg_index col_index
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some data_payload_hex ->
                               (match probe_parquet_column_page_header_num_values_in_row_group
                                        path rg_index col_index
                                with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some value_count ->
                                    (match probe_parquet_column_first_level_section_length_in_row_group
                                             path rg_index col_index
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         section_len ->
                                         (match skip_first_level_section_hex
                                                  data_payload_hex
                                                  section_len
                                          with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some
                                              values_hex ->
                                              (match decode_rle_dictionary_data_page
                                                       values_hex value_count
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   indices ->
                                                   FStar_Pervasives_Native.Some
                                                     (map_indices_to_dict
                                                        indices dict []))))))))))
let probe_parquet_column_page_header_data_encoding_in_row_group
  (path : Prims.string) (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group path rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (2))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_decode_in_row_group (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_page_header_data_encoding_in_row_group path
          rg_index col_index
  with
  | FStar_Pervasives_Native.Some "DELTA_LENGTH_BYTE_ARRAY" ->
      probe_parquet_column_delta_length_byte_array_decode_all_in_row_group
        path rg_index col_index
  | FStar_Pervasives_Native.Some "RLE_DICTIONARY" ->
      probe_parquet_column_rle_dictionary_decode_all_in_row_group path
        rg_index col_index
  | uu___ -> FStar_Pervasives_Native.None
type parquet_row_group_offset_table =
  {
  prgt_meta_hex: Prims.string ;
  prgt_meta_hex_len: Prims.nat ;
  prgt_row_group_starts: Prims.nat Prims.list }
let __proj__Mkparquet_row_group_offset_table__item__prgt_meta_hex
  (projectee : parquet_row_group_offset_table) : Prims.string=
  match projectee with
  | { prgt_meta_hex; prgt_meta_hex_len; prgt_row_group_starts;_} ->
      prgt_meta_hex
let __proj__Mkparquet_row_group_offset_table__item__prgt_meta_hex_len
  (projectee : parquet_row_group_offset_table) : Prims.nat=
  match projectee with
  | { prgt_meta_hex; prgt_meta_hex_len; prgt_row_group_starts;_} ->
      prgt_meta_hex_len
let __proj__Mkparquet_row_group_offset_table__item__prgt_row_group_starts
  (projectee : parquet_row_group_offset_table) : Prims.nat Prims.list=
  match projectee with
  | { prgt_meta_hex; prgt_meta_hex_len; prgt_row_group_starts;_} ->
      prgt_row_group_starts
let rec collect_compact_list_starts_loop (hex : Prims.string)
  (etype : Prims.nat) (remaining : Prims.nat) (p : Prims.nat)
  (acc_rev : Prims.nat Prims.list) (fuel : Prims.nat) :
  Prims.nat Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if remaining = Prims.int_zero
    then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc_rev)
    else
      (match skip_compact_value_hex hex etype p (fuel - Prims.int_one) with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some next ->
           collect_compact_list_starts_loop hex etype
             (remaining - Prims.int_one) next (p :: acc_rev)
             (fuel - Prims.int_one))
let probe_parquet_row_group_offset_table (path : Prims.string) :
  parquet_row_group_offset_table FStar_Pervasives_Native.option=
  match probe_parquet_footer path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some footer ->
      (match parquet_read_tail_hex path footer.pf_footer_len with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some footer_hex ->
           let meta_hex_len = footer.pf_metadata_len + footer.pf_metadata_len in
           if meta_hex_len <= (FStar_String.strlen footer_hex)
           then
             let meta_hex =
               FStar_String.sub footer_hex Prims.int_zero meta_hex_len in
             (match nth_field_hex meta_hex (Prims.of_int (4)) Prims.int_zero
                      Prims.int_zero meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some row_groups_field ->
                  if row_groups_field.cf_type <> compact_t_list
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_compact_list_info_hex meta_hex
                             row_groups_field.cf_value_start meta_hex_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some row_groups_info ->
                         if row_groups_info.cli_etype <> compact_t_struct
                         then FStar_Pervasives_Native.None
                         else
                           (match collect_compact_list_starts_loop meta_hex
                                    row_groups_info.cli_etype
                                    row_groups_info.cli_count
                                    row_groups_info.cli_payload_start []
                                    meta_hex_len
                            with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some starts ->
                                FStar_Pervasives_Native.Some
                                  {
                                    prgt_meta_hex = meta_hex;
                                    prgt_meta_hex_len = meta_hex_len;
                                    prgt_row_group_starts = starts
                                  })))
           else FStar_Pervasives_Native.None)
let probe_parquet_row_group_num_rows_from_table
  (table : parquet_row_group_offset_table) (rg_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.nth table.prgt_row_group_starts rg_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rg_start ->
      (match nth_field_hex table.prgt_meta_hex (Prims.of_int (3)) rg_start
               Prims.int_zero table.prgt_meta_hex_len
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some row_group_field ->
           if row_group_field.cf_type <> compact_t_i64
           then FStar_Pervasives_Native.None
           else
             (match decode_varint_value_hex table.prgt_meta_hex
                      row_group_field.cf_value_start Prims.int_zero
                      Prims.int_zero table.prgt_meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some raw ->
                  FStar_Pervasives_Native.Some (zigzag_decode_nat raw)))
let probe_parquet_column_chunk_locator_from_table
  (table : parquet_row_group_offset_table) (rg_index : Prims.nat)
  (col_index : Prims.nat) :
  meta_column_chunk_locator FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.nth table.prgt_row_group_starts rg_index with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rg_start ->
      (match nth_field_hex table.prgt_meta_hex Prims.int_one rg_start
               Prims.int_zero table.prgt_meta_hex_len
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some columns_field ->
           if columns_field.cf_type <> compact_t_list
           then FStar_Pervasives_Native.None
           else
             (match nth_compact_list_element_start_hex table.prgt_meta_hex
                      columns_field.cf_value_start col_index
                      table.prgt_meta_hex_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some column_chunk_start ->
                  FStar_Pervasives_Native.Some
                    {
                      mcc_meta_hex = (table.prgt_meta_hex);
                      mcc_meta_hex_len = (table.prgt_meta_hex_len);
                      mcc_column_chunk_start = column_chunk_start
                    }))
let probe_parquet_column_data_page_offset_in_row_group_from_table
  (table : parquet_row_group_offset_table) (rg_index : Prims.nat)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_chunk_locator_from_table table rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some loc ->
      (match column_metadata_start_of loc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some md_start ->
           (match nth_field_hex loc.mcc_meta_hex (Prims.of_int (9)) md_start
                    Prims.int_zero loc.mcc_meta_hex_len
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some offset_field ->
                if offset_field.cf_type <> compact_t_i64
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex loc.mcc_meta_hex
                           offset_field.cf_value_start Prims.int_zero
                           Prims.int_zero loc.mcc_meta_hex_len
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_dictionary_page_offset_in_row_group_from_table
  (table : parquet_row_group_offset_table) (rg_index : Prims.nat)
  (col_index : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_chunk_locator_from_table table rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some loc ->
      (match column_metadata_start_of loc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some md_start ->
           (match nth_field_hex loc.mcc_meta_hex (Prims.of_int (11)) md_start
                    Prims.int_zero loc.mcc_meta_hex_len
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some offset_field ->
                if offset_field.cf_type <> compact_t_i64
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex loc.mcc_meta_hex
                           offset_field.cf_value_start Prims.int_zero
                           Prims.int_zero loc.mcc_meta_hex_len
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some (zigzag_decode_nat raw))))
let probe_parquet_column_page_header_compressed_size_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group_from_table table
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      parquet_page_header_compressed_size_at path page_offset
let probe_parquet_column_page_header_uncompressed_size_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group_from_table table
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      parquet_page_header_uncompressed_size_at path page_offset
let probe_parquet_column_page_header_length_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group_from_table table
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      parquet_page_header_length_at path page_offset
let probe_parquet_column_page_header_num_values_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group_from_table table
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex Prims.int_one
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some num_values_field ->
                       if num_values_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  num_values_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (zigzag_decode_nat raw)))))
let probe_parquet_column_compression_codec_in_row_group_from_table
  (table : parquet_row_group_offset_table) (rg_index : Prims.nat)
  (col_index : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_chunk_locator_from_table table rg_index
          col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some loc ->
      (match column_metadata_start_of loc with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some md_start ->
           (match nth_field_hex loc.mcc_meta_hex (Prims.of_int (4)) md_start
                    Prims.int_zero loc.mcc_meta_hex_len
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some codec_field ->
                if codec_field.cf_type <> compact_t_i32
                then FStar_Pervasives_Native.None
                else
                  (match decode_varint_value_hex loc.mcc_meta_hex
                           codec_field.cf_value_start Prims.int_zero
                           Prims.int_zero loc.mcc_meta_hex_len
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some raw ->
                       FStar_Pervasives_Native.Some
                         (parquet_compression_codec_name
                            (zigzag_decode_nat raw)))))
let probe_parquet_column_decompressed_payload_hex_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match ((probe_parquet_column_data_page_offset_in_row_group_from_table table
            rg_index col_index),
          (probe_parquet_column_page_header_length_in_row_group_from_table
             table path rg_index col_index),
          (probe_parquet_column_page_header_compressed_size_in_row_group_from_table
             table path rg_index col_index),
          (probe_parquet_column_page_header_uncompressed_size_in_row_group_from_table
             table path rg_index col_index))
  with
  | (FStar_Pervasives_Native.Some page_offset, FStar_Pervasives_Native.Some
     header_len, FStar_Pervasives_Native.Some compressed_size,
     FStar_Pervasives_Native.Some uncompressed_size) ->
      let payload_offset = page_offset + header_len in
      (match parquet_read_range_hex path payload_offset compressed_size with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some compressed_hex ->
           (match probe_parquet_column_compression_codec_in_row_group_from_table
                    table rg_index col_index
            with
            | FStar_Pervasives_Native.Some "UNCOMPRESSED" ->
                FStar_Pervasives_Native.Some compressed_hex
            | uu___ ->
                parquet_zstd_decompress_hex compressed_hex uncompressed_size))
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_first_level_section_length_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_decompressed_payload_hex_in_row_group_from_table
          table path rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some payload_hex ->
      if (FStar_String.strlen payload_hex) < (Prims.of_int (8))
      then FStar_Pervasives_Native.None
      else le_u32_at_hex payload_hex Prims.int_zero
let probe_parquet_column_delta_length_byte_array_values_offset_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match probe_parquet_column_first_level_section_length_in_row_group_from_table
          table path rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some section_len ->
      FStar_Pervasives_Native.Some ((Prims.of_int (4)) + section_len)
let probe_parquet_column_delta_length_byte_array_page_cache_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  dlba_page_cache FStar_Pervasives_Native.option=
  match ((probe_parquet_column_decompressed_payload_hex_in_row_group_from_table
            table path rg_index col_index),
          (probe_parquet_column_delta_length_byte_array_values_offset_in_row_group_from_table
             table path rg_index col_index))
  with
  | (FStar_Pervasives_Native.Some payload_hex, FStar_Pervasives_Native.Some
     values_offset) ->
      let payload_len_hex = FStar_String.strlen payload_hex in
      let values_start_hex = mul_nat values_offset (Prims.of_int (2)) in
      if values_start_hex > payload_len_hex
      then FStar_Pervasives_Native.None
      else
        (let values_hex =
           FStar_String.sub payload_hex values_start_hex
             (payload_len_hex - values_start_hex) in
         let vh_len = FStar_String.strlen values_hex in
         match decode_varint_value_with_end_hex values_hex Prims.int_zero
                 Prims.int_zero Prims.int_zero vh_len
         with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (block_size, p1) ->
             (match decode_varint_value_with_end_hex values_hex p1
                      Prims.int_zero Prims.int_zero vh_len
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (miniblocks, p2) ->
                  if miniblocks = Prims.int_zero
                  then FStar_Pervasives_Native.None
                  else
                    (match decode_varint_value_with_end_hex values_hex p2
                             Prims.int_zero Prims.int_zero vh_len
                     with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (value_count, p3) ->
                         (match decode_varint_value_with_end_hex values_hex
                                  p3 Prims.int_zero Prims.int_zero vh_len
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (first_raw, p4) ->
                              let first_length = zigzag_decode_nat first_raw in
                              (match decode_varint_value_with_end_hex
                                       values_hex p4 Prims.int_zero
                                       Prims.int_zero vh_len
                               with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some
                                   (min_delta_raw, p5) ->
                                   let min_delta =
                                     zigzag_decode_int min_delta_raw in
                                   if (p5 + Prims.int_one) >= vh_len
                                   then FStar_Pervasives_Native.None
                                   else
                                     (match byte_at_hex values_hex p5 with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          bit_width ->
                                          let widths_offset = p5 in
                                          let packed_start =
                                            p5 +
                                              (mul_nat miniblocks
                                                 (Prims.of_int (2))) in
                                          let values_per_miniblock =
                                            if miniblocks > Prims.int_zero
                                            then
                                              div_nat_pos block_size
                                                miniblocks
                                            else Prims.int_zero in
                                          (match build_dlba_length_list
                                                   values_hex vh_len
                                                   block_size miniblocks
                                                   values_per_miniblock
                                                   min_delta widths_offset
                                                   packed_start bit_width
                                                   Prims.int_zero
                                                   Prims.int_zero value_count
                                                   first_length []
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some
                                               lengths ->
                                               let total_value_bytes =
                                                 sum_nat_list lengths in
                                               let payload_byte_len =
                                                 payload_len_hex /
                                                   (Prims.of_int (2)) in
                                               if
                                                 values_offset >
                                                   payload_byte_len
                                               then
                                                 FStar_Pervasives_Native.None
                                               else
                                                 (let values_stream_len =
                                                    payload_byte_len -
                                                      values_offset in
                                                  if
                                                    total_value_bytes >
                                                      values_stream_len
                                                  then
                                                    FStar_Pervasives_Native.None
                                                  else
                                                    (let value_data_offset =
                                                       values_stream_len -
                                                         total_value_bytes in
                                                     let starts =
                                                       prefix_sums lengths
                                                         Prims.int_zero [] in
                                                     FStar_Pervasives_Native.Some
                                                       {
                                                         dpc_payload_hex =
                                                           payload_hex;
                                                         dpc_values_offset =
                                                           values_offset;
                                                         dpc_value_count =
                                                           value_count;
                                                         dpc_first_length =
                                                           first_length;
                                                         dpc_min_delta =
                                                           min_delta;
                                                         dpc_bit_width =
                                                           bit_width;
                                                         dpc_packed_start =
                                                           packed_start;
                                                         dpc_value_data_offset
                                                           =
                                                           value_data_offset;
                                                         dpc_lengths =
                                                           lengths;
                                                         dpc_value_starts =
                                                           starts
                                                       })))))))))
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_delta_length_byte_array_decode_all_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_delta_length_byte_array_page_cache_in_row_group_from_table
          table path rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some cache ->
      FStar_Pervasives_Native.Some (dlba_page_decode_all_strings cache)
let probe_parquet_column_rle_dictionary_decode_all_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_dictionary_page_offset_in_row_group_from_table
          table rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dict_offset ->
      (match probe_parquet_column_compression_codec_in_row_group_from_table
               table rg_index col_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some codec ->
           (match parquet_decompressed_page_at path dict_offset codec with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some dict_payload_hex ->
                (match parquet_dictionary_page_num_values_at path dict_offset
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some dict_num_values ->
                     (match decode_plain_dictionary dict_payload_hex
                              dict_num_values
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some dict ->
                          (match probe_parquet_column_decompressed_payload_hex_in_row_group_from_table
                                   table path rg_index col_index
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some data_payload_hex ->
                               (match probe_parquet_column_page_header_num_values_in_row_group_from_table
                                        table path rg_index col_index
                                with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some value_count ->
                                    (match probe_parquet_column_first_level_section_length_in_row_group_from_table
                                             table path rg_index col_index
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         section_len ->
                                         (match skip_first_level_section_hex
                                                  data_payload_hex
                                                  section_len
                                          with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some
                                              values_hex ->
                                              (match decode_rle_dictionary_data_page
                                                       values_hex value_count
                                               with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   indices ->
                                                   FStar_Pervasives_Native.Some
                                                     (map_indices_to_dict
                                                        indices dict []))))))))))
let probe_parquet_column_page_header_data_encoding_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match probe_parquet_column_data_page_offset_in_row_group_from_table table
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some page_offset ->
      (match parquet_read_range_hex path page_offset (Prims.of_int (128))
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some page_hex ->
           (match nth_field_hex page_hex (Prims.of_int (5)) Prims.int_zero
                    Prims.int_zero (FStar_String.strlen page_hex)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some data_page_header_field ->
                if data_page_header_field.cf_type <> compact_t_struct
                then FStar_Pervasives_Native.None
                else
                  (match nth_field_hex page_hex (Prims.of_int (2))
                           data_page_header_field.cf_value_start
                           Prims.int_zero (FStar_String.strlen page_hex)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some encoding_field ->
                       if encoding_field.cf_type <> compact_t_i32
                       then FStar_Pervasives_Native.None
                       else
                         (match decode_varint_value_hex page_hex
                                  encoding_field.cf_value_start
                                  Prims.int_zero Prims.int_zero
                                  (FStar_String.strlen page_hex)
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some raw ->
                              FStar_Pervasives_Native.Some
                                (parquet_encoding_name
                                   (zigzag_decode_nat raw))))))
let probe_parquet_column_decode_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_column_page_header_data_encoding_in_row_group_from_table
          table path rg_index col_index
  with
  | FStar_Pervasives_Native.Some "DELTA_LENGTH_BYTE_ARRAY" ->
      probe_parquet_column_delta_length_byte_array_decode_all_in_row_group_from_table
        table path rg_index col_index
  | FStar_Pervasives_Native.Some "RLE_DICTIONARY" ->
      probe_parquet_column_rle_dictionary_decode_all_in_row_group_from_table
        table path rg_index col_index
  | uu___ -> FStar_Pervasives_Native.None
let probe_parquet_column_dictionary_in_row_group_from_table
  (table : parquet_row_group_offset_table) (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match probe_parquet_column_dictionary_page_offset_in_row_group_from_table
          table rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dict_offset ->
      (match probe_parquet_column_compression_codec_in_row_group_from_table
               table rg_index col_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some codec ->
           (match parquet_decompressed_page_at path dict_offset codec with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some dict_payload_hex ->
                (match parquet_dictionary_page_num_values_at path dict_offset
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some dict_num_values ->
                     decode_plain_dictionary dict_payload_hex dict_num_values)))
let rec list_rev_append :
  'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun xs acc ->
    match xs with | [] -> acc | hd::tl -> list_rev_append tl (hd :: acc)
let list_rev (xs : 'a Prims.list) : 'a Prims.list= list_rev_append xs []
let rec collect_row_group_columns (path : Prims.string)
  (table : parquet_row_group_offset_table FStar_Pervasives_Native.option)
  (col_index : Prims.nat) (rg_index : Prims.nat) (rg_count : Prims.nat)
  (fuel : Prims.nat)
  (acc_rev : Prims.string FStar_Pervasives_Native.option Prims.list) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.Some acc_rev
  else
    if rg_index >= rg_count
    then FStar_Pervasives_Native.Some acc_rev
    else
      (let decoded =
         match table with
         | FStar_Pervasives_Native.Some t ->
             probe_parquet_column_decode_in_row_group_from_table t path
               rg_index col_index
         | FStar_Pervasives_Native.None ->
             probe_parquet_column_decode_in_row_group path rg_index col_index in
       match decoded with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some this_rg ->
           let acc_rev' = list_rev_append this_rg acc_rev in
           collect_row_group_columns path table col_index
             (rg_index + Prims.int_one) rg_count (fuel - Prims.int_one)
             acc_rev')
let probe_parquet_column_decode_all_row_groups (path : Prims.string)
  (col_index : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option Prims.list
    FStar_Pervasives_Native.option=
  match probe_parquet_row_group_count path with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rg_count ->
      let table = probe_parquet_row_group_offset_table path in
      (match collect_row_group_columns path table col_index Prims.int_zero
               rg_count rg_count []
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some acc_rev ->
           FStar_Pervasives_Native.Some (list_rev acc_rev))
let probe_parquet_column_dictionary_in_row_group (path : Prims.string)
  (rg_index : Prims.nat) (col_index : Prims.nat) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match probe_parquet_column_dictionary_page_offset_in_row_group path
          rg_index col_index
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some dict_offset ->
      (match probe_parquet_column_compression_codec_in_row_group path
               rg_index col_index
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some codec ->
           (match parquet_decompressed_page_at path dict_offset codec with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some dict_payload_hex ->
                (match parquet_dictionary_page_num_values_at path dict_offset
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some dict_num_values ->
                     decode_plain_dictionary dict_payload_hex dict_num_values)))
