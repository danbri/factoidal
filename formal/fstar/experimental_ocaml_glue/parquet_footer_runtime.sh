#!/bin/bash
# Experimental runtime glue for Parquet.Footer.ml
#
# The raw file I/O stays in OCaml; footer parsing logic remains in F*.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/Parquet_Footer.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping Parquet footer runtime glue" >&2
  exit 0
fi

# Marker-idempotence (2026-08-26). The previous guard tested for
# `let parquet_read_tail_hex (path : Prims.string)`, which survives the
# patch -- the replacement keeps that same signature line -- so an
# already-patched file passed the guard and then hit the SystemExit
# below. ocaml-patches.sh runs over the whole output directory, so an
# incremental extract reaches this script with the file already patched;
# with a fatal patch step that aborted the build. Test the stub's own
# failwith text, which the patch removes.
if grep -q 'Not yet implemented: Parquet.Footer.parquet_read_range_hex' "$FILE"; then
  echo "  Applying Parquet footer runtime glue to $FILE..."
else
  echo "  [parquet-footer-runtime] already applied; skipping."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
import re
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

range_impl = r'''(* parquet_read_range_hex: depends on helpers defined earlier in
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
'''

tail_impl = r'''(* ---- Mim2 (issue #100 Phases B+C) ---------------------------------
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
'''

range_pattern = re.compile(
    r'let parquet_read_range_hex \(path : Prims\.string\) \(start : Prims\.nat\)\n'
    r'  \(count : Prims\.nat\) : Prims\.string FStar_Pervasives_Native\.option=\n'
    r'  failwith "Not yet implemented: Parquet\.Footer\.parquet_read_range_hex"\n?'
)

tail_pattern = re.compile(
    r'let parquet_read_tail_hex \(path : Prims\.string\) \(count : Prims\.nat\) :\n'
    r'  Prims\.string FStar_Pervasives_Native\.option=\n'
    r'  failwith "Not yet implemented: Parquet\.Footer\.parquet_read_tail_hex"\n?'
)

if not range_pattern.search(content):
    raise SystemExit("parquet_read_range_hex stub not found")
if not tail_pattern.search(content):
    raise SystemExit("parquet_read_tail_hex stub not found")
zstd_pattern = re.compile(
    r'let parquet_zstd_decompress_hex \(compressed_hex : Prims\.string\)\n'
    r'  \(expected_size : Prims\.nat\) : Prims\.string FStar_Pervasives_Native\.option=\n'
    r'  failwith "Not yet implemented: Parquet\.Footer\.parquet_zstd_decompress_hex"\n?'
)
if not zstd_pattern.search(content):
    raise SystemExit("parquet_zstd_decompress_hex stub not found")

content = range_pattern.sub(range_impl, content, count=1)
content = tail_pattern.sub(tail_impl, content, count=1)
content = zstd_pattern.sub("", content, count=1)
path.write_text(content)
PYEOF
