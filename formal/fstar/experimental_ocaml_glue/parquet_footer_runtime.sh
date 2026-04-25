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

if grep -q 'let parquet_read_tail_hex (path : Prims.string)' "$FILE"; then
  echo "  Applying Parquet footer runtime glue to $FILE..."
else
  echo "  Warning: parquet_read_tail_hex stub not found in $FILE" >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
import re
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

range_impl = r'''(* parquet_read_range_hex: depends on helpers defined earlier in
   the tail_impl block (Mim2 byte cache for issue #100 Phases B+C). *)

let parquet_read_range_hex (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_read_range path start count with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw -> FStar_Pervasives_Native.Some (__mim2_hex_encode raw)

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

(* Hex-encode a raw string. Buffer-once so the ~250MB row-group
   payloads don't trigger O(N^2) string concat. *)
let __mim2_hex_encode raw =
  let module S = Stdlib in
  let b = Buffer.create S.(2 * String.length raw) in
  String.iter
    (fun ch -> Buffer.add_string b (Printf.sprintf "%02X" (Char.code ch)))
    raw;
  Buffer.contents b

let parquet_read_tail_hex (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_read_tail path count with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw -> FStar_Pervasives_Native.Some (__mim2_hex_encode raw)
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
