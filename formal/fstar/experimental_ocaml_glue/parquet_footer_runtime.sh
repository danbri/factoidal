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

range_impl = r'''let parquet_read_range (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  if not (Sys.file_exists path) then FStar_Pervasives_Native.None
  else
    let ic = open_in_bin path in
    let module S = Stdlib in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let file_len = in_channel_length ic in
         let offset = Z.to_int start in
         let want = Z.to_int count in
         if S.(offset < 0 || want < 0 || offset > file_len || offset + want > file_len)
         then FStar_Pervasives_Native.None
         else
           (seek_in ic offset;
            FStar_Pervasives_Native.Some (really_input_string ic want)))

let parquet_read_tail (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  if not (Sys.file_exists path) then FStar_Pervasives_Native.None
  else
    let ic = open_in_bin path in
    let module S = Stdlib in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let file_len = in_channel_length ic in
         let want = Z.to_int count in
         if S.(file_len < want) then FStar_Pervasives_Native.None
         else
           let start = S.(file_len - want) in
           seek_in ic start;
           FStar_Pervasives_Native.Some (really_input_string ic want))

let parquet_read_range_hex (path : Prims.string) (start : Prims.nat) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_read_range path start count with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw ->
      let module S = Stdlib in
      let b = Buffer.create S.(2 * String.length raw) in
      String.iter
        (fun ch -> Buffer.add_string b (Printf.sprintf "%02X" (Char.code ch)))
        raw;
      FStar_Pervasives_Native.Some (Buffer.contents b)

external parquet_zstd_decompress_hex_runtime :
  Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option
  = "caml_parquet_zstd_decompress_hex"

let parquet_zstd_decompress_hex (compressed_hex : Prims.string) (expected_size : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  parquet_zstd_decompress_hex_runtime compressed_hex (Prims.string_of_int expected_size)
'''

tail_impl = r'''let parquet_read_tail (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  if not (Sys.file_exists path) then FStar_Pervasives_Native.None
  else
    let ic = open_in_bin path in
    let module S = Stdlib in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () ->
         let file_len = in_channel_length ic in
         let want = Z.to_int count in
         if S.(file_len < want) then FStar_Pervasives_Native.None
         else
           let start = S.(file_len - want) in
           seek_in ic start;
           FStar_Pervasives_Native.Some (really_input_string ic want))

let parquet_read_tail_hex (path : Prims.string) (count : Prims.nat) :
  Prims.string FStar_Pervasives_Native.option=
  match parquet_read_tail path count with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw ->
      let module S = Stdlib in
      let b = Buffer.create S.(2 * String.length raw) in
      String.iter
        (fun ch -> Buffer.add_string b (Printf.sprintf "%02X" (Char.code ch)))
        raw;
      FStar_Pervasives_Native.Some (Buffer.contents b)
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
