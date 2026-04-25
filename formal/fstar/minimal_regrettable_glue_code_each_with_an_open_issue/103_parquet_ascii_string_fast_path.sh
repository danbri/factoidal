#!/bin/bash
# Issue #103: ASCII fast-path for FStar_String ops in Parquet_Footer.ml
# https://github.com/danbri/factoidal/issues/103
#
# Background
# ----------
# F* extracts strings to OCaml using the fstar.lib runtime, where
# FStar_String routes index/length/sub through BatUTF8.  BatUTF8 walks
# the byte sequence on every call to count codepoints, so each call is
# O(N) and a substring or repeated index becomes O(N^2).
#
# Parquet.Footer.fst manipulates a *hex-encoded* representation of the
# decompressed page payload (see `dpc_payload_hex` and friends).  The
# hex strings are by construction pure ASCII (digits + a-f); for ASCII
# strings, codepoint count == byte count and codepoint slice ==
# byte slice, so byte-indexed operations are observationally equivalent
# to the F* String operations.  This means we can substitute byte ops
# for the F* String ops only inside Parquet_Footer.ml and preserve
# correctness.
#
# Why this is in the patch directory rather than F*
# -------------------------------------------------
# Parser.FastString.fst already declares byte-fast primitives behind
# `assume val` (issue #89).  The proper fix is for Parquet.Footer.fst
# to call those primitives directly, but that is a non-trivial refactor
# of ~30 helper functions and out of scope for the current
# COTTAS-load hang patch.  This file does the minimal sed-style rewrite
# of the extracted Parquet_Footer.ml to bypass FStar_String for the
# ASCII hex path.  No semantic logic moves into the patch -- it's a
# pure perf override of three string primitives in one .ml file.
#
# Symptom this fixes:
#   factoidal{,-http} --data-cottas <file>
#     pegs CPU at ~99% in BatUTF8.nth_aux for 5+ minutes on the
#     3.14M-quad UK Parliament COTTAS, never finishes, never reaches
#     LISTEN (HTTP) or prints the count (CLI).
#   See docs/designissues/2026-04-25-cottas-parquet-load-path-perf.md
#   for the prior diagnosis.
#
# Hot path that this patch unblocks (one-shot for the whole column):
#   probe_parquet_column_delta_length_byte_array_page_cache
#   -> String.sub payload_hex values_start_hex (...)   (line ~1553 in .fst)
#   -> slice_all_dlba_values  (one String.sub per row)
# Both call sites use FStar_String.sub on a multi-MB hex string and
# trigger the BatUTF8 O(N^2) blowup.
#
# Update 2026-04-25 (Yod3, #97): once the per-miniblock bit_width fix
# lets `build_dlba_length_list` decode every length on the parliament
# corpus, the next bottleneck moves to `ascii_string_of_hex_slice`
# which builds an FStar.Char.char list and then calls
# `String.string_of_list`.  FStar_String.string_of_list is implemented
# as `BatUTF8.init n (fun i -> chr (List.at l i))` which is O(N^2) per
# string -- and for parliament's ~12.6 M values that means many minutes
# of post-decode CPU.  We now also override `string_of_list` for this
# module: for ASCII chars the codepoint sequence equals the byte
# sequence, so we can build the result via Bytes.create + unsafe_set
# in O(N).  Same safety argument as the original three primitives: the
# Parquet_Footer code only ever feeds ASCII bytes (digits/A-F when
# reading from `_payload_hex`, or printable bytes 32-126 when decoding
# `value_string_at` via `ascii_string_of_hex_slice`).

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/Parquet_Footer.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Parquet_Footer.ml not found in $OUTDIR; skipping 103_parquet_ascii_string_fast_path.sh"
  exit 0
fi

# Idempotency: already patched if the local override module is present.
if grep -q '__PARQUET_ASCII_STRING_FAST_PATH__' "$FILE"; then
  echo "  103_parquet_ascii_string_fast_path.sh already applied to $FILE"
  exit 0
fi

echo "  Applying 103_parquet_ascii_string_fast_path.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

# Inject a private FStar_String shadow at the top of the module that
# routes index/strlen/length/sub/string_of_list through OCaml byte ops.
# This is only correct for ASCII-only hex strings, which is exactly
# what the rest of Parquet_Footer manipulates (every helper either
# consumes `payload_hex` / `tail` / `footer_hex` / etc., or builds a
# list of single-byte ASCII codepoints via `ascii_string_of_hex_slice`
# whose chars come from `byte_at_hex` and are therefore in [0,255] and
# in practice [32,126] for printable ASCII payload).

shadow = (
    "\n"
    "(* __PARQUET_ASCII_STRING_FAST_PATH__\n"
    "   Patched by 103_parquet_ascii_string_fast_path.sh.\n"
    "   See the patch file for the safety argument: every Parquet_Footer\n"
    "   call site that reaches one of these helpers passes an ASCII-only\n"
    "   hex string, so codepoint ops collapse onto byte ops. *)\n"
    "module FStar_String = struct\n"
    "  include FStar_String\n"
    "  (* The enclosing file does `open Prims`, which shadows OCaml's `int`\n"
    "     and `string` to Prims aliases (Z.t and Stdlib.String.t). All the\n"
    "     stdlib references below have to be fully qualified to escape that. *)\n"
    "  let index (s : Stdlib.String.t) (i : Z.t) : Stdlib.Int.t =\n"
    "    Stdlib.Char.code (Stdlib.String.unsafe_get s (Z.to_int i))\n"
    "  let strlen (s : Stdlib.String.t) : Z.t =\n"
    "    Z.of_int (Stdlib.String.length s)\n"
    "  let length = strlen\n"
    "  let sub (s : Stdlib.String.t) (i : Z.t) (j : Z.t) : Stdlib.String.t =\n"
    "    Stdlib.String.sub s (Z.to_int i) (Z.to_int j)\n"
    "  (* string_of_list: ASCII fast-path. Original walks the list O(n^2)\n"
    "     via BatUTF8.init+List.at; we materialise once into a Bytes.\n"
    "     The fstar.lib runtime declares `type char = FStar_Char.char =\n"
    "     int`, so the list is a list of codepoint ints. Safe iff every\n"
    "     codepoint fits in one byte, which is true for the\n"
    "     ascii_string_of_hex_slice path (chars come from byte_at_hex\n"
    "     and are always in [0,255]). *)\n"
    "  let string_of_list (l : FStar_Char.char list) : Stdlib.String.t =\n"
    "    let n = Stdlib.List.length l in\n"
    "    let b = Stdlib.Bytes.create n in\n"
    "    Stdlib.List.iteri (fun i c ->\n"
    "      Stdlib.Bytes.unsafe_set b i\n"
    "        (Stdlib.Char.unsafe_chr (c land 0xff))) l;\n"
    "    Stdlib.Bytes.unsafe_to_string b\n"
    "end\n"
    "\n"
)

marker = 'open Prims\n'
idx = content.find(marker)
if idx < 0:
    raise SystemExit("Parquet_Footer.ml: missing 'open Prims' preamble")
insert_at = idx + len(marker)
content = content[:insert_at] + shadow + content[insert_at:]

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  Parquet_Footer.ml patched."
