#!/bin/bash
# Issue #89: Fast byte-indexed string primitives for the parser hot path.
# https://github.com/danbri/factoidal/issues/89
#
# The F* OCaml runtime's FStar.String routes length/index/sub through
# BatUTF8, which walks the byte sequence on every call to count
# codepoints -- O(n) per call, inside an O(n) parse loop. Profiling
# (docs/designissues/2026-04-20-turtle-parser-profile.md) shows 99.9%
# of leaf CPU samples were inside BatUTF8 primitives on a 1000-triple
# Turtle parse.
#
# Parser.FastString declares four assume-val primitives:
#   fs_byte_length, fs_byte_at, fs_byte_sub, fs_find_byte
# This patch replaces the `failwith "Not yet implemented"` bodies with
# one-liner OCaml bindings to String.length / String.unsafe_get /
# String.sub -- which are all O(1) or O(len) on OCaml strings, not
# O(n) byte walks.
#
# See Parser.FastString.fst for the safety argument (byte semantics are
# only correct for parsers that commit on ASCII bytes and treat
# multi-byte UTF-8 as opaque substrings -- Turtle, N-Triples, N-Quads,
# TriG all satisfy this).

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

FILE="$OUTDIR/Parser_FastString.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Parser_FastString.ml not found in $OUTDIR; skipping 89_fast_string_primitives.sh"
  exit 0
fi

# Idempotency marker: look for a distinctive token from the patched bodies.
if grep -q 'String.unsafe_get' "$FILE"; then
  echo "  89_fast_string_primitives.sh already applied to $FILE"
  exit 0
fi

echo "  Applying 89_fast_string_primitives.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

# Replace the four assume-val failwith stubs with direct OCaml bindings.
# Order matters: we search for the exact extracted text, which uses
# `Prims.nat` (= Z.t in the runtime) and `Prims.string` (= string).

# fs_byte_length : O(1) String.length (bytes)
content = content.replace(
    'let fs_byte_length (uu___ : Prims.string) : Prims.nat=\n'
    '  failwith "Not yet implemented: Parser.FastString.fs_byte_length"',
    'let fs_byte_length (s : Prims.string) : Prims.nat=\n'
    '  Z.of_int (String.length s)'
)

# fs_byte_at : O(1) byte fetch, returns nat in [0, 255]
content = content.replace(
    'let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=\n'
    '  failwith "Not yet implemented: Parser.FastString.fs_byte_at"',
    'let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=\n'
    '  Z.of_int (Char.code (String.unsafe_get s (Z.to_int i)))'
)

# fs_byte_sub : O(len) String.sub allocation.
# Permissive: clamp start/len to valid range so callers never crash on
# off-by-one. If the precondition is satisfied, this is equivalent to
# String.sub s start len; if it's violated we return "" instead of
# raising Invalid_argument.
content = content.replace(
    'let fs_byte_sub (s : Prims.string) (start : Prims.nat) (len : Prims.nat) :\n'
    '  Prims.string= failwith "Not yet implemented: Parser.FastString.fs_byte_sub"',
    'let fs_byte_sub (s : Prims.string) (start : Prims.nat) (len : Prims.nat) :\n'
    '  Prims.string=\n'
    '  let open Stdlib in\n'
    '  let slen = String.length s in\n'
    '  let i = Z.to_int start in\n'
    '  let n = Z.to_int len in\n'
    '  if i < 0 || n < 0 || i > slen then ""\n'
    '  else\n'
    '    let m = if i + n > slen then slen - i else n in\n'
    '    String.sub s i m'
)

# fs_find_byte : O(end - start) scan for a specific byte code.
# Returns fs_byte_length s if not found.
content = content.replace(
    'let fs_find_byte (s : Prims.string) (b : Prims.nat) (start : Prims.nat) :\n'
    '  Prims.nat= failwith "Not yet implemented: Parser.FastString.fs_find_byte"',
    'let fs_find_byte (s : Prims.string) (b : Prims.nat) (start : Prims.nat) :\n'
    '  Prims.nat=\n'
    '  let open Stdlib in\n'
    '  let slen = String.length s in\n'
    '  let bi = Z.to_int b in\n'
    '  let si = Z.to_int start in\n'
    '  let rec loop i =\n'
    '    if i >= slen then Z.of_int slen\n'
    '    else if Char.code (String.unsafe_get s i) = bi then Z.of_int i\n'
    '    else loop (i + 1)\n'
    '  in\n'
    '  loop (if si < 0 then 0 else si)'
)

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  Parser_FastString.ml patched."
