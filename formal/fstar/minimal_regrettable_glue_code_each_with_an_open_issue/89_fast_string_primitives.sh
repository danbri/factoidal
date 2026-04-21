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
# Parser.FastString declares six assume-val primitives:
#   fs_byte_length, fs_byte_at, fs_byte_sub, fs_find_byte   (Pass 1)
#   fs_cp_at, fs_cp_len                                     (Pass 2)
# This patch replaces the `failwith "Not yet implemented"` bodies with
# direct OCaml bindings:
#   * byte primitives -> String.length / String.unsafe_get / String.sub
#     (all O(1) or O(len), not O(n) byte walks)
#   * codepoint primitives -> inline 1..4-byte UTF-8 decoder returning
#     (codepoint, advance); invalid UTF-8 maps to (0xFFFD, 1)
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

# Idempotency: check both Pass-1 and Pass-2 markers. Pass 1 = byte
# primitives (String.unsafe_get). Pass 2 = codepoint primitives
# (fs_cp_at_impl). We apply only the parts that are still stubs.
if grep -q 'String.unsafe_get' "$FILE" && grep -q 'fs_cp_at_impl' "$FILE"; then
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

# ---------------------------------------------------------------------------
# Pass 2: fs_cp_at / fs_cp_len -- UTF-8 codepoint decoder.
# Invalid UTF-8 at pos returns (0xFFFD, 1) so callers always make forward
# progress. fs_cp_len is just the second element of fs_cp_at, shared via a
# private fs_cp_at_impl helper so we don't allocate a Z.t twice.
# ---------------------------------------------------------------------------

# Find an anchor line to insert helper + primitives just before them.
# The extracted file starts with `open Prims`; we inject right after.
_helper = (
    "\n"
    "let fs_cp_at_impl (s : Prims.string) (pos : Prims.nat) : Stdlib.Int.t * Stdlib.Int.t =\n"
    "  let open Stdlib in\n"
    "  let p = Z.to_int pos in\n"
    "  let slen = String.length s in\n"
    "  if p < 0 || p >= slen then (0xFFFD, 1)\n"
    "  else\n"
    "    let b0 = Char.code (String.unsafe_get s p) in\n"
    "    if b0 < 0x80 then (b0, 1)\n"
    "    else if b0 < 0xC2 then (0xFFFD, 1)\n"
    "    else if b0 < 0xE0 then begin\n"
    "      if p + 1 >= slen then (0xFFFD, 1)\n"
    "      else\n"
    "        let b1 = Char.code (String.unsafe_get s (p + 1)) in\n"
    "        if (b1 land 0xC0) <> 0x80 then (0xFFFD, 1)\n"
    "        else\n"
    "          let cp = ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F) in\n"
    "          (cp, 2)\n"
    "    end\n"
    "    else if b0 < 0xF0 then begin\n"
    "      if p + 2 >= slen then (0xFFFD, 1)\n"
    "      else\n"
    "        let b1 = Char.code (String.unsafe_get s (p + 1)) in\n"
    "        let b2 = Char.code (String.unsafe_get s (p + 2)) in\n"
    "        if (b1 land 0xC0) <> 0x80 || (b2 land 0xC0) <> 0x80 then (0xFFFD, 1)\n"
    "        else\n"
    "          let cp = ((b0 land 0x0F) lsl 12) lor\n"
    "                   ((b1 land 0x3F) lsl 6) lor\n"
    "                   (b2 land 0x3F) in\n"
    "          (* Reject overlong (< 0x800) and UTF-16 surrogates. *)\n"
    "          if cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF) then (0xFFFD, 1)\n"
    "          else (cp, 3)\n"
    "    end\n"
    "    else if b0 < 0xF5 then begin\n"
    "      if p + 3 >= slen then (0xFFFD, 1)\n"
    "      else\n"
    "        let b1 = Char.code (String.unsafe_get s (p + 1)) in\n"
    "        let b2 = Char.code (String.unsafe_get s (p + 2)) in\n"
    "        let b3 = Char.code (String.unsafe_get s (p + 3)) in\n"
    "        if (b1 land 0xC0) <> 0x80 || (b2 land 0xC0) <> 0x80 ||\n"
    "           (b3 land 0xC0) <> 0x80 then (0xFFFD, 1)\n"
    "        else\n"
    "          let cp = ((b0 land 0x07) lsl 18) lor\n"
    "                   ((b1 land 0x3F) lsl 12) lor\n"
    "                   ((b2 land 0x3F) lsl 6) lor\n"
    "                   (b3 land 0x3F) in\n"
    "          if cp < 0x10000 || cp > 0x10FFFF then (0xFFFD, 1)\n"
    "          else (cp, 4)\n"
    "    end\n"
    "    else (0xFFFD, 1)\n"
)

if 'fs_cp_at_impl' not in content:
    # Place helper right after the `open Prims` preamble so it's in scope
    # for both fs_cp_at and fs_cp_len below.
    marker = 'open Prims\n'
    idx = content.find(marker)
    if idx < 0:
        raise SystemExit("Parser_FastString.ml: missing 'open Prims' preamble")
    insert_at = idx + len(marker)
    content = content[:insert_at] + _helper + content[insert_at:]

# fs_cp_at / fs_cp_len: the F* emitter sometimes wraps the return type
# onto the next line, sometimes keeps it on the signature line. Use a
# regex on the unique failwith message so either form matches. Use a
# lambda replacement to sidestep \\-escape issues in re.sub's repl arg.
import re as _re

_cp_at_body = (
    "let fs_cp_at (s : Prims.string) (pos : Prims.nat) : "
    "(Prims.nat * Prims.nat)=\n"
    "  let (cp, adv) = fs_cp_at_impl s pos in\n"
    "  (Z.of_int cp, Z.of_int adv)"
)
_cp_len_body = (
    "let fs_cp_len (s : Prims.string) (pos : Prims.nat) : Prims.nat=\n"
    "  let (_, adv) = fs_cp_at_impl s pos in\n"
    "  Z.of_int adv"
)

content = _re.sub(
    r'let fs_cp_at[^\n]*\n(?:[^\n]*\n)?'
    r'\s*failwith "Not yet implemented: Parser\.FastString\.fs_cp_at"',
    lambda _m: _cp_at_body,
    content,
    count=1,
)

content = _re.sub(
    r'let fs_cp_len[^\n]*\n(?:[^\n]*\n)?'
    r'\s*failwith "Not yet implemented: Parser\.FastString\.fs_cp_len"',
    lambda _m: _cp_len_body,
    content,
    count=1,
)

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  Parser_FastString.ml patched."
