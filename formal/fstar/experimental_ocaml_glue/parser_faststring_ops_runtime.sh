#!/bin/bash
# Parser.FastString hot-path realisation (rule-11(b), Option-B perf
# realisation -- FastString re-founding Step 3,
# docs/designissues/2026-08-10-faststring-refounding-plan.md).
#
# Parser.FastString.fst (Step 2, same migration) re-founded its six
# primitives -- fs_byte_length, fs_byte_at, fs_byte_sub, fs_find_byte,
# fs_cp_at, fs_cp_len -- as real Parser.FastString.Spec-backed
# DEFINITIONS instead of assume vals. Extracted as-is, those definitions
# walk a `list byte` built from the whole string on every call: correct,
# but O(n) (fs_byte_length/at/find_byte/cp_at/cp_len) to O(n^2) over a
# scan loop (the profiled BatUTF8 pathology this module exists to avoid
# in the first place -- see Parser.FastString.fst's own banner).
#
# This patch overrides each `fs_*` with the SAME fast OCaml bodies the
# old (pre-migration) `minimal_regrettable_glue_code_each_with_an_open_issue/
# 89_fast_string_primitives.sh` used to install directly over the
# assume-val stubs -- byte-true O(1)/O(len) operations against
# String.length / String.unsafe_get / String.sub -- with ONE change:
# fs_byte_at now does its own in-bounds check and returns 0 out of range,
# to match the TOTAL Spec-backed function it overrides (the pre-migration
# fs_byte_at was `assume val`, with no totality obligation at the F*
# level at all; Step 2's fs_byte_at is `s:string -> i:nat -> n:nat{n<256}`,
# total, and Spec.nth_byte's out-of-range case returns 0 -- the fast
# override must agree, or the two diverge on exactly the equivalence
# test's out-of-bounds probes).
#
# DELETABILITY. The Parser.FastString.fsti-declared `fs_*_spec` twins
# (Parser.FastString.fst, right next to each `fs_*`) are INDEPENDENT
# F*-verified functions computing the identical Spec formula under their
# own name -- this patch never touches them. Deleting this patch drops
# `fs_*` back to computing exactly what `fs_*_spec` already computes:
# slower, never wrong. tests/unit/parser_fast_string_equivalence.ml
# asserts `fs_* == fs_*_spec` on generated inputs to keep that true.
#
# WHY OVERRIDE IN PLACE rather than append new bindings at file end: F*
# extracts Parser.FastString.fst's definitions in source order --
# fs_byte_length, fs_byte_at, fs_byte_sub, fs_find_byte, fs_cp_at,
# fs_cp_len, THEN the six fs_*_spec twins, THEN
# fs_codepoints_of_string_aux (which calls `fs_cp_at` by name). OCaml's
# plain (non-`let rec`) top-level `let` shadowing resolves a name
# reference to the NEAREST PRECEDING binding at compile time -- so
# editing `fs_cp_at`'s definition IN PLACE (same name, same position,
# this patch's approach) means fs_codepoints_of_string_aux automatically
# picks up the fast fs_cp_at too, with no separate override needed (the
# pre-migration patch 89 carried a dedicated
# fs_codepoints_of_string_aux/fs_codepoints_of_string override for
# exactly this reason; it is deleted, not moved, in this migration --
# see the cut-down 89_fast_string_primitives.sh header). Appending new
# `fs_cp_at` bindings at file end instead would leave
# fs_codepoints_of_string_aux (defined earlier in the file) bound to the
# slow Spec-backed fs_cp_at forever -- confirmed against the actual
# extracted file layout before choosing in-place substitution.
#
# jsoo NOTE (carried over verbatim from the pre-migration patch): under
# jsoo's `use-js-string=true` mode, `caml_string_unsafe_get s i` returns
# `s.charCodeAt(i)` -- a UTF-16 code unit, not a byte -- but every
# Parser.FastString consumer already treats non-ASCII bytes inside
# literal/IRI bodies as opaque substrings under the project's
# "bytes-as-JS-chars" convention (see #240), so this file's byte
# primitives stay in that same parser-consistent shape. No change from
# the pre-migration patch's jsoo behaviour.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/Parser_FastString.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Parser_FastString.ml not found in $OUTDIR; skipping parser_faststring_ops_runtime.sh"
  exit 0
fi

# Idempotency: presence of the fs_cp_at_impl helper this patch installs
# means the fast bodies are already in place.
if grep -q 'fs_cp_at_impl' "$FILE"; then
  echo "  parser_faststring_ops_runtime.sh already applied to $FILE"
  exit 0
fi

echo "  Applying parser_faststring_ops_runtime.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys, re

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

def replace_exact(content, old, new, name):
    if old not in content:
        raise SystemExit(f"{name}: expected extracted body not found (Parser.FastString.fst changed shape?)")
    return content.replace(old, new, 1)

# --- fs_byte_length --------------------------------------------------
old = (
    'let fs_byte_length (s : Prims.string) : Prims.nat=\n'
    '  FStar_List_Tot_Base.length (Parser_FastString_Spec.utf8_bytes s)\n'
)
new = (
    'let fs_byte_length (s : Prims.string) : Prims.nat=\n'
    '  Z.of_int (String.length s)\n'
)
content = replace_exact(content, old, new, 'fs_byte_length')

# --- fs_byte_at (bounds-checked: total, returns 0 out of range to match
#     the Spec-backed fs_byte_at it overrides) ---------------------------
old = (
    'let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=\n'
    '  match Parser_FastString_Spec.nth_byte (Parser_FastString_Spec.utf8_bytes s)\n'
    '          i\n'
    '  with\n'
    '  | FStar_Pervasives_Native.Some b -> b\n'
    '  | FStar_Pervasives_Native.None -> Prims.int_zero\n'
)
new = (
    'let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=\n'
    '  let ii = Z.to_int i in\n'
    '  if ii < 0 || ii >= String.length s then Prims.int_zero\n'
    '  else Z.of_int (Char.code (String.unsafe_get s ii))\n'
)
content = replace_exact(content, old, new, 'fs_byte_at')

# --- fs_byte_sub (verbatim from the pre-migration patch 89) -----------
old = (
    'let fs_byte_sub (s : Prims.string) (start : Prims.nat) (len : Prims.nat) :\n'
    '  Prims.string=\n'
    '  FStar_String.string_of_list\n'
    '    (Parser_FastString_Spec.utf8_decode_all\n'
    '       (Parser_FastString_Spec.slice_bytes\n'
    '          (Parser_FastString_Spec.utf8_bytes s) start len))\n'
)
new = (
    'let fs_byte_sub (s : Prims.string) (start : Prims.nat) (len : Prims.nat) :\n'
    '  Prims.string=\n'
    '  let open Stdlib in\n'
    '  let slen = String.length s in\n'
    '  let i = Z.to_int start in\n'
    '  let n = Z.to_int len in\n'
    '  if i < 0 || n < 0 || i > slen then ""\n'
    '  else\n'
    '    let m = if i + n > slen then slen - i else n in\n'
    '    String.sub s i m\n'
)
content = replace_exact(content, old, new, 'fs_byte_sub')

# --- fs_find_byte (verbatim from the pre-migration patch 89) ----------
old = (
    'let fs_find_byte (s : Prims.string) (b : Prims.nat) (start : Prims.nat) :\n'
    '  Prims.nat=\n'
    '  Parser_FastString_Spec.find_byte (Parser_FastString_Spec.utf8_bytes s) b\n'
    '    start\n'
)
new = (
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
    '  loop (if si < 0 then 0 else si)\n'
)
content = replace_exact(content, old, new, 'fs_find_byte')

# --- fs_cp_at / fs_cp_len: shared fs_cp_at_impl helper, inserted once
#     right after the `open Prims` preamble (verbatim decode loop from
#     the pre-migration patch 89). ---------------------------------------
helper = (
    "\n"
    "(* fs_cp_at_impl: parser-shared codepoint decoder, verbatim from the\n"
    " * pre-migration patch 89 (FastString re-founding Step 3, 2026-08-10). *)\n"
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
marker = 'open Prims\n'
idx = content.find(marker)
if idx < 0:
    raise SystemExit("Parser_FastString.ml: missing 'open Prims' preamble")
insert_at = idx + len(marker)
content = content[:insert_at] + helper + content[insert_at:]

old = (
    'let fs_cp_at (s : Prims.string) (pos : Prims.nat) : (Prims.nat * Prims.nat)=\n'
    '  let uu___ =\n'
    '    Parser_FastString_Spec.utf8_decode_at\n'
    '      (Parser_FastString_Spec.utf8_bytes s) pos in\n'
    '  match uu___ with | (cp, adv) -> (cp, adv)\n'
)
new = (
    'let fs_cp_at (s : Prims.string) (pos : Prims.nat) : (Prims.nat * Prims.nat)=\n'
    '  let (cp, adv) = fs_cp_at_impl s pos in\n'
    '  (Z.of_int cp, Z.of_int adv)\n'
)
content = replace_exact(content, old, new, 'fs_cp_at')

old = (
    'let fs_cp_len (s : Prims.string) (pos : Prims.nat) : Prims.nat=\n'
    '  let uu___ =\n'
    '    Parser_FastString_Spec.utf8_decode_at\n'
    '      (Parser_FastString_Spec.utf8_bytes s) pos in\n'
    '  match uu___ with | (uu___1, adv) -> adv\n'
)
new = (
    'let fs_cp_len (s : Prims.string) (pos : Prims.nat) : Prims.nat=\n'
    '  let (_, adv) = fs_cp_at_impl s pos in\n'
    '  Z.of_int adv\n'
)
content = replace_exact(content, old, new, 'fs_cp_len')

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  Parser_FastString.ml patched (fast ops, spec twins untouched)."
