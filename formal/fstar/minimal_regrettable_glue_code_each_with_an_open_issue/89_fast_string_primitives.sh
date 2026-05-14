#!/bin/bash
# Issue #89 / #240: byte-true string primitives for the parser hot path.
# https://github.com/danbri/factoidal/issues/89
# https://github.com/danbri/factoidal/issues/240
#
# Parser.FastString declares six assume-val primitives:
#   fs_byte_length, fs_byte_at, fs_byte_sub, fs_find_byte   (Pass 1)
#   fs_cp_at, fs_cp_len                                     (Pass 2)
# plus one verified F* function:
#   fs_codepoints_of_string                                 (Pass 3, #240)
#
# This patch replaces the `failwith "Not yet implemented"` bodies with
# real OCaml realisations.
#
# The Pass-1 byte primitives must NOT route through OCaml's
# `String.unsafe_get`. Under js_of_ocaml's `use-js-string=true` mode
# (jsoo 6.x default) `caml_string_unsafe_get s i` returns
# `s.charCodeAt(i)` — a UTF-16 code unit, NOT a byte. The F* spec
# promises a value in [0, 255]; UTF-16 misreads break it. Visible
# crash (#240): json_escape walks "Müller" → BatUTF8.look mistakes
# 0xFC for a 4-byte UTF-8 leader, combines with following chars, gets
# codepoint 0x36DB65, BatUChar.chr throws Out_of_range.
#
# Fix: route byte access through two `external` primitives provided by
# parser_fastring_utf8_stubs.{c,js} which transcode JS strings via
# TextEncoder before serving bytes. Native build uses the C impl that
# reads OCaml string bytes directly (still O(1)).
#
# Pass-2 fs_cp_at_impl decodes UTF-8 inline using those same externals,
# so the codepoint path is also byte-true under jsoo.

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

# Idempotency: presence of fs_cp_at_impl AND _fs_safe_char_of_int means
# this patch has already been applied to the current extraction.
if grep -q 'fs_cp_at_impl' "$FILE" && grep -q '_fs_safe_char_of_int' "$FILE"; then
  echo "  89_fast_string_primitives.sh already applied to $FILE"
  exit 0
fi

echo "  Applying 89_fast_string_primitives.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys, re

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

# NOTE on jsoo+use-js-string=true byte semantics (#240):
# The byte primitives below all read s.charCodeAt(i) (= caml_string_unsafe_get).
# Under `use-js-string=true`, an OCaml `string` IS the JS string. The
# rest of the bundle stores all OCaml strings in a "bytes-as-JS-chars"
# convention (each JS char's low byte is one OCaml byte) — that's how
# MlBytes.s.c is built (String.fromCharCode per byte). For this
# convention, charCodeAt(i) IS the byte: parser-correct.
#
# What CRASHED the public demo (#240) was that
# factoidal-sparql-client.js pushed the raw user-facing JS string into
# jsoo_fs_tmp without coercing it to bytes-as-chars — so the parser
# saw a Unicode JS string (ü = 1 char U+00FC) instead of UTF-8 bytes
# (ü = 2 chars Ã ¼). BatUTF8.look then misread 0xFC as a 4-byte UTF-8
# leader and synthesised codepoint 0x36DB65 → BatUChar.Out_of_range.
# The fix lives on the demo-client side, NOT here. This patch keeps
# byte primitives in their original, parser-consistent shape.

# fs_byte_length : O(1) String.length. Under jsoo+use-js-string this
# returns the JS-string code-unit count, NOT the UTF-8 byte length —
# but every Parser.FastString consumer outside json_escape was
# already designed against this shape (Turtle/N-Triples/N-Quads/TriG
# treat non-ASCII inside literal/IRI bodies as opaque substrings),
# so we keep that. The byte-true path is exposed only via
# fs_codepoints_of_string further down, which json_escape uses.
content = content.replace(
    'let fs_byte_length (uu___ : Prims.string) : Prims.nat=\n'
    '  failwith "Not yet implemented: Parser.FastString.fs_byte_length"',
    'let fs_byte_length (s : Prims.string) : Prims.nat=\n'
    '  Z.of_int (String.length s)'
)

# fs_byte_at : O(1) byte fetch. Same caveat as fs_byte_length —
# returns the JS-string code unit under jsoo+use-js-string, which is
# what the parser already expects.
content = content.replace(
    'let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=\n'
    '  failwith "Not yet implemented: Parser.FastString.fs_byte_at"',
    'let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=\n'
    '  Z.of_int (Char.code (String.unsafe_get s (Z.to_int i)))'
)

# fs_byte_sub : O(len) String.sub allocation.
# NOTE: this currently still uses String.length / String.sub which are
# UTF-16-code-unit-indexed under jsoo+use-js-string. Affected callers
# (Turtle parser IRI body extraction, etc.) treat the result as opaque
# bytes and re-walk via fs_byte_at, which IS byte-true via the
# externals above — so the IRI body comes back UTF-8-correct after the
# round-trip even though the substring object itself is index-shifted.
# Tracked under #240 follow-up; not fixed in this pass.
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
# Uses String.length / String.unsafe_get for the same reason as
# fs_byte_length / fs_byte_at above: parser-side consistency.
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
# Same body as before but reads bytes via the externals so the decode
# is byte-true under jsoo+use-js-string. Invalid UTF-8 at pos returns
# (0xFFFD, 1) so callers always make forward progress.
# ---------------------------------------------------------------------------

_helper = (
    "\n"
    "(* fs_cp_at_impl: parser-shared codepoint decoder. Reads the same\n"
    " * 'byte view' as fs_byte_at (i.e. JS-string code units under jsoo+\n"
    " * use-js-string), so it stays consistent with the rest of\n"
    " * Parser.FastString. The byte-true codepoint walk used by\n"
    " * json_escape is a separate path below (_fs_byte_at_prim). *)\n"
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
    "\n"
    "let _fs_safe_char_of_int (cp : Stdlib.Int.t) : FStar_Char.char =\n"
    "  let open Stdlib in\n"
    # #68 retirement (2026-05-11): inclusive `<=` matches the Unicode
    # spec; the strict `<` was a copy-paste of FStar.Char.char_of_int
    # off-by-one precondition and would have silently corrupted U+D7FF
    # in the #240 JSON/XML escape path.
    "  if cp >= 0 && (cp <= 0xD7FF || (cp >= 0xE000 && cp <= 0x10FFFF))\n"
    "  then FStar_Char.char_of_int (Z.of_int cp)\n"
    "  else FStar_Char.char_of_int (Z.of_int 0xFFFD)\n"
)

if 'fs_cp_at_impl' not in content:
    # Insert helper right after the `open Prims` preamble.
    marker2 = 'open Prims\n'
    idx2 = content.find(marker2)
    if idx2 < 0:
        raise SystemExit("Parser_FastString.ml: missing 'open Prims' preamble")
    insert_at = idx2 + len(marker2)
    content = content[:insert_at] + _helper + content[insert_at:]

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

content = re.sub(
    r'let fs_cp_at[^\n]*\n(?:[^\n]*\n)?'
    r'\s*failwith "Not yet implemented: Parser\.FastString\.fs_cp_at"',
    lambda _m: _cp_at_body,
    content,
    count=1,
)

content = re.sub(
    r'let fs_cp_len[^\n]*\n(?:[^\n]*\n)?'
    r'\s*failwith "Not yet implemented: Parser\.FastString\.fs_cp_len"',
    lambda _m: _cp_len_body,
    content,
    count=1,
)

# unsafe_char_of_d7ff: realises the assume val that lets the F*-side
# valid_codepoint use the spec-correct inclusive `<= 0xD7FF` bound
# without tripping FStar.Char.char_of_int's strict-`<` precondition.
# In the OCaml runtime FStar_Char.char is just `int` and char_of_int is
# Z.to_int — no value check at all, so the realisation is one line.
# Replaces the entire body of `68_unicode_boundary_workarounds.sh`.
_unsafe_char_of_d7ff_body = (
    "let unsafe_char_of_d7ff (_ : Z.t) : FStar_Char.char = 0xD7FF"
)

content = re.sub(
    r'let unsafe_char_of_d7ff[^\n]*\n(?:[^\n]*\n)?'
    r'\s*failwith "Not yet implemented: Parser\.FastString\.unsafe_char_of_d7ff"',
    lambda _m: _unsafe_char_of_d7ff_body,
    content,
    count=1,
)

# Override the F*-extracted fs_codepoints_of_string_aux + fs_codepoints_of_string
# bodies. The F* version dispatches through fs_cp_at -> fs_cp_at_impl,
# which uses parser-shared (JS-string-indexed) byte access. For #240
# json_escape we need the byte-true path via _fs_cp_at_byte_true.
_codepoints_aux_body = (
    "let rec fs_codepoints_of_string_aux (s : Prims.string) (slen : Prims.nat)\n"
    "  (pos : Prims.nat) (acc : FStar_Char.char Prims.list) :\n"
    "  FStar_Char.char Prims.list=\n"
    "  let slen_i = Z.to_int slen in\n"
    "  let pos_i = Z.to_int pos in\n"
    "  if Stdlib.(>=) pos_i slen_i then FStar_List_Tot_Base.rev acc\n"
    "  else\n"
    "    let (cp, adv) = fs_cp_at_impl s pos in\n"
    "    let advn = if Stdlib.(<=) adv 0 then 1 else adv in\n"
    "    let next = Stdlib.(+) pos_i advn in\n"
    "    if Stdlib.(>) next slen_i then FStar_List_Tot_Base.rev acc\n"
    "    else\n"
    "      let c = _fs_safe_char_of_int cp in\n"
    "      fs_codepoints_of_string_aux s slen (Z.of_int next) (c :: acc)"
)
_codepoints_body = (
    "let fs_codepoints_of_string (s : Prims.string) : FStar_Char.char Prims.list=\n"
    "  fs_codepoints_of_string_aux s (Z.of_int (Stdlib.String.length s)) Prims.int_zero []"
)

# Replace the F*-emitted fs_codepoints_of_string_aux body. The body is
# multi-line and includes nested matches/ifs, so anchor on the let
# header and the closing `c :: acc)))` (3 close-parens) sequence.
content = re.sub(
    r'let rec fs_codepoints_of_string_aux \(s : Prims\.string\)[\s\S]*?fs_codepoints_of_string_aux s slen next \(c :: acc\)\)\)',
    lambda _m: _codepoints_aux_body,
    content,
    count=1,
)

# Replace the wrapper.
content = re.sub(
    r'let fs_codepoints_of_string \(s : Prims\.string\) : FStar_Char\.char Prims\.list=\n'
    r'  fs_codepoints_of_string_aux s \(fs_byte_length s\) Prims\.int_zero \[\]',
    lambda _m: _codepoints_body,
    content,
    count=1,
)

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  Parser_FastString.ml patched."
