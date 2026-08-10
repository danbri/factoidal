#!/bin/bash
# Issue #89 / #240: byte-true string primitives for the parser hot path.
# https://github.com/danbri/factoidal/issues/89
# https://github.com/danbri/factoidal/issues/240
#
# CUT DOWN 2026-08-10 (FastString re-founding Step 2/3,
# docs/designissues/2026-08-10-faststring-refounding-plan.md): this patch
# used to realise SIX assume vals (fs_byte_length, fs_byte_at, fs_byte_sub,
# fs_find_byte, fs_cp_at, fs_cp_len) plus a dedicated
# fs_codepoints_of_string_aux/fs_codepoints_of_string override. All six
# primitives are now real Parser.FastString.Spec-backed DEFINITIONS
# (Step 2) -- they are no longer acknowledged GAPs under iron rule #3(a),
# so this file no longer patches them. Their fast-OCaml realisation moved
# to experimental_ocaml_glue/parser_faststring_ops_runtime.sh as a
# rule-11(b) Option-B PERFORMANCE realisation (overrides `fs_*`, leaves
# the independently-F*-verified `fs_*_spec` twins untouched). The
# dedicated fs_codepoints_of_string_aux override is deleted outright
# (not moved): with fs_cp_at itself patched in place, F*-extracted
# fs_codepoints_of_string_aux (which calls fs_cp_at by name, defined
# after it in the same compilation unit) picks up the fast fs_cp_at
# automatically through ordinary OCaml let-shadowing -- confirmed by
# reading the post-patch Parser_FastString.ml, not assumed.
#
# What remains here is the ONE assume val this migration could not
# eliminate: unsafe_char_of_d7ff, now declared in its own
# Parser.FastString.CharBoundary.fst (Step 2 split -- see that file's
# header for why an axiom cannot live directly in a module that also
# carries a restrictive .fsti). `FStar.Char.char_of_int`'s F* precondition
# is `i < 0xd7ff \/ (i >= 0xe000 /\ i <= 0x10ffff)` -- the strict `<`
# excludes U+D7FF, a valid Unicode scalar (the surrogate gap is
# U+D800..U+DFFF inclusive). No F* term can inhabit this without either
# violating the precondition or using an escape hatch banned by iron rule
# #10. In the OCaml runtime `FStar_Char.char` is just `int` and
# `char_of_int = Z.to_int` -- no runtime check at all
# (`/root/.opam/fstar/lib/fstar/ulib/ml/app/FStar_Char.ml`), so the
# realisation is a one-line constant.
#
# Tracking: docs/designissues/2026-05-10-issue-68-options.md (subagent
# report). Optional upstream-track suggestion: file an F* issue against
# `ulib/FStar.Char.fsti` lines 38 and 57 -- both should read `<= 0xd7ff`.
# We don't block on it.

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

FILE="$OUTDIR/Parser_FastString_CharBoundary.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Parser_FastString_CharBoundary.ml not found in $OUTDIR; skipping 89_fast_string_primitives.sh"
  exit 0
fi

# Idempotency: the realised body no longer contains the failwith marker.
if ! grep -q 'failwith' "$FILE"; then
  echo "  89_fast_string_primitives.sh already applied to $FILE"
  exit 0
fi

echo "  Applying 89_fast_string_primitives.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys, re

path = sys.argv[1]
with open(path, 'r') as f:
    content = f.read()

# unsafe_char_of_d7ff: realises the assume val that lets the F*-side
# valid_codepoint use the spec-correct inclusive `<= 0xD7FF` bound
# without tripping FStar.Char.char_of_int's strict-`<` precondition.
pattern = re.compile(
    r'let unsafe_char_of_d7ff \(i : Prims\.int\) : FStar_Char\.char=\n'
    r'\s*failwith\n?'
    r'\s*"Not yet implemented: Parser\.FastString\.CharBoundary\.unsafe_char_of_d7ff"\n?'
)
replacement = 'let unsafe_char_of_d7ff (_ : Z.t) : FStar_Char.char = 0xD7FF\n'

if not pattern.search(content):
    raise SystemExit("unsafe_char_of_d7ff stub not found in Parser_FastString_CharBoundary.ml")

content = pattern.sub(replacement, content, count=1)

with open(path, 'w') as f:
    f.write(content)
PYEOF

echo "  Parser_FastString_CharBoundary.ml patched."
