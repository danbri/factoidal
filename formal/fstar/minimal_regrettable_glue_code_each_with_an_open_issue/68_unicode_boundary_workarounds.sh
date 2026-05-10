#!/bin/bash
# Post-extraction patch: Unicode boundary workarounds (NTriples only)
# Issue: https://github.com/danbri/factoidal/issues/68
#
# Patches:
#   - Parser_NTriples.ml: 0xD7FF -> 0xD800 boundary fix
#
# History (2026-05-10): the Turtle half of this patch was removed. The
# F* `Parser.Turtle.fst` source already contains the four
# `valid_codepoint` surrogate-validation guards (lines 1020, 1038, 1099,
# 1117), so extraction produces them in `Parser_Turtle.ml` directly —
# the regex-rewrite in this patch was a no-op (verified by md5sum
# before/after). Removed to shrink the rule-#11(c) footprint.
#
# What remains: the NTriples `0xD7FF` → `0xD800` sed. This is a
# workaround for an off-by-one in `FStar.Char.char_code`: the stdlib
# type strictly excludes `U+D7FF` (`type char_code = n: U32.t{U32.v n
# < 0xd7ff \/ ...}`), so `Parser.NTriples.fst`'s `valid_codepoint` /
# `safe_char_of_int` must use `< 0xD7FF` to satisfy F*'s type system.
# At runtime OCaml's `Char.chr 0xD7FF` succeeds, and per the Unicode
# spec U+D7FF IS a valid scalar (the surrogate gap is 0xD800-0xDFFF).
# This sed corrects the OCaml-side check to match Unicode while
# leaving the F* type-checker happy.
#
# Full retirement of this patch is gated on either (a) an upstream F*
# stdlib fix to `char_code` (probably loosening the strict `<` to `<=`
# at 0xd7ff, plus the symmetric inclusive-`<=` at 0x10FFFF), or (b)
# defining a project-local codepoint type that side-steps `char_code`.

set -euo pipefail

OUTDIR="$1"

# ======================================================================
# Parser_NTriples.ml — fix U+D7FF boundary (F* char type limitation)
# ======================================================================
FILE="$OUTDIR/Parser_NTriples.ml"
if [[ -f "$FILE" ]]; then
  echo "  Applying 68_unicode_boundary_workarounds.sh to $FILE..."
  if grep -q '(cp < (Prims.of_int (0xD7FF)))' "$FILE"; then
    # macOS sed -i requires '' argument; Linux sed -i doesn't.
    if [[ "$(uname)" == "Darwin" ]]; then
      sed -i '' 's/(cp < (Prims.of_int (0xD7FF)))/(cp < (Prims.of_int (0xD800)))/g' "$FILE"
    else
      sed -i 's/(cp < (Prims.of_int (0xD7FF)))/(cp < (Prims.of_int (0xD800)))/g' "$FILE"
    fi
  fi
  echo "  Parser_NTriples.ml patched."
fi
