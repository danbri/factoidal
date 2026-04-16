#!/bin/bash
# Post-extraction patch: Unicode boundary workarounds (surrogate validation)
# Issue: https://github.com/danbri/factoidal/issues/68
#
# Patches:
#   - Parser_NTriples.ml: 0xD7FF -> 0xD800 boundary fix
#   - Parser_Turtle.ml: 4 surrogate validation guards in string parsers

set -euo pipefail

OUTDIR="$1"

# ======================================================================
# Parser_NTriples.ml — fix U+D7FF boundary (F* char type limitation)
# ======================================================================
FILE="$OUTDIR/Parser_NTriples.ml"
if [[ -f "$FILE" ]]; then
  echo "  Applying 68_unicode_boundary_workarounds.sh to $FILE..."
  if grep -q '(cp < (Prims.of_int (0xD7FF)))' "$FILE"; then
    sed -i '' 's/(cp < (Prims.of_int (0xD7FF)))/(cp < (Prims.of_int (0xD800)))/g' "$FILE"
  fi
  echo "  Parser_NTriples.ml patched."
fi

# ======================================================================
# Parser_Turtle.ml — surrogate codepoint validation
# ======================================================================
FILE="$OUTDIR/Parser_Turtle.ml"
if [[ -f "$FILE" ]]; then
  echo "  Applying 68_unicode_boundary_workarounds.sh to $FILE..."
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

changed = False

# 1. parse_long_string_body, \u escape (4-digit, offset +6)
old1 = '''                                          + h3 in
                                      parse_long_string_body qch input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)'''
new1 = '''                                          + h3 in
                                      if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                      then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\u escape", pos)
                                      else
                                      parse_long_string_body qch input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)'''
if old1 in content:
    content = content.replace(old1, new1)
    changed = True

# 2. parse_long_string_body, \U escape (8-digit, offset +10)
old2 = '''                                            + h7 in
                                        parse_long_string_body qch input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int'''
new2 = '''                                            + h7 in
                                        if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                        then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\U escape", pos)
                                        else
                                        parse_long_string_body qch input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int'''
if old2 in content:
    content = content.replace(old2, new2)
    changed = True

# 3. parse_single_string_body, \u escape (4-digit, offset +6)
old3 = '''                                          + h3 in
                                      parse_single_string_body input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)'''
new3 = '''                                          + h3 in
                                      if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                      then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\u escape", pos)
                                      else
                                      parse_single_string_body input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)'''
if old3 in content:
    content = content.replace(old3, new3)
    changed = True

# 4. parse_single_string_body, \U escape (8-digit, offset +10)
old4 = '''                                            + h7 in
                                        parse_single_string_body input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int'''
new4 = '''                                            + h7 in
                                        if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                        then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\U escape", pos)
                                        else
                                        parse_single_string_body input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int'''
if old4 in content:
    content = content.replace(old4, new4)
    changed = True

if changed:
    with open(sys.argv[1], 'w') as f:
        f.write(content)
PYEOF
  echo "  Parser_Turtle.ml patched."
fi
