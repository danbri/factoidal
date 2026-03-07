#!/bin/bash
# Post-extraction patches for SPARQL_Parser.ml
# These fix assume-val stubs and integer parsing.
#
# Applied after F* extraction of SPARQL.Parser.fst.

set -euo pipefail

FILE="$1"

if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE..."

# 1. Replace parse_nat_digits stub with concrete implementation
PATCH_FILE="$FILE" python3 <<'PYEOF'
import os

filepath = os.environ['PATCH_FILE']

with open(filepath, 'r') as f:
    content = f.read()

# Replace parse_nat_digits stub
content = content.replace(
    'let parse_nat_digits (uu___ : pstate) :\n  (Prims.nat * pstate) FStar_Pervasives_Native.option=\n  failwith "Not yet implemented: SPARQL.Parser.parse_nat_digits"',
    '''let parse_nat_digits (ps : pstate) :
  (Prims.nat * pstate) FStar_Pervasives_Native.option=
  let rec go ps acc any =
    match ps_peek ps with
    | FStar_Pervasives_Native.Some c when FStar_Char.int_of_char c >= 0x30 && FStar_Char.int_of_char c <= 0x39 ->
      go (ps_advance ps Prims.int_one) (acc * (Prims.of_int (10)) + Prims.of_int (FStar_Char.int_of_char c - 0x30)) true
    | _ -> if any then FStar_Pervasives_Native.Some (acc, ps) else FStar_Pervasives_Native.None
  in
  go ps Prims.int_zero false'''
)

# Fix integer parsing: replace E_NumericLit 0 placeholder with actual parsing
content = content.replace(
    '((SPARQL11_Algebra.E_NumericLit Prims.int_zero), ps_after_int)',
    '''(let s = FStar_String.sub ps.inp start (ps_after_int.pos - start) in
              let n = try Prims.of_int (int_of_string s) with _ -> Prims.int_zero in
              (SPARQL11_Algebra.E_NumericLit n, ps_after_int))'''
)

with open(filepath, 'w') as f:
    f.write(content)
PYEOF

echo "  Parser patches applied successfully."
