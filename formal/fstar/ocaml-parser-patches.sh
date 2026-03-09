#!/bin/bash
# Post-extraction patches for SPARQL11_Parser.ml
# Wires assume-val stubs for character operations and utilities.
# Scanner functions (tokenize, scan_iri, scan_string, etc.) are now
# implemented in F* and extracted properly — no patches needed.
#
# Applied automatically by build-ocaml.sh after F* extraction.

set -euo pipefail

FILE="$1"

if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE..."

python3 -c "
import re
with open('$FILE', 'r') as f:
    content = f.read()

# 1. char_at — character access by position
content = content.replace(
    'let char_at (uu___ : Prims.string) (uu___1 : pos) : FStar_Char.char=\n  failwith \"Not yet implemented: SPARQL11.Parser.char_at\"',
    'let char_at (s : Prims.string) (p : pos) : FStar_Char.char=\n  if Z.lt p (Z.of_int (String.length s))\n  then Char.code s.[Z.to_int p]\n  else 0'
)

# 2. substring — string slicing
content = content.replace(
    'let substring (uu___ : Prims.string) (uu___1 : pos) (uu___2 : Prims.nat) :\n  Prims.string= failwith \"Not yet implemented: SPARQL11.Parser.substring\"',
    'let substring (s : Prims.string) (start : pos) (len : Prims.nat) :\n  Prims.string=\n  let st = (Z.to_int start) in\n  let ln = (Z.to_int len) in\n  let slen = (String.length s) in\n  if Stdlib.(st >= slen) then \"\"\n  else String.sub s st (Stdlib.min ln Stdlib.(slen - st))'
)

# 3. string_upper — uppercase conversion
content = content.replace(
    'let string_upper (uu___ : Prims.string) : Prims.string=\n  failwith \"Not yet implemented: SPARQL11.Parser.string_upper\"',
    'let string_upper (s : Prims.string) : Prims.string=\n  String.uppercase_ascii s'
)

# 4. token_eq — structural equality on tokens
content = content.replace(
    'let token_eq (uu___ : token) (uu___1 : token) : Prims.bool=\n  failwith \"Not yet implemented: SPARQL11.Parser.token_eq\"',
    'let token_eq (t1 : token) (t2 : token) : Prims.bool=\n  t1 = t2'
)

# 5. fresh_bnode_id — generate unique blank node IDs
content = content.replace(
    'let fresh_bnode_id (uu___ : unit) : Prims.string=\n  failwith \"Not yet implemented: SPARQL11.Parser.fresh_bnode_id\"',
    '''let _bnode_counter = ref 0
let fresh_bnode_id (uu___ : unit) : Prims.string=
  let id = Printf.sprintf \"_:sparql_b%d\" !_bnode_counter in
  incr _bnode_counter; id'''
)

# 6. parse_int_value — string to integer
content = content.replace(
    'let parse_int_value (uu___ : Prims.string) : Prims.int=\n  failwith \"Not yet implemented: SPARQL11.Parser.parse_int_value\"',
    'let parse_int_value (s : Prims.string) : Prims.int=\n  Z.of_string s'
)

# 7. parse_nat_value — string to natural number
content = content.replace(
    'let parse_nat_value (uu___ : Prims.string) : Prims.nat=\n  failwith \"Not yet implemented: SPARQL11.Parser.parse_nat_value\"',
    'let parse_nat_value (s : Prims.string) : Prims.nat=\n  Z.of_string s'
)

with open('$FILE', 'w') as f:
    f.write(content)
"

echo "  Parser patches applied successfully."
