#!/bin/bash
# parser-patches.sh — Wire assume-val stubs for SPARQL11_Parser.ml
# Replaces failwith stubs with calls to sparql_parser_bridge.ml

set -euo pipefail

FILE="${1:-ocaml-output/SPARQL11_Parser.ml}"

if [ ! -f "$FILE" ]; then
  echo "File not found: $FILE"
  exit 1
fi

echo "Patching $FILE..."

# Simple stubs
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.char_at"|Sparql_parser_bridge.char_at|' "$FILE"
sed -i 's|Prims.string= failwith "Not yet implemented: SPARQL11.Parser.substring"|Sparql_parser_bridge.substring|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.string_upper"|Sparql_parser_bridge.string_upper|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.token_eq"|Sparql_parser_bridge.token_eq|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.split_pname"|Sparql_parser_bridge.split_pname|' "$FILE"

# Lexer scanners
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_iri"|Sparql_parser_bridge.scan_iri|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_string"|Sparql_parser_bridge.scan_string|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_pname_or_keyword"|Sparql_parser_bridge.scan_pname_or_keyword|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_number"|Sparql_parser_bridge.scan_number|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_bnode_label"|Sparql_parser_bridge.scan_bnode_label|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_var_name"|Sparql_parser_bridge.scan_var_name|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.scan_langtag"|Sparql_parser_bridge.scan_langtag|' "$FILE"

# Tokenize
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.tokenize"|Sparql_parser_bridge.tokenize|' "$FILE"

# Parser (delegated to OCaml parser for now)
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.parse_expr"|fun _pm _ts -> ParseErr "use OCaml parser"|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.parse_group_graph_pattern"|fun _pm _fuel _ts -> ParseErr "use OCaml parser"|' "$FILE"
sed -i 's|failwith "Not yet implemented: SPARQL11.Parser.parse_select_query"|fun _pm _fuel _ts -> ParseErr "use OCaml parser"|' "$FILE"

echo "Done. Patched stubs in $FILE"

# Verify no remaining failwith stubs
remaining=$(grep -c 'Not yet implemented: SPARQL11.Parser' "$FILE" || true)
if [ "$remaining" -gt 0 ]; then
  echo "WARNING: $remaining unpatched stubs remain:"
  grep 'Not yet implemented: SPARQL11.Parser' "$FILE"
  exit 1
else
  echo "All stubs patched successfully."
fi
