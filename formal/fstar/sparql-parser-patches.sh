#!/bin/bash
# Post-extraction patches for SPARQL11_Parser.ml
set -euo pipefail

FILE="$1"
if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE..."

# FFI stubs (simple sed)
sed -i 's/  failwith "Not yet implemented: SPARQL11.Parser.char_at"/  Char.code (String.get uu___ (Z.to_int uu___1))/' "$FILE"
sed -i 's/failwith "Not yet implemented: SPARQL11.Parser.substring"/String.sub uu___ (Z.to_int uu___1) (Z.to_int uu___2)/' "$FILE"
sed -i 's/  failwith "Not yet implemented: SPARQL11.Parser.string_upper"/  String.uppercase_ascii uu___/' "$FILE"
sed -i 's/  failwith "Not yet implemented: SPARQL11.Parser.utf8_of_codepoint"/  Sparql_parser_stubs.utf8_of_codepoint_impl (Z.to_int uu___)/' "$FILE"
sed -i 's/  failwith "Not yet implemented: SPARQL11.Parser.process_iri_escapes"/  Sparql_parser_stubs.process_iri_escapes_impl uu___/' "$FILE"
sed -i 's/  failwith "Not yet implemented: SPARQL11.Parser.process_string_escapes"/  Sparql_parser_stubs.process_string_escapes_impl uu___/' "$FILE"

# Forward reference stubs (Python for multi-line replacements)
python3 - "$FILE" << 'PYEOF'
import sys

filepath = sys.argv[1]
with open(filepath, 'r') as f:
    content = f.read()

content = content.replace(
    'let parse_expr (uu___ : prefix_map) (uu___1 : token_stream) :\n  SPARQL11_Algebra.expr parse_result=\n  failwith "Not yet implemented: SPARQL11.Parser.parse_expr"',
    'let parse_expr_ref : (prefix_map -> token_stream -> SPARQL11_Algebra.expr parse_result) ref =\n  ref (fun _ _ -> failwith "parse_expr not yet wired")\nlet parse_expr (pm : prefix_map) (ts : token_stream) :\n  SPARQL11_Algebra.expr parse_result=\n  !parse_expr_ref pm ts'
)

content = content.replace(
    'let parse_group_graph_pattern (uu___ : prefix_map) (uu___1 : Prims.nat)\n  (uu___2 : token_stream) :\n  SPARQL11_Algebra.group_graph_pattern parse_result=\n  failwith "Not yet implemented: SPARQL11.Parser.parse_group_graph_pattern"',
    'let parse_group_graph_pattern_ref : (prefix_map -> Prims.nat -> token_stream -> SPARQL11_Algebra.group_graph_pattern parse_result) ref =\n  ref (fun _ _ _ -> failwith "parse_group_graph_pattern not yet wired")\nlet parse_group_graph_pattern (pm : prefix_map) (fuel : Prims.nat)\n  (ts : token_stream) :\n  SPARQL11_Algebra.group_graph_pattern parse_result=\n  !parse_group_graph_pattern_ref pm fuel ts'
)

content = content.replace(
    'let parse_select_query (uu___ : prefix_map) (uu___1 : Prims.nat)\n  (uu___2 : token_stream) : SPARQL11_Algebra.query parse_result=\n  failwith "Not yet implemented: SPARQL11.Parser.parse_select_query"',
    'let parse_select_query_ref : (prefix_map -> Prims.nat -> token_stream -> SPARQL11_Algebra.query parse_result) ref =\n  ref (fun _ _ _ -> failwith "parse_select_query not yet wired")\nlet parse_select_query (pm : prefix_map) (fuel : Prims.nat)\n  (ts : token_stream) : SPARQL11_Algebra.query parse_result=\n  !parse_select_query_ref pm fuel ts'
)

# Append wiring at end
content += '\n\n(* Wire forward references to their implementations *)\nlet () = parse_expr_ref := parse_expr_impl\nlet () = parse_group_graph_pattern_ref := parse_ggp_impl\nlet () = parse_select_query_ref := parse_query_impl\n'

with open(filepath, 'w') as f:
    f.write(content)
PYEOF

echo "  Done patching $FILE"
