#!/bin/bash
# Post-extraction patches for SPARQL11_Algebra.ml
# These fix assume-val stubs that F* extraction generates as failwith placeholders.
#
# Applied automatically by build-ocaml.sh after F* extraction.

set -euo pipefail

FILE="$1"

if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE..."

# 1. Replace eval_expr_ebv stub with mutable ref declarations + dispatch
sed -i 's/^let eval_expr_ebv (uu___ : expr)/let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =\n  ref (fun _ _ -> failwith "eval_expr_ebv not yet wired")\nlet eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =\n  ref (fun _ _ -> failwith "eval_expr_fwd not yet wired")\nlet eval_exists_fwd_ref : (group_graph_pattern -> RDF_Graph_Executable.solution_mapping -> RDF_Graph_Executable.rdf_graph -> Prims.bool) ref =\n  ref (fun _ _ _ -> failwith "eval_exists_fwd not yet wired")\nlet eval_expr_ebv (e : expr)/' "$FILE"

sed -i 's/  (uu___1 : RDF_Graph_Executable.solution_mapping) : Prims.bool=$/  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=/' "$FILE"

sed -i 's/  failwith "Not yet implemented: SPARQL11.Algebra.eval_expr_ebv"/  !eval_expr_ebv_ref e mu/' "$FILE"

sed -i 's/^let eval_expr_fwd (uu___ : expr)/let eval_expr_fwd (e : expr)/' "$FILE"

# 2. Fix remaining stubs and add wiring via Python
PATCH_FILE="$FILE" python3 <<'PYEOF'
import os

filepath = os.environ['PATCH_FILE']

with open(filepath, 'r') as f:
    content = f.read()

# Fix eval_expr_fwd stub
content = content.replace(
    '  (uu___1 : RDF_Graph_Executable.solution_mapping) : eval_result=\n  failwith "Not yet implemented: SPARQL11.Algebra.eval_expr_fwd"',
    '  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=\n  !eval_expr_fwd_ref e mu'
)

# Fix eval_exists_fwd stub
content = content.replace(
    'let eval_exists_fwd (uu___ : group_graph_pattern)\n  (uu___1 : RDF_Graph_Executable.solution_mapping)\n  (uu___2 : RDF_Graph_Executable.rdf_graph) : Prims.bool=\n  failwith "Not yet implemented: SPARQL11.Algebra.eval_exists_fwd"',
    'let eval_exists_fwd (p : group_graph_pattern)\n  (mu : RDF_Graph_Executable.solution_mapping)\n  (g : RDF_Graph_Executable.rdf_graph) : Prims.bool=\n  !eval_exists_fwd_ref p mu g'
)

# Replace regex_match stub with OCaml Str implementation
content = content.replace(
    'let regex_match (uu___ : Prims.string) (uu___1 : Prims.string)\n  (uu___2 : Prims.string FStar_Pervasives_Native.option) : Prims.bool=\n  failwith "Not yet implemented: SPARQL11.Algebra.regex_match"',
    "let regex_match (text : Prims.string) (pattern : Prims.string)\n  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=\n  try\n    let case_insensitive = match flags with\n      | FStar_Pervasives_Native.Some f -> String.contains f 'i'\n      | FStar_Pervasives_Native.None -> false in\n    let re = if case_insensitive\n      then Str.regexp_case_fold pattern\n      else Str.regexp pattern in\n    (try let _ = Str.search_forward re text 0 in true\n     with Not_found -> false)\n  with _ -> false"
)

# Add wiring after eval_expr definition (before 'type group')
content = content.replace(
    'type group = {',
    '(* Wire up the forward-declared eval_expr_ebv/fwd/exists to the real implementations *)\nlet () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))\nlet () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)\n\ntype group = {'
)

# Add eval_exists_fwd wiring after eval_exists is defined
content = content.replace(
    'let eval_not_exists',
    'let () = eval_exists_fwd_ref := (fun p mu g -> eval_exists p mu g)\nlet eval_not_exists'
)

# Replace hash function stubs with real implementations using digestif
for (name, mod_name) in [('md5', 'MD5'), ('sha1', 'SHA1'), ('sha256', 'SHA256'), ('sha384', 'SHA384'), ('sha512', 'SHA512')]:
    stub = f'let hash_{name} (uu___ : Prims.string) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Algebra.hash_{name}"'
    impl = f'let hash_{name} (s : Prims.string) : Prims.string=\n  Digestif.{mod_name}.digest_string s |> Digestif.{mod_name}.to_hex'
    content = content.replace(stub, impl)

with open(filepath, 'w') as f:
    f.write(content)
PYEOF

echo "  Patches applied successfully."
