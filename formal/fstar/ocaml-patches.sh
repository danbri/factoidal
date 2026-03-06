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

# 1. Replace eval_expr_ebv stub with mutable ref dispatch
sed -i 's/^let eval_expr_ebv (uu___ : expr)/let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =\n  ref (fun _ _ -> failwith "eval_expr_ebv not yet wired")\nlet eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =\n  ref (fun _ _ -> failwith "eval_expr_fwd not yet wired")\nlet eval_expr_ebv (e : expr)/' "$FILE"

sed -i 's/  (uu___1 : RDF_Graph_Executable.solution_mapping) : Prims.bool=$/  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=/' "$FILE"

sed -i 's/  failwith "Not yet implemented: SPARQL11.Algebra.eval_expr_ebv"/  !eval_expr_ebv_ref e mu/' "$FILE"

sed -i 's/^let eval_expr_fwd (uu___ : expr)/let eval_expr_fwd (e : expr)/' "$FILE"

# Fix the eval_expr_fwd parameter name and body
python3 -c "
import re
with open('$FILE', 'r') as f:
    content = f.read()

# Fix eval_expr_fwd stub
content = content.replace(
    '  (uu___1 : RDF_Graph_Executable.solution_mapping) : eval_result=\n  failwith \"Not yet implemented: SPARQL11.Algebra.eval_expr_fwd\"',
    '  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=\n  !eval_expr_fwd_ref e mu'
)

# 2. Replace regex_match stub with OCaml Str implementation
content = content.replace(
    '''let regex_match (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  failwith \"Not yet implemented: SPARQL11.Algebra.regex_match\"''',
    '''let regex_match (text : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let re = if case_insensitive
      then Str.regexp_case_fold pattern
      else Str.regexp pattern in
    (try let _ = Str.search_forward re text 0 in true
     with Not_found -> false)
  with _ -> false'''
)

# 3. Add wiring after eval_expr definition (before 'type group')
content = content.replace(
    'type group = {',
    '''(* Wire up the forward-declared eval_expr_ebv/fwd to the real implementations *)
let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)

type group = {'''
)

with open('$FILE', 'w') as f:
    f.write(content)
"

echo "  Patches applied successfully."
