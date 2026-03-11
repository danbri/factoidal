#!/bin/bash
# Issue #62: Forward-reference wiring for mutual recursion in SPARQL11_Algebra.ml
# https://github.com/danbri/factoidal/issues/62
#
# F* assume vals for eval_expr_ebv, eval_expr_fwd, eval_exists_fwd,
# eval_property_path_fwd, and eval_subselect_fwd are extracted as failwith stubs.
# This script replaces them with mutable-ref dispatch and wires the refs to the
# real implementations after they are defined.

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

FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE (forward ref wiring)..."

# --- Patch 1: Replace eval_expr_ebv stub with mutable ref declarations ---
if ! grep -q 'eval_expr_ebv_ref' "$FILE"; then
  sed -i 's/^let eval_expr_ebv (uu___ : expr)/let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =\n  ref (fun _ _ -> failwith "eval_expr_ebv not yet wired")\nlet eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =\n  ref (fun _ _ -> failwith "eval_expr_fwd not yet wired")\nlet eval_expr_ebv (e : expr)/' "$FILE"

  sed -i 's/  (uu___1 : RDF_Graph_Executable.solution_mapping) : Prims.bool=$/  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=/' "$FILE"

  sed -i 's/  failwith "Not yet implemented: SPARQL11.Algebra.eval_expr_ebv"/  !eval_expr_ebv_ref e mu/' "$FILE"

  sed -i 's/^let eval_expr_fwd (uu___ : expr)/let eval_expr_fwd (e : expr)/' "$FILE"
fi

# --- Patch 2: Fix eval_expr_fwd parameter + body, add forward ref declarations,
#     replace eval_exists_fwd/eval_subselect_fwd/eval_property_path_fwd stubs,
#     wire refs after definitions ---
if ! grep -q 'eval_exists_fwd_ref' "$FILE"; then
  python3 -c "
import re
with open('$FILE', 'r') as f:
    content = f.read()

# Fix eval_expr_fwd stub
content = content.replace(
    '  (uu___1 : RDF_Graph_Executable.solution_mapping) : eval_result=\n  failwith \"Not yet implemented: SPARQL11.Algebra.eval_expr_fwd\"',
    '  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=\n  !eval_expr_fwd_ref e mu'
)

# Add forward ref declarations for eval_exists_fwd, eval_property_path_fwd, eval_subselect_fwd
content = content.replace(
    '''let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =
  ref (fun _ _ -> failwith \"eval_expr_ebv not yet wired\")
let eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =
  ref (fun _ _ -> failwith \"eval_expr_fwd not yet wired\")''',
    '''let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =
  ref (fun _ _ -> failwith \"eval_expr_ebv not yet wired\")
let eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =
  ref (fun _ _ -> failwith \"eval_expr_fwd not yet wired\")
let eval_exists_fwd_ref : (group_graph_pattern -> RDF_Graph_Executable.solution_mapping -> RDF_Graph_Executable.rdf_graph -> RDF_Graph_Executable.rdf_dataset -> Prims.bool) ref =
  ref (fun _ _ _ _ -> false)
let eval_property_path_fwd_ref : (property_path -> RDF_Graph_Executable.rdf_graph -> (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list) ref =
  ref (fun _ _ -> [])
let eval_subselect_fwd_ref : (query -> RDF_Graph_Executable.rdf_graph -> RDF_Graph_Executable.rdf_dataset -> solution_sequence) ref =
  ref (fun _ _ _ -> [])'''
)

# Replace eval_exists_fwd failwith body with forward ref dispatch
content = content.replace(
    '''  failwith \"Not yet implemented: SPARQL11.Algebra.eval_exists_fwd\"''',
    '''  !eval_exists_fwd_ref uu___ uu___1 uu___2 uu___3'''
)

# Replace eval_subselect_fwd failwith body with forward ref dispatch
content = content.replace(
    '''  failwith \"Not yet implemented: SPARQL11.Algebra.eval_subselect_fwd\"''',
    '''  !eval_subselect_fwd_ref uu___ uu___1 uu___2'''
)

# Replace eval_property_path_fwd failwith body with forward ref dispatch
content = content.replace(
    '''  failwith \"Not yet implemented: SPARQL11.Algebra.eval_property_path_fwd\"''',
    '''  !eval_property_path_fwd_ref uu___ uu___1'''
)

# Wire eval_expr_ebv and eval_expr_fwd after eval_expr definition (before 'type group')
content = content.replace(
    'type group = {',
    '''(* Wire up the forward-declared eval_expr_ebv/fwd to the real implementations *)
let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)

type group = {'''
)

# Wire eval_exists_fwd_ref after eval_exists is defined
content = content.replace(
    'let filter_solutions (e : expr) (omega : solution_sequence) :',
    '''(* Wire up eval_exists_fwd to the real eval_exists *)
let () = eval_exists_fwd_ref := eval_exists

let filter_solutions (e : expr) (omega : solution_sequence) :'''
)

# Wire eval_property_path_fwd_ref after eval_property_path is defined
content = content.replace(
    'type numeric_precision =',
    '''(* Wire up eval_property_path_fwd to the real eval_property_path *)
let () = eval_property_path_fwd_ref := eval_property_path

type numeric_precision ='''
)

# Wire eval_subselect_fwd_ref after eval_select_query is defined
content = content.replace(
    'let is_not_literal',
    '''(* Wire up eval_subselect_fwd to the real eval_select_query *)
let () = eval_subselect_fwd_ref := eval_select_query

let is_not_literal'''
)

with open('$FILE', 'w') as f:
    f.write(content)
"
fi

echo "  Forward ref wiring patches applied."
