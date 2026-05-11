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

python3 - "$FILE" << 'PYEOF'
import re
import sys

path = sys.argv[1]
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

stub_block_re = re.compile(
    r'''let eval_expr_ebv\s*\n\s*\([^)]*\)\s*\n\s*\([^)]*\)\s+\([^)]*\)\s*:\s*\n?\s*Prims\.bool=\s*failwith "Not yet implemented: SPARQL11\.Algebra\.eval_expr_ebv"\n'''
    r'''let eval_expr_fwd\s*\n\s*\([^)]*\)\s*\n\s*\([^)]*\)\s+\([^)]*\)\s*:\s*\n?\s*eval_result=\s*failwith "Not yet implemented: SPARQL11\.Algebra\.eval_expr_fwd"\n'''
    r'''let eval_exists_fwd\s*\n\s*\([^)]*\)\s*\n\s*\([^)]*\)\s*\n\s*\([^)]*\)\s*\n\s*\([^)]*\)\s*\n\s*\([^)]*\)\s*:\s*Prims\.bool=\s*\n?\s*failwith "Not yet implemented: SPARQL11\.Algebra\.eval_exists_fwd"\n'''
    r'''let eval_subselect_fwd \([^)]*\)\n  \([^)]*\)\n  \([^)]*\) : solution_sequence=\n  failwith "Not yet implemented: SPARQL11\.Algebra\.eval_subselect_fwd"\n'''
    r'''type path_result_fwd =\n  \(RDF_Graph_Executable\.rdf_term \* RDF_Graph_Executable\.rdf_term\) Prims\.list\n'''
    r'''let eval_property_path_fwd \([^)]*\)\n  \([^)]*\) : path_result_fwd=\n  failwith "Not yet implemented: SPARQL11\.Algebra\.eval_property_path_fwd"''',
    re.MULTILINE
)

# #65 Step 2c (2026-05-10): the three eval_*_fwd assume vals now take
# `(base : option wf_iri)` as their first parameter. The ref types and
# realisations below are updated accordingly. eval_expr_ebv_ref dispatches
# to eval_expr_with_base directly so BASE flows through FILTER / OPTIONAL
# evaluation without consulting current_base_iri_ref.
replacement_block = '''let eval_expr_ebv_ref :
  (RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ->
    expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> failwith "eval_expr_ebv not yet wired")
let eval_expr_fwd_ref :
  (RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ->
    expr -> RDF_Graph_Executable.solution_mapping -> eval_result) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> failwith "eval_expr_fwd not yet wired")
let eval_exists_fwd_ref :
  (RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ->
    group_graph_pattern ->
    RDF_Graph_Executable.solution_mapping ->
    RDF_Graph_Executable.rdf_graph ->
    RDF_Graph_Executable.rdf_dataset -> Prims.bool) Stdlib.ref=
  Stdlib.ref (fun _ _ _ _ _ -> false)
let eval_subselect_fwd_ref :
  (query ->
    RDF_Graph_Executable.rdf_graph ->
    RDF_Graph_Executable.rdf_dataset -> solution_sequence) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> [])
let eval_expr_ebv
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  !eval_expr_ebv_ref base e mu
let eval_expr_fwd
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  !eval_expr_fwd_ref base e mu
let eval_exists_fwd
  (base : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option)
  (p : group_graph_pattern)
  (mu : RDF_Graph_Executable.solution_mapping)
  (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : Prims.bool=
  !eval_exists_fwd_ref base p mu g ds
let eval_subselect_fwd (q : query)
  (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : solution_sequence=
  !eval_subselect_fwd_ref q g ds
type path_result_fwd =
  (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list
let eval_property_path_fwd_ref :
  (property_path ->
    RDF_Graph_Executable.rdf_graph -> path_result_fwd) Stdlib.ref=
  Stdlib.ref (fun _ _ -> [])
let eval_property_path_fwd (p : property_path)
  (g : RDF_Graph_Executable.rdf_graph) : path_result_fwd=
  !eval_property_path_fwd_ref p g'''

content = stub_block_re.sub(replacement_block, content, count=1)

if 'let () = eval_expr_ebv_ref := (fun base e mu -> ebv (eval_expr_with_base base e mu))' not in content:
    content = content.replace(
        'type group = {',
        'let () = eval_expr_ebv_ref := (fun base e mu -> ebv (eval_expr_with_base base e mu))\n'
        'let () = eval_expr_fwd_ref := (fun base e mu -> eval_expr_with_base base e mu)\n'
        'type group = {',
        1
    )

if 'let () = eval_subselect_fwd_ref := eval_select_query' not in content:
    # eval_select_query goes near the end of the file, append outside any def.
    content += '\nlet () = eval_subselect_fwd_ref := eval_select_query\n'

if 'let () = eval_property_path_fwd_ref := eval_property_path' not in content:
    content = content.replace(
        'type numeric_precision =',
        'let () = eval_property_path_fwd_ref := eval_property_path\n'
        'type numeric_precision =',
        1
    )

if 'let () = eval_exists_fwd_ref := eval_exists' not in content:
    # #65 Step 2c (2026-05-10): eval_exists's def header changed shape after
    # threading `(base : option wf_iri)` as the first parameter. The original
    # anchor 'let filter_solutions (e : expr) (omega ...)' no longer matches
    # the multi-line emission that F* now produces. Anchor on the new
    # filter_solutions head — the wiring goes immediately above it.
    content = content.replace(
        'let filter_solutions\n  (base : RDF_Graph_Executable.wf_iri',
        'let () = eval_exists_fwd_ref := eval_exists\n'
        'let filter_solutions\n  (base : RDF_Graph_Executable.wf_iri',
        1
    )

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
PYEOF

echo "  Forward ref wiring patches applied."
