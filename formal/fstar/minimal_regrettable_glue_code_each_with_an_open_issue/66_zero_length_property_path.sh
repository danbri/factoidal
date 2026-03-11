#!/bin/bash
# Issue #66: Zero-length property path matching on empty graphs
# https://github.com/danbri/factoidal/issues/66
#
# SPARQL semantics: ZeroOrMore/ZeroOrOne paths must include zero-length
# matches for constant IRIs/BNodes from the query pattern, even when
# the graph is empty. eval_property_path only generates reflexive pairs
# for nodes already in the graph, so we augment GP_PropertyPath handling.
#
# Files patched: SPARQL11_Algebra.ml
# Category: SPARQL semantics fix (should be in F*)

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Skipping 66_zero_length_property_path (SPARQL11_Algebra.ml not found)"
  exit 0
fi

# Check if already applied
if grep -q 'SPARQL semantics: ZeroOrMore/ZeroOrOne paths must include zero-length' "$FILE"; then
  echo "  66_zero_length_property_path: already applied"
  exit 0
fi

echo "  Applying 66_zero_length_property_path..."

python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

content = content.replace(
    '''  | GP_PropertyPath (ps, pp, pt) ->
      let pairs = eval_property_path_fwd pp g in
      path_result_to_solutions ps pt pairs''',
    '''  | GP_PropertyPath (ps, pp, pt) ->
      let pairs = eval_property_path_fwd pp g in
      (* SPARQL semantics: ZeroOrMore/ZeroOrOne paths must include zero-length
         matches for any constant IRI/BNode in the pattern, even on empty graphs.
         eval_property_path only generates reflexive pairs for nodes in the graph,
         so we add reflexive pairs for constants from the query pattern here,
         but only if they are not already present (to avoid duplicates). *)
      let pairs = match pp with
        | PP_ZeroOrMore _ | PP_ZeroOrOne _ ->
            let constant_terms =
              (match ps with
               | PS_IRI i -> [RDF_Graph_Executable.T_IRI i]
               | PS_BNode b -> [RDF_Graph_Executable.T_BNode b]
               | PS_Var _ -> [])
              @
              (match pt with
               | PT_IRI i -> [RDF_Graph_Executable.T_IRI i]
               | PT_BNode b -> [RDF_Graph_Executable.T_BNode b]
               | PT_Literal l -> [RDF_Graph_Executable.T_Literal l]
               | PT_Var _ -> []) in
            let has_reflexive t =
              FStar_List_Tot_Base.existsb
                (fun pair -> match pair with (s, o) ->
                   RDF_Graph_Executable.rdf_term_eq s t &&
                   RDF_Graph_Executable.rdf_term_eq o t) pairs in
            let new_terms = FStar_List_Tot_Base.filter
              (fun t -> not (has_reflexive t)) constant_terms in
            let reflexive = FStar_List_Tot_Base.map (fun n -> (n, n)) new_terms in
            FStar_List_Tot_Base.op_At pairs reflexive
        | _ -> pairs in
      path_result_to_solutions ps pt pairs'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF

echo "  66_zero_length_property_path: applied"
