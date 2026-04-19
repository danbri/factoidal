#!/bin/bash
# Post-extraction patch: Blank-node-to-variable rewriting for entailment regimes
# Issue: https://github.com/danbri/factoidal/issues/53
#
# KNOWN VIOLATION: This logic belongs in F* (tracked in issue #53).
#
# Under RDF/RDFS/D entailment, blank nodes in query patterns act as
# existential variables — they match any term, not just blank nodes
# with the same label. This patch rewrites PS_BNode/PT_BNode to fresh
# variables before query evaluation.

set -euo pipefail

OUTDIR="$1"

FILE="$OUTDIR/w3c_runner.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Skipping 53_blank_node_variable_rewriting.sh: $FILE not found" >&2
  exit 0
fi

echo "  Applying 53_blank_node_variable_rewriting.sh to $FILE..."

if ! grep -q 'blank nodes in query patterns act as' "$FILE"; then
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

content = content.replace(
    '''  (* Execute query against extracted evaluator *)
  let actual_results = eval_select_query query graph dataset in''',
    '''  (* Under RDF/RDFS entailment, blank nodes in query patterns act as
     existential variables — they match any term, not just blank nodes
     with the same label. Rewrite PS_BNode/PT_BNode to fresh variables. *)
  let query = match tc.test_type_detail with
    | "RDFS" | "RDF" | "D" | "OWL-RL" ->
      let open SPARQL11_Algebra in
      let rewrite_pt = function
        | PT_BNode b -> PT_Var ("_bnode_" ^ b)
        | pt -> pt in
      let rewrite_ps = function
        | PS_BNode b -> PS_Var ("_bnode_" ^ b)
        | ps -> ps in
      let rewrite_tp tp = {
        tp_s = rewrite_ps tp.tp_s;
        tp_p = rewrite_pt tp.tp_p;
        tp_o = rewrite_pt tp.tp_o;
      } in
      let rec rewrite_ggp = function
        | GP_BGP bgp -> GP_BGP (List.map rewrite_tp bgp)
        | GP_Join (p1, p2) -> GP_Join (rewrite_ggp p1, rewrite_ggp p2)
        | GP_LeftJoin (p1, p2, e) -> GP_LeftJoin (rewrite_ggp p1, rewrite_ggp p2, e)
        | GP_Filter (e, p) -> GP_Filter (e, rewrite_ggp p)
        | GP_Union (p1, p2) -> GP_Union (rewrite_ggp p1, rewrite_ggp p2)
        | GP_Graph (gt, p) -> GP_Graph (rewrite_pt gt, rewrite_ggp p)
        | GP_Minus (p1, p2) -> GP_Minus (rewrite_ggp p1, rewrite_ggp p2)
        | GP_Bind (e, v, p) -> GP_Bind (e, v, rewrite_ggp p)
        | GP_SubSelect q -> GP_SubSelect (rewrite_query q)
        | GP_PropertyPath (s, pp, o) -> GP_PropertyPath (rewrite_ps s, pp, rewrite_pt o)
        | p -> p  (* GP_Values, GP_Service, GP_Empty unchanged *)
      and rewrite_query q =
        { q with q_pattern = rewrite_ggp q.q_pattern }
      in
      rewrite_query query
    | _ -> query in

  (* Execute query against extracted evaluator *)
  let actual_results = eval_select_query query graph dataset in'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
fi

echo "  53_blank_node_variable_rewriting.sh applied."
