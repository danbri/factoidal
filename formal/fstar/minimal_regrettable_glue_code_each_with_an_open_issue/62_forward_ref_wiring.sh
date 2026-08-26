#!/bin/bash
# Issue #62: Forward-reference wiring for mutual recursion in SPARQL11_Algebra.ml
# https://github.com/danbri/factoidal/issues/62
#
# PARTIALLY RETIRED (g4-filter-devacuation, 2026-08-09): eval_expr_ebv and
# eval_expr_fwd are no longer assume vals -- SPARQL11.Algebra.fst now defines
# them as concrete `irreducible let`s directly after the (relocated,
# self-contained) eval_expr_with_base mutual block, so F* extracts them as
# real OCaml functions with no failwith stub to patch.
#
# FURTHER RETIRED (g4-exists-cycle-pilot, 2026-08-09): eval_exists_fwd is
# also no longer an assume val. eval_pattern_store, substitute_existentials
# (+_list/_opt), and eval_exists were merged into one `let rec ... and ...`
# clique in SPARQL11.Algebra.fst (termination via pattern_size/expr_size +
# a lexicographic phase tiebreak -- see the metric/lemma and merge commits),
# so eval_exists is now a real recursive OCaml function with no failwith
# stub and no ref/wiring needed. This script's scope was 2 symbols.
#
# FURTHER RETIRED (G4-subselect-fold, 2026-08-10): eval_subselect_fwd is
# ALSO no longer an assume val. eval_select_query joined the SAME clique
# (eval_pattern_store/eval_exists/substitute_existentials/eval_select_query,
# terminating via the query_size extension of pattern_size/expr_size --
# GP_SubSelect q now sizes as `1 + query_size q` instead of a flat `1`,
# and lemma_lateral_substitute_preserves_size covers the LATERAL call
# site), so GP_SubSelect / GP_Lateral in eval_pattern_store call
# eval_select_query directly and it extracts as a real, mutually-recursive
# OCaml function with no failwith stub and no ref/wiring needed either.
# This script's scope is now the remaining 1 symbol only:
# eval_property_path_fwd (Part 13's property-path evaluator genuinely
# lives outside this mutual group).
#
# The F* assume val for eval_property_path_fwd is extracted as a failwith
# stub. This script replaces it with mutable-ref dispatch and wires the
# ref to the real implementation after it is defined. `path_result_fwd`
# is a plain `type` alias (not an assume val) so F* extracts it as real
# OCaml code already -- no patching needed for it.

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

# Marker-idempotence (2026-08-26). ocaml-patches.sh runs over the WHOLE
# output directory, and an incremental extract leaves untouched modules
# already patched. This script's own product is the
# `eval_property_path_fwd_ref` declaration; if it is already there, the
# failwith stub is correctly absent and there is nothing to do. Without
# this guard the stub search below exits 1, which ocaml-patches.sh now
# treats as fatal -- so an incremental extract aborted the build.
if 'eval_property_path_fwd_ref' in content:
    print("  Already patched (eval_property_path_fwd_ref present); skipping.")
    sys.exit(0)

# 2026-07-06 follow-up (same class of hazard fixed for issue #261 in
# experimental_ocaml_glue/cottas_ondisk_runtime.sh, and for #57 in
# 57_service_client_bind.sh): the ongoing RDF.Graph.Executable ->
# RDF.Term/RDF.Triple/RDF.Graph split means F* extraction's module
# qualifier for rdf_graph is a MOVING TARGET. Anchor ONLY on the stable,
# F*-chosen text that never varies: `let eval_property_path_fwd` through
# its OWN failwith message, matched non-greedily with DOTALL so internal
# whitespace/newlines are irrelevant, and look up the LIVE qualifier for
# rdf_graph from inside the matched span rather than assuming it.
whole_block_re = re.compile(
    r'let eval_property_path_fwd.*?failwith "Not yet implemented: '
    r'SPARQL11\.Algebra\.eval_property_path_fwd"',
    re.DOTALL
)
m = whole_block_re.search(content)
if m is None:
    sys.stderr.write(
        "  ERROR: patch 62 could not find the F*-extracted failwith stub "
        f"for eval_property_path_fwd in {path}.\n"
        "         Has the stub's own failwith message text changed, or "
        "has the function been renamed/reordered? Inspect "
        "eval_property_path_fwd directly and update the anchor above -- "
        "do NOT let this fall through silently, the wiring-line insert "
        "below assumes the *_ref declaration this substitution produces.\n"
    )
    sys.exit(1)
stub_text = m.group(0)

QUAL = r'[A-Za-z_][A-Za-z0-9_.]*'

def find_qualifier(type_name, label):
    qm = re.search(r'(' + QUAL + r')\.' + re.escape(type_name), stub_text)
    if qm is None:
        sys.stderr.write(
            f"  ERROR: patch 62 could not find a qualifier for `{type_name}` "
            f"({label}) inside the matched stub block.\n"
            "         Inspect the stub text directly:\n"
            f"{stub_text}\n"
        )
        sys.exit(1)
    return qm.group(1)

q_graph = find_qualifier("rdf_graph", "eval_property_path_fwd g param")

# #65 Step 2c (2026-05-10): the eval_*_fwd assume vals take
# `(base : option wf_iri)` as their first parameter (where applicable).
# eval_expr_ebv_ref/eval_expr_fwd_ref RETIRED (g4-filter-devacuation,
# 2026-08-09), eval_exists_fwd_ref RETIRED (g4-exists-cycle-pilot,
# 2026-08-09), eval_subselect_fwd_ref RETIRED (G4-subselect-fold,
# 2026-08-10) -- see the header comment for each story. Only
# eval_property_path_fwd still needs ref/wiring.
replacement_block = f'''let eval_property_path_fwd_ref :
  (property_path ->
    {q_graph}.rdf_graph -> path_result_fwd) Stdlib.ref=
  Stdlib.ref (fun _ _ -> [])
let eval_property_path_fwd (p : property_path)
  (g : {q_graph}.rdf_graph) : path_result_fwd=
  !eval_property_path_fwd_ref p g'''

content = whole_block_re.sub(lambda _m: replacement_block, content, count=1)

if 'let () = eval_property_path_fwd_ref := eval_property_path' not in content:
    content = content.replace(
        'type numeric_precision =',
        'let () = eval_property_path_fwd_ref := eval_property_path\n'
        'type numeric_precision =',
        1
    )

# eval_exists_fwd_ref wiring block RETIRED (g4-exists-cycle-pilot,
# 2026-08-09) and eval_subselect_fwd_ref wiring block RETIRED
# (G4-subselect-fold, 2026-08-10), both along with their ref/stub above --
# neither needs post-hoc wiring, each is defined directly in the
# eval_pattern_store/eval_select_query clique and called there like any
# other OCaml function.

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
PYEOF

echo "  Forward ref wiring patches applied."
