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
# stub and no ref/wiring needed. This script's scope is now the remaining
# 2 symbols only.
#
# F* assume vals for eval_property_path_fwd and eval_subselect_fwd are
# extracted as failwith stubs. This script replaces them with mutable-ref
# dispatch and wires the refs to the real implementations after they are
# defined.

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

# 2026-07-06 follow-up (same class of hazard fixed for issue #261 in
# experimental_ocaml_glue/cottas_ondisk_runtime.sh, and for #57 in
# 57_service_client_bind.sh): the ongoing RDF.Graph.Executable ->
# RDF.Term/RDF.Triple/RDF.Graph split means F* extraction's module
# qualifier for wf_iri/solution_mapping/rdf_graph/rdf_dataset/rdf_term
# is a MOVING TARGET -- and not even the SAME qualifier for every type
# in one extraction: a single fresh extraction of this file used
# `RDF_Term.wf_iri`, `RDF_Graph_Executable.solution_mapping`,
# `RDF_Graph.rdf_graph`, `RDF_Graph.rdf_dataset`, and `RDF_Term.rdf_term`
# all at once. This script used to hardcode `RDF_Graph_Executable` for
# every one of those five slots; when a fresh extraction split them
# across three different modules, the giant `stub_block_re` (needing
# ALL FIVE function stubs to match as one combined pattern) missed
# entirely -- .sub() silently returns the input unchanged on a
# non-match -- so eval_expr_ebv/eval_expr_fwd/eval_exists_fwd/
# eval_subselect_fwd/eval_property_path_fwd were all left as
# `failwith "Not yet implemented"`, and the wiring-line insertions
# below (guarded only by "not already present", not by "declarations
# actually landed") then referenced never-declared *_ref names,
# producing a hard `Unbound value` compile error days later with no
# hint of the real cause.
#
# Fixed two ways:
#  1. The MATCH no longer assumes a specific line-wrapping shape for
#     the 5 stub signatures (which parameter sits on which line also
#     drifts between extractions independent of the qualifier issue --
#     observed directly: eval_expr_ebv's single wf_iri parameter sits
#     on the SAME line as `let eval_expr_ebv` in one extraction and on
#     its own line in another). Anchor ONLY on the stable, F*-chosen
#     text that never varies: `let eval_expr_ebv` through the LAST
#     stub's own failwith message, matched non-greedily with DOTALL so
#     internal whitespace/newlines are irrelevant.
#  2. Each type's LIVE module qualifier
#     (wf_iri/solution_mapping/rdf_graph/rdf_dataset/rdf_term) is
#     looked up by a separate, targeted search over the matched span
#     rather than assumed positionally, so this script never needs to
#     know or guess the qualifier again.
whole_block_re = re.compile(
    r'let eval_subselect_fwd.*?failwith "Not yet implemented: '
    r'SPARQL11\.Algebra\.eval_property_path_fwd"',
    re.DOTALL
)
m = whole_block_re.search(content)
if m is None:
    sys.stderr.write(
        "  ERROR: patch 62 could not find the F*-extracted failwith stub "
        f"block (eval_subselect_fwd .. eval_property_path_fwd) in {path}.\n"
        "         Has a stub's own failwith message text changed, or has "
        "a function been renamed/reordered? Inspect the "
        "eval_subselect_fwd/eval_property_path_fwd stubs directly and "
        "update the anchors above -- do NOT let this fall through "
        "silently, the wiring-line inserts below assume the *_ref "
        "declarations this substitution produces.\n"
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

q_graph = find_qualifier("rdf_graph", "eval_subselect_fwd g param")
q_ds = find_qualifier("rdf_dataset", "eval_subselect_fwd ds param")
q_term = find_qualifier("rdf_term", "path_result_fwd type alias")

# #65 Step 2c (2026-05-10): the eval_*_fwd assume vals take
# `(base : option wf_iri)` as their first parameter (where applicable).
# The ref types and realisations below are updated accordingly.
# eval_expr_ebv_ref/eval_expr_fwd_ref RETIRED (g4-filter-devacuation,
# 2026-08-09): eval_expr_ebv/eval_expr_fwd are concrete F* definitions now
# (see script header), extracted as real functions -- no ref/wiring needed.
# eval_exists_fwd_ref RETIRED (g4-exists-cycle-pilot, 2026-08-09): same
# story -- eval_exists is a real recursive OCaml function now (part of
# the eval_pattern_store/substitute_existentials/eval_exists clique), no
# ref/wiring needed.
replacement_block = f'''let eval_subselect_fwd_ref :
  (query ->
    {q_graph}.rdf_graph ->
    {q_ds}.rdf_dataset -> solution_sequence) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> [])
let eval_subselect_fwd (q : query)
  (g : {q_graph}.rdf_graph)
  (ds : {q_ds}.rdf_dataset) : solution_sequence=
  !eval_subselect_fwd_ref q g ds
type path_result_fwd =
  ({q_term}.rdf_term * {q_term}.rdf_term) Prims.list
let eval_property_path_fwd_ref :
  (property_path ->
    {q_graph}.rdf_graph -> path_result_fwd) Stdlib.ref=
  Stdlib.ref (fun _ _ -> [])
let eval_property_path_fwd (p : property_path)
  (g : {q_graph}.rdf_graph) : path_result_fwd=
  !eval_property_path_fwd_ref p g'''

content = whole_block_re.sub(lambda _m: replacement_block, content, count=1)

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

# eval_exists_fwd_ref wiring block RETIRED (g4-exists-cycle-pilot,
# 2026-08-09) along with the ref/stub above -- eval_exists needs no
# post-hoc wiring, it is defined directly in the eval_pattern_store
# clique and called there like any other OCaml function.

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
PYEOF

echo "  Forward ref wiring patches applied."
