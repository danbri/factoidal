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
    r'let eval_expr_ebv.*?failwith "Not yet implemented: '
    r'SPARQL11\.Algebra\.eval_property_path_fwd"',
    re.DOTALL
)
m = whole_block_re.search(content)
if m is None:
    sys.stderr.write(
        "  ERROR: patch 62 could not find the F*-extracted failwith stub "
        f"block (eval_expr_ebv .. eval_property_path_fwd) in {path}.\n"
        "         Has a stub's own failwith message text changed, or has "
        "a function been renamed/reordered? Inspect the "
        "eval_expr_ebv/eval_expr_fwd/eval_exists_fwd/eval_subselect_fwd/"
        "eval_property_path_fwd stubs directly and update the anchors "
        "above -- do NOT let this fall through silently, the wiring-line "
        "inserts below assume the *_ref declarations this substitution "
        "produces.\n"
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

q_wfiri = find_qualifier("wf_iri", "eval_expr_ebv/eval_expr_fwd/eval_exists_fwd base param")
q_sm = find_qualifier("solution_mapping", "eval_exists_fwd mu param")
q_graph = find_qualifier("rdf_graph", "eval_exists_fwd/eval_subselect_fwd g param")
q_ds = find_qualifier("rdf_dataset", "eval_exists_fwd/eval_subselect_fwd ds param")
q_term = find_qualifier("rdf_term", "path_result_fwd type alias")

# #65 Step 2c (2026-05-10): the three eval_*_fwd assume vals now take
# `(base : option wf_iri)` as their first parameter. The ref types and
# realisations below are updated accordingly. eval_expr_ebv_ref dispatches
# to eval_expr_with_base directly so BASE flows through FILTER / OPTIONAL
# evaluation without consulting current_base_iri_ref.
replacement_block = f'''let eval_expr_ebv_ref :
  ({q_wfiri}.wf_iri FStar_Pervasives_Native.option ->
    expr -> {q_sm}.solution_mapping -> Prims.bool) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> failwith "eval_expr_ebv not yet wired")
let eval_expr_fwd_ref :
  ({q_wfiri}.wf_iri FStar_Pervasives_Native.option ->
    expr -> {q_sm}.solution_mapping -> eval_result) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> failwith "eval_expr_fwd not yet wired")
let eval_exists_fwd_ref :
  ({q_wfiri}.wf_iri FStar_Pervasives_Native.option ->
    group_graph_pattern ->
    {q_sm}.solution_mapping ->
    {q_graph}.rdf_graph ->
    {q_ds}.rdf_dataset -> Prims.bool) Stdlib.ref=
  Stdlib.ref (fun _ _ _ _ _ -> false)
let eval_subselect_fwd_ref :
  (query ->
    {q_graph}.rdf_graph ->
    {q_ds}.rdf_dataset -> solution_sequence) Stdlib.ref=
  Stdlib.ref (fun _ _ _ -> [])
let eval_expr_ebv
  (base : {q_wfiri}.wf_iri FStar_Pervasives_Native.option)
  (e : expr)
  (mu : {q_sm}.solution_mapping) : Prims.bool=
  !eval_expr_ebv_ref base e mu
let eval_expr_fwd
  (base : {q_wfiri}.wf_iri FStar_Pervasives_Native.option)
  (e : expr)
  (mu : {q_sm}.solution_mapping) : eval_result=
  !eval_expr_fwd_ref base e mu
let eval_exists_fwd
  (base : {q_wfiri}.wf_iri FStar_Pervasives_Native.option)
  (p : group_graph_pattern)
  (mu : {q_sm}.solution_mapping)
  (g : {q_graph}.rdf_graph)
  (ds : {q_ds}.rdf_dataset) : Prims.bool=
  !eval_exists_fwd_ref base p mu g ds
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
    # Same qualifier-drift hazard as the main stub block above: `wf_iri`'s
    # live qualifier may differ from the hardcoded `RDF_Graph_Executable`
    # this anchor used to assume. Also same line-wrapping hazard: whether
    # `(base` sits on the same line as `let filter_solutions` or its own
    # line varies between extractions, so match on whitespace generically
    # (`\s+`) rather than assuming a literal newline+indent. The negative
    # lookahead excludes `filter_solutions_fwd` / `filter_solutions_with_graph`,
    # which share the `filter_solutions` prefix but are different functions.
    filter_solutions_anchor_re = re.compile(
        r'let filter_solutions(?![A-Za-z_])\s+\(base : ' + QUAL + r'\.wf_iri'
    )
    fm = filter_solutions_anchor_re.search(content)
    if fm is None:
        sys.stderr.write(
            "  ERROR: patch 62 could not find the 'let filter_solutions' "
            f"anchor in {path} to wire eval_exists_fwd_ref.\n"
            "         eval_exists_fwd_ref would stay wired to `false` for "
            "every FILTER EXISTS/NOT EXISTS query -- a silent wrong-answer "
            "bug, not a compile failure. Inspect filter_solutions' current "
            "signature and update the anchor above.\n"
        )
        sys.exit(1)
    content = (
        content[:fm.start()]
        + 'let () = eval_exists_fwd_ref := eval_exists\n'
        + content[fm.start():]
    )

with open(path, 'w', encoding='utf-8') as f:
    f.write(content)
PYEOF

echo "  Forward ref wiring patches applied."
