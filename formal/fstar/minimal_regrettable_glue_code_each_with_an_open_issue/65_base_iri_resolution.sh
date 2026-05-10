#!/bin/bash
# Issue #65: BASE IRI resolution for SPARQL11_Algebra.ml and SPARQL11_Parser.ml
# https://github.com/danbri/factoidal/issues/65
#
# The SPARQL spec says IRI(string) resolves against the query's BASE declaration.
# eval_expr has no access to the query base, so we use a mutable ref
# (current_base_iri_ref) set/restored in eval_select_query.
#
# In the parser, relative IRIs (Tok_IRI) must be resolved against BASE during
# parsing. This adds resolve_tok_iri helper and patches all Tok_IRI blocks,
# datatype IRIs, and parse_prologue BASE propagation.

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

# ======================================================================
# SPARQL11_Algebra.ml patches
# ======================================================================
FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE (base IRI resolution)..."

if ! grep -q 'current_base_iri_ref' "$FILE"; then
  python3 -c "
import re, sys
with open('$FILE', 'r') as f:
    content = f.read()

# 1. Add current_base_iri_ref before eval_expr_with_base so it's in scope
#    for the mutual block, the wrapper, and eval_select_query.
#    #65 Step 2a (2026-05-10): the F*-side mutual eval functions were
#    renamed to eval_expr_with_base / eval_coalesce_with_base / etc., and
#    a non-mutual wrapper 'let eval_expr ... = eval_expr_with_base None ...'
#    was added. Anchor on the renamed mutual head so the ref declaration
#    sits above the entire eval* cluster.
content = content.replace(
    'let rec eval_expr_with_base',
    '''let current_base_iri_ref : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ref =
  ref FStar_Pervasives_Native.None

let rec eval_expr_with_base''',
    1
)

# 2. Set/restore base_iri in eval_select_query.  The extracted body now
# begins with apply_query_dataset and the inner match is paren-wrapped:
#   let eval_select_query ... =
#     let uu___ = apply_query_dataset q.q_dataset g ds in
#     match uu___ with
#     | (g1, ds1) ->
#         let q1 = { ... } in
#         (match q1.q_form with
#          | QF_Select sel -> ...
#          ...
#          | QF_Describe uu___1 -> [])
# We anchor on '(match (q|q1).q_form with' followed by '| QF_Select sel ->'
# at any indentation, then wrap the paren-bound match in save/restore of
# the base IRI ref.
m = re.search(
    r'''(let eval_select_query \(q : query\) \(g : RDF_Graph_Executable\.rdf_graph\)\n  \(ds : RDF_Graph_Executable\.rdf_dataset\) : solution_sequence=\n)(?P<body>.*?)(?P<indent>[ ]+)\((?P<match>match (?P<qvar>q1?)\.q_form with\n[ ]+\| QF_Select sel ->)''',
    content,
    flags=re.DOTALL,
)
if m is None:
    sys.stderr.write('WARNING: 65_base_iri_resolution could not find eval_select_query header\n')
else:
    qvar = m.group('qvar')
    indent = m.group('indent')
    new_header = (
        m.group(1)
        + m.group('body')
        + indent + '(let saved_base = !current_base_iri_ref in\n'
        + indent + ' current_base_iri_ref := ' + qvar + '.q_base;\n'
        + indent + ' let result = (' + m.group('match')
    )
    content = content[:m.start()] + new_header + content[m.end():]

# Closing anchor.  The QF_Describe arm now uses uu___1 (numbered) and the
# whole match is paren-wrapped.  Original ends '[])' (close of [] + close
# of paren-wrapped match).  Add ')' (close of let-result match) + restore
# + ')' (close of outer paren we opened in the header).
content, n_close = re.subn(
    r'''(?P<arm>[ ]+\| QF_Describe uu___\d* -> \[\])\)\n(?P<nextdef>let \(\) = eval_subselect_fwd_ref := eval_select_query\n|type path_result =|let eval_ask_query )''',
    lambda mm: (
        mm.group('arm') + ') in\n'
        + '         current_base_iri_ref := saved_base;\n'
        + '         result)\n'
        + mm.group('nextdef')
    ),
    content,
    count=1,
)
if n_close == 0:
    sys.stderr.write('WARNING: 65_base_iri_resolution could not close eval_select_query result scope\n')

# 3. Rewrite the eval_expr wrapper to consult current_base_iri_ref instead
#    of passing FStar_Pervasives_Native.None. The F*-side mutual block
#    (eval_expr_with_base) already handles E_IRI_fn correctly when given a
#    Some-base — see SPARQL11.Algebra.fst's E_IRI_fn arm. The wrapper is
#    the rule-#11 'wormhole' point where the OCaml-side current_base_iri_ref
#    feeds into the F* algorithm.
#
#    #65 Step 2a (2026-05-10) replaces the previous ~25-line regex rewrite
#    of the E_IRI_fn 'match … with' arm with this one-line wrapper rewrite.
#    The resolution algorithm is now in F*, not in this patch. Future Step
#    2b/2c will thread q.q_base explicitly and retire this wrapper hack
#    along with current_base_iri_ref itself.
content = content.replace(
    '''let eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result= eval_expr_with_base FStar_Pervasives_Native.None e mu''',
    '''let eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :
  eval_result= eval_expr_with_base (!current_base_iri_ref) e mu'''
)

with open('$FILE', 'w') as f:
    f.write(content)
"
fi

echo "  SPARQL11_Algebra.ml base IRI patched."

# ======================================================================
# SPARQL11_Parser.ml patches — relative IRI resolution against BASE
# ======================================================================
FILE="$OUTDIR/SPARQL11_Parser.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping parser patches" >&2
  exit 0
fi

echo "  Patching $FILE (base IRI resolution)..."

if ! grep -q 'resolve_tok_iri' "$FILE"; then
  python3 - "$FILE" << 'PYEOF'
import sys
import re

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 1. Add resolve_tok_iri helper after safe_sub function
content = content.replace(
    '''  if a >= b then a - b else Prims.int_zero''',
    '''  if a >= b then a - b else Prims.int_zero
(* Resolve a potentially relative IRI against the current BASE.
   If the IRI is already absolute (passes is_iri), return it unchanged.
   Otherwise, try resolving against the global current_base_iri_ref. *)
let resolve_tok_iri (i : Prims.string) : Prims.string =
  if RDF_Graph_Executable.is_iri i then i
  else match !(SPARQL11_Algebra.current_base_iri_ref) with
    | Some base -> SPARQL11_Algebra.resolve_iri base i
    | None -> i
'''
)

# 2. Regex-based patching: resolve ALL Tok_IRI i patterns globally.
# Each block matches: | Tok_IRI i -> ... if is_iri i ... else ParseErr ...
# We insert `let ri = resolve_tok_iri i in` and rename i -> ri in the block.
def patch_tok_iri_block(match):
    block = match.group(0)
    # Find the indentation of the 'if' line
    for line in block.split('\n'):
        if 'if RDF_Graph_Executable.is_iri i' in line:
            indent = line[:len(line) - len(line.lstrip())]
            break
    else:
        return block  # shouldn't happen

    # Insert resolve_tok_iri before the is_iri check
    block = block.replace(
        'if RDF_Graph_Executable.is_iri i',
        'let ri = resolve_tok_iri i in\n' + indent + 'if RDF_Graph_Executable.is_iri ri',
        1
    )
    # Rename i -> ri in IRI constructor uses
    block = block.replace('PS_IRI i)', 'PS_IRI ri)')
    block = block.replace('PT_IRI i), SPARQL11_Algebra.GP_Empty', 'PT_IRI ri), SPARQL11_Algebra.GP_Empty')
    block = block.replace('PT_IRI i), (parse_advance', 'PT_IRI ri), (parse_advance')
    block = block.replace('PP_IRI i), (parse_advance', 'PP_IRI ri), (parse_advance')
    block = block.replace('PP_IRI i)),', 'PP_IRI ri)),')
    block = block.replace('E_IRI i), ts', 'E_IRI ri), ts')
    block = block.replace('T_IRI i)),', 'T_IRI ri)),')
    block = block.replace('ParseOk (i, (parse_advance', 'ParseOk (ri, (parse_advance')
    block = block.replace('parse_func_call pm (fuel - Prims.int_one) i\n', 'parse_func_call pm (fuel - Prims.int_one) ri\n')
    # FROM <iri> / FROM NAMED <iri>: dataset-clause constructors stored
    # the unresolved `i` instead of the resolved `ri`, so the runtime
    # named-graph lookup (keyed by absolute file:// IRI) missed and the
    # default graph stayed empty. constructwhere04 (FROM with no BASE).
    block = block.replace('SPARQL11_Algebra.DC_Default i)', 'SPARQL11_Algebra.DC_Default ri)')
    block = block.replace('SPARQL11_Algebra.DC_Named i)', 'SPARQL11_Algebra.DC_Named ri)')
    return block

# Match each Tok_IRI i -> block from the | to the else ParseErr line
content = re.sub(
    r'\| Tok_IRI i ->\n(\s+)if RDF_Graph_Executable\.is_iri i\n.*?else ParseErr[^\n]+',
    patch_tok_iri_block,
    content,
    flags=re.DOTALL
)

# 3. Resolve datatype IRIs (Tok_IRI dt) - insert resolve_tok_iri dt
# These appear inside HATHAT handling for typed literals
content = content.replace(
    '''          | Tok_IRI dt ->
              if RDF_Graph_Executable.is_iri dt''',
    '''          | Tok_IRI dt ->
              let dt = resolve_tok_iri dt in
              if RDF_Graph_Executable.is_iri dt'''
)

# 4. parse_prologue: propagate BASE to current_base_iri_ref during parsing
# The F* code correctly returns Some iri but we also need to set the mutable
# ref so that resolve_tok_iri can access it during the rest of parsing.
content = content.replace(
    '''              if RDF_Graph_Executable.is_iri iri
              then
                (match parse_prologue pm (fuel - Prims.int_one)
                         (parse_advance ts')''',
    '''              if RDF_Graph_Executable.is_iri iri
              then begin
                SPARQL11_Algebra.current_base_iri_ref := Some iri;
                (match parse_prologue pm (fuel - Prims.int_one)
                         (parse_advance ts')'''
)
# Close the begin/end block
content = content.replace(
    '''                 | err -> err)
              else ParseErr "invalid BASE IRI"''',
    '''                 | err -> err)
              end
              else ParseErr "invalid BASE IRI"'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
fi

echo "  SPARQL11_Parser.ml base IRI patched."
