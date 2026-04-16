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
import re
with open('$FILE', 'r') as f:
    content = f.read()

# 1. Add current_base_iri_ref before eval_expr so it's in scope
content = content.replace(
    'let rec eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :',
    '''let current_base_iri_ref : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ref =
  ref FStar_Pervasives_Native.None

let rec eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :'''
)

# 2. Set/restore base_iri in eval_select_query
content = content.replace(
    '''let eval_select_query (q : query) (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : solution_sequence=
  match q.q_form with
  | QF_Select sel ->''',
    '''let eval_select_query (q : query) (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : solution_sequence=
  let saved_base = !current_base_iri_ref in
  current_base_iri_ref := q.q_base;
  let result = match q.q_form with
  | QF_Select sel ->'''
)

# Close the let result = match ... wrapper after QF_Describe
# The next definition after eval_select_query may be rewrite_query_bnode_term
# (from ballyhoo port) or type path_result (original). Handle both.
import re as _re
close_pattern = _re.compile(r'(\s*\| QF_Describe uu___ -> \[\])\n(let |type )')
m = close_pattern.search(content)
if m:
    insert_pos = m.end(1)
    content = content[:insert_pos] + '''
  in
  current_base_iri_ref := saved_base;
  result''' + content[insert_pos:]

# 3. Enhance IRI() function to resolve against base IRI
content = content.replace(
    '''  | E_IRI_fn e1 ->
      (match eval_expr e1 mu with
       | ER_Term (RDF_Graph_Executable.T_IRI i) ->
           ER_Term (RDF_Graph_Executable.T_IRI i)
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           (match string_to_iri (lit_lexical l) with
            | FStar_Pervasives_Native.Some i ->
                ER_Term (RDF_Graph_Executable.T_IRI i)
            | FStar_Pervasives_Native.None -> ER_Error)
       | uu___ -> ER_Error)''',
    '''  | E_IRI_fn e1 ->
      (match eval_expr e1 mu with
       | ER_Term (RDF_Graph_Executable.T_IRI i) ->
           ER_Term (RDF_Graph_Executable.T_IRI i)
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           let s = lit_lexical l in
           (match !current_base_iri_ref with
            | FStar_Pervasives_Native.Some base ->
                ER_Term (RDF_Graph_Executable.T_IRI (resolve_iri base s))
            | FStar_Pervasives_Native.None ->
                (match string_to_iri s with
                 | FStar_Pervasives_Native.Some i ->
                     ER_Term (RDF_Graph_Executable.T_IRI i)
                 | FStar_Pervasives_Native.None -> ER_Error))
       | uu___ -> ER_Error)'''
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
