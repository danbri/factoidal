#!/bin/bash
# Phase 2.7-mini (issue #118) — realise the four
# `ondisk_lookup_{subj,pred,obj,graph}_id_global` `assume val`s
# declared in RDF.CottasStore.fst.
#
# Why: the F*-extracted `build_qp_row` used to call
# `revmap_lookup h.coh_*_raw_revmap tok` to map a parquet column
# token back to its term-id. On Bet7-lazy-opened handles those
# F*-side assoc-lists are empty (Bet7 defers their construction to
# keep handle-open under 5 s for the parliament corpus). So the
# F*-extracted `cottas_ondisk_search` body returned 0 rows.
#
# This shim bridges the F* spec to Bet7's OCaml-side
# `ensure_*_loaded` + `Hashtbl<token, int>` infrastructure: the F*
# `build_qp_row` calls these `_global` lookups; OCaml realises them
# by ensuring the relevant column is populated, then a single
# `Hashtbl.find_opt`. Rule #11(c) thin dispatch shim.
#
# Soundness: post-realisation, the assume-val outcome is observably
# equivalent to `revmap_lookup h.coh_*_raw_revmap tok` on a
# fully-populated handle. The data is the same; only the lookup
# shape (assoc-list vs Hashtbl) differs.
#
# Sort order: zzzzzzzzzzzzzzzzz (17 z's) — runs LAST in the
# cottas_ondisk_* chain. Needs Cottas_ondisk_runtime (defined by
# cottas_ondisk_runtime.sh) and Cottas_ondisk_lazy (defined by
# cottas_ondisk_z_lazy_open.sh) to be in place.
#
# After 2.7-mini lands, Phase 2.5e (retire the OCaml `search_fast`
# / `estimate_fast` dispatch shims) becomes a clean removal of the
# `cottas_ondisk_search` / `_estimate` substitutions in
# cottas_ondisk_runtime.sh — the F* path will produce correct rows.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  ML="$OUTDIR"
else
  ML="$OUTDIR/RDF_CottasStore.ml"
fi

if [[ ! -f "$ML" ]]; then
  echo "  [token-lookup-runtime] WARN: $ML not found; skipping."
  exit 0
fi

if grep -q '__TOKEN_LOOKUP_RUNTIME_APPLIED__' "$ML"; then
  echo "  [token-lookup-runtime] already applied; skipping."
  exit 0
fi

# Sanity: prerequisite modules must already be present.
if ! grep -q 'module Cottas_ondisk_runtime' "$ML"; then
  echo "  [token-lookup-runtime] FATAL: Cottas_ondisk_runtime not in $ML; cottas_ondisk_runtime.sh must run first." >&2
  exit 1
fi
if ! grep -q 'module Cottas_ondisk_lazy' "$ML"; then
  echo "  [token-lookup-runtime] FATAL: Cottas_ondisk_lazy not in $ML; cottas_ondisk_z_lazy_open.sh must run first." >&2
  exit 1
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib, re

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Helper: substitute the four failwith stubs with stateful realisations
# that route via Cottas_ondisk_runtime + Cottas_ondisk_lazy.
#
# F* 2025.x extraction shape:
#   let ondisk_lookup_subj_id_global (path : Prims.string)
#     (token : Prims.string) :
#     Prims.nat FStar_Pervasives_Native.option=
#     failwith
#       "Not yet implemented: RDF.CottasStore.ondisk_lookup_subj_id_global"
# (and similar for pred / obj / graph)
# ----------------------------------------------------------------------

# Common helper: opens the per-path tables, runs the appropriate
# ensure_*_loaded hook, returns Hashtbl.find_opt result wrapped in
# the F*-extracted FStar_Pervasives_Native option type.
helper_block = '''
(* Phase 2.7-mini (issue #118): token -> id lookup helper, used by
   build_qp_row's `ondisk_lookup_*_id_global` assume-val realisations
   below. Rule #11(c) thin dispatch shim — no semantic decisions,
   only the same routing search_fast already uses.
   __TOKEN_LOOKUP_RUNTIME_APPLIED__ *)
module Cottas_token_lookup_global = struct
  let lookup_with_ensure
      (ensure : cottas_ondisk_handle -> Cottas_ondisk_runtime.fast_tables -> unit)
      (table_of : Cottas_ondisk_runtime.fast_tables -> (string, Stdlib.Int.t) Hashtbl.t)
      (path : Prims.string) (token : Prims.string)
    : Prims.nat FStar_Pervasives_Native.option =
    match Hashtbl.find_opt Cottas_ondisk_runtime.handles path with
    | None -> FStar_Pervasives_Native.None
    | Some h ->
      let tables = Cottas_ondisk_runtime.tables_for h in
      ensure h tables;
      (match Hashtbl.find_opt (table_of tables) token with
       | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
       | None   -> FStar_Pervasives_Native.None)
end

'''

# Insert helper module just BEFORE the first `ondisk_lookup_*_id_global`
# extracted stub so the realisations below can reference it.
anchor = "let ondisk_lookup_subj_id_global "
if anchor not in content:
    sys.stderr.write("  [token-lookup-runtime] FATAL: ondisk_lookup_subj_id_global stub not found; F* extraction may have changed.\n")
    sys.exit(1)

content = content.replace(anchor, helper_block + anchor, 1)

# Substitute each of the four failwith stubs with a one-line dispatch.
# F* 2025.x extracts assume-vals as `let foo (...) : ...= failwith "..."`.

# F* 2025.x extracts these assume-vals in slightly varying shapes:
# sometimes both args on one line, sometimes split; sometimes failwith
# on one line, sometimes split. Match permissively with a regex.
column_specs = [
    ("subj",  "ensure_subjects_loaded",   "ft_subj_tok_to_id"),
    ("pred",  "ensure_predicates_loaded", "ft_pred_tok_to_id"),
    ("obj",   "ensure_objects_loaded",    "ft_obj_tok_to_id"),
    ("graph", "ensure_graphs_loaded",     "ft_graph_tok_to_id"),
]

applied = 0
for col, ensure_fn, table_field in column_specs:
    fn = f"ondisk_lookup_{col}_id_global"
    # Permissive pattern: header (any whitespace, including line breaks
    # between params and return type), then the failwith with the full
    # "Not yet implemented: RDF.CottasStore.<fn>" message.
    pattern = re.compile(
        r"let " + re.escape(fn) +
        r"\s*\(path\s*:\s*Prims\.string\)\s*\(token\s*:\s*Prims\.string\)\s*"
        r":\s*Prims\.nat\s+FStar_Pervasives_Native\.option=\s*"
        r"failwith\s*"
        r'"Not yet implemented: RDF\.CottasStore\.' + re.escape(fn) + r'"',
        re.MULTILINE,
    )
    new_body = (
        f"let {fn} (path : Prims.string) (token : Prims.string)\n"
        f"  : Prims.nat FStar_Pervasives_Native.option =\n"
        f"  Cottas_token_lookup_global.lookup_with_ensure\n"
        f"    Cottas_ondisk_lazy.{ensure_fn}\n"
        f"    (fun t -> t.Cottas_ondisk_runtime.{table_field})\n"
        f"    path token"
    )
    new_content, n = pattern.subn(new_body, content, count=1)
    if n == 1:
        content = new_content
        applied += 1
    else:
        sys.stderr.write(f"  [token-lookup-runtime] WARN: {fn} stub not found (regex didn't match)\n")

path.write_text(content)
sys.stderr.write(f"  [token-lookup-runtime] applied {applied}/4 ondisk_lookup_*_id_global realisations\n")
PYEOF

echo "  Cottas token-lookup runtime applied."
