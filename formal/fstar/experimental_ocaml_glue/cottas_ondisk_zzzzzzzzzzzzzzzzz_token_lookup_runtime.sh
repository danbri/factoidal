#!/bin/bash
# Realise the ONE remaining dictionary `assume val` of
# RDF.CottasStore.fst: `ondisk_token_tables_global`.
#
# History. Until 2026-08-24 this patch realised EIGHT `assume val`s --
# `ondisk_id_to_{subj,pred,obj,graph}_token_global` and
# `ondisk_lookup_{subj,pred,obj,graph}_id_global`, the two directions of
# one token dictionary. None of the eight was input/output, so none of
# them qualified under CLAUDE.md rule #11, and their correctness
# requirement lived only in a prose comment in the F-star source that
# nothing could check.
#
# The F-star source now carries `cottas_token_tables` (the eight
# directions as one record), `token_tables_agree_with` (the requirement,
# as a Type0 predicate), `tables_of_handle` + `tables_of_handle_agree`
# (the populated-handle instance and its proof), and
# `build_qp_row_agrees` (the consequence: under agreement the fast
# tables and the handle's own assoc-lists build the same row). What is
# left assumed is a single value -- the deferred read of the four
# dictionary columns of the store file -- which this patch supplies.
#
# Why the deferred read exists: the F-star-side `coh_*_raw` /
# `coh_*_raw_revmap` assoc-lists are EMPTY on a lazily-opened handle
# (the lazy open defers building them to keep handle-open under 5 s for
# the parliament corpus). The OCaml runtime carries the same data in
# `Cottas_ondisk_runtime.fast_tables`, populated on first touch by
# `Cottas_ondisk_lazy.ensure_*_loaded`. This patch is a thin rule-#11
# dispatch shim over that: ensure_loaded + Hashtbl.find_opt, one
# closure per direction, no semantic decision and no byte layout.
#
# The eight closures ignore the `path` handed to
# `ondisk_token_tables_global` and take the path per call, exactly as
# the eight assume-vals did, so ONE shared record serves every path and
# `build_qp_row` allocates nothing per row.
#
# Sort order: zzzzzzzzzzzzzzzzz (17 z's) -- runs LAST in the
# cottas_ondisk_* chain. Needs Cottas_ondisk_runtime (defined by
# cottas_ondisk_runtime.sh) and Cottas_ondisk_lazy (defined by
# cottas_ondisk_z_lazy_open.sh) to be in place.

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
# Helper module: the two dispatch shapes, one per dictionary direction.
# Both open the per-path tables, run the column's ensure_*_loaded hook,
# and answer from the Hashtbl, wrapped in the F-star-extracted option
# type.
# ----------------------------------------------------------------------

helper_block = '''
(* Realisation of RDF.CottasStore.ondisk_token_tables_global: the
   deferred read of the four dictionary columns. Rule #11 dispatch
   shim over Cottas_ondisk_lazy's ensure_*_loaded + Hashtbl.find_opt.
   Its obligation is stated in F-star as
   `token_tables_agree_with (ondisk_token_tables_global h.coh_path) h`
   and consumed by `build_qp_row_agrees`.
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

  (* Mirror of lookup_with_ensure for the id -> raw token direction. *)
  let id_to_token_with_ensure
      (ensure : cottas_ondisk_handle -> Cottas_ondisk_runtime.fast_tables -> unit)
      (table_of : Cottas_ondisk_runtime.fast_tables -> (Stdlib.Int.t, string) Hashtbl.t)
      (path : Prims.string) (id : Prims.nat)
    : Prims.string FStar_Pervasives_Native.option =
    match Hashtbl.find_opt Cottas_ondisk_runtime.handles path with
    | None -> FStar_Pervasives_Native.None
    | Some h ->
      let tables = Cottas_ondisk_runtime.tables_for h in
      ensure h tables;
      (match Hashtbl.find_opt (table_of tables) (Z.to_int id) with
       | Some s -> FStar_Pervasives_Native.Some s
       | None   -> FStar_Pervasives_Native.None)
end

(* One shared record. Every closure takes its path per call, so this
   value is path-independent and `build_qp_row` allocates nothing per
   matched row. *)
let cottas_global_token_tables : cottas_token_tables =
  {
    ctt_id_to_subj_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_subjects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_subj_tok);
    ctt_id_to_pred_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_predicates_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_pred_tok);
    ctt_id_to_obj_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_objects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_obj_tok);
    ctt_id_to_graph_token =
      Cottas_token_lookup_global.id_to_token_with_ensure
        Cottas_ondisk_runtime.ensure_graphs_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_id_to_graph_tok);
    ctt_lookup_subj_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_subjects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_subj_tok_to_id);
    ctt_lookup_pred_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_predicates_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_pred_tok_to_id);
    ctt_lookup_obj_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_objects_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_obj_tok_to_id);
    ctt_lookup_graph_id =
      Cottas_token_lookup_global.lookup_with_ensure
        Cottas_ondisk_runtime.ensure_graphs_loaded
        (fun t -> t.Cottas_ondisk_runtime.ft_graph_tok_to_id);
  }

'''

anchor = "let ondisk_token_tables_global "
if anchor not in content:
    sys.stderr.write("  [token-lookup-runtime] FATAL: ondisk_token_tables_global stub not found; F-star extraction may have changed.\n")
    sys.exit(1)

content = content.replace(anchor, helper_block + anchor, 1)

# Substitute the failwith stub. F* 2025.x extracts the assume-val as
#   let ondisk_token_tables_global (path : Prims.string) : cottas_token_tables=
#     failwith "Not yet implemented: RDF.CottasStore.ondisk_token_tables_global"
pattern = re.compile(
    r"let ondisk_token_tables_global\s*\(path\s*:\s*Prims\.string\)\s*"
    r":\s*cottas_token_tables=\s*"
    r"failwith\s*"
    r'"Not yet implemented: RDF\.CottasStore\.ondisk_token_tables_global"',
    re.MULTILINE,
)

new_body = (
    "let ondisk_token_tables_global (_path : Prims.string)\n"
    "  : cottas_token_tables =\n"
    "  cottas_global_token_tables"
)

content, n = pattern.subn(new_body, content, count=1)
if n != 1:
    sys.stderr.write("  [token-lookup-runtime] FATAL: ondisk_token_tables_global stub regex did not match.\n")
    sys.exit(1)

path.write_text(content)
sys.stderr.write("  [token-lookup-runtime] applied ondisk_token_tables_global realisation (8 dictionary directions in 1 record)\n")
PYEOF

echo "  Cottas token-lookup runtime applied."
