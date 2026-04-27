#!/bin/bash
# Aleph6 demo-prep glue (issue #100, 2026-04-26).
#
# Two narrow shims, applied AFTER cottas_ondisk_runtime.sh and
# cottas_ondisk_z_lazy_open.sh have run:
#
# 1. Streaming-COUNT(*) shortcut: when the bound is all-None (= unbound
#    `?s ?p ?o`), `cottas_ondisk_estimate` reads the parquet footer's
#    FileMetaData.num_rows field directly — microseconds, no data-page
#    decode, no lazy-load triggered. For parliament's 3.14M-row corpus
#    this is the difference between < 1 s and > 100 s.
#
#    The bounded path still goes through Cottas_ondisk_runtime.estimate_fast
#    (Bet7's per-rg walk), since per-row matching IS required to count
#    matched rows. The spec for cottas_ondisk_estimate (in
#    RDF.CottasStore.fst) was updated in the same commit to use
#    probe_parquet_num_rows for the all-None case; this shim mirrors
#    that semantics in the OCaml runtime path.
#
# 2. LIMIT-pushdown OCaml fast path: a new
#    `Cottas_ondisk_runtime.search_fast_limited` clones search_fast
#    but stops the row-group walk once `limit` matches accumulate.
#    `cottas_ondisk_search_limited` (added to the F* spec for Aleph6)
#    is shimmed to call it. Without this, the F* implementation walks
#    the parquet using the empty `coh_subjects_raw`/`coh_objects_raw`
#    that Bet7's lazy-open leaves behind — so build_qp_row's revmap
#    lookups fail for every row and the result is empty.
#
# Rule #15 conformance: the matching/output shape and "stop at N
# matches" decision are identical to the F* spec's
# walk_row_groups_search_limited. No new RDF/SPARQL semantics — just
# the same loop with O(1) Hashtbl lookups + lazy-load hooks, matching
# what Bet7's search_fast does for the unlimited variant.
#
# Idempotency: skip if marker present.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping aleph6 patch" >&2
  exit 0
fi

if grep -q 'aleph6: search_fast_limited installed' "$FILE"; then
  echo "  Aleph6 demo-prep patch already present."
  exit 0
fi

# Sanity: prerequisite patches must have already run.
if ! grep -q 'let search_fast (h : cottas_ondisk_handle)' "$FILE"; then
  echo "  Warning: aleph6 patch needs Cottas_ondisk_runtime.search_fast;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_runtime.sh must run first." >&2
  exit 0
fi
if ! grep -q 'module Cottas_ondisk_lazy' "$FILE"; then
  echo "  Warning: aleph6 patch needs Cottas_ondisk_lazy;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh must run first." >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path
import re

path = Path(sys.argv[1])
content = path.read_text()

# ---- Step 1: Streaming COUNT(*) shortcut for cottas_ondisk_estimate.
# Replace the perf-shim version that always calls estimate_fast with
# one that takes the all-None fast path via probe_parquet_num_rows.

estimate_old = """let cottas_ondisk_estimate (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : Prims.nat=
  Z.of_int (Cottas_ondisk_runtime.estimate_fast ds.cods_handle bound)"""

estimate_new = """let cottas_ondisk_estimate (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : Prims.nat=
  (* Aleph6 streaming-COUNT shortcut: all-None bound -> read num_rows
     from the parquet footer (microseconds). Otherwise per-rg walk via
     estimate_fast. *)
  let any_bound_present =
    (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_s)
    || (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_p)
    || (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_o)
    || (FStar_Pervasives_Native.uu___is_Some bound.Parser_BallyhooCOTTAS.cbqp_g) in
  if not any_bound_present then
    (match Parquet_Footer.probe_parquet_num_rows
             (ds.cods_handle).coh_path with
     | FStar_Pervasives_Native.Some n ->
       Printf.eprintf "[aleph6-trace] estimate: all-None -> probe_parquet_num_rows = %s\\n%!"
         (Z.to_string n);
       n
     | FStar_Pervasives_Native.None ->
       Z.of_int (Cottas_ondisk_runtime.estimate_fast ds.cods_handle bound))
  else
    Z.of_int (Cottas_ondisk_runtime.estimate_fast ds.cods_handle bound)"""

if estimate_old in content:
    content = content.replace(estimate_old, estimate_new, 1)
    sys.stderr.write("  [aleph6] estimate streaming-COUNT shortcut installed\n")
else:
    sys.stderr.write("  [aleph6] WARN: estimate perf-shim text not found (already aleph6'd?)\n")

# ---- Step 2: Add Cottas_ondisk_runtime.search_fast_limited.
# Find the end of search_fast (it ends with "List.rev !acc") and add a
# limited variant just after it.

search_fast_anchor = """    Printf.eprintf "[qof3-trace] search_fast: matched %d row(s) across %d row group(s)\\n%!" !n_matches rg_count;
    Printf.eprintf "[pe4-trace] search_fast post-walk rss=%dMB heap=%dMB matches=%d\\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) !n_matches;
    List.rev !acc

  (* Estimate: same loop as search_fast but counts only — no per-row"""

if search_fast_anchor not in content:
    sys.stderr.write("  [aleph6] WARN: search_fast anchor not found — cannot install search_fast_limited\n")
    path.write_text(content)
    sys.exit(0)

search_fast_limited = '''    Printf.eprintf "[qof3-trace] search_fast: matched %d row(s) across %d row group(s)\\n%!" !n_matches rg_count;
    Printf.eprintf "[pe4-trace] search_fast post-walk rss=%dMB heap=%dMB matches=%d\\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) !n_matches;
    List.rev !acc

  (* aleph6: search_fast_limited installed.
     Same as search_fast but stops once `limit` matches accumulate.
     Used by F*-side cottas_ondisk_search_limited for LIMIT pushdown
     (issue #100, 2026-04-26). Keeps Bet7 lazy-load semantics intact —
     ensure_subjects_loaded / ensure_objects_loaded run on entry, then
     the per-rg walk uses O(1) Hashtbl lookups in build_qp_row.
     Matching predicate is byte-identical to search_fast. *)
  let search_fast_limited (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    let path = h.coh_path in
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    ensure_objects_loaded  h tables;
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = bound_id_to_token tables.ft_id_to_pred_tok  bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
    Printf.eprintf "[aleph6-trace] search_fast_limited: limit=%d bound s=%s p=%s o=%s g=%s\\n%!"
      limit
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>")
      (match bound_g with None -> "_" | Some s -> s);
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    let acc = ref [] in
    let n_matches = ref 0 in
    let arr_of_col col_opt =
      (* Phase 2.5c (issue #118): col_opt is `cottas_column option`
         (= `string option array option`) post-pagecache-hot-path patch.
         Identity-with-fallback. *)
      match col_opt with
      | FStar_Pervasives_Native.None -> [||]
      | FStar_Pervasives_Native.Some arr -> arr in
    let cell_of = function
      | FStar_Pervasives_Native.Some s -> s
      | FStar_Pervasives_Native.None -> "" in
    let rg = ref 0 in
    (try
      while !rg < rg_count && !n_matches < limit do
        let r = !rg in
        let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.zero in
        let s_arr = arr_of_col s_lst in
        let p_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.one in
        let p_arr = arr_of_col p_lst in
        let o_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 2) in
        let o_arr = arr_of_col o_lst in
        let g_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 3) in
        let g_arr = arr_of_col g_lst in
        let n = Array.length s_arr in
        if Array.length p_arr <> n || Array.length o_arr <> n || Array.length g_arr <> n then
          Printf.eprintf "[aleph6-FATAL] search_fast_limited: rg=%d column lengths disagree (s=%d p=%d o=%d g=%d)\\n%!"
            r n (Array.length p_arr) (Array.length o_arr) (Array.length g_arr)
        else begin
          let i = ref 0 in
          while !i < n && !n_matches < limit do
            let idx = !i in
            let s_tok = cell_of s_arr.(idx) in
            let p_tok = cell_of p_arr.(idx) in
            let o_tok = cell_of o_arr.(idx) in
            let g_tok = cell_of g_arr.(idx) in
            if cell_match_str bound_s s_tok &&
               cell_match_str bound_p p_tok &&
               cell_match_str bound_o o_tok &&
               cell_match_str bound_g g_tok
            then begin
              let s_id = Hashtbl.find_opt tables.ft_subj_tok_to_id  s_tok in
              let p_id = Hashtbl.find_opt tables.ft_pred_tok_to_id  p_tok in
              let o_id = Hashtbl.find_opt tables.ft_obj_tok_to_id   o_tok in
              let g_id =
                if g_tok = "DEFAULT" then None
                else Hashtbl.find_opt tables.ft_graph_tok_to_id g_tok in
              let opt_to_z = function
                | None -> FStar_Pervasives_Native.None
                | Some i -> FStar_Pervasives_Native.Some (Z.of_int i) in
              acc := {
                Parser_BallyhooCOTTAS.cqpr_s = opt_to_z s_id;
                cqpr_p = opt_to_z p_id;
                cqpr_o = opt_to_z o_id;
                cqpr_g = opt_to_z g_id;
              } :: !acc;
              incr n_matches
            end;
            incr i
          done
        end;
        incr rg
      done
    with e ->
      let bt = Printexc.get_backtrace () in
      Printf.eprintf "[aleph6-FATAL] search_fast_limited rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
        !rg (Printexc.to_string e) bt;
      raise e);
    Printf.eprintf "[aleph6-trace] search_fast_limited: matched %d/%d row(s), walked %d/%d rg(s)\\n%!"
      !n_matches limit !rg rg_count;
    List.rev !acc

  (* Estimate: same loop as search_fast but counts only — no per-row'''

content = content.replace(search_fast_anchor, search_fast_limited, 1)
sys.stderr.write("  [aleph6] search_fast_limited installed\n")

# ---- Step 3: Replace cottas_ondisk_search_limited's F* body with a
# call to Cottas_ondisk_runtime.search_fast_limited.

# The pattern is the F*-extracted body of cottas_ondisk_search_limited.
# We replace it with a direct dispatch to search_fast_limited.
shim_old = """let cottas_ondisk_search_limited (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list="""

shim_new = """let cottas_ondisk_search_limited (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list=
  Cottas_ondisk_runtime.search_fast_limited ds.cods_handle bound (Z.to_int limit)
let _spec_cottas_ondisk_search_limited_unused (ds : cottas_ondisk_store)
  (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : Prims.nat) :
  Parser_BallyhooCOTTAS.cottas_qp_row Prims.list="""

if shim_old in content:
    content = content.replace(shim_old, shim_new, 1)
    sys.stderr.write("  [aleph6] cottas_ondisk_search_limited -> search_fast_limited\n")
else:
    sys.stderr.write("  [aleph6] WARN: cottas_ondisk_search_limited header not found (F* extraction skipped Aleph6 changes?)\n")

path.write_text(content)
PYEOF

echo "  Aleph6 demo-prep patch applied."
