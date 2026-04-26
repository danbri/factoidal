#!/bin/bash
# Mem5 — presence-bitmap fast path for cottas_ondisk_estimate.
#
# Issue #100, 2026-04-26.
#
# What this patch does:
#
#   The BGP join-order optimiser calls cottas_ondisk_estimate (extracted
#   as Cottas_ondisk_runtime.estimate_fast) for every triple pattern.
#   After Yod6/Tet3, presence-bitmap pruning ALREADY skips row-groups
#   that demonstrably can't contain a bound term — but for surviving
#   row-groups, the previous code still decoded all 4 columns and
#   counted matching rows. On the 26-rg parliament corpus this is
#   minutes per query before the planner picks an order.
#
#   This patch replaces estimate_fast_inner's data-page-walk loop with
#   a presence-only approximation:
#
#     - For each row-group, consult the per-rg presence bitmaps
#       (Tet3's pred_rg_could_contain / subj_rg_could_contain /
#       obj_rg_could_contain). The surviving rgs are exactly the
#       candidate set.
#
#     - Estimate = |candidates| * (total_rows / rg_count) where
#       total_rows comes from the parquet footer (no I/O cost).
#
#     - Empty candidates returns 0 (definitive empty-result early-out).
#
#   The estimate is approximate (off-by-2x is fine; the optimiser only
#   needs ordinal cardinality). For exact counts callers should issue
#   an actual COUNT(*) query, which already has the Aleph6 footer
#   shortcut for the unbound case.
#
#   Cost drops from O(num_rgs * column_decode) approx seconds to
#   O(num_rgs * num_bounds) approx microseconds. On parliament's
#   3-pattern modern queries, optimiser cardinality lookup goes from
#   tens of seconds to milliseconds.
#
# Sort order: cottas_ondisk_zzzzzzz_* — must run AFTER Lamed3
# (zzzzzz) so the Lamed3 dispatcher's call to estimate_fast_inner
# sees this fast version, AND after Tet3 (zzzz) which installs the
# presence-bitmap helpers.
#
# Rule #15: pure performance shim. The semantics are encoded in the
# F* spec RDF.CottasStore.cottas_ondisk_estimate, which has been
# updated in lockstep (commit Mem5 / 2026-04-26) to use the same
# dictionary-cache fast path. The OCaml runtime uses Tet3's per-rg
# presence Hashtbls (a more compact structure than the F* dict_cache
# but semantically equivalent for the candidate-rg computation).
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping mem5 estimate-presence patch" >&2
  exit 0
fi

# Sanity: prior Tet3 patch must have installed the presence-bitmap
# helpers (subj_rg_could_contain etc.) we need.
if ! grep -q 'tet3: subj_presence_by_path installed' "$FILE"; then
  echo "  Warning: mem5 patch needs Tet3 presence helpers;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzz_tet3_subj_obj_prune.sh must run first." >&2
  exit 0
fi

# Lamed3's dispatcher renames the slow body to estimate_fast_inner
# (in the mutually-recursive `and estimate_fast_inner` form, since
# Lamed3 uses a `let rec ... and ...` group), so we look for either
# spelling.
if ! grep -qE '(let|and) estimate_fast_inner' "$FILE"; then
  echo "  Warning: mem5 patch needs Lamed3's estimate_fast_inner;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh must run first." >&2
  exit 0
fi

if grep -q 'mem5: estimate_fast_inner presence-bitmap fast path' "$FILE"; then
  echo "  Mem5 estimate-presence patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# Replace the entire body of estimate_fast_inner (Lamed3-renamed) with
# a presence-bitmap-only fast path. The match anchor goes from the
# function header through the previous body's final `!count` return.

# Lamed3's renamed-inner ends up either `let estimate_fast_inner ...`
# (when Mem5 runs against an old extraction predating Lamed3's `let
# rec ... and ...` form) or `and estimate_fast_inner ...` (current
# Lamed3). Match both spellings; we replace from the header through
# the slow walk's tail.
old_header_let = '''let estimate_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ='''
old_header_and = '''and estimate_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ='''

if old_header_and in content:
    inner_keyword = 'and'
    old_header = old_header_and
elif old_header_let in content:
    inner_keyword = 'let'
    old_header = old_header_let
else:
    sys.stderr.write("  [mem5] WARN: estimate_fast_inner header (let|and) not found; aborting\n")
    sys.exit(0)

old_body_anchor = old_header + '''
    let path = h.coh_path in
    let tables = tables_for h in
    (* Conditional populate: only the bound columns need their tables. *)
    (match bound.Parser_BallyhooCOTTAS.cbqp_s with
     | FStar_Pervasives_Native.Some _ -> ensure_subjects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_p with
     | FStar_Pervasives_Native.Some _ -> ensure_predicates_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_o with
     | FStar_Pervasives_Native.Some _ -> ensure_objects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_g with
     | FStar_Pervasives_Native.Some _ -> ensure_graphs_loaded h tables
     | _ -> ());'''

if old_body_anchor not in content:
    sys.stderr.write("  [mem5] WARN: estimate_fast_inner header anchor not found; aborting\n")
    sys.exit(0)

# Find the body end. Old body ends with `!count` followed by the
# closing of the function (next `let decode_subject_fast`).

old_body_tail = '''    Printf.eprintf "[qof3-trace] estimate_fast: matched %d row(s)\\n%!" !count;
    Printf.eprintf "[pe4-trace] estimate_fast post-walk rss=%dMB heap=%dMB count=%d\\n%!"
      (pe4_rss_mb ()) (pe4_gc_mb ()) !count;
    !count'''

if old_body_tail not in content:
    sys.stderr.write("  [mem5] WARN: estimate_fast_inner tail anchor not found; aborting\n")
    sys.exit(0)

# Locate the head and the tail; replace everything between (the slow
# walk body) with a presence-only fast computation.
head_idx = content.find(old_body_anchor)
tail_idx = content.find(old_body_tail, head_idx)
if head_idx < 0 or tail_idx < 0 or tail_idx < head_idx:
    sys.stderr.write("  [mem5] WARN: anchor positions invalid; aborting\n")
    sys.exit(0)

after_tail = tail_idx + len(old_body_tail)

new_body = inner_keyword + ''' estimate_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    (* mem5: estimate_fast_inner presence-bitmap fast path
       (issue #100, 2026-04-26).

       For BGP join-order optimisation, exact cardinality is
       unnecessary; ordinal estimates suffice. We compute the
       candidate row-groups using only Tet3's per-rg presence
       bitmaps (already populated by ensure_predicates_loaded /
       ensure_subjects_loaded / ensure_objects_loaded), then return
       |candidates| * avg_rows_per_rg. Total cost: O(num_rgs *
       num_bounds) — microseconds for the parliament corpus. *)
    let path = h.coh_path in
    let tables = tables_for h in
    (* Populate only the presence tables for bound columns. *)
    (match bound.Parser_BallyhooCOTTAS.cbqp_s with
     | FStar_Pervasives_Native.Some _ -> ensure_subjects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_p with
     | FStar_Pervasives_Native.Some _ -> ensure_predicates_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_o with
     | FStar_Pervasives_Native.Some _ -> ensure_objects_loaded h tables
     | _ -> ());
    (match bound.Parser_BallyhooCOTTAS.cbqp_g with
     | FStar_Pervasives_Native.Some _ -> ensure_graphs_loaded h tables
     | _ -> ());
    let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
    let bound_p = bound_id_to_token tables.ft_id_to_pred_tok  bound.Parser_BallyhooCOTTAS.cbqp_p in
    let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
    let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
    let any_bound_present =
      bound_s <> None || bound_p <> None || bound_o <> None || bound_g <> None in
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    if not any_bound_present then begin
      (* Aleph6: footer-only fast path. Mirrors the F* spec wrapper. *)
      let n =
        match Parquet_Footer.probe_parquet_num_rows path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      Printf.eprintf "[mem5-trace] estimate_fast_inner: unbound -> footer total=%d\\n%!" n;
      n
    end
    else begin
      (* AND of presence bitmaps across all bound columns. The graph
         column does not have a Tet3-installed presence helper; the
         3-of-4 column intersection is sufficient for cardinality. *)
      let candidates = ref 0 in
      for rg = 0 to rg_count - 1 do
        let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
        let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
        let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
        if could_p && could_s && could_o then incr candidates
      done;
      let n_candidates = !candidates in
      Printf.eprintf "[mem5-trace] estimate_fast_inner: candidates=%d/%d (s=%s p=%s o=%s g=%s)\\n%!"
        n_candidates rg_count
        (match bound_s with None -> "_" | Some _ -> "<sub>")
        (match bound_p with None -> "_" | Some s -> s)
        (match bound_o with None -> "_" | Some _ -> "<obj>")
        (match bound_g with None -> "_" | Some s -> s);
      if n_candidates = 0 then 0
      else if rg_count = 0 then 0
      else begin
        let total_rows =
          match Parquet_Footer.probe_parquet_num_rows path with
          | FStar_Pervasives_Native.None -> 0
          | FStar_Pervasives_Native.Some n -> Z.to_int n in
        if total_rows = 0 then n_candidates
        else
          let avg = total_rows / rg_count in
          let est = n_candidates * avg in
          Printf.eprintf "[mem5-trace] estimate_fast_inner: total=%d avg=%d est=%d\\n%!"
            total_rows avg est;
          est
      end
    end'''

content = content[:head_idx] + new_body + content[after_tail:]

# Idempotency marker (also disambiguates this patch in the source).
marker_anchor = "let estimate_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ="
if "mem5: estimate_fast_inner presence-bitmap fast path" not in content:
    sys.stderr.write("  [mem5] WARN: marker not in replacement output; this is a bug\n")
    sys.exit(1)

path.write_text(content)
sys.stderr.write("  [mem5] applied: estimate_fast_inner -> presence-bitmap fast path\n")
PYEOF

echo "  Mem5 estimate-presence patch applied."
