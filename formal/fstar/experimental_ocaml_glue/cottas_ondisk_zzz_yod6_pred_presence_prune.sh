#!/bin/bash
# Yod6 demo-prep glue (issue #100, 2026-04-26).
#
# Per-row-group predicate-presence pruning for the on-disk COTTAS backend.
#
# Background: predicate-bound queries currently walk all 26 row groups
# even when the bound predicate appears in only a handful. This blew up
# in two ways for the parliament corpus:
#   - geosparql-wktLiteral query (predicate absent from corpus) materialised
#     3.14M rows before filtering, OOM'd / SIGBUS'd.
#   - any predicate-bound query paid for 25 wasted full-rg scans on top
#     of the 1 productive scan.
#
# Root cause:
#   1. F* `cottas_ondisk_search` has a `plan_candidate_rgs` prune via
#      `populate_dict_cache_for_column` + `compute_candidate_rgs_loop`,
#      but that path is REPLACED by the OCaml `search_fast` perf shim
#      (cottas_ondisk_runtime.sh lines 885+).
#   2. The F*-side prune relies on `probe_parquet_column_dictionary_in_row_group`,
#      which returns None for COTTAS-style data (DLBA-encoded predicate
#      column with no per-rg dictionary page). So even if the F* path ran,
#      it would degenerate to "include all rgs" via the safe fallback.
#
# Aleph6 explicitly de-scoped this: "If time permits, attempt: also probe
# via DLBA distinct-extraction (walk the column once per rg, collect
# distinct strings, cache). Cost ~equal to a full data-page decode, but
# cached across queries — net positive amortised."
#
# What this patch does:
#
#   1. Adds a path-keyed presence Hashtbl
#      `pred_presence_by_path : (string, (int, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t`
#      mapping path → rg_index → set-of-predicate-tokens.
#
#   2. Replaces `ensure_predicates_loaded`'s body to walk the predicate
#      column PER-RG (via `probe_parquet_column_decode_in_row_group`),
#      populating both the existing tok_to_id / id_to_predicate /
#      id_to_pred_tok Hashtbls AND the new presence table. Same total
#      work as the previous batched `collect_distinct h.coh_path 1`, no
#      extra cold-boot cost; per-rg presence is a free byproduct.
#
#   3. Adds helper `pred_rg_could_contain : string -> int -> string option -> bool`:
#      returns true if the rg might contain the predicate (or there's no
#      bound, or the rg has no presence entry — safe fallback). Returns
#      false ONLY when we have an entry for that rg and the predicate
#      definitively isn't in it.
#
#   4. Modifies `search_fast`, `estimate_fast`, and `search_fast_limited`
#      to consult `pred_rg_could_contain` and skip rgs where the bound
#      predicate is absent. Logs per-query rg-skip counts as
#      [yod6-trace] skipped N/M rg(s) for predicate=...
#
# Rule #15 conformance: the semantic decision "skip rgs not containing
# the bound predicate" is already in F* in
# `RDF.CottasStore.compute_candidate_rgs_loop`. This patch mirrors that
# optimisation in the OCaml fast-path shims; no new RDF/SPARQL semantics.
# Result-set semantics are byte-identical because skipped rgs provably
# match no rows for that predicate (the presence set was built by
# enumerating EVERY value in the rg's predicate column).
#
# Pre-requisites: cottas_ondisk_runtime.sh, cottas_ondisk_z_lazy_open.sh,
# cottas_ondisk_zz_aleph6_count_limit.sh must all have run first.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping yod6 patch" >&2
  exit 0
fi

if grep -q 'yod6: pred_presence_by_path installed' "$FILE"; then
  echo "  Yod6 demo-prep patch already present."
  exit 0
fi

# Sanity: prerequisite patches must have already run.
if ! grep -q 'module Cottas_ondisk_lazy' "$FILE"; then
  echo "  Warning: yod6 patch needs Cottas_ondisk_lazy;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh must run first." >&2
  exit 0
fi
if ! grep -q 'aleph6: search_fast_limited installed' "$FILE"; then
  echo "  Warning: yod6 patch needs search_fast_limited;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zz_aleph6_count_limit.sh must run first." >&2
  exit 0
fi
if ! grep -q 'let ensure_predicates_loaded' "$FILE"; then
  echo "  Warning: yod6 patch needs ensure_predicates_loaded; skipping." >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Step 1: Augment Cottas_ondisk_lazy with the presence table + helper.
# ----------------------------------------------------------------------

lazy_anchor = """  let mark_subj_loaded  path = Hashtbl.replace subj_loaded  path ()
  let mark_pred_loaded  path = Hashtbl.replace pred_loaded  path ()
  let mark_obj_loaded   path = Hashtbl.replace obj_loaded   path ()
  let mark_graph_loaded path = Hashtbl.replace graph_loaded path ()
  let is_subj_loaded    path = Hashtbl.mem subj_loaded  path
  let is_pred_loaded    path = Hashtbl.mem pred_loaded  path
  let is_obj_loaded     path = Hashtbl.mem obj_loaded   path
  let is_graph_loaded   path = Hashtbl.mem graph_loaded path
end"""

lazy_new = """  let mark_subj_loaded  path = Hashtbl.replace subj_loaded  path ()
  let mark_pred_loaded  path = Hashtbl.replace pred_loaded  path ()
  let mark_obj_loaded   path = Hashtbl.replace obj_loaded   path ()
  let mark_graph_loaded path = Hashtbl.replace graph_loaded path ()
  let is_subj_loaded    path = Hashtbl.mem subj_loaded  path
  let is_pred_loaded    path = Hashtbl.mem pred_loaded  path
  let is_obj_loaded     path = Hashtbl.mem obj_loaded   path
  let is_graph_loaded   path = Hashtbl.mem graph_loaded path

  (* yod6: pred_presence_by_path installed (issue #100, 2026-04-26).
     For each artifact path, a rg_index -> set-of-predicate-tokens map.
     Populated by ensure_predicates_loaded (replaces the batched
     collect_distinct walk). Consulted by search_fast / estimate_fast /
     search_fast_limited to skip rgs that don't contain the bound
     predicate.

     Mirrors F*-side compute_candidate_rgs_loop (RDF.CottasStore.fst):
     skip rg if `not (list_string_mem dict bound_token)`. Soundness:
     the presence set is built by enumerating every value in the rg's
     predicate column, so a rg marked absent provably contains zero
     matching rows. *)
  (* Use Stdlib.Int.t explicitly: the file's `open Prims` makes `int` mean
     Prims.int = Z.t, even inside this submodule's `open Stdlib`. Bet7
     hit the same issue and aliased `pint = Stdlib.Int.t` in
     Cottas_ondisk_runtime; we mirror that. *)
  let pred_presence_by_path
    : (string, (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t
    = Hashtbl.create 17

  let presence_for_path (path : string)
    : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
    match Hashtbl.find_opt pred_presence_by_path path with
    | Some t -> t
    | None ->
      let t : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
      Hashtbl.add pred_presence_by_path path t;
      t

  (* Returns true iff the rg might contain `pred_tok`, or there's no bound,
     or we have no presence entry for this rg (safe fallback: walk it).
     Returns false ONLY when we have an entry and the predicate is
     definitively absent. *)
  let pred_rg_could_contain (path : string) (rg : Stdlib.Int.t)
    (bound_p : string option) : bool =
    match bound_p with
    | None -> true
    | Some pred_tok ->
      match Hashtbl.find_opt pred_presence_by_path path with
      | None -> true
      | Some by_rg ->
        match Hashtbl.find_opt by_rg rg with
        | None -> true  (* presence not yet recorded for this rg *)
        | Some pred_set -> Hashtbl.mem pred_set pred_tok
end"""

if lazy_anchor not in content:
    sys.stderr.write("  [yod6] WARN: Cottas_ondisk_lazy anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(lazy_anchor, lazy_new, 1)

# ----------------------------------------------------------------------
# Step 2: Replace ensure_predicates_loaded body.
# Old body uses collect_distinct (batched walk of all rgs at once).
# New body walks per-rg, populates the same Hashtbls AND the presence
# table. Same total work; per-rg presence is a free byproduct.
# ----------------------------------------------------------------------

old_ensure_pred = """  let ensure_predicates_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_pred_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (p_strs, p_tok_to_id, _n) = collect_distinct h.coh_path 1 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_pred_tok_to_id k v) p_tok_to_id;
      List.iteri (fun i raw ->
        match parse_iri_token raw with
        | Some iri ->
          Hashtbl.replace tables.ft_id_to_predicate i iri;
          Hashtbl.replace tables.ft_id_to_pred_tok  i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_predicates_loaded: invalid predicate token id=%d val=%s\\n%!" i raw)
        p_strs;
      Cottas_ondisk_lazy.mark_pred_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: %d distinct predicates\\n%!"
        (Hashtbl.length tables.ft_pred_tok_to_id)
    end"""

new_ensure_pred = """  let ensure_predicates_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_pred_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: lazy populate path=%s\\n%!" h.coh_path;
      (* yod6: walk predicate column per-rg to record per-rg presence
         (vs. the previous batched collect_distinct that lost which rg
         each token came from). *)
      let presence = Cottas_ondisk_lazy.presence_for_path h.coh_path in
      let next_id = ref (Hashtbl.length tables.ft_pred_tok_to_id) in
      let rg_count = match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      for rg = 0 to rg_count - 1 do
        let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 16 in
        (match Parquet_Footer.probe_parquet_column_decode_in_row_group
                 h.coh_path (Z.of_int rg) Z.one with
         | FStar_Pervasives_Native.None ->
           Printf.eprintf "[yod6-WARN] ensure_predicates_loaded: rg=%d decode failed\\n%!" rg
         | FStar_Pervasives_Native.Some lst ->
           List.iter (function
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some raw ->
               (* Record presence for this rg. *)
               if not (Hashtbl.mem rg_set raw) then
                 Hashtbl.add rg_set raw ();
               (* Build global tok_to_id / id_to_predicate / id_to_pred_tok
                  the same way collect_distinct would have. *)
               if not (Hashtbl.mem tables.ft_pred_tok_to_id raw) then begin
                 let id = !next_id in
                 incr next_id;
                 Hashtbl.add tables.ft_pred_tok_to_id raw id;
                 (match parse_iri_token raw with
                  | Some iri ->
                    Hashtbl.replace tables.ft_id_to_predicate id iri;
                    Hashtbl.replace tables.ft_id_to_pred_tok  id raw
                  | None ->
                    Printf.eprintf "[yod6-WARN] ensure_predicates_loaded: invalid predicate token id=%d val=%s\\n%!" id raw)
               end) lst);
        Hashtbl.replace presence rg rg_set;
        if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
          Printf.eprintf "[yod6-trace] ensure_predicates_loaded rg=%d/%d distinct_preds=%d\\n%!"
            rg rg_count (Hashtbl.length rg_set)
      done;
      Cottas_ondisk_lazy.mark_pred_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_predicates_loaded: %d distinct predicates (yod6 per-rg presence built for %d rgs)\\n%!"
        (Hashtbl.length tables.ft_pred_tok_to_id) rg_count
    end"""

if old_ensure_pred not in content:
    sys.stderr.write("  [yod6] WARN: ensure_predicates_loaded anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_ensure_pred, new_ensure_pred, 1)

# ----------------------------------------------------------------------
# Step 3: Patch search_fast to skip rgs the predicate isn't in.
# We replace the inner loop's `for rg = 0 to rg_count - 1 do try walk_rg rg ...`
# block with a version that gates `walk_rg rg` on pred_rg_could_contain.
# ----------------------------------------------------------------------

old_search_loop = """    for rg = 0 to rg_count - 1 do
      try walk_rg rg
      with e ->
        let bt = Printexc.get_backtrace () in
        Printf.eprintf "[pe4-FATAL] search_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
          rg (Printexc.to_string e) bt;
        raise e
    done;
    Printf.eprintf "[qof3-trace] search_fast: matched %d row(s) across %d row group(s)\\n%!" !n_matches rg_count;"""

new_search_loop = """    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      if not (Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[yod6-trace] search_fast rg=%d skipped (predicate absent)\\n%!" rg
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] search_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[yod6-trace] search_fast: skipped %d/%d rg(s) for predicate=%s\\n%!"
      !n_skipped rg_count (match bound_p with None -> "_" | Some s -> s);
    Printf.eprintf "[qof3-trace] search_fast: matched %d row(s) across %d row group(s)\\n%!" !n_matches rg_count;"""

if old_search_loop not in content:
    sys.stderr.write("  [yod6] WARN: search_fast loop anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_search_loop, new_search_loop, 1)

# ----------------------------------------------------------------------
# Step 4: Patch estimate_fast similarly.
# ----------------------------------------------------------------------

old_estimate_loop = """    for rg = 0 to rg_count - 1 do
      try walk_rg rg
      with e ->
        let bt = Printexc.get_backtrace () in
        Printf.eprintf "[pe4-FATAL] estimate_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
          rg (Printexc.to_string e) bt;
        raise e
    done;
    Printf.eprintf "[qof3-trace] estimate_fast: matched %d row(s)\\n%!" !count;"""

new_estimate_loop = """    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      if not (Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[yod6-trace] estimate_fast rg=%d skipped (predicate absent)\\n%!" rg
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] estimate_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[yod6-trace] estimate_fast: skipped %d/%d rg(s) for predicate=%s\\n%!"
      !n_skipped rg_count (match bound_p with None -> "_" | Some s -> s);
    Printf.eprintf "[qof3-trace] estimate_fast: matched %d row(s)\\n%!" !count;"""

if old_estimate_loop not in content:
    sys.stderr.write("  [yod6] WARN: estimate_fast loop anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_estimate_loop, new_estimate_loop, 1)

# ----------------------------------------------------------------------
# Step 5: Patch search_fast_limited similarly.
# Its loop uses while !rg < rg_count && !n_matches < limit; we add the
# presence gate inside the loop body.
# ----------------------------------------------------------------------

old_limited_loop = """    let rg = ref 0 in
    (try
      while !rg < rg_count && !n_matches < limit do
        let r = !rg in
        let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.zero in"""

new_limited_loop = """    (* yod6: search_fast_limited needs ensure_predicates_loaded too,
       so the presence table is populated before we consult it. *)
    ensure_predicates_loaded h tables;
    let rg = ref 0 in
    let n_skipped = ref 0 in
    (try
      while !rg < rg_count && !n_matches < limit do
        let r = !rg in
        if not (Cottas_ondisk_lazy.pred_rg_could_contain path r bound_p) then begin
          incr n_skipped;
          if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
            Printf.eprintf "[yod6-trace] search_fast_limited rg=%d skipped (predicate absent)\\n%!" r;
          incr rg
        end else begin
        let s_lst = Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.zero in"""

if old_limited_loop not in content:
    sys.stderr.write("  [yod6] WARN: search_fast_limited loop anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_limited_loop, new_limited_loop, 1)

# Close the new `else begin` we opened. Anchor on the existing `incr rg` /
# `done` / `with e ->` boundary.
old_limited_close = """        incr rg
      done
    with e ->
      let bt = Printexc.get_backtrace () in
      Printf.eprintf "[aleph6-FATAL] search_fast_limited rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
        !rg (Printexc.to_string e) bt;
      raise e);
    Printf.eprintf "[aleph6-trace] search_fast_limited: matched %d/%d row(s), walked %d/%d rg(s)\\n%!"
      !n_matches limit !rg rg_count;"""

new_limited_close = """        incr rg
        end (* yod6: close the not-skipped branch *)
      done
    with e ->
      let bt = Printexc.get_backtrace () in
      Printf.eprintf "[aleph6-FATAL] search_fast_limited rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
        !rg (Printexc.to_string e) bt;
      raise e);
    Printf.eprintf "[yod6-trace] search_fast_limited: skipped %d/%d rg(s) for predicate=%s\\n%!"
      !n_skipped rg_count (match bound_p with None -> "_" | Some s -> s);
    Printf.eprintf "[aleph6-trace] search_fast_limited: matched %d/%d row(s), walked %d/%d rg(s)\\n%!"
      !n_matches limit !rg rg_count;"""

if old_limited_close not in content:
    sys.stderr.write("  [yod6] WARN: search_fast_limited close anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_limited_close, new_limited_close, 1)

path.write_text(content)
sys.stderr.write("  [yod6] applied: pred-presence prune in search_fast / estimate_fast / search_fast_limited\n")
PYEOF

echo "  Yod6 demo-prep patch applied."
