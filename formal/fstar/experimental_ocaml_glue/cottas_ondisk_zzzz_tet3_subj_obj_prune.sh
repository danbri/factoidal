#!/bin/bash
# Tet3 demo-prep glue (issue #100, 2026-04-26).
#
# Per-row-group SUBJECT and OBJECT presence pruning for the on-disk
# COTTAS backend. Mirrors Yod6's predicate-presence prune for s + o.
#
# Background (post-Yod6): predicate-bound queries skip rgs absent of the
# bound predicate via `pred_rg_could_contain`. But subject/object-bound
# queries still walk ALL 26 rgs even when the bound term sits in only
# 1-3 rgs. Parliament corpus distinct counts:
#   - subjects: 908 k across 26 rgs (~35 k subjs/rg)
#   - objects:  956 k across 26 rgs (~37 k objs/rg)
# So most subjects and objects appear in just a handful of rgs; bound
# subj/obj queries pay 23-25 wasted full-rg scans.
#
# What this patch does (after cottas_ondisk_zzz_yod6_pred_presence_prune.sh
# has run):
#
#   1. Adds two path-keyed presence Hashtbls in Cottas_ondisk_lazy:
#        subj_presence_by_path : (path, rg_index -> subj-token-set)
#        obj_presence_by_path  : (path, rg_index -> obj-token-set)
#      Plus per-path getters and `subj_rg_could_contain` /
#      `obj_rg_could_contain` helpers, mirroring Yod6's API exactly.
#
#   2. Replaces `ensure_subjects_loaded` body to walk col=0 per-rg
#      (instead of the batched collect_distinct), populating both the
#      existing global ft_subj_tok_to_id / ft_id_to_subject /
#      ft_id_to_subj_tok tables AND the per-rg subj presence sets.
#      Same total work; per-rg presence is a free byproduct.
#
#   3. Same for `ensure_objects_loaded` (col=2).
#
#   4. Extends the existing pred-only rg gates in search_fast,
#      estimate_fast, and search_fast_limited with conjunctive subj +
#      obj presence checks. Skip a rg iff
#        not (pred_rg_could_contain ... && subj_rg_could_contain ...
#             && obj_rg_could_contain ...).
#      Each is `true` for an unbound term, so this is a strict
#      generalisation of Yod6.
#
# Rule #15 conformance: the semantic decision "skip rgs not containing
# the bound term" is already in F* in
# `RDF.CottasStore.compute_candidate_rgs_loop` (multi-column). This
# patch mirrors that optimisation in the OCaml fast-path shims; no new
# RDF/SPARQL semantics. Result-set semantics are byte-identical because
# skipped rgs provably match no rows for that bound term (the presence
# set was built by enumerating every value in the rg's column).
#
# Pre-requisites: cottas_ondisk_runtime.sh, cottas_ondisk_z_lazy_open.sh,
# cottas_ondisk_zz_aleph6_count_limit.sh, and especially
# cottas_ondisk_zzz_yod6_pred_presence_prune.sh must all have run first.
#
# Idempotency: skip-if-marker pattern.
#
# Boot-time cost (parliament): +10-20 s on top of Yod6's
# ensure_predicates_loaded. Acceptable; pre-warm already takes 107-130 s.
# RSS cost: ~50-100 MB extra (26 rgs x 35 k subjs + 37 k objs in tiny
# Hashtbls). Acceptable.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping tet3 patch" >&2
  exit 0
fi

if grep -q 'tet3: subj_presence_by_path installed' "$FILE"; then
  echo "  Tet3 demo-prep patch already present."
  exit 0
fi

# Sanity: prerequisite patches must have already run.
if ! grep -q 'module Cottas_ondisk_lazy' "$FILE"; then
  echo "  Warning: tet3 patch needs Cottas_ondisk_lazy;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_z_lazy_open.sh must run first." >&2
  exit 0
fi
if ! grep -q 'yod6: pred_presence_by_path installed' "$FILE"; then
  echo "  Warning: tet3 patch needs Yod6's pred_presence_by_path;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzz_yod6_pred_presence_prune.sh must run first." >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Step 1: Augment Cottas_ondisk_lazy with subj+obj presence tables and
# helpers. The anchor is Yod6's `pred_rg_could_contain` definition
# followed immediately by `end` (closing Cottas_ondisk_lazy).
# We insert AFTER the pred_rg_could_contain function, BEFORE `end`.
# ----------------------------------------------------------------------

lazy_anchor = """  let pred_rg_could_contain (path : string) (rg : Stdlib.Int.t)
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

lazy_new = """  let pred_rg_could_contain (path : string) (rg : Stdlib.Int.t)
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

  (* tet3: subj_presence_by_path installed (issue #100, 2026-04-26).
     Same shape as pred_presence_by_path. Populated by
     ensure_subjects_loaded; consulted via subj_rg_could_contain from
     search_fast / estimate_fast / search_fast_limited.

     Soundness: built by enumerating every value in the rg's subject
     column, so a rg marked absent provably contains zero matching rows
     for that bound subject. *)
  let subj_presence_by_path
    : (string, (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t
    = Hashtbl.create 17

  let obj_presence_by_path
    : (string, (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t) Hashtbl.t
    = Hashtbl.create 17

  let subj_presence_for_path (path : string)
    : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
    match Hashtbl.find_opt subj_presence_by_path path with
    | Some t -> t
    | None ->
      let t : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
      Hashtbl.add subj_presence_by_path path t;
      t

  let obj_presence_for_path (path : string)
    : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t =
    match Hashtbl.find_opt obj_presence_by_path path with
    | Some t -> t
    | None ->
      let t : (Stdlib.Int.t, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
      Hashtbl.add obj_presence_by_path path t;
      t

  let subj_rg_could_contain (path : string) (rg : Stdlib.Int.t)
    (bound_s : string option) : bool =
    match bound_s with
    | None -> true
    | Some s_tok ->
      match Hashtbl.find_opt subj_presence_by_path path with
      | None -> true
      | Some by_rg ->
        match Hashtbl.find_opt by_rg rg with
        | None -> true
        | Some s_set -> Hashtbl.mem s_set s_tok

  let obj_rg_could_contain (path : string) (rg : Stdlib.Int.t)
    (bound_o : string option) : bool =
    match bound_o with
    | None -> true
    | Some o_tok ->
      match Hashtbl.find_opt obj_presence_by_path path with
      | None -> true
      | Some by_rg ->
        match Hashtbl.find_opt by_rg rg with
        | None -> true
        | Some o_set -> Hashtbl.mem o_set o_tok
end"""

if lazy_anchor not in content:
    sys.stderr.write("  [tet3] WARN: Cottas_ondisk_lazy/pred_rg_could_contain anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(lazy_anchor, lazy_new, 1)

# ----------------------------------------------------------------------
# Step 2: Replace ensure_subjects_loaded body to walk per-rg and record
# presence sets. The OLD body (Bet7's, still in place since Yod6 only
# touched ensure_predicates_loaded) uses collect_distinct.
# ----------------------------------------------------------------------

old_ensure_subj = """  let ensure_subjects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_subj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (s_strs, s_tok_to_id, _n) = collect_distinct h.coh_path 0 in
      (* Move s_tok_to_id contents into tables.ft_subj_tok_to_id.
         (We can't just reassign — the field is a fresh Hashtbl.) *)
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_subj_tok_to_id k v) s_tok_to_id;
      List.iteri (fun i raw ->
        match parse_subject_str raw with
        | Some s ->
          Hashtbl.replace tables.ft_id_to_subject  i s;
          Hashtbl.replace tables.ft_id_to_subj_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_subjects_loaded: invalid subject token id=%d val=%s\\n%!" i raw)
        s_strs;
      Cottas_ondisk_lazy.mark_subj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: %d distinct subjects\\n%!"
        (Hashtbl.length tables.ft_subj_tok_to_id)
    end"""

new_ensure_subj = """  let ensure_subjects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_subj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: lazy populate path=%s\\n%!" h.coh_path;
      (* tet3: walk subject column per-rg to record per-rg presence
         (vs. the previous batched collect_distinct that lost which rg
         each token came from). *)
      let presence = Cottas_ondisk_lazy.subj_presence_for_path h.coh_path in
      let next_id = ref (Hashtbl.length tables.ft_subj_tok_to_id) in
      let rg_count = match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      for rg = 0 to rg_count - 1 do
        let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 4096 in
        (match Parquet_Footer.probe_parquet_column_decode_in_row_group
                 h.coh_path (Z.of_int rg) Z.zero with
         | FStar_Pervasives_Native.None ->
           Printf.eprintf "[tet3-WARN] ensure_subjects_loaded: rg=%d decode failed\\n%!" rg
         | FStar_Pervasives_Native.Some lst ->
           List.iter (function
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some raw ->
               (* Record presence for this rg. *)
               if not (Hashtbl.mem rg_set raw) then
                 Hashtbl.add rg_set raw ();
               (* Build global tok_to_id / id_to_subject / id_to_subj_tok
                  the same way collect_distinct would have. *)
               if not (Hashtbl.mem tables.ft_subj_tok_to_id raw) then begin
                 let id = !next_id in
                 incr next_id;
                 Hashtbl.add tables.ft_subj_tok_to_id raw id;
                 (match parse_subject_str raw with
                  | Some s ->
                    Hashtbl.replace tables.ft_id_to_subject  id s;
                    Hashtbl.replace tables.ft_id_to_subj_tok id raw
                  | None ->
                    Printf.eprintf "[tet3-WARN] ensure_subjects_loaded: invalid subject token id=%d val=%s\\n%!" id raw)
               end) lst);
        Hashtbl.replace presence rg rg_set;
        if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
          Printf.eprintf "[tet3-trace] ensure_subjects_loaded rg=%d/%d distinct_subjs=%d\\n%!"
            rg rg_count (Hashtbl.length rg_set)
      done;
      Cottas_ondisk_lazy.mark_subj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_subjects_loaded: %d distinct subjects (tet3 per-rg presence built for %d rgs)\\n%!"
        (Hashtbl.length tables.ft_subj_tok_to_id) rg_count
    end"""

if old_ensure_subj not in content:
    sys.stderr.write("  [tet3] WARN: ensure_subjects_loaded anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_ensure_subj, new_ensure_subj, 1)

# ----------------------------------------------------------------------
# Step 3: Replace ensure_objects_loaded body similarly.
# ----------------------------------------------------------------------

old_ensure_obj = """  let ensure_objects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_obj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: lazy populate path=%s\\n%!" h.coh_path;
      let (o_strs, o_tok_to_id, _n) = collect_distinct h.coh_path 2 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tables.ft_obj_tok_to_id k v) o_tok_to_id;
      List.iteri (fun i raw ->
        match parse_object_str raw with
        | Some o ->
          Hashtbl.replace tables.ft_id_to_object  i o;
          Hashtbl.replace tables.ft_id_to_obj_tok i raw
        | None ->
          Printf.eprintf "[bet7-WARN] ensure_objects_loaded: invalid object token id=%d val=%s\\n%!" i raw)
        o_strs;
      Cottas_ondisk_lazy.mark_obj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: %d distinct objects\\n%!"
        (Hashtbl.length tables.ft_obj_tok_to_id)
    end"""

new_ensure_obj = """  let ensure_objects_loaded (h : cottas_ondisk_handle) (tables : fast_tables) : unit =
    if not (Cottas_ondisk_lazy.is_obj_loaded h.coh_path) then begin
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: lazy populate path=%s\\n%!" h.coh_path;
      (* tet3: walk object column per-rg to record per-rg presence
         (vs. the previous batched collect_distinct that lost which rg
         each token came from). *)
      let presence = Cottas_ondisk_lazy.obj_presence_for_path h.coh_path in
      let next_id = ref (Hashtbl.length tables.ft_obj_tok_to_id) in
      let rg_count = match Parquet_Footer.probe_parquet_row_group_count h.coh_path with
        | FStar_Pervasives_Native.None -> 0
        | FStar_Pervasives_Native.Some n -> Z.to_int n in
      for rg = 0 to rg_count - 1 do
        let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 4096 in
        (match Parquet_Footer.probe_parquet_column_decode_in_row_group
                 h.coh_path (Z.of_int rg) (Z.of_int 2) with
         | FStar_Pervasives_Native.None ->
           Printf.eprintf "[tet3-WARN] ensure_objects_loaded: rg=%d decode failed\\n%!" rg
         | FStar_Pervasives_Native.Some lst ->
           List.iter (function
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some raw ->
               (* Record presence for this rg. *)
               if not (Hashtbl.mem rg_set raw) then
                 Hashtbl.add rg_set raw ();
               (* Build global tok_to_id / id_to_object / id_to_obj_tok
                  the same way collect_distinct would have. *)
               if not (Hashtbl.mem tables.ft_obj_tok_to_id raw) then begin
                 let id = !next_id in
                 incr next_id;
                 Hashtbl.add tables.ft_obj_tok_to_id raw id;
                 (match parse_object_str raw with
                  | Some o ->
                    Hashtbl.replace tables.ft_id_to_object  id o;
                    Hashtbl.replace tables.ft_id_to_obj_tok id raw
                  | None ->
                    Printf.eprintf "[tet3-WARN] ensure_objects_loaded: invalid object token id=%d val=%s\\n%!" id raw)
               end) lst);
        Hashtbl.replace presence rg rg_set;
        if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
          Printf.eprintf "[tet3-trace] ensure_objects_loaded rg=%d/%d distinct_objs=%d\\n%!"
            rg rg_count (Hashtbl.length rg_set)
      done;
      Cottas_ondisk_lazy.mark_obj_loaded h.coh_path;
      Gc.full_major ();
      Printf.eprintf "[bet7-trace] ensure_objects_loaded: %d distinct objects (tet3 per-rg presence built for %d rgs)\\n%!"
        (Hashtbl.length tables.ft_obj_tok_to_id) rg_count
    end"""

if old_ensure_obj not in content:
    sys.stderr.write("  [tet3] WARN: ensure_objects_loaded anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_ensure_obj, new_ensure_obj, 1)

# ----------------------------------------------------------------------
# Step 4: Extend the search_fast pred-only gate with subj+obj checks.
# Yod6 left this as `if not (pred_rg_could_contain ...)` — tet3 makes
# it conjunctive: a rg is candidate iff pred AND subj AND obj could
# contain. Skip iff any one definitively excludes it.
# ----------------------------------------------------------------------

old_search_gate = """    let n_skipped = ref 0 in
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
      !n_skipped rg_count (match bound_p with None -> "_" | Some s -> s);"""

new_search_gate = """    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
      let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
      let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] search_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
            rg could_p could_s could_o
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] search_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[tet3-trace] search_fast: skipped %d/%d rg(s) (s=%s p=%s o=%s)\\n%!"
      !n_skipped rg_count
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>");"""

if old_search_gate not in content:
    sys.stderr.write("  [tet3] WARN: search_fast yod6 gate anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_search_gate, new_search_gate, 1)

# ----------------------------------------------------------------------
# Step 5: Extend estimate_fast similarly.
# ----------------------------------------------------------------------

old_estimate_gate = """    let n_skipped = ref 0 in
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
      !n_skipped rg_count (match bound_p with None -> "_" | Some s -> s);"""

new_estimate_gate = """    let n_skipped = ref 0 in
    for rg = 0 to rg_count - 1 do
      let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path rg bound_p in
      let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path rg bound_s in
      let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path rg bound_o in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] estimate_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
            rg could_p could_s could_o
      end else begin
        try walk_rg rg
        with e ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "[pe4-FATAL] estimate_fast rg=%d EXCEPTION: %s\\nbacktrace=%s\\n%!"
            rg (Printexc.to_string e) bt;
          raise e
      end
    done;
    Printf.eprintf "[tet3-trace] estimate_fast: skipped %d/%d rg(s) (s=%s p=%s o=%s)\\n%!"
      !n_skipped rg_count
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>");"""

if old_estimate_gate not in content:
    sys.stderr.write("  [tet3] WARN: estimate_fast yod6 gate anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_estimate_gate, new_estimate_gate, 1)

# ----------------------------------------------------------------------
# Step 6: Extend search_fast_limited's gate with subj+obj checks.
# Yod6 inserted the gate AND wired ensure_predicates_loaded right before
# the rg loop. We need to also ensure subj+obj loaded at that point —
# the function already calls ensure_subjects_loaded / ensure_objects_loaded
# at the very top (Bet7 + Aleph6), so the presence tables will be built
# by the time the loop runs. Just patch the gate.
# ----------------------------------------------------------------------

old_limited_gate = """        if not (Cottas_ondisk_lazy.pred_rg_could_contain path r bound_p) then begin
          incr n_skipped;
          if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
            Printf.eprintf "[yod6-trace] search_fast_limited rg=%d skipped (predicate absent)\\n%!" r;
          incr rg
        end else begin"""

new_limited_gate = """        let could_p = Cottas_ondisk_lazy.pred_rg_could_contain path r bound_p in
        let could_s = Cottas_ondisk_lazy.subj_rg_could_contain path r bound_s in
        let could_o = Cottas_ondisk_lazy.obj_rg_could_contain  path r bound_o in
        if not (could_p && could_s && could_o) then begin
          incr n_skipped;
          if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
            Printf.eprintf "[tet3-trace] search_fast_limited rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
              r could_p could_s could_o;
          incr rg
        end else begin"""

if old_limited_gate not in content:
    sys.stderr.write("  [tet3] WARN: search_fast_limited yod6 gate anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_limited_gate, new_limited_gate, 1)

# Update the post-loop summary trace too.
old_limited_summary = """    Printf.eprintf "[yod6-trace] search_fast_limited: skipped %d/%d rg(s) for predicate=%s\\n%!"
      !n_skipped rg_count (match bound_p with None -> "_" | Some s -> s);"""

new_limited_summary = """    Printf.eprintf "[tet3-trace] search_fast_limited: skipped %d/%d rg(s) (s=%s p=%s o=%s)\\n%!"
      !n_skipped rg_count
      (match bound_s with None -> "_" | Some _ -> "<sub>")
      (match bound_p with None -> "_" | Some s -> s)
      (match bound_o with None -> "_" | Some _ -> "<obj>");"""

if old_limited_summary not in content:
    sys.stderr.write("  [tet3] WARN: search_fast_limited summary anchor not found; aborting\n")
    sys.exit(0)

content = content.replace(old_limited_summary, new_limited_summary, 1)

path.write_text(content)
sys.stderr.write("  [tet3] applied: subj+obj-presence prune in search_fast / estimate_fast / search_fast_limited\n")
PYEOF

echo "  Tet3 demo-prep patch applied."
