#!/bin/bash
# Lamed3 — per-row-group predicate row-offset index for the on-disk
# COTTAS backend.
#
# Issue #100, 2026-04-26.
#
# What this patch does:
#
#   1. After Vav3's dict + presence companions exist, builds a third
#      sibling companion file `<cottas>.p.offsets` that records, for
#      each (row_group, predicate_id) pair, the ascending list of
#      row positions WITHIN that rg whose predicate column equals
#      that predicate. With this file present, search_fast for a
#      bound predicate skips the predicate-column decode entirely:
#      it looks up row positions directly and only decodes subject +
#      object cells at those positions.
#
#   2. File format (companion to `.p.dict` / `.p.presence`):
#
#        [ magic 'COTO' u32 (0x4f544f43 LE) ]
#        [ version u32 ]
#        [ num_rgs u32 ]
#        [ num_predicates u32 ]
#        [ rg_offsets : u64 array, length num_rgs * num_predicates + 1 ]
#          rg_offsets[rg*np + pred]   = byte offset where row-list starts
#          rg_offsets[rg*np + pred+1] = end offset (exclusive)
#        [ data : u32[] row positions, ascending, packed ]
#
#      Per (rg, pred), row-positions = data[start..end) with
#      count = (end-start)/4 u32s.
#
#   3. Boot wiring: hooks into `Cottas_companion_boot.prewarm_via_companions`
#      after the 4 dict+presence pairs are validated/built. If the
#      offsets file is absent, build it here (one rg-walk over the
#      predicate column, ~30s on parliament). Then mmap it for the
#      lifetime of the process.
#
#   4. Reader: exposes `Cottas_offset_idx.row_positions_for :
#        path -> rg:int -> pred_id:int -> (int * int * int) option`
#      where the result is `Some (data_offset, count, total_size)` or
#      None for absent. The actual u32s are read directly from the mmap
#      view by the caller (search_fast) at offset `data_offset`.
#
#   5. Integration with search_fast: an `try_offset_index_search`
#      helper is added that, when the predicate is bound AND the
#      offsets file is mmap'd, decodes only the subject + object
#      columns at the row-positions listed for each rg the presence
#      bitmap permits. Skipped entirely otherwise.
#
#      Mem5 owns search_fast itself; this patch wraps that function
#      so any direct-path query that flows through cottas_ondisk_search
#      benefits without needing Mem5 changes. We replace the body of
#      search_fast with: "if offset-index path applicable, dispatch
#      there; else fall through to the existing per-rg full-decode
#      walk." If the offsets file isn't present (e.g. companion-build
#      hasn't run on this corpus), control flows through unchanged.
#
# Rule #15: writer + reader are I/O glue + memory layout only. No new
# RDF/SPARQL semantics: row positions are byte-identical to "rows
# whose predicate token equals P". The format is documented above
# and (as a follow-up) belongs in F* as
# RDF.CottasStore.OnDiskOffsetIdx.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping lamed3 offset-idx patch" >&2
  exit 0
fi

# Sanity: prior Vav3 patch must have run first (we depend on the
# Cottas_companion_boot module + Vav3_mmap helpers).
if ! grep -q 'vav3: Cottas_companion_writer installed' "$FILE"; then
  echo "  Warning: lamed3 patch needs Vav3 boot/writer module;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh must run first." >&2
  exit 0
fi

if grep -q 'lamed3: Cottas_offset_idx installed' "$FILE"; then
  echo "  Lamed3 offset-index patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ---------------------------------------------------------------------
# Step 1: Insert Cottas_offset_idx writer/reader module BEFORE
# Cottas_ondisk_runtime so the runtime's search_fast dispatcher can
# call into it. Cottas_offset_idx itself only references modules
# already defined (Parquet_Footer, RDF_CottasStore_OnDiskIndex) and
# avoids forward references to Cottas_companion_writer by inlining
# the .dict / .presence / .offsets path computations.
# ---------------------------------------------------------------------

offset_module = r'''
(* lamed3: Cottas_offset_idx installed (issue #100, 2026-04-26).
   Per-(rg, pred_id) row-position index. Sibling .p.offsets file:
     [ magic 'COTO' u32 | version u32 | num_rgs u32 | num_preds u32 ]
     [ rg_offsets : u64 array, length num_rgs * num_preds + 1 ]
     [ data : u32[] row positions, ascending, packed ]
   Saves the predicate-column decode on every bound-predicate query.
   Built once, mmap'd forever. *)
module Cottas_offset_idx = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let offsets_magic : pint = 0x4f544f43  (* 'COTO' little-endian *)
  let layout_version : pint = 1
  let header_size : pint = 16  (* 4 u32 fields *)

  let offsets_path (cottas_path : string) : string =
    cottas_path ^ ".p.offsets"

  let write_u32_le buf (v : pint) =
    Buffer.add_char buf (Stdlib.Char.chr (v land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 8) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 16) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 24) land 0xff))

  let write_u64_le buf (v : pint) =
    write_u32_le buf (v land 0xffffffff);
    write_u32_le buf ((v lsr 32) land 0xffffffff)

  let atomic_write (path : string) (data : string) : unit =
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc data;
    flush oc;
    (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
    close_out oc;
    Sys.rename tmp path

  (* Build the offsets file by walking the predicate column once per rg.
     Requires the predicate dict's tok_to_id mapping (as a Hashtbl)
     so we can encode each token to its dict id during the walk. *)
  let build_offsets_file (cottas_path : string)
    (pred_tok_to_id : (string, pint) Hashtbl.t)
    (num_rgs : pint) (num_preds : pint) : unit =
    let opath = offsets_path cottas_path in
    Printf.eprintf "[lamed3-trace] building offsets file %s (num_rgs=%d num_preds=%d)\n%!"
      opath num_rgs num_preds;
    let t0 = Unix.gettimeofday () in
    (* Per-(rg, pred) -> row-position list. We accumulate as growable
       int arrays; flatten + write at the end. We explicitly use
       Stdlib.Array because `open Prims` at the top of this file
       shadows `array` with `Prims.array`. *)
    let buckets =
      Stdlib.Array.make_matrix num_rgs num_preds (Stdlib.Array.make 0 0) in
    let bucket_lens =
      Stdlib.Array.make_matrix num_rgs num_preds 0 in
    let push_pos rg pred_id pos =
      let cur = buckets.(rg).(pred_id) in
      let n = bucket_lens.(rg).(pred_id) in
      let cap = Stdlib.Array.length cur in
      let arr =
        if n < cap then cur
        else
          let new_cap = if cap = 0 then 8 else cap * 2 in
          let na = Stdlib.Array.make new_cap 0 in
          if cap > 0 then Stdlib.Array.blit cur 0 na 0 cap;
          buckets.(rg).(pred_id) <- na;
          na
      in
      arr.(n) <- pos;
      bucket_lens.(rg).(pred_id) <- n + 1
    in
    for rg = 0 to num_rgs - 1 do
      let t_rg = Unix.gettimeofday () in
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group
               cottas_path (Z.of_int rg) Z.one with
       | FStar_Pervasives_Native.None ->
         Printf.eprintf "[lamed3-WARN] offsets-build: rg=%d predicate decode failed\n%!" rg
       | FStar_Pervasives_Native.Some lst ->
         (* lst is a list of `string option`. Walk with index. *)
         let row = ref 0 in
         List.iter (function
           | FStar_Pervasives_Native.None -> incr row
           | FStar_Pervasives_Native.Some raw ->
             (match Hashtbl.find_opt pred_tok_to_id raw with
              | None ->
                Printf.eprintf "[lamed3-WARN] offsets-build: rg=%d row=%d unknown predicate token %s\n%!"
                  rg !row raw
              | Some pred_id ->
                if pred_id >= 0 && pred_id < num_preds then
                  push_pos rg pred_id !row
                else
                  Printf.eprintf "[lamed3-WARN] offsets-build: pred_id %d out of range\n%!" pred_id);
             incr row) lst);
      if rg = 0 || rg = num_rgs - 1 || rg mod 5 = 0 then
        Printf.eprintf "[lamed3-trace] offsets-build rg=%d/%d (%.2fs this rg)\n%!"
          rg num_rgs (Unix.gettimeofday () -. t_rg)
    done;
    Printf.eprintf "[lamed3-trace] offsets-build columnscan done in %.2fs\n%!"
      (Unix.gettimeofday () -. t0);
    (* Build the file. Header (16 bytes) + rg_offsets (8 bytes each,
       length num_rgs*num_preds+1) + data (4 bytes per row position). *)
    let n_index = num_rgs * num_preds + 1 in
    let index_size = 8 * n_index in
    let data_offset0 = header_size + index_size in
    (* First pass: compute byte offset for every (rg, pred) cell. *)
    let rg_offsets = Stdlib.Array.make n_index 0 in
    let cur = ref data_offset0 in
    for rg = 0 to num_rgs - 1 do
      for p = 0 to num_preds - 1 do
        rg_offsets.(rg * num_preds + p) <- !cur;
        cur := !cur + 4 * bucket_lens.(rg).(p)
      done
    done;
    rg_offsets.(num_rgs * num_preds) <- !cur;
    let total_size = !cur in
    Printf.eprintf "[lamed3-trace] offsets-build computed total_size=%d bytes (%.1f MB)\n%!"
      total_size (float_of_int total_size /. (1024.0 *. 1024.0));
    let buf = Buffer.create total_size in
    (* Header. *)
    write_u32_le buf offsets_magic;
    write_u32_le buf layout_version;
    write_u32_le buf num_rgs;
    write_u32_le buf num_preds;
    (* Index. *)
    for i = 0 to n_index - 1 do
      write_u64_le buf rg_offsets.(i)
    done;
    (* Data. *)
    for rg = 0 to num_rgs - 1 do
      for p = 0 to num_preds - 1 do
        let arr = buckets.(rg).(p) in
        let n = bucket_lens.(rg).(p) in
        for i = 0 to n - 1 do
          write_u32_le buf (Stdlib.Array.unsafe_get arr i)
        done
      done
    done;
    let t1 = Unix.gettimeofday () in
    atomic_write opath (Buffer.contents buf);
    let t2 = Unix.gettimeofday () in
    let stat_size = try (Unix.stat opath).Unix.st_size with _ -> -1 in
    Printf.eprintf "[lamed3-trace] offsets-build wrote %s (Nbytes=%d) in %.2fs (build %.2fs + write %.2fs)\n%!"
      opath stat_size (t2 -. t0) (t1 -. t0) (t2 -. t1)

  (* ---- Reader. ---- *)

  (* Per-path cached header + mmap view. *)
  type idx_header = {
    ih_num_rgs : pint;
    ih_num_preds : pint;
    ih_index_offset : pint;  (* always 16 *)
    ih_data_offset : pint;
  }

  let header_cache : (string, idx_header) Hashtbl.t = Hashtbl.create 17

  let read_header (cottas_path : string) : idx_header option =
    let opath = offsets_path cottas_path in
    match Hashtbl.find_opt header_cache opath with
    | Some h -> Some h
    | None ->
      match RDF_CottasStore_OnDiskIndex.Vav3_mmap.try_open_mmap opath with
      | None -> None
      | Some _size ->
        match Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views opath with
        | None -> None
        | Some v ->
          let mv_data = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
          let mv_size = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_size in
          if mv_size < header_size then begin
            Printf.eprintf "[lamed3-WARN] offsets file %s too small (%d bytes)\n%!" opath mv_size;
            None
          end else
            let g i = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data i) in
            let read_u32 off =
              let b0 = g off in
              let b1 = g (off+1) in
              let b2 = g (off+2) in
              let b3 = g (off+3) in
              b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
            let magic = read_u32 0 in
            let ver   = read_u32 4 in
            if magic <> offsets_magic || ver <> layout_version then begin
              Printf.eprintf "[lamed3-WARN] offsets file %s bad magic/ver (0x%x ver=%d)\n%!"
                opath magic ver;
              None
            end else
              let num_rgs   = read_u32 8 in
              let num_preds = read_u32 12 in
              let index_off = header_size in
              let data_off  = index_off + 8 * (num_rgs * num_preds + 1) in
              let h = {
                ih_num_rgs = num_rgs;
                ih_num_preds = num_preds;
                ih_index_offset = index_off;
                ih_data_offset = data_off;
              } in
              Hashtbl.replace header_cache opath h;
              Printf.eprintf "[lamed3-trace] offsets reader: %s mapped (rgs=%d preds=%d data_off=%d total=%d)\n%!"
                opath num_rgs num_preds data_off mv_size;
              Some h

  (* Returns Some [|row_pos; ...|] (length 0 OK), or None if the file
     is absent / mismatched / out-of-range. The returned type is
     Stdlib's `int array`; we annotate with explicit `Stdlib.Array.t`
     because `open Prims` shadows `array`. *)
  let row_positions_for (cottas_path : string) (rg : pint) (pred_id : pint)
    : pint Stdlib.Array.t option =
    match read_header cottas_path with
    | None -> None
    | Some h ->
      if rg < 0 || rg >= h.ih_num_rgs || pred_id < 0 || pred_id >= h.ih_num_preds
      then None
      else
        let opath = offsets_path cottas_path in
        match Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views opath with
        | None -> None
        | Some v ->
          let mv_data = v.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
          let g i = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data i) in
          let read_u32 off =
            let b0 = g off in
            let b1 = g (off+1) in
            let b2 = g (off+2) in
            let b3 = g (off+3) in
            b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
          let read_u64 off =
            let lo = read_u32 off in
            let hi = read_u32 (off + 4) in
            lo lor (hi lsl 32) in
          let cell_idx = rg * h.ih_num_preds + pred_id in
          let start_off = read_u64 (h.ih_index_offset + 8 * cell_idx) in
          let end_off   = read_u64 (h.ih_index_offset + 8 * (cell_idx + 1)) in
          if end_off < start_off then None
          else
            let nbytes = end_off - start_off in
            let n = nbytes / 4 in
            let arr = Stdlib.Array.make n 0 in
            for i = 0 to n - 1 do
              Stdlib.Array.unsafe_set arr i (read_u32 (start_off + 4 * i))
            done;
            Some arr

  (* Build the offsets file if absent. Reads the predicate dict's
     tok_to_id mapping from the F* extracted reader (so id assignment
     matches the on-disk dict ordering). Called from boot (after Vav3
     companions are present). *)
  let ensure_offsets_built (cottas_path : string) : unit =
    let opath = offsets_path cottas_path in
    if Sys.file_exists opath && (try (Unix.stat opath).Unix.st_size with _ -> 0) >= header_size then begin
      Printf.eprintf "[lamed3-trace] offsets file present at %s, skipping build\n%!" opath
    end else begin
      Printf.eprintf "[lamed3-trace] offsets file absent; building\n%!";
      (* Read the predicate dict header to get num_predicates AND a
         tok_to_id Hashtbl built from the dict's ordering. We inline
         the path computation (Cottas_companion_writer.dict_path is
         forward-referenced from this module's earlier position). *)
      let dpath = cottas_path ^ ".p.dict" in
      match RDF_CottasStore_OnDiskIndex.read_dict_header dpath with
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[lamed3-FATAL] offsets-build: cannot read predicate dict header at %s\n%!" dpath
      | FStar_Pervasives_Native.Some dh ->
        let n_preds = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
        (* Read the predicate presence header to get num_rgs. *)
        let ppath = cottas_path ^ ".p.presence" in
        let n_rgs = match RDF_CottasStore_OnDiskIndex.read_presence_header ppath with
          | FStar_Pervasives_Native.Some ph ->
            Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs
          | FStar_Pervasives_Native.None ->
            (match Parquet_Footer.probe_parquet_row_group_count cottas_path with
             | FStar_Pervasives_Native.None -> 0
             | FStar_Pervasives_Native.Some n -> Z.to_int n) in
        Printf.eprintf "[lamed3-trace] offsets-build: n_rgs=%d n_preds=%d\n%!" n_rgs n_preds;
        (* Build a tok_to_id Hashtbl by reading every dict entry. The
           dict was sorted ascending so id i corresponds to the i'th
           token in lex order; we use dict_decode_token to map. *)
        let tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create (n_preds * 2 + 17) in
        for id = 0 to n_preds - 1 do
          match RDF_CottasStore_OnDiskIndex.dict_decode_token
                  dpath dh (Z.of_int id) with
          | FStar_Pervasives_Native.Some raw ->
            Hashtbl.replace tok_to_id raw id
          | FStar_Pervasives_Native.None ->
            Printf.eprintf "[lamed3-WARN] offsets-build: dict_decode_token failed for id=%d\n%!" id
        done;
        Printf.eprintf "[lamed3-trace] offsets-build: built tok_to_id (size=%d)\n%!"
          (Hashtbl.length tok_to_id);
        if n_rgs > 0 && n_preds > 0 && Hashtbl.length tok_to_id > 0 then
          build_offsets_file cottas_path tok_to_id n_rgs n_preds
        else
          Printf.eprintf "[lamed3-WARN] offsets-build: skipping (n_rgs=%d n_preds=%d tok_to_id=%d)\n%!"
            n_rgs n_preds (Hashtbl.length tok_to_id)
    end;
    (* Open mmap view for runtime reads. *)
    (match read_header cottas_path with
     | None ->
       Printf.eprintf "[lamed3-WARN] offsets-build: post-build read_header failed\n%!"
     | Some _ -> ())
end
'''

# Insert BEFORE `module Cottas_ondisk_runtime = struct` so the runtime
# module's search_fast dispatcher can reference Cottas_offset_idx.
runtime_anchor = '''module Cottas_ondisk_runtime = struct'''
if runtime_anchor in content:
    content = content.replace(runtime_anchor, offset_module + '\n' + runtime_anchor, 1)
    sys.stderr.write("  [lamed3] Cottas_offset_idx inserted before Cottas_ondisk_runtime\n")
else:
    sys.stderr.write("  [lamed3] WARN: Cottas_ondisk_runtime anchor not found; appending at end\n")
    content += offset_module

# ---------------------------------------------------------------------
# Step 2: Hook ensure_offsets_built into prewarm_via_companions so it
# runs right after the dict+presence companions are validated/built.
# ---------------------------------------------------------------------

old_prewarm_marker = '''    Cottas_ondisk_lazy.mark_subj_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_pred_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_obj_loaded   cottas_path;
    Cottas_ondisk_lazy.mark_graph_loaded cottas_path;'''

new_prewarm_marker = '''    Cottas_ondisk_lazy.mark_subj_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_pred_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_obj_loaded   cottas_path;
    Cottas_ondisk_lazy.mark_graph_loaded cottas_path;
    (* lamed3: build / mmap the predicate row-offset companion. *)
    (try Cottas_offset_idx.ensure_offsets_built cottas_path
     with e ->
       Printf.eprintf "[lamed3-WARN] ensure_offsets_built raised: %s\n%!"
         (Printexc.to_string e));'''

if old_prewarm_marker in content:
    content = content.replace(old_prewarm_marker, new_prewarm_marker, 1)
    sys.stderr.write("  [lamed3] hooked ensure_offsets_built into prewarm_via_companions\n")
else:
    sys.stderr.write("  [lamed3] WARN: prewarm_via_companions marker not found; offsets file will not auto-build at boot\n")

# ---------------------------------------------------------------------
# Steps 3 + 4 (reader half + dispatcher wrapping) RETIRED — Yod7 audit
# 2026-04-26 confirmed they were dead code post-q03-bypass; rename
# pivot patch (5f64a16) decoupled the search_fast/limited/estimate_fast
# rename to *_inner so the dispatcher wrapping was no longer needed.
# Removing here saves ~600 lines of dead OCaml semantic logic from
# being injected into the runtime module on every extract.
#
# `Cottas_offset_idx.read_header` and `row_positions_for` remain
# defined inside Cottas_offset_idx (Step 1) because they're library
# functions; nothing CALLS them from the runtime now, so they're
# unreferenced bindings — harmless. The on-disk `.p.offsets` file
# still gets built on boot via Step 2's hook.
#
# When a future F* `RDF.CottasStore.OnDiskOffsetIdx.fst` reader lands
# (issue #105 follow-up), the calling shim will go in a fresh patch.
# ---------------------------------------------------------------------

path.write_text(content)
sys.stderr.write("  [lamed3] applied (writer-only): Cottas_offset_idx writer + boot hook; reader half retired per Yod7 audit\n")
PYEOF

echo "  Lamed3 offset-index patch applied (writer-only)."
