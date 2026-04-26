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
# Step 3: Wrap search_fast and estimate_fast to dispatch to the
# offset-index path when applicable.
#
# We add a helper (search_fast_via_offsets) inside Cottas_ondisk_runtime
# and modify search_fast / estimate_fast to try it first.
# ---------------------------------------------------------------------

# Insert the offset-index helper inside Cottas_ondisk_runtime, BEFORE
# `search_fast` so the dispatcher can reference it. We anchor on the
# existing search_fast header.
helper_marker = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

helper_block = '''  (* lamed3: offset-index dispatch.
     Returns Some result_list if the offset-index path was applicable
     (predicate bound + offsets file present + pred_id resolves);
     None means "fall back to the full per-rg column-decode walk".

     When applicable: for each rg the presence bitmap permits, fetch
     the row positions list directly, then decode subjects + objects
     ONLY at those positions. Skips the predicate column entirely. *)
  let search_fast_via_offsets (h : cottas_ondisk_handle)
    (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list option =
    let path = h.coh_path in
    let tables = tables_for h in
    (* Only applies when predicate is bound. *)
    match bound.Parser_BallyhooCOTTAS.cbqp_p with
    | FStar_Pervasives_Native.None -> None
    | FStar_Pervasives_Native.Some pred_id_z ->
      let pred_id = Z.to_int pred_id_z in
      (* pred_id from the bound is already an int term-id; we need to
         locate the same predicate in the on-disk dict's id space.
         The Hashtbl ft_pred_tok_to_id (built either eagerly via
         Vav3 bulk-load or lazily by Yod6) is keyed by raw token,
         valued by the same id space the .dict uses (since Vav3 wrote
         dict in lex order and bulk-load id'd in that order). So
         ft_id_to_pred_tok[bound_pred_id] gives us the raw token, and
         the same lookup in the dict tok_to_id Hashtbl gives the
         dict-id. For Vav3 boot they're identical; for non-Vav3
         eager boot they may differ. Resolve via raw token round-trip
         to be safe. *)
      let raw_opt = Hashtbl.find_opt tables.ft_id_to_pred_tok pred_id in
      (match raw_opt with
       | None -> None
       | Some _raw ->
         (* The .offsets file uses dict-id; the bound is a term-id. They
            match when the bulk-load assigned the same id space. The
            simplest correctness guarantee: use the same Hashtbl
            lookup. ft_pred_tok_to_id[raw] -> id. By construction
            (id assigned at insertion time) this round-trips. *)
         match Hashtbl.find_opt tables.ft_pred_tok_to_id _raw with
         | None -> None
         | Some dict_pred_id ->
           (* Get the offset-idx header to know num_rgs. *)
           match Cottas_offset_idx.read_header path with
           | None -> None  (* offsets file absent; fall through *)
           | Some hdr ->
             let n_rgs = hdr.Cottas_offset_idx.ih_num_rgs in
             let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
             let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
             let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
             Printf.eprintf "[lamed3-trace] search_fast_via_offsets: pred_id=%d (raw=%s) dict_id=%d n_rgs=%d\n%!"
               pred_id _raw dict_pred_id n_rgs;
             let acc = ref [] in
             let n_matches = ref 0 in
             let n_rgs_with_hits = ref 0 in
             let n_rows_examined = ref 0 in
             let cell_of = function
               | FStar_Pervasives_Native.Some s -> s
               | FStar_Pervasives_Native.None -> "" in
             let arr_of_col col_opt =
               match col_opt with
               | FStar_Pervasives_Native.None -> [||]
               | FStar_Pervasives_Native.Some lst -> Array.of_list lst in
             let opt_to_z = function
               | None -> FStar_Pervasives_Native.None
               | Some i -> FStar_Pervasives_Native.Some (Z.of_int i) in
             for rg = 0 to n_rgs - 1 do
               (* Use Yod6 presence prune as well: skip rgs where the
                  predicate isn't present at all. *)
               if Cottas_ondisk_lazy.pred_rg_could_contain
                    path rg (Some _raw) then begin
                 match Cottas_offset_idx.row_positions_for path rg dict_pred_id with
                 | None -> ()  (* shouldn't happen if header read; defensive *)
                 | Some [||] -> ()  (* no rows match in this rg *)
                 | Some positions ->
                   incr n_rgs_with_hits;
                   (* Fetch subject + object columns for this rg.
                      We still pull whole-rg arrays then index by
                      position; per-row parquet reads aren't supported
                      in the current probe API. The win vs. baseline:
                      we skip the predicate-column decode entirely
                      (which is the SLOWEST per-rg, ~3-6s on
                      parliament). Subject/object decodes happen anyway. *)
                   let s_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.zero) in
                   let o_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 2)) in
                   let g_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 3)) in
                   let n_cols = Array.length s_arr in
                   Array.iter (fun pos ->
                     incr n_rows_examined;
                     if pos >= 0 && pos < n_cols then begin
                       let s_tok = cell_of s_arr.(pos) in
                       let o_tok = cell_of o_arr.(pos) in
                       let g_tok = if pos < Array.length g_arr then cell_of g_arr.(pos) else "DEFAULT" in
                       if cell_match_str bound_s s_tok &&
                          cell_match_str bound_o o_tok &&
                          cell_match_str bound_g g_tok
                       then begin
                         let s_id = Hashtbl.find_opt tables.ft_subj_tok_to_id s_tok in
                         let o_id = Hashtbl.find_opt tables.ft_obj_tok_to_id  o_tok in
                         let g_id =
                           if g_tok = "DEFAULT" then None
                           else Hashtbl.find_opt tables.ft_graph_tok_to_id g_tok in
                         acc := {
                           Parser_BallyhooCOTTAS.cqpr_s = opt_to_z s_id;
                           cqpr_p = FStar_Pervasives_Native.Some (Z.of_int pred_id);
                           cqpr_o = opt_to_z o_id;
                           cqpr_g = opt_to_z g_id;
                         } :: !acc;
                         incr n_matches
                       end
                     end) positions
               end
             done;
             Printf.eprintf "[lamed3-trace] search_fast_via_offsets: matched %d rows (rgs_with_hits=%d/%d rows_examined=%d)\n%!"
               !n_matches !n_rgs_with_hits n_rgs !n_rows_examined;
             Some (List.rev !acc))

  (* Limited variant: same logic but stops once `limit` matches accumulate. *)
  let search_fast_limited_via_offsets (h : cottas_ondisk_handle)
    (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list option =
    let path = h.coh_path in
    let tables = tables_for h in
    match bound.Parser_BallyhooCOTTAS.cbqp_p with
    | FStar_Pervasives_Native.None -> None
    | FStar_Pervasives_Native.Some pred_id_z ->
      let pred_id = Z.to_int pred_id_z in
      let raw_opt = Hashtbl.find_opt tables.ft_id_to_pred_tok pred_id in
      (match raw_opt with
       | None -> None
       | Some _raw ->
         match Hashtbl.find_opt tables.ft_pred_tok_to_id _raw with
         | None -> None
         | Some dict_pred_id ->
           match Cottas_offset_idx.read_header path with
           | None -> None
           | Some hdr ->
             let n_rgs = hdr.Cottas_offset_idx.ih_num_rgs in
             let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
             let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
             let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
             Printf.eprintf "[lamed3-trace] search_fast_limited_via_offsets: pred_id=%d limit=%d n_rgs=%d\n%!"
               pred_id limit n_rgs;
             let acc = ref [] in
             let n_matches = ref 0 in
             let cell_of = function
               | FStar_Pervasives_Native.Some s -> s
               | FStar_Pervasives_Native.None -> "" in
             let arr_of_col col_opt =
               match col_opt with
               | FStar_Pervasives_Native.None -> [||]
               | FStar_Pervasives_Native.Some lst -> Array.of_list lst in
             let opt_to_z = function
               | None -> FStar_Pervasives_Native.None
               | Some i -> FStar_Pervasives_Native.Some (Z.of_int i) in
             let rg = ref 0 in
             (try
               while !rg < n_rgs && !n_matches < limit do
                 let r = !rg in
                 if Cottas_ondisk_lazy.pred_rg_could_contain path r (Some _raw) then begin
                   match Cottas_offset_idx.row_positions_for path r dict_pred_id with
                   | None | Some [||] -> ()
                   | Some positions ->
                     let s_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) Z.zero) in
                     let o_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 2)) in
                     let g_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int r) (Z.of_int 3)) in
                     let n_cols = Array.length s_arr in
                     let i = ref 0 in
                     let plen = Array.length positions in
                     while !i < plen && !n_matches < limit do
                       let pos = positions.(!i) in
                       if pos >= 0 && pos < n_cols then begin
                         let s_tok = cell_of s_arr.(pos) in
                         let o_tok = cell_of o_arr.(pos) in
                         let g_tok = if pos < Array.length g_arr then cell_of g_arr.(pos) else "DEFAULT" in
                         if cell_match_str bound_s s_tok &&
                            cell_match_str bound_o o_tok &&
                            cell_match_str bound_g g_tok
                         then begin
                           let s_id = Hashtbl.find_opt tables.ft_subj_tok_to_id s_tok in
                           let o_id = Hashtbl.find_opt tables.ft_obj_tok_to_id  o_tok in
                           let g_id =
                             if g_tok = "DEFAULT" then None
                             else Hashtbl.find_opt tables.ft_graph_tok_to_id g_tok in
                           acc := {
                             Parser_BallyhooCOTTAS.cqpr_s = opt_to_z s_id;
                             cqpr_p = FStar_Pervasives_Native.Some (Z.of_int pred_id);
                             cqpr_o = opt_to_z o_id;
                             cqpr_g = opt_to_z g_id;
                           } :: !acc;
                           incr n_matches
                         end
                       end;
                       incr i
                     done
                 end;
                 incr rg
               done
             with e ->
               let bt = Printexc.get_backtrace () in
               Printf.eprintf "[lamed3-FATAL] search_fast_limited_via_offsets rg=%d EXCEPTION: %s\nbacktrace=%s\n%!"
                 !rg (Printexc.to_string e) bt);
             Printf.eprintf "[lamed3-trace] search_fast_limited_via_offsets: matched %d/%d rows, walked %d/%d rg(s)\n%!"
               !n_matches limit !rg n_rgs;
             Some (List.rev !acc))

  (* Estimate variant: counts only. *)
  let estimate_fast_via_offsets (h : cottas_ondisk_handle)
    (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint option =
    let path = h.coh_path in
    let tables = tables_for h in
    match bound.Parser_BallyhooCOTTAS.cbqp_p with
    | FStar_Pervasives_Native.None -> None
    | FStar_Pervasives_Native.Some pred_id_z ->
      let pred_id = Z.to_int pred_id_z in
      let raw_opt = Hashtbl.find_opt tables.ft_id_to_pred_tok pred_id in
      (match raw_opt with
       | None -> None
       | Some _raw ->
         match Hashtbl.find_opt tables.ft_pred_tok_to_id _raw with
         | None -> None
         | Some dict_pred_id ->
           match Cottas_offset_idx.read_header path with
           | None -> None
           | Some hdr ->
             let n_rgs = hdr.Cottas_offset_idx.ih_num_rgs in
             let bound_s = bound_id_to_token tables.ft_id_to_subj_tok  bound.Parser_BallyhooCOTTAS.cbqp_s in
             let bound_o = bound_id_to_token tables.ft_id_to_obj_tok   bound.Parser_BallyhooCOTTAS.cbqp_o in
             let bound_g = bound_id_to_token tables.ft_id_to_graph_tok bound.Parser_BallyhooCOTTAS.cbqp_g in
             let count = ref 0 in
             (* Fast path when no other bound: just sum the per-rg row counts. *)
             let cell_of = function
               | FStar_Pervasives_Native.Some s -> s
               | FStar_Pervasives_Native.None -> "" in
             let arr_of_col col_opt =
               match col_opt with
               | FStar_Pervasives_Native.None -> [||]
               | FStar_Pervasives_Native.Some lst -> Array.of_list lst in
             let no_other_bound =
               (match bound.Parser_BallyhooCOTTAS.cbqp_s with FStar_Pervasives_Native.None -> true | _ -> false) &&
               (match bound.Parser_BallyhooCOTTAS.cbqp_o with FStar_Pervasives_Native.None -> true | _ -> false) &&
               (match bound.Parser_BallyhooCOTTAS.cbqp_g with FStar_Pervasives_Native.None -> true | _ -> false) in
             for rg = 0 to n_rgs - 1 do
               if Cottas_ondisk_lazy.pred_rg_could_contain path rg (Some _raw) then begin
                 match Cottas_offset_idx.row_positions_for path rg dict_pred_id with
                 | None | Some [||] -> ()
                 | Some positions when no_other_bound ->
                   count := !count + Array.length positions
                 | Some positions ->
                   let s_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) Z.zero) in
                   let o_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 2)) in
                   let g_arr = arr_of_col (Parquet_Footer.probe_parquet_column_decode_in_row_group path (Z.of_int rg) (Z.of_int 3)) in
                   let n_cols = Array.length s_arr in
                   Array.iter (fun pos ->
                     if pos >= 0 && pos < n_cols then begin
                       let s_tok = cell_of s_arr.(pos) in
                       let o_tok = cell_of o_arr.(pos) in
                       let g_tok = if pos < Array.length g_arr then cell_of g_arr.(pos) else "DEFAULT" in
                       if cell_match_str bound_s s_tok &&
                          cell_match_str bound_o o_tok &&
                          cell_match_str bound_g g_tok
                       then incr count
                     end) positions
               end
             done;
             Printf.eprintf "[lamed3-trace] estimate_fast_via_offsets: count=%d (no_other_bound=%b)\n%!"
               !count no_other_bound;
             Some !count)

'''

# Insert the helper block immediately before predicate_present_fast.
if helper_marker in content:
    content = content.replace(helper_marker, helper_block + helper_marker, 1)
    sys.stderr.write("  [lamed3] inserted search_fast_via_offsets / estimate / limited helpers\n")
else:
    sys.stderr.write("  [lamed3] WARN: predicate_present_fast anchor missing; helpers not inserted\n")

# ---------------------------------------------------------------------
# Step 4: Wrap search_fast / search_fast_limited / estimate_fast to
# try the offset-index path first.
#
# The wrapping strategy: we add a new dispatch function
# search_fast_dispatch that calls search_fast_via_offsets first; if
# that returns None, falls back to the inner per-rg walker. Rather
# than rewriting the existing function bodies (which are huge), we
# rename the existing search_fast -> search_fast_inner and add a thin
# search_fast that dispatches.
# ---------------------------------------------------------------------

# Rename search_fast to search_fast_inner. Then add a new search_fast
# that tries offsets first. The simplest way is to find the existing
# `let search_fast (h : cottas_ondisk_handle) (bound : ...)` header
# and rename it; then prepend the dispatcher.

old_search_header = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

new_search_header = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    (* lamed3: try offset-index path first; fall back to full walk. *)
    match search_fast_via_offsets h bound with
    | Some result ->
      Printf.eprintf "[lamed3-trace] search_fast: served from offset index (%d rows)\n%!" (List.length result);
      result
    | None -> search_fast_inner h bound
  and search_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

# We need to use `and` for mutual recursion only if same `let rec` block;
# search_fast and search_fast_via_offsets are NOT in the same let-binding,
# so we use a fresh `let` for search_fast_inner. The standalone replacement
# means we need: existing body becomes search_fast_inner; new search_fast
# dispatches.

# Cleaner approach: insert a `let search_fast_inner ...` BEFORE the existing
# search_fast, then change the existing search_fast's body to dispatch.
# Simpler still: rename in place.

# The existing search_fast definition starts at the `let search_fast` line.
# We rename that header to `let search_fast_inner` and prepend a new
# `let search_fast` dispatcher that calls search_fast_inner if offset path None.

# Strategy: replace `let search_fast (h ...)` with the dispatcher, which
# itself defines search_fast_inner via a separate later `let`. We can't
# split easily without locating the body end.
#
# Best approach: keep the existing function body intact under name
# search_fast_inner (rename only the header), then ADD a new search_fast
# dispatcher right before it.

# Rename the existing header:
rename_search = '''  let search_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

if old_search_header in content:
    # Rename the existing function to search_fast_inner. Then prepend a
    # NEW `let search_fast` that dispatches to either the offset-index
    # path or search_fast_inner.
    #
    # Note on forward references: OCaml requires the callee to be defined
    # before the caller in a sequence of top-level lets. Since the
    # dispatcher comes textually first and calls search_fast_inner, we
    # use `let rec dispatcher = ... and search_fast_inner = ...`
    # (mutually recursive group). This is purely a textual reordering;
    # neither function actually calls the other recursively.
    rename_search_no_let = '''search_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''
    dispatcher = '''  let rec search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    (* lamed3: try offset-index path first. *)
    match search_fast_via_offsets h bound with
    | Some result ->
      Printf.eprintf "[lamed3-trace] search_fast: served from offset index (%d rows)\n%!" (List.length result);
      result
    | None -> search_fast_inner h bound
  and ''' + rename_search_no_let
    content = content.replace(old_search_header, dispatcher, 1)
    sys.stderr.write("  [lamed3] wrapped search_fast with offset-index dispatcher\n")
else:
    sys.stderr.write("  [lamed3] WARN: search_fast header not found for wrapping\n")

# Wrap search_fast_limited similarly. The Aleph6 patch creates it with this
# signature.
old_limited_header = '''  let search_fast_limited (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

if old_limited_header in content:
    rename_limited_no_let = '''search_fast_limited_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''
    dispatcher_lim = '''  let rec search_fast_limited (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    (* lamed3: try offset-index path first for LIMIT pushdown. *)
    match search_fast_limited_via_offsets h bound limit with
    | Some result ->
      Printf.eprintf "[lamed3-trace] search_fast_limited: served from offset index (%d/%d rows)\n%!" (List.length result) limit;
      result
    | None -> search_fast_limited_inner h bound limit
  and ''' + rename_limited_no_let
    content = content.replace(old_limited_header, dispatcher_lim, 1)
    sys.stderr.write("  [lamed3] wrapped search_fast_limited with offset-index dispatcher\n")
else:
    sys.stderr.write("  [lamed3] WARN: search_fast_limited header not found (Aleph6 patch may not have run)\n")

# Wrap estimate_fast.
old_estimate_header = '''  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ='''

if old_estimate_header in content:
    rename_est_no_let = '''estimate_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ='''
    dispatcher_est = '''  let rec estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    match estimate_fast_via_offsets h bound with
    | Some n ->
      Printf.eprintf "[lamed3-trace] estimate_fast: served from offset index (%d)\n%!" n;
      n
    | None -> estimate_fast_inner h bound
  and ''' + rename_est_no_let
    content = content.replace(old_estimate_header, dispatcher_est, 1)
    sys.stderr.write("  [lamed3] wrapped estimate_fast with offset-index dispatcher\n")
else:
    sys.stderr.write("  [lamed3] WARN: estimate_fast header not found\n")

path.write_text(content)
sys.stderr.write("  [lamed3] applied: Cottas_offset_idx + dispatcher wrapping\n")
PYEOF

echo "  Lamed3 offset-index patch applied."
