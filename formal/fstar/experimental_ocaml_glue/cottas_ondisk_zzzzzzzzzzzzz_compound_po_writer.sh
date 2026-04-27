#!/bin/bash
# Compound (predicate, object) presence-bitmap WRITER for the on-disk
# COTTAS backend.  Issue #104, 2026-04-26.  Handle: nun4 (writer-only
# parallel patch; reader integration is a future, separate commit).
#
# What this patch does:
#
#   1. Adds a NEW companion file `<cottas>.po.presence` next to the
#      existing per-column `.{s,p,o,g}.{dict,presence}` siblings (and
#      the lamed3 `.p.offsets`). Encoded as a sparse-roaring sorted
#      (p_id, o_id) pair list per row group.
#
#   2. WRITER ONLY. This patch installs a single new OCaml module
#      `Cottas_compound_po_writer` (rule-#11(b) companion-file writer:
#      pure I/O glue, no decisions) and a single boot hook that calls
#      `ensure_compound_po_built` once after the existing per-column
#      writers + lamed3 offset-index. There is NO reader code here;
#      query results are unchanged. The companion file just sits on
#      disk waiting for the reader-redirect patch.
#
#   3. File format (little-endian throughout):
#
#        Header (20 bytes, no padding):
#          [ magic    : u32  'COPO' = 0x4f504f43 (LE) ]
#          [ version  : u32  layout version, currently 1 ]
#          [ num_rgs  : u32 ]
#          [ pred_dict_size : u32   cross-checked vs .p.dict header ]
#          [ obj_dict_size  : u32   cross-checked vs .o.dict header ]
#
#        Index:
#          [ rg_offsets : u64[num_rgs + 1]  byte offsets from start
#                                            of file into pair_data
#                                            section, with a trailing
#                                            sentinel = end of file. ]
#
#        Pair data (per rg, sorted lex (p_id, o_id)):
#          [ pairs : u64[]  per pair: bytes 0..3 = o_id (u32 LE),
#                                     bytes 4..7 = p_id (u32 LE)
#                           so the u64 read = (p_id << 32) | o_id
#                           and ascending u64 sort == lex (p_id, o_id). ]
#
#      The (rg_offsets[k], rg_offsets[k+1]) range of bytes IS the
#      packed pair-list for rg=k. Per-rg pair count =
#      (rg_offsets[k+1] - rg_offsets[k]) / 8.
#
#      Total header + index = 20 + 8 * (num_rgs + 1) bytes
#                           = 236 bytes for parliament's 26 rgs.
#
#   4. Why u64-per-pair (not packed u32 with bit-split)? Parliament's
#      232 preds × 956K objs fits a 24+24 split into u32, but a u64
#      removes the dict-size question entirely (preds ≤ 2^32, objs
#      ≤ 2^32). Cost: 2x the pair-data section vs u32 packing. For
#      parliament: ~3.14 M pair entries (worst case = total quads if
#      every pair distinct) × 8 = ~25 MB. Acceptable.
#
#   5. Token-id contract: (p_id, o_id) live in the same id-space as
#      Vav3's per-column `.p.dict` and `.o.dict` token ids. This is
#      the SAME id-space `RDF_CottasStore_PresenceBitmap.rg_could_contain_token`
#      consumes, ensuring the reader (future patch) can compose with
#      Psi3's per-column bitmap. The writer does NOT introduce a new
#      tokenisation: it reads the existing `.p.dict` / `.o.dict`
#      headers + per-token decode to build the same encode tables.
#
#   6. Idempotency:  skip rebuild when `.po.presence` exists and its
#      header's pred_dict_size / obj_dict_size match the corresponding
#      `.p.dict` / `.o.dict`.  Mismatch => rebuild (same discipline as
#      Vav3).
#
#   7. Boot hook: a single try/with block in
#      `Cottas_companion_boot.prewarm_via_companions`, inserted AFTER
#      the existing lamed3 hook. If the writer raises, log + continue
#      (writer is best-effort; reader path is absent so nothing else
#      depends on it this run).
#
# Rule #11(b): companion-file writer in OCaml glue is allowed when
# the reader path is in F* (or, here, deferred to a future F* module
# `RDF.CottasStore.CompoundPresenceBitmap.fst` per design doc).
# Rule #15: NO RDF/SPARQL semantic logic here. The writer enumerates
# byte-identical (p_id, o_id) tokens already produced by Vav3.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping compound-po writer patch" >&2
  exit 0
fi

# Sanity: prior Vav3 patch must have run first (we depend on the
# Cottas_companion_boot module + Vav3_mmap helpers + Cottas_companion_writer).
if ! grep -q 'vav3: Cottas_companion_writer installed' "$FILE"; then
  echo "  Warning: compound-po writer needs Vav3 boot/writer module;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh must run first." >&2
  exit 0
fi

if grep -q 'compound-po: Cottas_compound_po_writer installed' "$FILE"; then
  echo "  Compound-po writer patch already present."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ---------------------------------------------------------------------
# Step 1: Insert Cottas_compound_po_writer module BEFORE
# Cottas_companion_boot so the boot orchestrator can call into it.
# This module references RDF_CottasStore_OnDiskIndex (header readers
# + Vav3_mmap), Parquet_Footer (column decoders) — both already
# defined upstream of Cottas_companion_boot.
# ---------------------------------------------------------------------

writer_module = r'''
(* compound-po: Cottas_compound_po_writer installed (issue #104, 2026-04-26).

   Sibling .po.presence companion file: per-row-group sparse-roaring
   sorted (p_id, o_id) pair list. Format:

     [ magic 'COPO' u32 (0x4f504f43 LE) | version u32 | num_rgs u32 |
       pred_dict_size u32 | obj_dict_size u32 ]                   (20 bytes)
     [ rg_offsets : u64 array, length num_rgs + 1                ]
       rg_offsets[k]   = byte offset into file where rg k's pairs begin
       rg_offsets[k+1] = end offset (exclusive)
     [ pairs : u64[] sorted lex (p_id, o_id)
               per pair: u32-LE o_id then u32-LE p_id
               so u64-LE read = (p_id << 32) | o_id and ascending
               u64 sort == lex (p_id, o_id).                       ]

   WRITER ONLY this run. No reader code; query results are unchanged.
   Future reader patch (#104 follow-on) will redirect search_fast /
   estimate_fast to consult this file when both p and o are bound. *)
module Cottas_compound_po_writer = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let copo_magic : pint = 0x4f504f43  (* 'COPO' little-endian *)
  let layout_version : pint = 1
  let header_size : pint = 20  (* 5 u32 fields *)

  let compound_path (cottas_path : string) : string =
    cottas_path ^ ".po.presence"

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

  (* Build a token -> id Hashtbl from a column dict, by walking every
     dict entry. The dict was sorted ascending so id i corresponds to
     the i'th token in lex order (Vav3 invariant). Hashtbl size hint
     is 2x num_tokens to keep load factor low. *)
  let build_tok_to_id (dict_path : string)
    (dh : RDF_CottasStore_OnDiskIndex.dict_header)
    (n_tok : pint) : (string, pint) Hashtbl.t =
    let tab : (string, pint) Hashtbl.t = Hashtbl.create (n_tok * 2 + 17) in
    for id = 0 to n_tok - 1 do
      match RDF_CottasStore_OnDiskIndex.dict_decode_token
              dict_path dh (Z.of_int id) with
      | FStar_Pervasives_Native.Some raw -> Hashtbl.replace tab raw id
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[compound-po-WARN] tok_to_id build: id=%d decode failed in %s\n%!"
          id dict_path
    done;
    tab

  (* Returns true iff the existing .po.presence file has the right
     magic, version, num_rgs, pred_dict_size, obj_dict_size. Otherwise
     the file is stale (corpus reload, dict size changed) and a rebuild
     is needed. *)
  let existing_file_matches (cottas_path : string)
    (expected_num_rgs : pint)
    (expected_pred_dict_size : pint)
    (expected_obj_dict_size  : pint) : bool =
    let opath = compound_path cottas_path in
    if not (Sys.file_exists opath) then false
    else begin
      let sz = try (Unix.stat opath).Unix.st_size with _ -> 0 in
      if sz < header_size then false
      else begin
        let ic = open_in_bin opath in
        let buf = Stdlib.Bytes.create header_size in
        let n_read = try Stdlib.really_input ic buf 0 header_size; header_size
                     with End_of_file -> 0 in
        close_in ic;
        if n_read < header_size then false
        else
          let g i = Stdlib.Char.code (Stdlib.Bytes.unsafe_get buf i) in
          let read_u32 off =
            let b0 = g off in
            let b1 = g (off+1) in
            let b2 = g (off+2) in
            let b3 = g (off+3) in
            b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
          let magic = read_u32 0 in
          let ver   = read_u32 4 in
          let num_rgs = read_u32 8 in
          let pred_sz = read_u32 12 in
          let obj_sz  = read_u32 16 in
          let ok =
            magic = copo_magic &&
            ver = layout_version &&
            num_rgs = expected_num_rgs &&
            pred_sz = expected_pred_dict_size &&
            obj_sz  = expected_obj_dict_size in
          if not ok then
            Printf.eprintf "[compound-po-trace] existing %s header mismatch (magic=0x%x ver=%d rgs=%d pred=%d obj=%d vs exp rgs=%d pred=%d obj=%d) -> rebuild\n%!"
              opath magic ver num_rgs pred_sz obj_sz
              expected_num_rgs expected_pred_dict_size expected_obj_dict_size;
          ok
      end
    end

  (* Build the .po.presence file by walking the predicate + object
     columns of each rg in tandem and collecting distinct (p_id, o_id)
     pairs. Idempotent: skip if existing file's header matches.
     Returns unit; logs progress on stderr. *)
  let build_compound_po_file (cottas_path : string)
    (pred_tok_to_id : (string, pint) Hashtbl.t)
    (obj_tok_to_id  : (string, pint) Hashtbl.t)
    (num_rgs : pint) (pred_dict_size : pint) (obj_dict_size : pint) : unit =
    let opath = compound_path cottas_path in
    Printf.eprintf "[compound-po-trace] writing %s (num_rgs=%d pred_dict=%d obj_dict=%d)\n%!"
      opath num_rgs pred_dict_size obj_dict_size;
    let t0 = Unix.gettimeofday () in
    (* Per-rg sorted distinct pair set. We accumulate unique pair-codes
       (p_id << 32) | o_id into a Hashtbl per rg, then sort + emit.
       Memory: each rg has up to ~120 K rows on parliament; pairs are
       8 bytes raw, Hashtbl overhead ~3-4x means ~5 MB per rg, peak
       ~125 MB across all rgs concurrently. We instead collect rg-by-
       rg and write into a per-rg buffer to amortise that. *)
    let n_index = num_rgs + 1 in
    let index_size = 8 * n_index in
    let data_offset0 = header_size + index_size in
    (* Two passes: first collect per-rg sorted unique pair-codes; then
       compute byte offsets; then emit header + index + data. We hold
       one rg's pair codes at a time as Stdlib.Array. *)
    let per_rg_codes : pint Stdlib.Array.t Stdlib.Array.t =
      Stdlib.Array.make num_rgs (Stdlib.Array.make 0 0) in
    let total_pairs = ref 0 in
    for rg = 0 to num_rgs - 1 do
      let t_rg = Unix.gettimeofday () in
      (* Decode predicate column (col=1) and object column (col=2) for this rg. *)
      let p_col_opt = Parquet_Footer.probe_parquet_column_decode_in_row_group
                        cottas_path (Z.of_int rg) Z.one in
      let o_col_opt = Parquet_Footer.probe_parquet_column_decode_in_row_group
                        cottas_path (Z.of_int rg) (Z.of_int 2) in
      (match p_col_opt, o_col_opt with
       | FStar_Pervasives_Native.None, _ ->
         Printf.eprintf "[compound-po-WARN] rg=%d: predicate-column decode failed; rg empty in compound\n%!" rg
       | _, FStar_Pervasives_Native.None ->
         Printf.eprintf "[compound-po-WARN] rg=%d: object-column decode failed; rg empty in compound\n%!" rg
       | FStar_Pervasives_Native.Some p_lst, FStar_Pervasives_Native.Some o_lst ->
         (* Walk the two lists in lockstep; require same length (rg-row
            count). Mismatch => log + truncate to min length. *)
         let p_arr = Stdlib.Array.of_list p_lst in
         let o_arr = Stdlib.Array.of_list o_lst in
         let np = Stdlib.Array.length p_arr in
         let no = Stdlib.Array.length o_arr in
         if np <> no then
           Printf.eprintf "[compound-po-WARN] rg=%d: pred col len=%d obj col len=%d (using min)\n%!"
             rg np no;
         let n_rows = if np < no then np else no in
         (* Use Hashtbl keyed by pair-code for de-dup. *)
         let seen : (pint, unit) Hashtbl.t = Hashtbl.create (n_rows + 17) in
         let unknown_p = ref 0 in
         let unknown_o = ref 0 in
         let null_cells = ref 0 in
         for i = 0 to n_rows - 1 do
           match p_arr.(i), o_arr.(i) with
           | FStar_Pervasives_Native.None, _
           | _, FStar_Pervasives_Native.None ->
             incr null_cells
           | FStar_Pervasives_Native.Some p_raw, FStar_Pervasives_Native.Some o_raw ->
             (match Hashtbl.find_opt pred_tok_to_id p_raw,
                    Hashtbl.find_opt obj_tok_to_id  o_raw with
              | None, _ -> incr unknown_p
              | _, None -> incr unknown_o
              | Some p_id, Some o_id ->
                if p_id < 0 || p_id >= pred_dict_size ||
                   o_id < 0 || o_id >= obj_dict_size  then
                  Printf.eprintf "[compound-po-WARN] rg=%d row=%d id-out-of-range (p=%d/%d o=%d/%d)\n%!"
                    rg i p_id pred_dict_size o_id obj_dict_size
                else
                  let code = (p_id lsl 32) lor o_id in
                  if not (Hashtbl.mem seen code) then
                    Hashtbl.add seen code ())
         done;
         (* Materialise + sort. *)
         let n_uniq = Hashtbl.length seen in
         let arr = Stdlib.Array.make n_uniq 0 in
         let k = ref 0 in
         Hashtbl.iter (fun code () ->
           Stdlib.Array.unsafe_set arr !k code;
           incr k) seen;
         Stdlib.Array.sort Stdlib.compare arr;
         per_rg_codes.(rg) <- arr;
         total_pairs := !total_pairs + n_uniq;
         if rg = 0 || rg = num_rgs - 1 || rg mod 5 = 0 then
           Printf.eprintf "[compound-po-trace] rg=%d/%d: rows=%d uniq_pairs=%d (unknown_p=%d unknown_o=%d nulls=%d) in %.2fs\n%!"
             rg num_rgs n_rows n_uniq !unknown_p !unknown_o !null_cells
             (Unix.gettimeofday () -. t_rg))
    done;
    Printf.eprintf "[compound-po-trace] columnscan done in %.2fs (total_unique_pairs=%d)\n%!"
      (Unix.gettimeofday () -. t0) !total_pairs;
    (* Compute rg_offsets (byte offsets into the data section). *)
    let rg_offsets = Stdlib.Array.make n_index 0 in
    let cur = ref data_offset0 in
    for rg = 0 to num_rgs - 1 do
      rg_offsets.(rg) <- !cur;
      cur := !cur + 8 * Stdlib.Array.length per_rg_codes.(rg)
    done;
    rg_offsets.(num_rgs) <- !cur;
    let total_size = !cur in
    Printf.eprintf "[compound-po-trace] total file size = %d bytes (%.1f MB)\n%!"
      total_size (float_of_int total_size /. (1024.0 *. 1024.0));
    let buf = Buffer.create total_size in
    (* Header. *)
    write_u32_le buf copo_magic;
    write_u32_le buf layout_version;
    write_u32_le buf num_rgs;
    write_u32_le buf pred_dict_size;
    write_u32_le buf obj_dict_size;
    (* Index. *)
    for i = 0 to n_index - 1 do
      write_u64_le buf rg_offsets.(i)
    done;
    (* Data. *)
    for rg = 0 to num_rgs - 1 do
      let arr = per_rg_codes.(rg) in
      let n = Stdlib.Array.length arr in
      for i = 0 to n - 1 do
        write_u64_le buf (Stdlib.Array.unsafe_get arr i)
      done
    done;
    let t1 = Unix.gettimeofday () in
    atomic_write opath (Buffer.contents buf);
    let t2 = Unix.gettimeofday () in
    let stat_size = try (Unix.stat opath).Unix.st_size with _ -> -1 in
    Printf.eprintf "[compound-po-trace] wrote %s (Nbytes=%d) in %.2fs (build %.2fs + write %.2fs)\n%!"
      opath stat_size (t2 -. t0) (t1 -. t0) (t2 -. t1)

  (* Build .po.presence if absent OR if its header doesn't match the
     current .p.dict / .o.dict / .p.presence dimensions. Reads dict
     headers + tok_to_id maps via the F*-extracted RDF_CottasStore_OnDiskIndex
     primitives. Idempotent. *)
  let ensure_compound_po_built (cottas_path : string)
    (_h : cottas_ondisk_handle) : unit =
    let dpath_p = cottas_path ^ ".p.dict" in
    let dpath_o = cottas_path ^ ".o.dict" in
    let ppath_p = cottas_path ^ ".p.presence" in
    match RDF_CottasStore_OnDiskIndex.read_dict_header dpath_p,
          RDF_CottasStore_OnDiskIndex.read_dict_header dpath_o with
    | FStar_Pervasives_Native.None, _ ->
      Printf.eprintf "[compound-po-WARN] cannot read predicate dict header at %s; skip compound build\n%!" dpath_p
    | _, FStar_Pervasives_Native.None ->
      Printf.eprintf "[compound-po-WARN] cannot read object dict header at %s; skip compound build\n%!" dpath_o
    | FStar_Pervasives_Native.Some dh_p, FStar_Pervasives_Native.Some dh_o ->
      let n_preds = Z.to_int dh_p.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
      let n_objs  = Z.to_int dh_o.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
      let n_rgs = match RDF_CottasStore_OnDiskIndex.read_presence_header ppath_p with
        | FStar_Pervasives_Native.Some ph ->
          Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs
        | FStar_Pervasives_Native.None ->
          (match Parquet_Footer.probe_parquet_row_group_count cottas_path with
           | FStar_Pervasives_Native.None -> 0
           | FStar_Pervasives_Native.Some n -> Z.to_int n) in
      Printf.eprintf "[compound-po-trace] dimensions: n_rgs=%d n_preds=%d n_objs=%d\n%!"
        n_rgs n_preds n_objs;
      if n_rgs <= 0 || n_preds <= 0 || n_objs <= 0 then begin
        Printf.eprintf "[compound-po-WARN] degenerate dimensions; skip\n%!"
      end else if existing_file_matches cottas_path n_rgs n_preds n_objs then begin
        Printf.eprintf "[compound-po-trace] existing %s header matches; skip\n%!"
          (compound_path cottas_path)
      end else begin
        let pred_tok_to_id = build_tok_to_id dpath_p dh_p n_preds in
        let obj_tok_to_id  = build_tok_to_id dpath_o dh_o n_objs in
        Printf.eprintf "[compound-po-trace] tok_to_id sizes: pred=%d obj=%d\n%!"
          (Hashtbl.length pred_tok_to_id) (Hashtbl.length obj_tok_to_id);
        if Hashtbl.length pred_tok_to_id > 0 && Hashtbl.length obj_tok_to_id > 0 then
          build_compound_po_file cottas_path pred_tok_to_id obj_tok_to_id
            n_rgs n_preds n_objs
        else
          Printf.eprintf "[compound-po-WARN] empty tok_to_id; skip\n%!"
      end
end
'''

# Insert BEFORE `module Cottas_companion_boot = struct` so the boot
# module can reference Cottas_compound_po_writer.
boot_anchor = '''module Cottas_companion_boot = struct'''
if boot_anchor in content:
    content = content.replace(boot_anchor,
                              writer_module + '\n' + boot_anchor, 1)
    sys.stderr.write("  [compound-po] Cottas_compound_po_writer inserted before Cottas_companion_boot\n")
else:
    sys.stderr.write("  [compound-po] FATAL: Cottas_companion_boot anchor not found; aborting patch\n")
    sys.exit(1)

# ---------------------------------------------------------------------
# Step 2: Hook ensure_compound_po_built into prewarm_via_companions,
# AFTER the existing lamed3 hook. We use a precise multi-line anchor
# to avoid fuzzy matches.
# ---------------------------------------------------------------------

old_hook = '''    (* lamed3: build / mmap the predicate row-offset companion. *)
    (try Cottas_offset_idx.ensure_offsets_built cottas_path
     with e ->
       Printf.eprintf "[lamed3-WARN] ensure_offsets_built raised: %s\n%!"
         (Printexc.to_string e));'''

new_hook = '''    (* lamed3: build / mmap the predicate row-offset companion. *)
    (try Cottas_offset_idx.ensure_offsets_built cottas_path
     with e ->
       Printf.eprintf "[lamed3-WARN] ensure_offsets_built raised: %s\n%!"
         (Printexc.to_string e));
    (* compound-po: build the (p, o) joint presence companion. *)
    (try Cottas_compound_po_writer.ensure_compound_po_built cottas_path h
     with e ->
       Printf.eprintf "[compound-po-WARN] ensure_compound_po_built raised: %s\n%!"
         (Printexc.to_string e));'''

if old_hook in content:
    content = content.replace(old_hook, new_hook, 1)
    sys.stderr.write("  [compound-po] hooked ensure_compound_po_built into prewarm_via_companions (post-lamed3)\n")
else:
    sys.stderr.write("  [compound-po] FATAL: lamed3 hook anchor not found in prewarm_via_companions; aborting\n")
    sys.exit(1)

path.write_text(content)
sys.stderr.write("  [compound-po] applied: Cottas_compound_po_writer + boot hook\n")
PYEOF

echo "  Compound-po writer patch applied."
