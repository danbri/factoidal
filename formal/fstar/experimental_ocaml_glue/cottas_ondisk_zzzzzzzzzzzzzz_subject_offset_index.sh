#!/bin/bash
# Subject row-offset index — per-row-group... no, per-SUBJECT
# contiguous global row range companion for the on-disk COTTAS
# backend. Issue #100 follow-up, 2026-07-13 (closes the q3
# subject-point-lookup gap, docs/test-results/competitive-bench.json).
#
# What this patch does:
#
#   1. After the dict + presence companions exist (Vav3), builds a
#      new sibling companion file `<cottas>.s.offsets` that records,
#      for each SUBJECT id, the CONTIGUOUS global row-index range
#      `[start, end)` that subject's rows occupy. This is a much
#      simpler structure than the predicate `.p.offsets` companion
#      (`cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`): the BaseWriter
#      sorts every row `(s, p, o, g)` subject-primary before
#      serialisation, so a subject's rows are always one contiguous
#      run in the GLOBAL row order -- one (start, end) pair per
#      subject is exact, no per-row-group breakdown needed.
#
#   2. File format (companion to `.s.dict` / `.s.presence`), byte
#      layout owned by F* (`RDF.CottasStore.SubjectOffsetsWriter.fst`
#      per CLAUDE.md rule #11):
#
#        [ magic 'COTS' u32 (0x53544f43 LE) ]
#        [ version u32 ]
#        [ num_subjects u32 ]
#        [ num_rows_total u32 ]
#        [ ranges : (u64 start, u64 end_exclusive) * num_subjects,
#          ascending subject-id order ]
#
#   3. Boot wiring: hooks into `Cottas_companion_boot.
#      prewarm_via_companions`, chained AFTER the existing lamed3 +
#      compound-po hooks (exact multi-line anchor match on THEIR
#      combined post-edit text, so this script must sort after both
#      `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` and
#      `cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh` --
#      confirmed both already chain on this same anchor). If the
#      offsets file is absent, build it here (one subject-column
#      row-group walk, same order of magnitude as lamed3's predicate
#      walk). Reads are served entirely by the GENERIC companion mmap
#      primitives (`mmap_companion_open` / `read_companion_u32_le` /
#      `read_companion_u64_le`, already realised for `.p.offsets` /
#      `.dict` / `.presence`) via
#      `RDF.Store.Columnar.SubjectOffsetIndex.fst` -- this patch does
#      NOT add a new OCaml reader, only the builder (rule #11: byte
#      layout + the read primitives are already F*-owned and
#      OCaml-realised; a companion-specific reader would duplicate
#      that).
#
# Rule #15: writer is I/O glue + memory layout only. No new RDF/SPARQL
# semantics: a subject's row range is byte-identical to "the
# contiguous run of rows whose subject-token equals S", which
# BaseWriter's global (s,p,o,g) sort guarantees exists.
#
# Idempotency: skip-if-marker pattern + skip-if-file-exists pattern
# (mirrors lamed3/compound-po).

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping subject-offset-index patch" >&2
  exit 0
fi

if ! grep -q 'vav3: Cottas_companion_writer installed' "$FILE"; then
  echo "  Warning: subject-offset-index patch needs Vav3 boot/writer module;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh must run first." >&2
  exit 0
fi

if grep -q 'subject-offset-index: Cottas_subject_offset_idx installed' "$FILE"; then
  echo "  Subject-offset-index patch already present."
  exit 0
fi

if ! grep -q 'compound-po: build the (p, o) joint presence companion.' "$FILE"; then
  echo "  Warning: subject-offset-index patch needs the compound-po writer patch;" >&2
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh must run first." >&2
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# ---------------------------------------------------------------------
# Step 1: Insert Cottas_subject_offset_idx writer module BEFORE
# Cottas_companion_boot (mirrors Cottas_compound_po_writer's own
# insertion point) so prewarm_via_companions can reference it.
# ---------------------------------------------------------------------

writer_module = r'''
(* subject-offset-index: Cottas_subject_offset_idx installed (issue
   #100 follow-up, 2026-07-13). Per-SUBJECT contiguous global
   row-range index. Sibling .s.offsets file:
     [ magic 'COTS' u32 | version u32 | num_subjects u32 | num_rows_total u32 ]
     [ ranges : (u64 start, u64 end_exclusive) * num_subjects, ascending
       subject-id order ]
   Closes the q3 subject-point-lookup gap: a bound-subject query can
   read one dense (start,end) entry instead of decoding whole row
   groups on spec. Built once (subject column is globally contiguous
   post-sort, so this is a single sequential pass), mmap'd on demand
   by the generic companion-file primitives at query time (no
   OCaml-side reader in this patch -- see this file's own header
   comment). *)
module Cottas_subject_offset_idx = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let header_size : pint = 16  (* 4 u32 fields *)

  let subject_offsets_path (cottas_path : string) : string =
    cottas_path ^ ".s.offsets"

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

  (* Build the offsets file by walking the SUBJECT column once,
     row-group order (= global row order, per BaseWriter's subject-
     primary sort). Requires the subject dict's tok_to_id mapping (as
     a Hashtbl) so we can encode each token to its dict id during the
     walk. Detects subject-value transitions (rows are pre-sorted) and
     records each subject's [start, end) global row range. *)
  let build_subject_offsets_file (cottas_path : string)
    (subj_tok_to_id : (string, pint) Hashtbl.t)
    (num_subjects : pint) (num_rgs : pint) : unit =
    let opath = subject_offsets_path cottas_path in
    Printf.eprintf "[subject-offset-trace] building offsets file %s (num_subjects=%d num_rgs=%d)\n%!"
      opath num_subjects num_rgs;
    let t0 = Unix.gettimeofday () in
    let starts = Stdlib.Array.make num_subjects (-1) in
    let ends   = Stdlib.Array.make num_subjects (-1) in
    let global_row = ref 0 in
    let cur_subj = ref (-1) in
    let close_cur () =
      if !cur_subj >= 0 then ends.(!cur_subj) <- !global_row
    in
    for rg = 0 to num_rgs - 1 do
      let t_rg = Unix.gettimeofday () in
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group
               cottas_path (Z.of_int rg) Z.zero with  (* col_index 0 = subject *)
       | FStar_Pervasives_Native.None ->
         Printf.eprintf "[subject-offset-WARN] offsets-build: rg=%d subject decode failed\n%!" rg
       | FStar_Pervasives_Native.Some lst ->
         List.iter (function
           | FStar_Pervasives_Native.None -> incr global_row
           | FStar_Pervasives_Native.Some raw ->
             (match Hashtbl.find_opt subj_tok_to_id raw with
              | None ->
                Printf.eprintf "[subject-offset-WARN] offsets-build: rg=%d row=%d unknown subject token %s\n%!"
                  rg !global_row raw
              | Some sid ->
                if sid >= 0 && sid < num_subjects then begin
                  if sid <> !cur_subj then begin
                    close_cur ();
                    cur_subj := sid;
                    starts.(sid) <- !global_row
                  end
                end else
                  Printf.eprintf "[subject-offset-WARN] offsets-build: subject id %d out of range\n%!" sid);
             incr global_row) lst);
      if rg = 0 || rg = num_rgs - 1 || rg mod 5 = 0 then
        Printf.eprintf "[subject-offset-trace] offsets-build rg=%d/%d (%.2fs this rg)\n%!"
          rg num_rgs (Unix.gettimeofday () -. t_rg)
    done;
    close_cur ();
    Printf.eprintf "[subject-offset-trace] offsets-build columnscan done in %.2fs (total_rows=%d)\n%!"
      (Unix.gettimeofday () -. t0) !global_row;
    (* Header — produced by F* (rule #11(a) byte-layout boundary). *)
    let header_chars =
      RDF_CottasStore_SubjectOffsetsWriter.serialize_subject_offsets_header
        (Z.of_int num_subjects) (Z.of_int !global_row)
    in
    let buf = Buffer.create (header_size + 16 * num_subjects) in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) header_chars;
    for sid = 0 to num_subjects - 1 do
      let s = starts.(sid) and e = ends.(sid) in
      if s < 0 || e < 0 then begin
        Printf.eprintf "[subject-offset-WARN] offsets-build: subject id %d never observed; writing (0,0)\n%!" sid;
        write_u64_le buf 0;
        write_u64_le buf 0
      end else begin
        write_u64_le buf s;
        write_u64_le buf e
      end
    done;
    let t1 = Unix.gettimeofday () in
    atomic_write opath (Buffer.contents buf);
    let t2 = Unix.gettimeofday () in
    let stat_size = try (Unix.stat opath).Unix.st_size with _ -> -1 in
    Printf.eprintf "[subject-offset-trace] offsets-build wrote %s (Nbytes=%d) in %.2fs (build %.2fs + write %.2fs)\n%!"
      opath stat_size (t2 -. t0) (t1 -. t0) (t2 -. t1)

  (* Build the offsets file if absent. Reads the subject dict's
     tok_to_id mapping from the F* extracted reader (so id assignment
     matches the on-disk dict's sorted-rank ordering, the SAME
     id-space `compound_po_dict_encode path "s" tok` resolves at query
     time). Called from boot (after Vav3 companions are present). *)
  let ensure_subject_offsets_built (cottas_path : string) : unit =
    let opath = subject_offsets_path cottas_path in
    if Sys.file_exists opath && (try (Unix.stat opath).Unix.st_size with _ -> 0) >= header_size then
      Printf.eprintf "[subject-offset-trace] offsets file present at %s, skipping build\n%!" opath
    else begin
      Printf.eprintf "[subject-offset-trace] offsets file absent; building\n%!";
      let dpath = cottas_path ^ ".s.dict" in
      match RDF_CottasStore_OnDiskIndex.read_dict_header dpath with
      | FStar_Pervasives_Native.None ->
        Printf.eprintf "[subject-offset-FATAL] offsets-build: cannot read subject dict header at %s\n%!" dpath
      | FStar_Pervasives_Native.Some dh ->
        let n_subjects = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
        let ppath = cottas_path ^ ".s.presence" in
        let n_rgs = match RDF_CottasStore_OnDiskIndex.read_presence_header ppath with
          | FStar_Pervasives_Native.Some ph ->
            Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs
          | FStar_Pervasives_Native.None ->
            (match Parquet_Footer.probe_parquet_row_group_count cottas_path with
             | FStar_Pervasives_Native.None -> 0
             | FStar_Pervasives_Native.Some n -> Z.to_int n) in
        Printf.eprintf "[subject-offset-trace] offsets-build: n_rgs=%d n_subjects=%d\n%!" n_rgs n_subjects;
        let tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create (n_subjects * 2 + 17) in
        for id = 0 to n_subjects - 1 do
          match RDF_CottasStore_OnDiskIndex.dict_decode_token
                  dpath dh (Z.of_int id) with
          | FStar_Pervasives_Native.Some raw ->
            Hashtbl.replace tok_to_id raw id
          | FStar_Pervasives_Native.None ->
            Printf.eprintf "[subject-offset-WARN] offsets-build: dict_decode_token failed for id=%d\n%!" id
        done;
        Printf.eprintf "[subject-offset-trace] offsets-build: built tok_to_id (size=%d)\n%!"
          (Hashtbl.length tok_to_id);
        if n_rgs > 0 && n_subjects > 0 && Hashtbl.length tok_to_id > 0 then
          build_subject_offsets_file cottas_path tok_to_id n_subjects n_rgs
        else
          Printf.eprintf "[subject-offset-WARN] offsets-build: skipping (n_rgs=%d n_subjects=%d tok_to_id=%d)\n%!"
            n_rgs n_subjects (Hashtbl.length tok_to_id)
    end
end
'''

# Insert BEFORE `module Cottas_companion_boot = struct` (same
# insertion point Cottas_compound_po_writer uses) so the boot module
# can reference Cottas_subject_offset_idx.
boot_anchor = '''module Cottas_companion_boot = struct'''
if boot_anchor in content:
    content = content.replace(boot_anchor,
                              writer_module + '\n' + boot_anchor, 1)
    sys.stderr.write("  [subject-offset-index] Cottas_subject_offset_idx inserted before Cottas_companion_boot\n")
else:
    sys.stderr.write("  [subject-offset-index] FATAL: Cottas_companion_boot anchor not found; aborting patch\n")
    sys.exit(1)

# ---------------------------------------------------------------------
# Step 2: Hook ensure_subject_offsets_built into prewarm_via_companions,
# AFTER the existing lamed3 + compound-po hooks. Precise multi-line
# anchor on their COMBINED post-edit text (both scripts sort before
# this one, per this file's own header comment).
# ---------------------------------------------------------------------

old_hook = '''    (* lamed3: build / mmap the predicate row-offset companion. *)
    (try Cottas_offset_idx.ensure_offsets_built cottas_path
     with e ->
       Printf.eprintf "[lamed3-WARN] ensure_offsets_built raised: %s\n%!"
         (Printexc.to_string e));
    (* compound-po: build the (p, o) joint presence companion. *)
    (try Cottas_compound_po_writer.ensure_compound_po_built cottas_path h
     with e ->
       Printf.eprintf "[compound-po-WARN] ensure_compound_po_built raised: %s\n%!"
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
         (Printexc.to_string e));
    (* subject-offset-index: build the per-subject contiguous
       global row-range companion. *)
    (try Cottas_subject_offset_idx.ensure_subject_offsets_built cottas_path
     with e ->
       Printf.eprintf "[subject-offset-WARN] ensure_subject_offsets_built raised: %s\n%!"
         (Printexc.to_string e));'''

if old_hook in content:
    content = content.replace(old_hook, new_hook, 1)
    sys.stderr.write("  [subject-offset-index] hooked ensure_subject_offsets_built into prewarm_via_companions (post-lamed3, post-compound-po)\n")
else:
    sys.stderr.write("  [subject-offset-index] FATAL: lamed3+compound-po hook anchor not found in prewarm_via_companions; aborting\n")
    sys.exit(1)

path.write_text(content)
sys.stderr.write("  [subject-offset-index] applied: Cottas_subject_offset_idx + boot hook\n")
PYEOF

echo "  Subject-offset-index writer patch applied."
