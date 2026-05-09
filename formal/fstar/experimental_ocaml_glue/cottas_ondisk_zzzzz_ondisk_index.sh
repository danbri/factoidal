#!/bin/bash
# Vav3 — persistent mmap'd companion indexes for the on-disk COTTAS backend.
#
# Issue #100, 2026-04-26.
#
# What this patch does:
#
#   1. Implements the 6 `assume val` I/O primitives in
#      RDF.CottasStore.OnDiskIndex (mmap_companion_open, read_companion_u32_le,
#      read_companion_u64_le, read_companion_byte, read_companion_string,
#      companion_file_size) using OCaml `Unix.openfile` + `Bigarray.Array1`
#      mmap. The mmap'd region is held in a per-path
#      `(string, Bigarray.Array1.t) Hashtbl.t` for the lifetime of the
#      process. This is rule #15 conformant: pure byte-range I/O glue.
#
#   2. Adds a writer module `Cottas_companion_writer` that walks the
#      parquet columns ONCE per column (via the existing
#      `probe_parquet_column_decode_in_row_group` route) to produce the
#      .dict + .presence companion files. Atomically: writes to a .tmp
#      sibling, fsync, rename. Same algorithmic cost as today's pre-warm,
#      but PERSISTENT — written once, mmap'd forever.
#
#   3. Adds a boot orchestrator `Cottas_companion_boot.prewarm_via_companions`:
#      For each of the 4 columns (s, p, o, g):
#        a. Look for `<cottas_path>.<col>.dict` + `<cottas_path>.<col>.presence`.
#        b. If both present and headers verify (magic + version), mmap them.
#        c. Else, build via Cottas_companion_writer and then mmap.
#      Then bulk-populate the existing Hashtbl-based fast_tables from
#      the mmap'd companion (sub-second, sequential read).
#
#   4. Rewires factoidal_http.ml's `prewarm_cottas_columns` to call
#      `Cottas_companion_boot.prewarm_via_companions` instead of the four
#      `ensure_*_loaded` calls. First boot ~110 s (companions get built
#      then loaded). Subsequent boots <2 s (mmap + bulk-load).
#
# Disposition of Yod6/Tet3 in-RAM presence Hashtbls:
#   - Yod6's `pred_presence_by_path` and Tet3's `subj_presence_by_path` /
#     `obj_presence_by_path` ARE STILL POPULATED at boot, but now from the
#     mmap'd .presence files instead of the per-rg parquet column walk.
#     Same byte-identical contents. The runtime query path
#     (`pred_rg_could_contain` / `subj_rg_could_contain` / etc.) is
#     unchanged — they consult the same Hashtbls.
#
# Why we still populate Hashtbls instead of switching to direct mmap reads:
#   - Time-box (5h). The clean architecture is "F* lookup functions
#     consult mmap directly via assume val byte readers". Phase D of
#     issue #100 will swap. For now the bulk-load from mmap to Hashtbl
#     at boot is sub-second on parliament (108MB dict + ~6MB presence)
#     and gives the user the "no 110s pre-warm" win on cold restart.
#
# Rule #15: this patch is I/O glue + memory layout only. The companion
# file FORMAT is fully F*-defined in RDF.CottasStore.OnDiskIndex.fst.
# All reading semantics (header check, binary search, bit test) live
# in F* and extract to OCaml.
#
# Idempotency: skip-if-marker pattern.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

FILE="$OUTDIR/RDF_CottasStore_OnDiskIndex.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Warning: $FILE not found, skipping vav3 ondisk-index patch" >&2
  exit 0
fi

# Track separately which half of the patch has been applied; either may
# already be done if a partial re-extract happened.
ONDISK_DONE=0
COTTAS_DONE=0
if grep -q 'vav3: companion mmap implementations installed' "$FILE"; then
  ONDISK_DONE=1
fi

# Also patch RDF_CottasStore.ml to add the boot+writer modules. Sanity-check
# the prerequisite files exist.
COTTAS_FILE="$OUTDIR/RDF_CottasStore.ml"
if [[ ! -f "$COTTAS_FILE" ]]; then
  echo "  Warning: $COTTAS_FILE not found, skipping vav3 ondisk-index patch" >&2
  exit 0
fi
if grep -q 'vav3: Cottas_companion_writer installed' "$COTTAS_FILE"; then
  COTTAS_DONE=1
fi
if [[ "$ONDISK_DONE" == "1" && "$COTTAS_DONE" == "1" ]]; then
  echo "  Vav3 ondisk-index patch already present (both halves)."
  exit 0
fi

# Step A: replace the 6 assume-val failwith stubs in OnDiskIndex.ml with
# real mmap-backed implementations. Skip if already done.

if [[ "$ONDISK_DONE" == "0" ]]; then
python3 - "$FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# We replace each `failwith "Not yet implemented: ..."` stub with a real
# implementation. The implementations are inserted near the top of the
# file (before the F*-extracted lookup functions that depend on them).
# Strategy: replace each stub function in-place with a real body that
# delegates to a shared `Vav3_mmap` module defined here at the top.

vav3_mmap_module = r'''(* vav3: companion mmap implementations installed (issue #100, 2026-04-26).
   Per-path mmap'd Bigarray.Array1.t bytes for each .dict + .presence
   companion file. Held for the lifetime of the process. *)
module Vav3_mmap = struct
  open Stdlib
  (* `open Prims` at the top of this file (via `let cotd_magic_u32 : Prims.nat`)
     shadows `int` with `Prims.int = Z.t`. We need plain machine ints here
     for offsets, so alias them. *)
  type pint = Stdlib.Int.t

  type mmap_view = {
    mv_path : string;
    mv_size : pint;
    mv_data : (Stdlib.Char.t, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t;
    mv_fd   : Unix.file_descr;
  }

  let views : (string, mmap_view) Hashtbl.t = Hashtbl.create 17

  (* Open a path read-only and mmap the whole file. Returns Some size on
     success. None if the file doesn't exist or is empty. *)
  let try_open_mmap (path : string) : pint option =
    match Hashtbl.find_opt views path with
    | Some v -> Some v.mv_size
    | None ->
      try
        let fd = Unix.openfile path [Unix.O_RDONLY] 0 in
        let st = Unix.fstat fd in
        let size = st.Unix.st_size in
        if size = 0 then begin Unix.close fd; None end
        else begin
          (* Bigarray.array1_of_genarray + Unix.map_file mmaps into a
             Bigarray. We then keep the genarray-derived array1 alive in
             the views hashtbl. *)
          let ga = Unix.map_file fd Bigarray.Char Bigarray.c_layout false [|size|] in
          let a1 = Bigarray.array1_of_genarray ga in
          let v : mmap_view = {
            mv_path = path;
            mv_size = size;
            mv_data = a1;
            mv_fd = fd;
          } in
          Hashtbl.replace views path v;
          Some size
        end
      with _ -> None

  let close_mmap (path : string) : unit =
    match Hashtbl.find_opt views path with
    | None -> ()
    | Some v ->
      (try Unix.close v.mv_fd with _ -> ());
      Hashtbl.remove views path

  let view_for (path : string) : mmap_view option =
    match Hashtbl.find_opt views path with
    | Some v -> Some v
    | None ->
      (* Open lazily: F* may call read_companion_* without an explicit open. *)
      match try_open_mmap path with
      | None -> None
      | Some _ -> Hashtbl.find_opt views path

  let read_byte_int (path : string) (offset : pint) : pint option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || offset >= v.mv_size then None
      else Some (Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data offset))

  let read_u32_le_int (path : string) (offset : pint) : pint option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || offset + 4 > v.mv_size then None
      else
        let b0 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data offset) in
        let b1 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 1)) in
        let b2 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 2)) in
        let b3 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 3)) in
        Some (b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24))

  (* Note: u64 read assumes the value fits in OCaml's native int (63-bit
     on 64-bit). Our companion files are <= a few hundred MB so all u64
     fields (token byte offsets) are well below 2^62. We sanity-check
     and return None if the high bit looks set. *)
  let read_u64_le_int (path : string) (offset : pint) : pint option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || offset + 8 > v.mv_size then None
      else
        let b0 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data offset) in
        let b1 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 1)) in
        let b2 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 2)) in
        let b3 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 3)) in
        let b4 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 4)) in
        let b5 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 5)) in
        let b6 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 6)) in
        let b7 = Stdlib.Char.code (Bigarray.Array1.unsafe_get v.mv_data (offset + 7)) in
        if b7 >= 0x80 then None  (* would not fit in 63-bit int *)
        else
          let lo = b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
          let hi = b4 lor (b5 lsl 8) lor (b6 lsl 16) lor (b7 lsl 24) in
          Some (lo lor (hi lsl 32))

  let read_string (path : string) (offset : pint) (count : pint) : string option =
    match view_for path with
    | None -> None
    | Some v ->
      if offset < 0 || count < 0 || offset + count > v.mv_size then None
      else
        let buf = Stdlib.Bytes.create count in
        for i = 0 to count - 1 do
          Stdlib.Bytes.unsafe_set buf i (Bigarray.Array1.unsafe_get v.mv_data (offset + i))
        done;
        Some (Stdlib.Bytes.unsafe_to_string buf)

  let file_size (path : string) : pint option =
    if not (Sys.file_exists path) then None
    else try
      let st = Unix.stat path in
      if st.Unix.st_size <= 0 then None else Some st.Unix.st_size
    with _ -> None
end

'''

# Insert the Vav3_mmap module right after `open Prims`.
anchor_open = "open Prims"
if anchor_open not in content:
    sys.stderr.write("  [vav3] WARN: 'open Prims' anchor not found in OnDiskIndex.ml\n")
    sys.exit(1)

content = content.replace(anchor_open, anchor_open + "\n\n" + vav3_mmap_module, 1)

# Replace each failwith stub with a real implementation.
replacements = [
    # mmap_companion_open : string -> nat option (returns size)
    ('''let mmap_companion_open (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.OnDiskIndex.mmap_companion_open"''',
     '''let mmap_companion_open (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.try_open_mmap path with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)'''),
    # read_companion_u32_le
    ('''let read_companion_u32_le (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.OnDiskIndex.read_companion_u32_le"''',
     '''let read_companion_u32_le (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.read_u32_le_int path (Z.to_int offset) with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)'''),
    # read_companion_u64_le
    ('''let read_companion_u64_le (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.OnDiskIndex.read_companion_u64_le"''',
     '''let read_companion_u64_le (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.read_u64_le_int path (Z.to_int offset) with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)'''),
    # read_companion_byte
    ('''let read_companion_byte (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.OnDiskIndex.read_companion_byte"''',
     '''let read_companion_byte (path : Prims.string) (offset : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.read_byte_int path (Z.to_int offset) with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)'''),
    # read_companion_string
    ('''let read_companion_string (path : Prims.string) (offset : Prims.nat)
  (count : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.OnDiskIndex.read_companion_string"''',
     '''let read_companion_string (path : Prims.string) (offset : Prims.nat)
  (count : Prims.nat) : Prims.string FStar_Pervasives_Native.option=
  match Vav3_mmap.read_string path (Z.to_int offset) (Z.to_int count) with
  | None -> FStar_Pervasives_Native.None
  | Some s -> FStar_Pervasives_Native.Some s'''),
    # companion_file_size
    ('''let companion_file_size (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  failwith
    "Not yet implemented: RDF.CottasStore.OnDiskIndex.companion_file_size"''',
     '''let companion_file_size (path : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  match Vav3_mmap.file_size path with
  | None -> FStar_Pervasives_Native.None
  | Some n -> FStar_Pervasives_Native.Some (Z.of_int n)'''),
]

applied = 0
for old, new in replacements:
    if old in content:
        content = content.replace(old, new, 1)
        applied += 1
    else:
        sys.stderr.write(f"  [vav3] WARN: stub not found in OnDiskIndex.ml: {old.splitlines()[0]}\n")

sys.stderr.write(f"  [vav3-ondisk-index] OnDiskIndex.ml: replaced {applied}/6 mmap I/O stubs\n")

path.write_text(content)
PYEOF
fi  # close: if [[ "$ONDISK_DONE" == "0" ]]

# Step B: append the Cottas_companion_writer + Cottas_companion_boot
# modules to RDF_CottasStore.ml. They use the F*-extracted OnDiskIndex
# lookups (RDF_CottasStore_OnDiskIndex.*) for header validation and
# token decode, but build the .dict / .presence files via raw OCaml I/O
# (writer is glue, not a verified spec).

if [[ "$COTTAS_DONE" == "1" ]]; then
  echo "  Vav3 boot module already present in RDF_CottasStore.ml."
  exit 0
fi

python3 - "$COTTAS_FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

# We append our module at the END of the file. Since RDF_CottasStore.ml
# ends with a closing brace or top-level let, appending text is safe.
# We tag the appended block with a marker for idempotency.

writer_module = r'''
(* vav3: Cottas_companion_writer installed (issue #100, 2026-04-26).
   Walks the parquet columns once per column (subjects, predicates,
   objects, graphs) and writes the .dict + .presence companion files
   sibling to the .cottas. Atomic: writes to .tmp, fsync, rename.

   Same algorithmic cost as today's pre-warm. Once the companions exist,
   subsequent boots skip this and just mmap. *)
module Cottas_companion_writer = struct
  open Stdlib
  type pint = Stdlib.Int.t

  let dict_magic : pint  = 0x44544f43  (* 'COTD' little-endian *)
  let presence_magic : pint  = 0x50544f43  (* 'COTP' little-endian *)
  let layout_version : pint = 1

  let column_suffix = function
    | 0 -> "s"
    | 1 -> "p"
    | 2 -> "o"
    | 3 -> "g"
    | _ -> "x"

  let dict_path     base col_idx = Printf.sprintf "%s.%s.dict"     base (column_suffix col_idx)
  let presence_path base col_idx = Printf.sprintf "%s.%s.presence" base (column_suffix col_idx)

  let write_u32_le buf (v : pint) =
    Buffer.add_char buf (Stdlib.Char.chr (v land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 8) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 16) land 0xff));
    Buffer.add_char buf (Stdlib.Char.chr ((v lsr 24) land 0xff))

  let write_u64_le buf (v : pint) =
    write_u32_le buf (v land 0xffffffff);
    write_u32_le buf ((v lsr 32) land 0xffffffff)

  (* Walk every row group of `path`, column `col_idx`, collecting
     per-rg sets of distinct tokens AND a globally-sorted unique token
     list. Returns:
       (sorted_unique_tokens : string array,
        sorted_token_to_id   : (string -> pint),  via Hashtbl
        per_rg_token_set     : pint -> (string, unit) Hashtbl.t,
        rg_count             : pint)
     The sorted_unique_tokens is the ascending lexicographic ordering
     used by the .dict's binary search. *)
  let collect_distinct_per_rg (path : string) (col_idx : pint) =
    let rg_count = match Parquet_Footer.probe_parquet_row_group_count path with
      | FStar_Pervasives_Native.None -> 0
      | FStar_Pervasives_Native.Some n -> Z.to_int n in
    let global : (string, unit) Hashtbl.t = Hashtbl.create 1024 in
    let per_rg : (pint, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 32 in
    for rg = 0 to rg_count - 1 do
      let rg_set : (string, unit) Hashtbl.t = Hashtbl.create 256 in
      (match Parquet_Footer.probe_parquet_column_decode_in_row_group
               path (Z.of_int rg) (Z.of_int col_idx) with
       | FStar_Pervasives_Native.None ->
         Printf.eprintf "[vav3-WARN] writer: rg=%d col=%d decode failed\n%!" rg col_idx
       | FStar_Pervasives_Native.Some lst ->
         List.iter (function
           | FStar_Pervasives_Native.None -> ()
           | FStar_Pervasives_Native.Some raw ->
             if not (Hashtbl.mem rg_set raw) then Hashtbl.add rg_set raw ();
             if not (Hashtbl.mem global raw) then Hashtbl.add global raw ()
         ) lst);
      Hashtbl.replace per_rg rg rg_set;
      if rg = 0 || rg = rg_count - 1 || rg mod 5 = 0 then
        Printf.eprintf "[vav3-trace] writer rg=%d/%d col=%d distinct_so_far=%d\n%!"
          rg rg_count col_idx (Hashtbl.length global)
    done;
    let arr = Array.make (Hashtbl.length global) "" in
    let i = ref 0 in
    Hashtbl.iter (fun k () -> arr.(!i) <- k; incr i) global;
    Array.sort String.compare arr;
    let tok_to_id : (string, pint) Hashtbl.t = Hashtbl.create (Array.length arr * 2 + 17) in
    Array.iteri (fun id tok -> Hashtbl.add tok_to_id tok id) arr;
    (arr, tok_to_id, per_rg, rg_count)

  let atomic_write (path : string) (data : string) : unit =
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc data;
    flush oc;
    (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
    close_out oc;
    Sys.rename tmp path

  (* Writer for one column's .dict file.
     Layout (per RDF.CottasStore.OnDiskIndex.fst):
       [ magic u32 | version u32 | num_tokens u32 | pad u32 ]
       [ ids_offset u64 | tokens_offset u64 ]
       [ ids[]         u32 * num_tokens, sorted ASC by token ]
       [ token_offs[]  u64 * (num_tokens+1) ]
       [ token_data    bytes ]
  *)
  (* #200 PR2 (2026-05-09): byte assembly migrated to F* at
     RDF.CottasStore.DictWriter.serialize_dict. The OCaml side here is
     reduced to the rule-#11(a) I/O step: convert the F*-extracted byte
     list to a string and atomic-write to disk. The F* serializer
     enforces the same on-disk format invariants (magic 'COKD', version,
     32-byte header, ids[], token_offs[], token_data) but with verified
     overflow checks (n < 2^32, total_offset < 2^64). *)
  let write_dict_file (path : string) (sorted_tokens : string array) : unit =
    let bytes_list =
      RDF_CottasStore_DictWriter.serialize_dict
        (Array.to_list sorted_tokens)
    in
    let buf = Buffer.create (List.length bytes_list) in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) bytes_list;
    atomic_write path (Buffer.contents buf)

  (* Writer for one column's .presence file.
     Layout:
       [ magic u32 | version u32 | num_rgs u32 | num_tokens u32 ]
       [ bitmap : ceil(num_rgs * num_tokens / 8) bytes, row-major,
                  bit (rg*num_tokens + tok) ]

     #200 PR2 part 2 (2026-05-09): the 16-byte header is now produced
     by F* (RDF.CottasStore.PresenceWriter.serialize_presence_header).
     Bitmap contents stay in OCaml because parliament-scale .presence
     files reach ~12.5MB; materialising as F-star's list-of-char
     would cost millions of cons cells per column. Atomic-write +
     bitmap bit-set are rule-#11(a) acceptable I/O-glue work. *)
  let write_presence_file (path : string)
    (rg_count : pint)
    (sorted_tokens : string array)
    (tok_to_id : (string, pint) Hashtbl.t)
    (per_rg : (pint, (string, unit) Hashtbl.t) Hashtbl.t) : unit =
    let n = Array.length sorted_tokens in
    let bits = rg_count * n in
    let bytes = (bits + 7) / 8 in
    let bitmap = Bytes.make bytes '\000' in
    for rg = 0 to rg_count - 1 do
      match Hashtbl.find_opt per_rg rg with
      | None -> ()
      | Some rg_set ->
        Hashtbl.iter (fun tok () ->
          match Hashtbl.find_opt tok_to_id tok with
          | None -> ()
          | Some tok_id ->
            let bit_index = rg * n + tok_id in
            let byte_index = bit_index / 8 in
            let bit_in_byte = bit_index mod 8 in
            let cur = Stdlib.Char.code (Bytes.unsafe_get bitmap byte_index) in
            Bytes.unsafe_set bitmap byte_index
              (Stdlib.Char.chr (cur lor (1 lsl bit_in_byte)))
        ) rg_set
    done;
    let header_chars =
      RDF_CottasStore_PresenceWriter.serialize_presence_header
        (Z.of_int rg_count) (Z.of_int n)
    in
    let buf = Buffer.create (16 + bytes) in
    List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) header_chars;
    Buffer.add_bytes buf bitmap;
    atomic_write path (Buffer.contents buf)

  let build_companion_pair (cottas_path : string) (col_idx : pint) : pint =
    let dpath = dict_path     cottas_path col_idx in
    let ppath = presence_path cottas_path col_idx in
    Printf.eprintf "[vav3-trace] writer: building companion col=%d dict=%s presence=%s\n%!"
      col_idx dpath ppath;
    let t0 = Unix.gettimeofday () in
    let (sorted, tok_to_id, per_rg, rg_count) = collect_distinct_per_rg cottas_path col_idx in
    let t1 = Unix.gettimeofday () in
    Printf.eprintf "[vav3-trace] writer col=%d collect_distinct: %.2fs (%d distinct, %d rgs)\n%!"
      col_idx (t1 -. t0) (Array.length sorted) rg_count;
    write_dict_file dpath sorted;
    let t2 = Unix.gettimeofday () in
    Printf.eprintf "[vav3-trace] wrote companion %s (Nbytes=%d) in %.2fs\n%!"
      dpath (try (Unix.stat dpath).Unix.st_size with _ -> -1) (t2 -. t1);
    write_presence_file ppath rg_count sorted tok_to_id per_rg;
    let t3 = Unix.gettimeofday () in
    Printf.eprintf "[vav3-trace] wrote companion %s (Nbytes=%d) in %.2fs\n%!"
      ppath (try (Unix.stat ppath).Unix.st_size with _ -> -1) (t3 -. t2);
    Array.length sorted
end

(* vav3: Cottas_companion_boot installed.
   The orchestrator: open mmaps if companions exist + verify; else
   build them via Cottas_companion_writer and then mmap. Then bulk-
   populate the existing fast_tables Hashtbls + Yod6/Tet3 presence
   maps from the mmap'd companions. Sub-second on parliament. *)
module Cottas_companion_boot = struct
  open Stdlib
  type pint = Stdlib.Int.t

  (* Check that all 4 .dict + 4 .presence companions exist for `cottas_path`
     and verify their headers. Returns true iff every companion is loadable. *)
  let companions_present_and_valid (cottas_path : string) : bool =
    let all_ok = ref true in
    for col_idx = 0 to 3 do
      let dpath = Cottas_companion_writer.dict_path     cottas_path col_idx in
      let ppath = Cottas_companion_writer.presence_path cottas_path col_idx in
      if not (Sys.file_exists dpath && Sys.file_exists ppath) then begin
        all_ok := false;
        Printf.eprintf "[vav3-trace] companion absent for col=%d (dict=%s presence=%s)\n%!"
          col_idx dpath ppath
      end else begin
        (* Verify headers via the F*-extracted readers. *)
        let dh = RDF_CottasStore_OnDiskIndex.read_dict_header dpath in
        let ph = RDF_CottasStore_OnDiskIndex.read_presence_header ppath in
        match dh, ph with
        | FStar_Pervasives_Native.Some dh', FStar_Pervasives_Native.Some ph' ->
          if not (RDF_CottasStore_OnDiskIndex.dict_header_ok dh' &&
                  RDF_CottasStore_OnDiskIndex.presence_header_ok ph') then begin
            all_ok := false;
            Printf.eprintf "[vav3-trace] companion header verify FAILED for col=%d\n%!" col_idx
          end
        | _ ->
          all_ok := false;
          Printf.eprintf "[vav3-trace] companion header read FAILED for col=%d\n%!" col_idx
      end
    done;
    !all_ok

  (* Build all 4 companion-pair files for `cottas_path`. One-time cost
     (~110s on parliament); persists forever. *)
  let build_all_companions (cottas_path : string) : unit =
    Printf.eprintf "[vav3-trace] building all companions for %s\n%!" cottas_path;
    let t0 = Unix.gettimeofday () in
    for col_idx = 0 to 3 do
      let _n = Cottas_companion_writer.build_companion_pair cottas_path col_idx in
      ()
    done;
    let dt = Unix.gettimeofday () -. t0 in
    Printf.eprintf "[vav3-trace] all 4 companion-pair files written in %.2fs\n%!" dt

  (* Bulk-populate the Hashtbl-based fast_tables AND Yod6/Tet3 presence
     maps from the mmap'd companions. Sub-second on parliament since the
     mmap'd region is just a sequential walk.

     We iterate dict tokens 0..num_tokens-1: each id maps to the raw
     column-token via dict_decode_token. We also walk the presence
     bitmap rg-by-rg: for each rg, scan the rg's bits to find set
     positions and add those token strings to the rg_set Hashtbl.

     This is the bulk-load shim: in a follow-on phase the _fast
     functions will consult the mmap'd companions directly via
     companion_encode/companion_decode/companion_rg_could_contain
     (extracted from F-star), eliminating the Hashtbls entirely. *)
  let bulk_load_column_into_tables
    (cottas_path : string) (col_idx : pint)
    (h : cottas_ondisk_handle)
    (tables : Cottas_ondisk_runtime.fast_tables) : pint =
    let dpath = Cottas_companion_writer.dict_path     cottas_path col_idx in
    let ppath = Cottas_companion_writer.presence_path cottas_path col_idx in
    let dh_opt = RDF_CottasStore_OnDiskIndex.read_dict_header dpath in
    let ph_opt = RDF_CottasStore_OnDiskIndex.read_presence_header ppath in
    match dh_opt, ph_opt with
    | FStar_Pervasives_Native.Some dh, FStar_Pervasives_Native.Some ph ->
      let n_tok = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_num_tokens in
      let n_rgs = Z.to_int ph.RDF_CottasStore_OnDiskIndex.ph_num_rgs in
      Printf.eprintf "[vav3-trace] bulk-load col=%d num_tokens=%d num_rgs=%d\n%!"
        col_idx n_tok n_rgs;
      (* Step 1: walk the .dict to populate global tok_to_id + id_to_tok.
         We use direct mmap reads (instead of dict_decode_token per id)
         to amortise mmap-view-lookup cost. The F* spec is byte-identical;
         this is a perf shim. *)
      let _ = h in  (* h.coh_path used only for sanity; we use cottas_path explicitly *)
      let _ = RDF_CottasStore_OnDiskIndex.Vav3_mmap.try_open_mmap dpath in
      let dview_opt = Hashtbl.find_opt RDF_CottasStore_OnDiskIndex.Vav3_mmap.views dpath in
      let read_token : pint -> string option = match dview_opt with
        | None -> (fun _ -> None)
        | Some dv ->
          let mv_data = dv.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_data in
          let mv_size = dv.RDF_CottasStore_OnDiskIndex.Vav3_mmap.mv_size in
          let tokens_offset_int = Z.to_int dh.RDF_CottasStore_OnDiskIndex.dh_tokens_offset in
          (* Read u64 LE inline; assumes value fits in 63-bit int (yes: file
             sizes are <500MB on parliament). *)
          let read_u64 off =
            if off + 8 > mv_size then None
            else
              let g i = Stdlib.Char.code (Bigarray.Array1.unsafe_get mv_data i) in
              let b0 = g off in let b1 = g (off+1) in
              let b2 = g (off+2) in let b3 = g (off+3) in
              let b4 = g (off+4) in let b5 = g (off+5) in
              let b6 = g (off+6) in let b7 = g (off+7) in
              if b7 >= 0x80 then None
              else
                let lo = b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24) in
                let hi = b4 lor (b5 lsl 8) lor (b6 lsl 16) lor (b7 lsl 24) in
                Some (lo lor (hi lsl 32)) in
          (* Token start offset for token-id `id` at byte offset
             tokens_offset + 8*id; end at tokens_offset + 8*(id+1). *)
          (fun id ->
            match read_u64 (tokens_offset_int + 8 * id) with
            | None -> None
            | Some token_start ->
              match read_u64 (tokens_offset_int + 8 * (id + 1)) with
              | None -> None
              | Some token_end ->
                if token_end < token_start then None
                else
                  let len = token_end - token_start in
                  if token_start + len > mv_size then None
                  else
                    let buf = Stdlib.Bytes.create len in
                    for i = 0 to len - 1 do
                      Stdlib.Bytes.unsafe_set buf i
                        (Bigarray.Array1.unsafe_get mv_data (token_start + i))
                    done;
                    Some (Stdlib.Bytes.unsafe_to_string buf)) in
      (* Bulk-populate the raw token mappings (encode + id_to_tok). The
         TYPED-term Hashtbls (ft_id_to_subject/predicate/object/graph)
         are NOT populated here — typed parses happen lazily on first
         decode_*_fast call. Predicates+graphs are tiny (232 + 1) so we
         do parse them eagerly here for simplicity. *)
      for id = 0 to n_tok - 1 do
        match read_token id with
        | None ->
          Printf.eprintf "[vav3-WARN] bulk-load col=%d id=%d decode failed\n%!" col_idx id
        | Some raw ->
          (match col_idx with
           | 0 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_subj_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_subj_tok id raw
             (* Skip ft_id_to_subject; populated lazily by decode_subject_fast. *)
           | 1 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_pred_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_pred_tok id raw;
             (* Predicates are small (232); eager parse is fine. *)
             (match Cottas_ondisk_runtime.parse_iri_token raw with
              | Some iri ->
                Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_predicate id (iri : RDF_Graph_Executable.wf_iri)
              | None -> Printf.eprintf "[vav3-WARN] bulk-load: bad predicate id=%d raw=%s\n%!" id raw)
           | 2 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_obj_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_obj_tok id raw
             (* Skip ft_id_to_object; populated lazily by decode_object_fast. *)
           | 3 ->
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_graph_tok_to_id raw id;
             Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_graph_tok id raw;
             (match Cottas_ondisk_runtime.parse_iri_token raw with
              | Some iri ->
                Hashtbl.replace tables.Cottas_ondisk_runtime.ft_id_to_graph id (iri : RDF_Graph_Executable.iri)
              | None ->
                (* DEFAULT graph token doesn't parse to an IRI; skip silently. *)
                if raw <> "DEFAULT" then
                  Printf.eprintf "[vav3-WARN] bulk-load: bad graph id=%d raw=%s\n%!" id raw)
           | _ -> ())
      done;
      (* Yod6/Tet3 presence Hashtbl population previously lived here as
         a transitional shim. The query path now consults the F*-pure
         RDF.CottasStore.PresenceBitmap.rg_could_contain (verifiable in
         SPARQL.Plan.Pruning.fst) directly against the mmap'd companion
         file, so the in-RAM Hashtbl mirror is unread dead code. Issue
         #249 retires this presence-bytewalk; #200 Section A codename
         track. *)
      n_tok
    | _ ->
      Printf.eprintf "[vav3-FATAL] bulk-load col=%d header read failed\n%!" col_idx;
      0

  let prewarm_via_companions (cottas_path : string)
    (h : cottas_ondisk_handle) : unit =
    let t0 = Unix.gettimeofday () in
    let tables = Cottas_ondisk_runtime.tables_for h in
    if not (companions_present_and_valid cottas_path) then begin
      Printf.eprintf "[vav3-trace] companions absent or invalid; building (one-time cost)\n%!";
      build_all_companions cottas_path
    end else begin
      Printf.eprintf "[vav3-trace] mmap'd companion files, skipping pre-warm\n%!"
    end;
    (* Bulk-load each column's tables from the (now-present) companions. *)
    for col_idx = 0 to 3 do
      let _ = bulk_load_column_into_tables cottas_path col_idx h tables in
      ()
    done;
    (* Mark every column as loaded so the lazy populators (Bet7) skip. *)
    Cottas_ondisk_lazy.mark_subj_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_pred_loaded  cottas_path;
    Cottas_ondisk_lazy.mark_obj_loaded   cottas_path;
    Cottas_ondisk_lazy.mark_graph_loaded cottas_path;
    let dt = Unix.gettimeofday () -. t0 in
    Printf.eprintf "[vav3-trace] prewarm_via_companions completed in %.2fs (subjs=%d preds=%d objs=%d graphs=%d)\n%!"
      dt
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_subj_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_pred_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_obj_tok_to_id)
      (Hashtbl.length tables.Cottas_ondisk_runtime.ft_graph_tok_to_id)
end
'''

content += writer_module
path.write_text(content)
sys.stderr.write("  [vav3-ondisk-index] RDF_CottasStore.ml: appended Cottas_companion_writer + Cottas_companion_boot\n")
PYEOF

# Step C: patch decode_subject_fast / decode_object_fast to fall back to
# raw-tok lookup + parse if the typed cache misses. This lets bulk_load
# skip eager subject/object parsing (1.86M typed parses on parliament,
# the bulk-load bottleneck) and parse on demand at query time instead.
# Each decode is at most O(1) hashtbl + O(parse) on first hit per id;
# most queries return only a few rows, so the amortised cost is near-zero.

python3 - "$COTTAS_FILE" <<'PYEOF'
import sys
from pathlib import Path

path = Path(sys.argv[1])
content = path.read_text()

if 'vav3: lazy decode-fast cache miss' in content:
    sys.stderr.write("  [vav3-ondisk-index] decode-fast lazy patch already applied\n")
    sys.exit(0)

# Patch decode_subject_fast: on cache miss, look up the raw token via
# id_to_subj_tok, parse it, cache the parse, return.
old_dec_sub = '''  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_subject (Z.to_int id) with
    | Some s -> s
    | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"'''
new_dec_sub = '''  let decode_subject_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.subject =
    let tables = tables_for h in
    ensure_subjects_loaded h tables;
    let id_int = Z.to_int id in
    match Hashtbl.find_opt tables.ft_id_to_subject id_int with
    | Some s -> s
    | None ->
      (* vav3: lazy decode-fast cache miss — bulk_load_column_into_tables
         skipped eager parse to save boot time; parse on demand here. *)
      (match Hashtbl.find_opt tables.ft_id_to_subj_tok id_int with
       | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"
       | Some raw ->
         (match parse_subject_str raw with
          | Some s ->
            Hashtbl.replace tables.ft_id_to_subject id_int s;
            s
          | None -> RDF_Graph_Executable.S_BNode "cottas_decode_oor"))'''

if old_dec_sub in content:
    content = content.replace(old_dec_sub, new_dec_sub, 1)
    sys.stderr.write("  [vav3-ondisk-index] patched decode_subject_fast for lazy parse\n")
else:
    sys.stderr.write("  [vav3-ondisk-index] WARN: decode_subject_fast anchor not found\n")

old_dec_obj = '''  let decode_object_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.rdf_term =
    let tables = tables_for h in
    ensure_objects_loaded h tables;
    match Hashtbl.find_opt tables.ft_id_to_object (Z.to_int id) with
    | Some o -> o
    | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"'''
new_dec_obj = '''  let decode_object_fast (h : cottas_ondisk_handle) (id : Prims.nat)
    : RDF_Graph_Executable.rdf_term =
    let tables = tables_for h in
    ensure_objects_loaded h tables;
    let id_int = Z.to_int id in
    match Hashtbl.find_opt tables.ft_id_to_object id_int with
    | Some o -> o
    | None ->
      (* vav3: lazy decode-fast cache miss for objects. *)
      (match Hashtbl.find_opt tables.ft_id_to_obj_tok id_int with
       | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"
       | Some raw ->
         (match parse_object_str raw with
          | Some o ->
            Hashtbl.replace tables.ft_id_to_object id_int o;
            o
          | None -> RDF_Graph_Executable.T_BNode "cottas_decode_oor"))'''

if old_dec_obj in content:
    content = content.replace(old_dec_obj, new_dec_obj, 1)
    sys.stderr.write("  [vav3-ondisk-index] patched decode_object_fast for lazy parse\n")
else:
    sys.stderr.write("  [vav3-ondisk-index] WARN: decode_object_fast anchor not found\n")

path.write_text(content)
PYEOF

echo "  Vav3 ondisk-index patch applied."
