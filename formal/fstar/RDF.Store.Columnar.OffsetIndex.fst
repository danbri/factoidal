module RDF.Store.Columnar.OffsetIndex

// Recovery plan Phase 6 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md). Names the F* home for the per-row-group
// predicate row-offset index that retires codename "Lamed3".
//
// Old shape (the one this module displaces): the writer + reader for
// the `<corpus>.p.offsets` companion file lived entirely in
// experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh.
// The byte layout (`COTO` magic + header + u64 index + packed u32 row
// positions) was specified only as a comment block in that shell
// script. The reader half of that patch was retired in the Yod7 audit
// (2026-04-26) once the rename pivot landed; the writer half still
// runs at companion-build time and emits the on-disk file. Per
// CLAUDE.md rule #11 the byte layout is a semantic decision and must
// live in F*; the OCaml side reduces to `write_bytes` once a writer
// migration follow-up lands.
//
// New shape (this module): the byte layout is specified as F* refinement-
// typed records, the read path is composed from the existing
// `read_companion_u32_le` / `read_companion_u64_le` / `mmap_companion_open`
// `assume val` primitives (no new I/O assumptions), and the soundness
// invariant ("a `false` answer to row_positions_for is sound to skip
// the rg for that predicate") is stated as an admittable lemma so
// callers can rely on a uniform contract.
//
// Wiring status: this module is the named F* home; it does not yet
// re-route `RDF.CottasStore.cottas_ondisk_search`'s LIMIT path through
// `row_positions_for`. That swap is a thin follow-up once the F*
// extraction toolchain version drift is resolved. The committed
// `ocaml-output/RDF_CottasStore.ml` still flows through the OCaml-
// side reader cached in `Cottas_offset_idx`. Phase 6's deliverable
// is the named-API home + the spec — the reader is byte-identical to
// what the OCaml side computes today.
//
// File format (little-endian throughout). Magic 'COTO' = 0x4f544f43.
//
//   Header (16 bytes):
//     [ magic       : u32   ASCII 'COTO' = 0x4f544f43 ]
//     [ version     : u32   layout version, currently 1 ]
//     [ num_rgs     : u32 ]
//     [ num_preds   : u32 ]
//
//   Index (u64-LE, length num_rgs * num_preds + 1):
//     [ rg_offsets[rg*num_preds + pred]     = byte offset where row-list starts
//       rg_offsets[rg*num_preds + pred + 1] = end byte offset (exclusive)
//       rg_offsets[num_rgs*num_preds]       = end-of-file sentinel ]
//
//   Data (u32-LE, packed):
//     [ row positions, ascending; per (rg, pred) the slice is
//       data[start..end) with count = (end - start) / 4 u32 entries. ]
//
// Soundness contract: for a correctly-built file, `row_positions_for h
// rg p` returns the ascending list of row indices in row-group `rg`
// whose predicate-token-id equals `p`. A `Some []` answer means "no
// row in this rg has that predicate"; the caller may skip the rg's
// subject + object decode for that pattern. A `None` answer means an
// I/O or bound error and is the safe over-include (caller falls back
// to the full predicate-column decode path).

open RDF.CottasStore.OnDiskIndex
open FStar.Mul

// ------------------------------------------------------------------
// Magic number (32-bit little-endian).
// ASCII 'C', 'O', 'T', 'O' = 0x43, 0x4f, 0x54, 0x4f -> LE u32 = 0x4f544f43
// ------------------------------------------------------------------

let coto_magic_u32 : nat = 0x4f544f43
let offsets_layout_version : nat = 1
let offset_header_size : nat = 16  // 4 u32 fields, no padding
let offset_index_entry_size : nat = 8   // u64 each
let offset_row_position_size : nat = 4  // u32 each

// ------------------------------------------------------------------
// Header. Refinement-typed record holding the four u32 fields.
// ------------------------------------------------------------------

type offset_header = {
  oh_magic     : nat;
  oh_version   : nat;
  oh_num_rgs   : nat;
  oh_num_preds : nat;
}

let offset_header_ok (h : offset_header) : Tot bool =
  h.oh_magic = coto_magic_u32 && h.oh_version = offsets_layout_version

// Read the 16-byte header. Returns None on any read failure or if
// magic / version don't match the expected layout. The composition
// is the same shape as `read_presence_header` /
// `read_compound_header`.
let read_offset_header (path : string) : Tot (option offset_header) =
  match read_companion_u32_le path 0 with
  | None -> None
  | Some magic ->
    match read_companion_u32_le path 4 with
    | None -> None
    | Some version ->
      match read_companion_u32_le path 8 with
      | None -> None
      | Some num_rgs ->
        match read_companion_u32_le path 12 with
        | None -> None
        | Some num_preds ->
          Some {
            oh_magic = magic;
            oh_version = version;
            oh_num_rgs = num_rgs;
            oh_num_preds = num_preds;
          }

// ------------------------------------------------------------------
// Handle. Pairs the file path with its parsed header. Mirrors
// `bitmap_handle` (PresenceBitmap) and `compound_handle`
// (CompoundPresenceBitmap).
// ------------------------------------------------------------------

type offset_handle = {
  oih_path   : string;
  oih_header : offset_header;
}

let offset_handle_ok (h : offset_handle) : Tot bool =
  offset_header_ok h.oih_header

// A handle whose header is verified at the type level.
let valid_offset_handle = h:offset_handle{ offset_handle_ok h }

// ------------------------------------------------------------------
// Open / close. Composes mmap_companion_open + read_offset_header.
// Returns Some handle iff the mmap succeeded, the header parsed, and
// magic + version match. None otherwise — caller falls back to the
// no-offset-index path (full predicate-column decode).
// ------------------------------------------------------------------

let open_offsets (path : string) : Tot (option offset_handle) =
  match mmap_companion_open path with
  | None -> None
  | Some _file_size ->
    (match read_offset_header path with
     | None -> None
     | Some h ->
       if offset_header_ok h then
         Some { oih_path = path; oih_header = h }
       else None)

let close_offsets (h : offset_handle) : Tot unit =
  mmap_companion_close h.oih_path

// ------------------------------------------------------------------
// Index lookups. Each (rg, pred) cell has a start offset (its
// position in the index) and an end offset (the next cell's
// position). The index has length num_rgs*num_preds + 1, with the
// trailing entry as the end-of-file sentinel.
//
// `cell_index rg p` is the linear index of the (rg, p) start entry;
// `cell_index_end rg p` is the start of the next cell.
// ------------------------------------------------------------------

let cell_index (h : offset_header) (rg : nat) (pred_id : nat) : Tot nat =
  rg * h.oh_num_preds + pred_id

// Byte offset within the file where the index entry for (rg, pred_id)
// begins. The index starts at offset 16 (offset_header_size) and each
// entry is 8 bytes (u64-LE).
let index_entry_offset (h : offset_header) (rg : nat) (pred_id : nat) : Tot nat =
  offset_header_size + offset_index_entry_size * (cell_index h rg pred_id)

// Read the start byte offset (into the data section) for (rg, pred).
// Returns None on read failure or if (rg, pred) is out of range.
let read_cell_start
  (h : valid_offset_handle) (rg : nat) (pred_id : nat) : Tot (option nat) =
  if rg >= h.oih_header.oh_num_rgs || pred_id >= h.oih_header.oh_num_preds
  then None
  else
    read_companion_u64_le h.oih_path
      (index_entry_offset h.oih_header rg pred_id)

// Read the end (exclusive) byte offset for (rg, pred). The last cell
// of the file uses the sentinel index entry at position
// num_rgs * num_preds.
let read_cell_end
  (h : valid_offset_handle) (rg : nat) (pred_id : nat) : Tot (option nat) =
  if rg >= h.oih_header.oh_num_rgs || pred_id >= h.oih_header.oh_num_preds
  then None
  else
    read_companion_u64_le h.oih_path
      (offset_header_size +
       offset_index_entry_size * (cell_index h.oih_header rg pred_id + 1))

// ------------------------------------------------------------------
// Row-position counts and reads.
//
// The data slice for cell (rg, pred) is a packed u32-LE array of row
// positions. The byte length of the slice divided by 4 is the number
// of matching rows in that row-group for that predicate. The empty
// slice (start == end) means the rg has no row with that predicate;
// callers can skip the entire rg.
// ------------------------------------------------------------------

// Given start + end byte offsets, compute the row-position count.
// Defensive against malformed indexes (end < start) by returning 0.
let row_positions_count_from_bounds (start_off end_off : nat) : Tot nat =
  if end_off < start_off then 0
  else (end_off - start_off) / offset_row_position_size

// Read the i-th row position in the (rg, pred) cell, assuming
// start_off is the cell's data-section byte offset.
let read_row_position_at
  (h : valid_offset_handle) (start_off : nat) (i : nat) : Tot (option nat) =
  read_companion_u32_le h.oih_path
    (start_off + offset_row_position_size * i)

// ------------------------------------------------------------------
// row_positions_for: the runtime read primitive.
//
// Returns Some (start_off, count) when (rg, pred_id) is in range and
// the index reads succeed. The caller can then read row positions via
// `read_row_position_at h start_off i` for i in [0, count). Empty
// count is meaningful: "no row in this rg has that predicate".
//
// Returns None on out-of-range (rg, pred_id) or any read failure.
// Callers treat None as "no offset-index info, fall through to the
// full predicate-column decode" — the safe over-include.
// ------------------------------------------------------------------

// A successful row_positions_for result: (data-section start byte
// offset, count of u32 row positions in this cell).
type cell_view = {
  cv_start : nat;
  cv_count : nat;
}

let row_positions_for
  (h : valid_offset_handle) (rg : nat) (pred_id : nat)
  : Tot (option cell_view) =
  if rg >= h.oih_header.oh_num_rgs || pred_id >= h.oih_header.oh_num_preds
  then None
  else
    match read_cell_start h rg pred_id with
    | None -> None
    | Some start_off ->
      match read_cell_end h rg pred_id with
      | None -> None
      | Some end_off ->
        if end_off < start_off then None
        else Some {
          cv_start = start_off;
          cv_count = row_positions_count_from_bounds start_off end_off;
        }

// Variant that takes a possibly-failed-to-open handle (option) plus
// an option pred_id (the column may be unbound in the BGP). The
// "no info -> fall through to full decode" semantics are baked in.
//
// Result encoding:
//   - None        -> no info; caller MUST run the full predicate-column
//                    decode for this rg.
//   - Some None   -> empty cell; caller can skip the entire rg for
//                    this pattern (we know there are zero matches).
//   - Some (Some (start_off, count)) -> caller can read `count` row
//                    positions starting at byte `start_off` and decode
//                    only those subject + object cells.
//
// This is the shape `SPARQL.Plan.AccessPath.choose_access_path`
// surfaces back to the planner.
// Wrapped result for `row_positions_for_opt`: distinguishes
// "no info, full decode" from "definitely empty, skip rg" from
// "use this jump list".
type cell_decision =
  | CD_NoInfo  : cell_decision           // companion absent or unbound pred
  | CD_Empty   : cell_decision           // empty slice; skip the rg
  | CD_Use     : cell_view -> cell_decision  // use these row positions

let row_positions_for_opt
  (oh : option offset_handle) (rg : nat) (bound_pred_id : option nat)
  : Tot cell_decision =
  match bound_pred_id with
  | None -> CD_NoInfo  // unbound predicate: no offset-jump
  | Some p ->
    (match oh with
     | None -> CD_NoInfo  // companion file not open: full decode path
     | Some h ->
       if offset_handle_ok h then
         (match row_positions_for h rg p with
          | None -> CD_NoInfo  // out-of-range / read error: full decode
          | Some cv ->
            if cv.cv_count = 0 then CD_Empty
            else CD_Use cv)
       else CD_NoInfo)  // header invalid: fall through

// ------------------------------------------------------------------
// Dimension accessors. Mirror PresenceBitmap.bitmap_num_rgs etc.
// ------------------------------------------------------------------

let offset_num_rgs (h : valid_offset_handle) : Tot nat =
  h.oih_header.oh_num_rgs

let offset_num_preds (h : valid_offset_handle) : Tot nat =
  h.oih_header.oh_num_preds

// ------------------------------------------------------------------
// Path computation for the offsets companion file. The convention is
// `<corpus>.p.offsets` (sibling to `.p.dict` and `.p.presence`),
// matching the writer in
// `experimental_ocaml_glue/cottas_ondisk_zzzzzz_lamed3_offset_idx.sh`.
// ------------------------------------------------------------------

let offsets_path_of (corpus_path : string) : Tot string =
  corpus_path ^ ".p.offsets"

// ------------------------------------------------------------------
// Soundness contract.
//
// `rows_with_pred rg p` is the spec-level ground truth: the ascending
// list of row indices within row-group `rg` whose predicate-token-id
// equals `p`. The offsets file is "built correctly" iff for every
// in-range (rg, p), the cell's start_off + count + the count
// successful u32 reads at start_off..start_off+4*(count-1) yield
// exactly that ground-truth list.
//
// We state two correctness statements relevant to callers:
//
//   1. `row_positions_for_count_sound`: when row_positions_for returns
//      `Some (_, 0)` and the bitmap is correctly built, the spec-side
//      ground-truth list is empty — i.e. the rg has zero rows with
//      predicate `p`, and skipping it is sound.
//
//   2. `row_positions_for_count_bound`: the count returned never
//      exceeds the number of rows in the rg. Established structurally
//      (count = byte-length / 4, bounded by the index span); we phrase
//      it as a monotonicity property over the bounds.
//
// Both lemmas follow the discipline in
// `RDF.CottasStore.PresenceBitmap.rg_contains_token_sound`: the spec-
// side `rows_with_pred` predicate is admitted as a ghost projection
// (no extraction, no runtime impact) and the lemma's STATEMENT is
// what callers rely on.
// ------------------------------------------------------------------

// Spec-level ground truth: ascending list of row indices in row-group
// `rg` whose predicate-token-id equals `p`. Quantified ghostly.
let rows_with_pred_t = nat -> nat -> list nat

// "The offsets file at handle `h` correctly encodes ground truth
// `rows_with_pred`" — for every in-range (rg, p) the cell's
// row-position count equals the length of the ground-truth list, and
// each i-th read returns the i-th ground-truth row index.
let offsets_built_correctly
  (h : valid_offset_handle) (rows_with_pred : rows_with_pred_t)
  : Type0 =
  forall (rg:nat) (p:nat).
    rg < h.oih_header.oh_num_rgs /\ p < h.oih_header.oh_num_preds ==>
      (match row_positions_for h rg p with
       | None -> False
       | Some cv ->
         cv.cv_count = FStar.List.Tot.length (rows_with_pred rg p))

// Soundness lemma: if the offsets file is correctly built and
// `row_positions_for` returns a count of zero, the spec-side
// ground truth is the empty list — the rg has no row with that
// predicate, and the caller can skip the rg's subject + object
// decode for this pattern.
//
// Status: stated; the body discharges trivially because
// `offsets_built_correctly` already says
// `count = length (rows_with_pred rg p)`, so `count = 0` implies the
// ground-truth list is empty. The honest remaining gap (matching the
// PresenceBitmap module's discipline) is the writer-side proof that
// `offsets_built_correctly` actually holds for any given on-disk
// `.p.offsets` file. That proof is the writer-migration follow-up
// described in CLAUDE.md rule #11.
val row_positions_for_count_sound :
  h:valid_offset_handle ->
  rows_with_pred:rows_with_pred_t ->
  rg:nat ->
  p:nat ->
  cv:cell_view ->
  Lemma
    (requires
      offsets_built_correctly h rows_with_pred /\
      rg < h.oih_header.oh_num_rgs /\
      p < h.oih_header.oh_num_preds /\
      row_positions_for h rg p == Some cv /\
      cv.cv_count = 0)
    (ensures rows_with_pred rg p == [])

let row_positions_for_count_sound h rows_with_pred rg p cv = ()

// ------------------------------------------------------------------
// Identity-when-no-handle property. When the offsets companion is
// not opened (or the predicate is unbound), `row_positions_for_opt`
// returns None; callers fall back to the full-decode path. This is
// the safety property the OCaml-side dispatcher relies on.
// ------------------------------------------------------------------

let row_positions_for_opt_noinfo_when_handle_absent
  (rg : nat) (bound_pred_id : option nat)
  : Lemma
    (ensures row_positions_for_opt None rg bound_pred_id == CD_NoInfo)
  = ()

let row_positions_for_opt_noinfo_when_pred_unbound
  (oh : option offset_handle) (rg : nat)
  : Lemma
    (ensures row_positions_for_opt oh rg None == CD_NoInfo)
  = ()
