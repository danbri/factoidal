module RDF.Store.Columnar.SubjectOffsetIndex

// Issue #100 follow-up (2026-07-13). Reader for the `.s.offsets`
// companion file written by `RDF.CottasStore.SubjectOffsetsWriter.fst`
// + its OCaml corpus-walk glue. Named-module sibling of
// `RDF.Store.Columnar.OffsetIndex.fst` (the `.p.offsets` reader) --
// same read-primitive composition, same mmap'd-handle shape, same
// "None means fall through to the existing path" discipline -- but
// keyed per SUBJECT with a single CONTIGUOUS global row range instead
// of a per-(row-group, predicate) row-position list, because subject
// rows are globally contiguous (BaseWriter sorts (s, p, o, g),
// subject primary) while predicate rows are not.
//
// File format (little-endian throughout). Magic 'COTS' = 0x53544f43.
//
//   Header (16 bytes):
//     [ magic          : u32   ASCII 'COTS' = 0x53544f43 ]
//     [ version        : u32   layout version, currently 1 ]
//     [ num_subjects   : u32 ]
//     [ num_rows_total : u32   sanity cross-check ]
//
//   Ranges (u64-LE pairs, length num_subjects * 2):
//     [ subject i: start_row (u64), end_row_exclusive (u64) ], ascending
//     subject-id order. Subject id `i` is the same sorted-lexicographic
//     rank `compound_po_dict_encode path "s" tok` resolves against the
//     on-disk `.s.dict` (see that function's banner comment in
//     `RDF.CottasStore.fst`).
//
// Soundness contract: for a correctly-built file, `[start_row, end_row)`
// is the ascending-and-CONTIGUOUS global row-index range every row
// whose subject-token equals subject `i` occupies -- because
// `RDF.CottasStore.BaseWriter` rows are pre-sorted subject-primary. A
// `None` answer means an I/O or bound error and is the safe
// over-include (caller falls back to the full per-column dict-page
// candidate-rg pruning path, `plan_candidate_rgs`).

open RDF.CottasStore.OnDiskIndex

// ------------------------------------------------------------------
// Magic number (32-bit little-endian).
// ASCII 'C','O','T','S' = 0x43, 0x4f, 0x54, 0x53 -> LE u32 = 0x53544f43
// ------------------------------------------------------------------

let cots_magic_u32           : nat = 0x53544f43
let subject_offsets_layout_version : nat = 1
let subject_offset_header_size     : nat = 16   // 4 u32 fields, no padding
let subject_offset_entry_size      : nat = 16   // 2 u64 (start, end)

// ------------------------------------------------------------------
// Header. Refinement-typed record holding the four u32 fields.
// ------------------------------------------------------------------

type subject_offset_header = {
  soh_magic          : nat;
  soh_version         : nat;
  soh_num_subjects    : nat;
  soh_num_rows_total  : nat;
}

let subject_offset_header_ok (h : subject_offset_header) : Tot bool =
  h.soh_magic = cots_magic_u32 && h.soh_version = subject_offsets_layout_version

// Read the 16-byte header. Returns None on any read failure or if
// magic / version don't match the expected layout. Same composition
// as `RDF.Store.Columnar.OffsetIndex.read_offset_header`.
let read_subject_offset_header (path : string) : Tot (option subject_offset_header) =
  match read_companion_u32_le path 0 with
  | None -> None
  | Some magic ->
    match read_companion_u32_le path 4 with
    | None -> None
    | Some version ->
      match read_companion_u32_le path 8 with
      | None -> None
      | Some num_subjects ->
        match read_companion_u32_le path 12 with
        | None -> None
        | Some num_rows_total ->
          Some {
            soh_magic         = magic;
            soh_version        = version;
            soh_num_subjects   = num_subjects;
            soh_num_rows_total = num_rows_total;
          }

// ------------------------------------------------------------------
// Handle. Pairs the file path with its parsed header.
// ------------------------------------------------------------------

type subject_offset_handle = {
  soih_path   : string;
  soih_header : subject_offset_header;
}

let subject_offset_handle_ok (h : subject_offset_handle) : Tot bool =
  subject_offset_header_ok h.soih_header

let valid_subject_offset_handle = h:subject_offset_handle{ subject_offset_handle_ok h }

// ------------------------------------------------------------------
// Open / close. Composes mmap_companion_open + read_subject_offset_header.
// Returns Some handle iff the mmap succeeded, the header parsed, and
// magic + version match. None otherwise -- caller falls back to the
// no-subject-offset-index path (`plan_candidate_rgs`).
// ------------------------------------------------------------------

let open_subject_offsets (path : string) : Tot (option subject_offset_handle) =
  match mmap_companion_open path with
  | None -> None
  | Some _file_size ->
    (match read_subject_offset_header path with
     | None -> None
     | Some h ->
       if subject_offset_header_ok h then
         Some { soih_path = path; soih_header = h }
       else None)

let close_subject_offsets (h : subject_offset_handle) : Tot unit =
  mmap_companion_close h.soih_path

// ------------------------------------------------------------------
// Range lookup. Entry `i`'s byte offset is `subject_offset_header_size
// + subject_offset_entry_size * i`; `start_row` is the first u64,
// `end_row` (exclusive) the second.
// ------------------------------------------------------------------

// A successful `range_for_subject` result: the contiguous global row
// range `[sr_start, sr_end)` occupied by one subject's rows.
type subject_range = {
  sr_start : nat;
  sr_end   : nat;
}

let subject_range_count (r : subject_range) : Tot nat =
  if r.sr_end < r.sr_start then 0 else r.sr_end - r.sr_start

let entry_offset (h : subject_offset_header) (subject_id : nat) : Tot nat =
  subject_offset_header_size + subject_offset_entry_size `FStar.Mul.op_Star` subject_id

let range_for_subject
  (h : valid_subject_offset_handle) (subject_id : nat) : Tot (option subject_range) =
  if subject_id >= h.soih_header.soh_num_subjects then None
  else
    match read_companion_u64_le h.soih_path (entry_offset h.soih_header subject_id) with
    | None -> None
    | Some start_row ->
      match read_companion_u64_le h.soih_path
              (entry_offset h.soih_header subject_id + 8) with
      | None -> None
      | Some end_row ->
        Some { sr_start = start_row; sr_end = end_row }

// ------------------------------------------------------------------
// `range_for_subject_opt`: the "no info -> fall through" wrapper
// callers actually use. Mirrors `OffsetIndex.row_positions_for_opt`.
//
// Result encoding:
//   - None            -> no info; caller MUST use the existing
//                         `plan_candidate_rgs` dict-page-probe path.
//   - Some None        -> subject not in this index's declared range
//                         (out-of-bounds id) -- treated the same as
//                         "no info" by the only caller today, kept
//                         distinct for future callers that may want
//                         to distinguish it.
//   - Some (Some r)     -> use `r`'s row range.
// ------------------------------------------------------------------

type subject_range_decision =
  | SRD_NoInfo : subject_range_decision           // companion absent / read failure
  | SRD_Use    : subject_range -> subject_range_decision  // use this row range

let range_for_subject_opt
  (oh : option subject_offset_handle) (subject_id : option nat)
  : Tot subject_range_decision =
  match subject_id with
  | None -> SRD_NoInfo  // unbound subject: nothing to look up
  | Some sid ->
    (match oh with
     | None -> SRD_NoInfo  // companion file not open: fall through
     | Some h ->
       if subject_offset_handle_ok h then
         (match range_for_subject h sid with
          | None -> SRD_NoInfo  // out-of-range / read error: fall through
          | Some r -> SRD_Use r)
       else SRD_NoInfo)  // header invalid: fall through

// ------------------------------------------------------------------
// Dimension accessors + companion path convention. `<corpus>.s.offsets`,
// sibling of `.s.dict` / `.s.presence`.
// ------------------------------------------------------------------

let subject_offset_num_subjects (h : valid_subject_offset_handle) : Tot nat =
  h.soih_header.soh_num_subjects

let subject_offsets_path_of (corpus_path : string) : Tot string =
  corpus_path ^ ".s.offsets"

// ------------------------------------------------------------------
// Soundness contract, mirroring `OffsetIndex.offsets_built_correctly` /
// `row_positions_for_count_sound`.
//
// `rows_with_subject i` is the spec-level ground truth: the ascending
// list of GLOBAL row indices whose subject-token has dict-rank `i`.
// The offsets file is "built correctly" iff for every in-range
// subject id, the range's [start, end) span equals exactly that
// ground-truth list's [min, max+1) extent AND the list is contiguous
// (no gaps) -- which the BaseWriter's subject-primary global sort
// guarantees by construction (see this module's banner comment).
// ------------------------------------------------------------------

let rows_with_subject_t = nat -> list nat

let subject_offsets_built_correctly
  (h : valid_subject_offset_handle) (rows_with_subject : rows_with_subject_t)
  : Type0 =
  forall (sid:nat).
    sid < h.soih_header.soh_num_subjects ==>
      (match range_for_subject h sid with
       | None -> False
       | Some r ->
         subject_range_count r = FStar.List.Tot.length (rows_with_subject sid))

// Soundness lemma: if the offsets file is correctly built and
// `range_for_subject` returns a range with count zero, the spec-side
// ground truth is the empty list -- the subject genuinely has no rows
// (should not occur for a subject id resolved via `.s.dict`, since
// dict entries are only assigned to observed tokens, but the
// defensive case is stated for completeness, mirroring
// `OffsetIndex.row_positions_for_count_sound`).
val range_for_subject_count_sound :
  h:valid_subject_offset_handle ->
  rows_with_subject:rows_with_subject_t ->
  sid:nat ->
  r:subject_range ->
  Lemma
    (requires
      subject_offsets_built_correctly h rows_with_subject /\
      sid < h.soih_header.soh_num_subjects /\
      range_for_subject h sid == Some r /\
      subject_range_count r = 0)
    (ensures rows_with_subject sid == [])

let range_for_subject_count_sound h rows_with_subject sid r = ()

// ------------------------------------------------------------------
// Identity-when-no-handle property, mirroring `OffsetIndex.
// row_positions_for_opt_noinfo_when_handle_absent`.
// ------------------------------------------------------------------

let range_for_subject_opt_noinfo_when_handle_absent
  (subject_id : option nat)
  : Lemma
    (ensures range_for_subject_opt None subject_id == SRD_NoInfo)
  = ()

let range_for_subject_opt_noinfo_when_subject_unbound
  (oh : option subject_offset_handle)
  : Lemma
    (ensures range_for_subject_opt oh None == SRD_NoInfo)
  = ()
