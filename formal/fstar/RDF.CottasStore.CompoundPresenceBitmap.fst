module RDF.CottasStore.CompoundPresenceBitmap

// Nun4 (issue #104, 2026-04-26) — F*-source-of-truth read API for the
// compound (predicate, object) presence-bitmap companion file
// `<cottas>.po.presence` written by `Cottas_compound_po_writer`
// (experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh).
//
// This is the READER-side counterpart to the writer's WRITER-only patch,
// and it is the second F* presence-bitmap module — it mirrors
// RDF.CottasStore.PresenceBitmap.fst (Psi3, single-column) but answers
// the joint question "could rg `r` contain at least one row whose
// predicate-token-id is `p` AND object-token-id is `o`?". When both
// p and o are bound the compound bitmap is strictly more selective
// than the per-column AND.
//
// File format produced by the writer (little-endian throughout, see
// docs/designissues/2026-04-27-nun4-compound-po-writer.md):
//
//   Header (20 bytes):
//     [ magic   : u32  'COPO' = 0x4f504f43 (LE)         ]
//     [ version : u32  layout version, currently 1      ]
//     [ num_rgs : u32                                    ]
//     [ pred_dict_size : u32  cross-check vs .p.dict    ]
//     [ obj_dict_size  : u32  cross-check vs .o.dict    ]
//
//   Index:
//     [ rg_offsets : u64[num_rgs + 1]
//                    byte offsets into the file where each rg's
//                    pair-list begins; the trailing entry is the
//                    end-of-file sentinel. ]
//
//   Pair data (per rg, sorted lex (p_id, o_id)):
//     [ pairs : u64[]
//               per pair: bytes 0..3 = o_id (u32 LE)
//                         bytes 4..7 = p_id (u32 LE)
//               so the whole u64-LE = (p_id << 32) | o_id, and ascending
//               u64 sort == lex (p_id, o_id) — perfect for binary search
//               on a packed mmap'd region. ]
//
// All byte-range I/O delegates to OnDiskIndex.fst's `assume val`
// primitives. No new I/O assumptions are introduced here.

open RDF.CottasStore.OnDiskIndex
open FStar.Mul

// ------------------------------------------------------------------
// Magic numbers (32-bit little-endian).
// ASCII 'C', 'O', 'P', 'O' = 0x43, 0x4f, 0x50, 0x4f -> LE u32 = 0x4f504f43
// ------------------------------------------------------------------

let copo_magic_u32 : nat = 0x4f504f43
let compound_layout_version : nat = 1
let compound_header_size : nat = 20  // 5 u32 fields, no padding

// ------------------------------------------------------------------
// Header layout (refinement-typed record).
// ------------------------------------------------------------------

type compound_header = {
  ch_magic           : nat;
  ch_version         : nat;
  ch_num_rgs         : nat;
  ch_pred_dict_size  : nat;
  ch_obj_dict_size   : nat;
}

let compound_header_ok (h : compound_header) : Tot bool =
  h.ch_magic = copo_magic_u32 && h.ch_version = compound_layout_version

// Read the 20-byte header. Returns None on any read failure.
let read_compound_header (path : string) : Tot (option compound_header) =
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
        | Some pred_dict_size ->
          match read_companion_u32_le path 16 with
          | None -> None
          | Some obj_dict_size ->
            Some {
              ch_magic = magic;
              ch_version = version;
              ch_num_rgs = num_rgs;
              ch_pred_dict_size = pred_dict_size;
              ch_obj_dict_size = obj_dict_size;
            }

// ------------------------------------------------------------------
// Handle. Mirrors PresenceBitmap.bitmap_handle: pairs the file path
// with its parsed header.
// ------------------------------------------------------------------

type compound_handle = {
  ph_path   : string;
  ph_header : compound_header;
}

let compound_handle_ok (h : compound_handle) : Tot bool =
  compound_header_ok h.ph_header

// A handle whose header is verified at the type level.
let valid_compound_handle = h:compound_handle{ compound_handle_ok h }

// ------------------------------------------------------------------
// Open / close. Composes the I/O assume_vals from OnDiskIndex.fst
// (mmap_companion_open + read_compound_header).
// ------------------------------------------------------------------

let open_compound (path : string) : Tot (option compound_handle) =
  match mmap_companion_open path with
  | None -> None
  | Some _file_size ->
    (match read_compound_header path with
     | None -> None
     | Some h ->
       if compound_header_ok h then
         Some { ph_path = path; ph_header = h }
       else None)

let close_compound (h : compound_handle) : Tot unit =
  mmap_companion_close h.ph_path

// ------------------------------------------------------------------
// Per-rg payload offsets. Reads rg_offsets[k] and rg_offsets[k+1]
// from the index. Both are u64-LE at offset 20 + 8*k and 20 + 8*(k+1).
// ------------------------------------------------------------------

let read_rg_start_offset
  (h : valid_compound_handle) (rg : nat) : Tot (option nat) =
  if rg >= h.ph_header.ch_num_rgs then None
  else
    let eight : nat = 8 in
    let pos : nat = compound_header_size + eight * rg in
    read_companion_u64_le h.ph_path pos

let read_rg_end_offset
  (h : valid_compound_handle) (rg : nat) : Tot (option nat) =
  if rg >= h.ph_header.ch_num_rgs then None
  else
    let eight : nat = 8 in
    let pos : nat = compound_header_size + eight * (rg + 1) in
    read_companion_u64_le h.ph_path pos

// ------------------------------------------------------------------
// Read one packed pair at byte offset `pair_off`. The u64-LE value
// IS the pair code: (p_id << 32) | o_id with the writer's
// (o_id, p_id) layout in bytes 0..7. We return the raw u64.
// ------------------------------------------------------------------

let read_pair_code_at
  (path : string) (pair_off : nat) : Tot (option nat) =
  read_companion_u64_le path pair_off

// Encode (p, o) as the u64 pair code that the writer used:
// code = (p_id << 32) | o_id. This is what we binary-search for.
// We use multiplication instead of bit-shift for F*-purity (`*` is
// total over nats; bit-shifts are conservatively axiomatised).
let pair_code (p o : nat) : Tot nat =
  let two_pow_32 : nat = 4294967296 in
  p * two_pow_32 + o

// ------------------------------------------------------------------
// Binary search the rg's sorted pair list for the target code.
//
// The writer guarantees the per-rg list is sorted ascending by u64
// value (equivalently, lex (p_id, o_id) — see
// docs/designissues/2026-04-27-nun4-compound-po-writer.md). Standard
// inclusive-bounds binary search; fuel = npairs+1 as the totality
// witness.
//
// On any read error: returns true (safe over-include — caller will
// run a normal scan for the rg, find nothing, correctness preserved).
// This matches the safety discipline of PresenceBitmap.presence_test_bit
// line 329 ("None -> true").
// ------------------------------------------------------------------

let rec compound_bsearch
  (path : string) (start_off : nat) (npairs : nat)
  (target : nat)
  (lo : nat) (hi : nat) (fuel : nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then true               // safe over-include
  else if lo > hi then false          // not found, decisive negative
  else
    let mid : nat = lo + (hi - lo) / 2 in
    if mid >= npairs then true         // out of bounds, safe over-include
    else
      let eight : nat = 8 in
      let pair_off : nat = start_off + eight * mid in
      match read_pair_code_at path pair_off with
      | None -> true                   // I/O error, safe over-include
      | Some code ->
        if code = target then true
        else if code > target then
          if mid = 0 then false
          else compound_bsearch path start_off npairs target lo (mid - 1) (fuel - 1)
        else
          compound_bsearch path start_off npairs target (mid + 1) hi (fuel - 1)

// ------------------------------------------------------------------
// rg_could_contain_pair: per-rg test that some row in rg has both
// predicate-token = p AND object-token = o.
//
// Semantics:
//   - rg out of range -> false (no such rg, vacuously no row)
//   - p out of pred_dict_size -> false (token id absent at write time)
//   - o out of obj_dict_size  -> false
//   - Otherwise: read this rg's payload offsets, compute npairs from
//     (end - start) / 8, binary-search for (p << 32) | o.
//   - On any I/O failure: returns true (safe over-include).
// ------------------------------------------------------------------

let rg_could_contain_pair
  (h : valid_compound_handle)
  (rg : nat) (p : nat) (o : nat) : Tot bool =
  if rg >= h.ph_header.ch_num_rgs then false
  else if p >= h.ph_header.ch_pred_dict_size then false
  else if o >= h.ph_header.ch_obj_dict_size then false
  else
    match read_rg_start_offset h rg with
    | None -> true
    | Some start_off ->
      match read_rg_end_offset h rg with
      | None -> true
      | Some end_off ->
        if end_off < start_off then true
        else
          let eight : nat = 8 in
          let span : nat = end_off - start_off in
          let npairs : nat = span / eight in
          if npairs = 0 then false   // empty rg in the compound bitmap
          else
            let target : nat = pair_code p o in
            compound_bsearch h.ph_path start_off npairs target 0 (npairs - 1) (npairs + 1)

// ------------------------------------------------------------------
// rg_passes_pair: caller-shaped wrapper. `bound_p` and `bound_o` are
// option-typed token ids. Returns true iff the rg cannot be ruled out.
//
// Semantics:
//   - Both bound: rg_could_contain_pair
//   - Either unbound: true (compound bitmap has no opinion; the
//     per-column gate carries the work)
// ------------------------------------------------------------------

let rg_passes_pair
  (h : valid_compound_handle)
  (rg : nat)
  (bound_p : option nat) (bound_o : option nat) : Tot bool =
  match bound_p, bound_o with
  | Some p, Some o -> rg_could_contain_pair h rg p o
  | _, _ -> true

// ------------------------------------------------------------------
// option-handle convenience (mirrors PresenceBitmap.rg_could_contain
// shape). Returns true if the handle is None or invalid (safe
// over-include); callers AND this with the per-column gate.
// ------------------------------------------------------------------

let compound_rg_passes_pair
  (oh : option compound_handle)
  (rg : nat)
  (bound_p : option nat) (bound_o : option nat) : Tot bool =
  match oh with
  | None -> true
  | Some h ->
    if compound_handle_ok h then
      rg_passes_pair h rg bound_p bound_o
    else
      true

// ------------------------------------------------------------------
// AND-of-bitmaps composition: compose the per-column Psi3 gate with
// the compound joint-(p,o) gate. Returns true iff both pass; false
// from either is sound to skip.
// ------------------------------------------------------------------

let rg_passes_compound_and_per_column
  (rg : nat)
  (oh_compound : option compound_handle)
  (oh_s : option PresenceBitmap.bitmap_handle) (bound_s : option nat)
  (oh_p : option PresenceBitmap.bitmap_handle) (bound_p : option nat)
  (oh_o : option PresenceBitmap.bitmap_handle) (bound_o : option nat)
  : Tot bool =
  PresenceBitmap.rg_passes_all rg oh_s bound_s oh_p bound_p oh_o bound_o &&
  compound_rg_passes_pair oh_compound rg bound_p bound_o

// ------------------------------------------------------------------
// Soundness lemma — statement-level (mirrors PresenceBitmap line
// 197-219).
//
// `pair_occurs rg p o = true` iff some row in rg has predicate-token
// id `p` and object-token id `o`. This is the spec-level ground truth
// the writer's enumeration is supposed to satisfy. Quantified
// ghostly; never extracted.
//
// `compound_built_correctly h pair_occurs` says: for every (rg, p, o)
// in bounds, `rg_could_contain_pair h rg p o = pair_occurs rg p o`.
// The producer-side proof obligation (that the on-disk file actually
// satisfies this) is delegated to the writer per Section 3 of the
// design doc. Today the writer is in OCaml; the formal producer-side
// proof is open.
//
// The lemma `rg_could_contain_pair_sound` states the contrapositive
// that matters at the prune call site: a `false` result is sound to
// trust as "no row in this rg has that (p, o) pair". The lemma BODY
// is `()` — it discharges from the universal hypothesis exactly as
// PresenceBitmap.rg_contains_token_sound does.
// ------------------------------------------------------------------

let pair_occurs_pred_t = nat -> nat -> nat -> bool

let compound_built_correctly
  (h : valid_compound_handle) (pair_occurs : pair_occurs_pred_t) : Type0 =
  forall (rg : nat) (p : nat) (o : nat).
    rg < h.ph_header.ch_num_rgs /\
    p  < h.ph_header.ch_pred_dict_size /\
    o  < h.ph_header.ch_obj_dict_size ==>
      (rg_could_contain_pair h rg p o = pair_occurs rg p o)

val rg_could_contain_pair_sound :
  h:valid_compound_handle ->
  pair_occurs:pair_occurs_pred_t ->
  rg:nat -> p:nat -> o:nat ->
  Lemma
    (requires compound_built_correctly h pair_occurs /\
              rg < h.ph_header.ch_num_rgs /\
              p  < h.ph_header.ch_pred_dict_size /\
              o  < h.ph_header.ch_obj_dict_size /\
              rg_could_contain_pair h rg p o = false)
    (ensures pair_occurs rg p o = false)

let rg_could_contain_pair_sound h pair_occurs rg p o = ()

// As with PresenceBitmap.rg_contains_token_sound: the body `()`
// discharges the lemma here because the `requires` hypothesis
// `compound_built_correctly h pair_occurs` (a forall over rg, p, o
// with the stated equation) plus the in-bounds requirements give SMT
// exactly the equality it needs. The honest remaining gap is the
// producer-side obligation that `compound_built_correctly` actually
// holds for any given on-disk .po.presence file — that's the writer-
// side proof, currently informal (writer is OCaml).

// ------------------------------------------------------------------
// Dimension accessors.
// ------------------------------------------------------------------

let compound_num_rgs (h : valid_compound_handle) : Tot nat =
  h.ph_header.ch_num_rgs

let compound_pred_dict_size (h : valid_compound_handle) : Tot nat =
  h.ph_header.ch_pred_dict_size

let compound_obj_dict_size (h : valid_compound_handle) : Tot nat =
  h.ph_header.ch_obj_dict_size
