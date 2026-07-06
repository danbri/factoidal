module HDT.Triples

// HDT (Header-Dictionary-Triples) BitmapTriples navigation — stage 3
// of the program plan in
// docs/designissues/2026-07-06-hdt-program-plan.md. Builds on stage 1
// (HDT.Container.fst, container skeleton + section boundaries) and
// stage 2 (HDT.Dictionary.fst, PFC dictionary decode + id<->term
// mapping), neither of which this module modifies: both are already
// registered in the build, and every function here is additive.
//
// Scope of this module (stage 3):
//   - Decode the Triples section's four sub-structures, in the order
//     hdt-cpp actually writes them (confirmed byte-for-byte against
//     both vendored fixtures during scoping, NOT assumed from the
//     spec-page prose): bitmap(Y), bitmap(Z), log-array(Y),
//     log-array(Z). ArrayY holds one predicate ID per
//     (subject, predicate) pair, in subject-major order; BitmapY[i]=1
//     marks the LAST such pair for its subject. ArrayZ holds one
//     object ID per (subject, predicate, object) triple, in the same
//     order; BitmapZ[i]=1 marks the last object of its
//     (subject, predicate) pair. Subject IDs are exactly the
//     dictionary's subject-role ID space (HDT.Dictionary's
//     Role_Subject numbering: shared IDs 1..Nshared, then the
//     subjects section) — the SPO forest is indexed by that same
//     1-based ID space, cross-checked in bin/hdt-probe/check.sh
//     against `HDT.Dictionary.hdt_role_max_id`.
//   - CRC32C (payload) and CRC8 (preamble) validation of both
//     bitmaps, reusing `HDT.Dictionary`'s CRC primitives and its
//     already-proven-correct log-array CRC checks for ArrayY/ArrayZ
//     (they are ordinary `hdt_log_array_info` values, no new CRC code
//     needed for them).
//   - Naive rank1/select1 over a decoded bitmap: `rank1 s bm i` is the
//     count of 1-bits in bit positions `[0, i]` inclusive (linear
//     scan, no auxiliary index); `select1 s bm k` is the bit position
//     of the `(k+1)`-th 1-bit for 0-based `k` (linear scan, stops at
//     the target). This choice of indexing gives the identity this
//     module's regression pins check on both fixtures:
//     `rank1 s bm (select1 s bm k) = Some (k + 1)`.
//   - The stage-5 swap seam: every caller above this line reaches a
//     bitmap ONLY through `rank1`/`select1`/`children_range` — never
//     through `bit_at` or the raw byte offsets directly except inside
//     those three functions' own definitions. Stage 5 replaces the
//     linear scans in `rank1`/`select1` with an indexed structure
//     (superblock/block popcount counters, per the program plan's
//     stage 5 section) behind the SAME names and signatures;
//     `children_range`, `collect_range`, `walk_y_positions`,
//     `hdt_triples_for_subject`, `hdt_enumerate_all` do not change.
//   - SPO navigation: `children_range` is the one range-decoding
//     primitive both tree levels use (parent index -> inclusive
//     `[lo, hi]` child-array range); `hdt_triples_for_subject` walks
//     subject -> Y-range -> (predicate, Z-range) -> object, and
//     `hdt_enumerate_all` walks every subject in ID order. Both
//     validated end to end against real fixture bytes during scoping
//     (a standalone Python re-implementation of this exact algorithm
//     reproduced both fixtures' full triple sets before this F* module
//     was written).
//
// I/O boundary: unchanged from stages 1-2 — no new assume val, no new
// OCaml glue. Every byte access goes through `HDT.Container.hex_byte`
// (via `HDT.Dictionary.la_bits_acc`) over the same hex-encoded
// whole-file string stage 1 already reads via `Parquet.Footer`'s
// generic byte-range reader.

open FStar.Mul
open FStar.List.Tot

module U32 = FStar.UInt32
module HC  = HDT.Container
module HD  = HDT.Dictionary

// ---------------------------------------------------------------------------
// Triples-section inventory: the two bitmaps + two log-arrays,
// decoded in file order directly after the Triples control
// information (`HC.hdt_inventory.inv_triples_data_start`).
// ---------------------------------------------------------------------------

type hdt_triples_info = {
  tri_bitmap_y : HC.hdt_bitmap_info;      // BitmapY: last-predicate-of-subject markers
  tri_bitmap_z : HC.hdt_bitmap_info;      // BitmapZ: last-object-of-(s,p) markers
  tri_array_y  : HC.hdt_log_array_info;   // ArrayY: predicate IDs, one per (s,p) pair
  tri_array_z  : HC.hdt_log_array_info;   // ArrayZ: object IDs, one per triple
}

let parse_triples_info (s:string) (pos:nat) : option hdt_triples_info =
  match HC.parse_bitmap_info s pos with
  | None -> None
  | Some bmy ->
    (match HC.parse_bitmap_info s bmy.HC.bm_end with
     | None -> None
     | Some bmz ->
       (match HC.parse_log_array_info s bmz.HC.bm_end with
        | None -> None
        | Some lay ->
          (match HC.parse_log_array_info s lay.HC.la_end with
           | None -> None
           | Some laz ->
             Some {
               tri_bitmap_y = bmy;
               tri_bitmap_z = bmz;
               tri_array_y = lay;
               tri_array_z = laz;
             })))

// Entry point combining stage 1's inventory with this stage's own
// section decode. Loud None on truncation, wrong bitmap/log-array
// type byte, or any other structural mismatch — the Triples CI itself
// is already validated (CRC16) by `HC.hdt_parse_inventory_hex`, so a
// truncated file that still has a valid CI but a cut-off payload
// fails HERE rather than at the whole-inventory stage.
let hdt_read_triples (s:string) (inv:HC.hdt_inventory) : option hdt_triples_info =
  parse_triples_info s inv.HC.inv_triples_data_start

// ---------------------------------------------------------------------------
// CRC validation: bitmap preamble CRC8 + payload CRC32C (the two
// flavours stage 1 does not check for bitmaps). ArrayY/ArrayZ are
// ordinary `hdt_log_array_info` values, so their CRCs reuse
// `HDT.Dictionary`'s existing log-array CRC checks verbatim.
// ---------------------------------------------------------------------------

let bm_preamble_len (bm:HC.hdt_bitmap_info) : nat =
  HD.nat_sub (HD.nat_sub bm.HC.bm_data_start 1) bm.HC.bm_start

let bm_preamble_crc8_pos (bm:HC.hdt_bitmap_info) : nat =
  HD.nat_sub bm.HC.bm_data_start 1

let bm_preamble_crc8_ok (s:string) (bm:HC.hdt_bitmap_info) : bool =
  match HD.crc8_range s bm.HC.bm_start (bm_preamble_len bm) 0ul,
        HD.read_u8 s (bm_preamble_crc8_pos bm) with
  | Some c, Some stored -> U32.v c = stored
  | _, _ -> false

let bm_data_crc32_ok (s:string) (bm:HC.hdt_bitmap_info) : bool =
  match HD.crc32c_of_range s bm.HC.bm_data_start bm.HC.bm_data_bytes,
        HD.read_u32_le s (HD.nat_sub bm.HC.bm_end 4) with
  | Some c, Some stored -> U32.v c = stored
  | _, _ -> false

let bitmap_crc_ok (s:string) (bm:HC.hdt_bitmap_info) : bool =
  bm_preamble_crc8_ok s bm && bm_data_crc32_ok s bm

// All six CRC checks the Triples section carries: both bitmaps' own
// preamble+payload, both log-arrays' preamble+payload.
let triples_crc_ok (s:string) (t:hdt_triples_info) : bool =
  bitmap_crc_ok s t.tri_bitmap_y &&
  bitmap_crc_ok s t.tri_bitmap_z &&
  HD.la_preamble_crc8_ok s t.tri_array_y &&
  HD.la_data_crc32_ok s t.tri_array_y &&
  HD.la_preamble_crc8_ok s t.tri_array_z &&
  HD.la_data_crc32_ok s t.tri_array_z

// ---------------------------------------------------------------------------
// Bit access + naive rank1/select1 — the stage-5 swap seam (see the
// module banner). `bit_at` reads bitmap bit `i` by treating the
// bitmap's data range as a 1-bit-wide log-array entry, reusing
// `HDT.Dictionary.la_bits_acc` (same little-endian-within-byte bit
// order stage 2 already validated for log-arrays; confirmed against
// real bitmap bytes during scoping — the two structures share one
// byte-level bit convention in hdt-cpp).
// ---------------------------------------------------------------------------

let bit_at (s:string) (bm:HC.hdt_bitmap_info) (i:nat) : option bool =
  if i >= bm.HC.bm_numbits then None
  else
    match HD.la_bits_acc s bm.HC.bm_data_start i 1 1 0 with
    | None -> None
    | Some v -> Some (v = 1)

// rank1_upto s bm pos fuel acc: count of 1-bits among positions
// [pos, pos+fuel) added to `acc`. `rank1 s bm i` calls this with
// pos=0, fuel=i+1 so it counts bit positions [0, i] inclusive.
let rec rank1_upto (s:string) (bm:HC.hdt_bitmap_info) (pos:nat) (fuel:nat) (acc:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then Some acc
  else
    match bit_at s bm pos with
    | None -> None
    | Some b -> rank1_upto s bm (pos + 1) (fuel - 1) (if b then acc + 1 else acc)

let rank1 (s:string) (bm:HC.hdt_bitmap_info) (i:nat) : option nat =
  if i >= bm.HC.bm_numbits then None
  else rank1_upto s bm 0 (i + 1) 0

// select1_scan s bm pos fuel target seen: linear scan starting at
// `pos` with `fuel` remaining positions and `seen` ones already
// counted before `pos`; returns the position of the bit that brings
// the running count to `target`.
let rec select1_scan (s:string) (bm:HC.hdt_bitmap_info) (pos:nat) (fuel:nat)
  (target:nat) (seen:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    match bit_at s bm pos with
    | None -> None
    | Some b ->
      let seen' = if b then seen + 1 else seen in
      if b && seen' = target then Some pos
      else select1_scan s bm (pos + 1) (fuel - 1) target seen'

// select1 s bm k: position of the (k+1)-th 1-bit, 0-based k — chosen
// so `rank1 s bm (select1 s bm k) = Some (k + 1)` (checked as a
// regression pin over every valid k of both fixture bitmaps in
// bin/hdt-probe/check.sh, rather than as a from-scratch universal
// proof — the naive scan's correctness is exercised exhaustively
// against real data at this stage; stage 5's indexed replacement is
// where a from-scratch proof pays for itself, over a structure that
// no longer degenerates to "re-scan everything").
let select1 (s:string) (bm:HC.hdt_bitmap_info) (k:nat) : option nat =
  select1_scan s bm 0 bm.HC.bm_numbits (k + 1) 0

// ---------------------------------------------------------------------------
// SPO forest navigation. `children_range` is the one range-decoding
// primitive both tree levels (subject -> Y-range, Y-position ->
// Z-range) use: parent index `idx` (0-based) maps to an inclusive
// `[lo, hi]` range in the child array, delimited by consecutive
// 1-bits of the level's bitmap. Verified against real fixture data
// during scoping (a standalone re-implementation walked both
// fixtures' full SPO trees and reproduced their exact triple sets).
// ---------------------------------------------------------------------------

let children_range (s:string) (bm:HC.hdt_bitmap_info) (idx:nat) : option (nat & nat) =
  match select1 s bm idx with
  | None -> None
  | Some hi ->
    if idx = 0 then Some (0, hi)
    else
      match select1 s bm (idx - 1) with
      | None -> None
      | Some prev -> Some (prev + 1, hi)

// Read `count` consecutive entries of a log-array starting at
// `pos` (0-based), in order. Generic over ArrayY/ArrayZ.
let rec collect_range (s:string) (la:HC.hdt_log_array_info) (pos:nat) (count:nat)
  (acc:list nat)
  : Tot (option (list nat)) (decreases count) =
  if count = 0 then Some (List.Tot.rev acc)
  else
    match HD.la_entry s la pos with
    | None -> None
    | Some v -> collect_range s la (pos + 1) (count - 1) (v :: acc)

let range_count (lo:nat) (hi:nat) : nat = if hi >= lo then hi - lo + 1 else 0

// Walk `count` consecutive Y-positions starting at `y`, emitting one
// (predicate, object) pair per object in each position's Z-range, in
// order.
let rec walk_y_positions (s:string) (t:hdt_triples_info) (y:nat) (count:nat)
  (acc:list (nat & nat))
  : Tot (option (list (nat & nat))) (decreases count) =
  if count = 0 then Some acc
  else
    match HD.la_entry s t.tri_array_y y with
    | None -> None
    | Some p ->
      (match children_range s t.tri_bitmap_z y with
       | None -> None
       | Some (zlo, zhi) ->
         (match collect_range s t.tri_array_z zlo (range_count zlo zhi) [] with
          | None -> None
          | Some objs ->
            let pairs = List.Tot.map (fun o -> (p, o)) objs in
            walk_y_positions s t (y + 1) (count - 1) (acc @ pairs)))

// The first pattern resolver: subject ID -> its (predicate, object)
// ID pairs, in the file's own (subject, predicate, object) order.
// `subj` is a 1-based ID in the dictionary's subject-role ID space
// (`HDT.Dictionary.Role_Subject`).
let hdt_triples_for_subject (s:string) (t:hdt_triples_info) (subj:pos)
  : option (list (nat & nat)) =
  match children_range s t.tri_bitmap_y (subj - 1) with
  | None -> None
  | Some (ylo, yhi) -> walk_y_positions s t ylo (range_count ylo yhi) []

// ---------------------------------------------------------------------------
// Whole-container enumeration.
// ---------------------------------------------------------------------------

// Total number of triples: ArrayZ carries exactly one entry per
// triple (its 1-bits mark the last object of each (s,p) pair, but
// EVERY entry — 1-bit or not — is one object of one triple).
let hdt_triple_count (t:hdt_triples_info) : nat = t.tri_array_z.HC.la_numentries

// Number of subjects with data: the count of 1-bits in BitmapY (each
// subject that appears ends its Y-range with exactly one 1-bit).
// Derived from the bitmap alone — cross-checked in
// bin/hdt-probe/check.sh against `HDT.Dictionary.hdt_role_max_id`
// (Role_Subject), an independent count from the dictionary section
// sizes.
let hdt_num_subjects (s:string) (t:hdt_triples_info) : option nat =
  let bm = t.tri_bitmap_y in
  if bm.HC.bm_numbits = 0 then Some 0
  else rank1 s bm (bm.HC.bm_numbits - 1)

type hdt_id_triple = {
  it_s : nat;
  it_p : nat;
  it_o : nat;
}

let rec hdt_enumerate_subjects (s:string) (t:hdt_triples_info) (subj:pos) (fuel:nat)
  (acc:list hdt_id_triple)
  : Tot (option (list hdt_id_triple)) (decreases fuel) =
  if fuel = 0 then Some acc
  else
    match hdt_triples_for_subject s t subj with
    | None -> None
    | Some pairs ->
      let new_triples =
        List.Tot.map (fun (p, o) -> { it_s = subj; it_p = p; it_o = o }) pairs in
      hdt_enumerate_subjects s t (subj + 1) (fuel - 1) (acc @ new_triples)

// Full dump as id-triples, in (subject, Y-position, Z-position) file
// order — i.e. subject-major, then predicate, then object.
let hdt_enumerate_all (s:string) (t:hdt_triples_info) : option (list hdt_id_triple) =
  match hdt_num_subjects s t with
  | None -> None
  | Some 0 -> Some []
  | Some n -> hdt_enumerate_subjects s t 1 n []
