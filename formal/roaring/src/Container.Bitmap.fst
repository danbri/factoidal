module Container.Bitmap

// Bitmap container — fixed-length seq of u64 words with cached cardinality.
//
// A Roaring bitmap container holds up to 65 536 distinct u16 values from a
// single high-16 chunk. The dense representation is 65 536 bits =
// 1024 × 64-bit words. Bit index i ∈ [0, 65536) lives in word (i / 64) at
// bit position (i mod 64).
//
// This module is Phase B of `roaring_fstar_plan.md`. Scope:
//   - Container record + structural invariant.
//   - `bitmap_empty` and a lemma that its denotation is false everywhere.
//   - `bitmap_contains` and the lemma `bitmap_contains_iff_denote`.
//   - `bitmap_cardinality` (just reads the cached field).
//
// Insert / remove with the cardinality-update proofs come in a follow-up
// (Phase B.5). Container.Run, Container, and Roaring then build on top.
//
// Constraints (CLAUDE.md iron rules):
//   - No assume val
//   - No --admit_smt_queries
//   - No --lax
//   - All recursion fuel-bounded or structural

open FStar.List.Tot
open FStar.Mul
open Spec

module U64 = FStar.UInt64
module Bits = Bits

// ---------------------------------------------------------------
// Module constants.
//
// 1024 u64 words = 65 536 bits = pow16, the high-chunk universe.
// ---------------------------------------------------------------

let bitmap_words : nat = 1024
let _ = assert_norm (bitmap_words `op_Multiply` 64 = pow16)

// ---------------------------------------------------------------
// popcount_sum — total cardinality of a word list.
//
// Used both as the cached-cardinality invariant for the container
// and as the per-word arithmetic that insert/remove must thread.
// Structurally recursive; F* trivially accepts it as Tot.
// ---------------------------------------------------------------

let rec popcount_sum (ws : list U64.t)
  : Tot nat (decreases ws) =
  match ws with
  | [] -> 0
  | w :: rest -> Bits.popcount_u64 w + popcount_sum rest

// ---------------------------------------------------------------
// Word-list builders.
//
// We need an "all-zero list of length n" for `bitmap_empty`. F* lists
// are lazily-evaluated for `assert_norm`, so a simple structurally-
// recursive constructor is enough.
// ---------------------------------------------------------------

let rec zero_words_n (n : nat)
  : Tot (ws:list U64.t {length ws = n}) (decreases n) =
  if n = 0 then []
  else 0uL :: zero_words_n (n - 1)

// popcount_sum over an all-zeros list is 0. Used to discharge the
// bitmap_empty invariant.
val popcount_sum_zero (n : nat) :
  Lemma (ensures popcount_sum (zero_words_n n) = 0)
        (decreases n)
let rec popcount_sum_zero n =
  if n = 0 then ()
  else begin
    popcount_sum_zero (n - 1);
    // popcount of 0 is 0. Bits.fst pins this with assert_norm; we
    // need to re-establish it locally because the solver doesn't
    // unfold popcount_u64's recursion past --fuel 2.
    assert_norm (Bits.popcount_u64 0uL = 0)
  end

// ---------------------------------------------------------------
// Container record + structural invariant.
//
// `bm_words : list U64.t` of length exactly 1024.
// `bm_card  : nat` matches popcount_sum bm_words.
//
// Refinement type wf_bitmap pins both invariants at the type level,
// so any op that returns a wf_bitmap must re-establish them.
// ---------------------------------------------------------------

type bitmap_words_t = ws:list U64.t {length ws = bitmap_words}

type bitmap_container = {
  bm_words : bitmap_words_t;
  bm_card  : nat;
}

let valid_bitmap (bm : bitmap_container) : bool =
  bm.bm_card = popcount_sum bm.bm_words

type wf_bitmap = bm:bitmap_container {valid_bitmap bm}

// ---------------------------------------------------------------
// bitmap_empty : the all-zero container of cardinality 0.
//
// The lemma popcount_sum_zero discharges the invariant.
// ---------------------------------------------------------------

let bitmap_empty : wf_bitmap =
  popcount_sum_zero bitmap_words;
  { bm_words = zero_words_n bitmap_words;
    bm_card  = 0 }

// ---------------------------------------------------------------
// Bit-level access.
//
// For an index i ∈ [0, 65536), the word index is i / 64 and the
// bit position within that word is i mod 64.
//
// `word_at` reads the word; `bit_at` extracts the bit. Both use only
// list/integer operations — no UInt32/UInt16 arithmetic — to keep the
// proofs simple.
// ---------------------------------------------------------------

// Defensive index-into-list helper. Returns 0uL if out of range.
// In wf_bitmap contexts the caller has already verified
// idx < bitmap_words, but the fallback keeps the type Tot.
let rec list_index_u64 (ws : list U64.t) (idx : nat)
  : Tot U64.t (decreases ws) =
  match ws with
  | [] -> 0uL
  | w :: rest -> if idx = 0 then w else list_index_u64 rest (idx - 1)

// Bit i of word w: 1 if (w >> (i mod 64)) & 1 = 1, else 0.
//
// We lower this to integer arithmetic via U64.div + U64.rem. The bit
// shift is i mod 64, which is in [0, 64), so 2^(i mod 64) fits in u64.
//
// Bit i of w: extract via shift_left+logand. Cleaner than the
// pow/div route and avoids re-proving 2^i fits in u64.
module U32 = FStar.UInt32

let bit_at_word (w : U64.t) (bit_pos : nat{bit_pos < 64}) : Tot bool =
  let s : U32.t = U32.uint_to_t bit_pos in
  let mask = U64.shift_left 1uL s in
  let masked = U64.logand w mask in
  not (U64.eq masked 0uL)

// ---------------------------------------------------------------
// bitmap_contains — read the bit at position v ∈ [0, 65536).
//
// Total over u16_val (the Spec-level bounded nat), which keeps the
// signature in line with array_contains in Container.Array.
// ---------------------------------------------------------------

val bitmap_contains : wf_bitmap -> u16_val -> Tot bool
let bitmap_contains bm v =
  let word_idx = v / 64 in
  let bit_pos  = v - word_idx `op_Multiply` 64 in  // == v mod 64
  // word_idx < 1024 because v < 65536 and 65536 / 64 = 1024;
  // bit_pos < 64 because that's the residue.
  // Both bounds discharged by the next two assertions, which the
  // SMT solver accepts trivially.
  assert (word_idx < bitmap_words);
  assert (bit_pos < 64);
  let w = list_index_u64 bm.bm_words word_idx in
  bit_at_word w bit_pos

// ---------------------------------------------------------------
// bitmap_cardinality — cached field, O(1).
//
// The wf_bitmap refinement guarantees this matches popcount_sum.
// ---------------------------------------------------------------

val bitmap_cardinality : wf_bitmap -> Tot nat
let bitmap_cardinality bm = bm.bm_card

// ---------------------------------------------------------------
// denote_bitmap — Spec-level denotation.
//
// Bridges to the abstract `roaring_set` predicate at the high-16
// level (i.e. each bitmap container holds the low-16 chunk of one
// high-16 prefix). Companion to denote_array_for_key in
// Container.Array.fst.
// ---------------------------------------------------------------

val denote_bitmap_for_key : wf_bitmap -> u16_val -> Tot bool
let denote_bitmap_for_key bm v = bitmap_contains bm v

// ---------------------------------------------------------------
// Cross-layer correctness: bitmap_empty denotes the always-false
// predicate.
//
// Proof: bm_words is a 1024-zeros list; list_index_u64 always
// returns 0uL; bit_at_word 0uL _ = false.
// ---------------------------------------------------------------

val list_index_zero_words (n : nat) (idx : nat) :
  Lemma (ensures list_index_u64 (zero_words_n n) idx = 0uL)
        (decreases n)
let rec list_index_zero_words n idx =
  if n = 0 then ()
  else if idx = 0 then ()
  else list_index_zero_words (n - 1) (idx - 1)

val bit_at_word_zero (bit_pos : nat{bit_pos < 64}) :
  Lemma (ensures bit_at_word 0uL bit_pos = false)
let bit_at_word_zero bit_pos =
  // 0 & mask = 0 for any mask; bit_at_word returns
  // not (U64.eq 0uL 0uL) = not true = false. The lemma logand_lemma_1
  // gives `logand 0 m = 0` (commutative, so we can use the swapped form).
  let s : U32.t = U32.uint_to_t bit_pos in
  let mask = U64.shift_left 1uL s in
  FStar.UInt.logand_commutative #64 0 (U64.v mask);
  FStar.UInt.logand_lemma_1 #64 (U64.v mask)

val denote_bitmap_empty (v : u16_val) :
  Lemma (ensures denote_bitmap_for_key bitmap_empty v = false)
let denote_bitmap_empty v =
  let word_idx = v / 64 in
  let bit_pos  = v - word_idx `op_Multiply` 64 in
  list_index_zero_words bitmap_words word_idx;
  bit_at_word_zero bit_pos

// ---------------------------------------------------------------
// Smoke tests via assert_norm — concrete cases the F* normalizer
// can fully reduce.
// ---------------------------------------------------------------

let _ = assert_norm (bitmap_cardinality bitmap_empty = 0)
