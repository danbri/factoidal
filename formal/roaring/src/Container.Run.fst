module Container.Run

// Run container — sorted, non-adjacent (start, length-1) pairs.
//
// A run container stores values from a single high-16 chunk
// (low-16 universe [0, 65 536)) as packed runs of consecutive
// integers. The pair (s, l) represents the l+1 values
// s, s+1, ..., s+l. We store length-minus-one per the paper §4
// so the maximum run [0, pow16-1] fits into a u16 length field.
//
// Phase C scope:
//   - run_pair type with bound invariant.
//   - sorted-and-non-adjacent predicate.
//   - run_container refinement type + run_empty.
//   - run_contains : run_container -> u16_val -> bool
//   - run_cardinality : run_container -> nat (computed each call)
//   - denote_run_for_key : Spec-bridge predicate
//   - denote_run_empty : empty denotes false everywhere
//   - spans_whole_chunk : canonical "all of [0, pow16) is in one run"
//
// Out of scope (Phase C.5 and later):
//   - run_insert / run_remove
//   - cross-layer insert/remove correctness lemmas (paper §4 ops)
//   - run-array / run-bitmap promotion (Phase D)
//
// Constraints (CLAUDE.md iron rules):
//   - No assume val
//   - No --admit_smt_queries
//   - No --lax
//   - All recursion structural

open FStar.List.Tot
open FStar.Mul
open Spec

// ---------------------------------------------------------------
// run_pair — (start, length-1).
//
// length-1 ("lmo" = length-minus-one) means "number of additional
// values after start". A pair with lmo = 0 holds the single value
// start. The full extent of (s, l) is [s, s+l].
//
// We refine the underlying tuple so that s + l < pow16, i.e. the
// run fits within the low-16 universe.
// ---------------------------------------------------------------

let run_pair_valid (s : u16_val) (lmo : nat) : bool =
  s + lmo < pow16

type run_pair = sl:(u16_val & nat) {
  run_pair_valid (fst sl) (snd sl)
}

let pair_start (p : run_pair) : u16_val = fst p
let pair_lmo   (p : run_pair) : nat = snd p

let pair_end (p : run_pair) : u16_val =
  // run_pair_valid pins fst + snd < pow16, so the sum is u16_val.
  pair_start p + pair_lmo p

// ---------------------------------------------------------------
// sorted_nonadjacent — runs are sorted by start AND not touching.
//
// For two consecutive runs (s1, l1), (s2, l2) we require
//   s2 > s1 + l1 + 1
// i.e. there is at least one missing value strictly between them.
// (s2 = s1 + l1 + 1 would be touching adjacency: those runs should
// have been merged. Canonical-form invariant.)
// ---------------------------------------------------------------

let rec sorted_nonadjacent (rs : list run_pair) : Tot bool =
  match rs with
  | [] -> true
  | [_] -> true
  | r1 :: r2 :: rest ->
    pair_start r2 > pair_end r1 + 1
    && sorted_nonadjacent (r2 :: rest)

type run_container = rs:list run_pair {sorted_nonadjacent rs}

let run_empty : run_container = []

// ---------------------------------------------------------------
// run_contains — linear scan.
//
// Each run is an inclusive range [pair_start, pair_end]. A future
// optimisation could exploit sortedness for early termination
// (if v < pair_start r, then v is not in any later run). Phase C
// stays linear; the lemma surface doesn't depend on that.
// ---------------------------------------------------------------

let rec run_contains (rc : list run_pair) (v : u16_val) : Tot bool =
  match rc with
  | [] -> false
  | r :: rest ->
    if pair_start r <= v && v <= pair_end r then true
    else run_contains rest v

// ---------------------------------------------------------------
// run_cardinality — sum of (lmo + 1) over runs.
//
// Per paper §4: run containers don't cache cardinality; they
// compute it on the fly. Canonical run containers cap num_runs
// at 2047 (paper §4 thresholds), so the scan is cheap.
// ---------------------------------------------------------------

let rec run_cardinality (rc : list run_pair) : Tot nat =
  match rc with
  | [] -> 0
  | r :: rest ->
    (pair_lmo r + 1) + run_cardinality rest

// ---------------------------------------------------------------
// denote_run_for_key — Spec-bridge predicate.
//
// Companion to denote_array_for_key (Container.Array) and
// denote_bitmap_for_key (Container.Bitmap). Low-16 only; the
// high-16 chunk lookup is the directory's job.
// ---------------------------------------------------------------

let denote_run_for_key (rc : run_container) (v : u16_val) : Tot bool =
  run_contains rc v

// ---------------------------------------------------------------
// denote_run_empty — empty run container denotes false everywhere.
// Trivial: run_contains [] _ = false by definition.
// ---------------------------------------------------------------

val denote_run_empty (v : u16_val) :
  Lemma (ensures denote_run_for_key run_empty v = false)
let denote_run_empty _ = ()

// ---------------------------------------------------------------
// spans_whole_chunk — canonical "all of [0, pow16) lives in one
// run". Detects the saturation case where bitmap → run conversion
// produces a single run pair (0, pow16-1).
//
// Used by the future bitmap_to_run / run_to_bitmap promotion
// proofs (Phase D). Defined here so Phase D doesn't need to
// expose pair internals.
// ---------------------------------------------------------------

let spans_whole_chunk (rc : run_container) : bool =
  match rc with
  | [r] -> pair_start r = 0 && pair_lmo r = pow16 - 1
  | _ -> false

// ---------------------------------------------------------------
// Smoke tests via assert_norm. Concrete cases the F* normalizer
// can fully reduce.
// ---------------------------------------------------------------

let _ = assert_norm (run_cardinality run_empty = 0)
let _ = assert_norm (run_contains run_empty 0 = false)
let _ = assert_norm (run_contains run_empty 65535 = false)

// Singleton run [(10, 4)] holds the values {10, 11, 12, 13, 14}.
let single_run : run_container = [(10, 4)]
let _ = assert_norm (run_cardinality single_run = 5)
let _ = assert_norm (run_contains single_run 10)
let _ = assert_norm (run_contains single_run 12)
let _ = assert_norm (run_contains single_run 14)
let _ = assert_norm (not (run_contains single_run 9))
let _ = assert_norm (not (run_contains single_run 15))

// Two non-adjacent runs: [(0, 0), (2, 0)] holds {0, 2}.
// (Gap of one value, namely 1, between them.)
let two_runs : run_container = [(0, 0); (2, 0)]
let _ = assert_norm (run_cardinality two_runs = 2)
let _ = assert_norm (run_contains two_runs 0)
let _ = assert_norm (not (run_contains two_runs 1))
let _ = assert_norm (run_contains two_runs 2)

// Saturation: a single run covering the entire chunk.
let full_chunk : run_container = [(0, 65535)]
let _ = assert_norm (run_cardinality full_chunk = 65536)
let _ = assert_norm (spans_whole_chunk full_chunk)
let _ = assert_norm (not (spans_whole_chunk run_empty))
let _ = assert_norm (not (spans_whole_chunk single_run))
let _ = assert_norm (not (spans_whole_chunk two_runs))
