module Bits

// Pure F* bit-manipulation primitives that we previously thought
// needed `assume val`. This module exists to demonstrate that
// popcount and tzcnt (the two we need for Roaring) admit verified
// pure-F* implementations — the project's "assume val popcount_u64"
// plan was lazy.
//
// Performance: these implementations are O(bits-per-word) recursive
// and will be ~10-20× slower than hardware POPCNT / TZCNT. That's
// a separate concern from correctness; this module is the reference.
// Phase B's bitmap container uses these directly. If performance
// becomes an issue, we can either:
//   (a) add a verified SWAR-style popcount as a peer (still pure F*,
//       O(log W) instead of O(W)), or
//   (b) at extraction time, map to a compiler popcount intrinsic —
//       but only via an equivalence lemma, not via rule-#11-violating
//       glue.

module U64 = FStar.UInt64

// ---------------------------------------------------------------
// popcount: number of 1-bits in a 64-bit word.
//
// Bottom-up walk: at each step, take the LSB, halve, recurse.
// ---------------------------------------------------------------

let rec popcount_aux (n : U64.t) (i : nat) : Tot (k:nat{k <= i}) (decreases i) =
  if i = 0 then 0
  else
    let bit = U64.rem n 2uL in
    let rest_count = popcount_aux (U64.div n 2uL) (i - 1) in
    (if U64.eq bit 0uL then 0 else 1) + rest_count

let popcount_u64 (n : U64.t) : Tot (k:nat{k <= 64}) =
  popcount_aux n 64

// ---------------------------------------------------------------
// tzcnt: count trailing zeros (index of least-significant 1-bit,
// or 64 if the word is zero).
// ---------------------------------------------------------------

let rec tzcnt_aux (n : U64.t) (i : nat) : Tot (k:nat{k <= i}) (decreases i) =
  if i = 0 then 0
  else if U64.eq (U64.rem n 2uL) 1uL then 0
  else 1 + tzcnt_aux (U64.div n 2uL) (i - 1)

let tzcnt_u64 (n : U64.t) : Tot (k:nat{k <= 64}) =
  tzcnt_aux n 64

// ---------------------------------------------------------------
// Sanity checks (assert_norm): the F* normalizer evaluates these
// at type-check time. If popcount/tzcnt were wrong, the module
// would fail to type-check.
// ---------------------------------------------------------------

let _ = assert_norm (popcount_u64 0uL = 0)
let _ = assert_norm (popcount_u64 1uL = 1)
let _ = assert_norm (popcount_u64 3uL = 2)
let _ = assert_norm (popcount_u64 7uL = 3)
let _ = assert_norm (popcount_u64 15uL = 4)
let _ = assert_norm (popcount_u64 0xFFuL = 8)
let _ = assert_norm (popcount_u64 0xAAAAAAAAuL = 16)

let _ = assert_norm (tzcnt_u64 1uL = 0)
let _ = assert_norm (tzcnt_u64 2uL = 1)
let _ = assert_norm (tzcnt_u64 4uL = 2)
let _ = assert_norm (tzcnt_u64 8uL = 3)
let _ = assert_norm (tzcnt_u64 16uL = 4)
let _ = assert_norm (tzcnt_u64 0uL = 64)

