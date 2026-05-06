module Spec

// Roaring bitmap — abstract specification layer.
//
// A Roaring bitmap denotes a finite set of 32-bit unsigned integers.
// This module gives the *meaning* of every operation: every executable
// data structure (array container, bitmap container, run container,
// top-level Roaring) will have a `denote` function into the types
// declared here, and a correctness lemma per operation.
//
// We model "set of u32" as a boolean-valued predicate
//   roaring_set : nat -> bool
// with the side condition that the predicate holds only for naturals
// less than 2^32. This avoids pulling FStar.Set or any other runtime
// container into the spec; the spec is purely propositional.
//
// 16-bit and 32-bit bounds are encoded as refinement-typed naturals
// rather than UInt16/UInt32, to keep the spec independent of the
// concrete machine-integer representation. Executable modules pick
// their representation; the bound here is the contract.

open FStar.Mul
open FStar.List.Tot

// ---------------------------------------------------------------
// Bounds.
// ---------------------------------------------------------------

// 2^16 = 65 536. Used both for the "low 16 bits" universe of a
// container and for the bitmap container's bit-count.
let pow16 : nat = 65536

// 2^32. Universe of values a Roaring bitmap can hold.
let pow32 : nat = 4294967296

// Refinement types for bounded naturals. Using nat-with-refinement
// (rather than FStar.UInt16.t / UInt32.t) keeps the spec-level
// reasoning in plain integer arithmetic — z3 handles it natively.
type u16_val = x:nat{x < pow16}
type u32_val = x:nat{x < pow32}

// ---------------------------------------------------------------
// The abstract Roaring set.
// ---------------------------------------------------------------

// A roaring_set is morally a `Set u32_val`. We represent it as the
// predicate "is x in the set?" Total functions; no implicit state.
type roaring_set = u32_val -> bool

let empty_set : roaring_set = fun _ -> false

let singleton_set (x : u32_val) : roaring_set =
  fun y -> y = x

let insert_set (s : roaring_set) (x : u32_val) : roaring_set =
  fun y -> y = x || s y

let remove_set (s : roaring_set) (x : u32_val) : roaring_set =
  fun y -> y <> x && s y

// Set algebra. These are the *spec* of union/intersect/etc — every
// executable op will have a lemma showing it agrees with these.
let union_set (a b : roaring_set) : roaring_set =
  fun x -> a x || b x

let intersect_set (a b : roaring_set) : roaring_set =
  fun x -> a x && b x

let xor_set (a b : roaring_set) : roaring_set =
  fun x -> (a x) <> (b x)

let andnot_set (a b : roaring_set) : roaring_set =
  fun x -> a x && not (b x)

// Set equivalence — extensional equality of the predicates.
// We deliberately don't use F*'s `==` here; we want a quantified
// equality that the lemmas can manipulate directly.
let set_equiv (a b : roaring_set) : prop =
  forall (x : u32_val). a x = b x

// ---------------------------------------------------------------
// High/low 16-bit splitting.
// ---------------------------------------------------------------
//
// The two-level structure of Roaring keys containers by the high
// 16 bits of each integer; the low 16 bits are stored in the
// container. These helpers give the spec-side semantics; executable
// modules will compute these with bit shifts rather than divmod.

let high16 (x : u32_val) : u16_val =
  x / pow16

let low16 (x : u32_val) : u16_val =
  x % pow16

// Recombination — given high and low 16, produce the original u32.
let combine16 (h : u16_val) (l : u16_val) : u32_val =
  let result = h * pow16 + l in
  // The bound result < pow32 is what we need to prove. Because
  // h < pow16 and l < pow16, we have h * pow16 + l < pow16*pow16
  // = pow32. Multiplication of nats stays within nats; F* needs
  // a hint to discharge the multiplicative bound.
  Math.Lemmas.lemma_mult_lt_right pow16 h pow16;
  result

// Round-trip: split-then-combine is the identity.
val combine_split (x : u32_val) :
  Lemma (combine16 (high16 x) (low16 x) = x)
let combine_split x =
  Math.Lemmas.lemma_div_mod x pow16

// And the other way: combining valid halves and then splitting
// recovers them.
val split_combine_high (h : u16_val) (l : u16_val) :
  Lemma (high16 (combine16 h l) = h)
let split_combine_high h l =
  // (h * pow16 + l) / pow16 = h, since 0 <= l < pow16.
  Math.Lemmas.lemma_div_plus l h pow16

val split_combine_low (h : u16_val) (l : u16_val) :
  Lemma (low16 (combine16 h l) = l)
let split_combine_low h l =
  // (h * pow16 + l) % pow16 = l, since 0 <= l < pow16.
  Math.Lemmas.lemma_mod_plus l h pow16

// ---------------------------------------------------------------
// Cardinality of a finite set, defined relative to a bounded
// witness. We use this for spec-side reasoning about cardinality
// without needing to commit to a particular finite enumeration.
// ---------------------------------------------------------------

// "x is the largest element less than n that's in s, if any" —
// an existence-only spec, useful for stating cardinality lemmas.
// We don't actually compute it spec-side; we just need to talk
// about it.
let has_member_below (s : roaring_set) (n : nat) : prop =
  exists (x : u32_val). x < n /\ s x

// Cardinality is left abstract at the spec level; executable
// modules introduce their own concrete count and prove it agrees
// with the abstract `count_below`.
//
// `count_below s n` = number of x < n with s x. Computed
// recursively for spec purposes. Slow; this is for proofs, not
// runtime.
let rec count_below (s : roaring_set) (n : nat) : Tot nat (decreases n) =
  if n = 0 then 0
  else
    let n' : nat = n - 1 in
    let rest = count_below s n' in
    if n' < pow32 && s n' then rest + 1 else rest

// Total cardinality.
let cardinality (s : roaring_set) : nat =
  count_below s pow32

// ---------------------------------------------------------------
// Container thresholds (paper §4).
// ---------------------------------------------------------------
//
// The cutoff between array and bitmap representation is 4096. The
// run-container thresholds are layered on top. These are constants
// of the spec; executable modules consult them.

let array_max_cardinality : nat = 4096

let bitmap_min_cardinality : nat = 4097  // strict: card > 4096

// Run container thresholds, paper §4:
//  - if card > 4096: must have num_runs <= 2047.
//  - if card <= 4096: num_runs < card / 2.
let run_max_runs_when_dense : nat = 2047
