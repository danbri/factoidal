module Test

// Phase A unit tests for the Roaring F* implementation.
//
// Two test layers in this file:
//
//  (a) `assert_norm` checks — concrete values evaluated by the F*
//      normalizer at type-check time. These are the closest analogue
//      to traditional unit tests: a pre-decided input and an expected
//      output. If the assertion fails, F* refuses to type-check this
//      module.
//
//  (b) Property lemmas — universally quantified properties whose
//      proofs are constructed by F* using the lemmas in Spec /
//      Container.Array. These are stronger than assert_norm but
//      slower to develop.
//
// Phase A scope is intentionally narrow: just the array container,
// because that's the only one implemented yet. Phase B/C/D will
// extend this file (or split it) to cover the bitmap and run
// containers and inter-container ops.

open FStar.List.Tot
open Spec
open Container.Array

// ---------------------------------------------------------------
// (a) assert_norm smoke tests for the array container.
// ---------------------------------------------------------------

// Empty container contains nothing.
let _ = assert_norm (not (array_contains array_empty 42))
let _ = assert_norm (array_cardinality array_empty = 0)

// Inserting a value makes it contained.
let _ =
  // F*'s normalizer needs to evaluate array_insert. The wrapper
  // has a precondition; assert_norm-friendly form computes via
  // the aux directly so the proof obligation is discharged
  // statically by sortedness of [].
  assert_norm (array_contains (array_insert_aux [] 42) 42)

let _ = assert_norm (length (array_insert_aux [] 42) = 1)

// Inserting a value already present does not grow the container.
let _ =
  assert_norm
    (length (array_insert_aux (array_insert_aux [] 42) 42) = 1)

// Inserting two distinct values: both are present.
let _ =
  assert_norm
    (let c = array_insert_aux (array_insert_aux [] 7) 42 in
     array_contains c 7 && array_contains c 42)

// Insertion places values in sorted order.
let _ =
  assert_norm
    (let c = array_insert_aux (array_insert_aux [] 42) 7 in
     // Smallest value first.
     match c with
     | 7 :: 42 :: [] -> true
     | _ -> false)

// Cardinality after two distinct inserts is 2.
let _ =
  assert_norm
    (let c = array_insert_aux (array_insert_aux [] 7) 42 in
     length c = 2)

// Removing the only element gives empty.
let _ =
  assert_norm
    (length (array_remove_aux (array_insert_aux [] 42) 42) = 0)

// Removing a not-present value is a no-op.
let _ =
  assert_norm
    (let c = array_insert_aux (array_insert_aux [] 7) 42 in
     length (array_remove_aux c 99) = length c)

// Insert/remove round-trip on a fresh empty container.
let _ =
  assert_norm
    (let c = array_remove_aux (array_insert_aux [] 42) 42 in
     not (array_contains c 42))

// ---------------------------------------------------------------
// Spec-layer smoke tests.
// ---------------------------------------------------------------

let _ = assert_norm (empty_set 0 = false)
let _ = assert_norm (empty_set 42 = false)

// singleton_set 42 contains 42 and nothing else (sample probes).
let _ = assert_norm (singleton_set 42 42 = true)
let _ = assert_norm (singleton_set 42 41 = false)
let _ = assert_norm (singleton_set 42 43 = false)

// insert_set then membership
let _ = assert_norm (insert_set empty_set 42 42 = true)
let _ = assert_norm (insert_set empty_set 42 99 = false)

// union/intersect on small concrete sets
let _ = assert_norm (
  let s1 = insert_set empty_set 1 in
  let s2 = insert_set empty_set 2 in
  let u = union_set s1 s2 in
  u 1 = true && u 2 = true && u 3 = false)

let _ = assert_norm (
  let s1 = insert_set (insert_set empty_set 1) 2 in
  let s2 = insert_set (insert_set empty_set 2) 3 in
  let i = intersect_set s1 s2 in
  i 1 = false && i 2 = true && i 3 = false)

// ---------------------------------------------------------------
// High/low 16-bit splitting tests.
// ---------------------------------------------------------------

// Round-trip on a few specific values.
let _ = assert_norm (combine16 (high16 0) (low16 0) = 0)
let _ = assert_norm (combine16 (high16 65535) (low16 65535) = 65535)
let _ = assert_norm (combine16 (high16 65536) (low16 65536) = 65536)
let _ = assert_norm (combine16 (high16 1234567) (low16 1234567) = 1234567)

// high16 / low16 of small values.
let _ = assert_norm (high16 5 = 0)
let _ = assert_norm (low16 5 = 5)
let _ = assert_norm (high16 65536 = 1)
let _ = assert_norm (low16 65536 = 0)
let _ = assert_norm (high16 65537 = 1)
let _ = assert_norm (low16 65537 = 1)

// ---------------------------------------------------------------
// (b) Property lemmas. These are universally quantified properties
// that F* discharges via proof obligations. Each one is small;
// together they form an invariant suite that should hold for any
// further changes to Spec / Container.Array.
// ---------------------------------------------------------------

// After inserting x, x is in the result.
val prop_insert_contains
  (c : array_container) (x : u16_val) :
  Lemma (requires length c < array_max_cardinality \/ array_contains c x)
        (ensures array_contains (array_insert c x) x)
let prop_insert_contains c x =
  // Postcondition of array_insert directly states this; F* should
  // discharge the lemma by unfolding the postcondition.
  ()

// After removing x, x is not in the result.
val prop_remove_does_not_contain
  (c : array_container) (x : u16_val) :
  Lemma (not (array_contains (array_remove c x) x))
let prop_remove_does_not_contain c x = ()

// Inserting a value that's already present doesn't change cardinality.
val prop_insert_idempotent_cardinality
  (c : array_container) (x : u16_val) :
  Lemma (requires array_contains c x)
        (ensures array_cardinality (array_insert c x) =
                 array_cardinality c)
let prop_insert_idempotent_cardinality c x =
  // array_contains c x ⇒ mem x c (via array_contains_iff_mem)
  // ⇒ length (array_insert_aux c x) = length c (idempotent_len).
  // The wrapper just calls array_insert_aux, so its length matches.
  array_contains_iff_mem c x;
  array_insert_aux_idempotent_len c x

// Cardinality grows by 1 when inserting a fresh value.
val prop_insert_fresh_grows_cardinality
  (c : array_container) (x : u16_val) :
  Lemma (requires length c < array_max_cardinality /\
                  not (array_contains c x))
        (ensures array_cardinality (array_insert c x) =
                 array_cardinality c + 1)
let prop_insert_fresh_grows_cardinality c x =
  array_contains_iff_mem c x;
  array_insert_aux_fresh_grows_len c x

// ---------------------------------------------------------------
// Cross-layer property: array_insert agrees with Spec.insert_set
// on the chunk's range.
//
// This is the central correctness contract for the array container:
// inserting into the executable representation has the same effect
// on membership as inserting into the abstract set.
// ---------------------------------------------------------------

val prop_insert_agrees_with_spec
  (c : array_container) (l : u16_val) (key : u16_val) :
  Lemma (requires length c < array_max_cardinality \/ array_contains c l)
        (ensures
          (let after = array_insert c l in
           let x : u32_val = combine16 key l in
           set_equiv (denote_array_for_key after key)
                     (insert_set (denote_array_for_key c key) x)))
let prop_insert_agrees_with_spec c l key =
  insert_correct_for_key c l key
