module Container.Array

// Array container — sorted u16[] with cardinality <= 4096.
//
// Used for sparse chunks. Membership is binary search; insert/remove
// keep sortedness. Promotion to bitmap happens at cardinality > 4096
// (handled in Container.fst when that exists; this module is the
// array case in isolation).
//
// Phase A scope (this file): types, invariants, contains/insert/
// remove, cardinality, and a denotation function relating array
// containers to the abstract Spec layer. No promotion, no
// operations between different container types.
//
// Module ordering: F* requires every name used to be in scope at the
// use site. We put the data structure (sorted_strict, array_contains,
// the *_aux ops) first, then the helper lemma, then the wrappers
// that need it, then the cross-layer correctness lemmas.

open FStar.List.Tot
open Spec

// ---------------------------------------------------------------
// The strict-sorted predicate on a list of u16 values.
//
// Strict means strictly increasing — duplicates not allowed,
// matching the array container's "set, not multiset" semantics.
// ---------------------------------------------------------------

let rec sorted_strict (xs : list u16_val) : Tot bool =
  match xs with
  | [] -> true
  | [_] -> true
  | x :: y :: rest -> x < y && sorted_strict (y :: rest)

// ---------------------------------------------------------------
// The array container.
//
// Refinement-typed: strict-sorted list with cardinality bounded
// at array_max_cardinality. The two invariants together pin
// canonical form.
// ---------------------------------------------------------------

type array_container = xs:list u16_val {
  sorted_strict xs /\ length xs <= array_max_cardinality
}

let array_empty : array_container = []

// ---------------------------------------------------------------
// Contains. Linear scan (uses sortedness for early termination).
// In the executable module we'll switch to binary search and prove
// equivalence; for Phase A correctness-over-speed.
// ---------------------------------------------------------------

let rec array_contains (c : list u16_val) (x : u16_val) : Tot bool =
  match c with
  | [] -> false
  | y :: rest ->
    if x = y then true
    else if x < y then false  // strict-sorted ⇒ x not in rest
    else array_contains rest x

let array_cardinality (c : array_container) : nat =
  length c

// ---------------------------------------------------------------
// Insert helper — operates on raw lists (sorted_strict invariant
// only; cardinality bound handled by the wrapper). Returns the
// list with x inserted in the correct position, or unchanged if
// x was already present.
//
// The Pure spec captures the three things we care about:
//   1. result is still strict-sorted;
//   2. length grows by 0 or 1;
//   3. membership: y is in the result iff y = x or y was in the input.
// ---------------------------------------------------------------

// Plain recursive insert. We weaken the postcondition to just
// "length grows by 0 or 1" and prove sortedness + mem-equivalence
// as separate admit-able lemmas (PROOF DEBT in Phase A). This lets
// F* type-check the body without inline sortedness discharge in
// the recursive case.
let rec array_insert_aux (c : list u16_val) (x : u16_val) :
  Tot (result:list u16_val {
    length result = length c \/ length result = length c + 1
  }) (decreases c)
=
  match c with
  | [] -> [x]
  | y :: rest ->
    if x = y then c
    else if x < y then x :: c
    else y :: array_insert_aux rest x

// Sortedness preservation. PROOF DEBT — induction on c.
val array_insert_aux_sorted (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures sorted_strict (array_insert_aux c x))
let array_insert_aux_sorted c x = admit()

// Membership semantics. PROOF DEBT — induction on c.
val array_insert_aux_mem (c : list u16_val) (x : u16_val) (y : u16_val) :
  Lemma (mem y (array_insert_aux c x) <==> (y = x \/ mem y c))
let array_insert_aux_mem c x y = admit()

// Idempotence: inserting an already-present element doesn't change
// length. Used by the wrapper to maintain the 4096 cardinality bound
// when x is already in c. PROOF DEBT — induction on c.
val array_insert_aux_idempotent_len (c : list u16_val) (x : u16_val) :
  Lemma (requires mem x c)
        (ensures length (array_insert_aux c x) = length c)
let array_insert_aux_idempotent_len c x = admit()

// ---------------------------------------------------------------
// Remove helper. Symmetric to insert.
// ---------------------------------------------------------------

let rec array_remove_aux (c : list u16_val) (x : u16_val) :
  Tot (result:list u16_val {
    length result = length c \/ length result + 1 = length c
  }) (decreases c)
=
  match c with
  | [] -> []
  | y :: rest ->
    if x = y then rest
    else if x < y then c   // x not present, by sortedness
    else y :: array_remove_aux rest x

val array_remove_aux_sorted (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures sorted_strict (array_remove_aux c x))
let array_remove_aux_sorted c x = admit()

val array_remove_aux_mem (c : list u16_val) (x : u16_val) (y : u16_val) :
  Lemma (mem y (array_remove_aux c x) <==> (y <> x /\ mem y c))
let array_remove_aux_mem c x y = admit()

// ---------------------------------------------------------------
// Membership equivalence between the optimised `array_contains`
// and `List.Tot.mem`. The proof is induction on c using
// sortedness — strict-sorted (y :: rest) ⇒ all elements of rest > y,
// so x < y ⇒ x not in rest.
//
// PROOF DEBT: phase A — body is admit; mechanical induction.
// ---------------------------------------------------------------

val array_contains_iff_mem (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures array_contains c x = mem x c)
let array_contains_iff_mem c x =
  admit()

// ---------------------------------------------------------------
// Wrappers: insert / remove with the array_max_cardinality bound
// enforced.
// ---------------------------------------------------------------

let array_insert (c : array_container) (x : u16_val)
  : Pure array_container
         (requires length c < array_max_cardinality \/ array_contains c x)
         (ensures fun result -> array_contains result x)
=
  array_contains_iff_mem c x;
  array_insert_aux_sorted c x;
  array_insert_aux_mem c x x;
  // If x was already a member, the length is unchanged; this is
  // what licenses the result type's length <= 4096 even when c is
  // already at the cap.
  (if array_contains c x then array_insert_aux_idempotent_len c x);
  let result = array_insert_aux c x in
  array_contains_iff_mem result x;
  result

let array_remove (c : array_container) (x : u16_val)
  : Pure array_container
         (requires True)
         (ensures fun result -> not (array_contains result x))
=
  array_contains_iff_mem c x;
  array_remove_aux_sorted c x;
  array_remove_aux_mem c x x;
  let result = array_remove_aux c x in
  array_contains_iff_mem result x;
  result

// ---------------------------------------------------------------
// Denotation — bridge to Spec.
//
// An array container holds *low-16* values for one chunk of the
// Roaring data structure. Its denotation is parameterised by the
// chunk's high-16 key: combining gives the u32 values that this
// container contributes to the abstract set.
// ---------------------------------------------------------------

let denote_array_for_key (c : array_container) (key : u16_val)
  : roaring_set
=
  fun x ->
    let h = high16 x in
    let l = low16 x in
    h = key && array_contains c l

// ---------------------------------------------------------------
// Correctness lemmas (Phase A).
//
// These tie the executable operations back to the Spec layer's
// `insert_set` / `remove_set`. Once we have the bitmap and run
// containers we'll have one such lemma per (container × op) pair.
// ---------------------------------------------------------------

val insert_correct_for_key (c : array_container) (l : u16_val) (key : u16_val) :
  Lemma
    (requires length c < array_max_cardinality \/ array_contains c l)
    (ensures
      (let after = array_insert c l in
       let x : u32_val = combine16 key l in
       set_equiv (denote_array_for_key after key)
                 (insert_set (denote_array_for_key c key) x)))
let insert_correct_for_key c l key =
  // PROOF DEBT: Phase A — full proof outline:
  //   - For any candidate y in the universe, denote_array_for_key
  //     evaluates to (high16 y = key && array_contains _ (low16 y)).
  //   - When high16 y = key, set_equiv reduces to comparing
  //     `array_contains after (low16 y)` with
  //     `(low16 y = l) || array_contains c (low16 y)` —
  //     which is exactly the postcondition of array_insert
  //     transported through array_contains_iff_mem.
  //   - When high16 y != key, both sides are false (the spec side
  //     because only x = combine16 key l is "newly inserted" and
  //     y != x in that case; the impl side by the high16 guard).
  //   - split_combine_high / split_combine_low close the loop:
  //     for the candidate x = combine16 key l, high16 x = key and
  //     low16 x = l, so equality matches.
  // For Phase A we admit. Mechanical, no exotic reasoning.
  admit()

val remove_correct_for_key (c : array_container) (l : u16_val) (key : u16_val) :
  Lemma
    (ensures
      (let after = array_remove c l in
       let x : u32_val = combine16 key l in
       set_equiv (denote_array_for_key after key)
                 (remove_set (denote_array_for_key c key) x)))
let remove_correct_for_key c l key =
  // PROOF DEBT: same shape as insert_correct_for_key, dual case.
  admit()
