module Container.Array

// Array container — sorted u16[] with cardinality <= 4096.
//
// Phase A scope: types, invariants, contains/insert/remove,
// cardinality, and a denotation function relating array containers
// to the abstract Spec layer. No promotion, no operations between
// different container types.
//
// Module ordering: F* requires every name used to be in scope at
// the use site, so this file is organised strictly bottom-up:
//
//   1. sorted_strict                      basic predicate
//   2. sorted_strict_head_lt_all          helper lemma
//   3. sorted_strict_head_not_in_rest     corollary
//   4. array_container, array_empty       data type
//   5. array_contains, array_cardinality  read ops
//   6. array_insert_aux + lemmas          insert path
//   7. array_remove_aux + lemmas          remove path
//   8. array_contains_iff_mem             bridge to List.mem
//   9. array_insert, array_remove         wrappers (use refinement type)
//  10. denote_array_for_key               bridge to Spec
//  11. insert_correct_for_key,            cross-layer correctness
//      remove_correct_for_key

open FStar.List.Tot
open Spec

// ---------------------------------------------------------------
// 1. The strict-sorted predicate.
// ---------------------------------------------------------------

let rec sorted_strict (xs : list u16_val) : Tot bool =
  match xs with
  | [] -> true
  | [_] -> true
  | x :: y :: rest -> x < y && sorted_strict (y :: rest)

// ---------------------------------------------------------------
// 2-3. Head/rest sortedness helpers.
//
// sorted_strict (h :: rest) ⇒ every element of rest > h.
// Direct corollary: h ∉ rest.
// ---------------------------------------------------------------

val sorted_strict_head_lt_all (h : u16_val) (rest : list u16_val) :
  Lemma (requires sorted_strict (h :: rest))
        (ensures forall (z : u16_val). mem z rest ==> z > h)
        (decreases rest)
let rec sorted_strict_head_lt_all h rest =
  match rest with
  | [] -> ()
  | r1 :: rest' ->
    sorted_strict_head_lt_all r1 rest'

val sorted_strict_head_not_in_rest (h : u16_val) (rest : list u16_val) :
  Lemma (requires sorted_strict (h :: rest))
        (ensures not (mem h rest))
let sorted_strict_head_not_in_rest h rest =
  sorted_strict_head_lt_all h rest

// ---------------------------------------------------------------
// 4. The array container.
// ---------------------------------------------------------------

type array_container = xs:list u16_val {
  sorted_strict xs /\ length xs <= array_max_cardinality
}

let array_empty : array_container = []

// ---------------------------------------------------------------
// 5. Read ops.
// ---------------------------------------------------------------

let rec array_contains (c : list u16_val) (x : u16_val) : Tot bool =
  match c with
  | [] -> false
  | y :: rest ->
    if x = y then true
    else if x < y then false
    else array_contains rest x

let array_cardinality (c : array_container) : nat =
  length c

// ---------------------------------------------------------------
// 6. Insert path: aux + sortedness, mem-equiv, idempotent-length.
// ---------------------------------------------------------------

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

// Membership semantics. Induction on c.
val array_insert_aux_mem (c : list u16_val) (x : u16_val) (y : u16_val) :
  Lemma (ensures mem y (array_insert_aux c x) <==> (y = x \/ mem y c))
        (decreases c)
let rec array_insert_aux_mem c x y =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then ()
    else if x < h then ()
    else array_insert_aux_mem rest x y

// Sortedness preservation. The recursive case needs the mem-equivalence
// lemma to pull the "every element of aux > h" fact out of "every
// element of aux is either x or in rest, and both are > h."
val array_insert_aux_sorted (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures sorted_strict (array_insert_aux c x))
        (decreases c)
let rec array_insert_aux_sorted c x =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then ()
    else if x < h then ()
    else begin
      array_insert_aux_sorted rest x;
      sorted_strict_head_lt_all h rest;
      // For every z in array_insert_aux rest x, mem z aux ⇒
      // (z = x \/ mem z rest), so z > h. Bring this into the
      // SMT context as a quantified fact:
      let mem_eq (y : u16_val) :
        Lemma (mem y (array_insert_aux rest x) <==> (y = x \/ mem y rest))
      = array_insert_aux_mem rest x y in
      FStar.Classical.forall_intro mem_eq
    end

// Idempotence: inserting an already-present element doesn't change
// length. Needs sortedness so the "x < h" branch becomes vacuous
// when mem x c.
val array_insert_aux_idempotent_len (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c /\ mem x c)
        (ensures length (array_insert_aux c x) = length c)
        (decreases c)
let rec array_insert_aux_idempotent_len c x =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then ()
    else if x < h then
      // Vacuous: mem x (h :: rest) and x ≠ h ⇒ mem x rest, but
      // sortedness ⇒ all of rest > h > x, contradiction.
      sorted_strict_head_lt_all h rest
    else
      array_insert_aux_idempotent_len rest x

// Companion: inserting a fresh element grows length by exactly 1.
val array_insert_aux_fresh_grows_len (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c /\ not (mem x c))
        (ensures length (array_insert_aux c x) = length c + 1)
        (decreases c)
let rec array_insert_aux_fresh_grows_len c x =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then ()  // vacuous: contradicts not (mem x c)
    else if x < h then ()  // result = x :: c
    else array_insert_aux_fresh_grows_len rest x

// ---------------------------------------------------------------
// 7. Remove path.
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
    else if x < y then c
    else y :: array_remove_aux rest x

val array_remove_aux_mem (c : list u16_val) (x : u16_val) (y : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures mem y (array_remove_aux c x) <==> (y <> x /\ mem y c))
        (decreases c)
let rec array_remove_aux_mem c x y =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then sorted_strict_head_not_in_rest h rest
    else if x < h then sorted_strict_head_lt_all h rest
    else array_remove_aux_mem rest x y

val array_remove_aux_sorted (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures sorted_strict (array_remove_aux c x))
        (decreases c)
let rec array_remove_aux_sorted c x =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then ()
    else if x < h then ()
    else begin
      array_remove_aux_sorted rest x;
      sorted_strict_head_lt_all h rest;
      // forall_intro requires a no-requires lemma; close the
      // sortedness precondition over the inner application:
      let mem_eq (y : u16_val) :
        Lemma (mem y (array_remove_aux rest x) <==> (y <> x /\ mem y rest))
      = array_remove_aux_mem rest x y
      in
      FStar.Classical.forall_intro mem_eq
    end

// ---------------------------------------------------------------
// 8. Bridge: array_contains ≡ List.Tot.mem under sortedness.
// ---------------------------------------------------------------

val array_contains_iff_mem (c : list u16_val) (x : u16_val) :
  Lemma (requires sorted_strict c)
        (ensures array_contains c x = mem x c)
        (decreases c)
let rec array_contains_iff_mem c x =
  match c with
  | [] -> ()
  | h :: rest ->
    if x = h then ()
    else if x < h then sorted_strict_head_lt_all h rest
    else array_contains_iff_mem rest x

// ---------------------------------------------------------------
// 9. Wrappers with the array_max_cardinality bound enforced.
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
// 10. Denotation — bridge to Spec.
// ---------------------------------------------------------------

let denote_array_for_key (c : array_container) (key : u16_val)
  : roaring_set
=
  fun x ->
    let h = high16 x in
    let l = low16 x in
    h = key && array_contains c l

// ---------------------------------------------------------------
// 11. Cross-layer correctness — denotation agrees with Spec ops.
//
// For any candidate y in the universe:
//   denote_array_for_key c key y = (high16 y = key && array_contains c (low16 y))
//
// case high16 y ≠ key:
//   denote_array_for_key after key y = false  (high16 guard)
//   insert_set (denote_array_for_key c key) (combine16 key l) y
//     = (y = combine16 key l) || denote_array_for_key c key y
//   The first disjunct is false because split_combine_high gives
//     high16 (combine16 key l) = key,
//   so y = combine16 key l would force high16 y = key, contradiction.
//   The second disjunct is false (high16 guard again).
//
// case high16 y = key:
//   denote_array_for_key after key y = array_contains after (low16 y)
//   By array_contains_iff_mem, this equals mem (low16 y) after.
//   By array_insert_aux_mem (lifted through the wrapper), this
//   equals (low16 y = l) || mem (low16 y) c
//        = (low16 y = l) || array_contains c (low16 y).
//   Spec side:
//     y = combine16 key l <==> low16 y = l (given high16 y = key,
//     by split_combine_low + combine_split).
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
  let after = array_insert c l in
  let x : u32_val = combine16 key l in
  // Round-trip facts on combine16/high16/low16:
  split_combine_high key l;
  split_combine_low key l;
  array_contains_iff_mem c l;
  array_insert_aux_sorted c l;
  // Quantify aux-level mem semantics over the candidate's low16:
  let aux_mem (y : u16_val) :
    Lemma (mem y (array_insert_aux c l) <==> (y = l \/ mem y c))
  = array_insert_aux_mem c l y in
  FStar.Classical.forall_intro aux_mem;
  // Bridge array_contains <-> mem on both `c` and `array_insert_aux c l`.
  let after_iff (y : u16_val) :
    Lemma (array_contains (array_insert_aux c l) y = mem y (array_insert_aux c l))
  = array_contains_iff_mem (array_insert_aux c l) y in
  FStar.Classical.forall_intro after_iff;
  let c_iff (y : u16_val) :
    Lemma (array_contains c y = mem y c)
  = array_contains_iff_mem c y in
  FStar.Classical.forall_intro c_iff;
  // Round-trip on candidates: every u32 y satisfies
  //   y = combine16 (high16 y) (low16 y)
  FStar.Classical.forall_intro combine_split

val remove_correct_for_key (c : array_container) (l : u16_val) (key : u16_val) :
  Lemma
    (ensures
      (let after = array_remove c l in
       let x : u32_val = combine16 key l in
       set_equiv (denote_array_for_key after key)
                 (remove_set (denote_array_for_key c key) x)))
let remove_correct_for_key c l key =
  let after = array_remove c l in
  let x : u32_val = combine16 key l in
  split_combine_high key l;
  split_combine_low key l;
  array_remove_aux_sorted c l;
  let aux_mem (y : u16_val) :
    Lemma (mem y (array_remove_aux c l) <==> (y <> l /\ mem y c))
  = array_remove_aux_mem c l y in
  FStar.Classical.forall_intro aux_mem;
  let after_iff (y : u16_val) :
    Lemma (array_contains (array_remove_aux c l) y = mem y (array_remove_aux c l))
  = array_contains_iff_mem (array_remove_aux c l) y in
  FStar.Classical.forall_intro after_iff;
  let c_iff (y : u16_val) :
    Lemma (array_contains c y = mem y c)
  = array_contains_iff_mem c y in
  FStar.Classical.forall_intro c_iff;
  FStar.Classical.forall_intro combine_split
