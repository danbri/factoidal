module Regex.Derivative

// Brzozowski derivatives + the correctness theorem.
// Phase 1 of issue #304. Design doc:
// docs/designissues/2026-07-15-verified-regex-engine.md
//
// This module proves the derivative engine correct against the denotational
// semantics `mem` from Regex.Syntax:
//
//   nullable_correct : nullable r        <==> mem r []              (in Regex.Syntax)
//   deriv_correct    : mem (deriv c r) w <==> mem r (c :: w)        (here, FULLY proven)
//   matches_correct  : matches r w       <==> mem r w               (here, FULLY proven)
//
// ALL THREE hold for the FULL AST including R_And and R_Not — there is no
// admit, no --lax, no assume val, and no fragment carve-out. The boolean-`mem`
// design (see Regex.Syntax banner) makes And/Not trivial (they recurse on
// strictly-smaller sub-regexes), so the only substantive proof work is
// concatenation and star. Both are discharged by relating the boolean
// split-enumeration functions `cat_try`/`star_try` on the word (c :: w)
// directly to a derivative on w — by induction on the split index, NOT by
// manipulating existential quantifiers (which SMT handles poorly).
//
// Derivative identities realized:
//   D_c(empty)  = empty
//   D_c(eps)    = empty
//   D_c(ranges) = eps        if c in ranges, else empty
//   D_c(r|s)    = D_c(r) | D_c(s)
//   D_c(r&s)    = D_c(r) & D_c(s)
//   D_c(~r)     = ~D_c(r)
//   D_c(rs)     = (D_c r) s  |  nullable(r) ? D_c(s) : empty
//   D_c(r*)     = (D_c r) r*

open FStar.Mul
open Regex.Syntax
module L = FStar.List.Tot

// ----------------------------------------------------------------------------
// take_n / drop_n behaviour on a cons cell — used throughout the proofs.
// All hold definitionally (one unfold of the simple structural recursions).
// ----------------------------------------------------------------------------

let take_zero (w:list nat) : Lemma (take_n 0 w == []) = ()
let drop_zero (w:list nat) : Lemma (drop_n 0 w == w) = ()

let take_cons (c:nat) (w:list nat) (k:nat)
  : Lemma (take_n (k + 1) (c :: w) == c :: take_n k w) = ()

let drop_cons (c:nat) (w:list nat) (k:nat)
  : Lemma (drop_n (k + 1) (c :: w) == drop_n k w) = ()

// ----------------------------------------------------------------------------
// The derivative
// ----------------------------------------------------------------------------
//
// The Cat and Star cases use PLAIN R_Cat (not smart_cat) so the correctness
// proof needs only the smart_alt/and/not language lemmas from Regex.Syntax.
// The fast path (Regex.Exec) re-normalizes with smart_cat/smart_star for DFA
// state finiteness; that is a performance layer and is not what this proof
// depends on.

let rec deriv (c:nat) (r:regex) : Tot regex (decreases r) =
  match r with
  | R_Empty -> R_Empty
  | R_Eps -> R_Empty
  | R_Ranges rs -> if in_ranges c rs then R_Eps else R_Empty
  | R_Alt a b -> smart_alt (deriv c a) (deriv c b)
  | R_And a b -> smart_and (deriv c a) (deriv c b)
  | R_Not a -> smart_not (deriv c a)
  | R_Cat a b ->
    let left = R_Cat (deriv c a) b in
    if nullable a then smart_alt left (deriv c b) else left
  | R_Star a -> R_Cat (deriv c a) (R_Star a)

// ----------------------------------------------------------------------------
// Concatenation shift lemma.
//
// Given the inductive hypothesis for `a` (the derivative of `a` on any word),
// the split-enumeration `cat_try a b (c::w) (k+1)` equals the j=0 term
// (a matches "", b matches c::w) OR the derivative split `cat_try (D_c a) b w k`.
// Proven by induction on the split index k.
// ----------------------------------------------------------------------------

let rec cat_shift (a b:regex) (c:nat) (w:list nat) (k:nat)
  : Lemma (requires (forall (w':list nat). mem (deriv c a) w' <==> mem a (c :: w')))
          (ensures (cat_try a b (c :: w) (k + 1) <==>
                    ((mem a [] && mem b (c :: w)) \/ cat_try (deriv c a) b w k)))
          (decreases k) =
  take_cons c w k;
  drop_cons c w k;
  if k = 0 then (take_zero (c :: w); drop_zero (c :: w); take_zero w; drop_zero w)
  else cat_shift a b c w (k - 1)

// ----------------------------------------------------------------------------
// Star shift lemma. Analogous: star_try a (c::w) (k+1) equals the derivative
// concatenation split cat_try (D_c a) (a*) w k.
// ----------------------------------------------------------------------------

let rec star_shift (a:regex) (c:nat) (w:list nat) (k:nat)
  : Lemma (requires (forall (w':list nat). mem (deriv c a) w' <==> mem a (c :: w')))
          (ensures (star_try a (c :: w) (k + 1) <==> cat_try (deriv c a) (R_Star a) w k))
          (decreases k) =
  take_cons c w k;
  drop_cons c w k;
  if k = 0 then (take_zero w; drop_zero w)
  else star_shift a c w (k - 1)

// ----------------------------------------------------------------------------
// Per-word derivative correctness for the two structural cases, given the IHs.
// ----------------------------------------------------------------------------

let deriv_cat_w (a b:regex) (c:nat) (w:list nat)
  : Lemma (requires (forall (w':list nat). mem (deriv c a) w' <==> mem a (c :: w')) /\
                    (forall (w':list nat). mem (deriv c b) w' <==> mem b (c :: w')))
          (ensures (mem (deriv c (R_Cat a b)) w <==> mem (R_Cat a b) (c :: w))) =
  nullable_correct a;
  // mem (R_Cat a b) (c::w) = cat_try a b (c::w) (|c::w|) = cat_try a b (c::w) (|w|+1)
  cat_shift a b c w (L.length w);
  // cat_try (deriv c a) b w (|w|) = mem (R_Cat (deriv c a) b) w   (by def of mem on R_Cat)
  if nullable a then
    smart_alt_ok (R_Cat (deriv c a) b) (deriv c b) w
  else ()

let deriv_star_w (a:regex) (c:nat) (w:list nat)
  : Lemma (requires (forall (w':list nat). mem (deriv c a) w' <==> mem a (c :: w')))
          (ensures (mem (deriv c (R_Star a)) w <==> mem (R_Star a) (c :: w))) =
  // mem (R_Star a) (c::w) = star_try a (c::w) (|w|+1)  (c::w is nonempty)
  star_shift a c w (L.length w)
  // star_try a (c::w) (|w|+1) <==> cat_try (deriv c a) (R_Star a) w (|w|)
  //                            = mem (R_Cat (deriv c a) (R_Star a)) w
  //                            = mem (deriv c (R_Star a)) w

// ----------------------------------------------------------------------------
// The derivative correctness theorem (FULL AST, no gaps).
// ----------------------------------------------------------------------------

let rec deriv_correct (c:nat) (r:regex)
  : Lemma (ensures (forall (w:list nat). mem (deriv c r) w <==> mem r (c :: w)))
          (decreases r) =
  match r with
  | R_Empty -> ()
  | R_Eps -> ()
  | R_Ranges _ -> ()
  | R_Alt a b ->
    deriv_correct c a; deriv_correct c b;
    introduce forall (w:list nat). mem (deriv c (R_Alt a b)) w <==> mem (R_Alt a b) (c :: w)
    with smart_alt_ok (deriv c a) (deriv c b) w
  | R_And a b ->
    deriv_correct c a; deriv_correct c b;
    introduce forall (w:list nat). mem (deriv c (R_And a b)) w <==> mem (R_And a b) (c :: w)
    with smart_and_ok (deriv c a) (deriv c b) w
  | R_Not a ->
    deriv_correct c a;
    introduce forall (w:list nat). mem (deriv c (R_Not a)) w <==> mem (R_Not a) (c :: w)
    with smart_not_ok (deriv c a) w
  | R_Cat a b ->
    deriv_correct c a; deriv_correct c b;
    introduce forall (w:list nat). mem (deriv c (R_Cat a b)) w <==> mem (R_Cat a b) (c :: w)
    with deriv_cat_w a b c w
  | R_Star a ->
    deriv_correct c a;
    introduce forall (w:list nat). mem (deriv c (R_Star a)) w <==> mem (R_Star a) (c :: w)
    with deriv_star_w a c w

// ----------------------------------------------------------------------------
// matches: fold the derivative over the word, then test nullability.
// ----------------------------------------------------------------------------

let rec deriv_word (r:regex) (w:list nat) : Tot regex (decreases w) =
  match w with
  | [] -> r
  | c :: rest -> deriv_word (deriv c r) rest

let matches (r:regex) (w:list nat) : bool = nullable (deriv_word r w)

let rec deriv_word_correct (r:regex) (w:list nat)
  : Lemma (ensures (mem (deriv_word r w) [] <==> mem r w)) (decreases w) =
  match w with
  | [] -> ()
  | c :: rest ->
    deriv_word_correct (deriv c r) rest;
    deriv_correct c r   // forall w'. mem (deriv c r) w' <==> mem r (c::w'); use at w' = rest

let matches_correct (r:regex) (w:list nat)
  : Lemma (matches r w <==> mem r w) =
  nullable_correct (deriv_word r w);
  deriv_word_correct r w
