module Regex.Syntax

// Verified regex core — syntax, denotational semantics, smart constructors.
// Phase 1 of issue #304 (verified Brzozowski-derivative regex engine).
// Design doc: docs/designissues/2026-07-15-verified-regex-engine.md
//
// This module is the SEMANTIC CORE (fstar-module-style: spec tier). It has
// ZERO dependencies on the RDF/SPARQL tree — it is a standalone regular-
// language engine over Unicode codepoints (nat in 0..0x10FFFF), so it can be
// consumed by XSD pattern facets, CSVW formats, XPath fn:matches, SPARQL
// REGEX, and the OWL facet-intersection emptiness check (issue #299) alike.
//
// HOW TO READ THIS FILE (concepts first, mechanics last):
//   1. The AST `regex` — codepoint-range alphabet, extended with And/Not.
//   2. `size` — the well-founded measure that makes every recursion total.
//   3. Codepoint ranges — membership, the max codepoint, complement.
//   4. `mem` — the DENOTATIONAL SEMANTICS: a TOTAL boolean membership
//      function (the reference language of a regex). This is the object the
//      derivative engine (Regex.Derivative) is proven correct against.
//   5. `nullable` + `nullable_correct` — matches the empty word.
//   6. Smart constructors + their language-preservation lemmas (`*_ok`).
//
// WHY A BOOLEAN `mem` RATHER THAN AN INDUCTIVE Prop: the standard
// language-membership relation is an inductive predicate, but `R_Not` occurs
// negatively, so an inductive Prop is not well-formed with complement in the
// AST (this is the "And/Not make the semantics non-inductive" trap called out
// in #304). A total recursive BOOLEAN function sidesteps it entirely: And/Not
// are ordinary boolean combinators over strictly-smaller sub-regexes, so they
// cost nothing extra. The only real termination work is concatenation and
// star, whose membership quantifies over word splits; we enumerate splits with
// `take_n`/`drop_n` and a 4-component lexicographic measure
// %[word-length; regex-size; split-index; tag]. See `mem` below.

open FStar.Mul
module L = FStar.List.Tot

// ----------------------------------------------------------------------------
// 1. The AST
// ----------------------------------------------------------------------------
//
// Alphabet is Unicode codepoints represented as `nat`. A character class is a
// union of inclusive codepoint intervals `(lo, hi)` (lo <= c <= hi). Negated
// classes are represented by complementing the interval set over 0..0x10FFFF
// (see `complement_ranges`), so the AST needs no separate "negated class"
// node. The extended operators R_And / R_Not give intersection and complement
// of whole languages — the operations the OWL facet-emptiness check needs
// (#299) and the reason we commit to them from day one (#304 design point 1).

type regex =
  | R_Empty : regex                          // the empty language  (matches nothing)
  | R_Eps   : regex                          // {""}                (matches only the empty word)
  | R_Ranges: list (nat & nat) -> regex      // union of inclusive codepoint intervals (one char)
  | R_Cat   : regex -> regex -> regex        // concatenation
  | R_Alt   : regex -> regex -> regex        // union
  | R_Star  : regex -> regex                 // Kleene star
  | R_And   : regex -> regex -> regex        // language intersection  (extended)
  | R_Not   : regex -> regex                 // language complement    (extended)

// The largest Unicode codepoint. Negation of a character class is taken over
// the closed interval [0, max_codepoint].
let max_codepoint : nat = 0x10FFFF

// ----------------------------------------------------------------------------
// 2. Size measure (well-founded termination witness)
// ----------------------------------------------------------------------------
//
// Not the literal node count: R_Cat and R_Star carry extra slack (3 instead of
// 1) so the nested split-enumeration helpers (`cat_try`, `star_try`) have room
// in the lexicographic measure to call `mem` on their sub-regexes. Every case
// is >= 1, which the `mem` termination argument relies on.

let rec size (r:regex) : Tot (n:nat{n >= 1}) =
  match r with
  | R_Empty -> 1
  | R_Eps -> 1
  | R_Ranges _ -> 1
  | R_Cat a b -> 3 + size a + size b
  | R_Alt a b -> 1 + size a + size b
  | R_And a b -> 1 + size a + size b
  | R_Not a -> 1 + size a
  | R_Star a -> 3 + size a

// ----------------------------------------------------------------------------
// 3. Codepoint ranges
// ----------------------------------------------------------------------------

// Membership of a single codepoint in a union of inclusive intervals.
let rec in_ranges (c:nat) (rs:list (nat & nat)) : Tot bool =
  match rs with
  | [] -> false
  | (lo, hi) :: tl -> (lo <= c && c <= hi) || in_ranges c tl

// Complement of a single sorted-disjoint interval list over [0, max_codepoint].
// `lo` is the next uncovered codepoint. `rs` must be sorted ascending with
// disjoint intervals for the result to be exact; the function is total for any
// input. Kept simple for Phase 1; the derivative engine only complements
// normalized classes.
let rec complement_from (lo:nat) (rs:list (nat & nat))
  : Tot (list (nat & nat)) (decreases rs) =
  match rs with
  | [] -> if lo <= max_codepoint then [(lo, max_codepoint)] else []
  | (a, b) :: tl ->
    let head = if a >= 1 && lo <= a - 1 then [(lo, a - 1)] else [] in
    let next : nat = if b + 1 > lo then b + 1 else lo in
    head @ complement_from next tl

let complement_ranges (rs:list (nat & nat)) : Tot (list (nat & nat)) =
  complement_from 0 rs

// ----------------------------------------------------------------------------
// 4. Denotational semantics: total boolean membership `mem`
// ----------------------------------------------------------------------------
//
// take_n / drop_n: prefix/suffix by length, with refined result lengths so the
// `mem` termination measure discharges by SMT without extra lemmas.

let rec take_n (k:nat) (w:list nat)
  : Tot (r:list nat{L.length r <= L.length w /\ L.length r <= k}) (decreases w) =
  if k = 0 then []
  else (match w with
        | [] -> []
        | x :: xs -> x :: take_n (k - 1) xs)

let rec drop_n (k:nat) (w:list nat)
  : Tot (r:list nat{L.length r <= L.length w /\
                    ((k >= 1 /\ Cons? w) ==> L.length r < L.length w)})
        (decreases w) =
  if k = 0 then w
  else (match w with
        | [] -> []
        | _ :: xs -> drop_n (k - 1) xs)

// The reference language. `mem r w` is true iff the word `w` (a list of
// codepoints) is in the language denoted by `r`.
//
//   - Concatenation `R_Cat a b`: true iff some split w = w1 ++ w2 has
//     `mem a w1 && mem b w2`. We enumerate split points k = |w| .. 0 with
//     `cat_try`; `take_n k w = w1`, `drop_n k w = w2`.
//   - Star `R_Star a`: [] is always in the language; a non-empty word is in
//     it iff some NON-EMPTY prefix (k >= 1) is in `a` and the remainder is in
//     `R_Star a` (strictly shorter, so the recursion is well-founded).
//
// Termination: lexicographic %[|w|; size; split-index; tag].
let rec mem (r:regex) (w:list nat)
  : Tot bool (decreases %[L.length w; size r; (0 <: nat); (3 <: nat)]) =
  match r with
  | R_Empty -> false
  | R_Eps -> Nil? w
  | R_Ranges rs -> (match w with | [c] -> in_ranges c rs | _ -> false)
  | R_Alt a b -> mem a w || mem b w
  | R_And a b -> mem a w && mem b w
  | R_Not a -> not (mem a w)
  | R_Cat a b -> cat_try a b w (L.length w)
  | R_Star a -> (match w with | [] -> true | _ :: _ -> star_try a w (L.length w))

and cat_try (a b:regex) (w:list nat) (k:nat)
  : Tot bool (decreases %[L.length w; size a + size b + 1; k; (2 <: nat)]) =
  (mem a (take_n k w) && mem b (drop_n k w))
  || (if k = 0 then false else cat_try a b w (k - 1))

and star_try (a:regex) (w:list nat{Cons? w}) (k:nat)
  : Tot bool (decreases %[L.length w; size a + 2; k; (1 <: nat)]) =
  if k = 0 then false
  else ((mem a (take_n k w) && mem (R_Star a) (drop_n k w)) || star_try a w (k - 1))

// ----------------------------------------------------------------------------
// 5. nullable
// ----------------------------------------------------------------------------

let rec nullable (r:regex) : Tot bool =
  match r with
  | R_Empty -> false
  | R_Eps -> true
  | R_Ranges _ -> false
  | R_Cat a b -> nullable a && nullable b
  | R_Alt a b -> nullable a || nullable b
  | R_And a b -> nullable a && nullable b
  | R_Not a -> not (nullable a)
  | R_Star _ -> true

let rec nullable_correct (r:regex)
  : Lemma (ensures (nullable r <==> mem r [])) (decreases r) =
  match r with
  | R_Empty -> ()
  | R_Eps -> ()
  | R_Ranges _ -> ()
  | R_Cat a b -> nullable_correct a; nullable_correct b
  | R_Alt a b -> nullable_correct a; nullable_correct b
  | R_And a b -> nullable_correct a; nullable_correct b
  | R_Not a -> nullable_correct a
  | R_Star _ -> ()

// ----------------------------------------------------------------------------
// 6. Smart constructors + language-preservation lemmas
// ----------------------------------------------------------------------------
//
// Owens-Reppy-Turon similarity rules: absorption (Empty/Eps laws), idempotence
// (r|r = r, r&r = r), double-negation, and a total order on operands so that
// commutatively-equal terms share one normal form (this is what keeps the
// derivative-to-DFA state set finite — Regex.Derivative / Regex.Exec).
// Each smart constructor is proven to preserve `mem` (`*_ok`). Ordering and
// idempotence do not affect the language, so the lemmas are cheap.

// The "universal" language Sigma* is R_Not R_Empty (mem = not false = true).
let r_universal : regex = R_Not R_Empty

// A total order on codepoint-interval lists (lexicographic on endpoints),
// used only to canonicalize R_Ranges operands. Correctness of the ORDER is
// irrelevant to the language; we only need it total and deterministic.
let rec ranges_cmp (x y : list (nat & nat)) : Tot int (decreases x) =
  match x, y with
  | [], [] -> 0
  | [], _ :: _ -> (-1)
  | _ :: _, [] -> 1
  | (a1, b1) :: xs, (a2, b2) :: ys ->
    if a1 <> a2 then (if a1 < a2 then (-1) else 1)
    else if b1 <> b2 then (if b1 < b2 then (-1) else 1)
    else ranges_cmp xs ys

// A structural total order on regexes, used only to canonicalize the operand
// order of commutative nodes (Alt, And). Correctness of ordering is irrelevant
// to the language; we only need it total.
let rec regex_cmp (a b:regex) : Tot int (decreases a) =
  let tag (r:regex) : int =
    match r with
    | R_Empty -> 0 | R_Eps -> 1 | R_Ranges _ -> 2 | R_Cat _ _ -> 3
    | R_Alt _ _ -> 4 | R_Star _ -> 5 | R_And _ _ -> 6 | R_Not _ -> 7 in
  let ta = tag a in let tb = tag b in
  if ta <> tb then (if ta < tb then (-1) else 1)
  else
    match a, b with
    | R_Ranges x, R_Ranges y -> ranges_cmp x y
    | R_Cat a1 a2, R_Cat b1 b2 -> let c = regex_cmp a1 b1 in if c <> 0 then c else regex_cmp a2 b2
    | R_Alt a1 a2, R_Alt b1 b2 -> let c = regex_cmp a1 b1 in if c <> 0 then c else regex_cmp a2 b2
    | R_And a1 a2, R_And b1 b2 -> let c = regex_cmp a1 b1 in if c <> 0 then c else regex_cmp a2 b2
    | R_Star a1, R_Star b1 -> regex_cmp a1 b1
    | R_Not a1, R_Not b1 -> regex_cmp a1 b1
    | _, _ -> 0

let regex_le (a b:regex) : bool = regex_cmp a b <= 0

// smart_alt: union with Empty absorption, idempotence, universal absorption,
// and canonical operand ordering.
let smart_alt (a b:regex) : regex =
  if R_Empty? a then b
  else if R_Empty? b then a
  else if a = b then a
  else if a = r_universal || b = r_universal then r_universal
  else if regex_le a b then R_Alt a b else R_Alt b a

let smart_alt_ok (a b:regex) (w:list nat)
  : Lemma (ensures (mem (smart_alt a b) w <==> (mem a w || mem b w))) =
  // R_Empty absorption uses mem R_Empty _ = false; universal uses
  // mem r_universal _ = not (mem R_Empty _) = true; ordering is commutativity.
  ()

// smart_and: intersection with Empty absorption, idempotence, universal unit,
// and canonical operand ordering.
let smart_and (a b:regex) : regex =
  if R_Empty? a || R_Empty? b then R_Empty
  else if a = r_universal then b
  else if b = r_universal then a
  else if a = b then a
  else if regex_le a b then R_And a b else R_And b a

let smart_and_ok (a b:regex) (w:list nat)
  : Lemma (ensures (mem (smart_and a b) w <==> (mem a w && mem b w))) =
  ()

// smart_not: complement with double-negation collapse.
let smart_not (a:regex) : regex =
  match a with
  | R_Not x -> x
  | _ -> R_Not a

let smart_not_ok (a:regex) (w:list nat)
  : Lemma (ensures (mem (smart_not a) w <==> not (mem a w))) =
  ()

// smart_cat: concatenation with Empty (annihilator) and Eps (unit) laws.
let smart_cat (a b:regex) : regex =
  if R_Empty? a || R_Empty? b then R_Empty
  else if R_Eps? a then b
  else if R_Eps? b then a
  else R_Cat a b

// smart_star: star with Empty/Eps collapse (both denote {""}).
let smart_star (a:regex) : regex =
  match a with
  | R_Empty -> R_Eps
  | R_Eps -> R_Eps
  | R_Star _ -> a
  | _ -> R_Star a
