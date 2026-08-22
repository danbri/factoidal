/-
L4Factoidal.Regex.Syntax — regular-expression AST over Unicode codepoints,
its denotational (language) semantics, nullability, and the smart
constructors the derivative engine normalises with.

Port of `formal/fstar/Regex.Syntax.fst` (issue #304, phase 1 + 2 of the
verified Brzozowski-derivative regex engine; design doc
`docs/designissues/2026-07-15-verified-regex-engine.md`).

The module is the SEMANTIC CORE of the engine. It has no dependency on
the RDF/SPARQL tree: it is a standalone regular-language engine over
codepoints (`Nat`, normally in `0 .. 0x10FFFF`; the XPath layer uses two
values ABOVE that range as begin/end sentinels, which is why the
alphabet is `Nat` and not `Char`). Consumers: XSD `xsd:pattern` facets,
CSVW `format`, XPath `fn:matches` / `fn:replace` (SPARQL `REGEX` /
`REPLACE`), and the OWL facet-emptiness check.

Reading order, as in the F* source:
  1. the AST `Re` — codepoint-interval alphabet, extended with
     intersection (`inter`, F* `R_And`) and complement (`compl`, F*
     `R_Not`);
  2. `size` — the F* termination measure; here only a fuel budget for
     the emptiness closure (Lean's structural recursion needs no measure);
  3. codepoint ranges — membership, the largest codepoint, complement;
  4. `mem` — the DENOTATIONAL SEMANTICS, a total Boolean membership
     function (the reference language the derivative is proven against);
  5. `nullable`;
  6. smart constructors (the `*_ok` language-preservation theorems are in
     `RegexTheorems.lean`).

Why a Boolean `mem` and not an inductive `Prop`: `compl` occurs
negatively, so an inductive language relation is not well-formed once
complement is in the AST. A total recursive Boolean function sidesteps
that; intersection and complement are then ordinary Boolean
combinators over strictly smaller sub-regexes, and the only real work
is concatenation and star, whose membership quantifies over word
splits.

Translation of the F* termination scheme. The F* `mem` / `cat_try` /
`star_try` are one mutual well-founded recursion on the lexicographic
measure `[word length; regex size; split index; tag]`. Lean gets the same
language with plain STRUCTURAL recursion: `mem` recurses on the regex,
the split enumerators `catTry` / `starTry` recurse on the split index
and take the sub-languages as FUNCTION arguments (so they are ordinary
first-order helpers, not part of a mutual block), and star iteration
`memStar` recurses on a fuel that is set to the word length
(`memStar_fuel` in `RegexTheorems.lean` shows any fuel `≥ |w|` gives the
same answer). The split order is the F* one: `k = |w| .. 0`.

Naming: F* `R_And` / `R_Not` are `Re.inter` / `Re.compl` here, because
inside `namespace Re` constructor names `and` / `not` would shadow the
Boolean functions `and` / `not` used in the very same definitions.
-/

namespace L4Factoidal.Regex

/-! ## 1. The AST

The alphabet is Unicode codepoints as `Nat`. A character class is a
union of INCLUSIVE codepoint intervals `(lo, hi)`. Negated classes are
represented by complementing the interval set over `0 .. maxCodepoint`
(`complementRanges`), so the AST needs no separate negated-class node.
-/

/-- Regular expression over codepoints (F* `Regex.Syntax.regex`). -/
inductive Re where
  /-- the empty language (matches nothing) — F* `R_Empty` -/
  | empty  : Re
  /-- `{""}`, matches only the empty word — F* `R_Eps` -/
  | eps    : Re
  /-- one codepoint drawn from a union of inclusive intervals — F* `R_Ranges` -/
  | ranges : List (Nat × Nat) → Re
  /-- concatenation — F* `R_Cat` -/
  | cat    : Re → Re → Re
  /-- union — F* `R_Alt` -/
  | alt    : Re → Re → Re
  /-- Kleene star — F* `R_Star` -/
  | star   : Re → Re
  /-- language intersection (extended operator) — F* `R_And` -/
  | inter  : Re → Re → Re
  /-- language complement (extended operator) — F* `R_Not` -/
  | compl  : Re → Re
  deriving DecidableEq, Repr, Inhabited

/-- The largest Unicode codepoint; class negation is taken over
`[0, maxCodepoint]`. -/
def maxCodepoint : Nat := 0x10FFFF

namespace Re

/-! ## 2. Size (F* `size`)

Not the node count: `cat` and `star` carry extra slack (3 instead of 1)
so the F* lexicographic measure had room for the split enumerators. Kept
with the same constants because `Regex.Exec.isEmpty` derives its fuel
budget from it. Every case is `≥ 1` (`size_pos` in `RegexTheorems.lean`).
-/
def size : Re → Nat
  | .empty      => 1
  | .eps        => 1
  | .ranges _   => 1
  | .cat a b    => 3 + size a + size b
  | .alt a b    => 1 + size a + size b
  | .inter a b  => 1 + size a + size b
  | .compl a    => 1 + size a
  | .star a     => 3 + size a

end Re

/-! ## 3. Codepoint ranges -/

/-- Membership of one codepoint in a union of inclusive intervals
(F* `in_ranges`). -/
def inRanges (c : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (lo, hi) :: tl => (lo ≤ c && c ≤ hi) || inRanges c tl

/-- Complement of a sorted-disjoint interval list over `[lo, maxCodepoint]`;
`lo` is the next uncovered codepoint (F* `complement_from`). Total for any
input; exact only when `rs` is sorted ascending with disjoint intervals. -/
def complementFrom (lo : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => if lo ≤ maxCodepoint then [(lo, maxCodepoint)] else []
  | (a, b) :: tl =>
    let head := if a ≥ 1 && lo ≤ a - 1 then [(lo, a - 1)] else []
    let next := if b + 1 > lo then b + 1 else lo
    head ++ complementFrom next tl

/-- Complement of a sorted-disjoint interval list over `[0, maxCodepoint]`
(F* `complement_ranges`). -/
def complementRanges (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  complementFrom 0 rs

/-! ## 4. Denotational semantics: total Boolean membership `mem`

`List.take k w` / `List.drop k w` play the F* `take_n` / `drop_n`
(same semantics: prefix / suffix by length, total for any `k`).
-/

/-- Split enumeration for concatenation (F* `cat_try`): is there a split
index `j ≤ k` with `ma (w.take j) && mb (w.drop j)`? Enumerated from `k`
down to `0`, as in the F* source. -/
def catTry (ma mb : List Nat → Bool) (w : List Nat) : Nat → Bool
  | 0     => ma (w.take 0) && mb (w.drop 0)
  | k + 1 => (ma (w.take (k + 1)) && mb (w.drop (k + 1))) || catTry ma mb w k

/-- Split enumeration for star (F* `star_try`): is there a NON-EMPTY
prefix length `j` with `1 ≤ j ≤ k` such that `ma (w.take j)` and the
remainder `w.drop j` is in the star language `ms`? -/
def starTry (ma ms : List Nat → Bool) (w : List Nat) : Nat → Bool
  | 0     => false
  | k + 1 => (ma (w.take (k + 1)) && ms (w.drop (k + 1))) || starTry ma ms w k

/-- Star language of the language `ma`, with fuel bounding the number of
iterations. `[]` is always accepted; a non-empty word is accepted iff some
non-empty prefix is in `ma` and the (strictly shorter) remainder is in the
star language again. With fuel `≥ |w|` this is exactly the F*
`mem (R_Star a) w` (see `memStar_fuel`). -/
def memStar (ma : List Nat → Bool) : Nat → List Nat → Bool
  | 0,     w => w.isEmpty
  | n + 1, w =>
    match w with
    | []     => true
    | _ :: _ => starTry ma (memStar ma n) w w.length

/-- The reference language (F* `mem`): `mem r w = true` iff the word `w`
(a list of codepoints) is in the language denoted by `r`.
  - `cat a b`: some split `w = w₁ ++ w₂` has `mem a w₁ && mem b w₂`;
  - `star a`: `[]`, or a non-empty prefix in `a` followed by a word in
    `star a`. -/
def mem : Re → List Nat → Bool
  | .empty,      _ => false
  | .eps,        w => w.isEmpty
  | .ranges rs,  w => match w with | [c] => inRanges c rs | _ => false
  | .alt a b,    w => mem a w || mem b w
  | .inter a b,  w => mem a w && mem b w
  | .compl a,    w => !(mem a w)
  | .cat a b,    w => catTry (mem a) (mem b) w w.length
  | .star a,     w => memStar (mem a) w.length w

/-! ## 5. nullable (F* `nullable`) — does the regex accept the empty word? -/

def nullable : Re → Bool
  | .empty     => false
  | .eps       => true
  | .ranges _  => false
  | .cat a b   => nullable a && nullable b
  | .alt a b   => nullable a || nullable b
  | .inter a b => nullable a && nullable b
  | .compl a   => !(nullable a)
  | .star _    => true

/-! ## 6. Smart constructors (F* §6)

Owens–Reppy–Turon similarity rules: absorption (empty / eps laws),
idempotence (`r|r = r`, `r&r = r`), double negation, and a total order on
operands so commutatively-equal terms share one normal form (this is
what keeps the derivative state set finite — `Regex.Exec`). Each
constructor preserves `mem` (`smartAlt_ok` etc. in `RegexTheorems.lean`).
-/

/-- The universal language `Σ*` is the complement of the empty language
(F* `r_universal`). -/
def rUniversal : Re := .compl .empty

/-- Total order on interval lists, lexicographic on endpoints (F*
`ranges_cmp`). Used only to canonicalise `ranges` operands. -/
def rangesCmp : List (Nat × Nat) → List (Nat × Nat) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (a1, b1) :: xs, (a2, b2) :: ys =>
    if a1 ≠ a2 then (if a1 < a2 then .lt else .gt)
    else if b1 ≠ b2 then (if b1 < b2 then .lt else .gt)
    else rangesCmp xs ys

/-- Constructor tag, the primary key of the structural order (F* `tag`
inside `regex_cmp`, same numbering). -/
def Re.tag : Re → Nat
  | .empty => 0 | .eps => 1 | .ranges _ => 2 | .cat _ _ => 3
  | .alt _ _ => 4 | .star _ => 5 | .inter _ _ => 6 | .compl _ => 7

/-- Structural total order on regexes (F* `regex_cmp`), used only to
canonicalise the operand order of commutative nodes. `reCmp a b = .eq`
implies `a = b` (`reCmp_eq` in `RegexTheorems.lean`). -/
def reCmp (a b : Re) : Ordering :=
  if a.tag ≠ b.tag then (if a.tag < b.tag then .lt else .gt)
  else
    match a, b with
    | .ranges x, .ranges y => rangesCmp x y
    | .cat a1 a2, .cat b1 b2 =>
      match reCmp a1 b1 with | .eq => reCmp a2 b2 | c => c
    | .alt a1 a2, .alt b1 b2 =>
      match reCmp a1 b1 with | .eq => reCmp a2 b2 | c => c
    | .inter a1 a2, .inter b1 b2 =>
      match reCmp a1 b1 with | .eq => reCmp a2 b2 | c => c
    | .star a1, .star b1 => reCmp a1 b1
    | .compl a1, .compl b1 => reCmp a1 b1
    | _, _ => .eq

/-- `a ≤ b` in the structural order (F* `regex_le`). -/
def reLe (a b : Re) : Bool := reCmp a b != .gt

/-- Union with empty absorption, idempotence, universal absorption and
canonical operand ordering (F* `smart_alt`). -/
def smartAlt (a b : Re) : Re :=
  if a = .empty then b
  else if b = .empty then a
  else if a = b then a
  else if a = rUniversal || b = rUniversal then rUniversal
  else if reLe a b then .alt a b else .alt b a

/-- Intersection with empty absorption, universal unit, idempotence and
canonical operand ordering (F* `smart_and`). -/
def smartAnd (a b : Re) : Re :=
  if a = .empty || b = .empty then .empty
  else if a = rUniversal then b
  else if b = rUniversal then a
  else if a = b then a
  else if reLe a b then .inter a b else .inter b a

/-- Complement with double-negation collapse (F* `smart_not`). -/
def smartNot : Re → Re
  | .compl x => x
  | a => .compl a

/-- Concatenation with the empty annihilator and eps unit laws
(F* `smart_cat`). -/
def smartCat (a b : Re) : Re :=
  if a = .empty || b = .empty then .empty
  else if a = .eps then b
  else if b = .eps then a
  else .cat a b

/-- Star with empty / eps collapse (both denote `{""}`) and star
idempotence (F* `smart_star`). -/
def smartStar : Re → Re
  | .empty => .eps
  | .eps => .eps
  | .star a => .star a
  | a => .star a

/-! ## Codepoint lists from strings

Lean's `Char` is a validated Unicode scalar value and `String.toList`
decodes UTF-8, so this is the F* `cps_of_string` with no byte-level
detour. -/

/-- The codepoint list of a string (F* `Regex.XSDPattern.cps_of_string`). -/
def cpsOfString (s : String) : List Nat := s.toList.map Char.toNat

/-- Codepoint → `Char`; a value that is not a Unicode scalar value
(surrogates, anything above `maxCodepoint`, the XPath sentinels) becomes
U+FFFD, as in the F* `rx_safe_char`. -/
def safeChar (n : Nat) : Char :=
  if h : n.isValidChar then Char.ofNatAux n h else '�'

/-- The string of a codepoint list (F* `rx_string_of_cps`). -/
def stringOfCps (cps : List Nat) : String := String.ofList (cps.map safeChar)

end L4Factoidal.Regex
