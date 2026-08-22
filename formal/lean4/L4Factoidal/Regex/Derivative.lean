/-
L4Factoidal.Regex.Derivative — Brzozowski derivatives and the matcher
built on them.

Port of `formal/fstar/Regex.Derivative.fst` (issue #304, phase 1). The
correctness theorems live in `RegexTheorems.lean`:

    nullable_correct : nullable r = true ↔ mem r [] = true
    deriv_correct    : mem (deriv c r) w = mem r (c :: w)
    matches_correct  : matches r w = mem r w

All three hold for the FULL AST including `inter` and `compl` — no
`sorry`, no axiom, no fragment carve-out (the F* source likewise has no
admit and no `--lax`).

Derivative identities realised (Brzozowski 1964):
    D_c(empty)  = empty
    D_c(eps)    = empty
    D_c(ranges) = eps  if c ∈ ranges, else empty
    D_c(r|s)    = D_c(r) | D_c(s)
    D_c(r&s)    = D_c(r) & D_c(s)
    D_c(¬r)     = ¬D_c(r)
    D_c(rs)     = (D_c r) s  |  (nullable r ? D_c(s) : empty)
    D_c(r*)     = (D_c r) r*

The `cat` and `star` cases use PLAIN `Re.cat` (not `smartCat`) so the
correctness proof needs only the `smartAlt` / `smartAnd` / `smartNot`
language lemmas. `Regex.Exec.nderiv` re-normalises with `smartCat` and
the ACI flatten for state finiteness; that is the performance layer.
-/
import L4Factoidal.Regex.Syntax

namespace L4Factoidal.Regex.Derivative

open Re

/-- The Brzozowski derivative of `r` by the codepoint `c` (F* `deriv`). -/
def deriv (c : Nat) : Re → Re
  | .empty     => .empty
  | .eps       => .empty
  | .ranges rs => if inRanges c rs then .eps else .empty
  | .alt a b   => smartAlt (deriv c a) (deriv c b)
  | .inter a b => smartAnd (deriv c a) (deriv c b)
  | .compl a   => smartNot (deriv c a)
  | .cat a b   =>
    let left := Re.cat (deriv c a) b
    if nullable a then smartAlt left (deriv c b) else left
  | .star a    => Re.cat (deriv c a) (.star a)

/-- Fold the derivative over a word (F* `deriv_word`). -/
def derivWord (r : Re) : List Nat → Re
  | []        => r
  | c :: rest => derivWord (deriv c r) rest

/-- Whole-word matching: derive by every codepoint, then test nullability
(F* `matches`; `accepts` here because `matches` is a Lean keyword). Proven equal to `mem` in `RegexTheorems.lean`
(`matches_correct`). -/
def accepts (r : Re) (w : List Nat) : Bool := nullable (derivWord r w)

end L4Factoidal.Regex.Derivative
