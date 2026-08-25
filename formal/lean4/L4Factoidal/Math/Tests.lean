/-
L4Factoidal.Math.Tests — build-time checks for the CAS layer.
-/
import L4Factoidal.Math.Diff
import L4Factoidal.Math.Series
import L4Factoidal.Math.Matrix

namespace L4Factoidal.Math

open L4Factoidal.MathML

private def x : Expr := .sym "x"
private def y : Expr := .sym "y"

private def k (e : Expr) : String := exprKey (simplify e)

/-! ## Substitution -/

#guard k (subst "x" (.int 3) (.app "plus" [x, .int 1])) == k (.int 4)
#guard k (subst "x" (.int 3) y) == k y

/-! ## Constant folding, and what is NOT folded

A fold that would be undefined stays symbolic. `1/0` is not a value,
and inventing one is exactly the failure this discipline exists to
prevent. -/

#guard k (.app "plus" [.int 2, .int 3]) == k (.int 5)
#guard k (.app "power" [.int 2, .int 3]) == k (.int 8)
#guard k (.app "divide" [.int 6, .int 2]) == k (.int 3)
#guard k (.app "divide" [.int 1, .int 0]) == k (.app "divide" [.int 1, .int 0])

/-! ## Like terms merge; unlike terms never do -/

#guard k (.app "plus" [x, x]) == k (.app "times" [.int 2, x])
#guard k (.app "plus" [y, .app "times" [.int 2, y],
                          .app "times" [.int 3, y],
                          .app "times" [.int 4, y]])
      == k (.app "times" [.int 10, y])
#guard k (.app "plus" [x, y]) != k (.app "times" [.int 2, x])

/-! ## Identities and annihilation -/

#guard k (.app "plus" [x, .int 0]) == k x
#guard k (.app "times" [x, .int 1]) == k x
#guard k (.app "times" [x, .int 0]) == k (.int 0)
#guard k (.app "power" [x, .int 1]) == k x
#guard k (.app "times" [x, x]) == k (.app "power" [x, .int 2])

/-! `a^0` for a SYMBOLIC base is NOT normalised to 1 — that is wrong
    at `a = 0`, and a rule that changes the domain of definition is
    exactly the kind this module refuses. -/
#guard k (.app "power" [x, .int 0]) == k (.app "power" [x, .int 0])

/-! ## `simplify` is idempotent — the property a normal form rests on -/

private def sample : Expr :=
  .app "plus" [.app "times" [.int 2, x], x, .int 3, .int 4,
               .app "times" [y, y]]

#guard exprKey (simplify sample) == exprKey (simplify (simplify sample))

/-! ## Differentiation -/

#guard k (diff "x" x) == k (.int 1)
#guard k (diff "x" y) == k (.int 0)
#guard k (diff "x" (.app "power" [x, .int 3]))
      == k (.app "times" [.int 3, .app "power" [x, .int 2]])
/-! The product rule, in full: d(x·y)/dx = y. -/
#guard k (diff "x" (.app "times" [x, y])) == k y
#guard k (diff "x" (.app "sin" [x])) == k (.app "cos" [x])

/-! A construct with NO rule comes back wrapped in an explicit marker,
    never with a guessed derivative. `eval` has no rule for that
    function name, so the marker cannot be mistaken for a number. -/
#guard k (diff "x" (.app "arcsin" [x])) == k (.app "diff_unsupported" [.app "arcsin" [x]])
#guard (eval (fun _ => some (1, 1)) (.app "diff_unsupported" [x])).isNone

/-! ## Series

The empty range gives the identity of the operator, with no special
case: an empty `plus` normalises to 0 and an empty `times` to 1. -/

#guard k (summation (.sym "i") "i" 1 4) == k (.int 10)
#guard k (summation (.sym "i") "i" 3 1) == k (.int 0)
#guard k (finiteProduct (.sym "i") "i" 1 4) == k (.int 24)
#guard k (finiteProduct (.sym "i") "i" 3 1) == k (.int 1)

/-! A summation with a symbolic body merges its like terms:
    Σ_{i=1}^{4} (x + i·y) = 4x + 10y. -/
#guard k (summation (.app "plus" [x, .app "times" [.sym "i", y]]) "i" 1 4)
      == k (.app "plus" [.app "times" [.int 4, x], .app "times" [.int 10, y]])

/-! ## Matrices -/

private def e (n : Int) : MEnt := some (n, 1)

private def m22 : List (List MEnt) := [[e 1, e 2], [e 3, e 4]]
private def m23 : List (List MEnt) := [[e 1, e 2, e 3], [e 4, e 5, e 6]]

private def M (rows : List (List MEnt)) : MRes := mkMatrixRes rows
private def V (v : List MEnt) : MRes := mkVectorRes v

#guard mresToString (dynAdd (M m22) (M m22)) == "[[2,4],[6,8]]"
#guard mresToString (dynTranspose (M m23)) == "[[1,4],[2,5],[3,6]]"
#guard mresToString (dynTimes (M m22) (M m22)) == "[[7,10],[15,22]]"
#guard mresToString (dynTimes (M [[e 2]]) (M m22)) == "undef"
#guard mresReason (dynTimes (M m23) (M m23))
      == "matrix-multiply-inner-dimension-mismatch"
#guard mresToString (dynDeterminant (M m22)) == "-2"
#guard mresToString (dynTrace (M m22)) == "5"
#guard mresReason (dynDeterminant (M m23)) == "determinant-requires-square-matrix"

/-! A RAGGED list of rows is not a matrix. It is refused, never
    padded — a padded row would make every later operation answer a
    question about a matrix nobody wrote. -/
#guard mresReason (M [[e 1, e 2], [e 3]]) == "non-rectangular-matrix"

/-! The identity is the multiplicative unit, and the determinant of a
    singular matrix is exactly zero — not nearly zero, because every
    entry is an exact rational. -/
#guard mresToString (dynTimes (M (identityM 2)) (M m22)) == "[[1,2],[3,4]]"
#guard mresToString (dynDeterminant (M [[e 1, e 2], [e 2, e 4]])) == "0"

/-! A 3x3 determinant exercises the cofactor expansion two levels
    deep. -/
#guard mresToString (dynDeterminant
        (M [[e 6, e 1, e 1], [e 4, e (-2), e 5], [e 2, e 8, e 7]])) == "-306"

/-! ## Vectors -/

#guard mresToString (dynScalarProduct (V [e 1, e 2, e 3]) (V [e 4, e 5, e 6])) == "32"
#guard mresToString (dynVectorProduct (V [e 1, e 0, e 0]) (V [e 0, e 1, e 0]))
      == "[0,0,1]"
#guard mresReason (dynVectorProduct (V [e 1, e 0]) (V [e 0, e 1]))
      == "vectorproduct-requires-3-vectors"
#guard mresToString (dynOuterProduct (V [e 1, e 2]) (V [e 3, e 4]))
      == "[[3,4],[6,8]]"

/-! ## Selection is ONE-BASED, and out of range is a refusal -/

#guard mresToString (dynSelector (M m22) 2 1) == "3"
#guard mresReason (dynSelector (M m22) 3 1) == "selector-index-out-of-range"
#guard mresReason (dynSelector (M m22) 0 1) == "selector-index-out-of-range"

/-! ## Exactness

Three thirds are one, which is the whole reason the entries are
rationals and not floats. -/
#guard entToString (entAdd (entAdd (some (1, 3)) (some (1, 3))) (some (1, 3))) == "1"

/-! `add` has no VECTOR case, in this port as in the F* module. Adding
    one silently would be a new operation, not a port; the refusal
    names itself instead. -/
#guard mresReason (dynAdd (V [e 1]) (V [e 1])) == "add-type-mismatch"

end L4Factoidal.Math
