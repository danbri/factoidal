/-
L4Factoidal.Math.Series — finite summation and product over an integer
index range.

Port of `formal/fstar/Math.Series.fst`. NO general binder machinery is
introduced: the bounds are CONCRETE integers, so each term comes from
substituting the index numerically and the whole thing is combined
with the n-ary `plus` / `times` nodes and normalised by `simplify`.

    summation body i lo hi      = simplify (Σ_{k=lo}^{hi} body[i := k])
    finiteProduct body i lo hi  = simplify (Π_{k=lo}^{hi} body[i := k])

The empty-range identities fall straight out of the normaliser: an
empty `plus` is `0` and an empty `times` is `1`, so `hi < lo` gives
those with no special case.

The product is LEFT FACTORED — it is not distributed, which is a
separate `expand`. A SYMBOLIC bound is out of scope: closed forms for
one (a Gauss sum, a geometric series) need the bound-variable layer
this module deliberately does not have.
-/
import L4Factoidal.Math.Simplify

namespace L4Factoidal.Math

open L4Factoidal.MathML

/-- The number of terms in the inclusive range, zero when empty. -/
def seriesCount (lo hi : Int) : Nat := if hi < lo then 0 else (hi - lo + 1).toNat

def seriesTerms (body : Expr) (idx : String) (lo : Int) : Nat → List Expr
  | 0     => []
  | n + 1 => subst idx (.int lo) body :: seriesTerms body idx (lo + 1) n

def seriesRangeTerms (body : Expr) (idx : String) (lo hi : Int) : List Expr :=
  seriesTerms body idx lo (seriesCount lo hi)

/-- Finite summation. The normaliser's like-term merge turns
    `summation (x + i*y) i 1 4` into `4*x + 10*y`. -/
def summation (body : Expr) (idx : String) (lo hi : Int) : Expr :=
  simplify (.app "plus" (seriesRangeTerms body idx lo hi))

/-- Finite product, LEFT FACTORED. -/
def finiteProduct (body : Expr) (idx : String) (lo hi : Int) : Expr :=
  simplify (.app "times" (seriesRangeTerms body idx lo hi))

end L4Factoidal.Math
