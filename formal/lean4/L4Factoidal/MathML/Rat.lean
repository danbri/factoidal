/-
L4Factoidal.MathML.Rat — exact rational arithmetic for Content MathML.

Split out of `MathML.Core` so that `MathML.Matrix` can use it without
importing the evaluator that itself needs matrices. The names are
unchanged and stay in the `L4Factoidal.MathML` namespace, so every
existing reference resolves exactly as before.

No floating point: an entry is `(num, den)` in lowest terms with a
positive denominator.
-/

namespace L4Factoidal.MathML

/-! ## Exact rational arithmetic -/

private partial def gcdNat (a b : Nat) : Nat := if b == 0 then a else gcdNat b (a % b)

/-- Normalise to lowest terms with a positive denominator. A zero
    denominator collapses to `0/1` rather than propagating — Content
    MathML has no infinity, so the F* module treats it as absent
    rather than inventing a value. -/
def normRat (n d : Int) : Int × Int :=
  if d == 0 then (0, 1)
  else
    let s : Int := if d < 0 then -1 else 1
    let n := n * s
    let d := d * s
    let g : Int := gcdNat n.natAbs d.natAbs
    if g == 0 then (0, 1) else (n / g, d / g)

def addRat (a b : Int × Int) : Int × Int :=
  normRat (a.1 * b.2 + b.1 * a.2) (a.2 * b.2)

def mulRat (a b : Int × Int) : Int × Int := normRat (a.1 * b.1) (a.2 * b.2)
def negRat (a : Int × Int) : Int × Int := (-a.1, a.2)
def subRat (a b : Int × Int) : Int × Int := addRat a (negRat b)

/-- Division. A zero divisor yields `none` — MathML has no infinity,
    so this refuses rather than inventing one. -/
def divRat (a b : Int × Int) : Option (Int × Int) :=
  if b.1 == 0 then none else some (normRat (a.1 * b.2) (a.2 * b.1))

def cmpRat (a b : Int × Int) : Ordering := compare (a.1 * b.2) (b.1 * a.2)


end L4Factoidal.MathML
