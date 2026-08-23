/-
L4Factoidal.Math.Sigmoid — a bounded-rational `exp` approximation and
a sigmoid point sampler.

Port of `formal/fstar/Math.Sigmoid.fst`. No float appears anywhere:
every value is a scaled INTEGER, `mantissa / 10^scale`, the same
convention the SPARQL decimal path uses.

## The algorithm

    exp(x) = exp(x / 2^m) ^ (2^m)

`reductionShift` (m) divides the argument down to a small `r`,
`expSmall` evaluates a degree-12 Taylor polynomial of `exp` at `r`,
and `squareRepeat` squares the result m times, which raises it to the
`2^m` power. Repeated squaring, not naive exponentiation.

## Why FIXED precision and not exact rationals

Exact rationals are the more transparent choice and are a performance
trap here: each exact-rational squaring roughly SQUARES the bit length
of numerator and denominator, so ten squarings multiply the starting
bit length by about a thousand. The fixed-point multiply and divide
below truncate back to `workScale` fractional digits at every step,
which is what keeps every intermediate value's digit count constant
across an arbitrary chain of multiplies. That truncation is the one
place this module approximates, and it is stated rather than hidden.
-/
namespace L4Factoidal.Math.Sigmoid

/-- The interchange representation: `mantissa / 10^scale`. -/
abbrev Scaled := Int × Nat

def pow10 : Nat → Int
  | 0     => 1
  | n + 1 => 10 * pow10 n

def ipow (b : Int) : Nat → Int
  | 0     => 1
  | n + 1 => b * ipow b n

def ifact : Nat → Int
  | 0     => 1
  | n + 1 => (n + 1 : Int) * ifact n

/-! ## The internal fixed-point representation

A plain `Int` mantissa, always at the ONE fixed `workScale`. -/

def workScale : Nat := 24
def workPow10 : Int := pow10 workScale

/-- Interchange to internal. EXACT when the caller's scale is at most
    `workScale` — it just pads with zeros, which is every caller here.
    A larger scale TRUNCATES, which is documented rather than
    silently claimed exact. -/
def toWork (s : Scaled) : Int :=
  let (m, sc) := s
  if sc ≤ workScale then m * pow10 (workScale - sc)
  else
    let d := pow10 (sc - workScale)
    if d == 0 then m else m / d

def fromWork (wp : Int) (scale : Nat) : Scaled :=
  if scale ≥ workScale then (wp * pow10 (scale - workScale), scale)
  else
    let d := pow10 (workScale - scale)
    if d == 0 then (wp, scale) else (wp / d, scale)

def wpFromInt (n : Int) : Int := n * workPow10

/-! Add, subtract and negate are EXACT: both sides carry the same
    fixed scale, so no truncation is needed or performed. -/
def wpAdd (a b : Int) : Int := a + b
def wpSub (a b : Int) : Int := a - b
def wpNeg (a : Int) : Int := -a

/-- Multiply and divide are the SIZE-BOUNDING operations: compute the
    exact product or quotient scaled by `workPow10`, then truncate
    back. This is what holds the digit count constant across a chain
    of multiplies. -/
def wpMul (a b : Int) : Int := if workPow10 == 0 then 0 else (a * b) / workPow10
def wpDiv (a b : Int) : Int := if b == 0 then 0 else (a * workPow10) / b

def wpIPow (base : Int) : Nat → Int
  | 0     => wpFromInt 1
  | e + 1 => wpMul base (wpIPow base e)

/-- `Σ_{k} r^k / k!`, `fuel` terms starting at index `termIdx`. -/
def taylorSum (r : Int) (termIdx : Nat) : Nat → Int → Int
  | 0,     acc => acc
  | f + 1, acc =>
      let rk := wpIPow r termIdx
      let factk := wpFromInt (ifact termIdx)
      taylorSum r (termIdx + 1) f (wpAdd acc (wpDiv rk factk))

/-! ## The fixed constants -/

def reductionShift : Nat := 10   -- divide the argument by 2^10
def taylorTerms : Nat := 13      -- k = 0 … 12, a degree-12 polynomial
def outputScale : Nat := 9       -- nine fractional decimal digits out

def expSmall (r : Int) : Int := taylorSum r 0 taylorTerms (wpFromInt 0)

/-- `v ↦ v^(2^times)`. -/
def squareRepeat (v : Int) : Nat → Int
  | 0     => v
  | n + 1 => squareRepeat (wpMul v v) n

def expApproxWp (xWp : Int) : Int :=
  let divisor := wpFromInt (ipow 2 reductionShift)
  squareRepeat (expSmall (wpDiv xWp divisor)) reductionShift

/-- `exp(x)`, over the interchange representation. -/
def expApprox (x : Scaled) : Scaled :=
  fromWork (expApproxWp (toWork x)) outputScale

/-! ## Sigmoid sampling

`L / (1 + exp(-k(x - x0)))` at `n+1` evenly spaced points in
`[xmin, xmax]`. Everything — the sample points included — is computed
in the same bounded fixed point, and rounded to `outputScale` digits
only at the very end. -/

def sigmoidPointsWp (kWp x0Wp lWp xminWp stepWp : Int) (i : Nat)
    : Nat → List (Int × Int)
  | 0     => []
  | f + 1 =>
      let xWp := wpAdd xminWp (wpMul (wpFromInt i) stepWp)
      let negKdx := wpNeg (wpMul kWp (wpSub xWp x0Wp))
      let eWp := expApproxWp negKdx
      -- A square is never negative, so `1 + e` is positive and the
      -- division below never divides by zero. `wpDiv` is defined for
      -- that case regardless, which is what keeps the function total
      -- rather than relying on the argument.
      let yWp := wpDiv lWp (wpAdd (wpFromInt 1) eWp)
      (xWp, yWp) :: sigmoidPointsWp kWp x0Wp lWp xminWp stepWp (i + 1) f

/-- `n+1` samples over `[xmin, xmax]`. `n = 0` yields the single
    sample at `xmin`, with the step set to zero rather than dividing
    by it. -/
def sigmoidPoints (k x0 l xmin xmax : Scaled) (n : Nat) : List (Scaled × Scaled) :=
  let kWp := toWork k
  let x0Wp := toWork x0
  let lWp := toWork l
  let xminWp := toWork xmin
  let xmaxWp := toWork xmax
  let stepWp := if n == 0 then wpFromInt 0
                else wpDiv (wpSub xmaxWp xminWp) (wpFromInt n)
  (sigmoidPointsWp kWp x0Wp lWp xminWp stepWp 0 (n + 1)).map
    (fun p => (fromWork p.1 outputScale, fromWork p.2 outputScale))

end L4Factoidal.Math.Sigmoid
