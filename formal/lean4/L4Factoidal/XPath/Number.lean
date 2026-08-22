/-
L4Factoidal.XPath.Number — the XPath 1.0 number type, ported from
`formal/fstar/XPath.Eval.fst`.

Spec: XPath 1.0 §3.5. XPath numbers are IEEE 754 doubles, so NaN and
±Infinity are REAL VALUES with specified behaviour, not error states.
But the F* port represents the finite case as an EXACT decimal
(`mantissa / 10^scale`) rather than a float, so `0.1 + 0.2 = 0.3`
holds and `number('0.1')` compares equal to the literal `0.1`.

That combination — IEEE's special values, exact decimal arithmetic
underneath — is deliberate: the special values are observable through
`NaN`-producing conversions and division, while binary rounding is
not something any XPath test actually asks for.
-/

namespace L4Factoidal.XPath

/-- An XPath number. `finite mantissa scale` denotes
    `mantissa / 10^scale`. -/
inductive Num where
  | nan
  | posInf
  | negInf
  | finite (mantissa : Int) (scale : Nat)
deriving Repr, DecidableEq, Inhabited

namespace Num

def pow10 : Nat → Int
  | 0     => 1
  | n + 1 => 10 * pow10 n

def ofInt (i : Int) : Num := .finite i 0
def zero : Num := ofInt 0

/-- Align two finite values to a common scale. -/
def align (m1 : Int) (s1 : Nat) (m2 : Int) (s2 : Nat) : Int × Int × Nat :=
  if s1 ≥ s2 then (m1, m2 * pow10 (s1 - s2), s1)
  else (m1 * pow10 (s2 - s1), m2, s2)

def add : Num → Num → Num
  | .nan, _ | _, .nan => .nan
  | .posInf, .negInf | .negInf, .posInf => .nan   -- ∞ + -∞ is NaN
  | .posInf, _ | _, .posInf => .posInf
  | .negInf, _ | _, .negInf => .negInf
  | .finite m1 s1, .finite m2 s2 =>
      let (a, b, s) := align m1 s1 m2 s2; .finite (a + b) s

def neg : Num → Num
  | .nan => .nan
  | .posInf => .negInf
  | .negInf => .posInf
  | .finite m s => .finite (-m) s

def sub (a b : Num) : Num := add a (neg b)

def mul : Num → Num → Num
  | .nan, _ | _, .nan => .nan
  | .finite 0 _, .posInf | .finite 0 _, .negInf => .nan   -- 0 × ∞ is NaN
  | .posInf, .finite 0 _ | .negInf, .finite 0 _ => .nan
  | .posInf, .posInf | .negInf, .negInf => .posInf
  | .posInf, .negInf | .negInf, .posInf => .negInf
  | .posInf, .finite m _ | .finite m _, .posInf => if m > 0 then .posInf else .negInf
  | .negInf, .finite m _ | .finite m _, .negInf => if m > 0 then .negInf else .posInf
  | .finite m1 s1, .finite m2 s2 => .finite (m1 * m2) (s1 + s2)

/-- Comparison. NaN compares unequal to EVERYTHING, including itself
    — the property that makes `nan != nan` true in XPath. -/
def cmp : Num → Num → Option Ordering
  | .nan, _ | _, .nan => none
  | .posInf, .posInf | .negInf, .negInf => some .eq
  | .posInf, _ => some .gt
  | _, .posInf => some .lt
  | .negInf, _ => some .lt
  | _, .negInf => some .gt
  | .finite m1 s1, .finite m2 s2 =>
      let (a, b, _) := align m1 s1 m2 s2
      some (compare a b)

def eq (a b : Num) : Bool := cmp a b == some .eq
def lt (a b : Num) : Bool := cmp a b == some .lt
def le (a b : Num) : Bool := match cmp a b with
  | some .lt | some .eq => true
  | _ => false

/-- Division. XPath 1.0 follows IEEE: `x/0` is ±Infinity for non-zero
    `x`, and `0/0` is NaN — NOT an error. Exact division is only
    possible when it terminates in decimal, so a non-terminating
    quotient is computed to a bounded scale, which is the one place
    this representation approximates and is marked as such. -/
def div (a b : Num) : Num :=
  match a, b with
  | .nan, _ | _, .nan => .nan
  | .posInf, .posInf | .posInf, .negInf
  | .negInf, .posInf | .negInf, .negInf => .nan
  | .posInf, .finite m _ => if m ≥ 0 then .posInf else .negInf
  | .negInf, .finite m _ => if m ≥ 0 then .negInf else .posInf
  | .finite _ _, .posInf | .finite _ _, .negInf => .finite 0 0
  | .finite m1 s1, .finite m2 s2 =>
      if m2 == 0 then
        (if m1 == 0 then .nan else if m1 > 0 then .posInf else .negInf)
      else
        -- Scale the numerator up so the quotient carries 18 decimal
        -- places, then truncate: the bounded-precision point.
        let extra := 18
        let (a', b', _) := align m1 s1 m2 s2
        .finite (a' * pow10 extra / b') extra

/-- Is this the number zero? Used by boolean conversion. -/
def isZero : Num → Bool
  | .finite m _ => m == 0
  | _           => false

/-- §4.4 `boolean()` on a number: false for zero and NaN, true
    otherwise. NaN being FALSE is the rule that surprises people. -/
def toBool : Num → Bool
  | .nan => false
  | .finite m _ => m != 0
  | _ => true

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- §4.4 `number()` on a string. Anything that is not a valid XPath
    number lexeme becomes NaN rather than an error. -/
def ofString (s : String) : Num :=
  let cs := s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
  let cs := (cs.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')).reverse
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | _        => (false, cs)
  let ip := cs.takeWhile isDigit
  let rest := cs.dropWhile isDigit
  let (fp, rest) := match rest with
    | '.' :: r => (r.takeWhile isDigit, r.dropWhile isDigit)
    | _        => ([], rest)
  if !rest.isEmpty || (ip.isEmpty && fp.isEmpty) then .nan
  else
    let digits := ip ++ fp
    let m : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat : Int)) 0
    .finite (if neg then -m else m) fp.length

end Num
end L4Factoidal.XPath
