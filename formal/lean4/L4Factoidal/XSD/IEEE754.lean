/-
L4Factoidal.XSD.IEEE754 — decimal lexical to IEEE-754 value.

Port of `formal/fstar/XSD.IEEE754.fst` (292 lines).

The module answers one question: do two numeric lexical forms denote the
SAME IEEE-754 value, with the sign of zero distinguished, overflow going
to the same signed infinity, and round-to-nearest-ties-to-even? It never
emits a float, only compares, so the whole computation is exact
big-integer rational arithmetic. No floating point is used anywhere in
the definitions below. This is what the RDF 1.2 D-entailment tests need
for `xsd:double`, `xsd:float` and `rdf:JSON` numbers.

## The method

A lexical parses to a sign and an exact rational `M * 10^E` — `M` the
mantissa from the concatenated integer and fraction digits, `E` the
adjusted exponent. That rational is rounded to the target binary format
by comparing it against powers of two with big-integer cross
multiplication: `a/b ≥ 2^k` iff `a ≥ b * 2^k` for `k ≥ 0`, iff
`a * 2^(-k) ≥ b` for `k < 0`, all exact integers. The round and sticky
decision is the exact remainder of that division. The result is a
canonical, comparable record, and two lexicals are equal iff they share
it.

- binary64: 53-bit significand, exponent range emin = -1022, emax = 1023.
- binary32: 24-bit significand, emin = -126, emax = 127.

`xsd:float` uses DOUBLE ROUNDING (decimal → binary64 → binary32), which
is what OCaml's `Int32.bits_of_float (float_of_string s)`, JavaScript's
`Math.fround(Number(s))` and Python all do. Single rounding (decimal →
binary32 directly) differs from that only on double-rounding boundary
decimals; matching the deployed path keeps both trees in step with those
runtimes.

## Differences from the F\*

1. `pow2` and `pow10` are `2 ^ n` and `10 ^ n`. The F\* module defines
   them recursively to carry a `pos` refinement; Lean's `Nat` needs no
   such witness.
2. `bitlen` is `Nat.log2 n + 1` for `n > 0`, which is the same function
   the F\* recursion computes.
3. `mul_pos` is absent. It exists in F\* to keep a `pos` type through a
   multiplication without per-site SMT nudging; `Nat` multiplication in
   Lean carries no such obligation.
4. `fvalToBits64` and `fvalToBits32` are new. They exist so the test
   module can compare this exact-rational implementation against an
   independent correctly-rounded one, bit for bit, rather than against
   a restatement of the same algorithm. Nothing in the port uses them.
-/

namespace L4Factoidal.XSD

/-! ## Exact big-integer helpers -/

/-- Bits in `n`: 0 for `n = 0`, `⌊log₂ n⌋ + 1` otherwise. Same function
    the F\* `bitlen` recursion computes. -/
def bitlen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- `num/den ≥ 2^k`, exactly, by cross multiplication. -/
def geqRatio (num den : Nat) (k : Int) : Bool :=
  if k ≥ 0 then num ≥ den * 2 ^ k.toNat
  else num * 2 ^ (-k).toNat ≥ den

/-- `⌊log₂(num/den)⌋`, exact. The candidate `bitlen num - bitlen den` is
    either the answer or one too high, so one comparison settles it. -/
def floorLog2Ratio (num den : Nat) : Int :=
  let k0 : Int := (bitlen num : Int) - (bitlen den : Int)
  if geqRatio num den k0 then k0 else k0 - 1

/-- Round `n/d` to the nearest integer, ties to even. Exact. -/
def roundTiesEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  let twice := 2 * r
  if twice < d then q
  else if twice > d then q + 1
  else if q % 2 == 0 then q else q + 1

/-! ## The canonical value

Sign-aware and comparable, so equality of two lexicals is equality of
two records. -/

inductive FClass where
  | zero                            -- signed zero
  | inf                             -- signed infinity
  | nan                             -- not a number; equal to nothing
  | finite (mant : Nat) (bexp : Int)
      -- value = mant * 2^bexp, normalised: normals have
      -- mant ∈ [2^(p-1), 2^p); subnormals have bexp = emin - (p-1)
  deriving Repr, DecidableEq, Inhabited

structure Fval where
  neg : Bool                        -- true means negative
  cls : FClass
  deriving Repr, DecidableEq, Inhabited

/-- IEEE-754 value equality. NaN equals nothing, including itself; `+0`
    and `-0` differ; `+∞` and `-∞` differ. -/
def fvalEq (a b : Fval) : Bool :=
  match a.cls, b.cls with
  | .nan, _ => false
  | _, .nan => false
  | .zero, .zero => a.neg == b.neg
  | .inf, .inf => a.neg == b.neg
  | .finite s1 e1, .finite s2 e2 => a.neg == b.neg && s1 == s2 && e1 == e2
  | _, _ => false

/-! ## Rounding an exact positive rational to a target format -/

/-- The magnitude's class: `.zero` on underflow, `.inf` on overflow,
    `.finite s e` otherwise. The sign is attached by the caller.
    `num > 0` is required. -/
def roundRational (p : Nat) (emin emax : Int) (num den : Nat) : FClass :=
  let eNorm := floorLog2Ratio num den
  let eDenorm : Int := emin - (p - 1)      -- the subnormal grid's fixed exponent
  let eMaxNormal : Int := emax - (p - 1)   -- exponent of the largest finite significand
  let eTent := eNorm - (p - 1)
  -- Strict overflow short-circuit: above this the round bits cannot
  -- matter, and it avoids building 2^k for k in the thousands on 1e400.
  if eTent > eMaxNormal then .inf
  else
    -- Clamp into the subnormal grid so the quantisation step is a
    -- uniform 2^eDenorm for every subnormal and the smallest normal.
    let e : Int := if eTent < eDenorm then eDenorm else eTent
    let bigN : Nat := if e ≥ 0 then num else num * 2 ^ (-e).toNat
    let bigD : Nat := if e ≥ 0 then den * 2 ^ e.toNat else den
    let s0 := roundTiesEven bigN bigD
    if s0 == 0 then .zero
    else
      -- Rounding can carry the significand up to exactly 2^p.
      let twop := 2 ^ p
      let s := if s0 ≥ twop then s0 / 2 else s0
      let e2 := if s0 ≥ twop then e + 1 else e
      if e2 > eMaxNormal then .inf else .finite s e2

/-! ## Lexical parsing -/

def isDigitChar (c : Char) : Bool := c.toNat ≥ 48 && c.toNat ≤ 57

def allDigits (cs : List Char) : Bool := cs.all isDigitChar

/-- Accumulating decimal reader. Non-digits are clamped to 0 so the
    result stays a `Nat`; callers check `allDigits` first, so the clamp
    never fires on well-formed input. -/
def digitsToNat (acc : Nat) : List Char → Nat
  | []      => acc
  | c :: cs =>
      let raw := c.toNat
      let d := if raw < 48 || raw > 57 then 0 else raw - 48
      digitsToNat (acc * 10 + d) cs

/-- Split at the first occurrence of `ch`: `(before, some after)` if it
    is present, `(all, none)` otherwise. -/
def splitAtChar (ch : Char) : List Char → (List Char × Option (List Char))
  | []      => ([], none)
  | c :: cs =>
      if c == ch then ([], some cs)
      else
        let (before, after) := splitAtChar ch cs
        (c :: before, after)

/-- An exponent tail: optional sign then one or more digits. -/
def parseSignedInt : List Char → Option Int
  | []      => none
  | c :: cs =>
      let (neg, digits) :=
        if c == '+' then (false, cs)
        else if c == '-' then (true, cs)
        else (false, c :: cs)
      if !digits.isEmpty && allDigits digits then
        let v := digitsToNat 0 digits
        some (if neg then -(v : Int) else (v : Int))
      else none

inductive Parsed where
  | num (neg : Bool) (m : Nat) (e : Int)
  | inf (neg : Bool)
  | nan
  deriving Repr, DecidableEq, Inhabited

/-- A decimal or scientific lexical, after INF and NaN are handled. -/
def parseDecimal (neg : Bool) (chars : List Char) : Option Parsed :=
  let (mant, expOpt) :=
    let split := splitAtChar 'e' chars
    if split.2.isSome then split else splitAtChar 'E' chars
  match (match expOpt with | none => some (0 : Int) | some ec => parseSignedInt ec) with
  | none => none
  | some expVal =>
      let (ipart, fopt) := splitAtChar '.' mant
      let fpart := fopt.getD []
      if allDigits ipart && allDigits fpart && ipart.length + fpart.length ≥ 1 then
        some (.num neg (digitsToNat 0 (ipart ++ fpart))
                       (expVal - (fpart.length : Int)))
      else none

def parseLexical (s : String) : Option Parsed :=
  if s == "NaN" then some .nan
  else if s == "INF" || s == "+INF" then some (.inf false)
  else if s == "-INF" then some (.inf true)
  else
    match s.toList with
    | []      => none
    | c :: cs =>
        if c == '+' then parseDecimal false cs
        else if c == '-' then parseDecimal true cs
        else parseDecimal false (c :: cs)

/-! ## Canonicalising a parsed lexical -/

def canon (p : Nat) (emin emax : Int) : Parsed → Fval
  | .nan       => { neg := false, cls := .nan }
  | .inf neg   => { neg := neg, cls := .inf }
  | .num neg m e =>
      if m == 0 then { neg := neg, cls := .zero }
      else
        let num := if e ≥ 0 then m * 10 ^ e.toNat else m
        let den := if e ≥ 0 then 1 else 10 ^ (-e).toNat
        { neg := neg, cls := roundRational p emin emax num den }

/-- binary64. -/
def canonDouble (pv : Parsed) : Fval := canon 53 (-1022) 1023 pv

/-- binary32, by DOUBLE ROUNDING through binary64 — see the module
    header. A finite binary64 value `s * 2^e` is an exact dyadic
    rational, which is re-rounded to binary32. -/
def canonFloat (pv : Parsed) : Fval :=
  let d64 := canonDouble pv
  match d64.cls with
  | .nan  => { neg := d64.neg, cls := .nan }
  | .zero => { neg := d64.neg, cls := .zero }
  | .inf  => { neg := d64.neg, cls := .inf }
  | .finite s e =>
      let num := if e ≥ 0 then s * 2 ^ e.toNat else s
      let den := if e ≥ 0 then 1 else 2 ^ (-e).toNat
      { neg := d64.neg, cls := roundRational 24 (-126) 127 num den }

/-! ## Value equality — the public API

Malformed input falls back to string equality, as in the F\* source.
That is what makes the function total on arbitrary lexicals; a lexical
outside the datatype's lexical space has no value to compare. -/

def doubleValueEq (a b : String) : Bool :=
  match parseLexical a, parseLexical b with
  | some pa, some pb => fvalEq (canonDouble pa) (canonDouble pb)
  | _, _ => a == b

def floatValueEq (a b : String) : Bool :=
  match parseLexical a, parseLexical b with
  | some pa, some pb => fvalEq (canonFloat pa) (canonFloat pb)
  | _, _ => a == b

/-- `rdf:JSON` numbers are IEEE-754 binary64. -/
def jsonNumberEq (a b : String) : Bool := doubleValueEq a b

/-! ## Bit patterns, for testing only

Nothing above uses these. They exist so `IEEE754Tests.lean` can compare
this implementation against an independent correctly-rounded one bit for
bit, instead of against a restatement of the same algorithm.

A quiet NaN has many bit patterns; the canonical one is used, since
`FClass.nan` carries no payload. -/

def fvalToBits64 (v : Fval) : UInt64 :=
  let signBit : UInt64 := if v.neg then (1 : UInt64) <<< 63 else 0
  match v.cls with
  | .nan  => 0x7FF8000000000000
  | .zero => signBit
  | .inf  => signBit ||| 0x7FF0000000000000
  | .finite s e =>
      -- normals: s ∈ [2^52, 2^53), value = s * 2^e, biased = e + 52 + 1023
      -- subnormals: e = -1074 and s < 2^52, biased = 0, fraction = s
      if s < 2 ^ 52 then signBit ||| UInt64.ofNat s
      else
        let biased : Int := e + 52 + 1023
        let b : Nat := if biased < 0 then 0 else biased.toNat
        signBit ||| (UInt64.ofNat b <<< 52) ||| UInt64.ofNat (s - 2 ^ 52)

def fvalToBits32 (v : Fval) : UInt32 :=
  let signBit : UInt32 := if v.neg then (1 : UInt32) <<< 31 else 0
  match v.cls with
  | .nan  => 0x7FC00000
  | .zero => signBit
  | .inf  => signBit ||| 0x7F800000
  | .finite s e =>
      if s < 2 ^ 23 then signBit ||| UInt32.ofNat s
      else
        let biased : Int := e + 23 + 127
        let b : Nat := if biased < 0 then 0 else biased.toNat
        signBit ||| (UInt32.ofNat b <<< 23) ||| UInt32.ofNat (s - 2 ^ 23)

/-- `(bits64, bits32)` of a lexical, or `none` if it is not in the
    lexical space. -/
def bitsOfLexical (s : String) : Option (UInt64 × UInt32) :=
  (parseLexical s).map (fun pv => (fvalToBits64 (canonDouble pv),
                                   fvalToBits32 (canonFloat pv)))

end L4Factoidal.XSD
