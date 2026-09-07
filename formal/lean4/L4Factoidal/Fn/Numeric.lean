/-
L4Factoidal.Fn.Numeric — the numeric part of XQuery 1.0 and XPath 2.0
Functions and Operators (https://www.w3.org/TR/xpath-functions/), §6.

RIF-DTB 4.5 cites `op:numeric-add`, `op:numeric-subtract`,
`op:numeric-multiply`, `op:numeric-divide`, `op:numeric-integer-divide`
and `op:numeric-mod`; SPARQL 1.1 §17.4.1 cites the same operators for
`+`, `-`, `*` and `/`. They are written HERE, once, over
`XSD.Dec` — the `xs:decimal` value space of XML Schema Part 2 §3.3.3.

`XSD.Dec` already carries addition, subtraction, negation, comparison
and normalisation. This module adds what the F&O operators need and
`XSD.Dec` does not have: multiplication of two decimals, division,
integer division, modulus, and the two roundings.

Division is TRUNCATED at `divScale` fractional digits. XSD 1.1 §3.3.4
gives `xs:decimal` arbitrary precision but lets an implementation state
a limit; this is the limit, stated.
-/
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.Fn.Numeric

open L4Factoidal.XSD (Dec)

/-- Fractional digits kept by `decDiv?`. -/
def divScale : Nat := 18

/-- Lean 4's `Int` `/` and `%` are EUCLIDEAN, not truncating:
    `(-7) / 2` is `-4` and `(-7) % 2` is `1`. F&O's numeric operators
    truncate toward zero (§6.2.4 `op:numeric-divide`, §6.2.5
    `op:numeric-integer-divide`), so every division in this module
    names `Int.tdiv` or `Int.fdiv` explicitly and none is written `/`.

    This was pinned after `RIF/Builtins.lean` carried the comment
    "`Int./` truncates toward zero, which is the direction this states,
    and both signs go the same way" on `divDec` — the comment was
    wrong, and `func:numeric-divide` floored on a negative operand
    where F&O truncates. `divDec` below is corrected. -/
example : ((-7 : Int) / 2) = -4 := by decide
example : ((-7 : Int) % 2) = 1 := by decide
example : Int.tdiv (-7 : Int) 2 = -3 := by decide
example : Int.fdiv (-7 : Int) 2 = -4 := by decide

/-- §6.2.3 `op:numeric-multiply` on `xs:decimal`: exact. -/
def decMul (a b : Dec) : Dec :=
  Dec.norm ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

/-- §6.2.4 `op:numeric-divide`. `none` on a zero divisor, which F&O
    makes the dynamic error `FOAR0001`; each front end maps `none` to
    its own error discipline. -/
def decDiv? (scale : Nat) (a b : Dec) : Option Dec :=
  if b.mantissa == 0 then none
  else
    let num := a.mantissa * (10 : Int) ^ (b.scale + scale)
    let den := b.mantissa * (10 : Int) ^ a.scale
    some (Dec.norm ⟨Int.tdiv num den, scale⟩)

/-- The FLOOR of a decimal, which is not `Dec.floorDiv` — that name is
    on a truncating division. Needed wherever a negative offset must
    carry into the next lower day (`Fn.DateTime.plusDuration`). -/
def decFloorInt (a : Dec) : Int := Int.fdiv a.mantissa ((10 : Int) ^ a.scale)

/-- The fractional part, in `[0, 1)`, for any sign. -/
def decFrac (a : Dec) : Dec := Dec.sub a (Dec.ofInt (decFloorInt a))

/-- §6.4.4 `fn:round`: the nearest integer, and a value exactly halfway
    goes toward POSITIVE infinity. `fn:round(-2.5)` is `-2`, not `-3`.
    RIF-DTB 4.8 needs this and not a half-away-from-zero rounding:
    F&O 10.6.5 rounds `func:multiply-yearMonthDuration` "to the nearest
    month", and the Approved `Builtins_Time` fixture asserts
    `multiply-yearMonthDuration("P2Y11M", 2.3) = "P6Y9M"` — 35 months
    times 2.3 is 80.5 months, and the answer is 81. -/
def decRound (a : Dec) : Int :=
  let p := (10 : Int) ^ a.scale
  if p == 1 then a.mantissa
  else Int.fdiv (a.mantissa * 2 + p) (2 * p)

/-- §6.2.5 `op:numeric-integer-divide`: truncated toward zero. -/
def decIntDiv? (a b : Dec) : Option Int :=
  if b.mantissa == 0 then none
  else
    let s := max a.scale b.scale
    let ma := a.mantissa * (10 : Int) ^ (s - a.scale)
    let mb := b.mantissa * (10 : Int) ^ (s - b.scale)
    some (Int.tdiv ma mb)

/-- §6.2.6 `op:numeric-mod`: `a - (a idiv b) * b`, so the result takes
    the sign of `a`. -/
def decMod? (a b : Dec) : Option Dec :=
  (decIntDiv? a b).map (fun q => Dec.sub a (decMul b (Dec.ofInt q)))

/-! ## The decimal-NUMERAL layer

RIF-DTB's built-ins are given ground terms whose lexical forms are
decimal numerals, and `RIF/Builtins.lean` worked in those strings
rather than in `XSD.Dec`. The five functions below are that layer,
moved here unchanged so there is one home for them. Replacing them
with `XSD.parseDecimalLex` + `Dec.canonical` is commit 7 of the
consolidation plan in
`docs/designissues/2026-09-07-xsd-datatypes-audit.md` §8, and is
deliberately NOT done here: it moves acceptance behaviour and needs
the SPARQL suites as its gate, not the RIF corpus. -/

/-- A decimal numeral as an exact MANTISSA and SCALE: the value is
    `mant / 10 ^ scale`. -/
def decParts (s : String) : Option (Int × Nat) :=
  match (s.splitOn ".") with
  | [i]    => (i.toInt?).map (fun m => (m, 0))
  | [i, f] =>
      if !(f.toList.all (·.isDigit)) then none
      else
        let neg := i.startsWith "-"
        let ii := if i == "" || i == "-" || i == "+" then (if neg then "-0" else "0") else i
        (match ii.toInt? with
         | some m =>
             let frac : Int := Int.ofNat (f.toNat?.getD 0)
             let pow : Int := (10 : Int) ^ f.length
             some ((if neg then m * pow - frac else m * pow + frac), f.length)
         | none   => none)
  | _      => none

/-- Render `mant / 10 ^ scale` as a decimal numeral, without a trailing
    fractional zero run. -/
def decRender (m : Int) (scale : Nat) : String :=
  if scale == 0 then toString m
  else
    let neg := m < 0
    let a := (if neg then -m else m).toNat
    let p := 10 ^ scale
    let ip := a / p
    let fp := a % p
    let fs := (toString fp)
    let fs := String.ofList (List.replicate (scale - fs.length) '0') ++ fs
    let fs := String.ofList (fs.toList.reverse.dropWhile (· == '0')).reverse
    (if neg then "-" else "") ++ toString ip ++ (if fs == "" then "" else "." ++ fs)

private def align (a b : String) : Option (Int × Int × Nat) :=
  match decParts a, decParts b with
  | some (ma, sa), some (mb, sb) =>
      let sc := Nat.max sa sb
      some (ma * (10 : Int) ^ (sc - sa), mb * (10 : Int) ^ (sc - sb), sc)
  | _, _ => none

def addDec (a b : String) : Option String :=
  (align a b).map (fun (x, y, sc) => decRender (x + y) sc)

def subDec (a b : String) : Option String :=
  (align a b).map (fun (x, y, sc) => decRender (x - y) sc)

def mulDec (a b : String) : Option String :=
  match decParts a, decParts b with
  | some (ma, sa), some (mb, sb) => some (decRender (ma * mb) (sa + sb))
  | _, _ => none

/-- `func:numeric-divide`. Division by zero has no value. -/
def divDec (a b : String) : Option String :=
  match decParts a, decParts b with
  | some (ma, sa), some (mb, sb) =>
      if mb == 0 then none
      else
        let num := ma * (10 : Int) ^ (sb + divScale)
        let den := mb * (10 : Int) ^ sa
        some (decRender (Int.tdiv num den) divScale)
  | _, _ => none

/-- A decimal numeral read as an `XSD.Dec`, which is the bridge from
    the numeral layer to the value layer the date/time functions work
    in. -/
def decOfNumeral (s : String) : Option Dec :=
  (decParts s).map (fun (m, sc) => Dec.norm ⟨m, sc⟩)

/-! ## Pins

Each `#guard` is an equation the specification or a vendored fixture
writes out. -/

-- RIF-DTB 4.5, the `Builtins_Numeric` lines.
#guard divDec "6" "3" = some "2"
#guard divDec "1" "8" = some "0.125"
#guard divDec "1" "0" = none
#guard addDec "1.5" "2.25" = some "3.75"
#guard subDec "1" "1" = some "0"
#guard mulDec "-1.5" "2" = some "-3"
-- The truncation direction §6.2.4 states, on both signs. Written `/`
-- this line gave `-0.333…334`, because Lean's `Int` `/` floors.
#guard divDec "-1" "3" = some "-0.333333333333333333"
#guard divDec "1" "3" = some "0.333333333333333333"

-- F&O 6.2.3-6.2.6 over `XSD.Dec`.
#guard decMul ⟨7800, 0⟩ ⟨21, 1⟩ = ⟨16380, 0⟩
#guard decDiv? 18 ⟨40, 0⟩ ⟨-16, 0⟩ = some ⟨-25, 1⟩
#guard decDiv? 18 ⟨1, 0⟩ ⟨0, 0⟩ = none
#guard decIntDiv? ⟨10, 0⟩ ⟨3, 0⟩ = some 3
#guard decIntDiv? ⟨-10, 0⟩ ⟨3, 0⟩ = some (-3)
#guard decMod? ⟨10, 0⟩ ⟨3, 0⟩ = some ⟨1, 0⟩

-- F&O 6.4.4 `fn:round`, including the tie the `Builtins_Time` fixture
-- depends on (80.5 months goes to 81).
#guard decRound ⟨805, 1⟩ = 81
#guard decRound ⟨-25, 1⟩ = -2
#guard decRound ⟨25, 1⟩ = 3
#guard decRound ⟨2333333333333333333, 17⟩ = 23

-- The floor, which is what a negative time-of-day offset needs.
#guard decFloorInt ⟨-15, 1⟩ = -2
#guard decFloorInt ⟨15, 1⟩ = 1
#guard decFrac ⟨-15, 1⟩ = ⟨5, 1⟩

end L4Factoidal.Fn.Numeric
