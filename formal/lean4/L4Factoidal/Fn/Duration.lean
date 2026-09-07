/-
L4Factoidal.Fn.Duration — the duration accessors and arithmetic of
XQuery 1.0 and XPath 2.0 Functions and Operators §10.5 and §10.6.

RIF-DTB 4.8.1 cites `fn:years-from-duration` through
`fn:seconds-from-duration` and `op:add-yearMonthDurations` through
`op:divide-dayTimeDuration-by-dayTimeDuration`; RIF-DTB 4.8.2 cites
`op:duration-equal`, `op:yearMonthDuration-less-than` and
`op:dayTimeDuration-less-than`.

The value space is `XSD.DurValue`, XML Schema Part 2 §3.3.6's
two-property model: a signed month count and a signed second count.
`xs:yearMonthDuration` (§3.4.27) is the sub-space with zero seconds and
`xs:dayTimeDuration` (§3.4.28) the sub-space with zero months, so one
representation carries all three datatypes and the sub-space is a
condition on the value, not a separate type.

Every accessor takes the sign of the WHOLE duration, so
`fn:minutes-from-duration("-P5DT12H30M")` is `-30` and not `30`. That
is truncation toward zero at every level, which is why `Int.tdiv` and
`Int.tmod` are named explicitly rather than written `/` and `%`.
-/
import L4Factoidal.Fn.Numeric

namespace L4Factoidal.Fn.Duration

open L4Factoidal.XSD

/-! ## Constructors -/

def yearMonth (months : Int) : DurValue := ⟨months, Dec.zero⟩
def dayTime (seconds : Dec) : DurValue := ⟨0, seconds⟩
def zero : DurValue := ⟨0, Dec.zero⟩

/-- Is the value in the `xs:yearMonthDuration` sub-space? -/
def isYearMonth (d : DurValue) : Bool := Dec.cmp d.seconds Dec.zero == .eq
/-- Is the value in the `xs:dayTimeDuration` sub-space? -/
def isDayTime (d : DurValue) : Bool := d.months == 0

def neg (d : DurValue) : DurValue := ⟨-d.months, Dec.neg d.seconds⟩

/-! ## §10.5.1-10.5.6 — the accessors -/

/-- §10.5.1 `fn:years-from-duration`. -/
def yearsFrom (d : DurValue) : Int := Int.tdiv d.months 12

/-- §10.5.2 `fn:months-from-duration`. -/
def monthsFrom (d : DurValue) : Int := Int.tmod d.months 12

/-- The whole seconds of the second component, truncated toward zero. -/
private def wholeSecs (d : DurValue) : Int := Dec.floorDiv d.seconds

/-- §10.5.3 `fn:days-from-duration`. -/
def daysFrom (d : DurValue) : Int := Int.tdiv (wholeSecs d) 86400

/-- §10.5.4 `fn:hours-from-duration`. -/
def hoursFrom (d : DurValue) : Int := Int.tdiv (Int.tmod (wholeSecs d) 86400) 3600

/-- §10.5.5 `fn:minutes-from-duration`. -/
def minutesFrom (d : DurValue) : Int := Int.tdiv (Int.tmod (wholeSecs d) 3600) 60

/-- §10.5.6 `fn:seconds-from-duration`, an `xs:decimal` that carries the
    fraction. -/
def secondsFrom (d : DurValue) : Dec :=
  let w := wholeSecs d
  Dec.add (Dec.ofInt (Int.tmod w 60)) (Dec.sub d.seconds (Dec.ofInt w))

/-! ## §10.6 — duration arithmetic -/

/-- §10.6.1 `op:add-yearMonthDurations`. -/
def addYearMonth (a b : DurValue) : DurValue := yearMonth (a.months + b.months)

/-- §10.6.2 `op:subtract-yearMonthDurations`. -/
def subYearMonth (a b : DurValue) : DurValue := yearMonth (a.months - b.months)

/-- §10.6.5 `op:multiply-yearMonthDuration`: the month count times the
    number, ROUNDED to the nearest month by `fn:round` (half toward
    positive infinity). The Approved `Builtins_Time` fixture asserts
    `multiply-yearMonthDuration("P2Y11M" 2.3) = "P6Y9M"`, which is
    80.5 months rounding to 81. -/
def mulYearMonth (a : DurValue) (k : Dec) : DurValue :=
  yearMonth (Numeric.decRound (Numeric.decMul (Dec.ofInt a.months) k))

/-- §10.6.6 `op:divide-yearMonthDuration`. `none` when the divisor is
    zero. -/
def divYearMonth? (a : DurValue) (k : Dec) : Option DurValue :=
  (Numeric.decDiv? Numeric.divScale (Dec.ofInt a.months) k).map
    (fun q => yearMonth (Numeric.decRound q))

/-- §10.6.7 `op:divide-yearMonthDuration-by-yearMonthDuration`, an
    `xs:decimal`. -/
def divYearMonthBy? (a b : DurValue) : Option Dec :=
  Numeric.decDiv? Numeric.divScale (Dec.ofInt a.months) (Dec.ofInt b.months)

/-- §10.6.3 `op:add-dayTimeDurations`. -/
def addDayTime (a b : DurValue) : DurValue := dayTime (Dec.add a.seconds b.seconds)

/-- §10.6.4 `op:subtract-dayTimeDurations`. -/
def subDayTime (a b : DurValue) : DurValue := dayTime (Dec.sub a.seconds b.seconds)

/-- §10.6.8 `op:multiply-dayTimeDuration`. The seconds are an
    `xs:decimal`, so this is exact and there is nothing to round. -/
def mulDayTime (a : DurValue) (k : Dec) : DurValue :=
  dayTime (Numeric.decMul a.seconds k)

/-- §10.6.9 `op:divide-dayTimeDuration`. -/
def divDayTime? (a : DurValue) (k : Dec) : Option DurValue :=
  (Numeric.decDiv? Numeric.divScale a.seconds k).map dayTime

/-- §10.6.10 `op:divide-dayTimeDuration-by-dayTimeDuration`. -/
def divDayTimeBy? (a b : DurValue) : Option Dec :=
  Numeric.decDiv? Numeric.divScale a.seconds b.seconds

/-! ## §10.4.1-10.4.4 — comparison

XML Schema Part 2 §3.3.6.2 makes the general `xs:duration` order
PARTIAL (`P1M` and `P30D` are incomparable), and `XSD.durCompare`
implements it. Inside either sub-space the order is total, which is
why RIF-DTB 4.8.2 has `pred:yearMonthDuration-less-than` and
`pred:dayTimeDuration-less-than` but no `pred:duration-less-than`. -/

/-- §10.4.1 `op:duration-equal`: equal month counts AND equal second
    counts. Defined on the whole `xs:duration` value space, so
    `pred:duration-equal("P1Y" "P12M")` holds. -/
def equal (a b : DurValue) : Bool :=
  a.months == b.months && Dec.cmp a.seconds b.seconds == .eq

/-- §10.4.2 `op:yearMonthDuration-less-than`. -/
def yearMonthLessThan (a b : DurValue) : Bool := a.months < b.months

/-- §10.4.4 `op:dayTimeDuration-less-than`. -/
def dayTimeLessThan (a b : DurValue) : Bool := Dec.cmp a.seconds b.seconds == .lt

/-! ## Pins — every line of the Approved `Builtins_Time` fixture that
this module answers, plus the F&O examples the specification prints. -/

-- The fixture's own values, written as they parse.
private def p20y15m : DurValue := yearMonth 255
private def p3dt10h : DurValue := dayTime (Dec.ofInt (3 * 86400 + 10 * 3600))
private def negP5dt12h30m : DurValue := dayTime (Dec.ofInt (-(5 * 86400 + 12 * 3600 + 30 * 60)))
private def p3dt10h12p5s : DurValue :=
  dayTime (Dec.norm ⟨(3 * 86400 + 10 * 3600 + 12) * 10 + 5, 1⟩)

#guard yearsFrom p20y15m = 21
#guard monthsFrom p20y15m = 3
#guard daysFrom p3dt10h = 3
#guard hoursFrom p3dt10h = 10
#guard minutesFrom negP5dt12h30m = -30
#guard secondsFrom p3dt10h12p5s = ⟨125, 1⟩

-- §10.6, the fixture's arithmetic lines.
#guard addYearMonth (yearMonth 35) (yearMonth 39) = yearMonth 74      -- P2Y11M + P3Y3M = P6Y2M
#guard subYearMonth (yearMonth 35) (yearMonth 39) = yearMonth (-4)    -- = -P4M
#guard mulYearMonth (yearMonth 35) ⟨23, 1⟩ = yearMonth 81             -- ×2.3 = P6Y9M
#guard divYearMonth? (yearMonth 35) ⟨15, 1⟩ = some (yearMonth 23)     -- ÷1.5 = P1Y11M
#guard divYearMonthBy? (yearMonth 40) (yearMonth (-16)) = some ⟨-25, 1⟩
#guard addDayTime (dayTime (Dec.ofInt 216300)) (dayTime (Dec.ofInt 475200))
     = dayTime (Dec.ofInt 691500)                                     -- P2DT12H5M + P5DT12H = P8DT5M
#guard subDayTime (dayTime (Dec.ofInt 216000)) (dayTime (Dec.ofInt 124200))
     = dayTime (Dec.ofInt 91800)                                      -- P2DT12H - P1DT10H30M = P1DT1H30M
#guard mulDayTime (dayTime (Dec.ofInt 7800)) ⟨21, 1⟩ = dayTime (Dec.ofInt 16380)
#guard divDayTime? (dayTime (Dec.ofInt 345600)) (Dec.ofInt 2)
     = some (dayTime (Dec.ofInt 172800))
#guard divDayTimeBy? (dayTime (Dec.ofInt 345600)) (dayTime (Dec.ofInt 172800))
     = some (Dec.ofInt 2)
#guard divDayTime? (dayTime (Dec.ofInt 4)) (Dec.ofInt 0) = none

-- §10.4, the fixture's comparison lines.
#guard equal (yearMonth 12) (yearMonth 12) = true
#guard equal (yearMonth 12) (yearMonth 1) = false
#guard yearMonthLessThan (yearMonth 12) (yearMonth 13) = true
#guard dayTimeLessThan (dayTime (Dec.ofInt 86400)) (dayTime (Dec.ofInt 90000)) = true
#guard dayTimeLessThan (dayTime (Dec.ofInt 86400)) (dayTime (Dec.ofInt 82800)) = false

/-! ## Theorems -/

/-- The year and month accessors decompose the month count exactly: no
    month is lost or invented between `fn:years-from-duration` and
    `fn:months-from-duration`. This is what makes it safe for a front
    end to report the two separately. -/
theorem years_months_decompose (d : DurValue) :
    yearsFrom d * 12 + monthsFrom d = d.months := by
  exact Int.tdiv_mul_add_tmod d.months 12

/-- Adding then subtracting the same `xs:yearMonthDuration` returns the
    month count unchanged: the pair of §10.6.1 and §10.6.2 loses
    nothing. -/
theorem addYearMonth_subYearMonth (a b : DurValue) :
    subYearMonth (addYearMonth a b) b = yearMonth a.months := by
  simp [addYearMonth, subYearMonth, yearMonth]

/-- Negation is an involution. -/
theorem neg_neg (d : DurValue) : neg (neg d) = d := by
  cases d with
  | mk m s => cases s with
    | mk mant sc => simp [neg, Dec.neg]

/-- `Dec.normFuel` never turns a zero mantissa into a non-zero one. -/
theorem normFuel_zero_mantissa (n s : Nat) :
    (Dec.normFuel n ⟨0, s⟩).mantissa = 0 := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp [Dec.normFuel]; split <;> simp [ih]

/-- Subtracting a decimal from itself gives zero. The `Dec`
    representation is not unique — `⟨0, 3⟩` and `⟨0, 0⟩` are the same
    value — so the theorem is stated on the mantissa, which is what
    `Dec.cmp` reads through. -/
theorem sub_self_mantissa (a : Dec) : (Dec.sub a a).mantissa = 0 := by
  have h : a.mantissa * (10 : Int) ^ (max a.scale a.scale - a.scale)
         + -a.mantissa * (10 : Int) ^ (max a.scale a.scale - a.scale) = 0 := by
    simp; omega
  simp only [Dec.sub, Dec.neg, Dec.add, Dec.norm, h]
  exact normFuel_zero_mantissa _ _

/-- `op:duration-equal` is reflexive. -/
theorem equal_refl (d : DurValue) : equal d d = true := by
  simp [equal, Dec.cmp]

end L4Factoidal.Fn.Duration
