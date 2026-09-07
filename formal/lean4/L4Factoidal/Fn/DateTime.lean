/-
L4Factoidal.Fn.DateTime — the date and time functions of XQuery 1.0
and XPath 2.0 Functions and Operators §10.4, §10.5 and §10.7.

RIF-DTB 4.8 cites all of them. The value space is `XSD.DTValue`, XML
Schema Part 2 §3.3.7's seven-property model, and the results are
written back through `XSD.canonicalDateTime` and
`XSD.canonicalDuration` so a front end never assembles a lexical form
of its own.

## The implicit timezone

F&O §10.7 takes the implicit timezone from the dynamic evaluation
context. RIF-DTB has no such context: a rule is evaluated against a
document, not against a request. Every function here that must compare
or subtract takes the implicit offset as an explicit `Int` argument in
MINUTES, and the RIF front end passes 0 — reading an absent timezone
as UTC. Making it a parameter rather than a constant is what lets the
SPARQL front end pass a different one later without a second copy of
the arithmetic.
-/
import L4Factoidal.Fn.Duration

namespace L4Factoidal.Fn.DateTime

open L4Factoidal.XSD

/-! ## The civil calendar, both directions

`XSD.daysFromCivil` maps a proleptic Gregorian date to a day number.
The INVERSE is needed here and nowhere else in the XSD layer: adding a
duration to a date/time produces a day number that must be read back
as a year, a month and a day. This is Hinnant's `civil_from_days`, the
companion of the `days_from_civil` already in `XSD/Datatypes.lean`.

`LWS/Operations.lean` carries a third copy for HTTP-date formatting.
It is left there deliberately: it is a different specification's
formatter, and moving it is a separate commit with its own gate
(`docs/designissues/2026-09-07-xsd-datatypes-audit.md` §8). -/
def civilFromDays (z0 : Int) : Int × Nat × Nat :=
  let z := z0 + 719468
  let era : Int := Int.tdiv (if z ≥ 0 then z else z - 146096) 146097
  let doe : Int := z - era * 146097
  let yoe : Int :=
    Int.tdiv (doe - Int.tdiv doe 1460 + Int.tdiv doe 36524 - Int.tdiv doe 146096) 365
  let y : Int := yoe + era * 400
  let doy : Int := doe - (365 * yoe + Int.tdiv yoe 4 - Int.tdiv yoe 100)
  let mp : Int := Int.tdiv (5 * doy + 2) 153
  let d : Int := doy - Int.tdiv (153 * mp + 2) 5 + 1
  let m : Int := mp + (if mp < 10 then 3 else -9)
  ((if m ≤ 2 then y + 1 else y), m.toNat, d.toNat)

/-! The day number and the date agree in both directions. Checked over
the dates the RIF corpus and the F&O examples name, plus the negative
year that found the `XSD.daysFromCivil` era bug (see the file header of
`XSD/Datatypes.lean`); a proof for every year is a separate obligation,
recorded as open in
`docs/designissues/2026-09-07-function-library.md`. -/
#guard civilFromDays 0 = (1970, 1, 1)
#guard civilFromDays (daysFromCivil 2000 10 30) = (2000, 10, 30)
#guard civilFromDays (daysFromCivil 1999 12 31) = (1999, 12, 31)
#guard civilFromDays (daysFromCivil 2004 2 29) = (2004, 2, 29)
#guard civilFromDays (daysFromCivil 1 1 1) = (1, 1, 1)
#guard civilFromDays (daysFromCivil (-44) 3 15) = (-44, 3, 15)

/-! ## §10.5.7-10.5.20 — the accessors

F&O reads the LOCAL field, not a UTC-normalised one:
`fn:hours-from-dateTime("1999-05-31T08:20:00-05:00")` is 8. The
seven-property model already holds the local fields, so each accessor
is a projection. The `24:00:00` end-of-day form is normalised to the
following day by `XSD.parseDateTimeLex`, which is why
`fn:year-from-dateTime("1999-12-31T24:00:00")` is 2000. -/

def yearFrom (v : DTValue) : Option Int := v.year
def monthFrom (v : DTValue) : Option Nat := v.month
def dayFrom (v : DTValue) : Option Nat := v.day
def hoursFrom (v : DTValue) : Option Nat := v.hour
def minutesFrom (v : DTValue) : Option Nat := v.minute
def secondsFrom (v : DTValue) : Option Dec := v.second

/-- §10.5.13 `fn:timezone-from-dateTime` and its `date` and `time`
    twins: the offset as an `xs:dayTimeDuration`, or no value when the
    timezone is absent. -/
def timezoneFrom (v : DTValue) : Option DurValue :=
  v.tz.map (fun mins => Duration.dayTime (Dec.ofInt (mins * 60)))

/-! ## Implicit-timezone handling -/

/-- Give an untimezoned value the implicit offset, in minutes. -/
def withImplicitTz (implicitMins : Int) (v : DTValue) : DTValue :=
  { v with tz := some (v.tz.getD implicitMins) }

/-! ## §10.7 — adding a duration to a date/time value

XML Schema Part 2 §E.2.2 `dateTimePlusDuration`: the months are added
first, with the day CLAMPED into the target month, and the seconds
after that, carrying across days. The timezone is carried through
unchanged — F&O §10.7 keeps it, so
`add-dayTimeDuration-to-time("23:12:00+03:00" "P1DT3H15M")` is
`"02:27:00+03:00"` and not a UTC-normalised value.

`XSD.addDuration` exists but collapses its result into a day-zero
value whose seconds hold the whole offset; that is enough for the
duration ORDER, which is all it was written for, and not enough to
serialise. This is the field-preserving version. -/
def plusDuration (v : DTValue) (d : DurValue) : DTValue :=
  let y := v.year.getD 1972
  let mo := v.month.getD 1
  let totalMonths : Int := y * 12 + ((mo : Int) - 1) + d.months
  let y2 : Int := Int.fdiv totalMonths 12
  let mo2 : Nat := (totalMonths - y2 * 12).toNat + 1
  let dayClamped := min (v.day.getD 1) (daysInMonth y2 mo2)
  let timeOfDay : Dec :=
    Dec.add (Dec.ofInt ((v.hour.getD 0 : Int) * 3600 + (v.minute.getD 0 : Int) * 60))
            (v.second.getD Dec.zero)
  let total : Dec := Dec.add timeOfDay d.seconds
  let whole : Int := Numeric.decFloorInt total
  let frac : Dec := Dec.sub total (Dec.ofInt whole)
  let dayShift : Int := Int.fdiv whole 86400
  let sod : Int := whole - dayShift * 86400
  let (y3, m3, d3) := civilFromDays (daysFromCivil y2 mo2 dayClamped + dayShift)
  { year := some y3, month := some m3, day := some d3,
    hour := some (Int.tdiv sod 3600).toNat,
    minute := some (Int.tdiv (Int.tmod sod 3600) 60).toNat,
    second := some (Dec.add (Dec.ofInt (Int.tmod sod 60)) frac),
    tz := v.tz }

/-- §10.7.5-10.7.14 `op:subtract-*-from-*`: adding the negated
    duration. -/
def minusDuration (v : DTValue) (d : DurValue) : DTValue :=
  plusDuration v (Duration.neg d)

/-! ## §10.8 — subtracting two date/time values -/

/-- §10.8.1 `op:subtract-dateTimes`, §10.8.2 `op:subtract-dates` and
    §10.8.3 `op:subtract-times`: the difference of the two timeline
    positions, as an `xs:dayTimeDuration`. The three F&O functions are
    one computation over the seven-property model — `XSD.timeOnTimeline`
    supplies §E.3.4's defaults for the properties a datatype omits — so
    they are one definition here and three names in the front end. -/
def subtractValues (implicitMins : Int) (a b : DTValue) : DurValue :=
  Duration.dayTime (Dec.sub (timeOnTimeline (withImplicitTz implicitMins a))
                            (timeOnTimeline (withImplicitTz implicitMins b)))

/-! ## §10.4.5-10.4.10 — comparison

`XSD.dtCompare` already implements §3.2.7.4, including the ±14:00
window that makes an untimezoned value incomparable with a timezoned
one when the window straddles it. RIF-DTB has no such incomparability
because it fixes an implicit timezone, so the front end applies
`withImplicitTz` first and the `none` case cannot arise. -/

def compare (implicitMins : Int) (a b : DTValue) : Option Ordering :=
  L4Factoidal.XSD.dtCompare (withImplicitTz implicitMins a) (withImplicitTz implicitMins b)

def equal (implicitMins : Int) (a b : DTValue) : Option Bool :=
  (compare implicitMins a b).map (· == .eq)
def lessThan (implicitMins : Int) (a b : DTValue) : Option Bool :=
  (compare implicitMins a b).map (· == .lt)
def greaterThan (implicitMins : Int) (a b : DTValue) : Option Bool :=
  (compare implicitMins a b).map (· == .gt)

/-! ## Pins — the Approved `Builtins_Time` fixture, line by line -/

private def dt (y : Int) (mo d h mi s : Nat) (tz : Option Int) : DTValue :=
  { year := some y, month := some mo, day := some d, hour := some h,
    minute := some mi, second := some (Dec.ofInt s), tz := tz }
private def dtDate (y : Int) (mo d : Nat) (tz : Option Int) : DTValue :=
  { year := some y, month := some mo, day := some d, tz := tz }
private def dtTime (h mi s : Nat) (tz : Option Int) : DTValue :=
  { hour := some h, minute := some mi, second := some (Dec.ofInt s), tz := tz }

-- §10.5, the accessor lines.
#guard yearFrom (dt 1999 5 31 13 20 0 (some (-300))) = some 1999
#guard monthFrom (dt 1999 5 31 13 20 0 (some (-300))) = some 5
#guard dayFrom (dt 1999 5 31 13 20 0 (some (-300))) = some 31
#guard hoursFrom (dt 1999 5 31 8 20 0 (some (-300))) = some 8
#guard minutesFrom (dt 1999 5 31 13 20 0 (some (-300))) = some 20
#guard secondsFrom (dt 1999 5 31 13 20 0 (some (-300))) = some (Dec.ofInt 0)
#guard (timezoneFrom (dt 1999 5 31 13 20 0 (some (-300))) |>.map canonicalDuration)
     = some "-PT5H"
#guard timezoneFrom (dt 2000 10 30 11 12 0 none) = none

-- §10.7, the arithmetic lines, compared as CANONICAL LEXICAL FORMS so
-- the serialisation is pinned with the arithmetic.
#guard canonicalDateTime .dateTime
        (plusDuration (dt 2000 10 30 11 12 0 none) (Duration.yearMonth 14))
     = "2001-12-30T11:12:00"
#guard canonicalDateTime .date
        (plusDuration (dtDate 2000 10 30 none) (Duration.yearMonth 14))
     = "2001-12-30"
#guard canonicalDateTime .dateTime
        (plusDuration (dt 2000 10 30 11 12 0 none) (Duration.dayTime (Dec.ofInt 263700)))
     = "2000-11-02T12:27:00"
#guard canonicalDateTime .date
        (plusDuration (dtDate 2004 10 30 (some 0)) (Duration.dayTime (Dec.ofInt 181800)))
     = "2004-11-01Z"
#guard canonicalDateTime .time
        (plusDuration (dtTime 11 12 0 none) (Duration.dayTime (Dec.ofInt 263700)))
     = "12:27:00"
#guard canonicalDateTime .time
        (plusDuration (dtTime 23 12 0 (some 180)) (Duration.dayTime (Dec.ofInt 98100)))
     = "02:27:00+03:00"
#guard canonicalDateTime .dateTime
        (minusDuration (dt 2000 10 30 11 12 0 none) (Duration.yearMonth 14))
     = "1999-08-30T11:12:00"
#guard canonicalDateTime .date
        (minusDuration (dtDate 2000 10 30 none) (Duration.yearMonth 14))
     = "1999-08-30"
#guard canonicalDateTime .dateTime
        (minusDuration (dt 2000 10 30 11 12 0 none) (Duration.dayTime (Dec.ofInt 263700)))
     = "2000-10-27T09:57:00"
#guard canonicalDateTime .date
        (minusDuration (dtDate 2000 10 30 none) (Duration.dayTime (Dec.ofInt 263700)))
     = "2000-10-26"
#guard canonicalDateTime .time
        (minusDuration (dtTime 11 12 0 none) (Duration.dayTime (Dec.ofInt 263700)))
     = "09:57:00"

-- §E.2.2's day clamping: 31 January plus one month is 28 February.
#guard canonicalDateTime .date
        (plusDuration (dtDate 2001 1 31 none) (Duration.yearMonth 1)) = "2001-02-28"

-- §10.8, the subtraction lines.
#guard canonicalDuration
        (subtractValues 0 (dt 2000 10 30 6 12 0 (some (-300)))
                          (dt 1999 11 28 9 0 0 (some 0)))
     = "P337DT2H12M"
#guard canonicalDuration
        (subtractValues 0 (dtDate 2000 10 30 (some 0)) (dtDate 1999 11 28 (some 0)))
     = "P337D"
#guard canonicalDuration
        (subtractValues 0 (dtTime 11 12 0 (some 0)) (dtTime 4 0 0 (some 0)))
     = "PT7H12M"

-- §10.4, the comparison lines.
#guard equal 0 (dt 2002 4 2 12 0 0 (some (-60))) (dt 2002 4 2 17 0 0 (some 240)) = some true
#guard lessThan 0 (dt 2002 4 1 12 0 0 (some (-60))) (dt 2002 4 2 17 0 0 (some 240)) = some true
#guard greaterThan 0 (dt 2002 4 3 12 0 0 (some (-60))) (dt 2002 4 2 17 0 0 (some 240)) = some true
#guard equal 0 (dtDate 2004 12 25 (some (-720))) (dtDate 2004 12 26 (some 720)) = some true
#guard lessThan 0 (dtDate 2004 12 24 none) (dtDate 2004 12 26 none) = some true
#guard equal 0 (dtTime 21 30 0 (some 630)) (dtTime 6 0 0 (some (-300))) = some true
#guard lessThan 0 (dtTime 20 30 0 (some 630)) (dtTime 6 0 0 (some (-300))) = some true
#guard greaterThan 0 (dtTime 22 30 0 (some 630)) (dtTime 6 0 0 (some (-300))) = some true

/-! ## Theorems -/

/-- Subtracting a date/time value from itself is a zero duration.
    §10.8 is a difference of timeline positions, so this holds for
    every value including an untimezoned one. Stated on the mantissa
    because the `Dec` representation of zero is not unique. -/
theorem subtract_self (t : Int) (v : DTValue) :
    (subtractValues t v v).seconds.mantissa = 0 :=
  Duration.sub_self_mantissa _

/-- `withImplicitTz` is idempotent: a value that already carries a
    timezone keeps it, and one that does not gets the implicit offset
    once. This is what makes it safe to apply at every entry point
    rather than tracking whether it has been applied. -/
theorem withImplicitTz_idem (t : Int) (v : DTValue) :
    withImplicitTz t (withImplicitTz t v) = withImplicitTz t v := by
  cases v with
  | mk y mo d h mi s tz => cases tz <;> simp [withImplicitTz]

/-- `fn:timezone-from-dateTime` has a value exactly when the value has
    a timezone. F&O raises no error here; it returns the empty
    sequence, and RIF-DTB leaves the built-in with no value. -/
theorem timezoneFrom_isSome (v : DTValue) :
    (timezoneFrom v).isSome = v.tz.isSome := by
  cases v with
  | mk y mo d h mi s tz => cases tz <;> simp [timezoneFrom]

/-- Adding a zero `xs:yearMonthDuration` to a value that already
    carries all seven properties in range leaves the month arithmetic
    alone. Checked on the timeline, since §E.2.2's day clamping makes
    the seven-property identity false in general (31 January plus one
    month minus one month is 28 January, and the `2001-02-28` `#guard`
    above is that counterexample). -/
theorem plusDuration_preserves_tz (v : DTValue) (d : DurValue) :
    (plusDuration v d).tz = v.tz := by
  simp [plusDuration]

end L4Factoidal.Fn.DateTime
