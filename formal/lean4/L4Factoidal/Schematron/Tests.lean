/-
L4Factoidal.Schematron.Tests — build-time checks, with the
assert/report inversion pinned in both directions.
-/
import L4Factoidal.Schematron.Validate

namespace L4Factoidal.Schematron

private def assertA : Assertion := { isAssert := true,  test := "T", message := "must hold" }
private def reportA : Assertion := { isAssert := false, test := "T", message := "found it" }

-- THE INVERSION. An `assert` fires when the test is FALSE; a
-- `report` fires when it is TRUE. Both directions pinned, because
-- getting either backwards produces a validator that is confidently
-- wrong rather than broken.
#guard (applyAssertion assertA "c" "p" .false').isSome
#guard (applyAssertion assertA "c" "p" .true').isNone
#guard (applyAssertion reportA "c" "p" .true').isSome
#guard (applyAssertion reportA "c" "p" .false').isNone

-- The two findings are DIFFERENT kinds, not one negated.
#guard match applyAssertion assertA "c" "p" .false' with
       | some f => f.kind == "assert-fail"
       | none   => false
#guard match applyAssertion reportA "c" "p" .true' with
       | some f => f.kind == "report-hit"
       | none   => false

-- An undecidable test yields an INDETERMINATE finding carrying its
-- reason, for BOTH assert and report — never a silent pass.
#guard match applyAssertion assertA "c" "p" (.undecided "no xpath engine") with
       | some f => f.kind == "indeterminate"
       | none   => false
#guard (applyAssertion reportA "c" "p" (.undecided "why")).isSome

-- Indeterminate is not a violation, and is reported separately so a
-- caller cannot read "could not decide" as "fine".
private def indet : List Finding := [.indeterminate "c" "t" "m" "p" "r"]
#guard !(hasViolations indet)
#guard hasIndeterminate indet
#guard hasViolations [.assertFail "c" "t" "m" "p"]
#guard !(hasIndeterminate [.assertFail "c" "t" "m" "p"])

-- Within a PATTERN the FIRST matching rule claims a node; later
-- rules in the same pattern do not fire for it. Getting this wrong
-- produces duplicate findings that look like extra violations.
private def alwaysTrue (_ _ : String) : Bool := true
private def alwaysFalseTest (_ _ : String) : TestResult := .false'
private def twoRules : Schema :=
  { patterns := [{ id := "p1", rules :=
      [ { context := "//a", assertions := [assertA] },
        { context := "//a", assertions := [assertA] } ] }] }
#guard (validate twoRules ["n1"] alwaysTrue alwaysFalseTest).length == 1

-- Patterns are INDEPENDENT: the same node is claimed afresh in each.
private def twoPatterns : Schema :=
  { patterns := [ { id := "p1", rules := [{ context := "//a", assertions := [assertA] }] },
                  { id := "p2", rules := [{ context := "//a", assertions := [assertA] }] } ] }
#guard (validate twoPatterns ["n1"] alwaysTrue alwaysFalseTest).length == 2

-- A passing assert produces nothing at all.
private def alwaysTrueTest (_ _ : String) : TestResult := .true'
#guard (validate twoRules ["n1"] alwaysTrue alwaysTrueTest).isEmpty

-- Finding accessors round-trip their fields.
#guard (Finding.assertFail "ctx" "tst" "msg" "pth").context == "ctx"
#guard (Finding.assertFail "ctx" "tst" "msg" "pth").test == "tst"
#guard (Finding.assertFail "ctx" "tst" "msg" "pth").message == "msg"
#guard (Finding.assertFail "ctx" "tst" "msg" "pth").path == "pth"

end L4Factoidal.Schematron
