/-
L4Factoidal.Fn.Casting — reading a lexical form as a value of a named
datatype: XQuery 1.0 and XPath 2.0 Functions and Operators §17, and
RIF-DTB 4.4's constructor functions.

RIF-DTB 4.4.1 gives a constructor `xs:T(...)` for each of 33 XML
Schema datatypes; RIF-DTB 4.2 gives a guard `pred:is-literal-T` for 35
of them. Both ask the same question — is this lexical form in the
value space of `T`? — and XML Schema Part 2 answers it. The answer
belongs in `XSD/Datatypes.lean`, and this module is the part of the
route that RIF, SPARQL and XPath share.

Scope, stated so the gap is visible: the date/time and duration
lexical spaces route through `XSD.parseDateTimeLex` and
`XSD.parseDurationLex` here. The NUMERIC lexical spaces still go
through `CSVW.isXsdNumericLexical` at the RIF call site. Moving them
is commit 7 of the plan in
`docs/designissues/2026-09-07-xsd-datatypes-audit.md` §8; it changes
ACCEPTANCE, not values, and its gate is the SPARQL suites rather than
the RIF corpus, so it is a separate commit with a separate measurement.
-/
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.Fn.Casting

open L4Factoidal.XSD

/-- The `DTKind` a datatype local name denotes. `xs:dateTimeStamp`
    (XSD 1.1 §3.4.28) is an `xs:dateTime` whose timezone is REQUIRED —
    a condition on the value, not a different seven-property kind. -/
def dtKindOfBase (b : String) : Option DTKind :=
  if b == "dateTime" || b == "dateTimeStamp" then some .dateTime
  else if b == "date" then some .date
  else if b == "time" then some .time
  else none

/-- Is `lex` in the lexical space of the date/time datatype `b`?
    `none` when `b` is not one of them. -/
def inDateTimeLexicalSpace (b lex : String) : Option Bool :=
  if b == "dateTimeStamp" then
    some (match parseDateTimeLex .dateTime lex with
          | some v => v.tz.isSome
          | none   => false)
  else
    (dtKindOfBase b).map (fun k => (parseDateTimeLex k lex).isSome)

/-- Is `lex` in the lexical space of the duration datatype `b`?
    `none` when `b` is not one of them. XSD §3.4.27 and §3.4.28 make
    `xs:yearMonthDuration` and `xs:dayTimeDuration` restrictions of
    `xs:duration` by PATTERN, so each has its own lexical space and
    `P1Y2DT3H` is in none of the two. -/
def inDurationLexicalSpace (b lex : String) : Option Bool :=
  if b == "duration" then some (parseDurationLex lex).isSome
  else if b == "dayTimeDuration" then some (parseDayTimeDurationLex lex).isSome
  else if b == "yearMonthDuration" then some (parseYearMonthDurationLex lex).isSome
  else none

/-- The two together, which is the whole of the RIF-DTB 4.8 datatype
    slice. -/
def inTemporalLexicalSpace (b lex : String) : Option Bool :=
  match inDateTimeLexicalSpace b lex with
  | some r => some r
  | none   => inDurationLexicalSpace b lex

/-! ## Pins — the `Builtins_Time` guard and cast lines -/

#guard inTemporalLexicalSpace "date" "2000-12-13-11:00" = some true
#guard inTemporalLexicalSpace "dateTime" "2000-12-13T00:11:11.3" = some true
#guard inTemporalLexicalSpace "dateTimeStamp" "2000-12-13T00:11:11.3Z" = some true
#guard inTemporalLexicalSpace "dateTimeStamp" "2000-12-13T00:11:11.3" = some false
#guard inTemporalLexicalSpace "time" "00:11:11.3Z" = some true
#guard inTemporalLexicalSpace "dayTimeDuration" "P3DT2H" = some true
#guard inTemporalLexicalSpace "yearMonthDuration" "P1Y2M" = some true
#guard inTemporalLexicalSpace "date" "foo" = some false
#guard inTemporalLexicalSpace "time" "foo" = some false
#guard inTemporalLexicalSpace "dayTimeDuration" "foo" = some false
#guard inTemporalLexicalSpace "string" "foo" = none
-- §3.4.27/§3.4.28: the sub-spaces are disjoint from each other's forms.
#guard inTemporalLexicalSpace "dayTimeDuration" "P1Y" = some false
#guard inTemporalLexicalSpace "yearMonthDuration" "P1D" = some false
#guard inTemporalLexicalSpace "duration" "P1Y2M3DT4H" = some true

end L4Factoidal.Fn.Casting
