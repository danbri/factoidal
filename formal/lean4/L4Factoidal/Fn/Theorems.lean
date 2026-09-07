/-
L4Factoidal.Fn.Theorems — what the three front ends agree on, and
exactly where they do not.

RIF-DTB, SPARQL 1.1 §17 and XPath 1.0 §4 all reach XQuery and XPath
Functions and Operators, but they do not all reach the same version of
it and they do not share an error discipline. Two kinds of theorem
live here.

**Agreement.** The front end calls `L4Factoidal.Fn` and does not carry
its own copy. Each such theorem is `rfl`, and that is the point: it is
not a deep fact, it is a GUARD. If someone reintroduces a second
implementation of `fn:encode-for-uri` in `SPARQL/Expr.lean`, the
theorem stops type-checking and the build fails. A comment saying "do
not duplicate this" does not do that.

**Difference.** Two Recommendations define the same-named function
differently. The theorem names the input that separates them and
proves both sides, so the difference is a checked fact rather than a
sentence in a design document. Reconciling them would be WRONG: each
front end must answer what its own specification says.

The catalogue is `docs/designissues/2026-09-07-function-library.md` §4.
-/
import L4Factoidal.Fn.Casting
import L4Factoidal.RIF.Builtins
import L4Factoidal.SPARQL.Expr
import L4Factoidal.XPath.Eval

namespace L4Factoidal.Fn.Theorems

/-! ## Agreement: one implementation, three callers -/

/-- F&O §5.4.5 `fn:encode-for-uri`. RIF-DTB 4.7
    `func:encode-for-uri` and SPARQL 1.1 §17.4.3.15 `ENCODE_FOR_URI`
    cite it unchanged, and both now call it. -/
theorem encodeForUri_rif (s : String) :
    L4Factoidal.RIF.encodeForUri s = Fn.String.encodeForUri s := rfl

theorem encodeForUri_sparql (s : String) :
    L4Factoidal.SPARQL.strEncodeUri s = Fn.String.encodeForUri s := rfl

/-- F&O §5.4.2 and §5.4.3. RIF-DTB `func:substring-before` /
    `-after`, SPARQL `STRBEFORE` / `STRAFTER` and the XPath 1.0
    function table agree on these, including on the not-found case
    (the empty string) and on the empty-needle case. -/
theorem substringBefore_sparql (s arg : String) :
    L4Factoidal.SPARQL.strBeforeRaw s arg = Fn.String.substringBefore s arg := rfl

theorem substringAfter_sparql (s arg : String) :
    L4Factoidal.SPARQL.strAfterRaw s arg = Fn.String.substringAfter s arg := rfl

theorem substringIndex_xpath (hay needle : String) :
    L4Factoidal.XPath.Full.substrIndex hay needle = Fn.String.indexOfSub hay needle := rfl

/-- RFC 4647 §3.3.1 basic filtering. SPARQL 1.1 §17.4.3.10
    `langMatches` cites it. -/
theorem langMatches_sparql (tag range : String) :
    L4Factoidal.SPARQL.fnLangMatches tag range = Fn.String.langMatchesBasic tag range := rfl

/-- F&O §6.2. RIF-DTB 4.5's four arithmetic built-ins are these. -/
theorem addDec_rif (a b : String) :
    L4Factoidal.RIF.addDec a b = Fn.Numeric.addDec a b := rfl
theorem subDec_rif (a b : String) :
    L4Factoidal.RIF.subDec a b = Fn.Numeric.subDec a b := rfl
theorem mulDec_rif (a b : String) :
    L4Factoidal.RIF.mulDec a b = Fn.Numeric.mulDec a b := rfl
theorem divDec_rif (a b : String) :
    L4Factoidal.RIF.divDec a b = Fn.Numeric.divDec a b := rfl

/-- RIF-DTB 4.11's list functions. -/
theorem listIndex_rif (len : Nat) (i : Int) :
    L4Factoidal.RIF.listIndex len i = Fn.List.listIndex len i := rfl

/-! ## Difference: the same name, two specifications

Each theorem below names the input that separates two Recommendations
and proves what each of them answers on it. -/

/-- **`substring`, SPARQL against F&O.** F&O §5.4.4 keeps every
    position `p` with `start <= p < start + length`, so a start of 0
    with a length of 3 keeps positions 1 and 2 and loses the third
    character. SPARQL 1.1 §17.4.3.3 `SUBSTR` cites `fn:substring` but
    CLAMPS a start below 1 to 1 instead, so it keeps three characters.
    `"foobar"` with start 0 and length 3 is the witness. -/
theorem substring_sparql_differs_from_fando :
    L4Factoidal.SPARQL.substrSpec "foobar" 0 (some 3) = "foo"
    ∧ Fn.String.substringFromLen "foobar" 0 3 = "fo" := by
  constructor <;> rfl

/-- **`substring`, RIF's 2-argument form against F&O's.** The Approved
    `Builtins_String` fixture writes `substring("foobar" 3) = "bar"`,
    which counts from 0, while F&O §5.4.4 counts from 1 and answers
    `"obar"`. The disagreement is inside one fixture, which also writes
    a 1-based 3-argument line; the fixture is the authority for the RIF
    front end and F&O for the others. -/
theorem substring2_rif_differs_from_fando :
    Fn.String.substringFromRif "foobar" 3 = "bar"
    ∧ Fn.String.substringFrom "foobar" 3 = "obar" := by
  constructor <;> rfl

/-! **Language-range matching.** RIF-DTB 4.10.2
`pred:matches-language-range` is RFC 4647 §3.3.2 EXTENDED filtering;
SPARQL 1.1 §17.4.3.10 `langMatches` is §3.3.1 BASIC filtering. The tag
`de-Latn-DE` against the range `de-*-DE` separates them: extended
filtering matches the wildcard against `Latn`, basic filtering has no
wildcard inside a range at all.

This one is a `#guard` and not a theorem, and the reason is worth
naming rather than hiding: both functions call `String.toLower` and
`String.startsWith`, which are `@[extern]` primitives. The KERNEL
cannot reduce them, so `decide` gets stuck and `rfl` fails; the
compiler evaluates them, which is what `#guard` uses. `native_decide`
would close the gap by trusting the compiler inside the kernel, and
this repository does not allow it. Every check below is in the same
position and for the same reason. -/
#guard Fn.String.matchesLanguageRange "de-Latn-DE" "de-*-DE" = true
#guard Fn.String.langMatchesBasic "de-Latn-DE" "de-*-DE" = false

/-- **`concat` arity.** `fn:concat` and SPARQL `CONCAT` are variadic
    over the whole argument list, including the empty one; XPath 1.0
    §4.2 `concat()` requires at least two arguments. The library takes
    a list, so the arity rule belongs to the front end and the empty
    case is well defined here. -/
theorem concat_nil : Fn.String.concat [] = "" := rfl

/-- **Error against no value.** F&O raises the dynamic error
    `FOAR0001` on a zero divisor; RIF-DTB leaves the built-in with no
    value, which `RIF/Builtins.lean` reports as `unknown` so the rule
    does not fire; SPARQL §17.2 makes the expression an error that a
    FILTER reads as `false`. The library returns `none` and each front
    end maps it. -/
theorem divide_by_zero_has_no_value (a : L4Factoidal.XSD.Dec) :
    Fn.Numeric.decDiv? 18 a ⟨0, 0⟩ = none := rfl

#guard L4Factoidal.RIF.evalFunc "numeric-divide"
      [L4Factoidal.RIF.gLit "1" (L4Factoidal.RIF.xsdNs ++ "integer"),
       L4Factoidal.RIF.gLit "0" (L4Factoidal.RIF.xsdNs ++ "integer")] = none

/-! ## The RIF-DTB 4.8 signature layer

These are not agreements between front ends — only RIF-DTB has these
built-ins today. They pin the two fixture accommodations that
`RIF/Builtins.lean` makes, so a later change cannot remove them
silently. -/

-- RIF-DTB 3.2 puts the `xs:date` values inside the `xs:dateTime`
-- value space at midnight, one way only.
#guard L4Factoidal.RIF.evalPred "is-literal-dateTime"
      [L4Factoidal.RIF.gLit "2008-07-22Z" (L4Factoidal.RIF.xsdNs ++ "date")] = .yes

#guard L4Factoidal.RIF.evalPred "is-literal-date"
      [L4Factoidal.RIF.gLit "2008-07-22T12:00:00Z" (L4Factoidal.RIF.xsdNs ++ "dateTime")]
    = .no

/-- `xs:dateTimeStamp` is `xs:dateTime` with the timezone required
    (XSD 1.1 §3.4.28), which is a condition on the VALUE. -/
theorem dateTimeStamp_requires_a_timezone :
    Fn.Casting.inTemporalLexicalSpace "dateTimeStamp" "2000-12-13T00:11:11.3" = some false
    ∧ Fn.Casting.inTemporalLexicalSpace "dateTime" "2000-12-13T00:11:11.3" = some true := by
  constructor <;> rfl

end L4Factoidal.Fn.Theorems
