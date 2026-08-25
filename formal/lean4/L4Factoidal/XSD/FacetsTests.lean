/-
L4Factoidal.XSD.FacetsTests — build-time checks for the datatype
value spaces.

The checks that matter here are the WITHHOLDING ones. An empty value
space is a CLASH, which refutes a whole ontology, so a value may be
dropped only on a proof that it is outside. Every `#guard` below that
asserts a set is NOT empty, or that two terms are neither provably
equal nor provably distinct, is that rule being pinned.
-/
import L4Factoidal.XSD.Facets

namespace L4Factoidal.XSD

open L4Factoidal.RDF

private def lit (v : String) (dt : WfIri) (h : literalWf
    { lexicalForm := v, datatype := dt, langTag := none, direction := none }) : Term :=
  .literal ⟨{ lexicalForm := v, datatype := dt, langTag := none, direction := none }, h⟩

private def intL (v : String) : Term :=
  lit v xsdInteger (by simp [literalWf, xsdInteger, rdfLangString, rdfDirLangString,
                            Subtype.ext_iff])
private def decL (v : String) : Term :=
  lit v xsdDecimal (by simp [literalWf, xsdDecimal, rdfLangString, rdfDirLangString,
                            Subtype.ext_iff])
private def ratL (v : String) : Term :=
  lit v owlRational (by simp [literalWf, owlRational, rdfLangString, rdfDirLangString,
                             Subtype.ext_iff])
private def strL (v : String) : Term :=
  lit v xsdString (by simp [literalWf, xsdString, rdfLangString, rdfDirLangString,
                           Subtype.ext_iff])
private def byteL (v : String) : Term :=
  lit v xsdByte (by simp [literalWf, xsdByte, rdfLangString, rdfDirLangString,
                         Subtype.ext_iff])
private def fltL (v : String) : Term :=
  lit v xsdFloat (by simp [literalWf, xsdFloat, rdfLangString, rdfDirLangString,
                          Subtype.ext_iff])
private def dtL (v : String) : Term :=
  lit v xsdDateTime (by simp [literalWf, xsdDateTime, rdfLangString, rdfDirLangString,
                             Subtype.ext_iff])

/-! ## Integer lexical forms -/

#guard parseFacetInt "42" == some 42
#guard parseFacetInt "-7" == some (-7)
#guard parseFacetInt "+7" == some 7
#guard parseFacetInt "" == none
#guard parseFacetInt "4x" == none

/-! ## Exact rationals

`"0.5"^^xsd:decimal` and `"1/2"^^owl:rational` denote the SAME real.
A reasoner that could not prove it would count a two-member
enumeration as two values, and a `≥ 2` cardinality over it would go
unrefuted. -/

#guard (parseDecimalRat "0.5").isSome
#guard (match parseDecimalRat "0.5", parseRationalLex "1/2" with
        | some a, some b => ratEq a b
        | _,      _      => false)
#guard (match parseDecimalRat "1.50", parseDecimalRat "1.5" with
        | some a, some b => ratEq a b
        | _,      _      => false)
#guard (match parseDecimalRat "1.5e1", parseDecimalRat "15" with
        | some a, some b => ratEq a b
        | _,      _      => false)
#guard parseDecimalRat "1.2.3" == none
#guard parseDecimalRat "1e" == none

#guard termProvablyEqual (decL "0.5") (ratL "1/2")
#guard termProvablyEqual (intL "3") (byteL "3")

/-! A decimal and an integer that DO denote one value must not be
called distinct. Calling them distinct would let a `≤ 1` bound refute
a satisfiable graph. -/
#guard !(termProvablyDistinct (decL "3.0") (intL "3"))
#guard termProvablyEqual (decL "3.0") (intL "3")

/-! Different families ARE provably distinct: the numeric, string and
boolean value spaces are pairwise disjoint. -/
#guard termProvablyDistinct (intL "3") (strL "3")
#guard termProvablyDistinct (intL "3") (intL "4")
#guard !(termProvablyDistinct (intL "3") (intL "3"))

/-! ## Integer intervals

Discrete: an open interval between ADJACENT integers is empty. -/

#guard intervalEmpty { lo := .excl 1, hi := .excl 2 }
#guard !(intervalEmpty { lo := .excl 1, hi := .excl 3 })
#guard intervalEmpty { lo := .incl 5, hi := .incl 4 }
#guard !(intervalEmpty { lo := .incl 4, hi := .incl 4 })
/-! An interval unbounded on either side is never reported empty:
absence of a proof is not a proof of absence. -/
#guard !(intervalEmpty { lo := .incl 5 })
#guard !(intervalEmpty {})

/-! Dense: adjacency does NOT empty the interval. Between any two
distinct reals lies a third. -/
#guard !(intervalEmptyDense { lo := .excl 1, hi := .excl 2 })
#guard intervalEmptyDense { lo := .excl 1, hi := .excl 1 }

#guard baseIntervalFor xsdByte == { lo := .incl (-128), hi := .incl 127 }
#guard intervalCount (baseIntervalFor xsdByte) == some 256
#guard intervalCount (baseIntervalFor xsdUnsignedByte) == some 256
/-! `xsd:integer` gets NO finite bound. Inventing one would be
unsound narrowing. -/
#guard intervalCount (baseIntervalFor xsdInteger) == none

/-! ## The `xsd:byte` ∩ `xsd:unsignedInt` window

`WebOnt-I5.8-003` asserts a property with BOTH ranges and a
cardinality of 129. The window is `[0, 127]`, which holds 128
values. -/
#guard intervalCount (intervalIntersect (baseIntervalFor xsdByte)
                                        (baseIntervalFor xsdUnsignedInt)) == some 128

/-! ## Value-space size, and the direction that keeps it sound

The answer must be at least the true count, so `k > M` implies `k`
values cannot be drawn. A dense space answers `none`, which makes
every cardinality rule inert there — right, because a
min-cardinality on `xsd:decimal` IS satisfiable. -/

#guard valueSetMaxSize (.interval (baseIntervalFor xsdByte)) == some 256
#guard valueSetMaxSize (.dense fullQInterval) == none
#guard valueSetMaxSize .unconstrained == none
#guard valueSetMaxSize (.family .string) == none

/-! An enumeration collapses only PROVABLY equal members, so the
count can be too high but never too low. Two spellings of one half
count as ONE. -/
#guard valueSetMaxSize (.enum [decL "0.5", ratL "1/2"]) == some 1
#guard valueSetMaxSize (.enum [intL "1", intL "2"]) == some 2

/-! ## Intersections -/

#guard valueSetIsEmpty (valueSetIntersect (.family .string) (.family .numeric))
#guard !(valueSetIsEmpty (valueSetIntersect (.family .string) (.family .string)))
#guard valueSetIsEmpty (valueSetIntersect (.interval { lo := .incl 5, hi := .incl 9 })
                                          (.interval { lo := .incl 1, hi := .incl 3 }))
/-! The `owl:real` line is disjoint from `xsd:dateTime` and from the
two floating-point grids. -/
#guard valueSetIsEmpty (valueSetIntersect (.dense fullQInterval) (.dateInterval fullInterval))
#guard valueSetIsEmpty (valueSetIntersect (.dense fullQInterval) (.family .float))
#guard valueSetIsEmpty (valueSetIntersect (.dense fullQInterval) (.family .double))
#guard !(valueSetIsEmpty (valueSetIntersect (.dense fullQInterval) (.family .numeric)))

/-! A decimal is KEPT in an integer interval: its value might lie
inside. Dropping it would manufacture emptiness. -/
#guard !(provablyOutsideInterval { lo := .incl 4, hi := .incl 10 } (decL "5.0"))
#guard provablyOutsideInterval { lo := .incl 4, hi := .incl 10 } (intL "11")
#guard provablyOutsideInterval { lo := .incl 4, hi := .incl 10 } (strL "5")

/-! ## `-INF` is not a real number

OWL 2 Syntax §4.1 puts the `xsd:float` value space outside
`owl:real`, so a `DataOneOf` member typed `xsd:float` is not
admissible under an `owl:real` constraint. That is the whole content
of "Minus Infinity is not in owl:real". -/

#guard termFloatSpecial (fltL "-INF") == some .negInf
#guard termInOwlReal (fltL "-INF") == some false
#guard termInOwlReal (intL "0") == some true
#guard termInOwlReal (strL "x") == some false

#guard valueSetIsEmpty
  (valueSetIntersect (.dense fullQInterval) (.enum [fltL "-INF"]))
/-! With a real in the enumeration it survives. -/
#guard !(valueSetIsEmpty
  (valueSetIntersect (.dense fullQInterval) (.enum [fltL "-INF", intL "0"])))

/-! ## The float grid is DISCRETE

`(0, 2^-149)` holds no float: `2^-149` is the smallest positive
subnormal, ordinal 1, and `0.0` is ordinal 0. The same open interval
over the reals is not empty, which is why the two value spaces cannot
share one representation. -/

#guard floatOrdinalOfLexical "0.0" == some 0
#guard floatOrdinalOfLexical "1.4E-45" == some 1
/-! A normal float is outside the band this places, and answers
`none` — which WIDENS the interval and withholds the verdict. -/
#guard floatOrdinalOfLexical "1.0" == none
#guard floatOrdinalOfLexical "-1.0" == none

/-! ## `xsd:dateTime`

A value WITHOUT a timezone gets no key: its instant is only partially
ordered against timezoned bounds, so it is kept rather than
compared. -/

#guard (termDateTimeKey (dtL "2000-01-01T00:00:00Z")).isSome
#guard termDateTimeKey (dtL "2000-01-01T00:00:00") == none
#guard (match termDateTimeKey (dtL "2000-01-01T00:00:00Z"),
              termDateTimeKey (dtL "2000-01-01T01:00:00+01:00") with
        | some a, some b => a == b
        | _,      _      => false)
#guard (match termDateTimeKey (dtL "2000-01-01T00:00:00Z"),
              termDateTimeKey (dtL "2000-01-02T00:00:00Z") with
        | some a, some b => b - a == 86400000
        | _,      _      => false)

/-! An untimezoned dateTime is KEPT in a dateTime interval. -/
#guard !(provablyOutsideDateInterval fullInterval (dtL "2000-01-01T00:00:00"))

/-! ## Complement subtracts only PROVABLY equal values -/

#guard valueSetIsEmpty (valueSetSubtract (.enum [intL "1"]) (.enum [intL "1"]))
#guard valueSetIsEmpty (valueSetSubtract (.enum [intL "1"]) (.enum [byteL "1"]))
#guard !(valueSetIsEmpty (valueSetSubtract (.enum [intL "1"]) (.enum [intL "2"])))
/-! Subtracting from a shape with no exact cover is a NO-OP, not a
guess. -/
#guard !(valueSetIsEmpty (valueSetSubtract (.dense fullQInterval) (.enum [intL "1"])))

end L4Factoidal.XSD
