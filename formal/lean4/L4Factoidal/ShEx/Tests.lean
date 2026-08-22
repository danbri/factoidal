/-
L4Factoidal.ShEx.Tests — build-time checks for the ShEx schema AST and
node-constraint satisfaction.
-/
import L4Factoidal.ShEx.Validation

namespace L4Factoidal.ShEx
open L4Factoidal.RDF

private def iriT (s : String) : Term :=
  if h : isIri s then .iri ⟨s, h⟩ else .bnode "invalid"
private def litT (s : String) : Term := .literal (Literal.string s)
private def langT (s tag : String) : Term := .literal (Literal.langString s tag)
private def bnodeT : Term := .bnode "b0"

-- nodeKind, including nonLiteral admitting both IRIs and bnodes.
#guard matchesNodeKind .iri (iriT "http://ex/a")
#guard matchesNodeKind .literal (litT "x")
#guard matchesNodeKind .bnode bnodeT
#guard matchesNodeKind .nonLiteral (iriT "http://ex/a")
#guard matchesNodeKind .nonLiteral bnodeT
#guard !(matchesNodeKind .nonLiteral (litT "x"))

-- datatype: only literals can match.
#guard matchesDatatype "http://www.w3.org/2001/XMLSchema#string" (litT "x")
#guard !(matchesDatatype "http://www.w3.org/2001/XMLSchema#string" (iriT "http://ex/a"))

-- Length facets count CHARACTERS, not bytes.
#guard matchesLengthFacets { length := some 3 } (litT "abc")
#guard !(matchesLengthFacets { length := some 3 } (litT "abcd"))
#guard matchesLengthFacets { length := some 1 } (litT "é")   -- 2 bytes, 1 char
#guard matchesLengthFacets { minLength := some 2, maxLength := some 4 } (litT "abc")

-- Exact object values. An absent language in the constraint means
-- UNCONSTRAINED, not "must be absent".
#guard matchesObjectValue (.iri "http://ex/a") (iriT "http://ex/a")
#guard matchesObjectValue (.literal "x" none none) (litT "x")
#guard matchesObjectValue (.literal "x" none none) (langT "x" "en")
#guard matchesObjectValue (.literal "x" (some "en") none) (langT "x" "en")
#guard !(matchesObjectValue (.literal "x" (some "fr") none) (langT "x" "en"))

-- Stems are PREFIX matches; wildcards match anything of the kind.
#guard matchesStem .iri (.plain "http://ex/") (iriT "http://ex/a")
#guard !(matchesStem .iri (.plain "http://other/") (iriT "http://ex/a"))
#guard matchesStem .iri .wildcard (iriT "http://anything")
#guard !(matchesStem .iri .wildcard (litT "x"))

-- A stem RANGE exclusion removes a term the stem would have admitted.
#guard matchesValueSetValue (.stemRange .iri (.plain "http://ex/") []) (iriT "http://ex/a")
#guard !(matchesValueSetValue
          (.stemRange .iri (.plain "http://ex/") [.iri "http://ex/a"]) (iriT "http://ex/a"))

-- An EMPTY value set is unconstrained.
#guard matchesValues [] (litT "anything")

-- Exact decimal comparison, no floats: 0.1 + 0.2 style precision
-- traps cannot arise because nothing is converted.
#guard compareDecimal "1.10" "1.1" == some .eq
#guard compareDecimal "2" "10" == some .lt
#guard compareDecimal "-5" "3" == some .lt
#guard compareDecimal "-5" "-10" == some .gt
#guard compareDecimal "abc" "1" == none

-- Numeric facets. A NON-NUMERIC lexical form fails rather than being
-- coerced to zero.
#guard matchesNumericFacets { minInclusive := some "5" } (litT "5")
#guard !(matchesNumericFacets { minExclusive := some "5" } (litT "5"))
#guard matchesNumericFacets { maxInclusive := some "5" } (litT "4.99")
#guard !(matchesNumericFacets { minInclusive := some "5" } (litT "abc"))
#guard !(matchesNumericFacets { minInclusive := some "5" } (iriT "http://ex/a"))
-- With no numeric facet set, any node passes that check.
#guard matchesNumericFacets {} (iriT "http://ex/a")

-- Full node constraints.
#guard satisfiesNodeConstraint {} (litT "anything")
#guard satisfiesNodeConstraint
         { nodeKind := some .iri, values := [.stem .iri (.plain "http://ex/")] }
         (iriT "http://ex/a")
#guard !(satisfiesNodeConstraint { nodeKind := some .iri } (litT "x"))

-- Cardinality helpers on triple constraints; -1 is unbounded.
private def tc1 : TripleConstraint := .mk none false "http://ex/p" none 1 (-1) [] []
#guard tc1.unbounded
#guard tc1.satisfiesCard 5
#guard !(tc1.satisfiesCard 0)
private def tc2 : TripleConstraint := .mk none false "http://ex/p" none 0 1 [] []
#guard tc2.satisfiesCard 0
#guard !(tc2.satisfiesCard 2)

-- Schema lookup by label.
private def sch : Schema :=
  { shapes := [{ id := "http://ex/S", expr := .nodeConstraint { nodeKind := some .iri } }] }
#guard (sch.lookup "http://ex/S").isSome
#guard (sch.lookup "http://ex/missing").isNone

end L4Factoidal.ShEx
