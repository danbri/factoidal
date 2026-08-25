/-
L4Factoidal.RDF.EntailmentRdfsDatatypeClash — D-inconsistency
detection under RDFS D-entailment.

Port of `formal/fstar/RDF.Entailment.RDFS.DatatypeClash.fst` (280
lines).

Baseline: RDF 1.1 Semantics §7 (datatyped interpretations) and §9. A
datatype map fixes, for each recognised datatype IRI, a value space and
a lexical-to-value mapping. A graph is D-INCONSISTENT when it forces a
term into two incompatible positions in that scheme. Two shapes are
decidable here.

## (a) Ill-formed literal under a recognised datatype

§7: "if E is not in the lexical space of a recognized datatype … every
triple containing lit is false". Gated on the RECOGNISED list the
caller supplies — an unrecognised datatype's lexical form is not
checked, per the rdf-mt suite's own framing: a test passes when the
implementation is "configured to recognize all the datatypes in the
list of recognized datatypes".

## (b) Range / type clash

rdfs3 forces every object of a range-restricted property into the range
class's extension. When that class IS a recognised datatype `C` and the
object is itself a literal typed with a DIFFERENT datatype, rdfs3
demands membership in `C`'s value space while the literal's own typing
fixes it elsewhere. §7 keeps a recognised datatype's value space
disjoint from any literal not of that datatype — a plain literal `"25"`
is not in `xsd:integer`'s value space merely because a range assertion
says it must be — so the two demands contradict.

The gate is on `C` alone. The literal's own datatype need not be
recognised: the fact being decided is membership in `C`'s value space,
and `C` IS recognised. That is what makes the rdf-mt fixture whose only
recognised datatype is `xsd:integer`, with a plain-literal object typed
`xsd:string`, still a clash.

## Conservative by construction, and INCOMPLETE by design

This can only add clashes the semantics requires, never invent ones it
does not: rule (a) checks nothing outside the recognised list, and rule
(b) fires only where rdfs3's premise triple is actually present.

It is NOT a complete D-inconsistency decision procedure. A graph whose
only inconsistency is a malformed `rdf:XMLLiteral` under a datatype the
literal checker does not model is reported as "not proven
inconsistent" — correctly, not silently — and a caller must not paper
that over as a pass.
-/
import L4Factoidal.RDF.EntailmentRdfsSpec
import L4Factoidal.RDF.Datatypes

namespace L4Factoidal.RDF

open L4Factoidal.RDFS (rdfsRange)

/-! ## (a) Ill-formed literal under a recognised datatype

`literalIllFormed` is reused verbatim from `RDF.Datatypes`, not
re-derived: it already carries the whitespace-strict numeric lexical
grammar the XSD whitespace-facet tests probe. -/

def hasIllFormedRecognizedLiteral (g : Graph) (recognized : List WfIri) : Bool :=
  g.any (fun t => match t.o with
                  | .literal l => literalIllFormed recognized l.val
                  | _ => false)

/-! ## (b) Range / datatype clash -/

/-- Does `g` hold a triple `_ pDescribed o` whose object is a literal
typed with a datatype other than `c`? -/
def existsRangeLiteralMismatch (g : Graph) (pDescribed c : WfIri) : Bool :=
  g.any (fun t => t.p == pDescribed &&
    (match t.o with
     | .literal l => l.val.datatype != c
     | _ => false))

/-- The whole graph is threaded through, NOT the shrinking recursion
suffix.

That is not a stylistic choice. Searching the suffix would silently
miss a clash whenever the matching literal triple sorts BEFORE the
`rdfs:range` declaration — which is exactly the order the rdf-mt
range-clash fixtures come in. The F\* source records that its own
single-parameter version failed its vacuity guards for this reason, and
the guards below are the same shape. -/
def hasRangeDatatypeClash (g : Graph) (recognized : List WfIri) : Bool :=
  g.any (fun decl =>
    decl.p == rdfsRange &&
    (match decl.o with
     | .iri c => recognized.contains c &&
         (match decl.s with
          | .iri pDescribed => existsRangeLiteralMismatch g pDescribed c
          | _ => false)
     | _ => false))

/-! ## The detector -/

def rdfsDInconsistent (g : Graph) (recognized : List WfIri) : Bool :=
  hasIllFormedRecognizedLiteral g recognized || hasRangeDatatypeClash g recognized

/-! ## Vacuity guard

A detector that degenerated to "always true" or "always false" would
pass every negative test for free. These fixtures pin BOTH answers on
each of the two rules, and pin the recognised-list gate in both
directions — which is the part that decides whether the detector is
doing anything at all.

The F\* module makes the same checks at verification time; here they
are `#guard`s, which fail the build the same way. -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def exFoo : WfIri := iriW "http://example.org/foo"
private def exBar : WfIri := iriW "http://example.org/bar"
private def exS : Subject := .iri (iriW "http://example.org/s")

private def litOf (lex : String) (dt : WfIri) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := none,
                       direction := none }
  if h : literalWf l then .literal ⟨l, h⟩ else .literal (Literal.string lex)

/-! ### Rule (a): an ill-formed integer IS a clash, and only when the
datatype is recognised -/

private def illFormed : Graph := [⟨exS, exFoo, litOf "flargh" xsdInteger⟩]

#guard rdfsDInconsistent illFormed [xsdInteger]
#guard !rdfsDInconsistent illFormed []

/-! A WELL-formed literal of the same recognised datatype is not a
clash — without this the rule could be "always true on a recognised
datatype". -/

#guard !rdfsDInconsistent [⟨exS, exFoo, litOf "25" xsdInteger⟩] [xsdInteger]

/-! ### Rule (b): a range onto a recognised datatype, used with a
literal of a different one -/

private def rangeClash : Graph :=
  [ ⟨.iri exFoo, rdfsRange, .iri xsdInteger⟩,
    ⟨exS, exFoo, litOf "25" xsdString⟩ ]

#guard rdfsDInconsistent rangeClash [xsdInteger]
#guard !rdfsDInconsistent rangeClash []

/-! The declaration order does NOT matter — which is the property the
whole-graph threading exists for, and the one a shrinking-suffix
version gets wrong. -/

private def rangeClashReversed : Graph :=
  [ ⟨exS, exFoo, litOf "25" xsdString⟩,
    ⟨.iri exFoo, rdfsRange, .iri xsdInteger⟩ ]

#guard rdfsDInconsistent rangeClashReversed [xsdInteger]

/-! A literal whose datatype MATCHES the range is not a clash. -/

#guard !rdfsDInconsistent
  [ ⟨.iri exFoo, rdfsRange, .iri xsdInteger⟩,
    ⟨exS, exFoo, litOf "25" xsdInteger⟩ ] [xsdInteger]

/-! Neither is a range declaration with no matching data triple: rule
(b) fires only where rdfs3's premise is actually present. -/

#guard !rdfsDInconsistent [⟨.iri exFoo, rdfsRange, .iri xsdInteger⟩] [xsdInteger]

/-! And a triple on a DIFFERENT property is not caught by the
declaration for `exFoo`. -/

#guard !rdfsDInconsistent
  [ ⟨.iri exFoo, rdfsRange, .iri xsdInteger⟩,
    ⟨exS, exBar, litOf "25" xsdString⟩ ] [xsdInteger]

/-! ### The empty graph is consistent

The degenerate case, pinned because a detector that answered `true`
here would report every graph inconsistent. -/

#guard !rdfsDInconsistent [] [xsdInteger]
#guard !rdfsDInconsistent [] []

end Checks

end L4Factoidal.RDF
