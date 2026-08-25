/-
L4Factoidal.RDF.EntailmentRdfSpec — RDF entailment, transcribed from
the specification text.

Port of `formal/fstar/RDF.Entailment.RDF.Spec.fst` (418 lines).

Rung two of the entailment ladder: above simple entailment
(`RDF.EntailmentSimpleSpec`) and below RDFS entailment.

Baseline: RDF 1.1 Semantics §8, "RDF Interpretations" — the semantic
conditions, the RDF axiomatic triples, and the two-row entailment rule
table. Cross-checked against Hayes, RDF Semantics (2004) §3, the
baseline the normative OWL 2 specifications build on.

Like the simple-entailment transcription, this module computes nothing
about the engine and calls no engine function: it can be diffed against
the specification text on its own.

## The datatype set is a parameter, and that is the point

§8 defines RDF entailment "recognizing D" for a set D of datatype IRIs,
with `rdf:langString` and `xsd:string` always in D. Keeping D a
parameter is what lets the rdfD1 row be stated at all without
prejudging which datatypes an implementation recognises.

## rdfD1 is specified and NOT implemented, deliberately

The shipping tree implements no rdfD1 — in either the F\* or the Lean
engine. It is written here so the rule table is COMPLETE in the
document and the gap is visible, and so a completeness statement about
the RDFS rung can name the fragment where rdfD1 cannot fire. A rule
table with a row quietly missing reads as a table with no gap.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.RDF.VocabularyAxioms
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RDF

open L4Factoidal.RDFS (rdfType rdfProperty)

/-! ## The recognised datatypes -/

abbrev DatatypeSet := WfIri → Prop

/-- The MINIMUM D of §8: "RDF interpretations … recognize the datatype
IRIs `rdf:langString` and `xsd:string`." -/
def dMinimal : DatatypeSet := fun d => d = rdfLangString ∨ d = xsdString

/-! ## Row rdfD2

§8, the RDF entailment rule table, verbatim:

> rdfD2 | xxx aaa yyy . | aaa rdf:type rdf:Property .

(2004 numbers the same rule `rdf1`; the content is identical.)

`aaa` is a predicate, hence an IRI, hence legal as the conclusion's
subject — this row needs no generalized-RDF escape. -/

def rdfD2Conclusion (u : Triple) : Triple :=
  { s := .iri u.p, p := rdfType, o := .iri rdfProperty }

def RdfD2Derives (g : Graph) (t : Triple) : Prop :=
  ∃ u : Triple, u ∈ g ∧ t = rdfD2Conclusion u

/-! ## Row rdfD1

§8, verbatim:

> rdfD1 | xxx aaa "sss"^^ddd . (for ddd in D) |
>         xxx aaa _:nnn . _:nnn rdf:type ddd .

The conclusion MINTS A FRESH BLANK NODE, so the relation carries the
label as an explicit parameter plus a freshness side condition rather
than hiding it in an existential: a rule that may invent a name is not
a function of its premise alone. -/

/-- Freshness at the top level of a triple. An RDF 1.2 triple term
could bury the same label deeper; rdfD1 is not implemented in either
tree, so nothing depends on that case. -/
def BnodeFreshFor (b : BNodeId) (g : Graph) : Prop :=
  ∀ t : Triple, t ∈ g → t.s ≠ Subject.bnode b ∧ t.o ≠ Term.bnode b

def RdfD1Derives (D : DatatypeSet) (g : Graph) (b : BNodeId) (t1 t2 : Triple) : Prop :=
  BnodeFreshFor b g ∧
  ∃ u : Triple, u ∈ g ∧ ∃ l : WfLiteral,
    u.o = .literal l ∧ D l.val.datatype ∧
    t1 = { s := u.s, p := u.p, o := .bnode b } ∧
    t2 = { s := .bnode b, p := rdfType, o := .iri l.val.datatype }

/-! ## The RDF axiomatic triples

§8 lists them. The finite rows are already transcribed one per row with
their citations in `RDF.VocabularyAxioms`; this module REUSES that
table rather than making a second copy.

The infinite family `rdf:_1 rdf:type rdf:Property .`, `rdf:_2 …` is not
tabulable, so it is captured by the schema below — the declarative form
of what the engine's finite slice approximates. -/

def rdfMemberIriStr (n : String) : String :=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#_" ++ n

/-- Stated as membership in the syntactic family rather than by
arithmetic on the IRI string: what matters downstream is only that the
engine's finite slice is CONTAINED in it. -/
def IsRdfMemberIri (i : WfIri) : Prop := ∃ n : String, i.val = rdfMemberIriStr n

def RdfAxiomatic (t : Triple) : Prop :=
  t ∈ rdfAxiomaticTriples ∨
  ∃ i : WfIri, IsRdfMemberIri i ∧
    t = { s := .iri i, p := rdfType, o := .iri rdfProperty }

/-! ## The specification, syntactic side

§8's completeness statement is about closures: "If S is RDF consistent,
then S RDF entails E just when the generalized RDF closure of S towards
E simply entails E." A graph is a closure when it holds the axiomatic
triples and is shut under the rule table.

rdfD1 is EXCLUDED from `RdfClosed` on purpose: it mints fresh blank
nodes, so a graph closed under it is not finite. The specification text
handles this the same way, by taking the closure "towards E". -/

def RdfClosed (g : Graph) : Prop :=
  (∀ t, RdfAxiomatic t → t ∈ g) ∧ (∀ t, RdfD2Derives g t → t ∈ g)

/-- The weaker, monotone notion an engine actually targets: every
triple it adds is licensed by the rule table applied to the ORIGINAL
graph. This is what a soundness proof about a one-pass rule function
establishes, and it composes. -/
def RdfStepLicensed (g out : Graph) : Prop :=
  ∀ t : Triple, t ∈ out → t ∈ g ∨ RdfAxiomatic t ∨ RdfD2Derives g t

/-! ## Bridges

Named rather than left implicit, so a proof can cite them instead of
re-noticing the disjunct. -/

/-- The transcribed finite table is sound for the semantic-side
recognizer.

SOUNDNESS ONLY: this does NOT claim the finite table lists every RDF
axiomatic triple. The `rdf:_n` family is infinite and is handled by
`IsRdfMemberIri`, not by enumeration. -/
theorem finiteRdfAxioms_sound {t : Triple} (h : t ∈ rdfAxiomaticTriples) :
    RdfAxiomatic t := Or.inl h

/-- Every conclusion rdfD2 licenses really is licensed by the step
relation, so an engine that emits exactly the rdfD2 conclusions of `g`
satisfies `RdfStepLicensed`. Stated so the composition direction is
checked rather than assumed. -/
theorem rdfD2_stepLicensed (g : Graph) (out : Graph)
    (h : ∀ t : Triple, t ∈ out → RdfD2Derives g t) : RdfStepLicensed g out :=
  fun t ht => Or.inr (Or.inr (h t ht))

/-- An RDF-closed graph is closed under rdfD2 by definition, so
extending it by rdfD2 conclusions adds nothing outside it. -/
theorem rdfClosed_absorbs_rdfD2 {g : Graph} (h : RdfClosed g) {t : Triple}
    (hd : RdfD2Derives g t) : t ∈ g := h.2 t hd

/-! ## Build-time checks

The predicates above are relations, so what a check can pin is the
COMPUTED side of each: the conclusion a row builds, and the membership
of the finite table. -/

section Checks

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def u1 : Triple :=
  ⟨.iri (iriW "http://e.org/s"), iriW "http://e.org/p", .iri (iriW "http://e.org/o")⟩

/-! rdfD2 puts the PREDICATE in subject position — the one thing about
this row that is easy to get backwards. -/

#guard rdfD2Conclusion u1 == ⟨.iri (iriW "http://e.org/p"), rdfType, .iri rdfProperty⟩
#guard (rdfD2Conclusion u1).s != .iri (iriW "http://e.org/s")

/-! The container-membership family the schema describes contains the
engine's finite slice, which is the only property downstream needs. -/

#guard rdfMemberIriStr "1" == "http://www.w3.org/1999/02/22-rdf-syntax-ns#_1"
#guard rdfMemberIriStr "42" == "http://www.w3.org/1999/02/22-rdf-syntax-ns#_42"

/-! The finite table is the one `RDF.VocabularyAxioms` transcribes, and
it is not empty — a soundness bridge into an empty table would prove
nothing. -/

#guard rdfAxiomaticTriples.length == 8

end Checks

end L4Factoidal.RDF
