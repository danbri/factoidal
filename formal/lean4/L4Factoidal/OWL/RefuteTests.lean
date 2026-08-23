/-
L4Factoidal.OWL.RefuteTests — build-time checks for the refutation
calculus.

Two kinds of check, and the second kind is the one that matters:

* a graph that HAS no model is refuted;
* a graph that HAS a model is NOT refuted.

The second kind is what a refuter gets wrong. `refute` answers
`some false` or `none`, so a consistent graph must come back `none`;
anything else is a fabricated contradiction, and a fabricated
contradiction turns a passing consistency test into a failing one
while looking exactly like progress.
-/
import L4Factoidal.OWL.Refute

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

private def exC : WfIri := ⟨"http://e/C", rfl⟩
private def exD : WfIri := ⟨"http://e/D", rfl⟩
private def exP : WfIri := ⟨"http://e/P", rfl⟩
private def exQ : WfIri := ⟨"http://e/Q", rfl⟩
private def exI : WfIri := ⟨"http://e/i", rfl⟩
private def exY : WfIri := ⟨"http://e/y", rfl⟩
private def exZ : WfIri := ⟨"http://e/z", rfl⟩

private def indI : Subject := .iri exI
private def bn (b : String) : Subject := .bnode b
private def bnT (b : String) : Term := .bnode b

private def fuel : Nat := 40

private def refuted (g : Graph) : Bool := refute g fuel == some false

/-! ## Negation normal form -/

#guard ClassExpr.beq (nnf (.complement (.complement (.named exC)))) (.named exC)
#guard ClassExpr.beq (nnf (.complement (.intersection [.named exC, .named exD])))
                     (.union [.complement (.named exC), .complement (.named exD)])
#guard ClassExpr.beq (nnf (.complement (.someOf exP (.named exC))))
                     (.allOf exP (.complement (.named exC)))
#guard ClassExpr.beq (nnf (.complement (.minCard 2 exP))) (.maxCard 1 exP)
#guard ClassExpr.beq (nnf (.complement (.maxCard 2 exP))) (.minCard 3 exP)

/-! `¬(≥ 0 p)` is `⊥`, not `≤ -1 p`: every individual has at least
zero successors in every model, so the negation is unsatisfiable. -/
#guard ClassExpr.beq (nnf (.complement (.minCard 0 exP))) (.named owlNothing)

/-! `= 0 p` normalises to `≤ 0 p` ALONE. Keeping the tautological
`≥ 0 p` conjunct would put a label in the set that no axiom
left-hand side written `≤ 0 p` could ever match. -/
#guard ClassExpr.beq (nnf (.exactCard 0 exP)) (.maxCard 0 exP)
#guard ClassExpr.beq (nnf (.exactCard 2 exP))
                     (.intersection [.minCard 2 exP, .maxCard 2 exP])

/-! The negation of an unreadable expression DROPS the constraint.
Dropping one loses clashes; it never invents one. -/
#guard ClassExpr.beq (nnfNeg .unknown) .unknown

/-! ## Clashes on the label set -/

/-! `owl:Nothing` is empty in every model. -/
#guard refuted [⟨indI, rdfType, .iri owlNothing⟩]

/-! `C` and `¬C` on one individual. -/
private def gComplement : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩,
    ⟨indI, rdfType, bnT "n"⟩,
    ⟨bn "n", owlComplementOf, .iri exC⟩ ]

#guard refuted gComplement

/-! Two disjoint classes on one individual. The disjointness axiom
gives `C ⊑ ¬D`, and the unfolding puts `¬D` beside `D`. -/
private def gDisjoint : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩, ⟨indI, rdfType, .iri exD⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩ ]

#guard refuted gDisjoint

/-! `≥ 2 p` beside `≤ 1 p`. No successors need to exist for this: the
two bounds contradict each other outright. -/
/-! ## `≤ 0 p` with an asserted successor -/

private def cardLit (v : String) : Term :=
  .literal ⟨{ lexicalForm := v,
              datatype := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩,
              langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff]⟩

private def gMaxZero : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlMaxCardinality, cardLit "0"⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard refuted gMaxZero

/-! ## `≤ 1 p` with two PROVABLY distinct successors

Two different IRIs are not enough — without `owl:differentFrom` they
may denote one individual, and a refuter that assumed otherwise would
be applying a unique-name assumption OWL does not make. -/

private def gMaxOneBase : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlMaxCardinality, cardLit "1"⟩,
    ⟨indI, exP, .iri exY⟩, ⟨indI, exP, .iri exZ⟩ ]

#guard !(refuted gMaxOneBase)
#guard refuted (gMaxOneBase ++ [⟨.iri exY, owlDifferentFrom, .iri exZ⟩])

/-! ## The `∀` rule pushes across successors -/

private def gAllValues : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlAllValuesFrom, .iri owlNothing⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard refuted gAllValues

/-! Without the successor there is nothing to push onto, and `∀` is
vacuously satisfiable. -/
#guard !(refuted (gAllValues.filter (fun t => t.p != exP)))

/-! ## An existential witness carries the filler

`∃ p.⊥` has no model: the witness would have to be in the empty
class. This needs the witness to be MINTED — the graph asserts no
`p`-successor at all. -/

private def gSomeBottom : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri owlNothing⟩ ]

#guard refuted gSomeBottom

/-! A witness is NOT counted against a cardinality bound: it may
coincide with an existing successor in some model. `∃ p.C` beside
`≤ 1 p` with one asserted successor is satisfiable, and a refuter
that counted the witness would say otherwise. -/

private def gWitnessNotCounted : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "m"⟩,
    ⟨bn "m", owlOnProperty, .iri exP⟩,
    ⟨bn "m", owlMaxCardinality, cardLit "1"⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard !(refuted gWitnessNotCounted)

/-! ## Union branching

`C ⊔ D` refutes the node only when BOTH disjuncts clash. -/

private def gUnionBothBad : Graph :=
  [ ⟨indI, rdfType, bnT "u"⟩,
    ⟨bn "u", owlUnionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri owlNothing⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri owlNothing⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard refuted gUnionBothBad

private def gUnionOneGood : Graph :=
  [ ⟨indI, rdfType, bnT "u"⟩,
    ⟨bn "u", owlUnionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri owlNothing⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exC⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard !(refuted gUnionOneGood)

/-! ## `owl:FunctionalProperty` is a global `≤ 1 p` -/

private def gFunctional : Graph :=
  [ ⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩,
    ⟨indI, rdfType, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩, ⟨indI, exP, .iri exZ⟩,
    ⟨.iri exY, owlDifferentFrom, .iri exZ⟩ ]

#guard refuted gFunctional

/-! ## The role hierarchy makes a subproperty edge count

`q rdfs:subPropertyOf p` gives `EXT(q) ⊆ EXT(p)` in every model, so a
`q`-edge is a `p`-successor wherever one is counted. -/

private def gSubProperty : Graph :=
  [ ⟨.iri exQ, rdfsSubPropertyOf, .iri exP⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlMaxCardinality, cardLit "0"⟩,
    ⟨indI, exQ, .iri exY⟩ ]

#guard refuted gSubProperty

/-! ## Graph-level violations -/

/-! G1: an `owl:AllDifferent` list naming one member twice. -/
private def gAllDifferent : Graph :=
  [ ⟨bn "ad", rdfType, .iri owlAllDifferent⟩,
    ⟨bn "ad", owlMembers, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exY⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exY⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard refuted gAllDifferent

/-! The same list with two members and no `owl:sameAs` between them is
fine: distinct NAMES are not distinct individuals, but a list may
name whatever it likes. -/
private def gAllDifferentOk : Graph :=
  [ ⟨bn "ad", rdfType, .iri owlAllDifferent⟩,
    ⟨bn "ad", owlMembers, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exY⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exZ⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard !(refuted gAllDifferentOk)

/-! G3: `p owl:propertyDisjointWith p` makes `EXT(p)` empty, so any
triple using `p` is false in every model. The RL marker misses this
because it wants two DIFFERENT predicates. -/
#guard refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exP⟩,
                ⟨indI, exP, .iri exY⟩]

/-! Declared but unused, the same axiom is satisfiable — `EXT(p)` is
simply empty. -/
#guard !(refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exP⟩])

/-! G4: `rdf:nil` is the empty list and carries no `rdf:first`. -/
#guard refuted [⟨.iri rdfNil, rdfFirst, .iri exY⟩]

/-! ## Consistent graphs stay unrefuted

The check a refuter fails. Every graph here has a model, and every
one must come back `none`. -/

#guard !(refuted [])
#guard !(refuted [⟨indI, rdfType, .iri exC⟩])
#guard !(refuted [⟨indI, rdfType, .iri exC⟩, ⟨indI, rdfType, .iri exD⟩])
#guard !(refuted [⟨.iri exC, owlDisjointWith, .iri exD⟩,
                  ⟨indI, rdfType, .iri exC⟩,
                  ⟨.iri exY, rdfType, .iri exD⟩])
#guard !(refuted gWitnessNotCounted)
#guard !(refuted [⟨.iri exP, rdfType, .iri owlTransitiveProperty⟩,
                  ⟨indI, exP, .iri exY⟩, ⟨.iri exY, exP, .iri exZ⟩])

/-! An unreadable class expression constrains nothing. A refuter that
guessed at one would answer a question it had not read. -/
#guard !(refuted [⟨indI, rdfType, bnT "mystery"⟩,
                  ⟨bn "mystery", exP, .iri exC⟩])

/-! ## There is no `some true`

A quiet, clash-free expansion is `none`, not a claim of consistency:
this calculus is incomplete, so an open branch proves nothing. -/
#guard refute [⟨indI, rdfType, .iri exC⟩] fuel == none
#guard refute [] fuel == none

end L4Factoidal.OWL.Refute
