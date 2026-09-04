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
import L4Factoidal.OWL.NegationGoals
import L4Factoidal.OWL.Tableau

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

/-! ## The ≤-rule: identifying witness successors

`f1`, `f2` and `f3` are functional with `f3 ⊑ f1` and `f3 ⊑ f2`, and
`U ≡ ∃f1.p1 ⊓ ∃f2.¬p1 ⊓ ∃f3.p2`. An individual in `U` has an
`f1`-witness in `p1`, an `f2`-witness in `¬p1`, and an `f3`-witness
in `p2`. Functionality forces the `f3`-witness to BE the `f1`-witness
and BE the `f2`-witness, so one element is in `p1` and in `¬p1`.

No clash rule sees this without the ≤-rule: `clashForLabel`'s
`maxCard` case counts only PROVABLY DISTINCT successors and never
counts witnesses at all. Seventeen `WebOnt-description-logic`
inconsistency fixtures are this shape. -/

private def exU : WfIri := ⟨"http://e/U", rfl⟩
private def exP1 : WfIri := ⟨"http://e/p1", rfl⟩
private def exP2 : WfIri := ⟨"http://e/p2", rfl⟩
private def exF1 : WfIri := ⟨"http://e/f1", rfl⟩
private def exF2 : WfIri := ⟨"http://e/f2", rfl⟩
private def exF3 : WfIri := ⟨"http://e/f3", rfl⟩

private def gFunctionalMerge : Graph :=
  [ ⟨.iri exU, owlEquivalentClass, bnT "i"⟩,
    ⟨bn "i", owlIntersectionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, bnT "r1"⟩, ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, bnT "r2"⟩, ⟨bn "l2", rdfRest, bnT "l3"⟩,
    ⟨bn "l3", rdfFirst, bnT "r3"⟩, ⟨bn "l3", rdfRest, .iri rdfNil⟩,
    ⟨bn "r1", owlOnProperty, .iri exF1⟩, ⟨bn "r1", owlSomeValuesFrom, .iri exP1⟩,
    ⟨bn "r2", owlOnProperty, .iri exF2⟩, ⟨bn "r2", owlSomeValuesFrom, bnT "nc"⟩,
    ⟨bn "nc", owlComplementOf, .iri exP1⟩,
    ⟨bn "r3", owlOnProperty, .iri exF3⟩, ⟨bn "r3", owlSomeValuesFrom, .iri exP2⟩,
    ⟨.iri exF1, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exF2, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exF3, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exF3, rdfsSubPropertyOf, .iri exF1⟩,
    ⟨.iri exF3, rdfsSubPropertyOf, .iri exF2⟩,
    ⟨bn "x", rdfType, .iri exU⟩ ]

#guard refuted gFunctionalMerge

/-! Drop the subproperty axioms and the same graph is satisfiable:
three separate successors on three unrelated functional properties
breach nothing. A refuter that merged them anyway would refute an
ontology with a model. -/

private def gNoSubProperty : Graph :=
  gFunctionalMerge.filter (fun t => t.p != rdfsSubPropertyOf)

#guard !(refuted gNoSubProperty)

/-! A NAMED individual is never a merge candidate. Its graph-asserted
edges cannot be rewritten, and a clash read off a half-merged state
is fabricated. -/
#guard !(isMergeableTerm (.iri exP1))
#guard isMergeableTerm (bnT "w")

/-! ## Closure scaffolding is inert

The OWL RL closure materialises `__rl_`-prefixed blank nodes as
support triples, with an encoding that is deliberately looser than
the class expression they resemble. Reading one literally
MANUFACTURES refutations of consistent premises. -/
#guard isScaffoldBNode (bnT "__rl_comp__http://e/C")
#guard !(isScaffoldBNode (bnT "ordinary"))

/-! ## `∃p.C` is discharged by a successor CARRYING `C`

Not by any successor at all. An existential whose filler is
anonymous gets an edge from the materialisation pass but no type, so
counting successors said "discharged", no witness was minted, and the
filler was never put on any node — the ≤-rule then pooled labels that
did not include it and every branch stayed open
(`WebOnt-description-logic-003` and its family; seven cases turned on
this one line). -/

private def gExistingSuccessorWrongClass : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri owlNothing⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    -- An asserted p-successor that is NOT in the filler. The
    -- obligation is still open, so a witness must be minted and the
    -- filler put on it — which refutes, since the filler is empty.
    ⟨indI, exP, .iri exY⟩ ]

#guard refuted gExistingSuccessorWrongClass

/-! With the successor already in the filler the obligation IS
discharged and nothing is minted. -/

private def gExistingSuccessorRightClass : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    ⟨indI, exP, .iri exY⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard !(refuted gExistingSuccessorRightClass)

/-! ## Four more graph-level violations

Each is a shape that has no model without any expansion at all, and
each is paired with the nearest SATISFIABLE graph — the pairing is
the check, because either half alone can be passed by an engine that
has the rule backwards. -/

/-! G6: OWL 2 Direct Semantics requires a NON-EMPTY domain and
interprets `owl:Thing` as the whole of it, so equating it with the
empty class has no model. -/
#guard refuted [⟨.iri owlThing, owlEquivalentClass, .iri owlNothing⟩]
#guard refuted [⟨.iri owlNothing, owlEquivalentClass, .iri owlThing⟩]
#guard !(refuted [⟨.iri exC, owlEquivalentClass, .iri owlNothing⟩])

/-! G7: two DIFFERENT properties declared disjoint, sharing a pair.
The RL marker wants two distinct predicates and so does this. -/
#guard refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exQ⟩,
                ⟨indI, exP, .iri exY⟩, ⟨indI, exQ, .iri exY⟩]
/-! Different pairs on the same two properties are fine. -/
#guard !(refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exQ⟩,
                  ⟨indI, exP, .iri exY⟩, ⟨indI, exQ, .iri exZ⟩])

/-! G8: `owl:AllDisjointProperties` asserts PAIRWISE disjointness. -/
private def gAllDisjointProps (o1 o2 : Term) : Graph :=
  [ ⟨bn "ad", rdfType, .iri owlAllDisjointProperties⟩,
    ⟨bn "ad", owlMembers, bnT "m1"⟩,
    ⟨bn "m1", rdfFirst, .iri exP⟩, ⟨bn "m1", rdfRest, bnT "m2"⟩,
    ⟨bn "m2", rdfFirst, .iri exQ⟩, ⟨bn "m2", rdfRest, .iri rdfNil⟩,
    ⟨indI, exP, o1⟩, ⟨indI, exQ, o2⟩ ]

#guard refuted (gAllDisjointProps (.iri exY) (.iri exY))
#guard !(refuted (gAllDisjointProps (.iri exY) (.iri exZ)))

/-! G9: asymmetry says `(x,y) ∈ EXT(p)` implies `(y,x) ∉ EXT(p)`;
irreflexivity says no pair `(x,x)` is in it. -/
#guard refuted [⟨.iri exP, rdfType, .iri owlAsymmetricProperty⟩,
                ⟨indI, exP, .iri exY⟩, ⟨.iri exY, exP, .iri exI⟩]
#guard !(refuted [⟨.iri exP, rdfType, .iri owlAsymmetricProperty⟩,
                  ⟨indI, exP, .iri exY⟩])
#guard refuted [⟨.iri exP, rdfType, .iri owlIrreflexiveProperty⟩,
                ⟨indI, exP, .iri exI⟩]
#guard !(refuted [⟨.iri exP, rdfType, .iri owlIrreflexiveProperty⟩,
                  ⟨indI, exP, .iri exY⟩])

/-! ## The three-valued verdict (issue 586)

`tableauConsistent` mirrors F* `tableau_consistent` meaning for
meaning: `some false` = clash, `some true` = quiescence, `none` =
budget out. `refute` is its refutation-only projection
(`refute_eq_false_iff`). -/

/-! Quiescence with no clash answers `some true` where `refute`
answers `none`. -/
#guard tableauConsistent [⟨indI, rdfType, .iri exC⟩] fuel == some true
#guard refute [⟨indI, rdfType, .iri exC⟩] fuel == none

/-! A clash answers `some false` through BOTH views. -/
#guard tableauConsistent gComplement fuel == some false
#guard refute gComplement fuel == some false

/-! A cyclic TBox (`A ⊑ ∃P.A`) keeps the expansion changing: budget 1
is exhausted mid-search and the verdict is `none` — indeterminate,
never collapsed into either Boolean. The SAME input at a working
budget saturates under the witness-depth cap and answers
`some true`. -/
private def gCyclicExists : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩,
    ⟨.iri exC, rdfsSubClassOf, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩ ]

#guard tableauConsistent gCyclicExists 1 == none
#guard tableauConsistent gCyclicExists fuel == some true
#guard refute gCyclicExists 1 == none

/-! ## Paired witness: procedural clash ↔ declarative `Refuted`

The same contradiction — `C` and `¬C` at one individual — refuted by
this module's search (the `#guard` above on `gComplement`) and by an
explicit derivation in the declarative calculus of
`OWL/Tableau.lean`. The pairing is the instance-level form of the
correspondence the module header states; the general abstraction is
the certificate-checker rung
(https://github.com/danbri/factoidal/issues/586 follow-up 6). -/
example : Refuted .empty [.inst "i" (.atom "C"), .inst "i" (.neg (.atom "C"))] :=
  .clash (.hyp (.head _)) (.hyp (.tail _ (.head _)))

/-! ## Negation goals (PE-via-refutation, issue 586)

Shape checks first, then two end-to-end verdicts. -/

/-! A class membership negates to ONE goal carrying the complement
pair. -/
#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map List.length == some 1

/-! A subsumption negates to one goal; an equivalence to two (C ⊑ D
and D ⊑ C, both required). -/
#guard (negationGoals [⟨.iri exC, rdfsSubClassOf, .iri exD⟩]).map List.length
       == some 1
#guard (negationGoals [⟨.iri exC, owlEquivalentClass, .iri exD⟩]).map List.length
       == some 2

/-! A plain property assertion negates through the `≤0 p.{y}`
encoding — ten triples, no base. -/
#guard (negationGoals [⟨indI, exP, .iri exY⟩]).map (·.map List.length)
       == some [10]

/-! A property assertion with a LITERAL object has no sound negation
in this encoding (`owl:oneOf` of a literal is a data range):
conservative `none`. A purely structural conclusion has no content
assertion to negate: `none`. -/
#guard negationGoals
        [⟨indI, exP, .literal ⟨{ lexicalForm := "v", datatype := xsdString,
                                 langTag := none, direction := none }, rfl⟩⟩]
       == none
#guard negationGoals [⟨bn "r", owlOnProperty, .iri exP⟩] == none

/-! End to end, entailed: `i ∈ C, C ⊑ D ⊨ i ∈ D`. The negated
conclusion (`i ∈ ¬D`) clashes with the derived `D`: every goal
refutes. -/
private def gPremiseSub : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩, ⟨.iri exC, rdfsSubClassOf, .iri exD⟩ ]

#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map
         (·.all (fun neg => tableauConsistent (gPremiseSub ++ neg) fuel
                            == some false))
       == some true

/-! End to end, NOT entailed: `i ∈ C ⊭ i ∈ D`. The augmented graph
has a model (quiescence, `some true`) — a countermodel, reported as
`entailed: false`, never as a silent miss. -/
#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map
         (·.any (fun neg => tableauConsistent ([⟨indI, rdfType, .iri exC⟩] ++ neg)
                              fuel == some true))
       == some true


/-! ## Literal distinctness is decided on VALUES

`provablyDistinct` used to compare LEXICAL forms and only for
`xsd:string`. These checks pin both directions of the value-level
replacement: a `true` is a licence to clash and must hold in every
model; a `false` is a withholding and must be kept wherever the value
question is open. -/

private def lit (lex : String) (dt : WfIri) : Literal :=
  { lexicalForm := lex, datatype := dt, langTag := none, direction := none }

/-! Different integers, and the lexical mapping of the integer family
    is not injective, so this needs the VALUE. -/
#guard literalValuesDistinct (lit "18" xsdInteger) (lit "19" xsdInteger)
#guard literalValuesDistinct (lit "18" xsdInteger) (lit "19" XSD.xsdInt)

/-! One integer written two ways is ONE value. `"1"` and `"01"` are
    the case the lexical predicate got wrong in the other direction. -/
#guard !literalValuesDistinct (lit "1" xsdInteger) (lit "01" xsdInteger)
#guard !literalValuesDistinct (lit "1" xsdInteger) (lit "1.0" xsdDecimal)

/-! XSD Datatypes §3.2.4: `positiveZero` and `negativeZero` are two
    distinct members of the `xsd:float` value space. -/
#guard literalValuesDistinct (lit "+0.0" XSD.xsdFloat) (lit "-0.0" XSD.xsdFloat)
#guard !literalValuesDistinct (lit "+0.0" XSD.xsdFloat) (lit "0" XSD.xsdFloat)

/-! Two finite non-zero floats WITHHOLD: the lexical-to-value map
    rounds to the grid, so unequal lexical forms can be one value. -/
#guard !literalValuesDistinct (lit "1.5" XSD.xsdFloat) (lit "1.6" XSD.xsdFloat)

/-! OWL 2 Syntax §4: the value spaces of the datatype-map families are
    pairwise disjoint. -/
#guard literalValuesDistinct (lit "1" xsdInteger) (lit "1" xsdString)
#guard literalValuesDistinct (lit "true" xsdBoolean) (lit "true" xsdString)

/-! `xsd:boolean` has two values and four lexical forms. -/
#guard !literalValuesDistinct (lit "1" xsdBoolean) (lit "true" xsdBoolean)
#guard literalValuesDistinct (lit "0" xsdBoolean) (lit "true" xsdBoolean)

/-! A datatype outside every family withholds. -/
#guard !literalValuesDistinct (lit "2026-09-04T00:00:00Z" XSD.xsdDateTime)
                              (lit "2026-09-05T00:00:00Z" XSD.xsdDateTime)

/-! `rdf:XMLLiteral` by exclusive canonical XML, RDF 1.1 Concepts
    §5.1. The first pair is `WebOnt-miscellaneous-202`, asserted
    CONSISTENT: insignificant whitespace, one value, no clash. The
    second is the `-203` shape: leading text is significant, two
    values, clash. -/
#guard !literalValuesDistinct (lit "<br></br>" rdfXMLLiteral)
                              (lit "<br\n></br>" rdfXMLLiteral)
#guard literalValuesDistinct (lit "\n<br></br>" rdfXMLLiteral)
                             (lit "<br></br>" rdfXMLLiteral)

end L4Factoidal.OWL.Refute
