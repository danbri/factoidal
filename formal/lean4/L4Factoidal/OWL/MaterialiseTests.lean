/-
L4Factoidal.OWL.MaterialiseTests — build-time checks for the
positive-sound membership rules.

Each check states one rule and, where the rule WITHHOLDS an answer,
says what the wrong answer would have been. The withholding checks
matter more than the positive ones: a reasoner that answers
`some false` for "I have not seen it" is wrong under the open world
assumption, and nothing downstream can tell the two apart once the
answer is written into a graph.
-/
import L4Factoidal.OWL.Materialise

namespace L4Factoidal.OWL.Mat

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

private def exC : WfIri := ⟨"http://e/C", rfl⟩
private def exD : WfIri := ⟨"http://e/D", rfl⟩
private def exE : WfIri := ⟨"http://e/E", rfl⟩
private def exP : WfIri := ⟨"http://e/P", rfl⟩
private def exI : WfIri := ⟨"http://e/i", rfl⟩
private def exY : WfIri := ⟨"http://e/y", rfl⟩
private def exZ : WfIri := ⟨"http://e/z", rfl⟩

private def indI : Subject := .iri exI
private def bn (b : String) : Subject := .bnode b
private def bnT (b : String) : Term := .bnode b

private def st (g : Graph) : Store := Store.ofGraph g

private def ask (g : Graph) (ce : ClassExpr) : Option Bool :=
  runWork (isMember (st g) indI ce 64)

/-! ## A named class is an open-world lookup

The graph asserting it settles the question. The graph NOT asserting
it settles nothing — `some false` here would be the reasoner
mistaking an empty search for a proof. -/

#guard ask [⟨indI, rdfType, .iri exC⟩] (.named exC) == some true
#guard ask [] (.named exC) == none

/-! ## `∃ p. c` -/

private def gSome : Graph :=
  [ ⟨indI, exP, .iri exY⟩, ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard ask gSome (.someOf exP (.named exC)) == some true

/-! No successor is not a refutation: an unseen one may exist. -/

#guard ask [] (.someOf exP (.named exC)) == none

/-! A successor whose membership is unknown leaves the question
    unknown, not false. -/

#guard ask [⟨indI, exP, .iri exY⟩] (.someOf exP (.named exC)) == none

/-! ## `∀ p. c`

`some true` when every KNOWN successor is provably in `c`, and
`some false` as soon as one provably is not. One unknown successor
makes the whole answer unknown — "all" cannot be proved past a
gap. -/

#guard ask gSome (.allOf exP (.named exC)) == some true
#guard ask [] (.allOf exP (.named exC)) == some true   -- vacuously

private def gAllUnknown : Graph :=
  [ ⟨indI, exP, .iri exY⟩, ⟨.iri exY, rdfType, .iri exC⟩,
    ⟨indI, exP, .iri exZ⟩ ]

#guard ask gAllUnknown (.allOf exP (.named exC)) == none

/-! ## `⊓` does not stop at an unknown conjunct

A later conjunct that is provably FALSE still refutes the whole
intersection. Returning `none` at the first unknown would lose that
refutation. -/

private def strLit (v : String) : Term :=
  .literal ⟨{ lexicalForm := v, datatype := xsdString, langTag := none,
              direction := none },
            by simp [literalWf, xsdString, rdfLangString, rdfDirLangString,
                     Subtype.ext_iff]⟩

/-! A LITERAL successor is in no class, so `∀ p. C` is provably
    false. That is the refutation this check needs: `isMember` never
    answers `some false` for a named class, so a merely-unknown
    successor would leave the conjunct unknown and prove nothing about
    the search order. -/
private def gIntersect : Graph :=
  [ ⟨indI, exP, strLit "v"⟩ ]

#guard runWork (isMember (st gIntersect) indI
         (.intersection [.named exC, .allOf exP (.named exD)]) 64) == some false

/-! The empty intersection is `owl:Thing`; the empty union is
    `owl:Nothing`. -/

#guard ask [] (.intersection []) == some true
#guard ask [] (.union []) == some false

/-! ## `⊔` does not stop at an unknown disjunct either -/

#guard runWork (isMember (st [⟨indI, rdfType, .iri exD⟩]) indI
         (.union [.named exC, .named exD]) 64) == some true

/-! ## Cardinality without a unique-name assumption

Two different IRIs may denote one individual, so a successor count is
a LOWER bound. `≥ k` may fire on it; `≤ k` may not, except in the
trivial case of `k = 0` with nothing seen. -/

private def gTwo : Graph :=
  [ ⟨indI, exP, .iri exY⟩, ⟨indI, exP, .iri exZ⟩ ]

#guard ask gTwo (.minCard 2 exP) == some true
#guard ask gTwo (.minCard 3 exP) == none

/-! `≤ 1` with two named successors is NOT provable: the two names
    may denote one individual. Answering `some false` here would
    assume unique names, which OWL does not. -/

#guard ask gTwo (.maxCard 1 exP) == none
#guard ask [] (.maxCard 0 exP) == some true
#guard ask gTwo (.maxCard 0 exP) == none

/-! ## A filler bound proves a maximum cardinality

`i` is in `∀ P. {y}`, so every `P`-filler of `i` is `y`. One
individual cannot be two distinct individuals, so `i` has at most one
DISTINCT `P`-filler — however many `P`-edges the graph asserts, and
whatever `owl:sameAs` does or does not say. This is entailment-sound
and needs no unique-name assumption, which is the exception the module
header records to "a positive maximum cardinality needs `owl:sameAs`
reasoning or a unique-name assumption". -/

private def gBound : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", rdfType, .iri owlRestriction⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlAllValuesFrom, bnT "o"⟩,
    ⟨bn "o", rdfType, .iri owlClass⟩,
    ⟨bn "o", owlOneOf, bnT "l"⟩,
    ⟨bn "l", rdfFirst, .iri exY⟩,
    ⟨bn "l", rdfRest, .iri rdfNil⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard ask gBound (.maxCard 1 exP) == some true
#guard ask gBound (.maxQualCard 1 exP (.named exC)) == some true

/-! A bound of `m` proves `≤ k` only for `k ≥ m`, so a bound of one
does not prove "at most zero". -/
#guard ask gBound (.maxCard 0 exP) == none

/-! ## ⚠️ The `k = 0` answers are NOT entailments

Recorded because `isMember` reads like an entailment oracle and is not
one for these two shapes. `maxCard 0` answers `some true` from an
EMPTY search, and `maxQualCard 0` answers `some true` when no
successor is PROVABLY in the filler. Under the open world assumption
neither is entailed: an unseen `P`-edge may exist, and `exY` may turn
out to be a `C`.

`cePositiveSound` is what keeps these out of the graph. They are
fenced off by the write gate, not by their own logic, so a caller that
reaches `isMember` directly gets them.
<https://github.com/danbri/factoidal/issues/236> -/

private def gUnknownFiller : Graph := [ ⟨indI, exP, .iri exY⟩ ]

#guard ask gUnknownFiller (.maxQualCard 0 exP (.named exC)) == some true
#guard !cePositiveSound (.maxQualCard 0 exP (.named exC))

/-! ## Qualified counting UNDER-counts

A successor whose membership in the filler is unknown does not count.
That is the direction that keeps `≥ k` sound. -/

private def gQual : Graph :=
  [ ⟨indI, exP, .iri exY⟩, ⟨.iri exY, rdfType, .iri exC⟩,
    ⟨indI, exP, .iri exZ⟩ ]

#guard ask gQual (.minQualCard 1 exP (.named exC)) == some true
#guard ask gQual (.minQualCard 2 exP (.named exC)) == none

/-! ## `owl:disjointWith` proves a complement, in either direction -/

private def gDisjoint : Graph :=
  [ ⟨indI, rdfType, .iri exD⟩, ⟨.iri exC, owlDisjointWith, .iri exD⟩ ]

private def gDisjointRev : Graph :=
  [ ⟨indI, rdfType, .iri exD⟩, ⟨.iri exD, owlDisjointWith, .iri exC⟩ ]

#guard ask gDisjoint (.complement (.named exC)) == some true
#guard ask gDisjointRev (.complement (.named exC)) == some true

/-! Without a disjoint witness a complement is unknown, not true.
    This is not classical negation. -/

#guard ask [] (.complement (.named exC)) == none

/-! ## `owl:oneOf` needs a syntactic match

`i` could be `owl:sameAs` a member without being spelled like one, so
a miss is unknown rather than false. -/

#guard ask [] (.oneOf [.iri exI]) == some true
#guard ask [] (.oneOf [.iri exY]) == none

/-! ## The positive-soundness gate

These are the shapes whose `some true` may be WRITTEN INTO the graph.
`∀`, the max/exact cardinalities and complement are excluded: their
`some true` is not entailed in every model. -/

#guard cePositiveSound (.named exC)
#guard cePositiveSound (.someOf exP (.named exC))
#guard cePositiveSound (.minCard 1 exP)
#guard cePositiveSound (.intersection [.named exC, .hasValue exP (.iri exY)])
#guard !cePositiveSound (.allOf exP (.named exC))
#guard !cePositiveSound (.maxCard 1 exP)
#guard !cePositiveSound (.exactCard 1 exP)
#guard !cePositiveSound (.complement (.named exC))
/-! The gate is structural: an excluded shape ANYWHERE inside a
    Boolean combination closes it. -/

#guard !cePositiveSound (.intersection [.named exC, .allOf exP (.named exD)])
#guard !cePositiveSound (.someOf exP (.maxCard 1 exP))

/-! ## Existential witnesses

`(i rdf:type B)` with `B` an `∃ p. C` obliges every model to give `i`
a `p`-successor in `C`. The RL closure is Datalog and cannot invent
one, so nothing downstream could see the obligation at all. -/

private def gWitness : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "r"⟩ ]

private def witnessed : Graph := introduceWitnesses gWitness

/-! Two triples are added: the edge and the witness's type. -/

#guard witnessed.length == gWitness.length + 2
#guard witnessed.any (fun t => t.s == indI && t.p == exP)
#guard witnessed.any (fun t => t.p == rdfType && t.o == .iri exC &&
                               match t.s with | .bnode _ => true | _ => false)

/-! The witness node is DETERMINISTIC, so a second pass mints nothing
    new. A fresh name each time would grow the graph without end. -/

#guard (introduceWitnesses witnessed).length == witnessed.length

/-! An obligation an existing successor already discharges mints no
    witness. -/
private def gDischarged : Graph :=
  gWitness ++ [⟨indI, exP, .iri exY⟩, ⟨.iri exY, rdfType, .iri exC⟩]

#guard (introduceWitnesses gDischarged).length == gDischarged.length

/-! ## The materialisation pass

A blank-node class expression gets its memberships written, and a
`(X owl:equivalentClass ⊓(A B))` gets `X ⊑ A` and `X ⊑ B` on the
NAMED side. -/

private def gMat : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard (materialise gMat).any (fun t =>
  t.s == indI && t.p == rdfType && t.o == bnT "r")

private def gEqc : Graph :=
  [ ⟨.iri exC, owlEquivalentClass, bnT "i"⟩,
    ⟨bn "i", owlIntersectionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exD⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exE⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard (materialise gEqc).contains ⟨.iri exC, rdfsSubClassOf, .iri exD⟩
#guard (materialise gEqc).contains ⟨.iri exC, rdfsSubClassOf, .iri exE⟩

/-! The subclass axiom lands on the NAMED side. Putting it on the
    anonymous intersection node would make that node an answer to
    `?C rdfs:subClassOf <D>` — a spurious anonymous class in the
    result rows. -/

#guard !((materialise gEqc).contains ⟨bn "i", rdfsSubClassOf, .iri exD⟩)

/-! ## A NAMED class expression, behind the gate

`z owl:onProperty p ; owl:someValuesFrom C` denotes that class even
when `z` is an IRI. The blank-node pass never looks at it, and
`parseClassExpr` maps every IRI straight to `named`, so without
`parseCeOfSubject` this membership is never written. -/

private def gNamedCe : Graph :=
  [ ⟨.iri exD, owlOnProperty, .iri exP⟩,
    ⟨.iri exD, owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard (materialise gNamedCe).contains ⟨indI, rdfType, .iri exD⟩

/-! The same shape with `owl:allValuesFrom` writes NOTHING: an unseen
    successor could violate the filler, so the membership is not
    entailed. -/
private def gNamedAll : Graph :=
  [ ⟨.iri exD, owlOnProperty, .iri exP⟩,
    ⟨.iri exD, owlAllValuesFrom, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard !((materialise gNamedAll).contains ⟨indI, rdfType, .iri exD⟩)

/-! ## `entails` leaves named classes to the closure -/

#guard entails [⟨indI, rdfType, .iri exC⟩] ⟨indI, rdfType, .iri exC⟩ == some true
#guard entails [] ⟨indI, rdfType, .iri exC⟩ == none
#guard entails gMat ⟨indI, rdfType, bnT "r"⟩ == some true



/-! ## A witness is withheld where it could breach a bound

The pass writes its witness INTO the graph, and the RL clash
detector downstream counts blank nodes like any other name. On
`WebOnt-description-logic-018` / `-020` / `-021` — three premises
the catalog asserts CONSISTENT — that counted witness fired the
clash detector against a bound the individual's real successors do
not exceed. Withholding the witness where a bound could be breached
is sound: a withheld witness only loses labels. -/

private def gBoundedWitness : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    ⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard (introduceWitnesses gBoundedWitness).length == gBoundedWitness.length

/-! Drop the functional declaration and the same graph mints one —
the withholding is the bound, not the successor. -/

private def gUnboundedWitness : Graph :=
  gBoundedWitness.filter (fun t => t.o != Term.iri owlFunctionalProperty)

#guard (introduceWitnesses gUnboundedWitness).length > gUnboundedWitness.length

end L4Factoidal.OWL.Mat
