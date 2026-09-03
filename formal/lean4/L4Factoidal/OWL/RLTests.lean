/-
L4Factoidal.OWL.RLTests — `#guard` checks for the OWL 2 RL/RDF closure
and clash detector. They run at build time, so a green `lake build` is
also a green test run.

WHAT THESE ARE NOT. They are not a conformance score. There is no
manifest reader and no RDF/XML parser on the Lean side, so the W3C OWL
2 test corpus (which is RDF/XML throughout, manifests included) is not
read here — see `Harness/OwlProbe.lean` for the measured statement
about that corpus, and iron rule #6 for why hand-written fixtures never
substitute for it.

WHAT THEY DO CHECK, and why each check is paired. Every family below
asserts BOTH something the closure DERIVES and something it does NOT —
the `measuring-inference` discipline: a closure test that only asserts
presence passes just as happily when the rule never fired and the
triple was in the input, and a closure that derived EVERYTHING would
pass every positive check ever written. The negative half is what makes
the positive half evidence.

Fuel: the checks pass a small explicit fuel rather than `closureFix`.
`closureFuelBound` is a worst-case bound (cubic in the graph size) and
spending it inside a kernel-reduced `#guard` is pointless work; the
fixtures here saturate in two or three rounds, and the idempotence
checks pin that.
-/
import L4Factoidal.OWL.RLTheorems
import L4Factoidal.OWL.RLClosureIndexed

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## Fixture vocabulary -/

private def cA : WfIri := ⟨"http://ex/A", rfl⟩
private def cB : WfIri := ⟨"http://ex/B", rfl⟩
private def cC : WfIri := ⟨"http://ex/C", rfl⟩
private def cD : WfIri := ⟨"http://ex/D", rfl⟩
private def pP : WfIri := ⟨"http://ex/p", rfl⟩
private def pQ : WfIri := ⟨"http://ex/q", rfl⟩
private def pR : WfIri := ⟨"http://ex/r", rfl⟩
private def iX : WfIri := ⟨"http://ex/x", rfl⟩
private def iY : WfIri := ⟨"http://ex/y", rfl⟩
private def iZ : WfIri := ⟨"http://ex/z", rfl⟩
private def iW : WfIri := ⟨"http://ex/w", rfl⟩

/-- A subject in IRI form. -/
private def S (i : WfIri) : Subject := Subject.iri i
/-- A term in IRI form. -/
private def O (i : WfIri) : Term := Term.iri i

/-- Does the closure of `g` at this fuel hold `t`? -/
private def derives (g : Graph) (fuel : Nat) (t : Triple) : Bool :=
  memB (closure g fuel) t

/-! ## Table 4, family 1 — equality

eq-ref makes every subject, predicate and object of the input
`owl:sameAs` itself; eq-sym, eq-trans and the three eq-rep-* rows then
move facts along a sameAs edge. -/

private def gEq : Graph :=
  [⟨S iX, owlSameAs, O iY⟩,
   ⟨S iX, pP, O iZ⟩]

-- eq-ref: reflexive sameAs on a subject, a predicate and an object.
#guard derives gEq 2 ⟨S iX, owlSameAs, O iX⟩
#guard derives gEq 2 ⟨S pP, owlSameAs, O pP⟩
#guard derives gEq 2 ⟨S iZ, owlSameAs, O iZ⟩
-- eq-sym.
#guard derives gEq 2 ⟨S iY, owlSameAs, O iX⟩
-- eq-trans (through the eq-ref reflexive edge on y).
#guard derives gEq 3 ⟨S iX, owlSameAs, O iY⟩
-- eq-rep-s: the p-edge moves from x to y.
#guard derives gEq 2 ⟨S iY, pP, O iZ⟩
-- eq-rep-o: an edge INTO x also reaches y.
#guard derives (⟨S iW, pQ, O iX⟩ :: gEq) 2 ⟨S iW, pQ, O iY⟩
-- eq-rep-p: a sameAs between two PROPERTY IRIs re-asserts under the
-- second name.
#guard derives [⟨S pP, owlSameAs, O pQ⟩, ⟨S iX, pP, O iZ⟩] 2
  ⟨S iX, pQ, O iZ⟩
-- NEGATIVE: sameAs does not invent an edge that never existed.
#guard !derives gEq 3 ⟨S iY, pQ, O iZ⟩
-- NEGATIVE: nothing relates two unrelated individuals.
#guard !derives gEq 3 ⟨S iZ, owlSameAs, O iY⟩

/-! ## Table 4, family 2 — property axioms -/

-- prp-trp: transitivity closes a two-step chain, and only that.
private def gTrp : Graph :=
  [⟨S pP, rdfType, O owlTransitiveProperty⟩,
   ⟨S iX, pP, O iY⟩,
   ⟨S iY, pP, O iZ⟩]

#guard derives gTrp 2 ⟨S iX, pP, O iZ⟩
#guard !derives gTrp 3 ⟨S iZ, pP, O iX⟩
#guard !derives gTrp 3 ⟨S iX, pQ, O iZ⟩

-- prp-symp.
private def gSymp : Graph :=
  [⟨S pP, rdfType, O owlSymmetricProperty⟩, ⟨S iX, pP, O iY⟩]

#guard derives gSymp 2 ⟨S iY, pP, O iX⟩
#guard !derives gSymp 3 ⟨S iY, pQ, O iX⟩

-- prp-inv1 / prp-inv2.
private def gInv : Graph :=
  [⟨S pP, owlInverseOf, O pQ⟩, ⟨S iX, pP, O iY⟩, ⟨S iZ, pQ, O iW⟩]

#guard derives gInv 2 ⟨S iY, pQ, O iX⟩
#guard derives gInv 2 ⟨S iW, pP, O iZ⟩
#guard !derives gInv 3 ⟨S iX, pQ, O iY⟩

-- prp-fp: a functional property makes two objects of one subject the
-- same; two objects of DIFFERENT subjects stay distinct.
private def gFp : Graph :=
  [⟨S pP, rdfType, O owlFunctionalProperty⟩,
   ⟨S iX, pP, O iY⟩,
   ⟨S iX, pP, O iZ⟩,
   ⟨S iW, pP, O cD⟩]

#guard derives gFp 2 ⟨S iY, owlSameAs, O iZ⟩
#guard !derives gFp 2 ⟨S iY, owlSameAs, O cD⟩

-- prp-ifp: an inverse-functional property makes two subjects sharing an
-- object the same.
private def gIfp : Graph :=
  [⟨S pP, rdfType, O owlInverseFunctionalProperty⟩,
   ⟨S iX, pP, O iZ⟩,
   ⟨S iY, pP, O iZ⟩,
   ⟨S iW, pP, O cD⟩]

#guard derives gIfp 2 ⟨S iX, owlSameAs, O iY⟩
#guard !derives gIfp 2 ⟨S iX, owlSameAs, O iW⟩

-- prp-dom / prp-rng.
private def gDomRng : Graph :=
  [⟨S pP, rdfsDomain, O cA⟩, ⟨S pP, rdfsRange, O cB⟩, ⟨S iX, pP, O iY⟩]

#guard derives gDomRng 2 ⟨S iX, rdfType, O cA⟩
#guard derives gDomRng 2 ⟨S iY, rdfType, O cB⟩
#guard !derives gDomRng 2 ⟨S iX, rdfType, O cB⟩

-- prp-spo1 and its Table 8 sibling scm-spo (transitivity of the
-- property hierarchy).
private def gSpo : Graph :=
  [⟨S pP, rdfsSubPropertyOf, O pQ⟩,
   ⟨S pQ, rdfsSubPropertyOf, O pR⟩,
   ⟨S iX, pP, O iY⟩]

#guard derives gSpo 2 ⟨S iX, pQ, O iY⟩
#guard derives gSpo 2 ⟨S pP, rdfsSubPropertyOf, O pR⟩
#guard derives gSpo 3 ⟨S iX, pR, O iY⟩
#guard !derives gSpo 3 ⟨S pR, rdfsSubPropertyOf, O pP⟩

-- prp-eqp1 / prp-eqp2.
private def gEqp : Graph :=
  [⟨S pP, owlEquivalentProperty, O pQ⟩, ⟨S iX, pP, O iY⟩,
   ⟨S iZ, pQ, O iW⟩]

#guard derives gEqp 2 ⟨S iX, pQ, O iY⟩
#guard derives gEqp 2 ⟨S iZ, pP, O iW⟩
#guard !derives gEqp 2 ⟨S iX, pR, O iY⟩

/-! ## Table 5 — classes, including the collection-valued rows -/

-- cls-int1 over a THREE-member list: an individual typed into all three
-- members gets typed into the intersection; one that misses a member
-- does not.
private def lst3 : Graph :=
  [⟨.bnode "l1", rdfFirst, O cA⟩, ⟨.bnode "l1", rdfRest, .bnode "l2"⟩,
   ⟨.bnode "l2", rdfFirst, O cB⟩, ⟨.bnode "l2", rdfRest, .bnode "l3"⟩,
   ⟨.bnode "l3", rdfFirst, O cC⟩, ⟨.bnode "l3", rdfRest, O rdfNil⟩]

private def gInt : Graph :=
  ⟨S cD, owlIntersectionOf, .bnode "l1"⟩ ::
  ⟨S iX, rdfType, O cA⟩ :: ⟨S iX, rdfType, O cB⟩ ::
  ⟨S iX, rdfType, O cC⟩ ::
  ⟨S iY, rdfType, O cA⟩ :: ⟨S iY, rdfType, O cB⟩ :: lst3

#guard derives gInt 2 ⟨S iX, rdfType, O cD⟩
#guard !derives gInt 2 ⟨S iY, rdfType, O cD⟩
-- cls-int2 and scm-int run the other way: membership of the
-- intersection gives membership of every member.
#guard derives gInt 2 ⟨S cD, rdfsSubClassOf, O cA⟩
#guard derives gInt 2 ⟨S cD, rdfsSubClassOf, O cC⟩
#guard !derives gInt 2 ⟨S cD, rdfsSubClassOf, O pP⟩

-- cls-uni and scm-uni over a two-member union.
private def lst2 : Graph :=
  [⟨.bnode "u1", rdfFirst, O cA⟩, ⟨.bnode "u1", rdfRest, .bnode "u2"⟩,
   ⟨.bnode "u2", rdfFirst, O cB⟩, ⟨.bnode "u2", rdfRest, O rdfNil⟩]

private def gUni : Graph :=
  ⟨S cD, owlUnionOf, .bnode "u1"⟩ :: ⟨S iX, rdfType, O cB⟩ :: lst2

#guard derives gUni 2 ⟨S iX, rdfType, O cD⟩
#guard derives gUni 2 ⟨S cA, rdfsSubClassOf, O cD⟩
#guard derives gUni 2 ⟨S cB, rdfsSubClassOf, O cD⟩
#guard !derives gUni 2 ⟨S cD, rdfsSubClassOf, O cA⟩
#guard !derives gUni 2 ⟨S iX, rdfType, O cC⟩

-- cls-svf1: an x with a p-edge to a member of the qualifying class is
-- a member of the someValuesFrom restriction.
private def gSvf : Graph :=
  [⟨.bnode "R", owlSomeValuesFrom, O cB⟩,
   ⟨.bnode "R", owlOnProperty, O pP⟩,
   ⟨S iX, pP, O iY⟩, ⟨S iY, rdfType, O cB⟩,
   ⟨S iZ, pP, O iW⟩]

#guard derives gSvf 2 ⟨S iX, rdfType, .bnode "R"⟩
#guard !derives gSvf 2 ⟨S iZ, rdfType, .bnode "R"⟩

-- cls-avf: every p-value of a member of an allValuesFrom restriction
-- is typed into the qualifying class.
private def gAvf : Graph :=
  [⟨.bnode "R", owlAllValuesFrom, O cB⟩,
   ⟨.bnode "R", owlOnProperty, O pP⟩,
   ⟨S iX, rdfType, .bnode "R"⟩,
   ⟨S iX, pP, O iY⟩,
   ⟨S iZ, pP, O iW⟩]

#guard derives gAvf 2 ⟨S iY, rdfType, O cB⟩
#guard !derives gAvf 2 ⟨S iW, rdfType, O cB⟩

-- cls-hv1 / cls-hv2.
private def gHv : Graph :=
  [⟨.bnode "R", owlHasValue, O iY⟩,
   ⟨.bnode "R", owlOnProperty, O pP⟩,
   ⟨S iX, rdfType, .bnode "R"⟩,
   ⟨S iZ, pP, O iY⟩]

#guard derives gHv 2 ⟨S iX, pP, O iY⟩
#guard derives gHv 2 ⟨S iZ, rdfType, .bnode "R"⟩
#guard !derives gHv 2 ⟨S iX, pP, O iW⟩

-- cls-hs1 / cls-hs2: a self-restriction on pP types its members into a
-- pP-loop, and a pP-loop types its subject into the restriction.
private def gHs : Graph :=
  [⟨.bnode "R", owlHasSelf, .literal litTrueBoolean⟩,
   ⟨.bnode "R", owlOnProperty, O pP⟩,
   ⟨S iX, rdfType, .bnode "R"⟩,
   ⟨S iZ, pP, O iZ⟩,
   ⟨S iY, pP, O iW⟩]

#guard derives gHs 2 ⟨S iX, pP, O iX⟩
#guard derives gHs 2 ⟨S iZ, rdfType, .bnode "R"⟩
#guard !derives gHs 2 ⟨S iY, rdfType, .bnode "R"⟩

/-! ## Table 6 and Table 8 — class axioms and schema vocabulary -/

-- cax-sco, plus scm-sco (transitivity of the class hierarchy).
private def gSco : Graph :=
  [⟨S cA, rdfsSubClassOf, O cB⟩,
   ⟨S cB, rdfsSubClassOf, O cC⟩,
   ⟨S iX, rdfType, O cA⟩]

#guard derives gSco 2 ⟨S iX, rdfType, O cB⟩
#guard derives gSco 2 ⟨S cA, rdfsSubClassOf, O cC⟩
#guard derives gSco 3 ⟨S iX, rdfType, O cC⟩
#guard !derives gSco 3 ⟨S cC, rdfsSubClassOf, O cA⟩
#guard !derives gSco 3 ⟨S iX, rdfType, O cD⟩

-- cax-eqc1 / cax-eqc2, and scm-eqc1 turning equivalence into two
-- subClassOf edges.
private def gEqc : Graph :=
  [⟨S cA, owlEquivalentClass, O cB⟩,
   ⟨S iX, rdfType, O cA⟩, ⟨S iY, rdfType, O cB⟩]

#guard derives gEqc 2 ⟨S iX, rdfType, O cB⟩
#guard derives gEqc 2 ⟨S iY, rdfType, O cA⟩
#guard derives gEqc 2 ⟨S cA, rdfsSubClassOf, O cB⟩
#guard derives gEqc 2 ⟨S cB, rdfsSubClassOf, O cA⟩
#guard !derives gEqc 2 ⟨S iX, rdfType, O cC⟩

-- scm-eqc2 runs the other way: mutual subClassOf gives
-- equivalentClass.
#guard derives [⟨S cA, rdfsSubClassOf, O cB⟩, ⟨S cB, rdfsSubClassOf, O cA⟩] 2
  ⟨S cA, owlEquivalentClass, O cB⟩
#guard !derives [⟨S cA, rdfsSubClassOf, O cB⟩] 2
  ⟨S cA, owlEquivalentClass, O cB⟩

-- scm-cls: a named class is its own subclass and equivalent, is under
-- owl:Thing, and is over owl:Nothing.
private def gCls : Graph := [⟨S cA, rdfType, O owlClass⟩]

#guard derives gCls 2 ⟨S cA, rdfsSubClassOf, O cA⟩
#guard derives gCls 2 ⟨S cA, owlEquivalentClass, O cA⟩
#guard derives gCls 2 ⟨S cA, rdfsSubClassOf, O owlThing⟩
#guard derives gCls 2 ⟨S owlNothing, rdfsSubClassOf, O cA⟩
#guard !derives gCls 2 ⟨S cA, rdfsSubClassOf, O owlNothing⟩

-- cls-thing / cls-nothing1 are premise-free rows: they hold of the
-- EMPTY graph, and nothing else does.
#guard derives [] 2 ⟨S owlThing, rdfType, O owlClass⟩
#guard derives [] 2 ⟨S owlNothing, rdfType, O owlClass⟩
#guard !derives [] 2 ⟨S cA, rdfType, O owlClass⟩

-- scm-dom1 / scm-dom2 / scm-rng1 / scm-rng2.
private def gDomProp : Graph :=
  [⟨S pQ, rdfsDomain, O cA⟩, ⟨S cA, rdfsSubClassOf, O cB⟩,
   ⟨S pP, rdfsSubPropertyOf, O pQ⟩]

#guard derives gDomProp 2 ⟨S pQ, rdfsDomain, O cB⟩
#guard derives gDomProp 2 ⟨S pP, rdfsDomain, O cA⟩
#guard !derives gDomProp 3 ⟨S pQ, rdfsDomain, O cC⟩

private def gRngProp : Graph :=
  [⟨S pQ, rdfsRange, O cA⟩, ⟨S cA, rdfsSubClassOf, O cB⟩,
   ⟨S pP, rdfsSubPropertyOf, O pQ⟩]

#guard derives gRngProp 2 ⟨S pQ, rdfsRange, O cB⟩
#guard derives gRngProp 2 ⟨S pP, rdfsRange, O cA⟩
#guard !derives gRngProp 3 ⟨S pQ, rdfsRange, O cC⟩

/-! ## Clash rows

`inconsistent g fuel` closes first and then looks for a no-consequent
row, which is what makes the disjointness clashes visible at all: the
`rdf:type` premises usually arrive by cax-sco. -/

-- cax-dw: two disjoint classes with a shared instance.
private def gDw : Graph :=
  [⟨S cA, owlDisjointWith, O cB⟩,
   ⟨S iX, rdfType, O cA⟩, ⟨S iX, rdfType, O cB⟩]

#guard detectClash gDw
#guard inconsistent gDw 2
-- and the same declaration with the instance in only one class is
-- consistent.
#guard !inconsistent
  [⟨S cA, owlDisjointWith, O cB⟩, ⟨S iX, rdfType, O cA⟩] 2

-- cax-dw reached only after cax-sco has run.
#guard inconsistent
  [⟨S cA, owlDisjointWith, O cB⟩, ⟨S cC, rdfsSubClassOf, O cB⟩,
   ⟨S iX, rdfType, O cA⟩, ⟨S iX, rdfType, O cC⟩] 2

-- prp-irp: an irreflexive property with a self-loop.
#guard detectClash
  [⟨S pP, rdfType, O owlIrreflexiveProperty⟩, ⟨S iX, pP, O iX⟩]
#guard !detectClash
  [⟨S pP, rdfType, O owlIrreflexiveProperty⟩, ⟨S iX, pP, O iY⟩]

-- prp-asyp: an asymmetric property with both directions asserted.
#guard detectClash
  [⟨S pP, rdfType, O owlAsymmetricProperty⟩,
   ⟨S iX, pP, O iY⟩, ⟨S iY, pP, O iX⟩]
#guard !detectClash
  [⟨S pP, rdfType, O owlAsymmetricProperty⟩, ⟨S iX, pP, O iY⟩]

-- eq-diff1: the same pair both same and different.
#guard detectClash
  [⟨S iX, owlSameAs, O iY⟩, ⟨S iX, owlDifferentFrom, O iY⟩]
#guard !detectClash [⟨S iX, owlDifferentFrom, O iY⟩]

-- prp-pdw: disjoint properties sharing a subject-object pair.
#guard detectClash
  [⟨S pP, owlPropertyDisjointWith, O pQ⟩,
   ⟨S iX, pP, O iY⟩, ⟨S iX, pQ, O iY⟩]
#guard !detectClash
  [⟨S pP, owlPropertyDisjointWith, O pQ⟩,
   ⟨S iX, pP, O iY⟩, ⟨S iX, pQ, O iZ⟩]

-- cls-nothing2 and cls-com.
#guard detectClash [⟨S iX, rdfType, O owlNothing⟩]
#guard detectClash
  [⟨S cA, owlComplementOf, O cB⟩,
   ⟨S iX, rdfType, O cA⟩, ⟨S iX, rdfType, O cB⟩]

-- A graph with no clash row satisfied is consistent, closure and all.
#guard !inconsistent gSco 3
#guard !inconsistent gInt 2
#guard !detectClash []

/-! ## Idempotence

Running the loop past saturation changes nothing. `closure g n` at a
fuel the fixture has already saturated under equals `closure g (n+k)`
for every k — the length test in `closure` is what makes that hold, and
`RLTheorems.step_eq_of_length_eq` is why the test is exact. -/

#guard closure gSco 4 == closure gSco 5
#guard closure gSco 4 == closure gSco 8
#guard closure gTrp 4 == closure gTrp 6
#guard closure gEq 4 == closure gEq 6
#guard closure gUni 4 == closure gUni 6
#guard (closure gSco 4).length == (step (closure gSco 4)).length

/-! ## The indexed engine computes the same list

`RLClosureIndexed.indexedClosure_eq` proves `indexedClosure g fuel =
closure g fuel` for every graph and fuel; these guards evaluate both
engines on the fixtures above and compare the LISTS (order included),
so a build also exercises the compiled `Std.HashMap` path the proof
reasons about abstractly. The clash verdict is compared the same way. -/

#guard indexedClosure gEq 4 == closure gEq 4
#guard indexedClosure gTrp 4 == closure gTrp 4
#guard indexedClosure gSymp 3 == closure gSymp 3
#guard indexedClosure gInv 3 == closure gInv 3
#guard indexedClosure gFp 3 == closure gFp 3
#guard indexedClosure gIfp 3 == closure gIfp 3
#guard indexedClosure gDomRng 3 == closure gDomRng 3
#guard indexedClosure gSpo 3 == closure gSpo 3
#guard indexedClosure gEqp 3 == closure gEqp 3
#guard indexedClosure gInt 3 == closure gInt 3
#guard indexedClosure gUni 3 == closure gUni 3
#guard indexedClosure gSvf 3 == closure gSvf 3
#guard indexedClosure gAvf 3 == closure gAvf 3
#guard indexedClosure gHv 3 == closure gHv 3
#guard indexedClosure gSco 4 == closure gSco 4
#guard indexedClosure gEqc 3 == closure gEqc 3
#guard indexedClosure gCls 3 == closure gCls 3
#guard indexedClosure gDomProp 3 == closure gDomProp 3
#guard indexedClosure gRngProp 3 == closure gRngProp 3
#guard indexedClosure gDw 3 == closure gDw 3
#guard indexedClosure [] 3 == closure [] 3
-- A duplicate in the input survives in both (the index pictures the
-- list, duplicates and all).
#guard indexedClosure (gSco ++ gSco) 4 == closure (gSco ++ gSco) 4
#guard detectClashI (closureI (Index.ofGraph gDw) 3) == inconsistent gDw 3
#guard detectClashI (closureI (Index.ofGraph gSco) 3) == inconsistent gSco 3
#guard detectClashI (Index.ofGraph
  [⟨S iX, owlSameAs, O iY⟩, ⟨S iX, owlDifferentFrom, O iY⟩]) == true

end L4Factoidal.OWL.RL
