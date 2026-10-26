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

private def searchResult (g : Graph) (budget : Nat) : Verdict × Nat :=
  let tb := collectAxioms g
  search tb g { initState g with tbox := tb } budget

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

/-! Generated witnesses are fresh under arbitrary input blank-node
names. Alpha-renaming an unrelated node to the old generated-name
pattern cannot pool its `not C` label with the `∃p.C` witness. Adding
`∀p.not C` makes the same existential genuinely inconsistent. -/
private def collidingWitness : BNodeId := witnessId indI exP 0

private def gWitnessNameCollision (constrained : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "fresh-some"⟩,
    ⟨bn "fresh-some", owlOnProperty, .iri exP⟩,
    ⟨bn "fresh-some", owlSomeValuesFrom, .iri exC⟩,
    ⟨.bnode collidingWitness, rdfType, bnT "fresh-not-c"⟩,
    ⟨bn "fresh-not-c", owlComplementOf, .iri exC⟩ ] ++
  if constrained then
    [ ⟨indI, rdfType, bnT "fresh-all"⟩,
      ⟨bn "fresh-all", owlOnProperty, .iri exP⟩,
      ⟨bn "fresh-all", owlAllValuesFrom, bnT "fresh-not-c"⟩ ]
  else []

#guard tableauConsistent (gWitnessNameCollision false) fuel == some true
#guard tableauConsistent (gWitnessNameCollision true) fuel == some false

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

/-! The total search keeps the old depth-first order and one shared
budget pool. The root and each visited disjunct consume one unit. -/
#guard searchResult gUnionBothBad 0 == (.out, 0)
#guard searchResult gUnionBothBad 2 == (.out, 0)
#guard searchResult gUnionBothBad 3 == (.clash, 0)
#guard searchResult gUnionBothBad 8 == (.clash, 5)
#guard searchResult gUnionOneGood 3 == (.open', 0)

/-! ## Deterministic union propagation -/

private def gForcedUnion (alsoNotD : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "forced-u"⟩,
    ⟨bn "forced-u", owlUnionOf, bnT "forced-u-1"⟩,
    ⟨bn "forced-u-1", rdfFirst, .iri exC⟩,
    ⟨bn "forced-u-1", rdfRest, bnT "forced-u-2"⟩,
    ⟨bn "forced-u-2", rdfFirst, .iri exD⟩,
    ⟨bn "forced-u-2", rdfRest, .iri rdfNil⟩,
    ⟨indI, rdfType, bnT "forced-not-c"⟩,
    ⟨bn "forced-not-c", owlComplementOf, .iri exC⟩ ] ++
  if alsoNotD then
    [ ⟨indI, rdfType, bnT "forced-not-d"⟩,
      ⟨bn "forced-not-d", owlComplementOf, .iri exD⟩ ]
  else []

#guard tableauConsistent (gForcedUnion false) fuel == some true
#guard tableauConsistent (gForcedUnion true) fuel == some false
#guard !(unionChoiceContradicted .unknown [.complement .unknown])
#guard ClassExpr.beqList
  (liveUnionChoices [.named exC, .named exD, .named exY]
    [.complement (.named exD)])
  [.named exC, .named exY]
#guard clashNodes [] { nodes := [{ id := indI, labels := [.union []] }] }

private def wideForcedUnionState (n : Nat) : RState :=
  { nodes := (List.range n).map (fun i =>
      { id := .bnode ("forced-union-" ++ toString i),
        labels := [.union [.named exC, .named exD],
                   .complement (.named exC)] }) }

private def forcedUnionPasses (n : Nat) : Bool :=
  let (st, changed) := onePass [] [] (wideForcedUnionState n)
  changed && st.nodes.all (fun node => memCe (.named exD) node.labels)

#guard forcedUnionPasses 100
#guard forcedUnionPasses 500
#guard forcedUnionPasses 1000

/-! ## Nominal identification and named class definitions -/

private def exK : WfIri := ⟨"http://e/K", rfl⟩

/-! The first nominal choice clashes after `i = y`; the second choice
`i = z` stays open. Adding `z : C` closes both choices. -/
private def gNominalChoice (zInC : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "nom"⟩,
    ⟨bn "nom", owlOneOf, bnT "nm1"⟩,
    ⟨bn "nm1", rdfFirst, .iri exY⟩, ⟨bn "nm1", rdfRest, bnT "nm2"⟩,
    ⟨bn "nm2", rdfFirst, .iri exZ⟩, ⟨bn "nm2", rdfRest, .iri rdfNil⟩,
    ⟨indI, rdfType, bnT "notC-nom"⟩,
    ⟨bn "notC-nom", owlComplementOf, .iri exC⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ] ++
  if zInC then [⟨.iri exZ, rdfType, .iri exC⟩] else []

#guard tableauConsistent (gNominalChoice false) fuel == some true
#guard tableauConsistent (gNominalChoice true) fuel == some false

/-! Forced equalities are collected in node and label order. The
batch closes a two-link equality cascade within two state visits;
without the final positive label the same cascade remains open. -/
private def forcedNominalCascadeState (contradiction : Bool) : RState :=
  { nodes :=
      [ { id := indI,
          labels := [.oneOf [.iri exY], .complement (.named exC)] },
        { id := .iri exY, labels := [.oneOf [.iri exZ]] },
        { id := .iri exZ,
          labels := if contradiction then [.named exC] else [] } ] }

#guard forcedNominalPairs [] (forcedNominalCascadeState false) ==
  [(indI.toTerm, .iri exY), (.iri exY, .iri exZ)]
#guard search [] [] (forcedNominalCascadeState false) 2 == (.open', 0)
#guard search [] [] (forcedNominalCascadeState true) 2 == (.clash, 0)

/-! Candidate collection is a fold, so a wide nominal does not consume
one native stack frame per member. These guards also pin the exact
source-order cardinality at n/2n/4n. -/
private def wideNominalState (n : Nat) : RState :=
  { nodes := [{ id := indI,
                labels := [.oneOf (List.replicate n (.iri exY))] }] }

#guard (pendingNominal [] (wideNominalState 1000)).map List.length == some 1000
#guard (pendingNominal [] (wideNominalState 2000)).map List.length == some 2000
#guard (pendingNominal [] (wideNominalState 4000)).map List.length == some 4000

private def wideForcedNominalBatchState (n : Nat) : RState :=
  { nodes := (List.range n).map (fun i =>
      { id := .bnode ("forced-batch-" ++ toString i),
        labels := [.oneOf [.bnode ("forced-member-" ++ toString i)]] }) }

private def forcedNominalBatchCount (n : Nat) : Nat :=
  (propagateForcedNominals [] (wideForcedNominalBatchState n)).ident.length

#guard forcedNominalBatchCount 25 == 25
#guard forcedNominalBatchCount 50 == 50
#guard forcedNominalBatchCount 100 == 100

/-! Grouped distinctness sees through an intermediate alias. Without
`i differentFrom z`, the two singleton choices can identify all three
names; with it, the second identification is impossible. -/
private def gNominalAlias (apart : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "iy"⟩,
    ⟨bn "iy", owlOneOf, bnT "iy-list"⟩,
    ⟨bn "iy-list", rdfFirst, .iri exY⟩,
    ⟨bn "iy-list", rdfRest, .iri rdfNil⟩,
    ⟨.iri exY, rdfType, bnT "yz"⟩,
    ⟨bn "yz", owlOneOf, bnT "yz-list"⟩,
    ⟨bn "yz-list", rdfFirst, .iri exZ⟩,
    ⟨bn "yz-list", rdfRest, .iri rdfNil⟩ ] ++
  if apart then [⟨indI, owlDifferentFrom, .iri exZ⟩] else []

#guard tableauConsistent (gNominalAlias false) fuel == some true
#guard tableauConsistent (gNominalAlias true) fuel == some false

/-! A live literal member makes the whole nominal choice unavailable.
The resource branch alone clashes, so exploring only that branch would
manufacture a refutation. -/
private def gNominalLiteral : Graph :=
  [ ⟨indI, rdfType, bnT "nl"⟩,
    ⟨bn "nl", owlOneOf, bnT "nl1"⟩,
    ⟨bn "nl1", rdfFirst, .iri exY⟩, ⟨bn "nl1", rdfRest, bnT "nl2"⟩,
    ⟨bn "nl2", rdfFirst, cardLit "7"⟩, ⟨bn "nl2", rdfRest, .iri rdfNil⟩,
    ⟨indI, rdfType, bnT "notC-lit"⟩,
    ⟨bn "notC-lit", owlComplementOf, .iri exC⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard tableauConsistent gNominalLiteral fuel == some true

/-! Every named `oneOf` marker contributes an equivalence. The two
singleton definitions force `y = z`; their asserted difference closes
the graph. Removing it leaves a model. -/
private def gNamedOneOfs (apart : Bool) : Graph :=
  [ ⟨.iri exK, owlOneOf, bnT "ky"⟩,
    ⟨bn "ky", rdfFirst, .iri exY⟩, ⟨bn "ky", rdfRest, .iri rdfNil⟩,
    ⟨.iri exK, owlOneOf, bnT "kz"⟩,
    ⟨bn "kz", rdfFirst, .iri exZ⟩, ⟨bn "kz", rdfRest, .iri rdfNil⟩ ] ++
  if apart then [⟨.iri exY, owlDifferentFrom, .iri exZ⟩] else []

#guard tableauConsistent (gNamedOneOfs false) fuel == some true
#guard tableauConsistent (gNamedOneOfs true) fuel == some false

/-! The empty enumeration denotes the empty class. Its declaration is
satisfiable; asserting a member is not. -/
private def gEmptyNamedOneOf : Graph :=
  [⟨.iri exK, owlOneOf, .iri rdfNil⟩]

#guard tableauConsistent gEmptyNamedOneOf fuel == some true
#guard tableauConsistent (gEmptyNamedOneOf ++ [⟨indI, rdfType, .iri exK⟩]) fuel
       == some false

/-! An unterminated list is withheld. Treating its readable prefix as
the complete singleton would conflict with `i differentFrom y`. -/
private def gTruncatedNamedOneOf : Graph :=
  [ ⟨.iri exK, owlOneOf, bnT "broken"⟩,
    ⟨bn "broken", rdfFirst, .iri exY⟩,
    ⟨indI, rdfType, .iri exK⟩,
    ⟨indI, owlDifferentFrom, .iri exY⟩ ]

#guard tableauConsistent gTruncatedNamedOneOf fuel == some true

/-! Named Boolean markers are equivalences. Their contrapositives let
`not K` expose the negated operands, and a disjoint union also makes
its operands pairwise disjoint. -/
private def namedBooleanList (marker : WfIri) : Graph :=
  [ ⟨.iri exK, marker, bnT "kb1"⟩,
    ⟨bn "kb1", rdfFirst, .iri exC⟩, ⟨bn "kb1", rdfRest, bnT "kb2"⟩,
    ⟨bn "kb2", rdfFirst, .iri exD⟩, ⟨bn "kb2", rdfRest, .iri rdfNil⟩ ]

private def notNamed (b : String) (c : WfIri) : Graph :=
  [⟨indI, rdfType, .bnode b⟩, ⟨.bnode b, owlComplementOf, .iri c⟩]

#guard refuted (namedBooleanList owlUnionOf ++
  [⟨indI, rdfType, .iri exK⟩] ++ notNamed "nu-c" exC ++ notNamed "nu-d" exD)
#guard refuted (namedBooleanList owlIntersectionOf ++
  [⟨indI, rdfType, .iri exK⟩] ++ notNamed "ni-c" exC)
#guard refuted (namedBooleanList owlUnionOf ++
  notNamed "nu-k" exK ++ [⟨indI, rdfType, .iri exC⟩])
#guard refuted (namedBooleanList owlDisjointUnionOf ++
  [⟨indI, rdfType, .iri exC⟩, ⟨indI, rdfType, .iri exD⟩])

/-! Pairwise disjointness necessarily emits quadratic output. These
bounded n/2n/4n guards pin its exact output size while the emitted-C
audit checks that neither fold consumes one native stack frame per
operand. -/
private def disjointUnionAxiomGraph (n : Nat) : Graph :=
  [⟨.iri exK, owlDisjointUnionOf,
      if n == 0 then .iri rdfNil else bnT "du-list-0"⟩] ++
  (List.range n).flatMap (fun i =>
    [ ⟨bn ("du-list-" ++ toString i), rdfFirst, .iri exC⟩,
      ⟨bn ("du-list-" ++ toString i), rdfRest,
        if i + 1 < n then bnT ("du-list-" ++ toString (i + 1))
        else .iri rdfNil⟩ ])

private def disjointUnionAxiomCount (n : Nat) : Nat :=
  let g := disjointUnionAxiomGraph n
  (namedClassExpressionAxioms [] (Store.ofGraph g)).length

#guard disjointUnionAxiomCount 25 == 604
#guard disjointUnionAxiomCount 50 == 2454
#guard disjointUnionAxiomCount 100 == 9904

/-! `∃p.{y}` produces the exact countable edge `(i,p,y)`. Through
`p inverseOf q`, it violates `y : ≤0 q`. -/
private def gSingletonNominalEdge (bounded : Bool) : Graph :=
  [ ⟨.iri exP, owlInverseOf, .iri exQ⟩,
    ⟨indI, rdfType, bnT "some-nom"⟩,
    ⟨bn "some-nom", owlOnProperty, .iri exP⟩,
    ⟨bn "some-nom", owlSomeValuesFrom, bnT "only-y"⟩,
    ⟨bn "only-y", owlOneOf, bnT "only-y-list"⟩,
    ⟨bn "only-y-list", rdfFirst, .iri exY⟩,
    ⟨bn "only-y-list", rdfRest, .iri rdfNil⟩ ] ++
  if bounded then
    [ ⟨.iri exY, rdfType, bnT "max-zero-inverse"⟩,
      ⟨bn "max-zero-inverse", owlOnProperty, .iri exQ⟩,
      ⟨bn "max-zero-inverse", owlMaxCardinality, cardLit "0"⟩ ]
  else []

#guard tableauConsistent (gSingletonNominalEdge false) fuel == some true
#guard tableauConsistent (gSingletonNominalEdge true) fuel == some false

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

/-! A generated existential edge is excluded from positive-cardinality
distinctness reasoning, but it still violates a maximum of zero. The
role hierarchy widens the generated `p` edge to a `q` successor. The
maximum-one and reversed-hierarchy neighbors are satisfiable. -/
private def gGeneratedSubpropertyMax (bound : String) (reverse : Bool) : Graph :=
  [ ⟨if reverse then .iri exQ else .iri exP, rdfsSubPropertyOf,
      if reverse then .iri exP else .iri exQ⟩,
    ⟨indI, rdfType, bnT "generated-some"⟩,
    ⟨bn "generated-some", owlOnProperty, .iri exP⟩,
    ⟨bn "generated-some", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "generated-max"⟩,
    ⟨bn "generated-max", owlOnProperty, .iri exQ⟩,
    ⟨bn "generated-max", owlMaxCardinality, cardLit bound⟩ ]

#guard tableauConsistent (gGeneratedSubpropertyMax "0" false) fuel == some false
#guard tableauConsistent (gGeneratedSubpropertyMax "1" false) fuel == some true
#guard tableauConsistent (gGeneratedSubpropertyMax "0" true) fuel == some true

/-! Qualified zero uses the same rule, restricted to a successor whose
filler label is known. Changing the bound's filler from `C` to unrelated
`D` leaves the graph satisfiable. -/
private def gGeneratedSubpropertyQualifiedZero (filler : WfIri) : Graph :=
  [ ⟨.iri exP, rdfsSubPropertyOf, .iri exQ⟩,
    ⟨indI, rdfType, bnT "generated-q-some"⟩,
    ⟨bn "generated-q-some", owlOnProperty, .iri exP⟩,
    ⟨bn "generated-q-some", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "generated-q-max"⟩,
    ⟨bn "generated-q-max", owlOnProperty, .iri exQ⟩,
    ⟨bn "generated-q-max", owlMaxQualifiedCardinality, cardLit "0"⟩,
    ⟨bn "generated-q-max", owlOnClass, .iri filler⟩ ]

#guard tableauConsistent (gGeneratedSubpropertyQualifiedZero exC) fuel == some false
#guard tableauConsistent (gGeneratedSubpropertyQualifiedZero exD) fuel == some true

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

No clash rule sees this without the ≤-rule: for a POSITIVE maximum,
`clashForLabel` counts only PROVABLY DISTINCT successors and does not
count fresh witnesses. Seventeen `WebOnt-description-logic`
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

/-! Merge siblings use the same budget pool and preserve their source
order. This fixture needs eleven visits and returns the unused pool. -/
#guard searchResult gFunctionalMerge 8 == (.out, 0)
#guard searchResult gFunctionalMerge 16 == (.clash, 5)

/-! A qualified maximum ranges only over successors proved to be in
the filler. `x : ≤1 p.C` has a model when `C` is empty, even if two
unrelated `p` successors carry contradictory labels. Merging those
successors would manufacture a contradiction. When both successors
are in `C`, every permitted identification closes. -/
private def gQualifiedMerge (inFiller : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "qr"⟩,
    ⟨bn "qr", owlOnProperty, .iri exP⟩,
    ⟨bn "qr", owlMaxQualifiedCardinality, cardLit "1"⟩,
    ⟨bn "qr", owlOnClass, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩, ⟨indI, exP, .iri exZ⟩,
    ⟨.iri exY, rdfType, .iri exD⟩,
    ⟨.iri exZ, rdfType, bnT "notD"⟩,
    ⟨bn "notD", owlComplementOf, .iri exD⟩ ] ++
  if inFiller then
    [⟨.iri exY, rdfType, .iri exC⟩, ⟨.iri exZ, rdfType, .iri exC⟩]
  else []

#guard tableauConsistent (gQualifiedMerge false) fuel == some true
#guard tableauConsistent (gQualifiedMerge true) fuel == some false

/-! The `≤0 p.C` clash uses the same filler restriction. -/
private def gQualifiedZero (inFiller : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "qz"⟩,
    ⟨bn "qz", owlOnProperty, .iri exP⟩,
    ⟨bn "qz", owlMaxQualifiedCardinality, cardLit "0"⟩,
    ⟨bn "qz", owlOnClass, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩ ] ++
  if inFiller then [⟨.iri exY, rdfType, .iri exC⟩] else []

#guard tableauConsistent (gQualifiedZero false) fuel == some true
#guard tableauConsistent (gQualifiedZero true) fuel == some false

/-! Drop the subproperty axioms and the same graph is satisfiable:
three separate successors on three unrelated functional properties
breach nothing. A refuter that merged them anyway would refute an
ontology with a model. -/

private def gNoSubProperty : Graph :=
  gFunctionalMerge.filter (fun t => t.p != rdfsSubPropertyOf)

#guard !(refuted gNoSubProperty)

/-! A named individual IS a merge candidate since 2026-09-07. The
merge records an identification and `labelsOf` / `successorsOf` pool
the group, so no state is half-rewritten; and offering only blank
nodes left every successor pair involving a named individual outside
the `≤`-rule's branch cover, which is what makes "every offered merge
closes" an argument at all (design record § 11.6).

A LITERAL is never a candidate: a literal and an IRI denote in
disjoint domains under OWL 2 Direct Semantics § 2.2, and two literals
with different values are already `provablyDistinct`. -/
#guard isMergeableTerm (.iri exP1)
#guard isMergeableTerm (bnT "w")
#guard !(isMergeableTerm (cardLit "1"))

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
is exhausted mid-search. A larger budget reaches the witness-depth
bound, but the existential obligation remains unsatisfied. Both are
`none` — indeterminate until a sound blocking rule is available. -/
private def gCyclicExists : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩,
    ⟨.iri exC, rdfsSubClassOf, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩ ]

#guard tableauConsistent gCyclicExists 1 == none
#guard tableauConsistent gCyclicExists fuel == none
#guard refute gCyclicExists 1 == none

/-! ## Withheld witness obligations are indeterminate

The depth bound must not turn an unfinished existential chain into a
consistency result. At depth three the generated witness exposes the
terminal `C`/`¬C` clash. At depth four the next witness is withheld, so
both the satisfiable control and the contradiction return `out`; the
engine must expand beyond this fixed limit to distinguish them. -/
private def nestedSome : Nat → ClassExpr
  | 0     => .named exC
  | n + 1 => .someOf exP (nestedSome n)

private def nestedAll (terminal : ClassExpr) : Nat → ClassExpr
  | 0     => terminal
  | n + 1 => .allOf exP (nestedAll terminal n)

private def nestedDepthState (depth : Nat) (contradiction : Bool) : RState :=
  let terminal := if contradiction then .complement (.named exC) else .named exC
  { initState [] with
    nodes := [{ id := indI,
                labels := [nestedSome depth, nnf (nestedAll terminal depth)] }] }

private def nestedDepthVerdict (depth : Nat) (contradiction : Bool) : Verdict :=
  (search [] [] (nestedDepthState depth contradiction) fuel).1

#guard nestedDepthVerdict maxWitnessDepth true == .clash
#guard nestedDepthVerdict maxWitnessDepth false == .open'
#guard nestedDepthVerdict (maxWitnessDepth + 1) true == .out
#guard nestedDepthVerdict (maxWitnessDepth + 1) false == .out

private def explicitCappedObligation : RState :=
  { initState [] with
    nodes := [{ id := bn "at-cap", labels := [.someOf exP (.named exC)] }],
    wdepth := [("at-cap", maxWitnessDepth)] }

#guard pendingWitnessObligation [] explicitCappedObligation

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

/-! A property assertion with a literal object negates to the four
triples of an OWL negative data-property assertion. A purely structural
conclusion has no content assertion to negate: `none`. -/
#guard (negationGoals
        [⟨indI, exP, .literal ⟨{ lexicalForm := "v", datatype := xsdString,
                                 langTag := none, direction := none }, rfl⟩⟩]).map
       (·.map List.length) == some [4]
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

/-! End to end, the refuter does not prove entailment:
`i ∈ C ⊭ i ∈ D`. The augmented graph reaches quiescence
(`some true`), but this executable result is not a certified model and
does not itself prove non-entailment. -/
#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map
         (·.any (fun neg => tableauConsistent ([⟨indI, rdfType, .iri exC⟩] ++ neg)
                              fuel == some true))
       == some true

/-! ## Fresh namespaces for generated negation goals

Every identifier below is legal N-Quads input. Before
`prepareNegationGoals`, a premise blank node named exactly like the
generated complement node could be conflated with that node and turn
the satisfiable `i : D, unrelated : ¬D, i : ¬C` goal into a false
clash. The prepared premise and goal remain open. -/
private def gNegationIdCollision : Graph :=
  [ ⟨indI, rdfType, .iri exD⟩,
    ⟨bn peNegClassBNode, owlComplementOf, .iri exD⟩ ]

private def cUnrelatedMembership : Graph :=
  [⟨indI, rdfType, .iri exC⟩]

private def preparedGoalResults (premise conclusion : Graph) : Option (List (Option Bool)) :=
  (prepareNegationGoals premise conclusion).map fun (premise', goals) =>
    goals.map fun goal => tableauConsistent (premise' ++ goal) fuel

#guard preparedGoalResults gNegationIdCollision cUnrelatedMembership
       == some [some true]

/-! `i rdf:type owl:Thing` is a semantic membership assertion, not a
declaration to discard. Its negation is impossible, so even an empty
premise refutes the single goal. -/
#guard !isMetaTypeIri owlThing
#guard preparedGoalResults [] [⟨indI, rdfType, .iri owlThing⟩]
       == some [some false]

/-! Conclusion scaffolding can carry the same legal input label. Its
references must remain co-referential after renaming while staying
disjoint from the generated complement node. Here the conclusion says
`i : ¬D`; its negation is consistent with the premise `i : D`. -/
private def cNegationIdCollision : Graph :=
  [ ⟨bn peNegClassBNode, owlComplementOf, .iri exD⟩,
    ⟨indI, rdfType, .bnode peNegClassBNode⟩ ]

#guard preparedGoalResults [⟨indI, rdfType, .iri exD⟩] cNegationIdCollision
       == some [some true]

/-! Positive neighbor: a named complement axiom entails the anonymous
complement membership even when its input label matches the generated
negation node. This requires refutation after scoping, not exact triple
containment in the premise. -/
#guard preparedGoalResults
    [⟨indI, rdfType, .iri exC⟩, ⟨.iri exC, owlComplementOf, .iri exD⟩]
    cNegationIdCollision == some [some false]

/-! The two input documents also receive different prefixes even when
they use the same raw blank-node label. -/
#guard bnodeScopePrefix ["owl-premise"] != bnodeScopePrefix ["owl-conclusion"]
#guard bnodeScopePrefix ["owl-premise"] != ""
#guard (bnodeScopePrefix ["owl-premise"]).startsWith "s_"
#guard !(bnodeScopePrefix ["owl-premise"]).startsWith "_"


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

/-! ## Total-search equations and proof audit -/

example (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState) :
    search tb g st 0 = (.out, 0) := search_zero tb g st

example (tb : List (ClassExpr × ClassExpr)) (g : Graph) (st : RState)
    (n : Nat) (h : clashNodes g st = true) :
    search tb g st (n + 1) = (.clash, n) :=
  search_immediate_clash tb g st n h

#print axioms search_remaining_le
#print axioms search_zero
#print axioms search_immediate_clash
#print axioms search_changed
#print axioms inputWitnessIdUsed_indexed_eq_spec
#print axioms foldl_filter_of_rejected_identity
#print axioms onePassFiltered_eq
#print axioms onePass_eq_filtered
#print axioms addLabel_initial
#print axioms fold_addLabel_initial
#print axioms InitialLabelBuilder.add_wf
#print axioms InitialLabelBuilder.add_nodes
#print axioms InitialLabelBuilder.fold_nodes
#print axioms InitialLabelBuilder.addSubject_wf
#print axioms InitialLabelBuilder.addSubject_nodes
#print axioms InitialLabelBuilder.foldSubject_nodes
#print axioms InitialLabelBuilder.foldSubject_wf
#print axioms initialLabelNodesIndexed_eq_spec
#print axioms initialGraphNodesIndexed_eq_spec
#print axioms fold_initialLabelEntries
#print axioms fold_ensureInitialSubjects
#print axioms indexedInitialState_eq_graphFold
#print axioms initStateIndexed_eq
#print axioms initState_eq_indexed
#print axioms clashForLabel_maxCard_zero
#print axioms clashForLabel_maxQualCard_zero
#print axioms NamedAxiomIndex.add_getD
#print axioms fold_namedAxiomIndex_getD
#print axioms buildNamedAxiomIndex_getD
#print axioms namedAxiomFor_rejected
#print axioms applyAxioms_named_filter_eq
#print axioms applyAxiomsDispatched_eq
#print axioms onePassNodeDispatched_eq
#print axioms onePassNodesDispatched_eq

/-! Named-antecedent buckets retain the exact TBox order while
interleaved nonmatching and nonnamed antecedents stay out. -/
private def namedDispatchOrderCheck : Bool :=
  let tb : List (ClassExpr × ClassExpr) :=
    [ (.named exC, .named exD),
      (.someOf exP (.named exC), .named exC),
      (.named exD, .named exC),
      (.named exC, .named exP) ]
  match (buildNamedAxiomIndex tb).getD exC [] with
  | [(.named a, .named b), (.named c, .named d)] =>
      a == exC && b == exD && c == exC && d == exP
  | _ => false

#guard namedDispatchOrderCheck

/-! The indexed initial-label builder preserves first-subject order,
per-subject append order, exact `memCe` duplicate behaviour, and the
rule that a top-level unreadable class expression is ignored. -/
private def nestedUnknown : ClassExpr :=
  .intersection [.unknown, .named exC]

private def initialLabelOrderCheck : Bool :=
  match initialLabelNodesIndexed
      [ (indI, .named exC),
        (bn "label-order", .named exD),
        (indI, .named exD),
        (indI, .named exC),
        (indI, .unknown),
        (indI, nestedUnknown),
        (indI, nestedUnknown) ] with
  | [first, second] =>
      first.id == indI &&
      second.id == bn "label-order" &&
      match first.labels, second.labels with
      | [a, b, c, d], [e] =>
          ClassExpr.beq a (.named exC) &&
          ClassExpr.beq b (.named exD) &&
          ClassExpr.beq c nestedUnknown &&
          ClassExpr.beq d nestedUnknown &&
          ClassExpr.beq e (.named exD)
      | _, _ => false
  | _ => false

#guard initialLabelOrderCheck

/-! ## Datatype witnesses with explicitly forbidden values

OWL 2 Direct Semantics §2.3.2 requires disjoint data-property
extensions to share no subject-value pair.  A value asserted through
`exP` is therefore excluded from an `exQ` existential when the two
properties are disjoint.  The restriction below has the singleton
integer value space `{10}`. -/

private def typedTerm (lex : String) (dt : WfIri)
    (h : literalWf { lexicalForm := lex, datatype := dt,
                     langTag := none, direction := none }) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := dt,
              langTag := none, direction := none }, h⟩

private def intTerm (lex : String) : Term :=
  typedTerm lex xsdInteger (by
    simp [literalWf, xsdInteger, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def uintTerm (lex : String) : Term :=
  typedTerm lex XSD.xsdUnsignedInt (by
    simp [literalWf, XSD.xsdUnsignedInt, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def floatTerm (lex : String) : Term :=
  typedTerm lex XSD.xsdFloat (by
    simp [literalWf, XSD.xsdFloat, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def decimalTerm (lex : String) : Term :=
  typedTerm lex xsdDecimal (by
    simp [literalWf, xsdDecimal, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def rationalTerm (lex : String) : Term :=
  typedTerm lex XSD.owlRational (by
    simp [literalWf, XSD.owlRational, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def disjointSingletonGraph
    (assertedSubject : Subject) (assertedProperty : WfIri)
    (assertedValue : Term) : Graph :=
  [ ⟨.iri exP, owlPropertyDisjointWith, .iri exQ⟩,
    ⟨assertedSubject, assertedProperty, assertedValue⟩,
    ⟨.iri exC, rdfsSubClassOf, bnT "dsr"⟩,
    ⟨bn "dsr", owlOnProperty, .iri exQ⟩,
    ⟨bn "dsr", owlSomeValuesFrom, bnT "ddr"⟩,
    ⟨bn "ddr", owlOnDatatype, .iri xsdInteger⟩,
    ⟨bn "ddr", owlWithRestrictions, bnT "dfl1"⟩,
    ⟨bn "dfl1", rdfFirst, bnT "dfmin"⟩,
    ⟨bn "dfl1", rdfRest, bnT "dfl2"⟩,
    ⟨bn "dfmin", facetMinInclusive, intTerm "10"⟩,
    ⟨bn "dfl2", rdfFirst, bnT "dfmax"⟩,
    ⟨bn "dfl2", rdfRest, .iri rdfNil⟩,
    ⟨bn "dfmax", facetMaxInclusive, intTerm "10"⟩,
    ⟨indI, rdfType, .iri exC⟩ ]

#guard refuted (disjointSingletonGraph indI exP (intTerm "10"))
/-! Integer lexical aliases and derived integer datatypes denote the
same OWL data value. -/
#guard refuted (disjointSingletonGraph indI exP (uintTerm "+010"))
/-! Subject identity, the disjointness declaration, and value equality
are each required. -/
#guard !(refuted (disjointSingletonGraph (.iri exY) exP (intTerm "10")))
#guard !(refuted (disjointSingletonGraph indI exF1 (intTerm "10")))
#guard !(refuted (disjointSingletonGraph indI exP (intTerm "9")))

/-! OWL 2 Syntax §9.6.4 makes a negative data-property assertion an
explicit exclusion.  In this graph `owl:real` removes `-INF` from the
enumeration, and the negative assertion removes integer negative zero
because it denotes the same value as unsigned integer zero. -/

private def negativeEnumGraph (source : Subject) (assertionProperty : WfIri)
    (target : Term) : Graph :=
  [ ⟨indI, rdfType, bnT "nall"⟩,
    ⟨bn "nall", owlOnProperty, .iri exP⟩,
    ⟨bn "nall", owlAllValuesFrom, .iri XSD.owlReal⟩,
    ⟨indI, rdfType, bnT "nsome"⟩,
    ⟨bn "nsome", owlOnProperty, .iri exP⟩,
    ⟨bn "nsome", owlSomeValuesFrom, bnT "nenum"⟩,
    ⟨bn "nenum", owlOneOf, bnT "nel1"⟩,
    ⟨bn "nel1", rdfFirst, floatTerm "-INF"⟩,
    ⟨bn "nel1", rdfRest, bnT "nel2"⟩,
    ⟨bn "nel2", rdfFirst, intTerm "-0"⟩,
    ⟨bn "nel2", rdfRest, .iri rdfNil⟩,
    ⟨bn "npa", rdfType, .iri owlNegativePropertyAssertion⟩,
    ⟨bn "npa", owlSourceIndividual, source.toTerm⟩,
    ⟨bn "npa", owlAssertionProperty, .iri assertionProperty⟩,
    ⟨bn "npa", owlTargetValue, target⟩ ]

#guard refuted (negativeEnumGraph indI exP (uintTerm "0"))
#guard !(refuted (negativeEnumGraph indI exP (uintTerm "1")))
#guard !(refuted (negativeEnumGraph (.iri exY) exP (uintTerm "0")))
#guard !(refuted (negativeEnumGraph indI exQ (uintTerm "0")))

/-! A second admissible enumeration value keeps the existential
satisfiable after zero is excluded. -/
private def negativeEnumChoiceGraph : Graph :=
  (negativeEnumGraph indI exP (uintTerm "0")).map (fun t =>
    if t.s == bn "nel2" && t.p == rdfRest then
      ⟨bn "nel2", rdfRest, bnT "nel3"⟩
    else t) ++
  [ ⟨bn "nel3", rdfFirst, intTerm "1"⟩,
    ⟨bn "nel3", rdfRest, .iri rdfNil⟩ ]

#guard !(refuted negativeEnumChoiceGraph)

/-! ## Finite XSD pattern languages

XSD pattern facets match the whole lexical form. The language of
`a(b|c)` is exactly `{ab, ac}`; values already used through a disjoint
property exhaust the existential filler. -/

private def stringTerm (lex : String) : Term :=
  typedTerm lex xsdString (by
    simp [literalWf, xsdString, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

/-! A functional superproperty constrains assertions through its
subproperties even when the assertion subject has no `rdf:type`.
Initialisation must therefore create an empty node for every graph
subject. Equal values, a nonfunctional superproperty, and assertions
on different subjects remain satisfiable controls. -/
private def untypedFunctionalStrings (functional equalValues : Bool)
    (differentSubjects : Bool := false) : Graph :=
  [ ⟨.iri exP, rdfType,
      .iri (if functional then owlFunctionalProperty else owlDatatypeProperty)⟩,
    ⟨.iri exQ, rdfsSubPropertyOf, .iri exP⟩,
    ⟨indI, exP, stringTerm "T000-01"⟩,
    ⟨if differentSubjects then .iri exY else indI, exQ,
      stringTerm (if equalValues then "T000-01" else "BOOLEAN")⟩ ]

#guard refuted (untypedFunctionalStrings true false)
#guard !(refuted (untypedFunctionalStrings true true))
#guard !(refuted (untypedFunctionalStrings false false))
#guard !(refuted (untypedFunctionalStrings true false true))

/-! ## Literal-valued positive-entailment goals

The exact negation of `i p value` is an OWL negative data-property
assertion with that target value. Value equality, rather than RDF term
identity, closes numeric lexical aliases and canonical XML aliases.
Unknown datatype mappings with unequal terms remain open. -/
private def xmlTerm (lex : String) : Term :=
  typedTerm lex rdfXMLLiteral (by
    simp [literalWf, rdfXMLLiteral, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def unknownDatatype : WfIri := ⟨"http://e/unknownDatatype", rfl⟩
private def aliasDatatype : WfIri := ⟨"http://e/decimalAlias", rfl⟩

private def unknownTerm (lex : String) : Term :=
  typedTerm lex unknownDatatype (by
    simp [literalWf, unknownDatatype, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def aliasTerm (lex : String) : Term :=
  typedTerm lex aliasDatatype (by
    simp [literalWf, aliasDatatype, rdfLangString, rdfDirLangString,
          Subtype.ext_iff])

private def literalEntailmentResult (premise : Graph)
    (conclusionValue : Term) : Option (List (Option Bool)) :=
  preparedGoalResults premise [⟨indI, exP, conclusionValue⟩]

#guard (negationGoals [⟨indI, exP, intTerm "1"⟩]).map List.length == some 1
#guard negationGoals [⟨bn "anonymous-conclusion", exP, intTerm "1"⟩] == none

#guard literalEntailmentResult [⟨indI, exP, intTerm "01"⟩] (intTerm "1") ==
  some [some false]
#guard literalEntailmentResult [⟨indI, exP, intTerm "1"⟩] (decimalTerm "1.0") ==
  some [some false]
#guard literalEntailmentResult [⟨indI, exP, xmlTerm "<br\n></br>"⟩]
  (xmlTerm "<br></br>") == some [some false]

/-! `owl:sameAs` on datatype IRIs does not import a lexical mapping in
OWL 2 Direct Semantics: individual and datatype interpretations are
separate. The Full/Proposed `WebOnt-I5.8-017` shape therefore remains
open in this DL refuter. -/
#guard literalEntailmentResult
  [ ⟨.iri aliasDatatype, owlSameAs, .iri xsdDecimal⟩,
    ⟨indI, exP, aliasTerm "01"⟩ ]
  (decimalTerm "1") == some [some true]

/-! Different values and incomparable unknown datatype values do not
license a contradiction. Exact term identity remains exact even for
an unsupported datatype. -/
#guard literalEntailmentResult [⟨indI, exP, intTerm "2"⟩] (intTerm "1") ==
  some [some true]
#guard literalEntailmentResult [⟨.iri exY, exP, intTerm "1"⟩] (intTerm "1") ==
  some [some true]
#guard literalEntailmentResult [⟨indI, exQ, intTerm "1"⟩] (intTerm "1") ==
  some [some true]
#guard literalEntailmentResult [⟨indI, exP, unknownTerm "01"⟩]
  (unknownTerm "1") == some [some true]
#guard literalEntailmentResult [⟨indI, exP, unknownTerm "same"⟩]
  (unknownTerm "same") == some [some false]

/-! The singleton numeric intersection in `WebOnt-I5.8-010`: the
premise forces one `p` value and the two ranges meet only at zero. -/
private def signedZeroEntailmentPremise : Graph :=
  [ ⟨.iri exP, rdfsRange, .iri XSD.xsdNonNegativeInteger⟩,
    ⟨indI, rdfType, bnT "pe-signed-zero"⟩,
    ⟨bn "pe-signed-zero", owlOnProperty, .iri exP⟩,
    ⟨bn "pe-signed-zero", owlSomeValuesFrom,
      .iri XSD.xsdNonPositiveInteger⟩ ]

#guard literalEntailmentResult signedZeroEntailmentPremise (intTerm "0") ==
  some [some false]

private def patternExclusionGraph (pattern : String)
    (asserted : List (Subject × String)) : Graph :=
  [ ⟨.iri exP, owlPropertyDisjointWith, .iri exQ⟩,
    ⟨.iri exC, rdfsSubClassOf, bnT "psome"⟩,
    ⟨bn "psome", owlOnProperty, .iri exQ⟩,
    ⟨bn "psome", owlSomeValuesFrom, bnT "pdr"⟩,
    ⟨bn "pdr", owlOnDatatype, .iri xsdString⟩,
    ⟨bn "pdr", owlWithRestrictions, bnT "pfl"⟩,
    ⟨bn "pfl", rdfFirst, bnT "pfacet"⟩,
    ⟨bn "pfl", rdfRest, .iri rdfNil⟩,
    ⟨bn "pfacet", facetPattern, stringTerm pattern⟩,
    ⟨indI, rdfType, .iri exC⟩ ] ++
  asserted.map (fun (s, lex) => ⟨s, exP, stringTerm lex⟩)

#guard refuted (patternExclusionGraph "a(b|c)" [(indI, "ab"), (indI, "ac")])
/-! A value on another subject, a remaining pattern value, or an
unsupported infinite regex cannot exhaust this existential. -/
#guard !(refuted (patternExclusionGraph "a(b|c)" [(indI, "ab"), (.iri exY, "ac")]))
#guard !(refuted (patternExclusionGraph "a(b|c|d)" [(indI, "ab"), (indI, "ac")]))
#guard !(refuted (patternExclusionGraph "a.*" [(indI, "ab"), (indI, "ac")]))
/-! Brace repetitions are rejected before the shared parser can
expand their AST; a huge bound therefore returns promptly. -/
#guard !(refuted (patternExclusionGraph "a{1000000000}"
  [(indI, "a"), (indI, "aa")]))

/-! ## Complete RDF collection parsing

Long collection fillers are read independently of the class-expression
depth cap. A minimum of 33 values from a 64-member nominal is
satisfiable; a minimum of 65 is impossible. -/

private def indexedBNode (stem : String) (n : Nat) : Term :=
  bnT (stem ++ toString n)

private def rdfListTriples (stem : String) (members : List Term) : Graph :=
  (List.range members.length).zip members |>.map (fun (idx, member) =>
    [ ⟨bn (stem ++ toString idx), rdfFirst, member⟩,
      ⟨bn (stem ++ toString idx), rdfRest,
        if idx + 1 < members.length then indexedBNode stem (idx + 1)
        else .iri rdfNil⟩ ]) |>.flatten

private def nominalMinGraph (minimum memberCount : Nat) : Graph :=
  let members := (List.range memberCount).map (indexedBNode "nominal-member-")
  [ ⟨indI, rdfType, bnT "nominal-min"⟩,
    ⟨bn "nominal-min", owlOnProperty, .iri exP⟩,
    ⟨bn "nominal-min", owlMinQualifiedCardinality, cardLit (toString minimum)⟩,
    ⟨bn "nominal-min", owlOnClass, bnT "nominal-filler"⟩,
    ⟨bn "nominal-filler", owlOneOf, indexedBNode "nominal-list-" 0⟩ ] ++
  rdfListTriples "nominal-list-" members

#guard !(refuted (nominalMinGraph 33 64))
#guard refuted (nominalMinGraph 65 64)

/-! Malformed and cyclic lists make the whole class expression
unknown. They never expose a finite prefix as a complete nominal. -/
private def malformedNominalGraph : Graph :=
  [ ⟨indI, rdfType, bnT "malformed-min"⟩,
    ⟨bn "malformed-min", owlOnProperty, .iri exP⟩,
    ⟨bn "malformed-min", owlMinQualifiedCardinality, cardLit "2"⟩,
    ⟨bn "malformed-min", owlOnClass, bnT "malformed-filler"⟩,
    ⟨bn "malformed-filler", owlOneOf, bnT "malformed-list"⟩,
    ⟨bn "malformed-list", rdfFirst, .iri exY⟩ ]

private def cyclicNominalGraph : Graph :=
  malformedNominalGraph ++
  [⟨bn "malformed-list", rdfRest, bnT "malformed-list"⟩]

#guard !(refuted malformedNominalGraph)
#guard !(refuted cyclicNominalGraph)

/-! IRI list cells are legal. Exact duplicate assertions carry one
value; genuinely different `rdf:first` values make the collection
ambiguous and therefore unreadable. -/
private def iriCell : Graph :=
  [ ⟨.iri exY, rdfFirst, .iri exZ⟩,
    ⟨.iri exY, rdfRest, .iri rdfNil⟩ ]

#guard walkRdfListComplete (Store.ofGraph iriCell) (.iri exY) == some [.iri exZ]
#guard walkRdfListComplete (Store.ofGraph (iriCell ++ iriCell)) (.iri exY) ==
  some [.iri exZ]
#guard walkRdfListComplete
  (Store.ofGraph (iriCell ++ [⟨.iri exY, rdfFirst, .iri exC⟩])) (.iri exY) == none

/-! These indexed-store build-time checks cross
the former depth boundary by two orders of magnitude and exercise the
tail-recursive collection reader at increasing sizes. -/
private def decodedListLength (n : Nat) : Option Nat :=
  let members := (List.range n).map (indexedBNode "scale-member-")
  let graph := rdfListTriples "scale-list-" members
  (walkRdfListComplete (Store.ofIndex (Index.ofGraph graph))
    (indexedBNode "scale-list-" 0)).map List.length

#guard decodedListLength 1000 == some 1000
#guard decodedListLength 2000 == some 2000
#guard decodedListLength 4000 == some 4000

/-! The intended, well-formed form of `New-Feature-Rational-002`
still clashes: decimal 0.5 and rational 1/2 denote one value, while
the minimum cardinality requires two. -/
private def validRationalCardinalityGraph : Graph :=
  [ ⟨indI, rdfType, bnT "rational-all"⟩,
    ⟨bn "rational-all", owlOnProperty, .iri exP⟩,
    ⟨bn "rational-all", owlAllValuesFrom, bnT "rational-enum"⟩,
    ⟨bn "rational-enum", owlOneOf, indexedBNode "rational-list-" 0⟩,
    ⟨indI, rdfType, bnT "rational-min"⟩,
    ⟨bn "rational-min", owlOnProperty, .iri exP⟩,
    ⟨bn "rational-min", owlMinCardinality, cardLit "2"⟩ ] ++
  rdfListTriples "rational-list-"
    [decimalTerm "0.5", rationalTerm "1/2"]

#guard refuted validRationalCardinalityGraph

/-! ## Anonymous data-property ranges and cardinality existence

Two anonymous ranges intersect independently. Here `{1,2,3,4}` and
`{4,5,6}` leave only value 4; `≥ 1 p` forces a filler, and a negative
assertion excluding 4 makes that impossible. -/
private def anonymousRangeMinGraph (negativeTarget : Option Term) : Graph :=
  let firstRange := [intTerm "1", intTerm "2", intTerm "3", intTerm "4"]
  let secondRange := [intTerm "4", intTerm "5", intTerm "6"]
  [ ⟨indI, rdfType, bnT "anon-min"⟩,
    ⟨bn "anon-min", owlOnProperty, .iri exP⟩,
    ⟨bn "anon-min", owlMinCardinality, cardLit "1"⟩,
    ⟨.iri exP, rdfsRange, bnT "anon-range-a"⟩,
    ⟨.iri exP, rdfsRange, bnT "anon-range-b"⟩,
    ⟨bn "anon-range-a", owlOneOf, indexedBNode "anon-list-a-" 0⟩,
    ⟨bn "anon-range-b", owlOneOf, indexedBNode "anon-list-b-" 0⟩ ] ++
  rdfListTriples "anon-list-a-" firstRange ++
  rdfListTriples "anon-list-b-" secondRange ++
  match negativeTarget with
  | none => []
  | some target =>
    [ ⟨bn "anon-negative", rdfType, .iri owlNegativePropertyAssertion⟩,
      ⟨bn "anon-negative", owlSourceIndividual, indI.toTerm⟩,
      ⟨bn "anon-negative", owlAssertionProperty, .iri exP⟩,
      ⟨bn "anon-negative", owlTargetValue, target⟩ ]

#guard refuted (anonymousRangeMinGraph (some (intTerm "4")))
#guard !(refuted (anonymousRangeMinGraph none))
#guard !(refuted (anonymousRangeMinGraph (some (intTerm "3"))))

/-! `WebOnt-oneOf-004` shape: the two anonymous ranges meet only at
value 4 and minimum cardinality one forces that assertion. Negating
the literal conclusion excludes precisely 4 and closes the goal. -/
#guard preparedGoalResults (anonymousRangeMinGraph none)
  [⟨indI, exP, intTerm "4"⟩] == some [some false]

/-! A named range and an existential filler restriction can also
meet at a singleton. Integer lexical aliases are compared by value. -/
private def nonPositiveNonNegativeGraph (negativeTarget : Term) : Graph :=
  [ ⟨indI, rdfType, bnT "signed-some"⟩,
    ⟨bn "signed-some", owlOnProperty, .iri exP⟩,
    ⟨bn "signed-some", owlSomeValuesFrom, .iri XSD.xsdNonPositiveInteger⟩,
    ⟨.iri exP, rdfsRange, .iri XSD.xsdNonNegativeInteger⟩,
    ⟨bn "signed-negative", rdfType, .iri owlNegativePropertyAssertion⟩,
    ⟨bn "signed-negative", owlSourceIndividual, indI.toTerm⟩,
    ⟨bn "signed-negative", owlAssertionProperty, .iri exP⟩,
    ⟨bn "signed-negative", owlTargetValue, negativeTarget⟩ ]

#guard refuted (nonPositiveNonNegativeGraph (uintTerm "0"))
#guard !(refuted (nonPositiveNonNegativeGraph (uintTerm "1")))

/-! Qualified-bound clashes require a definite shared filler. Two
unreadable fillers cannot be equated merely because both parsed as
`unknown`; a known equal filler still licenses the arithmetic clash. -/
#guard !(existsMaxQualLt 2 exP .unknown [.maxQualCard 1 exP .unknown])
#guard existsMaxQualLt 2 exP (.named exC) [.maxQualCard 1 exP (.named exC)]

end L4Factoidal.OWL.Refute
