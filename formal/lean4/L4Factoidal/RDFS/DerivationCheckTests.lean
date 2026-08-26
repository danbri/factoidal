/-
L4Factoidal.RDFS.DerivationCheckTests — the MATCHED PAIR that keeps
`checkDerivation_sound` from being satisfied vacuously.

`checkDerivation_sound` (DerivationCheck.lean) says: what the checker
ACCEPTS is derivable. A checker that returned `false` on every input
would satisfy it and be useless. So the gate has two halves, and both
are mandatory:

* POSITIVE — the three witnesses `DerivationTests.lean` builds must be
  ACCEPTED (141, 190 and 147 steps). A checker that cannot accept this
  engine's own output is not a checker.
* NEGATIVE — one mutation per row of design §5 that applies at this
  layer must be REJECTED. Each is built by changing ONE field of ONE
  step of a real, accepted witness, so the only difference between the
  accepted input and the rejected one is the defect.

Each negative case is pinned twice:

* `stepInIsolation` checks the mutated step against the REAL,
  unmutated prefix that precedes it. Nothing downstream can contribute
  to the rejection, so the rejection is attributable to the defect and
  to nothing else. The same call with the step unmutated is pinned
  `true` next to it as the control.
* `checkDerivation` on the whole mutated array is pinned `false` too,
  which is what a consumer actually calls.

Design: `docs/designissues/2026-08-26-proof-certificate-v1.md` §5.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDFS.DerivationCheck

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## The three witnesses, and their axiom sets

Same graphs as `DerivationTests.lean`. The checker takes the axiom
set as a parameter, so each witness is checked against the axiom set
its emitter was given — a witness checked against a DIFFERENT axiom
set is a different question, and design §5's `axiomatic` row covers
it below. -/

private def exA : WfIri := ⟨"http://example.org/a", by rfl⟩
private def exB : WfIri := ⟨"http://example.org/b", by rfl⟩
private def exP : WfIri := ⟨"http://example.org/p", by rfl⟩
private def exQ : WfIri := ⟨"http://example.org/q", by rfl⟩
private def exR : WfIri := ⟨"http://example.org/r", by rfl⟩
private def exC : WfIri := ⟨"http://example.org/C", by rfl⟩
private def exD : WfIri := ⟨"http://example.org/D", by rfl⟩
private def exE : WfIri := ⟨"http://example.org/E", by rfl⟩

/- A triple in neither graph nor any axiom set below. -/
private def exZ : WfIri := ⟨"http://example.org/z", by rfl⟩
private def alienTriple : Triple := ⟨.iri exZ, exZ, .iri exZ⟩

private def schemaGraph : Graph :=
  [ ⟨.iri exP, rdfsSubPropertyOf, .iri exQ⟩,
    ⟨.iri exQ, rdfsSubPropertyOf, .iri exR⟩,
    ⟨.iri exC, rdfsSubClassOf, .iri exD⟩,
    ⟨.iri exD, rdfsSubClassOf, .iri exE⟩,
    ⟨.iri exQ, rdfsDomain, .iri exC⟩,
    ⟨.iri exA, exP, .iri exB⟩ ]

private def dataOnlyGraph : Graph := [⟨.iri exA, exP, .iri exB⟩]

private def emptyWitness : Graph × Derivation := fullClosureWithProof [] [] []
private def emptyAx : Graph := axiomaticTriples [] []

private def schemaWitness : Graph × Derivation :=
  fullClosureWithProof [xsdString] [rdf1] schemaGraph
private def schemaAx : Graph := axiomaticTriples [xsdString] [rdf1]

private def dataOnlyWitness : Graph × Derivation :=
  fullClosureWithProof [] [] dataOnlyGraph
private def dataOnlyAx : Graph := axiomaticTriples [] []

/-! ## POSITIVE — the emitter's own output is accepted

Everything the emitter emits, the checker accepts. That is a THEOREM:
`checkDerivation_roundTrip` in `DerivationCheck.lean` states it for
every datatype map, `rdf:_n` slice and graph, unconditionally. The three `#guard`s below are the
concrete instances, kept because they also pin the SIZES and so fail
loudly if a row goes silent. -/

#guard emptyWitness.2.size = 141
#guard schemaWitness.2.size = 190
#guard dataOnlyWitness.2.size = 147

#guard checkDerivation emptyAx [] emptyWitness.2 = true
#guard checkDerivation schemaAx schemaGraph schemaWitness.2 = true
#guard checkDerivation dataOnlyAx dataOnlyGraph dataOnlyWitness.2 = true

/- The report form a consumer calls carries the same verdict. -/
#guard (checkDerivationReport schemaAx schemaGraph schemaWitness.2).valid = true

/-! ## The weakest link (design §6b)

Reported alongside the verdict, with no effect on it. Every
whole-closure witness contains
`base` and `axiomatic` steps, whose licence is the `DerivesFull`
constructor itself, so the weakest link is `constructorOnly` for all
three. Pinned here so the field is never read as saying more than it
does — see the header of `DerivationCheck.lean`. -/

#guard weakestAssurance emptyWitness.2 = some .constructorOnly
#guard weakestAssurance schemaWitness.2 = some .constructorOnly
#guard weakestAssurance dataOnlyWitness.2 = some .constructorOnly
#guard weakestAssurance (#[] : Derivation) = none

/-! ## Mutation harness

`mutateAt d i f` replaces step `i` of `d` by `f (d[i])` and changes
nothing else. `stepInIsolation` runs the step check for position `i`
against the REAL prefix `d.toList.take i`, so a rejection cannot come
from a downstream step the mutation happened to break. -/

private def mutateAt (d : Derivation) (i : Nat) (f : Step → Step) : Derivation :=
  (d.toList.zipIdx.map (fun (st, j) => if j == i then f st else st)).toArray

private def stepInIsolation (ax g : Graph) (d : Derivation) (i : Nat)
    (f : Step → Step) : Bool :=
  stepOk ax g (d.toList.take i) (f d[i]!)

private def withPremises (ps : List Nat) (st : Step) : Step :=
  { st with premises := ps }

private def withConclusion (t : Triple) (st : Step) : Step :=
  { st with conclusion := t }

/- Position of the first step naming a given row. Located rather
than hard-coded, so a change to row order shows up as a failed index
`#guard` below and not as a mutation applied to the wrong step. -/
private def idxOfRule (d : Derivation) (r : RuleId) : Nat :=
  match d.toList.findIdx? (fun st => st.rule == r) with
  | some i => i
  | none   => 0

private def baseIdx : Nat := idxOfRule schemaWitness.2 .base
private def axiomIdx : Nat := idxOfRule schemaWitness.2 .axiomatic
private def joinIdx : Nat := idxOfRule schemaWitness.2 .rdfs7

/- The three positions the mutations below act on, and the fact that
each really names the row it is supposed to name. -/
#guard baseIdx = 0
#guard axiomIdx = 6
#guard joinIdx = 59
#guard (schemaWitness.2[baseIdx]!).rule = .base
#guard (schemaWitness.2[axiomIdx]!).rule = .axiomatic
#guard (schemaWitness.2[joinIdx]!).rule = .rdfs7
#guard (schemaWitness.2[joinIdx]!).premises = [0, 5]

/- CONTROLS. Each of the three positions passes UNMUTATED, so every
`false` below is caused by the mutation and by nothing else. -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 baseIdx id = true
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 axiomIdx id = true
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx id = true

/-! ## NEGATIVE — design §5, one row at a time

If any of these were accepted it would be a FINDING about the
checker, not a test to adjust. -/

/- **1. Self-justification** — a premise index equal to the step's
own index. Design §5: "a step justified by its own consequence". -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx
  (withPremises [joinIdx, 5]) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 joinIdx (withPremises [joinIdx, 5])) = false

/- **2. Forward reference** — a premise index greater than the
step's own index. -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx
  (withPremises [joinIdx + 1, 5]) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 joinIdx (withPremises [joinIdx + 1, 5])) = false

/- **3. Premise index out of range** — design §5: "a step with no
justification at all". -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx
  (withPremises [schemaWitness.2.size + 7, 5]) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 joinIdx (withPremises [schemaWitness.2.size + 7, 5])) = false

/- **4. A `base` step whose conclusion is not a triple of `g`.** -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 baseIdx
  (withConclusion alienTriple) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 baseIdx (withConclusion alienTriple)) = false

/- **5. An `axiomatic` step whose conclusion is not in `ax`.** -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 axiomIdx
  (withConclusion alienTriple) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 axiomIdx (withConclusion alienTriple)) = false

/- **6. A real rule row cited over the WRONG premises.** rdfs7 with
premises 0 and 1 — two real, earlier steps, both `ex:p
rdfs:subPropertyOf ex:q` and `ex:q rdfs:subPropertyOf ex:r`. Neither
is an `ex:p`-triple, so rdfs7 licenses nothing from that pair and the
step's own conclusion is not among the row's output. -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx
  (withPremises [0, 1]) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 joinIdx (withPremises [0, 1])) = false

/- **7. A conclusion altered to an unrelated triple**, premises and
rule untouched. -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx
  (withConclusion alienTriple) = false
#guard checkDerivation schemaAx schemaGraph
  (mutateAt schemaWitness.2 joinIdx (withConclusion alienTriple)) = false

/-! ### Two more the row shapes make possible

`RuleId` is a closed inductive, so design §5's "unknown (component,
rule) pair" cannot be built at this layer — a row the checker does not
know does not typecheck. What CAN be built is a known row cited with
the wrong NUMBER of premises, and the checker rejects both directions
of that rather than ignoring the surplus. -/

/- A join row cited with one premise. -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 joinIdx
  (withPremises [0]) = false

/- A `base` step cited with a premise. -/
#guard stepInIsolation schemaAx schemaGraph schemaWitness.2 baseIdx
  (withPremises [0]) = false

/-! ### The whole witness checked against the WRONG axiom set

Design §5's `axiomatic` row at derivation scale: the schema
witness's `axiomatic` steps quote §9.3 triples that are not in the
RDF-only axiom set, so the same witness fails against it. This is
the layer at which "a valid proof about a different input" is caught;
graph identity by RDFC-1.0 canonical hash (design §3) is the
serialisation layer's job and is not in this module. -/

#guard checkDerivation (rdfAxiomaticTriples []) schemaGraph schemaWitness.2 = false

/- And against the wrong GRAPH: the schema witness's `base` steps
name triples the empty graph does not hold. -/
#guard checkDerivation schemaAx [] schemaWitness.2 = false

/-! ## The assurance field cannot buy a step its verdict

`checkDerivation_ignores_tags` is the theorem; this is its executable
shadow. Re-tagging every step of a REJECTED derivation with the
strongest assurance reference in the module leaves it rejected. -/

private def overclaim (st : Step) : Step :=
  { st with assurance := .provedBy "L4Factoidal.RDFS.rdfs7For_sound"
                                   "L4Factoidal.RDFS.ClosureTheorems" }

#guard checkDerivation schemaAx schemaGraph
  ((mutateAt schemaWitness.2 joinIdx (withConclusion alienTriple)).map overclaim)
  = false

/-! ## Axiom audit — expect propext / Classical.choice / Quot.sound only -/

#print axioms L4Factoidal.RDFS.checkDerivation_sound
#print axioms L4Factoidal.RDFS.checkDerivationReport_sound
#print axioms L4Factoidal.RDFS.checkDerivation_ignores_tags
#print axioms L4Factoidal.RDFS.stepOk_sound
#print axioms L4Factoidal.RDFS.checkSteps_sound
#print axioms L4Factoidal.RDFS.checkDerivation_roundTrip
#print axioms L4Factoidal.RDFS.fullClosureWithProof_checked
#print axioms L4Factoidal.RDFS.annStepConclusions_stepOk

end L4Factoidal.RDFS
