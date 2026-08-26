/-
L4Factoidal.RDFS.DerivationTests — build-time checks that the RDFS
derivation witness EXHIBITS derivations, and exhibits the right ones.

Why this file exists: `fullClosureWithProof_sound` quantifies over the
steps the emitter produces. An emitter that produced NO steps would
satisfy it, and so would one that produced steps for a rule set that
never fires. The checks below pin concrete chains — the rule of each
step, the conclusions of its premise steps, and a per-rule count over
a graph that exercises all sixteen rows — so a change that silences a
row fails the build instead of passing a vacuous theorem.

The chain for `rdfs:subPropertyOf rdfs:subPropertyOf
rdfs:subPropertyOf` over the EMPTY graph is pinned in full, four steps
deep. See the note there: the route the emitter takes is NOT the
rdfD2 route, and the reason is row order.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDFS.Derivation

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Reading a witness

The three functions a consumer needs: find the step that concluded a
triple, resolve its premise steps, and read a step's rule. -/

/-- The first step whose conclusion is `t`. -/
def stepFor (d : Derivation) (t : Triple) : Option Step :=
  match d.toList.findIdx? (fun st => st.conclusion == t) with
  | none   => none
  | some i => d[i]?

/-- The steps a step names as its premises, in the row's premise
order. -/
def premiseSteps (d : Derivation) (st : Step) : List Step :=
  st.premises.filterMap (fun j => d[j]?)

/-- The rule of the step that concluded `t`, and the conclusions of
that step's premise steps. -/
def ruleAndPremises (d : Derivation) (t : Triple) :
    Option (RuleId × List Triple) :=
  (stepFor d t).map (fun st => (st.rule, (premiseSteps d st).map (·.conclusion)))

/-- Executable form of `fullClosureWithProof_premises_lt`. -/
def premisesPointBackwards (d : Derivation) : Bool :=
  d.toList.zipIdx.all (fun (st, i) => st.premises.all (fun p => p < i))

/-- Executable form of `fullClosureWithProof_wellTagged`. -/
def stepsWellTagged (d : Derivation) : Bool :=
  d.toList.all (fun st => st.component == Component.rdfs
    && st.assurance == st.rule.assurance)

/-! ## The empty graph under full RDFS

`fullClosure [] [] []` is the RDFS closure of the axiom set alone: 141
triples, none of them `base`. -/

private def emptyWitness : Graph × Derivation := fullClosureWithProof [] [] []

#guard emptyWitness.1.length = 141
#guard emptyWitness.2.size = 141
#guard premisesPointBackwards emptyWitness.2
#guard stepsWellTagged emptyWitness.2
#guard emptyWitness.1 == fullClosure [] [] []

/-- `rdfs:subPropertyOf rdfs:subPropertyOf rdfs:subPropertyOf` — the
triple the witness is pinned on. -/
private def spoSelf : Triple :=
  ⟨.iri rdfsSubPropertyOf, rdfsSubPropertyOf, .iri rdfsSubPropertyOf⟩

/-- Its rdfs6 premise. -/
private def spoIsProperty : Triple :=
  ⟨.iri rdfsSubPropertyOf, rdfType, .iri rdfProperty⟩

/-- The §9.3 axiom `rdfs:domain rdfs:domain rdf:Property`. -/
private def domainDomain : Triple :=
  ⟨.iri rdfsDomain, rdfsDomain, .iri rdfProperty⟩

/-- The §9.3 axiom `rdfs:subPropertyOf rdfs:domain rdf:Property`. -/
private def spoDomain : Triple :=
  ⟨.iri rdfsSubPropertyOf, rdfsDomain, .iri rdfProperty⟩

/- The self-triple is in the closure of the EMPTY graph. -/
#guard emptyWitness.1.mem spoSelf

/- **The pinned chain, step by step.**

  `rdfs:domain rdfs:domain rdf:Property .`             (§9.3 axiom)
  `rdfs:subPropertyOf rdfs:domain rdf:Property .`      (§9.3 axiom)
  ⊢ rdfs2 ⊢ `rdfs:subPropertyOf rdf:type rdf:Property .`
  ⊢ rdfs6 ⊢ `rdfs:subPropertyOf rdfs:subPropertyOf rdfs:subPropertyOf .`

rdfs2 reads the first axiom as the DECLARATION (`aaa rdfs:domain xxx`
with aaa = `rdfs:domain`, xxx = `rdf:Property`) and the second as the
DATA triple (`yyy aaa zzz` with yyy = `rdfs:subPropertyOf`), and
concludes `yyy rdf:type xxx`.

⚠️ This is NOT the rdfD2 route (§9.3's `rdfs:isDefinedBy
rdfs:subPropertyOf rdfs:seeAlso`, then rdfD2, then rdfs6). That route
also exists, but `fullStepConclusions` runs the six rdfs-core rows
BEFORE the eight single-premise rows, and `addAll` keeps the first
derivation of a triple, so rdfs2 reaches `rdfs:subPropertyOf rdf:type
rdf:Property` first and rdfD2's copy is discarded as a duplicate.
Both routes are three rule applications deep; which one a witness
shows is decided by row order, not by the spec. -/
#guard ruleAndPremises emptyWitness.2 spoSelf = some (.rdfs6, [spoIsProperty])

#guard ruleAndPremises emptyWitness.2 spoIsProperty
  = some (.rdfs2, [domainDomain, spoDomain])

#guard ruleAndPremises emptyWitness.2 domainDomain = some (.axiomatic, [])
#guard ruleAndPremises emptyWitness.2 spoDomain = some (.axiomatic, [])

/- The assurance references the two rows of the chain carry. -/
#guard (stepFor emptyWitness.2 spoSelf).map (·.assurance)
  = some (.provedBy "L4Factoidal.RDFS.rdfs6For_sound"
      "L4Factoidal.RDFS.FullClosureTheorems")
#guard (stepFor emptyWitness.2 spoIsProperty).map (·.assurance)
  = some (.provedBy "L4Factoidal.RDFS.rdfs2For_sound"
      "L4Factoidal.RDFS.ClosureTheorems")
#guard (stepFor emptyWitness.2 domainDomain).map (·.assurance)
  = some (.constructorOnly "L4Factoidal.RDFS.DerivesFull.axiomatic"
      "L4Factoidal.RDFS.FullClosure")

/-! ## A graph that fires every rdfs-core row

Property chain, class chain, a domain declaration, one data triple; a
datatype in `D` (rdfs1 / rdfs13) and `rdf:_1` in the slice (rdfs12).
Every row except rdfD2 emits at least one step. -/

private def exA : WfIri := ⟨"http://example.org/a", by rfl⟩
private def exB : WfIri := ⟨"http://example.org/b", by rfl⟩
private def exP : WfIri := ⟨"http://example.org/p", by rfl⟩
private def exQ : WfIri := ⟨"http://example.org/q", by rfl⟩
private def exR : WfIri := ⟨"http://example.org/r", by rfl⟩
private def exC : WfIri := ⟨"http://example.org/C", by rfl⟩
private def exD : WfIri := ⟨"http://example.org/D", by rfl⟩
private def exE : WfIri := ⟨"http://example.org/E", by rfl⟩

private def schemaGraph : Graph :=
  [ ⟨.iri exP, rdfsSubPropertyOf, .iri exQ⟩,
    ⟨.iri exQ, rdfsSubPropertyOf, .iri exR⟩,
    ⟨.iri exC, rdfsSubClassOf, .iri exD⟩,
    ⟨.iri exD, rdfsSubClassOf, .iri exE⟩,
    ⟨.iri exQ, rdfsDomain, .iri exC⟩,
    ⟨.iri exA, exP, .iri exB⟩ ]

private def schemaWitness : Graph × Derivation :=
  fullClosureWithProof [xsdString] [rdf1] schemaGraph

#guard schemaWitness.1.length = 190
#guard schemaWitness.2.size = 190
#guard premisesPointBackwards schemaWitness.2
#guard stepsWellTagged schemaWitness.2
#guard schemaWitness.1 == fullClosure [xsdString] [rdf1] schemaGraph

/-- How many steps each row contributed. Every row of the rule set
except rdfD2 fires; rdfD2 fires in `dataOnlyWitness` below. A row that
drops to zero here is a row that stopped working. -/
private def ruleCount (d : Derivation) (r : RuleId) : Nat :=
  (d.toList.filter (fun st => st.rule == r)).length

#guard ruleCount schemaWitness.2 .base = 6
#guard ruleCount schemaWitness.2 .axiomatic = 53
#guard ruleCount schemaWitness.2 .rdfs2 = 31
#guard ruleCount schemaWitness.2 .rdfs3 = 9
#guard ruleCount schemaWitness.2 .rdfs4a = 19
#guard ruleCount schemaWitness.2 .rdfs4b = 10
#guard ruleCount schemaWitness.2 .rdfs5 = 1
#guard ruleCount schemaWitness.2 .rdfs6 = 20
#guard ruleCount schemaWitness.2 .rdfs7 = 2
#guard ruleCount schemaWitness.2 .rdfs8 = 17
#guard ruleCount schemaWitness.2 .rdfs9 = 3
#guard ruleCount schemaWitness.2 .rdfs10 = 16
#guard ruleCount schemaWitness.2 .rdfs11 = 1
#guard ruleCount schemaWitness.2 .rdfs12 = 1
#guard ruleCount schemaWitness.2 .rdfs13 = 1

/- The chains those rows produce, resolved one level. -/
#guard ruleAndPremises schemaWitness.2 ⟨.iri exA, rdfType, .iri exC⟩
  = some (.rdfs2, [⟨.iri exQ, rdfsDomain, .iri exC⟩, ⟨.iri exA, exQ, .iri exB⟩])
#guard ruleAndPremises schemaWitness.2 ⟨.iri exA, exQ, .iri exB⟩
  = some (.rdfs7, [⟨.iri exP, rdfsSubPropertyOf, .iri exQ⟩,
                   ⟨.iri exA, exP, .iri exB⟩])
#guard ruleAndPremises schemaWitness.2 ⟨.iri exC, rdfsSubClassOf, .iri exE⟩
  = some (.rdfs11, [⟨.iri exC, rdfsSubClassOf, .iri exD⟩,
                    ⟨.iri exD, rdfsSubClassOf, .iri exE⟩])
#guard ruleAndPremises schemaWitness.2 ⟨.iri exP, rdfsSubPropertyOf, .iri exR⟩
  = some (.rdfs5, [⟨.iri exP, rdfsSubPropertyOf, .iri exQ⟩,
                   ⟨.iri exQ, rdfsSubPropertyOf, .iri exR⟩])
#guard ruleAndPremises schemaWitness.2 ⟨.iri rdf1, rdfsSubPropertyOf, .iri rdfsMember⟩
  = some (.rdfs12, [⟨.iri rdf1, rdfType, .iri rdfsContainerMembershipProperty⟩])
#guard ruleAndPremises schemaWitness.2 ⟨.iri xsdString, rdfsSubClassOf, .iri rdfsLiteral⟩
  = some (.rdfs13, [⟨.iri xsdString, rdfType, .iri rdfsDatatype⟩])

/-! ## The one graph where rdfD2 is the first producer

`ex:p` occurs only in predicate position, so no rdfs-core row can
type it as a property and rdfD2's conclusion survives deduplication.
Without a case like this the rdfD2 row would be silent in every
witness and no `#guard` would notice. -/

private def dataOnlyGraph : Graph := [⟨.iri exA, exP, .iri exB⟩]
private def dataOnlyWitness : Graph × Derivation :=
  fullClosureWithProof [] [] dataOnlyGraph

#guard dataOnlyWitness.1.length = 147
#guard premisesPointBackwards dataOnlyWitness.2
#guard ruleCount dataOnlyWitness.2 .rdfD2 = 1
#guard ruleAndPremises dataOnlyWitness.2 ⟨.iri exP, rdfType, .iri rdfProperty⟩
  = some (.rdfD2, [⟨.iri exA, exP, .iri exB⟩])

/-! ## Axiom audit — expect propext / Classical.choice / Quot.sound only -/

#print axioms L4Factoidal.RDFS.fullClosureWithProof_graph
#print axioms L4Factoidal.RDFS.fullClosureWithProof_conclusions
#print axioms L4Factoidal.RDFS.fullClosureWithProof_sound
#print axioms L4Factoidal.RDFS.fullClosureWithProof_premises_lt
#print axioms L4Factoidal.RDFS.fullClosureWithProof_wellTagged
#print axioms L4Factoidal.RDFS.annStepConclusions_conclusions

end L4Factoidal.RDFS
