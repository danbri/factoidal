/-
L4Factoidal.OWL.Semantics — the semantic conditions the RL rules read.

Ports the condition family of `formal/fstar/OWL.Semantics.fst`. The
interpretation structure itself is in `RDF.Semantics`; this module adds
the semantic SEQUENCES and one `Prop` per condition, each cited to the
OWL 2 RDF-Based Semantics table row it comes from.

## Every condition is the WEAKEST reading its table row implies

Only-if halves and IP/IC membership side conditions are dropped unless
the row is itself stated as an iff. That is deliberate and it is the
safe direction: dropping a condition ENLARGES the class of
interpretations, and a soundness result over a larger class is a
stronger statement. A rule proved sound against these conditions is
therefore sound against genuine OWL 2 RDF-Based interpretations.

Three rows ARE stated as iffs, because two engine rules read opposite
halves of one condition: `sameAsIdentity`, `hasValue` (cls-hv1 forward,
cls-hv2 backward) and `inverseOf` (prp-inv1, prp-inv2). Weakening those
to one direction would leave the second rule of each pair unlicensed.

## What is NOT here, and why

The F\* module also carries five INDEX well-formedness predicates
(`ig_wf_pred`, `ig_wf_sp`, `ig_wf_subj`, `ig_wf_obj`, `ig_wf_po`) about
the shape of its `indexed_graph` bucket snapshot. They have no
counterpart here: the Lean tree's index is `OWL.RL.Index`, a
`Std.HashMap`-backed structure whose lookups are total functions with
their own lemmas rather than string-keyed buckets needing a key
injectivity side condition. Transcribing predicates about a data
structure this tree does not have would be a second copy of nothing.
-/
import L4Factoidal.RDF.Semantics
import L4Factoidal.OWL.Vocabulary

namespace L4Factoidal.OWL

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

/-! ## Semantic sequences

OWL 2 RDF-Based Semantics §3: "s is a sequence of a₁ … aₙ over IR"
when there are l₁ … lₙ with l₁ = s, `⟨lₖ, aₖ⟩ ∈ IEXT(I(rdf:first))`,
`⟨lₖ, lₖ₊₁⟩ ∈ IEXT(I(rdf:rest))`, and lₙ₊₁ = I(rdf:nil). The element
list is the induction handle. -/

def SeqIs (i : Interp) : i.idom → List i.idom → Prop
  | l, [] => l = i.iIri rdfNil
  | l, x :: rest =>
      ∃ l' : i.idom, i.iext (i.iIri rdfFirst) l x ∧
        i.iext (i.iIri rdfRest) l l' ∧ SeqIs i l' rest

/-! ## RDFS-level conditions

RDF 1.1 Semantics §9, identically present in OWL 2 RDF-Based Semantics
Table 5.8. -/

/-- `rdfs:domain`: if `⟨p, c⟩ ∈ IEXT(I(rdfs:domain))` and
`⟨x, y⟩ ∈ IEXT(p)` then `x ∈ ICEXT(c)`. -/
def CondDomain (i : Interp) : Prop :=
  ∀ p c x y : i.idom, i.iext (i.iIri rdfsDomain) p c → i.iext p x y → icext i x c

/-- `rdfs:range`, the dual: the OBJECT falls in the class. -/
def CondRange (i : Interp) : Prop :=
  ∀ p c x y : i.idom, i.iext (i.iIri rdfsRange) p c → i.iext p x y → icext i y c

def CondDomainSubclass (i : Interp) : Prop :=
  ∀ p c1 c2 : i.idom, i.iext (i.iIri rdfsDomain) p c1 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2 → i.iext (i.iIri rdfsDomain) p c2

def CondRangeSubclass (i : Interp) : Prop :=
  ∀ p c1 c2 : i.idom, i.iext (i.iIri rdfsRange) p c1 →
    i.iext (i.iIri rdfsSubClassOf) c1 c2 → i.iext (i.iIri rdfsRange) p c2

def CondDomainSubprop (i : Interp) : Prop :=
  ∀ p1 p2 c : i.idom, i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsDomain) p2 c → i.iext (i.iIri rdfsDomain) p1 c

def CondRangeSubprop (i : Interp) : Prop :=
  ∀ p1 p2 c : i.idom, i.iext (i.iIri rdfsSubPropertyOf) p1 p2 →
    i.iext (i.iIri rdfsRange) p2 c → i.iext (i.iIri rdfsRange) p1 c

/-! ## Equality

Table 5.2: `IEXT(I(owl:sameAs)) = { ⟨x, y⟩ | x = y }`. Stated as the
full iff — both directions are exactly what the table asserts. -/

def CondSameAsIdentity (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlSameAs) x y ↔ x = y

def CondSameAsReflexive (i : Interp) : Prop :=
  ∀ x : i.idom, i.iext (i.iIri owlSameAs) x x

/-- `owl:differentFrom` states DISTINCTNESS, which is symmetric in its
two arguments, so the relation the table defines is symmetric. -/
def CondDifferentFromSymmetric (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlDifferentFrom) x y →
    i.iext (i.iIri owlDifferentFrom) y x

/-! ## Property characteristics — Table 5.14 -/

def CondSymmetric (i : Interp) : Prop :=
  ∀ p x y : i.idom, icext i p (i.iIri owlSymmetricProperty) →
    i.iext p x y → i.iext p y x

def CondTransitive (i : Interp) : Prop :=
  ∀ p x y z : i.idom, icext i p (i.iIri owlTransitiveProperty) →
    i.iext p x y → i.iext p y z → i.iext p x z

def CondFunctional (i : Interp) : Prop :=
  ∀ p x y z : i.idom, icext i p (i.iIri owlFunctionalProperty) →
    i.iext p x y → i.iext p x z → y = z

/-- `owl:inverseOf`: `⟨p, q⟩ ∈ IEXT(I(owl:inverseOf))` exactly when
EXT(q) is the converse of EXT(p). Stated as the full iff, because
prp-inv1 and prp-inv2 read opposite halves of it. -/
def CondInverseOf (i : Interp) : Prop :=
  ∀ p q x y : i.idom, i.iext (i.iIri owlInverseOf) p q →
    (i.iext p x y ↔ i.iext q y x)

def CondInverseOfSymmetric (i : Interp) : Prop :=
  ∀ p q : i.idom, i.iext (i.iIri owlInverseOf) p q →
    i.iext (i.iIri owlInverseOf) q p

def CondPropertyDisjointWithSymmetric (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlPropertyDisjointWith) x y →
    i.iext (i.iIri owlPropertyDisjointWith) y x

/-! ## Class relations — Tables 5.8, 5.9, 5.14, 5.15 -/

def CondEquivalentClass (i : Interp) : Prop :=
  ∀ c d : i.idom, i.iext (i.iIri owlEquivalentClass) c d →
    i.iext (i.iIri rdfsSubClassOf) c d ∧ i.iext (i.iIri rdfsSubClassOf) d c

def CondEquivalentProperty (i : Interp) : Prop :=
  ∀ p q : i.idom, i.iext (i.iIri owlEquivalentProperty) p q →
    i.iext (i.iIri rdfsSubPropertyOf) p q ∧ i.iext (i.iIri rdfsSubPropertyOf) q p

def CondEquivalentClassSymmetric (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlEquivalentClass) x y →
    i.iext (i.iIri owlEquivalentClass) y x

def CondEquivalentPropertySymmetric (i : Interp) : Prop :=
  ∀ p q : i.idom, i.iext (i.iIri owlEquivalentProperty) p q →
    i.iext (i.iIri owlEquivalentProperty) q p

/-- The converse of `CondEquivalentClass`: mutual subclass makes two
classes equivalent, since the table states equality of class
extensions. -/
def CondMutualSubclassEquivalent (i : Interp) : Prop :=
  ∀ c d : i.idom, i.iext (i.iIri rdfsSubClassOf) c d →
    i.iext (i.iIri rdfsSubClassOf) d c → i.iext (i.iIri owlEquivalentClass) c d

def CondMutualSubpropertyEquivalent (i : Interp) : Prop :=
  ∀ p q : i.idom, i.iext (i.iIri rdfsSubPropertyOf) p q →
    i.iext (i.iIri rdfsSubPropertyOf) q p →
    i.iext (i.iIri owlEquivalentProperty) p q

def CondDisjointWithSymmetric (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlDisjointWith) x y →
    i.iext (i.iIri owlDisjointWith) y x

def CondComplementOfDisjoint (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlComplementOf) x y →
    i.iext (i.iIri owlDisjointWith) x y ∧ i.iext (i.iIri owlDisjointWith) y x

def CondComplementOfSymmetric (i : Interp) : Prop :=
  ∀ x y : i.idom, i.iext (i.iIri owlComplementOf) x y →
    i.iext (i.iIri owlComplementOf) y x

def CondRestrictionSubclassOfClass (i : Interp) : Prop :=
  ∀ x : i.idom, icext i x (i.iIri owlRestriction) → icext i x (i.iIri owlClass)

/-! ## Sequence-indexed conditions -/

/-- `owl:oneOf` — Table 5.9: every listed member is in the class
extension. The forward half is what the rule needs. -/
def CondOneOf (i : Interp) : Prop :=
  ∀ (c l : i.idom) (elems : List i.idom), i.iext (i.iIri owlOneOf) c l →
    SeqIs i l elems → ∀ x ∈ elems, icext i x c

def CondIntersectionOf (i : Interp) : Prop :=
  ∀ (c l : i.idom) (elems : List i.idom) (x : i.idom),
    i.iext (i.iIri owlIntersectionOf) c l → SeqIs i l elems →
    icext i x c → ∀ ci ∈ elems, icext i x ci

def CondUnionOf (i : Interp) : Prop :=
  ∀ (c l : i.idom) (elems : List i.idom) (ci : i.idom),
    i.iext (i.iIri owlUnionOf) c l → SeqIs i l elems →
    ci ∈ elems → i.iext (i.iIri rdfsSubClassOf) ci c

/-- A property chain composed with ITSELF makes the property
transitive — the specialisation of the chain row to Q = P₁ = P₂. -/
def CondChain2Transitive (i : Interp) : Prop :=
  ∀ p l : i.idom, i.iext (i.iIri owlPropertyChainAxiom) p l →
    SeqIs i l [p, p] → icext i p (i.iIri owlTransitiveProperty)

/-- The GENERAL two-hop chain, with the three properties unconstrained
by each other. Distinct from the row above, which is its
self-composition case. -/
def CondChain2Compose (i : Interp) : Prop :=
  ∀ q l p1 p2 x y z : i.idom, i.iext (i.iIri owlPropertyChainAxiom) q l →
    SeqIs i l [p1, p2] → i.iext p1 x y → i.iext p2 y z → i.iext q x z

def CondHasKey (i : Interp) : Prop :=
  ∀ (c l x y : i.idom) (pterms : List i.idom),
    i.iext (i.iIri owlHasKey) c l → SeqIs i l pterms →
    icext i x c → icext i y c →
    (∀ p ∈ pterms, ∃ v : i.idom, i.iext p x v ∧ i.iext p y v) →
    x = y

/-! ## Restrictions — Table 8 -/

/-- `owl:hasValue`. Stated as the full iff: cls-hv1 reads the forward
direction and cls-hv2 the backward one, so one condition serves both
rules and weakening it would leave cls-hv2 unlicensed. -/
def CondHasValue (i : Interp) : Prop :=
  ∀ x p v u : i.idom, i.iext (i.iIri owlOnProperty) x p →
    i.iext (i.iIri owlHasValue) x v → (icext i u x ↔ i.iext p u v)

/-- `owl:allValuesFrom`. One-directional, because the table's own
AllValuesFrom condition is one-directional — it constrains ICEXT(x) by
a universal, not by an equality. -/
def CondAllValuesFrom (i : Interp) : Prop :=
  ∀ x p d u v : i.idom, i.iext (i.iIri owlOnProperty) x p →
    i.iext (i.iIri owlAllValuesFrom) x d → icext i u x → i.iext p u v →
    icext i v d

/-! ## The pilot bundle

Every OWL 2 RDF-Based interpretation, with any datatype map, satisfies
all five. So entailment under this bundle is WEAKER than RDF-Based
entailment, which is the safe direction for soundness. -/

def OwlRlPilotConditions (i : Interp) : Prop :=
  CondDomain i ∧ CondRange i ∧ CondSymmetric i ∧
  CondSameAsIdentity i ∧ CondOneOf i

def PilotEntails (g1 g2 : Graph) : Prop := EntailsUnder OwlRlPilotConditions g1 g2

/-! ## The bundle is SATISFIABLE, and satisfiable NON-TRIVIALLY

A condition bundle nothing satisfies makes every `EntailsUnder`
statement about it vacuously true. So does a bundle satisfied only by
the interpretation whose IEXT is everywhere true, which satisfies every
graph and would leave `PilotEntails` as the everything-relation. Both
are ruled out below.

The F\* tree keeps these witnesses in a separate module,
`RDF.Semantics.HypothesisWitness`, written after a draft theorem whose
hypothesis was FALSE verified cleanly and proved nothing. -/

/-- The one-element interpretation with an everywhere-true IEXT. -/
def trivialInterp : Interp :=
  { idom := Unit, idomWit := (), iIri := fun _ => (), iLit := fun _ => (),
    iTt := fun _ _ _ => (), iext := fun _ _ _ => True }

theorem trivial_satisfies_pilot : OwlRlPilotConditions trivialInterp := by
  refine ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
          fun _ _ _ _ _ => trivial, fun x y => ?_, fun _ _ _ _ _ _ _ => trivial⟩
  constructor
  · intro _; rfl
  · intro _; trivial

/-- Non-triviality needs its own shape, and the reason is worth
recording: `CondSameAsIdentity` is an IFF, so an interpretation whose
IEXT relates everything fails it. The pilot's separating interpretation
therefore makes IEXT of the resource `owl:sameAs` denotes exactly the
diagonal and lets every other resource relate everything — which in
turn needs `owl:sameAs` to denote something no other IRI denotes. That
is the only place two IRIs have to be told apart. -/
def separatingInterp : Interp :=
  { idom := Bool, idomWit := true
  , iIri := fun a => a != owlSameAs
  , iLit := fun _ => true
  , iTt := fun _ _ _ => true
  , iext := fun p x y => p = true ∨ x = y }

theorem separating_satisfies_pilot : OwlRlPilotConditions separatingInterp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p c x y _ _; exact Or.inl (by simp [separatingInterp]; decide)
  · intro p c x y _ _; exact Or.inl (by simp [separatingInterp]; decide)
  · intro p x y _ hxy
    rcases hxy with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · intro x y
    constructor
    · rintro (h | h)
      · exact absurd h (by simp [separatingInterp])
      · exact h
    · intro h; exact Or.inr h
  · intro c l elems _ _ x _; exact Or.inl (by simp [separatingInterp]; decide)

/-- A graph the separating interpretation does NOT satisfy: its
predicate is `owl:sameAs`, whose IEXT is the diagonal, and its subject
and object denote different resources precisely because `owl:sameAs` is
the one IRI told apart. -/
def unsatTriple : Triple :=
  ⟨.iri ⟨"http://e.org/s", by decide⟩, owlSameAs, .iri owlSameAs⟩

theorem separating_rejects : ¬ Satisfies separatingInterp [unsatTriple] := by
  rintro ⟨a, ha⟩
  have h := ha unsatTriple (List.mem_singleton.mpr rfl)
  simp [TripleHolds, denotSubject, denotTerm, separatingInterp, unsatTriple] at h
  exact absurd h (by decide)

/-- Therefore `PilotEntails` is not the everything-relation: the empty
graph does not pilot-entail `unsatTriple`. Without this, every
soundness statement of the form `PilotEntails g1 g2` would be
uninformative — which is the failure mode the whole witness section
exists to rule out. -/
theorem pilot_not_everything : ¬ PilotEntails [] [unsatTriple] := by
  intro h
  exact separating_rejects
    (h separatingInterp separating_satisfies_pilot
       ⟨fun _ => true, fun _ hm => absurd hm (by simp)⟩)

end L4Factoidal.OWL
