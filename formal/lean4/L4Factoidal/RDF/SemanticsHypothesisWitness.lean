/-
L4Factoidal.RDF.SemanticsHypothesisWitness — satisfiability witnesses
for the hypotheses the refinement theorems restrict on.

Port of `formal/fstar/RDF.Semantics.HypothesisWitness.fst` (674 lines).

## Why this module exists

A theorem whose hypothesis is UNSATISFIABLE proves nothing and verifies
cleanly. That is not hypothetical in this project: the first draft of an
RDFS closure-soundness theorem in the F\* tree assumed a property of
every graph that is FALSE, and the prover reported all verification
conditions discharged. Until that was caught, the guard against a repeat
was a paragraph of prose. This module makes it machine-checked.

## What a witness has to be

NON-DEGENERATE. "The theorem holds of nothing" is exactly the failure
mode being guarded against, so a witness that is the empty graph or the
one-element everything-relation buys nothing on its own. Each bundle
therefore gets TWO witnesses:

* one showing the bundle is satisfiable at all — otherwise
  `EntailsUnder` over it is the everything-relation by vacuity;
* one showing it is satisfiable by an interpretation that does NOT
  satisfy some graph — otherwise `EntailsUnder` over it is the
  everything-relation for the opposite reason, because every
  interpretation in the class satisfies every graph.

Both failure modes end in the same place: a soundness theorem that says
nothing. The OWL pilot bundle's pair lives in `OWL.Semantics`; the RDF
and RDFS bundles' pair is here.
-/
import L4Factoidal.RDF.EntailmentRdfsModelTheory

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-! ## Shared vocabulary -/

def exIri : WfIri := ⟨"http://example.org/s", by decide⟩

def exLit : WfLiteral := Literal.string "v"

/-! ## 1. The bundles are CONSISTENT

Every condition is an implication whose conclusion is an `iext` atom,
so an interpretation whose IEXT is everywhere true satisfies all of
them. A one-element domain is used, matching the F\* witness, because
the OWL bundle's `sameAs` condition is an IFF whose forward half forces
`x = y` for every related pair — and `Unit` supplies exactly that. -/

def trivialInterp : Interp :=
  { idom := Unit, idomWit := (), iIri := fun _ => (), iLit := fun _ => (),
    iTt := fun _ _ _ => (), iext := fun _ _ _ => True }

theorem trivial_rdf_conditions : RdfConditions trivialInterp :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

theorem trivial_rdfs_conditions (D : DatatypeSet) :
    RdfsConditions D trivialInterp :=
  ⟨trivial_rdf_conditions, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
   fun _ _ => trivial, fun _ _ => trivial, fun _ => trivial,
   fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ => trivial,
   fun _ _ _ => ⟨trivial, trivial⟩,
   fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ => trivial,
   fun _ _ _ => ⟨trivial, trivial⟩,
   fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial,
   fun _ _ _ => trivial⟩

/-- A bundle satisfied by nothing makes every `EntailsUnder` statement
about it vacuously true. This rules that out for both rungs. -/
theorem rdf_conditions_satisfiable : ∃ i : Interp, RdfConditions i :=
  ⟨trivialInterp, trivial_rdf_conditions⟩

theorem rdfs_conditions_satisfiable (D : DatatypeSet) :
    ∃ i : Interp, RdfsConditions D i :=
  ⟨trivialInterp, trivial_rdfs_conditions D⟩

/-! ## 2. The bundles are satisfiable NON-TRIVIALLY

Part 1 alone is satisfied by the everywhere-true IEXT, which satisfies
EVERY graph — so it leaves open that `RdfsEntails` is the
everything-relation. This part closes that: a model of every condition
that does NOT satisfy some graph.

The shape: two truth values, every IRI denoting `true` and every
literal denoting `false`, and IEXT holding when the predicate is `true`
and either the object is `true` or the subject is `false`. Every
condition's conclusion is then reachable, and a triple with an IRI
subject and a LITERAL object is not. -/

def separatingInterp : Interp :=
  { idom := Bool, idomWit := true
  , iIri := fun _ => true
  , iLit := fun _ => false
  , iTt := fun _ _ _ => true
  , iext := fun p x y => p = true ∧ (y = true ∨ x = false) }

/-- Every axiomatic triple has an IRI object, which is what makes the
separating interpretation satisfy both axiom conditions. Checked by
evaluation over the transcribed tables rather than argued. -/
def objIsIri : Triple → Bool
  | ⟨_, _, .iri _⟩ => true
  | _ => false

theorem sep_holds_of_iri_object (a : BnodeAssignment separatingInterp.idom) :
    ∀ {t : Triple}, objIsIri t = true → TripleHolds separatingInterp a t
  | ⟨_, _, .iri _⟩, _ => ⟨rfl, Or.inl rfl⟩
  | ⟨_, _, .bnode _⟩, h => absurd h (by simp [objIsIri])
  | ⟨_, _, .literal _⟩, h => absurd h (by simp [objIsIri])
  | ⟨_, _, .tripleTerm _ _ _⟩, h => absurd h (by simp [objIsIri])

theorem sep_rdf_axioms : CondRdfAxioms separatingInterp := by
  intro a t h
  rcases h with hmem | ⟨i, _, rfl⟩
  · exact sep_holds_of_iri_object a (by
      have : rdfAxiomaticTriples.all objIsIri = true := by decide
      exact (List.all_eq_true.mp this) t hmem)
  · exact sep_holds_of_iri_object a rfl

theorem sep_rdfs_axioms : CondRdfsAxioms separatingInterp := by
  intro a t h
  rcases h with hmem | ⟨i, _, hrow⟩
  · exact sep_holds_of_iri_object a (by
      have : rdfsAxiomaticTriples.all objIsIri = true := by decide
      exact (List.all_eq_true.mp this) t hmem)
  · rcases hrow with rfl | rfl | rfl <;> exact sep_holds_of_iri_object a rfl

theorem separating_rdf_conditions : RdfConditions separatingInterp :=
  ⟨fun _ _ _ _ => ⟨rfl, Or.inl rfl⟩, sep_rdf_axioms⟩

theorem separating_rdfs_conditions (D : DatatypeSet) :
    RdfsConditions D separatingInterp := by
  refine ⟨separating_rdf_conditions, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, sep_rdfs_axioms⟩
  · intro p c x y h1 h2; exact ⟨rfl, Or.inl (by
      rcases h1 with ⟨_, hc | hp⟩
      · exact hc
      · exact absurd h2.1 (by simp [hp]))⟩
  · intro p c x y h1 h2; exact ⟨rfl, Or.inl (by
      rcases h1 with ⟨_, hc | hp⟩
      · exact hc
      · exact absurd h2.1 (by simp [hp]))⟩
  · intro _ _; exact ⟨rfl, Or.inl rfl⟩
  · intro _ _; exact ⟨rfl, Or.inl rfl⟩
  · intro _; exact ⟨rfl, Or.inl rfl⟩
  · intro x y u v h1 h2
    refine ⟨?_, h2.2⟩
    rcases h1 with ⟨_, hy | hx⟩
    · exact hy
    · exact absurd h2.1 (by simp [hx])
  · intro x y z h1 h2
    refine ⟨rfl, ?_⟩
    rcases h1.2 with hy | hx
    · rcases h2.2 with hz | hy'
      · exact Or.inl hz
      · exact absurd hy (by simp [hy'])
    · exact Or.inr hx
  · intro x _; exact ⟨rfl, by cases x <;> simp⟩
  · intro x y _; exact ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inl rfl⟩⟩
  · intro x y u h1 h2
    refine ⟨rfl, ?_⟩
    rcases h1.2 with hy | hx
    · exact Or.inl hy
    · rcases h2.2 with hx' | hu
      · exact absurd hx' (by simp [hx])
      · exact Or.inr hu
  · intro x y z h1 h2
    refine ⟨rfl, ?_⟩
    rcases h1.2 with hy | hx
    · rcases h2.2 with hz | hy'
      · exact Or.inl hz
      · exact absurd hy (by simp [hy'])
    · exact Or.inr hx
  · intro x _; exact ⟨rfl, by cases x <;> simp⟩
  · intro x y _; exact ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inl rfl⟩⟩
  · intro _ _; exact ⟨rfl, Or.inl rfl⟩
  · intro _ _; exact ⟨rfl, Or.inl rfl⟩
  · intro _ _; exact ⟨rfl, Or.inl rfl⟩

/-- The graph the separating interpretation refuses: an IRI subject and
a LITERAL object. Every IRI denotes `true` and every literal `false`,
and IEXT never relates `true` to `false`. -/
def unsatTriple : Triple := ⟨.iri exIri, exIri, .literal exLit⟩

theorem separating_rejects : ¬ Satisfies separatingInterp [unsatTriple] := by
  rintro ⟨a, ha⟩
  have h := ha unsatTriple (List.mem_singleton.mpr rfl)
  rcases h.2 with h1 | h1 <;> simp [denotTerm, denotSubject, separatingInterp,
    unsatTriple] at h1

/-- **Both rungs' entailment relations are therefore NOT the
everything-relation.** Without this, every theorem of the form
`RdfsEntails D g1 g2` would be uninformative. -/
theorem rdf_entails_not_everything : ¬ RdfEntails [] [unsatTriple] := by
  intro h
  exact separating_rejects
    (h separatingInterp separating_rdf_conditions
       ⟨fun _ => true, fun _ hm => absurd hm (by simp)⟩)

theorem rdfs_entails_not_everything (D : DatatypeSet) :
    ¬ RdfsEntails D [] [unsatTriple] := by
  intro h
  exact separating_rejects
    (h separatingInterp (separating_rdfs_conditions D)
       ⟨fun _ => true, fun _ hm => absurd hm (by simp)⟩)

/-! ## 3. The data-side restriction predicates

The simple-entailment vertical's soundness theorem restricts on
`GraphExact` (the literals where the tree's coarser literal test cannot
diverge from term equality) and on `GraphTtFree`. Both are exhibited
non-degenerately: a non-empty graph satisfying each.

`GraphExact`'s witness is the one worth checking, because the predicate
excludes two specific literal shapes and a witness that happened to
contain neither by accident would not show the predicate is
satisfiable by anything interesting. -/

def witnessExact : Graph :=
  [ ⟨.iri exIri, exIri, .literal exLit⟩,
    ⟨.iri exIri, exIri, .iri exIri⟩,
    ⟨.bnode "b", exIri, .bnode "c"⟩ ]

theorem witnessExact_exact : GraphExact witnessExact := by
  intro t ht
  simp only [witnessExact, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;>
    simp [TripleExact, TermExact, LitExact, exLit, Literal.string] <;> decide

theorem witnessExact_ttFree : GraphTtFree witnessExact := by
  intro t ht
  simp only [witnessExact, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [TermTtFree]

/-- And it is not the empty graph, which would satisfy every data-side
predicate and show nothing. -/
theorem witnessExact_nonempty : witnessExact ≠ [] := by simp [witnessExact]

/-! ## 4. Where the answer is a GAP

The F\* module reaches only a DEGENERATE witness for two hypotheses —
the index well-formedness predicate on a composite key, and the closure
chain well-formedness predicate — and labels them as such rather than
quietly omitting them.

Neither has a counterpart here, and the reason is the same for both:
the Lean index (`OWL.RLClosureIndexed`) keys its buckets on STRUCTURED
values in a `Std.HashMap` — `Subject`, `WfIri`, `Subject × WfIri`,
`WfIri × Term` — instead of on strings concatenated with a U+001F
separator. So there is no key-injectivity side condition to discharge
(`Index.Wf.ofGraph` holds for every graph, with no hypothesis), and
therefore no separator-freeness invariant to carry through the closure
chain either. `RDF.Entailment.RDFS.ChainWf` and
`RDF.Indexed.KeyInjectivity` are not ported for that reason, not from
neglect; see
<https://github.com/danbri/factoidal/issues/559> and the F\*-only
section of `docs/designissues/2026-08-23-lean-port-gap.md`.

Recording that is the point. A witness module whose gaps are invisible
is the same failure as a theorem whose hypothesis is invisible. -/

end L4Factoidal.RDF
