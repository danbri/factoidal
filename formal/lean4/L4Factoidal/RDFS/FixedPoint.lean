/-
L4Factoidal.RDFS.FixedPoint — is the length test a real fixed-point test?

Port of `formal/fstar/RDF.Entailment.RDFS.FixedPoint.fst` (1,566 lines).

## The question the F\* module asks

`closure g fuel` stops early when one round leaves the LENGTH unchanged:

    | n + 1 => let g' := step g
               if g'.length = g.length then g else closure g' n

A length test is not obviously a fixed-point test. If a round could both
ADD a new triple and DROP an old one, the length would be unchanged while
the content changed, and the loop would stop at a graph that is not
saturated — every completeness result downstream would then be resting
on a stopping rule that does not mean what it says.

The F\* module could not close that question. Its own banner states the
finding: the length test is faithful there ONLY modulo a key-injectivity
gap, and that gap is WIDER than the one tracked for the index keys,
because `graph_dedup_sort`'s key folds literal content through an ad hoc
`"^^"` join rather than a control-character separator. So the F\* module
proves saturation-stability in the form its machinery supports and STOPS
at the length-test theorem with an account of what blocks it.

## Why this tree can close it

The blockage is a consequence of ONE design decision, not of the rule
tables. The F\* round ends in `graph_dedup_sort`: it re-sorts the whole
graph by a string key and drops key-duplicates, so a round can both add
and drop.

`RDFS.step` here is `addAll g (stepConclusions g)`, and `addAll` folds
`Graph.add`:

    def Graph.add (t : Triple) (g : Graph) : Graph :=
      if g.mem t then g else g ++ [t]

It appends or does nothing. It never drops, never reorders, and never
consults a key. A round therefore cannot lose a triple, so the length
can only stay equal by nothing having been added — and that IS the
fixed point. `step_eq_of_length_eq` (`ClosureTheorems.lean`) proves it
with no hypothesis at all.

This module states the semantic fixed point directly, membership-wise
and with no length bookkeeping in it, and proves it EQUIVALENT to the
length test. That equivalence is the F\* module's theorem (a), the one it
had to stop short of.

## What is not claimed

Nothing here says the F\* proof is wrong. It says the obligation is
absent under a different `add`. If this tree ever adopts a key-sorted
dedup for the closure round — for an on-disk closure, say — the
obligation returns and the F\* module is the account to follow.
-/
import L4Factoidal.RDFS.ClosureTheorems

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## The semantic fixed point

Membership-wise, in the engine's own equality, and with no reference to
lengths, sorting or keys. -/

/-- One more round derives nothing the graph does not already hold. -/
def StepSaturated (g : Graph) : Prop :=
  ∀ t, Graph.mem t (step g) = true → Graph.mem t g = true

/-- Equivalently, every conclusion of the round is already present. This
is the form a rule-by-rule argument produces. -/
def ConclusionsPresent (g : Graph) : Prop :=
  ∀ t ∈ stepConclusions g, Graph.mem t g = true

/-! ## Extensivity, with no side condition

The F\* module proves the twelve-rule chain extensive unconditionally and
then needs a `no_dup_keys` canonicity hypothesis for the final
`graph_dedup_sort`. There is no dedup-sort here, so the hypothesis has
nothing to attach to. -/

theorem step_extensive (g : Graph) : ∀ t ∈ g, t ∈ step g :=
  fun _ h => mem_step_of_mem h

theorem step_extensive_mem (g : Graph) {t : Triple} (h : Graph.mem t g = true) :
    Graph.mem t (step g) = true := by
  obtain ⟨u, hu, hue⟩ := exists_of_graphMem h
  exact graphMem_of_exists ⟨u, mem_step_of_mem hu, hue⟩

/-- A round never shortens the graph. This is the fact the whole module
turns on, and it is `Graph.add`'s definition rather than an argument
about keys. -/
theorem length_le_step (g : Graph) : g.length ≤ (step g).length :=
  length_le_addAll _ g

/-! ## Adding what is already there changes nothing -/

theorem addAll_eq_of_all_mem : ∀ (ts : List Triple) (g : Graph),
    (∀ t ∈ ts, Graph.mem t g = true) → addAll g ts = g := by
  intro ts
  induction ts with
  | nil => intro g _; rfl
  | cons u rest ih =>
      intro g h
      have hu : Graph.mem u g = true := h u (by simp)
      have hadd : g.add u = g := by simp [Graph.add, hu]
      simp only [addAll, hadd]
      exact ih g (fun t ht => h t (by simp [ht]))

/-! ## The three forms agree

`ConclusionsPresent` (rule-by-rule), `StepSaturated` (semantic), and the
length test (what the loop actually runs) are one condition. -/

theorem step_eq_of_conclusionsPresent {g : Graph} (h : ConclusionsPresent g) :
    step g = g :=
  addAll_eq_of_all_mem _ g h

theorem conclusionsPresent_of_step_eq {g : Graph} (h : step g = g) :
    ConclusionsPresent g := by
  intro t ht
  have := graphMem_step_of_mem_conclusions ht
  rwa [h] at this

theorem stepSaturated_of_step_eq {g : Graph} (h : step g = g) : StepSaturated g := by
  intro t ht; rwa [h] at ht

theorem step_eq_of_stepSaturated {g : Graph} (h : StepSaturated g) : step g = g :=
  step_eq_of_conclusionsPresent
    (fun t ht => h t (graphMem_step_of_mem_conclusions ht))

/-- **The theorem the F\* module had to stop short of.** The length test
IS the fixed-point test — in both directions, with no key-injectivity
hypothesis, no canonicity hypothesis and no fragment. -/
theorem lengthTest_faithful (g : Graph) :
    (step g).length = g.length ↔ StepSaturated g := by
  constructor
  · intro h; exact stepSaturated_of_step_eq (step_eq_of_length_eq h)
  · intro h; rw [step_eq_of_stepSaturated h]

theorem lengthTest_iff_conclusionsPresent (g : Graph) :
    (step g).length = g.length ↔ ConclusionsPresent g := by
  constructor
  · intro h; exact conclusionsPresent_of_step_eq (step_eq_of_length_eq h)
  · intro h; rw [step_eq_of_conclusionsPresent h]

/-! ## Stability: a fixed point is where the loop stops, at every fuel -/

/-- A saturated graph is its own closure, however much fuel is spent.
The loop cannot walk past a fixed point. -/
theorem closure_eq_of_stepSaturated {g : Graph} (h : StepSaturated g) :
    ∀ fuel : Nat, closure g fuel = g := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ n =>
      have hs : step g = g := step_eq_of_stepSaturated h
      simp only [closure, hs]
      simp

/-- And the closure of a saturated graph stays saturated. -/
theorem closure_stepSaturated_of_stepSaturated {g : Graph} (h : StepSaturated g)
    (fuel : Nat) : StepSaturated (closure g fuel) := by
  rw [closure_eq_of_stepSaturated h fuel]; exact h

/-! ## What the loop delivers

`closure_saturated_or_underfueled` gives the dichotomy in terms of
`step (closure g fuel) = closure g fuel`. Through the equivalence above,
that is the SEMANTIC fixed point, so the dichotomy can be read without
mentioning `step` at all. -/

theorem closure_saturated_or_underfueled_semantic (fuel : Nat) (g : Graph) :
    StepSaturated (closure g fuel) ∨ g.length + fuel ≤ (closure g fuel).length := by
  rcases closure_saturated_or_underfueled fuel g with h | h
  · exact Or.inl (stepSaturated_of_step_eq h)
  · exact Or.inr h

/-- Completeness, restated at the semantic fixed point: a saturated
closure holds everything the graph derives. This is what the length test
being faithful BUYS — the stopping rule the engine runs is the condition
the completeness theorem needs. -/
theorem closure_complete_of_stepSaturated {g : Graph} {fuel : Nat}
    (hsat : StepSaturated (closure g fuel)) {t : Triple} (h : Derives g t) :
    Graph.mem t (closure g fuel) = true :=
  closure_complete_of_saturated (step_eq_of_stepSaturated hsat) h

/-! ## Pinned behaviour

A fixed-point module can be satisfied vacuously by a graph on which no
rule ever fires, so the pins below use a graph where a rule DOES fire
and check that the loop stops only after it has. -/

section Pins

private def exA : WfIri := ⟨"http://example/A", by decide⟩
private def exB : WfIri := ⟨"http://example/B", by decide⟩
private def exS : WfIri := ⟨"http://example/s", by decide⟩

/-- `s rdf:type A` and `A rdfs:subClassOf B`: rdfs9 fires once. -/
private def gSub : Graph :=
  [ { s := .iri exS, p := rdfType, o := .iri exA }
  , { s := .iri exA, p := rdfsSubClassOf, o := .iri exB } ]

/-! The graph is NOT saturated: one round adds a triple, so the length
test fails. Without this the pins below would be about a graph the
closure never touches. -/
#guard !((step gSub).length == gSub.length)

#guard (step gSub).length == gSub.length + 1

/-! One round is enough here, and the second round is the fixed point. -/
#guard (step (step gSub)).length == (step gSub).length

/-! The closure stops there and does not grow with more fuel. -/
#guard (closure gSub 1).length == (closure gSub 64).length

/-! The derived triple is in it. -/
#guard Graph.mem { s := .iri exS, p := rdfType, o := .iri exB } (closure gSub 8)

/-! Zero fuel returns the graph unchanged — the closure of a graph that
is NOT saturated is not saturated either, which is why the completeness
statements carry the hypothesis. -/
#guard (closure gSub 0) == gSub
#guard !((step (closure gSub 0)).length == (closure gSub 0).length)

/-! And an empty graph is saturated, so the loop stops at once. -/
#guard (step ([] : Graph)).length == ([] : Graph).length

end Pins

end L4Factoidal.RDFS
