/-
L4Factoidal.SPARQL.JoinRefinement — layer 2 of the port of
`SPARQL11.Algebra.Refinement`: JOIN.

Layer 1 (`SPARQL/AlgebraRefinement.lean`) did UNION and FILTER at both
layers, and built the compatibility bridge between the engine's
`Binding.compatible` and §18.3's `Compatible`. This layer is what that
bridge was for.

## The engine's merge is a merge

`Binding.merge` PREPENDS each new binding, so it accumulates in reverse
and its result is not `mu1 ++ mu2`. §18.3 states merge as a RELATION on
`sval`, precisely so nothing depends on the layout, and `merge_isMerge`
is the bridge: whatever list the engine builds, it denotes the merge.

That is the lemma the whole layer rests on, and it is where the
prepending has to be handled — the induction generalises over the LEFT
mapping, because the engine grows it.

## Two directions, two hypotheses

* COMPLETENESS (`join_spec_complete`) needs `noRepeats` on the left
  mapping, inherited from layer 1's `compatible_of_Compatible`: the
  engine tests every pair in the list while `sval` sees only the
  first, so a duplicate-key list makes the two disagree.
* SOUNDNESS (`join_spec_sound`) needs `BindingLitExact` as well,
  because the engine's compatibility test is strictly coarser than
  §18.3's — `Literal.eqb` folds language-tag case. Layer 1's
  `compatible_not_Compatible_of_coarse` is the witness that the
  hypothesis cannot be dropped.

Neither hypothesis is decoration, and neither is a weakening of the
specification: they name the fragment on which the shipping engine
DECIDES the specification's relation.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.AlgebraRefinement

namespace L4Factoidal.SPARQL.AlgebraRefinement

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.AlgebraSpec

/-! ## The engine's merge denotes §18.3's merge -/

theorem merge_isMerge : ∀ (mu2 mu1 : SMap), IsMerge mu1 mu2 (Binding.merge mu1 mu2)
  | [], mu1 => by
      intro v
      simp only [Binding.merge, mergeAt]
      cases h : sval v mu1 <;> simp [sval]
  | (w, t) :: rest, mu1 => by
      intro v
      have hlk := binding_lookup_eq_sval w mu1
      cases hw : Binding.lookup w mu1 with
      | some tw =>
          have hsw : sval w mu1 = some tw := by rw [← hlk, hw]
          simp only [Binding.merge, hw]
          rw [merge_isMerge rest mu1 v]
          by_cases hv : v = w
          · subst hv
            simp only [mergeAt, hsw]
          · simp only [mergeAt, sval, List.lookup,
                       show (v == w) = false by simp [hv]]
      | none =>
          have hsw : sval w mu1 = none := by rw [← hlk, hw]
          simp only [Binding.merge, hw]
          rw [merge_isMerge rest ((w, t) :: mu1) v]
          by_cases hv : v = w
          · subst hv
            unfold mergeAt
            rw [hsw]
            simp [sval, List.lookup]
          · have hvw : (v == w) = false := by simp [hv]
            simp only [mergeAt, sval, List.lookup, hvw]

/-! ## What the engine's join contains -/

theorem mem_join {o1 o2 : SolutionSeq} {mu : Binding} (h : mu ∈ join o1 o2) :
    ∃ mu1 ∈ o1, ∃ mu2 ∈ o2, Binding.compatible mu1 mu2 = true ∧ mu = Binding.merge mu1 mu2 := by
  simp only [join, List.mem_flatMap] at h
  obtain ⟨mu1, hmu1, hin⟩ := h
  simp only [List.mem_filterMap] at hin
  obtain ⟨mu2, hmu2, heq⟩ := hin
  by_cases hc : Binding.compatible mu1 mu2
  · rw [if_pos hc] at heq
    exact ⟨mu1, hmu1, mu2, hmu2, hc, by simpa using heq.symm⟩
  · rw [if_neg hc] at heq; exact absurd heq (by simp)

theorem join_mem_of {o1 o2 : SolutionSeq} {mu1 mu2 : Binding}
    (h1 : mu1 ∈ o1) (h2 : mu2 ∈ o2) (hc : mu1.compatible mu2 = true) :
    mu1.merge mu2 ∈ join o1 o2 := by
  simp only [join, List.mem_flatMap]
  exact ⟨mu1, h1, by
    simp only [List.mem_filterMap]
    exact ⟨mu2, h2, by simp [hc]⟩⟩

/-! ## Against §18.5 -/

/-- **Completeness.** Everything §18.5's JOIN asks for is in the
engine's answer, up to `SMapEq` — which is the right equality, because
a solution mapping is a partial function and the engine's merge builds
its list in its own order. -/
theorem join_spec_complete {o1 o2 : SolutionSeq} {mu : SMap}
    (hwf : ∀ m ∈ o1, noRepeats (sdom m) = true)
    (h : InJoin o1 o2 mu) : Occurs mu (join o1 o2) := by
  obtain ⟨mu1, mu2, h1, h2, hcompat, hmerge⟩ := h
  have hc : Binding.compatible mu1 mu2 = true :=
    compatible_of_Compatible (hwf mu1 h1) hcompat
  refine ⟨Binding.merge mu1 mu2, join_mem_of h1 h2 hc, ?_⟩
  exact merge_unique hmerge (merge_isMerge mu2 mu1)

/-- **Soundness**, on the fragment where the engine's compatibility
test IS §18.3's relation. Without `BindingLitExact` the engine can join
a pair the specification does not — layer 1's
`compatible_not_Compatible_of_coarse` exhibits one. -/
theorem join_spec_sound {o1 o2 : SolutionSeq} {mu : Binding}
    (hex : ∀ m1 ∈ o1, ∀ m2 ∈ o2, Binding.compatible m1 m2 = true → Compatible m1 m2)
    (h : mu ∈ join o1 o2) : InJoin o1 o2 mu := by
  obtain ⟨mu1, h1, mu2, h2, hc, rfl⟩ := mem_join h
  exact ⟨mu1, mu2, h1, h2, hex mu1 h1 mu2 h2 hc, merge_isMerge mu2 mu1⟩

/-- Both directions where both hypotheses hold. -/
theorem join_spec_iff {o1 o2 : SolutionSeq} {mu : SMap}
    (hwf : ∀ m ∈ o1, noRepeats (sdom m) = true)
    (hex : ∀ m1 ∈ o1, ∀ m2 ∈ o2, Binding.compatible m1 m2 = true → Compatible m1 m2) :
    Occurs mu (join o1 o2) ↔ InJoin o1 o2 mu := by
  constructor
  · rintro ⟨m, hm, he⟩
    obtain ⟨mu1, mu2, h1, h2, hcp, hmg⟩ := join_spec_sound hex hm
    exact ⟨mu1, mu2, h1, h2, hcp, fun v => (he v).trans (hmg v)⟩
  · exact join_spec_complete hwf

/-! ## Commutativity, at the engine

§18.3's merge is symmetric on compatible arguments, so the engine's
join answers the same SET either way round. It does NOT answer the same
LIST — `Binding.merge` is order-sensitive — which is exactly why the
statement is about `Occurs` and not about list equality. -/

theorem join_comm_engine {o1 o2 : SolutionSeq} {mu : SMap}
    (hwf1 : ∀ m ∈ o1, noRepeats (sdom m) = true)
    (hwf2 : ∀ m ∈ o2, noRepeats (sdom m) = true)
    (hex : ∀ m1 ∈ o1, ∀ m2 ∈ o2, Binding.compatible m1 m2 = true → Compatible m1 m2)
    (h : Occurs mu (join o1 o2)) : Occurs mu (join o2 o1) := by
  have hin : InJoin o1 o2 mu := (join_spec_iff hwf1 hex).mp h
  exact join_spec_complete hwf2 (AlgebraSpec.join_comm hin)

/-! ## Build-time checks -/

private def vX : VarName := "x"
private def vY : VarName := "y"
private def iriA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iriB : WfIri := ⟨"http://example.org/b", by decide⟩

/-! Disjoint domains always join. -/
#guard (join [[(vX, Term.iri iriA)]] [[(vY, Term.iri iriB)]]).length == 1

/-! Agreeing on the shared variable joins; disagreeing does not. -/
#guard (join [[(vX, Term.iri iriA)]] [[(vX, Term.iri iriA)]]).length == 1
#guard (join [[(vX, Term.iri iriA)]] [[(vX, Term.iri iriB)]]).length == 0

/-! The merge really does carry both bindings. -/
#guard ((Binding.merge [(vX, Term.iri iriA)] [(vY, Term.iri iriB)]).lookup vY)
        == some (Term.iri iriB)
#guard ((Binding.merge [(vX, Term.iri iriA)] [(vY, Term.iri iriB)]).lookup vX)
        == some (Term.iri iriA)

/-! And the left mapping wins on a shared variable, as §18.3 says. -/
#guard ((Binding.merge [(vX, Term.iri iriA)] [(vX, Term.iri iriB)]).lookup vX)
        == some (Term.iri iriA)

/-! ## Axiom audit -/

#print axioms merge_isMerge
#print axioms join_spec_complete
#print axioms join_spec_sound
#print axioms join_comm_engine

end L4Factoidal.SPARQL.AlgebraRefinement
