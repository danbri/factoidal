/-
L4Factoidal.OWL.TableauTheorems — soundness of the clash calculus.

The theorem the F* tree could not host (external advisor caution,
quoted in https://github.com/danbri/factoidal/issues/468): a refuted
ABox has no model, by structural induction on the clash derivation —
no solver, no hints, no `sorry`, no user axiom.

Each induction case is the model-theoretic argument that
`formal/fstar/Tableau.Refute.fst` carries as a comment on the
corresponding clash rule. Here the argument is machine-checked.
-/
import L4Factoidal.OWL.Tableau

namespace L4Factoidal.OWL

/-- Soundness of the forward layer: models satisfy every derived
    fact. -/
theorem derives_sound {δ : Type} {I : Interp δ} {ν : Ind → δ}
    {A : List Assertion} {φ : Assertion}
    (h : Derives A φ) (hM : SatAll I ν A) : Satisfies I ν φ := by
  induction h with
  | hyp hφ => exact hM _ hφ
  | conjE1 _ ih => exact ih.1
  | conjE2 _ ih => exact ih.2
  | allE _ _ ihAll ihRel => exact ihAll _ ihRel

/-- Satisfaction only reads the assignment at the individuals NAMED in
    the assertion (concepts in this fragment name none), so two
    assignments that agree there satisfy the same assertions. This is
    the whole reason the ∃-rule's fresh witness is harmless to the
    rest of the ABox. -/
theorem satisfies_agree {δ : Type} {I : Interp δ} {ν ν' : Ind → δ}
    {φ : Assertion} (h : ∀ i ∈ φ.inds, ν' i = ν i)
    (hs : Satisfies I ν φ) : Satisfies I ν' φ := by
  cases φ with
  | inst a c =>
      have ha : ν' a = ν a := h a (by simp [Assertion.inds])
      simpa [Satisfies, ha] using hs
  | rel r a b =>
      have ha : ν' a = ν a := h a (by simp [Assertion.inds])
      have hb : ν' b = ν b := h b (by simp [Assertion.inds])
      simpa [Satisfies, ha, hb] using hs
  | diff a b =>
      have ha : ν' a = ν a := h a (by simp [Assertion.inds])
      have hb : ν' b = ν b := h b (by simp [Assertion.inds])
      simpa [Satisfies, ha, hb] using hs

/-- Every individual named in a derived fact is already named in the
    ABox: the forward rules invent no names. (This is what turns the
    ∃-rule's `x ∉ indsOf A` into `x ≠ a` for the derived `∃r.C` at
    `a`.) -/
theorem derives_inds {A : List Assertion} {φ : Assertion}
    (h : Derives A φ) : ∀ i ∈ φ.inds, i ∈ indsOf A := by
  induction h with
  | hyp hφ =>
      intro i hi
      exact List.mem_flatMap.mpr ⟨_, hφ, hi⟩
  | conjE1 _ ih => exact ih
  | conjE2 _ ih => exact ih
  | allE _ _ _ ihRel =>
      intro i hi
      simp only [Assertion.inds, List.mem_singleton] at hi
      subst hi
      exact ihRel _ (by simp [Assertion.inds])

/-- Mapping a pairwise-related list preserves pairwiseness along a
    relation transformer. (Kept local: core-library-independent, and
    the mathlib name for it is not available under the
    zero-dependency rule.) -/
theorem pairwise_map_of {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (h : ∀ a b, R a b → S (f a) (f b)) :
    ∀ {l : List α}, l.Pairwise R → (l.map f).Pairwise S := by
  intro l hl
  induction hl with
  | nil => exact List.Pairwise.nil
  | cons ha _ ih =>
      refine List.Pairwise.cons ?_ ih
      intro b hb
      have ⟨a', ha', hfa⟩ := List.mem_map.mp hb
      exact hfa ▸ h _ _ (ha a' ha')

/-- SOUNDNESS: a refuted ABox has no model. Structural induction on
    the clash derivation. The disjunction-branching case — the
    specific subject of the SMT-wall caution — is the last `cases`
    block. -/
theorem refuted_sound {A : List Assertion} (h : Refuted A) :
    ∀ {δ : Type} (I : Interp δ) (ν : Ind → δ), ¬ SatAll I ν A := by
  induction h with
  | clash hc hnc =>
      intro δ I ν hM
      exact (derives_sound hnc hM) (derives_sound hc hM)
  | botClash hb =>
      intro δ I ν hM
      exact derives_sound hb hM
  | minMaxClash hmin hmax =>
      intro δ I ν hM
      have ⟨l, hw⟩ := derives_sound hmin hM
      exact (derives_sound hmax hM) ⟨l, hw⟩
  | maxClash l hmax hlen hdiff hrel =>
      intro δ I ν hM
      apply derives_sound hmax hM
      refine ⟨l.map ν, ?_, ?_, ?_⟩
      · simpa using hlen
      · refine pairwise_map_of ν ?_ hdiff
        intro x y hxy
        cases hxy with
        | inl hd => exact derives_sound hd hM
        | inr hd => exact (derives_sound hd hM).symm
      · intro y hy
        have ⟨b, hb, hfb⟩ := List.mem_map.mp hy
        exact hfb ▸ derives_sound (hrel b hb) hM
  | disjSplit hdisj _ _ ihc ihd =>
      intro δ I ν hM
      cases derives_sound hdisj hM with
      | inl hc =>
          exact ihc I ν (by
            intro φ hφ
            cases hφ with
            | head => exact hc
            | tail _ hφ' => exact hM _ hφ')
      | inr hd =>
          exact ihd I ν (by
            intro φ hφ
            cases hφ with
            | head => exact hd
            | tail _ hφ' => exact hM _ hφ')
  | @exWitness A' a r c x hex hfresh _ ih =>
      intro δ I ν hM
      -- The semantic witness ∃r.C guarantees.
      have ⟨y, hry, hcy⟩ := derives_sound hex hM
      -- Bend the assignment at the fresh name only.
      have hax : a ≠ x := fun h =>
        hfresh (h ▸ derives_inds hex a (by simp [Assertion.inds]))
      refine ih I (fun i => if i = x then y else ν i) ?_
      intro φ hφ
      cases hφ with
      | head =>
          show I.role r (if a = x then y else ν a) (if x = x then y else ν x)
          rw [if_neg hax, if_pos rfl]
          exact hry
      | tail _ hφ' =>
          cases hφ' with
          | head =>
              show I.sem c (if x = x then y else ν x)
              rw [if_pos rfl]
              exact hcy
          | tail _ hφ'' =>
              refine satisfies_agree ?_ (hM _ hφ'')
              intro i hi
              have hix : i ≠ x := fun h =>
                hfresh (h ▸ List.mem_flatMap.mpr ⟨_, hφ'', hi⟩)
              exact if_neg hix

/-- The corollary in the shape the runner cares about. -/
theorem refuted_not_consistent {A : List Assertion} (h : Refuted A) :
    ¬ Consistent A := by
  intro ⟨δ, I, ν, hM⟩
  exact refuted_sound h I ν hM

end L4Factoidal.OWL
