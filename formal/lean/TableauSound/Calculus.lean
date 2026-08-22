/- The declarative clash calculus and its soundness theorem.

   Experiment tracked in
   https://github.com/danbri/factoidal/issues/468.

   Two layers, mirroring how the F* engine's verdicts decompose:

   * `Derives A φ` — positive facts obtainable from the ABox by
     forward rules (the analogue of Tableau.fst's positive-sound
     materialisation). Soundness: every model of `A` satisfies every
     derived fact.

   * `Refuted A` — the clash calculus (the analogue of
     Tableau.Refute.fst's `tableau_consistent = Some false`). One
     constructor per clash rule; `disjSplit` is the branching rule.
     Soundness: a refuted ABox has NO model — proved by structural
     induction on the derivation, no SMT involved.

   Every constructor is a certificate node: a `Refuted` derivation
   tree IS the clash certificate the F* engine would emit under the
   architecture-(c) plan in issue 468. -/

import TableauSound.Semantics

namespace TableauSound

/-- Forward derivation of facts from an ABox. Deliberately minimal:
    hypothesis, conjunction elimination, and the ∀-rule (value
    restriction applied across a known role edge). -/
inductive Derives (A : List Assertion) : Assertion → Prop where
  | hyp {φ} : φ ∈ A → Derives A φ
  | conjE1 {a c d} :
      Derives A (.inst a (.conj c d)) → Derives A (.inst a c)
  | conjE2 {a c d} :
      Derives A (.inst a (.conj c d)) → Derives A (.inst a d)
  | allE {a b r c} :
      Derives A (.inst a (.all r c)) → Derives A (.rel r a b) →
      Derives A (.inst b c)

/-- Soundness of the forward layer: models satisfy every derived
    fact. Structural induction; each case is the one-line
    model-theoretic argument the F* file carries as a comment. -/
theorem derives_sound {δ : Type} {I : Interp δ} {ν : Ind → δ}
    {A : List Assertion} {φ : Assertion}
    (h : Derives A φ) (hM : SatAll I ν A) : Satisfies I ν φ := by
  induction h with
  | hyp hφ => exact hM _ hφ
  | conjE1 _ ih => exact ih.1
  | conjE2 _ ih => exact ih.2
  | allE _ _ ihAll ihRel => exact ihAll _ ihRel

/-- The clash calculus. A constructor = a clash rule = a certificate
    node. `Prop`-valued here for the soundness development; the
    certificate-checker wave re-states it as a `Type` so trees can be
    serialized and checked. -/
inductive Refuted : List Assertion → Prop where
  /-- C ⊓ ¬C at one individual. -/
  | clash {A a c} :
      Derives A (.inst a c) → Derives A (.inst a (.neg c)) →
      Refuted A
  /-- owl:Nothing is uninhabited. -/
  | botClash {A a} :
      Derives A (.inst a .bot) → Refuted A
  /-- ≥(n+1) r together with ≤n r at one individual
      (the engine's C3/C4 count clash). -/
  | minMaxClash {A a n r} :
      Derives A (.inst a (.atLeast (n + 1) r)) →
      Derives A (.inst a (.atMost n r)) →
      Refuted A
  /-- ≤n r refuted by n+1 named successors that are pairwise
      provably distinct via owl:differentFrom (the engine's
      differentFrom-based max-card refutation). -/
  | maxClash {A a n r} (l : List Ind) :
      Derives A (.inst a (.atMost n r)) →
      l.length = n + 1 →
      l.Pairwise (fun x y => Derives A (.diff x y) ∨ Derives A (.diff y x)) →
      (∀ b ∈ l, Derives A (.rel r a b)) →
      Refuted A
  /-- Disjunction branching: if both extensions are refuted, the
      ABox is refuted. THE rule the SMT wall was about — here it is
      one induction case. -/
  | disjSplit {A a c d} :
      Derives A (.inst a (.disj c d)) →
      Refuted (.inst a c :: A) →
      Refuted (.inst a d :: A) →
      Refuted A

/-- Helper: mapping a pairwise-related list preserves pairwiseness
    along a relation transformer. (Core-library-independent.) -/
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
    the clash derivation. This is the theorem whose F*/SMT version
    the advisors warned against attempting on the 4,682-line engine
    file; over the declarative calculus it is short and hint-free. -/
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

/-- The headline corollary in the shape the runner cares about. -/
theorem refuted_not_consistent {A : List Assertion} (h : Refuted A) :
    ¬ Consistent A := by
  intro ⟨δ, I, ν, hM⟩
  exact refuted_sound h I ν hM

end TableauSound
