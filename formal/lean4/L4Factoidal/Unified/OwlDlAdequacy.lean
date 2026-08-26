/-
L4Factoidal.Unified.OwlDlAdequacy — the stage 5 gate theorems for
OWL 2 Direct Semantics and the tableau, under the unified LBase/IKL
model theory.

Stage 5 of https://github.com/danbri/factoidal/issues/598, design
document `docs/designissues/2026-08-25-unified-semantics-lean.md` §4.5.

## What is proved here, and at what strength

* **`unified_adequate_dl`** — a FULL `↔` with no side conditions:
  the translation `owlDlDirect R A` has a CL model exactly when the
  ABox has a Direct-Semantics model respecting the role box
  (`OWL.Consistent`). Both directions come from
  `satisfiesAll_owlDlDirect_iff`, instantiated at `restrictInterpDL`
  and at `liftInterpDL`.
* **`refuted_unified_unsat`** — the clash calculus against the unified
  theory: a `Refuted` derivation tree is a proof that the translation
  has no model. Composes `OWL.refuted_not_consistent` (the branching
  induction, already landed in `OWL/TableauTheorems.lean`) with the
  `↔` above. This is the design document's `refuted_unified_unsat`,
  and the relation to the three-valued verdict contract of
  https://github.com/danbri/factoidal/issues/586 is:
  "inconsistent" (a refutation exists) ⇒ unified-unsatisfiable;
  "consistent" (a model exhibited) ⇒ unified-satisfiable, by the ←
  direction of `unified_adequate_dl`; "unknown" claims nothing.
* **`refuted_unified_entails_all`** — the explosion corollary.
* **`unified_sat_not_refuted`** — the contrapositive: exhibiting a
  model of the translation certifies that no refutation exists.

## The converse that is NOT proved

`¬ OWL.Consistent R A → OWL.Refuted R A` — completeness of the clash
calculus — is not available and is not claimed. `OWL/Tableau.lean`'s
`Refuted` has no blocking condition and no ⊔-saturation strategy;
`OWL/TableauTheorems.lean` proves soundness only. Recorded as gap row
1 of the stage 5 rows in `docs/theorem-registry.md` §9.

## Non-vacuity

The refutation gate would be worthless if `Refuted` held of nothing,
and the satisfiability gate would be worthless if every ABox were
satisfiable. The witnesses below are a SEPARATING PAIR that differs by
one `owl:differentFrom` assertion: without it the ABox is consistent
and the translation has a model; with it the ABox is refuted and the
translation has none. The equality machinery (`distinctBlock`, the
negated `CL.Sentence.eq` of `.diff`) is exactly what carries the
difference.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.OwlDlDirect

namespace L4Factoidal.Unified

/-! ## The stage 5 gate -/

/-- **Stage 5 gate theorem.** Direct-Semantics satisfiability of the
tableau fragment coincides with unified-theory satisfiability of the
direct translation. Full `↔`, no side conditions: the colon-carrying
name encoding of `Unified/OwlDlDirect.lean` removes the freshness
hypothesis, and `OWL.Interp` carries no conditions the CL side must
reproduce. -/
theorem unified_adequate_dl (R : OWL.RoleAxioms) (A : List OWL.Assertion) :
    (∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A)) ↔
      OWL.Consistent R A := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hR, hA⟩ := satisfiesAll_owlDlDirect_restrict i R A hi
    exact ⟨i.dom, restrictInterpDL i, dlNu i, hR, hA⟩
  · rintro ⟨δ, I, ν, hR, hA⟩
    exact ⟨liftInterpDL I ν, satisfiesAll_owlDlDirect_lift I ν R A hR hA⟩

/-- **Stage 5 gate, refutation side.** A tableau refutation proves the
translated theory unsatisfiable. The hypothesis is exactly
`OWL.Refuted R A` — the branching clash calculus including
`disjSplit`, `leqMerge` (the ABox-rewriting ≤-rule) and `exWitness`
(the fresh-individual ∃-rule); no fragment side condition is added
here, because `OWL.Concept` IS the fragment. -/
theorem refuted_unified_unsat {R : OWL.RoleAxioms} {A : List OWL.Assertion}
    (h : OWL.Refuted R A) :
    ¬ ∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A) := by
  intro hsat
  exact OWL.refuted_not_consistent h ((unified_adequate_dl R A).mp hsat)

/-- Explosion: a refuted ABox's translation entails every sentence. -/
theorem refuted_unified_entails_all {R : OWL.RoleAxioms}
    {A : List OWL.Assertion} (h : OWL.Refuted R A) (s : CL.Sentence) :
    Unified.Entails (owlDlDirect R A) s := by
  intro i _ hsat
  exact absurd ⟨i, hsat⟩ (refuted_unified_unsat h)

/-- The contrapositive, in the shape the three-valued verdict contract
of https://github.com/danbri/factoidal/issues/586 uses: a model of the
translation certifies that no refutation exists. -/
theorem unified_sat_not_refuted {R : OWL.RoleAxioms} {A : List OWL.Assertion}
    (h : ∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A)) :
    ¬ OWL.Refuted R A :=
  fun hr => refuted_unified_unsat hr h

/-- A Direct-Semantics model exhibited on the native side yields a
model of the translation — the "consistent" verdict direction, stated
separately because it is the half a model-building engine produces. -/
theorem consistent_unified_sat {R : OWL.RoleAxioms} {A : List OWL.Assertion}
    (h : OWL.Consistent R A) :
    ∃ i : CL.Interp, CL.SatisfiesAll i (owlDlDirect R A) :=
  (unified_adequate_dl R A).mpr h

/-! ## Non-vacuity: the separating pair

`nearClashAbox` and `clashAbox` differ by one `owl:differentFrom`
assertion. -/

/-- The all-true interpretation over a one-element domain. -/
def trivialDlInterp : OWL.Interp Unit where
  concept := fun _ _ => True
  role := fun _ _ _ => True

/-- A one-element domain has no two distinct elements — what makes
`atMost 1` true of `trivialDlInterp`. -/
theorem unit_no_pairwise_two :
    ∀ l : List Unit, l.length = 2 → ¬ l.Pairwise (· ≠ ·)
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], _ => fun h => (List.pairwise_cons.mp h).1 _ (by simp) rfl
  | _ :: _ :: _ :: _, h => by simp at h

/-- `at most 1 r` with two NAMED but not provably distinct
successors. Consistent: the two names may denote one element. -/
def nearClashAbox : List OWL.Assertion :=
  [ .inst "a" (.atMost 1 "r"), .rel "r" "a" "b", .rel "r" "a" "c" ]

/-- The same ABox with `owl:differentFrom` added. Refuted. -/
def clashAbox : List OWL.Assertion :=
  [ .inst "a" (.atMost 1 "r"), .rel "r" "a" "b", .rel "r" "a" "c",
    .diff "b" "c" ]

theorem nearClashAbox_consistent :
    OWL.Consistent OWL.RoleAxioms.empty nearClashAbox := by
  refine ⟨Unit, trivialDlInterp, fun _ => (), OWL.respects_empty _, ?_⟩
  intro φ hφ
  simp only [nearClashAbox, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · show ¬ ∃ l : List Unit, trivialDlInterp.succWitness "r" () 2 l
    rintro ⟨l, hlen, hpw, -⟩
    exact unit_no_pairwise_two l hlen hpw
  · exact trivial
  · exact trivial

/-- **Non-vacuity, satisfiable side**: the translation of a consistent
ABox has a model. -/
theorem nearClash_unified_sat :
    ∃ i : CL.Interp,
      CL.SatisfiesAll i (owlDlDirect OWL.RoleAxioms.empty nearClashAbox) :=
  consistent_unified_sat nearClashAbox_consistent

theorem clashAbox_refuted : OWL.Refuted OWL.RoleAxioms.empty clashAbox := by
  refine OWL.Refuted.maxClash (a := "a") (n := 1) (r := "r") ["b", "c"]
    (OWL.Derives.hyp (by decide)) rfl ?_ ?_
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨by simp, ?_⟩⟩
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      exact Or.inl (OWL.Derives.hyp (by decide))
    · exact List.Pairwise.nil
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact OWL.Derives.hyp (by decide)
    · exact OWL.Derives.hyp (by decide)

/-- **Non-vacuity, refutation side**: `Refuted` holds of something, so
`refuted_unified_unsat` is not vacuously true — and the ABox it holds
of differs from `nearClashAbox` by the `diff` assertion alone, so the
equality machinery is what carries the verdict. -/
theorem clash_unified_unsat :
    ¬ ∃ i : CL.Interp,
      CL.SatisfiesAll i (owlDlDirect OWL.RoleAxioms.empty clashAbox) :=
  refuted_unified_unsat clashAbox_refuted

/-- The separating pair, stated as one theorem: adding `diff` flips
unified satisfiability. -/
theorem diff_flips_satisfiability :
    (∃ i : CL.Interp,
        CL.SatisfiesAll i (owlDlDirect OWL.RoleAxioms.empty nearClashAbox)) ∧
      ¬ ∃ i : CL.Interp,
        CL.SatisfiesAll i (owlDlDirect OWL.RoleAxioms.empty clashAbox) :=
  ⟨nearClash_unified_sat, clash_unified_unsat⟩

/-! ## Non-vacuity: the translation asserts and withholds content -/

/-- A satisfiable ABox's translation does NOT entail everything — it is
not a theory that has collapsed. -/
theorem nearClash_not_entails_false :
    ¬ Unified.Entails (owlDlDirect OWL.RoleAxioms.empty nearClashAbox)
        (.disj []) := by
  intro h
  obtain ⟨i, hi⟩ := nearClash_unified_sat
  have hf := h i trivial hi
  rw [CL.Satisfies, sat_disj'] at hf
  simp [CL.SatAny] at hf

/-- The translation carries real content: a conjunction assertion
entails its component assertion, over the unified theory. -/
theorem conj_entails_component :
    Unified.Entails
      (owlDlDirect OWL.RoleAxioms.empty
        [OWL.Assertion.inst "a" (.conj (.atom "C") (.atom "D"))])
      (assertionSentence (.inst "a" (.atom "C"))) := by
  intro i _ hsat
  obtain ⟨-, hA⟩ := satisfiesAll_owlDlDirect_restrict i _ _ hsat
  have hc := hA (OWL.Assertion.inst "a" (.conj (.atom "C") (.atom "D"))) (by simp)
  simp only [OWL.Satisfies, OWL.Interp.sem] at hc
  exact (satisfies_assertionSentence (dlCompat_restrict i)
    (.inst "a" (.atom "C"))).mpr hc.1

/-- The empty configuration is satisfiable and unrefuted — the calculus
does not refute everything. -/
theorem empty_unified_sat :
    ∃ i : CL.Interp,
      CL.SatisfiesAll i (owlDlDirect OWL.RoleAxioms.empty []) :=
  consistent_unified_sat
    ⟨Unit, trivialDlInterp, fun _ => (), OWL.respects_empty _,
      fun _ h => absurd h (by simp)⟩

theorem empty_not_refuted : ¬ OWL.Refuted OWL.RoleAxioms.empty [] :=
  unified_sat_not_refuted empty_unified_sat

/-! ## Non-vacuity: the role box does work -/

/-- A subrole axiom is not inert: it turns an `r`-edge into an
`s`-edge, and the translation carries that. -/
theorem subRole_entails_super :
    Unified.Entails
      (owlDlDirect ⟨[("r", "s")], []⟩ [OWL.Assertion.rel "r" "a" "b"])
      (assertionSentence (.rel "s" "a" "b")) := by
  intro i _ hsat
  obtain ⟨hR, hA⟩ := satisfiesAll_owlDlDirect_restrict i _ _ hsat
  have hedge := hA (OWL.Assertion.rel "r" "a" "b") (by simp)
  exact (satisfies_assertionSentence (dlCompat_restrict i)
    (.rel "s" "a" "b")).mpr
    (hR.1 ("r", "s") (by simp) (dlNu i "a") (dlNu i "b") hedge)

/-! ## Axiom audit -/

#print axioms unified_adequate_dl
#print axioms refuted_unified_unsat
#print axioms refuted_unified_entails_all
#print axioms unified_sat_not_refuted
#print axioms consistent_unified_sat
#print axioms diff_flips_satisfiability
#print axioms nearClash_not_entails_false
#print axioms conj_entails_component
#print axioms subRole_entails_super
#print axioms empty_not_refuted
#print axioms satisfiesAll_owlDlDirect_iff
#print axioms sat_conceptFormula
#print axioms sem_inl

end L4Factoidal.Unified
