/-
L4Factoidal.CL.IklModels — a coherent IKL interpretation, built.

`CL.Semantics.IklRespectsThat` is a CONDITION on interpretations: the
zero-ary relation extension of the proposition a sentence expresses
agrees with satisfaction of that sentence, at every valuation. Nothing
in `CL.Semantics` shows the condition can be met, and every theorem
quantified over coherent interpretations is empty until something
does. Pat Hayes, "A Satisfiability-Preserving Reduction of IKL to
Common Logic" (IHMC 2009), says the normalization result "solves what
was previously an open question regarding the existence of IKL
interpretations".
Tracking: https://github.com/danbri/factoidal/issues/580

## The construction

The circularity to break is that satisfaction of `(that S)` consults
`iProp`, which is a field of the interpretation being defined. `pSat`
below is satisfaction with that field resolved by recursion instead:
it mirrors `CL.Semantics.Sat` clause for clause, and reads a
`that`-term by recursing into its body, which is a strictly smaller
sentence. `iklProp` then takes `pSat` as its `iProp` field, and
`sat_iklProp` proves the two agree, which makes `IklRespectsThat` hold
by unfolding.

The universe is `Prop` itself, with `rel x args := x` and
`fn x args := x`. Both are legitimate ISO/IEC 24707 §6.2 assignments:
`rel x` is the whole of `UD*` or none of it, and `fun x` is a constant
function. The consequence, which bounds what this model can witness,
is that an individual's relation extension does not depend on the
argument sequence, so `iklProp` cannot give a fresh name a non-trivial
FUNCTIONAL extension. That is exactly what the intrusion case of IKL
normalization needs, and is why `CL.NormalizeSemantics` proves its
theorems for the fragment where no quantifier intrudes into a
proposition name.
-/

import L4Factoidal.CL.Normalize
import L4Factoidal.CL.Semantics
import L4Factoidal.CL.FiniteSatTheorems

namespace L4Factoidal.CL

-- The `decreasing_by` blocks below share one simp set across seven
-- functions; not every function uses every size lemma.
set_option linter.unusedSimpArgs false

/-! ## Satisfaction with `that` resolved by recursion -/

mutual

/-- Denotation of a term in the `Prop` universe. `funapp` reads
`fn x args := x`; `that` recurses into the body. -/
def pDenot (nu : String → Prop) (sg : String → List Prop) : Term → Prop
  | .name n => nu n
  | .str _ => False
  | .funapp op _ => pDenot nu sg op
  | .that s => pSat nu sg s
termination_by t => t.size
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

/-- Denotation of an argument sequence. -/
def pDenotSeq (nu : String → Prop) (sg : String → List Prop) :
    List SeqItem → List Prop
  | [] => []
  | .term t :: r => pDenot nu sg t :: pDenotSeq nu sg r
  | .seqmark m :: r => sg m ++ pDenotSeq nu sg r
termination_by args => seqItemsSize args
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

/-- Satisfaction, mirroring `CL.Semantics.Sat` with `rel x args := x`. -/
def pSat (nu : String → Prop) (sg : String → List Prop) : Sentence → Prop
  | .atom p _ => pDenot nu sg p
  | .eq a b => pDenot nu sg a = pDenot nu sg b
  | .conj ss => pSatAll nu sg ss
  | .disj ss => pSatAny nu sg ss
  | .neg s => ¬ pSat nu sg s
  | .impl a b => pSat nu sg a → pSat nu sg b
  | .iff a b => pSat nu sg a ↔ pSat nu sg b
  | .all bs body => pSatFA nu sg bs body
  | .ex bs body => pSatEX nu sg bs body
termination_by s => s.size
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

/-- Every sentence of the list. -/
def pSatAll (nu : String → Prop) (sg : String → List Prop) :
    List Sentence → Prop
  | [] => True
  | s :: r => pSat nu sg s ∧ pSatAll nu sg r
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

/-- Some sentence of the list. -/
def pSatAny (nu : String → Prop) (sg : String → List Prop) :
    List Sentence → Prop
  | [] => False
  | s :: r => pSat nu sg s ∨ pSatAny nu sg r
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

/-- Universal quantification down a boundlist. -/
def pSatFA (nu : String → Prop) (sg : String → List Prop) :
    List Binding → Sentence → Prop
  | [], body => pSat nu sg body
  | .plain n :: r, body => ∀ x : Prop, pSatFA (updateInd nu n x) sg r body
  | .seqmark m :: r, body =>
      ∀ xs : List Prop, pSatFA nu (updateSeq sg m xs) r body
  | .restricted n g :: r, body =>
      ∀ x : Prop, pDenot nu sg g → pSatFA (updateInd nu n x) sg r body
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

/-- Existential quantification down a boundlist. -/
def pSatEX (nu : String → Prop) (sg : String → List Prop) :
    List Binding → Sentence → Prop
  | [], body => pSat nu sg body
  | .plain n :: r, body => ∃ x : Prop, pSatEX (updateInd nu n x) sg r body
  | .seqmark m :: r, body =>
      ∃ xs : List Prop, pSatEX nu (updateSeq sg m xs) r body
  | .restricted n g :: r, body =>
      ∃ x : Prop, pDenot nu sg g ∧ pSatEX (updateInd nu n x) sg r body
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Term.size, seqItemsSize, Sentence.size, sentencesSize,
                  bindingsSize]
  all_goals omega

end

/-! ## The interpretation -/

/-- A coherent IKL interpretation. The universe is `Prop`; an
individual's relation extension is all of `UD*` when the individual is
a true proposition and empty otherwise; the functional extension of
every individual is the constant function on that individual. -/
@[reducible] def iklProp : Interp where
  dom := Prop
  domWit := True
  iName := fun _ => False
  iStr := fun _ => False
  rel := fun x _ => x
  fn := fun x _ => x
  iProp := fun s nu sg => pSat nu sg s

/-- Term denotation in `iklProp` is `pDenot`. Structural on the term:
the `that` case is `iProp`, which IS `pSat`, so it needs no appeal to
the satisfaction agreement below. -/
theorem denot_iklProp (nu : String → Prop) (sg : String → List Prop) :
    ∀ t : Term, denotTerm iklProp nu sg t = pDenot nu sg t
  | .name _ => by rw [denotTerm, pDenot]
  | .str _ => by rw [denotTerm, pDenot]
  | .funapp op args => by
      simp only [denotTerm, pDenot, iklProp]
      exact denot_iklProp nu sg op
  | .that _ => by rw [denotTerm, pDenot]

/-! ## Satisfaction agreement -/

mutual

/-- Satisfaction in `iklProp` is `pSat`. -/
theorem sat_iklProp (nu : String → Prop) (sg : String → List Prop) :
    ∀ s : Sentence, Sat iklProp nu sg s ↔ pSat nu sg s
  | .atom p args => by
      rw [sat_atom_iff, pSat]
      show (denotTerm iklProp nu sg p) ↔ pDenot nu sg p
      exact Iff.of_eq (denot_iklProp nu sg p)
  | .eq a b => by
      rw [sat_eq_iff, pSat, denot_iklProp, denot_iklProp]
  | .conj ss => by rw [sat_conj_iff, pSat]; exact satAll_iklProp nu sg ss
  | .disj ss => by rw [sat_disj_iff, pSat]; exact satAny_iklProp nu sg ss
  | .neg s => by rw [sat_neg_iff, pSat]; exact not_congr (sat_iklProp nu sg s)
  | .impl a b => by
      rw [sat_impl_iff, pSat]
      exact imp_congr (sat_iklProp nu sg a) (sat_iklProp nu sg b)
  | .iff a b => by
      rw [sat_iff_iff, pSat]
      exact iff_congr (sat_iklProp nu sg a) (sat_iklProp nu sg b)
  | .all bs body => by rw [sat_all_iff, pSat]; exact satFA_iklProp nu sg bs body
  | .ex bs body => by rw [sat_ex_iff, pSat]; exact satEX_iklProp nu sg bs body
termination_by s => s.size
decreasing_by
  all_goals simp [Sentence.size, sentencesSize, bindingsSize]
  all_goals omega

/-- List agreement for `and`. -/
theorem satAll_iklProp (nu : String → Prop) (sg : String → List Prop) :
    ∀ ss : List Sentence, SatAll iklProp nu sg ss ↔ pSatAll nu sg ss
  | [] => by rw [satAll_nil_iff, pSatAll]
  | s :: r => by
      rw [satAll_cons_iff, pSatAll]
      exact and_congr (sat_iklProp nu sg s) (satAll_iklProp nu sg r)
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

/-- List agreement for `or`. -/
theorem satAny_iklProp (nu : String → Prop) (sg : String → List Prop) :
    ∀ ss : List Sentence, SatAny iklProp nu sg ss ↔ pSatAny nu sg ss
  | [] => by rw [satAny_nil_iff, pSatAny]
  | s :: r => by
      rw [satAny_cons_iff, pSatAny]
      exact or_congr (sat_iklProp nu sg s) (satAny_iklProp nu sg r)
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

/-- Boundlist agreement, universal. -/
theorem satFA_iklProp (nu : String → Prop) (sg : String → List Prop) :
    ∀ (bs : List Binding) (body : Sentence),
      SatForall iklProp nu sg bs body ↔ pSatFA nu sg bs body
  | [], body => by rw [satForall_nil_iff, pSatFA]; exact sat_iklProp nu sg body
  | .plain n :: r, body => by
      rw [satForall_plain_iff, pSatFA]
      exact forall_congr' (fun x => satFA_iklProp (updateInd nu n x) sg r body)
  | .seqmark m :: r, body => by
      rw [satForall_seqmark_iff, pSatFA]
      exact forall_congr' (fun xs => satFA_iklProp nu (updateSeq sg m xs) r body)
  | .restricted n g :: r, body => by
      rw [satForall_restricted_iff, pSatFA]
      refine forall_congr' (fun x => imp_congr ?_ ?_)
      · show (denotTerm iklProp nu sg g) ↔ pDenot nu sg g
        exact Iff.of_eq (denot_iklProp nu sg g)
      · exact satFA_iklProp (updateInd nu n x) sg r body
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Sentence.size, bindingsSize]
  all_goals omega

/-- Boundlist agreement, existential. -/
theorem satEX_iklProp (nu : String → Prop) (sg : String → List Prop) :
    ∀ (bs : List Binding) (body : Sentence),
      SatExists iklProp nu sg bs body ↔ pSatEX nu sg bs body
  | [], body => by rw [satExists_nil_iff, pSatEX]; exact sat_iklProp nu sg body
  | .plain n :: r, body => by
      rw [satExists_plain_iff, pSatEX]
      exact exists_congr (fun x => satEX_iklProp (updateInd nu n x) sg r body)
  | .seqmark m :: r, body => by
      rw [satExists_seqmark_iff, pSatEX]
      exact exists_congr (fun xs => satEX_iklProp nu (updateSeq sg m xs) r body)
  | .restricted n g :: r, body => by
      rw [satExists_restricted_iff, pSatEX]
      refine exists_congr (fun x => and_congr ?_ ?_)
      · show (denotTerm iklProp nu sg g) ↔ pDenot nu sg g
        exact Iff.of_eq (denot_iklProp nu sg g)
      · exact satEX_iklProp (updateInd nu n x) sg r body
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Sentence.size, bindingsSize]
  all_goals omega

end

/-- **A coherent IKL interpretation exists.** `IklRespectsThat` is not
an empty condition, so every theorem quantified over the coherent
interpretations has a model to speak about. -/
theorem iklProp_respects : IklRespectsThat iklProp := by
  intro s nu sg
  show pSat nu sg s ↔ Sat iklProp nu sg s
  exact (sat_iklProp nu sg s).symm

/-! ## Free-name coincidence

The proposition a `that`-term denotes must depend only on what the
names free in its body denote. Hayes's construction turns on it: the
fresh name introduced for `(that S)` is given ONE denotation, and the
occurrence of `(that S)` it replaces sits under quantifiers that
change the valuation at names S does not use. `IklPropLocal` states
the condition on an arbitrary interpretation; `pSat_coincide` proves
it for `iklProp`. -/

/-- Two valuations agree at every name of a list. -/
def AgreeOn {a : Type} (f g : String → a) (l : List String) : Prop :=
  ∀ n ∈ l, f n = g n

/-- Agreement transfers to any sublist. -/
theorem AgreeOn.mono {a : Type} {f g : String → a} {l l' : List String}
    (h : AgreeOn f g l) (hsub : ∀ n, n ∈ l' → n ∈ l) : AgreeOn f g l' :=
  fun n hn => h n (hsub n hn)

/-- Membership in `removeName`. -/
theorem mem_removeName {m n : String} {l : List String} :
    m ∈ removeName n l ↔ m ∈ l ∧ m ≠ n := by
  simp [removeName, List.mem_filter]

/-- Membership in `removeNames`. -/
theorem mem_removeNames {m : String} {ns : List String} :
    ∀ {l : List String}, m ∈ removeNames ns l ↔ m ∈ l ∧ m ∉ ns := by
  induction ns with
  | nil => intro l; simp [removeNames]
  | cons n r ih =>
      intro l
      rw [removeNames, ih, mem_removeName]
      constructor
      · rintro ⟨⟨hl, hn⟩, hr⟩
        exact ⟨hl, by simp [hn, hr]⟩
      · rintro ⟨hl, hnr⟩
        simp at hnr
        exact ⟨⟨hl, hnr.1⟩, hnr.2⟩

/-- A point-wise update preserves agreement: what the update writes is
the same on both sides, and the rest is covered by agreement off the
updated name. -/
theorem agree_updateInd {a : Type} {f g : String → a} {l : List String}
    {n : String} {x : a} (h : AgreeOn f g (removeName n l)) :
    AgreeOn (updateInd f n x) (updateInd g n x) l := by
  intro m hm
  by_cases hmn : m = n
  · subst hmn; simp [updateInd]
  · simp only [updateInd, if_neg hmn]
    exact h m (mem_removeName.mpr ⟨hm, hmn⟩)

/-- The sequence-marker counterpart. -/
theorem agree_updateSeq {a : Type} {f g : String → List a} {l : List String}
    {n : String} {x : List a} (h : AgreeOn f g (removeName n l)) :
    AgreeOn (updateSeq f n x) (updateSeq g n x) l := by
  intro m hm
  by_cases hmn : m = n
  · subst hmn; simp [updateSeq]
  · simp only [updateSeq, if_neg hmn]
    exact h m (mem_removeName.mpr ⟨hm, hmn⟩)

mutual

/-- Term denotation depends only on the free names and free markers. -/
theorem pDenot_coincide (nu nu' : String → Prop) (sg sg' : String → List Prop) :
    ∀ t : Term, AgreeOn nu nu' (freeNamesT t) → AgreeOn sg sg' (freeMarksT t) →
      pDenot nu sg t = pDenot nu' sg' t
  | .name n, hn, _ => by
      rw [pDenot, pDenot]; exact hn n (by simp [freeNamesT])
  | .str _, _, _ => by rw [pDenot, pDenot]
  | .funapp op args, hn, hm => by
      rw [pDenot, pDenot]
      exact pDenot_coincide nu nu' sg sg' op
        (hn.mono (fun n h => by simp [freeNamesT]; exact Or.inl h))
        (hm.mono (fun m h => by simp [freeMarksT]; exact Or.inl h))
  | .that s, hn, hm => by
      rw [pDenot, pDenot]
      exact propext (pSat_coincide nu nu' sg sg' s
        (hn.mono (fun n h => by rw [freeNamesT]; exact h))
        (hm.mono (fun m h => by rw [freeMarksT]; exact h)))
termination_by t => t.size
decreasing_by
  all_goals simp [Term.size]
  all_goals omega

/-- Satisfaction depends only on the free names and free markers. -/
theorem pSat_coincide (nu nu' : String → Prop) (sg sg' : String → List Prop) :
    ∀ s : Sentence, AgreeOn nu nu' (freeNamesS s) → AgreeOn sg sg' (freeMarksS s) →
      (pSat nu sg s ↔ pSat nu' sg' s)
  | .atom p args, hn, hm => by
      rw [pSat, pSat]
      exact Iff.of_eq (pDenot_coincide nu nu' sg sg' p
        (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inl h))
        (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inl h)))
  | .eq a b, hn, hm => by
      rw [pSat, pSat,
          pDenot_coincide nu nu' sg sg' a
            (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inl h))
            (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inl h)),
          pDenot_coincide nu nu' sg sg' b
            (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inr h))
            (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inr h))]
  | .conj ss, hn, hm => by
      rw [pSat, pSat]
      exact pSatAll_coincide nu nu' sg sg' ss
        (hn.mono (fun n h => by rw [freeNamesS]; exact h))
        (hm.mono (fun m h => by rw [freeMarksS]; exact h))
  | .disj ss, hn, hm => by
      rw [pSat, pSat]
      exact pSatAny_coincide nu nu' sg sg' ss
        (hn.mono (fun n h => by rw [freeNamesS]; exact h))
        (hm.mono (fun m h => by rw [freeMarksS]; exact h))
  | .neg s, hn, hm => by
      rw [pSat, pSat]
      exact not_congr (pSat_coincide nu nu' sg sg' s
        (hn.mono (fun n h => by rw [freeNamesS]; exact h))
        (hm.mono (fun m h => by rw [freeMarksS]; exact h)))
  | .impl a b, hn, hm => by
      rw [pSat, pSat]
      exact imp_congr
        (pSat_coincide nu nu' sg sg' a
          (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inl h))
          (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inl h)))
        (pSat_coincide nu nu' sg sg' b
          (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inr h))
          (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inr h)))
  | .iff a b, hn, hm => by
      rw [pSat, pSat]
      exact iff_congr
        (pSat_coincide nu nu' sg sg' a
          (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inl h))
          (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inl h)))
        (pSat_coincide nu nu' sg sg' b
          (hn.mono (fun n h => by simp [freeNamesS]; exact Or.inr h))
          (hm.mono (fun m h => by simp [freeMarksS]; exact Or.inr h)))
  | .all bs body, hn, hm => by
      rw [pSat, pSat]
      exact pSatFA_coincide nu nu' sg sg' bs body
        (hn.mono (fun n h => by rw [freeNamesS]; exact h))
        (hm.mono (fun m h => by rw [freeMarksS]; exact h))
  | .ex bs body, hn, hm => by
      rw [pSat, pSat]
      exact pSatEX_coincide nu nu' sg sg' bs body
        (hn.mono (fun n h => by rw [freeNamesS]; exact h))
        (hm.mono (fun m h => by rw [freeMarksS]; exact h))
termination_by s => s.size
decreasing_by
  all_goals simp [Sentence.size]
  all_goals omega

/-- Coincidence for an `and` list. -/
theorem pSatAll_coincide (nu nu' : String → Prop) (sg sg' : String → List Prop) :
    ∀ ss : List Sentence, AgreeOn nu nu' (freeNamesSs ss) →
      AgreeOn sg sg' (freeMarksSs ss) → (pSatAll nu sg ss ↔ pSatAll nu' sg' ss)
  | [], _, _ => by rw [pSatAll, pSatAll]
  | s :: r, hn, hm => by
      rw [pSatAll, pSatAll]
      exact and_congr
        (pSat_coincide nu nu' sg sg' s
          (hn.mono (fun n h => by simp [freeNamesSs]; exact Or.inl h))
          (hm.mono (fun m h => by simp [freeMarksSs]; exact Or.inl h)))
        (pSatAll_coincide nu nu' sg sg' r
          (hn.mono (fun n h => by simp [freeNamesSs]; exact Or.inr h))
          (hm.mono (fun m h => by simp [freeMarksSs]; exact Or.inr h)))
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

/-- Coincidence for an `or` list. -/
theorem pSatAny_coincide (nu nu' : String → Prop) (sg sg' : String → List Prop) :
    ∀ ss : List Sentence, AgreeOn nu nu' (freeNamesSs ss) →
      AgreeOn sg sg' (freeMarksSs ss) → (pSatAny nu sg ss ↔ pSatAny nu' sg' ss)
  | [], _, _ => by rw [pSatAny, pSatAny]
  | s :: r, hn, hm => by
      rw [pSatAny, pSatAny]
      exact or_congr
        (pSat_coincide nu nu' sg sg' s
          (hn.mono (fun n h => by simp [freeNamesSs]; exact Or.inl h))
          (hm.mono (fun m h => by simp [freeMarksSs]; exact Or.inl h)))
        (pSatAny_coincide nu nu' sg sg' r
          (hn.mono (fun n h => by simp [freeNamesSs]; exact Or.inr h))
          (hm.mono (fun m h => by simp [freeMarksSs]; exact Or.inr h)))
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

/-- Coincidence down a universal boundlist. -/
theorem pSatFA_coincide (nu nu' : String → Prop) (sg sg' : String → List Prop) :
    ∀ (bs : List Binding) (body : Sentence),
      AgreeOn nu nu'
        (freeNamesGuards bs ++ removeNames (bindNames bs) (freeNamesS body)) →
      AgreeOn sg sg'
        (freeMarksGuards bs ++ removeNames (bindMarks bs) (freeMarksS body)) →
      (pSatFA nu sg bs body ↔ pSatFA nu' sg' bs body)
  | [], body, hn, hm => by
      rw [pSatFA, pSatFA]
      exact pSat_coincide nu nu' sg sg' body
        (hn.mono (fun n h => by
          simp [freeNamesGuards, bindNames, removeNames]; exact h))
        (hm.mono (fun m h => by
          simp [freeMarksGuards, bindMarks, removeNames]; exact h))
  | .plain n :: r, body, hn, hm => by
      rw [pSatFA, pSatFA]
      refine forall_congr' (fun x => pSatFA_coincide _ _ sg sg' r body ?_ ?_)
      · refine agree_updateInd (hn.mono ?_)
        intro m hmem
        rw [mem_removeName] at hmem
        obtain ⟨hmem, hne⟩ := hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (mem_removeName.mpr ⟨h, hne⟩)
        · rw [mem_removeNames] at h
          refine Or.inr (mem_removeNames.mpr ⟨h.1, ?_⟩)
          simp [bindNames]
          exact ⟨hne, h.2⟩
      · refine hm.mono ?_
        intro m hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by simpa [freeMarksGuards] using h)
        · rw [mem_removeNames] at h
          exact Or.inr (mem_removeNames.mpr ⟨h.1, by simpa [bindMarks] using h.2⟩)
  | .seqmark mk :: r, body, hn, hm => by
      rw [pSatFA, pSatFA]
      refine forall_congr' (fun xs => pSatFA_coincide nu nu' _ _ r body ?_ ?_)
      · refine hn.mono ?_
        intro m hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by simpa [freeNamesGuards] using h)
        · rw [mem_removeNames] at h
          exact Or.inr (mem_removeNames.mpr ⟨h.1, by simpa [bindNames] using h.2⟩)
      · refine agree_updateSeq (hm.mono ?_)
        intro m hmem
        rw [mem_removeName] at hmem
        obtain ⟨hmem, hne⟩ := hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (mem_removeName.mpr ⟨h, hne⟩)
        · rw [mem_removeNames] at h
          refine Or.inr (mem_removeNames.mpr ⟨h.1, ?_⟩)
          simp [bindMarks]
          exact ⟨hne, h.2⟩
  | .restricted n g :: r, body, hn, hm => by
      rw [pSatFA, pSatFA]
      have hg : pDenot nu sg g = pDenot nu' sg' g := by
        refine pDenot_coincide nu nu' sg sg' g (hn.mono ?_) (hm.mono ?_)
        · intro m hmem
          simp only [List.mem_append, freeNamesGuards]
          exact Or.inl (Or.inl hmem)
        · intro m hmem
          simp only [List.mem_append, freeMarksGuards]
          exact Or.inl (Or.inl hmem)
      rw [hg]
      refine forall_congr' (fun x => imp_congr Iff.rfl
        (pSatFA_coincide _ _ sg sg' r body ?_ ?_))
      · refine agree_updateInd (hn.mono ?_)
        intro m hmem
        rw [mem_removeName] at hmem
        obtain ⟨hmem, hne⟩ := hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by
            simp only [freeNamesGuards, List.mem_append]
            exact Or.inr (mem_removeName.mpr ⟨h, hne⟩))
        · rw [mem_removeNames] at h
          refine Or.inr (mem_removeNames.mpr ⟨h.1, ?_⟩)
          simp [bindNames]
          exact ⟨hne, h.2⟩
      · refine hm.mono ?_
        intro m hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by
            simp only [freeMarksGuards, List.mem_append]; exact Or.inr h)
        · rw [mem_removeNames] at h
          exact Or.inr (mem_removeNames.mpr ⟨h.1, by simpa [bindMarks] using h.2⟩)
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Sentence.size, bindingsSize, Term.size]
  all_goals omega

/-- Coincidence down an existential boundlist. -/
theorem pSatEX_coincide (nu nu' : String → Prop) (sg sg' : String → List Prop) :
    ∀ (bs : List Binding) (body : Sentence),
      AgreeOn nu nu'
        (freeNamesGuards bs ++ removeNames (bindNames bs) (freeNamesS body)) →
      AgreeOn sg sg'
        (freeMarksGuards bs ++ removeNames (bindMarks bs) (freeMarksS body)) →
      (pSatEX nu sg bs body ↔ pSatEX nu' sg' bs body)
  | [], body, hn, hm => by
      rw [pSatEX, pSatEX]
      exact pSat_coincide nu nu' sg sg' body
        (hn.mono (fun n h => by
          simp [freeNamesGuards, bindNames, removeNames]; exact h))
        (hm.mono (fun m h => by
          simp [freeMarksGuards, bindMarks, removeNames]; exact h))
  | .plain n :: r, body, hn, hm => by
      rw [pSatEX, pSatEX]
      refine exists_congr (fun x => pSatEX_coincide _ _ sg sg' r body ?_ ?_)
      · refine agree_updateInd (hn.mono ?_)
        intro m hmem
        rw [mem_removeName] at hmem
        obtain ⟨hmem, hne⟩ := hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (mem_removeName.mpr ⟨h, hne⟩)
        · rw [mem_removeNames] at h
          refine Or.inr (mem_removeNames.mpr ⟨h.1, ?_⟩)
          simp [bindNames]
          exact ⟨hne, h.2⟩
      · refine hm.mono ?_
        intro m hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by simpa [freeMarksGuards] using h)
        · rw [mem_removeNames] at h
          exact Or.inr (mem_removeNames.mpr ⟨h.1, by simpa [bindMarks] using h.2⟩)
  | .seqmark mk :: r, body, hn, hm => by
      rw [pSatEX, pSatEX]
      refine exists_congr (fun xs => pSatEX_coincide nu nu' _ _ r body ?_ ?_)
      · refine hn.mono ?_
        intro m hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by simpa [freeNamesGuards] using h)
        · rw [mem_removeNames] at h
          exact Or.inr (mem_removeNames.mpr ⟨h.1, by simpa [bindNames] using h.2⟩)
      · refine agree_updateSeq (hm.mono ?_)
        intro m hmem
        rw [mem_removeName] at hmem
        obtain ⟨hmem, hne⟩ := hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (mem_removeName.mpr ⟨h, hne⟩)
        · rw [mem_removeNames] at h
          refine Or.inr (mem_removeNames.mpr ⟨h.1, ?_⟩)
          simp [bindMarks]
          exact ⟨hne, h.2⟩
  | .restricted n g :: r, body, hn, hm => by
      rw [pSatEX, pSatEX]
      have hg : pDenot nu sg g = pDenot nu' sg' g := by
        refine pDenot_coincide nu nu' sg sg' g (hn.mono ?_) (hm.mono ?_)
        · intro m hmem
          simp only [List.mem_append, freeNamesGuards]
          exact Or.inl (Or.inl hmem)
        · intro m hmem
          simp only [List.mem_append, freeMarksGuards]
          exact Or.inl (Or.inl hmem)
      rw [hg]
      refine exists_congr (fun x => and_congr Iff.rfl
        (pSatEX_coincide _ _ sg sg' r body ?_ ?_))
      · refine agree_updateInd (hn.mono ?_)
        intro m hmem
        rw [mem_removeName] at hmem
        obtain ⟨hmem, hne⟩ := hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by
            simp only [freeNamesGuards, List.mem_append]
            exact Or.inr (mem_removeName.mpr ⟨h, hne⟩))
        · rw [mem_removeNames] at h
          refine Or.inr (mem_removeNames.mpr ⟨h.1, ?_⟩)
          simp [bindNames]
          exact ⟨hne, h.2⟩
      · refine hm.mono ?_
        intro m hmem
        simp only [List.mem_append] at hmem ⊢
        rcases hmem with h | h
        · exact Or.inl (by
            simp only [freeMarksGuards, List.mem_append]; exact Or.inr h)
        · rw [mem_removeNames] at h
          exact Or.inr (mem_removeNames.mpr ⟨h.1, by simpa [bindMarks] using h.2⟩)
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Sentence.size, bindingsSize, Term.size]
  all_goals omega

end

/-- The locality condition on an interpretation: the proposition a
sentence expresses depends only on what its free names and free
sequence markers denote. -/
def IklPropLocal (i : Interp) : Prop :=
  ∀ (s : Sentence) (nu nu' : String → i.dom) (sg sg' : String → List i.dom),
    AgreeOn nu nu' (freeNamesS s) → AgreeOn sg sg' (freeMarksS s) →
      i.iProp s nu sg = i.iProp s nu' sg'

/-- `iklProp` is local. -/
theorem iklProp_local : IklPropLocal iklProp := by
  intro s nu nu' sg sg' hn hm
  exact propext (pSat_coincide nu nu' sg sg' s hn hm)

/-! ## Non-vacuity

`iklProp` is exhibited satisfying one sentence and refuting another,
and its relation extension is shown to be neither empty nor the whole
of `UD*`. The condition it meets is not met by every interpretation:
`CL.FiniteSatTheorems.witFin_not_ikl_coherent` exhibits one that fails
`IklRespectsThat`. -/

/-- The relation extension of a true proposition is not empty. -/
theorem iklProp_rel_true : iklProp.rel True [] := trivial

/-- The relation extension is not the whole of `UD*`: a false
proposition has the empty extension. -/
theorem iklProp_rel_false : ¬ iklProp.rel False [] := id

/-- `((that (= a a)))` holds: the assertion of a proposition whose
sentence is satisfied. -/
theorem iklProp_sat_assert :
    Satisfies iklProp (.atom (.that (.eq (.name "a") (.name "a"))) []) :=
  (satisfies_assert_that iklProp iklProp_respects _).mpr (by
    show Sat iklProp iklProp.iName (fun _ => []) (.eq (.name "a") (.name "a"))
    rw [sat_eq_iff])

/-- `((that (not (= a a))))` fails: the assertion is refuted, so the
model is not the everything-relation on assertions either. -/
theorem iklProp_not_sat_assert :
    ¬ Satisfies iklProp (.atom (.that (.neg (.eq (.name "a") (.name "a")))) []) := by
  rw [satisfies_assert_that iklProp iklProp_respects]
  show ¬ Sat iklProp iklProp.iName (fun _ => []) (.neg (.eq (.name "a") (.name "a")))
  rw [sat_neg_iff]
  intro h
  exact h (by rw [sat_eq_iff])

/-- **There is at least one coherent, local IKL interpretation.** -/
theorem exists_ikl_interp :
    ∃ i : Interp, IklRespectsThat i ∧ IklPropLocal i :=
  ⟨iklProp, iklProp_respects, iklProp_local⟩

#print axioms iklProp_respects
#print axioms iklProp_local
#print axioms exists_ikl_interp
#print axioms iklProp_sat_assert
#print axioms iklProp_not_sat_assert

end L4Factoidal.CL
