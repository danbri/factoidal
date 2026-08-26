/-
L4Factoidal.CL.NormalizeSemantics — what IKL normalization preserves.

Pat Hayes, "A Satisfiability-Preserving Reduction of IKL to Common
Logic" (IHMC 2009): the normalization mapping takes an IKL sentence to
a Common Logic text of one head sentence plus a set of tail sentences,
and "any IKL interpretation I of PHI defines a CL interpretation J of
S(PHI) which satisfies the tail ... such that in every case, J assigns
the same truthvalue to the head as I does to PHI".
Tracking: https://github.com/danbri/factoidal/issues/580

## What is proved here

For the fragment where no quantifier intrudes into a proposition name
(`CL.Normalize.noIntrusion`, which holds of all four of the paper's
paradoxes), and for a valuation that gives each allocated fresh name
the proposition its `that`-body denotes:

* `normS_head` — the head sentence has the same truth value under the
  new valuation as the original sentence has under the old one.
* `normS_tails` — every tail sentence holds under the new valuation.
* `normalize_preserves` — the two together at the top level, and
  `ikl_sat_to_cl_sat`, the satisfiability half of Hayes's claim.
* `tails_satisfiable` — Hayes's open conjecture, for this fragment:
  the tail set of a normalized IKL sentence is always CL-satisfiable.
  Note that `normS_tails` does NOT use the premise that the original
  sentence is satisfied, so a model of the tails can be built from ANY
  coherent IKL interpretation; `CL.IklModels.iklProp` is one.

## What is NOT proved

* The intrusion case. When the intrusion list is non-empty the
  replacement term is `(K U1 ... Un)`, and the model must give the
  individual `K` denotes a non-trivial FUNCTIONAL extension sending
  each argument tuple to a different proposition. Constructing that
  needs a universe carrying such functions; `iklProp`'s `Prop`
  universe collapses them. Recorded in the design note.
* The converse direction: from a CL model of head-plus-tails back to
  an IKL model of the original sentence. Coherence forces a model to
  contain an individual with empty zero-ary extension and one with
  non-empty (otherwise a sentence and its negation would both hold),
  and a CL model of head-plus-tails need not contain either; and
  because a `that`-term can occur in an equation (the Liar does), the
  converse construction has to make `iProp` return the very
  individual the fresh name denotes, not merely one with the same
  truth value.
* Injectivity of `propName`. The existence of a valuation meeting
  `KnowsA` is proved from a hypothesis that the fresh-name supply is
  injective. `propName k = "prop" ++ toString k` is injective, but the
  proof needs injectivity of `Nat.repr`, which this Lean toolchain's
  core library does not carry. The paradox instances do not use the
  hypothesis: their assignment lists are concrete.
-/

import L4Factoidal.CL.IklModels

namespace L4Factoidal.CL

-- The `decreasing_by` blocks below share one simp set across the
-- members of each mutual group; not every member uses every lemma.
set_option linter.unusedSimpArgs false

/-! ## The conditions the theorems carry -/

/-- Every name of the list is outside the fresh-name space. -/
def NoFresh (l : List String) : Prop := ∀ n ∈ l, isFreshName n = false

/-- The valuation gives each allocated name the proposition its
`that`-body denotes at the top-level valuation. -/
def KnowsA (i : Interp) (A : List (String × Sentence))
    (kap : String → i.dom) : Prop :=
  ∀ k b, (k, b) ∈ A → kap k = i.iProp b i.iName (fun _ => [])

/-- Every key of the assignment is in the fresh-name space. -/
def FreshKeys (A : List (String × Sentence)) : Prop :=
  ∀ k b, (k, b) ∈ A → isFreshName k = true

/-- Two valuations agree everywhere outside the fresh-name space. -/
def OffFresh (i : Interp) (kap nu : String → i.dom) : Prop :=
  ∀ m, isFreshName m = false → kap m = nu m

/-! ## Unfolding lemmas for a `that` node with no intrusion -/

/-- With no intrusion the replacement term is the bare fresh name. -/
theorem normTerm_that_noIntr (bnd bm : List String) (c : Nat) (s : Sentence)
    (h : noIntrT bnd bm (.that s) = true) :
    (normTerm bnd bm c (.that s)).1 = Term.name (propName c) := by
  rw [noIntrT] at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨hu, hum⟩, _⟩ := h
  rw [normTerm]
  simp only [hu, hum, kTerm, List.isEmpty_nil, Bool.and_self, if_pos]

/-- With no intrusion the emitted tails are the K-defining
biconditional followed by the body's own tails. -/
theorem normTerm_that_tails (bnd bm : List String) (c : Nat) (s : Sentence)
    (h : noIntrT bnd bm (.that s) = true) :
    (normTerm bnd bm c (.that s)).2.1 =
      Sentence.iff (.atom (.name (propName c)) []) (normSent [] [] (c + 1) s).1
        :: (normSent [] [] (c + 1) s).2.1 := by
  rw [noIntrT] at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨hu, hum⟩, _⟩ := h
  rw [normTerm]
  simp only [hu, hum, kTail, kTerm, List.isEmpty_nil, Bool.and_self, if_pos]

/-- With no intrusion the allocations of a `that` node are its own
name and the body's. -/
theorem assignT_that_noIntr (bnd bm : List String) (c : Nat) (s : Sentence)
    (h : noIntrT bnd bm (.that s) = true) :
    assignT bnd bm c (.that s) = (propName c, s) :: assignS [] [] (c + 1) s := by
  rw [noIntrT] at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨hu, hum⟩, _⟩ := h
  rw [assignT]
  simp only [hu, hum]

/-- No name free in the body is bound outside it. -/
theorem noIntr_free_not_bound (bnd bm : List String) (s : Sentence)
    (h : noIntrT bnd bm (.that s) = true) :
    (∀ n ∈ freeNamesS s, n ∉ bnd) ∧ (∀ m ∈ freeMarksS s, m ∉ bm) := by
  rw [noIntrT] at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨hu, hum⟩, _⟩ := h
  constructor
  · intro n hn hb
    have : n ∈ bnd.filter (fun n => (freeNamesS s).contains n) := by
      simp [List.mem_filter, hb, hn]
    rw [hu] at this
    exact absurd this (List.not_mem_nil)
  · intro m hm hb
    have : m ∈ bm.filter (fun m => (freeMarksS s).contains m) := by
      simp [List.mem_filter, hb, hm]
    rw [hum] at this
    exact absurd this (List.not_mem_nil)

/-- The body of a `that` node carries no intrusion of its own. -/
theorem noIntr_body (bnd bm : List String) (s : Sentence)
    (h : noIntrT bnd bm (.that s) = true) : noIntrS [] [] s = true := by
  rw [noIntrT] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-! ## The head clause

The head sentence, read under the new valuation, has the truth value
the original sentence has under the old one. Only the locality
condition is used: `IklRespectsThat` is what the TAIL clause needs. -/

mutual

/-- Head clause for terms. -/
theorem normT_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (t : Term) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesT t) → noIntrT bnd bm t = true →
      (∀ k b, (k, b) ∈ assignT bnd bm c t → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      denotTerm i kap sg (normTerm bnd bm c t).1 = denotTerm i nu sg t
  | .name n => by
      intro bnd bm c kap nu sg hfr _ _ _ hoff _ _
      rw [normTerm, denotTerm, denotTerm]
      exact hoff n (hfr n (by rw [allNamesT]; exact List.mem_singleton_self n))
  | .str _ => by
      intro bnd bm c kap nu sg _ _ _ _ _ _ _
      rw [normTerm, denotTerm, denotTerm]
  | .funapp op args => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normTerm, denotTerm, denotTerm]
      rw [noIntrT] at hni
      simp only [Bool.and_eq_true] at hni
      rw [normT_head i A hLoc hFK op bnd bm c kap nu sg
            (fun n hn => hfr n (by rw [allNamesT]; exact List.mem_append_left _ hn))
            hni.1
            (fun k b hb => hsub k b (by rw [assignT]; exact List.mem_append_left _ hb))
            hkn hoff hnu hsg,
          normSeq_head i A hLoc hFK args bnd bm (normTerm bnd bm c op).2.2 kap nu sg
            (fun n hn => hfr n (by rw [allNamesT]; exact List.mem_append_right _ hn))
            hni.2
            (fun k b hb => hsub k b (by rw [assignT]; exact List.mem_append_right _ hb))
            hkn hoff hnu hsg]
  | .that s => by
      intro bnd bm c kap nu sg _ hni hsub hkn _ hnu hsg
      rw [normTerm_that_noIntr bnd bm c s hni, denotTerm, denotTerm]
      have hmem : (propName c, s) ∈ A :=
        hsub _ _ (by rw [assignT_that_noIntr bnd bm c s hni]; exact List.mem_cons_self)
      rw [hkn _ _ hmem]
      obtain ⟨hfn, hfm⟩ := noIntr_free_not_bound bnd bm s hni
      exact (hLoc s nu i.iName sg (fun _ => [])
        (fun n hn => hnu n (hfn n hn)) (fun m hm => hsg m (hfm m hm))).symm
termination_by t => t.size
decreasing_by
  all_goals simp [Term.size]
  all_goals omega

/-- Head clause for argument sequences. -/
theorem normSeq_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (args : List SeqItem) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesSeq args) → noIntrSeq bnd bm args = true →
      (∀ k b, (k, b) ∈ assignSeq bnd bm c args → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      denotSeq i kap sg (normSeq bnd bm c args).1 = denotSeq i nu sg args
  | [] => by
      intro bnd bm c kap nu sg _ _ _ _ _ _ _
      rw [normSeq, denotSeq, denotSeq]
  | .term t :: r => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSeq, denotSeq, denotSeq]
      rw [noIntrSeq] at hni
      simp only [Bool.and_eq_true] at hni
      rw [normT_head i A hLoc hFK t bnd bm c kap nu sg
            (fun n hn => hfr n (by rw [allNamesSeq]; exact List.mem_append_left _ hn))
            hni.1
            (fun k b hb => hsub k b (by rw [assignSeq]; exact List.mem_append_left _ hb))
            hkn hoff hnu hsg,
          normSeq_head i A hLoc hFK r bnd bm (normTerm bnd bm c t).2.2 kap nu sg
            (fun n hn => hfr n (by rw [allNamesSeq]; exact List.mem_append_right _ hn))
            hni.2
            (fun k b hb => hsub k b (by rw [assignSeq]; exact List.mem_append_right _ hb))
            hkn hoff hnu hsg]
  | .seqmark m :: r => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSeq, denotSeq, denotSeq]
      rw [noIntrSeq] at hni
      rw [normSeq_head i A hLoc hFK r bnd bm c kap nu sg
            (fun n hn => hfr n (by rw [allNamesSeq]; exact hn))
            hni
            (fun k b hb => hsub k b (by rw [assignSeq]; exact hb))
            hkn hoff hnu hsg]
termination_by args => seqItemsSize args
decreasing_by
  all_goals simp [Term.size, seqItemsSize]
  all_goals omega

/-- Head clause for sentences. -/
theorem normS_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (s : Sentence) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesS s) → noIntrS bnd bm s = true →
      (∀ k b, (k, b) ∈ assignS bnd bm c s → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      (Sat i kap sg (normSent bnd bm c s).1 ↔ Sat i nu sg s)
  | .atom p args => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_atom_iff, sat_atom_iff]
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rw [normT_head i A hLoc hFK p bnd bm c kap nu sg
            (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
            hni.1
            (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_left _ hb))
            hkn hoff hnu hsg,
          normSeq_head i A hLoc hFK args bnd bm (normTerm bnd bm c p).2.2 kap nu sg
            (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
            hni.2
            (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_right _ hb))
            hkn hoff hnu hsg]
  | .eq a b => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_eq_iff, sat_eq_iff]
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rw [normT_head i A hLoc hFK a bnd bm c kap nu sg
            (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
            hni.1
            (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_left _ hb))
            hkn hoff hnu hsg,
          normT_head i A hLoc hFK b bnd bm (normTerm bnd bm c a).2.2 kap nu sg
            (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
            hni.2
            (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_right _ hb))
            hkn hoff hnu hsg]
  | .conj ss => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_conj_iff, sat_conj_iff]
      rw [noIntrS] at hni
      exact normSs_head i A hLoc hFK ss bnd bm c kap nu sg
        (fun n hn => hfr n (by rw [allNamesS]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignS]; exact hb)) hkn hoff hnu hsg
  | .disj ss => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_disj_iff, sat_disj_iff]
      rw [noIntrS] at hni
      exact normSsAny_head i A hLoc hFK ss bnd bm c kap nu sg
        (fun n hn => hfr n (by rw [allNamesS]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignS]; exact hb)) hkn hoff hnu hsg
  | .neg s => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_neg_iff, sat_neg_iff]
      rw [noIntrS] at hni
      exact not_congr (normS_head i A hLoc hFK s bnd bm c kap nu sg
        (fun n hn => hfr n (by rw [allNamesS]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignS]; exact hb)) hkn hoff hnu hsg)
  | .impl a b => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_impl_iff, sat_impl_iff]
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      exact imp_congr
        (normS_head i A hLoc hFK a bnd bm c kap nu sg
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff hnu hsg)
        (normS_head i A hLoc hFK b bnd bm (normSent bnd bm c a).2.2 kap nu sg
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff hnu hsg)
  | .iff a b => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_iff_iff, sat_iff_iff]
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      exact iff_congr
        (normS_head i A hLoc hFK a bnd bm c kap nu sg
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff hnu hsg)
        (normS_head i A hLoc hFK b bnd bm (normSent bnd bm c a).2.2 kap nu sg
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff hnu hsg)
  | .all bs body => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_all_iff, sat_all_iff]
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      exact normFA_head i A hLoc hFK bs body bnd bm c kap nu sg
        (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
        (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
        hni.1 hni.2
        (fun k b hb => hsub k b (by rw [assignS]; exact hb))
        hkn hoff hnu hsg
  | .ex bs body => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSent, sat_ex_iff, sat_ex_iff]
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      exact normEX_head i A hLoc hFK bs body bnd bm c kap nu sg
        (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
        (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
        hni.1 hni.2
        (fun k b hb => hsub k b (by rw [assignS]; exact hb))
        hkn hoff hnu hsg
termination_by s => s.size
decreasing_by
  all_goals simp [Term.size, Sentence.size, seqItemsSize, sentencesSize, bindingsSize]
  all_goals omega

/-- Head clause for an `and` list. -/
theorem normSs_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (ss : List Sentence) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesSs ss) → noIntrSs bnd bm ss = true →
      (∀ k b, (k, b) ∈ assignSs bnd bm c ss → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      (SatAll i kap sg (normSents bnd bm c ss).1 ↔ SatAll i nu sg ss)
  | [] => by
      intro bnd bm c kap nu sg _ _ _ _ _ _ _
      rw [normSents, satAll_nil_iff, satAll_nil_iff]
  | s :: r => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSents, satAll_cons_iff, satAll_cons_iff]
      rw [noIntrSs] at hni
      simp only [Bool.and_eq_true] at hni
      exact and_congr
        (normS_head i A hLoc hFK s bnd bm c kap nu sg
          (fun n hn => hfr n (by rw [allNamesSs]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignSs]; exact List.mem_append_left _ hb))
          hkn hoff hnu hsg)
        (normSs_head i A hLoc hFK r bnd bm (normSent bnd bm c s).2.2 kap nu sg
          (fun n hn => hfr n (by rw [allNamesSs]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignSs]; exact List.mem_append_right _ hb))
          hkn hoff hnu hsg)
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

/-- Head clause for an `or` list. -/
theorem normSsAny_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (ss : List Sentence) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesSs ss) → noIntrSs bnd bm ss = true →
      (∀ k b, (k, b) ∈ assignSs bnd bm c ss → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      (SatAny i kap sg (normSents bnd bm c ss).1 ↔ SatAny i nu sg ss)
  | [] => by
      intro bnd bm c kap nu sg _ _ _ _ _ _ _
      rw [normSents, satAny_nil_iff, satAny_nil_iff]
  | s :: r => by
      intro bnd bm c kap nu sg hfr hni hsub hkn hoff hnu hsg
      rw [normSents, satAny_cons_iff, satAny_cons_iff]
      rw [noIntrSs] at hni
      simp only [Bool.and_eq_true] at hni
      exact or_congr
        (normS_head i A hLoc hFK s bnd bm c kap nu sg
          (fun n hn => hfr n (by rw [allNamesSs]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignSs]; exact List.mem_append_left _ hb))
          hkn hoff hnu hsg)
        (normSsAny_head i A hLoc hFK r bnd bm (normSent bnd bm c s).2.2 kap nu sg
          (fun n hn => hfr n (by rw [allNamesSs]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignSs]; exact List.mem_append_right _ hb))
          hkn hoff hnu hsg)
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

/-- Head clause down a universal boundlist. -/
theorem normFA_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (bs : List Binding) (body : Sentence) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesBinds bs) → NoFresh (allNamesS body) →
      noIntrBinds bnd bm bs = true →
      noIntrS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs)) body = true →
      (∀ k b, (k, b) ∈ assignBinds bnd bm c bs
          ++ assignS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
               (normBinds bnd bm c bs).2.2 body → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      (SatForall i kap sg (normBinds bnd bm c bs).1
          (normSent (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
            (normBinds bnd bm c bs).2.2 body).1
        ↔ SatForall i nu sg bs body)
  | [], body => by
      intro bnd bm c kap nu sg _ hfb _ hnib hsub hkn hoff hnu hsg
      rw [normBinds]
      rw [bindNames, bindMarks, addNames, addNames] at *
      rw [satForall_nil_iff, satForall_nil_iff]
      exact normS_head i A hLoc hFK body bnd bm c kap nu sg hfb hnib
        (fun k b hb => hsub k b (by
          rw [assignBinds]; exact List.mem_append_right _ hb)) hkn hoff hnu hsg
  | .plain n :: r, body => by
      intro bnd bm c kap nu sg hfb hfbody hnib hnibody hsub hkn hoff hnu hsg
      have hnf : isFreshName n = false :=
        hfb n (by rw [allNamesBinds]; exact List.mem_cons_self)
      rw [normBinds, bindNames, bindMarks, addNames] at *
      rw [satForall_plain_iff, satForall_plain_iff]
      refine forall_congr' (fun x => ?_)
      rw [noIntrBinds] at hnib
      exact normFA_head i A hLoc hFK r body (addName bnd n) bm c
        (updateInd kap n x) (updateInd nu n x) sg
        (fun m hm => hfb m (by rw [allNamesBinds]; exact List.mem_cons_of_mem _ hm))
        hfbody hnib hnibody
        (fun k b hb => hsub k b (by rw [assignBinds]; exact hb))
        (fun k b hb => by
          have hk : isFreshName k = true := hFK k b hb
          have : k ≠ n := by intro h; rw [h, hnf] at hk; exact Bool.noConfusion hk
          rw [updateInd, if_neg this]; exact hkn k b hb)
        (fun m hm => by
          by_cases hmn : m = n
          · subst hmn; rw [updateInd, updateInd, if_pos rfl, if_pos rfl]
          · rw [updateInd, updateInd, if_neg hmn, if_neg hmn]; exact hoff m hm)
        (fun m hm => by
          have hm1 : m ∉ bnd ∧ m ≠ n := by
            constructor
            · intro h; exact hm (mem_addName.mpr (Or.inl h))
            · intro h; exact hm (mem_addName.mpr (Or.inr h))
          rw [updateInd, if_neg hm1.2]; exact hnu m hm1.1)
        hsg
  | .seqmark mk :: r, body => by
      intro bnd bm c kap nu sg hfb hfbody hnib hnibody hsub hkn hoff hnu hsg
      rw [normBinds, bindNames, bindMarks, addNames] at *
      rw [satForall_seqmark_iff, satForall_seqmark_iff]
      refine forall_congr' (fun xs => ?_)
      rw [noIntrBinds] at hnib
      exact normFA_head i A hLoc hFK r body bnd (addName bm mk) c
        kap nu (updateSeq sg mk xs)
        (fun m hm => hfb m (by rw [allNamesBinds]; exact hm))
        hfbody hnib hnibody
        (fun k b hb => hsub k b (by rw [assignBinds]; exact hb))
        hkn hoff hnu
        (fun m hm => by
          have hm1 : m ∉ bm ∧ m ≠ mk := by
            constructor
            · intro h; exact hm (mem_addName.mpr (Or.inl h))
            · intro h; exact hm (mem_addName.mpr (Or.inr h))
          rw [updateSeq, if_neg hm1.2]; exact hsg m hm1.1)
  | .restricted n g :: r, body => by
      intro bnd bm c kap nu sg hfb hfbody hnib hnibody hsub hkn hoff hnu hsg
      have hnf : isFreshName n = false :=
        hfb n (by rw [allNamesBinds]; exact List.mem_cons_self)
      rw [normBinds, bindNames, bindMarks, addNames] at *
      rw [satForall_restricted_iff, satForall_restricted_iff]
      rw [noIntrBinds] at hnib
      simp only [Bool.and_eq_true] at hnib
      rw [normT_head i A hLoc hFK g bnd bm c kap nu sg
            (fun m hm => hfb m (by
              rw [allNamesBinds]
              exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
            hnib.1
            (fun k b hb => hsub k b (by
              rw [assignBinds]; exact List.mem_append_left _ (List.mem_append_left _ hb)))
            hkn hoff hnu hsg]
      refine forall_congr' (fun x => imp_congr Iff.rfl ?_)
      exact normFA_head i A hLoc hFK r body (addName bnd n) bm
        (normTerm bnd bm c g).2.2 (updateInd kap n x) (updateInd nu n x) sg
        (fun m hm => hfb m (by
          rw [allNamesBinds]
          exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)))
        hfbody hnib.2 hnibody
        (fun k b hb => hsub k b (by
          rw [assignBinds]
          rcases List.mem_append.mp hb with h | h
          · exact List.mem_append_left _ (List.mem_append_right _ h)
          · exact List.mem_append_right _ h))
        (fun k b hb => by
          have hk : isFreshName k = true := hFK k b hb
          have : k ≠ n := by intro h; rw [h, hnf] at hk; exact Bool.noConfusion hk
          rw [updateInd, if_neg this]; exact hkn k b hb)
        (fun m hm => by
          by_cases hmn : m = n
          · subst hmn; rw [updateInd, updateInd, if_pos rfl, if_pos rfl]
          · rw [updateInd, updateInd, if_neg hmn, if_neg hmn]; exact hoff m hm)
        (fun m hm => by
          have hm1 : m ∉ bnd ∧ m ≠ n := by
            constructor
            · intro h; exact hm (mem_addName.mpr (Or.inl h))
            · intro h; exact hm (mem_addName.mpr (Or.inr h))
          rw [updateInd, if_neg hm1.2]; exact hnu m hm1.1)
        hsg
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Term.size, Sentence.size, bindingsSize]
  all_goals omega

/-- Head clause down an existential boundlist. -/
theorem normEX_head (i : Interp) (A : List (String × Sentence))
    (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (bs : List Binding) (body : Sentence) (bnd bm : List String) (c : Nat)
      (kap nu : String → i.dom) (sg : String → List i.dom),
      NoFresh (allNamesBinds bs) → NoFresh (allNamesS body) →
      noIntrBinds bnd bm bs = true →
      noIntrS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs)) body = true →
      (∀ k b, (k, b) ∈ assignBinds bnd bm c bs
          ++ assignS (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
               (normBinds bnd bm c bs).2.2 body → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap nu →
      (∀ m, m ∉ bnd → nu m = i.iName m) → (∀ m, m ∉ bm → sg m = []) →
      (SatExists i kap sg (normBinds bnd bm c bs).1
          (normSent (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
            (normBinds bnd bm c bs).2.2 body).1
        ↔ SatExists i nu sg bs body)
  | [], body => by
      intro bnd bm c kap nu sg _ hfb _ hnib hsub hkn hoff hnu hsg
      rw [normBinds]
      rw [bindNames, bindMarks, addNames, addNames] at *
      rw [satExists_nil_iff, satExists_nil_iff]
      exact normS_head i A hLoc hFK body bnd bm c kap nu sg hfb hnib
        (fun k b hb => hsub k b (by
          rw [assignBinds]; exact List.mem_append_right _ hb)) hkn hoff hnu hsg
  | .plain n :: r, body => by
      intro bnd bm c kap nu sg hfb hfbody hnib hnibody hsub hkn hoff hnu hsg
      have hnf : isFreshName n = false :=
        hfb n (by rw [allNamesBinds]; exact List.mem_cons_self)
      rw [normBinds, bindNames, bindMarks, addNames] at *
      rw [satExists_plain_iff, satExists_plain_iff]
      refine exists_congr (fun x => ?_)
      rw [noIntrBinds] at hnib
      exact normEX_head i A hLoc hFK r body (addName bnd n) bm c
        (updateInd kap n x) (updateInd nu n x) sg
        (fun m hm => hfb m (by rw [allNamesBinds]; exact List.mem_cons_of_mem _ hm))
        hfbody hnib hnibody
        (fun k b hb => hsub k b (by rw [assignBinds]; exact hb))
        (fun k b hb => by
          have hk : isFreshName k = true := hFK k b hb
          have : k ≠ n := by intro h; rw [h, hnf] at hk; exact Bool.noConfusion hk
          rw [updateInd, if_neg this]; exact hkn k b hb)
        (fun m hm => by
          by_cases hmn : m = n
          · subst hmn; rw [updateInd, updateInd, if_pos rfl, if_pos rfl]
          · rw [updateInd, updateInd, if_neg hmn, if_neg hmn]; exact hoff m hm)
        (fun m hm => by
          have hm1 : m ∉ bnd ∧ m ≠ n := by
            constructor
            · intro h; exact hm (mem_addName.mpr (Or.inl h))
            · intro h; exact hm (mem_addName.mpr (Or.inr h))
          rw [updateInd, if_neg hm1.2]; exact hnu m hm1.1)
        hsg
  | .seqmark mk :: r, body => by
      intro bnd bm c kap nu sg hfb hfbody hnib hnibody hsub hkn hoff hnu hsg
      rw [normBinds, bindNames, bindMarks, addNames] at *
      rw [satExists_seqmark_iff, satExists_seqmark_iff]
      refine exists_congr (fun xs => ?_)
      rw [noIntrBinds] at hnib
      exact normEX_head i A hLoc hFK r body bnd (addName bm mk) c
        kap nu (updateSeq sg mk xs)
        (fun m hm => hfb m (by rw [allNamesBinds]; exact hm))
        hfbody hnib hnibody
        (fun k b hb => hsub k b (by rw [assignBinds]; exact hb))
        hkn hoff hnu
        (fun m hm => by
          have hm1 : m ∉ bm ∧ m ≠ mk := by
            constructor
            · intro h; exact hm (mem_addName.mpr (Or.inl h))
            · intro h; exact hm (mem_addName.mpr (Or.inr h))
          rw [updateSeq, if_neg hm1.2]; exact hsg m hm1.1)
  | .restricted n g :: r, body => by
      intro bnd bm c kap nu sg hfb hfbody hnib hnibody hsub hkn hoff hnu hsg
      have hnf : isFreshName n = false :=
        hfb n (by rw [allNamesBinds]; exact List.mem_cons_self)
      rw [normBinds, bindNames, bindMarks, addNames] at *
      rw [satExists_restricted_iff, satExists_restricted_iff]
      rw [noIntrBinds] at hnib
      simp only [Bool.and_eq_true] at hnib
      rw [normT_head i A hLoc hFK g bnd bm c kap nu sg
            (fun m hm => hfb m (by
              rw [allNamesBinds]
              exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
            hnib.1
            (fun k b hb => hsub k b (by
              rw [assignBinds]; exact List.mem_append_left _ (List.mem_append_left _ hb)))
            hkn hoff hnu hsg]
      refine exists_congr (fun x => and_congr Iff.rfl ?_)
      exact normEX_head i A hLoc hFK r body (addName bnd n) bm
        (normTerm bnd bm c g).2.2 (updateInd kap n x) (updateInd nu n x) sg
        (fun m hm => hfb m (by
          rw [allNamesBinds]
          exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)))
        hfbody hnib.2 hnibody
        (fun k b hb => hsub k b (by
          rw [assignBinds]
          rcases List.mem_append.mp hb with h | h
          · exact List.mem_append_left _ (List.mem_append_right _ h)
          · exact List.mem_append_right _ h))
        (fun k b hb => by
          have hk : isFreshName k = true := hFK k b hb
          have : k ≠ n := by intro h; rw [h, hnf] at hk; exact Bool.noConfusion hk
          rw [updateInd, if_neg this]; exact hkn k b hb)
        (fun m hm => by
          by_cases hmn : m = n
          · subst hmn; rw [updateInd, updateInd, if_pos rfl, if_pos rfl]
          · rw [updateInd, updateInd, if_neg hmn, if_neg hmn]; exact hoff m hm)
        (fun m hm => by
          have hm1 : m ∉ bnd ∧ m ≠ n := by
            constructor
            · intro h; exact hm (mem_addName.mpr (Or.inl h))
            · intro h; exact hm (mem_addName.mpr (Or.inr h))
          rw [updateInd, if_neg hm1.2]; exact hnu m hm1.1)
        hsg
termination_by bs body => bindingsSize bs + body.size
decreasing_by
  all_goals simp [Term.size, Sentence.size, bindingsSize]
  all_goals omega

end

/-! ## The tail clause

Every emitted tail sentence holds under the new valuation. This clause
uses `IklRespectsThat`, and it does NOT use any premise about the
original sentence being satisfied — which is what makes Hayes's
conjecture follow from it. -/

mutual

/-- Tail clause for terms. -/
theorem normT_tails (i : Interp) (A : List (String × Sentence))
    (hIkl : IklRespectsThat i) (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (t : Term) (bnd bm : List String) (c : Nat) (kap : String → i.dom),
      NoFresh (allNamesT t) → noIntrT bnd bm t = true →
      (∀ k b, (k, b) ∈ assignT bnd bm c t → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap i.iName →
      ∀ tl ∈ (normTerm bnd bm c t).2.1, Sat i kap (fun _ => []) tl
  | .name _ => by
      intro bnd bm c kap _ _ _ _ _ tl htl
      rw [normTerm] at htl; exact absurd htl List.not_mem_nil
  | .str _ => by
      intro bnd bm c kap _ _ _ _ _ tl htl
      rw [normTerm] at htl; exact absurd htl List.not_mem_nil
  | .funapp op args => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normTerm] at htl
      rw [noIntrT] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normT_tails i A hIkl hLoc hFK op bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesT]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignT]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normSeq_tails i A hIkl hLoc hFK args bnd bm (normTerm bnd bm c op).2.2 kap
          (fun n hn => hfr n (by rw [allNamesT]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignT]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .that s => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normTerm_that_tails bnd bm c s hni] at htl
      have hbody : noIntrS [] [] s = true := noIntr_body bnd bm s hni
      have hfrs : NoFresh (allNamesS s) :=
        fun n hn => hfr n (by rw [allNamesT]; exact hn)
      have hsubb : ∀ k b, (k, b) ∈ assignS [] [] (c + 1) s → (k, b) ∈ A :=
        fun k b hb => hsub k b (by
          rw [assignT_that_noIntr bnd bm c s hni]; exact List.mem_cons_of_mem _ hb)
      have hhead : Sat i kap (fun _ => []) (normSent [] [] (c + 1) s).1
          ↔ Sat i i.iName (fun _ => []) s :=
        normS_head i A hLoc hFK s [] [] (c + 1) kap i.iName (fun _ => [])
          hfrs hbody hsubb hkn hoff (fun _ _ => rfl) (fun _ _ => rfl)
      rcases List.mem_cons.mp htl with rfl | h
      · rw [sat_iff_iff, sat_atom_iff, denotTerm, denotSeq]
        have hmem : (propName c, s) ∈ A :=
          hsub _ _ (by
            rw [assignT_that_noIntr bnd bm c s hni]; exact List.mem_cons_self)
        rw [hkn _ _ hmem]
        exact Iff.trans (hIkl s i.iName (fun _ => [])) hhead.symm
      · exact normS_tails i A hIkl hLoc hFK s [] [] (c + 1) kap
          hfrs hbody hsubb hkn hoff tl h
termination_by t => t.size
decreasing_by
  all_goals simp [Term.size]
  all_goals omega

/-- Tail clause for argument sequences. -/
theorem normSeq_tails (i : Interp) (A : List (String × Sentence))
    (hIkl : IklRespectsThat i) (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (args : List SeqItem) (bnd bm : List String) (c : Nat) (kap : String → i.dom),
      NoFresh (allNamesSeq args) → noIntrSeq bnd bm args = true →
      (∀ k b, (k, b) ∈ assignSeq bnd bm c args → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap i.iName →
      ∀ tl ∈ (normSeq bnd bm c args).2.1, Sat i kap (fun _ => []) tl
  | [] => by
      intro bnd bm c kap _ _ _ _ _ tl htl
      rw [normSeq] at htl; exact absurd htl List.not_mem_nil
  | .term t :: r => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSeq] at htl
      rw [noIntrSeq] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normT_tails i A hIkl hLoc hFK t bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesSeq]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignSeq]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normSeq_tails i A hIkl hLoc hFK r bnd bm (normTerm bnd bm c t).2.2 kap
          (fun n hn => hfr n (by rw [allNamesSeq]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignSeq]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .seqmark m :: r => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSeq] at htl
      rw [noIntrSeq] at hni
      exact normSeq_tails i A hIkl hLoc hFK r bnd bm c kap
        (fun n hn => hfr n (by rw [allNamesSeq]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignSeq]; exact hb)) hkn hoff tl htl
termination_by args => seqItemsSize args
decreasing_by
  all_goals simp [Term.size, seqItemsSize]
  all_goals omega

/-- Tail clause down a boundlist's guards. -/
theorem normBinds_tails (i : Interp) (A : List (String × Sentence))
    (hIkl : IklRespectsThat i) (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (bs : List Binding) (bnd bm : List String) (c : Nat) (kap : String → i.dom),
      NoFresh (allNamesBinds bs) → noIntrBinds bnd bm bs = true →
      (∀ k b, (k, b) ∈ assignBinds bnd bm c bs → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap i.iName →
      ∀ tl ∈ (normBinds bnd bm c bs).2.1, Sat i kap (fun _ => []) tl
  | [] => by
      intro bnd bm c kap _ _ _ _ _ tl htl
      rw [normBinds] at htl; exact absurd htl List.not_mem_nil
  | .plain n :: r => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normBinds] at htl
      rw [noIntrBinds] at hni
      exact normBinds_tails i A hIkl hLoc hFK r (addName bnd n) bm c kap
        (fun m hm => hfr m (by rw [allNamesBinds]; exact List.mem_cons_of_mem _ hm))
        hni (fun k b hb => hsub k b (by rw [assignBinds]; exact hb)) hkn hoff tl htl
  | .seqmark mk :: r => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normBinds] at htl
      rw [noIntrBinds] at hni
      exact normBinds_tails i A hIkl hLoc hFK r bnd (addName bm mk) c kap
        (fun m hm => hfr m (by rw [allNamesBinds]; exact hm))
        hni (fun k b hb => hsub k b (by rw [assignBinds]; exact hb)) hkn hoff tl htl
  | .restricted n g :: r => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normBinds] at htl
      rw [noIntrBinds] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normT_tails i A hIkl hLoc hFK g bnd bm c kap
          (fun m hm => hfr m (by
            rw [allNamesBinds]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
          hni.1
          (fun k b hb => hsub k b (by
            rw [assignBinds]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normBinds_tails i A hIkl hLoc hFK r (addName bnd n) bm
          (normTerm bnd bm c g).2.2 kap
          (fun m hm => hfr m (by
            rw [allNamesBinds]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)))
          hni.2
          (fun k b hb => hsub k b (by
            rw [assignBinds]; exact List.mem_append_right _ hb))
          hkn hoff tl h
termination_by bs => bindingsSize bs
decreasing_by
  all_goals simp [Term.size, bindingsSize]
  all_goals omega

/-- Tail clause for sentences. -/
theorem normS_tails (i : Interp) (A : List (String × Sentence))
    (hIkl : IklRespectsThat i) (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (s : Sentence) (bnd bm : List String) (c : Nat) (kap : String → i.dom),
      NoFresh (allNamesS s) → noIntrS bnd bm s = true →
      (∀ k b, (k, b) ∈ assignS bnd bm c s → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap i.iName →
      ∀ tl ∈ (normSent bnd bm c s).2.1, Sat i kap (fun _ => []) tl
  | .atom p args => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normT_tails i A hIkl hLoc hFK p bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normSeq_tails i A hIkl hLoc hFK args bnd bm (normTerm bnd bm c p).2.2 kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .eq a b => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normT_tails i A hIkl hLoc hFK a bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normT_tails i A hIkl hLoc hFK b bnd bm (normTerm bnd bm c a).2.2 kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .conj ss => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      exact normSs_tails i A hIkl hLoc hFK ss bnd bm c kap
        (fun n hn => hfr n (by rw [allNamesS]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignS]; exact hb)) hkn hoff tl htl
  | .disj ss => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      exact normSs_tails i A hIkl hLoc hFK ss bnd bm c kap
        (fun n hn => hfr n (by rw [allNamesS]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignS]; exact hb)) hkn hoff tl htl
  | .neg s => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      exact normS_tails i A hIkl hLoc hFK s bnd bm c kap
        (fun n hn => hfr n (by rw [allNamesS]; exact hn)) hni
        (fun k b hb => hsub k b (by rw [assignS]; exact hb)) hkn hoff tl htl
  | .impl a b => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normS_tails i A hIkl hLoc hFK a bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normS_tails i A hIkl hLoc hFK b bnd bm (normSent bnd bm c a).2.2 kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .iff a b => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normS_tails i A hIkl hLoc hFK a bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normS_tails i A hIkl hLoc hFK b bnd bm (normSent bnd bm c a).2.2 kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k bb hb => hsub k bb (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .all bs body => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normBinds_tails i A hIkl hLoc hFK bs bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normS_tails i A hIkl hLoc hFK body
          (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
          (normBinds bnd bm c bs).2.2 kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff tl h
  | .ex bs body => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSent] at htl
      rw [noIntrS] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normBinds_tails i A hIkl hLoc hFK bs bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normS_tails i A hIkl hLoc hFK body
          (addNames bnd (bindNames bs)) (addNames bm (bindMarks bs))
          (normBinds bnd bm c bs).2.2 kap
          (fun n hn => hfr n (by rw [allNamesS]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignS]; exact List.mem_append_right _ hb))
          hkn hoff tl h
termination_by s => s.size
decreasing_by
  all_goals simp [Term.size, Sentence.size, seqItemsSize, sentencesSize, bindingsSize]
  all_goals omega

/-- Tail clause for a sentence list. -/
theorem normSs_tails (i : Interp) (A : List (String × Sentence))
    (hIkl : IklRespectsThat i) (hLoc : IklPropLocal i) (hFK : FreshKeys A) :
    ∀ (ss : List Sentence) (bnd bm : List String) (c : Nat) (kap : String → i.dom),
      NoFresh (allNamesSs ss) → noIntrSs bnd bm ss = true →
      (∀ k b, (k, b) ∈ assignSs bnd bm c ss → (k, b) ∈ A) →
      KnowsA i A kap → OffFresh i kap i.iName →
      ∀ tl ∈ (normSents bnd bm c ss).2.1, Sat i kap (fun _ => []) tl
  | [] => by
      intro bnd bm c kap _ _ _ _ _ tl htl
      rw [normSents] at htl; exact absurd htl List.not_mem_nil
  | s :: r => by
      intro bnd bm c kap hfr hni hsub hkn hoff tl htl
      rw [normSents] at htl
      rw [noIntrSs] at hni
      simp only [Bool.and_eq_true] at hni
      rcases List.mem_append.mp htl with h | h
      · exact normS_tails i A hIkl hLoc hFK s bnd bm c kap
          (fun n hn => hfr n (by rw [allNamesSs]; exact List.mem_append_left _ hn))
          hni.1
          (fun k b hb => hsub k b (by rw [assignSs]; exact List.mem_append_left _ hb))
          hkn hoff tl h
      · exact normSs_tails i A hIkl hLoc hFK r bnd bm (normSent bnd bm c s).2.2 kap
          (fun n hn => hfr n (by rw [allNamesSs]; exact List.mem_append_right _ hn))
          hni.2
          (fun k b hb => hsub k b (by rw [assignSs]; exact List.mem_append_right _ hb))
          hkn hoff tl h
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

end

/-! ## Every allocated key is a fresh name -/

mutual

/-- Keys allocated inside a term. -/
theorem assignT_keys_fresh :
    ∀ (t : Term) (bnd bm : List String) (c : Nat) (k : String) (b : Sentence),
      (k, b) ∈ assignT bnd bm c t → isFreshName k = true
  | .name _ => by intro bnd bm c k b h; rw [assignT] at h; exact absurd h List.not_mem_nil
  | .str _ => by intro bnd bm c k b h; rw [assignT] at h; exact absurd h List.not_mem_nil
  | .funapp op args => by
      intro bnd bm c k b h
      rw [assignT] at h
      rcases List.mem_append.mp h with h | h
      · exact assignT_keys_fresh op bnd bm c k b h
      · exact assignSeq_keys_fresh args bnd bm _ k b h
  | .that s => by
      intro bnd bm c k b h
      rw [assignT] at h
      rcases List.mem_cons.mp h with h | h
      · have hk : k = propName c := congrArg Prod.fst h
        rw [hk]; exact isFreshName_propName c
      · exact assignS_keys_fresh s _ _ (c + 1) k b h
termination_by t => t.size
decreasing_by
  all_goals simp [Term.size]
  all_goals omega

/-- Keys allocated inside an argument sequence. -/
theorem assignSeq_keys_fresh :
    ∀ (args : List SeqItem) (bnd bm : List String) (c : Nat) (k : String) (b : Sentence),
      (k, b) ∈ assignSeq bnd bm c args → isFreshName k = true
  | [] => by intro bnd bm c k b h; rw [assignSeq] at h; exact absurd h List.not_mem_nil
  | .term t :: r => by
      intro bnd bm c k b h
      rw [assignSeq] at h
      rcases List.mem_append.mp h with h | h
      · exact assignT_keys_fresh t bnd bm c k b h
      · exact assignSeq_keys_fresh r bnd bm _ k b h
  | .seqmark _ :: r => by
      intro bnd bm c k b h
      rw [assignSeq] at h
      exact assignSeq_keys_fresh r bnd bm c k b h
termination_by args => seqItemsSize args
decreasing_by
  all_goals simp [Term.size, seqItemsSize]
  all_goals omega

/-- Keys allocated inside a boundlist. -/
theorem assignBinds_keys_fresh :
    ∀ (bs : List Binding) (bnd bm : List String) (c : Nat) (k : String) (b : Sentence),
      (k, b) ∈ assignBinds bnd bm c bs → isFreshName k = true
  | [] => by intro bnd bm c k b h; rw [assignBinds] at h; exact absurd h List.not_mem_nil
  | .plain n :: r => by
      intro bnd bm c k b h
      rw [assignBinds] at h
      exact assignBinds_keys_fresh r _ bm c k b h
  | .seqmark m :: r => by
      intro bnd bm c k b h
      rw [assignBinds] at h
      exact assignBinds_keys_fresh r bnd _ c k b h
  | .restricted n g :: r => by
      intro bnd bm c k b h
      rw [assignBinds] at h
      rcases List.mem_append.mp h with h | h
      · exact assignT_keys_fresh g bnd bm c k b h
      · exact assignBinds_keys_fresh r _ bm _ k b h
termination_by bs => bindingsSize bs
decreasing_by
  all_goals simp [Term.size, bindingsSize]
  all_goals omega

/-- Keys allocated inside a sentence. -/
theorem assignS_keys_fresh :
    ∀ (s : Sentence) (bnd bm : List String) (c : Nat) (k : String) (b : Sentence),
      (k, b) ∈ assignS bnd bm c s → isFreshName k = true
  | .atom p args => by
      intro bnd bm c k b h
      rw [assignS] at h
      rcases List.mem_append.mp h with h | h
      · exact assignT_keys_fresh p bnd bm c k b h
      · exact assignSeq_keys_fresh args bnd bm _ k b h
  | .eq a b => by
      intro bnd bm c k bb h
      rw [assignS] at h
      rcases List.mem_append.mp h with h | h
      · exact assignT_keys_fresh a bnd bm c k bb h
      · exact assignT_keys_fresh b bnd bm _ k bb h
  | .conj ss => by
      intro bnd bm c k b h; rw [assignS] at h
      exact assignSs_keys_fresh ss bnd bm c k b h
  | .disj ss => by
      intro bnd bm c k b h; rw [assignS] at h
      exact assignSs_keys_fresh ss bnd bm c k b h
  | .neg s => by
      intro bnd bm c k b h; rw [assignS] at h
      exact assignS_keys_fresh s bnd bm c k b h
  | .impl a b => by
      intro bnd bm c k bb h
      rw [assignS] at h
      rcases List.mem_append.mp h with h | h
      · exact assignS_keys_fresh a bnd bm c k bb h
      · exact assignS_keys_fresh b bnd bm _ k bb h
  | .iff a b => by
      intro bnd bm c k bb h
      rw [assignS] at h
      rcases List.mem_append.mp h with h | h
      · exact assignS_keys_fresh a bnd bm c k bb h
      · exact assignS_keys_fresh b bnd bm _ k bb h
  | .all bs body => by
      intro bnd bm c k b h
      rw [assignS] at h
      rcases List.mem_append.mp h with h | h
      · exact assignBinds_keys_fresh bs bnd bm c k b h
      · exact assignS_keys_fresh body _ _ _ k b h
  | .ex bs body => by
      intro bnd bm c k b h
      rw [assignS] at h
      rcases List.mem_append.mp h with h | h
      · exact assignBinds_keys_fresh bs bnd bm c k b h
      · exact assignS_keys_fresh body _ _ _ k b h
termination_by s => s.size
decreasing_by
  all_goals simp [Term.size, Sentence.size, seqItemsSize, sentencesSize, bindingsSize]
  all_goals omega

/-- Keys allocated inside a sentence list. -/
theorem assignSs_keys_fresh :
    ∀ (ss : List Sentence) (bnd bm : List String) (c : Nat) (k : String) (b : Sentence),
      (k, b) ∈ assignSs bnd bm c ss → isFreshName k = true
  | [] => by intro bnd bm c k b h; rw [assignSs] at h; exact absurd h List.not_mem_nil
  | s :: r => by
      intro bnd bm c k b h
      rw [assignSs] at h
      rcases List.mem_append.mp h with h | h
      · exact assignS_keys_fresh s bnd bm c k b h
      · exact assignSs_keys_fresh r bnd bm _ k b h
termination_by ss => sentencesSize ss
decreasing_by
  all_goals simp [Sentence.size, sentencesSize]
  all_goals omega

end

/-- The allocation list of a sentence has fresh keys throughout. -/
theorem freshKeys_assignS (s : Sentence) (bnd bm : List String) (c : Nat) :
    FreshKeys (assignS bnd bm c s) :=
  fun k b h => assignS_keys_fresh s bnd bm c k b h

/-! ## The valuation the construction builds -/

/-- Hayes's J: the original interpretation with each allocated fresh
name pointed at the proposition its `that`-body denotes. Only the name
valuation changes; `rel`, `fn` and `iProp` are untouched, which is why
this is stated as a valuation rather than as a new interpretation. -/
noncomputable def kapOf (i : Interp) (A : List (String × Sentence))
    (n : String) : i.dom :=
  match A.find? (fun p => p.1 == n) with
  | some p => i.iProp p.2 i.iName (fun _ => [])
  | none => i.iName n

/-- Off the fresh-name space the valuation is unchanged. -/
theorem kapOf_offFresh (i : Interp) :
    ∀ (A : List (String × Sentence)), FreshKeys A → OffFresh i (kapOf i A) i.iName
  | [] => by intro _ m _; rw [kapOf]; simp [List.find?]
  | (k0, b0) :: r => by
      intro hFK m hm
      have hk0 : isFreshName k0 = true := hFK k0 b0 List.mem_cons_self
      have hne : (k0 == m) = false := by
        by_cases h : k0 = m
        · rw [h, hm] at hk0; exact absurd hk0 (by simp)
        · simp [h]
      rw [kapOf, List.find?_cons]
      simp only [hne, Bool.false_eq_true, if_false]
      have hrec :=
        kapOf_offFresh i r (fun k b hb => hFK k b (List.mem_cons_of_mem _ hb)) m hm
      rw [kapOf] at hrec
      exact hrec

/-- With distinct keys, the valuation knows every allocation. -/
theorem kapOf_knowsA (i : Interp) :
    ∀ (A : List (String × Sentence)), (A.map Prod.fst).Nodup → KnowsA i A (kapOf i A)
  | [], _ => by intro k b h; exact absurd h List.not_mem_nil
  | (k0, b0) :: r, hnd => by
      intro k b hmem
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rw [kapOf, List.find?_cons]
      by_cases hk : (k0 == k) = true
      · simp only [hk, if_pos]
        have hkk : k0 = k := eq_of_beq hk
        rcases List.mem_cons.mp hmem with h | h
        · rw [(Prod.mk.injEq _ _ _ _).mp h |>.2]
        · exfalso
          exact hnd.1 ⟨(k, b), h, hkk.symm⟩
      · simp only [hk, if_neg, Bool.false_eq_true]
        have hne : (k0, b0) ≠ (k, b) := by
          intro h
          exact hk (by rw [(Prod.mk.injEq _ _ _ _).mp h |>.1]; exact beq_self_eq_true k)
        have hmr : (k, b) ∈ r := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hne
          · exact h
        have := kapOf_knowsA i r hnd.2 k b hmr
        rw [kapOf] at this
        exact this

/-! ## Satisfiability

`Satisfies i s` is `Sat i i.iName (fun _ => []) s` by definition, so
giving an interpretation plus a name valuation is the same as giving
an interpretation whose `iName` is that valuation. Stating
satisfiability with an explicit valuation avoids rebuilding the
interpretation record. -/

/-- A Common Logic text is satisfiable. -/
def ClSatisfiable (ss : List Sentence) : Prop :=
  ∃ (i : Interp) (nu : String → i.dom), ∀ s ∈ ss, Sat i nu (fun _ => []) s

/-- An IKL sentence is satisfiable: some coherent, local
interpretation satisfies it. -/
def IklSatisfiable (s : Sentence) : Prop :=
  ∃ i : Interp, IklRespectsThat i ∧ IklPropLocal i ∧ Satisfies i s

/-! ## The theorems

The three side conditions are: no quantifier intrudes into a
proposition name; the sentence uses no name from the fresh-name space;
and the allocation list has distinct keys. The third holds whenever
the fresh-name supply is injective — see the module header on why
injectivity of `propName` itself is not proved here — and is decidable
for any concrete sentence. -/

/-- **Hayes's construction, both halves.** The head sentence read
under the constructed valuation has the truth value the original
sentence has, and every tail sentence holds under that valuation. -/
theorem normalize_preserves (i : Interp) (hIkl : IklRespectsThat i)
    (hLoc : IklPropLocal i) (E : Sentence) (c : Nat)
    (hni : noIntrS [] [] E = true) (hfr : NoFresh (allNamesS E))
    (hnd : ((assignS [] [] c E).map Prod.fst).Nodup) :
    (Sat i (kapOf i (assignS [] [] c E)) (fun _ => []) (normSent [] [] c E).1
        ↔ Satisfies i E)
      ∧ (∀ tl ∈ (normSent [] [] c E).2.1,
          Sat i (kapOf i (assignS [] [] c E)) (fun _ => []) tl) := by
  have hFK : FreshKeys (assignS [] [] c E) := freshKeys_assignS E [] [] c
  have hkn : KnowsA i (assignS [] [] c E) (kapOf i (assignS [] [] c E)) :=
    kapOf_knowsA i (assignS [] [] c E) hnd
  have hoff : OffFresh i (kapOf i (assignS [] [] c E)) i.iName :=
    kapOf_offFresh i (assignS [] [] c E) hFK
  constructor
  · exact normS_head i (assignS [] [] c E) hLoc hFK E [] [] c
      (kapOf i (assignS [] [] c E)) i.iName (fun _ => [])
      hfr hni (fun _ _ h => h) hkn hoff (fun _ _ => rfl) (fun _ _ => rfl)
  · exact normS_tails i (assignS [] [] c E) hIkl hLoc hFK E [] [] c
      (kapOf i (assignS [] [] c E)) hfr hni (fun _ _ h => h) hkn hoff

/-- **Satisfiability is preserved forwards.** An IKL-satisfiable
sentence has a CL-satisfiable normalization. -/
theorem ikl_sat_to_cl_sat (E : Sentence) (c : Nat)
    (hni : noIntrS [] [] E = true) (hfr : NoFresh (allNamesS E))
    (hnd : ((assignS [] [] c E).map Prod.fst).Nodup) :
    IklSatisfiable E →
      ClSatisfiable ((normSent [] [] c E).1 :: (normSent [] [] c E).2.1) := by
  rintro ⟨i, hIkl, hLoc, hsat⟩
  obtain ⟨hhead, htails⟩ := normalize_preserves i hIkl hLoc E c hni hfr hnd
  refine ⟨i, kapOf i (assignS [] [] c E), ?_⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | h
  · exact hhead.mpr hsat
  · exact htails s h

/-- **Hayes's open conjecture, for the no-intrusion fragment.** The
tail sentences of a normalized IKL sentence are CL-satisfiable —
whatever the sentence, and whether or not the sentence itself is
satisfiable. The paper: "if the tail sentences are inconsistent in CL
... We have not found any such example, and believe that it is
impossible, but do not at the time of writing have a conclusive
proof." The proof here is that `normS_tails` never uses the premise
that the original sentence holds, so the model can be built from ANY
coherent, local IKL interpretation, and `iklProp` is one. -/
theorem tails_satisfiable (E : Sentence) (c : Nat)
    (hni : noIntrS [] [] E = true) (hfr : NoFresh (allNamesS E))
    (hnd : ((assignS [] [] c E).map Prod.fst).Nodup) :
    ClSatisfiable (normSent [] [] c E).2.1 := by
  obtain ⟨_, htails⟩ :=
    normalize_preserves iklProp iklProp_respects iklProp_local E c hni hfr hnd
  exact ⟨iklProp, kapOf iklProp (assignS [] [] c E), htails⟩

/-! ## The four paradoxes, semantically

`CL.Normalize` pins the SYNTAX of the paper's four normalizations.
This section pins their content: each sentence's side conditions are
discharged by decision, each normalization's head and tails are read
off by `rfl`, and each text is then decided satisfiable or not.

Three of the four normalized texts are CL-unsatisfiable, so by
`ikl_sat_to_cl_sat` the sentences themselves have no coherent IKL
model — which is what calling them paradoxes says. The Knower's fourth
sentence taken alone is satisfiable, and a model is exhibited.

Against each of those, `tails_satisfiable` gives a model of the TAIL
SET alone. That contrast is the non-vacuity check on Hayes's
conjecture: for the Liar the whole text is inconsistent while its tail
set is not. -/

/-- 1. That Nothing Is True. -/
def tnitS : Sentence :=
  .atom (.that (.all [.plain "p"] (.neg (.atom (.name "p") [])))) []

/-- 2. The Liar. -/
def liarS : Sentence :=
  .eq (.name "p") (.that (.neg (.atom (.name "p") [])))

/-- 3. Kripke's semantic paradox. -/
def kripkeS : Sentence :=
  .all [.plain "x"]
    (.iff (.atom (.name "S") [.term (.name "x")])
      (.eq (.name "x")
        (.that (.all [.plain "y"]
          (.impl (.atom (.name "S") [.term (.name "y")])
            (.neg (.atom (.name "y") [])))))))

/-- 4. The Knower, fourth sentence. -/
def knowerS : Sentence :=
  .eq (.name "D")
    (.that (.atom (.name "K") [.term (.that (.neg (.atom (.name "D") [])))]))

-- The abstract sentences are the paper's texts.
#guard tnitS.toClif == "((that (forall (p) (not (p)))))"
#guard liarS.toClif == "(= p (that (not (p))))"
#guard kripkeS.toClif ==
  "(forall (x) (iff (S x) (= x (that (forall (y) (if (S y) (not (y))))))))"
#guard knowerS.toClif == "(= D (that (K (that (not (D))))))"

/-! ### That Nothing Is True -/

theorem tnit_head : (normSent [] [] 1 tnitS).1 = .atom (.name "prop1") [] := rfl

theorem tnit_tails : (normSent [] [] 1 tnitS).2.1 =
    [.iff (.atom (.name "prop1") [])
      (.all [.plain "p"] (.neg (.atom (.name "p") [])))] := rfl

/-- The normalized text is CL-unsatisfiable: the head asserts the
proposition, the tail equates it with "no proposition holds". -/
theorem tnit_cl_unsat :
    ¬ ClSatisfiable ((normSent [] [] 1 tnitS).1 :: (normSent [] [] 1 tnitS).2.1) := by
  rintro ⟨i, nu, h⟩
  rw [tnit_head, tnit_tails] at h
  have h1 := h _ (List.mem_cons_self)
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [sat_atom_iff, denotTerm, denotSeq] at h1
  rw [sat_iff_iff, sat_atom_iff, denotTerm, denotSeq, sat_all_iff,
      satForall_plain_iff] at h2
  have h3 := h2.mp h1 (nu "prop1")
  rw [satForall_nil_iff, sat_neg_iff, sat_atom_iff, denotTerm, denotSeq,
      updateInd] at h3
  simp only [if_pos] at h3
  exact h3 h1

/-- Hence the sentence has no coherent IKL model. -/
theorem tnit_not_ikl_sat : ¬ IklSatisfiable tnitS := fun h =>
  tnit_cl_unsat (ikl_sat_to_cl_sat tnitS 1 (by decide)
    (by unfold NoFresh; decide) (by decide) h)

/-- Its tail set alone IS satisfiable — Hayes's conjecture, here. -/
theorem tnit_tails_sat : ClSatisfiable (normSent [] [] 1 tnitS).2.1 :=
  tails_satisfiable tnitS 1 (by decide) (by unfold NoFresh; decide) (by decide)

/-! ### The Liar -/

theorem liar_head : (normSent [] [] 2 liarS).1 = .eq (.name "p") (.name "prop2") := rfl

theorem liar_tails : (normSent [] [] 2 liarS).2.1 =
    [.iff (.atom (.name "prop2") []) (.neg (.atom (.name "p") []))] := rfl

/-- The normalized text is CL-unsatisfiable: the head makes the two
names co-denote, and the tail then says a proposition holds exactly
when it does not. -/
theorem liar_cl_unsat :
    ¬ ClSatisfiable ((normSent [] [] 2 liarS).1 :: (normSent [] [] 2 liarS).2.1) := by
  rintro ⟨i, nu, h⟩
  rw [liar_head, liar_tails] at h
  have h1 := h _ (List.mem_cons_self)
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [sat_eq_iff, denotTerm, denotTerm] at h1
  rw [sat_iff_iff, sat_atom_iff, denotTerm, denotSeq, sat_neg_iff, sat_atom_iff,
      denotTerm, denotSeq] at h2
  rw [← h1] at h2
  exact iff_not_self h2

/-- Hence the Liar has no coherent IKL model. -/
theorem liar_not_ikl_sat : ¬ IklSatisfiable liarS := fun h =>
  liar_cl_unsat (ikl_sat_to_cl_sat liarS 2 (by decide)
    (by unfold NoFresh; decide) (by decide) h)

/-- Its tail set alone is satisfiable. -/
theorem liar_tails_sat : ClSatisfiable (normSent [] [] 2 liarS).2.1 :=
  tails_satisfiable liarS 2 (by decide) (by unfold NoFresh; decide) (by decide)

/-! ### Kripke's semantic paradox -/

theorem kripke_head : (normSent [] [] 3 kripkeS).1 =
    .all [.plain "x"]
      (.iff (.atom (.name "S") [.term (.name "x")])
        (.eq (.name "x") (.name "prop3"))) := rfl

theorem kripke_tails : (normSent [] [] 3 kripkeS).2.1 =
    [.iff (.atom (.name "prop3") [])
      (.all [.plain "y"]
        (.impl (.atom (.name "S") [.term (.name "y")])
          (.neg (.atom (.name "y") []))))] := rfl

/-- The normalized text is CL-unsatisfiable. The head makes `S` hold
of exactly the one individual `prop3` denotes; the tail then says that
individual is a true proposition exactly when it is not. -/
theorem kripke_cl_unsat :
    ¬ ClSatisfiable ((normSent [] [] 3 kripkeS).1 :: (normSent [] [] 3 kripkeS).2.1) := by
  rintro ⟨i, nu, h⟩
  rw [kripke_head, kripke_tails] at h
  have h1 := h _ (List.mem_cons_self)
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [sat_all_iff, satForall_plain_iff] at h1
  have hS : ∀ x : i.dom, i.rel (nu "S") [x] ↔ x = nu "prop3" := by
    intro x
    have hx := h1 x
    rw [satForall_nil_iff, sat_iff_iff, sat_atom_iff, sat_eq_iff] at hx
    simpa [denotTerm, denotSeq, updateInd] using hx
  have hTail : i.rel (nu "prop3") [] ↔ ∀ x : i.dom, i.rel (nu "S") [x] → ¬ i.rel x [] := by
    rw [sat_iff_iff, sat_atom_iff, denotTerm, denotSeq, sat_all_iff,
        satForall_plain_iff] at h2
    refine Iff.trans h2 (forall_congr' (fun x => ?_))
    rw [satForall_nil_iff, sat_impl_iff, sat_atom_iff, sat_neg_iff, sat_atom_iff]
    simp [denotTerm, denotSeq, updateInd]
  by_cases hp : i.rel (nu "prop3") []
  · exact hTail.mp hp (nu "prop3") ((hS _).mpr rfl) hp
  · exact hp (hTail.mpr (fun x hx hrx => absurd ((hS x).mp hx ▸ hrx) hp))

/-- Hence Kripke's sentence has no coherent IKL model. -/
theorem kripke_not_ikl_sat : ¬ IklSatisfiable kripkeS := fun h =>
  kripke_cl_unsat (ikl_sat_to_cl_sat kripkeS 3 (by decide)
    (by unfold NoFresh; decide) (by decide) h)

/-- Its tail set alone is satisfiable. -/
theorem kripke_tails_sat : ClSatisfiable (normSent [] [] 3 kripkeS).2.1 :=
  tails_satisfiable kripkeS 3 (by decide) (by unfold NoFresh; decide) (by decide)

/-! ### The Knower

The paper's fourth Knower sentence taken alone is consistent: the
paradox needs the other three, which carry no proposition name and are
unchanged by normalization. A model of the whole normalized text is
exhibited, so this is where the preservation theorem is seen doing
work in the positive direction. -/

theorem knower_head : (normSent [] [] 4 knowerS).1 =
    .eq (.name "D") (.name "prop4") := rfl

theorem knower_tails : (normSent [] [] 4 knowerS).2.1 =
    [.iff (.atom (.name "prop4") [])
       (.atom (.name "K") [.term (.name "prop5")]),
     .iff (.atom (.name "prop5") []) (.neg (.atom (.name "D") []))] := rfl

/-- Two iterations of the main loop, so two tail sentences. -/
theorem knower_two_iterations : (normSent [] [] 4 knowerS).2.1.length = 2 := rfl

/-- The normalized text is satisfiable, in `iklProp`, under the
valuation that makes `prop5` the true proposition and everything else
false. -/
theorem knower_cl_sat :
    ClSatisfiable ((normSent [] [] 4 knowerS).1 :: (normSent [] [] 4 knowerS).2.1) := by
  refine ⟨iklProp, fun n => if n = "prop5" then True else False, ?_⟩
  rw [knower_head, knower_tails]
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · rw [sat_eq_iff, denotTerm, denotTerm]; simp
  rcases List.mem_cons.mp hs with rfl | hs
  · rw [sat_iff_iff, sat_atom_iff, sat_atom_iff]
    simp [iklProp, denotTerm, denotSeq]
  rcases List.mem_cons.mp hs with rfl | hs
  · rw [sat_iff_iff, sat_atom_iff, sat_neg_iff, sat_atom_iff]
    simp [iklProp, denotTerm, denotSeq]
  · exact absurd hs List.not_mem_nil

/-- Its tail set alone is satisfiable. -/
theorem knower_tails_sat : ClSatisfiable (normSent [] [] 4 knowerS).2.1 :=
  tails_satisfiable knowerS 4 (by decide) (by unfold NoFresh; decide) (by decide)

#print axioms normalize_preserves
#print axioms ikl_sat_to_cl_sat
#print axioms tails_satisfiable
#print axioms tnit_not_ikl_sat
#print axioms liar_not_ikl_sat
#print axioms kripke_not_ikl_sat
#print axioms knower_cl_sat
#print axioms tnit_tails_sat
#print axioms liar_tails_sat
#print axioms kripke_tails_sat
#print axioms knower_tails_sat

end L4Factoidal.CL
