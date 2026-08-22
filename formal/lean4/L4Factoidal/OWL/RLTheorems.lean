/-
L4Factoidal.OWL.RLTheorems — the OWL 2 RL/RDF closure operator against
its specification, proved natively.

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no solver.

## What is proved

* **T1 extensivity** — `closure_extensive`: `t ∈ g → t ∈ closure g
  fuel`, at any fuel, with no hypothesis.

* **T2 soundness** — `closure_sound`: `t ∈ closure g fuel → Derives g
  t`. This is the LICENSING theorem `formal/fstar/OWL.RL.Refinement.fst`
  states and `docs/theorem-registry.md` §1 tracks per row: every triple
  the engine emits is an input triple or a licensed application of a
  named table row. It is assembled from ONE LEMMA PER ROW
  (`eqSymFor_sound`, `prpTrpFor_sound`, ..., `scmUniFor_sound`) — 45
  of them, covering the 50 ported rows. Per-row status is therefore
  uniform: every ported row is proved licensed.

* **T3 monotonicity** — `closure_mono_of_saturated`: derived from T2 +
  `Derives.mono` + T4, hence conditional on the larger graph's closure
  being saturated. The unconditional same-fuel form is not proved and
  is not expected to hold pointwise: two runs stop at different rounds.

* **T4 completeness at the fixpoint** — `closure_complete_of_saturated`:
  `Derives g t → t ∈ closure g fuel`, given that the closure is
  saturated and that the collection-walk fuel was adequate
  (`ListFuelAdequate`, discussed below). All 55 constructor cases.

* **Clash soundness** — `detectClash_sound`: every `true` verdict of
  the decision procedure is a real `Clash`, again one lemma per clash
  row (13 of them).

## What is NOT proved, named rather than hidden

1. **Truth preservation (model theory) is not ported.** The F* tree
   proves, in `OWL.Semantics.fst` / `OWL.Semantics.Soundness.fst`, that
   each row PRESERVES TRUTH: for every OWL 2 RL interpretation `I` and
   graph `g`, if `I` satisfies `g` then `I` satisfies each row's
   conclusion. In Lean that statement would read

       theorem row_true {I : Interp} {g : Graph}
           (hI : Satisfies I g) {t : Triple} (h : Derives g t) :
           SatisfiesTriple I t

   and it needs the interpretation machinery (`OWL.Semantics.fst`'s
   `owl_interp`, `satisfies`, the class/property extension functions)
   ported first. Nothing here claims it. T2 is PROOF-THEORETIC: every
   computed triple has a derivation in the rule relation, which is the
   object a reviewer checks against the W3C table by eye. Do not read
   T2 as the F* model-theoretic soundness theorem.

2. **`closureFuelBound` is stated, not proved adequate.** What IS
   proved is `closure_saturated_or_underfueled`: the only alternative
   to saturation is a closure that grew by at least one triple per unit
   of fuel. Turning that into "the stated bound always suffices" needs
   the term-universe counting argument written out in
   `RLClosure.closureFuelBound`'s doc comment. Same named obligation
   the rdfs-core port carries.

3. **`ListFuelAdequate` is a hypothesis of T4, satisfiable but not
   discharged at `listFuel`.** The list-valued rows (cls-int1,
   cls-int2, cls-uni, cls-oo, scm-int, scm-uni, prp-spo2, prp-key,
   cax-adc) read their collection premises through a fuel-bounded walk.
   Soundness needs nothing: whatever the walk finds really is a list
   member (`listElems_sound`, `listSeqs_sound`, proved below, no
   hypothesis). Completeness needs the converse — that the walk finds
   everything — which is false for fuel 0 and true for fuel exceeding
   the longest chain. `exists_fuel_listElems` / `exists_fuel_listSeqs`
   prove such a fuel always exists; that `listFuel g = g.length + 1` is
   always one is the same counting obligation as (2), and is why T4
   carries the hypothesis instead of pretending.

## One membership relation throughout

Because `RLClosure.addOne` deduplicates with EXACT triple equality
rather than the engine's coarser `Triple.eqb`, every theorem here is
stated in ordinary list membership `t ∈ g` — in both directions. The
rdfs-core port has to state T1/T2 in list membership and T4 in
`Graph.mem`, because `Graph.add` can drop a triple in favour of an
eqb-equal variant. That asymmetry is absent here by construction.
-/
import L4Factoidal.OWL.RLClosure

namespace L4Factoidal.OWL

open L4Factoidal.RDF

/-! ## Section 1 — exact membership, `addOne`, `addAll` -/

theorem mem_of_memB {g : Graph} {t : Triple} (h : memB g t = true) : t ∈ g := by
  simp only [memB, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact hu

theorem memB_of_mem {g : Graph} {t : Triple} (h : t ∈ g) : memB g t = true := by
  simp only [memB, List.any_eq_true, beq_iff_eq]
  exact ⟨t, h, rfl⟩

theorem mem_addOne_of_mem {g : Graph} {t u : Triple} (h : t ∈ g) :
    t ∈ addOne g u := by
  unfold addOne
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_addOne_self (g : Graph) (t : Triple) : t ∈ addOne g t := by
  unfold addOne
  split
  · rename_i hm; exact mem_of_memB hm
  · exact List.mem_append_right _ (by simp)

theorem mem_addOne_cases {g : Graph} {t u : Triple} (h : t ∈ addOne g u) :
    t ∈ g ∨ t = u := by
  unfold addOne at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (List.mem_singleton.mp h')

theorem length_le_addOne (g : Graph) (u : Triple) :
    g.length ≤ (addOne g u).length := by
  unfold addOne
  split
  · exact Nat.le_refl _
  · simp

theorem addOne_eq_of_length_eq {g : Graph} {u : Triple}
    (h : (addOne g u).length = g.length) : addOne g u = g := by
  by_cases hm : memB g u = true
  · simp [addOne, hm]
  · simp [addOne, hm] at h

theorem mem_addAll_of_mem (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, t ∈ g → t ∈ addAll g ts := by
  induction ts with
  | nil => intro g t h; exact h
  | cons u ts ih =>
    intro g t h
    simp only [addAll]
    exact ih (addOne g u) (mem_addOne_of_mem h)

theorem mem_addAll_cases (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, t ∈ addAll g ts → t ∈ g ∨ t ∈ ts := by
  induction ts with
  | nil => intro g t h; exact Or.inl h
  | cons u ts ih =>
    intro g t h
    simp only [addAll] at h
    rcases ih (addOne g u) h with h' | h'
    · rcases mem_addOne_cases h' with h'' | rfl
      · exact Or.inl h''
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_addAll_of_mem_list (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, t ∈ ts → t ∈ addAll g ts := by
  induction ts with
  | nil => intro g t h; cases h
  | cons u ts ih =>
    intro g t h
    simp only [addAll]
    rcases List.mem_cons.mp h with rfl | h'
    · exact mem_addAll_of_mem ts (addOne g t) (mem_addOne_self g t)
    · exact ih (addOne g u) h'

theorem length_le_addAll (ts : List Triple) :
    ∀ (g : Graph), g.length ≤ (addAll g ts).length := by
  induction ts with
  | nil => intro g; exact Nat.le_refl _
  | cons u ts ih =>
    intro g
    simp only [addAll]
    exact Nat.le_trans (length_le_addOne g u) (ih (addOne g u))

/-- The fixpoint test made exact: if a round did not change the LENGTH,
the round was the identity. -/
theorem addAll_eq_of_length_eq (ts : List Triple) :
    ∀ (g : Graph), (addAll g ts).length = g.length → addAll g ts = g := by
  induction ts with
  | nil => intro g _; rfl
  | cons u ts ih =>
    intro g h
    simp only [addAll] at h ⊢
    have h1 : g.length ≤ (addOne g u).length := length_le_addOne g u
    have h2 : (addOne g u).length ≤ (addAll (addOne g u) ts).length :=
      length_le_addAll ts (addOne g u)
    have h3 : (addOne g u).length = g.length := by omega
    have h4 : addOne g u = g := addOne_eq_of_length_eq h3
    rw [h4] at h ⊢
    exact ih g h

theorem mem_step_of_mem {g : Graph} {t : Triple} (h : t ∈ g) : t ∈ step g :=
  mem_addAll_of_mem _ g h

theorem mem_step_cases {g : Graph} {t : Triple} (h : t ∈ step g) :
    t ∈ g ∨ t ∈ stepConclusions g :=
  mem_addAll_cases _ g h

theorem mem_step_of_mem_conclusions {g : Graph} {t : Triple}
    (h : t ∈ stepConclusions g) : t ∈ step g :=
  mem_addAll_of_mem_list _ g h

theorem step_eq_of_length_eq {g : Graph} (h : (step g).length = g.length) :
    step g = g :=
  addAll_eq_of_length_eq _ g h

theorem length_le_step (g : Graph) : g.length ≤ (step g).length :=
  length_le_addAll _ g

/-! ## Section 2 — premise lookup, characterised both ways -/

theorem mem_withPred {g : Graph} {p : WfIri} {u : Triple}
    (h : u ∈ withPred g p) : u ∈ g ∧ u.p = p := by
  simp only [withPred, List.mem_filter, beq_iff_eq] at h
  exact h

theorem mem_withPred_of {g : Graph} {p : WfIri} {u : Triple}
    (hg : u ∈ g) (hp : u.p = p) : u ∈ withPred g p := by
  simp only [withPred, List.mem_filter, beq_iff_eq]
  exact ⟨hg, hp⟩

theorem mem_withSubj {g : Graph} {s : Subject} {u : Triple}
    (h : u ∈ withSubj g s) : u ∈ g ∧ u.s = s := by
  simp only [withSubj, List.mem_filter, beq_iff_eq] at h
  exact h

theorem mem_withSubj_of {g : Graph} {s : Subject} {u : Triple}
    (hg : u ∈ g) (hs : u.s = s) : u ∈ withSubj g s := by
  simp only [withSubj, List.mem_filter, beq_iff_eq]
  exact ⟨hg, hs⟩

theorem mem_withObj {g : Graph} {o : Term} {u : Triple}
    (h : u ∈ withObj g o) : u ∈ g ∧ u.o = o := by
  simp only [withObj, List.mem_filter, beq_iff_eq] at h
  exact h

theorem mem_withObj_of {g : Graph} {o : Term} {u : Triple}
    (hg : u ∈ g) (ho : u.o = o) : u ∈ withObj g o := by
  simp only [withObj, List.mem_filter, beq_iff_eq]
  exact ⟨hg, ho⟩

theorem mem_withSubjPred {g : Graph} {s : Subject} {p : WfIri} {u : Triple}
    (h : u ∈ withSubjPred g s p) : u ∈ g ∧ u.s = s ∧ u.p = p := by
  simp only [withSubjPred, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem mem_withSubjPred_of {g : Graph} {s : Subject} {p : WfIri} {u : Triple}
    (hg : u ∈ g) (hs : u.s = s) (hp : u.p = p) : u ∈ withSubjPred g s p := by
  simp only [withSubjPred, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hg, hs, hp⟩

theorem mem_withPredObj {g : Graph} {p : WfIri} {o : Term} {u : Triple}
    (h : u ∈ withPredObj g p o) : u ∈ g ∧ u.p = p ∧ u.o = o := by
  simp only [withPredObj, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem mem_withPredObj_of {g : Graph} {p : WfIri} {o : Term} {u : Triple}
    (hg : u ∈ g) (hp : u.p = p) (ho : u.o = o) : u ∈ withPredObj g p o := by
  simp only [withPredObj, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hg, hp, ho⟩

theorem mem_subjectsOf {g : Graph} {u : Triple} (h : u ∈ g) :
    u.s ∈ subjectsOf g := List.mem_map_of_mem h

theorem mem_asSubject {t : Term} {s : Subject} (h : s ∈ asSubject t) :
    t = s.toTerm := by
  cases t <;> simp [asSubject, Term.toSubject?] at h <;>
    (subst h; rfl)

theorem mem_asSubject_toTerm (s : Subject) : s ∈ asSubject s.toTerm := by
  cases s <;> simp [asSubject, Subject.toTerm, Term.toSubject?]

theorem mem_asIri {t : Term} {i : WfIri} (h : i ∈ asIri t) : t = Term.iri i := by
  cases t <;> simp [asIri] at h <;> (subst h; rfl)

theorem mem_asIri_self (i : WfIri) : i ∈ asIri (Term.iri i) := by
  simp [asIri]

/-! ## Section 3 — rebuilding a triple from the slots a lookup fixed

Every row proof needs the same two moves: turn "this triple is in `g`
and its predicate is P" into a `Derives` premise of the exact shape the
rule constructor wants, or into a graph membership of that shape (for
the clash rows). Structure eta does the work — `⟨u.s, u.p, u.o⟩` IS
`u` — so the lemma is just the rewriting. -/

theorem mem_of_parts {g : Graph} {u : Triple} {s : Subject} {p : WfIri}
    {o : Term} (hg : u ∈ g) (hs : u.s = s) (hp : u.p = p) (ho : u.o = o) :
    (⟨s, p, o⟩ : Triple) ∈ g := by
  subst hs; subst hp; subst ho; exact hg

theorem derives_of_parts {g : Graph} {u : Triple} {s : Subject} {p : WfIri}
    {o : Term} (hg : u ∈ g) (hs : u.s = s) (hp : u.p = p) (ho : u.o = o) :
    Derives g ⟨s, p, o⟩ :=
  Derives.base (mem_of_parts hg hs hp ho)

/-! ## Section 4 — the collection walks are sound

`listElems` finds only real members and `listSeqs` finds only real
denotations. Neither needs a fuel hypothesis in this direction. -/

theorem listElems_sound (g : Graph) : ∀ (n : Nat) (head : Term) {e : Term},
    e ∈ listElems g head n → ListMember g head e := by
  intro n
  induction n with
  | zero => intro head e h; simp [listElems] at h
  | succ n ih =>
    intro head e h
    simp only [listElems, List.mem_flatMap] at h
    obtain ⟨node, hnode, h⟩ := h
    have hhead : head = node.toTerm := mem_asSubject hnode
    subst hhead
    rcases List.mem_append.mp h with h' | h'
    · simp only [List.mem_map] at h'
      obtain ⟨u, hu, rfl⟩ := h'
      obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
      exact ListMember.here (mem_of_parts hug hus hup rfl)
    · simp only [List.mem_flatMap] at h'
      obtain ⟨r, hr, hre⟩ := h'
      obtain ⟨hrg, hrs, hrp⟩ := mem_withSubjPred hr
      exact ListMember.there (mem_of_parts hrg hrs hrp rfl) (ih r.o hre)

theorem listSeqs_sound (g : Graph) : ∀ (n : Nat) (head : Term) {es : List Term},
    es ∈ listSeqs g head n → ListDenotes g head es := by
  intro n
  induction n with
  | zero => intro head es h; simp [listSeqs] at h
  | succ n ih =>
    intro head es h
    rw [listSeqs] at h
    split at h
    · rename_i hnil
      have hh : head = Term.iri rdfNil := by simpa using hnil
      subst hh
      have : es = [] := by simpa using h
      subst this
      exact ListDenotes.nil
    · simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨node, hnode, f, hf, r, hr, rest, hrest, rfl⟩ := h
      have hhead : head = node.toTerm := mem_asSubject hnode
      subst hhead
      obtain ⟨hfg, hfs, hfp⟩ := mem_withSubjPred hf
      obtain ⟨hrg, hrs, hrp⟩ := mem_withSubjPred hr
      exact ListDenotes.cons (mem_of_parts hfg hfs hfp rfl)
        (mem_of_parts hrg hrs hrp rfl) (ih r.o hrest)

theorem typesAllB_sound {g : Graph} {y : Subject} : ∀ {cs : List Term},
    typesAllB g y cs = true → TypesAll g y cs := by
  intro cs
  induction cs with
  | nil => intro _; exact TypesAll.nil
  | cons c cs ih =>
    intro h
    simp only [typesAllB, List.all_cons, Bool.and_eq_true] at h
    exact TypesAll.cons (mem_of_memB h.1) (ih h.2)

theorem sharesKeyValuesB_sound {g : Graph} {x y : Subject} :
    ∀ {ps : List WfIri},
      sharesKeyValuesB g x y ps = true → SharesKeyValues g x y ps := by
  intro ps
  induction ps with
  | nil => intro _; exact SharesKeyValues.nil
  | cons p ps ih =>
    intro h
    simp only [sharesKeyValuesB, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    simp only [List.any_eq_true] at hhead
    obtain ⟨ux, hux, hmem⟩ := hhead
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hux
    exact SharesKeyValues.cons (mem_of_parts hug hus hup rfl)
      (mem_of_memB hmem) (ih htail)

theorem chainTargets_sound (g : Graph) : ∀ (ps : List WfIri) (start : Subject)
    {fin : Term}, fin ∈ chainTargets g start ps → ChainHolds g start ps fin := by
  intro ps
  induction ps with
  | nil =>
    intro start fin h
    simp only [chainTargets, List.mem_singleton] at h
    subst h; exact ChainHolds.nil
  | cons p rest ih =>
    intro start fin h
    match rest with
    | [] =>
      simp only [chainTargets, List.mem_map] at h
      obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
      exact ChainHolds.last (mem_of_parts hug hus hup rfl)
    | q :: rest' =>
      simp only [chainTargets, List.mem_flatMap] at h
      obtain ⟨u, hu, mid, hmid, h⟩ := h
      obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
      have hmo : u.o = mid.toTerm := mem_asSubject hmid
      exact ChainHolds.step (mem_of_parts hug hus hup hmo) (ih mid h)

theorem allIris_sound : ∀ {ts : List Term} {ps : List WfIri},
    ps ∈ allIris ts → ts = ps.map Term.iri := by
  intro ts
  induction ts with
  | nil => intro ps h; simp [allIris] at h; subst h; rfl
  | cons t ts ih =>
    intro ps h
    cases t with
    | iri i =>
      simp only [allIris, List.mem_map] at h
      obtain ⟨l, hl, rfl⟩ := h
      simp [ih hl]
    | bnode _ => simp [allIris] at h
    | literal _ => simp [allIris] at h
    | tripleTerm _ _ _ => simp [allIris] at h

theorem mem_subjIri {s : Subject} {i : WfIri} (h : i ∈ subjIri s) :
    s = Subject.iri i := by
  cases s <;> simp [subjIri] at h <;> (subst h; rfl)

theorem mem_subjIri_self (i : WfIri) : i ∈ subjIri (Subject.iri i) := by
  simp [subjIri]

theorem mem_nonEmpty {a : Type} {ls : List (List a)} {l : List a}
    (h : l ∈ nonEmpty ls) : l ∈ ls ∧ l ≠ [] := by
  simp only [nonEmpty, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨h.1, ?_⟩
  intro hn
  subst hn
  simp at h

/-! ## Section 5 — one lemma per row: what the row emits is derivable

47 lemmas, one per row function of `RLClosure`, each of the shape "if
the driving triple is in `g` and `t` is emitted, then `Derives g t`".
This is the whole content of T2 and the whole content of the LICENSING
program `docs/theorem-registry.md` §1 tracks per row; everything after
is bookkeeping. -/

-- --- Table 4, equality ------------------------------------------------

/-- **eq-ref**, subject conclusion. -/
theorem eqRefSFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqRefSFor g d) : Derives g t := by
  simp only [eqRefSFor, List.mem_singleton] at h
  subst h
  exact Derives.eqRefS (derives_of_parts hd rfl rfl rfl)

/-- **eq-ref**, predicate conclusion. -/
theorem eqRefPFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqRefPFor g d) : Derives g t := by
  simp only [eqRefPFor, List.mem_singleton] at h
  subst h
  exact Derives.eqRefP (derives_of_parts hd rfl rfl rfl)

/-- **eq-ref**, object conclusion. -/
theorem eqRefOFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqRefOFor g d) : Derives g t := by
  simp only [eqRefOFor, List.mem_map] at h
  obtain ⟨os, hos, rfl⟩ := h
  exact Derives.eqRefO (derives_of_parts hd rfl rfl (mem_asSubject hos))

/-- **eq-sym**. -/
theorem eqSymFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqSymFor g d) : Derives g t := by
  unfold eqSymFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨ys, hys, rfl⟩ := h
    exact Derives.eqSym (derives_of_parts hd rfl hp (mem_asSubject hys))
  · simp at h

/-- **eq-trans**. -/
theorem eqTransFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqTransFor g d) : Derives g t := by
  unfold eqTransFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨ys, hys, u, hu, rfl⟩ := h
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Derives.eqTrans (derives_of_parts hd rfl hp (mem_asSubject hys))
      (derives_of_parts hug hus hup rfl)
  · simp at h

/-- **eq-rep-s**. -/
theorem eqRepSFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqRepSFor g d) : Derives g t := by
  unfold eqRepSFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨s', hs', u, hu, rfl⟩ := h
    obtain ⟨hug, hus⟩ := mem_withSubj hu
    exact Derives.eqRepS (derives_of_parts hd rfl hp (mem_asSubject hs'))
      (derives_of_parts hug hus rfl rfl)
  · simp at h

/-- **eq-rep-p**. -/
theorem eqRepPFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqRepPFor g d) : Derives g t := by
  unfold eqRepPFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, p', hp', u, hu, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.eqRepP
      (derives_of_parts hd (mem_subjIri hpi) hp (mem_asIri hp'))
      (derives_of_parts hug rfl hup rfl)
  · simp at h

/-- **eq-rep-o**. -/
theorem eqRepOFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqRepOFor g d) : Derives g t := by
  unfold eqRepOFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hug, huo⟩ := mem_withObj hu
    exact Derives.eqRepO (derives_of_parts hd rfl hp rfl)
      (derives_of_parts hug rfl rfl huo)
  · simp at h

-- --- Table 4, property axioms ----------------------------------------

/-- **prp-dom**. -/
theorem prpDomFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpDomFor g d) : Derives g t := by
  unfold prpDomFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, u, hu, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpDom (derives_of_parts hd (mem_subjIri hpi) hp rfl)
      (derives_of_parts hug rfl hup rfl)
  · simp at h

/-- **prp-rng**. -/
theorem prpRngFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpRngFor g d) : Derives g t := by
  unfold prpRngFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, u, hu, ys, hys, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpRng (derives_of_parts hd (mem_subjIri hpi) hp rfl)
      (derives_of_parts hug rfl hup (mem_asSubject hys))
  · simp at h

/-- **prp-fp**. -/
theorem prpFpFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpFpFor g d) : Derives g t := by
  unfold prpFpFor at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, u1, hu1, y1s, hy1, u2, hu2, rfl⟩ := h
    obtain ⟨hu1g, hu1p⟩ := mem_withPred hu1
    obtain ⟨hu2g, hu2s, hu2p⟩ := mem_withSubjPred hu2
    exact Derives.prpFp (derives_of_parts hd (mem_subjIri hpi) hp1 hp2)
      (derives_of_parts hu1g rfl hu1p (mem_asSubject hy1))
      (derives_of_parts hu2g hu2s hu2p rfl)
  · simp at h

/-- **prp-ifp**. -/
theorem prpIfpFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpIfpFor g d) : Derives g t := by
  unfold prpIfpFor at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, u1, hu1, u2, hu2, rfl⟩ := h
    obtain ⟨hu1g, hu1p⟩ := mem_withPred hu1
    obtain ⟨hu2g, hu2p, hu2o⟩ := mem_withPredObj hu2
    exact Derives.prpIfp (derives_of_parts hd (mem_subjIri hpi) hp1 hp2)
      (derives_of_parts hu1g rfl hu1p rfl)
      (derives_of_parts hu2g rfl hu2p hu2o)
  · simp at h

/-- **prp-symp**. -/
theorem prpSympFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpSympFor g d) : Derives g t := by
  unfold prpSympFor at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, u, hu, ys, hys, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpSymp (derives_of_parts hd (mem_subjIri hpi) hp1 hp2)
      (derives_of_parts hug rfl hup (mem_asSubject hys))
  · simp at h

/-- **prp-trp**. -/
theorem prpTrpFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpTrpFor g d) : Derives g t := by
  unfold prpTrpFor at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, u1, hu1, ys, hys, u2, hu2, rfl⟩ := h
    obtain ⟨hu1g, hu1p⟩ := mem_withPred hu1
    obtain ⟨hu2g, hu2s, hu2p⟩ := mem_withSubjPred hu2
    exact Derives.prpTrp (derives_of_parts hd (mem_subjIri hpi) hp1 hp2)
      (derives_of_parts hu1g rfl hu1p (mem_asSubject hys))
      (derives_of_parts hu2g hu2s hu2p rfl)
  · simp at h

/-- **prp-spo1**. -/
theorem prpSpo1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpSpo1For g d) : Derives g t := by
  unfold prpSpo1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hu, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpSpo1
      (derives_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i))
      (derives_of_parts hug rfl hup rfl)
  · simp at h

/-- **prp-spo2** — the property-chain row. -/
theorem prpSpo2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpSpo2For g d) : Derives g t := by
  unfold prpSpo2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, terms, hterms, preds, hpreds, x1, _hx1, xn, hxn, rfl⟩ := h
    obtain ⟨hpm, hpne⟩ := mem_nonEmpty hpreds
    refine Derives.prpSpo2 (derives_of_parts hd (mem_subjIri hpi) hp rfl)
      ?_ hpne (chainTargets_sound g preds x1 hxn)
    rw [← allIris_sound hpm]
    exact listSeqs_sound g (listFuel g) d.o hterms
  · simp at h

/-- **prp-eqp1**. -/
theorem prpEqp1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpEqp1For g d) : Derives g t := by
  unfold prpEqp1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hu, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpEqp1
      (derives_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i))
      (derives_of_parts hug rfl hup rfl)
  · simp at h

/-- **prp-eqp2**. -/
theorem prpEqp2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpEqp2For g d) : Derives g t := by
  unfold prpEqp2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hu, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpEqp2
      (derives_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i))
      (derives_of_parts hug rfl hup rfl)
  · simp at h

/-- **prp-inv1**. -/
theorem prpInv1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpInv1For g d) : Derives g t := by
  unfold prpInv1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hu, ys, hys, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpInv1
      (derives_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i))
      (derives_of_parts hug rfl hup (mem_asSubject hys))
  · simp at h

/-- **prp-inv2**. -/
theorem prpInv2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpInv2For g d) : Derives g t := by
  unfold prpInv2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hu, ys, hys, rfl⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.prpInv2
      (derives_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i))
      (derives_of_parts hug rfl hup (mem_asSubject hys))
  · simp at h

/-- **prp-key**. -/
theorem prpKeyFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpKeyFor g d) : Derives g t := by
  unfold prpKeyFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨terms, hterms, preds, hpreds, tx, htx, ty, hty, h⟩ := h
    obtain ⟨hpm, hpne⟩ := mem_nonEmpty hpreds
    split at h
    · rename_i hsh
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨htxg, htxp, htxo⟩ := mem_withPredObj htx
      obtain ⟨htyg, htyp, htyo⟩ := mem_withPredObj hty
      refine Derives.prpKey (derives_of_parts hd rfl hp rfl) ?_ hpne
        (derives_of_parts htxg rfl htxp htxo)
        (derives_of_parts htyg rfl htyp htyo)
        (sharesKeyValuesB_sound hsh)
      rw [← allIris_sound hpm]
      exact listSeqs_sound g (listFuel g) d.o hterms
    · simp at h
  · simp at h


-- --- Table 5, classes -------------------------------------------------

/-- **cls-int1**. -/
theorem clsInt1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsInt1For g d) : Derives g t := by
  unfold clsInt1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨cs, hcs, y, _hy, h⟩ := h
    obtain ⟨hcsm, hcsne⟩ := mem_nonEmpty hcs
    split at h
    · rename_i hta
      simp only [List.mem_singleton] at h
      subst h
      exact Derives.clsInt1 (derives_of_parts hd rfl hp rfl)
        (listSeqs_sound g (listFuel g) d.o hcsm) hcsne (typesAllB_sound hta)
    · simp at h
  · simp at h

/-- **cls-int2**. -/
theorem clsInt2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsInt2For g d) : Derives g t := by
  unfold clsInt2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨ci, hci, u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.clsInt2 (derives_of_parts hd rfl hp rfl)
      (listElems_sound g (listFuel g) d.o hci)
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **cls-uni**. -/
theorem clsUniFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsUniFor g d) : Derives g t := by
  unfold clsUniFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨ci, hci, u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.clsUni (derives_of_parts hd rfl hp rfl)
      (listElems_sound g (listFuel g) d.o hci)
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **cls-svf1**. -/
theorem clsSvf1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsSvf1For g d) : Derives g t := by
  unfold clsSvf1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨onp, honp, p, hpi, u, hu, vs, hvs, h⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨hug, hup⟩ := mem_withPred hu
    split at h
    · rename_i hmm
      simp only [List.mem_singleton] at h
      subst h
      exact Derives.clsSvf1 (derives_of_parts hd rfl hp rfl)
        (derives_of_parts honpg honps honpp (mem_asIri hpi))
        (derives_of_parts hug rfl hup (mem_asSubject hvs))
        (Derives.base (mem_of_memB hmm))
    · simp at h
  · simp at h

/-- **cls-svf2**. -/
theorem clsSvf2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsSvf2For g d) : Derives g t := by
  unfold clsSvf2For at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨onp, honp, p, hpi, u, hu, rfl⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Derives.clsSvf2 (derives_of_parts hd rfl hp1 hp2)
      (derives_of_parts honpg honps honpp (mem_asIri hpi))
      (derives_of_parts hug rfl hup rfl)
  · simp at h

/-- **cls-avf**. -/
theorem clsAvfFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsAvfFor g d) : Derives g t := by
  unfold clsAvfFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨onp, honp, p, hpi, tu, htu, u, hu, vs, hvs, rfl⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Derives.clsAvf (derives_of_parts hd rfl hp rfl)
      (derives_of_parts honpg honps honpp (mem_asIri hpi))
      (derives_of_parts htug rfl htup htuo)
      (derives_of_parts hug hus hup (mem_asSubject hvs))
  · simp at h

/-- **cls-hv1**. -/
theorem clsHv1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsHv1For g d) : Derives g t := by
  unfold clsHv1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨onp, honp, p, hpi, tu, htu, rfl⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    exact Derives.clsHv1 (derives_of_parts hd rfl hp rfl)
      (derives_of_parts honpg honps honpp (mem_asIri hpi))
      (derives_of_parts htug rfl htup htuo)
  · simp at h

/-- **cls-hv2**. -/
theorem clsHv2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsHv2For g d) : Derives g t := by
  unfold clsHv2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨onp, honp, p, hpi, u, hu, rfl⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.clsHv2 (derives_of_parts hd rfl hp rfl)
      (derives_of_parts honpg honps honpp (mem_asIri hpi))
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **cls-maxc2**. -/
theorem clsMaxc2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsMaxc2For g d) : Derives g t := by
  unfold clsMaxc2For at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨onp, honp, p, hpi, tu, htu, u1, hu1, y1s, hy1, u2, hu2, rfl⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    obtain ⟨hu1g, hu1s, hu1p⟩ := mem_withSubjPred hu1
    obtain ⟨hu2g, hu2s, hu2p⟩ := mem_withSubjPred hu2
    exact Derives.clsMaxc2 (derives_of_parts hd rfl hp1 hp2)
      (derives_of_parts honpg honps honpp (mem_asIri hpi))
      (derives_of_parts htug rfl htup htuo)
      (derives_of_parts hu1g hu1s hu1p (mem_asSubject hy1))
      (derives_of_parts hu2g hu2s hu2p rfl)
  · simp at h

/-- **cls-oo**. -/
theorem clsOoFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsOoFor g d) : Derives g t := by
  unfold clsOoFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨yi, hyi, yis, hyis, rfl⟩ := h
    have hy : yi = yis.toTerm := mem_asSubject hyis
    subst hy
    exact Derives.clsOo (derives_of_parts hd rfl hp rfl)
      (listElems_sound g (listFuel g) d.o hyi)
  · simp at h

-- --- Table 6, class axioms -------------------------------------------

/-- **cax-sco**. -/
theorem caxScoFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ caxScoFor g d) : Derives g t := by
  unfold caxScoFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.caxSco (derives_of_parts hd rfl hp rfl)
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **cax-eqc1**. -/
theorem caxEqc1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ caxEqc1For g d) : Derives g t := by
  unfold caxEqc1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.caxEqc1 (derives_of_parts hd rfl hp rfl)
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **cax-eqc2**. -/
theorem caxEqc2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ caxEqc2For g d) : Derives g t := by
  unfold caxEqc2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.caxEqc2 (derives_of_parts hd rfl hp rfl)
      (derives_of_parts hug rfl hup huo)
  · simp at h

-- --- Table 8, schema vocabulary --------------------------------------

/-- **scm-cls** — all four conclusions. -/
theorem scmClsFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmClsFor g d) : Derives g t := by
  unfold scmClsFor at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hbase : Derives g ⟨d.s, rdfType, Term.iri owlClass⟩ :=
      derives_of_parts hd rfl hp1 hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact Derives.scmClsSelf hbase
    · exact Derives.scmClsEqc hbase
    · exact Derives.scmClsThing hbase
    · exact Derives.scmClsNothing hbase
  · simp at h

/-- **scm-sco**. -/
theorem scmScoFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmScoFor g d) : Derives g t := by
  unfold scmScoFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨c2s, hc2s, u, hu, rfl⟩ := h
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Derives.scmSco (derives_of_parts hd rfl hp (mem_asSubject hc2s))
      (derives_of_parts hug hus hup rfl)
  · simp at h

/-- **scm-eqc1** — both conclusions. -/
theorem scmEqc1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmEqc1For g d) : Derives g t := by
  unfold scmEqc1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · exact Derives.scmEqc1a (derives_of_parts hd rfl hp rfl)
    · simp only [List.mem_map] at h
      obtain ⟨c2s, hc2s, rfl⟩ := h
      exact Derives.scmEqc1b (derives_of_parts hd rfl hp (mem_asSubject hc2s))
  · simp at h

/-- **scm-eqc2**. -/
theorem scmEqc2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmEqc2For g d) : Derives g t := by
  unfold scmEqc2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨c2s, hc2s, h⟩ := h
    split at h
    · rename_i hmm
      simp only [List.mem_singleton] at h
      subst h
      have hdo : d.o = c2s.toTerm := mem_asSubject hc2s
      rw [hdo]
      exact Derives.scmEqc2 (derives_of_parts hd rfl hp hdo)
        (Derives.base (mem_of_memB hmm))
    · simp at h
  · simp at h

/-- **scm-spo**. -/
theorem scmSpoFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmSpoFor g d) : Derives g t := by
  unfold scmSpoFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p2s, hp2s, u, hu, rfl⟩ := h
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Derives.scmSpo (derives_of_parts hd rfl hp (mem_asSubject hp2s))
      (derives_of_parts hug hus hup rfl)
  · simp at h

/-- **scm-eqp1** — both conclusions. -/
theorem scmEqp1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmEqp1For g d) : Derives g t := by
  unfold scmEqp1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · exact Derives.scmEqp1a (derives_of_parts hd rfl hp rfl)
    · simp only [List.mem_map] at h
      obtain ⟨p2s, hp2s, rfl⟩ := h
      exact Derives.scmEqp1b (derives_of_parts hd rfl hp (mem_asSubject hp2s))
  · simp at h

/-- **scm-eqp2**. -/
theorem scmEqp2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmEqp2For g d) : Derives g t := by
  unfold scmEqp2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨p2s, hp2s, h⟩ := h
    split at h
    · rename_i hmm
      simp only [List.mem_singleton] at h
      subst h
      have hdo : d.o = p2s.toTerm := mem_asSubject hp2s
      rw [hdo]
      exact Derives.scmEqp2 (derives_of_parts hd rfl hp hdo)
        (Derives.base (mem_of_memB hmm))
    · simp at h
  · simp at h

/-- **scm-dom1**. -/
theorem scmDom1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmDom1For g d) : Derives g t := by
  unfold scmDom1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨c1s, hc1s, u, hu, rfl⟩ := h
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Derives.scmDom1 (derives_of_parts hd rfl hp (mem_asSubject hc1s))
      (derives_of_parts hug hus hup rfl)
  · simp at h

/-- **scm-dom2**. -/
theorem scmDom2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmDom2For g d) : Derives g t := by
  unfold scmDom2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.scmDom2 (derives_of_parts hd rfl hp rfl)
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **scm-rng1**. -/
theorem scmRng1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmRng1For g d) : Derives g t := by
  unfold scmRng1For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨c1s, hc1s, u, hu, rfl⟩ := h
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Derives.scmRng1 (derives_of_parts hd rfl hp (mem_asSubject hc1s))
      (derives_of_parts hug hus hup rfl)
  · simp at h

/-- **scm-rng2**. -/
theorem scmRng2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmRng2For g d) : Derives g t := by
  unfold scmRng2For at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Derives.scmRng2 (derives_of_parts hd rfl hp rfl)
      (derives_of_parts hug rfl hup huo)
  · simp at h

/-- **scm-int**. -/
theorem scmIntFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmIntFor g d) : Derives g t := by
  unfold scmIntFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨ci, hci, rfl⟩ := h
    exact Derives.scmInt (derives_of_parts hd rfl hp rfl)
      (listElems_sound g (listFuel g) d.o hci)
  · simp at h

/-- **scm-uni**. -/
theorem scmUniFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ scmUniFor g d) : Derives g t := by
  unfold scmUniFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨ci, hci, cis, hcis, rfl⟩ := h
    have hc : ci = cis.toTerm := mem_asSubject hcis
    subst hc
    exact Derives.scmUni (derives_of_parts hd rfl hp rfl)
      (listElems_sound g (listFuel g) d.o hci)
  · simp at h

end L4Factoidal.OWL
