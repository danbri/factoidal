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
  (`eqSymFor_sound`, `prpTrpFor_sound`, ..., `caxAdcToDwFor_sound`) —
  56 of them, covering the 50 ported table rows and the 14 ported
  `[ext]` rows. Per-row status is therefore uniform: every ported row
  is proved licensed. Read T2 as LICENSING, not as truth preservation
  — see item 1 below, which applies to the `[ext]` rows too: each of
  those carries its OWL 2 RDF-Based Semantics justification in its
  `RLRules.lean` doc comment, and two of them carry a named datatype-map
  assumption on top.

* **T3 monotonicity** — `closure_mono_of_saturated`: derived from T2 +
  `Derives.mono` + T4, hence conditional on the larger graph's closure
  being saturated. The unconditional same-fuel form is not proved and
  is not expected to hold pointwise: two runs stop at different rounds.

* **T4 completeness at the fixpoint** — `closure_complete_of_saturated`:
  `Derives g t → t ∈ closure g fuel`, given that the closure is
  saturated and that the collection-walk fuel was adequate
  (`ListFuelAdequate`, discussed below). All 69 constructor cases.

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

namespace L4Factoidal.OWL.RL

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
    · rename_i hne
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨node, hnode, f, hf, r, hr, rest, hrest, rfl⟩ := h
      have hhead : head = node.toTerm := mem_asSubject hnode
      subst hhead
      obtain ⟨hfg, hfs, hfp⟩ := mem_withSubjPred hf
      obtain ⟨hrg, hrs, hrp⟩ := mem_withSubjPred hr
      exact ListDenotes.cons (by simpa using hne)
        (mem_of_parts hfg hfs hfp rfl)
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
    refine Derives.prpSpo2 (fun _ hu => Derives.base hu)
      (derives_of_parts hd (mem_subjIri hpi) hp rfl)
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
      refine Derives.prpKey (fun _ hu => Derives.base hu)
        (derives_of_parts hd rfl hp rfl) ?_ hpne
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
      exact Derives.clsInt1 (fun _ hu => Derives.base hu)
        (derives_of_parts hd rfl hp rfl)
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
    exact Derives.clsInt2 (fun _ hu => Derives.base hu)
      (derives_of_parts hd rfl hp rfl)
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
    exact Derives.clsUni (fun _ hu => Derives.base hu)
      (derives_of_parts hd rfl hp rfl)
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

/-- **cls-hs1**. -/
theorem clsHs1For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsHs1For g d) : Derives g t := by
  unfold clsHs1For at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨onp, honp, p, hpi, tu, htu, rfl⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    exact Derives.clsHs1 (derives_of_parts hd rfl hp.1 hp.2)
      (derives_of_parts honpg honps honpp (mem_asIri hpi))
      (derives_of_parts htug rfl htup htuo)
  · simp at h

/-- **cls-hs2**. -/
theorem clsHs2For_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsHs2For g d) : Derives g t := by
  unfold clsHs2For at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨onp, honp, p, hpi, u, hu, hmem⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨hug, hup⟩ := mem_withPred hu
    split at hmem
    · rename_i hself
      rw [beq_iff_eq] at hself
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact Derives.clsHs2 (derives_of_parts hd rfl hp.1 hp.2)
        (derives_of_parts honpg honps honpp (mem_asIri hpi))
        (derives_of_parts hug rfl hup hself)
    · simp at hmem
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
    exact Derives.clsOo (fun _ hu => Derives.base hu)
      (derives_of_parts hd rfl hp rfl)
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
    exact Derives.scmInt (fun _ hu => Derives.base hu)
      (derives_of_parts hd rfl hp rfl)
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
    exact Derives.scmUni (fun _ hu => Derives.base hu)
      (derives_of_parts hd rfl hp rfl)
      (listElems_sound g (listFuel g) d.o hci)
  · simp at h


-- --- The `[ext]` rows -------------------------------------------------
--
-- Same shape as every lemma above: the row's output is licensed by the
-- matching `Derives` constructor. What these lemmas do NOT say is that
-- the constructor preserves truth — that is the model-theoretic claim
-- the module header disclaims for the whole file, and each `[ext]`
-- constructor carries its RDF-Based-Semantics argument in its own doc
-- comment instead.

/-- **eq-diff-sym** `[ext]`. -/
theorem eqDiffSymFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ eqDiffSymFor g d) : Derives g t := by
  unfold eqDiffSymFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_map] at h
    obtain ⟨ys, hys, rfl⟩ := h
    exact Derives.eqDiffSym (derives_of_parts hd rfl hp (mem_asSubject hys))
  · simp at h

/-- **prp-pdw-diff** `[ext]`. -/
theorem pdwToDiffFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ pdwToDiffFor g d) : Derives g t := by
  unfold pdwToDiffFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨p1, hp1, p2, hp2, t1, ht1, o1s, ho1s, t2, ht2, h⟩ := h
    obtain ⟨ht1g, ht1p⟩ := mem_withPred ht1
    obtain ⟨ht2g, ht2s, ht2p⟩ := mem_withSubjPred ht2
    split at h
    · simp at h
    · rename_i hne
      simp only [List.mem_singleton] at h
      subst h
      refine Derives.pdwToDiff
        (derives_of_parts hd (mem_subjIri hp1) hp (mem_asIri hp2))
        (derives_of_parts ht1g rfl ht1p (mem_asSubject ho1s))
        (derives_of_parts ht2g ht2s ht2p rfl) ?_
      simpa using hne
  · simp at h

/-- **cax-dw-diff** `[ext]`. -/
theorem caxDwToDiffFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ caxDwToDiffFor g d) : Derives g t := by
  unfold caxDwToDiffFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨c1, hc1, c2, hc2, tx, htx, ty, hty, h⟩ := h
    obtain ⟨htxg, htxp, htxo⟩ := mem_withPredObj htx
    obtain ⟨htyg, htyp, htyo⟩ := mem_withPredObj hty
    split at h
    · simp at h
    · rename_i hne
      simp only [List.mem_singleton] at h
      subst h
      refine Derives.caxDwToDiff
        (derives_of_parts hd (mem_subjIri hc1) hp (mem_asIri hc2))
        (derives_of_parts htxg rfl htxp htxo)
        (derives_of_parts htyg rfl htyp htyo) ?_
      simpa using hne
  · simp at h

/-- **prp-fp-diff** `[ext]`. -/
theorem fpDiffToDiffFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ fpDiffToDiffFor g d) : Derives g t := by
  unfold fpDiffToDiffFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨t1, ht1, h⟩ := h
    obtain ⟨ht1g, ht1o⟩ := mem_withObj ht1
    split at h
    · rename_i hfp
      simp only [List.mem_flatMap] at h
      obtain ⟨t2, ht2, h⟩ := h
      obtain ⟨ht2g, ht2p, ht2o⟩ := mem_withPredObj ht2
      split at h
      · simp at h
      · rename_i hne
        simp only [List.mem_singleton] at h
        subst h
        refine Derives.fpDiffToDiff (Derives.base (mem_of_memB hfp))
          (derives_of_parts ht1g rfl rfl ht1o)
          (derives_of_parts ht2g rfl ht2p ht2o)
          (derives_of_parts hd rfl hp rfl) ?_
        simpa using hne
    · simp at h
  · simp at h

/-- **prp-ifp-diff** `[ext]`. -/
theorem ifpDiffToDiffFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ ifpDiffToDiffFor g d) : Derives g t := by
  unfold ifpDiffToDiffFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨t1, ht1, h⟩ := h
    obtain ⟨ht1g, ht1s⟩ := mem_withSubj ht1
    split at h
    · rename_i hifp
      simp only [List.mem_flatMap] at h
      obtain ⟨y1s, hy1s, x2s, hx2s, t2, ht2, h⟩ := h
      obtain ⟨ht2g, ht2s, ht2p⟩ := mem_withSubjPred ht2
      split at h
      · simp at h
      · rename_i hne
        simp only [List.mem_singleton] at h
        subst h
        refine Derives.ifpDiffToDiff (Derives.base (mem_of_memB hifp))
          (derives_of_parts ht1g ht1s rfl (mem_asSubject hy1s))
          (derives_of_parts ht2g ht2s ht2p rfl)
          (derives_of_parts hd rfl hp (mem_asSubject hx2s)) ?_
        simpa using hne
    · simp at h
  · simp at h

/-- **scm-trans-from-chain** `[ext]`. -/
theorem chainToTransFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ chainToTransFor g d) : Derives g t := by
  unfold chainToTransFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨p, hpi, terms, hterms, h⟩ := h
    split at h
    · rename_i heq
      simp only [List.mem_singleton] at h
      subst h
      have hterms' : terms = [Term.iri p, Term.iri p] := by simpa using heq
      subst hterms'
      exact Derives.chainToTrans (fun _ hu => Derives.base hu)
        (derives_of_parts hd (mem_subjIri hpi) hp rfl)
        (listSeqs_sound g (listFuel g) d.o hterms)
    · simp at h
  · simp at h

/-- **prp-rfl** `[ext]`. -/
theorem prpRflFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ prpRflFor g d) : Derives g t := by
  unfold prpRflFor at h
  split at h
  · rename_i hpo
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpo
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hpi, i, hi, rfl⟩ := h
    exact Derives.prpRfl (fun _ hu => Derives.base hu)
      (derives_of_parts hd (mem_subjIri hpi) hpo.1 hpo.2) hi
  · simp at h

/-- **xsd-axioms** `[ext]`. -/
theorem xsdAxiomsFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ xsdAxiomsFor g d) : Derives g t := by
  unfold xsdAxiomsFor at h
  split at h
  · rename_i hx
    exact Derives.xsdAxioms (Derives.base hd) hx h
  · simp at h

/-- **dt-rng-intersect** `[ext]`. -/
theorem dtRangeIntersectFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ dtRangeIntersectFor g d) : Derives g t := by
  unfold dtRangeIntersectFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨d1, hd1, t2, ht2, d2, hd2, e, he, h⟩ := h
    obtain ⟨ht2g, ht2s, ht2p⟩ := mem_withSubjPred ht2
    split at h
    · rename_i hmatch
      simp only [List.mem_map] at h
      obtain ⟨d3, hd3, rfl⟩ := h
      refine Derives.dtRangeIntersect
        (derives_of_parts hd rfl hp (mem_asIri hd1))
        (derives_of_parts ht2g ht2s ht2p (mem_asIri hd2)) ?_
      simp only [rangeIntersectLicenses, List.any_eq_true, Bool.and_eq_true]
      refine ⟨e, he, hmatch, ?_⟩
      simpa [List.contains_iff_mem] using hd3
    · simp at h
  · simp at h

/-- **cax-dw-comp** `[ext]`. -/
theorem caxDwToComplementFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ caxDwToComplementFor g d) : Derives g t := by
  unfold caxDwToComplementFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨c1, hc1, c2, hc2, hax⟩ := h
    exact Derives.caxDwToComplement
      (derives_of_parts hd (mem_subjIri hc1) hp (mem_asIri hc2)) hax
  · simp at h

/-- **cls-maxqc1-comp** `[ext]`. -/
theorem clsMaxqc1ToComplementFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ clsMaxqc1ToComplementFor g d) : Derives g t := by
  unfold clsMaxqc1ToComplementFor at h
  split at h
  · rename_i hpo
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpo
    simp only [List.mem_flatMap] at h
    obtain ⟨onp, honp, p, hp, onc, honc, c, hc, tu, htu, u1, hu1,
      y1s, hy1s, h⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨honcg, honcs, honcp⟩ := mem_withSubjPred honc
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    obtain ⟨hu1g, hu1s, hu1p⟩ := mem_withSubjPred hu1
    split at h
    · rename_i hy1c
      simp only [List.mem_flatMap] at h
      obtain ⟨df, hdf, y2s, hy2s, h⟩ := h
      obtain ⟨hdfg, hdfs, hdfp⟩ := mem_withSubjPred hdf
      split at h
      · rename_i hu2
        exact Derives.clsMaxqc1ToComplement
          (derives_of_parts hd rfl hpo.1 hpo.2)
          (derives_of_parts honpg honps honpp (mem_asIri hp))
          (derives_of_parts honcg honcs honcp (mem_asIri hc))
          (derives_of_parts htug rfl htup htuo)
          (derives_of_parts hu1g hu1s hu1p (mem_asSubject hy1s))
          (Derives.base (mem_of_memB hu2))
          (Derives.base (mem_of_memB hy1c))
          (derives_of_parts hdfg hdfs hdfp (mem_asSubject hy2s)) h
      · simp at h
    · simp at h
  · simp at h

/-- **minc1-comp** `[ext]`. -/
theorem minCard1ComprehensionFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ minCard1ComprehensionFor g d) : Derives g t := by
  unfold minCard1ComprehensionFor at h
  split at h
  · rename_i hpo
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpo
    simp only [List.mem_flatMap] at h
    obtain ⟨p, hp, hax⟩ := h
    exact Derives.minCard1Comprehension
      (derives_of_parts hd (mem_subjIri hp) hpo.1 hpo.2) hax
  · simp at h

/-- **cax-adc-dw** `[ext]`. -/
theorem caxAdcToDwFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ caxAdcToDwFor g d) : Derives g t := by
  unfold caxAdcToDwFor at h
  split at h
  · rename_i hpo
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpo
    simp only [List.mem_flatMap] at h
    obtain ⟨mem, hmem, ci, hci, ci', hci', cj, hcj, cj', hcj', h⟩ := h
    obtain ⟨hmemg, hmems, hmemp⟩ := mem_withSubjPred hmem
    split at h
    · simp at h
    · rename_i hne
      simp only [List.mem_singleton] at h
      subst h
      have hci2 : ci = Term.iri ci' := mem_asIri hci'
      have hcj2 : cj = Term.iri cj' := mem_asIri hcj'
      subst hci2; subst hcj2
      refine Derives.caxAdcToDw (fun _ hu => Derives.base hu)
        (derives_of_parts hd rfl hpo.1 hpo.2)
        (derives_of_parts hmemg hmems hmemp rfl)
        (listElems_sound g (listFuel g) mem.o hci)
        (listElems_sound g (listFuel g) mem.o hcj) ?_
      simpa [Subtype.ext_iff] using hne
  · simp at h

/-- **inv-flip** `[ext]`. -/
theorem inverseOfDomRngFlipFor_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ inverseOfDomRngFlipFor g d) : Derives g t := by
  unfold inverseOfDomRngFlipFor at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.mem_flatMap] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hug, hmem⟩ := h
    have hdinv : Derives g ⟨Subject.iri p1, owlInverseOf, Term.iri p2⟩ :=
      derives_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i)
    rcases u with ⟨us, up, uo⟩
    cases us with
    | iri srcP =>
      cases uo with
      | iri c =>
        simp only at hmem
        split at hmem
        · rename_i hcond
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
          obtain ⟨rfl, rfl⟩ := hcond
          simp only [List.mem_singleton] at hmem; subst hmem
          exact Derives.invFlipDomRng hdinv (Derives.base hug)
        · split at hmem
          · rename_i hcond
            rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
            obtain ⟨rfl, rfl⟩ := hcond
            simp only [List.mem_singleton] at hmem; subst hmem
            exact Derives.invFlipRngDom hdinv (Derives.base hug)
          · split at hmem
            · rename_i hcond
              rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
              obtain ⟨rfl, rfl⟩ := hcond
              simp only [List.mem_singleton] at hmem; subst hmem
              exact Derives.invFlipDomRngRev hdinv (Derives.base hug)
            · split at hmem
              · rename_i hcond
                rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcond
                obtain ⟨rfl, rfl⟩ := hcond
                simp only [List.mem_singleton] at hmem; subst hmem
                exact Derives.invFlipRngDomRev hdinv (Derives.base hug)
              · simp at hmem
      | _ => simp at hmem
    | _ => cases uo <;> simp at hmem
  · simp at h

/-! ## Section 6 — T2, soundness of a round and of the whole closure -/

/-- Every conclusion the ported rows emit from one driving triple is
derivable. The 47-way case split is over `conclusionsList`, in the
order that list is written. -/
theorem conclusionsFrom_sound {g : Graph} {d t : Triple} (hd : d ∈ g)
    (h : t ∈ conclusionsFrom g d) : Derives g t := by
  simp only [conclusionsFrom, List.mem_flatten, conclusionsList,
    List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨l, hl, ht⟩ := h
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact eqRefSFor_sound hd ht
  · exact eqRefPFor_sound hd ht
  · exact eqRefOFor_sound hd ht
  · exact eqSymFor_sound hd ht
  · exact eqTransFor_sound hd ht
  · exact eqRepSFor_sound hd ht
  · exact eqRepPFor_sound hd ht
  · exact eqRepOFor_sound hd ht
  · exact prpDomFor_sound hd ht
  · exact prpRngFor_sound hd ht
  · exact prpFpFor_sound hd ht
  · exact prpIfpFor_sound hd ht
  · exact prpSympFor_sound hd ht
  · exact prpTrpFor_sound hd ht
  · exact prpSpo1For_sound hd ht
  · exact prpSpo2For_sound hd ht
  · exact prpEqp1For_sound hd ht
  · exact prpEqp2For_sound hd ht
  · exact prpInv1For_sound hd ht
  · exact prpInv2For_sound hd ht
  · exact prpKeyFor_sound hd ht
  · exact clsInt1For_sound hd ht
  · exact clsInt2For_sound hd ht
  · exact clsUniFor_sound hd ht
  · exact clsSvf1For_sound hd ht
  · exact clsSvf2For_sound hd ht
  · exact clsAvfFor_sound hd ht
  · exact clsHv1For_sound hd ht
  · exact clsHv2For_sound hd ht
  · exact clsHs1For_sound hd ht
  · exact clsHs2For_sound hd ht
  · exact clsMaxc2For_sound hd ht
  · exact clsOoFor_sound hd ht
  · exact caxScoFor_sound hd ht
  · exact caxEqc1For_sound hd ht
  · exact caxEqc2For_sound hd ht
  · exact scmClsFor_sound hd ht
  · exact scmScoFor_sound hd ht
  · exact scmEqc1For_sound hd ht
  · exact scmEqc2For_sound hd ht
  · exact scmSpoFor_sound hd ht
  · exact scmEqp1For_sound hd ht
  · exact scmEqp2For_sound hd ht
  · exact scmDom1For_sound hd ht
  · exact scmDom2For_sound hd ht
  · exact scmRng1For_sound hd ht
  · exact scmRng2For_sound hd ht
  · exact scmIntFor_sound hd ht
  · exact scmUniFor_sound hd ht
  · exact eqDiffSymFor_sound hd ht
  · exact pdwToDiffFor_sound hd ht
  · exact caxDwToDiffFor_sound hd ht
  · exact fpDiffToDiffFor_sound hd ht
  · exact ifpDiffToDiffFor_sound hd ht
  · exact chainToTransFor_sound hd ht
  · exact prpRflFor_sound hd ht
  · exact xsdAxiomsFor_sound hd ht
  · exact dtRangeIntersectFor_sound hd ht
  · exact caxDwToComplementFor_sound hd ht
  · exact clsMaxqc1ToComplementFor_sound hd ht
  · exact minCard1ComprehensionFor_sound hd ht
  · exact caxAdcToDwFor_sound hd ht
  · exact inverseOfDomRngFlipFor_sound hd ht

/-- **cls-thing** and **cls-nothing1** are premise-free rows, and so is
the `dtType1Builtin` `[ext]` row, so the axiom triples are derivable
from any graph. -/
theorem axiomTriples_sound {g : Graph} {t : Triple} (h : t ∈ axiomTriples) :
    Derives g t := by
  simp only [axiomTriples, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | h'
  · exact Derives.clsThing
  · exact Derives.clsNothing1
  · exact Derives.dtType1Builtin h'

/-- Every conclusion a round emits is derivable from the round's
input. -/
theorem stepConclusions_sound {g : Graph} {t : Triple}
    (h : t ∈ stepConclusions g) : Derives g t := by
  simp only [stepConclusions, List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨d, hd, ht⟩
  · exact axiomTriples_sound h
  · exact conclusionsFrom_sound hd ht

/-- Every triple a round produces is derivable from the round's
input. -/
theorem step_sound {g : Graph} {t : Triple} (h : t ∈ step g) :
    Derives g t := by
  rcases mem_step_cases h with h' | h'
  · exact Derives.base h'
  · exact stepConclusions_sound h'

/-! ## Section 7 — T1, extensivity -/

/-- **T1.** The closure contains the input graph, at any fuel. -/
theorem closure_extensive (fuel : Nat) :
    ∀ (g : Graph) {t : Triple}, t ∈ g → t ∈ closure g fuel := by
  induction fuel with
  | zero => intro g t h; exact h
  | succ n ih =>
    intro g t h
    simp only [closure]
    split
    · exact h
    · exact ih (step g) (mem_step_of_mem h)

/-- **T2.** Every triple of the computed closure has a derivation in
the OWL 2 RL/RDF rule relation. This is the LICENSING statement of
`OWL.RL.Refinement.fst`, assembled from the 47 per-row lemmas above.

Chaining the rounds is `Derives.cut`, which needs no side condition
because the collection-valued rows carry their own derivable-collection
graph (see `RLRules.Derives.cut`'s comment for why reading `g`
directly would make cut false here). -/
theorem closure_sound (fuel : Nat) :
    ∀ (g : Graph) {t : Triple}, t ∈ closure g fuel → Derives g t := by
  induction fuel with
  | zero => intro g t h; exact Derives.base h
  | succ n ih =>
    intro g t h
    simp only [closure] at h
    split at h
    · exact Derives.base h
    · exact Derives.cut (fun _ hu => step_sound hu) (ih (step g) h)

/-! ## Section 8 — the fuel dichotomy -/

/-- **The fuel dichotomy.** For every graph and every fuel: either the
closure is saturated (one more round changes nothing), or the closure
grew by at least one triple per unit of fuel spent. This is what turns
`closure_complete_of_saturated`'s hypothesis into "provided the fuel
was not exhausted". -/
theorem closure_saturated_or_underfueled (fuel : Nat) :
    ∀ (g : Graph), step (closure g fuel) = closure g fuel ∨
      g.length + fuel ≤ (closure g fuel).length := by
  induction fuel with
  | zero => intro g; exact Or.inr (by simp [closure])
  | succ n ih =>
    intro g
    simp only [closure]
    split
    · rename_i heq
      exact Or.inl (step_eq_of_length_eq heq)
    · rename_i hne
      rcases ih (step g) with h | h
      · exact Or.inl h
      · have h1 : g.length ≤ (step g).length := length_le_step g
        exact Or.inr (by omega)

/-! ## Section 9 — the clash rows

One lemma per no-consequent row, then the decision procedure. -/

theorem exists_mem_of_not_isEmpty {a : Type} {l : List a}
    (h : (!l.isEmpty) = true) : ∃ x, x ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => exact ⟨x, List.mem_cons_self ..⟩

/-- **eq-diff1**. -/
theorem eqDiff1At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : eqDiff1At g d = true) : Clash g := by
  simp only [eqDiff1At, Bool.and_eq_true, beq_iff_eq] at h
  exact Clash.eqDiff1 (mem_of_parts hd rfl h.1 rfl) (mem_of_memB h.2)

/-- **prp-irp**. -/
theorem prpIrpAt_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : prpIrpAt g d = true) : Clash g := by
  unfold prpIrpAt at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨p, hpi, u, hu, hoo⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Clash.prpIrp (mem_of_parts hd (mem_subjIri hpi) hp1 hp2)
      (mem_of_parts hug rfl hup hoo)
  · simp at h

/-- **prp-asyp**. -/
theorem prpAsypAt_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : prpAsypAt g d = true) : Clash g := by
  unfold prpAsypAt at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.any_eq_true] at h
    obtain ⟨p, hpi, u1, hu1, y, hy, hm⟩ := h
    obtain ⟨hu1g, hu1p⟩ := mem_withPred hu1
    exact Clash.prpAsyp (mem_of_parts hd (mem_subjIri hpi) hp1 hp2)
      (mem_of_parts hu1g rfl hu1p (mem_asSubject hy))
      (mem_of_memB hm)
  · simp at h

/-- **prp-pdw**. -/
theorem prpPdwAt_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : prpPdwAt g d = true) : Clash g := by
  unfold prpPdwAt at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.any_eq_true] at h
    obtain ⟨p1, hp1i, p2, hp2i, u, hu, hm⟩ := h
    obtain ⟨hug, hup⟩ := mem_withPred hu
    exact Clash.prpPdw (mem_of_parts hd (mem_subjIri hp1i) hp (mem_asIri hp2i))
      (mem_of_parts hug rfl hup rfl) (mem_of_memB hm)
  · simp at h

/-- **prp-npa1**. -/
theorem prpNpa1At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : prpNpa1At g d = true) : Clash g := by
  unfold prpNpa1At at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.any_eq_true] at h
    obtain ⟨x, hx, ap, hap, p, hpi, ti, hti, hm⟩ := h
    obtain ⟨hapg, haps, happ⟩ := mem_withSubjPred hap
    obtain ⟨htig, htis, htip⟩ := mem_withSubjPred hti
    exact Clash.prpNpa1 (mem_of_parts hd rfl hp (mem_asSubject hx))
      (mem_of_parts hapg haps happ (mem_asIri hpi))
      (mem_of_parts htig htis htip rfl)
      (mem_of_memB hm)
  · simp at h

/-- **prp-npa2**. -/
theorem prpNpa2At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : prpNpa2At g d = true) : Clash g := by
  unfold prpNpa2At at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.any_eq_true] at h
    obtain ⟨x, hx, ap, hap, p, hpi, tv, htv, hm⟩ := h
    obtain ⟨hapg, haps, happ⟩ := mem_withSubjPred hap
    obtain ⟨htvg, htvs, htvp⟩ := mem_withSubjPred htv
    exact Clash.prpNpa2 (mem_of_parts hd rfl hp (mem_asSubject hx))
      (mem_of_parts hapg haps happ (mem_asIri hpi))
      (mem_of_parts htvg htvs htvp rfl)
      (mem_of_memB hm)
  · simp at h

/-- **cls-nothing2**. -/
theorem clsNothing2At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : clsNothing2At g d = true) : Clash g := by
  simp only [clsNothing2At, Bool.and_eq_true, beq_iff_eq] at h
  exact Clash.clsNothing2 (mem_of_parts hd rfl h.1 h.2)

/-- **cls-com**. -/
theorem clsComAt_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : clsComAt g d = true) : Clash g := by
  unfold clsComAt at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.any_eq_true] at h
    obtain ⟨u, hu, hm⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Clash.clsCom (mem_of_parts hd rfl hp rfl)
      (mem_of_parts hug rfl hup huo) (mem_of_memB hm)
  · simp at h

/-- **cls-maxc1**. -/
theorem clsMaxc1At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : clsMaxc1At g d = true) : Clash g := by
  unfold clsMaxc1At at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.any_eq_true] at h
    obtain ⟨onp, honp, p, hpi, tu, htu, hne⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    obtain ⟨u, hu⟩ := exists_mem_of_not_isEmpty hne
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Clash.clsMaxc1 (mem_of_parts hd rfl hp1 hp2)
      (mem_of_parts honpg honps honpp (mem_asIri hpi))
      (mem_of_parts htug rfl htup htuo)
      (mem_of_parts hug hus hup rfl)
  · simp at h

/-- **cls-maxqc1**. -/
theorem clsMaxqc1At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : clsMaxqc1At g d = true) : Clash g := by
  unfold clsMaxqc1At at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.any_eq_true] at h
    obtain ⟨onp, honp, p, hpi, onc, honc, tu, htu, u, hu, ys, hys, hm⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨honcg, honcs, honcp⟩ := mem_withSubjPred honc
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Clash.clsMaxqc1 (mem_of_parts hd rfl hp1 hp2)
      (mem_of_parts honpg honps honpp (mem_asIri hpi))
      (mem_of_parts honcg honcs honcp rfl)
      (mem_of_parts htug rfl htup htuo)
      (mem_of_parts hug hus hup (mem_asSubject hys))
      (mem_of_memB hm)
  · simp at h

/-- **cls-maxqc2**. -/
theorem clsMaxqc2At_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : clsMaxqc2At g d = true) : Clash g := by
  unfold clsMaxqc2At at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨onp, honp, p, hpi, onc, honc, honcth, tu, htu, hne⟩ := h
    obtain ⟨honpg, honps, honpp⟩ := mem_withSubjPred honp
    obtain ⟨honcg, honcs, honcp⟩ := mem_withSubjPred honc
    obtain ⟨htug, htup, htuo⟩ := mem_withPredObj htu
    obtain ⟨u, hu⟩ := exists_mem_of_not_isEmpty hne
    obtain ⟨hug, hus, hup⟩ := mem_withSubjPred hu
    exact Clash.clsMaxqc2 (mem_of_parts hd rfl hp1 hp2)
      (mem_of_parts honpg honps honpp (mem_asIri hpi))
      (mem_of_parts honcg honcs honcp honcth)
      (mem_of_parts htug rfl htup htuo)
      (mem_of_parts hug hus hup rfl)
  · simp at h

/-- **cax-dw**. -/
theorem caxDwAt_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : caxDwAt g d = true) : Clash g := by
  unfold caxDwAt at h
  split at h
  · rename_i hp; rw [beq_iff_eq] at hp
    simp only [List.any_eq_true] at h
    obtain ⟨u, hu, hm⟩ := h
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Clash.caxDw (mem_of_parts hd rfl hp rfl)
      (mem_of_parts hug rfl hup huo) (mem_of_memB hm)
  · simp at h

/-- **cax-adc**. -/
theorem caxAdcAt_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : caxAdcAt g d = true) : Clash g := by
  unfold caxAdcAt at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨mem, hmem, ci, hci, cj, hcj, hne, u, hu, hm⟩ := h
    obtain ⟨hmg, hms, hmp⟩ := mem_withSubjPred hmem
    obtain ⟨hug, hup, huo⟩ := mem_withPredObj hu
    exact Clash.caxAdc (mem_of_parts hd rfl hp1 hp2)
      (mem_of_parts hmg hms hmp rfl)
      (listElems_sound g (listFuel g) mem.o hci)
      (listElems_sound g (listFuel g) mem.o hcj)
      hne
      (mem_of_parts hug rfl hup huo)
      (mem_of_memB hm)
  · simp at h

/-- Every clash-row verdict for one driving triple is a real clash. -/
theorem clashFrom_sound {g : Graph} {d : Triple} (hd : d ∈ g)
    (h : clashFrom g d = true) : Clash g := by
  simp only [clashFrom, List.any_eq_true, clashRows, List.mem_cons,
    List.not_mem_nil, or_false] at h
  obtain ⟨b, hb, hv⟩ := h
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact eqDiff1At_sound hd hv
  · exact prpIrpAt_sound hd hv
  · exact prpAsypAt_sound hd hv
  · exact prpPdwAt_sound hd hv
  · exact prpNpa1At_sound hd hv
  · exact prpNpa2At_sound hd hv
  · exact clsNothing2At_sound hd hv
  · exact clsComAt_sound hd hv
  · exact clsMaxc1At_sound hd hv
  · exact clsMaxqc1At_sound hd hv
  · exact clsMaxqc2At_sound hd hv
  · exact caxDwAt_sound hd hv
  · exact caxAdcAt_sound hd hv

/-- **Clash soundness.** Every `true` verdict of the decision procedure
is a real `Clash` — the graph really does satisfy the premises of a
no-consequent row of the tables. (The converse, completeness of the
decision, is not claimed: `caxAdcAt` reads its member list through the
same fuel-bounded walk the list-valued rows use.) -/
theorem detectClash_sound {g : Graph} (h : detectClash g = true) : Clash g := by
  simp only [detectClash, List.any_eq_true] at h
  obtain ⟨d, hd, hc⟩ := h
  exact clashFrom_sound hd hc

/-! ## Section 10 — collection-walk fuel

The direction the T4 proof needs and the soundness proofs do not: that
a walk with enough fuel finds every list member and every denotation.
Both existence lemmas are proved; what is NOT proved is that
`listFuel g = g.length + 1` is always enough (the same term-universe
counting obligation `closureFuelBound` carries), which is why T4 takes
`ListFuelAdequate` as a hypothesis instead of asserting it. -/

/-- `iriIndividuals` is monotone: prp-rfl's individual set only grows
with the graph. The T4 case for that row needs it to carry the
individual from the rule's collection graph `gc` up to the saturated
graph. -/
theorem iriIndividuals_mono {g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {i : WfIri} (h : i ∈ iriIndividuals g) : i ∈ iriIndividuals g' := by
  simp only [iriIndividuals, List.mem_flatMap] at h ⊢
  obtain ⟨u, hu, hi⟩ := h
  exact ⟨u, hsub _ hu, hi⟩

/-- The hypothesis T4's list-valued rows need: the walks used by the
engine at this fuel find everything the specification relations
relate. -/
def ListFuelAdequate (g : Graph) (fuel : Nat) : Prop :=
  (∀ head e, ListMember g head e → e ∈ listElems g head fuel) ∧
  (∀ head es, ListDenotes g head es → es ∈ listSeqs g head fuel)

/-- Some fuel finds any given list member. -/
theorem exists_fuel_listElems {g : Graph} {head e : Term}
    (h : ListMember g head e) : ∃ n, e ∈ listElems g head n := by
  induction h with
  | @here node e hf =>
    refine ⟨1, ?_⟩
    simp only [listElems, List.mem_flatMap]
    refine ⟨node, mem_asSubject_toTerm node, ?_⟩
    exact List.mem_append_left _
      (List.mem_map_of_mem (mem_withSubjPred_of hf rfl rfl))
  | @there node tail e hr _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [listElems, List.mem_flatMap]
    refine ⟨node, mem_asSubject_toTerm node, ?_⟩
    refine List.mem_append_right _ ?_
    simp only [List.mem_flatMap]
    exact ⟨⟨node, rdfRest, tail⟩, mem_withSubjPred_of hr rfl rfl, hn⟩

/-- Some fuel finds any given denotation. -/
theorem exists_fuel_listSeqs {g : Graph} {head : Term} {es : List Term}
    (h : ListDenotes g head es) : ∃ n, es ∈ listSeqs g head n := by
  induction h with
  | nil =>
    refine ⟨1, ?_⟩
    simp [listSeqs]
  | @cons node e tail rest hnil hf hr _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [listSeqs, if_neg (by simpa using hnil)]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨node, mem_asSubject_toTerm node,
      ⟨node, rdfFirst, e⟩, mem_withSubjPred_of hf rfl rfl,
      ⟨node, rdfRest, tail⟩, mem_withSubjPred_of hr rfl rfl,
      rest, hn, rfl⟩


/-! ## Section 11 — the collection helpers, the other way round

`listElems_sound` and friends say the walk finds ONLY real members.
These say it finds ALL of them, for the parts that need no fuel
argument (the decisions and the chain walk are exact); the two that DO
need a fuel argument are what `ListFuelAdequate` packages. -/

theorem mem_nonEmpty_of {a : Type} {ls : List (List a)} {l : List a}
    (hm : l ∈ ls) (hne : l ≠ []) : l ∈ nonEmpty ls := by
  simp only [nonEmpty, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨hm, ?_⟩
  cases l with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

theorem allIris_complete : ∀ (ps : List WfIri), ps ∈ allIris (ps.map Term.iri) := by
  intro ps
  induction ps with
  | nil => simp [allIris]
  | cons p ps ih =>
    simp only [List.map_cons, allIris, List.mem_map]
    exact ⟨ps, ih, rfl⟩

theorem typesAllB_complete {g : Graph} {y : Subject} : ∀ {cs : List Term},
    TypesAll g y cs → typesAllB g y cs = true := by
  intro cs h
  induction h with
  | nil => simp [typesAllB]
  | cons hm _ ih =>
    simp only [typesAllB, List.all_cons, Bool.and_eq_true]
    exact ⟨memB_of_mem hm, ih⟩

theorem sharesKeyValuesB_complete {g : Graph} {x y : Subject} :
    ∀ {ps : List WfIri},
      SharesKeyValues g x y ps → sharesKeyValuesB g x y ps = true := by
  intro ps h
  induction h with
  | nil => simp [sharesKeyValuesB]
  | @cons p o rest hx hy _ ih =>
    simp only [sharesKeyValuesB, List.all_cons, Bool.and_eq_true, List.any_eq_true]
    exact ⟨⟨⟨x, p, o⟩, mem_withSubjPred_of hx rfl rfl, memB_of_mem hy⟩, ih⟩

theorem chainTargets_complete {g : Graph} : ∀ {s : Subject} {ps : List WfIri}
    {fin : Term}, ChainHolds g s ps fin → fin ∈ chainTargets g s ps := by
  intro s ps fin h
  induction h with
  | nil => simp [chainTargets]
  | @last s p o hm =>
    simp only [chainTargets, List.mem_map]
    exact ⟨⟨s, p, o⟩, mem_withSubjPred_of hm rfl rfl, rfl⟩
  | @step s mid p rest fin hm _ ih =>
    cases rest with
    | nil =>
      simp only [chainTargets, List.mem_singleton] at ih
      subst ih
      simp only [chainTargets, List.mem_map]
      exact ⟨⟨s, p, mid.toTerm⟩, mem_withSubjPred_of hm rfl rfl, rfl⟩
    | cons q rest' =>
      simp only [chainTargets, List.mem_flatMap]
      exact ⟨⟨s, p, mid.toTerm⟩, mem_withSubjPred_of hm rfl rfl,
        mid, mem_asSubject_toTerm mid, ih⟩

/-- The subject of a `ChainHolds` chain of at least one link occurs in
the graph, which is what puts it in `subjectsOf` — the candidate set
prp-spo2 iterates. -/
theorem chain_start_mem {g : Graph} {s : Subject} {ps : List WfIri}
    {fin : Term} (h : ChainHolds g s ps fin) (hne : ps ≠ []) :
    s ∈ subjectsOf g := by
  cases h with
  | nil => exact absurd rfl hne
  | last hm => exact mem_subjectsOf hm
  | step hm _ => exact mem_subjectsOf hm

/-- Likewise for cls-int1: a `TypesAll` over a non-empty class list
puts its individual in `subjectsOf`. -/
theorem typesAll_subject_mem {g : Graph} {y : Subject} {cs : List Term}
    (h : TypesAll g y cs) (hne : cs ≠ []) : y ∈ subjectsOf g := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hm _ => exact mem_subjectsOf hm

/-! ## Section 12 — T4, completeness at a saturated graph

One case per constructor of `Derives`. Each case runs the same three
moves:

1. the induction hypotheses give the row's triple premises AS MEMBERS
   of the saturated graph (exactly — there is no `Triple.eqb` slack
   here, which is the payoff of exact deduplication);
2. the row's own function is fired on the driving premise, producing
   the conclusion in that row's output list;
3. saturation carries anything in `stepConclusions` back into the
   graph.

The `ListFuelAdequate` hypothesis is used by exactly the nine
collection-valued rows, and only in move 2. -/

/-- **T4 (general form).** A saturated graph containing `g` contains
everything `g` derives, provided its collection walks are adequately
fuelled. -/
theorem complete_of_saturated {sat : Graph} (hsat : step sat = sat)
    (hlf : ListFuelAdequate sat (listFuel sat)) {g : Graph}
    (hg : ∀ u, u ∈ g → u ∈ sat) :
    ∀ {t : Triple}, Derives g t → t ∈ sat := by
  have fire : ∀ {t' : Triple}, t' ∈ stepConclusions sat → t' ∈ sat := by
    intro t' h'
    have h'' := mem_step_of_mem_conclusions h'
    rwa [hsat] at h''
  have R : ∀ {d t' : Triple} {l : List Triple}, d ∈ sat → t' ∈ l →
      l ∈ conclusionsList sat d → t' ∈ sat := by
    intro d t' l hd ht hl
    refine fire ?_
    simp only [stepConclusions, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨d, hd, List.mem_flatten.mpr ⟨l, hl, ht⟩⟩
  have axm : ∀ {t' : Triple}, t' ∈ axiomTriples → t' ∈ sat := by
    intro t' h'
    refine fire ?_
    simp only [stepConclusions, List.mem_append]
    exact Or.inl h'
  intro t h
  induction h with
  | base hm => exact hg _ hm
  | @eqRefS s p o _ ih =>
    have hc : (⟨s, owlSameAs, s.toTerm⟩ : Triple) ∈ eqRefSFor sat ⟨s, p, o⟩ := by
      simp [eqRefSFor]
    exact R ih hc (by simp [conclusionsList])
  | @eqRefP s p o _ ih =>
    have hc : (⟨Subject.iri p, owlSameAs, Term.iri p⟩ : Triple) ∈
        eqRefPFor sat ⟨s, p, o⟩ := by simp [eqRefPFor]
    exact R ih hc (by simp [conclusionsList])
  | @eqRefO s p os _ ih =>
    have hc : (⟨os, owlSameAs, os.toTerm⟩ : Triple) ∈
        eqRefOFor sat ⟨s, p, os.toTerm⟩ := by
      simp only [eqRefOFor, List.mem_map]
      exact ⟨os, mem_asSubject_toTerm os, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @eqSym x ys _ ih =>
    have hc : (⟨ys, owlSameAs, x.toTerm⟩ : Triple) ∈
        eqSymFor sat ⟨x, owlSameAs, ys.toTerm⟩ := by
      simp only [eqSymFor, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨ys, mem_asSubject_toTerm ys, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @eqTrans x ys z _ _ ih1 ih2 =>
    have hc : (⟨x, owlSameAs, z⟩ : Triple) ∈
        eqTransFor sat ⟨x, owlSameAs, ys.toTerm⟩ := by
      simp only [eqTransFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨ys, mem_asSubject_toTerm ys, ⟨ys, owlSameAs, z⟩,
        mem_withSubjPred_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @eqRepS s s' p o _ _ ih1 ih2 =>
    have hc : (⟨s', p, o⟩ : Triple) ∈
        eqRepSFor sat ⟨s, owlSameAs, s'.toTerm⟩ := by
      simp only [eqRepSFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨s', mem_asSubject_toTerm s', ⟨s, p, o⟩,
        mem_withSubj_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @eqRepP p p' s o _ _ ih1 ih2 =>
    have hc : (⟨s, p', o⟩ : Triple) ∈
        eqRepPFor sat ⟨Subject.iri p, owlSameAs, Term.iri p'⟩ := by
      simp only [eqRepPFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p, mem_subjIri_self p, p', mem_asIri_self p', ⟨s, p, o⟩,
        mem_withPred_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @eqRepO os s o' p _ _ ih1 ih2 =>
    have hc : (⟨s, p, o'⟩ : Triple) ∈ eqRepOFor sat ⟨os, owlSameAs, o'⟩ := by
      simp only [eqRepOFor, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨⟨s, p, os.toTerm⟩, mem_withObj_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpDom p cls x y _ _ ih1 ih2 =>
    have hc : (⟨x, rdfType, cls⟩ : Triple) ∈
        prpDomFor sat ⟨Subject.iri p, rdfsDomain, cls⟩ := by
      simp only [prpDomFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p, mem_subjIri_self p, ⟨x, p, y⟩, mem_withPred_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpRng p cls x ys _ _ ih1 ih2 =>
    have hc : (⟨ys, rdfType, cls⟩ : Triple) ∈
        prpRngFor sat ⟨Subject.iri p, rdfsRange, cls⟩ := by
      simp only [prpRngFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p, mem_subjIri_self p, ⟨x, p, ys.toTerm⟩,
        mem_withPred_of ih2 rfl, ys, mem_asSubject_toTerm ys, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpFp p x y1s y2 _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨y1s, owlSameAs, y2⟩ : Triple) ∈
        prpFpFor sat ⟨Subject.iri p, rdfType,
          Term.iri owlFunctionalProperty⟩ := by
      simp only [prpFpFor, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨p, mem_subjIri_self p, ⟨x, p, y1s.toTerm⟩,
        mem_withPred_of ih2 rfl, y1s, mem_asSubject_toTerm y1s,
        ⟨x, p, y2⟩, mem_withSubjPred_of ih3 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpIfp p x1 x2 y _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨x1, owlSameAs, x2.toTerm⟩ : Triple) ∈
        prpIfpFor sat ⟨Subject.iri p, rdfType,
          Term.iri owlInverseFunctionalProperty⟩ := by
      simp only [prpIfpFor, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨p, mem_subjIri_self p, ⟨x1, p, y⟩, mem_withPred_of ih2 rfl,
        ⟨x2, p, y⟩, mem_withPredObj_of ih3 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpSymp p x ys _ _ ih1 ih2 =>
    have hc : (⟨ys, p, x.toTerm⟩ : Triple) ∈
        prpSympFor sat ⟨Subject.iri p, rdfType,
          Term.iri owlSymmetricProperty⟩ := by
      simp only [prpSympFor, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨p, mem_subjIri_self p, ⟨x, p, ys.toTerm⟩,
        mem_withPred_of ih2 rfl, ys, mem_asSubject_toTerm ys, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpTrp p x ys z _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨x, p, z⟩ : Triple) ∈
        prpTrpFor sat ⟨Subject.iri p, rdfType,
          Term.iri owlTransitiveProperty⟩ := by
      simp only [prpTrpFor, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨p, mem_subjIri_self p, ⟨x, p, ys.toTerm⟩,
        mem_withPred_of ih2 rfl, ys, mem_asSubject_toTerm ys,
        ⟨ys, p, z⟩, mem_withSubjPred_of ih3 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpSpo1 p1 p2 x y _ _ ih1 ih2 =>
    have hc : (⟨x, p2, y⟩ : Triple) ∈
        prpSpo1For sat ⟨Subject.iri p1, rdfsSubPropertyOf,
          Term.iri p2⟩ := by
      simp only [prpSpo1For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p1, mem_subjIri_self p1, p2, mem_asIri_self p2, ⟨x, p1, y⟩,
        mem_withPred_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpSpo2 p lst preds x1 xn gc _ _ hlist hne hchain ihgc ih =>
    have hc : (⟨x1, p, xn⟩ : Triple) ∈
        prpSpo2For sat ⟨Subject.iri p, owlPropertyChainAxiom, lst⟩ := by
      simp only [prpSpo2For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p, mem_subjIri_self p, preds.map Term.iri,
        hlf.2 lst (preds.map Term.iri) (hlist.mono ihgc),
        preds, mem_nonEmpty_of (allIris_complete preds) hne,
        x1, chain_start_mem (hchain.mono ihgc) hne,
        xn, chainTargets_complete (hchain.mono ihgc), rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @prpEqp1 p1 p2 x y _ _ ih1 ih2 =>
    have hc : (⟨x, p2, y⟩ : Triple) ∈
        prpEqp1For sat ⟨Subject.iri p1, owlEquivalentProperty,
          Term.iri p2⟩ := by
      simp only [prpEqp1For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p1, mem_subjIri_self p1, p2, mem_asIri_self p2, ⟨x, p1, y⟩,
        mem_withPred_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpEqp2 p1 p2 x y _ _ ih1 ih2 =>
    have hc : (⟨x, p1, y⟩ : Triple) ∈
        prpEqp2For sat ⟨Subject.iri p1, owlEquivalentProperty,
          Term.iri p2⟩ := by
      simp only [prpEqp2For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p1, mem_subjIri_self p1, p2, mem_asIri_self p2, ⟨x, p2, y⟩,
        mem_withPred_of ih2 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpInv1 p1 p2 x ys _ _ ih1 ih2 =>
    have hc : (⟨ys, p2, x.toTerm⟩ : Triple) ∈
        prpInv1For sat ⟨Subject.iri p1, owlInverseOf, Term.iri p2⟩ := by
      simp only [prpInv1For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p1, mem_subjIri_self p1, p2, mem_asIri_self p2,
        ⟨x, p1, ys.toTerm⟩, mem_withPred_of ih2 rfl,
        ys, mem_asSubject_toTerm ys, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpInv2 p1 p2 x ys _ _ ih1 ih2 =>
    have hc : (⟨ys, p1, x.toTerm⟩ : Triple) ∈
        prpInv2For sat ⟨Subject.iri p1, owlInverseOf, Term.iri p2⟩ := by
      simp only [prpInv2For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p1, mem_subjIri_self p1, p2, mem_asIri_self p2,
        ⟨x, p2, ys.toTerm⟩, mem_withPred_of ih2 rfl,
        ys, mem_asSubject_toTerm ys, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @prpKey cls x ys lst preds gc _ _ hlist hne _ _ hshare ihgc ih1 ih2 ih3 =>
    have hc : (⟨x, owlSameAs, ys.toTerm⟩ : Triple) ∈
        prpKeyFor sat ⟨cls, owlHasKey, lst⟩ := by
      simp only [prpKeyFor, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨preds.map Term.iri,
        hlf.2 lst (preds.map Term.iri) (hlist.mono ihgc),
        preds, mem_nonEmpty_of (allIris_complete preds) hne,
        ⟨x, rdfType, cls.toTerm⟩, mem_withPredObj_of ih2 rfl rfl,
        ⟨ys, rdfType, cls.toTerm⟩, mem_withPredObj_of ih3 rfl rfl, ?_⟩
      rw [if_pos (sharesKeyValuesB_complete (hshare.mono ihgc))]
      simp
    exact R ih1 hc (by simp [conclusionsList])
  | clsThing => exact axm (by simp [axiomTriples])
  | clsNothing1 => exact axm (by simp [axiomTriples])
  | @clsInt1 cls y lst cs gc _ _ hlist hne htypes ihgc ih =>
    have hc : (⟨y, rdfType, cls.toTerm⟩ : Triple) ∈
        clsInt1For sat ⟨cls, owlIntersectionOf, lst⟩ := by
      simp only [clsInt1For, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨cs, mem_nonEmpty_of (hlf.2 lst cs (hlist.mono ihgc)) hne,
        y, typesAll_subject_mem (htypes.mono ihgc) hne, ?_⟩
      rw [if_pos (typesAllB_complete (htypes.mono ihgc))]
      simp
    exact R ih hc (by simp [conclusionsList])
  | @clsInt2 cls y lst ci gc _ _ hmem _ ihgc ih1 ih2 =>
    have hc : (⟨y, rdfType, ci⟩ : Triple) ∈
        clsInt2For sat ⟨cls, owlIntersectionOf, lst⟩ := by
      simp only [clsInt2For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨ci, hlf.1 lst ci (hmem.mono ihgc), ⟨y, rdfType, cls.toTerm⟩,
        mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsUni cls y lst ci gc _ _ hmem _ ihgc ih1 ih2 =>
    have hc : (⟨y, rdfType, cls.toTerm⟩ : Triple) ∈
        clsUniFor sat ⟨cls, owlUnionOf, lst⟩ := by
      simp only [clsUniFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨ci, hlf.1 lst ci (hmem.mono ihgc), ⟨y, rdfType, ci⟩,
        mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsSvf1 x u vs yc p _ _ _ _ ih1 ih2 ih3 ih4 =>
    have hc : (⟨u, rdfType, x.toTerm⟩ : Triple) ∈
        clsSvf1For sat ⟨x, owlSomeValuesFrom, yc⟩ := by
      simp only [clsSvf1For, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, p, vs.toTerm⟩, mem_withPred_of ih3 rfl,
        vs, mem_asSubject_toTerm vs, ?_⟩
      rw [if_pos (memB_of_mem ih4)]
      simp
    exact R ih1 hc (by simp [conclusionsList])
  | @clsSvf2 x u v p _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨u, rdfType, x.toTerm⟩ : Triple) ∈
        clsSvf2For sat ⟨x, owlSomeValuesFrom, Term.iri owlThing⟩ := by
      simp only [clsSvf2For, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, p, v⟩, mem_withPred_of ih3 rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsAvf x u vs yc p _ _ _ _ ih1 ih2 ih3 ih4 =>
    have hc : (⟨vs, rdfType, yc⟩ : Triple) ∈
        clsAvfFor sat ⟨x, owlAllValuesFrom, yc⟩ := by
      simp only [clsAvfFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, rdfType, x.toTerm⟩, mem_withPredObj_of ih3 rfl rfl,
        ⟨u, p, vs.toTerm⟩, mem_withSubjPred_of ih4 rfl rfl,
        vs, mem_asSubject_toTerm vs, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsHv1 x u yv p _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨u, p, yv⟩ : Triple) ∈ clsHv1For sat ⟨x, owlHasValue, yv⟩ := by
      simp only [clsHv1For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, rdfType, x.toTerm⟩, mem_withPredObj_of ih3 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsHv2 x u yv p _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨u, rdfType, x.toTerm⟩ : Triple) ∈
        clsHv2For sat ⟨x, owlHasValue, yv⟩ := by
      simp only [clsHv2For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, p, yv⟩, mem_withPredObj_of ih3 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsHs1 c u p _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨u, p, u.toTerm⟩ : Triple) ∈
        clsHs1For sat ⟨c, owlHasSelf, Term.literal litTrueBoolean⟩ := by
      simp only [clsHs1For, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨⟨c, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, rdfType, c.toTerm⟩, mem_withPredObj_of ih3 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsHs2 c u p _ _ _ ih1 ih2 ih3 =>
    have hc : (⟨u, rdfType, c.toTerm⟩ : Triple) ∈
        clsHs2For sat ⟨c, owlHasSelf, Term.literal litTrueBoolean⟩ := by
      simp only [clsHs2For, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap]
      exact ⟨⟨c, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, p, u.toTerm⟩, mem_withPred_of ih3 rfl, by simp⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsMaxc2 x u y1s y2 p _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have hc : (⟨y1s, owlSameAs, y2⟩ : Triple) ∈
        clsMaxc2For sat ⟨x, owlMaxCardinality, Term.literal litNni1⟩ := by
      simp only [clsMaxc2For, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨u, rdfType, x.toTerm⟩, mem_withPredObj_of ih3 rfl rfl,
        ⟨u, p, y1s.toTerm⟩, mem_withSubjPred_of ih4 rfl rfl,
        y1s, mem_asSubject_toTerm y1s,
        ⟨u, p, y2⟩, mem_withSubjPred_of ih5 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @clsOo cls yis lst gc _ _ hmem ihgc ih =>
    have hc : (⟨yis, rdfType, cls.toTerm⟩ : Triple) ∈
        clsOoFor sat ⟨cls, owlOneOf, lst⟩ := by
      simp only [clsOoFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨yis.toTerm, hlf.1 lst yis.toTerm (hmem.mono ihgc),
        yis, mem_asSubject_toTerm yis, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @caxSco c1 x c2 _ _ ih1 ih2 =>
    have hc : (⟨x, rdfType, c2⟩ : Triple) ∈
        caxScoFor sat ⟨c1, rdfsSubClassOf, c2⟩ := by
      simp only [caxScoFor, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨⟨x, rdfType, c1.toTerm⟩, mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @caxEqc1 c1 x c2 _ _ ih1 ih2 =>
    have hc : (⟨x, rdfType, c2⟩ : Triple) ∈
        caxEqc1For sat ⟨c1, owlEquivalentClass, c2⟩ := by
      simp only [caxEqc1For, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨⟨x, rdfType, c1.toTerm⟩, mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @caxEqc2 c1 x c2 _ _ ih1 ih2 =>
    have hc : (⟨x, rdfType, c1.toTerm⟩ : Triple) ∈
        caxEqc2For sat ⟨c1, owlEquivalentClass, c2⟩ := by
      simp only [caxEqc2For, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨⟨x, rdfType, c2⟩, mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmClsSelf cls _ ih =>
    have hc : (⟨cls, rdfsSubClassOf, cls.toTerm⟩ : Triple) ∈
        scmClsFor sat ⟨cls, rdfType, Term.iri owlClass⟩ := by
      simp [scmClsFor]
    exact R ih hc (by simp [conclusionsList])
  | @scmClsEqc cls _ ih =>
    have hc : (⟨cls, owlEquivalentClass, cls.toTerm⟩ : Triple) ∈
        scmClsFor sat ⟨cls, rdfType, Term.iri owlClass⟩ := by
      simp [scmClsFor]
    exact R ih hc (by simp [conclusionsList])
  | @scmClsThing cls _ ih =>
    have hc : (⟨cls, rdfsSubClassOf, Term.iri owlThing⟩ : Triple) ∈
        scmClsFor sat ⟨cls, rdfType, Term.iri owlClass⟩ := by
      simp [scmClsFor]
    exact R ih hc (by simp [conclusionsList])
  | @scmClsNothing cls _ ih =>
    have hc : (⟨Subject.iri owlNothing, rdfsSubClassOf, cls.toTerm⟩ : Triple) ∈
        scmClsFor sat ⟨cls, rdfType, Term.iri owlClass⟩ := by
      simp [scmClsFor]
    exact R ih hc (by simp [conclusionsList])
  | @scmSco c1 c2s c3 _ _ ih1 ih2 =>
    have hc : (⟨c1, rdfsSubClassOf, c3⟩ : Triple) ∈
        scmScoFor sat ⟨c1, rdfsSubClassOf, c2s.toTerm⟩ := by
      simp only [scmScoFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨c2s, mem_asSubject_toTerm c2s, ⟨c2s, rdfsSubClassOf, c3⟩,
        mem_withSubjPred_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmEqc1a c1 c2 _ ih =>
    have hc : (⟨c1, rdfsSubClassOf, c2⟩ : Triple) ∈
        scmEqc1For sat ⟨c1, owlEquivalentClass, c2⟩ := by
      simp [scmEqc1For]
    exact R ih hc (by simp [conclusionsList])
  | @scmEqc1b c1 c2s _ ih =>
    have hc : (⟨c2s, rdfsSubClassOf, c1.toTerm⟩ : Triple) ∈
        scmEqc1For sat ⟨c1, owlEquivalentClass, c2s.toTerm⟩ := by
      simp only [scmEqc1For, beq_self_eq_true, if_true, List.mem_cons,
        List.mem_map]
      exact Or.inr ⟨c2s, mem_asSubject_toTerm c2s, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @scmEqc2 c1 c2s _ _ ih1 ih2 =>
    have hc : (⟨c1, owlEquivalentClass, c2s.toTerm⟩ : Triple) ∈
        scmEqc2For sat ⟨c1, rdfsSubClassOf, c2s.toTerm⟩ := by
      simp only [scmEqc2For, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨c2s, mem_asSubject_toTerm c2s, ?_⟩
      rw [if_pos (memB_of_mem ih2)]
      simp
    exact R ih1 hc (by simp [conclusionsList])
  | @scmSpo p1 p2s p3 _ _ ih1 ih2 =>
    have hc : (⟨p1, rdfsSubPropertyOf, p3⟩ : Triple) ∈
        scmSpoFor sat ⟨p1, rdfsSubPropertyOf, p2s.toTerm⟩ := by
      simp only [scmSpoFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨p2s, mem_asSubject_toTerm p2s, ⟨p2s, rdfsSubPropertyOf, p3⟩,
        mem_withSubjPred_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmEqp1a p1 p2 _ ih =>
    have hc : (⟨p1, rdfsSubPropertyOf, p2⟩ : Triple) ∈
        scmEqp1For sat ⟨p1, owlEquivalentProperty, p2⟩ := by
      simp [scmEqp1For]
    exact R ih hc (by simp [conclusionsList])
  | @scmEqp1b p1 p2s _ ih =>
    have hc : (⟨p2s, rdfsSubPropertyOf, p1.toTerm⟩ : Triple) ∈
        scmEqp1For sat ⟨p1, owlEquivalentProperty, p2s.toTerm⟩ := by
      simp only [scmEqp1For, beq_self_eq_true, if_true, List.mem_cons,
        List.mem_map]
      exact Or.inr ⟨p2s, mem_asSubject_toTerm p2s, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @scmEqp2 p1 p2s _ _ ih1 ih2 =>
    have hc : (⟨p1, owlEquivalentProperty, p2s.toTerm⟩ : Triple) ∈
        scmEqp2For sat ⟨p1, rdfsSubPropertyOf, p2s.toTerm⟩ := by
      simp only [scmEqp2For, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨p2s, mem_asSubject_toTerm p2s, ?_⟩
      rw [if_pos (memB_of_mem ih2)]
      simp
    exact R ih1 hc (by simp [conclusionsList])
  | @scmDom1 p c1s c2 _ _ ih1 ih2 =>
    have hc : (⟨p, rdfsDomain, c2⟩ : Triple) ∈
        scmDom1For sat ⟨p, rdfsDomain, c1s.toTerm⟩ := by
      simp only [scmDom1For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨c1s, mem_asSubject_toTerm c1s, ⟨c1s, rdfsSubClassOf, c2⟩,
        mem_withSubjPred_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmDom2 p2 p1 cls _ _ ih1 ih2 =>
    have hc : (⟨p1, rdfsDomain, cls⟩ : Triple) ∈
        scmDom2For sat ⟨p2, rdfsDomain, cls⟩ := by
      simp only [scmDom2For, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨⟨p1, rdfsSubPropertyOf, p2.toTerm⟩,
        mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmRng1 p c1s c2 _ _ ih1 ih2 =>
    have hc : (⟨p, rdfsRange, c2⟩ : Triple) ∈
        scmRng1For sat ⟨p, rdfsRange, c1s.toTerm⟩ := by
      simp only [scmRng1For, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨c1s, mem_asSubject_toTerm c1s, ⟨c1s, rdfsSubClassOf, c2⟩,
        mem_withSubjPred_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmRng2 p2 p1 cls _ _ ih1 ih2 =>
    have hc : (⟨p1, rdfsRange, cls⟩ : Triple) ∈
        scmRng2For sat ⟨p2, rdfsRange, cls⟩ := by
      simp only [scmRng2For, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨⟨p1, rdfsSubPropertyOf, p2.toTerm⟩,
        mem_withPredObj_of ih2 rfl rfl, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @scmInt cls lst ci gc _ _ hmem ihgc ih =>
    have hc : (⟨cls, rdfsSubClassOf, ci⟩ : Triple) ∈
        scmIntFor sat ⟨cls, owlIntersectionOf, lst⟩ := by
      simp only [scmIntFor, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨ci, hlf.1 lst ci (hmem.mono ihgc), rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @scmUni cls cis lst gc _ _ hmem ihgc ih =>
    have hc : (⟨cis, rdfsSubClassOf, cls.toTerm⟩ : Triple) ∈
        scmUniFor sat ⟨cls, owlUnionOf, lst⟩ := by
      simp only [scmUniFor, beq_self_eq_true, if_true, List.mem_flatMap,
        List.mem_map]
      exact ⟨cis.toTerm, hlf.1 lst cis.toTerm (hmem.mono ihgc),
        cis, mem_asSubject_toTerm cis, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  -- `[ext]` rows
  | @eqDiffSym x ys _ ih =>
    have hc : (⟨ys, owlDifferentFrom, x.toTerm⟩ : Triple) ∈
        eqDiffSymFor sat ⟨x, owlDifferentFrom, ys.toTerm⟩ := by
      simp only [eqDiffSymFor, beq_self_eq_true, if_true, List.mem_map]
      exact ⟨ys, mem_asSubject_toTerm ys, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @pdwToDiff p1 p2 x o1s o2 _ _ _ hne ih1 ih2 ih3 =>
    have hc : (⟨o1s, owlDifferentFrom, o2⟩ : Triple) ∈
        pdwToDiffFor sat ⟨Subject.iri p1, owlPropertyDisjointWith,
          Term.iri p2⟩ := by
      simp only [pdwToDiffFor, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨p1, mem_subjIri_self p1, p2, mem_asIri_self p2,
        ⟨x, p1, o1s.toTerm⟩, mem_withPred_of ih2 rfl,
        o1s, mem_asSubject_toTerm o1s, ⟨x, p2, o2⟩,
        mem_withSubjPred_of ih3 rfl rfl, ?_⟩
      simp [hne]
    exact R ih1 hc (by simp [conclusionsList])
  | @caxDwToDiff c1 c2 x ys _ _ _ hne ih1 ih2 ih3 =>
    have hc : (⟨x, owlDifferentFrom, ys.toTerm⟩ : Triple) ∈
        caxDwToDiffFor sat ⟨Subject.iri c1, owlDisjointWith,
          Term.iri c2⟩ := by
      simp only [caxDwToDiffFor, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨c1, mem_subjIri_self c1, c2, mem_asIri_self c2,
        ⟨x, rdfType, Term.iri c1⟩, mem_withPredObj_of ih2 rfl rfl,
        ⟨ys, rdfType, Term.iri c2⟩, mem_withPredObj_of ih3 rfl rfl, ?_⟩
      simp [hne]
    exact R ih1 hc (by simp [conclusionsList])
  | @fpDiffToDiff p y1 y2 x1s x2 _ _ _ _ hne ih1 ih2 ih3 ih4 =>
    have hc : (⟨y1, owlDifferentFrom, y2.toTerm⟩ : Triple) ∈
        fpDiffToDiffFor sat ⟨x1s, owlDifferentFrom, x2⟩ := by
      simp only [fpDiffToDiffFor, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨⟨y1, p, x1s.toTerm⟩, mem_withObj_of ih2 rfl, ?_⟩
      rw [if_pos (memB_of_mem ih1)]
      simp only [List.mem_flatMap]
      refine ⟨⟨y2, p, x2⟩, mem_withPredObj_of ih3 rfl rfl, ?_⟩
      simp [hne]
    exact R ih4 hc (by simp [conclusionsList])
  | @ifpDiffToDiff p x1 x2s y1s y2 _ _ _ _ hne ih1 ih2 ih3 ih4 =>
    have hc : (⟨y1s, owlDifferentFrom, y2⟩ : Triple) ∈
        ifpDiffToDiffFor sat ⟨x1, owlDifferentFrom, x2s.toTerm⟩ := by
      simp only [ifpDiffToDiffFor, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨⟨x1, p, y1s.toTerm⟩, mem_withSubj_of ih2 rfl, ?_⟩
      rw [if_pos (memB_of_mem ih1)]
      simp only [List.mem_flatMap]
      refine ⟨y1s, mem_asSubject_toTerm y1s, x2s, mem_asSubject_toTerm x2s,
        ⟨x2s, p, y2⟩, mem_withSubjPred_of ih3 rfl rfl, ?_⟩
      simp [hne]
    exact R ih4 hc (by simp [conclusionsList])
  | @chainToTrans p lst gc _ _ hlist ihgc ih =>
    have hc : (⟨Subject.iri p, rdfType,
        Term.iri owlTransitiveProperty⟩ : Triple) ∈
        chainToTransFor sat ⟨Subject.iri p, owlPropertyChainAxiom, lst⟩ := by
      simp only [chainToTransFor, beq_self_eq_true, if_true, List.mem_flatMap]
      refine ⟨p, mem_subjIri_self p, [Term.iri p, Term.iri p],
        hlf.2 lst _ (hlist.mono ihgc), ?_⟩
      simp
    exact R ih hc (by simp [conclusionsList])
  | @prpRfl p i gc _ _ hind ihgc ih =>
    have hc : (⟨Subject.iri i, p, Term.iri i⟩ : Triple) ∈
        prpRflFor sat ⟨Subject.iri p, rdfType,
          Term.iri owlReflexiveProperty⟩ := by
      simp only [prpRflFor, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap, List.mem_map]
      exact ⟨p, mem_subjIri_self p, i, iriIndividuals_mono ihgc hind, rfl⟩
    exact R ih hc (by simp [conclusionsList])
  | @xsdAxioms d t' _ hx hax ih =>
    have hc : t' ∈ xsdAxiomsFor sat d := by
      simp only [xsdAxiomsFor, hx, if_true]
      exact hax
    exact R ih hc (by simp [conclusionsList])
  | @dtRangeIntersect pd d1 d2 d3 _ _ hlic ih1 ih2 =>
    have hc : (⟨pd, rdfsRange, Term.iri d3⟩ : Triple) ∈
        dtRangeIntersectFor sat ⟨pd, rdfsRange, Term.iri d1⟩ := by
      simp only [dtRangeIntersectFor, beq_self_eq_true, if_true,
        List.mem_flatMap]
      simp only [rangeIntersectLicenses, List.any_eq_true,
        Bool.and_eq_true] at hlic
      obtain ⟨e, he, hmatch, hcon⟩ := hlic
      refine ⟨d1, mem_asIri_self d1, ⟨pd, rdfsRange, Term.iri d2⟩,
        mem_withSubjPred_of ih2 rfl rfl, d2, mem_asIri_self d2,
        e, he, ?_⟩
      rw [if_pos hmatch]
      simp only [List.mem_map]
      exact ⟨d3, by simpa [List.contains_iff_mem] using hcon, rfl⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @dtType1Builtin t' hax =>
    refine axm ?_
    simp only [axiomTriples, List.cons_append, List.nil_append, List.mem_cons]
    exact Or.inr (Or.inr hax)
  | @caxDwToComplement c1 c2 t' _ hax ih =>
    have hc : t' ∈ caxDwToComplementFor sat
        ⟨Subject.iri c1, owlDisjointWith, Term.iri c2⟩ := by
      simp only [caxDwToComplementFor, beq_self_eq_true, if_true,
        List.mem_flatMap]
      exact ⟨c1, mem_subjIri_self c1, c2, mem_asIri_self c2, hax⟩
    exact R ih hc (by simp [conclusionsList])
  | @clsMaxqc1ToComplement x u y1s y2s p c t' _ _ _ _ _ _ _ _ hax
      ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8 =>
    have hc : t' ∈ clsMaxqc1ToComplementFor sat
        ⟨x, owlMaxQualifiedCardinality, Term.literal litNni1⟩ := by
      simp only [clsMaxqc1ToComplementFor, beq_self_eq_true, Bool.and_self,
        if_true, List.mem_flatMap]
      refine ⟨⟨x, owlOnProperty, Term.iri p⟩,
        mem_withSubjPred_of ih2 rfl rfl, p, mem_asIri_self p,
        ⟨x, owlOnClass, Term.iri c⟩, mem_withSubjPred_of ih3 rfl rfl,
        c, mem_asIri_self c,
        ⟨u, rdfType, x.toTerm⟩, mem_withPredObj_of ih4 rfl rfl,
        ⟨u, p, y1s.toTerm⟩, mem_withSubjPred_of ih5 rfl rfl,
        y1s, mem_asSubject_toTerm y1s, ?_⟩
      rw [if_pos (memB_of_mem ih7)]
      simp only [List.mem_flatMap]
      refine ⟨⟨y1s, owlDifferentFrom, y2s.toTerm⟩,
        mem_withSubjPred_of ih8 rfl rfl, y2s, mem_asSubject_toTerm y2s, ?_⟩
      rw [if_pos (memB_of_mem ih6)]
      exact hax
    exact R ih1 hc (by simp [conclusionsList])
  | @minCard1Comprehension p t' _ hax ih =>
    have hc : t' ∈ minCard1ComprehensionFor sat
        ⟨Subject.iri p, rdfType, Term.iri owlObjectProperty⟩ := by
      simp only [minCard1ComprehensionFor, beq_self_eq_true, Bool.and_self,
        if_true, List.mem_flatMap]
      exact ⟨p, mem_subjIri_self p, hax⟩
    exact R ih hc (by simp [conclusionsList])
  | @caxAdcToDw y lst ci cj gc _ _ _ h1 h2 hne ihgc ih1 ih2 =>
    have hc : (⟨Subject.iri ci, owlDisjointWith, Term.iri cj⟩ : Triple) ∈
        caxAdcToDwFor sat ⟨y, rdfType, Term.iri owlAllDisjointClasses⟩ := by
      simp only [caxAdcToDwFor, beq_self_eq_true, Bool.and_self, if_true,
        List.mem_flatMap]
      refine ⟨⟨y, owlMembers, lst⟩, mem_withSubjPred_of ih2 rfl rfl,
        Term.iri ci, hlf.1 lst (Term.iri ci) (h1.mono ihgc),
        ci, mem_asIri_self ci,
        Term.iri cj, hlf.1 lst (Term.iri cj) (h2.mono ihgc),
        cj, mem_asIri_self cj, ?_⟩
      have hb : (ci == cj) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hne
      simp [hb]
    exact R ih1 hc (by simp [conclusionsList])
  | @invFlipDomRng p q c _ _ ih1 ih2 =>
    have hc : (⟨Subject.iri q, rdfsRange, Term.iri c⟩ : Triple) ∈
        inverseOfDomRngFlipFor sat
          ⟨Subject.iri p, owlInverseOf, Term.iri q⟩ := by
      simp only [inverseOfDomRngFlipFor, beq_self_eq_true, if_true,
        List.mem_flatMap]
      exact ⟨p, mem_subjIri_self p, q, mem_asIri_self q,
        ⟨Subject.iri p, rdfsDomain, Term.iri c⟩, ih2, by simp⟩
    exact R ih1 hc (by simp [conclusionsList])
  | @invFlipRngDom p q c _ _ ih1 ih2 =>
    have hc : (⟨Subject.iri q, rdfsDomain, Term.iri c⟩ : Triple) ∈
        inverseOfDomRngFlipFor sat
          ⟨Subject.iri p, owlInverseOf, Term.iri q⟩ := by
      simp only [inverseOfDomRngFlipFor, beq_self_eq_true, if_true,
        List.mem_flatMap]
      refine ⟨p, mem_subjIri_self p, q, mem_asIri_self q,
        ⟨Subject.iri p, rdfsRange, Term.iri c⟩, ih2, ?_⟩
      have hdr : (rdfsRange == rdfsDomain) = false := by decide
      simp [hdr]
    exact R ih1 hc (by simp [conclusionsList])
  | @invFlipDomRngRev p q c _ _ ih1 ih2 =>
    have hc : (⟨Subject.iri p, rdfsRange, Term.iri c⟩ : Triple) ∈
        inverseOfDomRngFlipFor sat
          ⟨Subject.iri p, owlInverseOf, Term.iri q⟩ := by
      simp only [inverseOfDomRngFlipFor, beq_self_eq_true, if_true,
        List.mem_flatMap]
      refine ⟨p, mem_subjIri_self p, q, mem_asIri_self q,
        ⟨Subject.iri q, rdfsDomain, Term.iri c⟩, ih2, ?_⟩
      by_cases hqp : q = p
      · subst hqp; simp
      · have hb : (q == p) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact hqp
        simp [hb]
    exact R ih1 hc (by simp [conclusionsList])
  | @invFlipRngDomRev p q c _ _ ih1 ih2 =>
    have hc : (⟨Subject.iri p, rdfsDomain, Term.iri c⟩ : Triple) ∈
        inverseOfDomRngFlipFor sat
          ⟨Subject.iri p, owlInverseOf, Term.iri q⟩ := by
      simp only [inverseOfDomRngFlipFor, beq_self_eq_true, if_true,
        List.mem_flatMap]
      refine ⟨p, mem_subjIri_self p, q, mem_asIri_self q,
        ⟨Subject.iri q, rdfsRange, Term.iri c⟩, ih2, ?_⟩
      have hdr : (rdfsRange == rdfsDomain) = false := by decide
      by_cases hqp : q = p
      · subst hqp; simp [hdr]
      · have hb : (q == p) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact hqp
        simp [hb, hdr]
    exact R ih1 hc (by simp [conclusionsList])

/-- **T4.** Everything derivable from `g` is in `g`'s closure, provided
the closure is saturated (which `closure_saturated_or_underfueled`
turns into "provided the fuel was not exhausted") and its collection
walks are adequately fuelled. -/
theorem closure_complete_of_saturated {g : Graph} {fuel : Nat}
    (hsat : step (closure g fuel) = closure g fuel)
    (hlf : ListFuelAdequate (closure g fuel) (listFuel (closure g fuel)))
    {t : Triple} (h : Derives g t) : t ∈ closure g fuel :=
  complete_of_saturated hsat hlf (fun _ hu => closure_extensive fuel g hu) h

/-! ## Section 13 — T3, monotonicity

Not an independent proof: T2 says the small closure is derivable,
`Derives.mono` moves the derivation to the bigger graph, and T4 puts it
in the bigger closure. The saturation and collection-fuel hypotheses
are where the conditionality comes from — with a fixed fuel the two
runs stop at different rounds, so the unconditional inclusion is not
available. -/

/-- **T3.** If `g ⊆ g'` and `g'`'s closure is saturated and adequately
fuelled, then `g`'s closure is contained in it. -/
theorem closure_mono_of_saturated {g g' : Graph} {fuel fuel' : Nat}
    (hsub : ∀ u, u ∈ g → u ∈ g')
    (hsat : step (closure g' fuel') = closure g' fuel')
    (hlf : ListFuelAdequate (closure g' fuel') (listFuel (closure g' fuel')))
    {t : Triple} (h : t ∈ closure g fuel) : t ∈ closure g' fuel' :=
  closure_complete_of_saturated hsat hlf
    (Derives.mono hsub (closure_sound fuel g h))

end L4Factoidal.OWL.RL
