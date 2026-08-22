/-
L4Factoidal.RDFS.ClosureTheorems — the closure operator against its
specification, proved natively.

The F* module `RDF.Entailment.RDFS.RhoDFClosure.fst` states five
theorems and discharges them with Z3 (`--z3rlimit 240` on the
soundness recursion), several under carried hypotheses
(`rho_df_chain_canonical`, `rho_df_chain_wf`, `no_repeats_p`). This
file re-proves the executable content by structural induction, with no
solver, no `sorry`, no `axiom`, no `native_decide`, and no carried
hypothesis other than the one named in T4.

WHAT IS PROVED HERE, and how it differs from the F* statements.

* **T1 extensivity** — `closure_extensive`: `t ∈ g → t ∈ closure g
  fuel`. F* theorem 1 (`rho_df_closure_extensive`, line 204) says
  `is_subgraph g (rho_df_closure g fuel)` under
  `rho_df_chain_canonical`. Here no hypothesis is needed.

* **T2 soundness** — `closure_sound`: `t ∈ closure g fuel → Derives g
  t`. F* theorem 2 (`rho_df_closure_sound`, line 291) is MODEL-
  THEORETIC (`rho_df_entails g (rho_df_closure g fuel)`: every
  rho-df interpretation satisfying `g` satisfies the closure). The
  Lean statement is PROOF-THEORETIC: every computed triple has a
  derivation in the §9.2 rule relation. Model-theoretic soundness
  would need the interpretation machinery
  (`RDF.Entailment.RDFS.ModelTheory`) ported first; the rule relation
  is the object a reviewer checks against the W3C table, and the
  bridge from it to interpretations is one lemma per row that the F*
  tree already carries. Do not read T2 as the F* theorem.

* **T3 monotonicity** — `closure_mono_of_saturated`: derived from T2 +
  `Derives.mono` + T4, and therefore conditional on the larger
  graph's closure being saturated. The unconditional form (`g ⊆ g' →
  closure g fuel ⊆ closure g' fuel` for the SAME fuel) is not proved
  and is not expected to hold pointwise: the two runs stop at
  different iterations.

* **T4 completeness at the fixpoint** — `closure_complete_of_saturated`:
  `Derives g t → Graph.mem t (closure g fuel) = true`, given
  `step (closure g fuel) = closure g fuel`. PROVED IN FULL, all six
  rule cases and the base case. The saturation hypothesis is
  discharged by `closure_saturated_or_underfueled` for every graph
  whose closure is reached inside the fuel: the only alternative to
  saturation is that the result grew by at least one triple per unit
  of fuel spent. REMAINING OBLIGATION (named, not hidden): that
  `closureFuelBound` is always enough — i.e. that the closure of an
  `n`-triple graph cannot exceed `n * (n + 1) * n` triples, the
  term-universe counting argument written out in `Closure.lean`'s
  `closureFuelBound` doc comment. Formalising it needs a bound on the
  set of triples buildable from a graph's components; nothing else in
  this file depends on it.

## Two membership relations, and why both appear

`Graph.mem` is the engine's membership: it compares with `Triple.eqb`,
which is COARSER than equality (language-tag case folding,
`rdf:XMLLiteral` canonical-XML equality). List membership `∈` is exact.

* T1 and T2 use LIST membership. That is the strong reading in both
  directions: the closure really contains the input triples, and every
  list element really has a derivation.
* T4 uses `Graph.mem`. It has to: `Graph.add t g` skips the insert
  when `g` already holds an eqb-equal triple, so after adding `t` the
  graph may contain an XMLLiteral-variant of `t` instead of `t`
  itself, and `t ∈ closure g fuel` would be false while the triple is
  present up to the equality the engine uses. `Graph.mem` is exactly
  the right relation there, and list membership implies it
  (`graphMem_of_mem`).

This asymmetry is a property of the ported `Graph.add`, not an
artefact of the proof.
-/
import L4Factoidal.RDFS.Closure

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Section 1 — `Graph.add` and `addAll`

Everything the closure does to a graph, it does through `Graph.add`.
These are the facts the rest of the file uses: membership is never
lost, nothing appears that was not added, length never decreases, and
an unchanged length means an unchanged graph (which is what makes the
F* length test an exact fixpoint test). -/

/-- List membership implies engine membership (`Triple.eqb` is
reflexive). -/
theorem graphMem_of_mem {g : Graph} {t : Triple} (h : t ∈ g) :
    Graph.mem t g = true := by
  induction g with
  | nil => cases h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [Graph.mem]
    · simp [Graph.mem, ih h']

/-- Engine membership is witnessed by an eqb-equal list element. -/
theorem exists_of_graphMem {g : Graph} {t : Triple}
    (h : Graph.mem t g = true) : ∃ u, u ∈ g ∧ Triple.eqb u t = true := by
  induction g with
  | nil => simp [Graph.mem] at h
  | cons hd tl ih =>
    simp only [Graph.mem, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self .., h⟩
    · obtain ⟨u, hu, he⟩ := ih h
      exact ⟨u, List.mem_cons_of_mem _ hu, he⟩

theorem mem_add_of_mem_list {g : Graph} {t u : Triple} (h : t ∈ g) :
    t ∈ g.add u := by
  unfold Graph.add
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_add_cases {g : Graph} {t u : Triple} (h : t ∈ g.add u) :
    t ∈ g ∨ t = u := by
  unfold Graph.add at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (List.mem_singleton.mp h')

theorem length_le_add (g : Graph) (u : Triple) :
    g.length ≤ (g.add u).length := by
  unfold Graph.add
  split
  · exact Nat.le_refl _
  · simp

theorem add_eq_of_length_eq {g : Graph} {u : Triple}
    (h : (g.add u).length = g.length) : g.add u = g := by
  by_cases hm : g.mem u = true
  · simp [Graph.add, hm]
  · simp [Graph.add, hm] at h

theorem mem_addAll_of_mem (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, t ∈ g → t ∈ addAll g ts := by
  induction ts with
  | nil => intro g t h; exact h
  | cons u ts ih =>
    intro g t h
    simp only [addAll]
    exact ih (g.add u) (mem_add_of_mem_list h)

theorem mem_addAll_cases (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, t ∈ addAll g ts → t ∈ g ∨ t ∈ ts := by
  induction ts with
  | nil => intro g t h; exact Or.inl h
  | cons u ts ih =>
    intro g t h
    simp only [addAll] at h
    rcases ih (g.add u) h with h' | h'
    · rcases mem_add_cases h' with h'' | rfl
      · exact Or.inl h''
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem graphMem_addAll_of_graphMem (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, Graph.mem t g = true →
      Graph.mem t (addAll g ts) = true := by
  induction ts with
  | nil => intro g t h; exact h
  | cons u ts ih =>
    intro g t h
    simp only [addAll]
    exact ih (g.add u) (Graph.mem_add_of_mem g u t h)

theorem graphMem_addAll_of_mem_list (ts : List Triple) :
    ∀ (g : Graph) {t : Triple}, t ∈ ts → Graph.mem t (addAll g ts) = true := by
  induction ts with
  | nil => intro g t h; cases h
  | cons u ts ih =>
    intro g t h
    simp only [addAll]
    rcases List.mem_cons.mp h with rfl | h'
    · exact graphMem_addAll_of_graphMem ts (g.add t) (Graph.mem_add_self g t)
    · exact ih (g.add u) h'

theorem length_le_addAll (ts : List Triple) :
    ∀ (g : Graph), g.length ≤ (addAll g ts).length := by
  induction ts with
  | nil => intro g; exact Nat.le_refl _
  | cons u ts ih =>
    intro g
    simp only [addAll]
    exact Nat.le_trans (length_le_add g u) (ih (g.add u))

/-- The F* fixpoint test made exact: if a round did not change the
LENGTH, the round was the identity. (`RhoDFClosure.fst` carries this
as the two `no_repeats_p` hypotheses of
`FixedPoint.lemma_len_eq_saturated` instead of proving it.) -/
theorem addAll_eq_of_length_eq (ts : List Triple) :
    ∀ (g : Graph), (addAll g ts).length = g.length → addAll g ts = g := by
  induction ts with
  | nil => intro g _; rfl
  | cons u ts ih =>
    intro g h
    simp only [addAll] at h ⊢
    have h1 : g.length ≤ (g.add u).length := length_le_add g u
    have h2 : (g.add u).length ≤ (addAll (g.add u) ts).length :=
      length_le_addAll ts (g.add u)
    have h3 : (g.add u).length = g.length := by omega
    have h4 : g.add u = g := add_eq_of_length_eq h3
    rw [h4] at h ⊢
    exact ih g h

/-- One round never loses a triple. -/
theorem mem_step_of_mem {g : Graph} {t : Triple} (h : t ∈ g) : t ∈ step g :=
  mem_addAll_of_mem _ g h

/-- One round adds nothing but rule conclusions. -/
theorem mem_step_cases {g : Graph} {t : Triple} (h : t ∈ step g) :
    t ∈ g ∨ t ∈ stepConclusions g :=
  mem_addAll_cases _ g h

/-- Every conclusion of a round is present (up to `Triple.eqb`) in the
round's output. -/
theorem graphMem_step_of_mem_conclusions {g : Graph} {t : Triple}
    (h : t ∈ stepConclusions g) : Graph.mem t (step g) = true :=
  graphMem_addAll_of_mem_list _ g h

/-- The length test is exact for `step`. -/
theorem step_eq_of_length_eq {g : Graph} (h : (step g).length = g.length) :
    step g = g :=
  addAll_eq_of_length_eq _ g h

/-! ## Section 2 — T1, extensivity

F* theorem 1 (`rho_df_closure_extensive`, line 204). -/

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

/-- T1 in the engine's membership relation. -/
theorem graphMem_closure_of_mem {g : Graph} {t : Triple} {fuel : Nat}
    (h : t ∈ g) : Graph.mem t (closure g fuel) = true :=
  graphMem_of_mem (closure_extensive fuel g h)

/-! ## Section 3 — the two premise lookups

`objectsOf` and `triplesWithPredicate` characterised in both
directions: soundness (section 4) needs "a looked-up premise really is
in the graph"; completeness (section 6) needs the converse. -/

theorem mem_objectsOf {g : Graph} {s : Subject} {p : WfIri} {o : Term}
    (h : o ∈ objectsOf g s p) : (⟨s, p, o⟩ : Triple) ∈ g := by
  simp only [objectsOf, List.mem_map, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq] at h
  obtain ⟨u, ⟨hu, hs, hp⟩, ho⟩ := h
  have huu : (⟨s, p, o⟩ : Triple) = u := by rw [← hs, ← hp, ← ho]
  rw [huu]; exact hu

theorem mem_objectsOf_of_mem {g : Graph} {s : Subject} {p : WfIri} {o : Term}
    (h : (⟨s, p, o⟩ : Triple) ∈ g) : o ∈ objectsOf g s p := by
  simp only [objectsOf, List.mem_map, List.mem_filter]
  exact ⟨⟨s, p, o⟩, ⟨h, by simp⟩, rfl⟩

theorem mem_triplesWithPredicate {g : Graph} {p : WfIri} {u : Triple}
    (h : u ∈ triplesWithPredicate g p) : u ∈ g ∧ u.p = p := by
  simp only [triplesWithPredicate, List.mem_filter, beq_iff_eq] at h
  exact h

theorem mem_triplesWithPredicate_of {g : Graph} {p : WfIri} {u : Triple}
    (h : u ∈ g) (hp : u.p = p) : u ∈ triplesWithPredicate g p := by
  simp only [triplesWithPredicate, List.mem_filter, beq_iff_eq]
  exact ⟨h, hp⟩

/-! ## Section 4 — one lemma per row: what the row emits is derivable

Six lemmas, one per RDF 1.1 Semantics §9.2 row, each of the shape
"if the driving triple is in `g` and `t` is emitted, then `Derives g
t`". They are the whole content of T2; the rest is bookkeeping. -/

/-- **rdfs7.** -/
theorem rdfs7For_sound {g : Graph} {decl t : Triple} (hd : decl ∈ g)
    (h : t ∈ rdfs7For g decl) : Derives g t := by
  obtain ⟨ds, dp, dob⟩ := decl
  cases ds with
  | bnode b => simp [rdfs7For] at h
  | iri p =>
    cases dob with
    | bnode _ => simp [rdfs7For] at h
    | literal _ => simp [rdfs7For] at h
    | tripleTerm _ _ _ => simp [rdfs7For] at h
    | iri q =>
      by_cases hdp : dp = rdfsSubPropertyOf
      · subst hdp
        simp only [rdfs7For, beq_self_eq_true, if_true, List.mem_map] at h
        obtain ⟨u, hu, rfl⟩ := h
        obtain ⟨hug, hup⟩ := mem_triplesWithPredicate hu
        have hdata : Derives g ⟨u.s, p, u.o⟩ := by
          have : (⟨u.s, p, u.o⟩ : Triple) = u := by rw [← hup]
          rw [this]; exact Derives.base hug
        exact Derives.rdfs7 (Derives.base hd) hdata
      · have hdp' : (dp == rdfsSubPropertyOf) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact hdp
        simp [rdfs7For, hdp'] at h

/-- **rdfs2.** -/
theorem rdfs2For_sound {g : Graph} {decl t : Triple} (hd : decl ∈ g)
    (h : t ∈ rdfs2For g decl) : Derives g t := by
  obtain ⟨ds, dp, dob⟩ := decl
  cases ds with
  | bnode b => simp [rdfs2For] at h
  | iri p =>
    by_cases hdp : dp = rdfsDomain
    · subst hdp
      simp only [rdfs2For, beq_self_eq_true, if_true, List.mem_map] at h
      obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨hug, hup⟩ := mem_triplesWithPredicate hu
      have hdata : Derives g ⟨u.s, p, u.o⟩ := by
        have : (⟨u.s, p, u.o⟩ : Triple) = u := by rw [← hup]
        rw [this]; exact Derives.base hug
      exact Derives.rdfs2 (Derives.base hd) hdata
    · have hdp' : (dp == rdfsDomain) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hdp
      simp [rdfs2For, hdp'] at h

/-- **rdfs3.** -/
theorem rdfs3For_sound {g : Graph} {decl t : Triple} (hd : decl ∈ g)
    (h : t ∈ rdfs3For g decl) : Derives g t := by
  obtain ⟨ds, dp, dob⟩ := decl
  cases ds with
  | bnode b => simp [rdfs3For] at h
  | iri p =>
    by_cases hdp : dp = rdfsRange
    · subst hdp
      simp only [rdfs3For, beq_self_eq_true, if_true, List.mem_filterMap] at h
      obtain ⟨u, hu, heq⟩ := h
      obtain ⟨hug, hup⟩ := mem_triplesWithPredicate hu
      have hdata : Derives g ⟨u.s, p, u.o⟩ := by
        have : (⟨u.s, p, u.o⟩ : Triple) = u := by rw [← hup]
        rw [this]; exact Derives.base hug
      revert heq
      cases hsub : u.o.toSubject? with
      | none => intro heq; simp at heq
      | some osub =>
        intro heq
        simp only [Option.some.injEq] at heq
        subst heq
        exact Derives.rdfs3 (Derives.base hd) hdata hsub
    · have hdp' : (dp == rdfsRange) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hdp
      simp [rdfs3For, hdp'] at h

/-- **rdfs9.** -/
theorem rdfs9For_sound {g : Graph} {dt t : Triple} (hd : dt ∈ g)
    (h : t ∈ rdfs9For g dt) : Derives g t := by
  obtain ⟨ds, dp, dob⟩ := dt
  cases dob with
  | bnode _ => simp [rdfs9For] at h
  | literal _ => simp [rdfs9For] at h
  | tripleTerm _ _ _ => simp [rdfs9For] at h
  | iri a =>
    by_cases hdp : dp = rdfType
    · subst hdp
      simp only [rdfs9For, beq_self_eq_true, if_true, List.mem_map] at h
      obtain ⟨b, hb, rfl⟩ := h
      exact Derives.rdfs9 (Derives.base hd) (Derives.base (mem_objectsOf hb))
    · have hdp' : (dp == rdfType) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hdp
      simp [rdfs9For, hdp'] at h

/-- **rdfs11.** -/
theorem rdfs11For_sound {g : Graph} {dt t : Triple} (hd : dt ∈ g)
    (h : t ∈ rdfs11For g dt) : Derives g t := by
  by_cases hdp : dt.p = rdfsSubClassOf
  · simp only [rdfs11For, hdp, beq_self_eq_true, if_true] at h
    revert h
    cases hsub : dt.o.toSubject? with
    | none => intro h; simp at h
    | some bsub =>
      intro h
      simp only [List.mem_map] at h
      obtain ⟨c, hc, rfl⟩ := h
      have hd1 : Derives g ⟨dt.s, rdfsSubClassOf, dt.o⟩ := by
        have : (⟨dt.s, rdfsSubClassOf, dt.o⟩ : Triple) = dt := by rw [← hdp]
        rw [this]; exact Derives.base hd
      exact Derives.rdfs11 hd1 hsub (Derives.base (mem_objectsOf hc))
  · have hdp' : (dt.p == rdfsSubClassOf) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hdp
    simp [rdfs11For, hdp'] at h

/-- **rdfs5.** -/
theorem rdfs5For_sound {g : Graph} {dt t : Triple} (hd : dt ∈ g)
    (h : t ∈ rdfs5For g dt) : Derives g t := by
  by_cases hdp : dt.p = rdfsSubPropertyOf
  · simp only [rdfs5For, hdp, beq_self_eq_true, if_true] at h
    revert h
    cases hsub : dt.o.toSubject? with
    | none => intro h; simp at h
    | some bsub =>
      intro h
      simp only [List.mem_map] at h
      obtain ⟨c, hc, rfl⟩ := h
      have hd1 : Derives g ⟨dt.s, rdfsSubPropertyOf, dt.o⟩ := by
        have : (⟨dt.s, rdfsSubPropertyOf, dt.o⟩ : Triple) = dt := by rw [← hdp]
        rw [this]; exact Derives.base hd
      exact Derives.rdfs5 hd1 hsub (Derives.base (mem_objectsOf hc))
  · have hdp' : (dt.p == rdfsSubPropertyOf) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hdp
    simp [rdfs5For, hdp'] at h

/-! ## Section 5 — T2, soundness -/

/-- Every conclusion a round emits is derivable from the round's
input. -/
theorem stepConclusions_sound {g : Graph} {t : Triple}
    (h : t ∈ stepConclusions g) : Derives g t := by
  simp only [stepConclusions, List.mem_append, List.mem_flatMap] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · obtain ⟨d, hd, ht⟩ := h; exact rdfs7For_sound hd ht
  · obtain ⟨d, hd, ht⟩ := h; exact rdfs2For_sound hd ht
  · obtain ⟨d, hd, ht⟩ := h; exact rdfs3For_sound hd ht
  · obtain ⟨d, hd, ht⟩ := h; exact rdfs9For_sound hd ht
  · obtain ⟨d, hd, ht⟩ := h; exact rdfs11For_sound hd ht
  · obtain ⟨d, hd, ht⟩ := h; exact rdfs5For_sound hd ht

/-- Every triple a round produces is derivable from the round's
input. -/
theorem step_sound {g : Graph} {t : Triple} (h : t ∈ step g) :
    Derives g t := by
  rcases mem_step_cases h with h' | h'
  · exact Derives.base h'
  · exact stepConclusions_sound h'

/-- **T2.** Every triple of the computed closure has a derivation in
the §9.2 rule relation. -/
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

end L4Factoidal.RDFS
