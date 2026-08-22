/-
L4Factoidal.RDFS.FullClosureTheorems — the full RDF/RDFS closure
against its derivation relation, proved natively.

Follows `ClosureTheorems.lean` row for row. What is proved:

* **Embedding** — `Derives.toFull`: every rdfs-core derivation
  (`RdfsCore.Derives`) is a full-RDFS derivation (`DerivesFull`) for
  any axiom set. This is the theorem that RELATES the two rule sets;
  the six rdfs-core constructors map one-to-one onto the six
  same-named `DerivesFull` constructors.
* **Structural** — `DerivesFull.mono`, `DerivesFull.cut`, the two
  facts the soundness induction needs.
* **Per-row soundness** — one lemma per single-premise row (rdfD2,
  rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13): what the row
  emits from a triple of `g` is derivable from `g`. The six rdfs-core
  rows are covered by `ClosureTheorems.stepConclusions_sound` lifted
  through the embedding.
* **T1 extensivity** — `fullClosure_extensive`: the closure contains
  the input graph.
* **T2 soundness** — `fullClosure_sound`: every triple of the computed
  closure has a `DerivesFull (axiomaticTriples D cmps) g` derivation;
  `rdfClosure_sound` likewise for the RDF-regime closure against
  `DerivesFull (rdfAxiomaticTriples cmps) g` (the pure-RDF relation is
  the same inductive with the smaller axiom set — every RDFS row is
  still admissible, so this is a sound over-approximation of RDF
  entailment, never a claim that the RDF regime runs those rows).

NOT proved here: completeness at saturation (T4 of
`ClosureTheorems.lean`). Its proof for the six rdfs-core rows is in
that file; extending it to the eight new rows is the same three-move
argument per row and is the named remaining obligation of this stage.
`fullClosure_saturated_or_underfueled` (the fuel dichotomy) IS proved,
so the hypothesis such a theorem needs is discharged for every graph
whose closure is reached inside the fuel.

Membership conventions are those of `ClosureTheorems.lean` (list
membership in T1/T2). No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.RDFS.ClosureTheorems

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Section 1 — the embedding of rdfs-core -/

/-- **Every rdfs-core derivation is a full-RDFS derivation.** The
constructors correspond by name; the axiom set plays no part. -/
theorem Derives.toFull {ax g : Graph} {t : Triple} (h : Derives g t) :
    DerivesFull ax g t := by
  induction h with
  | base hm => exact DerivesFull.base hm
  | rdfs2 _ _ ih1 ih2 => exact DerivesFull.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact DerivesFull.rdfs3 ih1 ih2 hs
  | rdfs5 _ hs _ ih1 ih2 => exact DerivesFull.rdfs5 ih1 hs ih2
  | rdfs7 _ _ ih1 ih2 => exact DerivesFull.rdfs7 ih1 ih2
  | rdfs9 _ _ ih1 ih2 => exact DerivesFull.rdfs9 ih1 ih2
  | rdfs11 _ hs _ ih1 ih2 => exact DerivesFull.rdfs11 ih1 hs ih2

/-! ## Section 2 — structural properties -/

/-- Monotonicity in the graph (every rule is Horn). -/
theorem DerivesFull.mono {ax g g' : Graph} (hsub : ∀ u, u ∈ g → u ∈ g')
    {t : Triple} (h : DerivesFull ax g t) : DerivesFull ax g' t := by
  induction h with
  | base hm => exact DerivesFull.base (hsub _ hm)
  | axiomatic hm => exact DerivesFull.axiomatic hm
  | rdfD2 _ ih => exact DerivesFull.rdfD2 ih
  | rdfs2 _ _ ih1 ih2 => exact DerivesFull.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact DerivesFull.rdfs3 ih1 ih2 hs
  | rdfs4a _ ih => exact DerivesFull.rdfs4a ih
  | rdfs4b _ hs ih => exact DerivesFull.rdfs4b ih hs
  | rdfs5 _ hs _ ih1 ih2 => exact DerivesFull.rdfs5 ih1 hs ih2
  | rdfs6 _ ih => exact DerivesFull.rdfs6 ih
  | rdfs7 _ _ ih1 ih2 => exact DerivesFull.rdfs7 ih1 ih2
  | rdfs8 _ ih => exact DerivesFull.rdfs8 ih
  | rdfs9 _ _ ih1 ih2 => exact DerivesFull.rdfs9 ih1 ih2
  | rdfs10 _ ih => exact DerivesFull.rdfs10 ih
  | rdfs11 _ hs _ ih1 ih2 => exact DerivesFull.rdfs11 ih1 hs ih2
  | rdfs12 _ ih => exact DerivesFull.rdfs12 ih
  | rdfs13 _ ih => exact DerivesFull.rdfs13 ih

/-- Cut: derivations compose across rounds. -/
theorem DerivesFull.cut {ax g g' : Graph} (hall : ∀ u, u ∈ g' → DerivesFull ax g u)
    {t : Triple} (h : DerivesFull ax g' t) : DerivesFull ax g t := by
  induction h with
  | base hm => exact hall _ hm
  | axiomatic hm => exact DerivesFull.axiomatic hm
  | rdfD2 _ ih => exact DerivesFull.rdfD2 ih
  | rdfs2 _ _ ih1 ih2 => exact DerivesFull.rdfs2 ih1 ih2
  | rdfs3 _ _ hs ih1 ih2 => exact DerivesFull.rdfs3 ih1 ih2 hs
  | rdfs4a _ ih => exact DerivesFull.rdfs4a ih
  | rdfs4b _ hs ih => exact DerivesFull.rdfs4b ih hs
  | rdfs5 _ hs _ ih1 ih2 => exact DerivesFull.rdfs5 ih1 hs ih2
  | rdfs6 _ ih => exact DerivesFull.rdfs6 ih
  | rdfs7 _ _ ih1 ih2 => exact DerivesFull.rdfs7 ih1 ih2
  | rdfs8 _ ih => exact DerivesFull.rdfs8 ih
  | rdfs9 _ _ ih1 ih2 => exact DerivesFull.rdfs9 ih1 ih2
  | rdfs10 _ ih => exact DerivesFull.rdfs10 ih
  | rdfs11 _ hs _ ih1 ih2 => exact DerivesFull.rdfs11 ih1 hs ih2
  | rdfs12 _ ih => exact DerivesFull.rdfs12 ih
  | rdfs13 _ ih => exact DerivesFull.rdfs13 ih

/-! ## Section 3 — one lemma per single-premise row -/

/-- `typedAs t c = true` pins the predicate and the object. -/
theorem typedAs_parts {t : Triple} {c : WfIri} (h : typedAs t c = true) :
    t.p = rdfType ∧ t.o = Term.iri c := by
  simp only [typedAs, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- A triple equals the record of its parts. -/
theorem Triple.eta (t : Triple) : (⟨t.s, t.p, t.o⟩ : Triple) = t := rfl

/-- **rdfD2.** -/
theorem rdfD2For_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfD2For u) : DerivesFull ax g t := by
  simp only [rdfD2For, List.mem_singleton] at h
  subst h
  exact DerivesFull.rdfD2 (DerivesFull.base (t := u) hu)

/-- **rdfs4a.** -/
theorem rdfs4aFor_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs4aFor u) : DerivesFull ax g t := by
  simp only [rdfs4aFor, List.mem_singleton] at h
  subst h
  exact DerivesFull.rdfs4a (DerivesFull.base (t := u) hu)

/-- **rdfs4b.** -/
theorem rdfs4bFor_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs4bFor u) : DerivesFull ax g t := by
  unfold rdfs4bFor at h
  revert h
  cases hsub : u.o.toSubject? with
  | none => intro h; simp at h
  | some os =>
    intro h
    simp only [List.mem_singleton] at h
    subst h
    exact DerivesFull.rdfs4b (DerivesFull.base (t := u) hu) hsub

/-- The shared shape of rdfs6 / rdfs8 / rdfs10 / rdfs12 / rdfs13: a
`typedAs` guard, then one conclusion about the subject. -/
theorem typed_row_sound {ax g : Graph} {u : Triple} {c : WfIri}
    (hu : u ∈ g) (hc : typedAs u c = true) :
    DerivesFull ax g ⟨u.s, rdfType, Term.iri c⟩ := by
  obtain ⟨hp, ho⟩ := typedAs_parts hc
  have : (⟨u.s, rdfType, Term.iri c⟩ : Triple) = u := by
    rw [← hp, ← ho]
  rw [this]; exact DerivesFull.base hu

/-- **rdfs6.** -/
theorem rdfs6For_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs6For u) : DerivesFull ax g t := by
  unfold rdfs6For at h
  split at h
  · rename_i hc
    simp only [List.mem_singleton] at h; subst h
    exact DerivesFull.rdfs6 (typed_row_sound hu hc)
  · simp at h

/-- **rdfs8.** -/
theorem rdfs8For_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs8For u) : DerivesFull ax g t := by
  unfold rdfs8For at h
  split at h
  · rename_i hc
    simp only [List.mem_singleton] at h; subst h
    exact DerivesFull.rdfs8 (typed_row_sound hu hc)
  · simp at h

/-- **rdfs10.** -/
theorem rdfs10For_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs10For u) : DerivesFull ax g t := by
  unfold rdfs10For at h
  split at h
  · rename_i hc
    simp only [List.mem_singleton] at h; subst h
    exact DerivesFull.rdfs10 (typed_row_sound hu hc)
  · simp at h

/-- **rdfs12.** -/
theorem rdfs12For_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs12For u) : DerivesFull ax g t := by
  unfold rdfs12For at h
  split at h
  · rename_i hc
    simp only [List.mem_singleton] at h; subst h
    exact DerivesFull.rdfs12 (typed_row_sound hu hc)
  · simp at h

/-- **rdfs13.** -/
theorem rdfs13For_sound {ax g : Graph} {u t : Triple} (hu : u ∈ g)
    (h : t ∈ rdfs13For u) : DerivesFull ax g t := by
  unfold rdfs13For at h
  split at h
  · rename_i hc
    simp only [List.mem_singleton] at h; subst h
    exact DerivesFull.rdfs13 (typed_row_sound hu hc)
  · simp at h

/-! ## Section 4 — T2, soundness of a round and of the loop -/

/-- Every conclusion of a full round is derivable from the round's
input. The rdfs-core block goes through the embedding. -/
theorem fullStepConclusions_sound {ax g : Graph} {t : Triple}
    (h : t ∈ fullStepConclusions g) : DerivesFull ax g t := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact Derives.toFull (stepConclusions_sound h)
  · obtain ⟨u, hu, ht⟩ := h; exact rdfD2For_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs4aFor_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs4bFor_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs6For_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs8For_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs10For_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs12For_sound hu ht
  · obtain ⟨u, hu, ht⟩ := h; exact rdfs13For_sound hu ht

/-- One full round never loses a triple. -/
theorem mem_fullStep_of_mem {g : Graph} {t : Triple} (h : t ∈ g) : t ∈ fullStep g :=
  mem_addAll_of_mem _ g h

/-- One full round adds nothing but rule conclusions. -/
theorem mem_fullStep_cases {g : Graph} {t : Triple} (h : t ∈ fullStep g) :
    t ∈ g ∨ t ∈ fullStepConclusions g :=
  mem_addAll_cases _ g h

/-- Every triple a full round produces is derivable from its input. -/
theorem fullStep_sound {ax g : Graph} {t : Triple} (h : t ∈ fullStep g) :
    DerivesFull ax g t := by
  rcases mem_fullStep_cases h with h' | h'
  · exact DerivesFull.base h'
  · exact fullStepConclusions_sound h'

/-- The loop is sound at every fuel. -/
theorem fullClosureLoop_sound (ax : Graph) (fuel : Nat) :
    ∀ (g : Graph) {t : Triple}, t ∈ fullClosureLoop g fuel → DerivesFull ax g t := by
  induction fuel with
  | zero => intro g t h; exact DerivesFull.base h
  | succ n ih =>
    intro g t h
    simp only [fullClosureLoop] at h
    split at h
    · exact DerivesFull.base h
    · exact DerivesFull.cut (fun _ hu => fullStep_sound hu) (ih (fullStep g) h)

/-- The loop is extensive at every fuel. -/
theorem fullClosureLoop_extensive (fuel : Nat) :
    ∀ (g : Graph) {t : Triple}, t ∈ g → t ∈ fullClosureLoop g fuel := by
  induction fuel with
  | zero => intro g t h; exact h
  | succ n ih =>
    intro g t h
    simp only [fullClosureLoop]
    split
    · exact h
    · exact ih (fullStep g) (mem_fullStep_of_mem h)

/-- Seeding: a triple of `addAll g ax` is a triple of `g` or an axiom,
hence derivable. -/
theorem seeded_sound {ax g : Graph} {t : Triple} (h : t ∈ addAll g ax) :
    DerivesFull ax g t := by
  rcases mem_addAll_cases ax g h with h' | h'
  · exact DerivesFull.base h'
  · exact DerivesFull.axiomatic h'

/-- **T1.** The RDFS-regime closure contains the input graph. -/
theorem fullClosure_extensive (D cmps : List WfIri) (g : Graph) {t : Triple}
    (h : t ∈ g) : t ∈ fullClosure D cmps g :=
  fullClosureLoop_extensive _ _ (mem_addAll_of_mem _ g h)

/-- **T2.** Every triple of the RDFS-regime closure is derivable from
`g` and the axiomatic triples by the §8.1 / §9.2 rules. -/
theorem fullClosure_sound (D cmps : List WfIri) (g : Graph) {t : Triple}
    (h : t ∈ fullClosure D cmps g) :
    DerivesFull (axiomaticTriples D cmps) g t :=
  DerivesFull.cut (fun _ hu => seeded_sound hu) (fullClosureLoop_sound _ _ _ h)

/-- **T1 for the RDF regime.** -/
theorem rdfClosure_extensive (cmps : List WfIri) (g : Graph) {t : Triple}
    (h : t ∈ g) : t ∈ rdfClosure cmps g :=
  mem_addAll_of_mem _ _ (mem_addAll_of_mem _ g h)

/-- **T2 for the RDF regime**: derivable from `g` and the §8.2 axioms
(by rdfD2 — the only rule the closure runs, though the relation admits
the RDFS rows too; see the module header). -/
theorem rdfClosure_sound (cmps : List WfIri) (g : Graph) {t : Triple}
    (h : t ∈ rdfClosure cmps g) :
    DerivesFull (rdfAxiomaticTriples cmps) g t := by
  unfold rdfClosure at h
  rcases mem_addAll_cases _ _ h with h' | h'
  · exact seeded_sound h'
  · simp only [List.mem_flatMap] at h'
    obtain ⟨u, hu, ht⟩ := h'
    exact DerivesFull.cut (fun _ hv => seeded_sound hv) (rdfD2For_sound hu ht)

/-! ## Section 5 — the fuel dichotomy -/

/-- For every graph and every fuel: either the full closure is
saturated, or it grew by at least one triple per unit of fuel. -/
theorem fullClosure_saturated_or_underfueled (fuel : Nat) :
    ∀ (g : Graph), fullStep (fullClosureLoop g fuel) = fullClosureLoop g fuel ∨
      g.length + fuel ≤ (fullClosureLoop g fuel).length := by
  induction fuel with
  | zero => intro g; exact Or.inr (by simp [fullClosureLoop])
  | succ n ih =>
    intro g
    simp only [fullClosureLoop]
    split
    · rename_i heq
      exact Or.inl (addAll_eq_of_length_eq _ g heq)
    · rename_i hne
      rcases ih (fullStep g) with h | h
      · exact Or.inl h
      · have h1 : g.length ≤ (fullStep g).length := length_le_addAll _ g
        exact Or.inr (by omega)

end L4Factoidal.RDFS
