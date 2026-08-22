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

* **T4 completeness at saturation** — `fullComplete_of_saturated`, all
  SIXTEEN constructor cases (base, axiomatic, rdfD2, rdfs2–rdfs13):
  a graph saturated under `fullStep` that contains `g` and contains
  the axiom set contains everything `DerivesFull ax g` derives.
  `fullClosure_complete_of_saturated` is the form for the computed
  closure, and `fullClosure_saturated_or_underfueled` (the fuel
  dichotomy, proved below) discharges its hypothesis for every graph
  whose closure is reached inside the fuel. TWO hypotheses, both
  named: saturation, and `hax` — the axiom set must be present in the
  saturated graph, because `DerivesFull` may quote any axiomatic
  triple and rule-saturation alone does not put it there.
* **T3 monotonicity** — `fullClosure_mono_of_saturated`, conditional
  on the larger closure being saturated, as in `ClosureTheorems.lean`.
  The two closures must carry the SAME datatype map and `rdf:_n`
  slice: the axiom set is what `DerivesFull` quotes from.
* **The two closures compared** —
  `graphMem_fullClosure_of_mem_closure`: `closure g fuel ⊆ fullClosure
  D cmps g` in the engine's membership, via `Derives.toFull`.

The remaining obligation of the stage is the one
`Closure.closureFuelBound` already carries and this module's
`fullClosureFuelBound` inherits: that the stated fuel is always
enough, i.e. the term-universe counting bound. Nothing here depends on
it — T4 is stated against saturation, not against a fuel constant.

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

/-! ## Section 6 — a row's conclusion reaches `fullStepConclusions`

The nine blocks of `fullStepConclusions`, in the order the definition
lists them: the rdfs-core block, then rdfD2, rdfs4a, rdfs4b, rdfs6,
rdfs8, rdfs10, rdfs12, rdfs13. `++` is left-associative, so block `k`
of `n` sits under `n - 1 - k` `Or.inl`s and (unless it is the last)
one `Or.inr`. -/

/-- The rdfs-core block is the first summand. -/
theorem mem_fullStepConclusions_core {g : Graph} {t : Triple}
    (h : t ∈ stepConclusions g) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))

theorem mem_fullStepConclusions_rdfD2 {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfD2For u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨u, hu, h⟩)))))))

theorem mem_fullStepConclusions_rdfs4a {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs4aFor u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨u, hu, h⟩))))))

theorem mem_fullStepConclusions_rdfs4b {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs4bFor u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨u, hu, h⟩)))))

theorem mem_fullStepConclusions_rdfs6 {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs6For u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨u, hu, h⟩))))

theorem mem_fullStepConclusions_rdfs8 {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs8For u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨u, hu, h⟩)))

theorem mem_fullStepConclusions_rdfs10 {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs10For u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨u, hu, h⟩))

theorem mem_fullStepConclusions_rdfs12 {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs12For u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨u, hu, h⟩)

theorem mem_fullStepConclusions_rdfs13 {g : Graph} {u t : Triple}
    (hu : u ∈ g) (h : t ∈ rdfs13For u) : t ∈ fullStepConclusions g := by
  simp only [fullStepConclusions, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨u, hu, h⟩

/-! ## Section 7 — T4, completeness at a saturated graph

The counterpart of `ClosureTheorems.complete_of_saturated`, extended
from six rows to sixteen constructors. Two hypotheses, both named
rather than assumed:

* `hsat : fullStep c = c` — the same saturation hypothesis T4 of
  `ClosureTheorems.lean` carries, and the one
  `fullClosure_saturated_or_underfueled` discharges for every graph
  whose closure is reached inside the fuel;
* `hax : ∀ u ∈ ax, Graph.mem u c = true` — NEW, and forced by the
  `axiomatic` constructor: `DerivesFull` may quote any triple of the
  axiom set, so a graph that is closed under the RULES still fails to
  contain the derivations unless it was SEEDED with the axioms.
  `fullClosure` seeds them (`addAll g (axiomaticTriples D cmps)`),
  which is how `fullClosure_complete_of_saturated` discharges it.

No list-fuel hypothesis appears: unlike the OWL-RL collection rows,
every one of the eight rows this stage added is single-premise and
premise-local (`rdfD2For … rdfs13For` read one triple and return at
most one conclusion), so there is no bounded walk to fuel.

Each case runs the three moves of `ClosureTheorems.lean` § 9: take the
eqb-witnesses the induction hypotheses give, note that in every
position a row MATCHES on the engine equality collapses to equality
(`Subject.eqb_eq` for subjects, `Term.eqb_iri` for an IRI object,
`Term.eqb_eq_of_toSubject` for an object read as a subject), and carry
the remaining slack — always in a row's unexamined payload object —
into the conclusion. For the eight new rows there is no slack at all:
their conclusions are built from the premise's SUBJECT or PREDICATE
plus fixed vocabulary IRIs, so the fired triple is the target on the
nose. -/

/-- **T4 (general form).** A graph `c` that is saturated under the full
rule set, contains `g` and contains the axiom set contains everything
`DerivesFull ax g` derives. Membership is the engine's (`Graph.mem`) —
see the `ClosureTheorems.lean` header for why it must be. -/
theorem fullComplete_of_saturated {ax c : Graph} (hsat : fullStep c = c)
    (hax : ∀ u, u ∈ ax → Graph.mem u c = true)
    {g : Graph} (hg : ∀ u, u ∈ g → Graph.mem u c = true) :
    ∀ {t : Triple}, DerivesFull ax g t → Graph.mem t c = true := by
  have fire : ∀ {t' : Triple}, t' ∈ fullStepConclusions c →
      Graph.mem t' c = true := by
    intro t' h'
    have h'' : Graph.mem t' (fullStep c) = true :=
      graphMem_addAll_of_mem_list _ c h'
    rwa [hsat] at h''
  have fireCore : ∀ {t' : Triple}, t' ∈ stepConclusions c →
      Graph.mem t' c = true := by
    intro t' h'
    exact fire (mem_fullStepConclusions_core h')
  intro t h
  induction h with
  | @base t hm => exact hg _ hm
  | @axiomatic t hm => exact hax _ hm
  | @rdfD2 s p o _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      rw [hp1] at hu1
      have hconcl : (⟨Subject.iri p, rdfType, Term.iri rdfProperty⟩ : Triple) ∈
          rdfD2For ⟨a1, p, c1⟩ := by
        simp [rdfD2For]
      exact fire (mem_fullStepConclusions_rdfD2 hu1 hconcl)
  | @rdfs2 p cls s o _ _ ih1 ih2 =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih1
      obtain ⟨u2, hu2, he2⟩ := exists_of_graphMem ih2
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨a2, b2, c2⟩ := u2
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      obtain ⟨hs2, hp2, ho2⟩ := Triple.eqb_parts he2
      simp only at hs1 hp1 ho1 hs2 hp2 ho2
      subst hs1; subst hp1
      have hconcl : (⟨a2, rdfType, c1⟩ : Triple) ∈
          rdfs2For c ⟨Subject.iri p, rdfsDomain, c1⟩ := by
        simp only [rdfs2For, beq_self_eq_true, if_true, List.mem_map]
        exact ⟨⟨a2, b2, c2⟩, mem_triplesWithPredicate_of hu2 hp2, rfl⟩
      exact graphMem_of_graphMem_eqb
        (fireCore (mem_stepConclusions_rdfs2 hu1 hconcl))
        (Triple.eqb_of_parts hs2 rfl ho1)
  | @rdfs3 p cls s o osub _ _ hsub ih1 ih2 =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih1
      obtain ⟨u2, hu2, he2⟩ := exists_of_graphMem ih2
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨a2, b2, c2⟩ := u2
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      obtain ⟨hs2, hp2, ho2⟩ := Triple.eqb_parts he2
      simp only at hs1 hp1 ho1 hs2 hp2 ho2
      subst hs1; subst hp1
      have hc2 : c2 = o := Term.eqb_eq_of_toSubject ho2 hsub
      subst hc2
      have hconcl : (⟨osub, rdfType, c1⟩ : Triple) ∈
          rdfs3For c ⟨Subject.iri p, rdfsRange, c1⟩ := by
        simp only [rdfs3For, beq_self_eq_true, if_true, List.mem_filterMap]
        exact ⟨⟨a2, b2, c2⟩, mem_triplesWithPredicate_of hu2 hp2, by simp [hsub]⟩
      exact graphMem_of_graphMem_eqb
        (fireCore (mem_stepConclusions_rdfs3 hu1 hconcl))
        (Triple.eqb_of_parts rfl rfl ho1)
  | @rdfs4a s p o _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      rw [hs1] at hu1
      have hconcl : (⟨s, rdfType, Term.iri rdfsResource⟩ : Triple) ∈
          rdfs4aFor ⟨s, b1, c1⟩ := by
        simp [rdfs4aFor]
      exact fire (mem_fullStepConclusions_rdfs4a hu1 hconcl)
  | @rdfs4b s p o osub _ hsub ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      have hc1 : c1 = o := Term.eqb_eq_of_toSubject ho1 hsub
      rw [hc1] at hu1
      have hconcl : (⟨osub, rdfType, Term.iri rdfsResource⟩ : Triple) ∈
          rdfs4bFor ⟨a1, b1, o⟩ := by
        simp [rdfs4bFor, hsub]
      exact fire (mem_fullStepConclusions_rdfs4b hu1 hconcl)
  | @rdfs5 a b bsub cterm _ hsub _ ih1 ih2 =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih1
      obtain ⟨u2, hu2, he2⟩ := exists_of_graphMem ih2
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨a2, b2, c2⟩ := u2
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      obtain ⟨hs2, hp2, ho2⟩ := Triple.eqb_parts he2
      simp only at hs1 hp1 ho1 hs2 hp2 ho2
      subst hp1; subst hs2; subst hp2
      have hc1 : c1 = b := Term.eqb_eq_of_toSubject ho1 hsub
      subst hc1
      have hconcl : (⟨a1, rdfsSubPropertyOf, c2⟩ : Triple) ∈
          rdfs5For c ⟨a1, rdfsSubPropertyOf, c1⟩ := by
        simp only [rdfs5For, beq_self_eq_true, if_true, hsub, List.mem_map]
        exact ⟨c2, mem_objectsOf_of_mem hu2, rfl⟩
      exact graphMem_of_graphMem_eqb
        (fireCore (mem_stepConclusions_rdfs5 hu1 hconcl))
        (Triple.eqb_of_parts hs1 rfl ho2)
  | @rdfs6 x _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      have hc1 : c1 = Term.iri rdfProperty := Term.eqb_iri ho1
      rw [hs1, hp1, hc1] at hu1
      have hconcl : (⟨x, rdfsSubPropertyOf, x.toTerm⟩ : Triple) ∈
          rdfs6For ⟨x, rdfType, Term.iri rdfProperty⟩ := by
        simp [rdfs6For, typedAs]
      exact fire (mem_fullStepConclusions_rdfs6 hu1 hconcl)
  | @rdfs7 p q s o _ _ ih1 ih2 =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih1
      obtain ⟨u2, hu2, he2⟩ := exists_of_graphMem ih2
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨a2, b2, c2⟩ := u2
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      obtain ⟨hs2, hp2, ho2⟩ := Triple.eqb_parts he2
      simp only at hs1 hp1 ho1 hs2 hp2 ho2
      have hc1 : c1 = Term.iri q := Term.eqb_iri ho1
      subst hs1; subst hp1; subst hc1
      have hconcl : (⟨a2, q, c2⟩ : Triple) ∈
          rdfs7For c ⟨Subject.iri p, rdfsSubPropertyOf, Term.iri q⟩ := by
        simp only [rdfs7For, beq_self_eq_true, if_true, List.mem_map]
        exact ⟨⟨a2, b2, c2⟩, mem_triplesWithPredicate_of hu2 hp2, rfl⟩
      exact graphMem_of_graphMem_eqb
        (fireCore (mem_stepConclusions_rdfs7 hu1 hconcl))
        (Triple.eqb_of_parts hs2 rfl ho2)
  | @rdfs8 x _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      have hc1 : c1 = Term.iri rdfsClass := Term.eqb_iri ho1
      rw [hs1, hp1, hc1] at hu1
      have hconcl : (⟨x, rdfsSubClassOf, Term.iri rdfsResource⟩ : Triple) ∈
          rdfs8For ⟨x, rdfType, Term.iri rdfsClass⟩ := by
        simp [rdfs8For, typedAs]
      exact fire (mem_fullStepConclusions_rdfs8 hu1 hconcl)
  | @rdfs9 s a b _ _ ih1 ih2 =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih1
      obtain ⟨u2, hu2, he2⟩ := exists_of_graphMem ih2
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨a2, b2, c2⟩ := u2
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      obtain ⟨hs2, hp2, ho2⟩ := Triple.eqb_parts he2
      simp only at hs1 hp1 ho1 hs2 hp2 ho2
      have hc1 : c1 = Term.iri a := Term.eqb_iri ho1
      subst hp1; subst hc1; subst hs2; subst hp2
      have hconcl : (⟨a1, rdfType, c2⟩ : Triple) ∈
          rdfs9For c ⟨a1, rdfType, Term.iri a⟩ := by
        simp only [rdfs9For, beq_self_eq_true, if_true, List.mem_map]
        exact ⟨c2, mem_objectsOf_of_mem hu2, rfl⟩
      exact graphMem_of_graphMem_eqb
        (fireCore (mem_stepConclusions_rdfs9 hu1 hconcl))
        (Triple.eqb_of_parts hs1 rfl ho2)
  | @rdfs10 x _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      have hc1 : c1 = Term.iri rdfsClass := Term.eqb_iri ho1
      rw [hs1, hp1, hc1] at hu1
      have hconcl : (⟨x, rdfsSubClassOf, x.toTerm⟩ : Triple) ∈
          rdfs10For ⟨x, rdfType, Term.iri rdfsClass⟩ := by
        simp [rdfs10For, typedAs]
      exact fire (mem_fullStepConclusions_rdfs10 hu1 hconcl)
  | @rdfs11 a b bsub cterm _ hsub _ ih1 ih2 =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih1
      obtain ⟨u2, hu2, he2⟩ := exists_of_graphMem ih2
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨a2, b2, c2⟩ := u2
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      obtain ⟨hs2, hp2, ho2⟩ := Triple.eqb_parts he2
      simp only at hs1 hp1 ho1 hs2 hp2 ho2
      subst hp1; subst hs2; subst hp2
      have hc1 : c1 = b := Term.eqb_eq_of_toSubject ho1 hsub
      subst hc1
      have hconcl : (⟨a1, rdfsSubClassOf, c2⟩ : Triple) ∈
          rdfs11For c ⟨a1, rdfsSubClassOf, c1⟩ := by
        simp only [rdfs11For, beq_self_eq_true, if_true, hsub, List.mem_map]
        exact ⟨c2, mem_objectsOf_of_mem hu2, rfl⟩
      exact graphMem_of_graphMem_eqb
        (fireCore (mem_stepConclusions_rdfs11 hu1 hconcl))
        (Triple.eqb_of_parts hs1 rfl ho2)
  | @rdfs12 x _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      have hc1 : c1 = Term.iri rdfsContainerMembershipProperty :=
        Term.eqb_iri ho1
      rw [hs1, hp1, hc1] at hu1
      have hconcl : (⟨x, rdfsSubPropertyOf, Term.iri rdfsMember⟩ : Triple) ∈
          rdfs12For ⟨x, rdfType, Term.iri rdfsContainerMembershipProperty⟩ := by
        simp [rdfs12For, typedAs]
      exact fire (mem_fullStepConclusions_rdfs12 hu1 hconcl)
  | @rdfs13 x _ ih =>
      obtain ⟨u1, hu1, he1⟩ := exists_of_graphMem ih
      obtain ⟨a1, b1, c1⟩ := u1
      obtain ⟨hs1, hp1, ho1⟩ := Triple.eqb_parts he1
      simp only at hs1 hp1 ho1
      have hc1 : c1 = Term.iri rdfsDatatype := Term.eqb_iri ho1
      rw [hs1, hp1, hc1] at hu1
      have hconcl : (⟨x, rdfsSubClassOf, Term.iri rdfsLiteral⟩ : Triple) ∈
          rdfs13For ⟨x, rdfType, Term.iri rdfsDatatype⟩ := by
        simp [rdfs13For, typedAs]
      exact fire (mem_fullStepConclusions_rdfs13 hu1 hconcl)

/-! ## Section 8 — the seeded closure satisfies both hypotheses -/

/-- The loop never loses an engine-membership. (`fullClosureLoop_extensive`
is the same fact for LIST membership; the axioms need this one, because
`addAll` may have kept an eqb-equal variant instead of the triple.) -/
theorem graphMem_fullClosureLoop_of_graphMem (fuel : Nat) :
    ∀ (g : Graph) {t : Triple}, Graph.mem t g = true →
      Graph.mem t (fullClosureLoop g fuel) = true := by
  induction fuel with
  | zero => intro g t h; exact h
  | succ n ih =>
    intro g t h
    simp only [fullClosureLoop]
    split
    · exact h
    · exact ih (fullStep g) (graphMem_addAll_of_graphMem _ g h)

/-- T1 in the engine's membership relation. -/
theorem graphMem_fullClosure_of_mem {D cmps : List WfIri} {g : Graph}
    {t : Triple} (h : t ∈ g) : Graph.mem t (fullClosure D cmps g) = true :=
  graphMem_of_mem (fullClosure_extensive D cmps g h)

/-- The closure holds every axiomatic triple — the `hax` hypothesis of
`fullComplete_of_saturated`, discharged by the seeding step. -/
theorem graphMem_fullClosure_of_mem_axioms {D cmps : List WfIri} {g : Graph}
    {t : Triple} (h : t ∈ axiomaticTriples D cmps) :
    Graph.mem t (fullClosure D cmps g) = true :=
  graphMem_fullClosureLoop_of_graphMem _ _ (graphMem_addAll_of_mem_list _ g h)

/-- **T4.** Everything `g` derives under the full RDF/RDFS rule set and
the §8.2 / §9.3 axioms is in `g`'s computed closure, provided that
closure is saturated (which `fullClosure_saturated_or_underfueled`
turns into "provided the fuel was not exhausted"). -/
theorem fullClosure_complete_of_saturated {D cmps : List WfIri} {g : Graph}
    (hsat : fullStep (fullClosure D cmps g) = fullClosure D cmps g)
    {t : Triple} (h : DerivesFull (axiomaticTriples D cmps) g t) :
    Graph.mem t (fullClosure D cmps g) = true :=
  fullComplete_of_saturated hsat
    (fun _ hu => graphMem_fullClosure_of_mem_axioms hu)
    (fun _ hu => graphMem_fullClosure_of_mem hu) h

/-! ## Section 9 — T3, monotonicity, and the two closures compared

Both are corollaries of T2 + T4, exactly as `closure_mono_of_saturated`
is in `ClosureTheorems.lean`: soundness moves the computed triple into
the derivation relation, `DerivesFull.mono` (or `Derives.toFull`) moves
the derivation, and T4 puts it back into the larger closure. The
saturation hypothesis is where the conditionality comes from — with a
fixed fuel the two runs stop at different rounds, so an unconditional
inclusion is not available. -/

/-- **T3.** If `g ⊆ g'` and `g'`'s closure is saturated, then `g`'s
closure is contained in it. Both closures must use the SAME datatype
map and `rdf:_n` slice: the axiom set is what `DerivesFull` quotes
from, so `g`'s derivations are only admissible against `g'`'s closure
when the two axiom sets agree. -/
theorem fullClosure_mono_of_saturated {D cmps : List WfIri} {g g' : Graph}
    (hsub : ∀ u, u ∈ g → u ∈ g')
    (hsat : fullStep (fullClosure D cmps g') = fullClosure D cmps g')
    {t : Triple} (h : t ∈ fullClosure D cmps g) :
    Graph.mem t (fullClosure D cmps g') = true :=
  fullClosure_complete_of_saturated hsat
    (DerivesFull.mono hsub (fullClosure_sound D cmps g h))

/-- **The two closures compared.** The rdfs-core closure is contained in
the full closure of the same graph (at any rdfs-core fuel), because
every rdfs-core derivation is a full-RDFS derivation
(`Derives.toFull`). This is the membership form of
`closure g fuel ⊆ fullClosure D cmps g`. -/
theorem graphMem_fullClosure_of_mem_closure {D cmps : List WfIri} {g : Graph}
    {fuel : Nat}
    (hsat : fullStep (fullClosure D cmps g) = fullClosure D cmps g)
    {t : Triple} (h : t ∈ closure g fuel) :
    Graph.mem t (fullClosure D cmps g) = true :=
  fullClosure_complete_of_saturated hsat (Derives.toFull (closure_sound fuel g h))

end L4Factoidal.RDFS
