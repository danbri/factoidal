/-
L4Factoidal.RDF.IsomorphismTheorems — what is PROVED about the
isomorphism decision procedure of `RDF.Isomorphism`.

Two results, in increasing order of interest:

  * `Graph.isomorphic?_refl` / `Dataset.isomorphic?_refl` — every graph
    (dataset) is isomorphic to itself according to the procedure. Not
    free: it says the identity fast path really is accepted by the
    certificate, which pins down `bnodes` (duplicate-free),
    `renameBnodes` (identity-preserving) and `setEqB` (reflexive) all
    at once.

  * `Graph.isomorphic?_sound` / `Dataset.isomorphic?_sound` —
    **SOUNDNESS**: if the procedure answers `true`, the two graphs
    really are isomorphic in the sense of RDF 1.1 Concepts §3.6. The
    mapping the search returns is the witness, and every clause of the
    specification is discharged from the corresponding conjunct of the
    checked certificate. Nothing about the SEARCH is assumed — it may
    return any mapping at all; `Graph.isomorphismMap?` re-checks what
    comes back, and only the check is trusted. So the search can be
    replaced, pruned harder, or reordered without touching this proof.

The checker-correctness sub-lemmas are stated separately and used by
the soundness proofs:

  * `Graph.setEq_of_setEqB` — `setEqB g1 g2 = true` gives containment
    both ways, so `g1.renameBnodes f` and `g2` denote one triple set;
  * `bijectiveCert_inj` / `bijectiveCert_onto` — the checked pairing is
    injective on `g1`'s blank nodes and covers `g2`'s.

SYMMETRY is exercised on fixtures in `IsomorphismTests.lean` (each
`isomorphic?` case is asserted in both directions) but is NOT proved
here. It is true of the SPECIFICATION and should be provable there
(invert the bijection); it is not obviously true of the PROCEDURE,
whose search order and identity fast path are asymmetric, so proving
`isomorphic? g1 g2 = isomorphic? g2 g1` would mean proving
completeness first. Recorded, not claimed.

COMPLETENESS IS NOT PROVED, and is not claimed anywhere. The converse
— `Graph.Isomorphic g1 g2 → g1.isomorphic? g2 = true` — is false as
stated for two reasons, both deliberate and both recorded in
`Isomorphism.lean`:

  1. Two budgets refuse: `isoBnodeBudget` above 128 blank nodes, and
     `isoWorkBudget` above 100000 candidate assignments tried. On a
     trip the procedure answers `false` — reported as
     `IsoOutcome.budgetExceeded`, never as a bare `false` — on
     isomorphic pairs it declines to finish searching.
  2. Signature pruning writes literals out lexically, so two literals
     that `Literal.eqb` equates only through `rdf:XMLLiteral`
     canonicalisation can get different signature keys, and their
     blank-node neighbours are then never paired.

A completeness theorem would have to be conditional on the blank-node
count and on the absence of `rdf:XMLLiteral` literals. That is a
worthwhile later target; it is not stated here because a conditional
theorem nobody has proved is worth less than a plain comment.

No `sorry`, no `axiom`, no `native_decide`. Axiom audit at the foot of
the file.
-/
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.RDF

/-! ## `List.contains` ↔ `∈` bridges

`bijectiveCert` is a Bool test, so it speaks `List.contains`; the
specification speaks `∈`. These two one-liners carry each proof across
that seam. -/

theorem mem_of_contains {l : List BNodeId} {b : BNodeId}
    (h : l.contains b = true) : b ∈ l := by simpa using h

theorem contains_of_mem {l : List BNodeId} {b : BNodeId}
    (h : b ∈ l) : l.contains b = true := by simpa using h

/-- The same fact at any lawfully-compared element type — used for the
`Subject`-valued graph names of RDF 1.1 Concepts §4. -/
theorem contains_of_mem' {α : Type} [BEq α] [LawfulBEq α] {l : List α} {b : α}
    (h : b ∈ l) : l.contains b = true := by simpa using h

/-! ## Membership and set equality -/

/-- A triple that is literally in the list is a member under the
engine triple equality. (The one fact about `Graph.mem` this file
needs that `Graph.lean` does not already state; it follows from
`Graph.lean`'s `Triple.eqb_refl`.) -/
theorem Graph.mem_of_mem_list {g : Graph} {t : Triple} (h : t ∈ g) :
    g.mem t = true := by
  induction g with
  | nil => cases h
  | cons hd tl ih =>
    rcases List.mem_cons.1 h with h1 | h2
    · rw [h1]; simp [Graph.mem]
    · simp [Graph.mem, ih h2]

/-- `subsetB` decides `SubsetOf` in the direction that matters. -/
theorem Graph.subsetOf_of_subsetB {g1 g2 : Graph}
    (h : Graph.subsetB g1 g2 = true) : Graph.SubsetOf g1 g2 :=
  fun t ht => (List.all_eq_true.1 h) t ht

/-- CHECKER CORRECTNESS for the triple-set half of the certificate: a
`true` from `setEqB` really does give containment both ways. -/
theorem Graph.setEq_of_setEqB {g1 g2 : Graph}
    (h : Graph.setEqB g1 g2 = true) : Graph.SetEq g1 g2 := by
  unfold Graph.setEqB at h
  rw [Bool.and_eq_true] at h
  exact ⟨Graph.subsetOf_of_subsetB h.1, Graph.subsetOf_of_subsetB h.2⟩

theorem Graph.subsetB_self (g : Graph) : Graph.subsetB g g = true :=
  List.all_eq_true.2 (fun _ ht => Graph.mem_of_mem_list ht)

theorem Graph.setEqB_self (g : Graph) : Graph.setEqB g g = true := by
  simp [Graph.setEqB, Graph.subsetB_self]

/-! ## Renaming by the identity -/

theorem Subject.renameBnodes_id {f : BNodeId → BNodeId}
    (hf : ∀ b, f b = b) (s : Subject) : s.renameBnodes f = s := by
  cases s <;> simp [Subject.renameBnodes, hf]

theorem Term.renameBnodes_id {f : BNodeId → BNodeId}
    (hf : ∀ b, f b = b) (t : Term) : t.renameBnodes f = t := by
  induction t with
  | iri i => simp [Term.renameBnodes]
  | bnode b => simp [Term.renameBnodes, hf]
  | literal l => simp [Term.renameBnodes]
  | tripleTerm s p o ih =>
    simp [Term.renameBnodes, Subject.renameBnodes_id hf, ih]

theorem Triple.renameBnodes_id {f : BNodeId → BNodeId}
    (hf : ∀ b, f b = b) (t : Triple) : t.renameBnodes f = t := by
  simp [Triple.renameBnodes, Subject.renameBnodes_id hf,
        Term.renameBnodes_id hf]

theorem Graph.renameBnodes_id {f : BNodeId → BNodeId}
    (hf : ∀ b, f b = b) (g : Graph) : g.renameBnodes f = g := by
  have h : Triple.renameBnodes f = fun t => t := by
    funext t; exact Triple.renameBnodes_id hf t
  simp [Graph.renameBnodes, h]

/-! ## Duplicate-free label lists -/

theorem noDupLabels_dedupLabels (l : List BNodeId) :
    noDupLabels (dedupLabels l) = true := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : b ∈ dedupLabels bs
    · simpa [dedupLabels, h] using ih
    · simp [dedupLabels, h, noDupLabels, ih]

/-- The blank nodes of a graph are listed without repetition. -/
theorem noDupLabels_bnodes (g : Graph) : noDupLabels g.bnodes = true :=
  noDupLabels_dedupLabels _

theorem noDupLabels_dsBnodes (ds : Dataset) : noDupLabels ds.bnodes = true :=
  noDupLabels_dedupLabels _

/-- In a list whose keys are duplicate-free, an element is determined
by its key. -/
theorem uniq_of_nodup_key {α : Type} (key : α → String) {l : List α}
    (h : noDupLabels (l.map key) = true) {a b : α}
    (h1 : a ∈ l) (h2 : b ∈ l) (he : key a = key b) : a = b := by
  induction l with
  | nil => cases h1
  | cons x t ih =>
    simp only [List.map_cons, noDupLabels, Bool.and_eq_true,
               Bool.not_eq_true'] at h
    obtain ⟨hcont, htail⟩ := h
    rcases List.mem_cons.1 h1 with e1 | m1 <;> rcases List.mem_cons.1 h2 with e2 | m2
    · rw [e1, e2]
    · exfalso
      have hin : key b ∈ t.map key := List.mem_map_of_mem m2
      rw [← he, e1] at hin
      exact absurd (contains_of_mem hin) (by simpa using hcont)
    · exfalso
      have hin : key a ∈ t.map key := List.mem_map_of_mem m1
      rw [he, e2] at hin
      exact absurd (contains_of_mem hin) (by simpa using hcont)
    · exact ih htail m1 m2

/-- The `noDupNames` counterpart: in a list of named graphs whose names
are duplicate-free, the NAME determines the entry. This is exactly the
RDF 1.1 Concepts §4 well-formedness condition (at most one graph per
name) turned into the uniqueness fact `Dataset.lookupNamed` needs. -/
theorem uniq_of_nodup_name {l : List NamedGraph}
    (h : noDupNames (l.map (fun ng => ng.name)) = true) {a b : NamedGraph}
    (h1 : a ∈ l) (h2 : b ∈ l) (he : a.name = b.name) : a = b := by
  induction l with
  | nil => cases h1
  | cons x t ih =>
    simp only [List.map_cons, noDupNames, Bool.and_eq_true,
               Bool.not_eq_true'] at h
    obtain ⟨hcont, htail⟩ := h
    rcases List.mem_cons.1 h1 with e1 | m1 <;> rcases List.mem_cons.1 h2 with e2 | m2
    · rw [e1, e2]
    · exfalso
      have hin : b.name ∈ t.map (fun ng => ng.name) := List.mem_map_of_mem m2
      rw [← he, e1] at hin
      exact absurd (contains_of_mem' hin) (by simpa using hcont)
    · exfalso
      have hin : a.name ∈ t.map (fun ng => ng.name) := List.mem_map_of_mem m1
      rw [he, e2] at hin
      exact absurd (contains_of_mem' hin) (by simpa using hcont)
    · exact ih htail m1 m2

/-- Pairs are determined by their first (or second) component when
that component list is duplicate-free. -/
theorem pairs_uniq (proj : BNodeId × BNodeId → BNodeId)
    {m : List (BNodeId × BNodeId)} (h : noDupLabels (m.map proj) = true)
    {p1 p2 : BNodeId × BNodeId} (h1 : p1 ∈ m) (h2 : p2 ∈ m)
    (he : proj p1 = proj p2) : p1 = p2 :=
  uniq_of_nodup_key proj h h1 h2 he

/-! ## Association-list mappings -/

/-- The identity association list denotes the identity function — on
EVERY label, not only the ones it lists (`mapWith` falls through to
its argument). -/
theorem mapWith_diag (bs : List BNodeId) (b : BNodeId) :
    mapWith (bs.map (fun x => (x, x))) b = b := by
  have key : ∀ p : BNodeId × BNodeId,
      (bs.map (fun x => (x, x))).find? (fun q => q.1 == b) = some p →
      p.2 = b := by
    intro p hfind
    have hp : p ∈ bs.map (fun x => (x, x)) := List.mem_of_find?_eq_some hfind
    have hq := List.find?_some hfind
    obtain ⟨x, _, hx⟩ := List.mem_map.1 hp
    subst hx
    simpa using hq
  unfold mapWith
  cases hc : (bs.map (fun x => (x, x))).find? (fun q => q.1 == b) with
  | none => simp
  | some p => simp [key p hc]

theorem mapDomain_diag (bs : List BNodeId) :
    mapDomain (bs.map (fun x => (x, x))) = bs := by
  simp [mapDomain, List.map_map, Function.comp_def]

theorem mapImage_diag (bs : List BNodeId) :
    mapImage (bs.map (fun x => (x, x))) = bs := by
  simp [mapImage, List.map_map, Function.comp_def]

/-- If a label is in the domain of `m`, the lookup succeeds. -/
theorem find?_of_mem_domain {m : List (BNodeId × BNodeId)} {b : BNodeId}
    (h : b ∈ mapDomain m) : ∃ p, m.find? (fun q => q.1 == b) = some p := by
  induction m with
  | nil => simp [mapDomain] at h
  | cons a t ih =>
    by_cases hab : (a.1 == b) = true
    · exact ⟨a, by simp [List.find?, hab]⟩
    · have h' : b ∈ mapDomain t := by
        simp only [mapDomain, List.map_cons, List.mem_cons] at h
        rcases h with he | ht
        · exact absurd (by simp [he]) hab
        · simpa [mapDomain] using ht
      obtain ⟨p, hp⟩ := ih h'
      exact ⟨p, by simp [List.find?, hab, hp]⟩

/-- `mapWith` reads back the pair it was given, provided the domain
labels are duplicate-free. -/
theorem mapWith_of_mem {m : List (BNodeId × BNodeId)}
    (hnd : noDupLabels (mapDomain m) = true) {p : BNodeId × BNodeId}
    (hp : p ∈ m) : mapWith m p.1 = p.2 := by
  obtain ⟨q, hq⟩ := find?_of_mem_domain (m := m) (b := p.1)
    (List.mem_map_of_mem hp)
  have hqm : q ∈ m := List.mem_of_find?_eq_some hq
  have hq1 : q.1 = p.1 := by have := List.find?_some hq; simpa using this
  have hqp : q = p := pairs_uniq Prod.fst hnd hqm hp hq1
  simp [mapWith, hq, hqp]

/-! ## The certificate implies the specification -/

/-- CHECKER CORRECTNESS, injectivity clause. -/
theorem bijectiveCert_inj {m : List (BNodeId × BNodeId)} {bs1 bs2 : List BNodeId}
    (h : bijectiveCert m bs1 bs2 = true) :
    ∀ b1 ∈ bs1, ∀ b2 ∈ bs1, mapWith m b1 = mapWith m b2 → b1 = b2 := by
  unfold bijectiveCert at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, hImgND⟩, _⟩, hTotal⟩, _⟩ := h
  intro b1 hb1 b2 hb2 heq
  obtain ⟨p1, hp1⟩ := find?_of_mem_domain
    (mem_of_contains ((List.all_eq_true.1 hTotal) b1 hb1))
  obtain ⟨p2, hp2⟩ := find?_of_mem_domain
    (mem_of_contains ((List.all_eq_true.1 hTotal) b2 hb2))
  have m1 : p1 ∈ m := List.mem_of_find?_eq_some hp1
  have m2 : p2 ∈ m := List.mem_of_find?_eq_some hp2
  have k1 : p1.1 = b1 := by have := List.find?_some hp1; simpa using this
  have k2 : p2.1 = b2 := by have := List.find?_some hp2; simpa using this
  have v1 : mapWith m b1 = p1.2 := by simp [mapWith, hp1]
  have v2 : mapWith m b2 = p2.2 := by simp [mapWith, hp2]
  have : p1 = p2 := pairs_uniq Prod.snd hImgND m1 m2 (by rw [← v1, ← v2, heq])
  rw [← k1, ← k2, this]

/-- CHECKER CORRECTNESS, surjectivity clause. -/
theorem bijectiveCert_onto {m : List (BNodeId × BNodeId)} {bs1 bs2 : List BNodeId}
    (h : bijectiveCert m bs1 bs2 = true) :
    ∀ b ∈ bs2, ∃ b', b' ∈ bs1 ∧ mapWith m b' = b := by
  unfold bijectiveCert at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hDomND, _⟩, hDomIn⟩, _⟩, hCover⟩ := h
  intro b hb
  have hmem : b ∈ mapImage m :=
    mem_of_contains ((List.all_eq_true.1 hCover) b hb)
  obtain ⟨p, hp, hpb⟩ := List.mem_map.1 hmem
  exact ⟨p.1, mem_of_contains ((List.all_eq_true.1 hDomIn) p hp),
         by rw [mapWith_of_mem hDomND hp]; exact hpb⟩

/-! ## Soundness (graphs) -/

/-- The procedure only ever returns a CERTIFIED mapping. Immediate:
`Graph.isomorphismMap?` guards its `some` with exactly this check,
whatever the search produced. -/
theorem Graph.isomorphismMap?_cert {g1 g2 : Graph}
    {m : List (BNodeId × BNodeId)} (h : g1.isomorphismMap? g2 = some m) :
    Graph.isoCert m g1 g2 g1.bnodes g2.bnodes = true := by
  unfold Graph.isomorphismMap? at h
  cases hs : Graph.isoSearch g1 g2 with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some m' =>
    rw [hs] at h
    by_cases hc : Graph.isoCert m' g1 g2 g1.bnodes g2.bnodes = true
    · simp only [hc, if_true] at h
      have hmm : m' = m := by injection h
      rw [← hmm]; exact hc
    · simp only [Bool.not_eq_true] at hc
      simp [hc] at h

/-- **SOUNDNESS (graphs).** A `true` answer is backed by a real
blank-node bijection: RDF 1.1 Concepts §3.6 holds of the two graphs,
witnessed by the mapping the procedure returned. -/
theorem Graph.isomorphic?_sound {g1 g2 : Graph}
    (h : g1.isomorphic? g2 = true) : Graph.Isomorphic g1 g2 := by
  unfold Graph.isomorphic? at h
  cases hm : g1.isomorphismMap? g2 with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
    have hcert := Graph.isomorphismMap?_cert hm
    unfold Graph.isoCert at hcert
    rw [Bool.and_eq_true] at hcert
    exact ⟨mapWith m,
           bijectiveCert_inj hcert.1,
           bijectiveCert_onto hcert.1,
           Graph.setEq_of_setEqB hcert.2⟩

/-! ## Reflexivity (graphs) -/

theorem bijectiveCert_diag {bs : List BNodeId} (hnd : noDupLabels bs = true) :
    bijectiveCert (bs.map (fun x => (x, x))) bs bs = true := by
  simp [bijectiveCert, mapDomain_diag, mapImage_diag, hnd]

theorem Graph.isoCert_idMapping (g : Graph) :
    Graph.isoCert g.idMapping g g g.bnodes g.bnodes = true := by
  have hid : g.renameBnodes (mapWith g.idMapping) = g :=
    Graph.renameBnodes_id (fun b => mapWith_diag g.bnodes b) g
  have hbij : bijectiveCert g.idMapping g.bnodes g.bnodes = true :=
    bijectiveCert_diag (noDupLabels_bnodes g)
  simp [Graph.isoCert, hbij, hid, Graph.setEqB_self]

/-- **REFLEXIVITY (graphs).** Every graph is isomorphic to itself, via
the identity fast path. -/
theorem Graph.isomorphic?_refl (g : Graph) : g.isomorphic? g = true := by
  have hcert := Graph.isoCert_idMapping g
  have hsearch : Graph.isoSearch g g = some g.idMapping := by
    unfold Graph.isoSearch; rw [if_pos hcert]
  simp [Graph.isomorphic?, Graph.isomorphismMap?, hsearch, hcert]

/-- The three-way outcome agrees with the Bool on the reflexive
case. -/
theorem Graph.isomorphicOutcome_refl (g : Graph) :
    Graph.isomorphicOutcome g g = IsoOutcome.equal := by
  have h : (g.isomorphismMap? g).isSome = true := Graph.isomorphic?_refl g
  simp [Graph.isomorphicOutcome, h]

/-! ## Datasets -/

/-- A dataset that LISTS a graph under a name looks that name up
successfully. (Weaker than `lookupNamed_self` below — it does not say
WHICH graph comes back — but it needs no duplicate-free hypothesis,
which is what the onto direction of name matching wants.) -/
theorem Dataset.lookupNamed_isSome_of_mem {ds : Dataset} {n : Subject}
    {ng : NamedGraph} (h : ng ∈ ds.named) (hn : ng.name = n) :
    (ds.lookupNamed n).isSome = true := by
  unfold Dataset.lookupNamed
  cases hf : ds.named.find? (fun x => x.name == n) with
  | none   => exact absurd (List.find?_eq_none.1 hf ng h) (by simp [hn])
  | some _ => rfl

theorem Dataset.setEq_of_checkMapping {m : List (BNodeId × BNodeId)}
    {ds1 ds2 : Dataset} (h : Dataset.checkMapping m ds1 ds2 = true) :
    Dataset.SetEq (ds1.renameBnodes (mapWith m)) ds2 := by
  unfold Dataset.checkMapping Dataset.namesMatchB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hdef, hnamed⟩, _, hback⟩ := h
  refine ⟨Graph.setEq_of_setEqB hdef, ?_, ?_⟩
  · intro ng hng
    obtain ⟨ng0, hng0, hEq⟩ := List.mem_map.1 hng
    subst hEq
    have hstep := (List.all_eq_true.1 hnamed) ng0 hng0
    cases hlook : ds2.lookupNamed (ng0.name.renameBnodes (mapWith m)) with
    | none => rw [hlook] at hstep; simp at hstep
    | some g2 =>
      rw [hlook] at hstep
      simp only at hstep
      exact ⟨g2, rfl, Graph.setEq_of_setEqB hstep⟩
  · intro ng hng
    have hb := (List.all_eq_true.1 hback) ng hng
    obtain ⟨ng1, hng1, hname⟩ := List.any_eq_true.1 hb
    have hmem : ({ name := ng1.name.renameBnodes (mapWith m),
                   graph := ng1.graph.renameBnodes (mapWith m) } : NamedGraph)
                  ∈ (ds1.renameBnodes (mapWith m)).named :=
      List.mem_map_of_mem hng1
    exact Dataset.lookupNamed_isSome_of_mem hmem (by simpa using hname)

theorem Dataset.isomorphismMap?_cert {ds1 ds2 : Dataset}
    {m : List (BNodeId × BNodeId)} (h : ds1.isomorphismMap? ds2 = some m) :
    Dataset.isoCert m ds1 ds2 ds1.bnodes ds2.bnodes = true := by
  unfold Dataset.isomorphismMap? at h
  cases hs : Dataset.isoSearch ds1 ds2 with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some m' =>
    rw [hs] at h
    by_cases hc : Dataset.isoCert m' ds1 ds2 ds1.bnodes ds2.bnodes = true
    · simp only [hc, if_true] at h
      have hmm : m' = m := by injection h
      rw [← hmm]; exact hc
    · simp only [Bool.not_eq_true] at hc
      simp [hc] at h

/-- **SOUNDNESS (datasets).** One blank-node bijection, dataset-wide,
carrying the default graph and every named graph onto their
same-named counterparts. -/
theorem Dataset.isomorphic?_sound {ds1 ds2 : Dataset}
    (h : ds1.isomorphic? ds2 = true) : Dataset.Isomorphic ds1 ds2 := by
  unfold Dataset.isomorphic? at h
  cases hm : ds1.isomorphismMap? ds2 with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
    have hcert := Dataset.isomorphismMap?_cert hm
    unfold Dataset.isoCert at hcert
    rw [Bool.and_eq_true] at hcert
    exact ⟨mapWith m,
           bijectiveCert_inj hcert.1,
           bijectiveCert_onto hcert.1,
           Dataset.setEq_of_checkMapping hcert.2⟩

/-! ### Reflexivity for datasets

Conditional, and the condition is real: `Dataset.lookupNamed` returns
the FIRST graph carrying a name, so a `Dataset` value that lists two
different graphs under one name is not equal to itself under
name-matching. RDF 1.1 Concepts §4 gives a dataset at most one graph
per name, so the hypothesis is exactly that the value is a
well-formed dataset — but the Lean type does not enforce it, so the
theorem carries it explicitly rather than pretending. -/

theorem Dataset.lookupNamed_self {ds : Dataset}
    (hnd : ds.namesNoDup = true) {ng : NamedGraph} (h : ng ∈ ds.named) :
    ds.lookupNamed ng.name = some ng.graph := by
  unfold Dataset.lookupNamed
  cases hf : ds.named.find? (fun x => x.name == ng.name) with
  | none =>
    exact absurd (List.find?_eq_none.1 hf ng h) (by simp)
  | some ng' =>
    have hm : ng' ∈ ds.named := List.mem_of_find?_eq_some hf
    have hn : ng'.name = ng.name := by
      have := List.find?_some hf; simpa using this
    have hnd' : noDupNames (ds.named.map (fun x => x.name)) = true := hnd
    have : ng' = ng := uniq_of_nodup_name hnd' hm h hn
    simp [this]

theorem Dataset.isoCert_idMapping (ds : Dataset)
    (hnd : ds.namesNoDup = true) :
    Dataset.isoCert ds.idMapping ds ds ds.bnodes ds.bnodes = true := by
  have hidf : ∀ b, mapWith ds.idMapping b = b := fun b => mapWith_diag ds.bnodes b
  have hbij : bijectiveCert ds.idMapping ds.bnodes ds.bnodes = true :=
    bijectiveCert_diag (noDupLabels_dsBnodes ds)
  have hdef : Graph.setEqB (ds.default.renameBnodes (mapWith ds.idMapping))
                ds.default = true := by
    rw [Graph.renameBnodes_id hidf]; exact Graph.setEqB_self _
  have hidn : ∀ n : Subject, n.renameBnodes (mapWith ds.idMapping) = n :=
    fun n => Subject.renameBnodes_id hidf n
  have hnamed : ds.named.all (fun ng =>
      match ds.lookupNamed (ng.name.renameBnodes (mapWith ds.idMapping)) with
      | some g2 => Graph.setEqB (ng.graph.renameBnodes (mapWith ds.idMapping)) g2
      | none    => false) = true := by
    apply List.all_eq_true.2
    intro ng hng
    rw [hidn ng.name, Dataset.lookupNamed_self hnd hng]
    simp only
    rw [Graph.renameBnodes_id hidf]
    exact Graph.setEqB_self _
  have hmatch : Dataset.namesMatchB ds.idMapping ds ds = true := by
    have hs : ds.named.all (fun ng =>
        (ds.lookupNamed (ng.name.renameBnodes (mapWith ds.idMapping))).isSome) = true := by
      apply List.all_eq_true.2
      intro ng hng
      rw [hidn ng.name, Dataset.lookupNamed_self hnd hng]
      rfl
    have hb : ds.named.all (fun ng2 =>
        ds.named.any (fun ng1 =>
          ng1.name.renameBnodes (mapWith ds.idMapping) == ng2.name)) = true := by
      apply List.all_eq_true.2
      intro ng2 hng2
      exact List.any_eq_true.2 ⟨ng2, hng2, by rw [hidn ng2.name]; simp⟩
    simp [Dataset.namesMatchB, hs, hb]
  simp only [Dataset.isoCert, Dataset.checkMapping, Bool.and_eq_true]
  exact ⟨hbij, ⟨hdef, hnamed⟩, hmatch⟩

/-- **REFLEXIVITY (datasets).** A well-formed dataset is isomorphic to
itself. -/
theorem Dataset.isomorphic?_refl (ds : Dataset) (hnd : ds.namesNoDup = true) :
    ds.isomorphic? ds = true := by
  have hcert := Dataset.isoCert_idMapping ds hnd
  have hsearch : Dataset.isoSearch ds ds = some ds.idMapping := by
    unfold Dataset.isoSearch; rw [if_pos hcert]
  simp [Dataset.isomorphic?, Dataset.isomorphismMap?, hsearch, hcert]

/- Axiom audit — the build log must show only Lean's foundations
(`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no user
axiom, no `Lean.ofReduceBool` (which `native_decide` would add). -/
#print axioms Graph.isomorphic?_sound
#print axioms Graph.isomorphic?_refl
#print axioms Graph.isomorphicOutcome_refl
#print axioms Dataset.isomorphic?_sound
#print axioms Dataset.isomorphic?_refl

end L4Factoidal.RDF
