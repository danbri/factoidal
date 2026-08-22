/-
L4Factoidal.SPARQL.Invariants — proved properties of the algebra.

The F* source establishes its algebra properties through SMT `Lemma`s
discharged by Z3 (with `SMTPat` hints and fuel tuning); this file
states the corresponding properties as ordinary Lean theorems with
explicit tactic proofs. No `sorry`, no `axiom`, no external solver —
`lake build` re-checks every proof in the kernel.

Contents:
  * empty-pattern laws (empty BGP, join/union/minus with ∅);
  * the merge/lookup characterisation (`Binding.lookup_merge`) — the
    load-bearing lemma: what merge means, observationally;
  * join with the unit row `[∅]` is lookup-preserving;
  * safety: `filter`/`minus` only ever shrink their left input;
  * monotonicity: growing the graph never loses BGP solutions
    (`evalBgp_mono`) — stated with list membership, the
    specification-level counterpart of "adding triples adds answers".
-/
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Empty-pattern laws -/

/-- §18.3: the empty BGP evaluates to exactly the empty solution
mapping — the multiplicative unit row. -/
@[simp] theorem evalBgp_nil (g : Graph) :
    evalBgp [] g = [Binding.empty] := rfl

/-- Join with an empty left side is empty. -/
@[simp] theorem join_nil_left (omega : SolutionSeq) :
    join [] omega = [] := rfl

/-- Join with an empty right side is empty. -/
@[simp] theorem join_nil_right (omega : SolutionSeq) :
    join omega [] = [] := by
  simp [join]

/-- Minus with nothing to subtract is the identity (§18.5: the ∀μ2
condition is vacuous). -/
@[simp] theorem minus_nil_right (omega : SolutionSeq) :
    minus omega [] = omega := by
  simp [minus]

/-- LeftJoin with an empty right side keeps every left row,
unextended — OPTIONAL against nothing changes nothing. -/
@[simp] theorem leftJoin_nil_right (omega : SolutionSeq)
    (cond : Binding → Bool) : leftJoin omega [] cond = omega := by
  simp [leftJoin]

/-- Union length is additive (multiset semantics: nothing dropped,
nothing deduplicated). -/
theorem length_union (omega1 omega2 : SolutionSeq) :
    (union omega1 omega2).length = omega1.length + omega2.length := by
  simp [union]

/-- Union membership. -/
theorem mem_union {mu : Binding} {omega1 omega2 : SolutionSeq} :
    mu ∈ union omega1 omega2 ↔ mu ∈ omega1 ∨ mu ∈ omega2 := by
  simp [union]

/-! ## The merge/lookup characterisation -/

/-- The empty mapping is compatible with every mapping (its domain is
empty, so the §18.3 condition is vacuous). -/
@[simp] theorem compatible_empty_left (mu : Binding) :
    Binding.compatible Binding.empty mu = true := rfl

/-- What `merge` means, observationally: looking a variable up in
`merge acc mu2` gives `acc`'s binding when `acc` has one, else
`mu2`'s. (The F* `sm_merge_aux` accumulates by consing, so the
RESULT LIST ORDER differs from `mu2`'s — this lemma is exactly the
statement that the order shuffle is unobservable through lookup.) -/
theorem Binding.lookup_merge (acc mu2 : Binding) (v : VarName) :
    (acc.merge mu2).lookup v =
      match acc.lookup v with
      | some t => some t
      | none   => mu2.lookup v := by
  induction mu2 generalizing acc with
  | nil =>
      simp only [Binding.merge]
      cases acc.lookup v <;> rfl
  | cons hd rest ih =>
      obtain ⟨w, t⟩ := hd
      simp only [Binding.merge]
      cases hacc : acc.lookup w with
      | some u =>
          rw [ih acc]
          by_cases hwv : w = v
          · subst hwv
            simp [hacc, Binding.lookup]
          · simp [Binding.lookup, hwv]
      | none =>
          rw [ih ((w, t) :: acc)]
          by_cases hwv : w = v
          · subst hwv
            simp [Binding.lookup, hacc]
          · simp [Binding.lookup, hwv]

/-- Merging into the empty mapping preserves every lookup: the merged
row answers exactly as the original row did. -/
theorem Binding.lookup_merge_empty (mu : Binding) (v : VarName) :
    (Binding.empty.merge mu).lookup v = mu.lookup v := by
  rw [Binding.lookup_merge]
  rfl

/-- Join with the unit row `[∅]` on the left returns one row per
right row, and each is the merge of ∅ with that row — which, by
`lookup_merge_empty`, is observationally that row itself. This is the
§18.5 "Join(Ω, {μ0}) with μ0 the empty mapping is Ω" identity, stated
at the two levels the list representation supports. -/
theorem join_unit_left (omega : SolutionSeq) :
    join [Binding.empty] omega = omega.map (Binding.empty.merge ·) := by
  simp [join, List.filterMap_eq_map]

/-! ## Safety: filter and minus only shrink their left input -/

/-- Filter safety: every row a filter returns came from its input. -/
theorem mem_of_mem_filterSeq {cond : Binding → Bool} {mu : Binding}
    {omega : SolutionSeq} (h : mu ∈ filterSeq cond omega) : mu ∈ omega := by
  simpa [filterSeq] using (List.mem_filter.mp h).1

/-- A filtered row passes the condition. -/
theorem filterSeq_sound {cond : Binding → Bool} {mu : Binding}
    {omega : SolutionSeq} (h : mu ∈ filterSeq cond omega) :
    cond mu = true := by
  simpa [filterSeq] using (List.mem_filter.mp h).2

/-- Filters fuse: filtering twice is filtering by the conjunction. -/
theorem filterSeq_filterSeq (p q : Binding → Bool) (omega : SolutionSeq) :
    filterSeq p (filterSeq q omega) =
      filterSeq (fun mu => p mu && q mu) omega := by
  simp [filterSeq, List.filter_filter]

/-- Minus safety: every surviving row came from the left input
(§18.5: Minus selects a subset of Ω1). -/
theorem mem_of_mem_minus {mu : Binding} {omega1 omega2 : SolutionSeq}
    (h : mu ∈ minus omega1 omega2) : mu ∈ omega1 := by
  simpa [minus] using (List.mem_filter.mp h).1

/-! ## Monotonicity: more data, never fewer BGP answers

The specification-level counterpart of "RDF graphs are monotonic
under simple entailment": every solution a BGP has in `g` it still
has in any supergraph. Stated with list membership (`⊆` as
`∀ t ∈ g, t ∈ g'`). -/

/-- One-pattern step: matching against a larger graph keeps every
extension. -/
theorem evalTP_mono {g g' : Graph} (hsub : ∀ t, t ∈ g → t ∈ g')
    (tp : TriplePattern) (mu : Binding) {mu' : Binding}
    (h : mu' ∈ evalTP tp g mu) : mu' ∈ evalTP tp g' mu := by
  simp only [evalTP, List.mem_filterMap] at h ⊢
  obtain ⟨t, ht, hmatch⟩ := h
  exact ⟨t, hsub t ht, hmatch⟩

/-- BGP monotonicity from any seed row. -/
theorem evalBgpFrom_mono {g g' : Graph} (hsub : ∀ t, t ∈ g → t ∈ g')
    (patterns : Bgp) (mu : Binding) {mu' : Binding}
    (h : mu' ∈ evalBgpFrom g patterns mu) :
    mu' ∈ evalBgpFrom g' patterns mu := by
  induction patterns generalizing mu with
  | nil => simpa [evalBgpFrom] using h
  | cons tp rest ih =>
      simp only [evalBgpFrom, List.mem_flatMap] at h ⊢
      obtain ⟨mid, hmid, hrest⟩ := h
      exact ⟨mid, evalTP_mono hsub tp mu hmid, ih mid hrest⟩

/-- BGP monotonicity (the headline form): growing the graph never
loses a solution. -/
theorem evalBgp_mono {g g' : Graph} (hsub : ∀ t, t ∈ g → t ∈ g')
    (b : Bgp) {mu : Binding} (h : mu ∈ evalBgp b g) :
    mu ∈ evalBgp b g' :=
  evalBgpFrom_mono hsub b Binding.empty h

end L4Factoidal.SPARQL
