/-
L4Factoidal.SPARQL.QueryTheorems — proved properties of the solution
modifiers, the dataset-aware evaluator, and LATERAL.

Every proof is an ordinary Lean tactic proof, kernel-rechecked by
`lake build`. No `sorry`, no `axiom`, no external solver.

Contents:
  * §18.3 solution-mapping equality is an equivalence (reflexive,
    symmetric, transitive) — the property DISTINCT's correctness rests
    on, and the one the F* tree's issue #336 was about;
  * §18.4 DISTINCT: the result is a SUBLIST of its input (so a
    sub-multiset, both memberships in their true directions), it is
    IDEMPOTENT, and every input row is still REPRESENTED by an
    equivalent row in the output;
  * §18.4 OFFSET/LIMIT: the sliced sequence is never longer than the
    limit;
  * §18.4 projection: the row COUNT is preserved (projection changes
    rows, never how many);
  * §15.1 ORDER BY: the sorted sequence is a PERMUTATION of its input,
    so ordering neither invents nor loses a solution;
  * §18.5: single-graph evaluation is the default-graph case of
    dataset evaluation;
  * LATERAL with an empty right side per row yields no rows — the
    inner-join shape (`lateral_empty_rhs_per_row.rq` in the F* tree).
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## §18.3 — solution-mapping equality is an equivalence -/

/-- A variable a row lists is a variable that row binds. -/
theorem Binding.lookup_isSome_of_mem {mu : Binding} {e : VarName × Term}
    (h : e ∈ mu) : ∃ t, mu.lookup e.1 = some t := by
  induction mu with
  | nil => cases h
  | cons hd tl ih =>
    obtain ⟨w, u⟩ := hd
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨u, by simp [Binding.lookup]⟩
    · by_cases hw : w = e.1
      · exact ⟨u, by simp [Binding.lookup, hw]⟩
      · obtain ⟨t, ht⟩ := ih h'
        exact ⟨t, by simp [Binding.lookup, hw, ht]⟩

/-- A successful lookup names an entry of the row. -/
theorem Binding.exists_entry_of_lookup {mu : Binding} {v : VarName} {t : Term}
    (h : mu.lookup v = some t) : ∃ e, e ∈ mu ∧ e.1 = v := by
  induction mu with
  | nil => simp [Binding.lookup] at h
  | cons hd tl ih =>
    obtain ⟨w, u⟩ := hd
    by_cases hw : w = v
    · exact ⟨(w, u), List.mem_cons_self .., hw⟩
    · have h' : Binding.lookup v tl = some t := by
        simpa [Binding.lookup, hw] using h
      obtain ⟨e, he, hev⟩ := ih h'
      exact ⟨e, List.mem_cons_of_mem _ he, hev⟩

/-- What `subsumes` says, pointwise: every variable the left row binds,
the right row binds to an `eqb`-equal term. -/
theorem Binding.subsumes_lookup {mu1 mu2 : Binding}
    (h : mu1.subsumes mu2 = true) {v : VarName} {t1 : Term}
    (hv : mu1.lookup v = some t1) :
    ∃ t2, mu2.lookup v = some t2 ∧ t1.eqb t2 = true := by
  obtain ⟨e, he, hev⟩ := Binding.exists_entry_of_lookup hv
  have hall := List.all_eq_true.mp h e he
  cases h2 : mu2.lookup v with
  | none => simp [hev, hv, h2] at hall
  | some t2 => exact ⟨t2, rfl, by simpa [hev, hv, h2] using hall⟩

theorem Binding.subsumes_refl (mu : Binding) : mu.subsumes mu = true := by
  refine List.all_eq_true.mpr (fun e he => ?_)
  obtain ⟨t, ht⟩ := Binding.lookup_isSome_of_mem he
  simp [ht]

theorem Binding.subsumes_trans {mu1 mu2 mu3 : Binding}
    (h12 : mu1.subsumes mu2 = true) (h23 : mu2.subsumes mu3 = true) :
    mu1.subsumes mu3 = true := by
  refine List.all_eq_true.mpr (fun e he => ?_)
  obtain ⟨t1, ht1⟩ := Binding.lookup_isSome_of_mem he
  obtain ⟨t2, ht2, h1⟩ := Binding.subsumes_lookup h12 ht1
  obtain ⟨t3, ht3, h2⟩ := Binding.subsumes_lookup h23 ht2
  simp [ht1, ht3, Term.eqb_trans h1 h2]

/-- §18.3: every row is equal to itself. -/
@[simp] theorem Binding.equiv_refl (mu : Binding) : mu.equiv mu = true := by
  simp [Binding.equiv, Binding.subsumes_refl]

theorem Binding.equiv_symm {mu1 mu2 : Binding} (h : mu1.equiv mu2 = true) :
    mu2.equiv mu1 = true := by
  simp only [Binding.equiv, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

theorem Binding.equiv_trans {mu1 mu2 mu3 : Binding}
    (h12 : mu1.equiv mu2 = true) (h23 : mu2.equiv mu3 = true) :
    mu1.equiv mu3 = true := by
  simp only [Binding.equiv, Bool.and_eq_true] at h12 h23 ⊢
  exact ⟨Binding.subsumes_trans h12.1 h23.1, Binding.subsumes_trans h23.2 h12.2⟩

/-- §18.3-equivalent rows bind the same variable names.  This is phrased as
    a successful lookup transfer so it does not depend on the incidental
    association-list order of either mapping.  It is the first bridge used by
    the bucketed runtime DISTINCT refinement. -/
theorem Binding.equiv_lookup {mu1 mu2 : Binding}
    (h : mu1.equiv mu2 = true) {v : VarName} {t1 : Term}
    (hv : mu1.lookup v = some t1) :
    ∃ t2, mu2.lookup v = some t2 ∧ t1.eqb t2 = true := by
  simp only [Binding.equiv, Bool.and_eq_true] at h
  exact Binding.subsumes_lookup h.1 hv

/-- The canonical RDF-term keys of corresponding §18.3 bindings agree.
    `Term.joinKey` accounts for the two deliberately non-structural RDF term
    equality cases (language-tag case and canonical XML literals), so a hash
    bucket cannot separate equivalent lookup values. -/
theorem Binding.equiv_lookup_joinKey {mu1 mu2 : Binding}
    (h : mu1.equiv mu2 = true) {v : VarName} {t1 : Term}
    (hv : mu1.lookup v = some t1) :
    ∃ t2, mu2.lookup v = some t2 ∧ t1.joinKey = t2.joinKey := by
  obtain ⟨t2, ht2, heq⟩ := Binding.equiv_lookup h hv
  exact ⟨t2, ht2, Term.joinKey_eq_of_eqb heq⟩

/-- §18.3 equivalence also transfers absence of a binding. -/
theorem Binding.equiv_lookup_none {mu1 mu2 : Binding}
    (h : mu1.equiv mu2 = true) {v : VarName}
    (hv : mu1.lookup v = none) : mu2.lookup v = none := by
  cases h2 : mu2.lookup v with
  | none => rfl
  | some t2 =>
      obtain ⟨t1, ht1, _⟩ := Binding.equiv_lookup (Binding.equiv_symm h) h2
      simp [hv] at ht1

/-- Equivalent mappings have the same binding domain, independently of their
    association-list layout. -/
theorem Binding.equiv_lookup_none_iff {mu1 mu2 : Binding}
    (h : mu1.equiv mu2 = true) {v : VarName} :
    mu1.lookup v = none ↔ mu2.lookup v = none := by
  constructor
  · exact Binding.equiv_lookup_none h
  · exact Binding.equiv_lookup_none (Binding.equiv_symm h)

/-- Equivalent mappings have the same canonical optional value for every
    variable.  Both absence and the RDF-term equality cases are explicit: this
    is exactly the safety property needed by a fixed-universe hash key. -/
theorem Binding.equiv_lookup_joinKeyOption {mu1 mu2 : Binding}
    (h : mu1.equiv mu2 = true) (v : VarName) :
    (mu1.lookup v).map Term.joinKey = (mu2.lookup v).map Term.joinKey := by
  cases h1 : mu1.lookup v with
  | none =>
      have h2 := Binding.equiv_lookup_none h h1
      simp [h2]
  | some t1 =>
      obtain ⟨t2, h2, hkey⟩ := Binding.equiv_lookup_joinKey h h1
      simp [h2, hkey]

/-- The optimized DISTINCT candidate key is coherent with §18.3 solution-map
    equality for any fixed variable universe.  The universe need not be
    complete for safety because every candidate bucket still performs the
    full `Binding.equiv` check; completeness only improves partitioning. -/
theorem Binding.equiv_distinctKeyFor {mu1 mu2 : Binding}
    (h : mu1.equiv mu2 = true) (vars : List VarName) :
    mu1.distinctKeyFor vars = mu2.distinctKeyFor vars := by
  induction vars with
  | nil => rfl
  | cons v rest ih =>
      simp only [Binding.distinctKeyFor, List.map_cons]
      rw [Binding.equiv_lookup_joinKeyOption h v]
      simpa [Binding.distinctKeyFor] using ih

/-- The runtime hash table contains exactly the retained rows selected by each
    candidate key, in retained-list order. -/
def DistinctBucketWf (vars : List VarName)
    (buckets : Std.HashMap (List (Option Term)) SolutionSeq)
    (kept : SolutionSeq) : Prop :=
  ∀ key, buckets.getD key [] =
    kept.filter (fun mu => mu.distinctKeyFor vars == key)

theorem DistinctBucketWf.empty (vars : List VarName) :
    DistinctBucketWf vars
      (∅ : Std.HashMap (List (Option Term)) SolutionSeq) [] := by
  intro key
  simp [Std.HashMap.getD_empty]

theorem DistinctBucketWf.push {vars : List VarName}
    {buckets : Std.HashMap (List (Option Term)) SolutionSeq}
    {kept : SolutionSeq} (h : DistinctBucketWf vars buckets kept)
    (mu : Binding) :
    DistinctBucketWf vars
      (buckets.insert (mu.distinctKeyFor vars)
        (mu :: buckets.getD (mu.distinctKeyFor vars) []))
      (mu :: kept) := by
  intro key
  rw [Std.HashMap.getD_insert]
  by_cases hk : mu.distinctKeyFor vars = key
  · subst key
    simpa using h (mu.distinctKeyFor vars)
  · have hb : (mu.distinctKeyFor vars == key) = false := by
      simpa using hk
    simp [hb, h key]

private theorem any_filter_distinctKeyFor_eq (vars : List VarName)
    (mu : Binding) : ∀ kept : SolutionSeq,
    (kept.filter (fun prior =>
      prior.distinctKeyFor vars == mu.distinctKeyFor vars)).any
        (fun prior => mu.equiv prior) =
      kept.any (fun prior => mu.equiv prior) := by
  intro kept
  induction kept with
  | nil => rfl
  | cons prior rest ih =>
      by_cases heq : mu.equiv prior = true
      · have hkey := Binding.equiv_distinctKeyFor heq vars
        have hk : (prior.distinctKeyFor vars == mu.distinctKeyFor vars) = true := by
          simp [hkey]
        simp [heq, hk]
      · by_cases hk : (prior.distinctKeyFor vars == mu.distinctKeyFor vars) = true
        · simp [heq, hk, ih]
        · simp [heq, hk, ih]

/-- Under the bucket invariant, probing the candidate bucket is exactly the
    same duplicate test as scanning every retained row.  Key collisions remain
    harmless; key coherence ensures no equivalent row is filtered out. -/
theorem DistinctBucketWf.bucketAnyEq {vars : List VarName}
    {buckets : Std.HashMap (List (Option Term)) SolutionSeq}
    {kept : SolutionSeq} (h : DistinctBucketWf vars buckets kept)
    (mu : Binding) :
    (buckets.getD (mu.distinctKeyFor vars) []).any
        (fun prior => mu.equiv prior) =
      kept.any (fun prior => mu.equiv prior) := by
  rw [h]
  exact any_filter_distinctKeyFor_eq vars mu kept

/-! ## §18.4 DISTINCT -/

/-- DISTINCT only ever DELETES rows, in place: its result is a sublist
of its input. Sub-multiset, membership, and the length bound all
follow. -/
theorem distinctSolutions_sublist (omega : SolutionSeq) :
    (distinctSolutions omega).Sublist omega := by
  induction omega with
  | nil => simp [distinctSolutions]
  | cons hd tl ih =>
    unfold distinctSolutions
    split
    · exact ih.cons hd
    · exact ih.cons_cons hd

/-- Every row DISTINCT returns came from its input. -/
theorem mem_of_mem_distinctSolutions {mu : Binding} {omega : SolutionSeq}
    (h : mu ∈ distinctSolutions omega) : mu ∈ omega :=
  (distinctSolutions_sublist omega).subset h

theorem length_distinctSolutions_le (omega : SolutionSeq) :
    (distinctSolutions omega).length ≤ omega.length :=
  (distinctSolutions_sublist omega).length_le

/-- The converse membership direction: a row with no equivalent row
LATER in the sequence survives DISTINCT. Together with
`mem_of_mem_distinctSolutions` this pins membership in both
directions. -/
theorem mem_distinctSolutions_of_no_later_dup (mu : Binding) :
    ∀ l r : SolutionSeq, r.any (fun x => mu.equiv x) = false →
      mu ∈ distinctSolutions (l ++ mu :: r) := by
  intro l
  induction l with
  | nil =>
    intro r hno
    show mu ∈ distinctSolutions (mu :: r)
    unfold distinctSolutions
    simp [hno]
  | cons hd tl ih =>
    intro r hno
    show mu ∈ distinctSolutions (hd :: (tl ++ mu :: r))
    unfold distinctSolutions
    split
    · exact ih r hno
    · exact List.mem_cons_of_mem _ (ih r hno)

/-- No row of a DISTINCT result has an equivalent row after it. -/
def NoLaterDup : SolutionSeq → Prop
  | []        => True
  | mu :: rest => rest.any (fun x => mu.equiv x) = false ∧ NoLaterDup rest

/-- If `mu` has an equivalent representative in `suffix`, inserting `mu`
    cannot make it the sole later duplicate of another mapping.  Transitivity
    transfers any such comparison to the representative already in suffix. -/
private theorem any_equiv_cons_shadowed (head mu : Binding) {suffix : SolutionSeq}
    (hdup : suffix.any (fun x => mu.equiv x) = true) :
    (mu :: suffix).any (fun x => head.equiv x) =
      suffix.any (fun x => head.equiv x) := by
  by_cases hhead : head.equiv mu = true
  · obtain ⟨witness, hwitness, hmuw⟩ := List.any_eq_true.mp hdup
    have hheadw := Binding.equiv_trans hhead hmuw
    have hsuffix : suffix.any (fun x => head.equiv x) = true :=
      List.any_eq_true.mpr ⟨witness, hwitness, hheadw⟩
    simp [hhead, hsuffix]
  · simp [hhead]

/-- Removing a mapping which has an equivalent later representative does not
    change DISTINCT, even under an arbitrary earlier prefix. -/
theorem distinctSolutions_erase_shadowed (mu : Binding) (suffix : SolutionSeq)
    (hdup : suffix.any (fun x => mu.equiv x) = true) :
    ∀ earlier : SolutionSeq,
      distinctSolutions (earlier ++ mu :: suffix) =
        distinctSolutions (earlier ++ suffix) := by
  intro earlier
  induction earlier with
  | nil => simp [distinctSolutions, hdup]
  | cons head rest ih =>
      have hany :
          (rest ++ mu :: suffix).any (fun x => head.equiv x) =
            (rest ++ suffix).any (fun x => head.equiv x) := by
        simp only [List.any_append]
        rw [any_equiv_cons_shadowed head mu hdup]
      simp only [List.cons_append, distinctSolutions]
      rw [hany]
      by_cases hrest : (rest ++ suffix).any (fun x => head.equiv x) = true
      · simp [hrest, ih]
      · simp [hrest, ih]

private theorem any_false_of_subset {p : Binding → Bool} {l1 l2 : SolutionSeq}
    (hsub : ∀ x ∈ l1, x ∈ l2) (h : l2.any p = false) : l1.any p = false := by
  cases hh : l1.any p with
  | false => rfl
  | true =>
    obtain ⟨x, hx, hpx⟩ := List.any_eq_true.mp hh
    have : l2.any p = true := List.any_eq_true.mpr ⟨x, hsub x hx, hpx⟩
    rw [h] at this
    exact absurd this (by simp)

theorem noLaterDup_distinctSolutions (omega : SolutionSeq) :
    NoLaterDup (distinctSolutions omega) := by
  induction omega with
  | nil => simp [distinctSolutions, NoLaterDup]
  | cons hd tl ih =>
    unfold distinctSolutions
    split
    · exact ih
    · rename_i hno
      refine ⟨?_, ih⟩
      exact any_false_of_subset
        (fun x hx => mem_of_mem_distinctSolutions hx)
        (by simpa using hno)

theorem distinctSolutions_of_noLaterDup :
    ∀ {omega : SolutionSeq}, NoLaterDup omega → distinctSolutions omega = omega := by
  intro omega
  induction omega with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    unfold distinctSolutions
    rw [if_neg (by simp [h.1])]
    rw [ih h.2]

/-- The tail-recursive HashMap worker implements the reference DISTINCT for an
    arbitrary unprocessed suffix and a well-formed retained accumulator. -/
theorem distinctSolutionsFastGo_eq (vars : List VarName) :
    ∀ (xs : SolutionSeq)
      (buckets : Std.HashMap (List (Option Term)) SolutionSeq)
      (kept : SolutionSeq),
      DistinctBucketWf vars buckets kept →
      NoLaterDup kept →
      distinctSolutionsFastGo vars xs buckets kept =
        distinctSolutions (xs.reverse ++ kept) := by
  intro xs
  induction xs with
  | nil =>
      intro buckets kept _ hkept
      simpa [distinctSolutionsFastGo] using
        (distinctSolutions_of_noLaterDup hkept).symm
  | cons mu rest ih =>
      intro buckets kept hbuckets hkept
      unfold distinctSolutionsFastGo
      dsimp only
      rw [DistinctBucketWf.bucketAnyEq hbuckets mu]
      by_cases hdup : kept.any (fun prior => mu.equiv prior) = true
      · rw [if_pos hdup]
        rw [ih buckets kept hbuckets hkept]
        simpa [List.reverse_cons, List.append_assoc] using
          (distinctSolutions_erase_shadowed mu kept hdup rest.reverse).symm
      · rw [if_neg hdup]
        have hbuckets' := DistinctBucketWf.push hbuckets mu
        have hkept' : NoLaterDup (mu :: kept) := ⟨by simpa using hdup, hkept⟩
        rw [ih _ _ hbuckets' hkept']
        simp [List.reverse_cons, List.append_assoc]

/-- Exact refinement of the production DISTINCT implementation: same retained
    representatives and same list order as the simple §18.4 reference. -/
theorem distinctSolutionsFast_eq (omega : SolutionSeq) :
    distinctSolutionsFast omega = distinctSolutions omega := by
  unfold distinctSolutionsFast
  rw [distinctSolutionsFastGo_eq (distinctVariables omega) omega.reverse
    (∅ : Std.HashMap (List (Option Term)) SolutionSeq) []
    (DistinctBucketWf.empty (distinctVariables omega)) (by simp [NoLaterDup])]
  simp

/-- DISTINCT is IDEMPOTENT (§18.4: `Distinct(Distinct(Ω)) =
Distinct(Ω)` — deduplicating a deduplicated sequence changes
nothing). -/
theorem distinctSolutions_idem (omega : SolutionSeq) :
    distinctSolutions (distinctSolutions omega) = distinctSolutions omega :=
  distinctSolutions_of_noLaterDup (noLaterDup_distinctSolutions omega)

/-- Nothing is LOST: every input row still has an equivalent row in the
DISTINCT result. With `mem_of_mem_distinctSolutions` this is the
"same set of rows, up to §18.3 equality" statement. -/
theorem distinctSolutions_represents :
    ∀ (omega : SolutionSeq) (mu : Binding), mu ∈ omega →
      ∃ x, x ∈ distinctSolutions omega ∧ mu.equiv x = true := by
  intro omega
  induction omega with
  | nil => intro mu h; cases h
  | cons hd tl ih =>
    intro mu hmu
    unfold distinctSolutions
    split
    · rename_i hdup
      obtain ⟨y, hy, hey⟩ := List.any_eq_true.mp hdup
      rcases List.mem_cons.mp hmu with rfl | hrest
      · obtain ⟨x, hx, hex⟩ := ih y hy
        exact ⟨x, hx, Binding.equiv_trans hey hex⟩
      · exact ih mu hrest
    · rcases List.mem_cons.mp hmu with rfl | hrest
      · exact ⟨mu, List.mem_cons_self .., Binding.equiv_refl mu⟩
      · obtain ⟨x, hx, hex⟩ := ih mu hrest
        exact ⟨x, List.mem_cons_of_mem _ hx, hex⟩

/-- REDUCED keeps every row — the conformant "remove none" choice. -/
@[simp] theorem reducedSolutions_eq (omega : SolutionSeq) :
    reducedSolutions omega = omega := rfl

/-! ## §18.4 OFFSET / LIMIT -/

/-- LIMIT n never returns more than n rows. -/
theorem length_sliceSolutions_le (offset : Option Nat) (n : Nat)
    (omega : SolutionSeq) : (sliceSolutions offset (some n) omega).length ≤ n := by
  unfold sliceSolutions
  cases offset <;> simp [List.length_take] <;> omega

/-- With neither OFFSET nor LIMIT the sequence is untouched. -/
@[simp] theorem sliceSolutions_none (omega : SolutionSeq) :
    sliceSolutions none none omega = omega := rfl

/-- Slicing only ever shortens. -/
theorem length_sliceSolutions_le_input (offset limit : Option Nat)
    (omega : SolutionSeq) : (sliceSolutions offset limit omega).length ≤ omega.length := by
  unfold sliceSolutions
  cases offset <;> cases limit <;>
    simp [List.length_take, List.length_drop] <;> omega

/-! ## §18.4 projection -/

/-- Projection changes ROWS, never how many: one row in, one row out
(so a SELECT with no expression errors returns exactly as many rows as
its WHERE clause produced). -/
@[simp] theorem length_projectSolutions (vars : List VarName) (omega : SolutionSeq) :
    (projectSolutions vars omega).length = omega.length := by
  simp [projectSolutions]

/-- Projection keeps exactly the projected variables: a variable that
is not projected is unbound in every projected row. -/
theorem lookup_projectBinding_of_not_mem {vars : List VarName} {v : VarName}
    (mu : Binding) (h : v ∉ vars) :
    (projectBinding vars mu).lookup v = none := by
  induction mu with
  | nil => simp [projectBinding, Binding.lookup]
  | cons hd tl ih =>
    obtain ⟨w, u⟩ := hd
    unfold projectBinding
    split
    · rename_i hin
      have hmem : w ∈ vars := by simpa using hin
      by_cases hw : w = v
      · exact absurd (hw ▸ hmem) h
      · simpa [Binding.lookup, hw] using ih
    · exact ih

/-! ## §15.1 ORDER BY is a permutation -/

/-- Inserting one row adds exactly that row. -/
theorem insertOrdered_perm (cmp : Binding → Binding → Int) (mu : Binding) :
    ∀ l : SolutionSeq, (insertOrdered cmp mu l).Perm (mu :: l) := by
  intro l
  induction l with
  | nil => simp [insertOrdered]
  | cons x rest ih =>
    unfold insertOrdered
    split
    · exact List.Perm.refl _
    · exact ((ih.cons x).trans (List.Perm.swap mu x rest))

/-- ORDER BY neither invents nor loses a solution: the sorted sequence
is a PERMUTATION of its input. (§15.1 constrains the ORDER of the
result; this is the statement that ordering is all it does.) -/
theorem sortSolutions_perm (cmp : Binding → Binding → Int) :
    ∀ omega : SolutionSeq, (sortSolutions cmp omega).Perm omega := by
  intro omega
  induction omega with
  | nil => simp [sortSolutions]
  | cons mu rest ih =>
    exact (insertOrdered_perm cmp mu (sortSolutions cmp rest)).trans (ih.cons mu)

/-- Consequence: the row count survives ORDER BY. -/
theorem length_sortSolutions (cmp : Binding → Binding → Int) (omega : SolutionSeq) :
    (sortSolutions cmp omega).length = omega.length :=
  (sortSolutions_perm cmp omega).length_eq

/-- Consequence: ORDER BY preserves membership in both directions. -/
theorem mem_sortSolutions_iff (cmp : Binding → Binding → Int) (omega : SolutionSeq)
    (mu : Binding) : mu ∈ sortSolutions cmp omega ↔ mu ∈ omega :=
  (sortSolutions_perm cmp omega).mem_iff

/-! ## §18.5 / §18.6 — single-graph evaluation is a special case -/

/-- `eval` is `evalIn` on a dataset with no named graphs, by
definition. -/
theorem evalIn_default_eq_eval (g : Graph) (p : GraphPattern) :
    p.evalIn { default := g, named := [] } g = p.eval g := rfl

/-- Stated for any dataset that happens to have no named graphs:
evaluating against its default graph is single-graph evaluation. -/
theorem evalIn_eq_eval_of_no_named (ds : Dataset) (h : ds.named = [])
    (p : GraphPattern) : p.evalIn ds ds.default = p.eval ds.default := by
  cases ds with
  | mk d n => cases h; rfl

/-- With no named graphs there is nothing for `GRAPH ?g` to iterate. -/
theorem graphVar_no_named (ds : Dataset) (h : ds.named = []) (active : Graph)
    (v : VarName) (p : GraphPattern) :
    (GraphPattern.graph (.var v) p).evalIn ds active = [] := by
  cases ds with
  | mk d n => cases h; rfl

/-! ## LATERAL -/

private theorem flatMap_eq_nil_of_all {α β : Type} (l : List α) (f : α → List β)
    (h : ∀ x, f x = []) : l.flatMap f = [] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, h a, ih]

/-- LATERAL is INNER-JOIN shaped, not OPTIONAL shaped: when the
right-hand side has no solution for a row, that row contributes
nothing — it does not survive unextended. With an empty right side for
EVERY row, the whole LATERAL is empty. (The F* tree pins the same
behaviour in `tests/local/sparql/lateral_empty_rhs_per_row.rq`.) -/
theorem lateral_empty_rhs_per_row (ds : Dataset) (active : Graph)
    (l : GraphPattern) (r : Binding → GraphPattern)
    (h : ∀ mu, (r mu).evalIn ds active = []) :
    (GraphPattern.lateral l r).evalIn ds active = [] := by
  show (GraphPattern.evalIn ds active l).flatMap _ = []
  exact flatMap_eq_nil_of_all _ _ (fun mu => by rw [h mu]; rfl)

/-- An empty LEFT side means the right side is never evaluated. -/
theorem lateral_empty_lhs (ds : Dataset) (active : Graph)
    (l : GraphPattern) (r : Binding → GraphPattern)
    (h : l.evalIn ds active = []) :
    (GraphPattern.lateral l r).evalIn ds active = [] := by
  show (GraphPattern.evalIn ds active l).flatMap _ = []
  rw [h]
  rfl

/-- The empty group pattern is the unit row (§18.2.2.6). -/
@[simp] theorem evalIn_empty (ds : Dataset) (active : Graph) :
    GraphPattern.empty.evalIn ds active = [Binding.empty] := rfl

/-- `VALUES` does not read the graph at all — inline data is inline
(§10.2). -/
@[simp] theorem evalIn_values (ds : Dataset) (active : Graph)
    (vars : List VarName) (rows : List (List (Option Term))) :
    (GraphPattern.values vars rows).evalIn ds active = evalValues vars rows := rfl

/-- A VALUES block produces exactly one row per data row. -/
theorem length_evalValues (vars : List VarName) (rows : List (List (Option Term))) :
    (evalValues vars rows).length = rows.length := by
  simp [evalValues]

/-- SERVICE SILENT against an unreachable endpoint yields the empty
solution mapping, so a surrounding join keeps its rows (Federated
Query §2). -/
@[simp] theorem evalIn_service_silent_miss (ds : Dataset) (active : Graph)
    (p : GraphPattern) :
    (GraphPattern.service none true p).evalIn ds active = [Binding.empty] := rfl

/-- Without SILENT the same miss yields no rows. -/
@[simp] theorem evalIn_service_miss (ds : Dataset) (active : Graph)
    (p : GraphPattern) :
    (GraphPattern.service none false p).evalIn ds active = [] := rfl

end L4Factoidal.SPARQL

/-! ## Axiom audit

The acceptable base is exactly Lean's own foundations — `propext`,
`Classical.choice`, `Quot.sound`. Every build log shows these lines. -/

section Audit
open L4Factoidal.SPARQL

#print axioms distinctSolutions_idem
#print axioms distinctSolutions_represents
#print axioms mem_of_mem_distinctSolutions
#print axioms length_sliceSolutions_le
#print axioms length_projectSolutions
#print axioms sortSolutions_perm
#print axioms evalIn_eq_eval_of_no_named
#print axioms lateral_empty_rhs_per_row
#print axioms Binding.equiv_trans
#print axioms Binding.equiv_distinctKeyFor
#print axioms DistinctBucketWf.bucketAnyEq
#print axioms distinctSolutionsFastGo_eq
#print axioms distinctSolutionsFast_eq

end Audit
