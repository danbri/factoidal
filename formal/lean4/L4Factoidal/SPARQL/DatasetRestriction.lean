/-
L4Factoidal.SPARQL.DatasetRestriction — restrictions of a dataset, and
the fragment of the query language whose answer does not change when
the dataset is restricted.

This is the evaluator half of the planner-soundness theorem
(`docs/designissues/2026-09-06-planner-soundness-theorem.md`). A
persisted-store planner reads a SUBSET of the manifest entries; the
dataset it then materialises is a restriction of the dataset every
entry would have given. What has to hold for the answer to be
unchanged is stated here, over `Dataset`, and proved by induction on
the pattern.

## The one restriction, not four

Section 3 of the design record decomposes the planner into three
collectors — predicates, graph names, subject and object zones — and
asks for one lemma each. Three of the four are the SAME statement over
`Graph`: keep the triples a Boolean `keep` admits. `restrictPred`,
`restrictSubj` and `restrictObj` are three instances of `restrictGraph`
and commute because `List.filter` composes into a conjunction. Only the
graph-name restriction is a different shape, because it acts on the
dataset's named-graph LIST rather than inside a graph, and it is
carried here by `DatasetRestricted`'s two fields.

## Why the index disappears

`indexedDatasetBackend` wraps every graph in an `OWL.RL.Index`, so the
theorem is nominally about hash-map buckets. `Index.Wf`
(`OWL/RLClosureIndexed.lean`) already proves every bucket lookup equals
the corresponding list filter, so `igSearch_ofGraph_filter` below
reduces the whole index to `List.filter` and nothing downstream of it
mentions a bucket again.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.StoreDataset

namespace L4Factoidal.SPARQL.DatasetRestriction

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreDataset

/-! ## 1. Filter algebra

Two list facts. Everything about restriction reduces to them. -/

theorem filter_comm (p q : Triple → Bool) :
    ∀ l : List Triple, (l.filter p).filter q = (l.filter q).filter p := by
  intro l
  induction l with
  | nil => rfl
  | cons t rest ih =>
      by_cases hp : p t = true <;> by_cases hq : q t = true <;>
        simp [hp, hq, ih] at * <;> simp [hp, hq, ih]

/-- Filtering by `q` after `keep` is filtering by `q` alone, whenever
every triple `q` admits is a triple `keep` admits. -/
theorem filter_filter_of_imp {keep q : Triple → Bool}
    (h : ∀ t, q t = true → keep t = true) :
    ∀ l : List Triple, (l.filter keep).filter q = l.filter q := by
  intro l
  induction l with
  | nil => rfl
  | cons t rest ih =>
      by_cases hq : q t = true
      · have hk := h t hq
        simp [hk, hq, ih]
      · simp only [Bool.not_eq_true] at hq
        by_cases hk : keep t = true
        · simp [hk, hq, ih]
        · simp only [Bool.not_eq_true] at hk
          simp [hk, hq, ih]

/-! ## 2. A bound a restriction cannot narrow

`BoundKept keep b` is the whole hypothesis the storage side has to
supply: every triple the bound `b` admits survives `keep`. A triple
pattern with a constant predicate `p` presents a bound with
`b.p = some p`, so `keep = (·.p ∈ P)` satisfies it for every `p ∈ P` —
which is what the predicate collector computed. -/

def BoundKept (keep : Triple → Bool) (b : PatternBound) : Prop :=
  ∀ t, boundMatches b t = true → keep t = true

theorem tripleMatchesBound_filter {keep : Triple → Bool} {b : PatternBound}
    (h : BoundKept keep b) (l : Graph) :
    tripleMatchesBound b (l.filter keep) = tripleMatchesBound b l :=
  filter_filter_of_imp h l

/-! ## 3. The index is a list filter

`igSearch` reads one of six candidate sets out of the index and then
applies `tripleMatchesBound`. Under `Index.Wf` every candidate set is a
`List.filter` of the graph, so restricting the graph restricts each
candidate set the same way, and the bound filter absorbs the
restriction. -/

open L4Factoidal.OWL.RL in
/-- **The index lemma.** A bound whose matches all survive `keep` reads
the same rows, in the same order, from the restricted graph as from the
whole one. Every candidate set `igSearch` can read is a `List.filter` of
the graph (`Index.Wf`), so the restriction commutes out of the candidate
set and the bound filter then absorbs it. -/
theorem igSearch_ofGraph_filter {keep : Triple → Bool} {b : PatternBound}
    (h : BoundKept keep b) (g : Graph) :
    igSearch (Index.ofGraph (g.filter keep)) b = igSearch (Index.ofGraph g) b := by
  have hw : Index.Wf (Index.ofGraph g) g := Index.Wf.ofGraph g
  have hwk : Index.Wf (Index.ofGraph (g.filter keep)) (g.filter keep) :=
    Index.Wf.ofGraph _
  have hsp : ∀ s p, (Index.ofGraph (g.filter keep)).withSubjPred s p
      = ((Index.ofGraph g).withSubjPred s p).filter keep := by
    intro s p
    rw [hw.withSubjPred_eq, hwk.withSubjPred_eq, withSubjPred, withSubjPred, filter_comm]
  have hpo : ∀ p o, (Index.ofGraph (g.filter keep)).withPredObj p o
      = ((Index.ofGraph g).withPredObj p o).filter keep := by
    intro p o
    rw [hw.withPredObj_eq, hwk.withPredObj_eq, withPredObj, withPredObj, filter_comm]
  have hpr : ∀ p, (Index.ofGraph (g.filter keep)).withPred p
      = ((Index.ofGraph g).withPred p).filter keep := by
    intro p
    rw [hw.withPred_eq, hwk.withPred_eq, withPred, withPred, filter_comm]
  have hsu : ∀ s, (Index.ofGraph (g.filter keep)).withSubj s
      = ((Index.ofGraph g).withSubj s).filter keep := by
    intro s
    rw [hw.withSubj_eq, hwk.withSubj_eq, withSubj, withSubj, filter_comm]
  have hob : ∀ o, (Index.ofGraph (g.filter keep)).withObj o
      = ((Index.ofGraph g).withObj o).filter keep := by
    intro o
    rw [hw.withObj_eq, hwk.withObj_eq, withObj, withObj, filter_comm]
  have hall : (Index.ofGraph (g.filter keep)).toGraph
      = ((Index.ofGraph g).toGraph).filter keep := by
    rw [Index.toGraph, Index.toGraph, hw.all, hwk.all]
  simp only [igSearch]
  cases hs : b.s <;> cases hp : b.p <;> cases ho : b.o <;>
    simp only [] <;>
    first
      | (rw [hsp]; exact tripleMatchesBound_filter h _)
      | (rw [hsu]; exact tripleMatchesBound_filter h _)
      | (rw [hpr]; exact tripleMatchesBound_filter h _)
      | (rw [hall]; exact tripleMatchesBound_filter h _)
      | (split
         · rw [hpo]; exact tripleMatchesBound_filter h _
         · rw [hpr]; exact tripleMatchesBound_filter h _)
      | (split
         · rw [hob]; exact tripleMatchesBound_filter h _
         · rw [hall]; exact tripleMatchesBound_filter h _)


/-! ## 4. The backend dispatchers over a restricted graph

`indexedGraphBackend` is `capsOfIndexed ∘ Index.ofGraph`, so every
dispatcher inherits `igSearch_ofGraph_filter`. -/

theorem backendSearch_indexed_filter {keep : Triple → Bool} {b : PatternBound}
    (h : BoundKept keep b) (g : Graph) :
    backendSearch (indexedGraphBackend (g.filter keep)) b
      = backendSearch (indexedGraphBackend g) b := by
  simp only [backendSearch, indexedGraphBackend, capsOfBackend, capsOfIndexed]
  exact igSearch_ofGraph_filter h g

theorem backendEstimate_indexed_filter {keep : Triple → Bool} {b : PatternBound}
    (h : BoundKept keep b) (g : Graph) :
    backendEstimate (indexedGraphBackend (g.filter keep)) b
      = backendEstimate (indexedGraphBackend g) b := by
  simp only [backendEstimate, indexedGraphBackend, capsOfBackend, capsOfIndexed,
    igEstimate]
  rw [igSearch_ofGraph_filter h g]

theorem backendCountExact_indexed_filter {keep : Triple → Bool} {b : PatternBound}
    (h : BoundKept keep b) (g : Graph) :
    backendCountExact (indexedGraphBackend (g.filter keep)) b
      = backendCountExact (indexedGraphBackend g) b := by
  simp only [backendCountExact, indexedGraphBackend, capsOfBackend, capsOfIndexed,
    igEstimate]
  rw [igSearch_ofGraph_filter h g]

theorem backendSearchLimited_indexed_filter {keep : Triple → Bool} {b : PatternBound}
    (h : BoundKept keep b) (g : Graph) (n : Nat) :
    backendSearchLimited (indexedGraphBackend (g.filter keep)) b n
      = backendSearchLimited (indexedGraphBackend g) b n := by
  simp only [backendSearchLimited, indexedGraphBackend, capsOfBackend, capsOfIndexed]
  rw [igSearch_ofGraph_filter h g]

open L4Factoidal.OWL.RL in
/-- The empty graph answers nothing, whatever the bound. -/
theorem backendSearch_indexed_nil (b : PatternBound) :
    backendSearch (indexedGraphBackend []) b = [] := by
  have hw : Index.Wf (Index.ofGraph ([] : Graph)) [] := Index.Wf.ofGraph []
  simp only [backendSearch, indexedGraphBackend, capsOfBackend, capsOfIndexed, igSearch]
  have hsp : ∀ s p, (Index.ofGraph ([] : Graph)).withSubjPred s p = [] := by
    intro s p; rw [hw.withSubjPred_eq]; rfl
  have hpo : ∀ p o, (Index.ofGraph ([] : Graph)).withPredObj p o = [] := by
    intro p o; rw [hw.withPredObj_eq]; rfl
  have hpr : ∀ p, (Index.ofGraph ([] : Graph)).withPred p = [] := by
    intro p; rw [hw.withPred_eq]; rfl
  have hsu : ∀ s, (Index.ofGraph ([] : Graph)).withSubj s = [] := by
    intro s; rw [hw.withSubj_eq]; rfl
  have hob : ∀ o, (Index.ofGraph ([] : Graph)).withObj o = [] := by
    intro o; rw [hw.withObj_eq]; rfl
  have hall : (Index.ofGraph ([] : Graph)).toGraph = [] := by
    rw [Index.toGraph, hw.all]
  cases hs : b.s <;> cases hp : b.p <;> cases ho : b.o <;> simp only [] <;>
    first
      | (rw [hsp]; rfl)
      | (rw [hsu]; rfl)
      | (rw [hpr]; rfl)
      | (rw [hall]; rfl)
      | (split
         · rw [hpo]; rfl
         · rw [hpr]; rfl)
      | (split
         · rw [hob]; rfl
         · rw [hall]; rfl)

theorem backendEstimate_indexed_nil (b : PatternBound) :
    backendEstimate (indexedGraphBackend []) b = 0 := by
  have := backendSearch_indexed_nil b
  simp only [backendSearch, indexedGraphBackend, capsOfBackend, capsOfIndexed] at this
  simp only [backendEstimate, indexedGraphBackend, capsOfBackend, capsOfIndexed,
    igEstimate, this, List.length_nil]

/-! ## 5. A triple pattern whose every bound the restriction keeps -/

/-- Every bound `tp` can present, under any row, is one the restriction
keeps. A constant predicate in `P` gives this for `keep = (·.p ∈ P)`,
which is exactly what the predicate collector establishes. -/
def TpKept (keep : Triple → Bool) (tp : TriplePattern) : Prop :=
  ∀ mu : Binding, BoundKept keep (patternBoundFor tp mu)

theorem evalSingleTpBackend_restrict {keep : Triple → Bool} {tp : TriplePattern}
    (h : TpKept keep tp) (mu : Binding) (g : Graph) :
    evalSingleTpBackend tp (indexedGraphBackend (g.filter keep)) mu
      = evalSingleTpBackend tp (indexedGraphBackend g) mu := by
  simp only [evalSingleTpBackend, backendSearch_indexed_filter (h mu) g]

theorem evalSingleTpBackend_nil (tp : TriplePattern) (mu : Binding) :
    evalSingleTpBackend tp (indexedGraphBackend []) mu = [] := by
  simp only [evalSingleTpBackend, backendSearch_indexed_nil, List.filterMap_nil]

theorem estimateTpBackend_restrict {keep : Triple → Bool} {tp : TriplePattern}
    (h : TpKept keep tp) (mu : Binding) (g : Graph) :
    estimateTpBackend tp (indexedGraphBackend (g.filter keep)) mu
      = estimateTpBackend tp (indexedGraphBackend g) mu := by
  simp only [estimateTpBackend, backendEstimate_indexed_filter (h mu) g]

/-! ## 6. The planner picks the same pattern

`chooseBestTpBackend` orders by `estimateTpBackend`, and the estimates
agree, so the plan is the same list in the same order. -/

theorem chooseBest_mem :
    ∀ (ps : Bgp) (gb : GraphBackend) (mu : Binding) (tp : TriplePattern) (rest : Bgp),
      chooseBestTpBackend gb mu ps = some (tp, rest) →
      tp ∈ ps ∧ ∀ x ∈ rest, x ∈ ps
  | [], _, _, _, _, h => by simp [chooseBestTpBackend] at h
  | q :: qs, gb, mu, tp, rest, h => by
      simp only [chooseBestTpBackend] at h
      cases hc : chooseBestTpBackend gb mu qs with
      | none =>
          rw [hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          exact ⟨List.mem_cons_self, by intro x hx; simp at hx⟩
      | some pair =>
          obtain ⟨best, remaining⟩ := pair
          rw [hc] at h
          have hrec := chooseBest_mem qs gb mu best remaining hc
          by_cases hle : estimateTpBackend q gb mu <= estimateTpBackend best gb mu
          · simp only [hle, if_pos] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h1; subst h2
            exact ⟨List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ hx⟩
          · simp only [hle, if_neg, not_false_iff] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h1; subst h2
            refine ⟨List.mem_cons_of_mem _ hrec.1, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with hx | hx
            · exact hx ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hrec.2 x hx)

theorem chooseBestTpBackend_restrict {keep : Triple → Bool} (g : Graph) :
    ∀ (ps : Bgp) (mu : Binding), (∀ tp ∈ ps, TpKept keep tp) →
      chooseBestTpBackend (indexedGraphBackend (g.filter keep)) mu ps
        = chooseBestTpBackend (indexedGraphBackend g) mu ps
  | [], _, _ => rfl
  | q :: qs, mu, h => by
      have hq : TpKept keep q := h q List.mem_cons_self
      have hrest : ∀ tp ∈ qs, TpKept keep tp :=
        fun tp htp => h tp (List.mem_cons_of_mem _ htp)
      simp only [chooseBestTpBackend, chooseBestTpBackend_restrict g qs mu hrest]
      cases hc : chooseBestTpBackend (indexedGraphBackend g) mu qs with
      | none => rfl
      | some pair =>
          obtain ⟨best, remaining⟩ := pair
          have hbest : TpKept keep best := hrest best (chooseBest_mem qs _ mu best remaining hc).1
          simp only [estimateTpBackend_restrict hq mu g, estimateTpBackend_restrict hbest mu g]


/-! ## 7. The BGP evaluator over a restricted graph -/

theorem evalBgpFromMuFuel_restrict {keep : Triple → Bool} (g : Graph) :
    ∀ (fuel : Nat) (ps : Bgp) (mu : Binding), (∀ tp ∈ ps, TpKept keep tp) →
      evalBgpFromMuFuel ps (indexedGraphBackend (g.filter keep)) mu fuel
        = evalBgpFromMuFuel ps (indexedGraphBackend g) mu fuel := by
  intro fuel
  induction fuel with
  | zero => intro ps mu _; simp only [evalBgpFromMuFuel]
  | succ n ih =>
      intro ps mu hps
      have hacc : ∀ (rest : Bgp), (∀ tp ∈ rest, TpKept keep tp) →
          ∀ (rows acc : SolutionSeq),
            evalBgpConcatMapAcc rest (indexedGraphBackend (g.filter keep)) n rows acc
              = evalBgpConcatMapAcc rest (indexedGraphBackend g) n rows acc := by
        intro rest hrest rows
        induction rows with
        | nil => intro acc; simp only [evalBgpConcatMapAcc]
        | cons mu' more ihr =>
            intro acc
            simp only [evalBgpConcatMapAcc, ih rest mu' hrest, ihr]
      cases ps with
      | nil => simp only [evalBgpFromMuFuel]
      | cons q qs =>
          simp only [evalBgpFromMuFuel]
          rw [chooseBestTpBackend_restrict g (q :: qs) mu hps]
          cases hc : chooseBestTpBackend (indexedGraphBackend g) mu (q :: qs) with
          | none => rfl
          | some pair =>
              obtain ⟨tp, rest⟩ := pair
              have hmem := chooseBest_mem (q :: qs) _ mu tp rest hc
              have htp : TpKept keep tp := hps tp hmem.1
              have hrest : ∀ x ∈ rest, TpKept keep x := fun x hx => hps x (hmem.2 x hx)
              simp only [evalSingleTpBackend_restrict htp mu g,
                hacc rest hrest _ []]

theorem evalBgpBackend_restrict {keep : Triple → Bool} {ps : Bgp}
    (h : ∀ tp ∈ ps, TpKept keep tp) (g : Graph) :
    evalBgpBackend ps (indexedGraphBackend (g.filter keep))
      = evalBgpBackend ps (indexedGraphBackend g) :=
  evalBgpFromMuFuel_restrict g (ps.length + 1) ps Binding.empty h

/-- A non-empty BGP always gives the planner something to pick. -/
theorem chooseBest_cons_isSome (gb : GraphBackend) (mu : Binding)
    (q : TriplePattern) (qs : Bgp) :
    ∃ tp rest, chooseBestTpBackend gb mu (q :: qs) = some (tp, rest) := by
  simp only [chooseBestTpBackend]
  cases chooseBestTpBackend gb mu qs with
  | none => exact ⟨q, [], rfl⟩
  | some pair =>
      obtain ⟨best, remaining⟩ := pair
      by_cases hle : estimateTpBackend q gb mu <= estimateTpBackend best gb mu
      · exact ⟨q, qs, by simp [hle]⟩
      · exact ⟨best, q :: remaining, by simp [hle]⟩

/-- A non-empty BGP over the empty graph answers nothing. -/
theorem evalBgpFromMuFuel_nil :
    ∀ (fuel : Nat) (ps : Bgp) (mu : Binding), ps ≠ [] → 0 < fuel →
      evalBgpFromMuFuel ps (indexedGraphBackend []) mu fuel = [] := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ hf; exact absurd hf (by simp)
  | succ n _ =>
      intro ps mu hne _
      cases ps with
      | nil => exact absurd rfl hne
      | cons q qs =>
          obtain ⟨tp, rest, hc⟩ :=
            chooseBest_cons_isSome (indexedGraphBackend ([] : Graph)) mu q qs
          simp only [evalBgpFromMuFuel, hc, evalSingleTpBackend_nil,
            evalBgpConcatMapAcc, List.reverse_nil]

theorem evalBgpBackend_nil {ps : Bgp} (h : ps ≠ []) :
    evalBgpBackend ps (indexedGraphBackend []) = [] :=
  evalBgpFromMuFuel_nil (ps.length + 1) ps Binding.empty h (Nat.succ_pos _)

end L4Factoidal.SPARQL.DatasetRestriction
