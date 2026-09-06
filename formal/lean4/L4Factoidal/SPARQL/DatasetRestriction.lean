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
open L4Factoidal.SPARQL.StoreFastPath
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


/-! ## 8. The fragment

`plannerFragment` is the shape the induction below covers, and — after
the narrowing that lands with it — the shape all three collectors of
`Storage/ShardManifest.lean` admit. Three exclusions carry a reason
beyond "the induction does not reach it":

* **A nested `GRAPH`.** §18.6 gives `GRAPH <n> { P }` no solutions when
  the dataset does not name `n`, WHATEVER `P` is. An entry set that
  drops every entry of graph `n` therefore changes the answer of
  `GRAPH <n> { GRAPH <m> { ?s :p ?o } }`, because the inner pattern
  reads graph `m` and never touches `n`. The body of a `GRAPH` must be
  `graphFree`.
* **An empty BGP**, for the same reason one level down: it answers one
  solution without reading the active graph.
* **A `FILTER` or `OPTIONAL` condition that is not `Expr.backendLocal`.**
  `evalPatternBackend` materialises the whole dataset for those and runs
  the algebra evaluator, which is a second evaluator this induction does
  not cover.

Refusing a shape only makes the planner read more entries. -/

/-- No `GRAPH` anywhere inside. -/
def graphFree : QueryPattern → Bool
  | .bgp _ => true
  | .empty => true
  | .values _ _ => true
  | .propertyPath _ _ _ => true
  | .join a b | .union a b | .minus a b | .lateral a b => graphFree a && graphFree b
  | .leftJoin a b _ => graphFree a && graphFree b
  | .filter _ p | .bind _ _ p => graphFree p
  | .graph _ _ => false
  | .service _ _ _ | .serviceVar _ _ _ => false
  | .subSelect _ => false

/-- The shape the restriction theorem covers. -/
def plannerFragment : QueryPattern → Bool
  | .bgp ps => !ps.isEmpty
  | .join a b | .union a b | .minus a b => plannerFragment a && plannerFragment b
  | .leftJoin a b c => c.backendLocal && plannerFragment a && plannerFragment b
  | .filter c p => c.backendLocal && plannerFragment p
  | .graph (.iri _) p => graphFree p && plannerFragment p
  | _ => false

/-- The constant graph names the fragment reads. -/
def graphNamesIn : QueryPattern → List WfIri
  | .join a b | .union a b | .minus a b => graphNamesIn a ++ graphNamesIn b
  | .leftJoin a b _ => graphNamesIn a ++ graphNamesIn b
  | .filter _ p => graphNamesIn p
  | .graph (.iri i) p => i :: graphNamesIn p
  | _ => []

/-- Every bound the pattern's triple patterns can present survives the
restriction. -/
def PatternKept (keep : Triple → Bool) : QueryPattern → Prop
  | .bgp ps => ∀ tp ∈ ps, TpKept keep tp
  | .join a b | .union a b | .minus a b =>
      PatternKept keep a ∧ PatternKept keep b
  | .leftJoin a b _ => PatternKept keep a ∧ PatternKept keep b
  | .filter _ p => PatternKept keep p
  | .graph _ p => PatternKept keep p
  | _ => True

/-! ## 9. The dataset relation

`indexedDatasetBackend` keys its named backends by the raw `Iri` of the
graph name, so the relation is stated over the same key. -/

def ngKey (ng : NamedGraph) : Iri :=
  match ng.name with
  | .iri i => i.val
  | .bnode b => b

def lookupGraph : List NamedGraph → Iri → Option Graph
  | [], _ => none
  | ng :: rest, n => if ngKey ng == n then some ng.graph else lookupGraph rest n

theorem lookupNamedBackend_indexed (d : Dataset) (n : Iri) :
    lookupNamedBackend n (indexedDatasetBackend d).named
      = (lookupGraph d.named n).map indexedGraphBackend := by
  simp only [indexedDatasetBackend]
  induction d.named with
  | nil => rfl
  | cons ng rest ih =>
      obtain ⟨nm, gr⟩ := ng
      simp only [List.map_cons, lookupNamedBackend, lookupGraph, ngKey]
      cases nm with
      | iri i => by_cases h : (i.val == n) = true <;> simp [h, ih]
      | bnode b => by_cases h : (b == n) = true <;> simp [h, ih]

/-- What the planner leaves behind. The default graph is filtered by
`keep`. A named graph the pattern can read is either filtered by `keep`
as well, or gone — and gone only when `keep` empties it, which is what
`datasetOfQuads` does with a graph whose every row the planner dropped.

A graph the pattern CANNOT read is unconstrained: the graph-name
collector may have dropped its entries outright. -/
structure DatasetRestricted (keep : Triple → Bool) (readable : List WfIri)
    (d dr : Dataset) : Prop where
  dflt : dr.default = d.default.filter keep
  named : ∀ i : WfIri, i ∈ readable →
    lookupGraph dr.named i.val = (lookupGraph d.named i.val).map (fun g => g.filter keep)
    ∨ (lookupGraph dr.named i.val = none ∧
       ∀ g, lookupGraph d.named i.val = some g → g.filter keep = [])

/-! ## 10. A graph-free fragment over the empty active graph -/

theorem evalPatternBackend_nil (env : EvalEnv) (dsb : DatasetBackend) :
    ∀ p : QueryPattern, plannerFragment p = true → graphFree p = true →
      evalPatternBackend env dsb p (indexedGraphBackend []) = []
  | .bgp ps, hf, _ => by
      simp only [plannerFragment, Bool.not_eq_true'] at hf
      have hne : ps ≠ [] := by
        intro h; rw [h] at hf; simp at hf
      simpa [evalPatternBackend] using evalBgpBackend_nil hne
  | .join a b, hf, hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [evalPatternBackend,
        evalPatternBackend_nil env dsb a hf.1 hg.1,
        evalPatternBackend_nil env dsb b hf.2 hg.2, SPARQL.hashJoin]
      rfl
  | .union a b, hf, hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [evalPatternBackend,
        evalPatternBackend_nil env dsb a hf.1 hg.1,
        evalPatternBackend_nil env dsb b hf.2 hg.2, SPARQL.union]
      rfl
  | .minus a b, hf, hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [evalPatternBackend,
        evalPatternBackend_nil env dsb a hf.1 hg.1,
        evalPatternBackend_nil env dsb b hf.2 hg.2, SPARQL.minus, List.filter_nil]
  | .leftJoin a b c, hf, hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [evalPatternBackend, hf.1.1, if_pos,
        evalPatternBackend_nil env dsb a hf.1.2 hg.1,
        evalPatternBackend_nil env dsb b hf.2 hg.2, SPARQL.hashLeftJoin]
      rfl
  | .filter c p, hf, hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree] at hg
      simp only [evalPatternBackend, hf.1, if_pos,
        evalPatternBackend_nil env dsb p hf.2 hg, List.filter_nil]
  | .graph _ _, _, hg => by simp [graphFree] at hg
  | .lateral _ _, hf, _ => by simp [plannerFragment] at hf
  | .bind _ _ _, hf, _ => by simp [plannerFragment] at hf
  | .values _ _, hf, _ => by simp [plannerFragment] at hf
  | .service _ _ _, hf, _ => by simp [plannerFragment] at hf
  | .serviceVar _ _ _, hf, _ => by simp [plannerFragment] at hf
  | .subSelect _, hf, _ => by simp [plannerFragment] at hf
  | .propertyPath _ _ _, hf, _ => by simp [plannerFragment] at hf
  | .empty, hf, _ => by simp [plannerFragment] at hf

/-! ## 11. The pattern induction

The statement is an equality of LISTS: same rows, same order. -/

theorem evalPatternBackend_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : List WfIri} {d dr : Dataset}
    (hd : DatasetRestricted keep readable d dr) :
    ∀ (p : QueryPattern) (g : Graph), plannerFragment p = true → PatternKept keep p →
      (∀ i ∈ graphNamesIn p, i ∈ readable) →
      evalPatternBackend env (indexedDatasetBackend dr) p
          (indexedGraphBackend (g.filter keep))
        = evalPatternBackend env (indexedDatasetBackend d) p (indexedGraphBackend g)
  | .bgp ps, g, _, hk, _ => by
      simp only [evalPatternBackend]
      exact evalBgpBackend_restrict hk g
  | .join a b, g, hf, hk, hn => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [evalPatternBackend,
        evalPatternBackend_restrict env hd a g hf.1 hk.1 (fun i hi => hn i (Or.inl hi)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))]
  | .union a b, g, hf, hk, hn => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [evalPatternBackend,
        evalPatternBackend_restrict env hd a g hf.1 hk.1 (fun i hi => hn i (Or.inl hi)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))]
  | .minus a b, g, hf, hk, hn => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [evalPatternBackend,
        evalPatternBackend_restrict env hd a g hf.1 hk.1 (fun i hi => hn i (Or.inl hi)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))]
  | .leftJoin a b c, g, hf, hk, hn => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [evalPatternBackend, hf.1.1, if_pos,
        evalPatternBackend_restrict env hd a g hf.1.2 hk.1 (fun i hi => hn i (Or.inl hi)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))]
  | .filter c p, g, hf, hk, hn => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn] at hn
      simp only [evalPatternBackend, hf.1, if_pos,
        evalPatternBackend_restrict env hd p g hf.2 hk hn]
  | .graph (.iri i) p, g, hf, hk, hn => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      have hi : i ∈ readable := hn i (by simp [graphNamesIn])
      have hn' : ∀ j ∈ graphNamesIn p, j ∈ readable := by
        intro j hj
        exact hn j (by simp [graphNamesIn, hj])
      simp only [evalPatternBackend, lookupNamedBackend_indexed]
      rcases hd.named i hi with h | ⟨h1, h2⟩
      · rw [h]
        cases hl : lookupGraph d.named i.val with
        | none => simp only [Option.map_none]
        | some g' =>
            simp only [Option.map_some]
            exact evalPatternBackend_restrict env hd p g' hf.2 hk hn'
      · rw [h1]
        cases hl : lookupGraph d.named i.val with
        | none => simp only [Option.map_none]
        | some g' =>
            simp only [Option.map_none, Option.map_some]
            have hz : g'.filter keep = [] := h2 g' hl
            have hres := evalPatternBackend_restrict env hd p g' hf.2 hk hn'
            rw [hz] at hres
            rw [← hres]
            exact (evalPatternBackend_nil env (indexedDatasetBackend dr) p hf.2 hf.1).symm
  | .graph (.var _) _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .graph (.bnode _) _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .graph (.literal _) _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .graph (.tripleTerm _ _ _) _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .lateral _ _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .bind _ _ _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .values _ _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .service _ _ _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .serviceVar _ _ _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .subSelect _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .propertyPath _ _ _, _, hf, _, _ => by simp [plannerFragment] at hf
  | .empty, _, hf, _, _ => by simp [plannerFragment] at hf

/-! ## 12. The fast paths

`evalSelectBackendOnGraph` tries three detectors before the pattern
evaluator, and `evalSelectBackendDataset` a fourth. Each detector is a
function of the QUERY alone, so both sides take the same branch; what
is left is one invariance argument per branch. Two branches close
outright: the GROUP BY ?g detector needs `GRAPH ?v`, which the fragment
refuses, and the GROUP BY ?p resolver needs a backend with a
`distinctPredicates` capability, which the in-memory index does not
have. -/

theorem detectStreamingCountGroupByGraph_none (q : Query)
    (h : plannerFragment q.pattern = true) :
    detectStreamingCountGroupByGraph q = none := by
  cases hqp : q.pattern <;>
    simp only [detectStreamingCountGroupByGraph, hqp] <;>
    repeat' split
  all_goals (try rfl)
  all_goals simp_all [plannerFragment]

theorem distinctPredicates_indexed (g : Graph) :
    (capsOfBackend (indexedGraphBackend g)).distinctPredicates = none := rfl

theorem resolveStreamingCountGroupByPredicate_none (q : Query) (gb : GraphBackend)
    (dsb : DatasetBackend)
    (h1 : (capsOfBackend gb).distinctPredicates = none)
    (h2 : ∀ n t, lookupNamedBackend n dsb.named = some t →
      (capsOfBackend t).distinctPredicates = none) :
    resolveStreamingCountGroupByPredicate q gb dsb = none := by
  simp only [resolveStreamingCountGroupByPredicate]
  split
  · rfl
  · rename_i predVar countAlias scope _
    split
    · rfl
    · rename_i target heq2
      have hnone : (capsOfBackend target).distinctPredicates = none := by
        cases scope with
        | none =>
            simp only [Option.some.injEq] at heq2
            subst heq2
            exact h1
        | some gn => exact h2 _ _ heq2
      rw [hnone]

theorem lookupNamedBackend_indexed_distinct (d : Dataset) (n : Iri)
    (t : GraphBackend) (h : lookupNamedBackend n (indexedDatasetBackend d).named = some t) :
    (capsOfBackend t).distinctPredicates = none := by
  rw [lookupNamedBackend_indexed] at h
  cases hl : lookupGraph d.named n with
  | none => rw [hl] at h; simp at h
  | some g' =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact distinctPredicates_indexed g'

theorem resolveStreamingCountGroupByPredicate_indexed (q : Query) (d : Dataset)
    (g : Graph) :
    resolveStreamingCountGroupByPredicate q (indexedGraphBackend g)
      (indexedDatasetBackend d) = none :=
  resolveStreamingCountGroupByPredicate_none q _ _ (distinctPredicates_indexed g)
    (lookupNamedBackend_indexed_distinct d)

theorem extractSingleTpBgpScoped_bare {p : QueryPattern} {tp : TriplePattern} :
    extractSingleTpBgpScoped p = some (tp, none) → p = .bgp [tp] := by
  intro h
  unfold extractSingleTpBgpScoped at h
  split at h <;> simp_all

theorem extractSingleTpBgpScoped_scoped {p : QueryPattern} {tp : TriplePattern}
    {gname : WfIri} :
    extractSingleTpBgpScoped p = some (tp, some gname) →
    p = .graph (.iri gname) (.bgp [tp]) := by
  intro h
  unfold extractSingleTpBgpScoped at h
  split at h <;> simp_all

theorem detectStreamingCountStar_extract {q : Query} {v : VarName}
    {tp : TriplePattern} {scope : Option WfIri} :
    detectStreamingCountStar q = some (v, tp, scope) →
    extractSingleTpBgpScoped q.pattern = some (tp, scope) := by
  intro hh
  unfold detectStreamingCountStar at hh
  repeat' split at hh
  all_goals simp_all

theorem detectLimitSingleTpScoped_extract {q : Query} {tp : TriplePattern}
    {scope : LimitScope} {k : Nat} :
    detectLimitSingleTpScoped q = some (tp, scope, k) →
    extractSingleTpBgpLimitScope q.pattern = some (tp, scope) := by
  intro hh
  unfold detectLimitSingleTpScoped at hh
  repeat' split at hh
  all_goals simp_all

theorem extractSingleTpBgpLimitScope_active {p : QueryPattern} {tp : TriplePattern} :
    extractSingleTpBgpLimitScope p = some (tp, .active) → p = .bgp [tp] := by
  intro h
  unfold extractSingleTpBgpLimitScope at h
  split at h <;> simp_all

theorem extractSingleTpBgpLimitScope_named {p : QueryPattern} {tp : TriplePattern}
    {gname : WfIri} :
    extractSingleTpBgpLimitScope p = some (tp, .named gname) →
    p = .graph (.iri gname) (.bgp [tp]) := by
  intro h
  unfold extractSingleTpBgpLimitScope at h
  split at h <;> simp_all

/-- `GRAPH ?v { tp }` is outside the fragment, so the LIMIT push-down's
every-named-graph scope is unreachable here. -/
theorem extractSingleTpBgpLimitScope_everyNamed {p : QueryPattern}
    {tp : TriplePattern} {v : VarName} :
    extractSingleTpBgpLimitScope p = some (tp, .everyNamed v) →
    p = .graph (.var v) (.bgp [tp]) := by
  intro h
  unfold extractSingleTpBgpLimitScope at h
  split at h <;> simp_all

end L4Factoidal.SPARQL.DatasetRestriction
