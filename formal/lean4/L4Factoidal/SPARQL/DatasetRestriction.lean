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

theorem backendSearch_indexed_nil_aux (b : PatternBound) :
    L4Factoidal.RDF.igSearch (L4Factoidal.OWL.RL.Index.ofGraph []) b = [] := by
  have := backendSearch_indexed_nil b
  simpa [backendSearch, indexedGraphBackend, capsOfBackend, capsOfIndexed] using this

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
* **A `FILTER`, `OPTIONAL` or `BIND` expression that is not
  `Expr.backendLocal`.** `evalPatternBackend` materialises the whole
  dataset for those and runs the algebra evaluator, which is a second
  evaluator this induction does not cover.

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
  | .bgp _ => true
  | .empty => true
  | .join a b | .union a b | .minus a b => plannerFragment a && plannerFragment b
  | .leftJoin a b c => c.backendLocal && plannerFragment a && plannerFragment b
  | .filter c p => c.backendLocal && plannerFragment p
  | .bind e _ p => e.backendLocal && plannerFragment p
  | .graph (.iri _) p | .graph (.var _) p => graphFree p && plannerFragment p
  | _ => false

/-- The constant graph names the fragment reads. -/
def graphNamesIn : QueryPattern → List WfIri
  | .join a b | .union a b | .minus a b => graphNamesIn a ++ graphNamesIn b
  | .leftJoin a b _ => graphNamesIn a ++ graphNamesIn b
  | .filter _ p | .bind _ _ p => graphNamesIn p
  | .graph (.iri i) p => i :: graphNamesIn p
  | _ => []

/-- Whether a `GRAPH ?v` occurs. Such a pattern reads EVERY named graph, so
no graph-name selection may have been made when it does. -/
def graphVarIn : QueryPattern → Bool
  | .join a b | .union a b | .minus a b => graphVarIn a || graphVarIn b
  | .leftJoin a b _ => graphVarIn a || graphVarIn b
  | .filter _ p | .bind _ _ p => graphVarIn p
  | .graph (.var _) _ => true
  | .graph _ p => graphVarIn p
  | _ => false

/-- Every bound the pattern's triple patterns can present survives the
restriction. -/
def PatternKept (keep : Triple → Bool) : QueryPattern → Prop
  | .bgp [] => ∀ t, keep t = true
  | .bgp ps => ∀ tp ∈ ps, TpKept keep tp
  | .empty => ∀ t, keep t = true
  | .join a b | .union a b | .minus a b =>
      PatternKept keep a ∧ PatternKept keep b
  | .leftJoin a b _ => PatternKept keep a ∧ PatternKept keep b
  | .filter _ p | .bind _ _ p => PatternKept keep p
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

theorem lookupGraph_mem : ∀ (l : List NamedGraph) (n : Iri) (g : Graph),
    lookupGraph l n = some g → ∃ ng ∈ l, ng.graph = g
  | [], _, _, h => by simp [lookupGraph] at h
  | ng :: rest, n, g, h => by
      simp only [lookupGraph] at h
      split at h
      · exact ⟨ng, List.mem_cons_self, by simpa using h⟩
      · obtain ⟨x, hx, hxg⟩ := lookupGraph_mem rest n g h
        exact ⟨x, List.mem_cons_of_mem _ hx, hxg⟩

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

/-- The named graphs a query may read: `none` when the graph-name collector
established nothing, so every named graph is readable. -/
def readableName : Option (List WfIri) → WfIri → Prop
  | none, _ => True
  | some names, i => i ∈ names

/-- The named-graph list a restriction leaves: each graph filtered, and the
graphs `keep` empties gone. This is what `Storage/QuadDataset.lean`'s
`datasetOfQuads` produces from the shorter quad sequence — a graph with no
surviving row is absent, not empty. -/
def restrictNamed (keep : Triple → Bool) : List NamedGraph → List NamedGraph
  | [] => []
  | ng :: rest =>
      if (ng.graph.filter keep).isEmpty then restrictNamed keep rest
      else { ng with graph := ng.graph.filter keep } :: restrictNamed keep rest

/-- What the planner leaves behind. The default graph is filtered by `keep`.
A named graph the pattern can read is either filtered by `keep` as well, or
gone — and gone only when `keep` empties it. A graph the pattern CANNOT read
is unconstrained by `named`: the graph-name collector may have dropped its
entries outright.

`namedList` is the stronger statement `GRAPH ?v` needs, and is required only
when no graph-name selection was made (`readable = none`), which is exactly
when a `GRAPH ?v` may occur. `noEmpty` says the dataset carries no empty named
graph, which `datasetOfQuads` guarantees: a graph exists because a row put it
there. -/
structure DatasetRestricted (keep : Triple → Bool) (readable : Option (List WfIri))
    (d dr : Dataset) : Prop where
  dflt : dr.default = d.default.filter keep
  named : ∀ i : WfIri, readableName readable i →
    lookupGraph dr.named i.val = (lookupGraph d.named i.val).map (fun g => g.filter keep)
    ∨ (lookupGraph dr.named i.val = none ∧
       ∀ g, lookupGraph d.named i.val = some g → g.filter keep = [])
  namedList : readable = none → dr.named = restrictNamed keep d.named
  noEmpty : ∀ ng ∈ d.named, ng.graph ≠ []

theorem filter_all {keep : Triple → Bool} (h : ∀ t, keep t = true) :
    ∀ l : List Triple, l.filter keep = l
  | [] => rfl
  | t :: rest => by simp [List.filter_cons, h t, filter_all h rest]

/-! ## 10. A graph-free fragment over the empty active graph -/

theorem evalPatternBackend_nil (env : EvalEnv) (dsb : DatasetBackend)
    (keep : Triple → Bool) :
    ∀ p : QueryPattern, plannerFragment p = true → graphFree p = true → PatternKept keep p →
      evalPatternBackend env dsb p (indexedGraphBackend []) = [] ∨ (∀ t, keep t = true)
  | .bgp [], _, _, hk => Or.inr hk
  | .bgp (tp :: rest), _, _, hk => by
      refine Or.inl ?_
      simpa [evalPatternBackend] using evalBgpBackend_nil (ps := tp :: rest) (by simp)
  | .empty, _, _, hk => Or.inr hk
  | .join a b, hf, hg, hk => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [PatternKept] at hk
      rcases evalPatternBackend_nil env dsb keep a hf.1 hg.1 hk.1 with ha | ha
      · rcases evalPatternBackend_nil env dsb keep b hf.2 hg.2 hk.2 with hb | hb
        · exact Or.inl (by simp only [evalPatternBackend, ha, hb, SPARQL.hashJoin]; rfl)
        · exact Or.inr hb
      · exact Or.inr ha
  | .union a b, hf, hg, hk => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [PatternKept] at hk
      rcases evalPatternBackend_nil env dsb keep a hf.1 hg.1 hk.1 with ha | ha
      · rcases evalPatternBackend_nil env dsb keep b hf.2 hg.2 hk.2 with hb | hb
        · refine Or.inl ?_
          simp only [evalPatternBackend, ha, hb, SPARQL.union]
          rfl
        · exact Or.inr hb
      · exact Or.inr ha
  | .minus a b, hf, hg, hk => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [PatternKept] at hk
      rcases evalPatternBackend_nil env dsb keep a hf.1 hg.1 hk.1 with ha | ha
      · exact Or.inl (by simp only [evalPatternBackend, ha, SPARQL.minus, List.filter_nil])
      · exact Or.inr ha
  | .leftJoin a b c, hf, hg, hk => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree, Bool.and_eq_true] at hg
      simp only [PatternKept] at hk
      rcases evalPatternBackend_nil env dsb keep a hf.1.2 hg.1 hk.1 with ha | ha
      · refine Or.inl ?_
        simp only [evalPatternBackend, hf.1.1, if_pos, ha, SPARQL.hashLeftJoin]
        rfl
      · exact Or.inr ha
  | .filter c p, hf, hg, hk => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree] at hg
      simp only [PatternKept] at hk
      rcases evalPatternBackend_nil env dsb keep p hf.2 hg hk with ha | ha
      · exact Or.inl (by simp only [evalPatternBackend, hf.1, if_pos, ha, List.filter_nil])
      · exact Or.inr ha
  | .graph _ _, _, hg, _ => by simp [graphFree] at hg
  | .lateral _ _, hf, _, _ => by simp [plannerFragment] at hf
  | .bind e v p, hf, hg, hk => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphFree] at hg
      simp only [PatternKept] at hk
      rcases evalPatternBackend_nil env dsb keep p hf.2 hg hk with h | h
      · exact Or.inl (by
          simp only [evalPatternBackend, hf.1, if_pos, h, bindRowsFresh])
      · exact Or.inr h
  | .values _ _, hf, _, _ => by simp [plannerFragment] at hf
  | .service _ _ _, hf, _, _ => by simp [plannerFragment] at hf
  | .serviceVar _ _ _, hf, _, _ => by simp [plannerFragment] at hf
  | .subSelect _, hf, _, _ => by simp [plannerFragment] at hf
  | .propertyPath _ _ _, hf, _, _ => by simp [plannerFragment] at hf

/-- `indexedDatasetBackend`'s named list, in the shape the `GRAPH ?v` arm
walks. -/
theorem indexedDatasetBackend_named (d : Dataset) :
    (indexedDatasetBackend d).named
      = d.named.map (fun ng => (⟨ngKey ng, indexedGraphBackend ng.graph⟩ : NamedGraphBackend)) :=
  rfl

theorem ngKey_graph (ng : NamedGraph) (g : Graph) :
    ngKey { ng with graph := g } = ngKey ng := rfl

theorem restrictNamed_cons (keep : Triple → Bool) (ng : NamedGraph) (rest : List NamedGraph) :
    restrictNamed keep (ng :: rest)
      = (if (ng.graph.filter keep).isEmpty then restrictNamed keep rest
         else { ng with graph := ng.graph.filter keep } :: restrictNamed keep rest) := by
  simp only [restrictNamed]

/-- The `GRAPH ?v` arm walks the whole named list. A graph the restriction
empties contributes nothing on either side, so dropping it from the list
changes neither the rows nor their order. -/
theorem graphVar_flatMap_restrict {keep : Triple → Bool}
    (F G : NamedGraphBackend → SolutionSeq)
    (hkeepG : ∀ ng : NamedGraph,
        F ⟨ngKey ng, indexedGraphBackend (ng.graph.filter keep)⟩
          = G ⟨ngKey ng, indexedGraphBackend ng.graph⟩)
    (hdropG : ∀ ng : NamedGraph, ng.graph ≠ [] → ng.graph.filter keep = [] →
        G ⟨ngKey ng, indexedGraphBackend ng.graph⟩ = []) :
    ∀ l : List NamedGraph, (∀ ng ∈ l, ng.graph ≠ []) →
      ((restrictNamed keep l).map
        (fun ng => (⟨ngKey ng, indexedGraphBackend ng.graph⟩ : NamedGraphBackend))).flatMap F
      = (l.map
          (fun ng => (⟨ngKey ng, indexedGraphBackend ng.graph⟩ : NamedGraphBackend))).flatMap G := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons ng rest ih =>
      intro hne
      rw [restrictNamed_cons]
      by_cases hz : (ng.graph.filter keep).isEmpty = true
      · rw [if_pos hz, List.map_cons, List.flatMap_cons,
            hdropG ng (hne ng List.mem_cons_self) (List.isEmpty_iff.mp hz), List.nil_append,
            ih (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
      · rw [if_neg hz, List.map_cons, List.map_cons, List.flatMap_cons, List.flatMap_cons,
            ngKey_graph, hkeepG ng, ih (fun x hx => hne x (List.mem_cons_of_mem _ hx))]

/-! ## 11. The pattern induction

The statement is an equality of LISTS: same rows, same order. -/

theorem evalPatternBackend_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset}
    (hd : DatasetRestricted keep readable d dr) :
    ∀ (p : QueryPattern) (g : Graph), plannerFragment p = true → PatternKept keep p →
      (∀ i ∈ graphNamesIn p, readableName readable i) →
      (graphVarIn p = true → readable = none) →
      evalPatternBackend env (indexedDatasetBackend dr) p
          (indexedGraphBackend (g.filter keep))
        = evalPatternBackend env (indexedDatasetBackend d) p (indexedGraphBackend g)
  | .bgp [], g, _, _, _, _ => by
      simp only [evalPatternBackend]
      exact evalBgpBackend_restrict (ps := []) (by intro tp htp; simp at htp) g
  | .bgp (tp :: rest), g, _, hk, _, _ => by
      simp only [evalPatternBackend]
      exact evalBgpBackend_restrict hk g
  | .empty, _, _, _, _, _ => by simp only [evalPatternBackend]
  | .join a b, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [graphVarIn, Bool.or_eq_true] at hv
      simp only [evalPatternBackend,
        evalPatternBackend_restrict env hd a g hf.1 hk.1 (fun i hi => hn i (Or.inl hi))
          (fun h => hv (Or.inl h)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))
          (fun h => hv (Or.inr h))]
  | .union a b, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [graphVarIn, Bool.or_eq_true] at hv
      simp only [evalPatternBackend,
        evalPatternBackend_restrict env hd a g hf.1 hk.1 (fun i hi => hn i (Or.inl hi))
          (fun h => hv (Or.inl h)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))
          (fun h => hv (Or.inr h))]
  | .minus a b, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [graphVarIn, Bool.or_eq_true] at hv
      simp only [evalPatternBackend,
        evalPatternBackend_restrict env hd a g hf.1 hk.1 (fun i hi => hn i (Or.inl hi))
          (fun h => hv (Or.inl h)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))
          (fun h => hv (Or.inr h))]
  | .leftJoin a b c, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn, List.mem_append] at hn
      simp only [graphVarIn, Bool.or_eq_true] at hv
      simp only [evalPatternBackend, hf.1.1, if_pos,
        evalPatternBackend_restrict env hd a g hf.1.2 hk.1 (fun i hi => hn i (Or.inl hi))
          (fun h => hv (Or.inl h)),
        evalPatternBackend_restrict env hd b g hf.2 hk.2 (fun i hi => hn i (Or.inr hi))
          (fun h => hv (Or.inr h))]
  | .filter c p, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn] at hn
      simp only [graphVarIn] at hv
      simp only [evalPatternBackend, hf.1, if_pos,
        evalPatternBackend_restrict env hd p g hf.2 hk hn hv]
  | .graph (.iri i) p, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphVarIn] at hv
      have hi : readableName readable i := hn i (by simp [graphNamesIn])
      have hn' : ∀ j ∈ graphNamesIn p, readableName readable j := by
        intro j hj
        exact hn j (by simp [graphNamesIn, hj])
      simp only [evalPatternBackend, lookupNamedBackend_indexed]
      rcases hd.named i hi with h | ⟨h1, h2⟩
      · rw [h]
        cases hl : lookupGraph d.named i.val with
        | none => simp only [Option.map_none]
        | some g' =>
            simp only [Option.map_some]
            exact evalPatternBackend_restrict env hd p g' hf.2 hk hn' hv
      · rw [h1]
        cases hl : lookupGraph d.named i.val with
        | none => simp only [Option.map_none]
        | some g' =>
            simp only [Option.map_none, Option.map_some]
            have hz : g'.filter keep = [] := h2 g' hl
            have hres := evalPatternBackend_restrict env hd p g' hf.2 hk hn' hv
            rw [hz] at hres
            rw [← hres]
            rcases evalPatternBackend_nil env (indexedDatasetBackend dr) keep p hf.2 hf.1 hk
              with hn0 | htrue
            · exact hn0.symm
            · exfalso
              have hgg : g'.filter keep = g' := filter_all htrue g'
              have hg'nil : g' = [] := by rw [← hgg, hz]
              obtain ⟨ng, hng, hngg⟩ := lookupGraph_mem d.named i.val g' hl
              exact hd.noEmpty ng hng (by rw [hngg, hg'nil])
  | .graph (.var v) p, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      have hnone : readable = none := hv (by simp [graphVarIn])
      have hn' : ∀ j ∈ graphNamesIn p, readableName readable j := by
        intro j _
        rw [hnone]
        trivial
      have hv' : graphVarIn p = true → readable = none := fun _ => hnone
      have hkeepG : ∀ ng : NamedGraph,
          (match wfIriOf? (ngKey ng) with
           | none => []
           | some i =>
               (evalPatternBackend env (indexedDatasetBackend dr) p
                 (indexedGraphBackend (ng.graph.filter keep))).filterMap
                 (fun mu => Binding.bindIfCompatible v (Term.iri i) mu))
          = (match wfIriOf? (ngKey ng) with
             | none => []
             | some i =>
                 (evalPatternBackend env (indexedDatasetBackend d) p
                   (indexedGraphBackend ng.graph)).filterMap
                   (fun mu => Binding.bindIfCompatible v (Term.iri i) mu)) := by
        intro ng
        simp only [evalPatternBackend_restrict env hd p ng.graph hf.2 hk hn' hv']
      have hdropG : ∀ ng : NamedGraph, ng.graph ≠ [] → ng.graph.filter keep = [] →
          (match wfIriOf? (ngKey ng) with
           | none => []
           | some i =>
               (evalPatternBackend env (indexedDatasetBackend d) p
                 (indexedGraphBackend ng.graph)).filterMap
                 (fun mu => Binding.bindIfCompatible v (Term.iri i) mu)) = [] := by
        intro ng hgne hz
        have hres := evalPatternBackend_restrict env hd p ng.graph hf.2 hk hn' hv'
        rw [hz] at hres
        rcases evalPatternBackend_nil env (indexedDatasetBackend dr) keep p hf.2 hf.1 hk
          with hn0 | htrue
        · rw [← hres, hn0]
          cases wfIriOf? (ngKey ng) <;> rfl
        · exact absurd (by rw [← filter_all htrue ng.graph, hz]) hgne
      simp only [evalPatternBackend, indexedDatasetBackend_named, hd.namedList hnone]
      refine graphVar_flatMap_restrict _ _ ?_ ?_ d.named hd.noEmpty
      · intro ng
        simp only []
        exact hkeepG ng
      · intro ng hgne hz
        simp only []
        exact hdropG ng hgne hz
  | .graph (.bnode _) _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .graph (.literal _) _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .graph (.tripleTerm _ _ _) _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .lateral _ _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .bind e v p, g, hf, hk, hn, hv => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [PatternKept] at hk
      simp only [graphNamesIn] at hn
      simp only [graphVarIn] at hv
      simp only [evalPatternBackend, hf.1, if_pos,
        evalPatternBackend_restrict env hd p g hf.2 hk hn hv]
  | .values _ _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .service _ _ _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .serviceVar _ _ _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .subSelect _, _, hf, _, _, _ => by simp [plannerFragment] at hf
  | .propertyPath _ _ _, _, hf, _, _, _ => by simp [plannerFragment] at hf

/-! ## 12. The fast paths

`evalSelectBackendOnGraph` tries three detectors before the pattern
evaluator, and `evalSelectBackendDataset` a fourth. Each detector is a
function of the QUERY alone, so both sides take the same branch; what
is left is one invariance argument per branch. Two branches close
outright: the GROUP BY ?g detector needs `GRAPH ?v`, which the fragment
refuses, and the GROUP BY ?p resolver needs a backend with a
`distinctPredicates` capability, which the in-memory index does not
have. -/

theorem extractSingleTpBgp_eq {p : QueryPattern} {tp : TriplePattern} :
    extractSingleTpBgp p = some tp → p = .bgp [tp] := by
  intro h
  unfold extractSingleTpBgp at h
  split at h <;> simp_all

/-- What `SELECT ?g (COUNT(*) AS ?n) … GROUP BY ?g` needs: `GRAPH ?g` over a
triple pattern whose three positions are all variables. -/
theorem detectStreamingCountGroupByGraph_shape {q : Query} {gv nv : VarName}
    (hh : detectStreamingCountGroupByGraph q = some (gv, nv)) :
    ∃ w tp sv pv ov, q.pattern = .graph (.var w) (.bgp [tp])
      ∧ tp.s = .var sv ∧ tp.p = .var pv ∧ tp.o = .var ov := by
  unfold detectStreamingCountGroupByGraph at hh
  repeat' split at hh
  all_goals simp_all
  all_goals
    (rename_i h1 h2 h3 h4 h5 h6 h7 h8
     exact ⟨gv, _, ⟨rfl, extractSingleTpBgp_eq h3⟩, ⟨_, h4⟩, ⟨_, h5⟩, ⟨_, h6⟩⟩)

/-- A restriction that keeps every triple, over a dataset with no empty named
graph, is the identity. -/
theorem restrictNamed_trivial {keep : Triple → Bool} (h : ∀ t, keep t = true) :
    ∀ l : List NamedGraph, (∀ ng ∈ l, ng.graph ≠ []) → restrictNamed keep l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons ng rest ih =>
      intro hne
      have hg : ng.graph.filter keep = ng.graph := filter_all h ng.graph
      have hgne : ng.graph ≠ [] := hne ng List.mem_cons_self
      have hemp : (ng.graph.filter keep).isEmpty = false := by
        rw [hg]
        cases hgg : ng.graph with
        | nil => exact absurd hgg hgne
        | cons a b => rfl
      have h2 : ng.graph.isEmpty = false := by rw [← hg]; exact hemp
      simp only [restrictNamed, hg, h2, Bool.false_eq_true, if_false,
        ih (fun x hx => hne x (List.mem_cons_of_mem _ hx))]

theorem DatasetRestricted.trivial_eq {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset}
    (hd : DatasetRestricted keep readable d dr) (h : ∀ t, keep t = true)
    (hnone : readable = none) : dr = d := by
  have hdef : dr.default = d.default := by
    rw [hd.dflt]
    exact filter_all h d.default
  have hnam : dr.named = d.named := by
    rw [hd.namedList hnone]
    exact restrictNamed_trivial h d.named hd.noEmpty
  cases dr; cases d
  simp_all

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

/-! ## 13. The graph a constant `GRAPH` scope selects

Both scoped fast paths and the `GRAPH <iri>` arm need the same case
analysis: the restricted dataset either names the graph with its
`keep`-filter, or does not name it at all — and then `keep` had emptied
it. -/

/-- The three shapes a constant `GRAPH` scope can take after the
planner has run: the graph is there and filtered, it is absent from
both datasets, or it is absent from the restricted one because `keep`
emptied it. -/
theorem lookupNamedBackend_restrict_cases {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset}
    (hd : DatasetRestricted keep readable d dr) {gname : WfIri} (hi : readableName readable gname) :
    (∃ g', lookupNamedBackend gname.val (indexedDatasetBackend dr).named
             = some (indexedGraphBackend (g'.filter keep))
           ∧ lookupNamedBackend gname.val (indexedDatasetBackend d).named
             = some (indexedGraphBackend g'))
    ∨ (lookupNamedBackend gname.val (indexedDatasetBackend dr).named = none
       ∧ lookupNamedBackend gname.val (indexedDatasetBackend d).named = none)
    ∨ (∃ g', g'.filter keep = []
         ∧ lookupNamedBackend gname.val (indexedDatasetBackend dr).named = none
         ∧ lookupNamedBackend gname.val (indexedDatasetBackend d).named
           = some (indexedGraphBackend g')) := by
  simp only [lookupNamedBackend_indexed]
  rcases hd.named gname hi with h | ⟨h1, h2⟩
  · rw [h]
    cases hl : lookupGraph d.named gname.val with
    | none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | some g' => exact Or.inl ⟨g', rfl, rfl⟩
  · rw [h1]
    cases hl : lookupGraph d.named gname.val with
    | none => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | some g' => exact Or.inr (Or.inr ⟨g', h2 g' hl, rfl, rfl⟩)

theorem backendCountExact_indexed_nil (b : PatternBound) :
    backendCountExact (indexedGraphBackend []) b = 0 := by
  simp only [backendCountExact, indexedGraphBackend, capsOfBackend, capsOfIndexed,
    igEstimate, backendSearch_indexed_nil_aux, List.length_nil]

/-! ## 14. The LIMIT push-down -/

theorem evalLimitSingleTp_restrict {keep : Triple → Bool} {tp : TriplePattern}
    (h : TpKept keep tp) (sel : SelectClause) (g : Graph) (k : Nat) :
    evalLimitSingleTp sel tp (indexedGraphBackend (g.filter keep)) k
      = evalLimitSingleTp sel tp (indexedGraphBackend g) k := by
  simp only [evalLimitSingleTp,
    backendSearchLimited_indexed_filter (h Binding.empty) g k]

theorem evalLimitSingleTp_nil (sel : SelectClause) (tp : TriplePattern) (k : Nat) :
    evalLimitSingleTp sel tp (indexedGraphBackend []) k = [] := by
  have hs : backendSearchLimited (indexedGraphBackend []) (patternBoundFor tp Binding.empty) k
      = [] := by
    simp only [backendSearchLimited, indexedGraphBackend, capsOfBackend, capsOfIndexed,
      backendSearch_indexed_nil_aux, capsTakeN, List.take_nil]
  simp only [evalLimitSingleTp, hs, List.filterMap_nil, capsTakeN, List.take_nil]
  cases sel with
  | vars items => simp [projectSolutions]
  | all => rfl

theorem backendSearchLimited_indexed_nil (b : PatternBound) (n : Nat) :
    backendSearchLimited (indexedGraphBackend []) b n = [] := by
  simp only [backendSearchLimited, indexedGraphBackend, capsOfBackend, capsOfIndexed,
    backendSearch_indexed_nil_aux, capsTakeN, List.take_nil]

/-- Once the accumulator holds the limit, no further graph is read. -/
theorem limitGraphVarAcc_done (v : VarName) (tp : TriplePattern) (limit : Nat) :
    ∀ (l : List NamedGraphBackend) (acc : SolutionSeq), limit ≤ acc.length →
      limitGraphVarAcc v tp limit l acc = acc.reverse
  | [], _, _ => rfl
  | _ :: _, acc, h => by simp only [limitGraphVarAcc, if_pos h]

/-- The LIMIT push-down under `GRAPH ?v` walks the named list. A graph the
restriction empties returns no candidate, so it neither adds a row nor moves
the early stop. -/
theorem limitGraphVarAcc_restrict {keep : Triple → Bool} {tp : TriplePattern}
    (htp : TpKept keep tp) (v : VarName) (limit : Nat) :
    ∀ (l : List NamedGraph) (acc : SolutionSeq),
      limitGraphVarAcc v tp limit
          ((restrictNamed keep l).map
            (fun ng => (⟨ngKey ng, indexedGraphBackend ng.graph⟩ : NamedGraphBackend))) acc
        = limitGraphVarAcc v tp limit
            (l.map (fun ng => (⟨ngKey ng, indexedGraphBackend ng.graph⟩ : NamedGraphBackend)))
            acc := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons ng rest ih =>
      intro acc
      rw [restrictNamed_cons, List.map_cons]
      by_cases hlim : limit ≤ acc.length
      · rw [limitGraphVarAcc_done v tp limit _ acc hlim,
            limitGraphVarAcc_done v tp limit _ acc hlim]
      · by_cases hz : (ng.graph.filter keep).isEmpty = true
        · have hz' : ng.graph.filter keep = [] := List.isEmpty_iff.mp hz
          have hsearch : backendSearchLimited (indexedGraphBackend ng.graph)
              (patternBoundFor tp Binding.empty) (limit - acc.length) = [] := by
            rw [← backendSearchLimited_indexed_filter (htp Binding.empty) ng.graph
                  (limit - acc.length), hz', backendSearchLimited_indexed_nil]
          rw [if_pos hz, limitGraphVarAcc, if_neg hlim]
          cases wfIriOf? (ngKey ng) with
          | none => exact ih acc
          | some i =>
              simp only [hsearch, List.filterMap_nil, capsTakeN, List.take_nil,
                List.reverseAux]
              exact ih acc
        · have hkey : ngKey { ng with graph := ng.graph.filter keep } = ngKey ng := rfl
          rw [if_neg hz, List.map_cons, limitGraphVarAcc, limitGraphVarAcc,
            if_neg hlim, if_neg hlim, hkey,
            backendSearchLimited_indexed_filter (htp Binding.empty) ng.graph
              (limit - acc.length)]
          cases wfIriOf? (ngKey ng) with
          | none => exact ih acc
          | some i => exact ih _

/-! ## 15. SELECT and ASK -/

theorem evalSelectBackendOnGraph_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset} (hd : DatasetRestricted keep readable d dr)
    (q : Query) (hf : plannerFragment q.pattern = true) (hk : PatternKept keep q.pattern)
    (hn : ∀ i ∈ graphNamesIn q.pattern, readableName readable i)
    (hv : graphVarIn q.pattern = true → readable = none) :
    evalSelectBackendOnGraph env q (indexedGraphBackend dr.default) (indexedDatasetBackend dr)
      = evalSelectBackendOnGraph env q (indexedGraphBackend d.default)
          (indexedDatasetBackend d) := by
  rw [hd.dflt]
  cases hcs : detectStreamingCountStar q with
  | some triple =>
      obtain ⟨alias, tp, scope⟩ := triple
      have hex := detectStreamingCountStar_extract hcs
      cases scope with
      | none =>
          have hp : q.pattern = .bgp [tp] := extractSingleTpBgpScoped_bare hex
          have htp : TpKept keep tp := by
            rw [hp] at hk
            exact hk tp (List.mem_cons_self)
          simp only [evalSelectBackendOnGraph, hcs,
            backendCountExact_indexed_filter (htp Binding.empty) d.default]
      | some gname =>
          have hp : q.pattern = .graph (.iri gname) (.bgp [tp]) :=
            extractSingleTpBgpScoped_scoped hex
          have htp : TpKept keep tp := by
            rw [hp] at hk
            simp only [PatternKept] at hk
            exact hk tp (List.mem_cons_self)
          have hi : readableName readable gname := by
            refine hn gname ?_
            rw [hp]
            simp [graphNamesIn]
          simp only [evalSelectBackendOnGraph, hcs]
          rcases lookupNamedBackend_restrict_cases hd hi with
            ⟨g', hr, hl⟩ | ⟨hr, hl⟩ | ⟨g', hz, hr, hl⟩
          · simp only [hr, hl, backendCountExact_indexed_filter (htp Binding.empty) g']
          · simp only [hr, hl]
          · have hc := backendCountExact_indexed_filter (htp Binding.empty) g'
            rw [hz, backendCountExact_indexed_nil] at hc
            simp only [hr, hl, ← hc]
  | none =>
      cases hcl : detectLimitSingleTpScoped q with
      | none =>
          simp only [evalSelectBackendOnGraph, hcs, hcl,
            resolveStreamingCountGroupByPredicate_indexed]
          cases q.form with
          | select _ =>
              simp only [evalPatternBackend_restrict env hd q.pattern d.default hf hk hn hv]
          | construct _ => rfl
          | ask => rfl
          | describe _ => rfl
      | some tr =>
          obtain ⟨tp, scope, k⟩ := tr
          have hex := detectLimitSingleTpScoped_extract hcl
          simp only [evalSelectBackendOnGraph, hcs, hcl,
            resolveStreamingCountGroupByPredicate_indexed]
          cases q.form with
          | construct _ => rfl
          | ask => rfl
          | describe _ => rfl
          | select sel =>
              simp only [evalLimitSingleTpScoped]
              cases scope with
              | active =>
                  have hp : q.pattern = .bgp [tp] :=
                    extractSingleTpBgpLimitScope_active hex
                  have htp : TpKept keep tp := by
                    rw [hp] at hk
                    exact hk tp (List.mem_cons_self)
                  simp only [evalLimitSingleTp_restrict htp sel d.default k]
              | named gname =>
                  have hp : q.pattern = .graph (.iri gname) (.bgp [tp]) :=
                    extractSingleTpBgpLimitScope_named hex
                  have htp : TpKept keep tp := by
                    rw [hp] at hk
                    simp only [PatternKept] at hk
                    exact hk tp (List.mem_cons_self)
                  have hi : readableName readable gname := by
                    refine hn gname ?_
                    rw [hp]
                    simp [graphNamesIn]
                  simp only []
                  rcases lookupNamedBackend_restrict_cases hd hi with
                    ⟨g', hr, hl⟩ | ⟨hr, hl⟩ | ⟨g', hz, hr, hl⟩
                  · simp only [hr, hl, evalLimitSingleTp_restrict htp sel g' k]
                  · simp only [hr, hl]
                  · have hc := evalLimitSingleTp_restrict htp sel g' k
                    rw [hz, evalLimitSingleTp_nil] at hc
                    simp only [hr, hl, ← hc]
              | everyNamed w =>
                  have hp : q.pattern = .graph (.var w) (.bgp [tp]) :=
                    extractSingleTpBgpLimitScope_everyNamed hex
                  have htp : TpKept keep tp := by
                    rw [hp] at hk
                    simp only [PatternKept] at hk
                    exact hk tp List.mem_cons_self
                  have hnone : readable = none := by
                    refine hv ?_
                    rw [hp]
                    simp [graphVarIn]
                  simp only [indexedDatasetBackend_named, hd.namedList hnone,
                    limitGraphVarAcc_restrict htp w k d.named []]

theorem evalSelectBackendDataset_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset} (hd : DatasetRestricted keep readable d dr)
    (q : Query) (hf : plannerFragment q.pattern = true) (hk : PatternKept keep q.pattern)
    (hn : ∀ i ∈ graphNamesIn q.pattern, readableName readable i)
    (hv : graphVarIn q.pattern = true → readable = none) :
    evalSelectBackendDataset env q (indexedDatasetBackend dr)
      = evalSelectBackendDataset env q (indexedDatasetBackend d) := by
  cases hg : detectStreamingCountGroupByGraph q with
  | none =>
      simp only [evalSelectBackendDataset, hg]
      exact evalSelectBackendOnGraph_restrict env hd q hf hk hn hv
  | some pair =>
      obtain ⟨graphVar, countAlias⟩ := pair
      obtain ⟨w, tp, sv, pv, ov, hp, hs, hpp, ho⟩ :=
        detectStreamingCountGroupByGraph_shape hg
      have htp : TpKept keep tp := by
        rw [hp] at hk
        simp only [PatternKept] at hk
        exact hk tp List.mem_cons_self
      have hall : ∀ t, keep t = true := by
        intro t
        refine htp Binding.empty t ?_
        simp only [patternBoundFor, boundSubjectOfPattern, boundPredicateOfPattern,
          boundObjectOfPattern, hs, hpp, ho, Binding.lookup, Binding.empty, boundMatches]
        rfl
      have hnone : readable = none := by
        refine hv ?_
        rw [hp]
        simp [graphVarIn]
      rw [hd.trivial_eq hall hnone]

theorem backendDecodeFailure_indexed (g : Graph) :
    backendDecodeFailure (indexedGraphBackend g) = false := rfl

theorem evalAskBackend_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset} (hd : DatasetRestricted keep readable d dr)
    (q : Query) (hf : plannerFragment q.pattern = true) (hk : PatternKept keep q.pattern)
    (hn : ∀ i ∈ graphNamesIn q.pattern, readableName readable i)
    (hv : graphVarIn q.pattern = true → readable = none) :
    evalAskBackend env q (indexedDatasetBackend dr)
      = evalAskBackend env q (indexedDatasetBackend d) := by
  have hall : ∀ (x : Dataset), ∀ ngb ∈ (indexedDatasetBackend x).named,
      backendDecodeFailure ngb.backend = false := by
    intro x ngb hmem
    simp only [indexedDatasetBackend, List.mem_map] at hmem
    obtain ⟨ng, _, rfl⟩ := hmem
    exact backendDecodeFailure_indexed ng.graph
  have hdf : ∀ (x : Dataset),
      (backendDecodeFailure (indexedDatasetBackend x).default
        || (indexedDatasetBackend x).named.any
            (fun ngb => backendDecodeFailure ngb.backend)) = false := by
    intro x
    rw [show backendDecodeFailure (indexedDatasetBackend x).default = false from
      backendDecodeFailure_indexed _, Bool.false_or]
    simp only [List.any_eq_false]
    intro a ha
    simp [hall x a ha]
  cases hqf : q.form with
  | select _ => simp only [evalAskBackend, hqf]
  | construct _ => simp only [evalAskBackend, hqf]
  | describe _ => simp only [evalAskBackend, hqf]
  | ask =>
      have heval : evalPatternBackend env (indexedDatasetBackend dr) q.pattern
            (indexedDatasetBackend dr).default
          = evalPatternBackend env (indexedDatasetBackend d) q.pattern
            (indexedDatasetBackend d).default := by
        show evalPatternBackend env (indexedDatasetBackend dr) q.pattern
              (indexedGraphBackend dr.default) = _
        rw [hd.dflt]
        exact evalPatternBackend_restrict env hd q.pattern d.default hf hk hn hv
      simp only [evalAskBackend, hqf, heval, hdf dr, hdf d]

/-! ## 16. The two query entry points

Both rewrite the pattern's blank nodes before they evaluate anything
(`QueryPattern.rewriteBnodes`), so the hypotheses are about the
REWRITTEN pattern — which is what the collectors of
`Storage/ShardManifest.lean` also read, so that the run-time guard and
the theorem's hypothesis are one expression. -/

theorem runSelectQueryBackendDataset_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset} (hd : DatasetRestricted keep readable d dr)
    (q : Query)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runSelectQueryBackendDataset env q (indexedDatasetBackend dr)
      = runSelectQueryBackendDataset env q (indexedDatasetBackend d) := by
  simp only [runSelectQueryBackendDataset]
  exact evalSelectBackendDataset_restrict env hd _ hf hk hn hv

theorem runAskQueryBackendDataset_restrict (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {d dr : Dataset} (hd : DatasetRestricted keep readable d dr)
    (q : Query)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runAskQueryBackendDataset env q (indexedDatasetBackend dr)
      = runAskQueryBackendDataset env q (indexedDatasetBackend d) := by
  simp only [runAskQueryBackendDataset]
  exact evalAskBackend_restrict env hd _ hf hk hn hv

#print axioms evalPatternBackend_nil
#print axioms evalPatternBackend_restrict
#print axioms runSelectQueryBackendDataset_restrict
#print axioms runAskQueryBackendDataset_restrict

end L4Factoidal.SPARQL.DatasetRestriction
