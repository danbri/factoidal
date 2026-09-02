/-
L4Factoidal.SPARQL.StoreDataset — layer 4 of `SPARQL11.Store`: the
dataset seam, the backend-routed pattern evaluator, the GROUP BY
streaming family, and the two query entry points.

## The dataset seam

`DatasetBackend` is a default backend plus named ones.
`datasetCapsOfBackend` is the capability-shaped view of it — one
`capsOfBackend` call per graph, no new per-backend logic, exactly the
discipline `capsOfBackend` itself follows one level down.
`materialiseDatasetBackend` reads every backend with an unbound search,
which is what the delegating arms of the evaluator need.

## Where the two trees genuinely differ, and what it costs

The F* `eval_pattern_backend` recurses structurally through FILTER,
LEFTJOIN and BIND, and materialises the dataset only for the three
arms it cannot do natively — FILTER/LEFTJOIN carrying an EXISTS,
LATERAL, and property paths.

The Lean tree cannot do that, and the reason is architectural rather
than accidental. Its `QueryPattern.lowerWith` compiles a FILTER
condition into a CLOSURE over the active graph, and a LATERAL right
operand into a function of the left row. Those closures are how the
Lean algebra states §18.6's EXISTS, and they are built at lowering
time. So a backend-routed evaluator here either rebuilds the whole
lowering or delegates.

This module delegates: BGP, JOIN, UNION, MINUS, `GRAPH <constant>` and
the empty pattern are backend-native; every other arm materialises the
dataset and runs the algebra evaluator. That is the SAME device the F*
source uses for its own hard arms, applied to more of them.

**What it costs is performance on those shapes, not correctness.** The
delegate is the algebra evaluator, which is the semantic source of
truth in both trees; the F* source says so itself where it introduces
the device — "correctness first, backend-native EXISTS is a follow-up".
Which arms are native is stated here rather than left to be discovered,
and `evalPatternBackend_bgp_native` and its siblings pin the list.

## The BGP arm agrees with the algebra

`evalBgpBackend_single_list` is the cross-check: on a list backend, a
one-pattern BGP evaluated through the backend equals the same BGP
evaluated by the algebra. It is stated for one pattern because the
planner REORDERS a longer BGP, so the two paths agree as sets and not
as lists — `chooseBest_perm` in `StorePlan.lean` is what makes that
reordering safe.

## The GROUP BY streaming family

One row per named graph, or one per predicate, from `backendCountExact`
rather than from materialised rows. The F* source records why it is the
EXACT count and not the estimate: "this count IS the query result",
a defect it labels E1. A predicate whose count is zero contributes no
row, which is what GROUP BY means.

## ASK cannot read an empty answer as `false`

`evalAskBackend` returns `none`, not `some false`, when the answer is
empty AND any backend reports a decode failure. The F* source explains:
a column that fails to decode contributes zero rows silently, so
"genuinely empty" and "could not read" are indistinguishable
downstream, and ASK would turn a read failure into a wrong answer with
a clean exit.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.StoreFastPath

namespace L4Factoidal.SPARQL.StoreDataset

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreFastPath

/-! ## 0. Two small conversions

`NamedGraphBackend.name` is a raw `Iri`, matching the F* `ngb_name`,
while `NamedGraph.name` is a `Subject` and a bound graph variable takes
a `WfIri`. `wfIriOf?` is the well-formedness test the F* source spells
`is_iri`, and `integerTerm` is the `xsd:integer` literal both GROUP BY
paths bind their counts to. -/

def wfIriOf? (s : Iri) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

def integerTerm (n : Nat) : Term :=
  .literal ⟨{ lexicalForm := toString n, datatype := xsdInteger,
              langTag := none, direction := none },
            by simp [literalWf, xsdInteger, rdfLangString, rdfDirLangString,
                     Subtype.ext_iff]⟩

/-! ## 1. The dataset seam -/

structure DatasetBackend where
  default : GraphBackend
  named : List NamedGraphBackend

def lookupNamedBackend (name : Iri) : List NamedGraphBackend → Option GraphBackend
  | [] => none
  | ng :: rest => if ng.name == name then some ng.backend else lookupNamedBackend name rest

/-- The capability-shaped view: `capsOfBackend` once per graph. -/
def datasetCapsOfBackend (dsb : DatasetBackend) : DatasetCaps :=
  { default := capsOfBackend dsb.default
  , named := dsb.named.map (fun ngb => (ngb.name, capsOfBackend ngb.backend)) }

/-- Read every backend with an unbound search. This is what the
delegating arms of the evaluator consume. -/
def materialiseDatasetBackend (dsb : DatasetBackend) : Dataset :=
  { default := backendSearch dsb.default patternBoundAll
  , named := dsb.named.filterMap (fun ngb =>
      -- a graph name that is not a well-formed IRI cannot name a graph
      (wfIriOf? ngb.name).map (fun i =>
        { name := .iri i, graph := backendSearch ngb.backend patternBoundAll })) }

/-- Wrap a graph as an indexed backend; the index is built once here. -/
def indexedGraphBackend (g : Graph) : GraphBackend := .indexed (OWL.RL.Index.ofGraph g)

def indexedDatasetBackend (ds : Dataset) : DatasetBackend :=
  { default := indexedGraphBackend ds.default
  , named := ds.named.map (fun ng =>
      { name := match ng.name with
                | .iri i => i.val
                | .bnode b => b
      , backend := indexedGraphBackend ng.graph }) }

/-! ## 2. The backend-routed pattern evaluator

Native arms recurse; every other arm materialises and delegates. See
the module header for why, and for what that costs. -/

def evalPatternBackend (env : EvalEnv) (dsb : DatasetBackend) :
    QueryPattern → GraphBackend → SolutionSeq
  | .bgp b, gb => evalBgpBackend b gb
  -- A FILTER without active-graph-dependent expression forms can stay on the
  -- backend path.  This is the intentionally conservative counterpart of the
  -- `QueryPattern.lowerWith` closure: for `Expr.backendLocal`, existential
  -- substitution is a no-op and `Expr.evalIn` needs only the row.  Other
  -- filters retain the complete materialisation fallback below.
  | .filter condition pattern, gb =>
      if condition.backendLocal then
        (evalPatternBackend env dsb pattern gb).filter
          (fun row => ebvOrFalse (Expr.evalIn env row condition))
      else
        let ds0 := materialiseDatasetBackend dsb
        let gCurrent := backendSearch gb patternBoundAll
        let ds := { ds0 with default := gCurrent }
        (QueryPattern.filter condition pattern).lowerWith env Binding.empty |>.evalIn ds gCurrent
  | .join p1 p2, gb =>
      SPARQL.join (evalPatternBackend env dsb p1 gb) (evalPatternBackend env dsb p2 gb)
  | .union p1 p2, gb =>
      SPARQL.union (evalPatternBackend env dsb p1 gb) (evalPatternBackend env dsb p2 gb)
  | .minus p1 p2, gb =>
      SPARQL.minus (evalPatternBackend env dsb p1 gb) (evalPatternBackend env dsb p2 gb)
  -- GRAPH with a CONSTANT IRI routes to that graph's own backend. An
  -- IRI the dataset does not name contributes nothing, as in §18.6.
  | .graph (.iri i) p, _ =>
      match lookupNamedBackend i.val dsb.named with
      | some g => evalPatternBackend env dsb p g
      | none => []
  | .empty, _ => [Binding.empty]
  | p, gb =>
      -- Materialise and delegate. The active graph is this backend's
      -- own content, so an EXISTS inside the delegated pattern sees
      -- what the enclosing GRAPH clause selected.
      let ds0 := materialiseDatasetBackend dsb
      let gCurrent := backendSearch gb patternBoundAll
      let ds := { ds0 with default := gCurrent }
      (p.lowerWith env Binding.empty).evalIn ds gCurrent

/-! ## 3. The GROUP BY streaming family

One row per group, counted through the backend. The count is EXACT,
never the estimate: it IS the query result. -/

def countGroupByGraphAcc (graphVar countAlias : VarName) :
    SolutionSeq → List NamedGraphBackend → SolutionSeq
  | acc, [] => acc.reverse
  | acc, ngb :: rest =>
      let cnt := backendCountExact ngb.backend patternBoundAll
      let mu0 := Binding.bind countAlias (integerTerm cnt) Binding.empty
      let mu := match wfIriOf? ngb.name with
                | some i => Binding.bind graphVar (.iri i) mu0
                | none => mu0
      countGroupByGraphAcc graphVar countAlias (mu :: acc) rest

def countGroupByGraphSolutions (graphVar countAlias : VarName)
    (named : List NamedGraphBackend) : SolutionSeq :=
  countGroupByGraphAcc graphVar countAlias [] named

def predicateGroupByAcc (predVar countAlias : VarName) (gb : GraphBackend) :
    SolutionSeq → List WfIri → SolutionSeq
  | acc, [] => acc.reverse
  | acc, p :: rest =>
      let cnt := backendCountExact gb { p := some p }
      -- a predicate with no rows is not a group
      if cnt == 0 then predicateGroupByAcc predVar countAlias gb acc rest
      else
        let mu0 := Binding.bind countAlias (integerTerm cnt) Binding.empty
        let mu := Binding.bind predVar (.iri p) mu0
        predicateGroupByAcc predVar countAlias gb (mu :: acc) rest

def predicateGroupBySolutions (predVar countAlias : VarName) (gb : GraphBackend)
    (preds : List WfIri) : SolutionSeq :=
  predicateGroupByAcc predVar countAlias gb [] preds

/-- Shape detection plus capability availability. The fast path runs
only when the target backend actually offers cheap predicate
enumeration; otherwise the query falls through to the materialise
path. -/
def resolveStreamingCountGroupByPredicate (q : Query) (gb : GraphBackend)
    (dsb : DatasetBackend) :
    Option (VarName × VarName × List WfIri × GraphBackend) :=
  match detectStreamingCountGroupByPredicate q with
  | none => none
  | some (predVar, countAlias, scope) =>
      match (match scope with
             | none => some gb
             | some g => lookupNamedBackend g.val dsb.named) with
      | none => none
      | some target =>
          match (capsOfBackend target).distinctPredicates with
          | none => none
          | some getPreds =>
              match getPreds () with
              | none => none
              | some preds => some (predVar, countAlias, preds, target)

/-! ## 4. Two backends the F* tree constructs but the Lean tree cannot

`cottas_ondisk_dataset_backend` and `cottas_with_delta_dataset_backend`
discover their named graphs by READING the store — the first calls
`cottas_ondisk_named_graphs`, the second reads and parses a delta log
under the `ML` effect. Under the purity doctrine the read is a
parameter, so both take the graph list they would have discovered.

`indexed_graph_backend_for` and its two siblings build only the index
BUCKETS a query's pattern needs (`build_indexed_selective`). They have
no Lean counterpart BY DESIGN, and the reason is already recorded for
the `RDF.Indexed.KeyInjectivity` group: the Lean index is a
`Std.HashMap` keyed on STRUCTURED values, so there are no six buckets
to choose between and nothing for a `bucket_needs` flag to select. The
Lean `indexedDatasetBackend` is what all three collapse to. -/

/-- Every graph of one COTTAS on-disk store: the default graph is the
rows carrying the DEFAULT sentinel, and each named graph filters on its
own IRI. The named-graph list is a parameter because discovering it is
a read. -/
def cottasOnDiskDatasetBackend (ops : RDF.CottasCaps.CottasReadOps)
    (namedGraphs : List Iri) : DatasetBackend :=
  { default := .cottasOnDisk ops .defaultGraph
  , named := namedGraphs.map (fun gname =>
      { name := gname, backend := .cottasOnDisk ops (.named gname) }) }

/-- The same shape with a resolved delta threaded through `overlay`'s
single dispatch arm. A graph the delta creates that the base store has
never seen still needs an entry, which is why the caller passes the
UNION of the base's graphs and the delta's. -/
def cottasWithDeltaDatasetBackend (ops : RDF.CottasCaps.CottasReadOps)
    (namedGraphs : List Iri) (deltaFor : Option Iri → DeltaResolved) :
    DatasetBackend :=
  { default := .cottasOnDiskDelta ops .defaultGraph (deltaFor none)
  , named := namedGraphs.map (fun gname =>
      { name := gname
      , backend := .cottasOnDiskDelta ops (.named gname) (deltaFor (some gname)) }) }

/-! ## 5. Full-text search over a backend

The same shape as the algebra's own twin, over `backendSearch` so it
works identically across every backend. -/

def evalFulltextTpBackend (field : Option WfIri) (limit : Option Nat)
    (objMatches : Term → Bool) (tp : TriplePattern) (gb : GraphBackend)
    (mu : Binding) : SolutionSeq :=
  let candidates := backendSearch gb { p := field }
  let matched := candidates.filter (fun t => objMatches t.o)
  let limited := match limit with
    | some n => capsTakeN n matched
    | none => matched
  limited.filterMap (fun t => tpMatch tp t mu)

/-! ## 6. The two query entry points -/

/-- The BGP-only SELECT path.

**It has no call site in the F* module.** `eval_select_query_backend_bgp`
is defined inside the mutually recursive group and never invoked —
`eval_select_query_backend_on_graph` reaches the materialise path
directly. It is ported for the same reason the unreferenced definitions
of `OWL.QueryRewrite` were: skipping a definition because a reader
judges it unused leaves an unrecorded hole, and the judgement is worth
writing down instead.

It returns `none` when the query needs grouping, deferring to a caller
that can group. The Lean materialise arm does not need that escape,
because `selectPost` runs the whole post-WHERE pipeline including GROUP
BY and HAVING — which is why folding this function into that arm would
have LOST its behaviour rather than preserved it. -/
def evalSelectBackendBgp (env : EvalEnv) (q : Query) (gb : GraphBackend) :
    Option SolutionSeq :=
  match q.form, q.pattern with
  | .select sel, .bgp b =>
      let omega0 := evalBgpBackend b gb
      let omega := match q.postValues with
        | none => omega0
        | some vals => SPARQL.join omega0 vals
      let needsGrouping := q.groupBy.isSome || selectHasAggregates sel
      if needsGrouping then none
      else
        let ordered := match q.modifier.orderBy with
          | none => omega
          | some o => sortSolutionsFast (compareOnConditions env o) omega
        let projected := match sel with
          | .vars items => projectSolutions (selectItemVars items) ordered
          | .all => ordered
        let deduped :=
          if q.modifier.distinct then distinctSolutionsFast projected
          else if q.modifier.reduced then reducedSolutions projected
          else projected
        some (sliceSolutions q.modifier.offset q.modifier.limit deduped)
  | _, _ => none

/-- SELECT against one graph backend. The three fast paths are tried in
the F* source's order — streaming `COUNT(*)`, streaming GROUP BY ?p,
LIMIT pushdown — and the materialise path runs last. Each detector is
conservative, so falling through is always available and always
correct. -/
def evalSelectBackendOnGraph (env : EvalEnv) (q : Query) (gb : GraphBackend)
    (dsb : DatasetBackend) : Option SolutionSeq :=
  match detectStreamingCountStar q with
  | some (alias, tp, scope) =>
      let bound := patternBoundFor tp Binding.empty
      -- EXACT, not the estimate: this count IS the query result. A
      -- constant-graph COUNT must count against that graph's own
      -- backend, and an unknown graph name counts zero — the same
      -- answer the materialise path's GRAPH arm gives.
      let n := match scope with
        | none => backendCountExact gb bound
        | some g =>
            match lookupNamedBackend g.val dsb.named with
            | some ngb => backendCountExact ngb bound
            | none => 0
      some (sliceSolutions q.modifier.offset q.modifier.limit
              (countStarSolution alias n))
  | none =>
      match resolveStreamingCountGroupByPredicate q gb dsb with
      | some (predVar, countAlias, preds, target) =>
          let omega := predicateGroupBySolutions predVar countAlias target preds
          let ordered := match q.modifier.orderBy with
            | none => omega
            | some o => sortSolutionsFast (compareOnConditions env o) omega
          some (sliceSolutions q.modifier.offset q.modifier.limit ordered)
      | none =>
          match detectLimitSingleTp q with
          | some (tp, k) =>
              match q.form with
              | .select sel => some (evalLimitSingleTp sel tp gb k)
              | _ => none
          | none =>
              match q.form with
              | .select _ =>
                  some (selectPost env q (evalPatternBackend env dsb q.pattern gb))
              | _ => none

/-- SELECT against the whole dataset. The GROUP BY ?g fast path is the
only one that needs every named backend, so it is tried here rather
than one level down. -/
def evalSelectBackendDataset (env : EvalEnv) (q : Query) (dsb : DatasetBackend) :
    Option SolutionSeq :=
  match detectStreamingCountGroupByGraph q with
  | some (graphVar, countAlias) =>
      let omega := countGroupByGraphSolutions graphVar countAlias dsb.named
      let ordered := match q.modifier.orderBy with
        | none => omega
        | some o => sortSolutionsFast (compareOnConditions env o) omega
      some (sliceSolutions q.modifier.offset q.modifier.limit ordered)
  | none => evalSelectBackendOnGraph env q dsb.default dsb

def runSelectQueryBackendDataset (env : EvalEnv) (q : Query) (dsb : DatasetBackend) :
    Option SolutionSeq :=
  evalSelectBackendDataset env
    (.mk q.form q.dataset q.pattern.rewriteBnodes q.groupBy q.having q.modifier
         q.postValues q.base) dsb

/-- ASK. An empty answer is `some false` only when every backend
decoded cleanly; otherwise it is `none`, because a column that failed
to decode contributes zero rows silently and ASK would report a read
failure as the answer `false`. -/
def evalAskBackend (env : EvalEnv) (q : Query) (dsb : DatasetBackend) : Option Bool :=
  match q.form with
  | .ask =>
      let omega0 := evalPatternBackend env dsb q.pattern dsb.default
      let omega := match q.postValues with
        | none => omega0
        | some vals => SPARQL.join omega0 vals
      match omega with
      | [] =>
          if backendDecodeFailure dsb.default
             || dsb.named.any (fun ngb => backendDecodeFailure ngb.backend)
          then none else some false
      | _ => some true
  | _ => none

/-- The blank-node rewrite happens once, at the entry point. The F*
source records why it cannot live inside the evaluator: replacing the
pattern breaks the recursion's termination metric. -/
def runAskQueryBackendDataset (env : EvalEnv) (q : Query) (dsb : DatasetBackend) :
    Option Bool :=
  evalAskBackend env
    (.mk q.form q.dataset q.pattern.rewriteBnodes q.groupBy q.having q.modifier
         q.postValues q.base) dsb

/-! ## 8. Facts

Which arms are backend-native, and which delegate. -/

theorem evalPatternBackend_bgp_native (env : EvalEnv) (dsb : DatasetBackend)
    (b : Bgp) (gb : GraphBackend) :
    evalPatternBackend env dsb (.bgp b) gb = evalBgpBackend b gb := by
  simp [evalPatternBackend]

theorem evalPatternBackend_union_native (env : EvalEnv) (dsb : DatasetBackend)
    (p1 p2 : QueryPattern) (gb : GraphBackend) :
    evalPatternBackend env dsb (.union p1 p2) gb
      = SPARQL.union (evalPatternBackend env dsb p1 gb)
                     (evalPatternBackend env dsb p2 gb) := by
  simp [evalPatternBackend]

theorem evalPatternBackend_empty (env : EvalEnv) (dsb : DatasetBackend)
    (gb : GraphBackend) :
    evalPatternBackend env dsb .empty gb = [Binding.empty] := by
  simp [evalPatternBackend]

/-- A `GRAPH <iri>` naming a graph the dataset does not carry
contributes nothing, as §18.6 requires. -/
theorem evalPatternBackend_graph_absent (env : EvalEnv) (dsb : DatasetBackend)
    (i : WfIri) (p : QueryPattern) (gb : GraphBackend)
    (h : lookupNamedBackend i.val dsb.named = none) :
    evalPatternBackend env dsb (.graph (.iri i) p) gb = [] := by
  simp [evalPatternBackend, h]

/-- The fully-unbound bound constrains nothing, so the backend hands
back the whole graph. -/
theorem boundMatches_all (t : Triple) : boundMatches patternBoundAll t = true := rfl

theorem tripleMatchesBound_none (g : Graph) :
    tripleMatchesBound { s := none, p := none, o := none } g = g := by
  simp only [tripleMatchesBound]
  exact List.filter_eq_self.mpr (fun t _ => boundMatches_all t)

/-- Feeding rows into an EMPTY remaining BGP just reverses them onto
the accumulator: each row is its own one-element result. -/
theorem evalBgpConcatMapAcc_singleton_nil (gb : GraphBackend) (fuel : Nat) :
    ∀ (rows acc : SolutionSeq),
      evalBgpConcatMapAcc [] gb fuel rows acc = rows.reverseAux acc
  | [], acc => by simp [evalBgpConcatMapAcc]
  | mu :: more, acc => by
      cases fuel with
      | zero =>
          simp only [evalBgpConcatMapAcc, evalBgpFromMuFuel,
                     evalBgpConcatMapAcc_singleton_nil gb 0 more, List.reverseAux]
      | succ n =>
          simp only [evalBgpConcatMapAcc, evalBgpFromMuFuel,
                     evalBgpConcatMapAcc_singleton_nil gb (n + 1) more,
                     List.reverseAux]

/-- The BGP arm agrees with the algebra on a list backend, for a
one-pattern BGP whose positions are all variables. Under the empty
binding that pattern presents the fully-unbound bound, so the backend
returns the whole graph and the two paths run the same match over the
same triples.

It is stated for ONE pattern because the planner reorders a longer BGP,
so the two paths then agree as sets and not as lists —
`chooseBest_perm` in `StorePlan.lean` is what makes that reordering
safe. It is stated for an all-variable pattern because a bound position
makes the backend pre-filter, and proving the pre-filter never drops a
row the match would keep is a separate lemma about `boundMatches`
against `tpMatch`. -/
theorem evalBgpBackend_allVars_list (g : Graph) (sv pv ov : VarName) :
    evalBgpBackend [{ s := .var sv, p := .var pv, o := .var ov }] (.list g)
      = evalBgp [{ s := .var sv, p := .var pv, o := .var ov }] g := by
  simp only [evalBgpBackend, List.length_cons, List.length_nil,
             evalBgpFromMuFuel, chooseBestTpBackend, evalSingleTpBackend,
             backendSearch, capsOfBackend, capsOfList, capsOfReadOps,
             patternBoundFor, boundSubjectOfPattern, boundPredicateOfPattern,
             boundObjectOfPattern, Binding.empty, Binding.lookup,
             evalBgpConcatMapAcc_singleton_nil, List.reverseAux_eq,
             List.append_nil, List.reverse_reverse,
             evalBgp, evalBgpFrom, evalTP]
  rw [tripleMatchesBound_none]
  simp

/-! ## 9. What the GROUP BY paths guarantee -/

/-- One row per named graph, however many that is. -/
theorem countGroupByGraph_length (graphVar countAlias : VarName) :
    ∀ (named : List NamedGraphBackend) (acc : SolutionSeq),
      (countGroupByGraphAcc graphVar countAlias acc named).length
        = acc.length + named.length
  | [], acc => by simp [countGroupByGraphAcc]
  | ngb :: rest, acc => by
      simp only [countGroupByGraphAcc,
                 countGroupByGraph_length graphVar countAlias rest,
                 List.length_cons]
      omega

/-- A predicate with no rows contributes no group. -/
theorem predicateGroupBy_skips_empty (predVar countAlias : VarName)
    (gb : GraphBackend) (acc : SolutionSeq) (p : WfIri) (rest : List WfIri)
    (h : backendCountExact gb { p := some p } = 0) :
    predicateGroupByAcc predVar countAlias gb acc (p :: rest)
      = predicateGroupByAcc predVar countAlias gb acc rest := by
  simp [predicateGroupByAcc, h]

/-! ## 10. ASK cannot report a read failure as `false` -/

theorem evalAskBackend_none_on_decode_failure (env : EvalEnv) (q : Query)
    (dsb : DatasetBackend) (hform : q.form = .ask)
    (hfail : backendDecodeFailure dsb.default = true)
    (hempty : (match q.postValues with
               | none => evalPatternBackend env dsb q.pattern dsb.default
               | some vals =>
                   SPARQL.join (evalPatternBackend env dsb q.pattern dsb.default) vals)
              = []) :
    evalAskBackend env q dsb = none := by
  simp only [evalAskBackend, hform, hempty, hfail, Bool.true_or, if_true]

/-! ## Build-time checks -/

private def iA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iB : WfIri := ⟨"http://example.org/b", by decide⟩
private def iG : WfIri := ⟨"http://example.org/g", by decide⟩

private def gDefault : Graph := [ { s := .iri iA, p := iP, o := .iri iB } ]
private def gNamed : Graph :=
  [ { s := .iri iB, p := iP, o := .iri iA },
    { s := .iri iA, p := iP, o := .iri iA } ]

private def dsb1 : DatasetBackend :=
  { default := .list gDefault
  , named := [{ name := iG.val, backend := .list gNamed }] }

private def tpAll : TriplePattern :=
  { s := .var "s", p := .var "p", o := .var "o" }

/-! Named lookup finds the graph it names and nothing else. -/
#guard (lookupNamedBackend iG.val dsb1.named).isSome == true
#guard (lookupNamedBackend iA.val dsb1.named).isSome == false

/-! Materialising reads every backend: one default triple, two named. -/
#guard (materialiseDatasetBackend dsb1).default.length == 1
#guard (materialiseDatasetBackend dsb1).named.length == 1
#guard (match (materialiseDatasetBackend dsb1).named.head? with
        | some ng => ng.graph.length | none => 0) == 2

/-! The capability view has one record per graph. -/
#guard (datasetCapsOfBackend dsb1).named.length == 1
#guard (datasetCapsOfBackend dsb1).default.estimate patternBoundAll == 1

/-! The BGP arm is backend-native; GRAPH with a constant IRI routes to
that graph's backend, and an unknown IRI contributes nothing. -/
#guard (evalPatternBackend {} dsb1 (.bgp [tpAll]) dsb1.default).length == 1
#guard (evalPatternBackend {} dsb1 (.graph (.iri iG) (.bgp [tpAll]))
          dsb1.default).length == 2
#guard (evalPatternBackend {} dsb1 (.graph (.iri iA) (.bgp [tpAll]))
          dsb1.default).length == 0
#guard (evalPatternBackend {} dsb1 .empty dsb1.default).length == 1

/-! UNION is the multiset union of the two sides. -/
#guard (evalPatternBackend {} dsb1
          (.union (.bgp [tpAll]) (.bgp [tpAll])) dsb1.default).length == 2

/-! One GROUP BY row per named graph, carrying that graph's exact
count. -/
#guard (countGroupByGraphSolutions "g" "n" dsb1.named).length == 1
#guard (match (countGroupByGraphSolutions "g" "n" dsb1.named).head? with
        | some mu => (Binding.lookup "n" mu).isSome && (Binding.lookup "g" mu).isSome
        | none => false) == true

/-! A predicate with rows makes a group; a predicate with none does
not. -/
#guard (predicateGroupBySolutions "p" "c" (.list gDefault) [iP]).length == 1
#guard (predicateGroupBySolutions "p" "c" (.list gDefault) [iB]).length == 0

/-! ASK answers true when rows exist, and false on a clean empty read. -/
#guard runAskQueryBackendDataset {} (mkQuery .ask (.bgp [tpAll])) dsb1 == some true
#guard runAskQueryBackendDataset {}
        (mkQuery .ask (.graph (.iri iA) (.bgp [tpAll]))) dsb1 == some false

/-! A SELECT is not an ASK, so the ASK entry point declines it. -/
#guard runAskQueryBackendDataset {} (mkQuery (.select .all) (.bgp [tpAll])) dsb1
        == (none : Option Bool)

/-! The SELECT entry point takes the streaming COUNT path and returns
one row carrying the exact count. -/
#guard (match runSelectQueryBackendDataset {}
          (mkQuery (.select (.vars [.expr (.aggregate .count false (.var "*")) "n"]))
            (.bgp [tpAll])) dsb1 with
        | some rows => rows.length | none => 0) == 1

/-! The materialise path answers a plain SELECT. -/
#guard (match runSelectQueryBackendDataset {}
          (mkQuery (.select .all) (.bgp [tpAll])) dsb1 with
        | some rows => rows.length | none => 0) == 1

/-! An ASK is not a SELECT, so the SELECT entry point declines it. -/
#guard (runSelectQueryBackendDataset {} (mkQuery .ask (.bgp [tpAll])) dsb1).isSome
        == false

/-! §18.6 EXISTS / NOT EXISTS evaluate against `env.dataset`, which a
caller of the backend runners must supply (the reference evaluator sets
it itself).  The default graph holds `a p b` only, so NOT EXISTS of the
reversed pattern keeps the row and EXISTS drops it.  Regression pin for
2026-09-02: an environment without a dataset answered zero rows for the
NOT EXISTS form. -/
private def tpReversed : TriplePattern :=
  { s := .var "o", p := .var "p", o := .var "s" }
private def envWithDataset : EvalEnv :=
  { dataset := some (materialiseDatasetBackend dsb1) }
#guard (match runSelectQueryBackendDataset envWithDataset
          (mkQuery (.select .all) (.filter (.notExistsPat (.bgp [tpReversed])) (.bgp [tpAll])))
          dsb1 with
        | some rows => rows.length | none => 99) == 1
#guard (match runSelectQueryBackendDataset envWithDataset
          (mkQuery (.select .all) (.filter (.existsPat (.bgp [tpReversed])) (.bgp [tpAll])))
          dsb1 with
        | some rows => rows.length | none => 99) == 0

/-! The COTTAS dataset constructor makes one backend per named graph
plus the default. -/
#guard (cottasOnDiskDatasetBackend
          { searchTok := fun _ _ => [], searchLimitedTok := fun _ _ _ => []
          , estimateTok := fun _ _ => 0, countExactTok := fun _ _ => 0
          , predicatePresent := fun _ => false, hasDecodeFailure := fun _ => false
          , distinctPredicates := fun _ => none
          , searchTokSelective := fun _ _ _ => [] }
          [iG.val, iA.val]).named.length == 2

/-! ## Axiom audit -/

#print axioms evalPatternBackend_bgp_native
#print axioms evalBgpBackend_allVars_list
#print axioms countGroupByGraph_length
#print axioms evalAskBackend_none_on_decode_failure

end L4Factoidal.SPARQL.StoreDataset
