/-
L4Factoidal.SPARQL.StoreFastPath — the query-shape detectors and fast
paths of `SPARQL11.Store`.

Two query shapes have a much cheaper evaluation than materialising rows
and post-processing them:

1. **Streaming `COUNT(*)`.** `SELECT (COUNT(*) AS ?n) WHERE { tp }`
   with no GROUP BY, no DISTINCT and no modifier that would change the
   count. Ask the backend for the count directly instead of building
   millions of rows and taking the length.
2. **LIMIT pushdown.** `SELECT ?vars WHERE { tp } LIMIT k` with no
   DISTINCT, ORDER BY, aggregate or offset. Ask the backend for `k`
   rows so the on-disk walker stops early.

## The detectors are conservative, and that is the whole safety argument

The F* source states it:

> Both fast paths are SEMANTICS-PRESERVING: when the detector matches,
> the returned solution sequence equals what the materialise path would
> produce. Detectors are conservative — anything they don't recognise
> falls through to the existing materialise path.

Falling through is always correct. Matching when the shape is subtly
different is not. So every rejection below is a load-bearing line, and
the theorems in section 4 pin the ones a later widening would be
tempted to drop:

* `COUNT(DISTINCT *)` is rejected. It needs the dedup pass, so the
  count is not the row count.
* DISTINCT, REDUCED, ORDER BY, GROUP BY, HAVING and VALUES each reject.
* `GRAPH ?g { tp }` with a VARIABLE graph is rejected, and the F* source
  explains why at length: an unbound `?g` ranges over EVERY named
  graph, so a non-grouped `COUNT(*)` over that shape must SUM the count
  across every named graph. That is one sum over N backends, a
  different evaluation shape, not a mechanical widening. Only
  `GRAPH <constant> { tp }` matches.

## One representation difference, stated

The F* `q_having` is an `option`, so its detectors test `Some?`. The
Lean `Query.having` is a `List Expr`, so the same test is "not empty".
Both mean "the query has a HAVING clause"; the rejection fires on
exactly the same queries.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.StorePlan
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL.StoreFastPath

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan

/-! ## 1. Shape extraction -/

/-- A bare one-triple BGP. -/
def extractSingleTpBgp : QueryPattern → Option TriplePattern
  | .bgp [tp] => some tp
  | _ => none

/-- A one-triple BGP, bare or wrapped in exactly one `GRAPH <iri>`
layer. A variable graph does NOT match — see the module header. -/
def extractSingleTpBgpScoped : QueryPattern → Option (TriplePattern × Option WfIri)
  | .bgp [tp] => some (tp, none)
  | .graph (.iri g) (.bgp [tp]) => some (tp, some g)
  | _ => none

/-- `SELECT (COUNT(*) AS ?v)` and nothing else in the clause.
`COUNT(DISTINCT *)` is rejected: the dedup pass means the count is not
the row count. -/
def detectCountStarSelect : SelectClause → Option VarName
  | .vars [.expr e v] =>
      match e with
      | .aggregate .count distinct subE =>
          if distinct then none
          else
            match subE with
            | .var "*" => some v
            | .boolLit true => some v
            | _ => none
      | _ => none
  | _ => none

/-! ## 2. The two whole-query detectors -/

/-- The streaming `COUNT(*)` shape. Returns the alias, the triple
pattern, and the constant graph IRI when the pattern is
`GRAPH <g> { tp }`. -/
def detectStreamingCountStar (q : Query) :
    Option (VarName × TriplePattern × Option WfIri) :=
  match q.form with
  | .select sel =>
      match detectCountStarSelect sel with
      | none => none
      | some v =>
          if q.groupBy.isSome then none
          else if !q.having.isEmpty then none
          else if q.postValues.isSome then none
          else if q.modifier.distinct then none
          else if q.modifier.reduced then none
          else if q.modifier.orderBy.isSome then none
          else
            match extractSingleTpBgpScoped q.pattern with
            | none => none
            | some (tp, scope) => some (v, tp, scope)
  | _ => none

/-- The LIMIT-pushdown shape. -/
def detectLimitSingleTp (q : Query) : Option (TriplePattern × Nat) :=
  match q.form with
  | .select sel =>
      if selectHasAggregates sel then none
      else if q.groupBy.isSome then none
      else if !q.having.isEmpty then none
      else if q.postValues.isSome then none
      else if q.modifier.distinct then none
      else if q.modifier.reduced then none
      else if q.modifier.orderBy.isSome then none
      else if q.modifier.offset.isSome then none
      else
        match q.modifier.limit with
        | none => none
        | some k =>
            match extractSingleTpBgp q.pattern with
            | none => none
            | some tp => some (tp, k)
  | _ => none

/-! ## 3. The fast paths -/

/-- The one-row answer for `COUNT(*) = n`. -/
def countStarSolution (alias : VarName) (n : Nat) : SolutionSeq :=
  [ Binding.bind alias
      (.literal ⟨{ lexicalForm := toString n, datatype := xsdInteger,
                   langTag := none, direction := none },
                 by simp [literalWf, xsdInteger, rdfLangString,
                          rdfDirLangString, Subtype.ext_iff]⟩)
      Binding.empty ]

/-- LIMIT pushdown. The backend stops at `limit` rows; the full pattern
match still runs on what comes back, and the result is truncated again
because the bound is a filter and the match may reject rows. -/
def evalLimitSingleTp (sel : SelectClause) (tp : TriplePattern)
    (gb : GraphBackend) (limit : Nat) : SolutionSeq :=
  let candidates :=
    backendSearchLimited gb (patternBoundFor tp Binding.empty) limit
  let omega := candidates.filterMap (fun t => tpMatch tp t Binding.empty)
  let omega' := capsTakeN limit omega
  match sel with
  | .vars items => projectSolutions (selectItemVars items) omega'
  | .all => omega'

/-! ## 4. What the detectors refuse

Each of these is a query the fast path must NOT claim. A widening that
drops one of these lines makes a wrong answer fast. -/

/-- `COUNT(DISTINCT *)` is not the row count. -/
theorem detectCountStarSelect_rejects_distinct (v : VarName) (e : Expr) :
    detectCountStarSelect (.vars [.expr (.aggregate .count true e) v]) = none := by
  simp [detectCountStarSelect]

/-- `SELECT *` carries no alias to bind the count to. -/
theorem detectCountStarSelect_rejects_all :
    detectCountStarSelect .all = none := rfl

/-- More than one select item is not the shape. -/
theorem detectCountStarSelect_rejects_two (e : Expr) (v w : VarName) :
    detectCountStarSelect (.vars [.expr e v, .var w]) = none := rfl

/-- A VARIABLE graph is refused. An unbound `?g` ranges over every
named graph, so a non-grouped `COUNT(*)` over that shape is a SUM over
N backends, not one exact count. -/
theorem extractSingleTpBgpScoped_rejects_graph_var (v : VarName)
    (tp : TriplePattern) :
    extractSingleTpBgpScoped (.graph (.var v) (.bgp [tp])) = none := rfl

/-- A two-triple BGP is refused by both extractors. -/
theorem extractSingleTpBgp_rejects_two (tp1 tp2 : TriplePattern) :
    extractSingleTpBgp (.bgp [tp1, tp2]) = none := rfl

theorem extractSingleTpBgpScoped_rejects_two (tp1 tp2 : TriplePattern) :
    extractSingleTpBgpScoped (.bgp [tp1, tp2]) = none := rfl

/-- DISTINCT refuses the streaming count.

Checked NOT to be trivial (hazard #29). The last case closes by `rfl`
because `h` is already in context and the branch has reduced; with the
hypothesis REMOVED from the statement the same script fails there, on
the un-reduced `if q.modifier.distinct …` chain. The `#guard` below
that the clean query returns `some "n"` is the other half of the
check — the detector is not constantly `none`. -/
theorem detectStreamingCountStar_rejects_distinct (q : Query)
    (h : q.modifier.distinct = true) : detectStreamingCountStar q = none := by
  simp only [detectStreamingCountStar]
  split
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · rfl
  · rfl

/-- An ASK or CONSTRUCT query is not a SELECT, so neither detector
claims it. -/
theorem detectStreamingCountStar_rejects_ask (q : Query) (h : q.form = .ask) :
    detectStreamingCountStar q = none := by
  simp only [detectStreamingCountStar, h]

theorem detectLimitSingleTp_rejects_ask (q : Query) (h : q.form = .ask) :
    detectLimitSingleTp q = none := by
  simp only [detectLimitSingleTp, h]

/-- The LIMIT path never returns more rows than the limit. This is the
property a caller relies on, and it holds however the backend behaves,
because the result is truncated after the pattern match as well as
before it. -/
theorem evalLimitSingleTp_bounded (sel : SelectClause) (tp : TriplePattern)
    (gb : GraphBackend) (limit : Nat) :
    (evalLimitSingleTp sel tp gb limit).length <= limit := by
  simp only [evalLimitSingleTp]
  cases sel with
  | vars items =>
      simp only [projectSolutions, List.length_map, capsTakeN,
                 List.length_take]
      exact Nat.min_le_left _ _
  | all =>
      simp only [capsTakeN, List.length_take]
      exact Nat.min_le_left _ _

/-! ## Build-time checks -/

private def iriP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iriG : WfIri := ⟨"http://example.org/g", by decide⟩

private def tp1 : TriplePattern := { s := .var "s", p := .iri iriP, o := .var "o" }

private def countStarSel : SelectClause :=
  .vars [.expr (.aggregate .count false (.var "*")) "n"]

private def countTrueSel : SelectClause :=
  .vars [.expr (.aggregate .count false (.boolLit true)) "n"]

/-! Both spellings of `COUNT(*)` are recognised; the DISTINCT form is
not, and neither is `SUM`. -/
#guard detectCountStarSelect countStarSel == some "n"
#guard detectCountStarSelect countTrueSel == some "n"
#guard detectCountStarSelect (.vars [.expr (.aggregate .count true (.var "*")) "n"])
        == (none : Option VarName)
#guard detectCountStarSelect (.vars [.expr (.aggregate .sum false (.var "*")) "n"])
        == (none : Option VarName)

/-! A bare one-triple BGP matches with no scope; one GRAPH layer with a
CONSTANT IRI matches with a scope; a variable graph does not match. -/
#guard (match extractSingleTpBgpScoped (.bgp [tp1]) with
        | some (_, none) => true | _ => false) == true
#guard (match extractSingleTpBgpScoped (.graph (.iri iriG) (.bgp [tp1])) with
        | some (_, some g) => g == iriG | _ => false) == true
#guard (match extractSingleTpBgpScoped (.graph (.var "g") (.bgp [tp1])) with
        | none => true | _ => false) == true

/-! The whole-query detector matches the clean shape and refuses each
modifier in turn. -/
private def countQuery : Query := mkQuery (.select countStarSel) (.bgp [tp1])

#guard (match detectStreamingCountStar countQuery with
        | some (v, _, none) => v == "n" | _ => false) == true
#guard (match detectStreamingCountStar
          (mkQuery (.select countStarSel) (.bgp [tp1])
            (modifier := { distinct := true })) with
        | none => true | _ => false) == true
#guard (match detectStreamingCountStar
          (mkQuery (.select countStarSel) (.bgp [tp1])
            (having := [.boolLit true])) with
        | none => true | _ => false) == true
#guard (match detectStreamingCountStar (mkQuery .ask (.bgp [tp1])) with
        | none => true | _ => false) == true

/-! The LIMIT detector needs a limit and refuses an offset. -/
#guard (match detectLimitSingleTp
          (mkQuery (.select .all) (.bgp [tp1]) (modifier := { limit := some 5 })) with
        | some (_, k) => k == 5 | _ => false) == true
#guard (match detectLimitSingleTp (mkQuery (.select .all) (.bgp [tp1])) with
        | none => true | _ => false) == true
#guard (match detectLimitSingleTp
          (mkQuery (.select .all) (.bgp [tp1])
            (modifier := { limit := some 5, offset := some 2 })) with
        | none => true | _ => false) == true

/-! The count row binds the alias to an `xsd:integer` literal. -/
#guard (countStarSolution "n" 42).length == 1
#guard (match (countStarSolution "n" 42).head? with
        | some mu => (Binding.lookup "n" mu).isSome
        | none => false) == true

/-! ## Axiom audit -/

#print axioms detectCountStarSelect_rejects_distinct
#print axioms extractSingleTpBgpScoped_rejects_graph_var
#print axioms detectStreamingCountStar_rejects_distinct
#print axioms evalLimitSingleTp_bounded

end L4Factoidal.SPARQL.StoreFastPath
