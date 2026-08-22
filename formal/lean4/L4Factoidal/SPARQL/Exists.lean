/-
L4Factoidal.SPARQL.Exists — §18.6 EXISTS: the design record and the
named `exists(pattern, μ)` function.

SPARQL 1.1 §18.6: "exists(pattern, μ) … evaluates
substitute(pattern, μ) … and returns true if the result is not the
empty multiset". The F* does this in `eval_exists` (`substitute_pattern`
then `eval_pattern_store` against the ACTIVE graph `gs.gs_graph` and
the dataset), reached from `filter_solutions_with_graph` /
`left_join_with_graph` through `substitute_existentials`, which
replaces every EXISTS sub-expression by its boolean before the
graph-free expression evaluator runs (`SPARQL11.Algebra.fst`).

THE DESIGN CHOICE (2026-08-22, second EXISTS stage). The first stage
stored an already-LOWERED `GraphPattern` inside `Expr.existsPat` and
evaluated it through an `EvalEnv.existsHook` built for one active
graph. Two W3C cases showed the shape was wrong: `Exists within graph
pattern` (the EXISTS must see the graph its enclosing `GRAPH` clause
selected) and `Nested positive exists` (the parser had to lower the
body under `emptyEnv`, so a nested EXISTS had no hook). Two repairs
were on the table:

  (a) give `Expr.existsPat` its proper operand, the CONCRETE
      `QueryPattern`, exactly as the F* `E_Exists :
      group_graph_pattern -> expr`; lower the body at EVALUATION time,
      under the real environment and the row; or
  (b) keep the lowered `GraphPattern` and thread the active graph and
      the environment through the hook.

**(a) was taken.** (b) cannot be made faithful: a body lowered at parse
time has closed over whatever environment the parser had, so a nested
EXISTS, a SERVICE endpoint map or NOW() inside the body are fixed
before the query is ever evaluated, and a hook threading the active
graph would still need a fuel-tied knot to reach the nested level. (a)
costs one mutual inductive: `Expr`, `QueryPattern`, `Query` and the
query-level pieces that carry expressions are declared together in
`Expr.lean` (the F* has the same knot in one `type … and …` group);
`Expr` derives nothing, as before — a `GraphPattern` with function
fields never derived anything either. What it buys: the recursion is
STRUCTURAL. The EXISTS body is a subterm of the condition, which is a
subterm of the pattern, so `QueryPattern.lowerWith` and
`substituteExistentials` (`Query.lean`) form one structural mutual
block — no fuel, no hook, no `partial`.

The one change to the algebra: `GraphPattern.filter` and
`GraphPattern.leftJoin` conditions are `Graph → Binding → Bool`, the
active graph being the extra argument. This is the F* signature
(`filter_solutions_with_graph … g ds`): the active graph is only known
where the algebra evaluates the condition, inside `GRAPH ?g { … }` it
differs per named graph, and an EXISTS in the condition is evaluated
against it. `bind` binders stay `Binding → Option Term` because the F*
`fx_bind_rows` does no existential substitution (so `BIND(EXISTS {…} AS
?v)` is an error there; noted, not changed).

Substitution. `lowerWith env μ body` IS `substitute(body, μ)` — the
fused lowering LATERAL already used. Expressions inside the body are
evaluated on `μ ⊕ row` (μ first), the §18.6 text's "replace every
occurrence of a variable in pattern" read literally; the F* leaves
embedded expressions verbatim, and the two agree on every W3C case.

The dataset EXISTS evaluates against is `EvalEnv.dataset`, installed
by `evalSelect` / `evalAsk` / `evalConstruct` from the query's own
dataset (after FROM / FROM NAMED) — the §18.6 `D`, passed the way
`EvalEnv.services` already is, so the semantics stays a total function
of explicit inputs.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- `exists(pattern, μ)` — §18.6: true when `substitute(pattern, μ)`,
evaluated against the active graph `active` and the dataset `ds`, has
at least one solution (the F* `eval_exists`). -/
def evalExists (env : EvalEnv) (ds : Dataset) (active : Graph) (mu : Binding)
    (p : QueryPattern) : Bool :=
  !((QueryPattern.lowerWith env mu p).evalIn ds active).isEmpty

/-- What the pattern layer does with `EXISTS { P }` is exactly
`exists(P, μ)` — stated so it is checked rather than assumed. -/
theorem substituteExistentials_existsPat (env : EvalEnv) (ds : Dataset)
    (active : Graph) (mu : Binding) (p : QueryPattern) :
    substituteExistentials { env with dataset := some ds } active mu (.existsPat p)
      = .boolLit (evalExists { env with dataset := some ds } ds active mu p) := rfl

/-- `NOT EXISTS { P }` is its negation. -/
theorem substituteExistentials_notExistsPat (env : EvalEnv) (ds : Dataset)
    (active : Graph) (mu : Binding) (p : QueryPattern) :
    substituteExistentials { env with dataset := some ds } active mu (.notExistsPat p)
      = .boolLit (!evalExists { env with dataset := some ds } ds active mu p) := by
  simp [substituteExistentials, evalExists]

/-- An environment whose EXISTS evaluates against `ds`, with the other
fields taken from `base` — the shape `evalSelect` installs. -/
def EvalEnv.withDataset (base : EvalEnv) (ds : Dataset) : EvalEnv :=
  { base with dataset := some ds }

end L4Factoidal.SPARQL
