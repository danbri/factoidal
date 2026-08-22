/-
L4Factoidal.SPARQL.Exists — §18.6 EXISTS as a pattern-layer hook.

`Expr.lean` evaluates `EXISTS { P }` / `NOT EXISTS { P }` through
`EvalEnv.existsHook : GraphPattern → Binding → Bool` (the expression
layer cannot import the pattern layer, so the pattern evaluation is
supplied from above). This module supplies it.

SPARQL 1.1 §18.6: "exists(pattern, μ) … evaluates
substitute(pattern, μ) … and returns true if the result is not the
empty multiset". Port of the F* `eval_exists` (`substitute_pattern`
then `eval_pattern_store`, `SPARQL11.Algebra.fst`).

`substitute` works on the LOWERED algebra pattern, because that is
what the parser stores inside `Expr.existsPat` (see the AST-gap note
in `Parser.lean`). The lowered pattern carries its FILTER / BIND /
OPTIONAL expressions as closures over the row, so substituting into
an expression is done by evaluating the closure on `μ ⊕ row` — the
row extended with μ's bindings, μ taking priority, which is exactly
what replacing each variable `v ∈ dom(μ)` by `μ(v)` in the expression
text amounts to. (The F* `substitute_pattern` leaves embedded
expressions verbatim; the spec text substitutes into the whole
pattern, and this port follows the spec.)

Two limits, stated plainly:
  * the hook is built for ONE active graph. The F* evaluator threads
    the active graph through, so an EXISTS inside `GRAPH ?g { … }`
    sees the named graph; here it sees the graph the hook was built
    with. `existsHookFor` takes the top-level active graph.
  * an EXISTS nested inside an EXISTS body was lowered by the parser
    with `emptyEnv`, so its own hook is absent and it evaluates to an
    error (→ false). Tracked with the parser's AST-gap note.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- `substitute(pattern, μ)` over the lowered algebra (port of the F*
`substitute_pattern`, arm for arm; closures are re-based on `μ`). -/
def GraphPattern.substitute (mu : Binding) : GraphPattern → GraphPattern
  | .bgp b              => .bgp (substBgp mu b)
  | .join l r           => .join (l.substitute mu) (r.substitute mu)
  | .leftJoin l r cond  => .leftJoin (l.substitute mu) (r.substitute mu)
                             (fun row => cond (mu.merge row))
  | .filter cond p      => .filter (fun row => cond (mu.merge row)) (p.substitute mu)
  | .union l r          => .union (l.substitute mu) (r.substitute mu)
  | .minus l r          => .minus (l.substitute mu) (r.substitute mu)
  | .graph name p       => .graph (substPatternTerm mu name) (p.substitute mu)
  | .lateral l r        => .lateral (l.substitute mu) (fun row => (r row).substitute mu)
  | .bind binder v p    => .bind (fun row => binder (mu.merge row)) v (p.substitute mu)
  | .values vars rows   => .values vars rows
  -- F*: `GP_Service iri p1 silent -> GP_Service iri p1 silent` (verbatim).
  | .service remote silent p => .service remote silent p
  -- F*: a bound endpoint variable lowers to a fixed endpoint.
  | .serviceVar v resolve silent p =>
      match mu.lookup v with
      | some (.iri i) => .service (resolve i.val) silent (p.substitute mu)
      | _             => .serviceVar v resolve silent (p.substitute mu)
  -- F*: `GP_SubSelect q -> GP_SubSelect q` (verbatim).
  | .modified post p    => .modified post p
  | .propertyPath s path o =>
      .propertyPath (substPatternSubject mu s) path (substPatternTerm mu o)
  | .empty              => .empty

/-- `exists(pattern, μ)` against dataset `ds` with active graph
`active` — §18.6. -/
def evalExists (ds : Dataset) (active : Graph) (p : GraphPattern) (mu : Binding) : Bool :=
  !((p.substitute mu).evalIn ds active).isEmpty

/-- The `EvalEnv.existsHook` for a query over `ds` whose active graph
is `active` (the default graph, or the `FROM`-built one — see
`applyDataset`). -/
def existsHookFor (ds : Dataset) (active : Graph) : GraphPattern → Binding → Bool :=
  evalExists ds active

/-- An environment whose EXISTS hook evaluates against `ds`/`active`,
with the other fields taken from `base`. -/
def EvalEnv.withExists (base : EvalEnv) (ds : Dataset) (active : Graph) : EvalEnv :=
  { base with existsHook := some (existsHookFor ds active) }

end L4Factoidal.SPARQL
