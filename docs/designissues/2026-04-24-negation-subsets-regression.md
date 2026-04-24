# Negation subset-02 regression — NOT EXISTS inside FILTER expressions

Date: 2026-04-24
Status: diagnosed, fix deferred

## Observed

`subset-02` (manifest `:subset-02`, file `subset-02.rq`) in the SPARQL 1.1
negation suite fails with `Results mismatch: expected 11 rows, got 30`.

We produce 30 rows where the expected set has 11 — a pattern consistent with
a `MINUS` block failing to subtract anything, leaving the unfiltered
cartesian product of `?s1 × ?s2`.

## Query (simplified)

```sparql
SELECT (?s1 AS ?subset) (?s2 AS ?superset)
WHERE {
  ?s2 rdf:type :Set . ?s1 rdf:type :Set .
  MINUS {
    ?s1 rdf:type :Set . ?s2 rdf:type :Set .
    ?s1 :member ?x .
    FILTER ( ?s1 = ?s2 || NOT EXISTS { ?s2 :member ?x . } )
  }
  MINUS {
    ?s1 rdf:type :Set . ?s2 rdf:type :Set .
    FILTER ( NOT EXISTS { ?s1 :member ?y . } )
    FILTER ( NOT EXISTS { ?s2 :member ?y . } )
  }
}
```

The FILTERs in the MINUS arms are the load-bearing expressions. Each
contains `NOT EXISTS` — and crucially, the first combines it with `=`
via `||`, so the overall filter expression is
`E_Or (E_Eq ?s1 ?s2) (E_NotExists { … })`.

## Root cause (hypothesis)

`SPARQL11.Algebra.fst` dispatches `GP_Filter e p'` with special cases for
`E_Exists` / `E_NotExists` **only at the top level** of the filter
expression `e`. Anything else falls through to `filter_solutions_fwd e`
which uses `eval_expr_ebv` — that expression evaluator has no graph
parameter, so it cannot evaluate `EXISTS { … }`.

For plain FILTERs where `NOT EXISTS` is the whole expression (e.g. the
second MINUS arm's two separate FILTERs), the top-level case fires and
works. For the first MINUS arm's `?s1 = ?s2 || NOT EXISTS { … }`, the
disjunction is the top-level node, so `NOT EXISTS` falls through and
collapses to whatever default `eval_expr_ebv` returns for an
unimplemented form — probably "true", which makes the whole `||` true,
which makes the MINUS body always match, which means MINUS subtracts
nothing, which leaves the cartesian product.

(The subagent that started this investigation got as far as this
hypothesis, citing "GP_Filter e p' only handles E_Exists / E_NotExists
at the top-level of e" in its final stream before stalling.)

## Where to fix

In `formal/fstar/SPARQL11.Algebra.fst`, the expression evaluator needs
graph-context threading for `E_Exists` / `E_NotExists` wherever they
appear in an expression tree. Concretely:

1. Change `eval_expr_ebv` (and its transitively-called helpers —
   `eval_expr`, `eval_binary_op`, etc.) to take a `graph : rdf_graph`
   parameter (or a pair with `ds : rdf_dataset` for named-graph support).
2. Route `E_Exists p` / `E_NotExists p` to the same GP evaluator used by
   `GP_Filter` at top level, substituting the current `mu` so the pattern
   is evaluated bound to the outer solution.
3. Keep the top-level short-circuit in `GP_Filter` — that's a fine fast
   path — but the general expression evaluator must also support nested
   existentials.

## Test impact

Fixing the nested-EXISTS dispatch:
- **+1** for subset-02 (this test).
- Possibly +1 for `:temporal-proximity-by-exclusion-nex-1` if it uses a
  similar pattern (worth verifying).
- No obvious wider effect — other negation tests in the suite use plain
  top-level `FILTER(NOT EXISTS {…})` and already pass.

## Why deferred

- Threading a graph parameter through `eval_expr`-and-friends is a
  moderate refactor (probably 20–40 call sites) with latent risk: any
  helper that accidentally closes over a stale graph would produce
  silently-wrong answers in nested queries.
- The regression is 1 test out of 1604. The tail-recursion work,
  CONSTRUCT dedup, RDF/XML strict dispatch, and bnode-scope validator
  landed in the same session are higher-value.
- Best done when the evaluator is already being touched for another
  reason (e.g. adding `SERVICE` or property-path expressions).

## Action items for the next pass

1. Grep `SPARQL11.Algebra.fst` for every `eval_expr` / `eval_expr_ebv` /
   `eval_binary_op` signature to scope the diff.
2. Write a short spec note in this file about the new signature before
   editing.
3. Add a narrow test harness (a standalone F\* test, or a
   minimal-repro `.rq` / `.srx` pair) so the fix doesn't quietly
   regress.
