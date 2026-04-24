# 2026-04-25 — simple4 / simple5 / simple7: localised DISTINCT at CE union site

## Problem

Three OWL-entailment W3C tests (`simple4`, `simple5`, `simple7`) over-produce
exactly one row each. Diagnosis is well understood:

- `OWL.QueryRewrite` rewrites `?x a [owl:unionOf (:B :C)]` to
  `{ ?x a :B } UNION { ?x a :C }` via `expand_ce_subject` (Phase 4 union
  branch) and `build_union_ggp` (flat / Phase 3 union branch).
- SPARQL `UNION` is bag-semantic. An entity that is both a `:B` and a `:C`
  appears twice in the result.
- OWL set-theoretic semantics demand a single `?x` per satisfying entity.

## Why the conditional top-level DISTINCT is the wrong knob

`rewrite_query` currently sets `q_modifier.sm_distinct = true` whenever
`ggp_has_ce_marker` fires. This is too coarse:

1. It changes the user's projected solution multiset for the entire query
   (e.g. forces DISTINCT over the SELECT projection even when the user
   intentionally wanted bag semantics).
2. An earlier unconditional version of this knob regressed 9 non-CE tests
   in OWL_QueryEval (which is the eval path for ALL queries, not just
   entailment-tagged ones).
3. The CE-marker detector is heuristic: any future query that mentions a
   CE-marker predicate explicitly (without intending a class-expression)
   would silently get DISTINCT bolted on.

## Fix: wrap the CE-emitted UNION in a DISTINCT sub-select

When a CE expansion produces `GP_Union a b` (i.e. genuine 2+ branches),
wrap it as a `GP_SubSelect` whose inner `query` has `Select_All` and
`sm_distinct = true`. This deduplicates the union solutions before they
join with the surrounding pattern, while leaving the outer query's
modifier untouched.

## Targeted sites in `OWL.QueryRewrite.fst`

1. `build_union_ggp` (line ~456) — used by the flat Phase 3 path
   (`rewrite_bgp_one_union`, line ~752). Output is the union of named-class
   branches for a top-level CE consumer.
2. `expand_ce_subject` `CE_Union` arm (line ~947) — Phase 4 nested-CE path.
   Output is a `fold_left` ladder of `GP_Union`.

In both sites: only wrap when the result is a genuine `GP_Union` (>= 2
branches). A 0-branch union is `GP_Empty`; a 1-branch union collapses to
`GP_BGP` and needs no DISTINCT.

## Helper

```fstar
let wrap_distinct_over_ggp (g : group_graph_pattern) : group_graph_pattern =
  GP_SubSelect ({
    q_base     = None;
    q_prefixes = [];
    q_form     = QF_Select Select_All;
    q_dataset  = [];
    q_pattern  = g;
    q_group_by = None;
    q_having   = None;
    q_modifier = {
      sm_order_by = None;
      sm_distinct = true;
      sm_reduced  = false;
      sm_offset   = None;
      sm_limit    = None
    };
    q_values   = None
  })
```

`Select_All` projects every free variable bound inside `g`, so the outer
context (e.g. the join with the residue BGP) still sees `?x` and any other
union-branch-bound variables.

## Removing the existing top-level distinct

Drop the `ce_seen` branch in `rewrite_query` (lines 1523, 1525-1527) and
let `rewrite_ggp` handle DISTINCT locally. `ggp_has_ce_marker` and its
helpers can stay (they're cheap and may be useful for future heuristics)
but are no longer called.

## Verification plan

1. F* verify `OWL.QueryRewrite.fst` (no `--lax`).
2. Pure `.fst` edit — do not run extract / compile in this session per
   prompt.
3. Expected: `simple4`, `simple5`, `simple7` flip from FAIL (1 over-row)
   to PASS, no regressions among the 9 previously-broken non-CE tests
   (those never had a CE marker, so the top-level distinct is gone for
   them anyway — and they never had a GP_Union from rewriting).
4. Score expectation: 1590 -> 1593 of 1600 = 99.6%.

## Risk: variable scoping inside GP_SubSelect

Sub-selects in SPARQL introduce a new variable scope; outer variables are
not visible inside, but inner `Select_All` projects everything that is
bound within. For our case the inner pattern is the union of branches
each of which binds `?x` (and possibly fresh `?_sv_*` / `?_av_*` vars from
existential / universal restriction expansions). Those projected vars
become visible in the surrounding join, exactly like the un-wrapped union
would have been.
