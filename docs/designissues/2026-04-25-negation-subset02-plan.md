# negation/subset-02 — nested NOT EXISTS inside `||` (Agent Phi)

Date: 2026-04-25
Status: in progress
Goal: fix W3C SPARQL test `negation/subset-02` (currently 30 rows, expected 11).

## Recap of root cause

Background: see `2026-04-24-nested-not-exists-plan.md` and
`2026-04-24-negation-subsets-regression.md`.

The query has `FILTER (?s1 = ?s2 || NOT EXISTS { ?s2 :member ?x })`.

In `SPARQL11.Algebra.fst:1923-1932`, `GP_Filter` special-cases `E_Exists` /
`E_NotExists` only at the OUTER node of the filter expression. Anything else
falls through to `filter_solutions_fwd` -> `eval_expr_ebv` (assume val with no
graph parameter). When `E_NotExists` is nested under `E_Or`, the outer
expression is `E_Or _ _`, the special case misses it, and the existential
case in `eval_expr` returns `ER_Error` (line 2551-2552) — `ebv ER_Error =
false`, so `?s1 = ?s2 || NOT EXISTS {...}` collapses to `?s1 = ?s2`. (Or per
prior diagnosis, default-true; either way wrong rows leak through.)

## Approach (pure F\*)

Rather than thread `(graph, dataset)` through every `eval_expr` call (~92
sites, would blow past 60 min budget), **pre-process the filter expression
inside `GP_Filter`** before delegating to `eval_expr_ebv`:

1. Add a small F\* helper `evaluate_existentials_in_expr : expr -> mu ->
   gs -> ds -> expr` that walks the AST and replaces every `E_Exists p` /
   `E_NotExists p` sub-expression with `E_BoolLit (eval_exists_fwd p mu g ds)`
   (or its negation), while leaving the rest of the tree intact.

2. In `GP_Filter`, instead of branching on the outermost shape, ALWAYS run
   the helper to substitute existentials with their boolean values, then
   pass the rewritten expression to `filter_solutions_fwd`. The substituted
   expression contains no remaining `E_Exists`/`E_NotExists` nodes, so the
   graph-free `eval_expr_ebv` is sound.

3. Apply the same substitution in `left_join` (line 1870) for OPTIONAL with
   FILTER, and where `filter_solutions` is used for lemmas. This is the same
   minimal-invasive pattern used to thread context elsewhere.

This is pure F\* (no patch logic), tail-safe (the AST walk is structural
on expressions). It preserves the assume-val signatures, avoiding the
40-call-site cascade.

## Files touched

- `formal/fstar/SPARQL11.Algebra.fst` — add `substitute_existentials` helper,
  rewire `GP_Filter` and `left_join`.

## Verification

- `make verify` (mod the verification cache).
- Logical: structural recursion on `expr`, terminates by `decreases e`.

## Test impact (predicted)

- `negation/subset-02` 30 -> 11 rows = PASS.
- No regressions: substitution leaves non-existential expressions untouched,
  and the existing top-level `GP_Filter` special case continues to work the
  same way (existentials at the root get replaced by `E_BoolLit b`, then
  `eval_expr_ebv (E_BoolLit b) _` returns `b`).
- Possibly +1 for `temporal-proximity-by-exclusion-nex-1` if it has the
  same shape.

## Constraints honored

- No `(*` / `*)` inside F\* block comments (rule #12).
- F\*-first, semantic logic in `.fst` (rule #1, feedback_fstar_first_always).
- No `assume val` shape changes; existing patch 62 wiring untouched.
- No edits to OWL.QueryRewrite.fst (Rho lane) or RDF.Graph.Executable.fst
  (closure lane).
