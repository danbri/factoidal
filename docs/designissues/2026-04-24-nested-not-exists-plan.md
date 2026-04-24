# Threading graph through `eval_expr_ebv` — scoping

Date: 2026-04-24
Status: scoping. Unblocks `negation/subset-02` (SPARQL 1.1 entailment
bucket) and any future test that nests `EXISTS` / `NOT EXISTS` inside
`||` / `&&` / any non-top-level boolean operator.

## What fails today

`subset-02.rq` from
`third_party/testing/w3c/sparql/sparql11/negation/` — expected 11
rows, we produce 30 (all off-diagonal pairs). Diagnosis in
`docs/designissues/2026-04-24-negation-subsets-regression.md`:

```sparql
FILTER ( ?s1 = ?s2 || NOT EXISTS { ?s2 :member ?x . } )
```

`GP_Filter` special-cases `E_NotExists` / `E_Exists` only when the
filter expression is ONE of those at the outermost node. When they
appear nested inside `||` or `&&`, we fall through to
`filter_solutions_fwd e omega`, which calls
`assume val eval_expr_ebv : expr -> solution_mapping -> bool` —
a function with **no graph parameter** — which cannot evaluate the
existential, so it defaults / errors and the whole `||` collapses
in a way that lets the MINUS body match everything.

Tests we're getting 30 rows for: `subset-02` expects 11. Adjacent
tests at scale on Factoidal may hit the same pattern — e.g.
`paper-sparqldl-Q3`, which also involves `owl:complementOf` used
inside a filter; but Q3 also needs DL negation (separate issue).

## The fix, in one sentence

Thread `graph : rdf_graph` + `ds : rdf_dataset` through `eval_expr`,
`eval_expr_ebv`, `eval_expr_fwd`, and any callees that today take only
`(expr, solution_mapping)`. When `E_Exists p` / `E_NotExists p` are
reached anywhere in the expression tree, evaluate `p` against the
graph the same way the top-level filter does.

## Why it's non-trivial

The `assume val` declarations at `SPARQL11.Algebra.fst:1814-1815`
exist because `eval_expr` is mutually recursive with `eval_pattern`
(see comment at line 1992) and F\*'s module layout at the time made
the mutual-recursion pattern awkward. Callers everywhere assume the
2-arg signature.

Grep `eval_expr_ebv\|eval_expr_fwd\|eval_expr` turns up roughly
40 call sites across `SPARQL11.Algebra.fst` — every FILTER, BIND,
HAVING, aggregate, expression-evaluation in VALUES, project-
expression, etc. All need to pick up a graph argument.

## Phased plan (subagent-ready)

### Phase 0 — scratch doc + call-site inventory (15 min)

Commit scratch doc early. List every `eval_expr*` call site with
file:line. Classify:

- **Direct callers** (FILTER/BIND/HAVING) that already have the
  graph in scope from `eval_pattern`: trivial to thread.
- **Indirect callers** (aggregate helpers, sort-condition
  evaluators, optional-bind): may need the graph plumbed through
  one additional helper.
- **Terminal callers** in modules outside `SPARQL11.Algebra.fst`
  (e.g. `SPARQL11.Parser.fst`'s SSE printer): probably none, since
  those are pretty-printers not evaluators.

### Phase 1 — change signatures, preserve assume-val

Rather than eliminate the `assume val` declarations (which would
require a non-trivial re-architecture), CHANGE THEIR SHAPES:

```fstar
assume val eval_expr_ebv
  : rdf_graph -> rdf_dataset -> expr -> solution_mapping -> bool
assume val eval_expr_fwd
  : rdf_graph -> rdf_dataset -> expr -> solution_mapping -> eval_result
```

And similarly for the real `eval_expr` at line 2173 —
make it take `g ds e mu` and internally, at every recursion into a
sub-expression, pass the same `g ds`. For `E_Exists p` / `E_NotExists
p`, call into the pattern evaluator with `(g, ds, p, [mu])`.

### Phase 2 — update all call sites

Walk the call sites from Phase 0. At each:

- `GP_Filter` inner pattern already has `g ds` locally — pass them.
- `GP_Bind` — same.
- `HAVING` in `eval_select_query` — has the dataset in scope.
- Aggregate-aware paths — need to pass `g ds` into
  `eval_aggregate`.
- BIND/HAVING in subqueries — recursive `eval_select_query` calls
  need to thread.

Accept `(g, ds)` as a pair-tuple for some call sites to minimise
signature noise; leave singleton `eval_expr_ebv` callers to pass them
separately.

### Phase 3 — remove the GP_Filter top-level special case

The current special case at `GP_Filter`'s handler (lines ~1820–1900)
dispatches E_Exists / E_NotExists with graph access. Once the general
evaluator has `g`, the special case can be deleted — every nested
level already handles them.

Not strictly necessary for correctness (special case remains correct;
it just becomes redundant), but good for readability + one fewer
place where semantics can diverge between top-level and nested
contexts.

### Phase 4 — verify test delta

- `negation/subset-02` → PASS (+1).
- No SPARQL regressions in suites that don't use nested existentials.
- Run `./w3c-tests.sh` from repo root.

### Phase 5 — future-proofing

Document the convention: **every new predicate/function over
`expr` takes `g : rdf_graph, ds : rdf_dataset` as its first two
arguments**. Update CLAUDE.md's anti-pattern list if needed (e.g., "#6
promoted-type blindness" is an adjacent concern).

## Constraints

- F\* only (rule #10). No OCaml patches for semantic change.
- Stack-safe fold_left + accumulator throughout (tail-rec audit).
- No `(*` / `*)` in F\* block comments (rule #12).
- Termination: all new helpers fuel-indexed where they can recurse.
  `eval_expr` on `expr` AST can use structural `decreases e` since
  expressions are a finite tree.
- No `--lax`, no `admit()`.

## Risks

- `assume val` signature changes break every caller. Subagent must
  edit in a single pass and re-verify F\*. If F\* complains about
  stale caches, `make verify` will rebuild.
- Subquery cases: a subquery creates its own dataset for its WHERE;
  threading needs to use the INNER dataset, not the outer, when
  evaluating the sub-query's filters. Care required at
  `eval_subselect_fwd`.
- `eval_expr_ebv` is used by `SPARQL.Protocol.fst` for ASK / filter-
  result logic in the protocol layer. Signature change propagates.

## Acceptance criteria

1. F\* `make verify` passes.
2. `./w3c-tests.sh` from repo root shows
   - `negation` 11/1 → 12/0.
   - No regression in any other suite.
3. Runner's `-v` on `subset-02` shows the filter now correctly
   filters out the appropriate rows.
4. One commit preferred; if signature-cascade is too broad, split
   by module (F\*-core vs. SPARQL.Protocol wrappers).

## Not in scope

- `paper-sparqldl-Q3` — it uses `complementOf` + FunctionalProperty
  consequence under OWL-DL. Different problem; Tableau stage (d).
- Full refactor of `eval_expr` into a non-assume-val definition. That
  would require refactoring the mutual recursion between `eval_expr`
  and `eval_pattern` — out of scope.

## Hand-off

A subagent implementing this needs:
- This doc.
- `docs/designissues/2026-04-24-negation-subsets-regression.md`
- Read-access to `SPARQL11.Algebra.fst:1814-2250` (the whole expr
  evaluator region).
- Explicit "don't touch other agents' lanes" — tell them which
  .fst files are off-limits this session.

Timebox: 90 min. If the cascade proves too wide, abort and commit a
progress doc + partial-fix diagnosis rather than half-landing.
