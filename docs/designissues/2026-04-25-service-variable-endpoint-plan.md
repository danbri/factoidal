# SERVICE ?var endpoints — Phase 3 plan (Agent Tet, 2026-04-25)

## Goal

Make the SPARQL parser accept `SERVICE ?endpoint { ... }` (variable endpoint),
where `?endpoint` is bound by an outer BGP / VALUES / SubSelect that has
already executed when the SERVICE pattern is reached. Target test:
`third_party/testing/w3c/sparql/sparql11/service/service05.rq`.

Today the parser rejects with `unsupported: variable SERVICE endpoint`
(`SPARQL11.Parser.fst` line ~1788, `parse_service_iri`).

## Context

- Phase 1 (Omicron, `77c2969`): `assume val service_endpoint_lookup` hook +
  OCaml-side hashtable populated from `qt:serviceData`.
- Phase 2 (Pi, `e25bfce`): `service_endpoint_register` / `service_endpoint_clear`
  glue in `w3c_runner.ml`. Fixed-IRI SERVICE works.
- Wave 9 rebuild in flight; **must not** run `build-ocaml.sh extract` /
  `compile`.

## AST decision

Two options were on the table:

(a) Widen `GP_Service`'s first arg from `wf_iri` to `pattern_term`.
    Touches every consumer (Parser, Algebra, Store, OWL.QueryRewrite,
    w3c_runner.ml's `hoist_group_filters`). Disruptive.

(b) Add a parallel variant: `GP_ServiceVar : var_name -> group_graph_pattern
    -> bool -> group_graph_pattern`.
    All existing consumers keep working with no changes; only the parser
    (emit) and the eval branches (handle) need new code. Adding pattern
    matches in the consumers is mechanical and safe.

**Choice: (b)**. Less surface area; existing fixed-IRI flow is untouched.

## Phase A — minimum viable (this commit)

1. `SPARQL11.Algebra.fst`:
   - Add constructor `GP_ServiceVar : var_name -> group_graph_pattern -> bool
     -> group_graph_pattern` to `group_graph_pattern`.
   - In `eval_pattern_store`, evaluate `GP_ServiceVar v p' silent` per
     solution mapping: pre-evaluate the *outer* context isn't available
     here (eval is bottom-up), so for Phase A return `[]` (or `[[]]` if
     SILENT). The existing left-to-right join order on service05 means
     `GP_ServiceVar` will appear inside a `GP_Join`, but the right side
     can't see the left's bindings without a substitution step.
   - In `substitute_pattern`, replace `GP_ServiceVar v p' s` with
     `GP_Service iri p' s` when `mu` binds `v` to `T_IRI iri` and `iri`
     is a wf_iri; otherwise leave unchanged. **This is the magic** — the
     `GP_Join` evaluator already calls `substitute_pattern mu rhs` per
     left-side solution to propagate bindings into nested patterns.

2. `SPARQL11.Parser.fst`:
   - In `Tok_SERVICE` branch, before calling `parse_service_iri`, peek for
     `Tok_VAR`. If yes, build `GP_ServiceVar v g silent` directly.
     Otherwise fall through to the existing fixed-IRI flow.
   - Add cases for `GP_ServiceVar` in: `ggp_labeled_bnodes`,
     `validate_bnode_scope_pattern`, `gp_has_service` (line 3301),
     `gp_has_bnode` (line 3328), `sse_ggp` (line 3955).

3. Other consumers (mechanical):
   - `SPARQL11.Store.fst`: `pattern_predicate_hint`, `eval_pattern_backend`
     — both return `None` / `[]` like `GP_Service`.
   - `OWL.QueryRewrite.fst`: `normalise_joins`, `rewrite_ggp`,
     `ggp_has_ce_marker` — pass through.
   - `SPARQL11.Algebra.fst`: `substitute_pattern` (do the rewrite),
     `ggp_has_var`.

4. `ocaml-output/w3c_runner.ml`: `hoist_group_filters` — pass through.
   This is the only OCaml file touched and it's mechanical (one new line).

## Phase B (if time / if simpler-than-expected)

Per-solution dispatch directly inside `eval_pattern_store`'s
`GP_ServiceVar` branch — would need access to the outer mu, which the
current eval API doesn't carry. Practically, **Phase A's substitution-
based approach already gives Phase B's behaviour** because `GP_Join`
already substitutes the left-hand bindings into the right-hand pattern
before evaluating. So Phase B may be unnecessary.

## Verify

```
fstar.exe --include . --cache_dir .cache \
  SPARQL11.Parser.fst SPARQL11.Algebra.fst
```

No `--lax`. Then leave Wave 9 to rebuild and observe `service05` flip
from a parse error to either PASS (if substitution lands well) or to a
"different" failure (if eval still returns `[]`).
