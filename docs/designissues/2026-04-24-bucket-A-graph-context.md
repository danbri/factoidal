# Bucket A: graph-context threading diagnosis

Date: 2026-04-24
Status: diagnosis complete; 1 targeted F* fix proposed and implemented (FROM),
3 remaining are non-trivial or runner-side and escalated to main thread.
Timebox: 90 min.

## The 4 failing tests

| Suite | Test | Expected | Got | Signature |
|---|---|---|---|---|
| aggregates | `COUNT: no GROUP BY inside of GRAPH` (`agg-empty-group-count-graph`) | 17 tpls | 0 | runner: rs:ResultSet turtle |
| bindings | `VALUES inside GRAPH binding same var as graph name` (`graph`) | 24 tpls | 0 | runner: rs:ResultSet turtle |
| construct | `constructwhere04` | 4 tpls | 0 | F*: FROM dropped |
| basic-update | `INSERT same bnode twice` (`insert-05a`, `insert-data-same-bnode`) | 1/1 | 1/1 (content wrong) | F*: per-mapping bnode rename over-freshens |

`UPDATE result mismatch: default=0/0 triples, named=1/1 graphs` — counts
ARE equal; the message is misleading and only fires because the `triple_to_key`
contents differ within those equal counts.

## Per-test root causes

### 1. `agg-empty-group-count-graph` — RUNNER BUG, not evaluator

The query is a SELECT returning `?g ?c`. The expected file
`agg-empty-group-count-graph.ttl` is a Turtle-encoded `rs:ResultSet`
(SPARQL Results in Turtle form, §10.3 of the result set spec).

`w3c_runner.ml:958` dispatches on `Filename.check_suffix rf ".ttl"` and
unconditionally treats the expected file as a CONSTRUCT triple graph
(`expected_triples = parse_turtle_fstar content`) and compares to
`actual_triples`. But for SELECT queries, `actual_triples = []`
(line 943-946: `if is_construct then ... else []`). So any SELECT test
with a `.ttl` result file ALWAYS fails with "Triples mismatch: expected N,
got 0".

Evidence: `actual_triples = if is_construct then … else []`. SELECT results
go into `actual_results`, which is never reached on the `.ttl` branch.

Two W3C SPARQL 1.1 tests hit this: `aggregates/agg-empty-group-count-graph`
and `bindings/graph`. Both have `mf:result <X.ttl>` naming an `rs:ResultSet`
turtle.

**Fix (runner-side, NOT F*):** on the `.ttl` result branch, peek at
whether the parsed turtle contains `rs:ResultSet` (i.e., has a subject typed
`<.../result-set#ResultSet>`). If yes, parse it as an rs:ResultSet into
`(vars, rows)` and compare against `actual_results` the same way `.srx`
does; else fall through to the existing CONSTRUCT triple comparison.
Alternative: look at `query.q_form` — if it's not `QF_Construct`, the `.ttl`
file cannot be CONSTRUCT output.

### 2. `bindings/graph` — same runner bug as #1

Same mechanism as #1. Query is SELECT, expected is rs:ResultSet turtle,
runner misroutes into CONSTRUCT comparison.

Note: once the runner is fixed, the actual evaluator should handle
`GRAPH ?g { VALUES (?g ?t) { ... } }` correctly — the `PT_Var` branch of
`GP_Graph` in `SPARQL11.Algebra.fst:1953-1966` iterates every named graph,
evaluates the VALUES inner pattern (which yields rows with possibly
unbound `?g` for the UNDEF column), then calls `sm_bind_if_compatible`
to bind `?g` against the current `ngs_name`. That logic looks correct.

### 3. `constructwhere04` — REAL F* BUG: `q_dataset` / FROM is not applied

`formal/fstar/SPARQL11.Algebra.fst:495` declares
`q_dataset : list dataset_clause` on the query record. Grepping the file,
`q_dataset` is **never read** by `eval_select_query`, `eval_construct_query`
or `eval_ask_query`. So `FROM <x>` and `FROM NAMED <x>` on a top-level
query are silently dropped.

For `constructwhere04`:
```sparql
CONSTRUCT
FROM <data.ttl>
WHERE { ?s ?p ?o }
```
The manifest loads `data.ttl` as a NAMED graph (`qt:graphData`), default
is empty. `FROM <data.ttl>` should promote the named graph to default for
WHERE evaluation. Because `q_dataset` is ignored, WHERE runs against the
empty default graph → 0 bindings → 0 CONSTRUCT triples.

**Fix (F*):** at the top of `eval_select_query`, `eval_construct_query`,
and `eval_ask_query`, when `q.q_dataset` is non-empty, build a dataset
view similar to `build_where_dataset` in U_Modify (USING clauses):

- `DC_Default i` → union the triples from `lookup name ds.ds_named` into
  the new default graph.
- `DC_Named i` → add `{i, lookup i ds.ds_named}` to the new named list.

Then evaluate WHERE against that view. The existing `build_where_dataset`
/ `dc_default_triples` / `dc_named_graphs` helpers (for USING) are
structurally identical — factor out and share.

**Implemented in this commit.**

### 4. `insert-05a` / `insert-data-same-bnode` — per-mapping bnode rename
is too broad

`apply_modify` in `SPARQL11.Algebra.fst:4697-4698` invokes
`insert_quads_per_mapping ds_after_delete redirected_per_mu prefix 0`.
Each per-mu quad list is then passed through
`rename_quad_bnodes prefix`, which via `rename_triple_bnodes` calls
`rename_bnode_id` on every bnode appearing in the substituted triple —
**including bnodes introduced by the solution mapping** (i.e., the value
of a WHERE-bound variable).

SPARQL Update §3.1.3 says template bnodes are "scoped to the template
and fresh per solution mapping", but WHERE-matched bnode values bound to
variables MUST preserve their identity across the insert (they denote the
same blank node as in the source).

Consequence for `insert-05a`:
- `INSERT { GRAPH :g2 { ?S ?P ?O } } WHERE { GRAPH :g1 { ?S ?P ?O } }`
- WHERE matches `?S = T_BNode "b"` (from `_:b :p :o` in g1).
- per-mu instantiation: `(:g2, _:b :p :o)`.
- rename with prefix `_modify_1_m0_` → `(:g2, _modify_1_m0_:b :p :o)`.
- Op2 repeats: different `dataset_triple_count` → different prefix →
  NEW distinct bnode label. `:g2` ends up with 2 triples, not 1.
- Op3 COUNT(*) over :g2 gives 2, not 1. Final `:g3 = {:s :p 2}`,
  expected `:s :p 1` → mismatch.

For `insert-data-same-bnode`:
- Step 1 (INSERT DATA) correctly produces the same fresh label in both
  :g1 and :g2 (shared op prefix via `insert_data_bnode_prefix`) → each
  gets `_insdata_0_b :p :o`.
- Step 2 (INSERT WHERE `:g2 ← :g1`): WHERE match binds
  `?S = T_BNode "_insdata_0_b"`, template has no bnodes. Under the current
  `rename_quad_bnodes`, the matched bnode is renamed with the modify
  prefix — producing `_modify_X_m0_:_insdata_0_b`. Not equal to the
  already-present `_insdata_0_b :p :o` in :g2 → insert succeeds →
  :g2 has 2 triples. Then step 3 counts 2.

**Fix shape (F*):** template bnodes should be freshened BEFORE solution
substitution, so that only template-originating bnodes pick up the fresh
label and variable-bound bnodes survive unchanged. Concretely:

1. Before iterating `mus`, walk the insert template once and collect
   all bnode labels it contains.
2. For each per-mu instantiation, rename only those labels via a
   per-mu prefix (template-specific set), leaving other bnode labels
   (the ones introduced by the mapping) intact.

Simplest local fix: rename the template's bnodes to fresh labels
BEFORE calling `per_mapping_quads`, once per mu. I.e., walk `it`
substituting each template bnode `_:b` with `_:<prefix>_b`, then call
`instantiate_ggp_quads`. This keeps variable-bound bnodes verbatim.

**NOT implemented in this commit** — cleaner fix requires introducing
a template-bnode-rename helper and wiring it through `per_mapping_quads`
per solution. Handing to main thread after it rebuilds.

## Summary

| Test | Root cause | Location | Fix in this commit? |
|---|---|---|---|
| agg-empty-group-count-graph | Runner treats `.ttl` expected unconditionally as CONSTRUCT triples; SELECT `actual_triples = []` | `w3c_runner.ml:958` | No — runner fix (main thread) |
| bindings/graph | same as above | `w3c_runner.ml:958` | No — runner fix |
| constructwhere04 | `q.q_dataset` (FROM / FROM NAMED) never applied by query evaluators | `SPARQL11.Algebra.fst:495,3196,3279,3384` | **Yes** — added dataset-view application |
| insert-05a, insert-data-same-bnode | `rename_quad_bnodes` blanket-renames bnodes in substituted quads, including solution-bound bnode values | `SPARQL11.Algebra.fst:4697` → `rename_triple_bnodes` | No — needs template-bnode-only renamer (main thread) |

Two of four are runner-side (same bug). Two are F* evaluator semantics.
One F* fix (FROM) is small and landed here; the other (bnode scoping)
requires a more careful redesign.
