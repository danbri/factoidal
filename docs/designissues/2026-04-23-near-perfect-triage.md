# Near-perfect SPARQL 1.1 suites — triage (2026-04-23)

Source data: `docs/test-results/latest.csv` (commit
`a4813dcea65ed368f1ed6c070e292e58d1c2d880`) and
`formal/fstar/ocaml-output/sparql_results.log`. This is a scoping/QA
pass — no fixes, no `.fst` edits. Complements the deeper design-level
survey in
[`2026-04-23-near-perfect-fails-rootcauses.md`](2026-04-23-near-perfect-fails-rootcauses.md).

Scope: SPARQL suites with 1–3 fails AND otherwise high pass counts.
Explicitly excluded: `entailment` (51/19 — owned by another agent);
`service` (0/7 — known SERVICE federation gap, not near-perfect);
`rdf-xml` (161/5 — counted as RDF, separate triage).

## Buckets (re-stated)

- A: numeric lexical canonicalisation (xsd:float/decimal/double E-notation)
- B: bnode identity / scoping (INSERT, subquery, CONSTRUCT)
- C: graph-context threading (GRAPH + subquery/VALUES, DatasetClause)
- D: plan / optimiser ordering
- E: promoted-type blindness (ER_Num vs ER_Term T_Literal)
- F: parser/AST mismatch (evaluator vs parser shape)
- G: regex / string edge case
- H: result-format comparison (TSV/CSV/JSON)
- I: other (describe inline)

## Per-suite triage

### aggregates (46 pass, 1 fail)

| test | bucket | conf. | one-liner | next action |
|---|---|---|---|---|
| `COUNT: no GROUP BY inside of GRAPH` (`agg-empty-group-count-graph`) | C | high | `GRAPH ?g { SELECT (COUNT(*) AS ?c) WHERE { ?s :p ?x } }` returns 0 triples, expected 17 | Inspect `eval_pattern_store` sub-query invocation under `GP_Graph`; does `?g` bind per-named-graph before the inner SELECT is evaluated? |

### basic-update (11 pass, 2 fail)

| test | bucket | conf. | one-liner | next action |
|---|---|---|---|---|
| `INSERT same bnode twice` (`insert-05a.ru`) | B+C | high | Two INSERT DATA into `:g1` and `:g2` should produce the same bnode; we produce 0 triples in default, 1 in named | Check how bnode labels are scoped in `update_insert_data` across multiple GRAPH clauses in a single operation |
| `INSERTing the same bnode with INSERT DATA into two different Graphs…` (`insert-data-same-bnode.ru`) | B+C | high | Same pattern as above — multi-GRAPH bnode identity | Same fix point; both share root cause |

### bindings (10 pass, 1 fail)

| test | bucket | conf. | one-liner | next action |
|---|---|---|---|---|
| `VALUES inside GRAPH binding the same variable as the graph name` (`graph.rq`) | C | high | `GRAPH ?g { VALUES (?g ?t) { (UNDEF "foo") (<empty.ttl> "bar") } }` returns 0, expected 24 | `GP_Graph` eval doesn't reconcile an inner VALUES binding for `?g` against the outer graph iterator |

### cast (4 pass, 2 fail)

| test | bucket | conf. | one-liner | next action |
|---|---|---|---|---|
| `xsd:float cast` | A | high | 31 rows produced but none MATCH — lexical form mismatch (we keep `"0E1"`, expected `"0.0"`; we write `"-1.02E4"`, expected `"-10.2E3"`) | `xsd_cast` in `SPARQL11.Algebra.fst` needs a `canonicalize_float_lexical` helper producing spec form per XSD 1.1 §3.3.17 |
| `xsd:decimal cast` | A | high | 31 produced; 2 UNMATCHED (`"0.0"` vs `"0"`, `"1.0"` vs `"1"` trailing-zero rule) | Same point — canonicalise decimal lexical: trailing zero only when fractional, no redundant digits |

### construct (6 pass, 1 fail)

| test | bucket | conf. | one-liner | next action |
|---|---|---|---|---|
| `constructwhere04 - CONSTRUCT WHERE` | C | high | `CONSTRUCT FROM <data.ttl> WHERE { ?s ?p ?o }` returns 0 triples, expected 4 — uses in-query DatasetClause (`FROM`) instead of `qt:graphData` | `eval_construct_query` / query-exec setup: apply `FROM` DatasetClause to assemble the active default graph before BGP match. Likely untested path alongside `graphData`. |

### syntax-update-1 (53 pass, 1 fail)

| test | bucket | conf. | one-liner | next action |
|---|---|---|---|---|
| `syntax-update-54.ru` | F | med | Reuse of bnode label across update operations must be rejected (`INSERT DATA { _:b1 :p :o } ; INSERT DATA { _:b1 :p :o }`); we parse OK | Add bnode-scope check in SPARQL Update parser — track labels per-operation and reject re-use across `;`-separated operations |

## Bucket-level summary

| bucket | tests | suites touched |
|---|---|---|
| A (numeric lexical canon) | 2 | cast |
| B (bnode identity) | 2 | basic-update (co-classified with C) |
| C (graph-context threading / DatasetClause) | 5 (4 C-only + 2 C∩B) | aggregates, bindings, construct, basic-update |
| F (parser/AST mismatch) | 1 | syntax-update-1 |
| others (D,E,G,H,I) | 0 | — |

Total near-perfect fails triaged: 7 tests across 6 suites.

## Top 3 "if I could only fix one bucket"

### 1. Bucket C — graph-context threading (est. gain: 5 tests)

Tests `agg-empty-group-count-graph`, `bindings/graph`,
`constructwhere04`, `insert-05a`, `insert-data-same-bnode` all fail
because context (named-graph iterator, DatasetClause, or cross-GRAPH
bnode scope) is not consistently threaded into inner evaluation.
Highest leverage, but also highest blast radius — any change to
`eval_pattern_store` / `GP_Graph` handling risks regressing the
currently-passing `GRAPH`, `subquery`, and `delete-insert` suites.
Matches the rootcauses doc's "Bucket 3 — GRAPH + aggregate / VALUES
cross-context" and its cross-cutting code smell #1.

### 2. Bucket A — numeric lexical canonicalisation (est. gain: 2 tests, plus preventative)

`xsd:float cast` and `xsd:decimal cast` require XSD-spec canonical
lexical output. A single `canonicalize_numeric_literal` at the point
a numeric literal is first minted (parser + cast) would close both
tests and preempt future rdf-mt / construct regressions where a
`"3.14"^^xsd:decimal` compares to `"3.14000"^^xsd:decimal`. Low
blast radius (local to `xsd_cast`, numeric parser). Matches
rootcauses doc's Bucket 2.

### 3. Bucket F — parser scoping of update-bnode reuse (est. gain: 1 test)

Smallest but cleanest win: `syntax-update-54.ru` needs a
"bnodes-per-operation" reject in SPARQL Update parser. Self-contained
in `SPARQL11.Parser.fst`. No evaluator changes. Good warm-up commit
before tackling bucket C.

## Notes / caveats

- The two basic-update bnode failures are co-classified **B + C**:
  the primary symptom is "cross-GRAPH bnode identity not preserved"
  (bucket-B bnode identity) but the fix site is in multi-GRAPH update
  machinery (bucket-C graph-context threading). Counted once per
  bucket in the summary but the underlying commit likely fixes both
  with one change.
- No test in this triage is bucket-D/E/G/H — those buckets are empty
  at this near-perfect slice. Bucket-E (promoted-type blindness) may
  still explain individual rdf-xml and entailment fails not covered
  here.
- Confidence is **high** for all entries where the FAIL line already
  shows the specific shape mismatch (cast UNMATCHED rows, triples
  mismatch with zero actual). `syntax-update-54` is **med** because
  the fix site could be parser-scope OR a deliberate
  "parse-liberal, reject at exec-time" choice; W3C manifest treats
  it as a negative syntax test so parser rejection is correct.

## Source

Auto-generated from `sparql_results.log` on 2026-04-23. No code
changed.
