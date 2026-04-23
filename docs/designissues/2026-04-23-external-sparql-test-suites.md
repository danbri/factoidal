# External SPARQL Test & Benchmark Harness Survey (2026-04-23)

Licence-clean (non-GPL/AGPL) sources worth mining for tests and perf rigs,
alongside or instead of the W3C conformance suite we already run.

## Top picks (import directly as `tests/external/<project>/`)

### 1. Oxigraph — MIT OR Apache-2.0

Unique value: **planner-regression tests** (nothing similar exists elsewhere
in manifest form) and a **parser error-recovery corpus**.

Paths to mirror:

- `testsuite/oxigraph-tests/sparql/` — DESCRIBE/CBD, lateral joins, regex with
  variable, unicode escape with multibyte chars
- `testsuite/oxigraph-tests/sparql-optimization/` — `_input.rq` / `_output.rq`
  pairs: BGP reorder, bind constant fold, filter pushdown, empty-union
  elimination, `sameTerm` collapsing. Will directly test the #97 indexed
  store's BGP reorderer when we add one.
- `testsuite/oxigraph-tests/sparql-results/` — SRX/SRJ/TSV edge cases
- `testsuite/oxigraph-tests/parser-error/` + `parser-recovery/` — error
  classification + recovery
- `testsuite/oxigraph-tests/geosparql/`, `jsonld/` — format coverage

Perf: `bench/bsbm_*.sh` (one per engine: oxigraph/jena/rdf4j/blazegraph/graphdb/
virtuoso) + `explanation_to_flamegraph.py`. Worth reproducing a
`bench/bsbm_factoidal.sh` against BSBM.

### 2. Eclipse RDF4J — EDL v1.0 (= BSD-3)

Unique value: **SPARQL 1.2 draft fixtures** (triple terms, quoted triples,
directional language tags) and **SERVICE federation fixtures** with per-
endpoint data.

Paths:

- `testsuites/sparql/src/main/resources/testcases-sparql-1.1/`
- `testsuites/sparql/src/main/resources/testcases-sparql-1.2/` ← rare
- `testsuites/sparql/src/main/resources/testcases-service/` — multi-endpoint
  fixtures with pre-built `data0Nendpoint{1,2}.ttl`
- `testsuites/sparql/src/main/resources/testdata-update/` — UPDATE + Graph
  Store Protocol stress
- `testsuites/model/` — value-factory / literal-equivalence / blank-node
  isomorphism

Perf: `testsuites/benchmark/` (JMH) + `runBenchmarks.sh`.

### 3. Apache Jena — Apache 2.0

Unique value: **RDFS rule-engine tests** and **SPARQL-CDT (Composite
Datatypes, lists/maps)** fixtures.

Paths:

- `jena-arq/testing/ARQ/` — ARQ extensions (property functions, let/assign)
- `jena-arq/testing/RDFS/` — RDFS rule-engine regression
- `jena-arq/testing/SPARQL-CDTs/` — list/map CDT proposal
- `jena-arq/testing/Update/`, `jena-arq/testing/RIOT/`
- `jena-arq/testing/bsbm/` — pre-baked BSBM query set

Perf: `jena-benchmarks/jena-benchmarks-jmh/` — canonical JMH structure, and
`jena-benchmarks-shadedJena560/` runs against a frozen older Jena for
**continuous regression against a previous release** — the single best trick
in this survey. Worth reproducing.

### 4. Raptor — tri-licensed, take under Apache 2.0

Dave Beckett's 15-year parser corpus. Cherry-pick edge cases:

- `tests/turtle/` — numeric edge cases, comment/whitespace stress
- `tests/rdfxml/` — entity bombs, encoding fallbacks, BOM handling
- `tests/ntriples/` — line-ending mixing

Don't import the Rasqal driver — it's shell/Python and doesn't map cleanly to
our w3c_runner. Just copy the `.rdf`/`.ttl`/`.nt` files and re-run through
our harness.

### 5. rdflib — BSD-3

Mine for **edge-case fixtures only**, not structure (pytest doesn't map to
OCaml):

- `test/test_literal/` — datatype coercion + canonical-form corpus
- `test/test_sparql/test_datetime_processing.py` — xsd:dateTime offsets (known
  Factoidal weakness)
- `test/test_sparql/test_agg_undef.py`, `test_agg_distinct.py`
- `test/test_issues/` — 400+ GH-issue-keyed regression tests

Expect ~100 hours to convert to W3C-style manifests. Lower priority than the
top 4.

## Perf harness structures to copy

- **Jena's `jena-benchmarks-shadedJena560/`** pattern — benchmark the current
  build *against* a frozen older build of ourselves as a dep. Our analogue:
  keep `bin/darwin-arm64/factoidal.v<N>` around and have a
  `bench/baseline-regression.sh` that runs the same query through both.
- **Oxigraph's `bench/`** — cross-engine BSBM shell scripts + flamegraph
  pipeline (`explanation_to_flamegraph.py`). We can emit the same explanation
  format from our F* planner.

## Benchmarks status

| Suite | Licence | Verdict |
|---|---|---|
| BSBM (afs fork) | Apache 2.0 | **USE** — submodule under `tests/external/bsbm/` |
| BSBM-HOBBIT | AGPL 3.0 | skip |
| SP2Bench (dice-group mirror) | GPL 3 | skip |
| LUBM (SWAT Lehigh) | GPL | skip |
| WatDiv (dsg-uwaterloo) | no LICENSE | skip until clarified |
| FedBench | provenance broken | skip |
| LargeRDFBench | likely AGPL/GPL | skip |

## Absorption rules

Repo-root `THIRD_PARTY_NOTICES.md` (to be created) lists each origin with
licence + SHA of the import commit. Files from Oxigraph/RDF4J/Jena/Raptor/N3.js
get a header comment naming the origin, and their licence text is vendored
under `tests/external/<project>/LICENSE-<orig>.txt`.

**Never:** touch GPL/AGPL sources, even for single files. The moment any
GPL fragment is imported, the whole `tests/` tree becomes infected under
typical licence-compliance readings.

## Immediate actions (not in this doc — separate commits)

1. `tests/external/oxigraph-optimization/` — import the `sparql-optimization/`
   directory; wire into w3c_runner as a new suite.
2. `tests/external/rdf4j-sparql12/` — import `testcases-sparql-1.2/`; many
   will fail until we add 1.2 support but the corpus is where we'll
   measure progress.
3. `tests/external/jena-rdfs/` — import `testing/RDFS/`; will bump our
   rdf-mt / entailment coverage meaningfully.
4. `bench/bsbm/` — BSBM submodule + a shell runner comparing native
   factoidal vs Oxigraph vs Jena on the same query mix.

## Source links

Apache Jena, Eclipse RDF4J, Oxigraph, RDFLib, Raptor (dajobe), N3.js (rdfjs),
rdf-canonize (digitalbazaar), BSBM (afs/BSBM).

Survey generated by subagent on 2026-04-23.
