# 2026-05-08 — Foundational F\* tier audit

Last refreshed: 2026-05-08.

Per [#235](https://github.com/danbri/factoidal/issues/235) Step 2: classify
every file in `formal/fstar/*.fst` (73 modules total) so the per-suite
path-trigger architecture can map "what changed" → "what suites must re-run."

Three classes:

- **F (Foundational)** — change fires every suite. Small list (target ≤ 10).
- **D (Domain-specific)** — change fires only the suites in its domain track.
- **C (Consumer)** — used only by binaries / runners; changes don't fire any
  test suite (the runners they feed re-run on push to their own paths).

Domain track keys (used in the path-trigger manifest):

- `RDF` — parsing + serialisation + dataset model
- `RDFC` — canonicalisation 1.0
- `OWL` — RL closure / DL Tableau / OWL test runner
- `RIF` — Core engine + parser
- `SHACL` — Core validation (skeleton)
- `SPARQL.QUERY` — Algebra + Query
- `SPARQL.UPDATE` — Update + Sandbox
- `SPARQL.PROTOCOL` — HTTP request/response framing + Service Description
- `COTTAS` — on-disk store backend (read path)
- `PERF` — non-functional (profiling, debug)

A module can be on multiple tracks (e.g. `Parser.NTriples` fires both the
RDF N-Triples suite and the W3C SPARQL entailment suite which uses N-Triples
in test premises).

---

## F — Foundational tier (change fires every suite)

These are the load-bearing concepts every suite touches. Any change here
should be reviewed with extreme care, and the re-test fans out to all suites.

| Module | Reason it's foundational |
|---|---|
| `RDF.Graph.Executable` | Defines `triple` / `wf_iri` / `subject` / `rdf_term` / `rdf_graph` / `bnode_id` AT THE TYPE LEVEL — every other module references these constructors. ALSO carries OWL-RL closure (~30 rules). The closure should split out (see "Stratification work" below). |
| `RDF.Format` | Defines `rdf_term_format` discriminator + parse/serialise dispatch table. Used by every parser + every serialiser + the runner's format-detection. |
| `Parser.IRI` | RFC 3987 IRI normalisation. Every parser, every serialiser, every entailment regime relies on this for `rdf_term_eq` correctness on IRIs. |
| `Parser.FastString` | UTF-8 decode + char classification. Foundational because IRI/literal escape rules depend on it. |
| `OWL.Vocabulary` | Shared OWL/RDF IRI constants. Currently used by Tableau; OWL.QueryRewrite migration pending. Foundational because the constants ARE the standard vocabulary; getting one wrong silently breaks reasoning. |

**5 modules — within the ≤10 budget.** Stratification work below would shrink
`RDF.Graph.Executable` further, lowering the foundational LoC.

## D — Domain-specific (change fires its domain only)

### Track `RDF` (parsing, serialisation, dataset model)

| Module | Notes |
|---|---|
| `Parser.Combinators` | Generic combinator library used by NT/Turtle/RDFXML/SRX/CSV/JSONResults/N-Quads/TriG. Domain `RDF` (covers all RDF-syntax suites). |
| `Parser.TurtleScanner` | Used by Turtle + TriG. |
| `Parser.NTriples` | RDF 1.1 N-Triples suite. |
| `Parser.Turtle` | RDF 1.1 Turtle suite. |
| `Parser.NQuads` | RDF 1.1 N-Quads suite. |
| `Parser.TriG` | RDF 1.1 TriG suite. |
| `Parser.XML` | Generic XML scaffold used by RDFXML + RIFXML. |
| `Parser.RDFXML` | RDF 1.1 RDF/XML suite. |
| `Parser.SRX` | SPARQL Results XML — used by SPARQL test runner (compares expected vs actual results). |
| `Parser.CSVResults` | SPARQL Results CSV/TSV — same role as SRX. |
| `Parser.JSONResults` | SPARQL Results JSON — same. |
| `RDF.NQuads.Serialize` | Canonical N-Quads emission. Foundational for the NQuads suite + RDFC-1.0 (RDFC's canonical form is N-Quads). Effectively dual-track `RDF` + `RDFC`. |
| `RDF.List.Helpers` | Tail-recursive list ops (assoc_tr / concatMap_tr / append_tr). Used by SPARQL.Algebra. Effectively dual-track `SPARQL.QUERY` + general list correctness. |
| `RDF.Pretty` | Pretty-printer for RDF terms. Used by the test runner's diagnostic output. |

### Track `RDFC` (RDF Dataset Canonicalization 1.0)

| Module | Notes |
|---|---|
| `RDF.Canonical` | Phase 1 HFDQ + Phase 2 HNDQ. Dual-track with `RDFC` only because nothing else uses canonicalisation (yet). |
| `RDF.Canonical.Manifest` | RDFC-1.0 W3C manifest parser (test-runner companion). |

### Track `OWL` (RL closure + DL Tableau)

| Module | Notes |
|---|---|
| `OWL.QueryRewrite` | CE-bnode rewrite → BGP expansion. Used by SPARQL entailment regime + OWL conformance runner. Effectively dual-track `OWL` + `SPARQL.QUERY`. |
| `OWL.QueryEval` | Wires `rewrite_query` into the SPARQL evaluator. Same dual-track. |
| `OWL.Tests.Manifest` | OWL 2 W3C test manifest parser (runner companion). |
| `Tableau` | Class-expression membership + materialisation + existential witness synthesis. Live for OWL-Direct semantics. |

### Track `RIF` (Core engine)

| Module | Notes |
|---|---|
| `RIF.Core.Syntax` | RIF Core AST. |
| `RIF.Core.Translation` | RIF-to-RDF semantics translation. |
| `RIF.Core.Eval` | Forward-chaining fixpoint engine. |
| `RIF.Core.Tests` | RIF runner-shim API. |
| `Parser.RIFXML` | RIF-XML concrete syntax parser. Effectively dual-track `RIF` + `RDF` (uses Parser.XML which is foundational-ish for the XML format family). |

### Track `SHACL`

| Module | Notes |
|---|---|
| `SHACL.Validation` | Phase 1 skeleton (#181). Currently no live runner. |

### Track `SPARQL.QUERY` (Algebra + Query language)

| Module | Notes |
|---|---|
| `SPARQL11.Algebra` | The core SPARQL 1.1 algebra + BGP eval + aggregates + filter + bind + property-path. The biggest non-foundational module (~6000 LoC). |
| `SPARQL11.Parser` | SPARQL 1.1 query syntax → AST. |
| `SPARQL11.Store` | Backend-agnostic store wrapper. Affects every SPARQL eval path. |
| `SPARQL.Plan.Pruning` | Yod6/Tet3 home (predicate-presence pruning). |
| `SPARQL.Plan.Estimate` | Mem5 home (cardinality estimation). |
| `SPARQL.Plan.Explain` | Pe5 home (explain-plan rendering). |
| `SPARQL.Plan.Loader` | Bet7 home (lazy populate fallback). |
| `SPARQL.Plan.AccessPath` | Lamed3 home (per-RG predicate offset jump). |
| `SPARQL.Eval.Limits` | Tav5 home (row-cap circuit breaker). |
| `SPARQL.Eval.TimeBudget` | Heth3 home (cooperative cancellation). |
| `SPARQL.Query.Analysis` | Static query analysis. |
| `SPARQL.Diagnostics` | Diagnostic helpers for the SPARQL evaluator. |
| `SPARQL.JSON.Escape` | Used by SPARQL JSON results + by the HTTP response framing. Cross-track `SPARQL.QUERY` + `SPARQL.PROTOCOL`. |
| `SPARQL.Explain` | Plan-tree explanation. |

### Track `SPARQL.UPDATE`

| Module | Notes |
|---|---|
| `SPARQL.Update.Analysis` | Update-statement static analysis. |
| `SPARQL.Update.Sandbox` | Sandboxed update evaluation. |

### Track `SPARQL.PROTOCOL`

| Module | Notes |
|---|---|
| `SPARQL.Protocol` | HTTP request/response framing (SPARQL 1.1 Protocol). |
| `SPARQL.HTTP` | Top-level HTTP server logic. |
| `SPARQL.HTTP.Admin` | Admin endpoints. |
| `SPARQL.HTTP.BackendInfo` | Backend introspection. |
| `SPARQL.HTTP.Client` | Outgoing HTTP client (for SERVICE federation). |
| `SPARQL.HTTP.QueriesIndex` | Query catalog. |
| `SPARQL.HTTP.Response` | Response rendering. |
| `SPARQL.HTTP.StaticFiles` | Static-file serving for the demo. |
| `SPARQL.GraphStore` | SPARQL 1.1 Graph Store HTTP Protocol. |
| `SPARQL.ServiceDescription` | SPARQL 1.1 Service Description. |

### Track `COTTAS` (on-disk store)

| Module | Notes |
|---|---|
| `Parser.Ballyhoo` | Ballyhoo serialised-graph parser. |
| `Parser.BallyhooBloom` | Bloom-filter index reader. |
| `Parser.BallyhooHDT` | HDT format reader. |
| `Parser.BallyhooHDTQ` | HDT-Q quad reader. |
| `Parser.BallyhooCOTTAS` | COTTAS columnar reader. |
| `Parquet.Footer` | Parquet metadata reader. |
| `RDF.CottasInMem` | In-memory COTTAS store. |
| `RDF.CottasStore` | Top-level COTTAS store dispatch. |
| `RDF.CottasStore.ColumnSeq` | Column sequence reader. |
| `RDF.CottasStore.CompoundPresenceBitmap` | Tet3-related compound-presence bitmap. |
| `RDF.CottasStore.OnDiskIndex` | On-disk index reader. |
| `RDF.CottasStore.PageCache` | Page cache layer. |
| `RDF.CottasStore.PageCache.Bounds` | Page cache bounds proofs. |
| `RDF.CottasStore.PresenceBitmap` | Predicate-presence bitmap reader. |
| `RDF.Store.Columnar.OffsetIndex` | Lamed3 home (per-RG predicate offset jump). |

These modules collectively define the on-disk read path. Changes here fire
the COTTAS-backed test suites (which today are mostly bench harnesses + the
cottas_ondisk_smoketest harness) plus any SPARQL/RDF suite that runs over
COTTAS-backed datasets in CI.

### Track `PERF`

| Module | Notes |
|---|---|
| `Util.Log` | Logging shim. Effectively foundational at the OCaml-glue layer but no F\*-side semantics depend on it. |

## C — Consumer (no test suite is gated on this)

None of the .fst modules are pure-consumer. The consumer layer lives in
`bin/<consumer>/*.ml` (post-#200 D Phase 8): factoidal_cli, factoidal_serve,
factoidal_explain, factoidal_http, factoidal_dump_nq, w3c_runner, owl_runner,
rdfc10_runner, cottas_ondisk_smoketest. Changes to these fire only the suite
the runner serves (e.g. changing `bin/w3c-runner/w3c_runner.ml` fires every
W3C suite; changing `bin/rdfc10-runner/rdfc10_runner.ml` fires only RDFC-1.0).

---

## Stratification work motivated by this audit

Three cleanups would tighten the trigger surface significantly:

### 1. Split `RDF.Graph.Executable` (~3500 LoC)

Currently bundles:

- Type definitions (`triple`, `wf_iri`, `subject`, `rdf_term`, `rdf_graph`,
  `bnode_id`, …).
- OWL-RL closure rules (~30 rules + helpers).
- IRI helpers (`is_iri`, `iri_in_xsd_ns`, …).
- General graph utilities (`add_triple_if_new`, `find_objects`,
  `find_subjects`, …).
- XSD axiom emission.

Proposed split:

| New module | Contents | Track |
|---|---|---|
| `RDF.Term` | `wf_iri` / `bnode_id` / `subject` / `rdf_term` / `wf_literal` types + decidable equality. | F |
| `RDF.Triple` | `triple` record + `add_triple_if_new`. | F |
| `RDF.Graph` | `rdf_graph` + `find_objects`, `find_subjects`, etc. | F |
| `OWL.Closure` | All `owl_rule_*` functions + `owl_rl_closure_step` + `owl_rl_closure_with_reflexivity`. | OWL |
| `RDFS.Closure` | `rdfs_closure_step` family. | OWL (or its own track if separately wired). |
| `XSD.Axioms` | `owl_rule_xsd_datatype_axioms` + `xsd_*` constants. | RDF |

After the split, foundational is `RDF.Term + RDF.Triple + RDF.Graph` (~800 LoC)
instead of `RDF.Graph.Executable` (~3500 LoC). A change to OWL closure fires
only the OWL track, not every suite.

### 2. Migrate `OWL.QueryRewrite._iri` constants to `OWL.Vocabulary`

Currently OWL.QueryRewrite has its own set of `*_iri` suffixed constants
duplicating OWL.Vocabulary. Migrating means OWL.QueryRewrite changes only
trigger when actual rewrite-logic changes, not when vocabulary references move.

### 3. Split `SPARQL11.Algebra` (~6000 LoC)

Less urgent — already a single-track module, but a split into
`SPARQL.Algebra.AST + SPARQL.Eval.BGP + SPARQL.Eval.Solution + SPARQL.Filter +
SPARQL.Aggregates + SPARQL.PropertyPath` would let test-suite triggers be
finer-grained (e.g. a property-path fix shouldn't fire BGP-aggregate tests).

## Next steps

1. Pilot manifest format with one suite (`RDFC-1.0`).
2. Land the path-trigger dispatch shell script.
3. Land the foundational stratification (split #1 above).
4. Roll out manifests for the rest one at a time.
5. Fold in OWL DL conformance + new corpora.

Tracked in [#235](https://github.com/danbri/factoidal/issues/235).
