# Factoidal — Project Goals, Progress & Vision

## Verified RDF Transform System

This repository contains a clean-room implementation of a **formally grounded RDF graph transformation system**, intended for high-trust environments.

The system targets **post-ChatGPT infrastructure** where automated agents, data pipelines, and services must provide **cryptographically verifiable assertions about data and transformations**.

Core goals:

- Treat **graphs as units of assertability**
- Provide **signed and attestable transformations**
- Enable **formally verified reasoning kernels**
- Support **strict compliance environments** (finance, healthcare, defense, regulated AI)
- Integrate with modern **supply-chain attestation ecosystems**

The main architecture and rationale are documented in `docs/designissues/`.

### Key Concepts

- **Graph Transform Certificates**
- **Named Graph Operation Structures**
- **Verifiable Credentials for graph provenance**
- **Formal semantics verified in F\***
- **Cryptographically signed assertions**
- **Build provenance and runtime attestation**

The system focuses initially on:

- RDF dataset transforms
- RDFS closure
- deterministic canonicalization
- signed result bundles

Future work includes SPARQL evaluation kernels and trust-propagating graph pipelines.

### Design Philosophy

This project assumes that in modern AI-mediated systems:

- trust must be **computable**
- assertions must be **machine-verifiable**
- tools must emit **evidence, not just results**

The architecture combines:

- formal verification
- cryptographic signatures
- supply-chain provenance
- runtime attestation

to produce **high-confidence data transformations**.

See the design document for details.

## Vision

A **formally verified RDF toolkit** where every layer — types, parsing, querying, serialization — traces back to F* specifications. The Rust/WASM implementation is the single source of truth; the web demo consumes it directly. No JS reimplementations, no external addon scripts, no divergence.

```
F* formal spec  ->  Rust implementation  ->  WASM + JS bindings  ->  Web demo & tests
     ^                    ^                        ^
  verified          W3C test suite           real library, not a copy
```

## Principles

- **No cobbling.** Everything lives in Rust/WASM/F*. No external JS reimplementations.
- **Verify, don't trust.** F* specs define correctness; Rust implements; W3C tests validate.
- **One implementation.** The web demo uses the real WASM binary. Same code everywhere.
- **Incremental formalization.** Start with executable specs, progressively tighten to proofs.

## Architecture

```
factoidal/
├── formal/fstar/
│   └── rdfcore11.fstar.txt    # F* formal specification (RDF Core 1.1)
├── rdf-wasm/
│   ├── src/
│   │   ├── rdf.rs             # Core RDF types (mirrors F* spec)
│   │   ├── ntriples.rs        # N-Triples parser (W3C RDF 1.1)
│   │   ├── turtle.rs          # Turtle parser (W3C RDF 1.1)
│   │   ├── sparql.rs          # SPARQL SELECT engine
│   │   ├── wasm_api.rs        # wasm-bindgen JS bindings
│   │   └── lib.rs             # Module declarations
│   ├── tests/
│   │   ├── rdf_tests.rs       # Core RDF type tests (25)
│   │   ├── w3c_ntriples.rs    # W3C N-Triples test suite (72)
│   │   ├── w3c_turtle.rs      # W3C Turtle test suite (69+74+80)
│   │   ├── w3c_sparql.rs      # W3C SPARQL 1.0 test harness
│   │   └── sparql_large_graph.rs  # Large graph integration tests (17)
│   └── build.sh               # WASM build + copy to docs/pkg/
├── kgx/                         # Knowledge Graph eXchange (from google/schemarama)
│   ├── wikidata/
│   │   ├── basic/               # 20 SPARQL CONSTRUCT queries (raw Wikidata IRIs)
│   │   └── bioschemas/          # 20 SPARQL CONSTRUCT queries (Schema.org/Bioschemas vocab)
│   └── README.md
├── tests/
│   └── w3c/                   # Git submodule: github.com/w3c/rdf-tests
├── docs/
│   ├── pkg/                   # WASM build artifacts (committed)
│   ├── index.html             # Interactive demo (uses real WASM)
│   ├── designissues/
│   │   ├── overview.md                # Design issues overview
│   │   ├── graphflow.md               # Graph transform design (full)
│   │   ├── attestation-model.md       # Combined attestation data model + architecture
│   │   ├── fstar-lean4-formalisation.md  # F*/Lean4 RDF formalisation survey
│   │   ├── kgx-pipeline.md           # KGX materialization pipeline + attestation plan
│   │   └── grounding-analysis.md      # Grounding analysis
│   ├── skills/
│   │   ├── testing.md                 # Test infrastructure and W3C harness guide
│   │   ├── measuring.md              # Performance and coverage measurement
│   │   ├── improving-sparql.md       # SPARQL engine improvement strategy
│   │   ├── validating.md             # Correctness validation layers
│   │   ├── optimising.md             # Engine optimization guide
│   │   └── periodic-review.md        # Review hooks and accuracy audits
│   └── tests.html             # Browser integration tests
└── CLAUDE.md                  # This file
```

## Current Progress

### Done
- [x] F* specification of RDF Core 1.1 types (wf_iri, wf_literal, triple, graph)
- [x] F* specification of graph operations (add, remove, union, find_by_subject, find_by_predicate)
- [x] F* specification of graph properties with proofs (add_no_dup, remove_absent, empty_no_bnodes)
- [x] F* specification of N-Triples serialization (escape table, nt_escaped predicate)
- [x] F* specification of SPARQL algebra basics (pattern terms, BGPs, solution mappings)
- [x] Rust implementation faithful to F* spec (rdf.rs)
- [x] N-Triples parser with full escape sequence support (ntriples.rs)
- [x] **Turtle parser** with full W3C compliance (turtle.rs)
- [x] SPARQL SELECT engine: BGP, FILTER, OPTIONAL, DISTINCT, ORDER BY, LIMIT/OFFSET, BASE
- [x] SPARQL functions: STR, LANG, DATATYPE, BOUND, REGEX, CONTAINS, STRSTARTS, STRENDS, ISLITERAL, ISIRI, ISBLANK
- [x] WASM bindings via wasm-bindgen (wasm_api.rs)
- [x] Web demo using real WASM library (docs/index.html)
- [x] W3C N-Triples test suite: **72/72 passing**
- [x] W3C Turtle test suite: **69/69 positive syntax, 74/74 negative syntax, 80/80 eval**
- [x] W3C SPARQL test harness: **93/436 passing** (21.3%) across 1.0 + 1.1 combined
- [x] Large graph SPARQL integration tests: **17 passing** (117-triple graph, multi-hop joins, OPTIONAL, DISTINCT, ORDER BY, FILTER)
- [x] Core RDF unit tests: **25 passing**
- [x] SPARQL unit tests: **28 passing**
- [x] Turtle unit tests: **14 passing**
- [x] N-Triples roundtrip verification in tests
- [x] W3C rdf-tests git submodule integrated

### W3C SPARQL Combined Scorecard (1.0 + 1.1)

**SPARQL 1.0** (21 suites):

| Suite               | Pass | Total | Rate   | Key blockers                              |
|--------------------|------|-------|--------|-------------------------------------------|
| algebra            | 5    | 14    | 35.7%  | GRAPH keyword, nested scope               |
| basic              | 15   | 27    | 55.6%  | BASE resolution, list patterns, quotes    |
| bnode-coreference  | 1    | 1     | 100%   | -                                         |
| boolean-eff-value  | 5    | 7     | 71.4%  | Typed literal BEV                         |
| bound              | 1    | 1     | 100%   | -                                         |
| cast               | 0    | 7     | 0.0%   | Casting functions                         |
| distinct           | 7    | 11    | 63.6%  | Numeric value comparison                  |
| expr-builtin       | 9    | 24    | 37.5%  | Complex expression parsing                |
| expr-equals        | 1    | 15    | 6.7%   | Value equality semantics                  |
| expr-ops           | 9    | 17    | 52.9%  | Division, type promotion                  |
| i18n               | 2    | 5     | 40.0%  | Unicode normalization                     |
| open-world         | 5    | 18    | 27.8%  | UNION scope, complex filters              |
| optional           | 1    | 7     | 14.3%  | OPTIONAL result ordering                  |
| optional-filter    | 1    | 6     | 16.7%  | FILTER inside OPTIONAL                    |
| reduced            | 0    | 2     | 0.0%   | REDUCED modifier                          |
| regex              | 14   | 21    | 66.7%  | Quantifier edge cases                     |
| solution-seq       | 0    | 13    | 0.0%   | ORDER BY + solution sequences             |
| sort               | 4    | 4     | 100%   | -                                         |
| triple-match       | 2    | 4     | 50.0%  | Named graph matching                      |
| type-promotion     | 0    | 30    | 0.0%   | Numeric type promotion                    |

**SPARQL 1.1** (11 suites):

| Suite              | Pass | Total | Rate   | Key blockers                              |
|-------------------|------|-------|--------|-------------------------------------------|
| aggregates        | 0    | 35    | 0.0%   | COUNT, SUM, AVG, GROUP BY, HAVING         |
| bind              | 0    | 10    | 0.0%   | BIND clause                               |
| bindings          | 1    | 11    | 9.1%   | VALUES clause                             |
| cast              | 0    | 6     | 0.0%   | Casting functions                         |
| exists            | 3    | 6     | 50.0%  | Complex EXISTS patterns                   |
| functions         | 3    | 74    | 4.1%   | SPARQL 1.1 built-in functions             |
| grouping          | 2    | 4     | 50.0%  | Complex GROUP BY expressions              |
| negation          | 2    | 11    | 18.2%  | MINUS, complex NOT EXISTS                 |
| project-expression| 0    | 7     | 0.0%   | SELECT expressions                        |
| property-path     | 0    | 29    | 0.0%   | Property path operators                   |
| subquery          | 0    | 9     | 0.0%   | Sub-SELECT                                |

### In Progress
- [ ] SPARQL parser improvements (literals in patterns, BASE resolution, REGEX filters)
- [ ] F* <-> Rust verification alignment (see Formalization Roadmap below)
- [ ] W3C SPARQL test suite coverage expansion
- [ ] KGX pipeline: materialization runner with attestation logging (see `docs/designissues/kgx-pipeline.md`)

### Planned
- [ ] Extend F* spec to cover N-Triples roundtrip proof (specification written, proof pending)
- [ ] Extend F* spec to cover full SPARQL evaluation semantics
- [ ] Formalize Turtle grammar and IRI resolution in F*
- [ ] Turtle serializer in Rust
- [ ] N-Quads support
- [ ] SPARQL CONSTRUCT, ASK, DESCRIBE
- [ ] SPARQL aggregates (COUNT, SUM, AVG, GROUP BY, HAVING)
- [ ] SPARQL property paths
- [ ] KGX materialization via QLever (40 SPARQL CONSTRUCT queries against Wikidata)
- [ ] Attestation logger with verifiable timestamps (RFC 3161 TSA integration)
- [ ] KGX graph assembly: parse materialized Turtle, merge, canonicalize, sign
- [ ] Storage abstraction (verified interface in F*, SQLite/IndexedDB backends)
- [ ] Hax (Rust->F*) or Low* extraction pipeline for verified WASM

## F* <-> Rust Correspondence

The Rust types in `rdf.rs` mirror the F* spec in `formal/fstar/rdfcore11.fstar.txt`:

| F* Type/Function | Rust Type/Function | Status |
|---------|-----------|-------------|
| `wf_iri` (non-empty, has `:`) | `Iri` with `new()` validation | Aligned |
| `wf_literal` (lang<->langString) | `Literal` with `new()` validation | Aligned |
| `subject = S_IRI \| S_BNode` | `enum Subject { Iri, BNode }` | Aligned |
| `rdf_term = T_IRI \| T_BNode \| T_Literal` | `enum RdfTerm { Iri, BNode, Literal }` | Aligned |
| `triple = {s; p; o}` | `struct Triple { s, p, o }` | Aligned |
| `rdf_graph = list triple` | `RdfGraph(Vec<Triple>)` | Aligned |
| `graph_add` (set-based) | `RdfGraph::add()` | Aligned |
| `graph_remove` | `RdfGraph::remove()` | Aligned |
| `graph_bnodes` | `RdfGraph::bnodes()` | Aligned (u64 vs string) |
| `find_by_subject` | `RdfGraph::find_by_subject()` | Aligned |
| `find_by_predicate` | `RdfGraph::find_by_predicate()` | Aligned |
| `graph_union` | Not yet in Rust | Pending |
| `triple_pattern` / `bgp` | `sparql.rs` pattern matching | Spec only |
| `must_escape` / `is_nt_escaped` | `Literal::fmt()` escape logic | Spec only |

### Verification Approaches

1. **Hax** (github.com/hacspec/hax) — translates Rust subset -> F* for verification. Most promising for this project since we already have both Rust and F*.
2. **Parallel spec + shared tests** — maintain F* spec and Rust impl separately, validate both against W3C test suites.
3. **Low* extraction** — rewrite F* spec in Low* subset, extract to C/WASM via KaRaMeL. Production-proven (HACL*, EverParse) but requires significant spec rewrite.

## Formalization Roadmap

Current F* spec covers ~241 lines. Formalization gap by module:

| Module | Rust LOC | F* Coverage | Feasibility | Priority |
|--------|----------|-------------|-------------|----------|
| **rdf.rs** | 345 | ~70% | High — extend graph ops | Done (graph_add, remove, union, find) |
| **ntriples.rs** | 365 | ~15% | Medium — grammar + roundtrip | Escape spec written, parser grammar next |
| **turtle.rs** | 1,198 | 0% | Hard — complex grammar, Unicode | Long-term (IRI resolution, collections) |
| **sparql.rs** | 1,438 | ~10% | Medium — SPARQL algebra | BGP/pattern specs written, eval pending |
| **wasm_api.rs** | 194 | 0% | Low priority — binding layer | Not planned |

### F* Proofs Completed
- `lemma_add_no_dup`: Adding a triple guarantees it's in the graph
- `lemma_remove_absent`: Removing a triple guarantees it's gone
- `lemma_empty_no_bnodes`: Empty graph has no blank nodes

### F* Specifications Written (proofs pending)
- N-Triples escape table and `is_nt_escaped` predicate
- Roundtrip property: `graph_isomorphic g (parse(serialize g))`
- SPARQL triple pattern matching against solution mappings
- BGP evaluation specification

### Next Formalization Targets
1. N-Triples grammar as F* inductive type (production rules)
2. SPARQL OPTIONAL semantics (left outer join)
3. Graph canonicalization specification
4. FILTER expression evaluation rules

## W3C Test Report

### Execution Time (debug build, single-threaded)

| Test Suite | Tests | Time | Notes |
|-----------|-------|------|-------|
| Unit tests (rdf, sparql, turtle, ntriples) | 42 | 0.01s | Core types, parsers, query engine |
| Core RDF type tests | 25 | 0.01s | Iri, Literal, Triple, Graph |
| Large graph SPARQL integration | 17 | 0.04s | 117-triple graph, multi-hop joins |
| W3C N-Triples | 72 | 0.02s | 72/72 (100%) |
| W3C SPARQL (1.0 + 1.1) | 13 harness tests | 0.45s | 93/436 individual (21.3%, ~390ms query time) |
| W3C Turtle | 3 harness tests | 0.07s | 223/223 individual (100%) |
| **Total** | **172** | **~0.53s** | All passing |

### W3C Compliance Summary

| Spec | Coverage | Status |
|------|----------|--------|
| N-Triples (RDF 1.1) | 72/72 (100%) | Complete |
| Turtle (RDF 1.1) | 223/223 (100%) | Complete (69 pos + 74 neg + 80 eval) |
| SPARQL 1.0 | 82/234 (35.0%) | In progress — 21 suites evaluated |
| SPARQL 1.1 | 11/202 (5.4%) | Growing — 11 suites evaluated |
| **SPARQL combined** | **93/436 (21.3%)** | **32 suites, ~390ms** |

### SPARQL Improvement Path

| Blocker | Tests Unlockable | Effort | Status |
|---------|-----------------|--------|--------|
| ~~Literal values in triple patterns~~ | ~~40~~ | ~~Medium~~ | Done |
| ~~FILTER REGEX parsing~~ | ~~21~~ | ~~Medium~~ | Done (14/21) |
| ~~Arithmetic operators (+, -, *, /)~~ | ~~14~~ | ~~Low~~ | Done (9/17) |
| ~~Boolean effective value~~ | ~~7~~ | ~~Low~~ | Done (5/7) |
| ~~UNION support~~ | ~~10~~ | ~~Medium~~ | Done |
| BASE IRI resolution in queries | ~5 (basic) | Low | Pending |
| Value equality semantics | ~14 (expr-equals) | Medium | Pending |
| Numeric type promotion | ~30 (type-promotion) | Medium | Pending |
| Solution sequences (ORDER BY edge cases) | ~13 | Medium | Pending |
| Casting functions | ~13 (cast) | Medium | Pending |
| Sub-SELECT / nested queries | ~20 (algebra, subquery) | High | Pending |
| Aggregates (COUNT, SUM, GROUP BY) | ~35 (1.1 aggregates) | High | Pending |
| Property paths | ~29 (1.1 property-path) | High | Pending |
| 1.1 built-in functions (STRLEN, SUBSTR, etc.) | ~74 (1.1 functions) | Medium | Pending |

## Design Documents

All design documents live under `docs/designissues/`:

- [`docs/designissues/attestation-model.md`](docs/designissues/attestation-model.md) — Combined reference: system overview, architecture, RDF attestation data model (transform events, shadow graphs, verification workflow)
- [`docs/designissues/graphflow.md`](docs/designissues/graphflow.md) — Graph transform system design (assertable graphs, transform certificates, evidence chains, verifiable credentials)
- [`docs/designissues/overview.md`](docs/designissues/overview.md) — Design issues overview
- [`docs/designissues/grounding-analysis.md`](docs/designissues/grounding-analysis.md) — Grounding analysis
- [`docs/designissues/fstar-lean4-formalisation.md`](docs/designissues/fstar-lean4-formalisation.md) — Survey of F\* and Lean 4 RDF 1.1 formalisations (CoqRDF, RDF.lean, portability assessment, module boundaries, proof obligations)
- [`docs/designissues/kgx-pipeline.md`](docs/designissues/kgx-pipeline.md) — KGX materialization pipeline: QLever execution, attestation logging, verifiable timestamps, graph assembly

### Skills & Knowledge Base

Operational knowledge for testing, measuring, and improving the platform lives in `docs/skills/`:

- [`docs/skills/testing.md`](docs/skills/testing.md) — Test infrastructure, W3C harness, test quality checklist
- [`docs/skills/measuring.md`](docs/skills/measuring.md) — Coverage metrics, performance measurement, regression detection
- [`docs/skills/improving-sparql.md`](docs/skills/improving-sparql.md) — SPARQL engine improvement strategy (tiered by impact)
- [`docs/skills/validating.md`](docs/skills/validating.md) — F* alignment, W3C compliance, roundtrip verification
- [`docs/skills/optimising.md`](docs/skills/optimising.md) — Query execution, indexing, WASM optimization
- [`docs/skills/periodic-review.md`](docs/skills/periodic-review.md) — Review hooks, accuracy audits, update triggers

## Build & Test

```bash
# Run all Rust tests (172 total)
cd rdf-wasm && cargo test

# Build WASM
cd rdf-wasm && ./build.sh

# Serve demo locally
cd docs && python3 -m http.server 8080
```

## Key Dependencies

- `wasm-bindgen` — Rust<->JS WASM bindings
- `serde` / `serde_json` — serialization
- `regex` — SPARQL REGEX function support
- `wasm-pack` — WASM build toolchain

## Development Notes

- BNode IDs are `u64` with atomic auto-generation (diverges from F* `string` — intentional for WASM performance)
- N-Triples serializer escapes all control chars for valid roundtrip
- SPARQL parser is hand-written recursive descent (no parser generator dependency)
- Turtle parser handles full Unicode PN_CHARS ranges for W3C compliance
- `wasm-opt = false` in Cargo.toml (binaryen download issues in some environments)
- W3C test files reference: `tests/w3c/rdf/rdf11/rdf-n-triples/` for N-Triples, `tests/w3c/rdf/rdf11/rdf-turtle/` for Turtle, `tests/w3c/sparql/sparql10/` for SPARQL

## Manifest Parsing Note

When tooling solidifies, parse W3C test manifests with our own Turtle parser (and cross-validate against another implementation) for assurance. Currently test lists are extracted manually from manifest files.
