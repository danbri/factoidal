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

The main architecture and rationale are documented here:

-> `docs/verified-rdf-transform-design.md`

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
├── tests/
│   └── w3c/                   # Git submodule: github.com/w3c/rdf-tests
├── docs/
│   ├── pkg/                   # WASM build artifacts (committed)
│   ├── index.html             # Interactive demo (uses real WASM)
│   ├── verified-rdf-transform-design.md  # Design document (original)
│   ├── designissues.md        # Design issues (concise)
│   ├── designissues-graphflow.md  # Graph transform design (full)
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
- [x] W3C SPARQL test harness: **32/436 passing** (7.3%) across 1.0 + 1.1 combined
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
| algebra            | 3    | 14    | 21.4%  | Nested OPTIONAL, GRAPH, sub-SELECT        |
| basic              | 1    | 27    | 3.7%   | Literal patterns, BASE resolution, lists  |
| bnode-coreference  | 1    | 1     | 100%   | -                                         |
| boolean-eff-value  | 0    | 7     | 0.0%   | Boolean effective value semantics          |
| bound              | 1    | 1     | 100%   | -                                         |
| cast               | 0    | 7     | 0.0%   | Casting functions                         |
| distinct           | 6    | 11    | 54.5%  | Numeric value comparison                  |
| expr-builtin       | 5    | 24    | 20.8%  | Unbound var handling, expression parsing  |
| expr-equals        | 0    | 15    | 0.0%   | Value equality semantics                  |
| expr-ops           | 3    | 17    | 17.6%  | Arithmetic operators (+, -, *)            |
| i18n               | 2    | 5     | 40.0%  | Unicode normalization                     |
| open-world         | 3    | 18    | 16.7%  | Open-world semantics, UNION               |
| optional           | 0    | 7     | 0.0%   | OPTIONAL result mismatch                  |
| optional-filter    | 0    | 6     | 0.0%   | FILTER inside OPTIONAL                    |
| reduced            | 0    | 2     | 0.0%   | REDUCED modifier                          |
| regex              | 0    | 21    | 0.0%   | FILTER REGEX parsing                      |
| solution-seq       | 0    | 13    | 0.0%   | ORDER BY + solution sequences             |
| sort               | 3    | 4     | 75.0%  | Complex sort keys                         |
| triple-match       | 2    | 4     | 50.0%  | Named graph matching                      |
| type-promotion     | 0    | 30    | 0.0%   | Numeric type promotion                    |

**SPARQL 1.1** (11 suites):

| Suite              | Pass | Total | Rate   | Key blockers                              |
|-------------------|------|-------|--------|-------------------------------------------|
| aggregates        | 0    | 35    | 0.0%   | COUNT, SUM, AVG, GROUP BY, HAVING         |
| bind              | 0    | 10    | 0.0%   | BIND clause                               |
| bindings          | 0    | 11    | 0.0%   | VALUES clause                             |
| cast              | 0    | 6     | 0.0%   | Casting functions                         |
| exists            | 0    | 6     | 0.0%   | EXISTS / NOT EXISTS                       |
| functions         | 0    | 74    | 0.0%   | SPARQL 1.1 built-in functions             |
| grouping          | 2    | 4     | 50.0%  | Complex GROUP BY expressions              |
| negation          | 0    | 11    | 0.0%   | MINUS, NOT EXISTS                         |
| project-expression| 0    | 7     | 0.0%   | SELECT expressions                        |
| property-path     | 0    | 29    | 0.0%   | Property path operators                   |
| subquery          | 0    | 9     | 0.0%   | Sub-SELECT                                |

### In Progress
- [ ] SPARQL parser improvements (literals in patterns, BASE resolution, REGEX filters)
- [ ] F* <-> Rust verification alignment (see Formalization Roadmap below)
- [ ] W3C SPARQL test suite coverage expansion

### Planned
- [ ] Extend F* spec to cover N-Triples roundtrip proof (specification written, proof pending)
- [ ] Extend F* spec to cover full SPARQL evaluation semantics
- [ ] Formalize Turtle grammar and IRI resolution in F*
- [ ] Turtle serializer in Rust
- [ ] N-Quads support
- [ ] SPARQL CONSTRUCT, ASK, DESCRIBE
- [ ] SPARQL aggregates (COUNT, SUM, AVG, GROUP BY, HAVING)
- [ ] SPARQL property paths
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

Current F* spec covers ~160 lines. Formalization gap by module:

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
| W3C SPARQL (1.0 + 1.1) | 13 harness tests | 0.38s | 32/436 individual (7.3%) |
| W3C Turtle | 3 harness tests | 0.07s | 223/223 individual (100%) |
| **Total** | **172** | **~0.53s** | All passing |

### W3C Compliance Summary

| Spec | Coverage | Status |
|------|----------|--------|
| N-Triples (RDF 1.1) | 72/72 (100%) | Complete |
| Turtle (RDF 1.1) | 223/223 (100%) | Complete (69 pos + 74 neg + 80 eval) |
| SPARQL 1.0 | 30/234 (12.8%) | In progress — 21 suites evaluated |
| SPARQL 1.1 | 2/202 (1.0%) | Baseline — 11 query suites evaluated |
| **SPARQL combined** | **32/436 (7.3%)** | **32 suites, ~375ms** |

### SPARQL Improvement Path

| Blocker | Tests Unlockable | Effort |
|---------|-----------------|--------|
| Literal values in triple patterns | ~40 (basic, optional, sort, etc.) | Medium |
| FILTER REGEX parsing (`FILTER REGEX(?x, "pat")`) | ~21 (regex suite) | Medium |
| Arithmetic operators (+, -, *, /) | ~14 (expr-ops) | Low |
| BASE IRI resolution in queries | ~5 (basic) | Low |
| UNION support | ~10 (open-world, optional) | Medium |
| Sub-SELECT / nested queries | ~20 (algebra, subquery) | High |
| Aggregates (COUNT, SUM, GROUP BY) | ~35 (1.1 aggregates) | High |
| Property paths | ~29 (1.1 property-path) | High |
| 1.1 built-in functions (STRLEN, SUBSTR, etc.) | ~74 (1.1 functions) | Medium |

## Design Documents

- [`docs/designissues-graphflow.md`](docs/designissues-graphflow.md) — Full verified RDF transform system design (graphs as assertable objects, transform certificates, evidence chains, verifiable credentials)
- [`docs/designissues.md`](docs/designissues.md) — Design issues overview
- [`docs/verified-rdf-transform-design.md`](docs/verified-rdf-transform-design.md) — Original design document

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
