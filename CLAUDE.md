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
│   │   └── w3c_sparql.rs      # W3C SPARQL 1.0 test harness
│   └── build.sh               # WASM build + copy to docs/pkg/
├── tests/
│   └── w3c/                   # Git submodule: github.com/w3c/rdf-tests
├── docs/
│   ├── pkg/                   # WASM build artifacts (committed)
│   ├── index.html             # Interactive demo (uses real WASM)
│   ├── verified-rdf-transform-design.md  # Design document
│   └── tests.html             # Browser integration tests
└── CLAUDE.md                  # This file
```

## Current Progress

### Done
- [x] F* specification of RDF Core 1.1 types (wf_iri, wf_literal, triple, graph)
- [x] Rust implementation faithful to F* spec (rdf.rs)
- [x] N-Triples parser with full escape sequence support (ntriples.rs)
- [x] **Turtle parser** with full W3C compliance (turtle.rs)
- [x] SPARQL SELECT engine: BGP, FILTER, OPTIONAL, DISTINCT, ORDER BY, LIMIT/OFFSET, BASE
- [x] SPARQL functions: STR, LANG, DATATYPE, BOUND, REGEX, CONTAINS, STRSTARTS, STRENDS, ISLITERAL, ISIRI, ISBLANK
- [x] WASM bindings via wasm-bindgen (wasm_api.rs)
- [x] Web demo using real WASM library (docs/index.html)
- [x] W3C N-Triples test suite: **72/72 passing**
- [x] W3C Turtle test suite: **69/69 positive syntax, 74/74 negative syntax, 80/80 eval**
- [x] W3C SPARQL 1.0 test harness: **13/79 passing** (16.5%) — baseline established
- [x] Core RDF unit tests: **25 passing**
- [x] SPARQL unit tests: **28 passing**
- [x] Turtle unit tests: **14 passing**
- [x] N-Triples roundtrip verification in tests
- [x] W3C rdf-tests git submodule integrated

### W3C SPARQL 1.0 Scorecard

| Suite        | Pass | Total | Rate   | Key blockers                            |
|-------------|------|-------|--------|-----------------------------------------|
| basic       | 1    | 27    | 3.7%   | BASE IRI resolution, literal patterns   |
| distinct    | 6    | 11    | 54.5%  | Numeric value comparison                |
| regex       | 0    | 17    | 0.0%   | FILTER REGEX parsing                    |
| expr-ops    | 3    | 17    | 17.6%  | Arithmetic operators (+, -, *)          |
| expr-builtin| 3    | 7     | 42.9%  | Expression binding                      |

### In Progress
- [ ] SPARQL parser improvements (literals in patterns, BASE resolution, REGEX filters)
- [ ] F* <-> Rust verification alignment
- [ ] W3C SPARQL test suite coverage expansion

### Planned
- [ ] Extend F* spec to cover N-Triples serialization with roundtrip proof
- [ ] Extend F* spec to cover SPARQL algebra
- [ ] Turtle serializer in Rust
- [ ] N-Quads support
- [ ] SPARQL CONSTRUCT, ASK, DESCRIBE
- [ ] SPARQL aggregates (COUNT, SUM, AVG, GROUP BY, HAVING)
- [ ] SPARQL property paths
- [ ] Storage abstraction (verified interface in F*, SQLite/IndexedDB backends)
- [ ] Hax (Rust->F*) or Low* extraction pipeline for verified WASM

## F* <-> Rust Correspondence

The Rust types in `rdf.rs` mirror the F* spec in `formal/fstar/rdfcore11.fstar.txt`:

| F* Type | Rust Type | Enforcement |
|---------|-----------|-------------|
| `wf_iri` (non-empty, has `:`) | `Iri` with `new()` validation | `Result<Self, RdfError>` |
| `wf_literal` (lang<->langString) | `Literal` with `new()` validation | `Result<Self, RdfError>` |
| `subject = S_IRI \| S_BNode` | `enum Subject { Iri, BNode }` | Compile-time (no Literal variant) |
| `rdf_term = T_IRI \| T_BNode \| T_Literal` | `enum RdfTerm { Iri, BNode, Literal }` | Compile-time |
| `triple = {s; p; o}` | `struct Triple { s, p, o }` | Type-level |
| `rdf_graph = list triple` | `RdfGraph(Vec<Triple>)` | Set semantics via duplicate rejection |

### Verification Approaches

1. **Hax** (github.com/hacspec/hax) — translates Rust subset -> F* for verification. Most promising for this project since we already have both Rust and F*.
2. **Parallel spec + shared tests** — maintain F* spec and Rust impl separately, validate both against W3C test suites.
3. **Low* extraction** — rewrite F* spec in Low* subset, extract to C/WASM via KaRaMeL. Production-proven (HACL*, EverParse) but requires significant spec rewrite.

## Build & Test

```bash
# Run all Rust tests (148 total)
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
