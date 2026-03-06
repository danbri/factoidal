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

A **formally verified RDF toolkit** where every layer — types, parsing, querying, serialization — traces back to F* specifications. The **end goal** is verified WASM extracted directly from F* via KaRaMeL, not manually-written Rust that happens to mirror a spec.

### Target Architecture: F* → KaRaMeL → Verified WASM

```
F* formal spec (Low* subset)
    │
    ├── verify proofs (F* typechecker)
    ├── erase proofs
    └── KaRaMeL extraction → C or WASM (verified binary)
                                │
                            wasmsign2 + SLSA attestation
                                │
                            Signed, verified WASM module
```

This is production-proven: **HACL\*** crypto code extracted this way runs in Firefox, the Linux kernel, Python, mbedTLS, Tezos, and WireGuard. **EverParse** extracts verified parsers to C/WASM for Windows Hyper-V networking. The toolchain exists; the project's job is to apply it to RDF/SPARQL.

### Current Architecture (interim — converging toward target)

```
F* formal spec  ->  Rust implementation  ->  WASM + JS bindings  ->  Web demo & tests
     ^                    ^                        ^
  verified          W3C test suite           real library, not a copy
```

The Rust/WASM implementation is the current working system. The F* specs are **not just documentation** — they are the foundation for the KaRaMeL extraction pipeline. Every F* spec written today is an investment toward the target architecture. The gap to close:

1. **Rewrite core F* specs in Low\* subset** (required for KaRaMeL extraction)
2. **Set up KaRaMeL toolchain** in CI (F* → C/WASM extraction)
3. **Sign extracted WASM** with wasmsign2 + Sigstore/cosign attestation
4. **Retire manual Rust implementation** once extracted WASM covers the same surface

### Parallel verification path: Hax (Rust → F*)

[Hax](https://github.com/hacspec/hax) translates Rust subset → F* for verification. This is the **bridge** between the current Rust implementation and the F* specs:

1. Annotate Rust code with `#[hax::ensures(...)]` attributes
2. Extract F* from annotated Rust
3. Verify extracted F* against hand-written spec
4. Any divergence = bug in Rust or spec

This gives machine-checked verification of the Rust code *now*, while the Low*/KaRaMeL pipeline matures.

### Trust boundary

KaRaMeL itself is unverified OCaml — it's in the trusted computing base. Verification guarantees hold at the F* source level. The CI pipeline should: verify F* proofs → extract via KaRaMeL → sign with wasmsign2 → publish SLSA attestation.

## Principles

- **No cobbling.** Everything lives in Rust/WASM/F*. No external JS reimplementations.
- **Verify, don't trust.** F* specs define correctness; Rust implements; W3C tests validate.
- **One implementation.** The web demo uses the real WASM binary. Same code everywhere.
- **Incremental formalization.** Start with executable specs, progressively tighten to proofs.
- **F* specs are not documentation.** They are the source for verified WASM extraction via KaRaMeL. Every spec written is a step toward the target architecture.
- **Spec before code.** For new features, write the F* specification first (or concurrently). This prevents rework and ensures the verification pipeline stays aligned.

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
- [x] W3C SPARQL test harness: **159/436 passing** (36.5%) across 1.0 + 1.1 combined
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
| basic              | 20   | 27    | 74.1%  | BASE resolution, list patterns            |
| bnode-coreference  | 1    | 1     | 100%   | -                                         |
| boolean-eff-value  | 5    | 7     | 71.4%  | Typed literal BEV                         |
| bound              | 1    | 1     | 100%   | -                                         |
| cast               | 0    | 7     | 0.0%   | Casting functions                         |
| distinct           | 7    | 11    | 63.6%  | Numeric value comparison                  |
| expr-builtin       | 9    | 24    | 37.5%  | Complex expression parsing                |
| expr-equals        | 9    | 15    | 60.0%  | Cross-graph equality, remaining edge cases|
| expr-ops           | 9    | 17    | 52.9%  | Division, type promotion                  |
| i18n               | 2    | 5     | 40.0%  | Unicode normalization                     |
| open-world         | 7    | 18    | 38.9%  | UNION scope, complex filters              |
| optional           | 1    | 7     | 14.3%  | OPTIONAL result ordering                  |
| optional-filter    | 1    | 6     | 16.7%  | FILTER inside OPTIONAL                    |
| reduced            | 2    | 2     | 100%   | -                                         |
| regex              | 14   | 21    | 66.7%  | Quantifier edge cases                     |
| solution-seq       | 11   | 13    | 84.6%  | OFFSET edge cases                         |
| sort               | 4    | 4     | 100%   | -                                         |
| triple-match       | 2    | 4     | 50.0%  | Named graph matching                      |
| type-promotion     | 0    | 30    | 0.0%   | Numeric type promotion                    |

**SPARQL 1.1** (11 suites):

| Suite              | Pass | Total | Rate   | Key blockers                              |
|-------------------|------|-------|--------|-------------------------------------------|
| aggregates        | 0    | 35    | 0.0%   | COUNT, SUM, AVG, GROUP BY, HAVING         |
| bind              | 3    | 10    | 30.0%  | Complex BIND expressions                  |
| bindings          | 1    | 11    | 9.1%   | VALUES clause                             |
| cast              | 0    | 6     | 0.0%   | Casting functions                         |
| exists            | 3    | 6     | 50.0%  | Complex EXISTS patterns                   |
| functions         | 31   | 74    | 41.9%  | Remaining 1.1 built-in functions          |
| grouping          | 2    | 4     | 50.0%  | Complex GROUP BY expressions              |
| negation          | 2    | 11    | 18.2%  | MINUS, complex NOT EXISTS                 |
| project-expression| 7    | 7     | 100%   | -                                         |
| property-path     | 0    | 29    | 0.0%   | Property path operators                   |
| subquery          | 0    | 9     | 0.0%   | Sub-SELECT                                |

### In Progress
- [ ] **Layer 1: Type system** — XSD numeric type promotion, casting functions, value equality (next priority)
- [ ] F* <-> Rust verification alignment — extend `sparql11.fstar.txt` alongside implementation
- [ ] KGX pipeline: materialization runner with attestation logging (see `docs/designissues/kgx-pipeline.md`)

### Planned — Verification Pipeline (highest priority)
- [ ] **Low* rewrite of core types** — rewrite `rdfcore11.fstar.txt` in Low* subset for KaRaMeL extraction
- [ ] **N-Triples roundtrip proof** — specification written, prove in Low*, extract verified serializer via KaRaMeL
- [ ] **Hax integration** — annotate Rust with `#[hax::ensures(...)]`, extract F*, verify against hand-written spec
- [ ] **KaRaMeL CI pipeline** — verify F* proofs → extract to C/WASM → sign with wasmsign2 → SLSA attestation
- [ ] **EverParse-style parser extraction** — verified N-Triples/Turtle parsers extracted from F* format specs

### Planned — SPARQL Engine Layers
- [ ] **Layer 2: Query composition** — Sub-SELECT, MINUS, GRAPH, VALUES
- [ ] **Layer 3: Aggregation pipeline** — GROUP BY → aggregate functions → HAVING
- [ ] **Layer 4: Property paths** — sequence, alternative, inverse, transitive closure
- [ ] **Layer 6: DESCRIBE** — implementation-defined, low priority

### Planned — Other
- [ ] Formalize Turtle grammar and IRI resolution in F*
- [ ] Turtle serializer in Rust
- [ ] N-Quads support
- [ ] KGX materialization via QLever (40 SPARQL CONSTRUCT queries against Wikidata)
- [ ] Attestation logger with verifiable timestamps (RFC 3161 TSA integration)
- [ ] KGX graph assembly: parse materialized Turtle, merge, canonicalize, sign
- [ ] Storage abstraction (verified interface in F*, SQLite/IndexedDB backends)

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

### Verification Pipeline (current status and target)

The project has **two converging verification paths**. Both require the F* specs to be complete and correct — the specs are the project's primary deliverable, not supplementary documentation.

**Path A: KaRaMeL extraction (target architecture)**
```
F* Low* spec → F* typechecker (verify) → erase proofs → KaRaMeL → C/WASM
```
- Production-proven: HACL* (Firefox, Linux kernel), EverParse (Windows Hyper-V)
- **Current blocker:** F* specs use high-level F*, not Low* subset. Need Low* rewrite.
- **Precedent:** EverParse extracts verified parsers — directly applicable to N-Triples/Turtle serialization roundtrip proofs.
- **Priority:** Phase 1 target is verified N-Triples serialize/deserialize (see ARCHITECTURE.md Phase 1).

**Path B: Hax verification (bridge for current Rust)**
```
Rust code + #[hax::ensures(...)] → Hax → extracted F* → verify against hand-written spec
```
- Validates the existing Rust implementation against F* specs with machine-checked proofs.
- **Current blocker:** Hax integration not yet set up. Monthly review item to track readiness.
- **Value:** Gives machine-checked verification *now* while Low*/KaRaMeL pipeline matures.

**Path C: Parallel spec + shared tests (interim, currently active)**
- Maintain F* spec and Rust impl separately, validate both against W3C test suites.
- **This is the fallback**, not the goal. It validates behavior but doesn't constitute machine-checked proof.

## Formalization Roadmap (toward KaRaMeL extraction)

The F* specs are **not documentation** — they are the source code for the verified WASM binary. Every line of F* spec written is progress toward replacing the manual Rust implementation with KaRaMeL-extracted verified code.

Current F* spec covers ~1,638 lines (rdfcore11: 492, sparql11: 1,146). Formalization gap by module:

| Module | Rust LOC | F* Coverage | KaRaMeL Readiness | Priority |
|--------|----------|-------------|-------------------|----------|
| **rdf.rs** | 345 | ~70% | Needs Low* rewrite | High — closest to extraction |
| **ntriples.rs** | 365 | ~15% | Needs EverParse-style spec | High — Phase 1 extraction target |
| **turtle.rs** | 1,198 | 0% | Hard — complex grammar | Long-term |
| **sparql.rs** | 2,922 | ~15% | Algebra spec growing | Medium — after core types |
| **wasm_api.rs** | 194 | 0% | Binding layer, not extracted | Not applicable |

### KaRaMeL Extraction Phases

**Phase 1 — Verified serialization (near-term)**
- Rewrite N-Triples serialize/deserialize specs in Low* subset
- Prove roundtrip correctness: `graph_isomorphic g (parse(serialize g))`
- Extract to WASM via KaRaMeL
- Model: EverParse verified parsers

**Phase 2 — Verified core types (medium-term)**
- Rewrite `rdf.rs` types in Low* (wf_iri, wf_literal, triple, graph)
- Extract graph operations to WASM
- Verify with wasmsign2 + SLSA attestation

**Phase 3 — Verified SPARQL algebra (longer-term)**
- SPARQL algebra evaluation as pure function `query × graph → result_set`
- Prove correctness against W3C SPARQL algebra spec
- Model: Benzaken et al. (ITP 2018) verified SQL algebra in Coq

### F* Proofs Completed (all verified, zero admit() calls)

**RDF.Graph.Executable.fst** (zero admit, 5 remaining assume val for string library functions):
- `lemma_add_no_dup`: Adding a triple guarantees it's in the graph (proved via triple_eq reflexivity)
- `lemma_remove_absent`: Removing a triple guarantees it's gone (proved by induction on graph)
- `lemma_empty_no_bnodes`: Empty graph has no blank nodes
- `lemma_compare_reflexive`: Value equality is reflexive for all SPARQL value types
- `lemma_compare_symmetric`: Value equality is symmetric for all comparable types
- `lemma_incompatible_types`: Numeric vs plain literal comparison returns None
- `lemma_bind_preserves_existing`: BIND does not overwrite existing variable bindings
- Equality reflexivity lemmas: `subject_eq_refl`, `literal_eq_refl`, `rdf_term_eq_refl`, `triple_eq_refl`
- `lemma_mem_triple_append`: mem_triple finds a triple appended to a list

**SPARQL11.Algebra.fst** (43 remaining assume val — string/hash/date library functions + complex evaluators):
- `lemma_union_assoc`: Union is associative
- `lemma_union_nil_l/r`: Union with empty is identity
- `lemma_filter_union`: Filter distributes over union
- `lemma_offset_zero`: OFFSET 0 is identity
- `lemma_filter_mem`: Elements of filter are in original list
- `lemma_sm_compatible_refl`: Solution mapping compatibility is reflexive
- `lemma_sm_merge_empty_l/r`: Merge with empty is identity
- `lemma_domains_disjoint_empty_l`: Empty mapping is disjoint with any

### Concrete Implementations (replacing assume val)

**RDF.Graph.Executable.fst:**
- `string_contains_colon`: Concrete via `list_of_string` (was `assume val`)
- `subject_eq`, `literal_eq`, `rdf_term_eq`: Concrete decidable equality by pattern matching
- IRI constants (`xsd_string`, `rdf_lang_string`, etc.): Concrete strings with `assert_norm` verification

**SPARQL11.Algebra.fst** (32 remaining assume val — leaf functions only):
- `eval_expr`: Full recursive expression evaluator (~60 cases: arithmetic, comparison, logical, type tests, accessors, string/numeric/hash/datetime, BOUND, IF, COALESCE, IN/NOT IN)
- `eval_coalesce`, `eval_in`, `eval_concat`: List-based expression helpers (mutually recursive with eval_expr)
- `eval_expr_ebv`: EBV of expression evaluation
- `eval_pattern`: Complete group graph pattern evaluator (BGP, Join, LeftJoin, Filter, Union, Minus, Bind, Values, Empty)
- `value_compare`: Type-aware SPARQL comparison (int, bool, decimal, double, IRI, literal)
- `try_bind_subject`, `try_bind_term`: Pattern matching with binding extension
- `pattern_term_matches`, `pattern_subject_matches`: Concrete bool predicates
- `tp_match`: Triple pattern matching threading subject→predicate→object
- `eval_single_tp`, `eval_bgp`: Full BGP evaluation via concatMap
- `sm_empty/lookup/bind/domain/compatible/merge`: Solution mapping operations
- `graph_triples`, `triple_subject/predicate/object`: Graph accessors
- `lit_lexical/datatype/lang`, `iri_to_string`, `string_to_iri`: Literal/IRI accessors
- `fn_str`, `fn_lang`, `fn_datatype`, `fn_strdt`, `fn_strlang`: SPARQL accessor functions
- `ebv`: Effective Boolean Value (§17.2.2)
- `same_term`, `is_numeric_datatype`: Term comparison functions
- `domains_disjoint`, `list_drop`, `list_take`, `project`: Query operations
- `string_contains`, `string_starts_with`, `string_ends_with`: Via list_of_string
- `string_substring`, `string_upper`, `string_lower`, `string_concat`: Via FStar.String
- `int_abs`: Concrete absolute value
- All XSD/RDF IRI constants: Concrete strings with `assert_norm` verification

### F* Specifications Written (proofs pending)
- N-Triples escape table and `is_nt_escaped` predicate
- Roundtrip property: `graph_isomorphic g (parse(serialize g))`

### Next Formalization Targets
1. N-Triples grammar as F* inductive type (production rules)
2. Concrete `eval_expr` implementation (recursive expression evaluator)
3. Graph canonicalization specification
4. Low* rewrite of core types for KaRaMeL extraction

## W3C Test Report

### Execution Time (debug build, single-threaded)

| Test Suite | Tests | Time | Notes |
|-----------|-------|------|-------|
| Unit tests (rdf, sparql, turtle, ntriples) | 42 | 0.01s | Core types, parsers, query engine |
| Core RDF type tests | 25 | 0.01s | Iri, Literal, Triple, Graph |
| Large graph SPARQL integration | 17 | 0.04s | 117-triple graph, multi-hop joins |
| W3C N-Triples | 72 | 0.02s | 72/72 (100%) |
| W3C SPARQL (1.0 + 1.1) | 13 harness tests | 0.45s | 115/436 individual (26.4%, ~390ms query time) |
| W3C Turtle | 3 harness tests | 0.07s | 223/223 individual (100%) |
| **Total** | **172** | **~0.53s** | All passing |

### W3C Compliance Summary

| Spec | Coverage | Status |
|------|----------|--------|
| N-Triples (RDF 1.1) | 72/72 (100%) | Complete |
| Turtle (RDF 1.1) | 223/223 (100%) | Complete (69 pos + 74 neg + 80 eval) |
| SPARQL 1.0 | 110/234 (47.0%) | In progress — 21 suites evaluated |
| SPARQL 1.1 | 49/202 (24.3%) | Growing — 11 suites evaluated |
| **SPARQL combined** | **159/436 (36.5%)** | **32 suites, ~500ms** |

### SPARQL Implementation Roadmap (Architecture-Driven)

Implementation is ordered by **architectural layer**, not by individual test score impact.
Each layer builds on the one below. Leaf functions (hash, string, date/time) are added
last — they're easy to slot in once the evaluation pipeline is sound.

**Layer 0 — Core Algebra (the evaluation model)** ✅ Mostly done

The foundational join/filter/union machinery that everything else depends on.

| Component | Status | Notes |
|-----------|--------|-------|
| BGP evaluation (triple pattern matching) | ✅ Done | Core of all queries |
| OPTIONAL (left outer join) | ⚠️ Partial (1/7) | Semantics correct but result ordering, nested OPTIONAL need work |
| UNION | ✅ Done | |
| FILTER (boolean expressions) | ✅ Done | Core comparisons, AND/OR/NOT |
| DISTINCT, REDUCED | ✅ Done | |
| ORDER BY, LIMIT/OFFSET | ✅ Done (11/13) | Edge cases remain |
| NOT EXISTS / EXISTS | ⚠️ Partial (3/6) | Basic patterns work, complex nesting pending |
| ASK query form | Pending | Trivial — evaluate SELECT, return boolean |

**Layer 1 — Type System & Value Space** 🔜 Next priority

Correct value comparison underpins everything from FILTER to ORDER BY to aggregates.
Getting this right now prevents rework later.

| Component | Tests Affected | Status | Notes |
|-----------|---------------|--------|-------|
| XSD numeric type promotion (integer→decimal→float→double) | ~30 (type-promotion) + ripple across expr-ops, distinct | Pending | Needs clean promotion hierarchy in typed_compare |
| Casting functions (xsd:integer(), xsd:string(), etc.) | ~13 (cast suites) | Pending | Build on type promotion |
| Value equality semantics (RDF term equality vs value equality) | ~6 remaining (expr-equals) | Mostly done | Edge cases: typed vs untyped literals |
| Boolean effective value (complete) | ~2 remaining | Mostly done | Typed literal BEV |

**Layer 2 — Query Composition** 📋 After Layer 1

These features let queries nest and compose — prerequisite for real-world SPARQL.

| Component | Tests Affected | Status | Notes |
|-----------|---------------|--------|-------|
| Sub-SELECT (nested queries) | ~9 (subquery) + ~5 (algebra) | Pending | Requires recursive evaluate_query; also unblocks subquery suite |
| BIND clause (complete) | ~7 remaining (bind) | Partial (3/10) | Basic BIND works, complex expressions pending |
| VALUES clause | ~10 remaining (bindings) | Partial (1/11) | Inline data injection |
| MINUS | ~8 (negation) | Pending | Anti-join semantics — straightforward once joins are solid |
| GRAPH keyword (named graph patterns) | ~4 (algebra) + ~2 (triple-match) | Pending | Requires dataset model (default + named graphs) |
| CONSTRUCT query form | ~2 (subquery) | Pending | Template-based graph construction from bindings — **required for KGX pipeline** |

**Layer 3 — Aggregation Pipeline** 📋 After Layer 2

Aggregates require a clean evaluation pipeline: GROUP BY partitioning → aggregate
functions → HAVING filter → projection. Build the pipeline, then add functions.

| Component | Tests Affected | Status | Notes |
|-----------|---------------|--------|-------|
| GROUP BY partitioning | ~4 (grouping) + prerequisite for aggregates | Partial (2/4) | |
| Aggregate functions (COUNT, SUM, AVG, MIN, MAX, SAMPLE, GROUP_CONCAT) | ~35 (aggregates) | Pending | Pipeline first, functions second |
| HAVING (post-aggregation filter) | included in aggregates | Pending | Reuses FILTER machinery |

**Layer 4 — Property Paths** 📋 After Layer 2

Graph traversal extension — essentially a mini regex engine over the graph.

| Component | Tests Affected | Status | Notes |
|-----------|---------------|--------|-------|
| Simple property paths (single IRI) | ~5 | Pending | Trivial — same as triple pattern |
| Sequence (/) and alternative (\|) | ~8 | Pending | Finite composition |
| Inverse (^) | ~4 | Pending | Reverse edge traversal |
| Zero-or-more (*), one-or-more (+), zero-or-one (?) | ~8 | Pending | Recursive closure — needs cycle detection |
| Negated property sets (!) | ~4 | Pending | |

**Layer 5 — Leaf Functions** 📋 Ongoing (low priority)

Built-in functions that operate on individual values. These are architecturally
trivial — each is an isolated pure function. Add as needed but don't prioritize
over structural layers.

| Category | Examples | Tests Affected | Status |
|----------|----------|---------------|--------|
| String functions | STRLEN, SUBSTR, UCASE, LCASE, ENCODE_FOR_URI, REPLACE | ~20 remaining (1.1/functions) | Partial — many done |
| Hash functions | MD5, SHA1, SHA256, SHA384, SHA512 | ~5 (1.1/functions) | ✅ Done |
| Date/time accessors | YEAR, MONTH, DAY, HOURS, MINUTES, SECONDS, TZ | ~8 (1.1/functions) | ✅ Done |
| Term constructors | STRDT, STRLANG, IRI, BNODE | ~4 (1.1/functions) | ✅ Partial |
| Numeric functions | ABS, ROUND, CEIL, FLOOR | ~4 (1.1/functions) | ✅ Done |
| REGEX edge cases | Quantifiers, anchors | ~7 remaining (regex) | Partial |

**Layer 6 — DESCRIBE** 📋 Future

Implementation-defined query form. Low priority — not needed for core compliance or KGX.

### Design Principle: Spec Before Code — F* Specs Are the Primary Deliverable

For Layers 1–4, write the F* specification first (or concurrently), then implement in Rust.
This is not just good practice — the F* specs are the source for KaRaMeL-extracted verified WASM.
Every F* spec written today directly advances the target architecture.

- `formal/fstar/sparql11.fstar.txt` should grow alongside the Rust implementation
- New specs should be written with Low* extraction in mind (avoid high-level features that block KaRaMeL)
- When adding Rust code, check: "could this be extracted from F* instead?"

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

# Verify F* specifications
eval $(opam env --switch=fstar) && cd formal/fstar && make verify

# Serve demo locally
cd docs && python3 -m http.server 8080
```

### F* Toolchain

The F* formal verification toolchain is installed and operational:

- **F* compiler**: `fstar.exe` (2025.12.15) — installed via opam (`opam install fstar`)
- **Z3 SMT solver**: `z3-4.8.5` and `z3-4.13.3` — required by F* for proof discharge
- **opam switch**: `fstar` (OCaml 4.14.1)

To activate the F* environment: `eval $(opam env --switch=fstar)`

Both F* modules currently verify successfully:
- `formal/fstar/RDF.Graph.Executable.fst` — RDF core types, graph operations, properties
- `formal/fstar/SPARQL11.Algebra.fst` — SPARQL algebra, evaluation semantics, built-in functions

The `.fst` files are the compilable versions; the `.fstar.txt` files are kept as the original textual specs. The architecture for F*'s role in the project is documented in [`docs/designissues/fstar_role.md`](docs/designissues/fstar_role.md).

## Key Dependencies

- `wasm-bindgen` — Rust<->JS WASM bindings
- `serde` / `serde_json` — serialization
- `regex` — SPARQL REGEX function support
- `fstar` — F* formal verification compiler (opam)
- `z3` — SMT solver (z3-4.8.5, z3-4.13.3)
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
