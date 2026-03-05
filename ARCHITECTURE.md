# Factoidal: Architecture Analysis & Roadmap

## Q1: Is the JS wrapping more correct than the WASM?

**No — the Rust/WASM is structurally stricter.** Both implementations faithfully mirror the
F\* spec, but Rust's type system preserves more of the refinement-type guarantees at compile time:

| Aspect | JS (docs/index.html) | Rust (rdf-wasm/src/rdf.rs) | F\* (formal/) |
|--------|----------------------|---------------------------|---------------|
| Subject type restriction | `parseSubject()` convention only — `Triple` constructor accepts any object | `Subject` enum: `Iri \| BNode` — compiler rejects `Literal` | `subject = S_IRI \| S_BNode` — structurally impossible |
| Predicate type | Checked at call sites (`new Iri(...)`) | `Triple.p: Iri` — compiler-enforced | `p: wf_iri` — type-level |
| IRI well-formedness | Runtime `throw` in constructor | `Result<Self, RdfError>` — forces error handling | Refinement type `wf_iri` |
| Literal well-formedness | Runtime `throw` | `Result<Self, RdfError>` | Refinement type `wf_literal` |
| Equality | Manual `equals()` methods | Derived `PartialEq` + `Eq` | Structural equality |
| Serialization | Manual `toJSON()` / `toString()` | Derived `Serialize` / `Deserialize` + serde | N/A |

**Where JS is arguably better:**
- Zero-dependency, runs anywhere, easier to inspect and audit
- The `docs/tests.html` test suite is browser-runnable with no build step

**Where Rust/WASM is better:**
- Compile-time enforcement of subject/predicate restrictions
- Memory safety guarantees
- `Result` types force callers to handle invalid data
- Serde roundtrip means serialization is structurally verified

**Verdict:** Rust/WASM is the more correct implementation. JS is the more accessible one.
Both are faithful to the F\* spec; the gap is in *how much the language enforces* vs *trusts the programmer*.

---

## Q2: Can an F\* service sign WASM? Can browsers vouch for WASM hashes?

### F\* → WASM extraction pipeline

F\* can extract verified code to WASM via **KaRaMeL** (from the Low\* subset):

```
F* source → verify proofs → erase proofs → KaRaMeL → C or WASM
```

This is production-proven: **HACL\*** crypto code extracted this way runs in Firefox,
the Linux kernel, Python, mbedTLS, Tezos, and WireGuard.

**Current repo gap:** The F\* spec in `formal/fstar/rdfcore11.fstar.txt` uses
high-level F\* (not Low\*), so it can't be directly extracted to WASM via KaRaMeL today.
To close this gap, you'd need a Low\* version of the core types, or use F\* → OCaml
extraction + `js_of_ocaml` for a less-optimized but verified JS output.

### Signing WASM with verification attestation

No off-the-shelf "F\* verification service" exists, but the pieces are available:

1. **wasmsign2** — embeds Ed25519 signatures in WASM custom sections
2. **Sigstore/cosign** — SLSA attestations binding binary to build provenance
3. A CI pipeline could: verify F\* proofs → extract via KaRaMeL → sign with wasmsign2 →
   publish SLSA attestation

**Trust boundary:** KaRaMeL itself is unverified OCaml. The verification guarantees hold
at the F\* source level; KaRaMeL is in the trusted computing base.

### Browser-side WASM integrity

| Mechanism | Status | How it works |
|-----------|--------|-------------|
| **`fetch()` integrity option** | Supported (Chrome, Firefox, Safari) | `fetch('m.wasm', {integrity: 'sha384-...'})` — rejects if hash mismatch |
| **CSP `wasm-unsafe-eval`** | Supported (Chrome 103+, Firefox 102+) | Gates whether WASM can execute at all |
| **WASM module signatures** | Proposal stage (not in browsers) | [WebAssembly/design#1413](https://github.com/WebAssembly/design/issues/1413), wasmsign2 PoC exists |
| **SRI on `<script>`** | N/A for WASM | WASM loaded via fetch, not script tags |

**Practical approach today:** Use `fetch()` with `integrity` parameter + CSP headers.
No browser-native signature verification for WASM modules yet.

---

## Q3: Adding a top-level `tests/` folder with RDF/SPARQL test suites

### Official test suites

All W3C tests live in one repo: **[github.com/w3c/rdf-tests](https://github.com/w3c/rdf-tests)**

| Suite | Path | Manifest format |
|-------|------|----------------|
| RDF 1.1 Turtle | `rdf/rdf11/rdf-turtle/` | Turtle (`manifest.ttl`) |
| RDF 1.1 N-Triples | `rdf/rdf11/rdf-n-triples/` | Turtle |
| RDF 1.1 N-Quads | `rdf/rdf11/rdf-n-quads/` | Turtle |
| RDF 1.1 TriG | `rdf/rdf11/rdf-trig/` | Turtle |
| RDF 1.1 XML | `rdf/rdf11/rdf-xml/` | Turtle |
| RDF 1.1 Semantics | `rdf/rdf11/rdf-mt/` | Turtle |
| SPARQL 1.1 | `sparql/sparql11/` | Turtle (`manifest-all.ttl`) |

Test types: positive/negative syntax, positive/negative evaluation. SPARQL tests use
`qt:query` / `qt:data` / `qt:graphData` vocabulary. Results compared via blank-node isomorphism.

### Proposed structure

```
tests/
├── README.md
├── w3c/                          # git submodule of w3c/rdf-tests
│   └── ...
├── runners/
│   ├── run-js-tests.html         # runs W3C tests against docs/ JS impl
│   ├── run-rust-tests.sh         # runs W3C tests against rdf-wasm
│   └── run-ntriples-tests.js     # start with N-Triples (simplest format)
└── compliance/
    └── earl-report.ttl           # EARL vocabulary compliance results
```

**Recommended starting point:** N-Triples tests — the simplest format, and both
implementations already have `toNTriples()` output. The test suite has positive syntax,
negative syntax, and evaluation tests. The JS runner `rdf-test-suite.js`
(github.com/rubensworks/rdf-test-suite.js) can automate execution and produce EARL reports.

---

## Q4: Persistence (SQLite/PG/binary/HTTP) and F\* formalities

### How existing SPARQL stores persist

| Approach | Examples | Characteristics |
|----------|----------|----------------|
| **SQLite** | Oxigraph (sled→RocksDB), rdflib (SQLAlchemy) | Single-file, embedded, good for small-medium |
| **PostgreSQL** | Virtuoso, Blazegraph (custom), Jena SDB | ACID, scalable, SQL-based indexing (SPO/POS/OSP) |
| **Binary/mmap** | HDT, Jena TDB, Oxigraph (RocksDB) | Compact, fast range scans, memory-mapped |
| **HTTP ranges** | Linked Data Fragments (TPF), LDES | Lazy-load pages of triples via HTTP Range headers |

### How persistence fits with F\* formalities

The key insight: **verify the logic, specify the storage interface, trust the storage engine.**

```
┌──────────────────────────────────────────────────────┐
│  F*-verified layer (trusted)                         │
│  ┌─────────────┐  ┌──────────────┐  ┌─────────────┐ │
│  │ RDF types   │  │ SPARQL       │  │ Serializer/ │ │
│  │ (wf_iri,    │  │ algebra      │  │ Deserializer│ │
│  │  wf_literal,│  │ (verified    │  │ (EverParse  │ │
│  │  triple,    │  │  evaluation) │  │  style)     │ │
│  │  graph)     │  │              │  │             │ │
│  └─────────────┘  └──────────────┘  └─────────────┘ │
│                         │                            │
│  Storage interface (F* spec, not impl)               │
│  ┌──────────────────────────────────────────────────┐│
│  │ val store  : graph → storage → Result storage    ││
│  │ val load   : storage → Result graph              ││
│  │ val roundtrip_correct:                           ││
│  │   ∀ g s. load (store g s) ≡ Ok g                 ││
│  └──────────────────────────────────────────────────┘│
└──────────────────────────────────────────────────────┘
                         │
                    (trust boundary)
                         │
┌──────────────────────────────────────────────────────┐
│  Unverified storage backends                         │
│  SQLite │ PostgreSQL │ RocksDB │ HTTP/Range           │
└──────────────────────────────────────────────────────┘
```

**What can be verified:**

1. **Serialization roundtrips** — F\* can prove `deserialize(serialize(graph)) = graph` for
   formats like N-Triples, Turtle, JSON-LD. The **EverParse** project (F\*-based verified
   parsers) is the model here — it generates verified C/WASM parsers from format specs.

2. **SPARQL algebra evaluation** — the SPARQL algebra (BGP matching, joins, filters, etc.)
   is a pure function `query × graph → result_set`. This is ideal for F\* verification.
   You could prove that your evaluator correctly implements the W3C SPARQL algebra spec.

3. **Index invariants** — if you build SPO/POS/OSP indexes, you can verify that index
   lookups are equivalent to linear scan (correctness) even if you trust the B-tree impl.

**What should NOT be verified (trust the engine):**

- SQLite/PG/RocksDB internals — these are battle-tested, audited systems
- OS-level I/O, mmap, file locking
- Network transport (HTTP, TLS)

**Precedents:**

- **EverParse** — verified parsers for binary formats, used in Windows kernel
- **HACL\*** — verified crypto, extracted to C/WASM
- **Fiat-Crypto** — verified field arithmetic (different prover, same idea)
- **FSCQ** (MIT) — fully verified file system in Coq
- **Verdi** — verified distributed systems framework (Coq)
- **CertiKOS** — verified concurrent OS kernel (Yale, Coq)
- **IronFleet** (Microsoft) — verified distributed systems in Dafny

### Practical persistence roadmap for Factoidal

**Phase 1 — Verified serialization (near-term)**
- Write F\* specs for N-Triples serialize/deserialize
- Prove roundtrip correctness
- Extract to WASM via KaRaMeL (requires Low\* rewrite of relevant parts)

**Phase 2 — Storage abstraction (medium-term)**
- Define F\* interface for `store`/`load`/`query` operations
- Prove that SPARQL BGP evaluation over the interface is correct
- Implement backends (SQLite via `sql.js` WASM, or IndexedDB for browsers)

**Phase 3 — HTTP range / Linked Data Fragments (longer-term)**
- Verified pagination logic (prove completeness: all matching triples are returned)
- Backend serves triple pattern fragments; client reconstructs graph
- SRI hashes on each fragment for integrity

**For the Rust/WASM path specifically:**
- Oxigraph (Rust, SPARQL-compliant, RocksDB backend) is the natural reference
- Could use Aeneas to translate Rust core → F\* for verification
- Or maintain parallel F\* spec + Rust impl with shared test suites
