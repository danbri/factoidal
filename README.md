# Factoidal

A formally verified RDF graph library with F\* specifications, KaRaMeL-extracted C, a Rust/WebAssembly implementation, SPARQL query engine, and an interactive browser demo.

## Overview

Factoidal provides a formally-specified RDF graph library targeting high-trust environments. The F\* specifications are **not documentation** — they are the source for verified C extraction via KaRaMeL.

```
F* spec → verify proofs → KaRaMeL → C (1,710 lines extracted)
F* spec → Rust impl → WASM + JS bindings → Web demo & tests
```

- **Formally verified** — 3,317 lines of F\* with zero `admit()`, 16+ proved lemmas, zero assume val in the RDF module
- **C extraction working** — KaRaMeL extracts verified C from the RDF module (`make extract-c`)
- **W3C compliant** — N-Triples 100%, Turtle 100%, SPARQL 36.5% (159/436) and growing
- **Interactive demo** — Browser-based RDF graph explorer + SPARQL, powered by the real WASM library

## Project Structure

```
factoidal/
├── formal/fstar/
│   ├── RDF.Graph.Executable.fst     # Verified RDF types + graph ops (586 lines, 0 assume val)
│   ├── SPARQL11.Algebra.fst         # Verified SPARQL algebra (2731 lines, 7 assume val)
│   ├── c-output/                    # KaRaMeL-extracted C (1710 lines)
│   └── Makefile                     # verify + extract-c targets
├── rdf-wasm/
│   ├── src/
│   │   ├── rdf.rs             # Core RDF types (mirrors F* spec)
│   │   ├── ntriples.rs        # N-Triples parser (W3C RDF 1.1)
│   │   ├── turtle.rs          # Turtle parser (W3C RDF 1.1)
│   │   ├── sparql.rs          # SPARQL SELECT engine
│   │   ├── wasm_api.rs        # wasm-bindgen JS bindings
│   │   └── lib.rs             # Module declarations
│   ├── tests/                 # W3C test suites + unit tests (172 passing)
│   └── build.sh               # WASM build script
├── tests/w3c/                 # Git submodule: github.com/w3c/rdf-tests
└── docs/
    ├── pkg/                   # WASM build artifacts (committed)
    ├── index.html             # Interactive RDF graph explorer + SPARQL
    └── designissues/          # Architecture and design documents
```

## Building

```bash
# Run all Rust tests (172 passing)
cd rdf-wasm && cargo test

# Verify F* specifications
eval $(opam env --switch=fstar) && cd formal/fstar && make verify

# Extract verified C from RDF module
eval $(opam env --switch=fstar) && cd formal/fstar && make extract-c

# Build WASM (requires wasm-pack)
cd rdf-wasm && ./build.sh

# Serve demo locally
cd docs && python3 -m http.server 8080
```

## Usage

```javascript
import init, { JsRdfGraph } from './pkg/rdf_wasm.js';

await init();
const graph = new JsRdfGraph();

graph.addTriple("http://example.org/alice", "http://xmlns.com/foaf/0.1/name", "Alice");
graph.addTripleLang("http://example.org/alice", "http://xmlns.com/foaf/0.1/name", "Alicia", "es");
graph.addTriple("http://example.org/alice", "http://xmlns.com/foaf/0.1/knows", "http://example.org/bob");

console.log(graph.toNTriples());
console.log(graph.findBySubject("http://example.org/alice"));
```

### SPARQL

```javascript
const result = JSON.parse(graph.sparqlQuery(`
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?person ?name
  WHERE {
    ?person foaf:name ?name .
    FILTER (LANG(?name) = "es")
  }
`));
// { variables: ["person", "name"], rows: [["<http://example.org/alice>", "\"Alicia\"@es"]] }
```

Supported SPARQL features: `SELECT`, `PREFIX`, `BASE`, `FILTER`, `OPTIONAL`, `UNION`, `MINUS`, `BIND`, `VALUES`, `EXISTS`/`NOT EXISTS`, `DISTINCT`, `REDUCED`, `ORDER BY`, `LIMIT`, `OFFSET`, and 30+ built-in functions.

## Verification Status

| Component | F\* Lines | assume val | Proved Lemmas | C Extraction |
|-----------|----------|------------|---------------|--------------|
| RDF Core  | 586      | 0          | 9             | ✅ 1,710 lines |
| SPARQL    | 2,731    | 7 (regex + crypto) | 16+    | ❌ blocked (noeq) |

The F\* specs use zero `admit()` calls — all proofs are machine-checked. See [CLAUDE.md](CLAUDE.md) for the full verification roadmap.

## Key Design Decisions

- **F\* specs are primary** — they are the source for verified C extraction, not documentation
- **Spec + Impl pattern** — high-level specs for readability/proofs, Low\* implementations for C extraction
- **IRI well-formedness** — IRIs must be non-empty and contain `:`, enforced at construction time
- **Literal constraints** — The language-tag ↔ `rdf:langString` biconditional is enforced by `Literal::new()`
- **No JS reimplementation** — The web demo imports the WASM binary directly; the same Rust code runs everywhere

## License

Apache License 2.0 — see [LICENSE](LICENSE) for details.
