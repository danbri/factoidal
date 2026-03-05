# Factoidal

An RDF Core 1.1 graph library with a formal F\* specification, a Rust/WebAssembly implementation, SPARQL query support, and an interactive browser demo.

## Overview

Factoidal provides a formally-specified RDF graph library that compiles to WebAssembly for use in browsers and Node.js. The web demo uses the **real WASM library** — no reimplementation, no divergence from the verified types.

```
F* spec → Rust library → WASM + JS bindings → Web demo & tests
```

- **Formal specification** — An F\* model defining RDF terms, triples, and graphs with refinement types for well-formedness constraints
- **Rust/WASM library** — A faithful implementation of the spec with JavaScript bindings via `wasm-bindgen`, including a SPARQL SELECT engine
- **Interactive demo** — A browser-based RDF graph explorer with SPARQL query panel, powered by the WASM library, deployable via GitHub Pages

## Project Structure

```
factoidal/
├── formal/fstar/
│   └── rdfcore11.fstar.txt    # F* formal specification
├── rdf-wasm/
│   ├── src/
│   │   ├── rdf.rs             # Core RDF types and graph logic
│   │   ├── sparql.rs          # SPARQL SELECT engine
│   │   └── wasm_api.rs        # JavaScript/WASM bindings
│   ├── demo/
│   │   ├── demo.js            # Usage examples (Node.js + browser)
│   │   └── index.html         # Browser demo
│   ├── tests/
│   │   └── rdf_tests.rs       # Rust unit tests
│   └── build.sh               # WASM build script
└── docs/
    ├── pkg/                   # WASM build artifacts (committed)
    ├── index.html             # Interactive RDF graph explorer + SPARQL
    ├── tests.html             # WASM integration tests
    └── GROUNDING_ANALYSIS.md  # Formal spec ↔ implementation mapping
```

## Building

Requires [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/):

```bash
cd rdf-wasm
./build.sh
cp pkg/rdf_wasm_bg.wasm pkg/rdf_wasm.js pkg/rdf_wasm.d.ts pkg/rdf_wasm_bg.wasm.d.ts ../docs/pkg/
```

To run the demo locally:

```bash
cd docs
python3 -m http.server 8080
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

Supported SPARQL features: `SELECT` (with `*` or named variables), `PREFIX`, `FILTER` (comparison operators, `STR`, `LANG`, `DATATYPE`, `BOUND`, `REGEX`, `CONTAINS`, `STRSTARTS`, `STRENDS`, `ISLITERAL`, `ISIRI`, `ISBLANK`, `&&`, `||`), `OPTIONAL`, `DISTINCT`, `ORDER BY`, `LIMIT`, `OFFSET`.

## Key Design Decisions

- **IRI well-formedness** — IRIs must be non-empty and contain a `:` character, enforced at construction time in Rust
- **Literal constraints** — The language-tag ↔ `rdf:langString` biconditional from the RDF spec is enforced by `Literal::new()`
- **Set semantics** — Duplicate triples are rejected on insert (extending the F\* list-based model)
- **Subjects exclude literals** — Rust's `enum Subject { Iri, BNode }` makes this a compile-time guarantee, not a runtime check
- **No JS reimplementation** — The web demo imports the WASM binary directly; the same Rust code runs everywhere

## License

Apache License 2.0 — see [LICENSE](LICENSE) for details.
