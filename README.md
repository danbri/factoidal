# Factoidal

An RDF Core 1.1 graph library with a formal F\* specification, a Rust/WebAssembly implementation, and interactive JavaScript demos.

## Overview

Factoidal provides a formally-specified RDF graph library that compiles to WebAssembly for use in browsers and Node.js. The project spans three layers:

- **Formal specification** — An F\* model defining RDF terms, triples, and graphs with refinement types for well-formedness constraints (e.g. IRI validation, language-tag/datatype biconditional)
- **Rust/WASM library** — A faithful implementation of the spec using `wasm-bindgen`, with JavaScript bindings for creating and querying RDF graphs
- **Interactive demos** — A browser-based RDF graph explorer and a comprehensive test suite, both deployable via GitHub Pages

## Project Structure

```
factoidal/
├── formal/fstar/
│   └── rdfcore11.fstar.txt    # F* formal specification
├── rdf-wasm/
│   ├── src/
│   │   ├── rdf.rs             # Core RDF types and graph logic
│   │   └── wasm_api.rs        # JavaScript/WASM bindings
│   ├── demo/
│   │   ├── demo.js            # Usage examples (Node.js + browser)
│   │   └── index.html         # Browser demo
│   ├── tests/
│   │   └── rdf_tests.rs       # Rust unit tests
│   └── build.sh               # WASM build script
└── docs/
    ├── index.html             # Interactive RDF graph explorer
    ├── tests.html             # JS test suite (31+ tests)
    └── GROUNDING_ANALYSIS.md  # Formal spec ↔ implementation mapping
```

## Building

Requires [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/):

```bash
cd rdf-wasm
./build.sh
```

To run the demo locally:

```bash
cd rdf-wasm/demo
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

## Key Design Decisions

- **IRI well-formedness** — IRIs must be non-empty and contain a `:` character, enforced at construction time
- **Literal constraints** — The language-tag ↔ `rdf:langString` biconditional from the RDF spec is enforced at runtime
- **Set semantics** — Duplicate triples are rejected on insert (extending the F\* list-based model)
- **Subjects exclude literals** — The type system restricts triple subjects to IRIs and blank nodes

## License

Apache License 2.0 — see [LICENSE](LICENSE) for details.
