# Grounding Analysis: Web Demos vs. Formal Definitions

## Overview

The web demos in `docs/` use the **actual Rust/WASM library** (`rdf-wasm`), not
a reimplementation. The library is compiled from the same Rust code that
faithfully implements the F\* formal specification in
`formal/fstar/rdfcore11.fstar.txt`. This eliminates the risk of divergence
between the demo and the verified types.

## Architecture

```
F* spec (formal/fstar/rdfcore11.fstar.txt)
    ↓ manual faithful translation
Rust library (rdf-wasm/src/rdf.rs)
    ↓ wasm-bindgen
WASM + JS bindings (docs/pkg/)
    ↓ imported by
Web demos (docs/index.html, docs/tests.html)
```

## Type-by-Type Mapping (F\* → Rust → WASM)

| F\* Formal Definition | Rust Implementation | Exposed via WASM? |
|---|---|---|
| `bnode_id = string` | `BNode(String)` | Yes — `addTriple("_:id", ...)` |
| `wf_iri` (non-empty, contains `:`) | `Iri::new()` validates at construction | Yes — errors propagate to JS |
| `rdf_lang_string` constant | `RDF_LANG_STRING` constant (same URI) | Yes |
| `literal {lexical_form, datatype: wf_iri, lang_tag: option string}` | `Literal { lexical_form, datatype: Iri, lang_tag: Option<String> }` | Yes — `addTripleLang`, `addTripleTyped` |
| `literal_wf` biconditional (langTag ↔ rdf:langString) | `Literal::new()` enforces both directions | Yes — errors propagate to JS |
| `rdf_term = T_IRI \| T_BNode \| T_Literal` | `enum RdfTerm { Iri, BNode, Literal }` | Yes |
| `subject = S_IRI \| S_BNode` (no Literal) | `enum Subject { Iri, BNode }` — type-level exclusion | Yes |
| `triple = {s: subject, p: wf_iri, o: rdf_term}` | `Triple { s: Subject, p: Iri, o: RdfTerm }` | Yes |
| `rdf_graph = list triple` | `RdfGraph { triples: Vec<Triple> }` | Yes — `JsRdfGraph` |
| `graph_bnodes` (collect from s/o positions) | `RdfGraph::bnodes()` | Yes — `bnodes()` |

## Key Advantages Over Previous JS Reimplementation

1. **No code duplication** — the demo and tests exercise the same Rust code
2. **Type-level subject restriction** — Rust's `enum Subject` makes it impossible
   to construct a triple with a Literal subject, unlike JS where it was only
   enforced at the parsing layer
3. **Predicate type safety** — `p: Iri` is enforced by the Rust type system, not
   just by convention
4. **Single source of truth** — any fix or change to `rdf.rs` automatically
   applies to the web demo

## SPARQL Support

The WASM library includes a SPARQL SELECT engine (`sparql.rs`) supporting:

- `SELECT` with explicit variables or `*`
- `PREFIX` declarations
- Basic Graph Patterns (triple patterns with `?variables`)
- `FILTER` with: `=`, `!=`, `<`, `>`, `<=`, `>=`, `STR()`, `LANG()`,
  `DATATYPE()`, `BOUND()`, `REGEX()`, `CONTAINS()`, `STRSTARTS()`,
  `STRENDS()`, `ISLITERAL()`, `ISIRI()`/`ISURI()`, `ISBLANK()`,
  boolean `&&` and `||`
- `OPTIONAL` patterns
- `DISTINCT`
- `ORDER BY` (ASC/DESC)
- `LIMIT` / `OFFSET`

This runs entirely in WASM — no server-side query processing.

## Test Coverage

`tests.html` tests the WASM library directly via `JsRdfGraph`:

- IRI validation (4 tests)
- BNode support (3 tests)
- Literal well-formedness (3 tests)
- Plain literals (2 tests)
- Graph add/size (1 test)
- Graph deduplication (1 test)
- Graph removeByIndex (3 tests)
- Graph findBySubject (1 test)
- Graph findByPredicate (1 test)
- Graph N-Triples output (3 tests)
- Graph empty state (3 tests)
- Graph JSON output (2 tests)
- Graph triplesJSON (2 tests)
- SPARQL SELECT \* (2 tests)
- SPARQL PREFIX + variables (2 tests)
- SPARQL FILTER (1 test)
- SPARQL DISTINCT (1 test)
- SPARQL LIMIT/OFFSET (2 tests)
- SPARQL OPTIONAL (2 tests)
- SPARQL pattern join (1 test)
- SPARQL error handling (1 test)

## Verdict

The web demos are **directly grounded** in the formal definitions via the Rust
implementation. There is no reimplementation or translation layer that could
introduce divergence. The WASM binary *is* the verified code.
