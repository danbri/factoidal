# factoidal

Formally-verified SPARQL 1.1 + RDF 1.1, for Node and the browser.

The semantics live in [F*](https://www.fstar-lang.org/) and are
compiled via OCaml and js_of_ocaml / wasm_of_ocaml into the engine
bundles shipped in this package. There is no hand-written SPARQL
evaluator — the JavaScript you run here was extracted from the same
`.fst` specifications that verify under Z3.

Verification status qualifier: parser and algebra spec verified in
F*; on-disk backend has unverified OCaml-side optimization layers
being migrated back to F* (see fstar-purity-unwind.md).

> Status: **0.1.0-alpha.0, unpublished.** Scaffolding committed to the
> repo so the API surface can be iterated before a real release.
> Nothing has been published to the npm registry yet. See
> [CHANGELOG.md](CHANGELOG.md).

## Why this engine

- **Full SPARQL 1.1 client-side.** Query (and update, once the
  npm-entry bundle ships) run entirely in your process — no server,
  no endpoint.
- **RDFC-1.0 canonicalization built in.** `canonicalize()` gives you
  standard canonical N-Quads (rdflib and N3.js need a separate library
  for this).
- **RDFS / OWL-RL entailment as a query option** (`entail: 'RDFS'`).
- **The verified core**, subject to the qualifier stated above.

## Install

```bash
npm install factoidal
```

## Quickstart

```js
const { parse, query, serialize, canonicalize, dataFactory } = require('factoidal');
// ESM: import { parse, query } from 'factoidal';

const ds = await parse(`
  @prefix ex:   <http://example.org/> .
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  ex:alice foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob   foaf:name "Bob" .
`);                                       // -> Dataset (RDF/JS quads)

const rows = await query(ds, `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name }
`);                                       // -> Array<Map<string, Term>>
for (const row of rows) console.log(row.get('name').value);

await query(ds, 'ASK { ?s ?p ?o }');      // -> true
await serialize(ds);                      // -> sorted N-Quads string
await canonicalize(ds);                   // -> RDFC-1.0 canonical N-Quads
```

For the wasm engine (Node >= 22) with the same API:

```js
const factoidal = require('factoidal/wasm');
```

## API

| Function | Signature | Returns |
| --- | --- | --- |
| `parse` | `parse(text, {format?, baseIRI?})` | `Promise<Dataset>` |
| `query` | `query(data, sparql, {entail?, format?})` | `Promise<Bindings[]>` (SELECT), `Promise<boolean>` (ASK), `Promise<Dataset>` (CONSTRUCT) |
| `update` | `update(data, sparqlUpdate)` | `Promise<Dataset>` |
| `serialize` | `serialize(data, {format?: 'nquads'\|'ntriples'})` | `Promise<string>` |
| `canonicalize` | `canonicalize(data)` | `Promise<string>` (RDFC-1.0 canonical N-Quads) |
| `capabilities` | `capabilities()` | `Promise<{entry, construct, update, canonicalize}>` |
| `dataFactory` | RDF/JS DataFactory | terms with `.equals()` |
| `Dataset` | RDF/JS DatasetCore | `size/add/delete/has/match`, iterable, `toNQuads()` |
| `queryRaw` | `queryRaw(text, sparql, {dataFormat?, entail?, output?})` | `Promise<SparqlResultsJson\|string>` (legacy surface) |

`data` is a `Dataset`, a document string (`format` defaults to
`'turtle'`), a `{text, format}` object, or an array of those — each
array element is loaded as its own document, so blank-node labels
never join across documents. Input formats: Turtle, N-Triples,
N-Quads, TriG, RDF/XML. Bindings are `Map`s from variable name to
RDF/JS term (`NamedNode` / `BlankNode` / `Literal` with
`language` / `datatype`).

Full types: [index.d.ts](index.d.ts). RDF/JS data model + N-Quads
converters are importable on their own via `require('factoidal/rdfjs')`.

### Interop

The terms and `Dataset` follow the RDF/JS data-model and DatasetCore
specs, so quads flow into N3.js, Comunica, rdf-ext, graphy, etc.
Convert any RDF/JS quad stream into factoidal with
`new Dataset(quads)` and back out by iterating.

### CONSTRUCT / UPDATE / canonicalize availability

`capabilities()` reports what the bundled engine artifacts support.
With only the single-shot CLI bundle (`factoidal.js`), CONSTRUCT,
UPDATE and (on older bundles) `canonicalize()` reject with an Error
mentioning "pending npm-entry build"; the
`factoidal-npm-entry.js` bundle (see
[bin/npm-entry/README.md](https://github.com/danbri/factoidal/blob/main/bin/npm-entry/README.md))
enables all of them.

## Browser

The legacy SRJ-shaped `query()` is available as an ES module for
browsers via `factoidal/browser` (js_of_ocaml) and
`factoidal/browser-wasm` (wasm_of_ocaml, Chrome/Edge >= 119). The
typed RDF/JS API currently targets Node; browser support for it
arrives with the npm-entry bundle.

## Limits (v0.1, stated up front)

- **Memory:** the in-memory dataset costs roughly 1 KB per triple
  (measured ~1.2 KB/quad). A 1M-triple load wants ~1.2 GB.
- **No streaming parse:** documents are parsed whole; there is no
  StreamRDF-style incremental interface yet.
- **Bundle size:** the engine bundle is hundreds of KB of generated
  JavaScript (multi-MB unminified in some configurations).
- **Lenient Turtle parsing:** syntax errors in Turtle input currently
  yield an empty/partial dataset rather than a thrown error (error
  reporting is queued upstream).
- **No JSON-LD yet** (an F*-first parser is on the roadmap), and
  DESCRIBE is not implemented.
- **One call at a time:** the CLI-bundle path swaps process globals
  during a call and is not reentrant; concurrent calls in one process
  are serialized by await-discipline, not by the library.

## Engine selection

- `require('factoidal')` — js_of_ocaml bundle, works on Node >= 20.
- `require('factoidal/wasm')` — wasm_of_ocaml bundle, Node >= 22
  (WasmGC). `wasmAvailable()` reports whether the assets are present.
- Env overrides for development: `FACTOIDAL_JS_BUNDLE`,
  `FACTOIDAL_WASM_BUNDLE`, `FACTOIDAL_NPM_ENTRY`,
  `FACTOIDAL_NPM_ENTRY_WASM` (absolute paths to alternate bundles).

## Tests

```bash
npm test              # node --test test/*.test.js
npm run test:smoke    # legacy smoke tests (raw SRJ surface + wasm)
```

Tests that need the npm-entry bundle skip with reason
"pending npm-entry build" until it is built.

## License

Apache-2.0. See [LICENSE](LICENSE).
