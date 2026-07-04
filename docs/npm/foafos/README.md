# @danbri/foafos — DRAFT

> **DRAFT documentation.** `@danbri/foafos` is a placeholder name —
> not registered, not published; real package setup follows as things
> mature (`package.json` is marked `private` to prevent accidental
> publishing). API surface is 0.1.0-alpha and may change. See
> [CHANGELOG.md](CHANGELOG.md).

A formally verified RDF/SPARQL engine for JavaScript and WebAssembly.
The semantics live in [F\*](https://www.fstar-lang.org/) and are
compiled via OCaml and js_of_ocaml / wasm_of_ocaml into the engine
bundles shipped here. There is no hand-written SPARQL evaluator — the
JavaScript you run was extracted from the same `.fst` specifications
that verify under Z3 and pass the W3C suites.

Verification status qualifier: parser and algebra spec verified in
F\*; the on-disk backend has unverified OCaml-side optimization layers
being migrated back to F\* (the npm build does not include the
on-disk backend).

## Why this instead of N3.js / rdflib.js / Comunica?

- **Full SPARQL 1.1 client-side** — query and update evaluated in
  your process by conformance-tested code (631 of 631 W3C SPARQL
  tests, 1031 of 1031 RDF parsing tests on the native build of the
  same source); no server, no endpoint.
- **RDFC-1.0 canonicalization built in**: `canonicalize()` yields
  standard canonical N-Quads (stable under blank-node renaming — for
  content addressing, dataset diffing, cache keys) without a separate
  library.
- **RDFS / OWL-RL entailment** as a query option (`entail: "RDFS"`).
- **RDF/JS data model** (`DataFactory`, terms with `.equals`,
  `DatasetCore`) so it composes with the existing ecosystem.
- Provenance: every release corresponds to a gates-green commit of
  [danbri/factoidal](https://github.com/danbri/factoidal).

## Install (placeholder — not yet published)

```bash
npm install @danbri/foafos
```

## Quickstart

```js
import { parse, query, serialize, canonicalize, dataFactory }
  from "@danbri/foafos";

// Parse any supported syntax into an RDF/JS DatasetCore.
const ds = parse(`
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  _:a foaf:name "Alice" ; foaf:knows _:b .
  _:b foaf:name "Bob" .
`, { format: "turtle" });

// SELECT — bindings are Map<variableName, RDF/JS Term>.
const rows = query(ds, `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name
`);
for (const b of rows) console.log(b.get("name").value); // Alice, Bob

// ASK — plain boolean.
const yes = query(ds, "ASK { ?s ?p ?o }");   // true

// Canonical N-Quads (RDFC-1.0): identical output for isomorphic
// inputs regardless of blank-node labels.
const c14n = canonicalize(ds);

// Round-trip.
const nq = serialize(ds, { format: "nquads" });
```

CommonJS: `const foafos = require("@danbri/foafos")`.

### WebAssembly entry

```js
import { parse, query } from "@danbri/foafos/wasm";
// Same API over the wasm_of_ocaml bundle; needs a Wasm-GC engine
// (Chrome >= 119, Node >= 22). The unit suite asserts byte-parity
// between the JS and Wasm entries on parse/SELECT/ASK.
```

### Load in the browser without npm

You don't need `npm install` (or a bundler) to run this in a browser.
Two options, in preference order:

1. **This site's own mirror (recommended, same-origin, no build step
   for you).** Every push regenerates `docs/npm/foafos/` from this
   package (`formal/fstar/build-ocaml.sh npm`'s Pages-mirror step), so
   it's always in sync with what's published here:

   ```html
   <script type="module">
     import { query } from 'https://danbri.github.io/factoidal/npm/foafos/browser.js';
     const r = await query(dataTtl, 'SELECT * WHERE { ?s ?p ?o }');
     console.log(r.results.bindings);
   </script>
   ```

   See [`demo-jsonld-playground.html`](../../docs/fstar-extracted/demo-jsonld-playground.html)
   for a working page built exactly this way (loads `browser.js` from
   `../npm/foafos/browser.js`, a relative same-origin path).

2. **jsDelivr's GitHub proxy** (serves the correct
   `text/javascript` MIME type; no Pages dependency, works from any
   branch/tag):

   ```html
   <script type="module">
     import { query } from 'https://cdn.jsdelivr.net/gh/danbri/factoidal@claude/main/npm/factoidal/browser.js';
   </script>
   ```

**Do not** link `browser.js` (or `factoidal.js`) via
`raw.githubusercontent.com`. Raw GitHub serves every file as
`text/plain`, and browsers refuse to execute a `text/plain` response
as an ES module (`<script type="module">` fails with a MIME-type
error) — this bites people who copy a "raw" link expecting it to just
work. Use the Pages mirror or jsDelivr above instead.

`browser.js` also exports `toRdf(text, options)` (parse to sorted
N-Quads — `--dump-nq` under the hood) and `canonicalize(text,
options)` (RDFC-1.0 — `--canonicalize`) alongside `query()`; both
default `options.format` to `'jsonld'` since that's the playground's
use case, but accept the same formats as `query()`'s `dataFormat`.

### RDF/JS interop

```js
import { dataFactory } from "@danbri/foafos";
const { namedNode, literal, quad, blankNode } = dataFactory;
const q = quad(blankNode("x"),
               namedNode("http://xmlns.com/foaf/0.1/name"),
               literal("Alice", "en"));
// Terms implement termType/value/language/datatype/.equals per the
// RDF/JS data-model spec; Dataset implements DatasetCore
// (add/delete/has/match/size/iteration).
```

## API (draft)

| Function | Signature (informal) | Notes |
|---|---|---|
| `parse` | `(text, {format?, baseIRI?}) => Dataset` | formats: `turtle`, `ntriples`, `nquads`, `trig`, `rdfxml`, `jsonld`\* — auto-detected where possible. Each call is one document: blank-node labels are scoped per RDF 1.1 |
| `query` | `(Dataset \| string, sparql, {entail?}) => Bindings[] \| boolean \| Dataset` | SELECT → array of `Map<var, Term>`; ASK → boolean; CONSTRUCT → Dataset\*\*; `entail: "RDFS" \| "OWL-RL"` |
| `update` | `(Dataset, sparqlUpdate) => Dataset` | \*\* in-memory; no persistence |
| `serialize` | `(Dataset, {format}) => string` | `nquads`, `ntriples` (sorted); prettier Turtle output is staged work |
| `canonicalize` | `(Dataset \| string) => string` | RDFC-1.0 canonical N-Quads\*\* |
| `graphs` | `(Dataset) => Array<[iri, Dataset]>` | enumerate named graphs (default graph excluded); pure enumeration, no engine round-trip |
| `canonicalHash` | `(Dataset) => string` | RDFC-1.0 canonical hash of one graph\*\*; graph-scoped sibling of `canonicalize` — typically called with one entry of `graphs()`'s output |
| `queryRaw` | `(input, sparql) => string` | SPARQL-Results-JSON string, for callers that want the wire form |
| `capabilities` | `() => {construct, update, canonicalize, graphs, canonicalHash, ...}` | runtime feature probe |
| `dataFactory` | RDF/JS DataFactory | |
| `Dataset` | RDF/JS DatasetCore | returned by `parse`; accepted everywhere |

\* JSON-LD expanded form lands with the current engine build; full
JSON-LD 1.1 (contexts, remote `@context` via a pluggable
`documentLoader`) is staged, tracked against the vendored W3C
json-ld-api suite.
\*\* CONSTRUCT, UPDATE, `canonicalize`, and `canonicalHash` are probed
via `capabilities()`: they activate automatically when the dedicated
npm-entry engine bundle is present, and the package reports their
absence honestly against older bundles instead of guessing.
`canonicalHash` rides the same engine support as `canonicalize` (it
computes `canonicalize()` over one graph's triples); `graphs` is pure
JS enumeration and is always available.

## Limits (deliberate, documented)

- **In-memory only.** ~1.2 KB RAM per quad (measured); 1M quads ≈
  1.2 GB. No streaming parse yet — inputs are whole strings.
- Lenient Turtle parsing: `parse()` cannot yet reject syntax errors
  (bad input can yield an empty dataset).
- No persistence in the npm build; the on-disk store (COTTAS) is
  native-only today.
- Bundle sizes (measured 2026-07-04): JS engine 554 KB, npm entry
  461 KB, Wasm 43 KB loader + 1.3 MB assets. The Wasm entry trades
  startup cost for throughput.

## Testing

`npm test` — unit suite covering the parse/query/serialize surface,
the RDF/JS contract, canonicalization stability under blank-node
renaming, and JS↔Wasm byte-parity. The engine underneath is gated on
every landing by the full W3C suites, a cross-backend parity harness,
and comparison probes against Apache Jena ARQ — live scores with
dates and commit links at
[danbri.github.io/factoidal/test-results](https://danbri.github.io/factoidal/test-results/).

## Provenance & license

Built from [danbri/factoidal](https://github.com/danbri/factoidal)
(Apache-2.0). This package's JavaScript is a thin consumer layer (API
shaping + RDF/JS conversion) containing no RDF/SPARQL semantics of
its own — the semantics are F\*-extracted.
