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

For multi-file, multi-named-graph datasets (several documents, each
loaded into its own named graph or the default graph) and a choice of
extraction target, use `queryDataset(files, queryString, options)`:

```js
import { queryDataset } from 'https://danbri.github.io/factoidal/npm/foafos/browser.js';

const r = await queryDataset(
  [
    { content: defaultGraphTtl },
    { content: peopleTtl, graph: 'urn:x:people' },
  ],
  'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }',
  { entail: 'RDFS', engine: 'js' }   // or engine: 'wasm'
);
```

On `engine: 'wasm'` it merges the named graphs into one TriG document
(wasm_of_ocaml's `query()` only takes a single data string) via
`browser-wasm.js`, loaded on demand. Both `query()` and `queryDataset()`
attach a non-enumerable `engineMs` (bundle-eval wall-clock time) to the
returned results object — invisible to `JSON.stringify()`/`Object.keys()`
so it never perturbs a diff against a W3C `.srx`-derived fixture, but
readable as `result.engineMs` for timing/observability UIs. This is
what `docs/fstar-extracted/factoidal-sparql-client.js`'s web component
is built on, rather than duplicating the engine-invocation logic itself.

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

## Functional API (fn)

`factoidal/fn` is a strictly functional variant of the API above:
every extracted engine operation is already a value-to-value
function — `FnDataset` makes the JS surface match that instead of
papering over it with RDF/JS's mutable `add`/`delete`. Frozen
snapshots, free functions instead of methods (so they compose), and
RDFC-1.0 canonical hashes as a first-class, memoized identity — the
piece that makes dataflow-style recompute-skipping possible. Full
design rationale (cost model, backend/streaming extension points):
[`docs/designissues/2026-07-05-functional-dataset-api.md`](../../docs/designissues/2026-07-05-functional-dataset-api.md).

```js
const { parse, filter, hash, cell, derive } = require('@danbri/foafos/fn');

const ds = await parse(`
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  _:a foaf:name "Alice" ; a foaf:Person .
  _:b foaf:name "Bob".
`);

// Every op returns a new FnDataset; ds is never touched.
const people = filter(ds, (q) => q.predicate.value.endsWith('/type'));

// Dataflow: a derive() node recomputes only when its input's content
// hash actually changes -- not when a new (but equal-content)
// FnDataset object is set into the cell.
const source = cell(ds);
const derived = derive((d) => filter(d, (q) => q.predicate.value.endsWith('name')), source);
await derived.get();          // computes
source.set(await parse(sameTextAsBefore));
await derived.get();          // memoized hit -- same content, new object

await hash(ds);                // sha256 hex of RDFC-1.0 canonical N-Quads
```

`fromDataset(dataset)` / `toDataset(fnDataset)` convert to and from
the mutable RDF/JS `Dataset` above, so the two styles compose freely.
`union`/`difference`/`filter`/`mapQuads` give set algebra without
methods; `query`/`entail`/`canonicalize`/`graphs` mirror the plain
API's capability gating (`capabilities()`) exactly. `validate`/`shex`/
`fromMapping`/`fromCsvw`/`rif` wrap the SHACL/ShEx/RML/CSVW/RIF
surface below the same way — FnDataset in, FnDataset (or a plain
verdict) out:

```js
const { parse, validate, shex, fromMapping, fromCsvw, rif } = require('@danbri/foafos/fn');

const data = await parse(personTtl);
const shapes = await parse(shapesTtl);
const { conforms, report } = await validate(data, shapes); // SHACL

const ok = await shex(data, shexSchemaJson, 'http://example.org/alice'); // true|false|null

const mapped = await fromMapping(await parse(rmlMappingTtl), csvOrJsonText, 'csv'); // RML

const tabular = await fromCsvw(csvText, csvwMetadataJson, { mode: 'minimal' }); // CSVW csv2rdf

const saturated = await rif(data, rifRulesXml); // RIF Core forward chaining
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
| `shaclValidate` | `(data, shapes) => {conforms, report: Dataset}` | \*\* SHACL Core validation; `report` is the `sh:ValidationReport` graph |
| `shexValidate` | `(data, schemaJson, focus, shape?) => boolean \| null` | \*\* ShEx (Shape Expressions) validation of one focus node; `null` = outside this engine's decidable ShEx fragment, never a guessed answer |
| `owlClosure` | `(data, mode) => Dataset` | \*\* `mode: "RDFS" \| "OWL-RL"`; materializes the entailment closure (input + derived triples), default graph only |
| `rmlMap` | `(mapping, sourceData, sourceKind) => Dataset` | \*\* evaluates an RML mapping graph against one logical source (`sourceKind: "json" \| "csv"`); every triples map reads the SAME source — cross-source joins are out of scope for this entry point |
| `csvwToRdf` | `(csvText, metadataJson?, {mode?, base?, url?}) => Dataset` | \*\* CSVW csv2rdf conversion; metadata omitted = schema inferred from the CSV header row; `mode: "standard" \| "minimal"` (default standard); every table in a multi-table group reads the SAME csvText |
| `jsonldToRdf` | `(jsonldText, {base?, rdfDirection?, expandContext?, processingMode?}) => Dataset` | \*\* JSON-LD parsing with options `parse()` has no room for; plain `parse(text, {format:'jsonld'})` also works for the common case |
| `rifEval` | `(data, rifRulesXml) => Dataset` | \*\* RIF Core forward-chaining saturation (materializes input + derived triples); accepts real vendored RIF-XML (`<!DOCTYPE>` + `&rif;`/`&xs;`/`&rdf;` entities) unmodified |
| `queryRaw` | `(input, sparql) => string` | SPARQL-Results-JSON string, for callers that want the wire form |
| `capabilities` | `() => {construct, update, canonicalize, graphs, canonicalHash, shacl, shex, owlClosure, rml, csvw, jsonld, rif, ...}` | runtime feature probe |
| `dataFactory` | RDF/JS DataFactory | |
| `Dataset` | RDF/JS DatasetCore | returned by `parse`; accepted everywhere |

\* JSON-LD parsing (expanded form, inline `@context`, `@base`
resolution, `@reverse`, container maps) works through both `parse()`
and `jsonldToRdf()` when the npm-entry bundle is loaded. Remote
`@context` URLs need a `documentLoader`, which this package's entries
don't register (an honest failure, not a silent wrong answer) —
tracked against the vendored W3C json-ld-api suite.
\*\* CONSTRUCT, UPDATE, `canonicalize`, `canonicalHash`,
`shaclValidate`, `shexValidate`, `owlClosure`, `rmlMap`, `csvwToRdf`,
`jsonldToRdf`, and `rifEval` are probed via `capabilities()`: they
activate automatically when the dedicated npm-entry engine bundle is
present, and the package reports their absence honestly against
older bundles instead of guessing.
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
