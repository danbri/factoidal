# @factoidal/core

> Release 0.3.0. The API surface is early and may
> change before 1.0. This package was previously developed in-tree
> under the placeholder names `factoidal` and `@danbri/foafos`; it was
> never published under those names. See [CHANGELOG.md](CHANGELOG.md).

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

## Install

```bash
npm install @factoidal/core
```

## Quickstart

The API is **async throughout** — every engine call returns a Promise,
so `await` each one (the engine bundle loads lazily on first use).

```js
import { parse, query, serialize, canonicalize, dataFactory }
  from "@factoidal/core";

// Parse any supported syntax into an RDF/JS DatasetCore.
// If your data contains RELATIVE IRIs, pass { baseIRI: ... } —
// see the note below this example.
const ds = await parse(`
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  _:a foaf:name "Alice" ; foaf:knows _:b .
  _:b foaf:name "Bob" .
`, { format: "turtle" });

// SELECT — bindings are Map<variableName, RDF/JS Term>.
const rows = await query(ds, `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name
`);
for (const b of rows) console.log(b.get("name").value); // Alice, Bob

// ASK — plain boolean.
const yes = await query(ds, "ASK { ?s ?p ?o }");   // true

// Canonical N-Quads (RDFC-1.0): identical output for isomorphic
// inputs regardless of blank-node labels.
const c14n = await canonicalize(ds);

// Round-trip.
const nq = await serialize(ds, { format: "nquads" });
```

> ⚠️ **Pass `baseIRI` when your input uses relative IRIs.** In the
> current build, statements whose relative IRIs cannot be resolved are
> **dropped without an error**, so a document can parse to fewer
> triples than it contains (`{ baseIRI: "https://example.org/doc" }`
> fixes it). A count check after parsing is a cheap guard. Surfacing
> these drops as a throw or a warnings channel is tracked in the
> repository issues.

CommonJS: `const factoidal = require("@factoidal/core")`.

### WebAssembly entry

```js
import { parse, query } from "factoidal/wasm";
// Same API over the wasm_of_ocaml bundle; needs a Wasm-GC engine
// (Chrome >= 119, Node >= 22). The unit suite asserts byte-parity
// between the JS and Wasm entries on parse/SELECT/ASK.
```

### Load in the browser without npm

You don't need `npm install` (or a bundler) to run this in a browser.
Two options, in preference order:

1. **This site's own mirror (recommended, same-origin, no build step
   for you).** Every push regenerates `docs/npm/factoidal/` from this
   package (`formal/fstar/build-ocaml.sh npm`'s Pages-mirror step), so
   it's always in sync with what's published here:

   ```html
   <script type="module">
     import { query } from 'https://danbri.github.io/factoidal/npm/factoidal/browser.js';
     const r = await query(dataTtl, 'SELECT * WHERE { ?s ?p ?o }');
     console.log(r.results.bindings);
   </script>
   ```

   See [`demo-jsonld-playground.html`](../../docs/fstar-extracted/demo-jsonld-playground.html)
   for a working page built exactly this way (loads `browser.js` from
   `../npm/factoidal/browser.js`, a relative same-origin path).

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
import { queryDataset } from 'https://danbri.github.io/factoidal/npm/factoidal/browser.js';

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

### Durable browser persistence (delta log)

`browser.js` also exports a small IndexedDB-backed durable-UPDATE log —
see [`docs/designissues/2026-07-06-browser-persistence.md`](../../docs/designissues/2026-07-06-browser-persistence.md)
for the full design (why IndexedDB and not OPFS for v1, the tab-close/
crash guarantee mapping, and the quota/eviction honesty section). Every
byte moved through these functions is produced/consumed by the same
F\*-verified `RDF_Store_Columnar_DeltaLog`/`RDF_Store_Columnar_DeltaMerge`
modules the native on-disk delta log uses (`factoidal serve --rw
--delta-log`); this is a browser-native persistence path, not a mock:

```js
import { deltaLogOpen, deltaLogAppend, deltaLogMerge } from
  'https://danbri.github.io/factoidal/npm/factoidal/browser.js';

const handle = await deltaLogOpen();               // opens/creates an IndexedDB database
await deltaLogAppend(handle, 'INSERT DATA { <urn:x:a> <urn:x:p> "1" }');
await deltaLogAppend(handle, 'INSERT DATA { <urn:x:b> <urn:x:p> "2" }');

// ... reload the page, or close and reopen the browser ...

const merged = await deltaLogMerge(handle, '');    // '' = empty base dataset
console.log(merged);   // the two INSERT DATA ops, replayed from IndexedDB
```

Supported update ops: `INSERT DATA`, `DELETE DATA`, `CLEAR`, `DROP`,
`CREATE` — the same subset the native `--rw` commit path accepts;
anything else (`DELETE/INSERT WHERE`, `COPY`, `MOVE`, `ADD`) rejects
with `ok:false` rather than silently no-op'ing. `deltaLogReadAllHex`,
`deltaLogDestroy`, and the test-only `_deltaLogCorruptLastForTest` round
out the surface (see `browser.js`'s own JSDoc for each). This is a
prototype: no compaction and no `navigator.storage.persist()` wiring
yet (both named as staged next steps in the design doc), and it does
not yet back a hub demo page — that is separate, follow-on work.

### RDF/JS interop

```js
import { dataFactory } from "@factoidal/core";
const { namedNode, literal, quad, blankNode } = dataFactory;
const q = quad(blankNode("x"),
               namedNode("http://xmlns.com/foaf/0.1/name"),
               literal("Alice", "en"));
// Terms implement termType/value/language/datatype/.equals per the
// RDF/JS data-model spec; Dataset implements DatasetCore
// (add/delete/has/match/size/iteration).
```

## Custom extension functions (SPARQL 1.1 §17.6)

Register your own functions by IRI (the
[Comunica model](https://comunica.dev/docs/query/advanced/extension_functions/));
sync or async both work. The dispatch semantics are F\*-specified:
built-in function families always win, and a call to an IRI with no
registered function is the spec-required error (unbound in
SELECT/BIND position, row dropped in FILTER position). Issue:
[#463](https://github.com/danbri/factoidal/issues/463).

```js
import { query, registerExtensionFunction } from "@factoidal/core";

await registerExtensionFunction(
  "http://example.org/fn#isAdult",
  async ([age]) => Number(age.value) >= 18   // args are SRJ-style terms
);

const rows = await query(ds, `
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s WHERE { ?s <http://example.org/age> ?a
                    FILTER(fn:isAdult(?a)) }`);
```

Return a JS primitive (`boolean`/`number`/`string`), an SRJ-style term
object (`{type:'uri'|'literal'|'bnode', value, datatype?, 'xml:lang'?}`),
or a Promise of either; `null`/`undefined`/a thrown error is the §17.6
error. Async functions run over the synchronous verified engine
through a bounded, memoised re-evaluation loop — within one query
every call with the same arguments sees one stable answer.

## Functional API (fn)

`@factoidal/core/fn` is a strictly functional variant of the API above:
every extracted engine operation is already a value-to-value
function — `FnDataset` makes the JS surface match that instead of
papering over it with RDF/JS's mutable `add`/`delete`. Frozen
snapshots, free functions instead of methods (so they compose), and
RDFC-1.0 canonical hashes as a first-class, memoized identity — the
piece that makes dataflow-style recompute-skipping possible. Full
design rationale (cost model, backend/streaming extension points):
[`docs/designissues/2026-07-05-functional-dataset-api.md`](../../docs/designissues/2026-07-05-functional-dataset-api.md).

```js
const { parse, filter, hash, cell, derive } = require('@factoidal/core/fn');

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
const { parse, validate, shex, fromMapping, fromCsvw, rif } = require('@factoidal/core/fn');

const data = await parse(personTtl);
const shapes = await parse(shapesTtl);
const { conforms, report } = await validate(data, shapes); // SHACL

const ok = await shex(data, shexSchemaJson, 'http://example.org/alice'); // true|false|null

const mapped = await fromMapping(await parse(rmlMappingTtl), csvOrJsonText, 'csv'); // RML

const tabular = await fromCsvw(csvText, csvwMetadataJson, { mode: 'minimal' }); // CSVW csv2rdf

const saturated = await rif(data, rifRulesXml); // RIF Core forward chaining
```

## Lean engine (new in 0.2.0)

Two engines now ship in one package. `factoidal` and `factoidal/wasm`
are the F\*-extracted engine, unchanged. The subpaths below are the
Lean 4 engine (`L4Factoidal`, compiled to wasm).

`factoidal/l4` also exposes two deliberately narrow physical helpers:
`scanIBK2Predicate(ibk2Hex, predicateIri)` for the predecessor format and
`scanIBK3Predicate(ibk3Hex, predicateIri, blankNodeScope)` for the current
predicate-local format. They validate one canonical RDF block and scan its
named predicate, returning N-Triples and a row count. The IBK3 source scope
must be shared across blocks partitioned from one RDF import unit and differ
across unrelated units; this preserves document-scoped blank-node identity
when fragments are composed. The hexadecimal argument is a portable
diagnostic ABI, not the intended high-throughput buffer interface.

```js
const l4 = require('factoidal/l4-core');       // Lean engine, same API shape
const { select } = require('factoidal/select'); // choose an engine per call
```

### `factoidal/l4-core`

Same call shape as the main API — `parse`, `query`, `update`,
`serialize`, `canonicalize`, `graphs`, `canonicalHash`, `owlClosure`,
`coreRdfsClosure`, `coreRdfsCheck`, `rhoDfClosure`,
`rhoDfFragmentCheck`, `rdfsPlusClosure`, `owlIsConsistent` — plus four
Common Logic / IKL operations that exist only here, because the F\* tree
has no CL parser.

| Function | In → out | What the answer is worth |
|---|---|---|
| `clParse(clifText)` | CLIF text → shape report | sentence count, CL-vs-IKL dialect, canonical re-serialisation. Reads CLIF; never produces RDF |
| `clSerialize(clifText)` | CLIF → CLIF | canonical writer. Returns `roundTripProved: false` — `clif_roundTrip` is an open lemma and the fragment boundary is measured, not proved |
| `clAlphaNorm(clifText)` | CLIF → CLIF | alpha-equivalence canonical form (IKL Appendix B condition 1) |
| `clNormalize(clifText)` | CLIF → CLIF | Hayes's IKL-to-CL reduction. Returns `preserves: "satisfiability"` — **not** equivalence — and `noIntrusion`, the proof hypothesis decided rather than assumed |

A fifth op, `clFiniteSat(interpJson, clifText)`, is reachable only
through the raw dispatch ABI: `l4.call('clFiniteSat', [interpJson,
clifText])`. It is not in the typed layer.

### `factoidal/select`

Per-instance backend choice with a per-call override.

| Value | Behaviour |
|---|---|
| `lean` / `fstar` | that engine only; **throws** if it does not implement the function |
| `lean1st` / `fstar1st` | prefer that engine, fall through to the other for unimplemented functions |
| `slowcompareboth` | run both and **report** disagreement rather than throwing |

Every result names the engine that answered. `capabilityTable()`
returns which functions each engine implements.

### What this surface is, honestly

Four `String → String` operations plus one through raw dispatch. The
Lean tree behind them is larger than that — the CL/IKL and unified
model-theory modules run to about 22,000 lines — but only these reach
JavaScript today. Everything else in the Lean tree is used through
`parse`/`query`/`closure`, or not exposed at all.

## The `factoidal` command: querying a persisted store

Installing this package puts a `factoidal` command on PATH. It reads a
**Shardborough** store — the on-disk format the Lean `l4block-*` tools
write — with no native binary: JavaScript reads the files and moves the
bytes, and the Lean engine running as WebAssembly makes every format
decision (parsing the manifest, choosing the blocks, verifying their
SHA-256, evaluating the SPARQL).

> This command is not the native F\* `factoidal` binary that the API
> table below refers to. That one is `bin/<platform>/factoidal` in the
> repository and takes subcommands such as `shex` and `compact`. This
> one takes `version`, `sample-store`, `inspect` and `query`.

### First query, with nothing else to download

The package carries an activated store, so a fresh install answers a
SPARQL query at once:

```console
$ npm install @factoidal/core
$ npx factoidal query "$(npx factoidal sample-store)" \
    'SELECT ?c ?l
     WHERE { ?c <http://www.w3.org/2004/02/skos/core#inScheme>
                <http://cv.iptc.org/newscodes/videocodec/> ;
                <http://www.w3.org/2004/02/skos/core#prefLabel> ?l .
             FILTER(langMatches(lang(?l), "en")) }
     LIMIT 4'
c                                               l
<http://cv.iptc.org/newscodes/videocodec/c001>  "Analogue Black and White"@en-gb
<http://cv.iptc.org/newscodes/videocodec/c002>  "PAL"@en-gb
<http://cv.iptc.org/newscodes/videocodec/c003>  "NTSC"@en-gb
<http://cv.iptc.org/newscodes/videocodec/c004>  "SECAM"@en-gb
```

`factoidal sample-store` prints the path; `--json` adds what was
recorded when the store was packed. From JavaScript:

```js
import { sampleStorePath, sampleStoreFacts } from '@factoidal/core/sample-store'
```

The store holds 4,434 triples in 13 predicate blocks: five IPTC
NewsCodes vocabularies, published by the IPTC under CC BY 4.0 and taken
from [danbri/skosdex](https://github.com/danbri/skosdex). See `NOTICE`.

### Any other store

```console
$ factoidal inspect ./mystore
store ./mystore
generation gen-1 (activated through CURRENT)
manifest manifest.sbm2, 2372 bytes, wire version 6
layout predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0
blank-node profile (none recorded)
term registry local-ibk3-ptd1-v0
fixed-chunk Merkle commitment yes
5 entries, 393775 bytes, 6455 rows
generation directory holds 42 files, 846592 bytes

#  rows  bytes   kind  graphs  predicate
0  1800  110085  IBK3  -       http://www.wikidata.org/prop/direct/P31
1  719   35535   IBK3  -       http://www.wikidata.org/prop/direct/P361
...

$ factoidal query ./mystore 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
mode ibk3-paged-merkle-full-manifest(5), 5 artifacts, 393775 bytes read, plan declares 6455 block rows
n
"6455"^^<http://www.w3.org/2001/XMLSchema#integer>
1 row
```

`STORE` is a collection root: the directory holding `CURRENT`. The plan
line goes to stderr, so stdout carries only the result; `--quiet`
removes it.

| Option | What it does |
|---|---|
| `--format table` | default; a human display of the results |
| `--format json` | SELECT prints the engine's SPARQL 1.1 Query Results JSON; ASK and CONSTRUCT print the operation's envelope |
| `--format nquads` | CONSTRUCT only: the graph the engine serialized |
| `--format turtle` | CONSTRUCT only: that graph through the engine's own Turtle writer |
| `--explain` | print the artifacts the query needs and the open mode, and stop |
| `--limit N` | print at most N table rows; the total is always named |
| `--file PATH` | read the query text from a file |
| `--generation NAME` | read that generation rather than the activated one |

Under Deno, run the file directly; `inspect` and `query` need only
`--allow-read`:

```console
$ deno run --allow-read node_modules/@factoidal/core/bin/factoidal.mjs query ./mystore 'ASK { ?s ?p ?o }'
```

### What the command answers for, and what it does not

* **Every artifact is verified.** The engine refuses the whole query
  when a block's bytes do not hash to the SHA-256 the manifest commits,
  and names the artifact.
* **Three caps.** One call reads at most 64 artifacts, 8388608 artifact
  bytes and 100000 rows. A query over any of them is refused before a
  single file is read, with the cap and the value named. Nothing is
  truncated.
* **Committed artifacts only.** A store carrying uncompacted delta-log
  updates is not served by this path; use the native `l4block-*` tools.
* **`pack`, `activate`, `update` and `compact` exit 3.** They need
  WebAssembly operations that do not exist yet
  (https://github.com/danbri/factoidal/issues/641).
* **Node's WebAssembly frame budget.** Some evaluator paths recurse once
  per row. Measured 2026-09-03 on a 6455-row store, `SELECT ?s ?p ?o
  WHERE { ?s ?p ?o }` overflows the stack under Node's default while
  `SELECT *`, or the same query with a `LIMIT`, does not, and Deno
  clears all of them. The command reports it and exits 1 rather than
  crashing; `node --stack-size=4000` clears it.

Measured 2026-09-03 on macOS arm64, the 6455-triple `sequence_variant`
store, `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`, whole process
including start-up: 220 ms through this command, 33 ms through the
native `l4block-id-v3-query`.

## API (draft)

The `factoidal` CLI (`bin/factoidal-cli/factoidal_cli.ml`, built to
`bin/<platform>/factoidal`) calls the exact same F\*-extracted
functions as this npm surface — see `tests/local/cli_api_parity.sh`
for the test that diffs CLI output against the npm API on shared
fixtures.

| Function | Signature (informal) | CLI equivalent | Notes |
|---|---|---|---|
| `parse` | `(text, {format?, baseIRI?}) => Dataset` | `factoidal dump-nq -d FILE` (or `dump`/`dump-turtle`) | formats: `turtle`, `ntriples`, `nquads`, `trig`, `rdfxml`, `jsonld`\* — auto-detected where possible. Each call is one document: blank-node labels are scoped per RDF 1.1 |
| `query` | `(Dataset \| string, sparql, {entail?}) => Bindings[] \| boolean \| Dataset` | `factoidal query -d FILE -e 'SPARQL' [--entail RDFS\|OWL-RL]` | SELECT → array of `Map<var, Term>`; ASK → boolean; CONSTRUCT → Dataset\*\*; `entail: "RDFS" \| "OWL-RL"` |
| `update` | `(Dataset, sparqlUpdate) => Dataset` | `factoidal update -d FILE -e 'SPARQL update'` | \*\* in-memory; no persistence. (Durable UPDATE against a COTTAS store is a separate path: `factoidal serve --rw --delta-log ...` / `factoidal compact`.) |
| `serialize` | `(Dataset, {format}) => string` | `factoidal dump-nq FILE` (nquads) / `factoidal dump FILE` (ntriples) / `factoidal dump-turtle FILE` | `nquads`, `ntriples` (sorted); `turtle`\*\* (prefix-compacted, subject-grouped — needs the entry bundle, flattens named graphs into the default graph) |
| `canonicalize` | `(Dataset \| string) => string` | `factoidal canonicalize FILE` | RDFC-1.0 canonical N-Quads\*\* |
| `graphs` | `(Dataset) => Array<[iri, Dataset]>` | `factoidal graphs list FILE` | enumerate named graphs (default graph excluded); pure enumeration, no engine round-trip |
| `canonicalHash` | `(Dataset) => string` | `factoidal graphs hash FILE IRI` | RDFC-1.0 canonical hash of one graph\*\*; graph-scoped sibling of `canonicalize` — typically called with one entry of `graphs()`'s output |
| `shaclValidate` | `(data, shapes) => {conforms, report: Dataset}` | `factoidal shacl --data FILE --shapes FILE [--json]` (alias: `factoidal validate --shapes FILE FILE`) | \*\* SHACL Core validation; `report` is the `sh:ValidationReport` graph; exit code 0 iff `sh:conforms` |
| `shexValidate` | `(data, schemaText, focus, shape?) => boolean \| null` | `factoidal shex --data FILE --schema FILE.{json,shex} --node N [--shape S]` | \*\* ShEx (Shape Expressions) validation of one focus node; `schemaText` accepts ShExJ or ShExC — dispatched by the first non-whitespace character (`{` ⇒ ShExJ, else ShExC; the CLI additionally honors a `.shex` file extension); `null` = outside this engine's decidable ShEx fragment, never a guessed answer |
| `owlClosure` | `(data, mode) => Dataset` | `factoidal entail --data FILE --regime RDFS\|OWL-RL` | \*\* materializes the entailment closure (input + derived triples), default graph only. (`query --entail` applies the same closure internally before evaluating a query, but does not dump it on its own.) |
| `rmlMap` | `(mapping, sourceData, sourceKind) => Dataset` | `factoidal rml --mapping FILE --source FILE --kind json\|csv` | \*\* evaluates an RML mapping graph against one logical source (`sourceKind: "json" \| "csv"`); every triples map reads the SAME source — cross-source joins are out of scope for this entry point |
| `csvwToRdf` | `(csvText, metadataJson?, {mode?, base?, url?}) => Dataset` | `factoidal csvw --csv FILE [--metadata FILE] [--minimal] [--base IRI] [--url URL]` | \*\* CSVW csv2rdf conversion; metadata omitted = schema inferred from the CSV header row; `mode: "standard" \| "minimal"` (default standard); every table in a multi-table group reads the SAME csvText |
| `jsonldToRdf` | `(jsonldText, {base?, rdfDirection?, expandContext?, processingMode?}) => Dataset` | `factoidal jsonld --in FILE [--base IRI]` (or `factoidal dump-nq FILE.jsonld`, format auto-detected) | \*\* JSON-LD parsing with options `parse()` has no room for; plain `parse(text, {format:'jsonld'})` also works for the common case |
| `jsonldFromRdf` | `(data, {useNativeTypes?, useRdfType?}) => JSON-LD` | `factoidal dump-nq` ← (reverse) | \*\* serializes an RDF dataset as expanded-form JSON-LD (the reverse of `jsonldToRdf`); returns the parsed JSON-LD document (array of node objects), JCS-canonical |
| `didKeyResolve` | `(didString) => Dataset` | N/A (`did_runner`) | \*\* resolves a `did:key:z6Mk...` (Ed25519) to its DID Document as RDF; non-Ed25519 / malformed inputs reject rather than guess |
| `xmlWellformed` | `(xmlText) => boolean` | N/A (`xml_runner`) | \*\* XML 1.0 well-formedness check (byte-oriented, no DOCTYPE/DTD production — a document with a DOCTYPE reports `false`) |
| `xpathEval` | `(xmlText, xpathExpr) => {resultType, value \| nodes, ...}` | N/A | \*\* XPath 1.0 evaluation over an XML document; `resultType` is `'nodeset' \| 'string' \| 'number' \| 'boolean'` |
| `rifEval` | `(data, rifRulesXml) => Dataset` | `factoidal rif --rules FILE --data FILE` | \*\* RIF Core forward-chaining saturation (materializes input + derived triples); accepts real vendored RIF-XML (`<!DOCTYPE>` + `&rif;`/`&xs;`/`&rdf;` entities) unmodified |
| `toCottas` | `(data, {format?}) => Uint8Array` | `factoidal compact --native-writer` | \*\* serializes a dataset to COTTAS/Parquet bytes via the native writer; round-trips into `openCottas()` and into the native `--data-cottas`/`--data-cottas-mem` CLI flags byte-for-byte |
| `openCottas` | `(bytes: string \| Uint8Array \| ArrayBuffer) => handle` | `factoidal query --data-cottas-mem FILE` | \*\* opens a whole `.cottas` artifact's bytes as a queryable, read-only, in-memory store; rows decode lazily as `queryCottas()` touches them (no heap `Dataset`, no full parse) |
| `queryCottas` | `(handle, sparql) => Bindings[] \| boolean \| Dataset` | `factoidal query --data-cottas-mem FILE -e 'SPARQL'` | \*\* SPARQL over a store opened by `openCottas()`; no `entail` option, no write overlay (read-only), no DESCRIBE |
| `closeCottas` | `(handle) => void` | N/A | releases a handle from this process's registry; does not evict the underlying byte cache |
| `queryRaw` | `(input, sparql) => string` | `factoidal query -d FILE -e 'SPARQL' -o json` | SPARQL-Results-JSON string, for callers that want the wire form |
| `capabilities` | `() => {construct, update, canonicalize, graphs, canonicalHash, shacl, shex, owlClosure, rml, csvw, jsonld, jsonldFromRdf, didKey, xml, xpath, rif, cottasBytesStore, ...}` | N/A | runtime feature probe; the CLI is one fixed native binary, not a runtime bundle whose feature set varies |
| `dataFactory` | RDF/JS DataFactory | N/A | data-model class, not an engine operation |
| `Dataset` | RDF/JS DatasetCore | N/A | returned by `parse`; accepted everywhere |

The `fn.js` functional layer's own combinators — `union`, `difference`,
`filter`, `mapQuads`, `equals`, `hash`, `builder`/`fromChunks`,
`cell`/`derive` — are pure client-side set algebra and dataflow
plumbing over already-materialized `Dataset`s. They have no CLI
equivalent by design: there is no engine operation to wrap, only JS
composition on top of the operations already listed above.

\* JSON-LD parsing (expanded form, inline `@context`, `@base`
resolution, `@reverse`, container maps) works through both `parse()`
and `jsonldToRdf()` when the npm-entry bundle is loaded. Remote
`@context` URLs need a `documentLoader`, which this package's entries
don't register (an honest failure, not a silent wrong answer) —
tracked against the vendored W3C json-ld-api suite.
\*\* CONSTRUCT, UPDATE, `canonicalize`, `canonicalHash`,
`shaclValidate`, `shexValidate`, `owlClosure`, `rmlMap`, `csvwToRdf`,
`jsonldToRdf`, `jsonldFromRdf`, `didKeyResolve`, `xmlWellformed`, `xpathEval`, `rifEval`, `toCottas`, `openCottas`, `queryCottas`, and
`closeCottas` are probed via `capabilities()`: they activate
automatically when the dedicated npm-entry engine bundle is present,
and the package reports their absence honestly against older bundles
instead of guessing.
`canonicalHash` rides the same engine support as `canonicalize` (it
computes `canonicalize()` over one graph's triples); `graphs` is pure
JS enumeration and is always available.

### The db API (openCottas/queryCottas/closeCottas/toCottas)

The in-memory COTTAS/Parquet bytes store works identically on both
engines: `require('@factoidal/core')` (js_of_ocaml) and
`require('factoidal/wasm')` (wasm_of_ocaml, Node ≥ 22) expose the same
`toCottas`/`openCottas`/`queryCottas`/`closeCottas` functions, backed
by the same F\*-verified reader
(`RDF.CottasStore`/`Parquet.Footer`/`SPARQL11_Store`). A store is
read-only and holds no `entail` option — see the divergence list on
`queryCottas`'s doc comment in `lib/api.js`. Zstd-compressed COTTAS
pages are supported under js_of_ocaml (via the vendored `fzstd`
decompressor baked into `factoidal.js`); under wasm_of_ocaml, Zstd
decompression is still an identity-stubbed primitive (a documented
gap, tracked separately) — write bytes with `toCottas()` (which never
reaches for Zstd on small in-memory writes) rather than a
Zstd-compressed on-disk fixture if you need a wasm-portable test case.
The browser entries mirror this: `browser.js`'s `openCottas`/
`queryCottas`/`closeCottas`/`toCottas` drive the js_of_ocaml npm-entry
ABI over `fetch()`; `browser-wasm.js` exposes the same four functions
against the wasm_of_ocaml npm-entry ABI (`factoidal-npm-entry.wasm.js`).

## Capability matrix

Every public function, where it runs, and what it needs. "Node" is the
`require('@factoidal/core')` / `import '@factoidal/core'` entry (`index.js` /
`index.mjs`); "Browser" is `import 'factoidal/browser'` (`browser.js`);
"Wasm" is `require('factoidal/wasm')`. **Needs** legend: *CLI bundle* =
the fresh-eval `factoidal.js` bundle (always present); *entry* = the
persistent `factoidal-npm-entry.js` ABI bundle (probe with
`capabilities()`); *HACL\* init* = the wasm crypto backend must be
initialised (auto on Node, explicit in the browser — see below);
*IndexedDB* = a browser storage layer.

| Function(s) | Node | Browser | Wasm | Needs |
|---|---|---|---|---|
| `parse`, `query` (SELECT/ASK), `serialize` (nquads/ntriples), `canonicalize`, `graphs`, `canonicalHash`, `queryHdt`, `queryRaw` | ✓ | ✓\* | ✓ | CLI bundle |
| `query` (CONSTRUCT), `update`, `serialize` (turtle) | ✓ | ✓\* | ✓ | entry |
| `shaclValidate`, `shexValidate`, `owlClosure`, `rmlMap`, `csvwToRdf`, `jsonldToRdf`, `jsonldFromRdf`, `didKeyResolve`, `xmlWellformed`, `xpathEval`, `rifEval` | ✓ | ✓ | partial† | entry |
| `coreRdfsClosure`/`rhoDfClosure`, `coreRdfsCheck`/`rhoDfFragmentCheck`, `rdfsPlusClosure`, `tableauMaterialise`, `tableauDlInconsistent`, `owlIsConsistent`, `owlEntails` | ✓ | ✓ | wrapper only‡ | entry |
| `xsltTransform`, `mathmlEval`, `xformsRecalc`, `jsonSchemaValidate`, `schematronValidate`, `toan*`, `matrix*` | ✓ | ✓ | partial† | entry |
| `openCottas`, `queryCottas`, `closeCottas`, `toCottas` | ✓ | ✓ | ✓ | entry |
| `vcSha256Hex`, `vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical` | ✓ | ✓ | ✓ | entry + HACL\* init |
| `deltaLogOpen`/`Append`/`ReadAllHex`/`Merge`/`Destroy` | ✗ | ✓ | ✗ | entry + IndexedDB |
| `dataFactory`, `Dataset`, `fn.*` combinators (`union`/`difference`/`filter`/`mapQuads`/`equals`/`hash`/`builder`/`cell`/`derive`/`pipe`) | ✓ | — | ✓ | none (pure JS) |
| `capabilities` | ✓ | — | ✓ | none (probe) |

\* In the browser the same capability is reached through `browser.js`'s
own function names, which differ from the Node API: SELECT/ASK is
`query(dataString, sparql, {output})` (returns SPARQL-Results JSON, not
`Bindings[]`); parse-to-N-Quads is `toRdf()`; multi-graph queries use
`queryDataset()`. CONSTRUCT/UPDATE/Turtle ride the same `entry` bundle,
fetched over the network on first use.
† Wasm (`require('factoidal/wasm')`) today re-exports the core +
validation/inference/COTTAS set (`parse`/`query`/`update`/`serialize`/
`canonicalize`/`shaclValidate`/`shexValidate`/`owlClosure`/`rmlMap`/
`csvwToRdf`/`jsonldToRdf`/`rifEval`/`openCottas`…/`capabilities`); the
typed-engine `#74` functions and the `vc*`/`did`/`xml`/`xpath` wrappers
are exposed on the js and browser entries. The underlying wasm ABI
carries them — the `/wasm` re-export surface is being brought to parity.
‡ `coreRdfsClosure`/`rhoDfClosure`/`coreRdfsCheck`/`rhoDfFragmentCheck`/
`rdfsPlusClosure`/`tableauMaterialise`/`tableauDlInconsistent`/
`owlIsConsistent`/`owlEntails` are exported from `factoidal/wasm`
(wrapper wiring — the same `buildApi()` `index.js` uses), but the
committed `factoidal-npm-entry.wasm.js` ABI bundle predates these
functions (built before they landed on the ABI) — calling them on the
wasm engine throws the existing "pending npm-entry bundle" error until
that bundle is rebuilt via a real `wasm_of_ocaml` build (not a copy).
`capabilities()` on the wasm engine reports this honestly (`tableau:
false` etc.) rather than guessing.

### VC crypto: the init story

The `vc*` functions run the F\*-extracted VC Data Integrity pipeline
over HACL\*'s official WebAssembly build, so the wasm backend has to be
initialised before the first call (a verify against an uninitialised
backend **throws** — it never silently returns `true`; issue #286).

- **Node** (`index.js`/`index.mjs`, `/wasm`, `fn`): the typed wrappers
  **auto-await `initHacl()` on first call** — a caller writes
  `await vcEd25519Verify(pk, msg, sig)` and never touches init.
- **Browser** (`browser.js`): **explicit init required** — the
  `hacl-wasm` URL is page-specific. Serve `hacl-wasm/` next to the page
  and `await initHacl({ apiUrl })` from `hacl-init.js` once, then call
  the `vc*` wrappers. (Auto-init isn't possible without a URL to fetch.)

### Native-CLI-only capabilities (not on the npm surface, by design)

These live only in `bin/factoidal-cli` (the native `factoidal` binary),
not in the JS package — they are I/O- or process-shaped, not pure
value transforms:

- **SPARQL endpoint / federation.** `factoidal serve` (HTTP endpoint),
  `SERVICE` federation and `--data-cottas`/`--data-hdt` *file-path*
  backends read the filesystem/network at query time. The npm
  `queryHdt`/`openCottas` take *bytes* in-process instead.
- **Durable UPDATE against on-disk COTTAS.** `factoidal serve --rw
  --delta-log …` + `factoidal compact` — the npm `update()` is
  in-memory only; the browser `deltaLog*` family is the closest
  in-package durable path (IndexedDB, browser-only).
- **Internal primitives.** `runFactoidalCli` / `loadNpmEntry` (browser)
  are exported but are the low-level bundle drivers, not the intended
  API; the `_*` functions (e.g. `_deltaLogCorruptLastForTest`) are
  test-only and intentionally left untyped.

### GeoSPARQL — six topological functions

The `geof:` functions below are built into the SPARQL engine and need no
import. They work through `query()` / `fn.query()` AND against a
persisted store through `factoidal query`, because both paths evaluate
in the same environment.

    geof:sfEquals   geof:sfDisjoint   geof:sfIntersects
    geof:sfTouches  geof:sfWithin     geof:sfContains

```sparql
PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
PREFIX geo:  <http://www.opengis.net/ont/geosparql#>
SELECT ?a WHERE {
  ?a :footprint ?w
  FILTER(geof:sfWithin(?w, "POLYGON((0 0,0 2,2 2,2 0,0 0))"^^geo:wktLiteral))
}
```

**What is NOT there**, stated so nobody plans around it: no
`geof:distance`, `geof:buffer`, `geof:envelope`, `geof:boundary`,
`geof:convexHull` or any other non-topological measure; no
`geof:relate` with a DE-9IM matrix; no coordinate reference system
handling beyond what the WKT literal carries; no GML literals. Geometry
comes from a WKT parser, so a shapefile, GeoJSON or GML source must be
converted to `geo:wktLiteral` before it is loaded.

### Full text: SPARQL's own functions, no index

`CONTAINS`, `STRSTARTS`, `STRENDS` and `REGEX` (SPARQL 1.1 §17.4.3) are
implemented and are the way to search text. They are evaluated per row
after a block is decoded — **there is no inverted index and no
`text:query`-style extension**. Measured 2026-09-04: a `CONTAINS` over
45,806 `skos:prefLabel` values in one block answers in about 6 seconds.
That is fine for a vocabulary and will not scale to a large literal
corpus.

## Limits (deliberate, documented)

- **In-memory only.** ~1.2 KB RAM per quad (measured); 1M quads ≈
  1.2 GB. No streaming parse yet — inputs are whole strings.
- Lenient Turtle parsing: `parse()` cannot yet reject syntax errors
  (bad input can yield an empty dataset).
- No *write* persistence in the npm build (SPARQL Update stays
  in-memory; durable UPDATE against a COTTAS store on disk is
  native-only today). *Reading* a COTTAS artifact's bytes is available
  in-process via `openCottas`/`queryCottas`/`closeCottas`/`toCottas`
  (both engines, both npm and browser entries) — see "The db API"
  above.
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
