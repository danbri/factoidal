# Changelog

## Unreleased

- CSVW csv2rdf (`csvwToRdf`) added to the npm-entry ABI, the typed API
  (`index.js`/`wasm.js`), and the functional API (`factoidal/fn`:
  `fromCsvw`): raw CSV text + an optional CSVW metadata document
  (tabular-metadata JSON; omitted = schema inferred from the header
  row) to a Dataset, in `standard` (csvw:TableGroup/Table/Row wrapper)
  or `minimal` (bare cell triples) mode. `capabilities()` gained a
  matching `csvw` probe. Engine modules: `CSVW.Metadata.fst` /
  `CSVW.URITemplate.fst` / `CSVW.Conversion.fst` (measured against the
  vendored W3C csv2rdf suite -- see the CSVW program plan's stage
  table for coverage and known gaps: datatype `format` facets,
  list-valued cells, and full inherited-property propagation are not
  yet implemented).
- SHACL Core (`shaclValidate`), ShEx (`shexValidate`), RDFS/OWL-RL
  closure (`owlClosure`), RML (`rmlMap`), and RIF Core
  (`rifEval`) added to the npm-entry ABI and the typed API
  (`index.js`/`wasm.js`) and the functional API (`factoidal/fn`:
  `validate`/`shex`/`fromMapping`/`rif`). `jsonldToRdf` exposes
  JSON-LD-specific options (`base`/`rdfDirection`/`expandContext`/
  `processingMode`); plain `parse(text, {format:'jsonld'})` through
  the npm-entry bundle also now works (previously an unhandled
  format-dispatch case). `capabilities()` gained matching
  `shacl`/`shex`/`owlClosure`/`rml`/`jsonld`/`rif` probes.
- Typed public API: `parse` -> RDF/JS `Dataset`, `query` ->
  `Bindings[]` (Maps of variable -> RDF/JS term) | boolean | Dataset,
  `update`, `serialize`, `canonicalize` (RDFC-1.0), `capabilities`.
- RDF/JS data model (`rdfjs.js`): spec-compliant DataFactory + terms
  with `.equals()`, DatasetCore `Dataset`, converters to/from the
  engine's N-Quads interchange text. Exported as `factoidal/rdfjs`.
- `factoidal/wasm`: same API on the wasm_of_ocaml engine (Node >= 22).
- npm-entry ABI consumer (`bin/npm-entry/entry_jsoo.ml` in the repo):
  persistent string/JSON ABI enabling CONSTRUCT, UPDATE and
  canonicalize; the API falls back to argv-driving the CLI bundle
  until that bundle is built and staged.
- Rewritten `index.d.ts` with self-contained RDF/JS typings; the old
  SRJ-shaped `query()` lives on as `queryRaw()`.
- `node:test` unit suite (`npm test`); entry-dependent tests skip with
  reason "pending npm-entry build".

## 0.1.0-alpha.0 — Initial scaffold, unpublished

Directory layout committed to the main repo under `npm/factoidal/`.
Not yet published to the npm registry.

- `package.json` with dual CJS (`index.js`) / ESM (`index.mjs`)
  entry points, a `browser` condition, and a TypeScript declaration
  file (`index.d.ts`).
- `index.js` wraps the js_of_ocaml-compiled `factoidal.js` bundle in
  an `async` `query(data, query, options)` API with `dataFormat`,
  `entail`, and `output` options.
- `browser.js` mirrors the same API for browsers, fetching
  `factoidal.js` via `fetch()` relative to the module URL.
- `build-ocaml.sh npm` target (in the repo root's
  `formal/fstar/build-ocaml.sh`) populates this directory from the
  existing extraction output.
