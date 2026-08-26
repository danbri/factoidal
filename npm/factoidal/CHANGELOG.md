# Changelog

## 0.3.0 — both engines in one package, with a backend selector

- The Lean 4 engine (`L4Factoidal`, wasm) now ships INSIDE
  `@factoidal/core` as `l4-assets/`, alongside the F\*-extracted
  engine. One install gets both. `require('factoidal/l4')` and
  `factoidal/l4-core` are unchanged; the resolver checks in-package
  assets first, then falls through to the old order (companion
  package, `$FACTOIDAL_L4_ASSETS`, repo checkout).
- `@factoidal/lean` is superseded and was never published.
- New subpath `factoidal/select`: a backend selector, per-instance
  with per-call override. Values `lean`, `fstar`, `lean1st`,
  `fstar1st`, `slowcompareboth`. A request naming exactly one engine
  never gets an answer from the other -- `lean` and `fstar` throw on a
  function that engine does not implement; `lean1st` / `fstar1st` fall
  through, and `lean1st` also takes a list of functions to route to
  F\* regardless. Every result carries the answering engine.
  `slowcompareboth` runs both and REPORTS disagreement rather than
  throwing; comparison is RDFC-1.0 isomorphism for Dataset-shaped
  results and bag equality (blank nodes relabelled per side) for
  SELECT bindings.
- Measured on the typed API surface at this release: 15 functions both
  engines answer, 39 F\*-only, 0 Lean-only (out of 54). This measures
  the typed wrapper surface, not the Lean engine's total capability --
  `l4-core.js` wires 12 of the engine's 21 dispatch ops.
- The CL/IKL ops (`clParse`, `clToDataset`, `queryWithIklService`) are
  NOT exposed through the npm API, and `x-ikl-*` entailment regimes
  are rejected. The ops remain present in the compiled wasm; they are
  unreachable through the package. Owner decision, 2026-08-26: the
  IKL-to-RDF projection stays out of npm until it has a reversibility
  theorem (danbri/factoidal#620).

## 0.2.0 — Lean 4 engine subpath

- New `factoidal/l4-core` subpath: the same typed API served by the
  Lean 4-extracted wasm engine instead of the F\*-extracted one
  ([#476](https://github.com/danbri/factoidal/issues/476)). Engine
  assets resolve from the `@factoidal/lean` companion package, the
  `FACTOIDAL_L4_ASSETS` environment variable, or the repository
  checkout, in that order. `capabilities()` reports the Lean engine's
  actual surface; `shaclValidate`/`owlIsConsistent`/`owlEntails`
  raise pinned errors rather than returning wrong answers
  ([#586](https://github.com/danbri/factoidal/issues/586) tracks the
  OWL verdicts).
- `serialize({ format: "nquads" })` now normalizes through the entry
  ABI instead of the CLI path.


## 0.1.0 — First published release (as `@factoidal/core`)

- SPARQL 1.1 §17.6 extension functions
  ([#463](https://github.com/danbri/factoidal/issues/463)),
  Comunica-style: `registerExtensionFunction(iri, fn)` /
  `unregisterExtensionFunction(iri)` / `clearExtensionFunctions()`.
  `fn` may be sync or async; it receives the evaluated arguments as
  SRJ-style term objects and returns a term object, a JS primitive,
  or a Promise of either. Dispatch semantics are F*-specified
  (SPARQL11.Algebra.fst's E_FunctionCall arm consults the registry
  LAST; an unregistered IRI is the spec-required error — unbound in
  SELECT/BIND position, row dropped in FILTER position). Async
  functions run over the synchronous extracted engine via a bounded
  memoised re-evaluation trampoline in `lib/api.js`.

- Final name: `@factoidal/core`, published under the `@factoidal` npm
  org (owner decision, 2026-08-22). Everything under "Unreleased"
  below ships in this first cut. The `private` flag and the
  publish-blocking `prepublishOnly` guard are removed; `prepublishOnly`
  now runs the package test suite instead.
- The wasm bundle (`factoidal.wasm.js` + assets) is rebuilt in sync
  with the js bundle. The previous in-tree wasm build predated the
  2026-08-15 COTTAS UTF-8 writer fix (issue #445) and its
  format-compatibility gate rejected stores written by the current js
  bundle (caught by the wasm/js parity test in `test/`).

## Unreleased

- Package renamed from the placeholder `@danbri/foafos` to `factoidal`
  (issue #403). The package was never published under the old name, so
  there is no npm-registry alias or deprecation notice to add -- this
  is a rename of unpublished scaffolding, not a breaking change to a
  released package.
- `coreRdfsClosure`/`coreRdfsCheck`/`rhoDfClosure`/`rhoDfFragmentCheck`/
  `rdfsPlusClosure`/`owlIsConsistent`/`owlEntails` now exported from
  `factoidal/wasm` (previously js_of_ocaml-only); `coreRdfsClosure`/
  `coreRdfsCheck`/`rhoDfClosure`/`rhoDfFragmentCheck`/`rdfsPlusClosure`
  added to `factoidal/fn` (FnDataset-returning wrappers around the
  certified ρdf closure family; `owlIsConsistent`/`owlEntails` were
  already there). No new engine logic -- these functions were already
  wired into the npm-entry ABI (`bin/npm-entry/entry_jsoo.ml`) and
  `lib/api.js`'s `buildApi()`; this closes a wrapper-surface gap
  between `index.js`/`browser.js` (which had them) and `wasm.js`/
  `fn.js` (which didn't). See docs/theorem-registry.md for
  `rho_df_closure`'s decides-iff guarantee.
- `version.json` gains a machine-readable `claims` block (issue #403's
  G2 item): a summary of theorem-backed guarantees, each entry naming
  the exact F* theorem, its file, and the docs/theorem-registry.md
  section to check it against -- never a bare assertion. `build-
  ocaml.sh npm` now preserves this block across rebuilds.
- Browser-side durable-UPDATE persistence (issue #282): `browser.js`
  gains `deltaLogOpen`/`deltaLogAppend`/`deltaLogReadAllHex`/
  `deltaLogMerge`/`deltaLogDestroy` (IndexedDB-backed, survives page
  reloads and browser restarts), plus `deltaBatchToHex`/
  `deltaMergeApplyBrowser` on the npm-entry ABI. Every byte moved is
  produced/consumed by the F*-verified `RDF_Store_Columnar_DeltaLog`/
  `RDF_Store_Columnar_DeltaMerge` modules the native on-disk delta log
  (`factoidal serve --rw --delta-log`) uses -- see
  `docs/designissues/2026-07-06-browser-persistence.md` for the v1
  architecture decision (IndexedDB vs. OPFS), the crash/reload
  guarantee mapping, and the quota/eviction honesty section. Prototype
  scope: no compaction, no `navigator.storage.persist()` wiring yet
  (both named as staged next steps); supported update ops are
  `INSERT DATA`/`DELETE DATA`/`CLEAR`/`DROP`/`CREATE`, same subset the
  native `--rw` path accepts.
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
