# Changelog

## Unreleased

- The `factoidal` command answers SPARQL against a persisted
  Shardborough store with no native binary. `factoidal inspect STORE`
  decodes the manifest through the engine's `storeManifestInspect`
  operation and prints the wire version, layout, blank-node profile and
  the entry table; `factoidal query STORE 'SELECT ...'` asks the engine
  which artifacts the query needs, reads exactly those, and hands their
  bytes to `storeQuery` through one WebAssembly heap buffer with no
  encoding. Every artifact is verified against the SHA-256 the manifest
  commits before an answer is given. Formats: `table`, `json`,
  `nquads`, `turtle`; `--explain` prints the artifact plan. Runs under
  Node and under Deno (`--allow-read`).
- The three caps of the store query operation — 64 artifacts, 8388608
  artifact bytes, 100000 rows — are reported with the cap, the value
  and a next step, and are decided before a single file is read.
  Nothing is truncated.
- `pack`, `activate`, `update` and `compact` still exit 3; they need
  operations that do not exist yet
  (https://github.com/danbri/factoidal/issues/641).
- A large piped result is no longer truncated: the command sets
  `process.exitCode` instead of calling `process.exit()`, which dropped
  everything past the 64 KiB pipe boundary.

## 0.3.0 — Lean block-worker preview

- The bundled Lean-derived WASM artifact exports
  `scanIBK2Predicate(ibk2Hex, predicateIri)` through `factoidal/l4`.
  It validates a canonical IBK2 block and executes its selective predicate
  scan, returning N-Triples plus a row count.  This is a narrow physical
  helper for the Shardborough work, not full SPARQL execution inside a storage
  backend and not a high-throughput buffer ABI (the current hex transport is
  intentionally diagnostic).
- The regenerated Lean artifact is synchronized across the package's
  `l4-assets/` and the Hub build, and is exercised against the music IBK2
  fixture by `tools/wasm-ibk2-smoke.mjs` in the repository.
- The current-format companion
  `scanIBK3Predicate(ibk3Hex, predicateIri, blankNodeScope)` validates and
  scans complete predicate-local IBK3 artifacts. Its mandatory source/dataset
  scope preserves one blank node across blocks from the same RDF import while
  keeping same-spelled labels in unrelated inputs apart. Hub post 51 composes
  three real IBK3 scans into an editable Lean-WASM SPARQL query.

## 0.2.0 — both engines in one package, with a backend selector

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
  engines answer, 38 F\*-only, 4 Lean-only (out of 57). This measures
  the typed wrapper surface, not the Lean engine's total capability --
  `l4-core.js` wires 16 of the engine's 21 dispatch ops.
- `clParse` (Common Logic Interchange Format text, ISO/IEC 24707:2018,
  with the IKL `that`-operator extension) is now wired into the typed
  API -- `l4-core.js`/`lib/api.js`/`select.js`, with `.d.ts` types and
  tests. It reads CLIF text and reports its shape (sentence count,
  `pureCL` dialect flag, canonical re-serialisation); it never produces
  RDF. `pureCL` is a DIALECT flag, not a validity or quality signal:
  true while the text stays inside ISO/IEC 24707 Common Logic, false
  once it uses IKL's `that` operator. It is the first Lean-only entry
  on the typed capability table -- formal/fstar has no CL/IKL parser at
  all, so `index.js`/`wasm.js` never export it, `factoidal/select`'s
  `backend:'fstar'` throws for it (never falls back to Lean), and
  `backend:'slowcompareboth'` fails the capability precondition rather
  than comparing one side against nothing.
- `clSerialize`, `clAlphaNorm` and `clNormalize` join `clParse` on the
  same Lean-only typed surface (owner instruction, 2026-08-26 -- "wire
  into js functional api"), same `.d.ts`-typed, test-covered pattern:
  `clSerialize` reads CLIF text and writes it back in canonical
  spacing, surfacing `roundTripProved: false` unmodified (the
  round-trip lemma `clif_roundTrip`, `CL/ClifAdequacy.lean`, is OPEN --
  the fragment boundary `marksLexable` is measured, not proved).
  `clAlphaNorm` gives each sentence's bound-variable-renaming canonical
  form (IKL GUIDE Appendix B condition (1)). `clNormalize` is Hayes's
  satisfiability-preserving reduction of IKL to Common Logic
  ([#625](https://github.com/danbri/factoidal/issues/625)): it
  surfaces `preserves: "satisfiability"` (not equivalence -- suited to
  entailment/consistency testing, not to transforming data you intend
  to keep) and `noIntrusion` (the proof hypothesis `CL.noIntrSs [] []`
  decides, not a paraphrase of it). `clFiniteSat`, the fifth CL/IKL op,
  is DEFERRED rather than wired: it takes a caller-supplied finite-
  interpretation JSON encoding with no user yet, and a typed wrapper
  would freeze that shape before it is known to be right; it stays
  reachable through the raw dispatch ABI.
- The IKL-to-RDF projection ops (`clToDataset`, `queryWithIklService`)
  are DELETED from the engine source (danbri/factoidal#626), along with
  the content-addressed proposition graph names they minted. They were
  never exposed through the npm API. `x-ikl-*` entailment regimes are
  still rejected at the JS layer, and the engine no longer defines the
  family either. The two ops remain present in the compiled wasm
  artifact until it is rebuilt (danbri/factoidal#627) -- the artifact
  is ahead of its source. `clParse` is a different op (it never
  produces RDF) and is unaffected.

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
