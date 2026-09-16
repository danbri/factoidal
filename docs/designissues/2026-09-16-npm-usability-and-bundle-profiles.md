# 2026-09-16 — npm usability: strict parsing, dataset handles, prefixes, bundle profiles

## Status

Landed on 2026-09-16 on the branch `claude/daw-module-usability-7z5wfa`.
Tracking: https://github.com/danbri/factoidal/issues/679 (umbrella), with
https://github.com/danbri/factoidal/issues/344,
https://github.com/danbri/factoidal/issues/680,
https://github.com/danbri/factoidal/issues/681,
https://github.com/danbri/factoidal/issues/682,
https://github.com/danbri/factoidal/issues/683,
https://github.com/danbri/factoidal/issues/684,
https://github.com/danbri/factoidal/issues/686 and
https://github.com/danbri/factoidal/issues/687.
Open follow-ups: https://github.com/danbri/factoidal/issues/685 (Lean engine
parity), https://github.com/danbri/factoidal/issues/688 (a dead branch in the
N-Triples and N-Quads strict walks), https://github.com/danbri/factoidal/issues/689
(a stale extraction that blocked the JavaScript build step).

## 1. The report

A session that built a browser digital audio workstation on `@factoidal/core`
0.7.1 reported six defects (quoted verbatim in
https://github.com/danbri/factoidal/issues/679). None was an RDF semantics
defect. All six were packaging and diagnostics:

| Item | Report | Mechanism that landed |
|---|---|---|
| 1 | `parse("this is not turtle")` returned an empty dataset; a missing `.` dropped one statement silently | Parsing is strict by default. The new leaf module `formal/fstar/Parser.Diagnostics.fst` gives every syntax a first error with byte offset, line and column, and the Turtle and TriG walks also return the prefix table. `parseToDatasetJson` answers `{"ok":false,"error","offset","line","column","format"}`; `parseDocument(..., {"lenient":true})` returns the recoverable statements plus the diagnostic. JavaScript rejects with `ParseError` (`line`, `column`, `offset`, `format`). |
| 2 | Every `query(dataset, sparql)` serialised the Dataset to N-Quads and the engine re-parsed it and rebuilt its indexes | Dataset handles on the F\* entry, mirroring the Lean ABI of https://github.com/danbri/factoidal/issues/585: `datasetOpen`, `datasetQuery`, `datasetUpdate`, `datasetSerialize`, `datasetSerializeWith`, `datasetClose`. The indexed backend is built once per open or update. JavaScript: `openDataset()` and `DatasetHandle`. |
| 3 | `browser.js` fetched and evaluated the bundle per call, which a page under `script-src 'self'` refuses; the working path was not exported; `version` was missing | `@factoidal/core/api` (`createApi(entry)` over a loaded engine object), the engine bundles in the `exports` map, `version` and `engine` on every API object, `browser.js` reads a classic-script preload from `globalThis` before fetching, and routes parse and query through the persistent ABI. Proved by an esbuild bundle running under Node and by a headless Chromium page served with `Content-Security-Policy: script-src 'self'`. |
| 4 | Turtle output invented `ns1:` labels; `parse` discarded the prefixes it read; `"220.0"^^xsd:decimal` printed in quoted form | `RDF.Turtle.Serialize.fst`: `turtle_of_graph_opts` with a caller prefix table and grammar-guarded bare literals. `Dataset.prefixes`; `serialize(ds, {format:'turtle', prefixes, literalShorthand})`; a handle's Turtle output uses the document's own prefixes. |
| 5 | Blank nodes are labelled in document order (`p7_d7__anon43`), relied on but undocumented | Documented and pinned: `parse()` returns quads in canonical N-Quads order; anonymous nodes are numbered `_anonN` in document order by `Parser.Turtle.fst`; `d<n>_` is the engine's per-document scope, `p<k>_` the wrapper's per-call prefix. |
| 6 | 1.17 MB entry bundle, no gzip figure, no lean build | `tools/bundle-sizes.sh` and `docs/test-results/bundle-sizes.json`; a README table; a lite bundle profile at half the size (section 4). |

## 2. Decisions and their provenance

- **Strict by default.** Requested in https://github.com/danbri/factoidal/issues/344
  ("Default to strict") and again by the report. Lenience is an explicit option
  (`{lenient:true}`) whose result carries the diagnostic. The parser records
  the first error only (its existing single-error convention), so a count of
  skipped statements is not available; the lenient result carries one
  diagnostic and the count of statements kept.
- **Bare numeric and boolean literals by default.** The 2026-07-04 serializer
  brief kept the quoted form. The report asked for the shorthand and the owner
  forwarded the report with "address all of these". The default is one boolean
  in `RDF.Turtle.Serialize.fst` (`turtle_render_defaults`); this is a
  Claude-inferred default, recorded in
  https://github.com/danbri/factoidal/issues/681, and the owner can reverse it
  there. A literal prints bare only when its datatype is `xsd:integer`,
  `xsd:decimal`, `xsd:double` or `xsd:boolean` and its lexical form matches
  the Turtle terminal for that datatype, so the parse of the output gives the
  same (lexical form, datatype) pair. Checked by a round-trip probe on 18
  literal cases (valid, invalid, padded, misdatatyped) and by the extended
  `tests/local/turtle_pretty_regressions.sh` fixture.
- **Prefix rule.** Caller pairs win in the caller's order; a caller namespace
  no IRI uses is not emitted; well-known prefixes yield on a namespace or label
  collision with the caller; auto labels `ns1:`, `ns2:` skip any label the
  caller used.
- **One global name for both bundle profiles.** Both `factoidal-npm-entry.js`
  and `factoidal-npm-entry-lite.js` register `factoidalNpmEntry`, with a
  `profile` member. The 2026-07-05 design record left this open (its decision
  5); one name keeps `lib/api.js`, `browser.js` and `createApi` unchanged
  across profiles. Two bundles never load in one page by design.
- **The F\* handle registry mirrors the Lean one.** Same op names, same
  envelopes, same "unknown dataset handle" error, so `lib/api.js` serves both
  engines with one wrapper. One deliberate difference in behaviour, not shape:
  the F\* `datasetSerialize(h, "turtle")` uses the document's own prefixes.
- **`OWL_QueryRewrite` stays in the lite bundle** because the stateless query
  path applies `rewrite_query` today; leaving it out would make query
  semantics differ between profiles.
- **Vendoring.** The Valis Turtle files are MIT at upstream commit
  0aeec1cfcf07f4068f124774ecb08470406c52ae (the README sentence is quoted in
  `third_party/valis/PROVENANCE.md`); nothing from the upstream `src/` or
  `include/` (AGPL-3.0) enters this repository. The drum-machine engine
  JavaScript is the owner's clean-room work, reviewed element by element
  against the C++ in https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083.

## 3. Measurements

All from this container (4 cores, 16 GB), 2026-09-16, Node 22.22.2, js_of_ocaml
6.4.1, F\* 2025.12.15 with z3 4.13.3.

Bundle sizes (`gzip -9`):

| Bundle | Raw bytes | gzip bytes | Share of full |
|---|---:|---:|---:|
| `factoidal-npm-entry.js` (full) | 1,179,299 | 346,914 | 100 percent |
| `factoidal-npm-entry-lite.js` | 595,343 | 173,219 | 50 percent |

The lite bundle links 81 of the 188 extracted modules. The ten largest linked
units by bytecode size: `SPARQL11_Algebra`, `SPARQL11_Parser`,
`RDF_CottasStore`, `Parser_Turtle`, `OWL_Closure`, `Parquet_Footer`,
`Parser_NTriples`, `SPARQL_Protocol`, `RDF_Canonical`, `SPARQL11_Store`.
`RDF_CottasStore` and `Parquet_Footer` arrive through `SPARQL11_Store`'s
`dataset_backend` type and `OWL_Closure` through `OWL_QueryRewrite`; OCaml
links whole compilation units, and js_of_ocaml's dead-code elimination then
works inside them. Splitting those types out of `SPARQL11.Store` is the next
size lever (the foundational-core refactor in the 2026-07-05 record).

Query cost, 2,000 triples, a two-pattern join, median of 20 runs
(`bin/npm-entry/smoke.mjs`):

| Path | Full bundle | Lite bundle |
|---|---:|---:|
| Stateless `queryDataset` (N-Quads text each call) | 155.6 ms | 132.6 ms |
| `datasetQuery` on a handle | 58.9 ms | 53.6 ms |

Through the typed JavaScript API (`tests/perf/npm_handle_vs_stateless.mjs`,
2,000 triples, median of five runs, two runs): stateless `query()` 154.0 and
159.0 ms; `handle.query()` 68.3 and 65.7 ms; `parse()` 424 and 420 ms;
`openDataset()` 115 and 121 ms.

The report measured 160 to 190 ms per SELECT on 1,486 triples and 600 to 660
ms on 2,132 triples through the stateless path in Node.

F\* verification with the restored `.checked` cache: `RDF.Turtle.Serialize`
13 s, `Parser.Diagnostics` 14 s. The cache is partly stale
(`Parser.Combinators.fst` has changed since the snapshot), so the new
module's own `.checked` file was not written; a refresh of the
`checked-cache` branch is due at the next gates-green state.

## 4. Bundle granularity: the answer to the owner's question

The owner asked (2026-09-16) for "a lite module that only loads parser(s) and
rdf graph / sparql in memory datasets", whether "only the specific parsers we
need" is possible, whether both "core for everything or v finegrained chunks"
can exist, and what the best practice is.

- The engine bundles are whole-program js_of_ocaml outputs. Granularity is
  decided at link time: one artifact per profile, dead code removed per
  artifact. js_of_ocaml has no dynamic chunk loading, and every artifact
  carries the runtime floor (86 KB raw, 27 KB gzip, measured 2026-07-05).
- Per-parser chunks would each carry that floor, and the parsers are small
  next to the SPARQL evaluator and parser (about 610 KB of bytecode between
  `SPARQL11_Algebra` and `SPARQL11_Parser`). A consumer who only parses is
  served by the parse-only pilot's measured 40 percent, but such a consumer
  has not appeared; the report's consumer parses, queries, updates and
  serialises.
- Best practice on npm is subpath exports per profile with `sideEffects:
  false`, the sizes stated in the README, and the default export unchanged.
  Two profiles now: `@factoidal/core` (full) and `@factoidal/core/lite`. The
  build loop in `formal/fstar/build-ocaml.sh` makes a third profile a list
  edit plus an export table, when a measured need appears.
- The Lean engine's wasm (6.2 MB raw, 1.17 MB gzip) is one module; the same
  argument applies there.

## 5. Hub notebooks

- Cells closed by default: a fence flag (```` ```observable-js closed
  title="..." ````) carried to the page as `data-hub-cell-flags`; `mountCell()`
  wraps the cell in `<details>`; an error opens it. Library cells may sit at
  the end of a post because the page registers every declared name before
  mounting and the runtime orders cells by reference. Documented in
  `docs/web/hub/README.md` and post 47, pinned by `tests/hub/post47_test.mjs`
  and the headless sweep.
- Post 55 recreates the drum machine as a notebook: the same parses, queries,
  update and serialisation the reporting session ran, with timings and an
  `apiItems` probe whose booleans track items 1, 2 and 4 against
  `tests/hub/post55_expected.json`.

## 6. Costs paid and open items

- Two F\* agents each rediscovered that `bin/npm-entry-core/README.md`'s manual
  module list was missing ten files; the pilot directory is deleted, the lite
  entry supersedes it.
- The strict parse flipped `tests/hub/post31_test.mjs`, which pinned the old
  silent skip of RDF 1.2 syntax under the 1.1 parser; the post now shows the
  positioned rejection and the `turtle12` format.
- `formal/fstar/ocaml-output/RDF_Entailment_Regime.ml` was stale against its
  `.fst` (https://github.com/danbri/factoidal/issues/689), which aborted
  `build-ocaml.sh js` at the W3C runner; the module is re-extracted on this
  branch and the bundles rebuilt through the script.
- The native binaries under `bin/linux-x86_64/` are rebuilt by the CI shadow
  build on `claude/main`, not on this branch; until then the CLI `dump-turtle`
  prints the quoted literal form and fixture 4 of
  `tests/local/turtle_pretty_regressions.sh` is inactive.
- Lean parity (positioned errors, prefixes, `serializeTurtleWith`, shorthand)
  is pinned as expected failures in `npm/factoidal/test/l4-core.test.js`
  naming https://github.com/danbri/factoidal/issues/685.
