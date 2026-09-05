# Changelog

## 0.7.0 — 2026-09-05

**Wire version 10.** The command and `bin/store.mjs` read a generation
packed at `--layout ibk5`: out-of-line literals, RDF 1.2 triple terms and
directional literals, and per-entry zone maps.

### Out-of-line literals

A literal above 65,536 UTF-8 bytes is stored as one `blob-<sha256
hex>.lit` file beside the block, committed by the manifest blob table.
The block holds only the byte extent and the digest, so a host must fetch
the blob as well as the block:

- `storeQueryPlan` lists them under `blobKeys`, after `keys` and
  `sidecarKeys`, and counts their bytes in `bytes`;
- `queryStore` and `openStoreHandle` fetch them without a flag;
- a blob that is absent or whose bytes hash differently REFUSES the
  query by name. Nothing is answered with a shortened literal.

A store handle resolves every blob ONCE, at `storeOpen`, and the open
envelope reports how many. The two candidate-filter indexes keep an
out-of-line literal in every candidate set, so `CONTAINS` over a
70,000-byte literal and `geof:sfIntersects` over a polygon above the
ceiling both answer their rows.

### RDF 1.2 terms

A triple term and a directional language literal are stored and read
back. Wire version 9 refuses both.

### Zone maps

Each manifest entry carries the first 64 bytes of the smallest and the
largest subject key and object key of its block. A query with a constant
subject or object skips every block whose range cannot hold it, from the
manifest alone. `storeQueryPlan` reports the count as `zoneExcluded`, and
`factoidal inspect` prints the bounds beside each entry.

### Unchanged

Wire version 9 and earlier answer exactly what they answered before: no
manifest below version 10 carries a blob table or a zone map, so
`blobKeys` is empty and `zoneExcluded` is zero for them.

## 0.6.0 — 2026-09-05

**A full-text index, a geometry index, extension functions from
JavaScript, and a planner that no longer reads the whole store for a
`REGEX`.** Measured end to end on the largest corpus we have: 7,315,251
quads over 204 named graphs, 3,286 blocks, a 1.0 GB generation, queried
through a store handle on plain `node` with no flags.

| search | rows | time |
|---|---|---|
| `water` | 5 | 645 ms |
| `glacier` | **0** | 670 ms |
| `bicycle` | 2 | 617 ms |

A miss costs what a hit costs, because both are index lookups.

### The planner stopped reading the whole store

`REGEX`, `REPLACE`, `IRI()`, `NOW()`, the digest functions, aggregates in
a filter position, the triple-term accessors and every SPARQL 1.1
section 17.6 extension call each made the planner abandon predicate
selection and take every block in the manifest. On a 119-block store a
`REGEX` filter selected 119 artifacts where the same query with
`CONTAINS` selected 1.

The test was `Expr.backendLocal`, which answers a different question: may
the backend evaluate this expression, or must it materialise and
delegate. The right test is `Expr.existsFree` — `Expr.existsPat` and
`Expr.notExistsPat` are the only constructors carrying a pattern, so an
exists-free expression reads no triple whatever functions it calls. A
FILTER may narrow a plan or leave it alone; it must never widen it.
`EXISTS` and `NOT EXISTS` still widen, correctly.

### LGI1, a character-gram literal index

The packer writes a `.lgi1` sidecar beside each block and the planner
uses it where the query shape allows. It holds character 3-grams of the
case-folded lexical form and is a CANDIDATE FILTER, never a decider: it
answers a superset and the engine re-evaluates the original `FILTER`, so
the rows are the scan's rows. Tokens would not do, because `CONTAINS` is
a substring test and "underwater" contains "water" without being the
token "water".

Falls back to a scan, silently and correctly: a needle under 3
characters, a variable needle, `REGEX`, `UCASE`, `!CONTAINS`, `CONTAINS`
under `||`, a filter on a variable not bound in object position, and any
generation without the sidecar. Costs about 55% of the block bytes.

### GBI1, a geometry bounding-box index

The same construction for `geof:`. Five of the six topological functions
are filtered by a box — `sfIntersects`, `sfWithin`, `sfContains`,
`sfTouches`, `sfEquals` — at 74 to 94 times a scan, with a miss at 82
times. **`sfDisjoint` is refused** and falls back: it accepts exactly the
rows a box can exclude, so a box test inverts and would drop answers.

### Extension functions, from JavaScript, on the Lean engine

`registerExtensionFunction` reaches the Lean engine and the persisted
store, not only the in-memory F* path. Section 17.6 semantics are gated:
an unregistered IRI is unbound in SELECT and drops the row in FILTER, a
registration never overrides a built-in family, and `geof:` still
answers from the built-in table. Synchronous only; async is designed and
deferred.

### A handle is bounded by retained bytes

`storeOpen` was capped at 64 artifacts, inherited from the stateless path
where every query re-read and re-decoded its blocks. A handle pays that
once, so a count was the wrong shape — 257 small blocks may cost less
than 4 large ones. The cap is now 134,217,728 retained bytes, derived
from a measured 16.2 bytes resident per retained byte against half the
wasm32 address space, and the check runs BEFORE the read rather than
after hashing and decoding the whole set. A corpus-wide handle over 257
blocks and 741,179 rows now opens.

### Named graphs pack at scale

Blocks cut at graph boundaries, so `GRAPH <iri>` with a constant
predicate reads one block and the graph filter is exact rather than
conservative. Packer peak memory fell 32.6% and dictionary duplication
is 2.57%. No new wire version was needed: SBM7 already admitted several
entries per predicate.

**A large store no longer needs `node --stack-size`.** Several engine
paths recurse once per manifest entry and once per row, and on a
7,315,251-quad collection of 3,286 blocks `storeQueryPlan` alone
overflowed the default call stack of Node, before an artifact byte was
read ([issue 653](https://github.com/danbri/factoidal/issues/653)).

- New `@factoidal/core/store-worker`: `openStoreHandleOnWorker` holds the
  engine and the handle on a `worker_threads` thread with a raised stack.
  A handle is state inside the wasm instance and an instance does not
  cross a thread boundary, so the handle lives there and `query()` and
  `close()` are messages to it. One thread per session, many handles per
  thread. Every call is asynchronous; the synchronous `openStoreHandle`
  is unchanged.
- `factoidal query` still runs IN PROCESS, so a one-shot query pays
  nothing for a worker it would drop. It runs again on a worker only when
  the runtime runs out of frames — under Deno by re-executing itself with
  a raised V8 stack, which needs `--allow-run` and `--allow-env`.
  `--no-worker` turns the retry off.
- Measured: the worker costs about 110 ms once (thread start plus a
  second engine load) and under a millisecond per query after that.
  Deno's `worker_threads` shim does not raise the stack (10,835 frames
  by default, 13,837 at `stackSizeMb` 64, against Node's 41,195 and
  696,555), so a Deno library caller gets an in-process handle behind the
  same interface and starts its process with
  `--v8-flags=--stack-size=65536`.

### Fixed

- `openStoreHandle` with no options failed on any IBK3 generation with
  `artifact 'predicate-0.ibk3.sri2' is not declared by this manifest`.
  Two engine operations disagreed: `storeManifestInspect` reports
  `subjectIndex`, `termIndex` and `objectIndex`, while the handle's
  admission accepted only the block, `literalIndex` and `geoIndex`. One
  list now serves both.
- The README named GeoSPARQL functions that do not exist and said a text
  index was "separate work". Both corrected, with the shapes that fall
  back to a scan listed.

### Known limits, measured

- Ingest is about 2,180 quads per second and peak memory is 2.07 times
  the source, so a 142 GB corpus is not importable at that ratio. Making
  memory flat is a wire change and is not done.
- The quad packer streams N-Quads only; Turtle and TriG are buffered.
- `ORDER BY ... LIMIT n` still overflows above about 14,576 materialised
  rows. https://github.com/danbri/factoidal/issues/653
- The manifest is at version 9. Older generations still read.

## 0.5.1 — 2026-09-04

**A store can be opened once and queried many times.** `storeQuery` is
stateless: it re-reads, re-verifies and re-decodes the block on every
call, so a chat bot or a server paid the full cost for every question.
The new handle pays it once.

Measured on a 141-graph store, `skos:prefLabel` block of 5,571,302 bytes
and 45,806 rows, a DIFFERENT search string every query, load 10:

| | stateless | handle |
|---|---|---|
| first query (open + query) | 1,376 ms | 1,363 ms |
| second query, different string | 1,376 ms | **95 ms** |
| tenth query, all different | 1,382 ms | 103 ms |
| ten queries, total | 13,962 ms | **2,277 ms** |

```js
import { openStoreHandle } from '@factoidal/core/store'
import { loadEngine } from '@factoidal/core/engine'
const engine = await loadEngine()
const store  = await openStoreHandle(engine, '/path/to/store')
const a = store.query('PREFIX skos: … SELECT … ')   //  95 ms
const b = store.query('PREFIX skos: … SELECT … ')   //  95 ms
store.close()
```

**What it buys**: the per-query SHA-256 verification, block decode,
dataset build and index build all happen once. **What it does not buy**:
`CONTAINS` still scans every retained row, so cost stays proportional to
row count. This is not a search fix. There is still no inverted index.

⚠️ **Memory.** A held-open handle is about 170 MiB resident, of which
roughly 94 MiB is the decoded form of that 5.5 MB packed block — about
17 times the packed size. Query evaluation peaks at 346 MiB. A process
holding several stores should watch this; `storeHandleList` reports each
handle's retained bytes and rows.

**For a long-lived process**: several stores may be open at once, keyed
independently. `storeOpen` REFUSES at its cap and never evicts another
caller's handle — an eviction policy is a host decision and is not
implemented. The WebAssembly module is single-threaded, so a host must
queue overlapping calls; use one module instance per worker thread for
concurrency. A server would still need a re-open path when a generation
is replaced on disk, and delta-log overlay support: this path serves the
manifest's committed artifacts only.

Handle answers are gated against the stateless path by comparing ROWS,
not row counts, in `tools/wasm-store-query-smoke.sh` and
`Wasm/native-smoke.sh` (85 pass, 0 fail, out of 85; was 79).

## 0.5.0 — 2026-09-04

**Queries against a persisted store are about six times faster.** Measured
end to end the way a caller runs them — process start, engine load,
digest verification, block decode and scan — on a 141-graph store with a
5,571,302-byte `skos:prefLabel` block of 45,806 rows, at the same machine
load:

| query | 0.4.0 | 0.5.0 |
|---|---|---|
| `CONTAINS` over labels, `LIMIT 8` | 12.03 s | **2.06 s** |
| the same for a second word | 12.18 s | **2.04 s** |
| the same for a third | 11.96 s | **2.02 s** |

Two causes, both fixed.

- **A quadratic byte copy in SHA-256.** `Crypto.processBlocks256` copied
  the whole remaining message once per 64-byte block, so verifying an
  artifact was quadratic in its size. Fitting `t = c*n^k` to the
  admission step gave k = 2.08 before and **k = 0.98 after**. On the
  three blocks of that store, admission went 1,179 / 2,150 / 11,069 ms to
  303 / 413 / 872 ms. Decode and evaluation were linear throughout.
- **`LIMIT` was not pushed down through `GRAPH`.** A `LIMIT 8` cost what
  a full count cost, because `GRAPH ?g { ... }` fell through to the
  reference evaluator over the whole materialised dataset. The push-down
  now takes one `GRAPH` layer with a constant IRI or a variable.
  `ORDER BY`, `OFFSET`, `DISTINCT`, `REDUCED`, `GROUP BY`, `HAVING`,
  `VALUES` and aggregates still reject, two of them pinned by theorems.
- A `RangeError: Maximum call stack size exceeded` on `SELECT ... LIMIT 8`
  is gone with it, because the query no longer materialises 45,806 rows
  to return eight.

**A correctness fix found while measuring.** The pre-existing bare-BGP
`LIMIT` push-down could answer SHORT: a repeated variable (`?x ?p ?x`) or
an RDF-star triple term let the backend stop early on rows the match then
rejected. It now refuses both shapes.

**New exports.** `@factoidal/core/store`, `/pack` and `/engine`. A caller
can drive the store in process instead of spawning the command:

```js
import { openStore, queryStore } from '@factoidal/core/store'
import { loadEngine } from '@factoidal/core/engine'
const engine = await loadEngine()
const store  = openStore('/path/to/store', null)
const { result } = queryStore(engine, store, 'PREFIX skos: ... SELECT ...')
```

**The engine carries a day of OWL work**: OWL RL 1,181 pass, 266 fail
(out of 1,457) and OWL DL about 1,326 pass, 121 fail (out of 1,457), both
against a conclusion check corrected to require one functional blank-node
mapping (RDF 1.1 Semantics §1.5 and the interpolation lemma). A false
clash was removed — the materialiser had minted one existential witness
for several obligations, so the engine denied three consistent
ontologies; ConsistencyTest went 758 pass, 4 fail to 761 pass, 1 fail.

**Named graphs now pack at scale.** The IBK4 quad path read the whole
source file and a 553 MB, 194-graph corpus could not be packed at all. It
streams now, and a quadratic term that only named graphs paid — a hash
map copied per quad in `addQuadFast` — is gone. Peak memory per source
byte fell from 37 and 20 to between 7.4 and 11.4; a 316,816,934-byte,
194-graph input that used to fail now packs in 750 s at 2.34 GB. Byte
identity with the previous packer holds by theorem, not only by diff.

**Documentation corrected.** The GeoSPARQL section named functions that
do not exist. Six topological functions are implemented — `geof:sfEquals`,
`sfDisjoint`, `sfIntersects`, `sfTouches`, `sfWithin`, `sfContains` — and
they work against a persisted store, verified. There is no
`geof:distance`, `buffer`, `envelope`, `boundary`, `convexHull`, no
`relate` with a DE-9IM matrix, no CRS handling beyond the WKT literal and
no GML. Full text is SPARQL 1.1's own `CONTAINS` / `STRSTARTS` / `REGEX`,
evaluated per row after a block decodes: **there is no inverted index**.

Known limits, measured:

- A query is still O(rows) per search string, and nothing is retained
  between queries: `storeQuery` re-reads, re-verifies and re-decodes the
  block every call. A store handle that decodes once is the next step.
- `ORDER BY ... LIMIT n` still overflows the call stack above about
  14,576 materialised rows.
  https://github.com/danbri/factoidal/issues/653
- `update` and `compact` still exit 3.
  https://github.com/danbri/factoidal/issues/641
- A query plan is refused above 64 artifacts, 8,388,608 blob bytes or
  100,000 rows. https://github.com/danbri/factoidal/issues/648
- The two SHA-256 folds are checked equal by the FIPS 180-4 build-time
  guards and the HACL* differential, not proved.

## 0.4.0 — 2026-09-04

The package builds a store of its own. `pack` and `activate` join
`inspect` and `query`, so `npm install @factoidal/core` gives a complete
RDF store — import, activate, query — with no native binary on the
machine. https://github.com/danbri/factoidal/issues/641

- **`factoidal pack INPUT OUTPUT`** builds one immutable Shardborough
  generation from a Turtle, TriG, N-Triples or N-Quads file, streaming
  it in 65,536-byte chunks through the Lean engine's WebAssembly module.
  The generation is BYTE-IDENTICAL to what the native
  `l4block-shard-pack` writes: `diff -r` is empty for the `ibk3` triple
  layout and for the `ibk4` quad layout, on inputs up to 888,949
  triples. `--layout ibk3|ibk4`, `--syntax`, `--base`.
- **`factoidal activate STORE GENERATION`** verifies every artifact
  against the SHA-256 the manifest commits, and every cross-artifact
  relation, then replaces `CURRENT` atomically. A generation that fails
  verification never becomes current.
- **`factoidal sample-store`** prints the path of a store this package
  now carries, so a fresh install answers a SPARQL query with nothing
  else to download: 4,434 triples in 13 predicate blocks, five IPTC
  NewsCodes vocabularies under CC BY 4.0. Also exported as
  `@factoidal/core/sample-store`. See NOTICE.
- The engine gained a raw byte path out of the module
  (`l4_call_blob_io`), so artifact bytes cross the boundary with no
  encoding. Hexadecimal doubled them; base64 was refused. Measured on
  the read path: 242,416 bytes and 96 ms hexadecimal against 4,893 bytes
  and 70 ms raw.
- The pack hashes with HACL* SHA-256, the same primitive the native
  packer uses. It hashed with the pure Lean SHA-256 in development,
  which cost 3.3 times: 104 s against 31 s on 888,949 triples. Now at
  parity, 29.24 s against the native packer's 29.38 s.
- `packBegin` takes a base IRI, defaulted by the command to
  `file://<input>` so relative IRIs resolve exactly as the native packer
  resolves them. `--base ''` asks for no base, which makes a relative
  IRI a parse error rather than a silently different term.
- `pack` on a syntax the streaming fold cannot read now says so by name
  rather than raising an unhandled error.
- `store-host` gained `readChunk` (a short read means end of file, not
  an error), `writeNew` (create and fsync, refusing an existing file so
  a name collision in a generation is reported) and `makeDirectory`, on
  Node and on Deno both.
- `factoidal activate` runs on the raised stack too. Verification decodes
  the same blocks the pack encoded, so it recurses as deep; the worker was
  given to `pack` alone at first, and a 112,742-row generation packed
  successfully and then failed to activate with `Maximum call stack size
  exceeded`, leaving a store that could be built and not opened. Found by
  installing the tarball and running the command, which is why that step
  is in the release procedure. `tests/store-host/cli.mjs` now gates
  pack-then-activate on both runtimes.
- `factoidal pack` no longer needs a runtime flag. The pack fold recurses
  deeper than either runtime's default call stack allows, so an input
  above roughly 0.5 MB ended with `Maximum call stack size exceeded`
  (https://github.com/danbri/factoidal/issues/649). Under Node the pack
  now runs on a `worker_threads` worker with a 64 MiB stack; under Deno
  the command re-executes itself once with
  `--v8-flags=--stack-size=65536`, which needs `--allow-run` and
  `--allow-env` in addition to `--allow-read` and `--allow-write`.
  `gene.ttl`, 17,363,312 bytes and 888,949 triples, packs on the default
  stack of both runtimes, byte-identical to `l4block-shard-pack`.
  `--no-worker` forces the in-process path, which still reports the
  frame budget and the flag that raises it rather than crashing. A
  browser tab has a fixed frame budget and no flag, so this does not
  make an in-page packer possible.

Known limits, measured:

- `update` and `compact` still exit 3. The delta-log operations are
  stage 4 of https://github.com/danbri/factoidal/issues/641.
- The `ibk4` quad layout reads the whole source rather than streaming,
  because a quad block commits a graph-set summary over the entire
  input. The wasm packer refuses a quad file above 128 MiB.
  https://github.com/danbri/factoidal/issues/650
- A query plan is refused above 64 artifacts, 8,388,608 blob bytes or
  100,000 rows. https://github.com/danbri/factoidal/issues/648
- Packing in a browser tab is limited to about 7,800 distinct terms in
  one block, whatever the file size, and no host flag raises it.
  https://github.com/danbri/factoidal/issues/647

## 0.3.0 — 2026-09-03

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
