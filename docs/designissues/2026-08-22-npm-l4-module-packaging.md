# npm packaging for two verified engines: F\* extractions + Lean 4 wasm

**STATUS UPDATE, issue #618 (2026-08-26): option A was chosen after
all.** Everything below through "Done 2026-08-25" is the ORIGINAL
design record (option B, the companion-package split) — kept in full,
unedited, as the record of why the decision changed; do not delete it
when reading further down. See "## 2026-08-26 (#618): the merge into
`@factoidal/core`, and why option A's rejection no longer holds" at the
end of this file for the current state, the premise that changed, and
the backend-selector spec built on top of it.

Owner request 2026-08-22: "Draft an l4 module of npm factoidal package
and scope out ways for the module to include both lean 4 and f\*
extractions without being a hideous bloated monolith." Workstream:
[#476](https://github.com/danbri/factoidal/issues/476); Lean tree:
[#466](https://github.com/danbri/factoidal/issues/466).

## What exists after this landing

`@factoidal/core` gains subpath **`factoidal/l4`** (`npm/factoidal/l4.js`
+ `l4.d.ts`, wired into `exports` and `files`): the Lean 4 engine under
the same package namespace as the F\* engines. It is a **thin resolver**,
~90 lines, no binary payload. Asset resolution, first hit wins:

1. companion package `@factoidal/lean` (not yet published — see below);
2. `$FACTOIDAL_L4_ASSETS` (a directory holding
   `l4factoidal.{js,mjs,wasm}`);
3. the repository checkout layout (`docs/web/hub/assets/l4/`).

Gate: `tests/hub/npm_l4_test.mjs` — 4 pass, 0 fail, including a
two-pattern join whose rows must equal the F\* engine's.

## The bloat question — sizes, measured 2026-08-22

| Artifact set | Bytes |
|---|---|
| Lean wasm (`l4factoidal.wasm` + Emscripten glue + loader) | 1,497,431 |
| F\* wasm_of_ocaml npm-entry (`.wasm.js` + assets dir) | ~1,493,000 |
| F\* wasm_of_ocaml CLI flavor (`factoidal.wasm.js` + assets dir) | ~1,406,000 |
| F\* js_of_ocaml bundle (`factoidal.js`) | 1,156,968 |
| `@factoidal/core` package dir today (all of the above F\* forms + HACL\* + lib) | 6.4 MB |

Bundling the Lean engine into core would add ~1.5 MB (+23%) paid by
every installer, most of whom want one engine.

## The three packaging options

**A. Bundle into `@factoidal/core`.** One install, no resolution logic.
Rejected as default: +23% tarball for a phase-1 ABI (BGP only), and the
Lean artifact revs on a different cadence (every `lean-toolchain` bump
forces a wasm rebuild — skills/lean4-wasm-export).

**B. Companion package `@factoidal/lean`, thin subpath in core.**
RECOMMENDED. The companion ships exactly the three wasm-side files plus
its own version.json (Lean toolchain hash, L4Factoidal git SHA — the
same claims-block pattern core's version.json uses). `@factoidal/core`
keeps `factoidal/l4` as the resolver (already written), so user code
never changes: `require('factoidal/l4')` works the moment the companion
is installed next to it. Core declares it as an **optionalDependency-
style suggestion in README only** — NOT `optionalDependencies` (npm
installs those by default, which is bloat through the back door), NOT
`peerDependencies` (installers get warnings for an engine they may not
want). Version coupling: core's `l4.js` reads the companion's
version.json and warns on a major mismatch.

**C. Download-on-demand.** Rejected: violates the self-contained/CSP
posture the hub already enforces, breaks offline installs, and makes
supply-chain review harder than a signed npm tarball.

## Non-monolith principles (apply to every future engine artifact)

1. **One engine per entry point.** Subpath exports (`.` / `./wasm` /
   `./l4`) are the unit of choice; no entry point imports two engines.
2. **Binary payloads live in leaf packages that rev with their
   toolchain**; `@factoidal/core` carries logic and resolution only.
   (The F\* wasm assets predate this rule; migrating them OUT of core
   into `@factoidal/wasm` is a candidate follow-up, listed in
   [#476](https://github.com/danbri/factoidal/issues/476), not done
   here.)
3. **Same-shape claims metadata everywhere**: every engine package
   ships a version.json stating source SHA, toolchain, and what is and
   is not verified.
4. **Differential parity is a gate, not a demo**: any subpath that
   exposes an operation both engines implement gets a test asserting
   equal results (the `npm_l4_test.mjs` join pin is the template).

## Benchmark: Lean wasm vs F\* wasm_of_ocaml vs F\* js_of_ocaml

Harness: `tests/perf/l4_vs_fstar_wasm_bench.mjs` (each engine in its own
Node process; init / ingest / query timed separately; query = median of
5 after warmup). Node v22.22.2, this container, 2026-08-22. Workload: K
people → 2K triples; two-pattern join `?s :name ?n . ?s :age ?a`.

| Metric | Lean wasm | F\* wasm_of_ocaml | F\* js_of_ocaml |
|---|---|---|---|
| init (module + runtime) | 57–64 ms | 51–55 ms | 78–85 ms |
| ingest 8,000 triples | 7.7 ms (JSON stringify — NOT a parse; see below) | 5,480 ms (Turtle parse) | 2,245 ms (Turtle parse) |
| query 200 triples | 5.7 ms | 6.2 ms | 16.3 ms |
| query 2,000 triples | 170 ms | 45 ms | 121 ms |
| query 8,000 triples | 2,891 ms | 205 ms | 577 ms |
| RSS after init | 16–21 MB | 22–90 MB (grows with data) | 26–70 MB |
| RSS after queries, 8k triples | 124 MB | 108 MB | 137 MB |

Readings, with their limits stated:

- **Ingest is not comparable across the columns.** The Lean ABI takes
  pre-built JSON triples (no parsing; the 7.7 ms is `JSON.stringify`),
  the F\* engines parse Turtle. The Lean tree HAS a verified Turtle
  parser now, but it is not behind the wasm ABI yet
  ([#476](https://github.com/danbri/factoidal/issues/476) item 2).
- **The Lean query column is quadratic** (5.7 → 170 → 2,891 ms as
  triples go 200 → 2,000 → 8,000). Cause, measured: the Lean evaluator
  joins by nested list scan, with no index. The F\* engine is the
  indexed path and stays ~14x faster at 8k triples; small graphs
  (≤ ~2,000 triples) are competitive either way. 🧭 Whether the Lean
  tree SHOULD acquire indexed joins — and prove the indexed evaluator
  refines the plain one, which is the interesting theorem — is an OPEN
  question for the owner, not a settled design point. An earlier draft
  of this file asserted the plain evaluator "must stay that way, by
  design"; no owner instruction said so (correction 2026-08-22, see
  the provenance note in skills/factoidal-lean-basics).
- **The F\* wasm_of_ocaml Turtle parse is 2.4x SLOWER than its own
  js_of_ocaml build** (5,480 vs 2,245 ms at 8k) while its query is
  2.8x faster (205 vs 577 ms). Worth its own profile before anyone
  "fixes" either number — recorded in
  [#476](https://github.com/danbri/factoidal/issues/476).
- Sizes are a wash: all three engines land at 1.1–1.5 MB.

## Done 2026-08-25 (superseding "Not done here")

The section that stood here said the ABI widening needed a build
machine this container could not hold. Both halves are done:
Emscripten 6.0.8 runs in the Linux container (first Linux build of
`build-wasm.sh`, four defects fixed at source — see the commits of
2026-08-24/25 and `skills/lean4-wasm-export` traps 5–8), and the
committed module now serves the ten-op dispatch ABI (`l4_call`) behind
`factoidal/l4-core`, with `@factoidal/lean` as the companion package
(`npm/factoidal-lean/`, mirrored to `docs/npm/lean/`).

### Size decomposition, measured 2026-08-25 (M1)

| Variant | Bytes | Note |
|---|---|---|
| BGP-only surface (targeted imports) | 1,448,306 | the floor: runtime + Init + the BGP closure |
| Full v1 dispatch surface | 3,510,827 | + five parsers, SPARQL 1.1/1.2 eval + update, four closures, RDFC-1.0 |
| v1 + Common Logic / IKL ops (measured 2026-08-25, Linux) | 3,598,886 | + `clParse` / `clToDataset` / `queryWithIklService` (`Wasm/Ops/CL.lean`, `L4Factoidal/CL/`) — ~88 KB over the v1 surface. The last two were deleted from the source on 2026-08-26 ([#626](https://github.com/danbri/factoidal/issues/626)); the rows below therefore measure a surface the tree no longer has |
| + dataset handles + x-ikl regime (measured 2026-08-25, Linux) | 3,866,580 | + `datasetOpen`/`datasetQuery`/`datasetUpdate`/`datasetSerialize`/`datasetClose` (`Wasm/Ops/Handles.lean`, [#585](https://github.com/danbri/factoidal/issues/585)) and the `x-ikl-*` regime module ([#581](https://github.com/danbri/factoidal/issues/581)) — ~261 KB over the CL row; abiVersion 0.2.0 |
| + OWL verdict ops (measured 2026-08-25, Linux) | 4,190,019 | + `owlIsConsistent`/`owlEntails` (three-valued, `OWL/Refute.tableauConsistent` + `OWL/NegationGoals.lean`, [#586](https://github.com/danbri/factoidal/issues/586)) — ~316 KB over the handles row |
| + content-addressed proposition naming (measured 2026-08-25, Linux) | 4,220,881 | + `CL/Alpha.lean` alpha-normalization and the content-addressed proposition graph names with the sentence-record triple — ~30 KB over the OWL row. The naming scheme is DELETED ([#626](https://github.com/danbri/factoidal/issues/626)); `CL/Alpha.lean` stays, for the IKL individuation condition |
| + graph-decoration CL translation (measured 2026-08-25, Linux) | 4,248,818 | + the CL-to-RDF projection rules and the `x-ikl-*` regime + SERVICE view, plus RDF 1.2 read mode in `queryDataset`/`updateDataset` — ~28 KB over the naming row. Everything in this row except the RDF 1.2 read mode is DELETED ([#626](https://github.com/danbri/factoidal/issues/626)) |
| + triple-term decoration + uniform conjunction (measured 2026-08-25, Linux) | 4,248,606 | ~0.2 KB under the previous row. This is the byte count of the COMMITTED artifact, and it is now ahead of its source ([#627](https://github.com/danbri/factoidal/issues/627)) — the projection it measures is deleted |
| `import L4Factoidal` umbrella | 4,534,258 | non-functional — its 374-module initializer chain dies under wasm32 |

Decision the table settles: ONE module, no payload split. The v1
surface costs ~2.1 MB over a ~1.4 MB floor that any split would pay
per module; the ~8 MB raw budget alarm is far off. Granularity is
API-level (npm subpaths over one memoised instance); the
`Wasm/Ops/*.lean` file-per-group layout and the single `l4_call`
export keep a later split mechanical if a future op group changes the
economics.

## 2026-08-26 (#618): the merge into `@factoidal/core`, and why option A's rejection no longer holds

Owner, 2026-08-26: "Can't our lean module be part of core, and
eventually we settle on lean vs fstar? We could add backend
args/switcher but it seems lean is already outshining fstar even if
fstar helped bootstrap the lean 4 port." Issue:
[#618](https://github.com/danbri/factoidal/issues/618).

### The premise that changed

Option A was rejected above for one stated reason: "+23% tarball for a
phase-1 ABI (BGP only)." That premise was true when it was written
(2026-08-22, `l4factoidal.wasm` ~1.4 MB, BGP-only). It is no longer
true:

- The ABI is not BGP-only. The "Done 2026-08-25" section above already
  records the widening through OWL verdicts and CL/IKL; the wasm now
  serves a **21-op dispatch surface** (`bin/linux-x86_64/l4factoidal
  ops`), 12 of which are wired into `l4-core.js`'s typed API (see the
  capability table below).
- The measured wasm is 4,248,606 bytes (the last row of the table
  above) — carrying its own weight for what it now does, not a
  disproportionate tax on a thin surface.
- `npm/factoidal` was already 6.4 MB and `npm/factoidal-lean` 4.2 MB
  before this landing; folding the latter into the former is a
  reorganization of where the bytes live, not new bytes.
- Non-monolith principle #2 above ("binary payloads live in leaf
  packages that rev with their toolchain") was already violated by
  core carrying the F\* wasm assets, flagged in this file's own text as
  predating the rule. Adding Lean's artifacts makes core consistent
  with what it already is, rather than newly monolithic.
- CLAUDE.md standing decision, owner 2026-08-24/26: "There are no
  users. Prefer the right structure to the compatible one" — the
  release-cadence annoyance (the Lean artifact revs with
  `lean-toolchain`) costs nothing with zero installers depending on the
  split today.

### What landed

`npm/factoidal-lean/{l4factoidal.js,l4factoidal.mjs,l4factoidal.wasm,version.json}`
moved into `npm/factoidal/l4-assets/` (identical bytes — `wasmSha256`
unchanged: `6593d0449b5905e5b02c1e32cf643238ef26a67589cb910158948dbf3798f58d`).
`l4.js`'s resolver ladder gained a new first-hit source ahead of the
existing three, so `require('factoidal/l4')` / `require('factoidal/l4-core')`
are unchanged for every existing call site:

1. this package's own `l4-assets/` (new, the normal case now);
2. the companion package `@factoidal/lean` (kept as a manual-override
   path, not deleted — see `npm/factoidal-lean/README.md`, now marked
   superseded);
3. `$FACTOIDAL_L4_ASSETS`;
4. the repository checkout layout (`docs/web/hub/assets/l4/`).

`version.json` claims stay in TWO files, not merged: `npm/factoidal/version.json`
(F\*, tagged `"engine": "fstar"`) and `npm/factoidal/l4-assets/version.json`
(Lean, tagged `"engine": "lean4"`), each pointing at the other in a
`note` field. `.github/workflows/npm-publish-lean.yml` is disabled by
default (a `workflow_dispatch` confirm phrase is required to run it) —
publishing the superseded package by accident is worse than not
publishing it at all.

### The backend selector (`factoidal/select`, `npm/factoidal/select.js`)

Owner ruling, 2026-08-26 (issue #618 comments
[1](https://github.com/danbri/factoidal/issues/618#issuecomment-5425162574),
[2](https://github.com/danbri/factoidal/issues/618#issuecomment-5425193280)):
a per-instance backend option with per-call override on at least the
`fn` flavour of the API; five values (`lean`, `fstar`, `lean1st`,
`fstar1st`, `slowcompareboth`); `lean`/`fstar` throw rather than
silently answer from the other engine; `lean1st`/`fstar1st` fall
through for functions the primary engine lacks, with an optional
override-function list; `slowcompareboth` runs both and compares.

`createSelector({backend, overrideFns})` returns an instance whose
methods (`parse`, `query`, `update`, `serialize`, `canonicalize`,
`owlClosure`, `owlIsConsistent`, `owlEntails`, `coreRdfsClosure`,
`shaclValidate`, ... and the generic `call(fnName, args, callOptions)`)
each take a trailing `{backend, overrideFns}` that overrides the
instance default for that one call. Three sub-questions the ruling left
for the implementation:

1. **Observability.** Every result is an envelope naming the answering
   engine: `{engine: 'lean'|'fstar', backend, value}` for the four
   single/fallthrough modes, `{engine: 'both', backend, agree,
   comparison: {method}, lean, fstar}` for `slowcompareboth`. A caller
   can always tell `lean1st` apart from `lean` by reading `.engine` on
   the result.
2. **`slowcompareboth` disagreement.** Returns both values with
   `agree: false` — a disagreement is a reportable finding, not a
   thrown error. `slowcompareboth` DOES throw in two other cases, kept
   distinct: (a) a capability precondition fails (either engine lacks
   the function — nothing to compare, `lean1st`/`fstar1st` exist for
   that case instead), or (b) the call itself throws on at least one
   side (an execution error, not a semantic disagreement; the thrown
   `Error` carries `.lean`/`.fstar` outcome records so both sides stay
   inspectable).
3. **"Same answer."** RDFC-1.0 isomorphism (reusing `fn.js`'s
   `equals()`, which already implements the cheapest-correct-path
   chain down to canonical-hash comparison) for anything Dataset-shaped
   — bare `Dataset` results, and the `ntriples`/`dataset`/`report`
   fields other results wrap one in. SPARQL SELECT bindings are
   compared as a **bag** (order-insensitive, duplicate rows
   significant — SPARQL results are bags, and RDFC-1.0 canonicalizes
   graphs, not solution bindings) with blank-node labels renamed to a
   stable per-side form first, documented as `method:
   'bag-of-bindings'` on the result so a caller can see which
   comparison ran. `serialize()` text is parsed back to a `Dataset` and
   compared the same isomorphism-aware way when it parses as N-Quads/
   N-Triples; other serialization formats fall back to a labelled
   strict-string comparison (`method:
   'strict-equality(non-nquads-text)'`) rather than silently guessing.

### The capability table (derived, not hand-written)

`select.capabilityTable()` computes this live from both engines'
`capabilities()` probes (`lib/api.js`'s `capabilitiesUncached()`,
itself `typeof <the real loaded entry object>[opName] === 'function'`
against each engine) — never a maintained list. Measured against this
repo's committed artifacts, 2026-08-26:

| Function | Lean | F\* |
|---|---|---|
| `canonicalHash` | yes | yes |
| `canonicalize` | yes | yes |
| `closeCottas` | no | yes |
| `coreRdfsCheck` | yes | yes |
| `coreRdfsClosure` | yes | yes |
| `csvwToRdf` | no | yes |
| `didKeyResolve` | no | yes |
| `graphs` | yes | yes |
| `jsonSchemaValidate` | no | yes |
| `jsonldFromRdf` | no | yes |
| `jsonldToRdf` | no | yes |
| `mathmlEval` | no | yes |
| `matrixDeterminant` | no | yes |
| `matrixOuterProduct` | no | yes |
| `matrixScalarProduct` | no | yes |
| `matrixVectorProduct` | no | yes |
| `openCottas` | no | yes |
| `owlClosure` | yes | yes |
| `owlEntails` | yes | yes |
| `owlIsConsistent` | yes | yes |
| `parse` | yes | yes |
| `query` | yes | yes |
| `queryCottas` | no | yes |
| `rdfsPlusClosure` | yes | yes |
| `rhoDfClosure` | yes | yes |
| `rhoDfFragmentCheck` | yes | yes |
| `rifEval` | no | yes |
| `rmlMap` | no | yes |
| `schematronValidate` | no | yes |
| `serialize` | yes | yes |
| `shaclValidate` | no | yes |
| `shexValidate` | no | yes |
| `sigmoidFormulaMathml` | no | yes |
| `sigmoidPoints` | no | yes |
| `tableauDlInconsistent` | no | yes |
| `tableauMaterialise` | no | yes |
| `toCottas` | no | yes |
| `toanDiff` | no | yes |
| `toanProduct` | no | yes |
| `toanSimplify` | no | yes |
| `toanSubst` | no | yes |
| `toanSummation` | no | yes |
| `update` | yes | yes |
| `vcEd25519SecretToPublic` | no | yes |
| `vcEd25519Sign` | no | yes |
| `vcEd25519Verify` | no | yes |
| `vcEddsaCreateFromCanonical` | no | yes |
| `vcEddsaVerifyFromCanonical` | no | yes |
| `vcSha256Hex` | no | yes |
| `xformsRecalc` | no | yes |
| `xmlWellformed` | no | yes |
| `xpathEval` | no | yes |
| `xsltTransform` | no | yes |

F\* is a strict superset on this typed-API surface today: 15 functions
both engines answer, 39 that only F\* does, 0 that only Lean does. This
is a statement about the **npm typed-API wrapper surface** in
`lib/api.js`, not about the Lean engine's total capability — the raw
wasm has 21 ops (see below), and the parity ledger referenced from
issue #618 (SPARQL 1.1, ShEx, OWL RL+DL, RIF Core, XSLT, GRDDL,
JSON-LD, CSVW, JSON Schema, entailment regimes) shows Lean matching or
leading F\* on several suites at the engine-conformance level even
where no typed npm wrapper exists yet for that surface. Filling in the
remaining parity-ledger rows (SHACL, VC/DID, GeoSPARQL, RDFC-1.0) is
issue #618 work item 4, out of scope for this npm-packaging landing.

### CL/IKL and the dataset-handle ops: 9 of 21 unwired, for two different reasons

Owner, 2026-08-26 (same issue, scope-change comment): "I don't want npm
code for direction b at this stage, unless for the shape of ikl which
is the subset we get mapping rdf into ikl. But ikl doesn't have shapes
or named profiles. Take it out of npm for now."

`clToDataset` and `queryWithIklService` were withheld from the npm
typed-API surface by that decision, and are now DELETED from the engine
source entirely ([#626](https://github.com/danbri/factoidal/issues/626)):
they went through `CL/ToRdf.lean`, whose content-addressed proposition
graph names were never asked for. `clParse` was never part of that
family — it reads CLIF and produces no RDF — and is wired.

`lib/api.js`'s `query()` (the shared choke point for `index.js`,
`l4-core.js` and `select.js`) and `fn.js`'s `entail()` both still
reject any `entail` value matching `/^x-ikl/i` explicitly, independent
of the `ENTAIL_VALUES` whitelist, so a later whitelist edit cannot
reopen this without a deliberate second look. The Lean engine no longer
defines an `x-ikl-*` regime either, so the JS check is where the name
is answered. Pinned by regression tests in `test/select.test.js`.

The committed wasm artifact still EXPORTS both deleted ops: it was not
rebuilt in that landing (emsdk absent). Tracked in
[#627](https://github.com/danbri/factoidal/issues/627), and recorded in
the three Lean `version.json` files under `sourceDrift`.

`datasetOpen`/`datasetQuery`/`datasetUpdate`/`datasetSerialize`/
`datasetClose` are the other 5 of the 9 unwired ops — ordinary RDF
dataset handles, explicitly NOT covered by the owner decision above.
They stay unwired only because `lib/api.js` has no typed-wrapper shape
for a stateful handle yet (every existing typed op is request/
response); wiring them in is a reasonable follow-up, not a ruling to
revisit.

### Gates

`npm test` (`npm/factoidal`): 235 pass, 0 fail, 1 skip, 1 todo (out of
237) — includes the pre-existing suite plus 28 new selector tests
(`test/select.test.js`) and 4 new `.d.ts`-drift tests. `node --test
tests/hub/npm_l4_test.mjs`: 4 pass, 0 fail (unchanged).
