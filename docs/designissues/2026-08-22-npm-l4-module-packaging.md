# npm packaging for two verified engines: F\* extractions + Lean 4 wasm

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

## Not done here (needs Emscripten; this container cannot hold it)

Widening the Lean wasm ABI beyond `l4_bgp_query` — Turtle parsing,
RDFC-1.0 canonicalization, rdfs-core closure, isomorphism check,
SHA-256 — so hub post 36 (and `factoidal/l4`) can show the breadth of
`formal/lean4`. Export list, per-export steps, and the build-machine
requirement are scoped in
[#476](https://github.com/danbri/factoidal/issues/476). Hub cells must
NOT call exports the committed wasm lacks (anti-pattern #28), so the
page grows only when the rebuilt artifact lands with it.
