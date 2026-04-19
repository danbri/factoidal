# Wiring COTTAS/Parquet into the full Factoidal build — plan 2026-04-19

Companion to
[`2026-04-19-hdt-fstar-status.md`](2026-04-19-hdt-fstar-status.md),
which audits what's in F\* today. This note describes what it takes to
actually ship the ballyhoo binary-format stack — specifically the
F\*-verified Parquet parser and the COTTAS path that rides on top of
it — across native + js_of_ocaml + wasm_of_ocaml.

## Scope: what "full part of the system" means here

- Native OCaml: `./build-ocaml.sh` on `claude/main` produces a
  `factoidal` / `w3c_runner` that can `--data-cottas file.parquet`
  (or equivalent) and run SPARQL queries over the resulting quads.
- js_of_ocaml: `docs/fstar-extracted/factoidal.js` can load a Parquet
  file (via Fetch / HTTP Range) and query it in the browser.
- wasm_of_ocaml: the existing `build-ocaml.sh wasm` path grows the
  same capability, with a Zstd primitive available to the wasm binary.
- HDT via `hdtSearch` is explicitly *not* shipped to browser/wasm
  targets (it spawns subprocesses). Browser story is COTTAS-via-Parquet.
  Native can keep HDT optional-if-`hdtSearch`-is-on-PATH.

Out of scope for this plan:
- A verified F\* Zstd implementation. C stub stays.
- Parquet encodings other than DeltaLengthByteArray. Emitters we care
  about today use DLBA; others are a future extension in
  `Parquet.Footer.fst`.
- Parallel row groups, predicate pushdown, column statistics. The
  current probes are single-row-group / first-column-index. Enough
  for small COTTAS datasets; not enough to be competitive on big data.

## The starting position

What exists on `claude/main` (commit `8d4fa67`):

- Source files: `Parquet.Footer.fst` (1453 lines), five
  `Parser.Ballyhoo*.fst`, `SPARQL11.Store.fst`.
- Glue: `experimental_ocaml_glue/{ballyhoo_hdt_runtime.sh,
  cottas_runtime.sh, parquet_footer_runtime.sh, parquet_zstd_stubs.c}`.
- Stale pre-extracted `.ml` in `ocaml-output/` (mtime predates the
  `.fst` sources; won't match a fresh extract).

What's **missing** on `claude/main` but exists on
`origin/codex/ballyhoo-baseline`:

- `build-ocaml.sh` extract-list entries for the new `.fst` files.
- `build-ocaml.sh` `COMMON_MODULES` entries for the new `.ml` files.
- Any zstd linking / `parquet_zstd_stubs.c` compile step.
- js/wasm build integration for Zstd.

So the cherry-pick did source but not wiring. Plan is to finish the
job.

## Recalibration note on estimates

These estimates assume coding-agent-paced work (read-many-files-in-
parallel, cherry-pick hunks mechanically, run builds in background,
iterate on failures while other things continue). Human-paced would
multiply by ~3×. Also: the mechanical cherry-picks are fast and
reliable; the Zstd integration paths have genuine unknowns that
could eat a day if the obvious option turns out not to work.

## Phase 1 — Native restore (commit-sized)

**Goal:** `./build-ocaml.sh` on `claude/main` produces a factoidal
that can open a COTTAS Parquet file and return quads.

**Steps:**

1. Cherry-pick `build-ocaml.sh` hunks from
   `origin/codex/ballyhoo-baseline`:
   - Line ~71 `for fst in …`: add `Parquet.Footer.fst`,
     `Parser.Ballyhoo.fst`, `Parser.BallyhooBloom.fst`,
     `Parser.BallyhooHDT.fst`, `Parser.BallyhooHDTQ.fst`,
     `Parser.BallyhooCOTTAS.fst`, `SPARQL11.Store.fst`. Order
     matters — `RDF.Graph.Executable.fst` first, then
     `Parquet.Footer.fst`, then the Ballyhoo modules (HDT before
     COTTAS — COTTAS runtime glue calls `Parquet_Footer`), then
     `SPARQL11.Algebra.fst`, then `SPARQL11.Store.fst`.
   - Line ~101 `COMMON_MODULES`: mirror the ordering.
   - `ocamlfind ocamlopt` call: add `-package zstd` (or
     `-cclib -lzstd` + the C stub `.o`).
2. Compile `experimental_ocaml_glue/parquet_zstd_stubs.c` into a
   `.o` inside `build-ocaml.sh` compile step, link alongside the
   `.cmx` files. `ocamlfind ocamlopt` with `-cc cc -cclib -lzstd`
   and including `parquet_zstd_stubs.o` as a plain object.
3. Verify `ocaml-patches.sh` runs the three ballyhoo glue scripts
   in the right order: `ballyhoo_hdt_runtime.sh` →
   `cottas_runtime.sh` → `parquet_footer_runtime.sh`. COTTAS glue
   calls into `Parquet_Footer`, so the Parquet patch should land
   first; re-read both scripts to confirm the direction.
4. opam: add `zstd` (the `zstd` opam package is the bindings to
   libzstd; also needs the `libzstd-dev` system package on
   Debian/macOS-brew — already present on most CI setups).
5. Smoke test: one `examples/berlin_hdt_*.sh` script that uses a
   COTTAS artifact, runs end-to-end against a small fixture,
   returns the right row count.
6. Commit the binary to `bin/darwin-arm64/` per CLAUDE.md rule 9.

**Estimate:** 30 min–2 hours with an agent. The only thing that
can go wrong is zstd linking (opam version / system library
mismatch). Fallback: declare the C stub compilation optional and
gate Parquet support on it, so if libzstd is missing the build
still succeeds without Parquet rather than failing.

**Exit criterion:** a w3c_runner / factoidal that can answer
BGPs over a small COTTAS/Parquet file, with the same SPARQL pass
rate as the pre-ballyhoo build plus a new test or two exercising
the new path.

## Phase 2 — js_of_ocaml integration

**Goal:** `docs/fstar-extracted/factoidal.js` (and the npm package
built from it) can open a Parquet file and run SPARQL over it.

**Steps:**

1. Pick a JS Zstd library. Candidates: `fzstd` (BSD, ~20 KB,
   active), `zstddec` (LGPL, might be heavier), `numcodecs` (big,
   overkill). Default pick: `fzstd`.
2. Write a js_of_ocaml external primitive for
   `caml_parquet_zstd_decompress_hex` that mirrors the C stub's
   contract: take hex string + expected size, return decompressed
   hex or None. The primitive lives as a `//Provides:` block in
   a `.js` runtime file referenced from the `build-ocaml.sh js`
   step (pattern established by existing `fstar_int_stubs.js`).
   Implementation: hex→`Uint8Array`, call `fzstd.decompress`,
   `Uint8Array`→hex.
3. File I/O primitive. `parquet_read_tail_hex` / `_range_hex`
   currently do `open_in_bin` + `seek_in`. In js_of_ocaml this
   works for the virtual FS (files mounted via
   `Sys_js.update_file`), so local-file factoidal-js use cases
   work as-is. For remote Parquet URLs, add a separate
   `parquet_fetch_range_hex` primitive using browser Fetch with
   `Range:` headers. Wire it as an alternate path in the
   `parquet_footer_runtime.sh`-equivalent for js targets.
4. Bundle `fzstd` into the factoidal-js build. Either inline its
   source (10–20 KB) or load it via ES module import, depending
   on how the existing js build packages third-party JS.
5. Smoke test in a real browser: one existing factoidal demo
   page (`docs/fstar-extracted/index.html` is the demo) plus a
   new code path that fetches a small Parquet file and runs a
   SPARQL query over it.
6. Measure size impact on `factoidal.js`. Expected: +30–60 KB
   for fzstd + glue. If unacceptable, lazy-load fzstd only when
   a Parquet path is actually used.

**Estimate:** 2–6 hours with an agent. The bottleneck is step 2/3
if fzstd's hex↔bytes conversion is awkward or if the `Bytes` vs
`String` distinction in js_of_ocaml surfaces a snag. Step 4
(bundling) can be slow if the existing build pipeline is picky
about new dependencies.

**Known potential snag:** `Parquet.Footer.fst` is `nat`-heavy in
its varint / zigzag loops (same issue as Turtle parser — see
`2026-04-19-turtle-parser-speed.md`). In JS this extracts to
`zarith_stubs_js` bignum ops. Functionally correct but slow —
a few-MB Parquet file may take seconds to parse in the browser.
Not a blocker for Phase 2, but track it as a follow-on; the same
`pos_t` migration that helps Turtle would help here.

**Exit criterion:** a browser demo that loads a small Parquet
file (say, 100 KB) and runs a SELECT over it without timing out.

## Phase 3 — wasm_of_ocaml integration

**Goal:** `./build-ocaml.sh wasm` produces a wasm bundle that
includes Parquet/COTTAS capability.

Per CLAUDE.md, the wasm path is already partially working —
SPARQL suites like bind/bindings/aggregates pass identically to
native. The gaps are SHA/MD5 stubs (separate issue) and now
Zstd.

**Two options for Zstd in wasm:**

- **Option A (recommended first try):** same as Phase 2 — call
  a JS Zstd library through the wasm→JS bridge. `wasm_of_ocaml`
  supports external primitives via `.wat` + JS shim pairs (see
  CLAUDE.md mention of `janestreet/zarith_stubs_js`'s
  `(wasm_of_ocaml (wasm_files runtime_wasm.js runtime.wat))`).
  The `caml_parquet_zstd_decompress_hex` primitive gets a
  `.wat` stub that tail-calls into a JS function that runs
  fzstd. Cheap, identical semantics to Phase 2.
- **Option B (the purer path):** compile libzstd to wasm with
  emscripten and link it into the wasm_of_ocaml output. Gives
  wasm-bundle independence from JS. Cost: one-time emscripten
  setup (~½ day), possible size bloat (libzstd is ~200 KB
  wasm), and a build-system complication (wasm linker flags).

**Steps (assuming Option A):**

1. Write `wasm_runtime/parquet_zstd_stubs.wat` that exports a
   function matching the `caml_parquet_zstd_decompress_hex`
   contract, forwarding to JS.
2. Write `wasm_runtime/parquet_zstd_stubs.js` providing the JS
   side (same fzstd call as Phase 2; shared if layered right).
3. Reference both in `build-ocaml.sh wasm`'s linker flags,
   next to the existing Zarith runtime wiring.
4. HDT amputation. The wasm/js builds should NOT include
   `Parser_BallyhooHDT.ml` patched with `Unix.open_process_full`
   — that runtime dependency can't be satisfied in a browser.
   Two approaches:
   - (a) Don't extract/compile HDT for wasm targets. Requires a
     `COMMON_MODULES` split: `COMMON_MODULES_NATIVE` (with HDT)
     vs `COMMON_MODULES_BROWSER` (without).
   - (b) Provide a browser-side stub for `hdt_search` that returns
     empty results and logs a warning. Uglier but keeps one
     module list.
   Recommend (a); the code split follows a clean boundary.
5. Smoke test in a wasm runtime (browser or wasmtime).

**Estimate:** 4 hours–1 day with an agent, assuming Option A
works. Option B adds a day for emscripten integration.

**Known snag:** the hex-string memory ceiling. A 10 MB
compressed Parquet page becomes a 20 MB hex input to the Zstd
stub, and the decompressed output becomes a 2× larger hex string
back. In wasm's 32-bit address space (4 GB hard cap, browser
limits typically ~2 GB), this ceilings out at roughly 500 MB
decompressed data per call. Fine for COTTAS files up to that
size; catastrophic beyond. Worth measuring before promising
anything to users. Real fix would be chunked
`caml_parquet_zstd_decompress_hex_streaming`, which is a bigger
refactor of the F\*–C boundary.

**Exit criterion:** `./build-ocaml.sh wasm` produces a bundle
that answers the same SPARQL query over the same small Parquet
file as Phase 2, running under wasm_of_ocaml.

## Phase 4 — Tests, CI, docs

1. Add a COTTAS/Parquet fixture to `tests/` — a tiny Parquet
   file (say, 10 quads) committed as binary under
   `tests/fixtures/cottas/`. Document how it was generated
   (which emitter, encoding settings).
2. Add a single-file test that runs a SPARQL SELECT against
   that fixture through the factoidal binary.
3. GitHub Actions: ensure the CI image has `libzstd-dev` (or
   install it in the workflow).
4. Update docs:
   - `docs/designissues/cottas-native-backend.md` — drop the
     "no implementation yet" caveats, cross-link
     `Parquet.Footer.fst`.
   - `docs/designissues/2026-04-19-hdt-fstar-status.md` — remove
     the "build-wiring caveat" section once Phase 1 lands.
   - CLAUDE.md "Known Performance Issues" HDT workaround bullet
     — update to reflect that COTTAS-via-Parquet is now a real
     F\*-verified path.
5. Commit the platform binaries per CLAUDE.md rule 9.

**Estimate:** 1–2 hours.

## Total agent-time estimate

- Phase 1 (native): 30 min – 2 h
- Phase 2 (js): 2 – 6 h
- Phase 3 (wasm): 4 h – 1 day
- Phase 4 (tests/docs): 1 – 2 h

**Realistic plan-to-ship total: one agent-day, two at most** if
the Zstd-in-wasm path needs Option B or the hex-ceiling requires
a chunked primitive. Single-day outcomes are plausible if
Phase 3 uses Option A without surprises.

The big unknowns (in order of likelihood to bite):

1. **opam `zstd` binding compatibility** with the pinned F\*
   opam switch (Phase 1). If the binding's OCaml version
   requirements clash with `ocaml-base-compiler.4.14.1`,
   fall back to a lower-level `Ctypes` binding or a hand-rolled
   FFI. Adds ~2 hours.
2. **fzstd hex-encoding perf** (Phase 2/3). If turning a 10 MB
   compressed page into a 20 MB hex string via JS
   `TextDecoder`/`String.fromCharCode` tricks is too slow in
   practice, we need to bypass hex and pass `Uint8Array`
   directly, which means changing the F\* side to accept
   `FStar.Bytes` rather than `string` — a real refactor of
   `Parquet.Footer.fst`. Adds ~1 day. Defer unless measurement
   forces it.
3. **wasm Option A handshake** (Phase 3). If the `.wat` →
   JS-primitive wiring has some undocumented snag specific to
   `wasm_of_ocaml`'s current version, could eat a few hours
   debugging the bridge. Fallback is Option B (emscripten),
   which costs ~1 day but avoids the JS↔wasm bridge entirely.

## What this plan does not promise

- **Competitive performance on large Parquet files.** The
  hex-string trick, single-row-group limitation, and
  DeltaLengthByteArray-only coverage all cap what sizes are
  usable. Ceiling is probably tens of MB of compressed Parquet
  before the per-call cost becomes unworkable.
- **Full Parquet spec compliance.** Only the
  DeltaLengthByteArray encoding is supported. A Parquet file
  emitted by anything other than the specific COTTAS producer
  likely won't parse. Expanding encoding support is F\* work
  inside `Parquet.Footer.fst`, not build-plumbing work.
- **SPARQL `--data-parquet` as a generic flag.** The plan wires
  COTTAS-shaped Parquet (4 columns: subject, predicate,
  object, graph) into the Store layer. Generic Parquet-to-RDF
  mapping (arbitrary schemas, typed columns) is a separate
  project.

## Tracking

Candidate GitHub issue titles if/when this moves:

- "Restore Parquet/Ballyhoo build wiring on claude/main (Phase 1)"
- "Add fzstd-based zstd primitive for factoidal-js (Phase 2)"
- "Add wasm_of_ocaml zstd shim for factoidal-wasm (Phase 3)"
- "Tiny Parquet fixture + CI smoke test (Phase 4)"

Recommend opening them only once Phase 1 is in flight, so the
concrete shape of the commit informs the later issue text.
