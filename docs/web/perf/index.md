---
title: Performance hub
layout: base.njk
---

# Performance hub — one engine, four extraction targets

The F\* specification extracts to four executable forms: native OCaml
(`bin/<platform>/factoidal`), js\_of\_ocaml (JavaScript, runs in Node
and browsers), wasm\_of\_ocaml (WasmGC, needs Node ≥ 22 or a recent
browser), and KaRaMeL C (today: the delta-log module family only, not
the full engine). This page answers "how do those four compare on the
same work" — a **runtime-vs-runtime** axis. The
**engine-vs-engine** axis (factoidal vs Jena vs pyoxigraph vs rdflib)
is a different question, measured in
[the competitive benchmark](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-06-competitive-benchmark-results.md);
correctness scores live on
[the test-results dashboard]({{ '/test-results/' | url }}).

Every number below is a median of 3 runs (wall-clock seconds), each
run capped at 600 s, measured 2026-07-06 at commit `ea87334` on the
machine described under Methodology.

## The short answers

- **Native OCaml is the fastest runtime on every SPARQL query shape
  measured** — between 2.3× and 23× faster than the Node-hosted
  runtimes, with the gap widening on aggregation at 1M triples.
- **Except parsing: wasm\_of\_ocaml parses Turtle faster than the
  native binary** — 0.47 s vs 0.63 s at 100k triples, 4.08 s vs
  6.46 s at 1M (verified, correct triple counts). WasmGC under
  Node 22's V8 is a serious runtime.
- **wasm\_of\_ocaml generally beats js\_of\_ocaml** — 5.7× on parse,
  2.4× on GROUP BY, 2.5× on regex at 100k; the exception measured is
  full-scan COUNT at 1M (35.4 s wasm vs 25.1 s js).
- **KaRaMeL C (delta-log micro-bench only) is the fastest native form
  of that module** — 1.6× faster than the extracted-OCaml native
  binary at N=10,000 entries.
- **KaRaMeL C compiled to wasm32-wasi runs correctly and tracks
  C-native within about 1.0–1.4× per phase at small sizes, then falls
  off a cliff** (48× slower parse at N=10,000, near its stack
  ceiling). On today's evidence the C→wasm pathway is **not** a
  shortcut to a faster full-engine wasm — see the C→wasm section.

## Methodology

- **Commit measured:** `ea873340202c5f0edf34dfd9a253d7713c4f6e93`
  (committed native binaries and committed js/wasm bundles; the bench
  drivers were added by the same change that adds this page).
- **Machine:** Intel(R) Xeon(R) Processor @ 2.10GHz, 4 logical cores,
  15 GB RAM (cloud sandbox). Node v22.22.2, OCaml 4.14.1 (fstar opam
  switch), gcc 13.3.0, clang 18.1.3.
- **Harness:** [`tools/bench-runtimes.sh`](https://github.com/danbri/factoidal/blob/claude/main/tools/bench-runtimes.sh)
  — rerunnable end to end; raw machine-readable output at
  [`docs/test-results/runtime-bench.json`](https://github.com/danbri/factoidal/blob/claude/main/docs/test-results/runtime-bench.json).
  Median of 3 runs per cell via bash `EPOCHREALTIME`; `timeout 600`
  per run; a cap trip is recorded as a skip, never silently dropped.
  Peak-RSS numbers use
  [`tools/bench_rusage_run.py`](https://github.com/danbri/factoidal/blob/claude/main/tools/bench_rusage_run.py)
  (`getrusage(RUSAGE_CHILDREN)`; `/usr/bin/time -v` is not installed
  in this sandbox). Four delta-log rows (the `ocaml-native` rows and
  `c-wasm` N=10,000) were re-measured manually with the identical
  protocol minutes after the main run, following a harness build bug
  fixed in the same commit — flagged in the JSON's `notes` field.
- **Fixture:** synthetic multi-predicate Turtle (each entity carries
  `rdf:type` + `foaf:name` + `ex:dept` cycling 20 buckets +
  `foaf:knows` ring edge) at 100,000 and 1,000,000 triples, generated
  deterministically by the harness. Synthetic because no suitably
  large real corpus is checked into the repo
  (`third_party/data/ukparliament/` ships query text + readme only;
  the demo `.ttl` samples are under 50 lines) — same precedent as
  `tools/bench-parse-serialize.sh`.
- **Commands measured:** the identical CLI on all three runtimes
  (the js/wasm bundles ship the same F\*-extracted `factoidal_cli`
  driver the native binary links):
  - parse: `<runtime> count multi-N.ttl`
  - query: `<runtime> query --data multi-N.ttl --query <q>.rq -o json`

## Full engine: native vs js_of_ocaml vs wasm_of_ocaml

Wall-clock includes process start-up, Turtle parse, index build where
the query needs one, query evaluation, and JSON serialization — the
end-to-end "run this query from a shell" cost. Node process +
bundle-load overhead is roughly 0.1 s (js) / 0.3 s (wasm) per
invocation, so it does not explain the gaps.

At 100,000 triples (median of 3 runs, seconds):

| Operation | native | js_of_ocaml (Node) | wasm_of_ocaml (Node) |
|---|---:|---:|---:|
| Turtle parse (`count`) | 0.63 | 2.66 | **0.47** |
| `SELECT (COUNT(*) …)` full scan | **0.63** | 2.58 | 2.61 |
| 2-pattern join + FILTER | **14.92** | 38.54 | 34.62 |
| GROUP BY + COUNT (20 groups) | **1.71** | 7.40 | 3.11 |
| regex FILTER on names | **1.74** | 7.09 | 2.85 |

At 1,000,000 triples (median of 3 runs, seconds; each run capped at
600 s):

| Operation | native | js_of_ocaml (Node) | wasm_of_ocaml (Node) |
|---|---:|---:|---:|
| Turtle parse (`count`) | 6.46 | 26.43 | **4.08** |
| `SELECT (COUNT(*) …)` full scan | **6.59** | 25.13 | 35.35 |
| 2-pattern join + FILTER | >600 s (skip) | >600 s (skip) | >600 s (skip) |
| GROUP BY + COUNT (20 groups) | **20.91** | 484.20 | 270.29 |
| regex FILTER | not attempted (time budget) | — | — |

Readings:

- **Queries: native wins everything, 2.3×–23×.** The gap is smallest
  on the join (2.3× vs wasm at 100k) and largest on GROUP BY at 1M
  (23× vs js, 13× vs wasm).
- **Parsing: wasm beats native**, at both sizes (0.74× and 0.63× of
  native's time). The parse-only path through WasmGC is faster than
  the statically-linked OCaml native code on this machine. This was
  re-verified by hand outside the harness (correct `100000 triples`
  output, 0.463–0.470 s across runs).
- **wasm vs js:** wasm is the better Node runtime on 8 of the 9
  measured cells; the exception is full-scan COUNT at 1M (35.4 s vs
  25.1 s).
- **The join query hit the 600 s cap on all three runtimes at 1M**
  (it was already the slowest shape at 100k on all three). That is an
  engine-shape wall (join evaluation), not a runtime difference —
  recorded as skips, no number claimed.

**W3C-suite-per-runtime note.** The wall-clock of the full W3C SPARQL
suite per runtime is not reported here: the js/wasm W3C runners
(`docs/fstar-extracted/w3c-runner{.js,.wasm.js}`) are exercised by
`tests/beyond-w3c/` for **parity** (same answers as native), and a
per-runtime suite timing would mostly measure Node process spawns and
manifest I/O rather than engine speed. The query-shape table above is
the runtime-speed comparison; suite *scores* are runtime-independent
(same extracted logic).

## Delta-log micro-bench: the four-way (plus C→wasm) comparison

`RDF.Store.Columnar.DeltaLog` — the durable-UPDATE delta-log byte
format (serialize + parse of a batch of `DE_Add` entries, framing and
checksum included) — is the one module family that exists in **all
four** extracted forms today. Two distinct pipelines are measured;
they are not comparable with each other:

- **`pure`**: hand-build a `delta_batch` of N entries in the host
  language, time `serialize_delta_batch` then `parse_delta_batch`.
  Available for OCaml-native, C-native, and C-wasm. (The shipped
  js/wasm bundles do not export the raw serialize/parse functions.)
- **`sparql`**: one `INSERT DATA { …N triples… }` string through
  `parse_sparql_update` → `update_ops_to_delta_entries` →
  `serialize_delta_batch` → hex — the `deltaBatchToHex` export the
  browser persistence path actually ships. Available for
  OCaml-native, js\_of\_ocaml, and wasm\_of\_ocaml.

Drivers: [`tools/deltalog-bench/`](https://github.com/danbri/factoidal/tree/claude/main/tools/deltalog-bench)
(`deltalog_bench.c`, `deltalog_bench.ml`, `bench-js-wasm.mjs`,
`run-wasi.mjs`). All three `pure` binaries run with unlimited process
stack (`ulimit -s unlimited`); the wasm module is additionally linked
with a 1 GB wasm stack and run under `node --stack-size=200000` — see
"what this reveals" below for why.

### `pure` mode — serialize + parse of an N-entry batch, process wall-clock (seconds)

| N entries | OCaml native | KaRaMeL C native | KaRaMeL C → wasm32-wasi (node:wasi) |
|---:|---:|---:|---:|
| 1,000 | 0.056 | **0.047** | 0.107 |
| 5,000 | 0.316 | **0.242** | 0.319 |
| 10,000 | 0.747 | **0.465** | 7.61 (see note) |

Per-phase timings reported by the binary itself (single run at
N=10,000; the serialized batch is 1,107,816 bytes):

| Phase | OCaml native | C native | C wasm32-wasi |
|---|---:|---:|---:|
| `serialize_delta_batch` | 0.214 s | 0.221 s | 0.291 s |
| `parse_delta_batch` | 0.463 s | **0.149 s** | 7.16 s |

Notes:

- **C-native is the fastest form of this module**: 1.6× faster than
  extracted-OCaml native at N=10,000 wall, with parse 3.1× faster
  per-phase.
- **C-wasm tracks C-native closely until it doesn't.** At N=1,000 and
  N=5,000 the per-phase gap is 1.0–1.4× (parse at N=5,000: 0.078 s
  wasm vs 0.077 s native — parity). At N=10,000 parse degrades to
  7.16 s (48× slower than C-native) and 1 of 3 harness runs died on a
  V8 stack error (6 of 6 immediate manual retries succeeded, walls
  6.95–8.25 s). N=10,000 sits near this build's stack ceiling;
  N=20,000 fails outright.
- **N=1,000,000 was OOM-killed at ~15 GB RSS even for C-native**
  (~15 s wall before the kill, on 15 GB RAM). C-native peak RSS grows
  ~41 KB per entry (4.07 GB at N=100k, 12.4 GB at N=300k — measured
  via `getrusage`). See "what this reveals".

### `sparql` mode — `INSERT DATA` → `deltaBatchToHex`, wall-clock (seconds)

The same wrapper function across the three runtimes that ship it
(N counts triples in the INSERT DATA; in-process `total_s` shown in
parentheses — the difference from wall is process + bundle start-up):

| N triples | OCaml native | js_of_ocaml (Node) | wasm_of_ocaml (Node) |
|---:|---:|---:|---:|
| 100 | **0.39** (0.38) | 0.67 (0.57) | 0.41 (0.34) |
| 300 | 3.46 (3.44) | 5.00 (4.87) | **2.89** (2.80) |

Two things stand out:

- **wasm_of_ocaml beats OCaml native at N=300** (2.80 s vs 3.44 s
  in-process) — consistent with the full-engine parse result: for
  parser-shaped work, WasmGC is competitive with, and sometimes ahead
  of, the native binary.
- **The pipeline is super-linearly slow in N on every runtime**
  (~9× the time for 3× the input; a native N=1,000 probe took ~39 s
  vs ~0.4 s at N=100). The wall is in SPARQL-Update
  parsing/translation, not delta-log serialization — `pure` mode
  handles N=10,000 in under a second. Filed as a perf-opportunism
  observation below.

## The C→wasm question

The question this page was commissioned to answer: **could the KaRaMeL
C pathway produce a better wasm than js_of_ocaml / wasm_of_ocaml?**

**How the C→wasm leg was built.** No emscripten, wasi-sdk tarball, or
zig was available in this sandbox, but Ubuntu's own apt archive
carries a working wasm32-wasi toolchain: `apt install wasi-libc
libclang-rt-18-dev-wasm32`, then
`clang --target=wasm32-wasi --sysroot=/usr` compiles the
KaRaMeL-generated `Factoidal_DeltaLog.c` (plus krmllib pieces and the
demo stubs) unmodified. The resulting module runs under Node 22's
built-in `node:wasi` (preview1). The 12-check correctness demo
(`formal/fstar/c-output/deltalog/demo/delta_log_demo.c`) passes 12 of
12 checks under wasm exactly as natively — the C build is not just
timeable under wasm, it is *correct* under wasm.

**What the numbers say (delta-log micro-bench only):** C→wasm is
1.0–1.4× C-native per phase at N≤5,000 — at that scale it is the
fastest wasm-form of this module we can measure (its parse at N=5,000,
0.078 s, is 2.4× faster than OCaml-native's 0.185 s). But it
collapses at N=10,000 (48× slower parse, intermittent stack death)
where OCaml-native and, by the `sparql`-mode evidence, wasm_of_ocaml
keep working. There is no N at which the C→wasm route demonstrated an
advantage over the wasm_of_ocaml route on the same shipped
functionality, because the two cannot run the identical pipeline —
and where indirect comparison is possible, wasm_of_ocaml's showing
against native OCaml (beating it on parse) is stronger than
C-wasm's showing against C-native (cliff at N=10,000).

**What this implies — and does not imply — for a full-engine KaRaMeL
wasm build:**

1. **The full engine cannot take this path today.** krml's
   monomorphizer blows up (stack overflow / >10 min at >5 GB RSS) on
   the `SPARQL11.Algebra` / `RDF.Graph.Executable` dependency graph —
   reproduced and documented in
   [`tools/karamel-c-build.sh`](https://github.com/danbri/factoidal/blob/claude/main/tools/karamel-c-build.sh)
   (Groups B and D) and scoped in
   [the C-build plan](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-05-07-c-build-and-roaring-plan.md).
   Only leaf modules with small dependency cones (delta log,
   RDF.Format, JSON escape, static files) extract to C at all.
2. **Even where it works, KaRaMeL C inherits the F\* spec's data
   layout.** The generated C processes linked lists of heap-allocated
   cons cells with deep non-tail recursion (`serialize_ops`,
   `parse_n_delta_entries`). Measured consequences: `ulimit -s
   unlimited` needed above ~1,000 entries; ~41 KB peak RSS per entry;
   OOM-killed at N=1M on 15 GB RAM — *in native C*. The wasm build
   additionally needs the wasm linker stack raised and V8's
   `--stack-size` raised, and still ceilings between N=10,000 and
   N=20,000. "C" does not mean "fast and lean" when the compiled
   program is a list-processing functional program in C clothing.
3. **wasm32-wasi vs WasmGC is a real architectural fork.** The C
   route brings its own malloc heap in linear memory (GC-less
   krmllib compatibility mode — the demo and bench allocate and never
   free); wasm_of_ocaml targets WasmGC and inherits the host GC. For
   long-running in-browser sessions the memory story, not micro-bench
   latency, is likely decisive — and it favours WasmGC.
4. **What a fair full-engine comparison would need:** either the krml
   monomorphizer blocker fixed / the algebra modules restructured
   into KaRaMeL-compatible form (the C-build plan's long track), or
   Low\*-style rewrites of hot paths onto flat buffers — at which
   point the speed would owe more to the rewrite than to the C
   target. Until then, no full-engine C-vs-js number can be measured,
   and none is claimed here.

**Bottom line:** on today's evidence, KaRaMeL → C → wasm is not a
shortcut to a faster full-engine wasm. The C build is the fastest
*native* form of the one module family that has it, but compiled to
wasm it gains no demonstrated advantage over the wasm_of_ocaml route
and hits a scale cliff the other runtimes don't. Meanwhile
wasm_of_ocaml already beats the *native binary* on parse throughput.
A faster wasm engine is more likely to come from wasm_of_ocaml plus
F\*-side data-structure work (the same lesson as
[the 2026-04 Turtle-parser history](https://github.com/danbri/factoidal/blob/claude/main/docs/claude-rules/performance.md))
than from switching extraction pipelines.

## What is NOT measured here

- **Full engine under KaRaMeL C** — does not exist (see above); no
  number is extrapolated for it.
- **Browser-hosted runs** — everything here is Node-hosted; browser
  numbers (different JIT warm-up, IndexedDB persistence path) are
  future work under
  [tests/beyond-w3c phase 5, issue #247](https://github.com/danbri/factoidal/issues/247).
- **W3C suite wall-clock per runtime** — see the note in the
  full-engine section.
- **`pure`-mode delta-log for the js/wasm bundles** — the raw
  serialize/parse functions are not exported by the shipped bundles;
  only the SPARQL-driven `deltaBatchToHex` wrapper is measurable
  there (`sparql` mode).
- **2-pattern join at 1,000,000 triples** — hit the 600 s per-run cap
  on all three runtimes (skips recorded in the JSON); regex FILTER at
  1M was not attempted (time budget, also recorded).
- **On-disk COTTAS backend across runtimes** — the on-disk path is
  native-only today.

## Perf-opportunism observations (filed, not fixed here)

Recorded per the standing order in
[`skills/perf-benchmarking/SKILL.md`](https://github.com/danbri/factoidal/blob/claude/main/skills/perf-benchmarking/SKILL.md):

1. **`deltaBatchToHex` scales super-linearly in update size** on all
   runtimes (OCaml-native: N=100 → 1,000 went ~0.4 s → ~39 s, ~100×
   for 10× input). The wall is in SPARQL-Update parsing/translation,
   not delta-log serialization (`pure` mode does N=10,000 in under a
   second). Browser persistence writes batches of a few ops, so this
   does not bite today; bulk INSERT DATA through this path would.
2. **Delta-log extraction shape** — non-tail-recursive
   serialize/parse recursion (stack) and cons-cell-per-byte output
   (heap, ~41 KB RSS per entry measured) put a hard scale ceiling far
   below the format's design limit of 2^32 ops per batch, on every
   runtime including C.
3. **GROUP BY at 1M is 23× slower on js than native** (484 s vs
   21 s) — the widest runtime gap measured; whatever allocation
   pattern aggregation uses is disproportionately expensive under
   js_of_ocaml.

## See also

- [Competitive benchmark (engine-vs-engine)](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-06-competitive-benchmark-results.md)
- [Performance status + history](https://github.com/danbri/factoidal/blob/claude/main/docs/claude-rules/performance.md)
- [Hub post 15: How fast — the performance story]({{ '/web/hub/15-how-fast-the-performance-story/' | url }})
- [Test-results dashboard]({{ '/test-results/' | url }})
- [Disk-backed DB perf review](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-05-disk-backed-db-perf-review.md)
