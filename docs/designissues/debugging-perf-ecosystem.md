# Factoidal — Debugging & Performance Ecosystem

**Status:** living reference, written 2026-04-26 during the parliament-COTTAS demo prep cycle. Capture everything we know about how the SPARQL evaluator can be deployed and observed. Nothing is declared "out of scope" — this is the menu, not the plan.

**Audience:** project owner; future agents who need to pick a debugging approach; corpus managers deciding hot vs cold; engineers learning what the F\* extraction targets actually do at runtime.

**Why this file exists:** an LLM can author thousands of lines of code per day, and that code lands in F\*, gets extracted to OCaml, sometimes to JS via `js_of_ocaml`, sometimes to WASM via `wasm_of_ocaml`, sometimes to C via KaRaMeL. The debugging burden has moved from "find the bug" to "find which target the bug lives in, with what tooling." If you can't step through *one* extraction target with confidence, the AI's code velocity becomes a liability instead of an asset.

---

## Part I — Where the SPARQL evaluator can run

### 1.1 The full extraction-target matrix

The F\* sources in `formal/fstar/*.fst` are the source of truth. Each module can be extracted to several backends. Today's status (verified, not assumed):

| Target | F\* command | Output artifact | Runs on | Today's status |
|---|---|---|---|---|
| **OCaml native** | `fstar.exe --codegen OCaml` | `.ml` files → `dune build *.exe` → Mach-O / ELF | macOS / Linux process | ✅ `bin/<platform>/factoidal-http`, this is what `:3032` runs |
| **OCaml bytecode** | as above + `ocamlc -c` | `.cmo` / `.cma` → `ocamlrun` | OCaml bytecode VM | 🟡 not built today; `dune build *.bc` would produce it |
| **JavaScript** (`js_of_ocaml`) | as native, then `js_of_ocaml` | `factoidal.js` (~458 KB) | Browser, Node ≥ 20 | ✅ `docs/fstar-extracted/factoidal.js`; `kind=exe` (standalone CLI shape) |
| **WebAssembly** (`wasm_of_ocaml`) | as native, then `wasm_of_ocaml` | `factoidal.wasm.js` shim + `*.wasm` | Browser (Chrome ≥ 110), Node ≥ 20 | ✅ `docs/fstar-extracted/factoidal.wasm.js` + assets |
| **C** (KaRaMeL) | `fstar.exe --codegen C` then `kremlin` | `.c` / `.h` → `gcc` / `clang` | Bare metal, embedded, `cc -o`-anywhere | 🟡 blocked by `noeq` types in some modules; not building today |
| **F\* interactive** | `fstar.exe --interactive` | proof state | F\* itself (mostly for development) | ✅ used during proof writing |
| **OCaml toplevel / utop** | `utop -require fstar.lib` | REPL session | OCaml interpreter | ✅ available; some libs (cohttp, zarith) need explicit `#require` |

### 1.2 Deployment shapes (what wraps the evaluator)

Each extraction target can be packaged in multiple ways:

| Shape | Wraps | Today's status |
|---|---|---|
| **Standalone HTTP server** | OCaml native + cohttp_lwt_unix | ✅ `factoidal-http`, native OCaml only today |
| **Node HTTP server** | factoidal.js + `http.createServer` + small glue | 🟡 doesn't exist; ~50 LoC away |
| **Node CLI / library** | factoidal.js or factoidal.wasm.js | ✅ `npm/factoidal/` (published-ready, no consumer) |
| **Browser web component** | factoidal.js or .wasm.js loaded into page | ✅ `factoidal-sparql-client.js`; supports `engines="js,wasm"` |
| **Browser remote client** | same web component but `endpoint=URL` mode | ✅ this is what the parliament demo at `:3032/` uses |
| **Lambda / serverless** | `factoidal.js` invoked per-request | 🟡 no example; npm package would suit |
| **Service-worker** | `factoidal.js` running in browser SW context | 🟡 untried; would need DOM-API-free verification |
| **C library embedded** in another tool (Rust, Python, Go) | KaRaMeL output linked via FFI | 🟡 blocked by `noeq`; once unblocked, `pyo3` / `cgo` wrappers feasible |

**None of these is in scope or out of scope.** We pick from this menu when a need arises.

### 1.3 Data residency: hot indexed vs cold on-disk

Independent axis from the evaluator target. Today's COTTAS backend mixes both:

| Data tier | What it is | Today on parliament (3.14 M quads) | Engine target it constrains |
|---|---|---|---|
| **Hot in-RAM, eager** | F\* `rdf_dataset` value built from N-Quads/TriG parse | `--dataset` flag; `GB_List` / `GB_Indexed` backends | All targets — but RAM-bounded |
| **Hot in-RAM, lazy populate** | Bet7's lazy hashtbl → Mim3's pre-warm | `--data-cottas` boot path before today | OCaml native (had it) ; JS would need filesystem polyfill |
| **Mmap'd column data, in-RAM dictionaries** | `.cottas` parquet on disk + Vav3's `.dict` companions mmap'd | Today's `:3032` path: dicts in RAM (~700 MB), columns on disk | OCaml native today; would port to Node via `mmap-io`, browser would need fetch+IndexedDB for the data |
| **Mmap'd everything, on-disk indexes** | Vav3's `.dict` + Lamed3's `.p.offsets` + (future) row_ids all mmap'd | Closest to "world's best RDF system" goal | Native OCaml or Rust; browser would emulate via byte-range fetch + cache |
| **Cold-file fetch on demand** | Data sits on object storage; pulled by query | hypothetical; e.g. S3-backed COTTAS per dataset | Any target with HTTP fetch primitives |
| **Hybrid**: schema/vocab in RAM, instance data cold | Common-predicate dictionaries hot; instance triples cold | We're roughly here for parliament | Same as mmap'd everything |

**The corpus manager's question** — "what should be hot vs cold for my workload?" — depends on:

- **Working-set size**: if 1% of triples answer 99% of queries, only those need to be hot.
- **Query shapes**: predicate-bound queries want predicate dicts hot; object-bound want object dicts hot.
- **Latency budget**: SPARQL Protocol GETs from a browser want sub-second response; batch ETL doesn't care about cold-start.
- **Cost shape**: RAM is expensive at scale; disk is cheap; network fetches are fastest in cache, slowest cold.

Vav3's persistent companion files (`.dict`, `.presence`, `.offsets`) are the foundation that lets the corpus manager *choose* — they let the engine boot with everything cold and warm up only what's queried. The JS-build can read these companion files via `Response.bytes()` + offset arithmetic, so the browser-embedded mode could match the OCaml native mode on cold-start performance once the companion-file reader is ported to JS.

---

## Part II — Debugging concerns, expressed as axes

A bug isn't just "it crashes" or "it's slow." Concrete axes that map to different tools.

### 2.1 Performance — speed (single-query latency)

**Question:** "why does query Q take N ms / s / minutes?"

**Sub-questions:**
- Is the bottleneck in parse, plan, search, decode, marshal, or transport?
- Is it CPU, memory bandwidth, disk IO, network IO?
- Does the bottleneck differ between extraction targets?

**Tools per target:**

- **Native OCaml**: `lldb` for sampling profile (`sample <pid>`); `strace` / `dtruss` for syscall trace; the existing `[qof3-trace]` / `[pe4-trace]` / `[mim3-trace]` etc. stderr lines (already in code). Linux `perf record` + `flamegraph`.
- **Native bytecode**: `ocamldebug` step-through; `Spacetime` profiler (heap allocations); `Landmarks` library for hot-path annotations.
- **JS (Node or browser)**: chrome devtools Performance panel; flame graph; `--cpu-prof` flag in Node.
- **WASM**: chrome devtools v110+ has WASM flame graph; per-instruction sampling.
- **Cross-target compare**: same query Q on same data, three targets, three flame graphs side-by-side. Reveals whether a slow phase is target-specific or F\*-source.

### 2.2 Performance — fidelity / quality of extraction

**Question:** "does target A produce the same output as target B?"

**Why it matters:** F\* proves the source. Extraction must preserve semantics. If `js_of_ocaml` mis-extracts a `Z.t` integer or `wasm_of_ocaml` rounds a float differently, our F\* proofs don't transfer.

**Sub-questions:**
- Numeric precision: do `xsd:decimal` arithmetic results match across native / JS / WASM?
- Unicode handling: do regex bounds match across `Str` (OCaml regex on bytes) and JS `RegExp` (codepoints)?
- Hash determinism: do skolemised blank-node IDs differ across targets?
- Error reporting: does target A say "parse error at line 42" while target B says "internal error"?

**Tools:**
- **W3C suite differential run**: same `w3c_runner` code compiled to three targets, run on the same test suite. Compare pass/fail diffs.
- **Property-based tests** (QuickCheck-style): generate random RDF + queries, run on all targets, assert results equal. We don't have this yet but it's the gold standard.
- **Spec-encoded oracle**: F\* `Lemma` that two extracted versions agree (research-grade).

### 2.3 Performance — concurrent load, memory, warmups

**Question:** "what happens when 1, 10, 100 simultaneous SPARQL queries hit the daemon?"

**Sub-questions:**
- Is there a thread/worker pool? (Today: native OCaml uses one cohttp accept loop; SIGALRM-based timeout per request.)
- Does cold-start matter? (Vav3 reduced first-boot 107s → 4s on subsequent boots.)
- Memory under load: does RSS grow unboundedly with concurrent queries?
- Backpressure: do we 503 cleanly or accept-and-stall?

**Tools:**
- **`vegeta` / `wrk` / `bombardier`** for HTTP load generation against `factoidal-http`.
- **`/proc/<pid>/status` polling** (Linux) or `vmmap <pid>` (macOS) for RSS tracking.
- **`ps -L`** for thread count.
- **Custom `[concurrency-trace]` instrumentation** in `factoidal_http.ml` — log each accept, each request start/end, queue depth.

### 2.4 Security — adversarial queries

**Question:** "can a malicious or accidentally-pathological SPARQL query lock up the daemon, OOM the host, or escape the data sandbox?"

**Sub-questions:**
- Resource exhaustion: cartesian-product BGPs, deeply nested OPTIONAL, exponential-blowup property paths.
- Timeout enforcement: is Heth3's `--query-timeout` actually invoked on every code path, or are there bypasses?
- Memory cap: Tav5's `--max-rows` prevents marshal-time OOM, but the BGP walker's accumulator can still grow before the cap fires.
- File-system access: if the daemon serves static files, can a path-traversal attack read arbitrary files?
- Update endpoint: does `--read-only` actually block all SPARQL Update verbs?

**Tools:**
- **Adversarial test suite**: hand-curated bad queries plus randomly mutated variants. Run with `--query-timeout 5 --max-rows 1000` and assert the daemon stays responsive.
- **Fuzzing**: AFL on the SPARQL parser (extracted as a standalone binary).
- **Static analysis**: F\* refinement types already prevent some classes (e.g. Mem4's `pcache_put_capacity_bound` proves the cache can't grow past `cap`).

### 2.5 Educational / mental-model

**Question:** "what is actually happening when I run this query?"

**Why it matters:** an LLM-generated F\*-OCaml-glue-WASM stack is opaque. Humans need a window into the parse → algebra → optimiser → backend → search → marshal pipeline. Without it, neither the human reviewer nor the AI's next iteration knows what's correct.

**Sub-questions:**
- What does the parser produce? (AST shape.)
- How does the algebra rewrite (BIND, FILTER push-down, OPTIONAL → LeftJoin, etc.)?
- What's the join-order plan?
- For a backend-routed BGP, which row groups get walked? Which get pruned by Yod6/Tet3?
- For the on-disk data, what bytes are mmap'd? When?
- What's the solution-sequence shape after each modifier (DISTINCT, ORDER BY, LIMIT)?

**Tools today (text-only):**
- The existing `[qof3-trace]` / `[mim3-trace]` / `[pe4-trace]` / `[lamed3-trace]` / `[tet3-trace]` / `[yod6-trace]` / `[vav3-trace]` stderr lines.
- `--verbose` flag on the daemon.
- `factoidal --explain QUERY` (does this exist? unverified).

**Tools we don't have but should consider:**
- **A human-friendly query-introspection GUI** — see Part V below.

### 2.6 Cross-cutting: corpus management

**Question:** "given my data, my queries, and my budget, what should I make hot vs cold?"

A practical question for anyone running factoidal in production. Mostly answered by measuring (Part 2.1 + 2.3) and choosing companion-file generation policy (Part 1.3).

---

## Part III — Tooling matrix

The intersection: which tool, on which target, answers which question.

|  | OCaml native | OCaml bytecode | JS (browser) | JS (Node) | WASM (browser) | WASM (Node) |
|---|---|---|---|---|---|---|
| **Sampling profiler** | `lldb sample` / `perf` | `Spacetime` / `Landmarks` | chrome devtools Performance | `node --cpu-prof` | chrome devtools | `node --cpu-prof` (WASM-aware in 22+) |
| **Step debugger** | `lldb` (assembly-level) | **`ocamldebug` (time-travel — !!)** | chrome devtools Sources + sourcemap | `node --inspect` + chrome | chrome devtools (DWARF) | `node --inspect` |
| **Heap snapshot** | `vmmap` / `heap` | `Spacetime` | chrome devtools Memory | `node --heap-prof` | chrome devtools Memory | `node --heap-prof` |
| **Live REPL on internals** | `utop` (limited) | `utop` (limited) | browser console + bound exports | Node REPL + bound exports | not really | not really |
| **Trace I/O** | `dtruss` / `strace` | same | chrome Network panel | Node `--trace-events` | chrome Network panel | Node `--trace-events` |
| **Differential against W3C** | `w3c_runner` native | bytecode `w3c_runner` | `w3c_runner.js` in browser | `w3c_runner.js` in Node | `w3c_runner.wasm.js` | same |
| **Fuzz parser** | `afl-fuzz`-instrumented build | usable | `jsfuzz` | `jsfuzz` | wasm-fuzz | same |

**Key observation:** `ocamldebug` is the only **time-travel** debugger in the list. You can step *backwards* through execution. For chasing "why did this state get corrupted by step N?" it's irreplaceable. **We don't currently build a bytecode target.** That's a gap.

---

## Part IV — The underused path: bytecode + ocamldebug

### 4.1 Why it's underused

When the project converted from "vibe-coded OCaml" to "F\*-extracted OCaml," the build script (`formal/fstar/build-ocaml.sh`) only emits the `.exe` (native). No `.bc` (bytecode) target, so no `ocamldebug` substrate.

### 4.2 What it would take

A small build-script addition:

```bash
# Inside build-ocaml.sh, after the dune build .exe step:
dune build factoidal_http.bc        # bytecode target
dune build w3c_runner.bc            # likewise
```

The `dune` config already supports both — the `(modes (native exe) (byte exe))` stanza, or explicit `*.bc` targets. We just don't run them.

### 4.3 What it gives us

```
$ ocamldebug formal/fstar/ocaml-output/factoidal_http.bc \
    --port 3033 --data-cottas tmp/.../data.cottas --max-rows 50000

(ocd) load_printer "fstar_compiler_lib.cmxa"
(ocd) install_printer Prims.string_of_int
(ocd) break @ Sparql11_algebra__eval_bgp_backend_from_mu_fuel
(ocd) run
... daemon boots ... handles request ...
... breakpoint hits inside the BGP loop ...
(ocd) print mu             (* current solution mapping *)
(ocd) step                 (* one F*-source-line forward *)
(ocd) reverse step         (* one F*-source-line BACKWARD — the killer feature *)
(ocd) where                (* full call stack, F*-source-named *)
```

For chasing the Q03 regression specifically: set a breakpoint on `estimate_fast_via_offsets`, run a query, step through the join-order computation, see exactly where the optimiser routes both triples instead of short-circuiting. **No print-statement-driven-development.**

### 4.4 Caveat

Bytecode is ~10× slower than native. So `ocamldebug` on a 30-minute extract isn't practical. But: a single SPARQL query against a 3 M-triple dataset takes 6–30 seconds in native; bytecode would take 60–300 seconds. Acceptable for a debugging session.

### 4.5 Action item (deferred)

Add `dune build factoidal_http.bc` to `build-ocaml.sh`. Document a `make ocamldebug` target. ~30 min of work; high leverage when the next regression lands.

---

## Part V — The Node V8 server hypothesis

### 5.1 What it would unlock

A long-running Node process serving SPARQL via `factoidal.js`:

```js
import http from 'http';
import { initialize, query, parseAndLoad } from './factoidal-node-wrapper.js';

await initialize();
const dataset = await parseAndLoad('parliament.nq');

http.createServer((req, res) => {
  // ... read SPARQL query from req body or query string ...
  const result = query(dataset, sparqlText);
  res.writeHead(200, { 'Content-Type': 'application/sparql-results+json' });
  res.end(JSON.stringify(result));
}).listen(3033);
```

This gives:

- **chrome devtools attach to a server** via `node --inspect`. The same JS that runs in browser now runs server-side and is debuggable with the same tooling. Cold-start indistinguishable.
- **Differential: native vs Node, same F\* sources, same data, same queries.** Lets you say with confidence "this is a target-specific bug" or "this is an F\* source bug."
- **Lambda / Cloudflare-Worker / Vercel-Function deployment**: the npm package becomes a one-line edge deploy.
- **No COTTAS-on-disk in this mode initially** — the JS engine doesn't have the mmap path. But: the in-memory `--dataset` mode already works in JS. Parliament-scale (3.14 M triples) fits in V8's default 4 GB heap.
- **Companion-file reader port**: ~200 LoC of JS to read Vav3's `.dict` / Lamed3's `.offsets` over HTTP byte-range. Then Node-side gets the same fast cold-boot the OCaml daemon has.

### 5.2 What it doesn't unlock

- **Native-level perf**: V8 is fast but the OCaml runtime is faster on this kind of code. ~2–4× slower per query is a reasonable expectation.
- **Memory efficiency**: js_of_ocaml-extracted code uses JS objects for everything; OCaml's value representation is denser.

### 5.3 Action item (deferred)

`tools/factoidal-node-server.mjs`, ~50 LoC. Could be one agent's morning.

---

## Part VI — Human-friendly query-introspection GUI

### 6.1 Why we need it

LLM-pace code generation has outrun human review pace. The user can't keep up if the only way to understand "what does this query do" is to read 1500 LoC of trace output. A GUI that **shows** parse → algebra → plan → execute, with each stage's data structure rendered visually, is the bridge between AI velocity and human comprehension.

This is also the educational angle: a SPARQL learner, an ontology author, or a corpus manager can hover over each stage and see "ah, that's where my query gets translated to relational algebra; that's where the optimiser decides to walk row groups 4, 7, 12; that's where the join happens."

### 6.2 What it should show

For one query end-to-end:

1. **Source** — the SPARQL text, syntax-highlighted.
2. **Parse tree** — the F\* `query` value, rendered as a clickable tree. Click a node → see its sub-AST + the F\* source line that constructed it.
3. **Algebra** — after `parse_to_algebra`, the relational-algebra-flavoured tree. Each operator node (BGP, Filter, Project, OrderBy, Slice, Distinct, Reduced, etc.) shows its inputs and outputs.
4. **Plan** — the optimiser's join-order decisions. For each triple pattern, show its estimated cardinality (Mem5's `estimate_fast`), which row groups will be walked (Yod6/Tet3 prune output), which offset indexes will be consulted (Lamed3).
5. **Execution** — live trace of the walker. Per row group: which columns get decoded, how many candidates pass each filter, how many rows match. Animated.
6. **Solution sequence** — the rows after BGP, after each modifier (DISTINCT, ORDER BY, LIMIT). Counts + samples.
7. **Marshal** — the final wire format (JSON, XML, CSV, TSV).
8. **Timing** — flame chart on the side, each phase sized by wall-clock cost.

### 6.3 How it would connect to factoidal

The daemon already emits `[qof3-trace]` lines for many of these stages. A small enhancement: emit them as **structured JSON-lines** instead of free-form `Printf.eprintf`:

```json
{"phase":"parse","query_id":"abc","ast":{...},"elapsed_us":120}
{"phase":"algebra","query_id":"abc","tree":{...},"elapsed_us":15}
{"phase":"plan","query_id":"abc","triples":[{"tp":"...","est":3140000,"chosen_first":false},...],"elapsed_us":2300}
{"phase":"walk","query_id":"abc","rg":0,"col_decode_us":4200,"matches_so_far":598}
...
```

A web page subscribes to these via a sibling endpoint (e.g. `/trace?query_id=abc` returning Server-Sent Events) and renders the visualisation.

### 6.4 Why this is also a perf tool

If you can *see* the optimiser planning Q03 with `estimate_fast_via_offsets: count=1222 (no_other_bound=true)` followed by walking both BGP triples, the regression jumps out visually — you'd instantly see "the second triple has bound object, why isn't its estimate reflecting that?" The current text traces require pattern-matching across 100+ log lines.

### 6.5 Why this is the educational tool

A graduate student studying SPARQL can run a query and see the algebra rewrite happen in real time. A SQL person learning RDF can see how `?s ?p ?o` patterns become joins. An ontology author can verify their `owl:sameAs` rules fire as expected.

### 6.6 Action item (deferred)

This is a multi-week effort: structured-trace emission in F\*/OCaml + a web component (`factoidal-query-introspector`) + visualisations (force-directed graph for ASTs, sankey for join flow, flame chart for timing). Probably the most leverage-per-LoC single feature on this entire roadmap.

A v0.1 might start with **just the algebra tree** rendered as JSON next to the query. From there, incrementally add stages.

---

## Part VII — Decision table: which path for which question?

When you have a specific question, this table picks the path.

| Question | First-line tool | Backup tool |
|---|---|---|
| "Why is query Q slow?" | `[qof3-trace]` stderr from native daemon | chrome devtools Performance on Node-served `factoidal.js` |
| "Did the JS extraction break Q?" | Open `demo-cottas.html`, run Q, compare to native | W3C suite differential |
| "Why does the optimiser route Q this way?" | `ocamldebug` on bytecode + breakpoint in optimiser | (future) introspection GUI |
| "Is Q a security risk?" | Run Q with `--query-timeout 5 --max-rows 1000`; observe RSS | Fuzz the parser |
| "What does the algebra look like for Q?" | `--explain` flag (verify it exists) | (future) introspection GUI |
| "Will my corpus fit in hot mode?" | `factoidal cottas-info <file>` (Bet7) + napkin math on dict sizes | Trial run + RSS measurement |
| "Same query on native, JS, WASM — same answer?" | Run W3C runner on all three | Hand-curate diff suite |
| "Where is memory going?" | `vmmap` on native; chrome Memory panel on JS | Spacetime on bytecode |
| "Why did the daemon crash?" | macOS `~/Library/Logs/DiagnosticReports/` + `ocamldebug` post-mortem | last `[qof3-trace]` lines + `git bisect` |
| "Is the new commit faster?" | Bench harness over a query suite, compare timings | Performance trace flame graph |

---

## Part VIII — Concrete near-term work items

In rough priority order, none committed:

1. **Emit `dune build factoidal_http.bc`** + document `make ocamldebug`. Highest leverage / lowest cost.
2. **Tools/factoidal-node-server.mjs** + `node --inspect` recipe. Unlocks server-side chrome devtools.
3. **Differential W3C runner** (`make w3c-diff`) — run native + JS + WASM on the same suite, diff outputs. Catches extraction-fidelity bugs early.
4. **Structured `[trace]` JSON-lines** in `factoidal_http.ml`. Pre-requisite for the introspection GUI.
5. **Adversarial query suite** — `tests/adversarial/*.rq` plus a runner that asserts the daemon stays alive.
6. **Vav3 / Lamed3 companion-file reader in JS** — unlocks browser-embedded mode at parliament scale.
7. **Introspection GUI v0.1** — algebra-tree side panel.

Each is independently shippable and adds a specific debugging axis.

---

## Part IX — What this document does NOT cover

- F\* proof obligations (separate concern; see `docs/claude-rules/`).
- Build-system reproducibility (separate concern; see `docs/build/`).
- Specific bugs (those go in dated `docs/designissues/YYYY-MM-DD-*.md`).
- The COTTAS file-format spec (see `docs/designissues/cottas-format-v1.md`).

---

## Provenance & honesty

Every claim above was verified at write time except where marked 🟡 (untested) or "(unverified)". Specifically:

- "C extraction is blocked by `noeq` types": stated in CLAUDE.md, not tested today.
- "WASM DWARF support in chrome 110+": from chrome release notes; not exercised by this project today.
- "ocamldebug step-through F\*-extracted code": works in principle (the .ml is plain OCaml after extraction); not exercised because we don't build bytecode.
- "Node V8 server is ~50 LoC": informed estimate; not implemented.
- "factoidal.js fits parliament in V8 4 GB heap": untested; based on RAM math from native daemon (1.5 GB after pre-warm).

This document is a **menu, not a plan**. Pick what you need. Update when you learn something new.
