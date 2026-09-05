# The call stack a store query needs, and where the handle lives

2026-09-05.
[Issue 653](https://github.com/danbri/factoidal/issues/653).
Sibling of [`2026-09-03-npm-pack-in-wasm.md`](2026-09-03-npm-pack-in-wasm.md),
which records the same defect on the pack path
([issue 649](https://github.com/danbri/factoidal/issues/649)).

## The defect

Several engine paths recurse once per manifest entry, and several
evaluator paths recurse once per row. Against a large collection that
exceeds the default call stack of Node and of Deno, and the failure is
`Maximum call stack size exceeded` rather than an engine refusal.

MEASURED 2026-09-05, macOS 15 arm64, Node 22.22.2, against the committed
wasm module and the full skosdex collection
(`/Users/danbri/working/factoidal-skosfull`: 7,315,251 quads, 3,286
blocks, 204 graphs, activated):

- `storeQueryPlan` alone overflows on plain `node`, before a single
  artifact byte is read.
- `node --stack-size=60000` clears the plan, the `storeOpen`, and every
  query.

Earlier the same limit was narrowed to any query that materialises about
14,576 rows or more, whatever it returns.

## Where the handle lives, and why

A store handle is STATE INSIDE THE WASM INSTANCE: the artifacts
`storeOpen` verified, decoded and indexed. A WebAssembly instance does
not cross a thread boundary, so a handle opened on the main thread
cannot be queried from a worker, and the reverse. Two designs were
available:

1. **The handle lives in the worker.** `query()` and `close()` are
   messages to it. One decoded copy; every call gets the big stack.
2. **Each query spawns a worker.** Every query re-reads and re-decodes
   every artifact.

(2) destroys the reason a handle exists. Measured on the collection
above, `storeOpen` costs 5.4 s and a `CONTAINS` query over the retained
rows costs 0.5 s; paying the open per query is worse than the stateless
`queryStore` path, which at least transfers the artifacts only once per
call. So (1) is what `npm/factoidal/bin/store-worker-host.mjs` and
`npm/factoidal/bin/store-worker.mjs` implement.

### The cost of (1), stated

- **One worker thread per SESSION, not per handle.** A session holds one
  engine and as many handles as the engine's own handle cap allows, so a
  caller that opens several stores pays for one thread and one copy of
  the 5.6 MB module. `openStoreHandleOnWorker` uses a shared session by
  default; `{ownWorker: true}` gives a handle its own thread when a
  caller wants failure isolation between stores.
- **Every call is asynchronous**, where the in-process handle is
  synchronous.
- **An extension function registered on the main thread's engine**
  (`bin/ext.mjs`) is not visible to the worker's engine. Register it
  inside the worker, or use the in-process handle.
- **The worker keeps the process alive** until `close()` or
  `terminate()`. `unref()` is not used: a server that dropped its last
  reference would otherwise lose its store with no report.

### A one-shot query pays none of it

`factoidal query` builds no handle and drops whatever it loads, so a
worker is overhead it cannot amortise. It runs IN PROCESS, and only when
the runtime runs out of frames does it run again on a worker. The normal
case pays nothing; `--no-worker` turns the retry off and the frame
budget is reported as it was before.

## The two runtimes

Deno has a `node:worker_threads` shim, it accepts
`resourceLimits.stackSizeMb`, and it does almost nothing with it.
MEASURED 2026-09-05, deno 2.9.4 / V8 15.0.245.2 against Node 22.22.2, by
counting frames to the overflow inside the worker:

| runtime | default | `stackSizeMb: 64` |
|---|---|---|
| node | 41,195 | 696,555 |
| deno | 10,835 | 13,837 |

A 1.28-times raise does not carry an open that needs sixteen times the
default. So Deno keeps the re-exec route `bin/pack-host.mjs` already
carries: the command runs itself again once with
`--v8-flags=--stack-size=65536`, guarded by an environment variable so
it cannot loop, which needs `--allow-run` and `--allow-env`. A Deno
LIBRARY caller cannot re-execute its own host, so
`openStoreHandleOnWorker` gives it an in-process handle behind the same
asynchronous interface and the process supplies the stack:
`deno run --allow-read --v8-flags=--stack-size=65536`.

## The stack budget

`WORKER_STACK_MB` is 64, defined in `bin/pack-host.mjs` and shared by
both paths. It was bisected for the pack (8 MiB is the measured minimum
there, 64 is eight times it) and 64 MiB also exceeds the 58.6 MiB that
`--stack-size=60000` gives, which is the value measured to clear the
whole store path on the collection above. The headroom is cheap: a
thread stack is reserved address space, and only the pages touched
become resident.

## What was measured after the change

Full skosdex collection, plain `node`, no flag. A handle scoped to
`GRAPH <https://danbri.org/ns/skosdex/graph/iptc-mediatopic>
{ ?c skos:prefLabel ?l }` — 3 artifacts, 1,928,825 bytes, 17,648 rows —
opened in 4.9 s, then three `CONTAINS` searches:

| needle | time | rows |
|---|---|---|
| `volcan` | 524 ms | 3 |
| `election` | 514 ms | 8 |
| `zzzznotathing` | 505 ms | 0 |

The same three searches through the in-process handle under
`node --stack-size=60000` answer the SAME ROWS, compared binding by
binding rather than by count (anti-pattern 34), and so does the Deno
in-process handle under `--v8-flags=--stack-size=65536`.

Worker overhead, on the bundled sample store so it is not lost in the
query: a one-shot query is 163 ms in process and 220 ms on a worker; a
handle open is 124 ms in process and 236 ms on a worker; every query
after the open is 1 ms either way.

## Still open

- A `CONTAINS` search still scans every retained row, so 0.5 s per
  search on 17,648 rows is the scan, not the stack. The literal token
  index ([`2026-09-04-literal-token-index.md`](2026-09-04-literal-token-index.md))
  is the separate work.
- The recursion depth itself is a property of the Lean source. Reducing
  it — tail recursion, or a fold over an accumulator, on the manifest
  walk and on the per-row evaluator paths — would remove the need for
  the raised stack on every runtime, including a browser tab, which no
  host route can rescue.
- `openStoreHandle` with no options passes sidecar keys the manifest
  does not declare to `storeOpen` on the bundled sample store, and
  `storeOpen` refuses them
  (`artifact 'predicate-0.ibk3.sri2' is not declared by this manifest`).
  It predates this work and belongs with the handle caps,
  [issue 657](https://github.com/danbri/factoidal/issues/657). Passing
  `{sparql}` or `{keys}` avoids it.
