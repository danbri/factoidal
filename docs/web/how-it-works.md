---
title: How Factoidal works
layout: base.njk
---

# How Factoidal works

Factoidal is an RDF/SPARQL engine whose logic is written as F\*
specifications and turned into runnable code by extraction, not by
hand-writing an implementation that mirrors a spec. This page collects
the machinery behind the engine: what "verified" means here, how one
source becomes four runtimes, and how the read-write store is
structured. For what you can do with your data, start at the
[home page]({{ '/' | url }}) or the
[documentation hub]({{ '/web/hub/' | url }}).

## What "verified" means here

The parser and the SPARQL algebra are specified in F\* and verify
under z3 with no `--lax` and no escape hatches. Executable code comes
out of `fstar.exe --codegen OCaml`, so the code you run is derived
from the spec rather than written to match it.

Standing qualifier: parser and algebra spec verified in F\*; on-disk
backend has unverified OCaml-side optimization layers being migrated
back to F\*. That boundary is tracked openly in
[issue #118](https://github.com/danbri/factoidal/issues/118) and the
[recovery plan](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-05-07-query-planning-fstar-recovery.md).

The [verified-in-F\* hub post]({{ '/web/hub/16-the-verified-in-fstar-story/' | url }})
walks through why F\*, what the proofs cover, and what one proof gap
looks like when stated plainly.

## One source, four extraction targets

The same F\* source is extracted once and then compiled for several
runtimes:

| Target | Output | Status |
|---|---|---|
| **Native** | `bin/<platform>/w3c_runner`, `bin/<platform>/factoidal` | full W3C pass counts |
| **JavaScript** (js_of_ocaml) | [`/fstar-extracted/w3c-runner.js`]({{ '/fstar-extracted/' | url }}) | runs in any modern browser or Node |
| **WebAssembly** (wasm_of_ocaml) | [`/fstar-extracted/w3c-runner.wasm.js`]({{ '/fstar-extracted/' | url }}) + `.wasm.assets/` | Wasm-GC engines (Chrome ≥ 119, Node ≥ 22); experimental — cross-runtime parity tracked in `tests/beyond-w3c/` |
| **C** (KaRaMeL) | native C from the same spec | pilot; see the C-build plan |

The artifacts are rebuilt by CI on every push and ship from
`docs/fstar-extracted/`. The Wasm binary links a vendored copy of
[zarith\_stubs\_js](https://github.com/janestreet/zarith_stubs_js)'s
`runtime.wat` + `runtime_wasm.js` to wire the `ml_z_*`
arbitrary-precision integer primitives through to JavaScript BigInt.
The hash builtins (MD5/SHA family) are realised in pure OCaml
(`fstar_pure_hashes.ml`) so native, JS, and Wasm builds share one code
path — the historical `functions`-suite Wasm gap came from C hash
stubs and no longer applies.

```
F* formal spec  (the product)
    |
    v
fstar.exe --codegen OCaml
    |
    ├── ocamlfind ocamlc     → bin/<platform>/w3c_runner      (native)
    ├── js_of_ocaml          → docs/fstar-extracted/w3c-runner.js
    └── wasm_of_ocaml        → docs/fstar-extracted/w3c-runner.wasm.{js,assets/}
```

See
[`formal/fstar/build-ocaml.sh`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/build-ocaml.sh)
for the exact invocation.

## The module dependency graph

The F\* spec is split across 90 modules. The
[interactive dependency graph]({{ '/web/demos/dep-graph/' | url }})
shows what depends on what — derived from `fstar.exe --dep graph` so
the edges match what the build sees. Static
[SVG]({{ '/web/demos/dep-graph/modules.svg' | url }}) /
[PNG]({{ '/web/demos/dep-graph/modules.png' | url }}) /
[Graphviz]({{ '/web/demos/dep-graph/modules.dot' | url }}) /
[Mermaid]({{ '/web/demos/dep-graph/modules.mmd' | url }}) /
[plain-text]({{ '/web/demos/dep-graph/modules.txt' | url }}) renders are
shipped alongside.

## A read-write database

The on-disk store accepts SPARQL UPDATE and the Graph Store Protocol
over HTTP (`factoidal-http --rw`), backed by an immutable COTTAS base
plus an append-only delta log with framing round-trips proved in F\*.
Readers merge the log on read (the merge lemma is proved, not
asserted); compaction swaps in a new base atomically via a symlink,
guarded by an epoch check. Crash-safety is measured, not claimed:
SIGKILL harnesses at every write stage accept zero torn or corrupt
states. The store lifecycle is self-contained — `factoidal import`
writes COTTAS natively (byte-compatible with DuckDB's Parquet reader),
so no Python or third-party tooling is needed to create, update,
compact, or serve a database.

The same delta-log write path runs on native OCaml, KaRaMeL-extracted
C ([`bd9e5be`](https://github.com/danbri/factoidal/commit/bd9e5be)),
and js\_of\_ocaml / wasm\_of\_ocaml in the browser, where the log
persists in IndexedDB across page reloads
([`8ff60eb`](https://github.com/danbri/factoidal/commit/8ff60eb)).
The [durable-log hub post]({{ '/web/hub/18-the-durable-log-live/' | url }})
runs the whole cycle — update, persist, reload, corrupt, recover —
live in the page.

On-disk fast paths still include unverified OCaml optimization layers
being migrated back to F\*; the parser and algebra spec are verified,
and that boundary is tracked openly.

## Performance

Speed is measured separately from correctness — each number names its
date and the commit it was measured on.

| What | Measured | Date / commit |
|---|---|---|
| Turtle parsing | ~100k triples/s, near-linear to 1M triples (1M in 9.66s) | 2026-07-03, [`11ba254`](https://github.com/danbri/factoidal/commit/11ba254) |
| In-memory dataset, end-to-end (parse + index + GRAPH-count query) | 1M quads in ~41s, ~1.2 GB peak RSS (~1.2 KB/quad) | 2026-07-03, [`bef4e4b`](https://github.com/danbri/factoidal/commit/bef4e4b) |
| In-memory COTTAS-bytes store (`--data-cottas-mem`) | 64.4 B/quad for a full-corpus COUNT, 160.9 B/quad for point lookups — vs 877 B/quad on the heap store | 2026-07-06, [`677bdf1`](https://github.com/danbri/factoidal/commit/677bdf1) |
| OWL-RL closure, sameAs 32-clique (was >590s cap-trip) | 1.07s — closure step reduced from O(k⁶) to ~O(k³) | 2026-07-03, [`4812c3d`](https://github.com/danbri/factoidal/commit/4812c3d) |
| On-disk COTTAS | serves the 3,143,406-quad UK Parliament corpus ([live demo]({{ '/web/demos/ukparliament/' | url }})); fast paths still unverified OCaml being migrated to F\* | [issue #118](https://github.com/danbri/factoidal/issues/118) |

How the four extraction targets (native OCaml, js\_of\_ocaml,
wasm\_of\_ocaml, KaRaMeL C) compare on the same work — including
whether the C pathway could yield a faster wasm — is measured on the
[performance hub]({{ '/web/perf/' | url }}).

## Source

- [github.com/danbri/factoidal](https://github.com/danbri/factoidal)
- [F\* specifications](https://github.com/danbri/factoidal/tree/claude/main/formal/fstar) — RDF.Graph.Executable.fst, SPARQL11.Algebra.fst, SPARQL11.Parser.fst, Parser.\*.fst
- [Browser build notes]({{ '/fstar-extracted/' | url }}) — JS + Wasm artifact details
