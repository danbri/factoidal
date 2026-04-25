# Scoping: F\* parser as pyoxigraph replacement, and Parquet/COTTAS CLI/JS access

**Agent:** Yod2
**Date:** 2026-04-25
**Status:** scoping only — no `.fst` / `.ml` edits, no extract/compile.
**Related:**
[`2026-04-24-turtle-parser-perf-diagnosis.md`](2026-04-24-turtle-parser-perf-diagnosis.md),
[`2026-04-19-turtle-parser-speed.md`](2026-04-19-turtle-parser-speed.md),
[`2026-04-25-cottas-parquet-load-path-perf.md`](2026-04-25-cottas-parquet-load-path-perf.md),
[`2026-04-25-millenniumdb-study.md`](2026-04-25-millenniumdb-study.md),
[`2026-04-19-cottas-parquet-wiring-plan.md`](2026-04-19-cottas-parquet-wiring-plan.md).

The HEAD binary at `bin/darwin-arm64/factoidal` (5.66 MB, mtime
2026-04-25 06:32 = commit `08f1855`, Wave 12) is **PRE-Tet2**. The Tet2
prepend-during-bulk-parse + `dataset_finalise` fix landed in `ac78f57`
and is in `Parser.TriG.fst:54–66` / `:494–525` and
`RDF.Graph.Executable.fst:255` (`graph_add_unchecked`) / `:261–270`
(`graph_finalise` / `dataset_finalise`). Wave 13 rebuild owns
extracting + recompiling. This doc plans against the **post-Tet2**
behaviour the next binary will have.

---

## Part A — F\* Turtle/TriG vs pyoxigraph in `tools/corpus_pipeline.py`

### Today: how `corpus_pipeline.py` uses pyoxigraph

`tools/corpus_pipeline.py:160-188` defines
`convert_rdf_to_nquads_pyoxigraph`: streams a TriG/Turtle/RDF-XML file
through `pyoxigraph.parse(src, mime)` and writes one quad per line.
It's invoked by `materialize_nq_cottas_corpus` (`:1041–1044`) for any
input format in `{trig, turtle, rdfxml}`. The fallback at `:207–234`
uses rdflib if pyoxigraph is missing. The pipeline only needs:

1. Input path + MIME → iterator yielding `(s, p, o, graph_name?)`.
2. Stable N-Quads escaping (the helper `_pyoxigraph_term` already
   does this).
3. Reasonable memory: parliament TriG is 331 MB, ~3.14 M quads.

There is **no SPARQL extension** demanded — pyoxigraph here is a
pure parser, not a query engine.

### W3C conformance: what works today

`docs/test-results/latest.csv` (CI run 2026-04-25 05:35 UTC):

- `rdf-turtle` 313 pass / 0 fail / 0 todo / 0 skip.
- `rdf-trig`   356 pass / 0 fail / 0 todo / 0 skip.

So per CLAUDE.md rule #4 + W3C conformance, the parser side is
**correct** — there's no Turtle 1.1 / TriG syntactic gap blocking a
swap. Parliament's TriG uses standard `@prefix`, named-graph blocks,
typed/lang literals, blank nodes — nothing exotic.

### Performance evidence at parliament scale

Live test `bin/darwin-arm64/factoidal --count
third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig` was
launched with a 60 s wall-clock cap (`.claude-runs/yod2-parliament-count-v2-*.log`).
On the **PRE-Tet2 binary** it does not finish in 60 s — consistent
with Delta's diagnosis: O(N²) bulk parse via `graph_add` +
`mem_triple` (`RDF.Graph.Executable.fst:248-249`) was the dominant
cost. Wave 13's POST-Tet2 binary is expected to clear this in
minutes (see Delta's table row #1: 10⁴–10⁶× speedup, parse drops to
Θ(N)). Re-benchmark once Wave 13 lands.

After Tet2, the next-tier costs are:

- **Finding 3** (Delta): fuel/positions are Zarith `Z.t`. ~6×10⁸
  ops on a 331 MB file → ≈ 3–10× constant overhead remaining.
- **Finding 4** (Delta): per-statement `append_list` in Turtle
  grammar (`Parser.Turtle.fst:1469, 1497, 1567, 1634, 1775`) is
  small for parliament (short statements) but unbounded for
  collection-heavy inputs.
- **`Parser.FastString`** (`Parser.FastString.fst:50, 60, 124`)
  uses `fs_byte_length` / `fs_byte_index` / `fs_byte_sub` — all
  byte-indexed against the underlying OCaml string. Index is O(1);
  `fs_byte_sub` is one allocation per call. Hot loops still dispatch
  through these, which is fine for correctness, costly for absolute
  speed.

### What blocks pyoxigraph removal

| # | Blocker | Severity | Mitigation |
|---|---------|----------|------------|
| 1 | Wave 13 binary not yet shipped — current `bin/darwin-arm64/factoidal` is PRE-Tet2 and cannot finish parliament TriG in <10 min. | **Hard blocker** until Wave 13 commits. | Wait for Wave 13 (in flight). Re-time `--count` on parliament; require ≤10 min, ≤2 GB RSS. |
| 2 | `corpus_pipeline.py` expects an **iterator** — pyoxigraph's `parse()` yields lazily. Today's F\* entry point `parse_trig_with_base_lenient` (`Parser.TriG.fst:519`) returns a fully-materialised `rdf_dataset`. | Medium — peak RSS doubles vs streaming. | Acceptable for parliament-scale (3 M quads ≈ ~600 MB peak). For ≥30 M quad inputs we'd need the streaming entry Delta sketches as mitigation #4 (`fold_trig`). |
| 3 | API shape: pipeline calls `pyoxigraph.parse(bytes_io, mime)` and consumes Python tuples. F\* `parse_trig_lenient` is OCaml; the bridge would shell out to the `factoidal` binary in a "convert TriG→N-Quads" mode. | Low — that mode already exists conceptually as `factoidal --dump`. | Add a one-shot `--dump --format trig --output-format nq` CLI mode if it's not already there (it is — see `factoidal --help`: `-o/--output csv,ntriples,json` plus `--dump`). |
| 4 | Performance gap vs pyoxigraph (Rust). Pyoxigraph parses parliament-sized TriG in ~30 s; post-Tet2 F\* will likely sit at 2–5 min on the same hardware (Zarith + FastString overhead). | Tolerable for a one-time corpus build; not for interactive use. | Delta mitigation #3 (machine-int positions) is a separate weeks-of-work item, not on critical path. |
| 5 | RDF/XML — `corpus_pipeline.py` accepts `.rdf/.xml/.owl`. F\* `Parser.RDFXML.fst` covers the W3C RDF/XML 11 suite. Confirmed by `factoidal --help`: `Supported RDF formats: ... RDF/XML (.rdf, .xml, .owl)`. | None at parser level. | Same Wave 13 dependency. |

### Recommended path

1. **Wait for Wave 13 + bench the parliament TriG with the new
   binary.** Goal: `factoidal --count parliament.trig` finishes in
   ≤10 min, ≤2 GB RSS.
2. If (1) passes, **add a `--rdf-parser fstar` flag to
   `corpus_pipeline.py`** (or simpler: a function
   `convert_rdf_to_nquads_fstar` symmetric to the existing
   `convert_rdf_to_nquads_pyoxigraph`) that shells out to
   `factoidal --dump --format trig --output ntriples` (or `--dump`
   with auto-detect). Keep pyoxigraph as the default for one
   release; flip default after one passing CI cycle.
3. **Do NOT remove pyoxigraph yet.** The W3C suite covers
   correctness, but pyoxigraph is also a useful cross-check
   oracle (Codex's Tet2 diagnosis cross-referenced pyoxigraph's
   3.14 M-quad output to verify our parser's count). Keeping
   both behind a flag is a feature, not tech debt.
4. **Keep an eye on Delta's mitigation #3 (machine-int positions)**
   only if (1) + post-Tet2 benchmarks show parliament still takes
   >10 min. Otherwise that's premature.

**Verdict (Part A):** *Needs Tet2 in production* — i.e. wait for
Wave 13 to extract+compile, then re-bench parliament TriG. After
that, pyoxigraph can be **demoted to fallback**, not removed.
Specific named blockers: Tet2 not yet in `bin/darwin-arm64/factoidal`
(commit `ac78f57` post-dates the binary); secondary slow path is
Zarith fuel + FastString allocation overhead, not parser correctness.

---

## Part B — JS / CLI access to the Parquet/COTTAS path

### Today's CLI surface

`factoidal --help` documents:

- `--data-cottas FILE` (repeatable). Loads a COTTAS/Parquet artifact
  via the F\*-verified Parquet footer + DeltaLengthByteArray decoder;
  Zstd via the C stub.
- Composes with `-e`, `--query`, `--count`, `--dump`, `-o`,
  `--entail`. The wiring lives at
  `formal/fstar/ocaml-output/factoidal_cli.ml:195–236` —
  `load_cottas_dataset` calls
  `Parser_BallyhooCOTTAS.cottas_open_dataset_store`, walks the cache
  populated by `Ballyhoo_cottas_runtime`, buckets quads into
  default + named graphs, returns an `rdf_dataset`.

End-to-end check (logical, not run here):
`factoidal --data-cottas data.cottas -e 'SELECT * WHERE { ?s ?p ?o } LIMIT 10'`
**should** work; what does NOT work today is *speed*. Per
`2026-04-25-cottas-parquet-load-path-perf.md`:

- 90+ s of CPU before any SPARQL evaluation begins on a 3.14 M-quad
  artifact, because `load_cache` re-probes Parquet metadata for
  **every** cell (12.6 M per-cell fetches for COUNT(\*) just to
  build the in-memory list).
- Cottas-Perf agent owns the fix: footer cache + per-page column
  decode + lazy/streaming load.

UX gaps in the current CLI:

- No `--cottas-info FILE` to dump artifact stats (file size,
  row count, page count, dictionary sizes) without doing a full
  load. Useful for debugging the perf cliff.
- No streaming N-Quads emit (`--data-cottas FOO --dump`) that
  bypasses the eager dataset rebuild. Adding this is a
  Cottas-Perf-aligned task.
- Error path is `exit 1` with a single line; no `--verbose`
  diagnostic for footer-decode failures.

### JS bridge story

There is no path to Parquet from the JS bundle today
(`docs/fstar-extracted/factoidal.js`). Reasons:

1. **Zstd is C.** `formal/fstar/experimental_ocaml_glue/parquet_zstd_stubs.c`
   is a thin wrapper around `libzstd`. js_of_ocaml does not link
   C stubs — only OCaml-level stubs.
2. **Footer probing reads bytes from disk.** The OCaml glue assumes
   `Unix.openfile` / `Bytes.unsafe_get`. The browser has neither.
   We'd need to feed the parser a `Uint8Array` from `fetch()` or
   `File`.
3. **Bundle size.** A pure-JS zstd is ~50 KB gzipped (e.g.
   `fzstd`); not free, but tolerable. A WASM zstd is ~30 KB.
   Either is small relative to the existing 7 MB+ js_of_ocaml
   bundle.

Three plausible paths:

#### (a) Pure-OCaml zstd decoder

Replace `parquet_zstd_stubs.c` with a pure-OCaml zstd implementation
(e.g. extend an existing minimal-zstd library, or vendor one).

Pros: no FFI, js_of_ocaml extracts cleanly.
Cons: pure-OCaml zstd is ~5–10× slower than libzstd; correctness
risk on edge cases (window sizes, dictionary mode, long-range mode);
a non-trivial multi-week port. **Violates "no cobbling" if we
hand-write it; OK if we vendor a maintained library.** No verified
F\* zstd exists; this would not be F\*-extracted.

#### (b) WASM zstd shim alongside the F\* extracted bundle

Bundle a tiny zstd JS/WASM shim (`fzstd` or `zstd-codec`) and replace
the C-level stub with a JS-level stub that calls into it. The F\*
extracted code stays the same; only the runtime glue swaps.

Pros: minimal new code; leverages a maintained C-compiled-to-WASM
zstd. Footer probing logic stays in F\*.
Cons: still need to thread `Uint8Array` through to the Parquet
reader. Probably needs new `Parser.BallyhooCOTTAS.fst` entry points
that take `seq byte` rather than a file handle.

#### (c) Server-side: factoidal-http SPARQL endpoint as the wire

Browser hits `factoidal-http` (already at `bin/darwin-arm64/factoidal-http`)
over SPARQL Protocol; `factoidal-http` is the only thing that ever
reads `*.cottas`. The browser sees only result formats (SRX/JSON/CSV).

Pros: zero browser changes; uses existing components; matches MDB's
deployment model (SIGMOD demo serves Wikidata via SPARQL endpoint).
Aligns with rule #5 (full SPARQL Protocol is in scope).
Cons: requires a server somewhere; doesn't help the "static GitHub
Pages demo" use case; doesn't help offline.

### Recommendation

**Phase 1 (now):** Path (c). Keep COTTAS server-only. The
`factoidal-http` binary already exists; just document that the
browser demo route for COTTAS is "stand up factoidal-http and
point it at your `.cottas` file". Cost: a paragraph in
`docs/`. Zero JS work.

**Phase 2 (after Cottas-Perf lands the footer cache + per-page
decode):** Re-evaluate (b). If the F\* COTTAS reader is rewritten
to take `seq byte` rather than a file path (which it should be
anyway, for testability), then a JS `Uint8Array` slice can flow
through the same code. At that point a 30 KB WASM zstd shim is
the only remaining browser-side cost.

**Phase 3 (only if there's user demand):** Path (a) — pure-OCaml
zstd. Skip unless someone explicitly wants offline Parquet without
a server.

### CLI fixes worth doing in the meantime (independent of JS)

1. `factoidal --cottas-info FILE` — dump footer + page metadata
   without loading any column data. Cheap; one-shot.
2. `factoidal --data-cottas FOO --dump` — streaming N-Quads
   emit. After Cottas-Perf's lazy-load lands, this becomes
   constant-memory and trivially fast.
3. Diagnostic `--verbose` flag that times each phase
   (footer-probe / dictionary-decode / page-decode / quad-build).
   Mirrors the instrumentation Codex's perf doc asked for.

**Verdict (Part B):** **(c) for Phase 1 — server-side via
factoidal-http SPARQL endpoint.** No JS work. Re-evaluate (b)
once the F\* COTTAS reader takes `seq byte` rather than a file
path. (a) is escape valve only.

---

## Tracking

- Wave 13 rebuild (in flight) — owner: main thread.
- Re-bench parliament TriG with post-Tet2 binary — depends on Wave 13.
- Cottas-Perf footer-cache patch — separate agent.
- This scoping doc is the input to a future "swap pyoxigraph for
  F\*" PR; do **not** start that PR until Wave 13 closes and the
  bench passes.
