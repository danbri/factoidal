---
title: "How fast: the performance story"
description: "Every number here carries a date and a commit — Turtle throughput, the streaming fast path, and the COTTAS on-disk reader wins, plus one in-browser timing illustration (not a benchmark)."
layout: hub.njk
series: docs-hub
series_order: 15
vocab: wikidata
status: published
tests: tests/hub/post15_test.mjs
---

Every other post in this series asked "is it correct" — W3C test suites,
pass/fail counts, no synthetic queries. This post asks "is it fast," and
that question gets a different discipline: [`skills/perf-benchmarking/SKILL.md`](https://github.com/danbri/factoidal/blob/claude/main/skills/perf-benchmarking/SKILL.md)
requires every speed claim in this project to carry a date and a commit,
measured separately from any correctness change, never asserted from
memory. Every number below follows that rule — no bare "faster now"
claims.

## Parsing throughput

Against the committed native binary, Turtle parsing holds
**~100k triples/second, near-linear scaling through 1,000,000 triples**
(1M in 9.66s):

| N triples | Time | Rate |
|---|---|---|
| 1,000 (prefixed) | 0.02 s | ~50k triples/s |
| 100,000 | 0.93 s | ~108k triples/s |
| 1,000,000 | 9.66 s | ~104k triples/s |

Measured 2026-07-03, commit
[`11ba254`](https://github.com/danbri/factoidal/commit/11ba254) — see
[`docs/claude-rules/performance.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/claude-rules/performance.md)
for the full table and the 2026-04 slow-Turtle history this replaced
(1,000 triples took 25s under the earlier implementation).

## The streaming fast path: RAM bounded by the answer, not the store

Parsing is fast, but a naive query has to materialize the *entire*
graph into memory before answering even a one-row question.
`SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }` over 888,949 triples
(the vendored Wikidata life-sci gene subset) cost 730.5 MiB peak RSS
and 28.4 seconds — RAM and time scaling with the whole store, not with
the one integer the query actually returns. A new one-pass streaming
path answers `COUNT`/`ASK` shapes directly off the parse stream, never
building the graph at all:

| | Before | After |
|---|---|---|
| Peak RSS | 730.5 MiB | **44.1 MiB** (16.6× less) |
| Wall time | 28.4 s | **6.6 s** (4.3× faster) |

Measured 2026-07-05, commit
[`7cd6465`](https://github.com/danbri/factoidal/commit/7cd6465) — the
full writeup, including the exact query shapes the fast path covers
(single-triple-pattern `COUNT`, `GRAPH ?g` wildcard `COUNT`, early-stop
`ASK`) and the correctness pinning
(`tests/local/streamable_fastpath_regressions.sh`, 13 pass, 0 fail), is
in [`docs/designissues/2026-07-05-disk-backed-db-perf-review.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-05-disk-backed-db-perf-review.md).

## COTTAS on-disk reader wins

The on-disk COTTAS (Parquet-backed quad store) reader carries three
separate, individually measured fixes — a pattern worth naming
explicitly: each is a specific bug found by measuring, not a general
"made it faster":

| Fix | Before | After | Commit |
|---|---|---|---|
| Row-group offset table (eliminated an O(row-groups²) per-locate walk in the Parquet footer reader) | `?s rdf:type ?o LIMIT 5` at 44 row groups: ~1,427–1,446 ms | **83–84 ms** | [`f82cbfa`](https://github.com/danbri/factoidal/commit/f82cbfa), 2026-07-06 |
| `.dict` magic-constant fix (writer and validator disagreed, forcing a sidecar rebuild on every boot) | second server boot: 57.3 s | **0.26–0.27 s** | [`4b9fd72`](https://github.com/danbri/factoidal/commit/4b9fd72), 2026-07-05 |
| Selective-column count walk (a bound-predicate `COUNT` no longer decodes the two unrelated high-cardinality columns it never needed) | cold `COUNT` of a universal predicate: ~55 s (54.99–58.26 s measured) | **2.77–2.82 s** | [`7af6bbd`](https://github.com/danbri/factoidal/commit/7af6bbd), 2026-07-06 |

Each of these is a specific mechanism, diagnosed with `strace` evidence
ruling out I/O as the cost and pinned with a regression test, not a
vague "on-disk got faster" — see
[`docs/designissues/2026-07-05-disk-backed-db-perf-review.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-05-disk-backed-db-perf-review.md)
for the full root-cause writeup behind each row, including one
correctness bug (a compound-index ID-space mismatch) found while
chasing these wins — covered in
[the next post](./16-the-verified-in-fstar-story.md), because it's a
story about proof coverage, not speed.

The on-disk store is what serves the
[UK Parliament live demo]({{ '/web/demos/ukparliament/' | url }}) — 3,143,406
real quads, queryable today. Per Iron Rule #11, that demo (and every
claim above touching the on-disk reader) carries this project's
standing qualifier verbatim:

> parser and algebra spec verified in F\*; on-disk backend has
> unverified OCaml-side optimization layers being migrated back to F\*
> (see fstar-purity-unwind.md)

The three fixes in the table above are progress *inside* that
qualifier (some, like the offset table, are verified F\* fixes to
`Parquet.Footer.fst`; others, like the selective-column walk, are
F\* too — see the perf review doc for which is which) — not a claim
that the qualifier has been lifted.

## Try it yourself — an in-browser illustration, not a benchmark

The cell below generates a few thousand triples right here in your
browser, parses them, runs one query, and times the whole thing with
`performance.now()`. This is **not a benchmark** — it runs on whatever
JavaScript engine and hardware loaded this page, with no warmup, no
repetition, and no isolation from everything else the tab is doing.
Every number in the tables above came from the committed native binary
under controlled, repeated measurement; this cell is here so you can
watch the same engine work, not to produce a citable figure:

```observable-js
const N = 3000;
let nquads = "";
for (let i = 0; i < N; i++) {
  nquads += `<http://example.org/person${i}> <http://xmlns.com/foaf/0.1/name> "Person ${i}" .\n`;
}

const t0 = performance.now();
const dataset = await fn.parse(nquads, { format: "nquads" });
const rows = await fn.query(dataset, `# How many triples the parsed graph holds: count every solution of the
# open triple pattern ?s ?p ?o.
SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`);
const t1 = performance.now();

return pretty({
  note: "in-browser illustration only -- uncontrolled JS engine, not a benchmark",
  triplesGenerated: N,
  countResult: Number(rows[0].get("n").value),
  parseAndQueryMs: Math.round(t1 - t0),
});
```

`countResult` should read back `3000` — confirming the generated
triples actually round-tripped through the real F\*-extracted parser
and SPARQL evaluator — with `parseAndQueryMs` whatever this page's
engine took on your device, right now.

## What's next

[The next post](./16-the-verified-in-fstar-story.md) is this series'
last: why F\*, what "verified" actually means here, and what proof
caught — along with what a proof gap missed — while these performance
fixes were made.

The live cell above is pinned in
[`tests/hub/post15_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post15_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn` adapter.
