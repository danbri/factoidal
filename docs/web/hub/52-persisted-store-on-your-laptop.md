---
title: "The persisted store on your laptop: what a query costs"
description: "Measured on 2026-09-02: pack 888,949 and 1,290,077 Wikidata life-sciences triples into Shardborough IBK3 generations, activate them, and answer a SPARQL workload through the Lean native harness in under a second per query, with the theorems and checks each number rests on."
layout: hub.njk
series: docs-hub
series_order: 52
vocab: sparql
status: experimental
tests: tests/hub/post52_test.mjs
hubHideCellSource: true
hubEngineLabel: "numbers recorded from the Lean native harness on 2026-09-02; this page renders them"
---

The [Shardborough notebook](../50-shardborough-life-sciences/) runs on twelve
blocks inside the browser. This page is about the same format on disk, at
the sizes the browser worker does not yet take: the whole `gene.ttl`
extract (888,949 triples) and the whole life-sciences extract (1,290,077
triples), packed by the Lean publisher, activated, and queried through the
native harness. Nothing here runs live; the cell below renders the numbers
recorded on one laptop on 2026-09-02, and the commands that produce them
are listed so you can reproduce them. The record with every intermediate
measurement is
[the persisted query ladder worknote](../../../20260902-persisted-query-ladder/).

## Five commands

```bash
cd formal/lean4 && lake build              # once
B=.lake/build/bin
$B/l4block-shard-pack gene.ttl COLL/gen-1 ibk3   # 13 IBK3 blocks + sidecars + SBM6 manifest
$B/l4block-shard-activate COLL gen-1            # verify everything, then CURRENT = gen-1
$B/l4block-id-v3-query COLL --query 'SELECT ...' # query the collection root
$B/l4block-delta-log COLL --update 'INSERT DATA { ... }'   # durable delta, visible at once
$B/l4block-shard-compact COLL/gen-1 COLL/gen-2 && $B/l4block-shard-activate COLL gen-2
```

## The workload, before and after one day of work

```observable-js
milestone = ({
  store: { source: "gene.ttl", triples: 888949, blocks: 13, predicates: 6, bytesOnDisk: "50 MB" },
  rows: [
    { id: "q1", shape: "COUNT(*) over everything", rows: 1, morning: "12.5 s", evening: "3.9 s", path: "full read of every block; HACL* SHA-256 Merkle verification" },
    { id: "q2", shape: "COUNT of P684 (759,263 rows)", rows: 1, morning: "1.95 s", evening: "1.3 s", path: "per-predicate count" },
    { id: "q3", shape: "subject point lookup, unbound predicate", rows: 3, morning: "10.0 s", evening: "0.12 s", path: "term index + subject postings of every block" },
    { id: "q4", shape: "two-pattern join P684 / P682", rows: 14, morning: "0.17 s", evening: "0.07 s", path: "subject join, hash join" },
    { id: "q5", shape: "GROUP BY ?p with counts", rows: 6, morning: "2.4 s", evening: "0.62 s", path: "per-predicate counts" },
    { id: "q6", shape: "?s P1057 ?o1 . OPTIONAL { ?s P688 ?o2 } FILTER(isIRI(?o1))", rows: 25083, morning: "31.8 s", evening: "0.86 s", path: "two predicates' blocks, hash LeftJoin" },
    { id: "s1", shape: "?s P684 ?o LIMIT 10", rows: 10, morning: "0.66 s", evening: "0.03 s", path: "bounded prefix scan" },
    { id: "o1", shape: "?s P682 wd:Q14860489", rows: 0, morning: "0.05 s", evening: "0.01 s", path: "object postings scan" },
  ],
  nextRung: { source: "all twelve life-science files", triples: 1290077, blocks: 52, predicates: 26, bytesOnDisk: "103 MB",
    pack: "35.8 s", activate: "45.5 s",
    rows: [
      { id: "q1", shape: "COUNT(*) over everything", time: "10.3 s" },
      { id: "q3", shape: "subject point lookup, unbound predicate", time: "0.20 s" },
      { id: "q4", shape: "two-pattern join", time: "0.05 s" },
      { id: "q5", shape: "GROUP BY ?p", time: "0.66 s" },
      { id: "q6", shape: "OPTIONAL + FILTER", time: "0.36 s" },
      { id: "s1", shape: "LIMIT 10 scan", time: "0.02 s" },
    ] },
})
```

```observable-js
milestoneTable = {
  const m = milestone;
  const cell = (t, cls) => html`<td class=${cls || ""}>${t}</td>`;
  const row = r => html`<tr><td>${r.id}</td><td><code>${r.shape}</code></td><td>${r.rows.toLocaleString()}</td><td>${r.morning}</td><td class="now">${r.evening}</td><td>${r.path}</td></tr>`;
  const row2 = r => html`<tr><td>${r.id}</td><td><code>${r.shape}</code></td><td class="now">${r.time}</td></tr>`;
  return html`<div class="milestone">
    <style>
      .milestone table { width:100%; border-collapse:collapse; font-size:.92rem; }
      .milestone th, .milestone td { text-align:left; padding:.35rem .5rem; border-bottom:1px solid #d6e6ec; vertical-align:top; }
      .milestone td.now { font-weight:700; color:#1d5e3a; }
      .milestone caption { text-align:left; font-weight:600; padding:.4rem 0; }
    </style>
    <table>
      <caption>${m.store.source}: ${m.store.triples.toLocaleString()} triples, ${m.store.blocks} blocks, ${m.store.bytesOnDisk} on disk. Single cold runs; same rows in both columns.</caption>
      <thead><tr><th>#</th><th>Query shape</th><th>Rows</th><th>Morning</th><th>Evening</th><th>Path taken</th></tr></thead>
      <tbody>${m.rows.map(row)}</tbody>
    </table>
    <table>
      <caption>Next rung: ${m.nextRung.source}, ${m.nextRung.triples.toLocaleString()} triples, ${m.nextRung.blocks} blocks over ${m.nextRung.predicates} predicates, ${m.nextRung.bytesOnDisk} on disk; pack ${m.nextRung.pack}, activate ${m.nextRung.activate}.</caption>
      <thead><tr><th>#</th><th>Query shape</th><th>Time</th></tr></thead>
      <tbody>${m.nextRung.rows.map(row2)}</tbody>
    </table>
  </div>`;
}
```

The selective paths scale with the number of blocks a query touches, not
with the triple count: the subject lookup probes every block's term index
and subject postings and went from 0.12 s over 13 blocks to 0.20 s over 52.
The two costs that grow with bytes are activation, which verifies every
artifact and recomputes every index relation once per generation, and the
whole-store count, which reads everything.

## What the numbers rest on

- **The bytes.** Every complete-artifact codec of the format family (the term
  codec, PTD1, IBK3, SRI2/OLI2, TLI1) has a kernel-checked round-trip theorem
  with `encode? = some bytes` as its only hypothesis, because each encoder
  now refuses exactly what its decoder would refuse
  ([specification section 10.1](../../../shardborough-storage-spec/#101-gate-2-progress-2026-09-02)).
- **The joins.** The hash join and the hash LeftJoin are each proved equal
  to their nested-loop specification as a list, rows and order
  (`hashJoin_eq_join`, `hashLeftJoin_eq_leftJoin`), and the backend arms
  that use them carry their own theorems.
- **The hash.** SHA-256 is the pure Lean function that every guard and
  theorem uses; the host passes a HACL*-backed hasher for speed, and a
  differential probe over the FIPS vectors, block boundaries and a 1 MiB
  buffer is a required CI step.
- **The answers.** The Lean W3C SPARQL 1.1 suite: 631 pass, 0 fail (out of
  631). The persisted-path executability census: 535 of 535 eligible
  evaluation tests pack, activate and answer.
- **Not yet a theorem.** The planner's choice of which blocks to open is
  argued in its docstrings and checked by the census and by comparing row
  counts and previews against the full-manifest path, not proved. The
  quad-aware layout that puts named graphs into the bytes is
  specification gate 4 and is what the next rung, a 347 MB TriG dump with
  named graphs, waits on.

Operating manual for the commands above: the
[`shardborough-storage` skill](https://github.com/danbri/factoidal/blob/claude/main/skills/shardborough-storage/SKILL.md).
