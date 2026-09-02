---
title: "Mutating and serving data: SPARQL Update, Protocol, Graph Store"
description: "SPARQL 1.1 Update live in your browser via the npm-entry ABI, the durable delta-log write path that gives updates a crash-safe home on disk, and what factoidal-http and the Graph Store Protocol do and don't do."
layout: hub.njk
series: docs-hub
series_order: 17
vocab: foaf
status: published
tests: tests/hub/post17_test.mjs
---

Every post so far in this series read data. This one writes it —
SPARQL 1.1 Update, and then, because a write that vanishes on restart
isn't durable, the delta-log write path that gives updates a crash-safe
home on disk.

## SPARQL 1.1 Update: not a gap

`SPARQL11.Algebra.fst:5733`'s `apply_update : rdf_dataset ->
sparql_update -> rdf_dataset` is a verified, total F\* function
implementing INSERT DATA, DELETE DATA, DELETE/INSERT WHERE, CLEAR, and
full graph management (ADD/COPY/MOVE/CREATE/DROP) — LOAD is accepted by
the algebra but rejected defensively at the HTTP sandbox layer
(`SPARQL.Update.Analysis.fst`'s `update_has_load`, an operational
policy decision, not a gap in the algebra). The W3C SPARQL 1.1 Update
conformance suite — 14 manifests, 176 test cases — scores **176 pass, 0
fail (out of 176)**, per
[`docs/test-results/latest.json`](https://github.com/danbri/factoidal/blob/claude/main/docs/test-results/latest.json)
(2026-07-06 05:29 UTC, commit
[`616247d`](https://github.com/danbri/factoidal/commit/616247d)):
`add` 8/8, `basic-update` 13/13, `clear` 4/4, `copy` 6/6, `delete`
19/19, `delete-data` 6/6, `delete-insert` 17/17, `delete-where` 6/6,
`drop` 4/4, `move` 6/6, `syntax-update-1` 54/54, `syntax-update-2`
1/1, `update-silent` 13/13, `http-rdf-update` 19/19.

### Try it — INSERT DATA, live

`docs/_includes/hub.njk`'s `fn` adapter now wires up `update` —
`fn.update(dataset, updateText)` — the same typed shape
`npm/factoidal/index.js`'s `update(data, updateText) -> Dataset`
exposes, built on the raw npm-entry ABI's `updateDataset` export
underneath (the js_of_ocaml build this whole series' cells run
against). This cell wraps it in a try/catch per the
[cell contract](../README/)'s capability-check pattern (an older bundle
might predate the Update export), and actually runs an INSERT DATA:

```observable-js
const ttl = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  <http://example.org/alice> foaf:name "Alice" .
`;

try {
  const before = await fn.parse(ttl, { format: "turtle" });

  const insertData = `# Add Bob's name to the dataset as a new ground triple.
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    INSERT DATA { <http://example.org/bob> foaf:name "Bob" . }
  `;
  const after = await fn.update(before, insertData);

  const rows = await fn.query(
    after,
    `# List every name now in the dataset, alphabetically.
    PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?s foaf:name ?name } ORDER BY ?name`
  );

  return {
    available: true,
    namesBeforeInsertData: ["Alice"],
    namesAfterInsertData: rows.map((row) => row.get("name").value),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

`namesAfterInsertData` should read `["Alice", "Bob"]` — Bob's triple,
inserted by a real `apply_update` call running in your browser right
now, is already there when the very next query runs.

### Try it — DELETE/INSERT WHERE

INSERT DATA/DELETE DATA only ever touch ground triples. The pattern
most real edits need is DELETE/INSERT WHERE — find whatever matches a
pattern, then replace it. Same `fn.update`, same engine, correcting
Bob's name in place rather than deleting and re-inserting by hand:

```observable-js
const ttl2 = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  <http://example.org/alice> foaf:name "Alice" .
  <http://example.org/bob> foaf:name "Bob" .
`;

try {
  const before = await fn.parse(ttl2, { format: "turtle" });

  const deleteInsertWhere = `# Rename Bob to Bobby: find the triple matching foaf:name "Bob"
    # and replace it with foaf:name "Bobby".
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    DELETE { ?s foaf:name "Bob" }
    INSERT { ?s foaf:name "Bobby" }
    WHERE  { ?s foaf:name "Bob" }
  `;
  const after = await fn.update(before, deleteInsertWhere);

  const rows = await fn.query(
    after,
    `# List every name now in the dataset, alphabetically.
    PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?s foaf:name ?name } ORDER BY ?name`
  );

  return {
    available: true,
    namesAfterDeleteInsertWhere: rows.map((row) => row.get("name").value),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

`namesAfterDeleteInsertWhere` should read `["Alice", "Bobby"]` — the
`WHERE` clause found the one triple matching `foaf:name "Bob"`, and
the `DELETE`/`INSERT` pair swapped it for `"Bobby"` in a single
request, entirely in your browser, against the same engine
`bin/linux-x86_64/factoidal` runs natively.

## Durability: a crash-safe delta log

Everything above runs `apply_update` over a plain in-memory
`rdf_dataset` — correct, but gone the moment the process exits. To make
an update survive a restart, factoidal writes it to an append-only
delta log on disk, specified first in
[`docs/designissues/2026-07-06-durable-update-design.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-06-durable-update-design.md).
Three layers make that work, each with its own proof and measurement:

**The delta-log entry format, proved.**
[`RDF.Store.Columnar.DeltaLog.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Store.Columnar.DeltaLog.fst)
defines the five delta-entry shapes an update can produce
(`DE_Add`/`DE_Remove`/`DE_Clear`/`DE_Drop`/`DE_Create`), each
serialized to a length-prefixed, checksummed byte frame. The module's
payoff is a proved lemma, not an assertion: `parse_delta_entry
(serialize_delta_entry e ++ rest) == Some (e, rest)` for every
well-formed entry — parsing what serializing just wrote is a
**theorem**, checked by Z3 4.13.3, not a round-trip test that merely
happened to pass. 74 unit assertions (every constructor, non-ASCII and
astral-plane UTF-8, a 100KB literal, 8 corruption cases) additionally
pin the extracted OCaml against the same claim
([`868a20b`](https://github.com/danbri/factoidal/commit/868a20b)).

**A crash-safe log file.** The same module's `delta_batch`/`DLOG` file
layer adds streaming `serialize_log`/`parse_log` with an extended
round-trip lemma, realized on disk by five `assume val` I/O primitives
(append/fsync/read-all/atomic-rename/fsync-dir — issue #282, per Iron
Rule #3). The check that matters for a crash-safety claim:
`tests/local/delta_log_crash_harness.sh` SIGKILLs a writer process
mid-append at random points and confirms the log recovers a clean
prefix every time — **270 kills, 270 clean recoveries, 0 corrupt
accepts** over two seeded runs
([`1f27320`](https://github.com/danbri/factoidal/commit/1f27320)).

**Reads see the delta.**
[`RDF.Store.Columnar.DeltaMerge.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Store.Columnar.DeltaMerge.fst)'s
`merge_on_read` composes a base graph's rows with a resolved delta
(adds, tombstoned removes, CLEAR/DROP/CREATE applied in sequence
order), backed by a **proved** correspondence lemma
(`lemma_merge_on_read_matches_apply_entries`): for every triple,
membership in the reference application of delta entries to the base
graph equals membership in the merged read. The CLI's `--delta-log
PATH` (alongside `--data-cottas`) routes a query through this path
([`5e8399a`](https://github.com/danbri/factoidal/commit/5e8399a),
`tests/local/durable_update_stage3.sh`, 15 pass, 0 fail, plus a
25-kill-iteration harness with 25 clean recoveries).

One boundary, stated plainly rather than oversold: the proved lemma
covers `merge_on_read` against *delta entries*, the primitive op
shapes. The fuller lemma over real SPARQL `update_op` values (what
`apply_update` consumes) rests on the `update_ops_to_delta_entries`
translator, which is pinned by acceptance test rather than by proof.
That gap is written into the module itself as a residual.

**Compaction** — folding an accumulated delta back into a fresh
`.cottas` base so the log doesn't grow without bound — has since
landed as `factoidal compact` (durable-UPDATE stage 4): each
compaction writes a full new artifact set under a versioned directory
and repoints a `current` symlink, so older epochs stay queryable and
a crash mid-compaction never corrupts the live store.

**What the delta log still does not have:**

- **Parliament-scale validation**: the delta-penalty measurement
  (empty-delta query cost must match the base-file baseline; a
  realistic-size delta must add a small, bounded cost, not scale with
  corpus size) has not been run against the full 3.14M-quad UK
  Parliament store — it needs corpus access the sandbox doesn't have,
  the same caveat the
  [performance post](./15-how-fast-the-performance-story.md)'s COTTAS
  numbers carry.

Every claim above carries its own commit rather than a blanket "durable
UPDATE shipped" — the write path and compaction are real and measured;
the Parliament-scale run is not.

## Serving: the SPARQL Protocol, observability, and the Graph Store gap

`bin/factoidal-http` is the standalone SPARQL 1.1 Protocol server:
`GET`/`POST /query` (and `/sparql`), `POST /update`, a `--read-only`
flag that turns the latter into a 403, and CORS controls — the same
34/34 `protocol` suite score cited above covers this dispatch layer.
It's what serves the
[live UK Parliament demo]({{ '/web/demos/ukparliament/' | url }}) —
**3,143,406 real quads**, queryable today over the actual SPARQL 1.1
Protocol, not a mock.

Every query against it produces layered timing data
([`docs/observability.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/observability.md)):
a fixed-field stderr line per query (operator-only), a machine-readable
`Server-Timing` response header (`parse;dur=0, eval;dur=137000,
format;dur=0, total;dur=137001`, renders natively in browser DevTools),
and `/admin/recent.json` (last 50 queries + counters). The
`Server-Timing` header is the one surface gated by policy — per issue
[`#266`](https://github.com/danbri/factoidal/issues/266), per-stage
timing can leak query-cost information (named-graph cardinality, FILTER
selectivity) to a requester who shouldn't observe it, so
`--server-timing` defaults to `auto`: **off** whenever the deployment
looks multi-tenant or tunnel-exposed (a per-user write sandbox flag is
set, CORS is anything but off, or the bind host isn't loopback), **on**
otherwise. `on`/`off` are also available as explicit overrides. The
stderr line and `/admin/recent.json` are operator-only and are never
gated — only the header that goes back to the requester is.

**Graph Store Protocol: specified, proven, and routed**
([`e8085da`](https://github.com/danbri/factoidal/commit/e8085da)).
[`SPARQL.GraphStore.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/SPARQL.GraphStore.fst)
is a verified, `assume-val`-free F\* module implementing the five GSP
operations (`gsp_get`/`gsp_head`/`gsp_put`/`gsp_post`/`gsp_delete`) over
a `graph_store` value — PUT-creates-vs-replaces, POST-merges,
DELETE-existence, all decided in F\*, not in a runner shim. It's
exercised by the W3C `http-rdf-update` manifest's stateful test
sequence in the test runner (19/19, cited above) — a suite-level shared
store that runs PUT/POST/DELETE against it across a whole manifest.

`bin/factoidal-http/factoidal_http.ml` wires
`GET`/`HEAD /data?graph=...` unconditionally and `PUT`/`POST`/`DELETE`
under a `--rw` flag, through total GSP-to-delta-entry translators
(`update_ops_to_delta_entries`'s sibling for GSP verbs), with
`SPARQL.GraphStore.fst`'s own spec-correct status codes, 405 without
`--rw`. One limitation is disclosed rather than papered over: a
`DELETE` durably clears a named graph's content, but a later `GET` may
still answer `200` with an empty body rather than `404` — the
merge-on-read architecture doesn't yet distinguish "emptied" from
"never existed." Acceptance:
`tests/local/durable_update_stage8_http.sh`, 29 pass, 0 fail (a curl
matrix over all five GSP verbs, plus concurrent-reader/SIGKILL-mid-
write recovery checks). [Post 18](./18-the-durable-log-live.md) picks
up the in-browser side of this same durable-UPDATE story.

## Related

[The verified-in-F\* post](./16-the-verified-in-fstar-story.md) covers
why F\* and what "verified" means here.
[Post 18](./18-the-durable-log-live.md) runs the durable-UPDATE
lifecycle — update, persist, reload, corrupt, recover — live in your
browser.

The live cells above are pinned in
[`tests/hub/post17_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post17_test.mjs) —
the exact same source, executed against the real `npm/factoidal` typed
API instead of the in-browser `fn` adapter.
