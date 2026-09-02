---
title: "The durable log, live: update, persist, reload, corrupt"
description: "The full durable-UPDATE lifecycle running in your browser -- parse, SPARQL UPDATE, IndexedDB persistence proved across a real reload, and a checksum-rejection demo -- plus the same F* delta-log module proven running natively, as KaRaMeL C, and as wasm_of_ocaml too."
layout: hub.njk
series: docs-hub
series_order: 18
vocab: foaf
status: published
tests: tests/hub/post18_test.mjs
---

[Post 17](./17-mutating-and-serving-data.md) covered SPARQL 1.1 Update
running live and the durable delta-log write path. This post runs the
**whole lifecycle in the page** — parse, update, persist, reload, and
corrupt — and then shows that the exact same F\* module proving all of
it is not a browser-only trick. It runs natively, it
runs as KaRaMeL-extracted C, and it runs as `wasm_of_ocaml` too — the
wasm npm-entry bundle now ships `DeltaLog`/`DeltaMerge`, and a
require.main path bug in `wasm.js`'s entry loader that had silently
broken every wasm-side capability probe (SHACL, ShEx, OWL/RDFS
closure, RML, CSVW, JSON-LD, RIF, and this delta log alike) is fixed.

Nothing below is a mock. Every cell calls the real
`RDF_Store_Columnar_DeltaLog`/`RDF_Store_Columnar_DeltaMerge` functions
`fstar.exe --codegen` produced from
[`RDF.Store.Columnar.DeltaLog.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/RDF.Store.Columnar.DeltaLog.fst) —
the same module the native CLI's `--delta-log` flag and
`factoidal-http --rw` use, compiled to `js_of_ocaml` instead of native
code, running against real browser `IndexedDB`.

## Step 1 of 4: parse and update, in memory

Same `fn.update` [post 17](./17-mutating-and-serving-data.md)
introduced, capability-checked per the [cell contract](../README/)'s
try/catch pattern:

```observable-js
const ttl = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  <http://example.org/alice> foaf:name "Alice" .
  <http://example.org/bob> foaf:name "Bob" .
`;

try {
  const before = await fn.parse(ttl, { format: "turtle" });

  const addCarol = `
    # Add a name for Carol.
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    INSERT DATA { <http://example.org/carol> foaf:name "Carol" . }
  `;
  const after = await fn.update(before, addCarol);

  const rows = await fn.query(
    after,
    `# Every foaf:name in the updated graph, in alphabetical order, to show
# that Carol is now present.
PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?s foaf:name ?name } ORDER BY ?name`
  );

  return {
    available: true,
    step: "1 of 4 -- apply_update, in memory only (gone the instant this tab closes)",
    namesAfterInsert: rows.map((row) => row.get("name").value),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

`namesAfterInsert` should read `["Alice", "Bob", "Carol"]`. This is
exactly what every cell in this series has done since post 2 — correct,
and gone the moment you close the tab. The next three cells are the
part that's new.

## Step 2 of 4: persist it, durably, via IndexedDB

This is not the same code path as Step 1. `deltaLogAppend` translates
a SPARQL Update into a `delta_batch`
(`RDF_Store_Columnar_DeltaMerge.update_ops_to_delta_entries` — INSERT
DATA/DELETE DATA/CLEAR/DROP/CREATE only, the same subset the native
`--rw` commit path accepts), serializes it with the **proved**
round-trip framing
(`RDF_Store_Columnar_DeltaLog.serialize_delta_batch`), and commits it
to a real `IndexedDB` object store with `durability: 'strict'`
requested explicitly (Chrome quietly changed its own default to
`'relaxed'` from Chrome 121 onward — this cell does not silently
inherit that weaker guarantee). None of this touches `npm/factoidal`,
`lib/api.js`, or the engine's parser/algebra code — `browser.js`'s
`deltaLogOpen`/`deltaLogAppend`/`deltaLogReadAllHex`/`deltaLogMerge`/
`deltaLogDestroy` (commit
[`8ff60eb`](https://github.com/danbri/factoidal/commit/8ff60eb)) move
opaque hex bytes only; the F\* functions still do every byte decision.

```observable-js
try {
  const handle = await Factoidal.deltaLogOpen("factoidal-hub-post18-lifecycle");
  const result = await Factoidal.deltaLogAppend(
    handle,
    `# Add one triple giving ex:dana the foaf:name "Dana", as a durable
# delta-log entry rather than an in-memory update.
INSERT DATA { <http://example.org/dana> <http://xmlns.com/foaf/0.1/name> "Dana" . }`
  );
  return {
    available: true,
    step: "2 of 4 -- deltaLogAppend: one durable delta entry, committed to IndexedDB",
    seq: result.seq,
    opCount: result.opCount,
    note: "seq is this batch's position in the durable log -- reload this " +
      "page for real (not just re-running the cell) and watch seq keep " +
      "climbing instead of resetting to 0. That's the persistence proof.",
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

**Try it now: reload this page.** Not "re-run the cell" — an actual
browser reload (Cmd/Ctrl+R, or the reload button). Every cell on this
page auto-runs again from scratch, including this one, in a brand-new
JS heap with no memory of anything above. If `seq` reads anything
other than `0` after that reload, the data survived something a plain
in-memory `rdf_dataset` never could: the whole page tearing down and
starting over.

## Step 3 of 4: read the log back and merge

This cell does not share any JavaScript state with Step 2 — it opens
the *same* `IndexedDB` database fresh, reads every committed batch back
(`deltaLogReadAllHex`), and merges them onto an empty base graph via
`RDF_Store_Columnar_DeltaMerge.apply_entries_ref`, the function backed
by a **proved** correspondence lemma
(`lemma_merge_on_read_matches_apply_entries` — for every triple,
membership in the reference application of delta entries equals
membership in the merged read).

```observable-js
try {
  // Step 2's cell and this one mount independently and can start
  // executing concurrently on the very FIRST page load this browser
  // has ever seen -- a brief wait here avoids racing Step 2's write.
  // On every later reload this is moot: Step 2's earlier writes are
  // already durably committed long before this page load even starts.
  await new Promise((resolve) => setTimeout(resolve, 300));

  const handle = await Factoidal.deltaLogOpen("factoidal-hub-post18-lifecycle");
  const hexBlobs = await Factoidal.deltaLogReadAllHex(handle);
  const batchesInLog = hexBlobs ? hexBlobs.split("\n").filter(Boolean).length : 0;
  const merged = await Factoidal.deltaLogMerge(handle, "");

  return {
    available: true,
    step: "3 of 4 -- deltaLogMerge: read the whole log back, merge-on-read",
    batchesInLog,
    containsDana: /dana/i.test(merged),
    mergedPreview: merged.split("\n").filter(Boolean).slice(0, 5),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

If you reloaded between Step 2 and here, `batchesInLog` should already
be `2` or more (this cell's own auto-run of Step 2 adds one more every
page load) — proof the merged view isn't starting from nothing.
[`tests/web-demos/browser_persistence_smoke.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/web-demos/browser_persistence_smoke.sh)
is the harder version of this same proof: real headless Chromium, a
real `page.reload()`, and an assertion that the merged output is
byte-identical before and after — 17 of 17 checks, not a sample of 1.

## Step 4 of 4: the torn write

Ordinary `IndexedDB` transactions are atomic — there's no natural
browser-native way to reproduce a killed `write()` syscall mid-append
the way the native crash harness does. So this cell pokes the store
directly (`_deltaLogCorruptLastForTest`, a test-only export, never
called by Steps 2-3 above) to truncate the most recently written
batch's hex bytes, simulating exactly that. It runs against its own
dedicated, disposable database — never the log Steps 2-3 are building
up — so this is safe to run (and re-run) without touching your
persistence demo above.

```observable-js
try {
  const dbName = "factoidal-hub-post18-tornwrite-demo";
  await Factoidal.deltaLogDestroy({ dbName }).catch(() => {});
  const handle = await Factoidal.deltaLogOpen(dbName);

  await Factoidal.deltaLogAppend(handle,
    `# First delta entry: ex:eve has foaf:name "Eve". This entry stays intact.
INSERT DATA { <http://example.org/eve> <http://xmlns.com/foaf/0.1/name> "Eve" . }`);
  await Factoidal.deltaLogAppend(handle,
    `# Second delta entry: ex:frank has foaf:name "Frank". This is the entry
# the torn-write test corrupts below.
INSERT DATA { <http://example.org/frank> <http://xmlns.com/foaf/0.1/name> "Frank" . }`);

  const beforeCorrupt = await Factoidal.deltaLogMerge(handle, "");
  const corrupted = await Factoidal._deltaLogCorruptLastForTest(handle);
  const afterCorrupt = await Factoidal.deltaLogMerge(handle, "");

  return {
    available: true,
    step: "4 of 4 -- truncate the last entry's bytes, watch the checksum reject it",
    corruptedARecord: corrupted,
    eveSurvivesCorruption: /eve/i.test(afterCorrupt),
    frankWasLostToCorruption: /frank/i.test(beforeCorrupt) && !/frank/i.test(afterCorrupt),
  };
} catch (err) {
  return { available: false, note: err.message };
}
```

`frankWasLostToCorruption` should read `true`: Frank's batch is the one
truncated, `parse_delta_batch`'s checksum framing rejects it as
unparseable, and it is **skipped whole** — never partially decoded,
never silently accepted with garbage bytes. `eveSurvivesCorruption`
should also read `true`: Eve's earlier, uncorrupted batch is untouched.
This is the same "clean prefix survives, corrupt entry never appears"
contract the native on-disk log's crash harness measured 270 times
(0 corrupt accepts) — here it's one keystroke away, in a browser tab,
on a public page.

## One module, four runtimes, one gap

Nothing above is browser-specific logic. `RDF.Store.Columnar.DeltaLog.fst`
declares exactly **five** `ML`-effect `assume val`s for durability —
`delta_log_append`, `delta_log_fsync`, `delta_log_read_all`,
`atomic_rename`, `fsync_dir`
(`RDF.Store.Columnar.DeltaLog.fst:1155-1159`) — and nothing else in
either module: `serialize_delta_batch`/`parse_delta_batch`/
`merge_on_read`/`apply_entries_ref`/`update_ops_to_delta_entries` are
all `Tot`, proved, and byte-identical across every target below. Those
five primitives meet the outside world four different ways depending
on where the module runs: **(1)** native OCaml, plain `Unix` syscalls
(`minimal_regrettable_glue_code_each_with_an_open_issue/282_delta_log_io.sh`,
issue #282) — real `fsync`, real `rename`, the path the CLI's
`--delta-log` flag and `factoidal-http --rw` (commit
[`e8085da`](https://github.com/danbri/factoidal/commit/e8085da)) both
commit through; **(2)** if anything under `js_of_ocaml` or
`wasm_of_ocaml` called that *same* `Unix`-shaped realisation, it would
hit jsoo's own ephemeral pseudo-filesystem (`MlFakeDevice`) — in-memory,
reset on every page load — which is exactly why **(3)** the cells
above never call it at all: `browser.js`'s
`deltaLogOpen`/`deltaLogAppend`/.../`deltaLogMerge` bypass the
`assume val` boundary entirely and hand the pure serialize/parse bytes
straight to `IndexedDB` instead, and the wasm npm-entry ABI's
`deltaBatchToHex`/`deltaMergeApplyBrowser` call the identical pure
functions compiled through `wasm_of_ocaml` instead of `js_of_ocaml`;
**(4)** the KaRaMeL C target declares the same five primitives as
`extern`s in its generated header but ships no C stub body for them
yet — the demo below proves the pure spec cone, not the file-write
boundary. Three of those four are durable and working today; the
fourth (C file I/O) is a named gap, not a hidden one — see the table's
own footnote.

```observable-js
return pretty([
  { runtime: "Native (OCaml)", proves: "the whole lifecycle: append, fsync, read-all, atomic-rename compaction",
    evidence: "270 kills / 270 clean recoveries (crash harness); 29 pass, 0 fail (stage-8 HTTP curl matrix)",
    landed: "commits 1f27320, e8085da" },
  { runtime: "JavaScript (js_of_ocaml)", proves: "serialize/parse/merge -- durability via IndexedDB, bypassing the assume-val boundary",
    evidence: "the four cells on this page; 17/17 in tests/web-demos/browser_persistence_smoke.sh incl. a real page.reload()",
    landed: "commit 8ff60eb" },
  { runtime: "C (KaRaMeL)", proves: "serialize/parse/checksum/epoch-filter -- the pure spec cone, NOT the file-write boundary",
    evidence: "delta_log_demo: 12 of 12 assertions pass",
    landed: "commit bd9e5be" },
  { runtime: "WebAssembly (wasm_of_ocaml)", proves: "serialize/parse/merge -- the same pure functions as the JS row, called through the wasm npm-entry ABI",
    evidence: "npm/factoidal/test/delta-log-wasm.test.js: 3/3 pass against factoidal-npm-entry.wasm.js; capabilities() on the wasm engine reports every npm-entry function true (was blocked by a require.main path bug in wasm.js's loader, not a missing feature or a missing build)",
    landed: "wasm rebuild + wasm.js entry-loader fix" },
]);
```

**The C demo's actual transcript** (`formal/fstar/c-output/deltalog/demo/delta_log_demo`,
[`c-output/deltalog/`](https://github.com/danbri/factoidal/tree/claude/main/formal/fstar/c-output/deltalog) on GitHub):

```
delta_batch_ok(batch)                                            OK
serialize_delta_batch -> 487 bytes
serialized length > 0                                            OK
parse_delta_batch(serialize_delta_batch(batch)) = Some            OK
parsed batch equals original (round-trip)                        OK
no leftover bytes                                                 OK
parse(serialize(batch) ++ 'X') = Some, batch recovered            OK
...and the trailing 'X' is exactly what's left over               OK
parse_delta_batch(corrupted bytes) = None (checksum rejects it)   OK
parse_delta_batch(corrupted magic) = None                        OK
filter_batches_since_epoch(Some 3, [epoch3, epoch5]) keeps exactly 1 OK
...and it's the epoch-5 (post-threshold) batch                   OK
filter_batches_since_epoch(None, [_, _]) keeps both               OK

All checks passed -- F* -> krml -> C -> gcc round trip OK (RDF.Store.Columnar.DeltaLog).
```

Honestly scoped, per that commit's own message: `DeltaMerge` (the
merge-on-read half) is **not** in the C build — its cone pulls in
`SPARQL11.Algebra`, whose monomorphization is the design doc's known
KaRaMeL stratification blocker (reproduced there: over 10 minutes and
5.6 GB RSS before the harness's own cap). The C target proves the
delta-entry framing/checksum layer, not the whole read path — the same
distinction the table above draws between "proves" and "not yet."

### The base-store write path: `BaseWriter` reaches the browser too

This page's persistence story above is the **delta log**
(append-only, small updates). The complementary half is the **base
store** — writing a whole `.cottas` (Parquet) base file — and that path
now reaches the browser as well. The native
`factoidal import`/`compact --native-writer` path
(`RDF.CottasStore.BaseWriter.fst`'s `serialize_cottas`, commit
[`4f8fc95`](https://github.com/danbri/factoidal/commit/4f8fc95)) writes
the actual base file with zero Python — DuckDB's own `parquet_scan`
verdict was **accepted, byte-exact, on 5-quad, 6,780-quad, and
888,949-quad corpora: 0 missing, 0 extra vs source**.

The npm-entry ABI now exposes the same writer to the browser as
`toCottas(nquads) -> { ok, cottasHex, quadCount }`
(`bin/npm-entry/entry_jsoo.ml`). It sorts the quads `(s,p,o,g)` and
encodes them through the identical pure-`Tot` F\* serializer
`RDF.CottasStore.BaseWriter.serialize_cottas_v2` that `factoidal
compact --native-writer` calls, so a browser-produced `.cottas` is
byte-for-byte the same writer's output — not a parallel encoder. The
hex result is the caller's to persist (IndexedDB / OPFS / a browser
download) and feed straight back into `openCottas`, which round-trips
through the same reader/writer pair the native CLI uses. So the "create
a store" story in a browser is now **both** paths: the delta log you
ran above for incremental updates, and `toCottas` for writing a fresh
base file. (This corrects an earlier version of this post, which said
no `BaseWriter` export existed in the browser — it does now.)

## Zero Python, restated with a link

[Post 15](./15-how-fast-the-performance-story.md) and the durability
work above both lean on a claim worth pinning precisely rather than
repeating from memory: `factoidal import --nq FILE --out DIR` and
`factoidal compact --data-cottas FILE --delta-log PATH --native-writer`
are the entire write path, no Python involved — quoting the landing
commit
[`4f8fc95`](https://github.com/danbri/factoidal/commit/4f8fc95)
directly: *"DuckDB verdict: ACCEPTED byte-exact on 5-quad, 6,780-quad,
and 888,949-quad corpora - 0 missing, 0 extra vs source... `compact
--native-writer` removes the LAST Python dependency in the write
path."* `tests/local/cottas_native_import_regressions.sh` re-runs that
DuckDB cross-check (skipping with a loud `SKIP` line, never a silent
pass, if the `pycottas` venv isn't present) alongside the unit-level
byte pins that run everywhere regardless.

## What's next

The delta log's file-I/O boundary in C (the fourth cell of the table
above) is the one named, disclosed gap this post leaves open — the
wasm gap the table used to carry is closed. Compaction (folding an
accumulated delta back into a fresh `.cottas` base) and
`navigator.storage.persist()` wiring remain the browser-side follow-ups
[the design doc](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-06-browser-persistence.md)
already named before this post existed.

Two newer query-language features continue the series from here:
[correlated joins with LATERAL](./19-correlated-joins-lateral.md) and
[full-text search with text:query](./20-fulltext-search-text-query.md),
both Jena-compatible and both running as plain SPARQL through the same
in-browser `fn` adapter.

The four live cells above are pinned in
[`tests/hub/post18_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post18_test.mjs) —
the exact same source, executed against an in-memory stand-in for
`IndexedDB` (Node has no global `indexedDB`) that calls the same real
`deltaBatchToHex`/`deltaMergeApplyBrowser` ABI functions the browser
does; only the storage layer underneath is swapped, never the F\*
logic being pinned. The harder, real-`IndexedDB`-in-real-Chromium proof
is
[`tests/web-demos/browser_persistence_smoke.sh`](https://github.com/danbri/factoidal/blob/claude/main/tests/web-demos/browser_persistence_smoke.sh),
which this post's cells are drawn from directly.
