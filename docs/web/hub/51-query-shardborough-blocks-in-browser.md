---
title: "Three blocks, one SPARQL query"
description: "Load current IBK3 files, scan them through the Lean WebAssembly block worker, and query the resulting RDF with the Lean SPARQL runtime in the same browser process."
layout: hub.njk
series: docs-hub
series_order: 51
vocab: sparql
status: experimental
tests: tests/hub/post51_test.mjs
hubHideCellSource: true
hubEngineLabel: "the Lean-derived WebAssembly engine"
---

# Three blocks, one SPARQL query

This page runs current Shardborough block bytes. Three small `IBK3` files are
fetched, checked against their published SHA-256 identities, decoded by the
Lean WebAssembly block worker, and then queried by the Lean SPARQL runtime.
Nothing is uploaded.

In this demonstration, *worker* means a small stateless execution operation;
it runs in the page's Lean WASM runtime rather than in a JavaScript Web Worker
or a remote service.

The example has people, names and team memberships in separate
predicate-local blocks. Dana has two names and two memberships, so the query
has four Dana solutions rather than silently treating those values as one
record. To inspect the storage contents instead of joining them, choose
**Show all 13 triples**. It runs the equally ordinary query
`SELECT * WHERE { ?person ?p ?v . }` over the three decoded blocks.

```observable-js
shardboroughBlockQuery = {
  const example = {
    workerOperation: "scanIBK3Predicate",
    blankNodeScope: "source:three-way-subject:8d07b81bf71e0b4c548b5faae50c4231b41bd99ecedc00a5e46817413e815346",
    blocks: [
      { file: "type.ibk3", predicate: "http://example.org/type", rows: 4, bytes: 310, sha256: "7797b38983808f0dded40813672b79f4b8d9f07956ff203d9becab9df8e40a68" },
      { file: "name.ibk3", predicate: "http://example.org/name", rows: 5, bytes: 536, sha256: "6a26193245b2ede29b80a5dcc8530da9f3415f7f96188948d27438142bbd7ede" },
      { file: "member.ibk3", predicate: "http://example.org/member", rows: 4, bytes: 342, sha256: "78540ea53aab57c78d4b0f025d6fbbe307e40d16fbd822331ec1cc0d6c2e542d" },
    ],
  };
  const initialQuery = `# Each person with their type, name and team: a three-way join on
# ?person across the three predicate blocks (one block per property).
SELECT ?person ?type ?name ?team WHERE {
  ?person <http://example.org/type> ?type .     # from type.ibk3
  ?person <http://example.org/name> ?name .     # from name.ibk3
  ?person <http://example.org/member> ?team .   # from member.ibk3
}
ORDER BY ?person ?name ?team`;
  const allTriplesQuery = `# Every triple the three blocks hold, as decoded: 13 rows.
SELECT * WHERE {
  ?person ?p ?v .
}
ORDER BY ?person ?p ?v`;
  const root = html`<section class="block-query-demo">
    <style>
      .block-query-demo { display:grid; gap:.9rem; padding:clamp(.85rem, 2.5vw, 1.35rem); border:1px solid #c4dce5; border-radius:1rem; background:linear-gradient(145deg,#f7fbfc 0%,#eef7f8 100%); box-shadow:0 .8rem 2.2rem rgba(21,57,75,.08); }
      .block-query-demo .demo-head { display:grid; grid-template-columns:minmax(0,1fr) auto; align-items:end; gap:1rem; }
      .block-query-demo .eyebrow { margin:0 0 .2rem; color:#196a85; font-size:.72rem; font-weight:800; letter-spacing:.12em; text-transform:uppercase; }
      .block-query-demo h2 { margin:0; color:#15394b; font-size:clamp(1.15rem,3.5vw,1.65rem); line-height:1.15; }
      .block-query-demo .subhead { margin:.35rem 0 0; color:#4b6572; font-size:.92rem; }
      .block-query-demo .facts { display:flex; flex-wrap:wrap; justify-content:flex-end; gap:.4rem; margin:0; padding:0; list-style:none; }
      .block-query-demo .facts li { padding:.3rem .55rem; border:1px solid #c4dce5; border-radius:999px; background:#fff; color:#15394b; font-size:.78rem; font-weight:700; white-space:nowrap; }
      .block-query-demo label { display:grid; gap:.35rem; font-weight:700; }
      .block-query-demo textarea { width:100%; min-height:13rem; resize:vertical; padding:.85rem; border:1px solid #a8cbd7; border-radius:.7rem; background:#fff; color:#15394b; box-shadow:inset 0 1px 2px rgba(21,57,75,.05); font: .88rem/1.5 ui-monospace, SFMono-Regular, Menlo, monospace; }
      .block-query-demo textarea:focus-visible, .block-query-demo button:focus-visible { outline:3px solid #075fd0; outline-offset:2px; }
      .block-query-demo .actions { display:flex; flex-wrap:wrap; gap:.55rem; }
      .block-query-demo button { min-height:2.75rem; padding:.55rem .85rem; border:1px solid #196a85; border-radius:.6rem; color:#fff; background:#196a85; font:inherit; font-weight:700; cursor:pointer; }
      .block-query-demo button.secondary { color:#15394b; background:#f7fbfc; border-color:#b8d2dc; }
      .block-query-demo button:disabled { opacity:.65; cursor:wait; }
      .block-query-demo .status { margin:0; padding:.7rem .8rem; border-left:4px solid #196a85; background:#e5f1f5; color:#15394b; }
      .block-query-demo details { border:1px solid #c4dce5; border-radius:.65rem; padding:.55rem .75rem; background:#f7fbfc; }
      .block-query-demo summary { cursor:pointer; font-weight:700; color:#15394b; }
      .block-query-demo pre { white-space:pre-wrap; overflow-wrap:anywhere; }
      @media (max-width: 640px) {
        .block-query-demo .demo-head { grid-template-columns:1fr; align-items:start; }
        .block-query-demo .facts { justify-content:flex-start; }
        .block-query-demo .actions button { flex:1 1 11rem; }
      }
      @media (prefers-color-scheme: dark) {
        .block-query-demo { background:linear-gradient(145deg,#13252d 0%,#172f38 100%); border-color:#345866; box-shadow:none; }
        .block-query-demo h2 { color:#e8f7fb; }
        .block-query-demo .subhead { color:#b9d1da; }
        .block-query-demo .facts li { background:#17272e; color:#d9eef5; border-color:#345866; }
        .block-query-demo textarea, .block-query-demo details { background:#17272e; color:#d9eef5; border-color:#345866; }
        .block-query-demo .status { background:#19323d; color:#d9eef5; }
        .block-query-demo button.secondary { background:#17272e; color:#d9eef5; border-color:#4e7786; }
      }
    </style>
    <header class="demo-head">
      <div><p class="eyebrow">Local binary RDF</p><h2>Query three verified blocks</h2><p class="subhead">Edit the query, then run it entirely in this browser.</p></div>
      <ul class="facts" aria-label="Dataset summary"><li>3 IBK3 blocks</li><li>13 triples</li><li>1,188 bytes</li></ul>
    </header>
    <label>SPARQL query<textarea spellcheck="false" aria-describedby="block-query-status"></textarea></label>
    <div class="actions"><button type="button" class="run">Load and query the blocks</button><button type="button" class="secondary all">Show all 13 triples</button><button type="button" class="secondary reset">Restore join query</button></div>
    <p id="block-query-status" class="status" aria-live="polite">Ready. The three binary artifacts total 1,188 bytes.</p>
    <details><summary>Execution report</summary><pre>No run yet.</pre></details>
    <div class="result" aria-live="polite"></div>
  </section>`;
  const query = root.querySelector("textarea");
  const run = root.querySelector(".run");
  const all = root.querySelector(".all");
  const reset = root.querySelector(".reset");
  const status = root.querySelector(".status");
  const report = root.querySelector("details pre");
  const result = root.querySelector(".result");
  query.value = initialQuery;
  const hex = bytes => Array.from(bytes, byte => byte.toString(16).padStart(2, "0")).join("");
  const digest = async bytes => Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)), byte => byte.toString(16).padStart(2, "0")).join("");
  let preparedPromise = null;
  const prepareDataset = () => {
    if (preparedPromise) return preparedPromise;
    preparedPromise = (async () => {
      const scans = [];
      const started = performance.now();
      for (const block of example.blocks) {
        const response = await fetch(new URL(`../assets/blocks/shardborough-three-way/${block.file}`, location.href));
        if (!response.ok) throw new Error(`${block.file}: HTTP ${response.status}`);
        const bytes = new Uint8Array(await response.arrayBuffer());
        const foundHash = await digest(bytes);
        if (bytes.length !== block.bytes) throw new Error(`${block.file}: expected ${block.bytes} bytes, received ${bytes.length}`);
        if (foundHash !== block.sha256) throw new Error(`${block.file}: SHA-256 identity does not match the notebook manifest`);
        const scanStarted = performance.now();
        const scan = await fn.l4Call(example.workerOperation, [hex(bytes), block.predicate, example.blankNodeScope]);
        scans.push({ file:block.file, bytes:bytes.length, rows:scan.rows, elapsedMs:Math.round((performance.now()-scanStarted)*10)/10, ntriples:scan.ntriples });
      }
      const graphText = scans.map(scan => scan.ntriples).join("\n");
      const opened = await fn.l4Call("datasetOpen", [graphText, "nquads", ""]);
      return {
        scans,
        handle: opened.handle,
        triples: opened.count,
        elapsedMs: Math.round((performance.now()-started)*10)/10,
      };
    })().catch(error => {
      preparedPromise = null;
      throw error;
    });
    return preparedPromise;
  };
  const showResult = answer => {
    result.replaceChildren();
    if (answer.kind === "select") {
      const view = document.createElement("factoidal-sparql-results");
      view.setAttribute("palette", "ocean");
      view.results = answer.srj;
      result.append(view);
    } else if (answer.kind === "ask") {
      const view = document.createElement("factoidal-sparql-boolean");
      view.setAttribute("palette", "ocean");
      view.results = { boolean: answer.boolean };
      result.append(view);
    } else if (answer.kind === "construct") {
      const output = document.createElement("pre");
      output.textContent = answer.nquads;
      result.append(output);
    }
  };
  reset.addEventListener("click", () => { query.value = initialQuery; query.focus(); });
  all.addEventListener("click", () => { query.value = allTriplesQuery; run.click(); });
  run.addEventListener("click", async () => {
    run.disabled = true;
    result.replaceChildren();
    const reused = preparedPromise !== null;
    status.textContent = reused
      ? "Reusing the parsed dataset held in this page's Lean/WASM memory…"
      : "Loading, checking and decoding the three IBK3 artifacts once…";
    try {
      const started = performance.now();
      const prepared = await prepareDataset();
      status.textContent = "The blocks are valid. Evaluating the editable SPARQL query…";
      const queryStarted = performance.now();
      const answer = await fn.l4Call("datasetQuery", [prepared.handle, query.value]);
      const queryMs = Math.round((performance.now()-queryStarted)*10)/10;
      const totalMs = Math.round((performance.now()-started)*10)/10;
      const answerSize = answer.kind === "select" ? answer.srj.results.bindings.length : answer.kind === "ask" ? 1 : answer.nquads.split("\n").filter(Boolean).length;
      status.textContent = `${prepared.triples} triples; ${answerSize} ${answer.kind === "select" ? "solution rows" : "result"}. ${reused ? "Reused the prepared in-memory dataset" : "Prepared the in-memory dataset"}; this run took ${totalMs} ms.`;
      run.textContent = "Run query again";
      report.textContent = JSON.stringify({
        kernel: "Lean-derived l4factoidal.wasm",
        workerOperation: example.workerOperation,
        blankNodeScope: example.blankNodeScope,
        artifacts: prepared.scans.map(({ntriples, ...scan}) => scan),
        composition: "N-Triples fragments opened once as an in-memory Lean dataset handle",
        browserPersistence: "none; reload discards the dataset handle",
        reusedPreparedDataset: reused,
        preparationElapsedMs: reused ? 0 : prepared.elapsedMs,
        queryKind: answer.kind,
        queryElapsedMs: queryMs,
        totalElapsedMs: totalMs,
      }, null, 2);
      showResult(answer);
    } catch (error) {
      status.textContent = "The block query did not complete.";
      const view = document.createElement("factoidal-sparql-error");
      view.setAttribute("message", error.message);
      result.append(view);
      report.textContent = String(error.stack || error);
    } finally {
      run.disabled = false;
    }
  });
  return root;
}
```

## The three blocks

The arrows below show each block's RDF meaning. On disk, the repeated terms
are block-local integer IDs resolved through that block's own dictionary.

```text
three-way-subject.ttl                                         13 triples
  │
  ├─ type.ibk3     310 bytes / 4 rows / predicate ex:type
  │    alice → Person    bob → Person    carol → Robot    dana → Person
  │
  ├─ name.ibk3     536 bytes / 5 rows / predicate ex:name
  │    alice → "Alice"  bob → "Bob"     carol → "Carol"
  │    dana  → "Dana"   dana → "Dana D."
  │
  └─ member.ibk3   342 bytes / 4 rows / predicate ex:member
       alice → team1     carol → team2    dana → team3    dana → team4

       fetch + SHA-256 check + Lean/WASM scan
                              │
                              ▼
                    13 RDF triples in one default graph
                              │
                              ▼
                         editable SPARQL
```

Each of those files has the same canonical `IBK3` arrangement. Every fixed
row is 16 bytes: four little-endian 32-bit integers. `position` preserves the
source row order; `s`, `p` and `o` refer into the embedded `PTD1` term
dictionary.

```text
one IBK3 artifact
┌──────────────────────────────────────────────────────────────────┐
│ "IBK3" │ v3 │ row count │ PTD1 byte count                       │ 13-byte header
├──────────────────────────────────────────────────────────────────┤
│ position │ subject ID │ predicate ID │ object ID                 │ 16 bytes × rows
├──────────────────────────────────────────────────────────────────┤
│ embedded PTD1 dictionary                                        │
│   "PTD1" │ v1 │ term count │ 256 terms/page │ page count       │
│   page directory │ encoded RDF-term pages │ PTD1 CRC32C         │
├──────────────────────────────────────────────────────────────────┤
│ IBK3 CRC32C                                                     │
└──────────────────────────────────────────────────────────────────┘
```

There are two explicit stages. `scanIBK3Predicate` is the small block-worker
operation: it checks and decodes one complete predicate-local artifact and
returns RDF statements. Its third argument is one source scope shared by all
blocks from this Turtle document; it preserves cross-block blank-node identity
without merging same-spelled labels from unrelated inputs. `queryDataset`
parses the editable SPARQL and evaluates it over those statements. Both
operations come from the same Lean-derived WASM module.

The returned fragments are N-Triples and form one default graph. This first
operation does not carry named-graph identity; the blank-node scope preserves
local node identity but is not a graph name.

The first run fetches and verifies the files, asks Lean/WASM to decode them,
and opens one parsed dataset inside the WebAssembly module. Later queries on
this page reuse that in-memory dataset handle. A reload discards it. The
browser may separately retain the JavaScript, WASM and block files in its
ordinary HTTP cache, but this notebook does not yet put an RDF database in
Origin Private File System, IndexedDB or the File System API.

The query entry point accepts `PREFIX` and `BASE`, and executes `SELECT`,
`ASK` and `CONSTRUCT`. Its implemented algebra includes joins, filters,
optional patterns, unions, property paths, subqueries, grouping, aggregates,
ordering and slicing. The Lean GeoSPARQL extension table is installed for the
implemented `geof:sf*` topology predicates. `DESCRIBE` and remote `SERVICE`
execution are not available through this notebook, and no claim of complete
SPARQL 1.1 conformance is made for the browser/block combination yet.

The current browser call passes blocks as hexadecimal strings and materializes
N-Triples between the two stages. This is a diagnostic API for complete small
artifacts. The native Shardborough query host already adds active-generation
manifests, authenticated Merkle reads, SRI2/TLI1/OLI2 sidecars and durable
delta replay. A production remote worker still needs direct byte buffers,
authenticated ranges, resource limits and the bounded PushIR request format.
Those boundaries are specified in the
[Shardborough storage and execution artifact specification](../../../shardborough-storage-spec/#24-block-query-workers).
