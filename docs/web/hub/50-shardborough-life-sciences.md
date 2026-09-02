---
title: "Shardborough: compose a local graph neighbourhood"
description: "Query 43,103 Wikidata life-sciences triples from twelve verified IBK3 blocks: the notebook fetches only the predicate blocks a query names, decodes them with the Lean WebAssembly block worker, and runs the cross-graph SPARQL in the same browser process."
layout: hub.njk
series: docs-hub
series_order: 50
vocab: sparql
status: experimental
tests: tests/hub/post50_test.mjs
hubHideCellSource: true
hubEngineLabel: "the Lean-derived WebAssembly engine"
---

A **Shardborough** is a declared local working set: selected graph/block
artifacts, their provenance and layout policy, prepared to be queried together.
This 43,103-triple life-sciences example now runs on current block bytes. The
three Wikidata extracts (chromosome, sequence variant, disease) were packed by
the Lean publisher into twelve predicate-local `IBK3` blocks, 2.5 MB in
total. A query fetches only the blocks whose predicates it names, checks each
block's exact byte length and SHA-256, decodes it with the Lean WebAssembly
block worker, and evaluates the SPARQL with the Lean runtime. Nothing is
uploaded, and the [three-block notebook](../51-query-shardborough-blocks-in-browser/)
explains the block format itself.

```observable-js
lifeSciShardborough = ({
  id: "shardborough:lifesci-crossgraph:v0",
  layout: "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0 (primary blocks only in the browser)",
  workerOperation: "scanIBK3Predicate",
  assetBase: "../assets/blocks/lifesci-crossgraph/",
  members: [
    { graph: "urn:kgx:chromosome", file: "chromosome.ttl", triples: 9227, role: "chromosome type facts",
      scope: "source:chromosome.ttl:58fc83f472a86526c5ce442bfefe83d25364f20d51f4c06158f9881a0f03b42f",
      blocks: [
        { file: "chromosome/P31.ibk3", property: "P31", rows: 9227, bytes: 563282, sha256: "01484578d6b9696d0298a20898b8a2bf209f7477cc938002c35aa1c55611068a" },
      ] },
    { graph: "urn:kgx:sequence_variant", file: "sequence_variant.ttl", triples: 6455, role: "variant-to-chromosome links",
      scope: "source:sequence_variant.ttl:f5b5a08b0b30df1ed4e42f1db4417cbaac239a878e8c26a419cdb2dfa9c04fcb",
      blocks: [
        { file: "sequence_variant/P31.ibk3", property: "P31", rows: 1800, bytes: 110085, sha256: "a7722b5893193e59cc3429b99a3e1550b86145c6d680b2104a0bb34bef7bb7af" },
        { file: "sequence_variant/P361.ibk3", property: "P361", rows: 719, bytes: 35535, sha256: "e726e04b9a9d15f5097ac2c4befe55baddbb9699635c3ceba6136c3c60fe9dda" },
        { file: "sequence_variant/P3354.ibk3", property: "P3354", rows: 877, bytes: 46502, sha256: "b1c22afab1539748f75b7d70c5d68dd7c0692f8804d0c330f484b823821fbb76" },
        { file: "sequence_variant/P3433.ibk3", property: "P3433", rows: 1702, bytes: 118769, sha256: "0c1bec972f134d617a98a7bb6275e0e421b2b4a930df9cd6d3c0cf9f34dd59c1" },
        { file: "sequence_variant/P1057.ibk3", property: "P1057", rows: 1357, bytes: 82884, sha256: "24c8a5b2faf5d56f41edcb8707e17c9d26bf4cc903f8618efbdb3bcd29130e15" },
      ] },
    { graph: "urn:kgx:disease", file: "disease.ttl", triples: 27421, role: "disease facts: causes, symptoms, genetic associations, treatments",
      scope: "source:disease.ttl:b8f06644f0fce1cb0577c38fda2e4f6f1e65d7fae6aee900a9065a9bb8048b42",
      blocks: [
        { file: "disease/P31.ibk3", property: "P31", rows: 13283, bytes: 806110, sha256: "a28630ba7f87c4e579e5be4bf6a9165285895921cbf7fa2c71d8613e17d214b5" },
        { file: "disease/P780.ibk3", property: "P780", rows: 3416, bytes: 127726, sha256: "2777b3af2b0f2cbba8057795956f02ad33183ab07aae2054ad28c7b7f0b6ebd6" },
        { file: "disease/P828.ibk3", property: "P828", rows: 1842, bytes: 150632, sha256: "79e09106dd4633f2fa2d009b26d5a801b52bc871bf48a0996880df58f45c5173" },
        { file: "disease/P2293.ibk3", property: "P2293", rows: 5586, bytes: 424997, sha256: "811ce421fe4973bae40534dbc73792e9c6a6a4d8820de3ecfd9947eb8bf41c3f" },
        { file: "disease/P927.ibk3", property: "P927", rows: 542, bytes: 39028, sha256: "f145420c498cc83c2b207e942e39ab3143e2acf34c224fd18f010dbebc497152" },
        { file: "disease/P2176.ibk3", property: "P2176", rows: 2752, bytes: 115718, sha256: "bfafa617d56ca49fa38284ff5dd61b1e2356b5e85f3071aa379749c660bb5579" },
      ] },
  ],
  integrity: "every block is checked against its published byte length and SHA-256 before the Lean worker decodes it; graph identity is assigned by this manifest, not carried by the block bytes",
})
```

```observable-js
shardboroughRunner = {
  const manifest = lifeSciShardborough;
  const crossGraphQuery = `PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX wd: <http://www.wikidata.org/entity/>
SELECT ?variant ?chrom WHERE {
  GRAPH <urn:kgx:chromosome> { ?chrom wdt:P31 wd:Q37748 }
  GRAPH <urn:kgx:sequence_variant> { ?variant wdt:P1057 ?chrom }
} LIMIT 20`;
  const diseaseQuery = `PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX wd: <http://www.wikidata.org/entity/>
SELECT ?variant ?gene WHERE {
  GRAPH <urn:kgx:sequence_variant> {
    ?variant wdt:P1057 wd:Q138955 .
    ?variant wdt:P3433 ?gene .
  }
} LIMIT 20`;
  const allBlocks = manifest.members.flatMap(member => member.blocks.map(block => ({ member, block })));
  const totalBytes = allBlocks.reduce((n, x) => n + x.block.bytes, 0);
  const root = html`<section class="shardborough-query">
    <style>
      .shardborough-query { display:grid; gap:.8rem; }
      .shardborough-query textarea { width:100%; min-height:11rem; resize:vertical; padding:.75rem; border:1px solid #a8cbd7; border-radius:.6rem; font:.86rem/1.5 ui-monospace, SFMono-Regular, Menlo, monospace; }
      .shardborough-query .actions { display:flex; flex-wrap:wrap; gap:.5rem; }
      .shardborough-query button { min-height:2.6rem; padding:.5rem .8rem; border:1px solid #196a85; border-radius:.55rem; color:#fff; background:#196a85; font:inherit; font-weight:700; cursor:pointer; }
      .shardborough-query button.secondary { color:#15394b; background:#f7fbfc; border-color:#b8d2dc; }
      .shardborough-query button:disabled { opacity:.65; cursor:wait; }
      .shardborough-query .status { margin:0; padding:.6rem .75rem; border-left:4px solid #196a85; background:#e5f1f5; color:#15394b; }
      .shardborough-query details pre, .shardborough-query .details { white-space:pre-wrap; overflow-wrap:anywhere; }
      @media (prefers-color-scheme: dark) {
        .shardborough-query textarea { background:#17272e; color:#d9eef5; border-color:#345866; }
        .shardborough-query .status { background:#19323d; color:#d9eef5; }
        .shardborough-query button.secondary { background:#17272e; color:#d9eef5; border-color:#4e7786; }
      }
    </style>
    <p><strong>${manifest.id}</strong> — ${manifest.members.length} graphs, ${manifest.members.reduce((n, x) => n + x.triples, 0).toLocaleString()} triples, ${allBlocks.length} IBK3 blocks, ${totalBytes.toLocaleString()} bytes. A query fetches only the blocks it names.</p>
    <label>SPARQL query<textarea spellcheck="false" aria-describedby="shardborough-status"></textarea></label>
    <div class="actions"><button type="button" class="run">Run the query</button><button type="button" class="secondary cross">Cross-graph variant query</button><button type="button" class="secondary disease">Variants on one chromosome</button><button type="button" class="secondary show">Show manifest details</button></div>
    <p id="shardborough-status" class="status" aria-live="polite">Ready. Loading starts only when you choose to run it.</p>
    <details><summary>Execution report</summary><pre>No run yet.</pre></details>
    <div class="details" hidden></div>
    <div class="result" aria-live="polite"></div>
  </section>`;
  const query = root.querySelector("textarea"), status = root.querySelector(".status"), report = root.querySelector("details pre");
  const details = root.querySelector(".details"), resultEl = root.querySelector(".result");
  const run = root.querySelector(".run"), cross = root.querySelector(".cross"), disease = root.querySelector(".disease"), show = root.querySelector(".show");
  query.value = crossGraphQuery;
  const hex = bytes => Array.from(bytes, byte => byte.toString(16).padStart(2, "0")).join("");
  const digest = async bytes => Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)), byte => byte.toString(16).padStart(2, "0")).join("");
  // Block selection mirrors the native planner's constant-predicate rule:
  // a block is fetched when the query names its property (prefixed or full
  // IRI). A query that names no known property loads every block, which is
  // the complete fallback, never a partial answer.
  const blocksFor = text => {
    const named = allBlocks.filter(({ block }) => text.includes(`wdt:${block.property}`) || text.includes(`/prop/direct/${block.property}>`));
    return named.length ? named : allBlocks;
  };
  const scanned = new Map();
  const scanBlock = async ({ member, block }) => {
    if (scanned.has(block.file)) return scanned.get(block.file);
    const response = await fetch(new URL(manifest.assetBase + block.file, location.href));
    if (!response.ok) throw new Error(`${block.file}: HTTP ${response.status}`);
    const bytes = new Uint8Array(await response.arrayBuffer());
    if (bytes.length !== block.bytes) throw new Error(`${block.file}: expected ${block.bytes} bytes, received ${bytes.length}`);
    if ((await digest(bytes)) !== block.sha256) throw new Error(`${block.file}: SHA-256 identity does not match the manifest`);
    const scanStarted = performance.now();
    const scan = await fn.l4Call(manifest.workerOperation, [hex(bytes), `http://www.wikidata.org/prop/direct/${block.property}`, member.scope]);
    if (!scan.ok) throw new Error(`${block.file}: ${scan.error}`);
    // The worker returns default-graph N-Triples. The manifest assigns each
    // member's graph name, so the statements become N-Quads for the dataset.
    const nquads = scan.ntriples.split("\n").filter(Boolean).map(line => line.replace(/ \.$/, ` <${member.graph}> .`)).join("\n");
    const entry = { file: block.file, graph: member.graph, rows: scan.rows, bytes: bytes.length, scanMs: Math.round((performance.now() - scanStarted) * 10) / 10, nquads };
    scanned.set(block.file, entry);
    return entry;
  };
  const datasets = new Map();
  const datasetFor = async selection => {
    const key = selection.map(x => x.block.file).sort().join("|");
    if (datasets.has(key)) return datasets.get(key);
    const entries = [];
    for (const item of selection) entries.push(await scanBlock(item));
    const opened = await fn.l4Call("datasetOpen", [entries.map(e => e.nquads).join("\n"), "nquads", ""]);
    if (!opened.ok) throw new Error(opened.error);
    const dataset = { handle: opened.handle, triples: opened.count, entries };
    datasets.set(key, dataset);
    return dataset;
  };
  show.addEventListener("click", () => {
    const wasHidden = details.hidden; details.hidden = !wasHidden; show.setAttribute("aria-expanded", String(wasHidden));
    show.textContent = wasHidden ? "Hide manifest details" : "Show manifest details";
    details.textContent = wasHidden ? JSON.stringify({ manifest, executionNow: "blocks named by the query are fetched, verified and decoded by the Lean/WASM block worker; graph names come from this manifest; SPARQL runs in the Lean runtime", executionNext: "a graph-aware block layout that carries GraphId in the bytes; native activation, Merkle range reads and sidecars are exercised by the native harness only" }, null, 2) : "";
  });
  cross.addEventListener("click", () => { query.value = crossGraphQuery; query.focus(); });
  disease.addEventListener("click", () => { query.value = diseaseQuery; query.focus(); });
  run.addEventListener("click", async () => {
    run.disabled = true; resultEl.replaceChildren();
    try {
      const started = performance.now();
      const selection = blocksFor(query.value);
      const selectedBytes = selection.reduce((n, x) => n + x.block.bytes, 0);
      status.textContent = `Fetching, checking and decoding ${selection.length} of ${allBlocks.length} blocks (${selectedBytes.toLocaleString()} of ${totalBytes.toLocaleString()} bytes)…`;
      const dataset = await datasetFor(selection);
      status.textContent = `${dataset.triples.toLocaleString()} triples in Lean/WASM memory. Evaluating the query…`;
      const queryStarted = performance.now();
      const answer = await fn.l4Call("datasetQuery", [dataset.handle, query.value]);
      if (!answer.ok) throw new Error(answer.error);
      const queryMs = Math.round(performance.now() - queryStarted), totalMs = Math.round(performance.now() - started);
      const rows = answer.kind === "select" ? answer.srj.results.bindings.length : 1;
      status.textContent = `${rows.toLocaleString()} ${answer.kind === "select" ? "solution rows" : "result"} from ${selection.length} block${selection.length === 1 ? "" : "s"} (${dataset.triples.toLocaleString()} triples). Query ${queryMs.toLocaleString()} ms; ${totalMs.toLocaleString()} ms including fetch, verification and decode. LIMIT limits the displayed answers, not the input work.`;
      report.textContent = JSON.stringify({ kernel: "Lean-derived l4factoidal.wasm", workerOperation: manifest.workerOperation, blocks: dataset.entries.map(({ nquads, ...e }) => e), datasetTriples: dataset.triples, queryKind: answer.kind, queryElapsedMs: queryMs, totalElapsedMs: totalMs, browserPersistence: "none; reload discards the dataset handle" }, null, 2);
      if (answer.kind === "select") { const view = document.createElement("factoidal-sparql-results"); view.setAttribute("palette", "ocean"); view.results = answer.srj; resultEl.append(view); }
      else if (answer.kind === "ask") { const view = document.createElement("factoidal-sparql-boolean"); view.setAttribute("palette", "ocean"); view.results = { boolean: answer.boolean }; resultEl.append(view); }
      else { const pre = document.createElement("pre"); pre.textContent = answer.nquads; resultEl.append(pre); }
    } catch (e) {
      status.textContent = "The query did not complete.";
      const error = document.createElement("factoidal-sparql-error"); error.setAttribute("message", e.message); resultEl.append(error);
      report.textContent = String(e.stack || e);
    } finally { run.disabled = false; }
  });
  return root;
}
```

This is SPARQL over three named graphs, including the two `GRAPH` patterns
in the default query. The default cross-graph query names `wdt:P31` and
`wdt:P1057`, so it fetches the four blocks that hold those properties —
`P31` from every member plus `P1057` (1,562,361 of 2,621,268 bytes; 25,667
rows) — rather than all twelve; the `GRAPH` patterns then confine matching
to the named members. Block selection is by predicate only, the same rule
the native planner applies; graph-aware selection waits for a layout that
carries graph identity. The second query names two properties of one
member and fetches two blocks (201,653 bytes; 3,059 rows): the variants
located on one chromosome and the genes they are variants of. Its first
pattern binds the chromosome, so the join stays small; the browser query
path is the reference Lean evaluator, which evaluates patterns left to
right, and a wide unbound join (thousands by thousands of rows) exceeds
the WebAssembly stack today. The native host's proved hash-join and
shared-subject finishers are not yet wired into this browser operation. A query that names no known
property loads every block: that is the complete fallback, the same rule the
native planner applies, and it never returns a partial answer. LIMIT 20
limits the displayed answers, not the input work.

Blocks decoded once stay in this page's Lean/WASM memory and later queries
reuse them; a reload discards them. No RDF index or parsed dataset is saved
in a browser filesystem.

## What the block layout carries, and what it does not

Each `IBK3` block holds one predicate's rows with a block-local term
dictionary; the worker decodes the complete artifact and returns its
statements. The blocks do not carry graph identity yet: this manifest assigns
each member's graph name when the statements are opened as a dataset, exactly
as the earlier Turtle version did. A graph-aware successor layout that stores
`GraphId` in the bytes is a stated beta gate of the
[Shardborough storage and execution artifact specification](../../../shardborough-storage-spec/);
until it lands, this notebook states the default-graph boundary explicitly
and keeps named-graph identity as manifest metadata.

The native Shardborough host goes further than this page: activated
generations, authenticated Merkle range reads, `SRI2`/`TLI1`/`OLI2`
sidecars and durable delta replay. The browser worker used here receives
complete block bytes over a diagnostic hexadecimal interface, checks framing,
CRC, dictionary and rows, and is bounded by the page's memory; the
gene-scale extracts (888,949 triples, blocks up to 4.7 MB) wait for the
bounded block-set operation.
