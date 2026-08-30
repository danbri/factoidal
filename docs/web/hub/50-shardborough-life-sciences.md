---
title: "Shardborough: compose a local graph neighbourhood"
description: "An inspectable working-set manifest over the life-sciences named graphs, with a user-run cross-graph SPARQL query and explicit current execution boundary."
layout: hub.njk
series: docs-hub
series_order: 50
vocab: sparql
status: experimental
---

A **Shardborough** is a declared local working set: selected graph/block
artifacts, their provenance and layout policy, prepared to be queried together.
This first browser version makes the selection and query plan visible. It still
loads Turtle into the established browser evaluator; it is the UI/manifest
contract that the later cached Lean-block runner will replace.

```observable-js
lifeSciShardborough = ({
  id: "shardborough:lifesci-crossgraph:v0",
  members: [
    { graph: "urn:kgx:chromosome", file: "chromosome.ttl", triples: 9227, role: "chromosome type facts" },
    { graph: "urn:kgx:sequence_variant", file: "sequence_variant.ttl", triples: 6455, role: "variant-to-chromosome links" },
    { graph: "urn:kgx:disease", file: "disease.ttl", triples: 27421, role: "available named graph" },
  ],
  layout: "named-graph members; future graph-aware blocks",
  integrity: "source files committed with the documentation; block hashes pending the binary manifest",
})
```

```observable-js
shardboroughRunner = {
  const q = `PREFIX wdt: <http://www.wikidata.org/prop/direct/>\nPREFIX wd: <http://www.wikidata.org/entity/>\nSELECT ?variant ?chrom WHERE {\n  GRAPH <urn:kgx:chromosome> { ?chrom wdt:P31 wd:Q37748 }\n  GRAPH <urn:kgx:sequence_variant> { ?variant wdt:P1057 ?chrom }\n} LIMIT 20`;
  const root = html`<div><p><strong>${lifeSciShardborough.id}</strong> — ${lifeSciShardborough.members.length} graphs, ${lifeSciShardborough.members.reduce((n, x) => n + x.triples, 0).toLocaleString()} triples.</p><button>Show manifest</button> <button class="run">Load borough and run cross-graph query</button><pre aria-live="polite">Ready. The current runner fetches Turtle only after your click.</pre></div>`;
  const out = root.querySelector("pre"), show = root.querySelector("button"), run = root.querySelector(".run");
  show.addEventListener("click", () => out.textContent = JSON.stringify({ manifest: lifeSciShardborough, query: q, executionNow: "browser Turtle fallback", executionNext: "cached checked blocks + Lean-WASM query ABI" }, null, 2));
  run.addEventListener("click", async () => { run.disabled = true; out.textContent = "Fetching named-graph members…"; try {
    const files = await Promise.all(lifeSciShardborough.members.map(async x => { const r = await fetch(new URL("../../../fstar-extracted/lifesci/" + x.file, location.href)); if (!r.ok) throw new Error(`${x.file}: HTTP ${r.status}`); return { graph: x.graph, content: await r.text(), dataFormat: "turtle" }; }));
    const start = performance.now(); const result = await Factoidal.queryDataset(files, q, { output: "json" });
    out.textContent = JSON.stringify({ elapsedMs: Math.round(performance.now() - start), rows: result.results?.bindings?.length || 0, firstRows: (result.results?.bindings || []).slice(0, 5), plan: "chromosome type scan ⋈ sequence-variant location scan" }, null, 2);
  } catch (e) { out.textContent = `Run failed: ${e.message}`; } finally { run.disabled = false; } }); return root;
}
```

The AI-skills notebook can propose a read-only query against this manifest, but
it must not execute one without the reader's approval. This division keeps the
working-set dataflow inspectable even when no AI capability is installed.
