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
This life-sciences version makes the selection and query plan visible. It still
loads Turtle into the established browser evaluator. The smaller
[three-block notebook](../51-query-shardborough-blocks-in-browser/) now runs
current IBK3 artifacts through the Lean-WASM worker; packaging this 43,103-
triple named-graph corpus in the graph-aware successor format remains work in
progress. The result view below is a reusable web component: it understands
standard SPARQL Results JSON, preserves RDF term detail, and adapts from a
phone to a wide screen.

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
  const root = html`<section class="shardborough-query"><p><strong>${lifeSciShardborough.id}</strong> — ${lifeSciShardborough.members.length} graphs, ${lifeSciShardborough.members.reduce((n, x) => n + x.triples, 0).toLocaleString()} triples.</p><div class="actions"><button type="button">Show manifest details</button> <button type="button" class="run">Run the cross-graph query</button></div><p class="status" aria-live="polite">Ready. Loading starts only when you choose to run it.</p><div class="details" hidden></div><div class="result" aria-live="polite"></div></section>`;
  const status = root.querySelector(".status"), details = root.querySelector(".details"), resultEl = root.querySelector(".result"), show = root.querySelector("button"), run = root.querySelector(".run");
  show.addEventListener("click", () => { const wasHidden = details.hidden; details.hidden = !wasHidden; show.setAttribute("aria-expanded", String(wasHidden)); show.textContent = wasHidden ? "Hide manifest details" : "Show manifest details"; details.textContent = wasHidden ? JSON.stringify({ manifest: lifeSciShardborough, query: q, executionNow: "browser Turtle fallback", executionNext: "graph-aware checked blocks through the landed Lean-WASM scan ABI" }, null, 2) : ""; details.style.whiteSpace = "pre-wrap"; });
  run.addEventListener("click", async () => { run.disabled = true; resultEl.replaceChildren(); status.textContent = "Fetching the two named graphs needed for this query…"; try {
    const files = await Promise.all(lifeSciShardborough.members.map(async x => { const r = await fetch(new URL("../../../fstar-extracted/lifesci/" + x.file, location.href)); if (!r.ok) throw new Error(`${x.file}: HTTP ${r.status}`); return { graph: x.graph, content: await r.text(), dataFormat: "turtle" }; }));
    status.textContent = "Parsing Turtle and evaluating the cross-graph join locally…";
    const start = performance.now(); const result = await Factoidal.queryDataset(files, q, { output: "json" });
    const elapsed = Math.round(performance.now() - start); const rows = result.results?.bindings?.length || 0;
    status.textContent = `${rows.toLocaleString()} matching variants in ${elapsed.toLocaleString()} ms. Current plan: chromosome type scan ⋈ sequence-variant location scan.`;
    const view = document.createElement("factoidal-sparql-results"); view.setAttribute("palette", "ocean"); view.results = result; resultEl.append(view);
  } catch (e) { status.textContent = "The query did not complete."; const error = document.createElement("factoidal-sparql-error"); error.setAttribute("message", e.message); resultEl.append(error); } finally { run.disabled = false; } }); return root;
}
```

The `factoidal-sparql-results` element defaults to a sortable table, with
variables as columns and result bindings as rows. Its own controls let a
reader choose record cards, transpose the table, filter and independently
hide/show language tags or datatypes, and sort by a variable, language tag, or
datatype. The same module also provides
`factoidal-sparql-graph`, `factoidal-sparql-boolean`, and
`factoidal-sparql-error`; each is configurable with ordinary attributes such
as `palette="ocean"`, `view="cards"`, `language-tags="hide"`,
`datatypes="hide"`, and
`card-direction="horizontal"`.

The AI-skills notebook can propose a read-only query against this manifest, but
it must not execute one without the reader's approval. This division keeps the
working-set dataflow inspectable even when no AI capability is installed.
