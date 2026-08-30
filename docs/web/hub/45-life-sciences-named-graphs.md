---
title: "Life sciences: named graphs, on demand"
description: "The established Wikidata/KGX life-sciences workload, recast as a small Hub notebook: three named graph files, one cross-graph SPARQL join, and an explicit user action before the browser loads the corpus."
layout: hub.njk
series: docs-hub
series_order: 45
vocab: wikidata
status: published
tests: tests/hub/post45_test.mjs
---

This established life-sciences workload is presented here as a Hub notebook:
the data catalogue, the query and the runner are separate cells. It uses the
same committed KGX Turtle files and F\*-derived browser evaluator; no service
receives the data or the query.

The runner is deliberately click-to-run. The three files total 43,103 RDF
triples, so loading them should be an intentional experiment, not a cost paid
by every reader of the documentation index.

```observable-js
lifeSciCatalog = ([
  { graph: "urn:kgx:chromosome", file: "chromosome.ttl", triples: 9227 },
  { graph: "urn:kgx:sequence_variant", file: "sequence_variant.ttl", triples: 6455 },
  { graph: "urn:kgx:disease", file: "disease.ttl", triples: 27421 },
])
```

The original page's most informative small result is a cross-graph join: a
variant links to a chromosome in one graph, while the chromosome's type lives
in another. `LIMIT 20` keeps the result readable; it does not reduce the
input that must be parsed by this current browser engine.

```observable-js
lifeSciQuery = `
PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX wd:  <http://www.wikidata.org/entity/>
SELECT ?variant ?chrom WHERE {
  GRAPH <urn:kgx:chromosome>       { ?chrom wdt:P31 wd:Q37748 }
  GRAPH <urn:kgx:sequence_variant> { ?variant wdt:P1057 ?chrom }
}
LIMIT 20`
```

```observable-js
lifeSciRunner = {
  const root = html`<div>
    <p><strong>${lifeSciCatalog.length} files, ${lifeSciCatalog.reduce((n, f) => n + f.triples, 0).toLocaleString()} triples.</strong></p>
    <button type="button">Load the named graphs and run the join</button>
    <pre aria-live="polite">Waiting for a click.</pre>
  </div>`;
  const button = root.querySelector("button");
  const output = root.querySelector("pre");
  button.addEventListener("click", async () => {
    button.disabled = true;
    output.textContent = "Fetching Turtle files…";
    try {
      const files = await Promise.all(lifeSciCatalog.map(async (entry) => {
        const url = new URL("../../../fstar-extracted/lifesci/" + entry.file, location.href);
        const response = await fetch(url);
        if (!response.ok) throw new Error(`${entry.file}: HTTP ${response.status}`);
        return { graph: entry.graph, content: await response.text(), dataFormat: "turtle" };
      }));
      output.textContent = "Parsing and evaluating SPARQL in this browser…";
      const started = performance.now();
      const result = await Factoidal.queryDataset(files, lifeSciQuery, { output: "json" });
      const elapsed = Math.round(performance.now() - started);
      const rows = result.results?.bindings || [];
      output.textContent = JSON.stringify({ elapsedMs: elapsed, rows: rows.length, firstRows: rows.slice(0, 5) }, null, 2);
    } catch (error) {
      output.textContent = `Run failed: ${error.message}`;
    } finally {
      button.disabled = false;
    }
  });
  return root;
}
```

The result is a concrete SPARQL execution over the legacy workload, rather
than a screenshot or a precomputed answer. It is still the older F\*-derived
in-memory execution path: each click fetches and parses source Turtle. The
new Lean block engine's purpose is to replace that repeated text-to-memory
step with checked binary blocks and bounded reads. The next notebook makes
that binary boundary visible without pretending that the browser can query an
IBK file before the corresponding Lean-WASM operation is exported.

## Related notebooks

- [RIF Core](../10-rules-rif-core/) is the maintained rules notebook.
- [Post 42](../42-cottas-a-store-at-scale/) opens COTTAS bytes and queries
  them: the closest current browser analogue of the block-engine direction.

The cells that define the dataset catalogue and SPARQL workload are pinned in
[`tests/hub/post45_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post45_test.mjs).
