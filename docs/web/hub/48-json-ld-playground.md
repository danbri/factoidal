---
title: "JSON-LD playground"
description: "Paste JSON-LD and inspect its RDF and canonical N-Quads locally in the browser."
layout: hub.njk
series: docs-hub
series_order: 48
vocab: schema.org
status: published
tests: tests/hub/post48_test.mjs
---

This is the maintained Hub form of the JSON-LD playground. Paste JSON-LD,
then run its `toRdf` conversion and RDFC-1.0 canonicalization entirely in the
browser. It deliberately has no remote-context loader: an inline `@context`
is supported; a URL used as `@context` is reported as unsupported rather than
silently fetched.

```observable-js
jsonldPlayground = {
  const sample = JSON.stringify({
    "@context": { "schema": "http://schema.org/", "name": "schema:name", "Person": "schema:Person" },
    "@id": "http://example.org/alice", "@type": "Person", "name": "Alice"
  }, null, 2);
  const root = html`<div class="jsonld-playground">
    <label>JSON-LD input<textarea spellcheck="false"></textarea></label>
    <p><button type="button">Convert and canonicalize</button> <output aria-live="polite">Ready.</output></p>
    <details open><summary>RDF / N-Quads</summary><pre></pre></details>
    <details><summary>Canonical N-Quads</summary><pre></pre></details>
  </div>`;
  const input = root.querySelector("textarea");
  const button = root.querySelector("button");
  const status = root.querySelector("output");
  const [rdfOut, canonOut] = root.querySelectorAll("pre");
  input.value = sample;
  button.addEventListener("click", async () => {
    button.disabled = true;
    status.textContent = "Converting…";
    try {
      const rdf = await Factoidal.jsonldToRdf(input.value);
      rdfOut.textContent = rdf.nquads || "(no triples)";
      const dataset = await fn.parse(rdf.nquads, { format: "nquads" });
      canonOut.textContent = await fn.canonicalize(dataset);
      status.textContent = "Done.";
    } catch (error) {
      rdfOut.textContent = String(error.message || error);
      canonOut.textContent = "";
      status.textContent = "The input was not accepted.";
    } finally {
      button.disabled = false;
    }
  });
  return root;
}
```

The [JSON-LD introduction](../07-json-ld-rdf-as-json/) explains contexts,
the RDF mapping, and the reverse `fromRdf` direction. This page is for trying
your own input; it does not claim that unsupported JSON-LD features work.
