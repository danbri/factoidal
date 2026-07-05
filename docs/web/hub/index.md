---
title: Documentation Hub
layout: hub.njk
---

# Documentation Hub

A home for longer-form, interactive write-ups about how Factoidal
works — RDF/SPARQL concepts demonstrated by running the real
F\*-extracted engine in your browser, not by prose alone.

This is scaffolding: the layout, the interactive-cell convention, and
this index page. The posts themselves are wave B — the list below is
placeholders.

## How the interactive cells work

A fenced code block tagged `observable-js` becomes a **live cell**:
the page's runtime script (see `docs/_includes/hub.njk`) finds every
` ```observable-js ` block, wraps its body in an async function, and
runs it through a vendored
[Observable Runtime](https://github.com/observablehq/runtime) +
[Inspector](https://github.com/observablehq/inspector) pair — the same
reactive-execution model observablehq.com notebooks use, vendored
under `third_party/observable/` so nothing loads from a CDN.

Each cell's function body receives five fixed bindings by parameter
name:

| Name | What it is |
|---|---|
| `Factoidal` | the npm package (`../npm/foafos/browser.js`) — `query`, `queryDataset`, `toRdf`, `canonicalize`, etc., running the F\*-extracted engine in-browser |
| `d3` | vendored `d3` 7.9.0, for hand-rolled charts |
| `Plot` | vendored `@observablehq/plot` 0.6.17, for declarative charts |
| `html` | vendored `@observablehq/stdlib`'s tagged-template HTML helper |
| `md` | vendored `@observablehq/stdlib`'s tagged-template Markdown helper |

Write a `return` statement to produce the value the Inspector renders
(a string, number, DOM node, or `Plot`/`html` output all work — the
Inspector knows how to display each). Here's a real cell, computing a
value with the npm module right now:

```observable-js
const result = await Factoidal.query(
  '<http://example.org/a> <http://example.org/b> "42" .',
  'SELECT ?o WHERE { ?s ?p ?o }'
);
const row = result.results.bindings[0];
return `hub scaffold smoke test: ${result.results.bindings.length} binding(s), o = ${row.o.value}`;
```

If the cell's rendered output above ends with `1 binding(s), o = 42`
(the Observable Inspector prefixes it with the cell's internal name
and quotes the string — that's expected, not a bug), the whole
chain — vendored Eleventy build, vendored Observable runtime, the
fenced-block convention, and the npm-packaged engine — is working end
to end. `tests/web-demos/hub_smoke.sh` asserts exactly this,
headlessly.

## Planned post series

<ul class="post-series">
  <li class="placeholder">Why RDF terms need three kinds of equality</li>
  <li class="placeholder">SPARQL property paths, one operator at a time</li>
  <li class="placeholder">What RDF Dataset Canonicalization (RDFC-1.0) actually proves</li>
  <li class="placeholder">Reading an OWL 2 RL closure as it happens</li>
</ul>

(Titles are working placeholders for wave B — see the tracker issue
for the documentation-hub effort.)
