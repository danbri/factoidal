# SPARQL client as a Web Component

Status: tentative, first draft, partial implementation landed
Date: 2026-04-23
Author: claude/main
Related: `docs/fstar-extracted/demo-lifesci.html` (existing production demo,
~830 lines of page-local JS), `docs/fstar-extracted/index.html`
(alternative demo with a dataset dropdown), `docs/fstar-extracted/browser-wasm.js`
(wasm_of_ocaml adapter)

## Problem

Factoidal ships a verified SPARQL engine as `factoidal.js` (js_of_ocaml)
and `factoidal.wasm.js` (wasm_of_ocaml). To turn those bundles into a
usable page, a page author currently has to hand-write:

- data-file fetching + caching
- engine-bundle fetching + caching
- the js_of_ocaml `jsoo_fs_tmp` shim and argv construction
- the WASM path's TriG-merge (since `browser-wasm.js::query()` takes a
  single data string)
- a run button that gives immediate feedback within one animation frame
- a progress indicator for 5+ second queries
- a results renderer (URI abbreviation, typed-literal suffixes, boolean
  vs bindings)
- a timing breakdown that splits engine-load / data-fetch / query-run
- defensive cleanup so a crashed query can't leave the spinner on

`demo-lifesci.html` is ~700 lines of this glue, tied to one dataset.
`index.html` is ~1400 lines of a similar shape with a dataset dropdown.
Both reimplement the same orchestration.

The goal is a drop-in `<factoidal-sparql-client>` custom element that
third parties can use without reading our source.

## Design

### Component hierarchy (tentative)

```
<factoidal-sparql-client>            orchestrator; owns engine state and runs queries
  <factoidal-query name="..." label="...">
     # query text as textContent
  </factoidal-query>
  ...more queries as light-DOM children, or via the `queries` property
</factoidal-sparql-client>
```

The first cut is a **single-element** orchestrator. The internal UI
(engine toggle, query-picker dropdown, run button, results table, timing
panel) lives in the Shadow DOM as plain HTML. Splitting each into its own
Custom Element is planned but not required for v1 — it would let a page
author replace (e.g.) the results renderer with their own without
reimplementing the orchestrator. See "follow-up" below.

### Attributes / properties

| Attribute       | Property          | Description                                               |
|-----------------|-------------------|-----------------------------------------------------------|
| `src-data`      | `srcData`         | JSON array of `{url, graph, vfs?}` entries                |
| `engines`       | `engines`         | Comma list: `"js"`, `"wasm"`, `"js,wasm"` (default both)  |
| `default-engine`| `defaultEngine`   | `"js"` or `"wasm"`                                        |
| `entail`        | `entail`          | `"none"` / `"RDFS"` / `"OWL-RL"` (passed to WASM only)    |
| `js-url`        | `jsUrl`           | Override for `factoidal.js` location                      |
| `wasm-url`      | `wasmUrl`         | Override for `factoidal.wasm.js` location                 |
| `queries`       | `queries`         | JSON array `[{key, label, body}, ...]`                    |
| `warm`          | —                 | If present, pre-fetch engines + data on connect           |

Properties accept full JS values (arrays/objects); attributes accept
stringified equivalents and are reflected into properties on
`attributeChangedCallback`.

### Slot content: `<factoidal-query>`

Instead of `queries=`, a page author can declare queries inline:

```html
<factoidal-sparql-client src-data="...">
  <factoidal-query name="count-all" label="Count triples">
    SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }
  </factoidal-query>
</factoidal-sparql-client>
```

The orchestrator reads its light-DOM children at connect time, builds a
`queries[]` array, and hides them (they are config, not rendered).
Light-DOM queries and the `queries` property merge; light-DOM wins on
key collision.

### Events

Bubbled `CustomEvent`s on the orchestrator:

- `factoidal:query-start` — `{detail: {engine, query}}`
- `factoidal:query-done`  — `{detail: {engine, query, results, runMs, totalMs, phases}}`
- `factoidal:query-error` — `{detail: {engine, query, error}}`

Page authors can listen for these to drive their own UI without poking
into Shadow DOM.

### Shadow DOM / styling

All internal DOM lives in open shadow root. Styles are fully encapsulated.
Theming is via CSS custom properties, each defaulting to the value used
by the current `demo-lifesci.html`:

```css
:host {
  --fc-fg:     #222;
  --fc-muted:  #666;
  --fc-bg:     #fff;
  --fc-surface: #f7f7f7;
  --fc-border: #e0e0e0;
  --fc-brand:  #2d6a4f;
  --fc-brand-dark: #1b4332;
  --fc-error:  #c0392b;
  --fc-ok:     #2d6a4f;
}
```

CSS `::part()` is exposed for deeper styling:
`part(run-button)`, `part(query-editor)`, `part(status)`,
`part(results)`, `part(timing-detail)`.

### Accessibility primitives kept from the existing demo

- `aria-busy="true"` on the run button while a query is in flight
- `role="progressbar"` on the striped running indicator
- `role="radiogroup" aria-label="Engine"` on the JS/WASM toggle
- visually-hidden radio inputs with a positioned parent (fixes the
  "opacity:0 absolute without parent context" bug from the current demo)
- `requestAnimationFrame` yield after synchronous DOM updates, so the
  "Running…" state paints before the main thread is hogged

## What shipped in this commit

- `docs/fstar-extracted/factoidal-sparql-client.js` — ES module that
  registers `<factoidal-sparql-client>` and `<factoidal-query>`.
- `docs/fstar-extracted/demo-lifesci-v2.html` — side-by-side demo that
  uses the component instead of hand-rolled glue. Drives the same three
  lifesci TTLs, offers the same engine toggle, same default query.
- `demo-lifesci.html` left untouched (production demo remains the
  known-good).

### Tested

- Component loads, renders, engine toggle works, default query runs
  end-to-end on the JS engine, results table populates, timing panel
  renders. Verified through chrome-devtools MCP against a localhost
  server.

### Not tested / not ported

- WASM engine path is wired but not verified in this commit because
  the wasm bundle is slow to warm on an Apple Silicon laptop and we
  don't want to sit on a 30+ s wait during smoke testing. The code
  path is a straightforward call into `browser-wasm.js::query()` with
  `payloadsToTriG()` as in the original, so any wasm regression is on
  the `browser-wasm.js` side, not the component.
- CSV / TSV / XML output formats (component currently only wires `json`).
- `entail` for the JS engine path (browser-wasm supports it already;
  js_of_ocaml CLI takes `--entail` but we don't pass it yet).
- Deep child components. `<factoidal-engine-toggle>`,
  `<factoidal-results-view>`, `<factoidal-timing-panel>` etc. are
  inline shadow DOM today, not first-class custom elements.

## Follow-up

1. **Split into child custom elements**: `<factoidal-engine-toggle>`,
   `<factoidal-query-editor>`, `<factoidal-results-view>`,
   `<factoidal-timing-panel>`. The orchestrator would compose them via
   slots so a page author can swap any one without reimplementing
   the whole.
2. **`entail` wiring for JS path** — js_of_ocaml CLI accepts
   `--entail RDFS`; thread it through.
3. **Output format** property so CSV/TSV/XML downloads work.
4. **Bind events on keyboard shortcut**: Ctrl/Cmd+Enter to run from
   inside the textarea. The current demo does not have this either,
   but the component is a natural place to add it once.
5. **Replace per-demo dataset list with a `<factoidal-dataset-loader>`
   component** that does the fetch + cache + TriG-merge. That would
   let the orchestrator be truly dataset-agnostic.
6. **`factoidal:query-start` / `:query-done` hooks for the page author
   telemetry story** (basic events exist; document them in a README
   once the shape stabilises).

## How to drop this on your page

```html
<script type="module" src="./factoidal-sparql-client.js"></script>

<factoidal-sparql-client
    engines="js,wasm"
    default-engine="js"
    src-data='[{"url":"./data.ttl","graph":"urn:x:main"}]'>

  <factoidal-query name="count" label="Count triples">
    SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }
  </factoidal-query>

  <factoidal-query name="first-20" label="First 20 triples">
    SELECT * WHERE { ?s ?p ?o } LIMIT 20
  </factoidal-query>

</factoidal-sparql-client>
```

That's the whole integration. No npm, no bundler, no framework. Styling
via CSS variables on `factoidal-sparql-client {}` or the parent.
