# Documentation hub — cell-authoring contract

This is the implementation reference for writing a hub post. The
reader-facing explanation lives in [the hub index](../)'s "How the
interactive cells work" section; this file is the fuller contract for
whoever writes the next post.

<!-- Linked as `../` (the directory), not `index.md` -- `index.md`
     is the one page in this directory Eleventy does NOT give its own
     pretty-URL subdirectory, so docs/.eleventy.js's mdlink-to-slug
     transform's blanket "prepend ../, drop .md, append /" rewrite
     turns a `.md`-suffixed link to it into a nonexistent `index/`
     path. See the equivalent note in index.md. -->

## Front matter

```yaml
---
title: "Post title"
description: "One-sentence description."
layout: hub.njk
series: docs-hub
series_order: N
vocab: foaf | wikidata | schema.org | skos | none
status: draft | published
tests: tests/hub/postNN_test.mjs
---
```

`layout: hub.njk` is required — it's what wires in the Observable
runtime and the fenced-block cell convention. The rest of the fields
are read by nothing at build time today; they're bookkeeping (the
series plan doc, `docs/designissues/2026-07-05-docs-hub-plan.md`, is
the source of truth for the series map) but keep them, since the next
post's author will grep for them.

## Fence conventions

- ` ```observable-js ` — a **live cell**. `docs/_includes/hub.njk`'s
  runtime script finds every `pre > code.language-observable-js`,
  wraps its text content in an async function body, and runs it
  through the vendored Observable Runtime + Inspector. Write a
  `return` statement to produce the value the Inspector renders.
- ` ```js `, ` ```turtle `, ` ```fstar `, etc. — static, inert code
  samples. Use these for pure notation (Turtle syntax being
  introduced, an F\* type definition being quoted) where there is
  nothing to *compute*, only something to *read*.

Only convert a code sample to a live cell when it actually computes
something a reader benefits from seeing run (a parse, a query, an
entailment closure) — not every fenced block needs to be live.

## Cell bindings (`CELL_BINDINGS`)

Every live cell's function body receives these bindings by parameter
name. This list and the `new Function(...)` parameter list in
`hub.njk` are mirrored deliberately — extend both together if a future
post needs a new binding.

| Name | What it is |
|---|---|
| `Factoidal` | the raw npm package entry (`npm/foafos/browser.js`) — `query(dataString, sparqlString, {dataFormat, entail, output})` returns a raw SPARQL-JSON results object (or a raw string for non-JSON `output`), `toRdf()`/`canonicalize()` dump N-Quads text, `queryDataset()` handles multi-named-graph/multi-engine queries. No `Dataset`, no typed bindings — this is the CLI's own shape, one call in, one string/JSON out. |
| `fn` | the **typed** cell-facing API: `fn.parse(text, {format}) -> Promise<Dataset>`, `fn.query(dataset, sparql, {entail}) -> Promise<Bindings[] \| boolean \| Dataset>` — the same external contract `npm/factoidal/index.js`'s Node-side typed API exposes (`parse()`/`query()`/`Dataset.size`/iteration/`toNQuads()`), reshaped from `Factoidal`'s raw calls by a small adapter defined inline in `hub.njk` (see "Why `fn` is an adapter, not an import" below). Use this for any cell that parses a document or runs SELECT/ASK/CONSTRUCT and wants to work with terms/bindings rather than raw JSON. |
| `d3` | vendored `d3` 7.9.0, for hand-rolled charts. |
| `Plot` | vendored `@observablehq/plot` 0.6.17, for declarative charts. |
| `html` | vendored `@observablehq/stdlib`'s tagged-template HTML helper. |
| `md` | vendored `@observablehq/stdlib`'s tagged-template Markdown helper. |

### The `fn` typed surface in full

```
fn.parse(text: string, options?: {format?: string, baseIRI?: string}) -> Promise<Dataset>

fn.query(dataset: Dataset, sparql: string, options?: {entail?: 'none'|'RDFS'|'OWL-RL'})
  -> Promise<Map<string, Term>[]>   // SELECT
   | Promise<boolean>               // ASK
   | Promise<Dataset>                // CONSTRUCT / DESCRIBE

fn.shaclValidate(data: Dataset|string, shapes: Dataset|string, options?: {format?: string})
  -> Promise<{conforms: boolean, report: Dataset}>
  // report is SHACL_Validation.validation_report_to_graph's graph: one
  // sh:ValidationResult per violation (sh:focusNode, sh:resultPath,
  // sh:resultMessage, sh:sourceConstraintComponent). Throws if the
  // loaded bundle predates the SHACL export -- see "Capability checks"
  // below for the try/catch pattern a cell should use instead of
  // assuming this always resolves.

// Dataset:
dataset.size                        // number of quads
[...dataset]                        // iterate {subject, predicate, object} quads
dataset.toNQuads()                  // N-Quads/N-Triples text

// Term (subject/predicate/object, and Map values from query() rows):
term.termType                       // 'NamedNode' | 'BlankNode' | 'Literal'
term.value                          // IRI, blank-node label, or literal lexical form
term.language                       // '' unless termType === 'Literal' and it has a language tag
term.datatype.value                 // datatype IRI, Literal terms only
```

This is intentionally the same shape `npm/factoidal/index.js`'s
`parse()`/`query()` expose — a post's code sample is written once
against that typed API (and pinned by a `node:test` file importing the
real `npm/factoidal` module directly), then dropped into an
` ```observable-js ` fence with `factoidal.` renamed to `fn.` and any
`import` statement removed (cell bodies are plain function bodies, not
ES modules — no `import`/`export` inside a fence).

### Capability checks

Not every `fn` method is guaranteed to work against every loaded
engine bundle — `fn.shaclValidate` (and the raw `Factoidal.shaclValidate`/
`shexValidate`/`owlClosure`/etc. it's built on) needs the npm-entry ABI
bundle, which an older or stale build might not expose. A cell that
calls one of these should try/catch it and produce an explanatory
value on failure rather than let the whole cell render as a hard
`.observable-cell-error`:

```js
try {
  const result = await fn.shaclValidate(data, shapes);
  return { available: true, conforms: result.conforms };
} catch (err) {
  return { available: false, note: err.message };
}
```

This is the same pattern `npm/factoidal/lib/api.js`'s own `capabilities()`
probe uses server-side (per-function `typeof` checks); a cell doesn't
have access to `capabilities()` directly (it's Node-only, `npm/factoidal`'s
typed API, not exposed on `browser.js`), so try/catch around the call
itself is the client-side equivalent.

### Why `fn` is an adapter, not an import

`npm/factoidal/index.js` (and `fn.js`, the FP dataset wrapper it in
turn wraps) is CommonJS and uses `node:fs`/`node:crypto`/`require()` —
none of which exist in a browser. `npm/factoidal/browser.js` is the
one browser-safe ESM entry point, but it only exposes the raw
CLI-shaped `query()`/`toRdf()`/`canonicalize()` calls (see the API
mismatch documented in
`docs/designissues/2026-07-05-docs-hub-plan.md`'s "Coordination with
the scaffold" section). Rather than fork the engine, re-mirror a
browser build of the typed API, or change `npm/factoidal` itself (all
out of this wave's territory — `npm/factoidal` and `lib/api.js` are
verified-library-adjacent surfaces with their own test suite), `fn` is
a small, self-contained reshaping layer defined directly in
`docs/_includes/hub.njk`: it feeds `Factoidal.toRdf()`/`.query()`
results through a short N-Quads/SPARQL-JSON parser to produce
Dataset/Map-shaped values. It does not touch `npm/factoidal`,
`lib/api.js`, or the `docs/npm/foafos/` mirror.

## Testing discipline

Every live cell's source must also be pinned in that post's test file
under `tests/hub/postNN_test.mjs`. The pinning tests extract the exact
fenced source out of the shipped post file
(`extractObservableCells()` in `tests/hub/_helpers.mjs`) and execute it
via `runObservableCell()` — the same `new Function(...CELL_BINDINGS,
body)` construction `hub.njk`'s `mountCell()` uses — so the test runs
the literal string that ships on the page, not a hand-copied
approximation that can drift. The Node-side `fn` binding used in tests
is the *real* `npm/factoidal` typed API (imported the same way
`npm/factoidal/test/*.js` does), not the browser adapter — since both
implementations satisfy the same external contract above, one cell
source works correctly executed against either.

The browser-side correctness check (does `fn`'s adapter actually work
against the real F\*-extracted engine in a real browser) is
`tests/web-demos/hub_posts_smoke.sh`, which drives headless Chromium
over each built post page and asserts every `.observable-cell` on the
page computes without `.observable-cell-error` and produces a value.

## Constraints every cell must respect

- **Same-origin only.** Every import in `hub.njk` is a same-origin
  Pages path (`{{ '...' | url }}`) — never a CDN URL. Cell bodies
  inherit this: don't `fetch()` an external URL from inside a cell.
- **js engine only.** The wasm_of_ocaml build
  (`docs/npm/foafos/browser-wasm.js`) is stale for newer CLI
  surfaces cells rely on (`--dump-nq` byte-for-byte parity, etc.);
  cells use the default js_of_ocaml path (`Factoidal`/`fn`'s default
  engine), not `queryDataset(..., {engine: 'wasm'})`.
- **No engine/npm/lib changes.** If a cell genuinely cannot be
  expressed against `Factoidal`/`fn` as they stand, don't extend
  `npm/factoidal` or `docs/npm/foafos/` to make it work — write the
  cell against the raw `Factoidal` API instead and note the gap in
  the post's prose.
