---
title: "The API tour"
description: "npm/factoidal's whole surface, one function per capability this series has demonstrated — plus a live probe of what this very page's engine bundle actually supports."
layout: hub.njk
series: docs-hub
series_order: 12
vocab: foaf
status: published
tests: tests/hub/post12_test.mjs
---

Every live cell in this series so far has quietly gone through one
door: [`npm/factoidal`](https://github.com/danbri/factoidal/blob/claude/main/npm/factoidal/README.md),
the JavaScript package this project ships from its F\*-extracted
engine. This post makes that door explicit — the full function list,
and a live look at which of those functions the engine bundle backing
*this page* actually supports.

## The typed surface, function by function

`npm/factoidal/index.js`'s public API, each function paired with the
post in this series that already exercises it:

| Function | Does | Seen in |
|---|---|---|
| `parse(text, {format})` | text → `Dataset` | [post 1](./01-triples-rdf-from-first-principles.md), [post 11](./11-one-graph-five-syntaxes.md) |
| `query(data, sparql, {entail})` | SELECT/ASK/CONSTRUCT, with an `entail: 'RDFS'\|'OWL-RL'` option | [post 2](./02-asking-questions-sparql.md), [post 3](./03-schemas-that-infer-rdfs-owl.md) |
| `update(data, updateText)` | SPARQL Update (INSERT/DELETE) | — |
| `serialize(data, {format})` / `canonicalize(data)` | `Dataset` → text, the second RDFC-1.0-canonical | — |
| `shaclValidate(data, shapes)` | SHACL Core validation report | [post 5](./05-shapes-that-validate-shacl.md) |
| `shexValidate(data, schema, focus, shape)` | ShEx shape-expression validation | [post 6](./06-shapes-the-other-dialect-shex.md) |
| `owlClosure(data, mode)` | RDFS/OWL 2 RL forward closure | [post 3](./03-schemas-that-infer-rdfs-owl.md) |
| `rmlMap(mapping, sourceData, kind)` | RML source-to-triples mapping | — |
| `csvwToRdf(csvText, metadataJson, options)` | CSVW csv2rdf conversion | [post 13](./13-verifiable-credentials-and-csvw.md) |
| `jsonldToRdf(jsonldText, options)` | JSON-LD-specific parsing options | — |
| `rifEval(data, rifRulesXml)` | RIF Core forward-chaining saturation | [post 10](./10-rules-rif-core.md) |
| `capabilities()` | feature probe — which of the above the loaded engine bundle actually supports | this post |

Every function past `query` needs the **npm-entry ABI bundle**
(`factoidal-npm-entry.js`) rather than just the CLI-shaped bundle —
`capabilities()` exists precisely because that's an optional extra,
not a given.

## One door, one example

`parse` then `query` — the same two calls under almost every other
live cell in this series, spelled out plainly this once:

```observable-js
const turtle = `
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  @prefix ex:   <http://example.org/> .
  ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
  ex:bob a foaf:Person ; foaf:name "Bob" .
`;

const dataset = await fn.parse(turtle);
const rows = await fn.query(
  dataset,
  `# Every foaf:name in the graph, in alphabetical order.
PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name`
);
return rows.map((row) => row.get("name").value);
```

`["Alice", "Bob"]` — a `Dataset` in, `Map<string, Term>[]` rows out,
same shape whether the query is a five-line SELECT or (as in post 3)
an `entail: 'OWL-RL'` closure running underneath it.

## What can *this page's* engine actually do?

`npm/factoidal`'s own `capabilities()` (server-side, Node-only) walks
the loaded ABI object and reports a `typeof entry.X === 'function'`
check per feature. `fn.capabilities()` is the browser-side mirror
(`docs/_includes/hub.njk`'s `fn` adapter) — it hides the ABI lookup
entirely and returns the same shape:

```observable-js
const caps = await fn.capabilities();
return { available: caps.entry, caps };
```

If every value in `caps` is `true`, the engine bundle this page loaded
is current enough for every live cell in this series to actually run
— including the RIF and CSVW cells two posts either side of this one.
A stale bundle would show `false` for whichever feature it predates,
which is exactly what `capabilities()`'s own doc comment (`{entry:
boolean, ..., rif: boolean}` — see
[`npm/factoidal/lib/api.js`](https://github.com/danbri/factoidal/blob/claude/main/npm/factoidal/lib/api.js))
promises server-side: a per-feature probe, not a blanket
version check.

## The wasm entry caught up

`npm/factoidal` ships two engines side by side: `require('factoidal')`
(js_of_ocaml) and `require('factoidal/wasm')` (wasm_of_ocaml, Node
≥ 22 / WasmGC). Both expose the identical function list above, and —
measured directly against this repository's current wasm build —
`factoidal/wasm`'s `capabilities()` now reports:

```js
{
  entry: true, construct: true, update: true,
  canonicalize: true, graphs: true, canonicalHash: true,
  shacl: true, shex: true, owlClosure: true,
  rml: true, csvw: true, jsonld: true, rif: true
}
```

Two things make this work: the npm-entry ABI bundle
(`factoidal-npm-entry.wasm.js`) includes every export the js_of_ocaml
build ships, and a `require.main`-path bug in `wasm.js`'s entry loader
is fixed — the loader
resolved the bundle's `.wasm.assets/` directory relative to
`require.main.filename`, which is wrong for any caller whose own main
module lives somewhere else (any `test/` file, any downstream
consumer), so the asset read threw deep inside wasm init and was
silently swallowed, misreporting `entry: false` and every function
built on it even when the bundle genuinely had the export. This whole
series' live cells still run against the plain js engine per
[`docs/web/hub/README.md`](../README/)'s "Constraints every cell must
respect" — a separate, still-current constraint (the wasm CLI-bundle
lags newer CLI surfaces like `--dump-nq` byte-for-byte parity), unrelated
to the npm-entry ABI capability gap this section used to describe.

## What's next

[The previous post](./11-one-graph-five-syntaxes.md) parsed one graph
five ways. [The next post](./13-verifiable-credentials-and-csvw.md)
covers the two newest arrivals behind this door — Verifiable
Credentials and CSVW — including one capability this whole series'
"live cell" convention can't reach at all.

Every live cell above is pinned in
[`tests/hub/post12_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post12_test.mjs) —
the exact same source, executed against the real `npm/factoidal`
typed API instead of the in-browser `fn`/`Factoidal` adapters.
