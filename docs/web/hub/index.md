---
title: Documentation Hub
layout: hub.njk
---

# Documentation Hub

A home for longer-form, interactive write-ups about how Factoidal
works — RDF/SPARQL concepts demonstrated by running the real
F\*-extracted engine in your browser, not by prose alone.

Sixteen posts are published below, each with live runnable cells. The
rest of the series (see
[the series plan](../../designissues/2026-07-05-docs-hub-plan/) for
the full map and vocabulary strategy) is still planned.

## How the interactive cells work

A fenced code block tagged `observable-js` becomes a **live cell**:
the page's runtime script (see `docs/_includes/hub.njk`) finds every
` ```observable-js ` block, wraps its body in an async function, and
runs it through a vendored
[Observable Runtime](https://github.com/observablehq/runtime) +
[Inspector](https://github.com/observablehq/inspector) pair — the same
reactive-execution model observablehq.com notebooks use, vendored
under `third_party/observable/` so nothing loads from a CDN.

Each cell's function body receives six fixed bindings by parameter
name:

| Name | What it is |
|---|---|
| `Factoidal` | the raw npm package entry (`../npm/foafos/browser.js`) — `query`, `queryDataset`, `toRdf`, `canonicalize`, etc., running the F\*-extracted engine in-browser. Single-shot: strings in, SPARQL-JSON out. |
| `fn` | the typed cell-facing API — `fn.parse()` returns a `Dataset` you can iterate and check `.size` on, `fn.query()` returns `Map<string, Term>[]` / `boolean` / another `Dataset` depending on the query form. Most posts below use this. |
| `d3` | vendored `d3` 7.9.0, for hand-rolled charts |
| `Plot` | vendored `@observablehq/plot` 0.6.17, for declarative charts |
| `html` | vendored `@observablehq/stdlib`'s tagged-template HTML helper |
| `md` | vendored `@observablehq/stdlib`'s tagged-template Markdown helper |

The full cell-authoring contract — the `fn` typed API in detail, why
it's an adapter rather than a direct import, and the testing
discipline every live cell is held to — is documented in
[`README.md`](README/).

<!-- Note: linked as a pre-resolved `README/` path, not `./README.md`.
     docs/.eleventy.js's mdlink-to-slug transform assumes every page
     it rewrites links on is nested one pretty-URL directory below its
     source's directory (true for the three posts, which each get
     their own subdirectory) -- but this page IS the directory index
     (`web/hub/index.md` serves at `/web/hub/`, no nesting), so the
     transform's blanket `../` prefix would point one level too high.
     A `.md`-suffixed link here would resolve to a broken URL. -->


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

## The series

<ul class="post-series">
  <li><a href="./01-triples-rdf-from-first-principles/">Triples: RDF from first principles</a> — RDF terms/triples, Turtle parsing (foaf)</li>
  <li><a href="./02-asking-questions-sparql/">Asking questions: SPARQL</a> — SELECT/ASK/CONSTRUCT, property paths (wikidata)</li>
  <li><a href="./03-schemas-that-infer-rdfs-owl/">Schemas that infer: RDFS and OWL 2 RL</a> — RDFS + OWL 2 RL closure (schema.org)</li>
  <li><a href="./04-concept-schemes-skos/">Concept schemes: SKOS and its integrity conditions</a> — SKOS + the S9/S13/S14/S27/S37/S46 integrity conditions (skos)</li>
  <li><a href="./05-shapes-that-validate-shacl/">Shapes that validate: SHACL</a> — minCount/datatype/class constraints, validation reports (foaf)</li>
  <li><a href="./11-one-graph-five-syntaxes/">One graph, five syntaxes</a> — Turtle/N-Triples/N-Quads/TriG/RDF-XML round-tripping to identical bytes (foaf)</li>
  <li class="placeholder">Mutating and serving data: SPARQL Update, Protocol, Graph Store</li>
  <li><a href="./06-shapes-the-other-dialect-shex/">Shapes, the other dialect: ShEx</a> — ShExJ validation, Wikidata EntitySchemas (wikidata)</li>
  <li><a href="./07-json-ld-rdf-as-json/">JSON-LD: RDF as JSON</a> — @context as mapping, toRdf/jsonldToRdf (schema.org)</li>
  <li><a href="./08-canonical-graphs-rdfc10/">Canonical graphs: RDFC-1.0 and content addressing</a> — canonicalize + urn:rdfc:sha256 (foaf)</li>
  <li><a href="./09-mapping-tables-to-triples-rml/">Mapping tables to triples: RML</a> — CSV/JSON to RDF via rmlMap, real rml-core/rml-io fixtures (schema.org)</li>
  <li><a href="./10-rules-rif-core/">Rules over RDF: RIF Core</a> — RIF frame/BGP rules forward-chained live</li>
  <li><a href="./14-the-rdfjs-api/">The RDF/JS API</a> — DataFactory, Quad terms, .equals() vs === (foaf)</li>
  <li><a href="./12-the-api-tour/">The API tour</a> — npm/factoidal's full function surface + a live capabilities probe (foaf)</li>
  <li><a href="./13-verifiable-credentials-and-csvw/">Verifiable Credentials and CSVW</a> — VC structural validation (no crypto yet) + CSVW csv2rdf live (schema.org)</li>
  <li><a href="./15-how-fast-the-performance-story/">How fast: the performance story</a> — dated, commit-linked throughput and on-disk reader numbers, one live in-browser timing illustration (wikidata)</li>
  <li><a href="./16-the-verified-in-fstar-story/">The verified-in-F* story</a> — why F*, the standing verification qualifier, the skimmable RDF.Term.fsti core, one source to four extraction targets</li>
</ul>

(Placeholder titles come straight from
[the series plan](../../designissues/2026-07-05-docs-hub-plan/)'s
series map, which also names each post's central vocabulary, live
elements, and pinning test file.)
