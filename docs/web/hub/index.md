---
title: Documentation Hub
layout: hub.njk
---

# Documentation Hub

A home for longer-form, interactive write-ups about how Factoidal
works — RDF/SPARQL concepts demonstrated by running the real
F\*-extracted engine in your browser, not by prose alone.

Each post takes one thing you can do with RDF data — parse it, query
it, validate it, transform it, canonicalize it, serve it — and shows
it running. Most carry live runnable cells; one is a
CLI-transcript-and-architecture page for the network/native features a
sandboxed browser cell can't run. The
[series plan](../../designissues/2026-07-05-docs-hub-plan/) records
each post's central vocabulary and live elements.

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
| `Factoidal` | the raw npm package entry (`../npm/factoidal/browser.js`) — the primitives `fn` is built on, running the F\*-extracted engine in-browser. Cells call `fn`, not this, directly. |
| `fn` | the typed cell-facing API — `fn.parse()` returns a `Dataset` you can iterate and check `.size` on, `fn.query()` returns `Map<string, Term>[]` / `boolean` / another `Dataset` depending on the query form. Every post below calls a Factoidal capability through this. |
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
const graph = await fn.parse('<http://example.org/a> <http://example.org/b> "42" .');
const rows = await fn.query(graph, 'SELECT ?o WHERE { ?s ?p ?o }');
return `hub scaffold smoke test: ${rows.length} binding(s), o = ${rows[0].get("o").value}`;
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
  <li><a href="./17-mutating-and-serving-data/">Mutating and serving data: SPARQL Update, Protocol, Graph Store</a> — INSERT/DELETE DATA and DELETE/INSERT WHERE live via the npm-entry ABI, the durable delta-log write path, and factoidal-http/Graph Store Protocol status (foaf)</li>
  <li><a href="./06-shapes-the-other-dialect-shex/">Shapes, the other dialect: ShEx</a> — ShExJ validation, Wikidata EntitySchemas (wikidata)</li>
  <li><a href="./07-json-ld-rdf-as-json/">JSON-LD: RDF as JSON</a> — @context as mapping, toRdf/jsonldToRdf (schema.org)</li>
  <li><a href="./08-canonical-graphs-rdfc10/">Canonical graphs: RDFC-1.0 and content addressing</a> — canonicalize + urn:rdfc:sha256 (foaf)</li>
  <li><a href="./09-mapping-tables-to-triples-rml/">Mapping tables to triples: RML</a> — CSV/JSON to RDF via rmlMap, real rml-core/rml-io fixtures (schema.org)</li>
  <li><a href="./10-rules-rif-core/">Rules over RDF: RIF Core</a> — RIF frame/BGP rules forward-chained live</li>
  <li><a href="./14-the-rdfjs-api/">The RDF/JS API</a> — DataFactory, Quad terms, .equals() vs === (foaf)</li>
  <li><a href="./12-the-api-tour/">The API tour</a> — npm/factoidal's full function surface + a live capabilities probe (foaf)</li>
  <li><a href="./13-verifiable-credentials-and-csvw/">Verifiable Credentials and CSVW</a> — VC structural validation + eddsa-rdfc-2022 Data Integrity signatures (Ed25519/SHA-256 via HACL*, browser + Node via wasm) + CSVW csv2rdf live (schema.org)</li>
  <li><a href="./15-how-fast-the-performance-story/">How fast: the performance story</a> — dated, commit-linked throughput and on-disk reader numbers, one live in-browser timing illustration (wikidata)</li>
  <li><a href="./16-the-verified-in-fstar-story/">The verified-in-F* story</a> — why F*, the standing verification qualifier, the skimmable RDF.Term.fsti core, one source to four extraction targets</li>
  <li><a href="./18-the-durable-log-live/">The durable log, live: update, persist, reload, corrupt</a> — the full durable-UPDATE lifecycle running in your browser via IndexedDB across a real page reload, a live checksum-rejection demo, and the same delta-log module proven running natively, as KaRaMeL C, and as wasm (foaf)</li>
  <li><a href="./19-correlated-joins-lateral/">Correlated joins: LATERAL</a> — LATERAL evaluates its right side once per left row with that row's bindings substituted in, making top-N-per-group expressible (SPARQL 1.2-track / Jena-compatible)</li>
  <li><a href="./20-fulltext-search-text-query/">Full-text search: text:query</a> — the jena-text magic predicate that searches literals instead of matching triples, conjunctive token matching, no relevance ranking</li>
  <li><a href="./21-geosparql-geometry-and-topology/">GeoSPARQL: geometry, topology, and exact-rational arithmetic</a> — geo:wktLiteral geometries and the geof: Simple Features predicates (sfWithin/sfIntersects/sfDisjoint/sfTouches), geof:distance and geof:envelope, with a point-exactly-on-a-polygon-edge case decided by pure exact-rational F* — no floating-point epsilon (geosparql)</li>
  <li><a href="./22-reaching-out-to-other-data/">Reaching out to other data: the SPARQL client, SERVICE tool-wrapping, and virtual RML</a> — answering SPARQL over data factoidal doesn't hold locally, three ways: query --endpoint against a remote SPARQL 1.1 Protocol server, SERVICE &lt;wrap+http://...&gt; triplifying a REST/CSV/Turtle source (SPARQL-Anything-adjacent), and --data-rml answering through an RML mapping non-materialized (D2RQ/Ontop-style pushdown). A CLI-transcript-and-architecture page — network/native features, no live cell (none)</li>
  <li><a href="./23-decentralized-identifiers-did-key/">Decentralized Identifiers: did:key</a> — resolving a did:key:z6Mk… Ed25519 identifier to its DID Document as pure, offline, F*-verified function application, rendered live as triples and a node-graph (did)</li>
  <li><a href="./24-hdt-header-dictionary-triples/">HDT: querying a compressed binary RDF file</a> — SPARQL run straight over the RML-Core ontology's Header-Dictionary-Triples binary via --data-hdt, with a live triple count, class table, and predicate histogram; no prior decompression to text (hdt)</li>
  <li><a href="./25-xml-wellformedness-and-xpath/">XML well-formedness and XPath</a> — the generic F* XML parser deciding well-formed vs malformed live, plus XPath 1.0 evaluation returning node-sets, strings, numbers, and booleans over a sample document (xml)</li>
  <li><a href="./26-reactive-cells-declare-once-use-everywhere/">Reactive cells: declare once, use everywhere</a> — the hub's cells reference each other ObservableHQ-style: <code>ttl = `…`</code> in one cell, <code>graph = parse(ttl)</code> in the next, then a query, then a chart, each its own cell; the vendored runtime orders them by dependency and re-runs dependents on edit (foaf)</li>
  <li><a href="./27-transforming-and-checking-xml/">Transforming and checking XML: XSLT and Schematron</a> — an XSLT 1.0 stylesheet reshaping a document with <code>xsl:for-each</code>/<code>xsl:value-of</code>, and a Schematron rule firing on a document that violates it and clearing on one that doesn't (none)</li>
  <li><a href="./28-verified-math-rendered/">Verified math, rendered: MathML, TOAN, and linear algebra</a> — MathML evaluation to an exact rational (and a clean <code>undef</code> on division by zero, never <code>NaN</code>), an exact-arithmetic CAS emitting Content MathML for a summation with a small honest Content-to-Presentation converter so the browser can typeset it, and matrix determinants over exact rationals including a fractional result (none)</li>
  <li><a href="./29-validating-data-json-schema-and-xforms/">Validating data: JSON Schema and XForms recalculation</a> — a draft-07 JSON Schema accepting one instance and rejecting another missing a required property, and an XForms bind's <code>calculate</code> MIP deriving one leaf from two others on a live recalculation pass (none)</li>
  <li><a href="./30-owl-reasoning-tableau/">OWL reasoning by model construction: the tableau</a> — a model-construction reasoner classifying individuals into <code>owl:someValuesFrom</code> and <code>owl:hasValue</code> class expressions the Datalog closure cannot reach, an unsatisfiable <code>∃hasChild.owl:Nothing</code> restriction caught as a DL inconsistency RL leaves consistent, a clash-detecting refutation sibling (<code>Tableau.Refute</code>, 2026-07-10) scoring the W3C inconsistency catalogs, and a measured account of what the tableau does not cover (none)</li>
  <li><a href="./31-rdf-1-2-triple-terms/">RDF 1.2: triple terms, reifiers &amp; directional text</a> — statements as first-class terms (<code>&lt;&lt;( s p o )&gt;&gt;</code>) parsed live from Turtle 1.2, queried with SPARQL 1.2 triple-term patterns and the <code>isTRIPLE</code>/<code>TRIPLE</code> builtins, plus <code>~</code> reifier + <code>{| |}</code> annotation provenance and directional literals — with an honest account of what 1.2 still lacks (none)</li>
  <li><a href="./32-this-answer-is-a-theorem/">This answer is a theorem: the certified core-RDFS closure</a> — SPARQL answers over the six-rule core-RDFS (ρdf) closure are machine-checked equivalent to entailment; run the certified engine live and watch the checker refuse false claims (none)</li>
  <li><a href="./33-correlated-federation-lateral-service/">Correlated federation: LATERAL meets SERVICE</a> — SERVICE endpoints bound to local graph snapshots, then driven one row at a time by LATERAL: per-row remote lookups, per-row endpoint SELECTION with <code>SERVICE ?endpoint</code> proved by deliberately conflicting endpoint data, and SILENT's keep-the-row semantics (none)</li>
  <li><a href="./34-extension-functions/">Extension functions: your code inside the verified engine</a> — SPARQL 1.1 §17.6 custom functions registered by IRI (the Comunica model): sync and async JavaScript bodies, a WebAssembly-bodied function, and a function whose body is itself F*-verified (<code>Math.Sigmoid.fst</code>), with a precise account of which links in that pipeline are proved (none)</li>
  <li><a href="./35-wikifunctions-extension-functions/">Wikifunctions inside the query: two F* engines, one SPARQL seam</a> — real Wikifunctions (the <a href="https://github.com/danbri/wikifn-fstar">wikifn-fstar</a> corpus, translated to F*, checked, extracted to JavaScript) registered as §17.6 extension functions by ZID: palindrome canals via <code>Z10052</code>∘<code>Z10096</code>, ROT13, an honest compiled-vs-interpreter distinction, and what it would take to make two proofs into one (none)</li>
  <li><a href="./37-from-the-registry/">Installed, not vendored</a> — loads the actual <code>@factoidal/core@0.1.0</code> package published to npmjs.com, live, from a public CDN that serves npm packages verbatim, and cross-checks it against this site's own same-origin copy: version comparison, parse/SELECT/ASK/canonicalize/extension-function calls run through the fetched registry module, and a row-for-row agreement check against the same-origin engine — this post's CSP alone allows the two npm CDN hosts (none)</li>
  <li><a href="./36-lean-in-the-browser/">Lean 4 in the browser: a second engine on the page</a> — the <a href="https://github.com/danbri/factoidal/issues/466">Lean 4 port</a> compiled Lean → C → wasm32 (Lean's runtime and core library rebuilt for the target, GMP-free, one module for browser + Node + Deno) parsing the same Turtle text and answering the same SPARQL SELECT and typed-literal ASK as the F*-derived engine, with the row-set agreement computed on the page (none)</li>
  <li><a href="./38-one-triple-at-a-time/">One triple at a time</a> — the Lean 4 engine's dispatch surface climbed step by step through <code>fn.l4Call</code>: parse one N-Triples line, ASK, SELECT, a join, Turtle in with byte-identical N-Quads out, INSERT DATA, CONSTRUCT, RDFS and OWL-RL closures queried live, RDFC-1.0 canonicalization deciding graph sameness — and the F* engine answering the final join over the same bytes, the agreement computed on the page (none)</li>
  <li><a href="./40-a-dataset-that-stays-open/">A dataset that stays open</a> — the Lean 4 engine's <a href="https://github.com/danbri/factoidal/issues/585">dataset-handle graph API</a> worked as one session: <code>fn.l4Parse</code> opens a three-department TriG corpus into one handle, a <code>GRAPH ?g</code> query joins across the named graphs, <code>fn.l4Update</code> mutates the same handle in place with no re-parse, <code>rdfsPlusClosure</code> derives a triple from the handle's own serialized data, and <code>owlIsConsistent</code>'s three-valued verdict flips from consistent to inconsistent — with a reason — once a disjoint-class pair is inserted (none)</li>
  <li><a href="./41-a-walkthrough-of-the-ikl-guide/">A walkthrough of the IKL GUIDE</a> — worked examples straight from Pat Hayes and Chris Menzel's <a href="https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html">IKL GUIDE</a>, parsed live section by section: ground predication, restricted quantifier binders, proposition names and the cancelling-parentheses assertion form, quantifying-in, and the GUIDE's own stated <code>=p</code> boundary on propositional identity — with the reader's fragment limits stated where a GUIDE example goes beyond them (none)</li>
  <li><a href="./42-cottas-a-store-at-scale/">COTTAS: a store, not just a format</a> — a 4,000-triple, four-graph corpus loaded into the browser's in-memory COTTAS bytes store and queried three ways (point lookup, star join, cross-graph GRAPH join), each timed against the same queries over a plain parsed dataset — store answers in milliseconds where the re-parsing path takes hundreds, rows equal in both, part of the <a href="https://github.com/danbri/factoidal/issues/595">persistence program</a> (none)</li>
  <li><a href="./43-one-model-theory-under-all-of-it/">One model theory under all of it</a> — the <a href="https://www.w3.org/TR/lbase/">LBase</a> programme of 2003 carried out in Lean 4 and proved instead of sketched: RDF, RDFS, ρdf, OWL 2 RL, OWL 2 DL and SPARQL BGPs translated into one Common Logic/IKL interpretation with per-language axiom schemas, each stage's adequacy against the native formalization stated at its exact strength — with the ρdf closure, Finding C-1's separating pair and an OWL 2 RL row computed live next to the theorems that cover them, and the defects the proof attempts found in shipping code (<a href="https://github.com/danbri/factoidal/issues/598">issue 598</a>) (none)</li>
</ul>

See also: the <a href="../perf/">performance hub</a> — measured
runtime-vs-runtime comparisons across the four extraction targets
(native OCaml, js_of_ocaml, wasm_of_ocaml, KaRaMeL C), including the
C-to-wasm question.
