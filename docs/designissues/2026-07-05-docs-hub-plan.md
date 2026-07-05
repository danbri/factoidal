# Documentation hub: series plan

**Status:** plan doc + first three drafts (this wave). Landing/scaffold
wiring is a separate sibling deliverable — see "Coordination with the
scaffold" below.

**Goal (from the owner's `/goal`):** a series of blog-post-like docs
showcasing every piece of tech this project has implemented, building
up from RDF, using foaf, skos, schema.org, and wikidata as the central
vocabularies, forming the project's documentation hub.

This doc is the series map: one post per implemented capability,
ordered pedagogically (bottom-up: terms → syntaxes → queries →
inference → shapes/validation → interchange → engineering story), each
entry naming its central vocabulary, its live interactive elements
(what actually runs, client-side, against the committed npm package),
and the unit test file that pins its code samples. Every score cited
below is checked against
[`docs/claude-rules/current-state.md`](../claude-rules/current-state.md)
(refreshed 2026-07-05) and, where a figure exists there, against
[`docs/test-results/latest.json`](../test-results/latest.json) — the
two occasionally disagree (see the JSON-LD note under post 09) and
this doc always takes the most recently dated entry as ground truth.

## Format convention

Each post is a standalone Markdown file with:

- YAML front matter: `title`, `description`, `series: docs-hub`,
  `series_order`, `vocab`, `status` (`draft` | `planned`), `tests`
  (path to its pinning test file).
- Prose sections per `skills/markdown-style/SKILL.md` (no sycophantic
  adjectives, clickable links).
- Live cells as fenced ` ```js ` blocks — the convention Observable
  Framework treats natively (a top-level ` ```js ` block in a Markdown
  page is a reactive cell, not a static code sample). This repo already
  runs Eleventy for `docs/` (`docs/.eleventy.js`); if the sibling
  vendoring Observable wires it in as an Eleventy plugin/shortcode
  rather than the standalone Observable Framework static-site
  generator, the fence marker is what needs to change, not the code
  inside the fences — every cell in the three drafts below is plain
  JS calling the published npm surface (`parse`, `query`, `Dataset`,
  `dataFactory`), no framework-specific syntax. **This is a
  loose-coordination point, not a hard contract** — wave-B integration
  adjusts the fence convention if the scaffold's actual mechanism
  differs; the content and code samples do not need to change.
- Every code sample in a post also exists, verbatim in effect (same
  input strings, same assertions), in that post's test file under
  `tests/hub/`, run with `node --test` against the committed
  `npm/factoidal` bundles (no F* toolchain needed, matching
  `npm/factoidal/test`'s own harness style: `node:test`,
  `tests/hub/_helpers.mjs` mirrors `npm/factoidal/test/helpers.js`'s
  bundle-selection logic).

## Central vocabulary strategy

- **foaf** — the entry point (`foaf:knows`, `foaf:Person`, `foaf:name`):
  small, human-legible, no reasoning required to read a foaf graph.
  Anchors posts 01, 04, 05, 10, 13, 14 (the "mechanics" posts — terms,
  syntaxes, update/protocol, canonicalization, the two JS APIs) so the
  running example dataset carries across without re-explaining a new
  domain each time.
- **wikidata** (`wd:`/`wdt:`/`rdfs:label`) — query showcases (posts 02,
  08, 15): real Wikidata entity/property IRIs so the query syntax
  matches production Wikidata queries, but every dataset is a small
  hand-authored excerpt of well-known, easily-verified facts (Douglas
  Adams `wd:Q42`, `wdt:P31` instance-of, `wdt:P106` occupation), not a
  live fetch — no network dependency in a pinned test.
- **schema.org** — typed-data and inference posts (03, 07, 09, 11):
  the vocabulary most real-world structured data (JSON-LD in
  `<script type="application/ld+json">`, GS1/schema.org mixed graphs)
  actually uses, and it cleanly demonstrates cross-vocabulary
  `owl:equivalentClass` mapping to foaf.
- **skos** — concept-scheme posts (06), reusing
  `skills/skos-integrity/` artifacts wholesale (shapes, queries, axiom
  data, valid/broken fixture pair) rather than inventing new SKOS data.
- No fixed vocab — the verified-in-F\* story (16) and RIF (12), which
  are about the engine and rule language respectively, not a domain.

## Series map

| # | Title | Capability | Vocab | Live elements | Test file | Status |
|---|---|---|---|---|---|---|
| 01 | Triples: RDF from first principles | RDF terms/triples (`RDF.Term.fsti`), Turtle parsing | foaf | live Turtle parse, dataset size, iterate quads, blank-node example | `tests/hub/post01_test.mjs` | **drafted** |
| 02 | Asking questions: SPARQL | SPARQL 1.1 query (SELECT/ASK/CONSTRUCT, property paths) | wikidata | live SELECT/ASK/CONSTRUCT, live property-path alternation | `tests/hub/post02_test.mjs` | **drafted** |
| 03 | Schemas that infer: RDFS and OWL 2 RL | RDFS closure, OWL 2 RL closure | schema.org | live entail:'RDFS' vs entail:'OWL-RL' toggle showing inferred triples | `tests/hub/post03_test.mjs` | **drafted** |
| 04 | All the syntaxes: N-Triples, N-Quads, TriG, RDF/XML | the other four parsers/serializers | foaf (same running dataset) | live round-trip: parse in one format, serialize/compare in another | `tests/hub/post04_test.mjs` | planned |
| 05 | Mutating and serving data: SPARQL Update, Protocol, Graph Store | INSERT/DELETE/LOAD/CLEAR, SPARQL HTTP protocol, GSP | foaf | live `update()` before/after diff; note on the HTTP endpoint (`SPARQL.HTTP.*`) as a server-side capability, not client-runnable in a static page | `tests/hub/post05_test.mjs` | planned |
| 06 | Concept schemes: SKOS and its integrity conditions | SKOS + the six S-numbered integrity conditions | skos | live SHACL + SPARQL checks against `skills/skos-integrity/sample-vocab(-broken).ttl` | `tests/hub/post06_test.mjs` | planned |
| 07 | Shapes that validate: SHACL | `SHACL.Validation.fst` | schema.org | live `validate`-equivalent call showing a conforming vs violating report | `tests/hub/post07_test.mjs` | planned |
| 08 | Shapes, the other dialect: ShEx | ShEx schema validation | wikidata (ShEx's home community is Wikidata's EntitySchemas) | live ShEx validate against a small schema | `tests/hub/post08_test.mjs` | planned |
| 09 | JSON-LD: RDF as JSON | JSON-LD 1.1 `toRdf`/context processing | schema.org | live expand/compact toggle over a `application/ld+json` snippet | `tests/hub/post09_test.mjs` | planned |
| 10 | Canonical graphs: RDFC-1.0 and content addressing | `RDF.Canonical.fst`, graphs API | foaf | live `canonicalize()` + hash display; relabel blank nodes, show hash unchanged | `tests/hub/post10_test.mjs` | planned |
| 11 | Mapping tables to triples: RML | `RML.Mapping.fst`/`RML.Sources.fst`/`RML.Eval.fst` | schema.org | live CSV-row-to-triples preview from a small inline CSV + mapping doc | `tests/hub/post11_test.mjs` | planned |
| 12 | Rules over RDF: RIF | `RIF.Core.*` | none (rule language, not a domain vocab) | live RIF rule evaluation over a tiny fact base | `tests/hub/post12_test.mjs` | planned |
| 13 | The RDF/JS API | `rdfjs.js` (`Dataset`, `DataFactory`, `match()`) | foaf | live `Dataset.match()` playground | `tests/hub/post13_test.mjs` | planned |
| 14 | The functional dataset API | `fn.js` (`FnDataset`, `filter`/`union`/`difference`/`cell`/`derive`) | foaf | live pipeline: `parse` → `filter` → `union` → `canonicalize`, purity demonstrated (inputs unchanged) | `tests/hub/post14_test.mjs` | planned |
| 15 | How fast: the performance story | throughput measurements, `Server-Timing`, profiling policy | wikidata (the `wikidata-lifesci-kgx` and UK Parliament perf corpora) | live in-browser timer over a small dataset, with a link out to the full benchmark numbers (large corpora are not shippable to a static page) | `tests/hub/post15_test.mjs` | planned |
| 16 | The verified-in-F\* story | the F\*→OCaml/JS/wasm/C extraction pipeline itself | none | no live cell (the "live element" is the reader opening `RDF.Term.fsti` and the module dep-graph demo at `docs/web/demos/dep-graph/`) | `tests/hub/post16_test.mjs` | planned |
| 17 | Tables with metadata: CSVW *(pending)* | `CSVW.Metadata.fst` — Stage 1 only | schema.org | none yet | none yet | **pending** (F\* module is a sibling's in-progress skeleton; do not draft until Stage 6+ CSV→RDF conversion lands) |
| 18 | Verifiable Credentials *(pending)* | none yet | schema.org/foaf | none yet | none yet | **pending** (no `VC.fst` module exists; `third_party/testing/vc` is vendored test data only, no engine to demo) |

Labelled total: **16 posts have an implemented capability to draw on
today** (01–16); **2 are marked pending** (17–18) because the
underlying F\* module either doesn't exist yet (VC) or is a
stage-1-only skeleton with no CSV→RDF conversion path (CSVW) — both
explicitly out of this task's territory (no F\* edits) and correctly
left undrafted rather than padded with a placeholder.

## Per-post detail

### 01 — Triples: RDF from first principles (drafted)

Anchor module: [`formal/fstar/RDF.Term.fsti`](../../formal/fstar/RDF.Term.fsti)
— the tree's third `.fsti`, written prose-first: blank nodes, IRIs
(`wf_iri`), literals (`wf_literal`, the `literal_wf` language-tag
rule), the three-way `rdf_term` sum type, and `subject` (the strictly
smaller IRI-or-blank-node set). The post walks the same three
concepts — term, triple, graph — informally, then parses a `foaf:knows`
Turtle snippet live and inspects the resulting quads. Also shows a
blank-node example (`[] a foaf:Person`) so "blank node" isn't only a
definition.

Score/feature grounding: RDF 1.1 combined 1031 pass, 0 fail (of 1031)
— rdf-turtle 313/313, per
[`docs/test-results/latest.json`](../test-results/latest.json).

### 02 — Asking questions: SPARQL (drafted)

SELECT with `OPTIONAL`, ASK, CONSTRUCT, and a property-path alternation
(`wdt:P31|wdt:P106`) over a five-triple Wikidata-shaped excerpt
(`wd:Q42` Douglas Adams, `wdt:P31` instance-of `wd:Q5` human, `wdt:P106`
occupation `wd:Q36180` writer — real, well-attested Wikidata
IRIs/facts, not a live fetch).

Score grounding: SPARQL 1.1 631 pass, 0 fail (of 631), including
`property-path` 33/33 and `construct` 7/7
([`docs/test-results/latest.json`](../test-results/latest.json)).

### 03 — Schemas that infer: RDFS and OWL 2 RL (drafted)

Two small schema.org graphs. First: `schema:Person rdfs:subClassOf
schema:Thing`, one instance — `entail: 'RDFS'` adds the `schema:Thing`
type that plain SELECT doesn't see. Second: `schema:Person
owl:equivalentClass foaf:Person` — RDFS entailment does *not* add
`foaf:Person` (equivalence isn't an RDFS construct), but `entail:
'OWL-RL'` derives both `foaf:Person` and `owl:Thing`. The two toggles
side by side make the RDFS/OWL-RL boundary concrete instead of
asserted.

Score grounding: rdf-mt (RDFS closure rules, 14 of its 39 tests) 39
pass, 0 fail; OWL 2 RL positive entailment 28 pass, 2 fail (of 30 —
the two documented-impossible comprehension cases), NE 6/6,
Consistency 76/76, Inconsistency 14/14 (`docs/claude-rules/current-state.md`,
wave-10 battery, `owl_rl_positive_entailment` in
`docs/test-results/latest.json` confirms 28/2/30).

### 04 — All the syntaxes (planned)

Same foaf dataset as post 01, parsed once from Turtle, then serialized
and re-parsed through N-Triples, N-Quads (named-graph variant), TriG,
and RDF/XML, diffing the triple set each time. Grounding: rdf-n-triples
70/70, rdf-n-quads 87/87, rdf-trig 356/356, rdf-xml 166/166 (RDF 1.1
combined 1031/1031).

### 05 — Mutating and serving data (planned)

`update()` (INSERT DATA/DELETE DATA/DELETE-WHERE) shown as a
before/after diff over the foaf dataset — this runs client-side today
via the npm-entry ABI. The HTTP protocol/Graph Store layer
(`SPARQL.HTTP.*`, `SPARQL.Protocol.fst`) is server-side; the post
documents it (protocol 34/34, http-rdf-update 19/19) with a `curl`
transcript rather than a live cell, since a static docs page has no
server to call.

### 06 — Concept schemes: SKOS (planned)

Reuses `skills/skos-integrity/` verbatim: `skos-shapes.ttl`,
`queries/*.rq`, `skos-axioms.ttl`, and the valid/broken fixture pair.
The post is the six S-numbered integrity conditions (S9, S13, S14,
S27, S37, S46) with the same SHACL-then-SPARQL-then-closure structure
the skill doc already uses, reframed as tutorial prose rather than a
runbook. No new SKOS engine code — the skill's own "Engine notes"
section already confirms no gaps were found building it.

### 07 — Shapes that validate: SHACL (planned)

Score grounding: SHACL 120 pass, 0 fail (of 120 — 98 core +
report-isomorphism, 22 `sh:sparql` including custom constraint
components and `$shapesGraph`/`$currentShape`). Vocab: schema.org
typed data (a `schema:Person` shape requiring `schema:name`).

### 08 — Shapes, the other dialect: ShEx (planned)

Score grounding: ShEx 1181 pass, 1 mismatch (upstream fixture defect
— `start2RefS2.json` has `p1` where the canonical `.shex` has `p2`),
0 deferred, 0 skipped (of 1182). Vocab: wikidata, since ShEx's primary
real-world adoption is Wikidata's EntitySchemas namespace — the post
can note that connection explicitly rather than picking wikidata
arbitrarily.

### 09 — JSON-LD: RDF as JSON (planned)

Score grounding: **460 pass, 1 fail, 6 skip (of 467)** — commit
`a69aa2c` ("JSON-LD toRdf: 460 pass, 1 fail, 6 skip (of 467) — the
goal line"). An earlier draft of this section cited 437/22/8 from
`current-state.md`'s then-stale "Last refreshed" paragraph;
commit-order checking (`2d3bddc` 437/22/8 → `a69aa2c` 460/1/6, same
day) settled it, and `current-state.md` has been corrected. The 1
fail is the documented Ryu-class float-formatting case; the 6 skips
are JSON-LD 1.0-only tests. Re-check `current-state.md` when the
post is drafted in case the number has moved again.

### 10 — Canonical graphs: RDFC-1.0 (planned)

Score grounding: RDFC-1.0 86 pass, 0 fail (of 86,
`docs/test-results/latest.json`'s `rdfc10` total — supersedes the
stale "84 pass, 1 fail, 1 stub" figure still sitting in
`current-state.md`'s item 6 prose from an earlier wave). Live cell:
canonicalize the foaf dataset twice with different blank-node labels,
show the hash is identical; change one triple, show the hash changes.

### 11 — Mapping tables to triples: RML (planned)

Score grounding: RML rml-core 76 pass, 0 fail (of 76) — joins
(index-paired joinless RefObjectMaps), error-fixture validations.
Vocab: schema.org (a CSV of people mapped to `schema:Person` +
`schema:name`).

### 12 — Rules over RDF: RIF (planned)

Score grounding: RIF 34 pass, 4 labelled fails, 12 precise skips (of
50) — DTB builtins, safeness/conformance checker, import-rejection
table; every entry scored or construct-named (no unexplained gaps).

### 13 — The RDF/JS API (planned)

`npm/factoidal/rdfjs.js`'s `Dataset`/`DataFactory`/`match()` as a
standalone practical-ergonomics post — this is the layer every other
post's live cells are already built on, made explicit for readers who
want to write their own JS against factoidal without the higher-level
`fn.js` wrapper.

### 14 — The functional dataset API (planned)

`npm/factoidal/fn.js`: frozen `FnDataset`, `filter`/`mapQuads`/
`union`/`difference` purity (inputs never mutated — `npm/factoidal/test/fn.test.js`
already pins this with 23 pass, 0 fail), memoized RDFC hashes, the
`cell`/`derive` reactive-composition seam. This is the piece most
directly reusable inside Observable-style live cells in the other
posts, so this post is also implicitly the "how the live cells in this
whole series work" reference.

### 15 — How fast: the performance story (planned)

Grounding: `skills/perf-benchmarking/SKILL.md` — Turtle throughput
~100k triples/s near-linear to 1M (2026-07-03 spot-check,
`docs/claude-rules/current-state.md` line 133-134), in-memory
index-build wall 137s → 2.2s (issue #259), the known superlinear
`dump-nq`/`canonicalize` tail on bnode-heavy graphs (documented as an
open item, not hidden). A live cell can only time a small (thousands
of triples) dataset in-browser; the post links out to the full
benchmark numbers rather than trying to reproduce a 1M-triple run on a
docs page.

### 16 — The verified-in-F\* story (planned)

No live cell — the point of this post is to send the reader into the
actual `.fst`/`.fsti` files. Structure: Iron Rules #1–#2 (F\* is the
source of truth, code is extracted not hand-written) from `CLAUDE.md`,
then a guided tour: `RDF.Term.fsti` (terms) → `RDF.Vocabulary.fsti` /
`RDF.Indexed.fsti` (the other two human-readable `.fsti`s) →
`RDF.Graph.Executable.fst` (the executable core) →
`SPARQL11.Algebra.fst`/`SPARQL11.Parser.fst` (the ⚠ `--admit_smt_queries`
caveat disclosed honestly, per Iron Rule #10's neighbor concern) →
`build-ocaml.sh` (the extraction pipeline) → the `assume val` glue
taxonomy (`skills/ocaml-boundary/SKILL.md`). Closing figure: 90 F\*
modules, 47517 lines, 141 `assume val` declarations across 20 modules
— cited with the caveat that every `assume val` has a named stub patch
and an open issue (Iron Rule #3), not a silent hole. Embed the existing
module dependency graph demo (`docs/web/demos/dep-graph/`) as the one
genuinely interactive element.

## Coordination with the scaffold

This wave's territory is content only: the plan doc, three drafts, and
their pinning tests. The Eleventy/Observable vendoring and hub scaffold
landed in parallel, in the same working tree, during this wave —
`docs/_includes/hub.njk`, `docs/web/hub/index.md`,
`third_party/observable/`. Reading those (read-only, not this task's
territory) surfaced a concrete, non-hypothetical adjustment wave B
needs to make, precise enough to write down now instead of leaving as
a vague "coordinate loosely":

1. **Front-matter shape.** The three drafts use `title`, `description`,
   `series`, `series_order`, `vocab`, `status`, `tests`. The landed
   scaffold's own page (`docs/web/hub/index.md`) uses `title` +
   `layout: hub.njk`. Reconciling these is a rename, not a rewrite.

2. **Live-cell fence marker: `js` vs `observable-js`.** `hub.njk`'s
   runtime only mounts ` ```observable-js ` blocks (see its
   `mountCell`/`querySelectorAll('code.language-observable-js')`); a
   plain ` ```js ` fence renders as an inert, static code sample. The
   three drafts here deliberately keep plain ` ```js ` — see point 3,
   this isn't an oversight to fix by a find/replace.

3. **API-shape mismatch (the finding worth flagging loudly).** The
   landed scaffold's cell binding, `Factoidal`, is
   `npm/factoidal/browser.js` — a **raw, single-shot** API:
   `Factoidal.query(dataString, sparqlString, {dataFormat, entail,
   output})` takes a plain string and returns a raw SPARQL-JSON results
   object (`result.results.bindings[i].varName.value`); there is no
   `Factoidal.parse()` returning an RDF/JS `Dataset`, no `Dataset`/
   `dataFactory` binding at all. The three drafts here instead use the
   **typed** `npm/factoidal` API (`index.js`/`index.mjs`:
   `factoidal.parse()` → `Dataset`, `factoidal.query()` → an array of
   `Map<string, Term>` bindings or a `Dataset` for CONSTRUCT) — the
   same API `npm/factoidal/test/api.test.js` and `fn.test.js` test,
   and the one this task's rules point at ("Use the COMMITTED npm
   module (npm/factoidal) for tests... see test/fn.test.js"). Dropping
   these cells' bodies verbatim into an ` ```observable-js ` fence
   today would throw (`Factoidal.parse is not a function`) — that
   mismatch is why the fences stay plain ` ```js ` rather than being
   mechanically renamed. Two ways wave B can close this gap, in
   ascending order of effort:
   - **(a) Adapt the cell bodies** to `browser.js`'s dataString-in/
     SPARQL-JSON-out shape (drop `Dataset` iteration, read
     `result.results.bindings` directly) — mechanical per-post rewrite,
     no runtime change.
   - **(b) Extend `hub.njk`'s `CELL_BINDINGS`** to also expose the
     typed Dataset API (e.g. a browser build of `index.mjs`'s surface,
     or add `parse`/typed `query` to `browser.js` itself) so future
     posts get `Dataset.match()`, iteration, `termType` checks, etc.
     for free — richer cells, one-time runtime cost.
   Either way, the *content* in the three drafts doesn't need to
   change — only which JS API the cell bodies call.

## What is NOT in this wave

- No F\* edits (CSVW/VC posts stay `pending` rather than speculative).
- No build scripts, no `third_party/` changes.
- No commit/push — the coordinator lands after checks, per this
  agent's task rules.
- Posts 04–18 are planned, not drafted — their test files
  (`tests/hub/post04_test.mjs` onward) don't exist yet. Creating them
  without the post they pin would violate the same "code sample must
  have a test" discipline this plan asks every future post to follow.
