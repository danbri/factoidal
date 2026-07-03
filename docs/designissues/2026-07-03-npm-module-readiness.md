# npm module readiness — gaps vs a Jena / RDF4J / rdflib user's expectations

**Status:** assessment + sequencing, 2026-07-03 (owner question: "what
is missing before it is worth rolling an npm module?").
**Packaging plumbing exists:** `build-ocaml.sh npm` stages the JS/wasm
bundles into `npm/factoidal/` with a generated `version.json`. The
gaps below are product gaps, not build gaps.

## Blocking (a toolkit user bounces off without these)

1. **Programmatic API.** Jena/RDF4J users think in `Model` /
   `Repository` objects: parse into a dataset, add/remove quads, run a
   query, iterate bindings. Today's JS surface is demo glue (the
   `factoidal-sparql-client` web component, the runner bundle). Needed:
   a stable, documented, typed entry —
   `parse(text, {format}) -> Dataset`,
   `query(dataset, sparql) -> Bindings[]`, `update(...)`,
   `serialize(dataset, {format})`, `canonicalize(dataset)` — plus
   TypeScript `.d.ts`. Single biggest gap.
2. **RDF/JS data-model interop.** The npm RDF ecosystem (Comunica,
   N3.js, rdf-ext, graphy) composes via the RDF/JS spec (`DataFactory`,
   `Quad`, `Term`, `Store`). An adapter between our extracted term
   representation and RDF/JS terms is the community entry ticket;
   without it we are an island, with it every existing tool becomes a
   test harness and distribution channel.
3. **JSON-LD.** Absent entirely; for the npm audience it is the
   dominant RDF syntax. Jena/RDF4J/rdflib all ship it. W3C suite is
   ~800 tests; a Phase-1 expanded-form parser in F\* (rule #4: parsers
   are F\*-first) is the meaningful start.
4. **Per-file blank-node scoping (standing priority 2d).** The
   load-two-files-and-query workflow — the first thing a Sesame user
   does — hits the cross-document `_:x` join bug. Must land first.

## Important, not blocking (state limits honestly in v1)

5. Native bindings objects (JS maps, not serialized SRJ strings) —
   the F\* results writers exist; API shaping only.
6. Memory/size honesty: ~1.2 KB/quad in-memory, multi-MB bundle, no
   streaming parse (Jena's `StreamRDF` has no analogue here yet).
   Document limits in v1; chunk-resumable parse is the follow-up.
7. Release discipline: semver, changelog, the rule-#11 qualifier in
   the package README, publish wired to the gated-push flow so every
   published version corresponds to a gates-green commit.

## Differentiators to lead with

- Full SPARQL 1.1 (query + update + protocol semantics) entirely
  client-side, no server.
- **RDFC-1.0 canonicalization built in** (`factoidal canonicalize`;
  rdflib/N3.js require a separate library).
- OWL-RL entailment as a query option (`--entail OWL-RL`).
- The formally-verified-core story, with the honest qualifier.

## Sequencing

2d fix (queued) → JS API design doc + `.d.ts` + RDF/JS adapter (one
work package) → JSON-LD Phase 1 (largest lift) → bindings API +
release discipline → publish v0.x with documented limits.
