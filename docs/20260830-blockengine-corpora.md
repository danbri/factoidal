# Block engine corpus ladder

Date: 2026-08-30

## Purpose

The block engine needs one reproducible corpus ladder, not a single enormous
dump. Each stage should have a known source, RDF syntax, query set, byte size,
and result oracle.

## Selected inputs

| Stage | Input | Role | Status |
|---|---|---|---|
| Micro | `BlockMvp` fixture | proofs and byte-corruption guards | runnable |
| Small real RDF | `examples/wikidata/subsets/lifesci-kgx/data/active_site.ttl` | Lean Turtle -> indexed block -> parsed SPARQL SELECT/COUNT | runnable: 486 triples, 132 `wdt:P31` rows |
| Medium raw KGX | `disease.ttl`, `chromosome.ttl`, `sequence_variant.ttl` | realistic Wikidata-shaped access and joins | `chromosome.ttl` runs through the indexed path: 9,227 triples and a `wdt:P31` COUNT in about 25 seconds including parse and build; `disease.ttl` remains a later load-path target |
| Medium Schema.org/Bioschemas | materialize `kgx/wikidata/bioschemas/{disease,chromosome,sequence_variant}.sparql` | vocabulary-mapped benchmark for the block engine | selected; materialization not yet run in this workstream |

The checked KGX Turtle files are raw Wikidata-property materializations. Their
prefix declarations include Schema.org and Bioschemas, but this does not make
their emitted `wdt:` triples Schema.org data. The `kgx/wikidata/bioschemas/`
CONSTRUCT queries are the explicit conversion source: for example,
`disease.sparql` constructs `schema:MedicalCondition`,
`schema:signOrSymptom`, `schema:associatedAnatomy`, and `schema:drug` from
Wikidata properties.

## Corpus tool

`l4block-corpus` is a native executable-edge probe. It accepts Turtle plus an
optional predicate-count shortcut or a full SELECT query, then runs:

```text
Lean Turtle parser -> TermId dictionary + predicate partitions
  -> backend candidate scan -> parsed SPARQL SELECT
```

From `formal/lean4/`:

```bash
/Users/danbri/.elan/bin/lake build l4block-corpus
./.lake/build/bin/l4block-corpus \
  ../../examples/wikidata/subsets/lifesci-kgx/data/active_site.ttl \
  http://www.wikidata.org/prop/direct/P31
```

Observed result on 2026-08-30:

```text
triples=486 terms=476 id-rows=486 predicate-partitions=2
COUNT(wdt:P31)=132
```

This is a correctness and integration probe, not a timing claim. The indexed
path selects the predicate partition but still parses and builds the entire
in-memory graph for each process invocation. It is not yet the stream-oriented
canonical storage path for large corpora.

## Bioschemas conversion protocol

Use the checked query sources and retain the execution evidence. Do not commit
materialized outputs by default.

```bash
mkdir -p tmp/blockengine-kgx/bioschemas
curl --fail-with-body --retry 4 --retry-delay 2 \
  -X POST https://qlever.dev/api/wikidata \
  -H 'Content-Type: application/sparql-query' \
  -H 'Accept: text/turtle' \
  --data-binary @kgx/wikidata/bioschemas/disease.sparql \
  -o tmp/blockengine-kgx/bioschemas/disease.ttl
```

Before a result is used as a benchmark input, record the query hash, retrieval
time, endpoint response status, output byte count, triple count after parsing,
and result hash. Convert the accepted materialization to line-oriented RDF
before the canonical TermId block codec work. The current BLK0 format is only
a transition probe and must not become the persistent corpus artifact.

## Next corpus gate

The next block-engine corpus target is the three-file Bioschemas subset. Its
first query should count `rdf:type schema:MedicalCondition` in the disease
graph. A following cross-graph query should use the converted disease and
sequence-variant data. Run that only after the stream-oriented load and
dictionary block path exists; the current whole-file Turtle-plus-BLK0 probe is
already showing why that boundary is needed.
