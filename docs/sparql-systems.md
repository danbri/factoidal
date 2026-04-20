# SPARQL Systems Review

Date: 2026-04-20

## Purpose

This note sketches the comparison set for Factoidal performance work. It is not
a full benchmark report. It records which systems are credible SPARQL 1.1 role
models, what they are known for, and where Factoidal currently sits.

## Local Test Corpus

The immediate local data target is `tmp/wikidata-lifesci-kgx/`.

Observed size: about 243 MB of Turtle files. The largest files are:

- `taxon (timesout).ttl`: 134 MB
- `Protein__protein3.ttl`: 48 MB
- `Protein__protein1.ttl`: 33 MB
- `gene.ttl`: 17 MB

Naive Factoidal ingestion of these Turtle files is expected to be very slow.
For performance work, prefer a line-oriented conversion path into N-Quads and
then a binary backend path such as COTTAS/Parquet. Current Factoidal can query
COTTAS/Parquet via `--data-cottas` using native extracted code. Artifact
production may still rely on a producer such as `pycottas`; that producer is
not part of the query path.

## Factoidal Current Position

Factoidal is currently best understood as a formally grounded RDF/SPARQL
implementation with useful compatibility coverage, not yet as a competitive RDF
store.

Local observations:

- Native CLI, HTTP endpoint, npm wrapper, JS bundle, Wasm smoke path, and W3C
  runner all execute real RDF/SPARQL work.
- Selected conformance slices are strong: `bind`, `property-path`, `subquery`,
  `rdf-mt`, and `rdf-n-triples` are mostly or fully passing in local checks.
- COTTAS/Parquet query-time reading is native. A query still works with
  `FACTOIDAL_COTTAS_BRIDGE=/definitely/missing` and
  `PYCOTTAS_PYTHON=/definitely/missing`.
- Current COTTAS performance is not yet good. On the committed 5-row sample,
  N-Quads query startup was around milliseconds, while the COTTAS/Parquet path
  was around nine seconds. This reflects the current direct-Parquet probe and
  value reconstruction path, not a page-aware indexed storage engine.

The backend roadmap already states the right caution: do not claim COTTAS
speedups until benchmarks on realistic datasets exist and direct-Parquet scans
are implemented.

## Comparable Systems

### Apache Jena / Fuseki / TDB2

Jena is the open-source baseline role model for broad SPARQL compatibility and
developer ergonomics. Fuseki documents support for the SPARQL 1.1 family:
Query, Update, Protocol, Graph Store HTTP Protocol, Service Description, and
standard result formats. TDB2 is Jena's disk-backed single-machine store and is
described as high performance, with bulk-loading workflows for very large
datasets.

Role-model lessons:

- Treat parsing, loading, storage, query planning, and protocol serving as
  separate workflows.
- Make bulk loading explicit and documented.
- Provide query tooling that can run directly against a persisted store.
- Expose explain/planning/statistics tooling for performance debugging.

### RDF4J

RDF4J is a mature Java framework and store API with SPARQL 1.1 Query and Update
support, broad RDF serialization support, and multiple storage backends. Its
Native Store is positioned for medium-sized datasets, documented around the
order of 100 million triples.

Role-model lessons:

- Keep an embedded API and server/repository model cleanly separated.
- Make storage backends pluggable without changing the query API.
- Be explicit about scale ranges for memory and native stores.

### GraphDB

GraphDB is a commercial RDF database with documented SPARQL 1.1 Protocol,
Query, Update, Federation, and Graph Store HTTP support. It is a role model for
enterprise operational features: repository management, inference, federation,
monitoring, and documentation of deviations from SPARQL tests.

Role-model lessons:

- Publish compliance details and known deviations.
- Treat inference and query performance as a first-class product surface.
- Document behavior around named graphs, federation, and update semantics.

### Stardog

Stardog is a commercial knowledge graph platform with SPARQL 1.1 support,
reasoning, federation, HTTP APIs, and query tooling. It is a role model for
operational query diagnostics and integrated reasoning.

Role-model lessons:

- Provide query explain and execution diagnostics.
- Integrate reasoning without hiding the performance cost.
- Make protocol and CLI behavior consistent.

### Virtuoso

Virtuoso is a long-running multi-model system with RDF quad storage, SPARQL
protocol support, bulk loading, SQL-backed execution machinery, and historically
strong performance on DBpedia-scale deployments. It is a role model for
storage-engine pragmatism and index-oriented RDF execution.

Role-model lessons:

- Quad-table storage with tailored indexes can be very effective.
- Bulk loading and statistics matter as much as query evaluation.
- Cost-based planning and compact indexes are central for large data.

### Oxigraph

Oxigraph is a Rust graph database implementing SPARQL 1.1 Query, Update, and
Federated Query with RDF parsing/serialization support. Its own materials note
that query evaluation has not historically been the most optimized part.

Role-model lessons:

- A modern, safe implementation can be useful even before it reaches mature
  database performance.
- Be clear about spec differences and numeric/literal representation choices.

### QLever

QLever is an RDF/SPARQL system focused on very large datasets. Its documentation
positions it for efficient loading and querying of datasets with hundreds of
billions of triples on a single commodity machine or server.

Role-model lessons:

- For very large RDF, query planning and specialized indexes dominate.
- Benchmark-oriented documentation is valuable.
- Public endpoints and reproducible benchmark setups help establish credibility.

### Other Relevant Systems

Other useful references include Corese, dotNetRDF, rdflib, AllegroGraph, and
Rasqal. They are useful for compatibility behavior and API design, but the main
performance role models for Factoidal are Jena/TDB2, RDF4J Native Store,
GraphDB, Stardog, Virtuoso, Oxigraph, and QLever.

## Performance Expectations

The realistic performance comparison is not "Factoidal vs SPARQL engines" yet.
It is staged:

1. Correctness parity: Can Factoidal answer the same queries as plain N-Quads
   and mature engines on the same data?
2. Load path: Can we turn local RDF into a durable binary store without the
   Factoidal Turtle parser becoming the bottleneck?
3. Query path: Can `--data-cottas` avoid full reconstruction and instead scan
   or seek relevant Parquet pages/columns?
4. Planning: Can the evaluator exploit predicate presence, graph candidates,
   and cardinality estimates?
5. Benchmarking: Can we compare against Jena, RDF4J, Oxigraph, QLever, or
   Virtuoso on the same KGX queries and data?

For `tmp/wikidata-lifesci-kgx`, the first practical step is to convert Turtle
to a line-oriented form with a mature parser (`riot` or `rapper`), materialize
COTTAS/Parquet, then run result-parity and timing queries through
`factoidal --data-cottas`.

## Open Questions

- Do we want one COTTAS dataset for the whole KGX corpus, or one named graph per
  source file?
- Which queries define "useful" for this KGX corpus: simple lookups, class
  summaries, joins across biological entity types, path queries, aggregates?
- Should benchmark comparison target embedded tools first (`tdb2.tdbquery`,
  `oxigraph`, `qlever`) before standing up servers?
- What is the expected import boundary: only already-line-oriented RDF, or a
  supported external parser pipeline for Turtle/RDFXML/TriG?
- What is the target COTTAS query path: fully resident reconstructed cache,
  page-aware scan, mmap-backed scan, or column/statistics-guided lookup?
