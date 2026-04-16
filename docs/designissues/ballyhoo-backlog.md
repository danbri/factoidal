# Ballyhoo Backlog

Ballyhoo is the experimental parser / I/O / storage track.

It does **not** replace the current more compliant parser stack yet. Its role is
to explore faster ingestion, binary/on-disk paths, corpus organization, and
streaming interfaces without forcing everything through the current text-parser
architecture.

These tasks are intentionally tracked in local `.md` files rather than GitHub
issues for now.

## Current Ballyhoo scope

- streaming/chunk-oriented parsing experiments
- fast ingestion paths for large RDF inputs
- on-disk corpus organization
- binary artifact consumption, especially HDT-like formats
- bridge tooling for format conversion during testing

## Immediate tasks

1. Keep `Parser.Ballyhoo.fst` separate and clearly marked experimental.
2. Add a Ballyhoo-specific benchmark path so its timings are measured directly,
   instead of inferring performance through the main parser stack.
3. Add a small CLI or test harness for Ballyhoo event-counting and dataset
   construction on line-oriented RDF inputs.
4. Measure Ballyhoo on:
   - small W3C N-Quads samples
   - Berlin converted to `.nt`
   - large N-Quads slices

## Corpus / TOC tasks

1. Define a TOC vocabulary for corpus chunks, source files, generated artifacts,
   graph IRIs, and provenance.
2. Treat the TOC as just another corpus chunk under `Corpus/toc/`.
3. Standardize the initial filesystem layout:

```text
Corpus/
  toc/
  berlin-dbpedia-page/
    v1/
      data.hdt
```

4. Define recognized version-directory conventions such as `v1/`, `v2/`, etc.
5. Decide how non-versioned corpora are represented.
6. Record graph IRIs and artifact paths in the TOC graph.

## HDT / binary ingestion tasks

1. Evaluate a binary ingestion path based on HDT or related formats.
2. Keep in mind that standard HDT is graph-oriented, not dataset-oriented.
3. For N-Quads corpora, consider:
   - partition by graph IRI
   - emit one HDT per logical graph
   - record the mapping in the TOC graph
4. Create a `Parser.BallyhooHDT.fst` design note and module skeleton.
5. Investigate which HDT metadata and structural checks are suitable for F*
   binary parsing techniques.
6. Tie HDT work to a SPARQL storage backend rather than treating HDT as only a
   parser/import concern.
   See `docs/designissues/sparql-store-backend.md`.

## SPARQL storage tasks

1. Stop assuming that SPARQL evaluation always runs over `list triple`.
2. Introduce a storage/query boundary under `SPARQL11.Algebra`.
3. Keep the algebra in F*, but let extracted backends answer indexed
   triple-pattern lookups.
4. Support both:
   - persisted graph stores such as HDT-backed corpus chunks
   - ephemeral in-memory indexed graph stores built from parsed RDF
5. Rework named-graph access around manifest/TOC metadata, not quad-native HDT
   assumptions.

## Parallel ingestion tasks

1. Use N-Quads as the primary large-ingest format for parallel parsing.
2. Split large N-Quads files by byte range, then adjust chunk boundaries to
   newline boundaries.
3. Confirm and document the key property: N-Quads lines can be parsed
   independently once line boundaries are respected.
4. Build a sharding utility that can:
   - split N-Quads safely
   - route lines by graph IRI
   - emit line-oriented per-graph files for later HDT generation

## Bridge-tooling tasks

1. Keep `tools/rdf_convert.py` as the standard local RDF format conversion tool.
2. Add utilities around it for corpus import workflows.
3. Benchmark and document `rdflib`-based conversion on representative files.
4. Consider temporary external-tool workflows acceptable for corpus preparation,
   while keeping parser logic in F*.

## Validation tasks

1. Run parser-quality checks against temporary bridge tooling such as `rdflib`
   so we know how much to trust conversions used for benchmarking or corpus
   preparation.
2. Separate these results from Factoidal’s own W3C conformance numbers.
3. Record known bridge-tool limitations locally in docs.

## Open architectural questions

1. How much of corpus metadata should be RDF immediately, versus bootstrap text
   files that later generate RDF?
2. Whether the TOC should itself be stored as HDT eventually.
3. Whether dataset-preserving persistence should use HDT extensions, per-graph
   HDTs, or another format entirely.
4. What the clean API boundary should be between:
   - corpus lookup
   - artifact loading
   - RDF graph/dataset construction
   - SPARQL execution
