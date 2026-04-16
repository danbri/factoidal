# Corpus Layout

This note records the current experimental direction for organizing on-disk RDF
corpora and generated binary artifacts.

## Current decision

Use a single top-level `Corpus/` directory for now.

Do **not** introduce a higher-level multi-corpus abstraction yet. If that is
needed later, it can be added explicitly rather than guessed in advance.

## Initial layout

```text
Corpus/
  toc/
  berlin-dbpedia-page/
    v1/
      data.hdt
```

The TOC is itself just another chunk of corpus, represented under `Corpus/toc/`
rather than as a special top-level file.

## Naming and versioning

- Corpus chunk directories use stable readable names such as
  `berlin-dbpedia-page/`.
- Version directories use recognized names such as `v1/`, `v2/`, etc.
- Versioning is optional; some corpus chunks may later be represented without
  a version subdirectory if that proves simpler.
- Additional versioning mechanisms may be added later, but `vN/` is the first
  convention to support.

## TOC requirements

The TOC should eventually assign IRIs to:

- corpus chunks
- logical graphs / datasets
- artifacts
- source snapshots

The TOC should record at least:

- corpus-chunk IRI
- source format
- source path
- artifact format
- artifact path
- graph IRI
- provenance notes such as generator and timestamp

## Likely evolution

Near term:

- the TOC may be simple RDF files in `Corpus/toc/`
- HDT artifacts may sit beside source and metadata files under chunk/version
  directories

Later:

- the TOC itself may become an HDT-backed artifact
- per-graph or per-version conventions may tighten
- dataset-aware storage conventions may be added once quad persistence is
  better understood

## Non-goals for now

- no attempt yet to design a full multi-corpus federation layout
- no commitment yet to one permanent versioning model
- no assumption that one binary artifact format will handle every graph/dataset
  use case
