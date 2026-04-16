# Corpus Pipeline

This note records the first repo-local implementation of the experimental
`N-Quads sharding + TOC + HDT` pipeline.

## Tool

Use:

```bash
python3 tools/corpus_pipeline.py import-line-rdf ...
python3 tools/corpus_pipeline.py shard-line-rdf ...
```

Current supported inputs:

- `--input-format nt`
- `--input-format nq`

The implementation is intentionally line-oriented and aimed at large-ingest
workflows. It does not depend on the current F* text parser stack.

## Sharding

Large `.nt` / `.nq` inputs can be split into line-safe shards with a byte budget:

```bash
python3 tools/corpus_pipeline.py shard-line-rdf \
  --input bigdump.nq \
  --input-format nq \
  --output-dir /tmp/bigdump-shards \
  --max-bytes 134217728
```

This preserves full lines and therefore avoids breaking RDF records or UTF-8
sequences across shards.

The shard command writes:

```text
/tmp/bigdump-shards/
  manifest.tsv
  shard-00000.nq
  shard-00001.nq
  ...
```

## Current behavior

The pipeline:

1. reads a line-oriented RDF file
2. parses one line at a time
3. assigns each triple to a graph IRI
4. writes one corpus chunk per graph under `Corpus/`
5. writes `Corpus/toc/data.ttl`
6. optionally invokes an external HDT builder such as `rdf2hdt`

If no HDT builder is available, it still produces a usable corpus layout with
`data.nt` artifacts and metadata.

## Layout

```text
Corpus/
  toc/
    data.ttl
  some-graph-slug/
    v1/
      data.nt
      source-info.ttl
      data.hdt        # only when external HDT generation succeeds
```

## Example

For N-Triples imported as one logical graph:

```bash
python3 tools/corpus_pipeline.py import-line-rdf \
  --input /tmp/Berlin.nt \
  --input-format nt \
  --dataset-name berlin-dbpedia-page \
  --chunk-name berlin-dbpedia-page \
  --default-graph-iri https://factoidal.example/id/graph/berlin-dbpedia-page
```

For N-Quads:

```bash
python3 tools/corpus_pipeline.py import-line-rdf \
  --input bigdump.nq \
  --input-format nq \
  --dataset-name bigdump
```

## Notes

- This is a bridge pipeline, not a final verified storage layer.
- The long-term direction is still to move binary artifact reading and more
  validation into F*.
- Standard HDT is graph-oriented, so the current approach naturally emits one
  artifact per graph.

## Imagesnippets discovery

`examples/data/third_party/imagesnippets.nq` is a useful stress case because it
appears to contain a very large number of distinct graph IRIs.

Observed locally:

- about `6.6M` lines total
- a `200k`-line sample already showed about `47k` distinct graph IRIs

That means a naive one-graph-per-chunk import can explode into a very large
number of tiny chunk directories. For this kind of dataset, the pipeline needs
an explicit grouping policy before full `Corpus/` import is sensible.

Likely directions:

- graph-per-chunk for curated/smaller corpora
- grouped graph buckets for very high-graph-count corpora
- manifest-level graph summaries before committing to HDT generation

## Subset Blooms

The corpus should support many rolled-up subset summaries, not just per-graph
sidecars.

Examples:

- all named graphs added in `2025`
- all named graphs about `Texas`
- all named graphs matching a curated graph list

These subset Blooms belong naturally under the corpus TOC area or other
predictable subset directories, for example:

```text
Corpus/
  toc/
    blooms/
      added-2025/
      texas/
```

The first implementation uses OR-rolled predicate Bloom filters, but that only
works when the per-graph Bloom sidecars share the same `bit_count` and
`hash_count`. That is why `tools/graph_bloom.py` now supports fixed-size Bloom
generation.
