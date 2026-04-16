# Graph Bloom Sidecars

This note records the first sidecar-summary path for graph-level pruning.

## Goal

Avoid opening or querying every graph artifact for every SPARQL pattern.

The first summary type is a predicate Bloom filter per graph folder.

## Files

For a graph folder such as:

```text
.../some-graph/v1/
  data.nt
  data.hdt
```

the sidecar generator writes:

```text
.../some-graph/v1/
  graph.bloom.pred.bin
  graph.bloom.pred.json
```

## Current Scope

- predicate-only Bloom filter
- generated from `data.nt`
- safe to regenerate
- intended as a pre-query routing hint

False positives are acceptable.
False negatives are not.

## Tool

Use:

```bash
python3 tools/graph_bloom.py ROOT
```

Example:

```bash
python3 tools/graph_bloom.py /tmp/Corpus3
```

If you want Bloom sidecars that can later be rolled up with bitwise OR, generate
them with a shared fixed bit count:

```bash
python3 tools/graph_bloom.py /tmp/Corpus3 --fixed-bit-count 65536 --overwrite
```

Without shared `bit_count` and `hash_count`, per-graph Bloom files are not
safe to OR together.

## Roll-up Tool

Use:

```bash
python3 tools/graph_bloom_rollup.py ROOT --output-dir OUTDIR ...
```

Example:

```bash
python3 tools/graph_bloom_rollup.py /tmp/Corpus3 \
  --output-dir /tmp/Corpus3/toc/berlin-bundle \
  --graph-iri-regex 'berlin' \
  --label berlin
```

Current selectors:

- `--graph-iri-regex`
- `--path-regex`
- `--metadata-regex`
- `--graph-list`

This is enough to support bundles like:

- all NGs added in `2025`
- all NGs about `Texas`
- all NGs listed by an external selection step

The catch is that those work well only if the relevant metadata is present in
`source-info.ttl` or in an external graph-list file. For richer bundle
selection, the corpus metadata needs to carry more explicit dates, topics, and
other facets.

## Why predicate Bloom first

Predicate constants are extremely common in SPARQL BGPs and `GRAPH ?g` pruning.

If a graph definitely does not contain:

- `foaf:depiction`
- `rdf:type`
- `dbo:country`

then we should be able to skip opening/searching that graph artifact entirely.

## Next likely summaries

- type/object Bloom filter
- subject Bloom filter
- triple count
- distinct term counts
- cheap topical / vocabulary flags
- rolled bundle Blooms under `Corpus/toc/` or other subset directories
