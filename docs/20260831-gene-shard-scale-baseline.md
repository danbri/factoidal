# Gene shard scale baseline

## Corpus and command

The bounded Turtle publisher was run on the local Schema.org-oriented
Wikidata life-science export:

```text
examples/wikidata/subsets/lifesci-kgx/data/gene.ttl
17 MiB source, 433,832 text lines
```

with:

```text
l4block-shard-pack gene.ttl STORE
```

The committed SBM2 store contains 888,949 triples in 13 immutable IBK2
artifacts (24,921,609 IBK2 bytes before Merkle sidecars).  The reproducible
native gate recorded 72 seconds (about 12.4k triples/s) for this pack.  This
is the largest current direct run of the streaming shard publisher.

## What it establishes

The source was published without creating one all-source RDF graph.  The
manifest is written only after its second streaming pass confirms the source
SHA-256.  The resulting store supports ordinary parsed constant-predicate
SPARQL and Merkle-verified range reads.

For example, a ten-row `P682` query opened one 500-byte artifact and returned
four bindings in approximately 0.01 seconds.

## Important measured limit

The frequent `P684` predicate spans five input-publication artifacts:

```text
36,056 + 180,667 + 251,148 + 256,698 + 34,694 rows
```

SBM2 correctly permits and selects all five artifacts.  `--explain-analyze`
scanned all 759,263 rows in approximately 2.13 seconds on this laptop.

The ordinary `LIMIT 10` fast path returned ten rows in 0.31 seconds, but read
1,548,846 logical bytes / 1,572,864 fetched Merkle-chunk bytes.  It only
needed the first predicate artifact, but that artifact's shared dictionary is
large and must presently be loaded before its rows can be decoded.

This confirms two design points:

1. several bounded immutable blocks per predicate are semantically correct
   and required for streaming publication; a query must select *all* matching
   manifest entries, not one arbitrary entry; and
2. IBK2's per-block shared dictionary is now the dominant small-result cost
   for high-cardinality predicates.  A YAGO-class format needs a separately
   addressable/sharded dictionary (or a compact stable TermId dictionary) so
   a small row-range scan does not need to read megabytes of term material.

The packed cursor landed in the preceding increment removes avoidable
`ByteArray -> List UInt8` copies from this path.  It cannot remove the
semantic need to resolve dictionary IDs; the physical layout must change for
that.

## Next scale increment

The repository already has the relevant landed component:
`L4Factoidal.Storage.PagedTermDictionary` (`PTD1`).  It retains exactly the
same per-block array-index meaning as `IndexedBlock.Block.dict`, but stores a
small directory and 256-term pages.  The diagnostic executable measured the
first ten rows of the first P684 artifact as:

```text
current IBK2 logical read: 1,548,846 bytes
PTD1 directory + needed pages: 12,559 bytes
```

The next increment is therefore to integrate PTD1 into an IBK3-style block
layout with the existing row-segment layout, preserving the IBK2 denotation
and manifest/Merkle admission boundary.  Then benchmark the same `P684 LIMIT
10` query.  This is more useful than downloading a multi-gigabyte YAGO dump
before dictionary-read amplification is fixed.
