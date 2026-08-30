# IBK2 ingest scale gate — 2026-08-30

## Observation

The checked-in Wikidata/KGX life-sciences `gene.ttl` is 17 MB and its
README records 888,949 triples. It is a useful medium-scale local corpus; the
complete checked-in KGX subset is approximately one million triples.

On this machine, the current native `l4block-shard-pack` did not produce an
artifact during a two-minute observation of this input. This is not a
throughput benchmark or a claim that it cannot complete: the process was
intentionally stopped to avoid unattended duplicate local jobs. Its output
directory was still empty because the current packer emits blocks only after
the complete Turtle graph and predicate store have been constructed.

The parser previously accumulated top-level triples as `acc ++ ts`, which is
quadratic for normal one-triple-per-line Turtle. The Lean implementation now
uses a reverse accumulator and reverses once at the terminal boundary,
preserving source order. It also no longer traverses the full remaining
character list twice per statement merely to compute a fuel bound and a
no-progress check: it uses the existing absolute positions and document-level
fuel instead. The Turtle guards and the persistent Merkle-SPARQL smoke pass
with these changes.

A second controlled observation still had no emitted artifact after roughly
1:43. This does not invalidate the repairs; it shows the next bottleneck is
the remaining full-document `String.toList`/character-list parser and
whole-graph construction. It must be addressed with a real incremental parser
state and sink, not a naive newline splitter.

Further inspection found that every prefixed IRI token had also computed the
length of its entire remaining input to fuel its name-body scanner. That
scanner and Turtle whitespace/comment skipping are now structurally recursive;
the normal KGX shape no longer takes a full-tail length just to scan each IRI
or whitespace boundary. As a bounded confirmation, the 9,227-triple
`chromosome.ttl` KGX graph packed into one predicate shard in 2.46 seconds
and produced a 568 KiB SBM1/IBK2/Merkle collection on this macOS host. This is
a local wall-clock observation, not a general performance claim. The
889k-triple `gene.ttl` gate remains open until an incremental reader and
bounded block publication are implemented.

## Required next ingest shape

Do not split Turtle naively on lines: directives, multi-line literals,
collections, blank-node property lists and comments make that unsound. Instead
factor the established Turtle parser into a statement/event sink that retains
the one document's prefix, base IRI, RDF version and blank-node state while
emitting each completed statement's triples.

The initial streaming packer can then:

1. parse a bounded byte/input window while carrying parser state;
2. route emitted triples to predicate (and later graph/permutation) spool
   partitions;
3. sort/build bounded immutable IBK2 blocks per partition;
4. atomically publish block bytes, Merkle leaves and an SBM1 manifest only
   after every artifact has been committed; and
5. retain source identity, parser mode and per-source provenance in the
   manifest/publication record.

This avoids promising that the current in-memory `Graph` parser is a
web-scale loader. The existing one-file predicate-local packer remains a
correctness/reference encoder for fixtures and bounded sources.

## Wikidata → derived named-graph trail

Dan Brickley's proposed useful provenance/dataflow vertical is:

```text
QLever Wikidata CONSTRUCT result
        -> immutable asserted named-graph artifact
        -> local verified re-query / CONSTRUCT
        -> Schema.org, Bioschemas or medical/life-science derived named graph
```

The checked-in `kgx/wikidata/basic/` and `kgx/wikidata/bioschemas/` construct
queries provide the local transformation corpus. The external acquisition
policy is QLever-only for Wikidata queries. A derived graph must identify its
source graph artifact/snapshot, construct query identity, transformation
kernel/version and resulting content commitment; it must never be silently
presented as an asserted Wikidata graph.

This is naturally compatible with the planned dataflow/profile node identity:
the source fetch, local query, transformation and derived block publication
are distinct immutable-artifact operations in one provenance DAG.
