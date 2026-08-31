# IBK2 `gene.ttl` ingest gate — 2026-08-31

## Reproducible bounded observation

The current native reference packer was run once against
`examples/wikidata/subsets/lifesci-kgx/data/gene.ttl` (17 MiB; the checked-in
KGX README records 888,949 triples) with a 20-second external wall-clock cap:

```text
gtimeout -s INT 20 l4block-shard-pack gene.ttl OUTPUT-DIR
```

It consumed 20.00 seconds wall time / 19.85 seconds user CPU, exited with the
expected timeout status `124`, and had emitted zero output artifacts. The run
was synchronous and no packer remained running afterwards.

This is intentionally a **gate**, not a throughput result. It establishes
that the current reference encoder cannot publish a usable partial store while
it is still parsing and retaining the full source/buckets. Recent improvements
remove repeat character-list allocation and expected linear predicate-bucket
lookup, but are not enough to change that architectural boundary.

## Consequence

The next implementation must make a true input/event boundary:

1. incremental UTF-8 decoding and Turtle statement parsing while retaining
   prefix/base/mode/blank-node state;
2. a pre-pass or equivalent bounded method for the collision-safe generated
   blank-node prefix and source commitment;
3. bounded predicate/graph spool partitions and immutable IBK2 publication;
4. publication of the SBM1 manifest only after all artifact and Merkle
   commitments have succeeded.

Splitting merely on newlines is explicitly not an acceptable substitute: valid
Turtle permits multi-line strings, comments, directives, blank-node property
lists and collections.
