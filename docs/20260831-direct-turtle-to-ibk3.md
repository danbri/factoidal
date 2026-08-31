# Direct streaming Turtle to IBK3 publication

`l4block-shard-pack` now retains its existing IBK2 default and accepts an
explicit `ibk3` format argument:

```text
l4block-shard-pack INPUT.ttl OUTPUT-DIR ibk3
```

The existing two-pass UTF-8/Turtle fold remains responsible for source digest
stability and generated blank-node naming. Complete decoded batches are still
partitioned by predicate and published independently, but their artifacts are
now direct IBK3/PTD1 bytes with 64 KiB Merkle sidecars and an SBM2 manifest
whose layout is `predicate-ibk3-ptd1-merkle-v0`. No SPARQL UPDATE path is
involved in loading: this is a bulk immutable-artifact publisher.

The first direct exercise used `binding_site.ttl` (368 triples): it published
two IBK3 artifacts (78 `wdt:P31` rows and 290 `wdt:P361` rows). The native
Merkle/paged scanner returned ten rows from each artifact, confirming that the
direct publisher's output—not only the IBK2-to-IBK3 migration tool—is usable
by the range host.

The next ingestion benchmark remains the substantially larger `gene.ttl`
corpus, using this direct path rather than the migration shortcut.
