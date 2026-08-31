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

The direct `gene.ttl` exercise has now published all 888,949 triples. Since
the packer flushes bounded input batches, this yielded 13 artifacts and split
the 759,263 P684 triples across five IBK3 artifacts. This is an intentional
multi-entry SBM2 shape, not duplicate data: its total manifest row count is
the source triple count.

`l4block-id-v3-merkle-scan` currently demonstrates one manifest entry at a
time, so its ten-row P684 result is a valid bounded read of the first matching
artifact, not yet an all-five-artifact SPARQL scan. The next host increment is
manifest-order `selectAll` traversal with a global limit and accumulated I/O
evidence.
