# Packed IBK2 selective reader

## Purpose

The persistent SPARQL path must be able to scan selected IBK2 predicate
segments without copying every opened block into a `List UInt8`.  Such copies
make range-capable local-file, `bytea`, object-store and future TiKV hosts pay
for data the plan deliberately avoided reading.

## Landed change

`formal/lean4/L4Factoidal/Storage/IndexedBlockWireV2.lean` now has a bounded
private `Cursor` over `ByteArray`.  The selective range-reader path uses it
for:

- the fixed IBK2 prefix;
- dictionary terms;
- the fixed-width predicate directory; and
- selected predicate segment rows, including prefix scans for `LIMIT`.

Only one variable-width RDF string is extracted at a time for UTF-8 decoding.
The reader no longer converts a complete dictionary, directory, or selected
segment to a `List UInt8` in those paths.

The existing list-based full decoder remains the checked artifact-admission
implementation.  It is intentionally unchanged in this increment: its CRC
and whole-block compatibility behavior need a separate cursor/CRC refactor
with equivalent regression and proof work.  This is therefore a hot-path
memory/copy reduction, not a claim that every IBK2 decode is already
zero-copy.

## Verification

On 2026-08-31:

```text
lake build L4Factoidal.Storage.IndexedBlockWireV2
bash tools/blockengine-shard-selective-smoke.sh
```

both passed.  The smoke test executes parsed SPARQL over a two-shard,
Merkle-verified store.  Its prefix-limited predicate query opened one shard,
made three range requests, fetched one 579-byte verified chunk, and returned
the expected two bindings.

## Remaining scale work

The `scanPredicateDecoded` and complete `decode` compatibility paths still
use list conversion, as does whole-artifact CRC checking.  More importantly,
the streaming publisher currently commits per-input-chunk predicate blocks;
YAGO-scale ingestion needs externally mergeable/global predicate coalescing,
statistics and measured multi-block joins.  This change makes the selected
range-reader suitable as the lower-level basis for that work; it does not by
itself establish YAGO throughput.
