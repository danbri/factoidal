# Durable SPARQL Update slice — 2026-08-31

## What landed

The Lean 4 block-store work now has a usable durable-update foundation in
addition to its immutable IBK2/SBM2 base artifacts.

`L4Factoidal.Storage.DeltaLog` was aligned with the established F* byte
format, rather than retaining an accidental Lean-only variant:

```text
DLE1 entry = magic:u32, version:u32, payload-length:u32, payload, checksum:u32
DLB1 batch = magic:u32, version:u32, body-length:u32, body, checksum:u32
DLOG file  = magic:u32, version:u32, DLB1 batch*
```

The body carries a u64 commit sequence, a u64 base epoch, an operation count,
then independently framed typed operations. A reader accepts a checksum-valid
prefix only and returns the undecoded suffix. This gives the desired recovery
rule for an interrupted append: committed batches replay; the incomplete tail
does not.

The build-time checks now cover:

- mixed typed update operations in one `DLB1` batch;
- batch and full-log encode/decode round trips;
- a valid batch followed by a deliberately truncated batch;
- parser → `INSERT DATA` / `DELETE DATA` → `DeltaBatch` → DLB1 decode.

`SPARQL.UpdateDelta` is the narrow translation boundary. It admits:

- `INSERT DATA`;
- `DELETE DATA`;
- `CLEAR DEFAULT` and `CLEAR GRAPH`;
- `DROP GRAPH`;
- `CREATE GRAPH`.

It refuses, explicitly and without omission, WHERE-dependent `DELETE/INSERT`,
`DELETE WHERE`, `COPY`, `MOVE`, `ADD`, and graph-wide `ALL`/`NAMED` forms.
Those require evaluation against the composed base-plus-delta dataset.

## Runnable tool

The native Lean executable is:

```text
formal/lean4/.lake/build/bin/l4block-delta-log STORE-DIR --update 'INSERT DATA { ... }'
formal/lean4/.lake/build/bin/l4block-delta-log STORE-DIR --inspect
```

It uses the Lean SPARQL Update parser and Lean serializer, writes a `DLOG`
sidecar named `deltas.dlog`, and refuses to append if the existing file has a
torn suffix. A local run committed two parsed requests (`seq=1`, `seq=2`) and
then reported `committed-batches=2 committed-ops=2 clean-tail=true`.

The tool deliberately refuses `INSERT DATA` blank nodes for now. SPARQL
requires a request-fresh scope; obtaining a collision-free prefix means
consulting the composed base-plus-delta state. The semantic translator already
accepts a supplied renamer, so this is an admission gate at the native edge,
not a changed data model.

## What this does and does not establish

The existing `RDF.StoreDeltaMerge` Lean module has the important semantic
bridge: `mergeOnRead_matches_applyEntries` proves membership equivalence
between base-plus-delta reads and literal application of the same entries.

This work makes its durable input real. It does **not** yet connect the
Shardborough IBK2 query host to `deltas.dlog`; so an appended update is not
yet visible through `l4block-shard-merkle-query`. That is the next end-to-end
implementation task.

The native append utility currently relies on Lean's file append primitive;
it is not yet the assurance-grade `write → fsync → report success` host
adapter. Before treating a log as crash-durable across a power loss, add that
small POSIX adapter, a directory-fsync/rename recovery procedure, and a
SHA-256 or Merkle commitment for the resulting log generation. The current
frame checksum is intentionally only a torn-write detector, not tamper
evidence.

## Next implementation sequence

1. Read a clean `deltas.dlog` beside an SBM2 collection and fold batches by
   graph with `foldDeltaBatches`.
2. Wrap selected IBK2 base scans with `mergeOnRead`, then prove/guard that
   parsed SELECT observes an INSERT and DELETE.
3. Allocate SPARQL request-fresh blank-node prefixes from the composed store.
4. Add a native fsync append/compaction adapter and manifest/epoch update.
5. Compact base plus committed delta into a new immutable, Merkle-committed
   generation; only then retire the old delta sidecar.

This retains the intended architecture: fast immutable sorted blocks for most
reads, a small ordered update log for writes, and deterministic compaction
rather than making every update rewrite the base indexes.
