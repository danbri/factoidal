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
torn suffix. The native edge writes the already Lean-validated frame in a
write-all loop and calls file `fsync` before it reports success. A local run
committed two parsed requests (`seq=1`, `seq=2`) and then reported
`committed-batches=2 committed-ops=2 clean-tail=true`.

Concurrent writers use an exclusive advisory lock and a compare-on-file-size
append. The writer first parses the exact clean byte prefix, then the native
edge appends only if that same length still holds under the lock. A competing
writer reloads and retries with the next sequence number. The repeatable
`tools/blockengine-delta-log-race-smoke.sh` test starts two writers from an
empty log and verifies two distinct committed batches.

The tool deliberately refuses `INSERT DATA` blank nodes for now. SPARQL
requires a request-fresh scope; obtaining a collision-free prefix means
consulting the composed base-plus-delta state. The semantic translator already
accepts a supplied renamer, so this is an admission gate at the native edge,
not a changed data model.

## What this does and does not establish

The existing `RDF.StoreDeltaMerge` Lean module has the important semantic
bridge: `mergeOnRead_matches_applyEntries` proves membership equivalence
between base-plus-delta reads and literal application of the same entries.

This work now connects its durable input to the default-graph Shardborough
IBK2 query host. `l4block-shard-merkle-query` reads a clean `deltas.dlog`,
folds it with `foldDeltaBatches`, and passes the selected Merkle-verified base
rows through `mergeOnRead` before invoking the normal Lean SPARQL evaluator.
The repeatable smoke test
`tools/blockengine-shard-delta-smoke.sh` proves that an inserted triple becomes
visible and a base triple deleted through SPARQL Update disappears.

The bounded single-triple-pattern `LIMIT` scan is delta-aware. A tombstoned
base row does not count toward the prefix, so the reader continues until it
has enough surviving base rows; the normal overlay then supplies matching
additions. A `CLEAR` skips base reads entirely. The smoke test deletes the
first base row and verifies that a later base row plus a newly inserted row
still satisfy `LIMIT 2`.

The overlay preserves RDF graph set semantics across the base/delta boundary:
an `INSERT DATA` of a triple already present in the immutable base does not
produce a duplicate query row. `mergeOnRead` now performs the Lean graph's
set-union operation, with a proved membership law and a regression guard.

The first query integration is default graph only. The delta format and update
translator preserve named-graph targets, but this predicate-local triple store
does not yet have named-graph manifests or a named-graph query reader; those
operations need their corresponding graph-aware physical path before they can
be exposed through this executable.

The current native append is a `write → fsync → report success` adapter for
the file contents. Before treating a newly created log or a compaction as
fully crash-durable across a power loss, add directory fsync plus the
temp-file/rename recovery procedure, and a SHA-256 or Merkle commitment for
the resulting log generation. The current frame checksum is intentionally
only a torn-write detector, not tamper evidence.

## Next implementation sequence

1. Allocate SPARQL request-fresh blank-node prefixes from the composed store.
2. Add named-graph manifests and an equivalent named-graph delta overlay.
3. Extend the delta-aware bounded scan beyond this single triple-pattern,
   unordered `LIMIT` fragment.
4. Add a native fsync append/compaction adapter and manifest/epoch update.
5. Compact base plus committed delta into a new immutable, Merkle-committed
   generation; only then retire the old delta sidecar.

This retains the intended architecture: fast immutable sorted blocks for most
reads, a small ordered update log for writes, and deterministic compaction
rather than making every update rewrite the base indexes.

## Fresh-generation compaction

`l4block-shard-compact SOURCE-SHARD-DIR OUTPUT-FRESH-DIR` now performs the
first conservative compaction form. It verifies every source IBK2 range through
the source manifest, requires a clean default-graph-only DLOG, folds it with
the Lean merge definition, and publishes new IBK2/Merkle artifacts plus a new
SBM2 manifest. The new source identity is SHA-256 over the input manifest and
the exact log bytes consumed.

It never rewrites or redirects the source collection. That is deliberate: a
separate activation protocol still needs a directory fsync, an atomic
generation-pointer/rename step, epoch handling for writers that raced the
compaction, and eventual retirement of the old generation. The repeatable
`tools/blockengine-shard-compact-smoke.sh` test proves the new base sees an
inserted triple and no longer sees a deleted base triple without any DLOG.
