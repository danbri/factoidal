# Epoch-safe Shardborough compaction

## Result

The Lean Shardborough path now prevents the classic immutable-base plus
append-log error: replaying an update that compaction already folded into a
new base.

The current lifecycle is:

```text
immutable IBK2/SBM2 base + DLOG batches
             │ compact eligible batches
             ▼
fresh immutable generation + compacted.epoch + source identity
             │ validate, then atomically point CURRENT at it
             ▼
read base + only later DLOG batches
```

## Defined formats and rules

`CEP1` (`compacted.epoch`) is a versioned, length-delimited, checksummed
companion artifact containing an unsigned 64-bit epoch. Its framing matches
the established F* direction: magic, version, body length, u64 body, and
checksum. An absent marker means a legacy, never-compacted base; a present but
malformed marker is an admission failure, never silently treated as absent.

Readers use `filterBatchesSinceEpoch`: for a base at epoch `n`, only batches
with epoch strictly greater than `n` are replayed. A durable UPDATE writer
consults the active generation's marker and stamps `n + 1` (or `1` for a
legacy base). The initial model therefore gives all writes since one
compaction the same next epoch; ordering within it remains the DLOG sequence.

The compactor first filters already-folded source batches, writes a fresh
immutable collection, and writes the greatest consumed epoch as
`compacted.epoch`. It also writes `compacted.source.sha256`, the SHA-256 of
the exact source manifest plus clean DLOG bytes it observed. Before replacing
`CURRENT`, activation verifies this identity against the active source. Thus a
source append racing compaction causes activation to fail closed and requires a
new compaction; it cannot silently disappear at cutover.

Activation additionally validates every child artifact against its full
SHA-256 commitment and checks its Merkle-admitted ranges. This is an
activation-time check over the actual bytes, not yet a pure theorem that a
manifest's two commitment fields are structurally related.

## Lean assurance and tests

`L4Factoidal/RDF/StoreDeltaMerge.lean` now proves
`mergeOnRead_after_compaction`: applying an old history followed by a newer
suffix has the same membership result as folding the old history into the base
and reading with only the newer overlay. `DeltaLog.replay` and
`replayDeltaBatches` are total, fuel-bounded functions rather than `partial`
definitions.

The verified operational checks are:

- `lake build L4Factoidal.Storage.DeltaLogTests L4Factoidal.RDF.StoreDeltaMerge l4block-shard-pack l4block-shard-activate l4block-delta-log l4block-shard-merkle-query l4block-shard-compact`
- `tools/blockengine-shard-compact-smoke.sh`: compact, activate, and then
  append/query an epoch-2 update.
- `tools/blockengine-shard-activation-race-smoke.sh`: append after the
  compactor snapshot and confirm activation refuses the stale candidate.
- Existing parsed-update and two-writer DLOG smoke scripts still pass.

## Deliberate boundary

This is a safe single-host publication protocol, not a distributed transaction
or lease system. It detects source drift at activation. Coordinated compaction
and multiple writers across hosts will need an explicit lease/CAS policy when
PostgreSQL, TiKV, or distributed Shardborough workers become authoritative.
