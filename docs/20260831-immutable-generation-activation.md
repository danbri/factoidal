# Immutable generation activation for Shardborough stores

## 2026-08-31

The durable SPARQL-update slice can now move from a compacted candidate to an
active generation without rewriting a live collection in place.

## Layout and activation protocol

```text
collection-root/
  CURRENT                 # UTF-8 safe child name, e.g. generation-0002
  generation-0001/        # immutable SBM2 + IBK2 artifacts (+ optional DLOG)
  generation-0002/        # freshly compacted, fully verified artifacts
```

`l4block-shard-activate COLLECTION-ROOT GENERATION-NAME`:

1. accepts only one safe child-directory name (not paths);
2. decodes the candidate SBM1/SBM2 manifest and requires a Merkle range
   commitment;
3. scans every admitted artifact through its manifest commitment;
4. writes a temporary `CURRENT`, syncs its complete bytes, renames it over the
   old pointer, and syncs the parent directory.

A reader given the collection root resolves `CURRENT` before reading the
manifest or DLOG.  A malformed pointer or missing target is an explicit
admission failure; only an absent `CURRENT` retains compatibility with the
existing direct-store layout.

The supported native tools (`l4block-shard-merkle-query`,
`l4block-delta-log`, and `l4block-shard-compact`) all use the same resolver.
This means queries and updates follow the active immutable generation rather
than accidentally operating on the collection root.

## What this establishes

The semantic data remains the canonical IBK2/SBM2 object. `CURRENT` is a tiny
control-plane indirection, not a second data format or an unverified mutable
manifest. A candidate is verified before it becomes visible to new root-based
operations. Existing readers that already opened a prior generation can finish
against that immutable generation, while later root-based readers use the new
one.

This is not yet a distributed commit protocol: PostgreSQL and TiKV adapters,
lease/refcount-based old-generation reclamation, and multi-host activation are
future work. The POSIX implementation covers normal local crash durability of
the pointer replacement, but it cannot make guarantees about a filesystem
which lies about `fsync` or an administrator who changes artifacts after
activation; the per-read Merkle verification continues to detect the latter.

## Verification

`tools/blockengine-shard-compact-smoke.sh` now compacts a base plus DLOG,
activates the compacted child through `CURRENT`, and re-runs parsed SPARQL
against the collection root. It confirms that Carol is found, Alice remains
deleted, and the compacted generation has no DLOG sidecar. Focused Lean builds
cover `l4block-shard-activate`, query, compaction, and delta-log executables.
