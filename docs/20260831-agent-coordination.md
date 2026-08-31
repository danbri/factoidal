# Concurrent-agent handoff protocol

## Purpose

Factoidal is sometimes worked on concurrently by Codex, Claude Code, and
humans against the same checkout. The repository, not a chat transcript, is
the authoritative handoff medium.

## Rules for an active increment

1. Before editing, inspect `git status --short`, the most recent dated
   `docs/YYYYMMDD-*.md` worknotes, and the relevant current source.
2. Record a non-trivial in-progress slice here or in its dedicated dated
   worknote: owner/session, intended invariant, files being edited, and the
   exact verification command.
3. Do not rewrite, reset, stage, or include another agent's unrelated diff.
   Re-read the diff immediately before a commit.
4. Commit only coherent, verified increments; fetch, merge normally, and push
   without force-pushing shared branches.
5. A review finding should name its snapshot commit and current paths. Later
   work may already have repaired it; verify rather than treating it as stale
   or blindly repeating it.

## Live handoff — epoch-safe Shardborough compaction

**Owner:** Codex session, 2026-08-31.

**Invariant:** a generation records the greatest DLOG epoch folded into its
immutable base. Readers replay only later batches; writers stamp a strictly
later epoch. This prevents a compaction from replaying already-folded updates.

**Active files:**

- `formal/lean4/L4Factoidal/Storage/DeltaLog.lean`
- `formal/lean4/L4Factoidal/RDF/StoreDeltaMerge.lean`
- `formal/lean4/Harness/CompactedEpoch.lean`
- `formal/lean4/Harness/{DeltaLogTool,ShardMerkleMaterialize,ShardDeltaCompact,ShardActivate}.lean`
- `formal/lean4/L4Factoidal/Storage/DeltaLogTests.lean`
- `tools/blockengine-shard-compact-smoke.sh`

**Current implementation status:** CEP1 is now a framed u64 companion
artifact matching the F* layout; query replay filters against it; writers use
`baseEpoch + 1`; compaction persists the new threshold; replayers are total;
activation verifies both each artifact's full SHA-256 and its Merkle-admitted
ranges. A kernel-checked `mergeOnRead_after_compaction` theorem now relates a
compacted base plus a newer suffix to the full reference history.

**Verification completed before commit:** focused Lean build; normal
compaction → activation → epoch-2 update smoke; parsed UPDATE smoke;
two-writer DLOG smoke; and a negative source-write race smoke. The latter
proves operationally that a source append after compaction prevents the stale
candidate becoming `CURRENT`.

**Additional activation admission rule:** a compacted candidate carries
`compacted.source.sha256`, the SHA-256 of the source manifest plus clean DLOG
bytes observed by the compactor. Activation recomputes that identity for the
presently active source. A mismatch refuses activation; a fresh compaction is
required. This is a safety gate, not a multi-host writer lease protocol.

**Next handoff:** after this increment is committed, the next independent
correctness priorities are wire-format theorems, disk-backed W3C execution,
and replacing byte-list decoder hot paths. Do not independently alter the
listed files until this increment is committed, unless deliberately taking
over the slice.
