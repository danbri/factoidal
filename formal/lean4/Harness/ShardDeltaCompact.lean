/-
Conservative default-graph compaction for a Shardborough collection.

The source path is admitted through the same Merkle-verified IBK2 reader as
queries.  A clean DLOG is folded with the existing Lean merge semantics, then
the reusable Lean block publisher writes a *new* immutable SBM2 collection.
There is intentionally no in-place replacement here: publication selection,
old-generation retirement, directory fsync and epoch-marker rollover belong
to the next activation protocol rather than to a tool that can be safely run
against a live source directory.
-/
import Harness.ShardPublish
import Harness.ShardMerkleMaterialize
import Harness.IndexedBlockV3Materialize
import Harness.GenerationPointer
import Harness.CompactedEpoch
import Harness.PosixRangeIO
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardDeltaCompact

open Harness.ShardPublish
open Harness.ShardMerkleMaterialize
open Harness.GenerationPointer
open Harness.CompactedEpoch
open Harness.PosixRangeIO
open L4Factoidal.Crypto
open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.ShardManifest

private def readManifest (directory : System.FilePath) : IO ByteArray := do
  let sbm2 := directory / "manifest.sbm2"
  try IO.FS.readBinFile sbm2
  catch _ => IO.FS.readBinFile (directory / "manifest.sbm1")

private def isDefaultGraphEntry : DeltaEntry → Bool
  | .add _ none | .remove _ none | .clear none => true
  | _ => false

private def ibk3Layout : String :=
  "predicate-ibk3-ptd1-merkle-v0"

private def compactedIbk3Layout : String :=
  "predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1"

private def isIbk3Layout (layout : String) : Bool :=
  layout == ibk3Layout || layout == compactedIbk3Layout

private def defaultGraphOnly (batches : List DeltaBatch) : Bool :=
  batches.all fun batch => batch.ops.all isDefaultGraphEntry

private def readDelta (directory : System.FilePath) : IO (List DeltaBatch × ByteArray) := do
  let path := directory / "deltas.dlog"
  try
    let bytes ← IO.FS.readBinFile path
    match parseLog bytes.toList with
    | some (batches, []) =>
        if validBatchHistory batches then pure (batches, bytes)
        else throw <| IO.userError "DLOG batch sequence or epoch order is invalid"
    | _ => throw <| IO.userError "DLOG is malformed or has an uncommitted suffix"
  catch e =>
    if (← path.pathExists) then throw e else pure ([], ByteArray.empty)

private def compact (source output : String) : IO UInt32 := do
  try
    let sourcePath ← resolveStoreDirectory (System.FilePath.mk source)
    let manifestBytes ← readManifest sourcePath
    match decode? manifestBytes with
    | none => throw <| IO.userError "source manifest is malformed or unsupported"
    | some manifest =>
        if !rangeCommitted manifest then
          throw <| IO.userError "source manifest has no IBK2 Merkle range commitment"
        let baseEpoch ← CompactedEpoch.read? sourcePath
        let (allBatches, deltaBytes) ← readDelta sourcePath
        let batches := filterBatchesSinceEpoch baseEpoch allBatches
        if !defaultGraphOnly batches then
          throw <| IO.userError "this first compactor refuses named-graph or graph-management DLOG entries"
        if isIbk3Layout manifest.layout then
          match ← Harness.IndexedBlockV3Materialize.materializeEntries sourcePath manifest.entries with
          | none => throw <| IO.userError "source IBK3 child artifact is missing, changed, or malformed"
          | some (base, counters) =>
              let delta := foldDeltaBatches batches none
              let compacted := mergeOnRead base delta {}
              let identity := sha256 (manifestBytes ++ deltaBytes)
              let written ← publishTriplesV3 output identity compactedIbk3Layout compacted
              let epoch := foldedThrough baseEpoch batches
              let outputPath := System.FilePath.mk output
              if ← CompactedEpoch.write outputPath epoch then
                if !(← atomicReplaceFileSyncRaw (outputPath / "compacted.source.sha256").toString identity) then
                  throw <| IO.userError "could not persist compaction source identity"
                IO.println s!"l4block-shard-compact source={source} output={output} format=ibk3 base-triples={base.length} delta-batches={batches.length} compacted-triples={written} epoch={epoch} verified-logical-bytes={counters.requestedBytes}"
                pure 0
              else throw <| IO.userError "could not persist compacted.epoch"
        else match ← scanEntries sourcePath manifest.entries with
        | none => throw <| IO.userError "source child artifact is missing, changed, or malformed"
        | some (base, logicalBytes) =>
            let delta := foldDeltaBatches batches none
            let compacted := mergeOnRead base delta {}
            let identity := sha256 (manifestBytes ++ deltaBytes)
            let written ← publishTriples output identity
              "predicate-ibk2-merkle-v2-compacted-default-dlog-v1" compacted
            let epoch := foldedThrough baseEpoch batches
            let outputPath := System.FilePath.mk output
            if ← CompactedEpoch.write outputPath epoch then
              if !(← atomicReplaceFileSyncRaw (outputPath / "compacted.source.sha256").toString identity) then
                throw <| IO.userError "could not persist compaction source identity"
              IO.println s!"l4block-shard-compact source={source} output={output} format=ibk2 base-triples={base.length} delta-batches={batches.length} compacted-triples={written} epoch={epoch} verified-logical-bytes={logicalBytes}"
              pure 0
            else throw <| IO.userError "could not persist compacted.epoch"
  catch e => IO.eprintln s!"l4block-shard-compact failure: {e}"; pure 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [source, output] => compact source output
  | _ => do
      IO.eprintln "usage: l4block-shard-compact SOURCE-SHARD-DIR OUTPUT-FRESH-DIR"
      pure 2

end Harness.ShardDeltaCompact

def main (args : List String) : IO UInt32 := Harness.ShardDeltaCompact.main args
