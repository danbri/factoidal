/- Validate a fresh immutable generation, then atomically make it the active
   child of a Shardborough collection root. -/
import Harness.GenerationPointer
import Harness.ShardMerkleMaterialize
import Harness.IndexedBlockV3Materialize
import Harness.PosixRangeIO
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.ChunkedArtifact

namespace Harness.ShardActivate

open Harness.GenerationPointer
open Harness.ShardMerkleMaterialize
open L4Factoidal.Crypto
open L4Factoidal.Storage
open L4Factoidal.Storage.ShardManifest
open Harness.PosixRangeIO

private def compactedDefaultLayout : String :=
  "predicate-ibk2-merkle-v2-compacted-default-dlog-v1"

private def ibk3Layout : String :=
  "predicate-ibk3-ptd1-merkle-v0"

private def ibk3Sri1Layout : String :=
  "predicate-ibk3-ptd1-sri1-merkle-v0"

private def ibk3Sri1Tli1Layout : String :=
  "predicate-ibk3-ptd1-sri1-tli1-merkle-v0"

private def compactedIbk3Layout : String :=
  "predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1"

private def compactedIbk3Sri1Layout : String :=
  "predicate-ibk3-ptd1-sri1-merkle-v0-compacted-default-dlog-v1"

private def compactedIbk3Sri1Tli1Layout : String :=
  "predicate-ibk3-ptd1-sri1-tli1-merkle-v0-compacted-default-dlog-v1"

private def isIbk3Layout (layout : String) : Bool :=
  layout == ibk3Layout || layout == ibk3Sri1Layout || layout == compactedIbk3Layout ||
    layout == compactedIbk3Sri1Layout || layout == ibk3Sri1Tli1Layout ||
    layout == compactedIbk3Sri1Tli1Layout

private def isCompactedLayout (layout : String) : Bool :=
  layout == compactedDefaultLayout || layout == compactedIbk3Layout || layout == compactedIbk3Sri1Layout ||
    layout == compactedIbk3Sri1Tli1Layout

private def readManifest (directory : System.FilePath) : IO ByteArray := do
  let sbm2 := directory / "manifest.sbm2"
  try IO.FS.readBinFile sbm2
  catch _ => IO.FS.readBinFile (directory / "manifest.sbm1")

/-- The compactor commits the exact source manifest and clean DLOG bytes it
    observed. Recomputing this identity at activation turns a concurrent
    source append into an admission failure, rather than activating a base
    which silently omits that append. -/
private def sourceIdentity? (directory : System.FilePath) : IO ByteArray := do
  let manifest ← readManifest directory
  let dlog := directory / "deltas.dlog"
  let delta ← try
    let bytes ← IO.FS.readBinFile dlog
    match parseLog bytes.toList with
    | some (batches, []) =>
        if validBatchHistory batches then pure bytes
        else throw <| IO.userError "source DLOG batch sequence or epoch order is invalid"
    | _ => throw <| IO.userError "source DLOG is malformed or has an uncommitted suffix"
  catch e =>
    if (← dlog.pathExists) then throw e else pure ByteArray.empty
  pure <| sha256 (manifest ++ delta)

/-- A compacted candidate is only valid for the exact source snapshot it was
    built from. This is deliberately checked before `CURRENT` is replaced;
    retrying compaction is the safe response to a source-side write race. -/
private def sourceStillCurrent (root candidate : System.FilePath) (manifest : Manifest) : IO Bool := do
  if !isCompactedLayout manifest.layout then pure true else
  try
    let expected ← IO.FS.readBinFile (candidate / "compacted.source.sha256")
    if expected.size != 32 || expected != manifest.sourceIdentity then pure false else
    let source ← resolveStoreDirectory root
    pure (expected == (← sourceIdentity? source))
  catch _ => pure false

/-- Activation is intentionally stricter than a selective query: before a
    generation becomes globally visible, every child must satisfy both
    independently recorded commitments over the same observed bytes. The
    later range scan checks the Merkle roots; this pass checks full SHA-256.
    Thus a hand-crafted manifest whose digest and root describe different
    artifacts is rejected at activation rather than deferred to a query path. -/
private def verifyFullArtifact (directory : System.FilePath) (artifact : ArtifactRef) : IO Bool := do
  if !safeLeafKey artifact.key then pure false else
  try
    let bytes ← IO.FS.readBinFile (directory / artifact.key.value)
    match artifact.chunked with
    | none => pure false
    | some chunks =>
        let leafBytes ← IO.FS.readBinFile ((directory / artifact.key.value).toString ++ ".merkle")
        let rebuilt := L4Factoidal.Storage.ChunkedArtifact.chunksOf chunks.chunkBytes bytes |>
          List.map L4Factoidal.Storage.BlockMerkle.leaf
        match leaves? chunks.chunkCount leafBytes with
        | none => pure false
        | some leaves =>
            pure <| bytes.size == artifact.bytes && BlockArtifact.verify artifact.sha256 bytes &&
              leaves == rebuilt && L4Factoidal.Storage.BlockMerkle.root leaves == chunks.root &&
              L4Factoidal.Storage.ChunkedArtifact.fromChunks? chunks.chunkBytes
                (L4Factoidal.Storage.ChunkedArtifact.chunksOf chunks.chunkBytes bytes) == some chunks
  catch _ => pure false

private def verifyFullEntries (directory : System.FilePath) : List Entry → IO Bool
  | [] => pure true
  | entry :: rest => do
      if !(← verifyFullArtifact directory entry.artifact) then pure false
      else
        match entry.subjectIndex with
        | none => verifyFullEntries directory rest
        | some index =>
            if !(← verifyFullArtifact directory index) then pure false
            else match entry.termIndex with
              | none => verifyFullEntries directory rest
              | some term =>
                  if !(← verifyFullArtifact directory term) then pure false
                  else verifyFullEntries directory rest

/-- TLI1 is a physical identity bridge, not advisory planner metadata: it is
   admissible only when its framing/checksum decode and its target digest binds
   it to the exact IBK3 artifact in the same manifest entry. -/
private def verifyTermIndexes (directory : System.FilePath) : List Entry → IO Bool
  | [] => pure true
  | entry :: rest => do
      match entry.termIndex with
      | none => verifyTermIndexes directory rest
      | some index =>
          if !safeLeafKey index.key then pure false else
          try
            let bytes ← IO.FS.readBinFile (directory / index.key.value)
            match L4Factoidal.Storage.TermLocalIndexWire.decode? bytes with
            | some decoded =>
                if decoded.targetIBKSha256 == entry.artifact.sha256 then
                  verifyTermIndexes directory rest
                else pure false
            | none => pure false
          catch _ => pure false

/-- SBM3's subject index is part of the generation, not optional query
    advice.  Before publishing a generation verify its Merkle admission,
    SRI1 framing/checksum, and agreement with the committed IBK3 row count. -/
private def verifySubjectIndexes (directory : System.FilePath) : List Entry → IO Bool
  | [] => pure true
  | entry :: rest => do
      match entry.subjectIndex with
      | none => verifySubjectIndexes directory rest
      | some _ =>
          try
            match ← Harness.IndexedBlockV3Materialize.subjectPostings? directory entry with
            | some _ => verifySubjectIndexes directory rest
            | none => pure false
          catch _ => pure false

/-- Validate the selected physical layout after full-file SHA-256 admission.
    IBK2 uses its existing all-entry materializer; IBK3 uses the paged reader,
    which rechecks every selected byte range against the committed Merkle
    leaves while decoding the same entries. -/
private def verifyReadableEntries (directory : System.FilePath) (manifest : Manifest) : IO (Option Nat) := do
  if isIbk3Layout manifest.layout then
    match ← Harness.IndexedBlockV3Materialize.materializeEntries directory manifest.entries with
    | none => pure none
    | some (_, counters) => pure (some counters.requestedBytes)
  else
    match ← scanEntries directory manifest.entries with
    | none => pure none
    | some (_, verifiedBytes) => pure (some verifiedBytes)

private def activate (rootText generation : String) : IO UInt32 := do
  try
    if !safeGenerationName generation then
      throw <| IO.userError "generation must be one safe child-directory name"
    let root := System.FilePath.mk rootText
    let candidate := root / generation
    let manifestBytes ← readManifest candidate
    match decode? manifestBytes with
    | none => throw <| IO.userError "candidate manifest is malformed or unsupported"
    | some manifest =>
        if !rangeCommitted manifest then
          throw <| IO.userError "candidate manifest has no Merkle range commitment"
        if !(← sourceStillCurrent root candidate manifest) then
          throw <| IO.userError "candidate source changed since compaction; compact again before activation"
        if !(← verifyFullEntries candidate manifest.entries) then
          throw <| IO.userError "candidate child artifact fails its declared SHA-256 commitment"
        if !(← verifySubjectIndexes candidate manifest.entries) then
          throw <| IO.userError "candidate subject-index sidecar is missing, changed, or malformed"
        if !(← verifyTermIndexes candidate manifest.entries) then
          throw <| IO.userError "candidate term-index sidecar is missing, changed, malformed, or bound to another block"
        match ← verifyReadableEntries candidate manifest with
        | none => throw <| IO.userError "candidate child artifact is missing, changed, or malformed"
        | some verifiedBytes =>
            if ← activateGeneration root generation then
              IO.println s!"l4block-shard-activate root={root} generation={generation} verified-logical-bytes={verifiedBytes} pointer=CURRENT"
              pure 0
            else throw <| IO.userError "could not atomically replace CURRENT"
  catch e => IO.eprintln s!"l4block-shard-activate failure: {e}"; pure 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [root, generation] => activate root generation
  | _ => do
      IO.eprintln "usage: l4block-shard-activate COLLECTION-ROOT GENERATION-NAME"
      pure 2

end Harness.ShardActivate

def main (args : List String) : IO UInt32 := Harness.ShardActivate.main args
