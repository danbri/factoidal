/- Validate a fresh immutable generation, then atomically make it the active
   child of a Shardborough collection root. -/
import Harness.GenerationPointer
import Harness.ShardMerkleMaterialize
import Harness.IndexedBlockV3Materialize
import Harness.PosixRangeIO
import Harness.NativeHasher
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.Storage.TermLocalIndexWire
import L4Factoidal.Storage.TermLocalIndex
import L4Factoidal.Storage.IndexedBlockWireV3
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
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

private def ibk3Sri2Tli1Layout : String :=
  "predicate-ibk3-ptd1-sri2-tli1-merkle-v0"

private def ibk3Sri2Tli1Oli2Layout : String :=
  "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0"

private def compactedIbk3Layout : String :=
  "predicate-ibk3-ptd1-merkle-v0-compacted-default-dlog-v1"

private def compactedIbk3Sri1Layout : String :=
  "predicate-ibk3-ptd1-sri1-merkle-v0-compacted-default-dlog-v1"

private def compactedIbk3Sri1Tli1Layout : String :=
  "predicate-ibk3-ptd1-sri1-tli1-merkle-v0-compacted-default-dlog-v1"

private def compactedIbk3Sri2Tli1Layout : String :=
  "predicate-ibk3-ptd1-sri2-tli1-merkle-v0-compacted-default-dlog-v1"

private def compactedIbk3Sri2Tli1Oli2Layout : String :=
  "predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0-compacted-default-dlog-v1"

private def isIbk3Layout (layout : String) : Bool :=
  layout == ibk3Layout || layout == ibk3Sri1Layout || layout == compactedIbk3Layout ||
    layout == compactedIbk3Sri1Layout || layout == ibk3Sri1Tli1Layout ||
    layout == compactedIbk3Sri1Tli1Layout || layout == ibk3Sri2Tli1Layout ||
    layout == compactedIbk3Sri2Tli1Layout || layout == ibk3Sri2Tli1Oli2Layout ||
    layout == compactedIbk3Sri2Tli1Oli2Layout

private def isCompactedLayout (layout : String) : Bool :=
  layout == compactedDefaultLayout || layout == compactedIbk3Layout || layout == compactedIbk3Sri1Layout ||
    layout == compactedIbk3Sri1Tli1Layout || layout == compactedIbk3Sri2Tli1Layout ||
    layout == compactedIbk3Sri2Tli1Oli2Layout

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
  pure <| nativeSha256 (manifest ++ delta)

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
    artifacts is rejected at activation rather than deferred to a query path.

    The hashing itself uses `Harness.nativeHasher` (HACL* C) instead of the
    pure Lean specification hash. Activation rebuilds every leaf and every
    root of the whole generation, so this is the dominant cost; the two
    hashers compute the same function (measured by `lake exe l4vc-probe`),
    so no committed byte and no acceptance decision changes. -/
private def verifyFullArtifact (directory : System.FilePath) (artifact : ArtifactRef) : IO Bool := do
  if !safeLeafKey artifact.key then pure false else
  try
    let bytes ← IO.FS.readBinFile (directory / artifact.key.value)
    match artifact.chunked with
    | none => pure false
    | some chunks =>
        let leafBytes ← IO.FS.readBinFile ((directory / artifact.key.value).toString ++ ".merkle")
        let rebuilt := L4Factoidal.Storage.ChunkedArtifact.chunksOf chunks.chunkBytes bytes |>
          List.map (L4Factoidal.Storage.BlockMerkle.leafWith nativeHasher)
        match leaves? chunks.chunkCount leafBytes with
        | none => pure false
        | some leaves =>
            pure <| bytes.size == artifact.bytes &&
              BlockArtifact.verifyWith nativeHasher artifact.sha256 bytes &&
              leaves == rebuilt &&
              L4Factoidal.Storage.BlockMerkle.rootWith nativeHasher leaves == chunks.root &&
              L4Factoidal.Storage.ChunkedArtifact.fromChunksWith? nativeHasher chunks.chunkBytes
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
                  else match entry.objectIndex with
                    | none => verifyFullEntries directory rest
                    | some object =>
                        if !(← verifyFullArtifact directory object) then pure false
                        else verifyFullEntries directory rest

private def subjectIndexFailure : String :=
  "candidate subject-index sidecar is missing, changed, or malformed"
private def termIndexFailure : String :=
  "candidate term-index sidecar is missing, changed, malformed, or bound to another block"
private def objectIndexFailure : String :=
  "candidate object-index sidecar is missing, changed, malformed, or inconsistent with its block"

/-- Read and decode one entry's IBK3 artifact. `none` on any I/O or decode
    failure; the caller turns that into the message of the first sidecar
    check that needed the block. -/
private def decodePrimary? (directory : System.FilePath) (entry : Entry) :
    IO (Option L4Factoidal.Storage.IndexedBlock.Block) := do
  try
    let primary ← IO.FS.readBinFile (directory / entry.artifact.key.value)
    pure (L4Factoidal.Storage.IndexedBlockWireV3.decode primary)
  catch _ => pure none

/-- SBM3's subject index is part of the generation, not optional query
    advice: SRI2 framing/checksum, binding to the exact IBK3 digest,
    agreement with the committed row count, and equality with the canonical
    subject-to-row relation of the decoded block. -/
private def subjectIndexAgrees (directory : System.FilePath) (version : Nat) (entry : Entry)
    (index : ArtifactRef) (block? : Option L4Factoidal.Storage.IndexedBlock.Block) : IO Bool := do
  if version >= 5 then
    try
      match block? with
      | none => pure false
      | some block =>
          let indexBytes ← IO.FS.readBinFile (directory / index.key.value)
          match L4Factoidal.Storage.SubjectRowIndexWireV2.decode? indexBytes with
          | some decoded =>
              pure (decoded.targetIBKSha256 == entry.artifact.sha256 && decoded.rowCount == entry.rows &&
                decoded.pairs.toList == L4Factoidal.Storage.SubjectRowIndexWire.pairsOfRows block.rows)
          | none => pure false
    catch _ => pure false
  else
    try
      match ← Harness.IndexedBlockV3Materialize.subjectPostings? directory entry with
      | some _ => pure true
      | none => pure false
    catch _ => pure false

/-- TLI1 is a physical identity bridge, not advisory planner metadata: it is
   admissible only when its framing/checksum decode and its target digest binds
   it to the exact IBK3 artifact in the same manifest entry. -/
private def termIndexAgrees (directory : System.FilePath) (entry : Entry)
    (index : ArtifactRef) (block? : Option L4Factoidal.Storage.IndexedBlock.Block) : IO Bool := do
  if !safeLeafKey index.key then pure false else
  try
    match block? with
    | none => pure false
    | some block =>
        let bytes ← IO.FS.readBinFile (directory / index.key.value)
        match L4Factoidal.Storage.TermLocalIndexWire.decode? bytes with
        | some decoded =>
            pure (decoded.targetIBKSha256 == entry.artifact.sha256 &&
              decoded.entries == L4Factoidal.Storage.TermLocalIndex.entriesOf block.dict)
        | none => pure false
  catch _ => pure false

/-- SBM6's OLI2 bytes use the pageable local-ID/row-offset framing, but are
    separately manifest-typed and must equal the canonical object-to-row
    relation of their IBK3 artifact before activation. -/
private def objectIndexAgrees (directory : System.FilePath) (version : Nat) (entry : Entry)
    (index : ArtifactRef) (block? : Option L4Factoidal.Storage.IndexedBlock.Block) : IO Bool := do
  if version != 6 || !safeLeafKey index.key then pure false else
  try
    match block? with
    | none => pure false
    | some block =>
        let indexBytes ← IO.FS.readBinFile (directory / index.key.value)
        match L4Factoidal.Storage.SubjectRowIndexWireV2.decode? indexBytes with
        | some decoded =>
            pure (decoded.targetIBKSha256 == entry.artifact.sha256 && decoded.rowCount == entry.rows &&
              decoded.pairs.toList == L4Factoidal.Storage.SubjectRowIndexWire.pairsOfObjects block.rows)
        | none => pure false
  catch _ => pure false

/-- One entry's three index sidecars, checked in the order subject, term,
    object against ONE read and ONE decode of its IBK3 artifact. Returns the
    failure message of the first check that fails. Before 2026-09-03 each
    check re-read and re-decoded the primary (four reads and three decodes
    per block over a whole generation); the acceptance decision is the same,
    only the work is shared. -/
private def verifyEntryIndexes (directory : System.FilePath) (version : Nat) (entry : Entry) :
    IO (Option String) := do
  let needsBlock := (entry.subjectIndex.isSome && version >= 5) ||
    entry.termIndex.isSome || entry.objectIndex.isSome
  let block? ← if needsBlock then decodePrimary? directory entry else pure none
  let subjectOk ← match entry.subjectIndex with
    | none => pure true
    | some index => subjectIndexAgrees directory version entry index block?
  if !subjectOk then return some subjectIndexFailure
  let termOk ← match entry.termIndex with
    | none => pure true
    | some index => termIndexAgrees directory entry index block?
  if !termOk then return some termIndexFailure
  let objectOk ← match entry.objectIndex with
    | none => pure true
    | some index => objectIndexAgrees directory version entry index block?
  if !objectOk then return some objectIndexFailure
  pure none

private def verifyIndexSidecars (directory : System.FilePath) (version : Nat) :
    List Entry → IO (Option String)
  | [] => pure none
  | entry :: rest => do
      match ← verifyEntryIndexes directory version entry with
      | some failure => pure (some failure)
      | none => verifyIndexSidecars directory version rest

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
        match ← verifyIndexSidecars candidate manifest.version manifest.entries with
        | some failure => throw <| IO.userError failure
        | none => pure ()
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
