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
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.SubjectRowIndexWire
import L4Factoidal.Storage.SubjectRowIndexWireV2
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.GenerationVerify

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

/-- The IBK4 layout labels: SBM7's, SBM8's, which adds the LGI1 literal search
    index sidecar, and SBM9's, which adds the GBI1 geometry bounding-box index
    beside it. There is no compacted variant of any of the three: the
    compactor does not build IBK4 generations. -/
private def ibk4Layout : String :=
  "quad-ibk4-ptd1-merkle-v0"

private def ibk4Lgi1Layout : String :=
  "quad-ibk4-ptd1-lgi1-merkle-v0"

private def ibk4Lgi1Gbi1Layout : String :=
  "quad-ibk4-ptd1-lgi1-gbi1-merkle-v0"

private def isIbk4Layout (layout : String) : Bool :=
  layout == ibk4Layout || layout == ibk4Lgi1Layout || layout == ibk4Lgi1Gbi1Layout

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

/-! ## The checks, which are shared with the WebAssembly activator

Every byte-level check below is `L4Factoidal.Storage.GenerationVerify`, which
is pure and takes a READER from an artifact name to its bytes. This file
supplies a reader over the candidate directory; `Wasm/Ops/Pack.lean` supplies
one over a byte region a JavaScript host wrote into the module's heap. The
two therefore reach the same verdict on the same generation, and there is one
implementation of the rules (iron rule 7 of CLAUDE.md).

Activation is intentionally stricter than a selective query: before a
generation becomes globally visible, every child must satisfy both
independently recorded commitments over the same observed bytes. The later
range scan checks the Merkle roots; the full pass checks full SHA-256. A
hand-crafted manifest whose digest and root describe different artifacts is
rejected at activation rather than deferred to a query path.

The hashing uses `Harness.nativeHasher` (HACL* C) instead of the pure Lean
specification hash. Activation rebuilds every leaf and every root of the
whole generation, so this is the dominant cost; the two hashers compute the
same function (measured by `lake exe l4vc-probe`), so no committed byte and
no acceptance decision changes. -/

private def directoryReader (directory : System.FilePath) :
    L4Factoidal.Storage.GenerationVerify.Reader IO := fun name => do
  try
    pure (some (← IO.FS.readBinFile (directory / name)))
  catch _ => pure none

/-- The SBM4-and-earlier subject index, whose SRI1 postings only the paged
    native materializer reads. A wasm caller has no positioned reads and
    refuses a pre-SBM5 generation instead. -/
private def legacySubjectPostings (directory : System.FilePath) :
    Entry → ArtifactRef → IO Bool := fun entry _index => do
  try
    match ← Harness.IndexedBlockV3Materialize.subjectPostings? directory entry with
    | some _ => pure true
    | none => pure false
  catch _ => pure false

private def verifyFullEntries (directory : System.FilePath) (entries : List Entry) : IO Bool :=
  L4Factoidal.Storage.GenerationVerify.verifyFullEntries nativeHasher
    (directoryReader directory) entries

private def verifyIndexSidecars (directory : System.FilePath) (version : Nat)
    (entries : List Entry) : IO (Option String) :=
  L4Factoidal.Storage.GenerationVerify.verifyIndexSidecars (directoryReader directory)
    version (legacySubjectPostings directory) entries

private def quadEntryFailure : String :=
  L4Factoidal.Storage.GenerationVerify.quadEntryFailure

private def verifyQuadEntries (directory : System.FilePath) (entries : List Entry) :
    IO (Option Nat) :=
  L4Factoidal.Storage.GenerationVerify.verifyQuadEntries (directoryReader directory) entries 0


/-- Validate the selected physical layout after full-file SHA-256 admission.
    IBK2 uses its existing all-entry materializer; IBK3 uses the paged reader,
    which rechecks every selected byte range against the committed Merkle
    leaves while decoding the same entries. -/
private def verifyReadableEntries (directory : System.FilePath) (manifest : Manifest) : IO (Option Nat) := do
  if isIbk4Layout manifest.layout then
    verifyQuadEntries directory manifest.entries
  else if isIbk3Layout manifest.layout then
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
        | none =>
            if isIbk4Layout manifest.layout then throw <| IO.userError quadEntryFailure
            else throw <| IO.userError "candidate child artifact is missing, changed, or malformed"
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
