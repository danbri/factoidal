/- Validate a fresh immutable generation, then atomically make it the active
   child of a Shardborough collection root. -/
import Harness.GenerationPointer
import Harness.ShardMerkleMaterialize
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardActivate

open Harness.GenerationPointer
open Harness.ShardMerkleMaterialize
open L4Factoidal.Crypto
open L4Factoidal.Storage
open L4Factoidal.Storage.ShardManifest

private def compactedDefaultLayout : String :=
  "predicate-ibk2-merkle-v2-compacted-default-dlog-v1"

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
    | some (_, []) => pure bytes
    | _ => throw <| IO.userError "source DLOG is malformed or has an uncommitted suffix"
  catch e =>
    if (← dlog.pathExists) then throw e else pure ByteArray.empty
  pure <| sha256 (manifest ++ delta)

/-- A compacted candidate is only valid for the exact source snapshot it was
    built from. This is deliberately checked before `CURRENT` is replaced;
    retrying compaction is the safe response to a source-side write race. -/
private def sourceStillCurrent (root candidate : System.FilePath) (manifest : Manifest) : IO Bool := do
  if manifest.layout != compactedDefaultLayout then pure true else
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
private def verifyFullEntries (directory : System.FilePath) : List Entry → IO Bool
  | [] => pure true
  | entry :: rest => do
      if !safeLeafKey entry.artifact.key then pure false else
      try
        let bytes ← IO.FS.readBinFile (directory / entry.artifact.key.value)
        if !verifyEntry entry bytes then pure false
        else verifyFullEntries directory rest
      catch _ => pure false

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
        match ← scanEntries candidate manifest.entries with
        | none => throw <| IO.userError "candidate child artifact is missing, changed, or malformed"
        | some (_, verifiedBytes) =>
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
