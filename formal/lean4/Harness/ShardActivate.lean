/- Validate a fresh immutable generation, then atomically make it the active
   child of a Shardborough collection root. -/
import Harness.GenerationPointer
import Harness.ShardMerkleMaterialize
import L4Factoidal.Storage.ShardManifest

namespace Harness.ShardActivate

open Harness.GenerationPointer
open Harness.ShardMerkleMaterialize
open L4Factoidal.Storage.ShardManifest

private def readManifest (directory : System.FilePath) : IO ByteArray := do
  let sbm2 := directory / "manifest.sbm2"
  try IO.FS.readBinFile sbm2
  catch _ => IO.FS.readBinFile (directory / "manifest.sbm1")

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
