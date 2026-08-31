/- A small control-plane layer for immutable Shardborough generations.

`CURRENT` is UTF-8 containing exactly one safe child-directory name. Existing
direct collection paths remain valid when no pointer exists. The pointer is
not RDF data and is deliberately outside the IBK2/Merkle semantic core. -/
import Harness.PosixRangeIO

namespace Harness.GenerationPointer

open Harness.PosixRangeIO

def currentName : String := "CURRENT"

def safeGenerationName (name : String) : Bool :=
  !name.isEmpty && name != "." && name != ".." &&
    !(name.contains '/') && !(name.contains '\\')

private def asBytes (text : String) : ByteArray := text.toUTF8

/-- Resolve a collection root through its optional `CURRENT` pointer. A
    malformed, missing-target or non-UTF-8 existing pointer is an admission
    failure; only a genuinely absent pointer means the root is itself a direct
    collection. -/
def resolveStoreDirectory (root : System.FilePath) : IO System.FilePath := do
  let pointer := root / currentName
  try
    let bytes ← IO.FS.readBinFile pointer
    match String.fromUTF8? bytes with
    | some name =>
        if !safeGenerationName name then
          throw <| IO.userError "CURRENT does not name a safe generation directory"
        let target := root / name
        if ← target.pathExists then pure target
        else throw <| IO.userError s!"CURRENT names missing generation: {name}"
    | none => throw <| IO.userError "CURRENT is not valid UTF-8"
  catch e =>
    if (← pointer.pathExists) then throw e else pure root

/-- Publish a fully validated generation name. The native edge syncs the
    complete temporary contents before atomic rename, so concurrent readers
    never observe a partial pointer. -/
def activateGeneration (root : System.FilePath) (name : String) : IO Bool :=
  if !safeGenerationName name then pure false
  else atomicReplaceFileSyncRaw (root / currentName).toString (asBytes name)

end Harness.GenerationPointer
