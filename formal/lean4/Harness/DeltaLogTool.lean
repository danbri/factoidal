/-
Small native edge for the DLOG sidecar used by a Shardborough collection.

It deliberately owns only filesystem effects.  Parsing, translating an UPDATE,
and serialising the batch are Lean definitions.  This first host refuses
INSERT DATA blank nodes because allocating their fresh request scope requires
the composed base-plus-delta dataset; it will be admitted when that reader is
wired.  Existing logs with a torn suffix are also refused for mutation: replay
may safely query their committed prefix, but a repair/compaction tool must make
the recovery decision before a writer appends after it.
-/
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.Storage.DeltaLog
import Harness.PosixRangeIO
import Harness.GenerationPointer

namespace Harness.DeltaLogTool

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open Harness.PosixRangeIO
open Harness.GenerationPointer

private def logPath (directory : System.FilePath) : System.FilePath := directory / "deltas.dlog"

private def asBytes (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

private def readExisting (path : System.FilePath) : IO (List DeltaBatch × Nat) := do
  try
    let bytes ← IO.FS.readBinFile path
    match parseLog bytes.toList with
    | none => throw <| IO.userError "DLOG header is malformed or unsupported"
    | some (batches, []) => pure (batches, bytes.size)
    | some (_, _) => throw <| IO.userError "DLOG has a torn or uncommitted suffix; recover it before appending"
  catch e =>
    if (← path.pathExists) then throw e else pure ([], 0)

private def nextSeq : List DeltaBatch → Nat
  | [] => 1
  | batch :: rest =>
      let last := rest.foldl (fun _ next => next) batch
      last.seq + 1

private def hasInsertBnode : List UpdateOp → Bool
  | [] => false
  | .insertData quads :: rest =>
      (collectQuads none quads).any (fun q => q.2.hasBnode) || hasInsertBnode rest
  | _ :: rest => hasInsertBnode rest

private def commitUpdate (path : System.FilePath) (update : Update) : Nat → IO UInt32
  | 0 => do
      IO.eprintln "l4block-delta-log failed: concurrent writers prevented a stable append after 3 retries"
      pure 1
  | retries + 1 => do
      let (batches, expectedSize) ← readExisting path
      match deltaBatchForUpdate? (nextSeq batches) 0 id update with
      | none =>
          IO.eprintln "l4block-delta-log rejected: update needs WHERE evaluation or unsupported graph-wide operation"
          pure 1
      | some batch =>
          let frame := serializeDeltaBatch batch
          let bytes := if expectedSize == 0 then serializeLog [] ++ frame else frame
          if ← appendSyncAtSizeRaw path.toString (UInt64.ofNat expectedSize) (asBytes bytes) then
            IO.println s!"l4block-delta-log committed path={path} seq={batch.seq} epoch={batch.epoch} ops={batch.ops.length} bytes={frame.length} sync=file retries={3 - retries}"
            pure 0
          else commitUpdate path update retries

private def appendUpdate (directory : System.FilePath) (updateText : String) : IO UInt32 := do
  let directory ← resolveStoreDirectory directory
  let path := logPath directory
  match parseSparqlUpdate updateText with
  | .error error => IO.eprintln s!"l4block-delta-log update parse error at {error.pos}: {error.msg}"; pure 1
  | .ok update =>
      if hasInsertBnode update.ops then
        IO.eprintln "l4block-delta-log rejected: INSERT DATA blank nodes await composed-store freshness allocation"
        pure 1
      else commitUpdate path update 3

private def inspect (directory : System.FilePath) : IO UInt32 := do
  let directory ← resolveStoreDirectory directory
  let path := logPath directory
  try
    let bytes ← IO.FS.readBinFile path
    match parseLog bytes.toList with
    | none => IO.eprintln "l4block-delta-log rejected: DLOG header is malformed or unsupported"; pure 1
    | some (batches, tail) =>
        IO.println s!"l4block-delta-log path={path} committed-batches={batches.length} committed-ops={(batches.flatMap (·.ops)).length} clean-tail={tail.isEmpty}"
        pure (if tail.isEmpty then 0 else 1)
  catch _ => IO.eprintln s!"l4block-delta-log no log at {path}"; pure 1

def main (args : List String) : IO UInt32 :=
  match args with
  | directory :: "--update" :: updateParts =>
      if updateParts.isEmpty then do
        IO.eprintln "l4block-delta-log requires SPARQL UPDATE text after --update"
        pure 2
      else appendUpdate (System.FilePath.mk directory) (String.intercalate " " updateParts)
  | directory :: "--inspect" :: [] => inspect (System.FilePath.mk directory)
  | _ => do
      IO.eprintln "usage: l4block-delta-log STORE-DIR --update SPARQL-UPDATE | --inspect"
      pure 2

end Harness.DeltaLogTool

def main (args : List String) : IO UInt32 := Harness.DeltaLogTool.main args
