/- Durable companion metadata for an immutable Shardborough generation.

`compacted.epoch` says which DLOG epochs have already been folded into the
generation's IBK2 base. It is deliberately a separate, framed control file:
the base bytes remain canonical IBK2/SBM2 artifacts, while a reader can refuse
a malformed epoch marker before it replays any log record. -/
import Harness.PosixRangeIO
import L4Factoidal.Storage.DeltaLog

namespace Harness.CompactedEpoch

open Harness.PosixRangeIO
open L4Factoidal.Storage

def markerName : String := "compacted.epoch"

def markerPath (directory : System.FilePath) : System.FilePath := directory / markerName

/-- Absent metadata denotes a never-compacted legacy generation. A present
    malformed marker is not silently treated as absent: the caller must refuse
    replay rather than risk applying an already-folded update twice. -/
def read? (directory : System.FilePath) : IO (Option Nat) := do
  let path := markerPath directory
  try
    let bytes ← IO.FS.readBinFile path
    match parseEpoch bytes.toList with
    | some marker => pure (some marker.epoch)
    | none => throw <| IO.userError "compacted.epoch is malformed or unsupported"
  catch e =>
    if ← path.pathExists then throw e else pure none

/-- Persist a completed compaction threshold before a caller activates its
    generation. The POSIX edge writes a temporary file, syncs it, renames it,
    then syncs its parent directory. -/
def write (directory : System.FilePath) (epoch : Nat) : IO Bool :=
  let framed := frameEpoch ⟨epoch⟩
  if framed.isEmpty then pure false
  else atomicReplaceFileSyncRaw (markerPath directory).toString
    (ByteArray.mk framed.toArray)

/-- New requests must be strictly newer than the threshold recorded by an
    already compacted base. A legacy base starts its first DLOG epoch at one. -/
def nextWriteEpoch (baseEpoch : Option Nat) : Nat :=
  match baseEpoch with
  | none => 1
  | some epoch => epoch + 1

/-- The output base of a compaction incorporates both its source threshold and
    every replayed source batch, so its marker advances through the greatest
    epoch it consumed. -/
def foldedThrough (baseEpoch : Option Nat) (batches : List DeltaBatch) : Nat :=
  batches.foldl (fun maximum batch => max maximum batch.epoch) (baseEpoch.getD 0)

end Harness.CompactedEpoch
