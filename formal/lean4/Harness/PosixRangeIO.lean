/- Native POSIX range reader for executable block-engine probes.

   This deliberately lives under Harness, not L4Factoidal: `pread` is an
   operating-system realization of the pure IBK2 ByteRange contract, not part
   of the verified block semantics and not available to the WASM target. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.ChunkedArtifact

namespace Harness.PosixRangeIO

open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.BlockMerkle

/-- Read at an absolute file offset without changing any shared file cursor.
    The C implementation returns an empty array on open/read/short-read
    failure; `readRange?` below turns that into an explicit refusal by checking
    the exact requested extent. -/
@[extern "l4_block_pread"]
opaque preadRaw (path : @& String) (offset length : UInt64) : IO ByteArray

/-- Multi-writer counterpart: append only if the file still has the exact
    byte length Lean validated.  The native edge holds an exclusive advisory
    lock for the size check, write-all loop and file `fsync`. -/
@[extern "l4_delta_log_append_sync_at_size"]
opaque appendSyncAtSizeRaw (path : @& String) (expectedSize : UInt64)
  (bytes : @& ByteArray) : IO Bool

/-- Atomically replace a small, Lean-validated control file after syncing its
    complete new contents and the parent directory entry. Readers observe
    either whole version, and a successful result survives normal crash
    recovery rather than merely concurrent access. -/
@[extern "l4_atomic_replace_file_sync"]
opaque atomicReplaceFileSyncRaw (path : @& String) (bytes : @& ByteArray) : IO Bool

def readRange? (path : String) (range : ByteRange) : IO (Option ByteArray) := do
  let bytes ← preadRaw path (UInt64.ofNat range.offset) (UInt64.ofNat range.length)
  if bytes.size == range.length then pure (some bytes) else pure none

/-- Decode untrusted raw 32-byte leaf hashes from a packer's `.merkle`
    sidecar. Their authority comes only from a successful proof to an SBM1
    root, never from the sidecar file itself. `extract` avoids copying the
    whole sidecar into a linked list for each individual leaf. -/
def leaves? (expected : Nat) (bytes : ByteArray) : Option (List Digest) :=
  if bytes.size != expected * 32 then none
  else some <| (List.range expected).map fun index =>
    bytes.extract (index * 32) (index * 32 + 32)

private def singleChunkIndex? (ref : Ref) (range : ByteRange) : Option Nat := do
  if range.length == 0 || range.offset + range.length > ref.totalBytes then none else do
  let first := range.offset / ref.chunkBytes
  let last := (range.offset + range.length - 1) / ref.chunkBytes
  if first == last then some first else none

private def chunkIndices? (ref : Ref) (range : ByteRange) : Option (Nat × List Nat) := do
  if range.length == 0 || range.offset + range.length > ref.totalBytes then none else do
  let first := range.offset / ref.chunkBytes
  let last := (range.offset + range.length - 1) / ref.chunkBytes
  some (first, (List.range (last - first + 1)).map fun delta => first + delta)

/-- Honest positioned-read accounting for one verified range. `requestedBytes`
    is the logical range length; `fetchedBytes` is the sum of complete fixed
    chunks the native host must obtain before it can return that range. -/
structure VerifiedReadFootprint where
  requestedBytes : Nat
  fetchedBytes : Nat
  chunks : Nat
  deriving Repr, DecidableEq

def verifiedReadFootprint? (ref : Ref) (range : ByteRange) : Option VerifiedReadFootprint := do
  let (_, indices) ← chunkIndices? ref range
  let lengths ← indices.mapM (expectedBytes? ref)
  some { requestedBytes := range.length
         fetchedBytes := lengths.foldl (fun total length => total + length) 0
         chunks := lengths.length }

/-- A chunk retained here was admitted through `verifyChunk` in this process.
    It is a native-host cache only; its contents are never accepted directly
    from an artifact sidecar or another process. -/
structure VerifiedChunk where
  index : Nat
  bytes : ByteArray

def newVerifiedChunkCache : IO (IO.Ref (List VerifiedChunk)) := IO.mkRef []

private def readVerifiedChunk? (path : String) (ref : Ref) (leaves : List Digest)
    (index : Nat) : IO (Option ByteArray) := do
  match offset? ref index, expectedBytes? ref index, proof? leaves index with
  | some offset, some length, some proof =>
      match ← readRange? path { offset, length } with
      | some chunk => if verifyChunk ref index chunk proof then pure (some chunk) else pure none
      | none => pure none
  | _, _, _ => pure none

private def readVerifiedChunks (path : String) (ref : Ref) (leaves : List Digest) :
    List Nat → IO (Option (List ByteArray))
  | [] => pure (some [])
  | index :: rest => do
      match ← readVerifiedChunk? path ref leaves index, ← readVerifiedChunks path ref leaves rest with
      | some chunk, some chunks => pure (some (chunk :: chunks))
      | _, _ => pure none

private def concatChunks (chunks : List ByteArray) : ByteArray :=
  ByteArray.mk (chunks.flatMap (fun chunk => chunk.data.toList) |>.toArray)

/-- Compatibility helper for one fixed SBM1 chunk. The generic verified-range
    reader below now handles cross-chunk requests; this narrower form remains
    useful to callers that intentionally require a single inclusion proof. -/
def readVerifiedSingleChunkRange? (path : String) (ref : Ref) (leaves : List Digest)
    (range : ByteRange) : IO (Option ByteArray) := do
  if leaves.length != ref.chunkCount then return none
  match singleChunkIndex? ref range with
  | none => pure none
  | some index =>
      match offset? ref index, expectedBytes? ref index, proof? leaves index with
      | some offset, some length, some proof =>
          match ← readRange? path { offset, length } with
          | some chunk =>
              if !verifyChunk ref index chunk proof then pure none
              else
                let localOffset := range.offset - offset
                pure (some (chunk.extract localOffset (localOffset + range.length)))
          | none => pure none
      | _, _, _ => pure none

/-- Read an exact contiguous range by verifying every fixed chunk it touches
    to the same SBM1 root, then returning only the requested interior bytes. -/
def readVerifiedRange? (path : String) (ref : Ref) (leaves : List Digest)
    (range : ByteRange) : IO (Option ByteArray) := do
  if leaves.length != ref.chunkCount then return none
  match chunkIndices? ref range with
  | none => pure none
  | some (first, indices) =>
      match ← readVerifiedChunks path ref leaves indices with
      | none => pure none
      | some chunks =>
          let all := concatChunks chunks
          let localOffset := range.offset - first * ref.chunkBytes
          if localOffset + range.length <= all.size then
            pure (some (all.extract localOffset (localOffset + range.length)))
          else pure none

private def readCachedChunks (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) : List Nat → IO (Option (List ByteArray × Nat × Nat))
  | [] => pure (some ([], 0, 0))
  | index :: rest => do
      match (← cache.get).find? (fun cached => cached.index == index) with
      | some cached =>
          match ← readCachedChunks path ref leaves cache rest with
          | some (chunks, freshChunks, freshBytes) => pure (some (cached.bytes :: chunks, freshChunks, freshBytes))
          | none => pure none
      | none =>
          match ← readVerifiedChunk? path ref leaves index with
          | none => pure none
          | some chunk =>
              cache.modify fun chunks => { index, bytes := chunk } :: chunks
              match ← readCachedChunks path ref leaves cache rest with
              | some (chunks, freshChunks, freshBytes) =>
                  pure (some (chunk :: chunks, freshChunks + 1, freshBytes + chunk.size))
              | none => pure none

/-- Cached variant of `readVerifiedRange?`. Cache misses still perform the
    full positioned read and proof check; the returned footprint counts only
    those newly obtained chunks, not chunks already admitted by this cache. -/
def readVerifiedRangeCached? (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref (List VerifiedChunk)) (range : ByteRange) :
    IO (Option (ByteArray × VerifiedReadFootprint)) := do
  if leaves.length != ref.chunkCount then return none
  match chunkIndices? ref range with
  | none => pure none
  | some (first, indices) =>
      match ← readCachedChunks path ref leaves cache indices with
      | none => pure none
      | some (chunks, freshChunks, freshBytes) =>
          let all := concatChunks chunks
          let localOffset := range.offset - first * ref.chunkBytes
          if localOffset + range.length <= all.size then
            let bytes := all.extract localOffset (localOffset + range.length)
            pure (some (bytes, { requestedBytes := range.length, fetchedBytes := freshBytes, chunks := freshChunks }))
          else pure none

end Harness.PosixRangeIO
