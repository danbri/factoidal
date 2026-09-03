/- Native POSIX range reader for executable block-engine probes.

   This deliberately lives under Harness, not L4Factoidal: `pread` is an
   operating-system realization of the pure IBK2 ByteRange contract, not part
   of the verified block semantics and not available to the WASM target. -/
import L4Factoidal.Storage.IndexedBlockWireV2
import L4Factoidal.Storage.ChunkedArtifact
import L4Factoidal.Storage.GenerationVerify
import Harness.NativeHasher

namespace Harness.PosixRangeIO

open L4Factoidal.Storage.IndexedBlockWireV2
open L4Factoidal.Storage.ChunkedArtifact
open L4Factoidal.Storage.BlockMerkle

/- Every chunk admission below hashes with `Harness.nativeHasher` (HACL*
    `Hacl_Hash_SHA2_hash_256`) rather than the pure Lean specification
    hash. The admitted bytes are identical either way — the two hashers
    agree on every input, measured by `lake exe l4vc-probe` — and a full
    scan of a 25 MB store was spending about half its wall clock inside the
    pure `sha256`. The specification instance stays `pureHasher`; nothing
    proved about `ChunkedArtifact` or `BlockMerkle` mentions the extern. -/

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
  L4Factoidal.Storage.GenerationVerify.leaves? expected bytes

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

/-- A cache is indexed by the already validated fixed-chunk ordinal.  The
    earlier association-list representation was deliberately simple, but a
    full scan of a large artifact performs one lookup per row and made cache
    hits grow linearly with the number of admitted chunks.  This bounded
    sparse array keeps the same trust boundary -- only `readVerifiedChunk?`
    inserts bytes -- while making an admitted-chunk lookup constant time. -/
abbrev VerifiedChunkCache := Array (Option ByteArray)

def newVerifiedChunkCache (ref : Ref) : IO (IO.Ref VerifiedChunkCache) :=
  IO.mkRef (Array.replicate ref.chunkCount none)

private def readVerifiedChunk? (path : String) (ref : Ref) (leaves : List Digest)
    (index : Nat) : IO (Option ByteArray) := do
  match offset? ref index, expectedBytes? ref index, proofWith? nativeHasher leaves index with
  | some offset, some length, some proof =>
      match ← readRange? path { offset, length } with
      | some chunk => if verifyChunkWith nativeHasher ref index chunk proof then pure (some chunk) else pure none
      | none => pure none
  | _, _, _ => pure none

/-- Admit one fixed chunk through the same positioned-read and Merkle-proof
    path as `readVerifiedRangeCached?`.  A cache hit reports zero newly
    fetched/requested bytes; callers that form a larger logical range account
    for that range separately.  This primitive is useful for streaming
    validators which must not first concatenate every touched chunk. -/
def readVerifiedChunkCached? (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) (index : Nat) :
    IO (Option (ByteArray × VerifiedReadFootprint)) := do
  match (← cache.get)[index]? with
  | some (some chunk) =>
      pure (some (chunk, { requestedBytes := 0, fetchedBytes := 0, chunks := 0 }))
  | _ =>
      match ← readVerifiedChunk? path ref leaves index with
      | none => pure none
      | some chunk =>
          cache.modify fun chunks => chunks.set! index (some chunk)
          pure (some (chunk, { requestedBytes := chunk.size, fetchedBytes := chunk.size, chunks := 1 }))

private def readVerifiedChunks (path : String) (ref : Ref) (leaves : List Digest) :
    List Nat → IO (Option (List ByteArray))
  | [] => pure (some [])
  | index :: rest => do
      match ← readVerifiedChunk? path ref leaves index, ← readVerifiedChunks path ref leaves rest with
      | some chunk, some chunks => pure (some (chunk :: chunks))
      | _, _ => pure none

private def concatChunks (chunks : List ByteArray) : ByteArray :=
  /- `fastAppend` is Lean's growing-capacity append intended for repeated
     assembly. This keeps verified cross-chunk reads packed throughout rather
     than materializing every chunk as a linked byte list. -/
  chunks.foldl ByteArray.fastAppend ByteArray.empty

/-- Compatibility helper for one fixed SBM1 chunk. The generic verified-range
    reader below now handles cross-chunk requests; this narrower form remains
    useful to callers that intentionally require a single inclusion proof. -/
def readVerifiedSingleChunkRange? (path : String) (ref : Ref) (leaves : List Digest)
    (range : ByteRange) : IO (Option ByteArray) := do
  if leaves.length != ref.chunkCount then return none
  match singleChunkIndex? ref range with
  | none => pure none
  | some index =>
      match offset? ref index, expectedBytes? ref index, proofWith? nativeHasher leaves index with
      | some offset, some length, some proof =>
          match ← readRange? path { offset, length } with
          | some chunk =>
              if !verifyChunkWith nativeHasher ref index chunk proof then pure none
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
          /- Most row reads touch one chunk.  Do not copy a full fixed chunk
             merely to take the requested few bytes from it; concatenate only
             when an exact range actually crosses a chunk boundary. -/
          let all := match chunks with
            | [chunk] => chunk
            | _ => concatChunks chunks
          let localOffset := range.offset - first * ref.chunkBytes
          if localOffset + range.length <= all.size then
            pure (some (all.extract localOffset (localOffset + range.length)))
          else pure none

private def readCachedChunks (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) : List Nat → IO (Option (List ByteArray × Nat × Nat))
  | [] => pure (some ([], 0, 0))
  | index :: rest => do
      match ← readVerifiedChunkCached? path ref leaves cache index with
      | some (chunk, footprint) =>
          match ← readCachedChunks path ref leaves cache rest with
          | some (chunks, freshChunks, freshBytes) =>
              pure (some (chunk :: chunks, freshChunks + footprint.chunks, freshBytes + footprint.fetchedBytes))
          | none => pure none
      | none => pure none

/-- Cached variant of `readVerifiedRange?`. Cache misses still perform the
    full positioned read and proof check; the returned footprint counts only
    those newly obtained chunks, not chunks already admitted by this cache. -/
def readVerifiedRangeCached? (path : String) (ref : Ref) (leaves : List Digest)
    (cache : IO.Ref VerifiedChunkCache) (range : ByteRange) :
    IO (Option (ByteArray × VerifiedReadFootprint)) := do
  if leaves.length != ref.chunkCount then return none
  match chunkIndices? ref range with
  | none => pure none
  | some (first, indices) =>
      match ← readCachedChunks path ref leaves cache indices with
      | none => pure none
      | some (chunks, freshChunks, freshBytes) =>
          /- A cached fixed-row read ordinarily has exactly one chunk.  This
             branch avoids allocating and copying that whole chunk on every
             row while retaining the existing general cross-chunk behaviour. -/
          let all := match chunks with
            | [chunk] => chunk
            | _ => concatChunks chunks
          let localOffset := range.offset - first * ref.chunkBytes
          if localOffset + range.length <= all.size then
            let bytes := all.extract localOffset (localOffset + range.length)
            pure (some (bytes, { requestedBytes := range.length, fetchedBytes := freshBytes, chunks := freshChunks }))
          else pure none

end Harness.PosixRangeIO
