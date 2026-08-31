/- Verified fixed-chunk artifact admission, independent of an SBM wire version.
   It is the host-facing bridge between a Merkle commitment and a positioned
   range read: the host supplies a chunk index, exact chunk bytes and proof;
   this module decides whether those bytes are admitted under the declared
   immutable artifact identity. -/
import L4Factoidal.Storage.BlockMerkle

namespace L4Factoidal.Storage.ChunkedArtifact

open L4Factoidal.Storage.BlockMerkle

structure Ref where
  totalBytes : Nat
  chunkBytes : Nat
  chunkCount : Nat
  root : Digest
  deriving DecidableEq

def expectedCount (totalBytes chunkBytes : Nat) : Nat :=
  if chunkBytes == 0 then 0 else (totalBytes + chunkBytes - 1) / chunkBytes

/-- Canonical fixed-width chunking directly over byte offsets.  Building a
    `List UInt8` for every chunk makes full Merkle admission quadratic in the
    artifact size. The reverse accumulator retains canonical ascending order
    without repeatedly traversing the source bytes. -/
def chunksOf (width : Nat) (bytes : ByteArray) : List ByteArray :=
  if width == 0 then []
  else
    let rec go : Nat → Nat → List ByteArray → List ByteArray
      | 0, _, reversed => reversed.reverse
      | count + 1, offset, reversed =>
          let next := min bytes.size (offset + width)
          go count next (bytes.extract offset next :: reversed)
    go (expectedCount bytes.size width) 0 []

def valid (ref : Ref) : Bool :=
  ref.totalBytes > 0 && ref.chunkBytes > 0 && ref.root.size == 32 &&
    ref.chunkCount == expectedCount ref.totalBytes ref.chunkBytes

private def canonicalLengths (width : Nat) : List ByteArray → Bool
  | [] => false
  | [last] => last.size > 0 && last.size <= width
  | chunk :: rest => chunk.size == width && canonicalLengths width rest

def fromChunks? (width : Nat) (chunks : List ByteArray) : Option Ref :=
  let totalBytes := chunks.foldl (fun n chunk => n + chunk.size) 0
  let ref : Ref := { totalBytes, chunkBytes := width, chunkCount := chunks.length, root := rootOfChunks chunks }
  if valid ref && canonicalLengths width chunks
  then some ref else none

def offset? (ref : Ref) (index : Nat) : Option Nat :=
  if valid ref && index < ref.chunkCount then some (index * ref.chunkBytes) else none

def expectedBytes? (ref : Ref) (index : Nat) : Option Nat := do
  let offset ← offset? ref index
  some (min ref.chunkBytes (ref.totalBytes - offset))

/-- Admission for one independently fetched fixed chunk. The caller is still
    responsible for using `offset?` as the actual positioned-read offset. -/
def verifyChunk (ref : Ref) (index : Nat) (bytes : ByteArray) (proof : List Step) : Bool :=
  match expectedBytes? ref index with
  | none => false
  | some expected => bytes.size == expected && BlockMerkle.verify ref.root bytes proof

private def c0 : ByteArray := ByteArray.mk #[1, 2]
private def c1 : ByteArray := ByteArray.mk #[3, 4]
private def c2 : ByteArray := ByteArray.mk #[5]
private def chunks : List ByteArray := [c0, c1, c2]
private def leaves := chunks.map leaf
private def sample : Ref :=
  { totalBytes := 5, chunkBytes := 2, chunkCount := 3, root := root leaves }

#guard valid sample
#guard chunksOf 2 (ByteArray.mk #[1, 2, 3, 4, 5]) == chunks
#guard (fromChunks? 2 chunks) == some sample
#guard (fromChunks? 2 [c0, c2, c1]).isNone
#guard offset? sample 0 == some 0
#guard offset? sample 2 == some 4
#guard expectedBytes? sample 2 == some 1
#guard ((proof? leaves 0).map (verifyChunk sample 0 c0)) == some true
#guard ((proof? leaves 2).map (verifyChunk sample 2 c2)) == some true
#guard ((proof? leaves 2).map (verifyChunk sample 2 c1)) == some false
#guard !(verifyChunk sample 3 c2 [])
#guard !(verifyChunk { sample with chunkCount := 2 } 0 c0 [])

end L4Factoidal.Storage.ChunkedArtifact
