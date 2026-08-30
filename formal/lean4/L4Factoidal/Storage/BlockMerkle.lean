/- Merkle commitments for independently read block chunks.

   This module commits an already-fixed sequence of chunks; it deliberately
   does not choose an IBK2 chunking policy or alter SBM0.  A later manifest
   version can commit a root, hash algorithm and chunk policy, then a range
   host can validate only the chunks it received plus this compact proof. -/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Storage.BlockMerkle

open L4Factoidal.Crypto

abbrev Digest := ByteArray

private def concat (a b : ByteArray) : ByteArray :=
  ByteArray.mk ((a.data.toList ++ b.data.toList).toArray)

/-- Domain separation prevents a payload hash being confused with a tree node
    hash. The chunk position is carried by the manifest/chunk policy; the tree
    binds the ordered sequence through left/right node position. -/
def leaf (chunk : ByteArray) : Digest := sha256 (concat (ByteArray.mk #[0]) chunk)
def node (left right : Digest) : Digest := sha256 (concat (ByteArray.mk #[1]) (concat left right))

/-- One level of a Bitcoin-style binary Merkle tree. A final unpaired leaf is
    duplicated, making the root defined for every nonempty length. -/
def nextLevel : List Digest → List Digest
  | [] => []
  | [x] => [node x x]
  | left :: right :: rest => node left right :: nextLevel rest

private def rootFuel : Nat → List Digest → Digest
  | 0, _ => ByteArray.empty
  | _ + 1, [] => ByteArray.empty
  | _ + 1, [x] => x
  | fuel + 1, xs => rootFuel fuel (nextLevel xs)

/-- Root of a nonempty sequence of leaf digests; the empty sequence has the
    distinguished empty digest and is not suitable for an artifact root. -/
def root (leaves : List Digest) : Digest := rootFuel leaves.length leaves
def rootOfChunks (chunks : List ByteArray) : Digest := root (chunks.map leaf)

structure Step where
  sibling : Digest
  siblingOnLeft : Bool
  deriving DecidableEq

private def sibling? (level : List Digest) (index : Nat) : Option Step := do
  let current ← level[index]?
  if index % 2 == 0 then
    some { sibling := (level[index + 1]?).getD current, siblingOnLeft := false }
  else
    some { sibling := (level[index - 1]?).getD current, siblingOnLeft := true }

private def proofFuel : Nat → List Digest → Nat → List Step → Option (List Step)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | _ + 1, [_], 0, acc => some acc
  | _ + 1, [_], _, _ => none
  | fuel + 1, level, index, acc => do
      let step ← sibling? level index
      proofFuel fuel (nextLevel level) (index / 2) (acc ++ [step])

/-- Compact inclusion proof for the indexed leaf. -/
def proof? (leaves : List Digest) (index : Nat) : Option (List Step) :=
  proofFuel leaves.length leaves index []

def applyStep (current : Digest) (step : Step) : Digest :=
  if step.siblingOnLeft then node step.sibling current else node current step.sibling

def verify (expected : Digest) (chunk : ByteArray) (proof : List Step) : Bool :=
  proof.foldl applyStep (leaf chunk) == expected

private def a : ByteArray := ByteArray.mk #[1, 2]
private def b : ByteArray := ByteArray.mk #[3]
private def c : ByteArray := ByteArray.mk #[4, 5, 6]
private def sampleChunks : List ByteArray := [a, b, c]
private def sampleLeaves : List Digest := sampleChunks.map leaf
private def sampleRoot : Digest := root sampleLeaves

#guard ((proof? sampleLeaves 0).map (verify sampleRoot a)) == some true
#guard ((proof? sampleLeaves 1).map (verify sampleRoot b)) == some true
#guard ((proof? sampleLeaves 2).map (verify sampleRoot c)) == some true
#guard ((proof? sampleLeaves 2).map (verify sampleRoot b)) == some false
#guard (proof? sampleLeaves 3).isNone

end L4Factoidal.Storage.BlockMerkle
