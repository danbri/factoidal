/- Merkle commitments for independently read block chunks.

   This module commits an already-fixed sequence of chunks; it deliberately
   does not choose an IBK2 chunking policy or alter SBM0.  A later manifest
   version can commit a root, hash algorithm and chunk policy, then a range
   host can validate only the chunks it received plus this compact proof.

   ## The hash is a parameter

   Every tree operation takes a `Hasher` and is defined `…With h`. The
   SPECIFICATION instance is `pureHasher`, the pure Lean FIPS 180-4
   `Crypto.sha256`; the unsuffixed names (`leaf`, `node`, `root`, …) are
   exactly those partial applications, so every `#guard` here and in
   `ChunkedArtifact.lean` still evaluates the pure function in the Lean
   interpreter, and every theorem about this tree is a theorem about
   `pureHasher`.

   A HOST may pass a different instance for speed — `Harness/
   NativeHasher.lean`'s `nativeHasher`, HACL*'s extracted C through
   `Crypto.sha256Hacl`. That is sound only because the two agree on every
   input, which `lake exe l4vc-probe`'s `sha256 differential` section measures on
   the FIPS vectors, the block/padding boundaries and a 1 MiB buffer. The
   parameter is deliberately explicit rather than an `@[implemented_by]` on
   `sha256`: build-time `#guard`s run in the interpreter, which cannot call
   an extern. -/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Storage.BlockMerkle

open L4Factoidal.Crypto

abbrev Digest := ByteArray

/-- The hash a Merkle computation is taken over. One field, so a host can
    substitute a faster realisation of the SAME function without any other
    part of the tree changing. -/
structure Hasher where
  digest : ByteArray → ByteArray

/-- The specification instance: pure Lean SHA-256 (`Crypto/SHA2.lean`,
    FIPS 180-4 vectors as build-time `#guard`s). Every unsuffixed name
    below is this instance, and every theorem is about it. -/
def pureHasher : Hasher := ⟨sha256⟩

private def concat (a b : ByteArray) : ByteArray :=
  ByteArray.mk ((a.data.toList ++ b.data.toList).toArray)

/-- Domain separation prevents a payload hash being confused with a tree node
    hash. The chunk position is carried by the manifest/chunk policy; the tree
    binds the ordered sequence through left/right node position. -/
def leafWith (h : Hasher) (chunk : ByteArray) : Digest :=
  h.digest (concat (ByteArray.mk #[0]) chunk)

def nodeWith (h : Hasher) (left right : Digest) : Digest :=
  h.digest (concat (ByteArray.mk #[1]) (concat left right))

/-- One level of a Bitcoin-style binary Merkle tree. A final unpaired leaf is
    duplicated, making the root defined for every nonempty length. -/
def nextLevelWith (h : Hasher) : List Digest → List Digest
  | [] => []
  | [x] => [nodeWith h x x]
  | left :: right :: rest => nodeWith h left right :: nextLevelWith h rest

private def rootFuelWith (h : Hasher) : Nat → List Digest → Digest
  | 0, _ => ByteArray.empty
  | _ + 1, [] => ByteArray.empty
  | _ + 1, [x] => x
  | fuel + 1, xs => rootFuelWith h fuel (nextLevelWith h xs)

/-- Root of a nonempty sequence of leaf digests; the empty sequence has the
    distinguished empty digest and is not suitable for an artifact root. -/
def rootWith (h : Hasher) (leaves : List Digest) : Digest :=
  rootFuelWith h leaves.length leaves

def rootOfChunksWith (h : Hasher) (chunks : List ByteArray) : Digest :=
  rootWith h (chunks.map (leafWith h))

structure Step where
  sibling : Digest
  siblingOnLeft : Bool
  deriving DecidableEq

/-- Sibling selection reads the level it is given; it does not hash, so it
    needs no `Hasher`. -/
private def sibling? (level : List Digest) (index : Nat) : Option Step := do
  let current ← level[index]?
  if index % 2 == 0 then
    some { sibling := (level[index + 1]?).getD current, siblingOnLeft := false }
  else
    some { sibling := (level[index - 1]?).getD current, siblingOnLeft := true }

private def proofFuelWith (h : Hasher) :
    Nat → List Digest → Nat → List Step → Option (List Step)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | _ + 1, [_], 0, acc => some acc
  | _ + 1, [_], _, _ => none
  | fuel + 1, level, index, acc => do
      let step ← sibling? level index
      proofFuelWith h fuel (nextLevelWith h level) (index / 2) (acc ++ [step])

/-- Compact inclusion proof for the indexed leaf. -/
def proofWith? (h : Hasher) (leaves : List Digest) (index : Nat) : Option (List Step) :=
  proofFuelWith h leaves.length leaves index []

def applyStepWith (h : Hasher) (current : Digest) (step : Step) : Digest :=
  if step.siblingOnLeft then nodeWith h step.sibling current else nodeWith h current step.sibling

def verifyWith (h : Hasher) (expected : Digest) (chunk : ByteArray) (proof : List Step) : Bool :=
  proof.foldl (applyStepWith h) (leafWith h chunk) == expected

/-! ## The pure instance

The names every existing caller, `#guard` and theorem uses. They are the
`…With pureHasher` partial applications and nothing else, so nothing about
the committed byte format or any proved property changes by the parameter
existing. -/

def leaf : ByteArray → Digest := leafWith pureHasher
def node : Digest → Digest → Digest := nodeWith pureHasher
def nextLevel : List Digest → List Digest := nextLevelWith pureHasher
def root : List Digest → Digest := rootWith pureHasher
def rootOfChunks : List ByteArray → Digest := rootOfChunksWith pureHasher
def proof? : List Digest → Nat → Option (List Step) := proofWith? pureHasher
def applyStep : Digest → Step → Digest := applyStepWith pureHasher
def verify : Digest → ByteArray → List Step → Bool := verifyWith pureHasher

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

/- The suffixed and unsuffixed forms are the same function at `pureHasher`;
   this pins that they stay so if either is edited. -/
#guard rootOfChunks sampleChunks == rootOfChunksWith pureHasher sampleChunks

end L4Factoidal.Storage.BlockMerkle
