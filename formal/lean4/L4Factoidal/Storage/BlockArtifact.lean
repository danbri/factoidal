/-
L4Factoidal.Storage.BlockArtifact — content identity for persisted block bytes.

CRC frames a block; this module adds the cryptographic identity checked before
the block decoder is trusted. Signature/key verification is intentionally a
separate host trust-policy concern.
-/
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Storage.BlockMerkle

namespace L4Factoidal.Storage.BlockArtifact

open L4Factoidal.Crypto
open L4Factoidal.Storage.BlockMerkle (Hasher pureHasher)

abbrev Digest256 := ByteArray

/-- Content identity under a supplied hash. The specification instance is
    `pureHasher`; a host may pass `Harness.nativeHasher` (HACL* through
    `Crypto.sha256Hacl`) to admit a large artifact at C speed. The two agree
    on every input — measured by `lake exe l4vc-probe`, not proved. -/
def digestWith (h : Hasher) (bytes : ByteArray) : Digest256 := h.digest bytes

def digest (bytes : ByteArray) : Digest256 := digestWith pureHasher bytes

structure Artifact where
  payload : ByteArray
  claimedDigest : Digest256

def Artifact.valid (artifact : Artifact) : Bool :=
  artifact.claimedDigest == digest artifact.payload

def Artifact.fromPayload (payload : ByteArray) : Artifact :=
  { payload, claimedDigest := digest payload }

def verifyWith (h : Hasher) (trustedDigest : Digest256) (bytes : ByteArray) : Bool :=
  trustedDigest == digestWith h bytes

def verify (trustedDigest : Digest256) (bytes : ByteArray) : Bool :=
  verifyWith pureHasher trustedDigest bytes

end L4Factoidal.Storage.BlockArtifact
