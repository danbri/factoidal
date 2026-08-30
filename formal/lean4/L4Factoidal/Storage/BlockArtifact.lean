/-
L4Factoidal.Storage.BlockArtifact — content identity for persisted block bytes.

CRC frames a block; this module adds the cryptographic identity checked before
the block decoder is trusted. Signature/key verification is intentionally a
separate host trust-policy concern.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Storage.BlockArtifact

open L4Factoidal.Crypto

abbrev Digest256 := ByteArray

def digest (bytes : ByteArray) : Digest256 := sha256 bytes

structure Artifact where
  payload : ByteArray
  claimedDigest : Digest256

def Artifact.valid (artifact : Artifact) : Bool :=
  artifact.claimedDigest == digest artifact.payload

def Artifact.fromPayload (payload : ByteArray) : Artifact :=
  { payload, claimedDigest := digest payload }

def verify (trustedDigest : Digest256) (bytes : ByteArray) : Bool :=
  trustedDigest == digest bytes

end L4Factoidal.Storage.BlockArtifact
