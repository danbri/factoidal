/- The HACL*-backed `Hasher` instance for host (executable-edge) callers.

   `L4Factoidal/Storage/BlockMerkle.lean` takes the hash as an explicit
   parameter. `pureHasher` — pure Lean `Crypto.sha256` — is the
   specification and stays what every `#guard` and every theorem
   evaluates. `nativeHasher` below is the same function realised by
   HACL*'s extracted C (`Crypto/SHA2Native.lean`, `sha256Hacl`), for
   hosts that must admit tens of megabytes of PUBLIC block bytes through
   Merkle roots and full-file digests.

   It lives under `Harness/`, not under `L4Factoidal/`, for two reasons:
   the verified library must not depend on an extern for its own
   semantics, and `Wasm/build-wasm.sh` skips every `Harness_*`
   translation unit, so the browser worker's closure is unaffected.
   (The browser worker checks CRC, not Merkle, so it has no use for it.)

   The substitution is sound only because the two hashers agree on every
   input. That is MEASURED, not proved: `lake exe l4vc-probe` runs a
   `sha256 differential` section over the FIPS 180-4 vectors, the SHA-256 block
   and padding boundaries, and a 1 MiB buffer, and exits non-zero on any
   mismatch. -/
import L4Factoidal.Crypto.SHA2Native
import L4Factoidal.Storage.BlockMerkle

namespace Harness

/-- HACL* SHA-256 for host callers that hash a whole artifact rather than
build a tree. Extensionally equal to `L4Factoidal.Crypto.sha256`; see the
module comment for where that equality is checked. Every host call site goes
through this name (and `nativeHasher` below) rather than naming the extern
directly, so the whole executable edge can be moved back to the pure
specification hash by editing this one file — which is how the before/after
measurements of the change were taken. -/
def nativeSha256 : ByteArray → ByteArray := L4Factoidal.Crypto.sha256Hacl

/-- HACL* SHA-256 as a `BlockMerkle.Hasher`. Extensionally equal to
`L4Factoidal.Storage.BlockMerkle.pureHasher`. -/
def nativeHasher : L4Factoidal.Storage.BlockMerkle.Hasher := ⟨nativeSha256⟩

end Harness
