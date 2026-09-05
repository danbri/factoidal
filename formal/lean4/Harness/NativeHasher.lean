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

/-! ## The streaming edge

`nativeHasher` above hashes a WHOLE artifact, so it cannot digest a source
the packer never holds in memory. The packer's source identity is built by
`Crypto.Sha256Stream`, which walks its 65,536-byte chunks with the pure Lean
compression fold, and the shard packer runs that walk TWICE over every input
byte: once in the pre-pass that commits the source identity, and once in the
ingest pass that checks the file did not change between the two.

Measured with `/usr/bin/sample` on a 104,857,577-byte N-Quads pack,
2026-09-05: the pre-pass held every one of the 21,918 samples of the
20-second window, and 14,162 of its 21,806 leaf samples were inside
`Sha256Stream.update`. `nativeBlockFold256` below is the same fold realised
by HACL* C, injected at the executable edge only. -/

private def wordsToStateBytes (h : Array UInt32) : ByteArray :=
  (List.range 8).foldl
    (fun acc i =>
      let w : UInt32 := h[i]!
      ((acc.push (w >>> 24).toUInt8).push (w >>> 16).toUInt8).push
        (w >>> 8).toUInt8 |>.push w.toUInt8)
    ByteArray.empty

private def stateBytesToWords (b : ByteArray) : Array UInt32 :=
  (List.range 8).foldl
    (fun acc i =>
      acc.push
        ((b[4 * i]!).toUInt32 <<< 24 ||| (b[4 * i + 1]!).toUInt32 <<< 16 |||
          (b[4 * i + 2]!).toUInt32 <<< 8 ||| (b[4 * i + 3]!).toUInt32))
    (Array.empty)

/-- The SHA-256 compression walk realised by HACL* C. Extensionally equal to
`L4Factoidal.Crypto.pureBlockFold256`; see `Crypto/SHA2Native.lean` for where
that equality is measured. A refusal from the extern (an empty result, which
is never a chaining value) falls back to the pure walk, so this function
computes the specification fold whatever the extern answers. -/
def nativeBlockFold256 : L4Factoidal.Crypto.BlockFold256 :=
  ⟨fun h data offset blocks =>
    if blocks == 0 then h
    else
      let next := L4Factoidal.Crypto.sha256BlocksHacl (wordsToStateBytes h) data
                    offset.toUSize blocks.toUSize
      if next.size == 32 then stateBytesToWords next
      else L4Factoidal.Crypto.processBlocks256At h data offset blocks⟩

end Harness
