/-
L4Factoidal.Crypto.SHA2Native — SHA-256 bound to HACL* through Lean's C
FFI. THE SECOND MEMBER OF THE LEAN TREE'S `@[extern]` CRYPTO FAMILY
(the first is `L4Factoidal/Crypto/Ed25519.lean`).

This module does NOT replace `L4Factoidal/Crypto/SHA2.lean`. That pure
Lean `sha256` stays the SPECIFICATION and stays what every `#guard`,
every theorem and every WASM operation evaluates: build-time `#guard`s
run in the Lean interpreter, which cannot call an extern, so an
`@[implemented_by]` on `sha256` would break the FIPS 180-4 vectors that
`Crypto/SHA2Tests.lean` checks at build time. The two functions live
side by side and the host chooses, per call site, which one to pass in
(`Storage/BlockMerkle.lean`'s `Hasher` parameter).

Why it exists: Merkle admission of a persisted Shardborough store
hashes every 65,536-byte chunk of every artifact. The pure Lean
`sha256` runs at roughly 5 MB/s, and a full read or an activation of a
25 MB store spends about half its wall clock inside `nextLevel`,
`sha256`, `processBlocks256` and `sha256CompressBlock`. HACL*'s
extracted C is the same primitive at C speed, on data that is already
public.

## Crypto policy

`skills/crypto-policy/SKILL.md`, Lean 4 tree amendment: hashes over
PUBLIC data may be pure Lean; anything touching a SECRET must be
HACL*. Block bytes on disk are public, so the pure implementation was
and remains admissible there — this binding is a speed choice, not a
policy correction. Nothing here weakens the rule that we never write
our own primitive: the C is HACL*'s, vendored unmodified.

## Trust statement

`sha256Hacl` is `opaque`: Lean knows its TYPE and nothing about its
VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT IT COMPUTES. Every
`#guard` and every proof about digests, Merkle leaves, nodes and roots
is stated over `Crypto.sha256` (equivalently, over
`BlockMerkle.pureHasher`), and `#print axioms` on every theorem of the
library still reports only `propext`, `Classical.choice`, `Quot.sound`.

What is trusted, and by whom:

  * FIPS 180-4 SHA-256 as implemented by HACL* (`third_party/hacl/src/
    Hacl_Hash_SHA2.c`, entry point `Hacl_Hash_SHA2_hash_256`),
    extracted by KaRaMeL from F*/Low* code proved memory-safe and
    functionally correct against the specification by Project Everest.
    Vendored unmodified from cryspen/hacl-packages commit
    05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 (2024-09-30), Apache-2.0
    — `third_party/hacl/PROVENANCE.md`. The same translation unit was
    already compiled and linked (native `extern_lib libl4hacl`, and
    `Wasm/build-wasm.sh`) because Ed25519 needs SHA-512 internally.
  * `formal/lean4/ffi/hacl_ed25519.c`, whose `l4_hacl_sha256` entry is
    one length check and `lean_sarray` plumbing, containing no
    arithmetic.
  * The Lean C FFI convention: a `@&` (borrowed) `ByteArray` is a
    `b_lean_obj_arg`, a returned `ByteArray` is a fresh `lean_obj_res`.

## The obligation this module carries

`sha256Hacl` MUST agree with `Crypto.sha256` on every input. That
cannot be proved here — one side is opaque — so it is MEASURED:
`Harness/VcProbe.lean` (`lake exe l4vc-probe`) runs a `sha256 differential`
section comparing the two functions on the FIPS 180-4 vectors, on the
empty input, on inputs of 1, 55, 56, 63, 64 and 65 bytes (the SHA-256
block and padding boundaries), and on a 1 MiB deterministic buffer.
The probe exits non-zero on any mismatch, so the agreement is a CI
gate rather than an assumption. Externs do not evaluate at compile
time, which is why this is a probe and not a `#guard`.

## Contract

  * `sha256Hacl m` → the 32-byte SHA-256 digest of `m`.
  * A message longer than 2^32-1 bytes is REFUSED with the EMPTY
    `ByteArray` (HACL*'s length parameter is a `uint32_t`). An empty
    result is never a digest: the digest of the empty message is 32
    bytes, so callers can distinguish a refusal by size.
-/

namespace L4Factoidal.Crypto

/-- SHA-256 (FIPS 180-4) via HACL* `Hacl_Hash_SHA2_hash_256`. Extensionally
equal to the pure `Crypto.sha256` on every message of at most 2^32-1 bytes;
that equality is measured by `l4vc-probe`, not proved. A message above that
length returns the EMPTY `ByteArray` (a refusal, never a digest). -/
@[extern "l4_hacl_sha256"]
opaque sha256Hacl (m : @& ByteArray) : ByteArray

end L4Factoidal.Crypto
