/-
L4Factoidal.Crypto.Ed25519 — the Ed25519 signature primitive, bound to
HACL* through Lean's C FFI. THE FIRST MEMBER OF THE LEAN TREE'S
`@[extern]` CRYPTO FAMILY, WHICH HAS TWO: these three Ed25519
declarations and `sha256Hacl` (`Crypto/SHA2Native.lean`), all realised
by `ffi/hacl_ed25519.c` over the same vendored HACL* C.
(`Harness/PosixRangeIO.lean` also declares externs — `pread` and the
atomic-write host adapters — but those are POSIX I/O, not crypto, and
are a separate family outside the verified library.)

Port of the three crypto `assume val`s of `formal/fstar/VC.DataIntegrity.fst`
(`ed25519_secret_to_public`, `ed25519_sign`, `ed25519_verify`), which the
F* tree realises over the same vendored HACL* C
(`experimental_ocaml_glue/hacl_stubs.c`). The fourth `assume val` there,
`hash_sha256_hex`, is not bound HERE: SHA-256's specification is pure
Lean (`Crypto/SHA2.lean`, FIPS 180-4 vectors as `#guard`s) under the
crypto-policy skill's two-tier rule — hashes over public data may be
pure Lean; anything touching a secret must be HACL*. `Crypto/
SHA2Native.lean` adds a HACL*-backed SHA-256 ALONGSIDE it, for hosts
that must hash tens of megabytes of public block bytes; the pure
function stays the specification and stays what every `#guard` and
every theorem evaluates.

## Trust statement

These three declarations are `opaque`: Lean knows their TYPE and nothing
about their VALUE. No theorem in this tree depends on what they compute;
the one theorem that mentions verification (`VC/Theorems.lean`,
`verifyFromCanonical_createFromCanonical`) takes the signature scheme's
correctness — `verify pk m (sign sk m) = true` — as an explicit
HYPOTHESIS, so the assumption is visible in the theorem statement rather
than hidden in an axiom. `#print axioms` on every theorem of the library
still reports only `propext`, `Classical.choice`, `Quot.sound`.

What is trusted, and by whom:

  * RFC 8032 Ed25519 as implemented by HACL* (`third_party/hacl/src/
    Hacl_Ed25519.c`, `Hacl_Curve25519_51.c`, `Hacl_Hash_SHA2.c` for the
    internal SHA-512), extracted by KaRaMeL from F*/Low* code proved
    memory-safe, functionally correct against the RFC specification, and
    secret-independent by Project Everest. Vendored unmodified from
    cryspen/hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2
    (2024-09-30), Apache-2.0 — `third_party/hacl/PROVENANCE.md`.
  * `formal/lean4/ffi/hacl_ed25519.c`, 60 lines of length checks and
    `lean_sarray` plumbing, written here, reviewable by eye, containing
    no arithmetic.
  * The Lean C FFI convention itself: a `@&` (borrowed) `ByteArray` is a
    `b_lean_obj_arg`, a returned `ByteArray` is a fresh `lean_obj_res`, a
    `Bool` is a `uint8_t`.

What is measured, not trusted: `Harness/VcProbe.lean` runs the RFC 8032
§7.1 test vectors (TEST 1, 2, 3, 1024) through all three bindings at
run time — `secretToPublic` against the published public key, `sign`
against the published signature (Ed25519 is deterministic), `verify` on
the published triple and on a one-byte-flipped signature — and prints
the result as a score line. Externs do not evaluate at compile time, so
this cannot be a `#guard`; it is the probe's first section for that
reason.

## Contract (what the C side guarantees, and what it refuses)

  * `secretToPublic sk`: 32-byte `sk` → 32-byte public key. Any other
    input length → the EMPTY `ByteArray` (a refusal, never a key).
  * `sign sk msg`: 32-byte `sk`, any `msg` up to 2^32-1 bytes → 64-byte
    signature. Wrong `sk` length or over-long `msg` → EMPTY.
  * `verify pk msg sig`: `true` only when `pk` is 32 bytes, `sig` is 64
    bytes, and HACL* accepts the signature over `msg`. Every
    length refusal is `false`. There is no "unknown" answer and no
    success-by-default path: a verifier that returned `true` without a
    real check would be a security hole, not a degradation.

Every consumer above this module (`VC/DataIntegrity.lean`) takes the
signing and verifying functions as PARAMETERS, so the algorithm is a
total function of explicit inputs and `#guard`s can exercise it with a
stub verifier. Only the probe (and any future executable edge) passes
these opaques in.
-/

namespace L4Factoidal.Crypto.Ed25519

/-- Ed25519 public key of a 32-byte secret key (RFC 8032 §5.1.5), via
HACL* `Hacl_Ed25519_secret_to_public`. Empty result = wrong input length. -/
@[extern "l4_hacl_ed25519_secret_to_public"]
opaque secretToPublic (sk : @& ByteArray) : ByteArray

/-- Ed25519 signature (RFC 8032 §5.1.6, deterministic) of `msg` under
the 32-byte secret key, via HACL* `Hacl_Ed25519_sign`. Empty result =
wrong key length or over-long message. -/
@[extern "l4_hacl_ed25519_sign"]
opaque sign (sk : @& ByteArray) (msg : @& ByteArray) : ByteArray

/-- Ed25519 verification (RFC 8032 §5.1.7) via HACL* `Hacl_Ed25519_verify`.
`false` on any length refusal (pk ≠ 32 bytes, sig ≠ 64 bytes) as well as
on a rejected signature. -/
@[extern "l4_hacl_ed25519_verify"]
opaque verify (pk : @& ByteArray) (msg : @& ByteArray) (sig : @& ByteArray) : Bool

end L4Factoidal.Crypto.Ed25519
