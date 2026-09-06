/-
L4Factoidal.Crypto.P256Native — NIST P-256 ECDSA verification bound to
HACL* through Lean's C FFI. THE THIRD MEMBER OF THE LEAN TREE'S
`@[extern]` CRYPTO FAMILY (the first is `Crypto/Ed25519.lean`, the second
`Crypto/SHA2Native.lean`).

It exists for JWS `ES256` (RFC 7518 §3.4), which Solid-OIDC access
tokens and RFC 9449 DPoP proofs use.

## Crypto policy

`skills/crypto-policy/SKILL.md`, Lean 4 tree amendment, item 2:
signature primitives come from HACL* via FFI ONLY, never a hand-written
Lean implementation. This module adds a member to that family and
follows the same three obligations it names: a module-header trust
statement (below), a shim with no arithmetic (`ffi/hacl_p256.c`), and a
run-time vector check in a probe (`lake exe l4jose-probe`, which runs
Wycheproof `ecdsa_secp256r1_sha256_p1363_test.json` and the RFC 7515
Appendix A.3 example).

## Trust statement

`p256VerifySha256` is `opaque`: Lean knows its TYPE and nothing about its
VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT IT COMPUTES. The JOSE
theorems (`JOSE/Theorems.lean`) are about which verifier is REACHED for a
given header and key — algorithm confusion, key-type confusion, the
allowlist — and they hold whatever the verifier returns; the verifier is
a parameter or an opaque leaf in every one of them. `#print axioms` on
each still reports only `propext`, `Classical.choice`, `Quot.sound`.

What is trusted, and by whom:

  * ECDSA over NIST P-256 with SHA-256, as implemented by HACL*
    (`third_party/hacl/src/Hacl_P256.c`, entry point
    `Hacl_P256_ecdsa_verif_p256_sha2`, with `Hacl_Hash_SHA2.c` for the
    digest), extracted by KaRaMeL from F*/Low* code proved memory-safe
    and functionally correct against the specification by Project
    Everest. Vendored unmodified from cryspen/hacl-packages commit
    05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 (2024-09-30), Apache-2.0 —
    `third_party/hacl/PROVENANCE.md`.
  * `formal/lean4/ffi/hacl_p256.c`: two length checks and one pointer
    offset, containing no arithmetic.
  * The Lean C FFI convention: a `@&` (borrowed) `ByteArray` is a
    `b_lean_obj_arg`, a `Bool` is a `uint8_t`.

What we do NOT check, and where it is checked instead:

  * That the message bytes are the JWS signing input
    `ASCII(BASE64URL(protected) || '.' || BASE64URL(payload))`. That
    assembly is `JOSE/Jws.lean`, in Lean, with theorems.
  * That the caller MEANT ES256. The algorithm allowlist and the
    key-type match are `JOSE/Jws.lean`; this module is reached only
    through `Alg.es256` with a `Jwk.ec` key.
  * Signature malleability (`s` and `n - s` both verifying). ECDSA is
    malleable by design and JWS does not require a low-`s` form, so this
    is not a check we may add. A caller that needs signature uniqueness
    must not use ECDSA.

## Calling-convention match, stated because guessing here is a bug

RFC 7518 §3.4 fixes the ES256 signature as `R || S`, two 32-byte
big-endian integers, 64 bytes total — NOT the ASN.1 DER `SEQUENCE` that
X.509 and TLS use. HACL* takes `signature_r` and `signature_s` as two
32-byte big-endian buffers, so the conversion is a pointer offset and
there is no DER parser anywhere in this path. The public key is `x || y`,
64 raw bytes, which is the concatenation of the base64url-decoded JWK
`x` and `y` members (`JOSE/Jwk.lean` builds it, and a `#guard` there
pins the RFC 7515 Appendix A.3 key). HACL* hashes the message itself
with SHA-256; the caller passes the signing input, never a digest.

## Contract

  * `p256VerifySha256 pubXY msg sig`: `true` only when `pubXY` is 64
    bytes and a valid curve point, `sig` is 64 bytes, and HACL* accepts
    `(r, s)` over SHA-256 of `msg`. Every length refusal is `false`.
    There is no "unknown" answer and no success-by-default path.
  * `p256ValidatePublicKey pubXY`: `true` when `pubXY` is 64 bytes and
    the point is on the curve and is not the point at infinity.
-/

namespace L4Factoidal.Crypto.P256

/-- ECDSA-P256-SHA256 verification (RFC 6979 / FIPS 186-4, as used by JWS
`ES256`, RFC 7518 §3.4) via HACL* `Hacl_P256_ecdsa_verif_p256_sha2`.

`pubXY` is the raw 64-byte `x || y` public key; `sig` is the raw 64-byte
`r || s` JWS signature; `msg` is the JWS signing input, unhashed. `false`
on any length refusal, on an invalid public key, and on a rejected
signature. -/
@[extern "l4_hacl_p256_verify_sha256"]
opaque p256VerifySha256 (pubXY : @& ByteArray) (msg : @& ByteArray)
    (sig : @& ByteArray) : Bool

/-- Point validity of a raw 64-byte `x || y` P-256 public key, via HACL*
`Hacl_P256_validate_public_key`. `false` on a wrong length, a point off
the curve, or the point at infinity. -/
@[extern "l4_hacl_p256_validate_public_key"]
opaque p256ValidatePublicKey (pubXY : @& ByteArray) : Bool

end L4Factoidal.Crypto.P256
