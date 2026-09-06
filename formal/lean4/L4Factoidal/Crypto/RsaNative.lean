/-
L4Factoidal.Crypto.RsaNative — the RSA PUBLIC operation (RFC 8017 §5.2.2,
RSAVP1) bound to HACL*'s generic 64-bit bignum field through Lean's C
FFI. THE FOURTH MEMBER OF THE LEAN TREE'S `@[extern]` CRYPTO FAMILY
(`Crypto/Ed25519.lean`, `Crypto/SHA2Native.lean`, `Crypto/P256Native.lean`
are the others).

It exists for JWS `RS256` (RFC 7518 §3.3), which Solid-OIDC identity
providers still issue.

## What this module is, and what it deliberately is not

It is modular exponentiation `s^e mod n` over public data, and nothing
else. It is NOT an RSA signature verifier. The padding — EMSA-PKCS1-v1_5,
RFC 8017 §9.2 — is generated and compared in pure Lean
(`JOSE/Pkcs1.lean`), where it carries theorems, and this module makes no
decision about whether a signature is valid.

That split is the point. The Bleichenbacher 2006 forgery class (and its
2019/2021 repetitions) comes from a verifier that PARSES the padding and
skips trailing bytes. Nothing in this project parses PKCS#1 padding:
`Pkcs1.emsaEncode` builds the whole `k`-byte template and
`Pkcs1.rs256Verify` compares the full `k` bytes for equality. There is
no code path that could be lenient, and `Pkcs1.rs256Verify_iff_template`
states that as a theorem.

There is no private operation, no key generation and no signing entry
point here or in `ffi/hacl_rsa.c`, so no secret reaches this path.

## Crypto policy

`skills/crypto-policy/SKILL.md`, Lean 4 tree amendment, item 2. The
arithmetic is HACL*'s; we never write our own. Variable-time modular
exponentiation (`Hacl_Bignum64_mod_exp_vartime`) is used deliberately:
the exponent is the RSA PUBLIC exponent and the base is the published
signature, so a timing observer learns only values already carried in the
token. The constant-time variant is the one required if a private
exponent is ever introduced, which this module forbids by construction.

## Trust statement

`rsaPublicOp` is `opaque`: Lean knows its TYPE and nothing about its
VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT IT COMPUTES.
`Pkcs1.rs256Verify` takes the public operation as a PARAMETER, so every
theorem about RS256 verification is stated over an arbitrary function of
that type and holds whatever HACL* returns; the opaque is passed in only
at the executable edge. `#print axioms` reports only the three standard
axioms on all of them.

What is trusted, and by whom:

  * HACL*'s verified bignum arithmetic (`third_party/hacl/src/
    Hacl_Bignum64.c` and `Hacl_Bignum.c`, entry points
    `Hacl_Bignum64_new_bn_from_bytes_be`, `Hacl_Bignum64_mod_exp_vartime`,
    `Hacl_Bignum64_bn_to_bytes_be`), extracted by KaRaMeL from F*/Low*
    code proved memory-safe and functionally correct by Project Everest.
    Vendored unmodified from cryspen/hacl-packages commit
    05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 (2024-09-30), Apache-2.0 —
    `third_party/hacl/PROVENANCE.md`.
  * `formal/lean4/ffi/hacl_rsa.c`: length checks, a big-endian bit-length
    count over the PUBLIC exponent, one right-alignment `memcpy`, and the
    three HACL* calls. No modular arithmetic of its own.

What we do NOT check:

  * That `n` is a real RSA modulus (a product of two primes). A caller
    who trusts a hostile JWK gets a hostile answer; key trust is the
    Solid-OIDC issuer-pinning layer's job (`JOSE/Jwt.lean`), not this
    one.
  * That `e` is one of the common exponents. RFC 8017 does not require
    it. A pathological `e` costs time, not soundness.
  * Anything about the padding. See above.

## Contract

`rsaPublicOp n e s`, with `k = n.size`:

  * `some res` with `res.size = k` when `k` is 256, 384 or 512 bytes
    (2048, 3072 or 4096 bits), `s.size = k`, `e` is non-empty, at most
    `k` bytes and has a set bit, and HACL*'s own preconditions hold
    (`n` odd, `n > 1`, `s < n`).
  * `none` otherwise. `s ≥ n` is RFC 8017's "signature representative
    out of range" and lands here, which is the specified rejection.

Modulus sizes below 2048 bits are REFUSED rather than supported. RFC 7518
§3.3 requires a key of at least 2048 bits for RS256, and a verifier that
accepts a 1024-bit modulus is a downgrade target.
-/

namespace L4Factoidal.Crypto.Rsa

/-- The RSA public operation `s^e mod n` (RFC 8017 §5.2.2 RSAVP1) via
HACL* `Hacl_Bignum64_mod_exp_vartime`, over big-endian byte strings.

`n`, `e` and `s` are big-endian unsigned integers; the result, when
present, is `n.size` bytes big-endian. `none` is every refusal: a modulus
that is not 2048, 3072 or 4096 bits, a signature of the wrong length or
not less than the modulus, an empty or zero exponent, an even modulus, or
an allocation failure. This is NOT a signature check — see
`JOSE/Pkcs1.lean`. -/
@[extern "l4_hacl_rsa_public_op"]
opaque rsaPublicOpRaw (n : @& ByteArray) (e : @& ByteArray)
    (s : @& ByteArray) : ByteArray

/-- `rsaPublicOpRaw` with its empty-means-refusal convention read into
`Option`. A successful result is always exactly `n.size` bytes, and
`n.size` is never zero for an accepted modulus, so the empty `ByteArray`
is unambiguously a refusal. -/
def rsaPublicOp (n e s : ByteArray) : Option ByteArray :=
  let r := rsaPublicOpRaw n e s
  if r.size == 0 then none else some r

end L4Factoidal.Crypto.Rsa
