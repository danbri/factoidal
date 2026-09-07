/-
L4Factoidal.Crypto.ChaChaPoly — the ChaCha20-Poly1305 AEAD (RFC 8439)
bound to HACL* through Lean's C FFI. THE FOURTH MEMBER OF THE LEAN
TREE'S `@[extern]` CRYPTO FAMILY (`Crypto/Ed25519.lean`,
`Crypto/SHA2Native.lean`, `Crypto/P256Native.lean` and
`Crypto/RsaNative.lean` are the others).

It exists for the XMPP client role and group end-to-end encryption
(`docs/designissues/2026-09-07-crypto-primitives.md`): MLS ciphersuite 3
is DHKEM(X25519, HKDF-SHA256) with HKDF-SHA256, ChaCha20-Poly1305 and
Ed25519, and HPKE (RFC 9180) uses the same AEAD as its sealing
primitive.

## Crypto policy

`skills/crypto-policy/SKILL.md`: this project never writes a primitive.
An AEAD protects SECRETS, so the pure-Lean route the policy allows for
digests over PUBLIC data is not available here even in principle — a
pure Lean ChaCha20 or Poly1305 would leak through the interpreter's
timing and through `Nat` allocation. There is exactly one implementation
and it is HACL*'s.

## Trust statement

`seal` and `open?` are built on `opaque`s: Lean knows their TYPE and
nothing about their VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT THEY
COMPUTE. `#print axioms` on every theorem of the library still reports
only `propext`, `Classical.choice`, `Quot.sound`.

What is trusted, and by whom:

  * ChaCha20-Poly1305 as implemented by HACL*
    (`third_party/hacl/src/Hacl_AEAD_Chacha20Poly1305.c` over
    `Hacl_Chacha20.c` and `Hacl_MAC_Poly1305.c`, entry points
    `Hacl_AEAD_Chacha20Poly1305_encrypt` and `_decrypt`), extracted by
    KaRaMeL from F*/Low* code proved memory-safe and functionally
    correct against the specification by Project Everest. Vendored
    unmodified from cryspen/hacl-packages commit
    05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 (2024-09-30), Apache-2.0 —
    `third_party/hacl/PROVENANCE.md`. The PORTABLE scalar unit was
    taken; the Simd128 and Simd256 units need target intrinsics that
    wasm32 does not have.
  * The tag comparison on the open path is HACL*'s own and is the only
    one in this path. `ffi/hacl_chachapoly.c` does not compare tags and
    must never grow a comparison, because a hand-written one would not
    be constant time.
  * `ffi/hacl_chachapoly.c`: length checks, one pointer offset for the
    `ciphertext || tag` split, and a `memset` of the output on
    authentication failure. No arithmetic on secrets.

What we do NOT check, and where it is checked instead:

  * NONCE REUSE. Encrypting two different plaintexts under the same
    (key, nonce) pair destroys the confidentiality AND the
    authentication of both, and nothing in this module can see it: it
    holds no state. The nonce discipline belongs to the protocol layer
    that owns the key schedule (OMEMO's double ratchet, MLS's sender
    data key, HPKE's own sequence counter, which
    `Crypto/Hpke.lean` gets from HACL*'s context rather than
    reimplementing). A caller that generates nonces itself must not use
    a counter it cannot prove is unique.
  * Any binding of the associated data to a protocol meaning. `aad` is
    passed through unexamined.
  * That the key is secret, or was derived at all. See `Crypto/Hkdf.lean`.

## Contract

  * `seal key nonce aad plain` → `some (ciphertext || tag)`, of size
    `plain.size + 16`, when `key` is 32 bytes and `nonce` is 12 bytes;
    `none` on any other length. The 16-byte Poly1305 tag is APPENDED,
    which is the layout RFC 8439 §2.8, HPKE, OMEMO and MLS all use.
  * `open? key nonce aad ct` → `some plain` when `key` is 32 bytes,
    `nonce` is 12 bytes, `ct` is at least 16 bytes and the tag
    authenticates; `none` on any length refusal AND on a failed tag.
    The two are deliberately the same answer to the caller: a decryption
    that did not happen has no plaintext, whatever the reason.

A `#guard` cannot check any of this. `#guard` runs in the Lean
INTERPRETER, which cannot call an `@[extern]` symbol, so the RFC 8439
§2.8.2 vector is checked at RUN time by `lake exe l4crypto-probe`
(section `rfc8439`) rather than at build time — the same arrangement
`Crypto/SHA2Native.lean` and `Crypto/P256Native.lean` already document
for their externs. The probe also runs the whole Wycheproof
`chacha20_poly1305_test.json` corpus, and re-runs every `valid` vector
with one ciphertext bit flipped, which must fail to open.
-/

namespace L4Factoidal.Crypto.ChaChaPoly

/-- Nonce length in bytes, RFC 8439 §2.8: 96 bits. -/
def nonceBytes : Nat := 12

/-- Key length in bytes, RFC 8439 §2.8: 256 bits. -/
def keyBytes : Nat := 32

/-- Poly1305 tag length in bytes, RFC 8439 §2.8: 128 bits. -/
def tagBytes : Nat := 16

/-- Raw seal: `ciphertext || tag`, or the EMPTY `ByteArray` on a length
refusal. Prefer `aeadSeal`, which turns the refusal into `none`. -/
@[extern "l4_hacl_chachapoly_seal"]
opaque sealRaw (key : @& ByteArray) (nonce : @& ByteArray) (aad : @& ByteArray)
    (plain : @& ByteArray) : ByteArray

/-- Raw open: `plaintext || status`, where `status` is the single last
byte, `1` for an authenticated decryption and `0` for a rejected tag; or
the EMPTY `ByteArray` on a length refusal. Prefer `open?`. -/
@[extern "l4_hacl_chachapoly_open"]
opaque openRaw (key : @& ByteArray) (nonce : @& ByteArray) (aad : @& ByteArray)
    (ct : @& ByteArray) : ByteArray

/-- AEAD seal (RFC 8439 §2.8). `none` unless `key` is 32 bytes and
`nonce` is 12 bytes. The result is `ciphertext || tag`, 16 bytes longer
than `plain`. -/
def aeadSeal (key nonce aad plain : ByteArray) : Option ByteArray :=
  if key.size ≠ keyBytes ∨ nonce.size ≠ nonceBytes then none
  else
    let out := sealRaw key nonce aad plain
    if out.size = plain.size + tagBytes then some out else none

/-- AEAD open (RFC 8439 §2.8). `none` on a length refusal AND on a tag
that does not authenticate; the caller is given no way to tell those
apart, because neither yields a plaintext. -/
def open? (key nonce aad ct : ByteArray) : Option ByteArray :=
  if key.size ≠ keyBytes ∨ nonce.size ≠ nonceBytes ∨ ct.size < tagBytes then none
  else
    let raw := openRaw key nonce aad ct
    let n := ct.size - tagBytes
    if raw.size ≠ n + 1 then none
    else if raw.get! n ≠ 1 then none
    else some (raw.extract 0 n)

end L4Factoidal.Crypto.ChaChaPoly
