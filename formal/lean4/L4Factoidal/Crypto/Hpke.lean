/-
L4Factoidal.Crypto.Hpke — Hybrid Public Key Encryption (RFC 9180),
single-shot BASE mode, ciphersuite DHKEM(X25519, HKDF-SHA256) /
HKDF-SHA256 / ChaCha20-Poly1305, bound to HACL* through Lean's C FFI.

That ciphersuite is the one RFC 9180 Appendix A.1 gives vectors for, and
its KEM, KDF and AEAD are exactly MLS ciphersuite 3's
(`MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519`), which is why it
is the one vendored. See
`docs/designissues/2026-09-07-crypto-primitives.md`.

## MODES: BASE ONLY

The vendored translation unit
`third_party/hacl/src/Hacl_HPKE_Curve51_CP32_SHA256.c` exports
`setupBaseS`, `setupBaseR`, `sealBase` and `openBase`, and NOTHING ELSE.
The pinned release ships no `mode_psk` (1), `mode_auth` (2) or
`mode_auth_psk` (3) entry point for this ciphersuite. This module
therefore covers RFC 9180 `mode_base` (0) only, and does not emulate the
others: an emulation would be a hand-written key schedule, which the
crypto policy forbids. A caller needing PSK or authenticated modes has
nothing here to call, deliberately.

Single-shot only, likewise: `Seal(pkR, info, aad, pt)` and
`Open(enc, skR, info, aad, ct)` of RFC 9180 §6.1. The multi-message
context API (`ContextS.Seal` with its own sequence number) is not
exposed, because HACL*'s context struct is a C value this shim would
have to own across calls, and no caller in this tree needs it yet.

## Crypto policy

`skills/crypto-policy/SKILL.md`: HACL* only. Everything in RFC 9180 —
the KEM, the key schedule, the AEAD — is HACL*'s C. Nothing in this
module or in `ffi/hacl_hpke.c` derives, mixes or compares a key.

## Trust statement

`sealBaseRaw` and `openBaseRaw` are `opaque`: Lean knows their TYPE and
nothing about their VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT THEY
COMPUTE.

Trusted: HPKE as implemented by HACL*
(`Hacl_HPKE_Curve51_CP32_SHA256_sealBase` / `_openBase` over
`Hacl_Curve25519_51.c`, `Hacl_HKDF.c`, `Hacl_HMAC.c`,
`Hacl_AEAD_Chacha20Poly1305.c`), extracted by KaRaMeL from F*/Low* code
proved by Project Everest, vendored unmodified from
cryspen/hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2 —
`third_party/hacl/PROVENANCE.md`. And `ffi/hacl_hpke.c`, which is length
checks and one concatenation.

What we do NOT check:

  * That `skE` was freshly generated. RFC 9180's security depends on the
    ephemeral private key being used ONCE and being unpredictable. This
    module takes it as an argument so the RFC 9180 Appendix A.1 vectors
    can be reproduced exactly; production callers must pass a fresh
    random 32 bytes from the host's CSPRNG, never a stored value.
  * That `info` binds the encryption to a context. RFC 9180 §5.1 leaves
    the meaning of `info` to the application.
  * That `pkR` belongs to the intended recipient. There is no identity
    layer here.

## Wire format

`sealBase` returns `enc || ciphertext || tag` in ONE buffer:

  * `enc` — 32 bytes, the KEM encapsulated key (an X25519 public key).
  * `ciphertext` — as long as the plaintext.
  * `tag` — 16 bytes, ChaCha20-Poly1305.

so the result is `32 + plaintext.size + 16` bytes, and `openBase?` takes
exactly that buffer back. RFC 9180 itself transmits `enc` and `ct`
separately; joining them is this module's calling convention, stated
here because guessing it is a bug, and `encBytes` / `tagBytes` let a
caller split them.

## Test vectors

A `#guard` cannot check any of this: `#guard` runs in the Lean
interpreter, which cannot call an `@[extern]` symbol. The RFC 9180
Appendix A.1 vectors are therefore checked at RUN time by
`lake exe l4crypto-probe` (section `rfc9180-a1`), which reproduces the
Appendix A.1 encryption from its own `skEm` and `pkRm` and compares
`enc` and `ct` to the published bytes, then opens them again with
`skRm`, then re-opens with one ciphertext bit flipped and requires
failure.
-/

namespace L4Factoidal.Crypto.Hpke

/-- The KEM encapsulated key is an X25519 public key: 32 bytes
(RFC 9180 §7.1, `Nenc` for DHKEM(X25519, HKDF-SHA256)). -/
def encBytes : Nat := 32

/-- ChaCha20-Poly1305 tag length, RFC 9180 §7.3 `Nt`. -/
def tagBytes : Nat := 16

/-- X25519 private and public keys are 32 bytes each. -/
def keyBytes : Nat := 32

/-- Raw single-shot base-mode seal: `enc || ciphertext || tag`, or the
EMPTY `ByteArray` on a length refusal or a HACL* failure (which for
`sealBase` means an invalid recipient public key). Prefer `sealBase`. -/
@[extern "l4_hacl_hpke_seal_base"]
opaque sealBaseRaw (skE : @& ByteArray) (pkR : @& ByteArray) (info : @& ByteArray)
    (aad : @& ByteArray) (plain : @& ByteArray) : ByteArray

/-- Raw single-shot base-mode open: `plaintext || status`, `status` the
single last byte, `1` on success and `0` on failure; EMPTY on a length
refusal. Prefer `openBase?`. -/
@[extern "l4_hacl_hpke_open_base"]
opaque openBaseRaw (skR : @& ByteArray) (info : @& ByteArray) (aad : @& ByteArray)
    (encCt : @& ByteArray) : ByteArray

/-- RFC 9180 §6.1 `SealBase`, single shot. `skE` is the EPHEMERAL private
key: fresh random 32 bytes in production, and the Appendix A.1 `skEm`
only when reproducing a vector. Result: `enc || ciphertext || tag`,
`32 + plain.size + 16` bytes. `none` on a wrong key length and on an
invalid `pkR`. -/
def sealBase (skE pkR info aad plain : ByteArray) : Option ByteArray :=
  if skE.size ≠ keyBytes ∨ pkR.size ≠ keyBytes then none
  else
    let out := sealBaseRaw skE pkR info aad plain
    if out.size = encBytes + plain.size + tagBytes then some out else none

/-- RFC 9180 §6.1 `OpenBase`, single shot, over the `enc || ciphertext ||
tag` buffer `seal` produced. `none` on a wrong key length, a buffer too
short to hold `enc` and a tag, AND on a tag that does not authenticate;
the caller is given no way to tell those apart, because none of them
yields a plaintext. -/
def openBase? (skR info aad encCt : ByteArray) : Option ByteArray :=
  if skR.size ≠ keyBytes ∨ encCt.size < encBytes + tagBytes then none
  else
    let raw := openBaseRaw skR info aad encCt
    let n := encCt.size - encBytes - tagBytes
    if raw.size ≠ n + 1 then none
    else if raw.get! n ≠ 1 then none
    else some (raw.extract 0 n)

/-- The 32-byte KEM encapsulated key of a `sealBase` result. `none` if the
buffer is too short to carry one. -/
def encOf? (b : ByteArray) : Option ByteArray :=
  if b.size < encBytes then none else some (b.extract 0 encBytes)

/-- The `ciphertext || tag` part of a `sealBase` result. -/
def ciphertextOf? (b : ByteArray) : Option ByteArray :=
  if b.size < encBytes + tagBytes then none else some (b.extract encBytes b.size)

end L4Factoidal.Crypto.Hpke
