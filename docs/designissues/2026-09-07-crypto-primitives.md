# Crypto primitives for the XMPP client role and group encryption

2026-09-07. Companion to
[`2026-09-07-attestation-and-adversarial-server.md`](2026-09-07-attestation-and-adversarial-server.md)
§6, which set the requirement: OMEMO 0.8 uses AES-128-GCM; MLS
ciphersuite 3 is DHKEM(X25519, HKDF-SHA256) with ChaCha20-Poly1305 and
Ed25519; HPKE is RFC 9180.

Owner instruction, 2026-09-07, verbatim: "Vendor those AEADs please, and
any other obvious bits needed for client role as sketched or server for
that matter."

## What landed

| Primitive | HACL\* unit | Lean module | Portable | Builds for wasm32 |
|---|---|---|---|---|
| ChaCha20-Poly1305 (RFC 8439) | `Hacl_AEAD_Chacha20Poly1305.c`, `Hacl_Chacha20.c`, `Hacl_MAC_Poly1305.c` | [`Crypto/ChaChaPoly.lean`](../../formal/lean4/L4Factoidal/Crypto/ChaChaPoly.lean) | yes (scalar) | yes |
| HMAC-SHA-256 (RFC 2104) | `Hacl_HMAC.c` | [`Crypto/Hkdf.lean`](../../formal/lean4/L4Factoidal/Crypto/Hkdf.lean) | yes | yes |
| HKDF-SHA-256 (RFC 5869) | `Hacl_HKDF.c` | `Crypto/Hkdf.lean` (and a pure Lean twin) | yes | yes |
| X25519 (RFC 7748) | `Hacl_Curve25519_51.c` (already vendored) | [`Crypto/X25519.lean`](../../formal/lean4/L4Factoidal/Crypto/X25519.lean) | yes | yes |
| HPKE base mode (RFC 9180) | `Hacl_HPKE_Curve51_CP32_SHA256.c` | [`Crypto/Hpke.lean`](../../formal/lean4/L4Factoidal/Crypto/Hpke.lean) | yes | yes |
| AES-128-GCM, AES-256-GCM | **none in the pinned release** | **not implemented** | — | — |

Link closure, not called by any Lean code: `Hacl_Hash_SHA1.c`,
`Hacl_Hash_Blake2s.c`, `Hacl_Hash_Blake2b.c`, `Lib_Memzero0.c`.
`Hacl_HMAC.c` is one translation unit covering every HMAC hash, so
linking it for HMAC-SHA-256 pulls its SHA-1 and BLAKE2 call targets in.

All from the pin the tree already used,
`cryspen/hacl-packages` `05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`. The
previously vendored headers were re-checked byte-identical to that commit
while these were added. File hashes and the reproduction command:
[`third_party/hacl/PROVENANCE.md`](../../third_party/hacl/PROVENANCE.md).

## AES-GCM is not implemented

Tracked in <https://github.com/danbri/factoidal/issues/677>.

The pinned release has no portable AES-GCM. Its only AES-GCM is reached
through `EverCrypt_AEAD.c`, whose every AES-GCM branch is inside
`#if HACL_CAN_COMPILE_VALE` and calls Vale x86-64 assembly (AES-NI plus
PCLMULQDQ) that the C distribution does not ship; with Vale absent those
entry points return `EverCrypt_Error_UnsupportedAlgorithm`.
`include/Hacl_AES128.h` declares `Hacl_AES128_*` symbols the release
never defines. There is no bitsliced constant-time AES in it.

The AES-NI variant was refused rather than taken: it does not build for
wasm32 and does not build on arm64 without intrinsics, so it would break
the wasm compatibility gate of
[`skills/crypto-policy/SKILL.md`](../../skills/crypto-policy/SKILL.md).
A per-architecture crypto path is not a thing this project ships.

⚠️ This blocks **OMEMO 0.8 and nothing else**. XEP-0384 version 0.8
specifies AES-128-GCM. MLS ciphersuite 3 and HPKE both use
ChaCha20-Poly1305, which is here.

Per the shortfall rule the gap is visible in a score line rather than
absent from one: `lake exe l4crypto-probe` has an `aes-gcm` section that
prints the reasoning, links issue 677, and counts the 316 vectors of
Wycheproof `aes_gcm_test.json` in a `NOT RUN` bucket that is never added
to `pass`. The `aeadSeal` / `aeadOpen` ABI ops likewise accept
`"alg":"aes-128-gcm"` as a NAMED refusal carrying that issue, so a
caller learns the primitive is missing instead of receiving a bare
"unknown alg".

## Two decisions worth stating

### HKDF exists twice, on purpose

`Crypto/Hkdf.lean` carries HKDF-SHA-256 as HACL\* externs AND as pure
Lean over the existing `Crypto.hmacSha256`. The crypto policy prefers
HACL\* for the primitive and HACL\* is what every runtime path uses. The
pure pair exists because a `#guard` runs in the Lean INTERPRETER, which
cannot call an `@[extern]` symbol, so the RFC 5869 Appendix A vectors can
only be build-time checks against a pure definition — and because the
wasm and interpreter surfaces need a definition Lean can unfold.

HKDF is not a new primitive under the policy: RFC 5869 §2 defines
extract as one HMAC call and expand as a chain of HMAC calls over a
counter, and the primitive under both is SHA-256. Same reading
`Crypto/Hmac.lean` already records for HMAC and PBKDF2.

The obligation that the two agree cannot be proved, because one side is
opaque. It is measured: `l4crypto-probe`'s `hmac-hkdf-differential`
section compares them byte for byte on the RFC 4231 HMAC vectors, the
RFC 5869 vectors, the block boundaries and every Wycheproof
`hkdf_sha256` vector, and exits non-zero on any mismatch.

### The RFC 7748 §6.1 abort is decided in Lean, not in C

An all-zero X25519 shared secret is what a low-order input point
produces. RFC 7748 §6.1 says protocols that need contributory behaviour
MAY abort on it, which makes it a PROTOCOL decision. So `ffi/hacl_kdf.c`
reports what the curve computed, `X25519.scalarmult` returns the raw
result, and `X25519.dh?` — what protocol code should call — answers
`none` on all-zero. Wycheproof marks those vectors `acceptable` for
exactly this reason, and the probe counts them in their own bucket while
separately checking that `dh?` aborts on all 31 `ZeroSharedSecret`
vectors.

## The ABI

Four ops in `Wasm/Dispatch.lean`, over
[`Wasm/Ops/Crypto.lean`](../../formal/lean4/Wasm/Ops/Crypto.lean). Byte
fields cross as **lowercase hex**, the same choice every other
byte-carrying op in this dispatch makes; an odd-length or non-hex field
is an error envelope, never a truncated buffer.

```
aeadSeal({"alg":"chacha20-poly1305","key":hex32,"nonce":hex12,
          "aad":hex,"plaintext":hex})
  -> {"ok":true,"ciphertext":hex}

aeadOpen({"alg":"chacha20-poly1305","key":hex32,"nonce":hex12,
          "aad":hex,"ciphertext":hex})
  -> {"ok":true,"plaintext":hex}

hpkeSeal({"skE":hex32,"pkR":hex32,"info":hex,"aad":hex,"plaintext":hex})
  -> {"ok":true,"message":hex,"enc":hex32,"ciphertext":hex}

hpkeOpen({"skR":hex32,"info":hex,"aad":hex,"message":hex})
  -> {"ok":true,"plaintext":hex}
```

`ciphertext` on the AEAD ops is `ciphertext || tag` — the tag is
appended, 16 bytes, and is not a separate member, because two members
let a caller reassemble them in the wrong order. `message` on the HPKE
ops is `enc || ciphertext || tag`; `enc` and `ciphertext` are the same
bytes split for a caller that transmits them separately as RFC 9180 §6.1
does, and `message == enc + ciphertext` always.

`aad` and `info` are optional and default to the empty byte string;
RFC 8439 and RFC 9180 both allow them empty.

⚠️ `skE` on `hpkeSeal` is the EPHEMERAL private key and MUST be fresh
random bytes from the host's CSPRNG for every call. It is an argument
because this ABI has no entropy source and because the RFC 9180
Appendix A.2 vectors have to be reproducible. Reusing one destroys the
security of every message sealed under it.

⚠️ Nonce reuse on `aeadSeal` is not detected and cannot be: the module
holds no state. Encrypting two different plaintexts under the same
(key, nonce) destroys the confidentiality AND the authentication of
both. The nonce discipline belongs to the protocol layer owning the key
schedule.

## HPKE: base mode only, single shot only

The vendored translation unit exports `setupBaseS`, `setupBaseR`,
`sealBase` and `openBase` and nothing else. The pinned release has no
`mode_psk`, `mode_auth` or `mode_auth_psk` entry point for this
ciphersuite, and none is emulated, because an emulation would be a
hand-written key schedule. The multi-message context API is likewise not
exposed, so sequence numbers above 0 are unreachable — which is why the
probe checks RFC 9180 Appendix A.2.1 sequence number 0 and not the five
later ones the appendix also lists.

## Scores, measured 2026-09-07

`lake exe l4crypto-probe`:

| Section | Result |
|---|---|
| `rfc8439` | 13 pass, 0 fail (out of 13) |
| `wycheproof-chacha20-poly1305` | 837 pass, 0 fail (out of 837) |
| `hmac-hkdf-differential` | 25 pass, 0 fail (out of 25) |
| `wycheproof-hkdf-sha256` | 172 pass, 0 fail (out of 172) |
| `wycheproof-x25519` | 299 pass, 0 fail, 254 acceptable (out of 553) |
| `rfc9180-a2` | 15 pass, 0 fail (out of 15) |
| `aes-gcm` | 0 pass, 0 fail, 316 NOT RUN (out of 316) |
| **TOTAL** | **1361 pass, 0 fail, 254 acceptable, 316 NOT RUN (out of 1931)** |

Denominators are checks, not vectors: every `valid` ChaCha20-Poly1305
vector earns three (open, re-seal, and open with a flipped ciphertext
bit that must fail), so 325 vectors give 837 checks. Every Wycheproof
`hkdf_sha256` vector earns two (the corpus expectation, and the pure
versus HACL\* agreement).

`x25519_test.json` has NO `invalid` bucket: 264 vectors are `valid` and
254 are `acceptable`, the latter being the low-order-point, twist and
non-canonical cases discussed above.

Unchanged by this landing, re-run to confirm: `l4jose-probe` 1077 pass,
0 fail, 3 acceptable (out of 1080); `l4vc-probe` 119 pass, 0 fail (out
of 119); `Wasm/native-smoke.sh` 128 pass, 0 fail (out of 128, eight of
them new).

Hygiene: `tools/lean-hygiene-audit.py` clean — 0 `sorry`, 0 user
`axiom`, 0 `native_decide`, 0 `unsafe`, 0 `@[implemented_by]`,
`partial def` at the 172 baseline.

## 🔴 The wasm module has NOT been rebuilt

`Wasm/build-wasm.sh` carries the ten new C units and the three new
shims, and `lake build` compiles `Wasm/Ops/Crypto.lean` so the ABI is
type-checked, but **the committed `.wasm` artifacts are stale**: they do
not contain `aeadSeal`, `aeadOpen`, `hpkeSeal`, `hpkeOpen`, or any of
the new HACL\* code. A rebuild through Emscripten is needed before any
browser or Node surface can call these ops, and the four byte-identical
wasm mirrors and the three `version.json` files must be re-stamped with
it (see [`skills/npm-release`](../../skills/npm-release/SKILL.md)).

Until then, treat these primitives as native-only.

## Two paid-for notes

**A tamper twin that clamping made vacuous.** The HPKE
wrong-recipient-key check first flipped bit 0 of byte 0 of `skR`. RFC
7748 §5 clamping CLEARS the low three bits of an X25519 scalar's first
byte, so the flip was undone and the "wrong" key was the right one. The
check failed, which is the only reason it was noticed; a twin written
that way on a path where the tamper is *expected* to still open would
have passed and tested nothing. The probe now flips byte 16 and
separately asserts that the byte-0 flip really is a no-op.

**`seal` is a Lean 4 command keyword.** `def seal` does not parse. The
AEAD entry point is `aeadSeal` and HPKE's is `sealBase`.
