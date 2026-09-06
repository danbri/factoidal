# JOSE, DPoP and Solid-OIDC over HACL\* (2026-09-06)

Owner instruction, 2026-09-06, verbatim: "do lots of reassuring proofs to
catch screwups and test with all the tests we get snarf from suitably
licensed repos".

## What this record is for

`2026-09-06-lws-and-solid-protocols.md` §2 said token verification was a
host boundary because "RSA and P-256 are not vendored". That was true
when it was written and stopped being true the same day. This record
says what replaced it, who verifies what, and what the tests found.

## The split: HACL\* for arithmetic, Lean for bytes and policy

**HACL\*.** Four `opaque` declarations, realised by three
length-checking C shims over vendored, unmodified KaRaMeL-extracted C
from `cryspen/hacl-packages` at the commit already pinned for Ed25519
(`05c3d8fb`, Apache-2.0):

| Lean | HACL\* entry point | shim |
|---|---|---|
| `Crypto.sha256Hacl`, `Ed25519.{secretToPublic,sign,verify}` | `Hacl_Hash_SHA2_hash_256`, `Hacl_Ed25519_*` | `ffi/hacl_ed25519.c` (already there) |
| `Crypto.P256.p256VerifySha256`, `p256ValidatePublicKey` | `Hacl_P256_ecdsa_verif_p256_sha2`, `Hacl_P256_validate_public_key` | `ffi/hacl_p256.c` |
| `Crypto.Rsa.rsaPublicOpRaw` | `Hacl_Bignum64_{new_bn_from_bytes_be,mod_exp_vartime,bn_to_bytes_be}` | `ffi/hacl_rsa.c` |

`Hacl_Bignum4096.c` was not taken. The generic 64-bit field takes the
limb count at run time, so one translation unit serves 2048-, 3072- and
4096-bit moduli where the fixed-width unit serves only the largest.

**Lean.** `L4Factoidal/JOSE/` — base64url (RFC 7515 §2, RFC 4648 §5),
EMSA-PKCS1-v1_5 (RFC 8017 §9.2), JWK and RFC 7638 thumbprints, JWS
compact serialisation with the algorithm allowlist, JWT claims, and RFC
9449 DPoP — plus `L4Factoidal/Solid/Server/Auth.lean`, which composes
them into a Solid-OIDC decision. No `partial def`, no `IO`, no clock
call, and no extern anywhere in those six modules: the signature
primitives arrive as a `Verifiers` record and the current time as a
policy field.

**The host.** What is left for the Node host is what a host must do:
hold the socket, fetch the identity provider's JWKS over the network,
and remember `jti` values for replay detection. It decides nothing.
Which key verifies a token, whether the claims are acceptable, and
whether the proof binds the token are all decided in Lean.

## Three forgery classes, and how each is excluded

**Algorithm confusion.** A verifier that dispatches on the token's own
`alg` with a public key in hand can be handed `alg: HS256` and an HMAC
computed with that public key as the secret. `JOSE.Alg` has three
constructors and no HMAC one, so no HMAC code path exists to reach.
`verify_independent_of_key_before_key_stage` states the consequence as a
proposition: a token refused before the key stage gives the same outcome
for EVERY key and EVERY set of verifier functions, so the result does
not depend on them at all. `hmacFamily_not_allowed`,
`alg_none_not_allowed` and `unsupported_algs_not_allowed` close the
allowlist by `decide`.

**Key-type confusion.** `verifyWith` matches the algorithm against the
key type and has no coercing arm; `verifyWith_kty_matches` says a
verification only happens when they agree.

**Bleichenbacher 2006, and its 2019 and 2021 repetitions.** RFC 8017
§8.2.2 note 2 offers two verification methods and names comparison as
preferred; the other, parsing the recovered block, is where the forgery
lives. Only comparison is implemented, and there is no code path that
could implement the other: `emsaEncode` generates the whole `k`-octet
block and never reads one, and `rs256Verify` compares all `k` octets.
`rs256Verify_iff_template` states acceptance in BOTH directions, so a
later change that adds a lenient path breaks the theorem rather than
passing the tests. There is no PKCS#1 parser anywhere in this project.

Two smaller ones are excluded the same way. A DPoP proof whose header
carries a private JWK is refused (`parsePublicJwk_no_private`), and a
key-bound access token presented as a `Bearer` credential is refused
rather than accepted (`authenticate_bearer_refused`).

## Strictness in base64url, and why it is load-bearing

RFC 7515 §2 defines base64url without padding. The decoder here refuses
`=`, refuses `+` and `/`, refuses whitespace, refuses a `4k+1` length,
and refuses a final group whose unused low bits are set. That last
refusal is what makes the codec injective in both directions
(`decode_encode` and `encode_decode`), so a JWS `protected` header has
exactly one spelling and cannot be re-serialised without changing the
signing input the signature covers.

The arithmetic is deliberately `Nat` multiplication, division and
remainder by literals rather than `UInt8` shifts and masks: `omega`
decides the first and no tactic in this toolchain decides the second.

## What the tests found

**Wycheproof** (C2SP/wycheproof, Apache-2.0, shallow submodule at
`third_party/testing/wycheproof`), through `lake exe l4jose-probe`:

```
jose-rfc-fixtures                        17 pass, 0 fail (out of 17)
wycheproof-ecdsa-secp256r1-sha256-p1363  262 pass, 0 fail (out of 262)
wycheproof-rsa-2048-sha256               258 pass, 0 fail, 1 acceptable (out of 259)
wycheproof-rsa-3072-sha256               258 pass, 0 fail, 1 acceptable (out of 259)
wycheproof-rsa-4096-sha256               257 pass, 0 fail, 1 acceptable (out of 258)
dpop-rfc9449                             11 pass, 0 fail (out of 11)
solid-oidc                               14 pass, 0 fail (out of 14)
TOTAL                                    1077 pass, 0 fail, 3 acceptable (out of 1080)
```

It found no defect in this layer. That is a weaker statement than it
looks and is worth being precise about: HACL\*'s P-256 answered all 262
ECDSA vectors correctly on the first run, before any Lean code was
involved, which is what a verified implementation should do. The RSA
vectors exercise this project's own code — the padding template and the
comparison — and all 773 scored vectors agree.

The three `acceptable` vectors are one per modulus size, all the
"Missing NULL in the ASN encoding" DigestInfo variant. They are counted
in their own bucket and never folded into pass or fail, because
`acceptable` means neither answer is a defect and counting one as a pass
would inflate the score. This project REFUSES all three, and the probe
prints that it did. RFC 8017 §9.2 note 1 permits one encoding for
SHA-256, and `sha256DigestInfo` is that encoding as a constant.

**Two things the corpus run did catch**, both in the harness rather than
the library, and both worth recording because each would have produced a
green score that meant less than it appeared to:

1. Nine of the 112 ECDSA groups carry no `publicKeyJwk` — they are the
   special-case public keys Wycheproof constructs to probe point
   validation, which JWK cannot express. The first version reported nine
   group-level failures. Skipping those groups would have made the score
   green while dropping 10 `invalid` vectors out of the denominator. The
   probe now falls back to the raw `publicKey.wx`/`.wy` hex, and when no
   key can be built at all it takes the verifier to refuse every vector
   in the group and still scores each one against its own expectation.
2. The first transcription of the RFC 9449 Figure 2 proof was written out
   by hand and decoded to garbage. Every RFC fixture in this landing is
   now extracted from the RFC's own `.txt` by script, with RFC 8792 line
   wrapping removed, and the header and payload are decoded and compared
   with the RFC's printed decoded form.

**The WebCrypto differential** (`node tests/jose/webcrypto-differential.mjs`):
Node generates a fresh P-256 key and a fresh RSA-2048 key, signs 200
random messages with each, and asks the probe about every signature and
about the same signature with one random bit flipped.

```
jose-webcrypto-differential ES256: 400 pass, 0 fail (out of 400)
jose-webcrypto-differential RS256: 400 pass, 0 fail (out of 400)
```

Both directions are scored, so a verifier that answered `true` to
everything would fail half of each. The script exits 77 with a printed
reason when the native binary is absent.

**RFC fixtures.** RFC 7515 Appendix A.2 (RS256) and A.3 (ES256) and RFC
7520 §4.1 (RS256) verify end to end; each is also run with a flipped
signature bit, a replaced payload and under the other example's key. RFC
7520 §4.2 (PS384) and §4.3 (ES512) are REFUSED by the allowlist, which
is the correct outcome for two real algorithms this project cannot
check — accepting them would be claiming a check that is not performed.
RFC 7638 §3.1's thumbprint, RFC 8037 Appendix A.3's thumbprint, RFC 4648
§10's base64 vectors and RFC 9449 §4.1's `ath` all reproduce as
build-time `#guard`s.

## What moved in the conformance ledger

| id | was | is | decided by |
|---|---|---|---|
| `lws-core-14` "unknown requester" | host-verified | guarded | `solidGuardSolidOidcDpop` |
| `lws-core-15` LWS uses OpenID Connect etc. | open ("RS256 and ES256 are not vendored") | guarded | `solidGuardSolidOidcDpop` |
| `solid-10-01` Servers MUST conform to Solid-OIDC | host-verified | guarded | `solidGuardSolidOidcDpop` |

LWS core: 2 proved, 9 guarded, 0 host-verified, 7 open (out of 18).
Solid: 3 proved, 60 guarded, 3 host-verified, 7 open (out of 73).

The three remaining Solid host-verified rows are HTTP framing, the
http-to-https redirect and storage allocation across handles — a
listener's business, not an engine's.

## Off by default, in two switches

`ServerConfig.auth.enforceAuth` is `false`, exactly as
`ServerConfig.enforceWac` is. With it false, `authenticate` answers
`disabled` and the WebID keeps coming from the handle configuration, so
every existing host suite and interop script behaves as before
(`requesterOf_unchanged_when_auth_off`). Two switches rather than one
because they are two decisions: whether the server BELIEVES a claimed
identity, and whether it ENFORCES a policy over it.

A deployment that turns authentication on without configuring its
identity provider's keys refuses every credential
(`checkCredential_no_keys`). It does not fall open.

## Costs paid, and open items

* **Variable-time modular exponentiation.** `Hacl_Bignum64_mod_exp_vartime`
  is not constant time in the exponent. Acceptable here and only here:
  the exponent is the RSA public exponent and the base is the published
  signature, so a timing observer learns nothing the token does not
  already carry. `ffi/hacl_rsa.c` exposes no private operation, no key
  generation and no signer, so the constant-time variant is not needed
  and cannot become needed by accident.
* **No signer for P-256.** `Crypto/P256Native.lean` exposes only
  verification. HACL\*'s ECDSA signing entry takes a caller-supplied
  nonce, and a nonce is exactly the thing this project has no safe
  source for. The `solid-oidc` probe section therefore mints its test
  tokens with Ed25519, which is deterministic and already bound.
* **ECDSA malleability is not refused.** `s` and `n-s` both verify. JWS
  does not require a low-`s` form, so refusing it would be
  non-conformant; a caller who needs signature uniqueness must not use
  ECDSA. Stated in the module header rather than silently accepted.
* **Nonce (RFC 9449 §8) is read but not enforced.** `ProofClaims.nonce`
  is parsed; a server that issues nonces supplies its own predicate over
  it. No row claims otherwise.
* **The wasm module was not rebuilt in this landing.** The lakefile and
  `Wasm/build-wasm.sh` both carry the new translation units and shims,
  so a wasm build will link them; the evidence here is native.
* **`Jwt.Claims.webid` is not an RFC 7519 registered claim.** It is
  Solid-OIDC's, and the fallback to `sub` is behind
  `AuthConfig.subjectIsWebId`, off by default, because making every
  subject identifier a WebID is a decision a deployment should state.

## Gates

* `lake build` — clean, 1080 jobs.
* `lake exe l4jose-probe` — 1077 pass, 0 fail, 3 acceptable (out of 1080).
* `lake exe l4vc-probe` — 119 pass, 0 fail (out of 119).
* `lake exe l4lws-probe` — 9 pass, 0 fail (out of 9) guarded checks.
* `lake exe l4solid-probe` — 60 pass, 0 fail (out of 60) guarded checks.
* `node tests/jose/webcrypto-differential.mjs` — 400 + 400 pass, 0 fail.
* `tools/lean-hygiene-audit.py` — clean; `partial def` still 172.
* `#print axioms` on all 49 new theorems — `propext`,
  `Classical.choice`, `Quot.sound`, and nothing else.
