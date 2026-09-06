/-
L4Factoidal.JOSE.Jws — JWS Compact Serialization (RFC 7515 §3.1) and
signature verification, with an explicit algorithm allowlist.

## The two confusions this module is built to exclude

**Algorithm confusion.** A verifier that reads `alg` from the token and
dispatches on it, with an RSA public key in hand, can be handed
`alg: HS256` and an HMAC computed with that public key as the secret —
the public key is public, so the attacker can compute it. The published
form of the attack also includes `alg: none`. The defence is not to
"reject `none`": it is to decide, from a fixed allowlist, before any key
is touched, and to have no HMAC verifier reachable at all.

  * `Alg` has exactly three constructors: `es256`, `rs256`, `eddsa`.
    There is no HMAC constructor, so no HMAC code path exists to reach.
  * `algOfString?` answers `none` for every other string, `HS256`,
    `HS384`, `HS512`, `none`, `None`, `NONE` and the empty string
    included (`hmacFamily_not_allowed`, `alg_none_not_allowed`).
  * `preKey` runs the whole decision — split, decode, parse, `crit`
    check, allowlist — before the key is read.
    `verify_independent_of_key_before_key_stage` states that a token
    refused at that stage gives the same answer for EVERY key and EVERY
    set of verifier functions. That is what "never reaches the verifier"
    means as a proposition: the result does not depend on the verifiers
    at all.

**Key-type confusion.** An `ES256` header with an RSA key, or an `EdDSA`
header with an EC key, must be refused rather than coerced. `verifyWith`
matches the algorithm against the key type and has no fallback arm;
`verifyWith_kty_matches` states that a verification only happens when
the types agree.

## `crit`

RFC 7515 §4.1.11 says a recipient that does not understand an extension
listed in `crit` MUST reject the JWS. This module understands no
extensions, so any `crit` member is a rejection
(`crit_refused`). Silently ignoring `crit` is how an extension meant to
constrain a token gets dropped.

## What is a parameter, and why

The three signature primitives arrive in a `Verifiers` record. Every
theorem here is universally quantified over that record, so none of them
depends on HACL* and all of them are checkable with stub verifiers,
which is what the `#guard`s below do. The executable edge builds the
record from `Crypto.P256.p256VerifySha256`, `Pkcs1.rs256Verify` over
`Crypto.Rsa.rsaPublicOp`, and `Crypto.Ed25519.verify`.
-/
import L4Factoidal.JOSE.Jwk
import L4Factoidal.JOSE.Pkcs1

namespace L4Factoidal.JOSE

open L4Factoidal.JSON

/-! ## Algorithms -/

/-- The JWS algorithms this project verifies. RFC 7518 §3.1 lists many
more; each one absent here is absent because no code in this project can
check it, which is the only safe reason to name an algorithm. -/
inductive Alg where
  | es256
  | rs256
  | eddsa
  deriving DecidableEq, Repr, BEq

/-- The `alg` header value (RFC 7518 §3.1, RFC 8037 §3.1). -/
def Alg.name : Alg → String
  | .es256 => "ES256"
  | .rs256 => "RS256"
  | .eddsa => "EdDSA"

/-- The key type an algorithm requires (RFC 7518 §3.4, §3.3, RFC 8037
§3.1). -/
def Alg.kty : Alg → Kty
  | .es256 => .ec
  | .rs256 => .rsa
  | .eddsa => .okp

/-- **The allowlist.** A closed match with a `none` default: adding an
algorithm means adding a constructor to `Alg` and a verifier to
`Verifiers`, which cannot be done by accident. -/
def algOfString? : String → Option Alg
  | "ES256" => some .es256
  | "RS256" => some .rs256
  | "EdDSA" => some .eddsa
  | _ => none

/-! ## Compact serialisation -/

/-- The three parts of a JWS Compact Serialization, plus the signing
input the signature covers (RFC 7515 §5.2 step 8:
`ASCII(BASE64URL(UTF8(header)) || '.' || BASE64URL(payload))`). The
signing input is stored rather than recomputed so that no consumer can
re-derive it differently. -/
structure Compact where
  protectedB64 : String
  payloadB64 : String
  signatureB64 : String
  signingInput : ByteArray

/-- The refusals decided from the token alone, BEFORE any key is read.
They are a type of their own rather than constructors of `Outcome` so
that "this refusal happened before the key" is a fact about types rather
than a comment. -/
inductive Refusal where
  | notThreeParts
  | headerNotBase64Url
  | headerNotUtf8
  | headerNotJson
  | headerNotObject
  | algMissing
  | algNotAllowed (alg : String)
  | criticalHeaderUnsupported
  deriving DecidableEq, Repr, BEq

/-- Why a token was or was not verified. Every constructor except
`verified` is a refusal; there is no "unknown" and no default-accept. -/
inductive Outcome where
  | verified
  | refused (r : Refusal)
  | keyTypeMismatch
  | signatureNotBase64Url
  | signatureRejected
  deriving DecidableEq, Repr, BEq

/-- RFC 7515 §3.1: exactly two `.` separators, so exactly three parts.
An empty payload is legal (RFC 7515 Appendix F detached content is not
supported, but a zero-length payload is); an empty header or an empty
signature is not. -/
def splitCompact? (token : String) : Option Compact :=
  match token.splitOn "." with
  | [h, p, s] =>
      if h.isEmpty || s.isEmpty then none
      else some { protectedB64 := h, payloadB64 := p, signatureB64 := s,
                  signingInput := (h ++ "." ++ p).toUTF8 }
  | _ => none

/-! ## The stage before the key -/

/-- The protected header and the algorithm it names, or the refusal that
stopped it. Everything here is decided from the token alone. -/
structure Header where
  alg : Alg
  json : Json

/-- Split, decode, parse, check `crit`, resolve the algorithm against the
allowlist. THE KEY IS NOT AN ARGUMENT: that is the property the theorems
below turn into a proposition. -/
def preKey (token : String) : Except Refusal (Compact × Header) :=
  match splitCompact? token with
  | none => .error .notThreeParts
  | some c =>
      match Base64Url.decode c.protectedB64 with
      | none => .error .headerNotBase64Url
      | some raw =>
          match String.fromUTF8? raw with
          | none => .error .headerNotUtf8
          | some text =>
              match parseJson? text with
              | none => .error .headerNotJson
              | some j =>
                  match j with
                  | .object _ =>
                      if (j.field? "crit").isSome then .error .criticalHeaderUnsupported
                      else
                        match j.getString? "alg" with
                        | none => .error .algMissing
                        | some a =>
                            match algOfString? a with
                            | none => .error (.algNotAllowed a)
                            | some alg => .ok (c, { alg := alg, json := j })
                  | _ => .error .headerNotObject

/-! ## Verification -/

/-- The three signature primitives, supplied by the caller.

  * `es256 pubXY msg sig` — raw 64-octet key, raw 64-octet `r || s`.
  * `rs256 n e sig msg` — big-endian modulus and exponent.
  * `eddsa pk msg sig` — 32-octet key, 64-octet signature.

There is deliberately no HMAC field. -/
structure Verifiers where
  es256 : ByteArray → ByteArray → ByteArray → Bool
  rs256 : ByteArray → ByteArray → ByteArray → ByteArray → Bool
  eddsa : ByteArray → ByteArray → ByteArray → Bool

/-- Dispatch on the algorithm AND the key type together. `none` means
the two do not agree; there is no arm that coerces one to the other. -/
def verifyWith (V : Verifiers) (alg : Alg) (k : Jwk)
    (signingInput sig : ByteArray) : Option Bool :=
  match alg, k with
  | .es256, .ec x y => some (V.es256 (x ++ y) signingInput sig)
  | .rs256, .rsa n e => some (V.rs256 n e sig signingInput)
  | .eddsa, .okp p => some (V.eddsa p signingInput sig)
  | _, _ => none

/-- Verify a JWS Compact Serialization against one key. -/
def verifyCompact (V : Verifiers) (k : Jwk) (token : String) : Outcome :=
  match preKey token with
  | .error r => .refused r
  | .ok (c, h) =>
      match Base64Url.decode c.signatureB64 with
      | none => .signatureNotBase64Url
      | some sig =>
          match verifyWith V h.alg k c.signingInput sig with
          | none => .keyTypeMismatch
          | some true => .verified
          | some false => .signatureRejected

/-! ## Theorems -/

/-- A refusal decided before the key is the answer. -/
theorem verify_refuses_at_pre_key_stage (V : Verifiers) (k : Jwk) (token : String)
    {r : Refusal} (h : preKey token = .error r) : verifyCompact V k token = .refused r := by
  simp [verifyCompact, h]

/-- **A token refused before the key stage is refused identically for
every key and every set of verifier functions.** This is the precise
sense in which such a token "never reaches" the EC, RSA or Ed25519
verifier: the outcome does not depend on them. -/
theorem verify_independent_of_key_before_key_stage
    (V₁ V₂ : Verifiers) (k₁ k₂ : Jwk) (token : String) {r : Refusal}
    (h : preKey token = .error r) :
    verifyCompact V₁ k₁ token = verifyCompact V₂ k₂ token := by
  rw [verify_refuses_at_pre_key_stage V₁ k₁ token h,
      verify_refuses_at_pre_key_stage V₂ k₂ token h]

/-- **An `alg` outside the allowlist stops the token at the pre-key
stage.** With the previous theorem, that is the algorithm-confusion
statement: the outcome is `algNotAllowed` for every key and every
verifier. -/
theorem alg_not_allowed_stops_before_key {token : String} {c : Compact} {j : Json}
    {a : String} (hs : splitCompact? token = some c)
    (hd : ((Base64Url.decode c.protectedB64).bind String.fromUTF8?).bind parseJson?
            = some j)
    (hobj : ∃ fs, j = .object fs)
    (hcrit : (j.field? "crit").isSome = false)
    (halg : j.getString? "alg" = some a)
    (hbad : algOfString? a = none) :
    preKey token = .error (.algNotAllowed a) := by
  obtain ⟨fs, rfl⟩ := hobj
  unfold preKey
  cases hb : Base64Url.decode c.protectedB64 with
  | none => rw [hb] at hd; simp at hd
  | some raw =>
      rw [hb] at hd
      simp only [Option.bind_some] at hd
      cases hu : String.fromUTF8? raw with
      | none => rw [hu] at hd; simp at hd
      | some text =>
          rw [hu] at hd
          simp only [Option.bind_some] at hd
          simp [hs, hb, hu, hd, hcrit, halg, hbad]

/-- **No HMAC algorithm is in the allowlist.** There is no HMAC verifier
in `Verifiers` for one to reach. -/
theorem hmacFamily_not_allowed :
    ∀ s ∈ ["HS256", "HS384", "HS512"], algOfString? s = none := by decide

/-- **`alg: none` is not in the allowlist**, in every spelling that has
been used against real verifiers. -/
theorem alg_none_not_allowed :
    ∀ s ∈ ["none", "None", "NONE", "nOnE", ""], algOfString? s = none := by decide

/-- Nor are the other RFC 7518 §3.1 algorithms this project cannot
check. Each would be a silent accept if the allowlist were a denylist
instead. -/
theorem unsupported_algs_not_allowed :
    ∀ s ∈ ["ES384", "ES512", "PS256", "PS384", "PS512", "RS384", "RS512",
           "ES256K", "es256", "rs256", "eddsa"], algOfString? s = none := by decide

/-- The allowlist maps exactly the three names it accepts, and each to
the algorithm whose `name` it is. -/
theorem algOfString_roundTrip (a : Alg) : algOfString? a.name = some a := by
  cases a <;> rfl

/-- **A verification only happens when the key type matches the
algorithm.** `verifyWith` has no coercing arm, so an `ES256` header with
an RSA key gives `none`, which `verifyCompact` turns into
`keyTypeMismatch`. -/
theorem verifyWith_kty_matches {V : Verifiers} {alg : Alg} {k : Jwk}
    {si sig : ByteArray} {b : Bool} (h : verifyWith V alg k si sig = some b) :
    alg.kty = k.kty := by
  cases alg <;> cases k <;> simp_all [verifyWith, Alg.kty, Jwk.kty]

/-- **A verified token's key type is the one its algorithm required.** -/
theorem verified_kty_matches {V : Verifiers} {k : Jwk} {token : String}
    (h : verifyCompact V k token = .verified) :
    ∃ c hd, preKey token = .ok (c, hd) ∧ hd.alg.kty = k.kty := by
  unfold verifyCompact at h
  cases hp : preKey token with
  | error r => rw [hp] at h; simp at h
  | ok ch =>
      obtain ⟨c, hd⟩ := ch
      rw [hp] at h
      simp only at h
      cases hs : Base64Url.decode c.signatureB64 with
      | none => rw [hs] at h; simp at h
      | some sig =>
          rw [hs] at h
          simp only at h
          cases hv : verifyWith V hd.alg k c.signingInput sig with
          | none => rw [hv] at h; simp at h
          | some b =>
              exact ⟨c, hd, rfl, verifyWith_kty_matches hv⟩

/-- **A `crit` header is a rejection** (RFC 7515 §4.1.11): this module
understands no extensions, and an unrecognised `crit` entry MUST stop
the JWS. -/
theorem crit_refused {token : String} {c : Compact} {j : Json}
    (hs : splitCompact? token = some c)
    (hd : ((Base64Url.decode c.protectedB64).bind String.fromUTF8?).bind parseJson?
            = some j)
    (hobj : ∃ fs, j = .object fs)
    (hcrit : (j.field? "crit").isSome = true) :
    preKey token = .error .criticalHeaderUnsupported := by
  obtain ⟨fs, rfl⟩ := hobj
  unfold preKey
  cases hb : Base64Url.decode c.protectedB64 with
  | none => rw [hb] at hd; simp at hd
  | some raw =>
      rw [hb] at hd
      simp only [Option.bind_some] at hd
      cases hu : String.fromUTF8? raw with
      | none => rw [hu] at hd; simp at hd
      | some text =>
          rw [hu] at hd
          simp only [Option.bind_some] at hd
          simp [hs, hb, hu, hd, hcrit]

/-- A token that is not three non-empty-ended parts never reaches
anything. -/
theorem not_three_parts_refused {token : String} (h : splitCompact? token = none) :
    preKey token = .error .notThreeParts := by
  simp [preKey, h]

/-! ## Fixtures

The RFC 7515 Appendix A examples that need a real signature primitive
are sections of `lake exe l4jose-probe`; an extern does not evaluate at
compile time. What is checked here is everything the pre-key stage
decides, with stub verifiers standing in for the primitives. -/

private def stubAccept : Verifiers :=
  { es256 := fun _ _ _ => true, rs256 := fun _ _ _ _ => true, eddsa := fun _ _ _ => true }
private def stubReject : Verifiers :=
  { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }

private def ecKey : Jwk :=
  (parseJwkString? ("{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
    "\"x\":\"f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU\"," ++
    "\"y\":\"x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0\"}")).getD (.okp ByteArray.empty)

private def rsaKey : Jwk :=
  .rsa ⟨(List.replicate 256 (0xFF : UInt8)).toArray⟩ ⟨#[0x01, 0x00, 0x01]⟩

private def edKey : Jwk :=
  (parseJwkString? ("{\"kty\":\"OKP\",\"crv\":\"Ed25519\"," ++
    "\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}")).getD (.okp ByteArray.empty)

/-- Build a token with the given protected-header JSON and a one-octet
signature. -/
private def tokenWith (header payload : String) : String :=
  Base64Url.encodeUtf8 header ++ "." ++ Base64Url.encodeUtf8 payload ++ "." ++
  Base64Url.encode ⟨#[0x00]⟩

-- The RFC 7515 Appendix A.3.1 protected header, `{"alg":"ES256"}`, whose
-- encoding the RFC gives as "eyJhbGciOiJFUzI1NiJ9".
#guard Base64Url.encodeUtf8 "{\"alg\":\"ES256\"}" == "eyJhbGciOiJFUzI1NiJ9"
-- The RFC 7515 Appendix A.1.1 header, `{"typ":"JWT",\r\n "alg":"HS256"}`.
#guard Base64Url.encodeUtf8 "{\"typ\":\"JWT\",\r\n \"alg\":\"HS256\"}"
        == "eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9"

-- Algorithm confusion: the RFC 7515 Appendix A.1 HS256 header, offered
-- with an EC, an RSA and an Ed25519 key, and with both an accepting and
-- a rejecting set of verifiers. Every combination is `algNotAllowed`.
#guard verifyCompact stubAccept ecKey
  (tokenWith "{\"typ\":\"JWT\",\r\n \"alg\":\"HS256\"}" "{}") == .refused (.algNotAllowed "HS256")
#guard verifyCompact stubAccept rsaKey
  (tokenWith "{\"typ\":\"JWT\",\r\n \"alg\":\"HS256\"}" "{}") == .refused (.algNotAllowed "HS256")
#guard verifyCompact stubAccept edKey
  (tokenWith "{\"typ\":\"JWT\",\r\n \"alg\":\"HS256\"}" "{}") == .refused (.algNotAllowed "HS256")
#guard verifyCompact stubReject rsaKey
  (tokenWith "{\"typ\":\"JWT\",\r\n \"alg\":\"HS256\"}" "{}") == .refused (.algNotAllowed "HS256")
#guard verifyCompact stubAccept rsaKey (tokenWith "{\"alg\":\"none\"}" "{}")
        == .refused (.algNotAllowed "none")
#guard verifyCompact stubAccept rsaKey (tokenWith "{\"alg\":\"NONE\"}" "{}")
        == .refused (.algNotAllowed "NONE")
#guard verifyCompact stubAccept rsaKey (tokenWith "{\"alg\":\"PS256\"}" "{}")
        == .refused (.algNotAllowed "PS256")
#guard verifyCompact stubAccept rsaKey (tokenWith "{\"typ\":\"JWT\"}" "{}") == .refused .algMissing

-- Key-type confusion: the right algorithm with the wrong key type.
#guard verifyCompact stubAccept rsaKey (tokenWith "{\"alg\":\"ES256\"}" "{}")
        == .keyTypeMismatch
#guard verifyCompact stubAccept ecKey (tokenWith "{\"alg\":\"RS256\"}" "{}")
        == .keyTypeMismatch
#guard verifyCompact stubAccept ecKey (tokenWith "{\"alg\":\"EdDSA\"}" "{}")
        == .keyTypeMismatch
#guard verifyCompact stubAccept edKey (tokenWith "{\"alg\":\"ES256\"}" "{}")
        == .keyTypeMismatch
-- Matched types reach the verifier, and the verifier's answer is the
-- outcome — in both directions.
#guard verifyCompact stubAccept ecKey (tokenWith "{\"alg\":\"ES256\"}" "{}") == .verified
#guard verifyCompact stubReject ecKey (tokenWith "{\"alg\":\"ES256\"}" "{}")
        == .signatureRejected
#guard verifyCompact stubAccept rsaKey (tokenWith "{\"alg\":\"RS256\"}" "{}") == .verified
#guard verifyCompact stubAccept edKey (tokenWith "{\"alg\":\"EdDSA\"}" "{}") == .verified

-- `crit` stops the token whatever it lists.
#guard verifyCompact stubAccept ecKey
  (tokenWith "{\"alg\":\"ES256\",\"crit\":[\"exp\"]}" "{}") == .refused .criticalHeaderUnsupported
#guard verifyCompact stubAccept ecKey
  (tokenWith "{\"alg\":\"ES256\",\"crit\":[]}" "{}") == .refused .criticalHeaderUnsupported

-- Structural refusals.
#guard verifyCompact stubAccept ecKey "eyJhbGciOiJFUzI1NiJ9.e30" == .refused .notThreeParts
#guard verifyCompact stubAccept ecKey "a.b.c.d" == .refused .notThreeParts
#guard verifyCompact stubAccept ecKey ".e30.AA" == .refused .notThreeParts
#guard verifyCompact stubAccept ecKey "eyJhbGciOiJFUzI1NiJ9.e30." == .refused .notThreeParts
#guard verifyCompact stubAccept ecKey "eyJhbGciOiJFUzI1NiJ9.e30.A=" == .signatureNotBase64Url
#guard verifyCompact stubAccept ecKey "!!!.e30.AA" == .refused .headerNotBase64Url
#guard verifyCompact stubAccept ecKey (tokenWith "[1,2]" "{}") == .refused .headerNotObject
#guard verifyCompact stubAccept ecKey (tokenWith "{" "{}") == .refused .headerNotJson

end L4Factoidal.JOSE
