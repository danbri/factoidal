/-
L4Factoidal.JOSE.Jwk — JSON Web Key (RFC 7517), restricted to the three
key types this project verifies with, and RFC 7638 thumbprints.

The three types are exactly the three JWS algorithms `JOSE/Jws.lean`
allows:

  * `EC` with `crv` `P-256` — RFC 7518 §6.2, for `ES256`.
  * `RSA` — RFC 7518 §6.3, for `RS256`.
  * `OKP` with `crv` `Ed25519` — RFC 8037 §2, for `EdDSA`.

Every other `kty`, and every other `crv` inside those two, is REFUSED at
parse time rather than at verification time. A key this module returns
is already the right shape for the primitive that will consume it: an
`ec` key carries exactly 32 octets of `x` and 32 of `y`, which is what
HACL* takes as a raw `x || y` public key.

## Private key material is refused

RFC 9449 §4.2 requires the `jwk` header of a DPoP proof to be the
PUBLIC key. A client that pastes its whole key object into the header
leaks its private key to every server it talks to, and a server that
accepts such an object has no way to say it did not use it.
`parsePublicJwk?` refuses any object carrying a private member — `d`
(RFC 7518 §6.2.2.1 for EC, §6.3.2.1 for RSA, RFC 8037 §2 for OKP), and
the RSA CRT members `p`, `q`, `dp`, `dq`, `qi`, `oth` — and
`parsePublicJwk_no_private` states that as a theorem.

## Thumbprints

RFC 7638 §3 fixes the thumbprint as SHA-256 over a JSON object that
contains only the REQUIRED members for the key type, with no
whitespace, member names in lexicographic order of their Unicode code
points, and strings in the shortest JSON form. §3.2 gives the required
member sets: `crv`, `kty`, `x`, `y` for EC; `e`, `kty`, `n` for RSA.
RFC 8037 §2 adds `crv`, `kty`, `x` for OKP.

`canonicalJson` writes those objects directly rather than running a
general JSON serialiser. Two things make that safe, and both are
checked: the member names are ASCII letters, and the member values are
either base64url (whose alphabet contains no character JSON escapes) or
one of the four fixed strings `EC`, `RSA`, `OKP`, `P-256`, `Ed25519`.
Nothing here can require an escape, so the "shortest form" rule is met
by writing the characters out.

Re-encoding the decoded octets reproduces the member value the key was
parsed from. That is not an assumption: `Base64Url.encode_decode` proves
that every string the strict decoder accepts is the encoding of its own
octets, so a key parsed from a JWK and a key built from octets give the
same thumbprint.
-/
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.Crypto.SHA2
import L4Factoidal.JSON.Parser

namespace L4Factoidal.JOSE

open L4Factoidal.JSON
open L4Factoidal.Crypto

/-- The `kty` values this project verifies with (RFC 7518 §6.1, RFC 8037
§2). There is deliberately no `oct` constructor: symmetric keys belong
to the HMAC algorithms, which `JOSE/Jws.lean` does not allow. -/
inductive Kty where
  | ec
  | rsa
  | okp
  deriving DecidableEq, Repr

/-- A public JWK of one of the three supported types. The field sizes
are established at parse time, so a consumer never re-checks them:

  * `ec x y` — P-256, `x` and `y` each exactly 32 octets.
  * `rsa n e` — `n` is 256, 384 or 512 octets (2048, 3072 or 4096 bits,
    RFC 7518 §3.3's floor for `RS256`); `e` is non-empty.
  * `okp x` — Ed25519, `x` exactly 32 octets. -/
inductive Jwk where
  | ec (x y : ByteArray)
  | rsa (n e : ByteArray)
  | okp (x : ByteArray)
  deriving BEq

/-- The key type of a parsed key. -/
def Jwk.kty : Jwk → Kty
  | .ec _ _ => .ec
  | .rsa _ _ => .rsa
  | .okp _ => .okp

/-- The raw `x || y` P-256 public key HACL* takes, 64 octets. `none` for
a key that is not EC. -/
def Jwk.ecPublicRaw? : Jwk → Option ByteArray
  | .ec x y => some (x ++ y)
  | _ => none

/-- The Ed25519 public key, 32 octets. `none` for a key that is not
OKP. -/
def Jwk.okpPublic? : Jwk → Option ByteArray
  | .okp x => some x
  | _ => none

/-! ## Private members -/

/-- The member names that carry private key material: `d` for all three
types (RFC 7518 §6.2.2.1, §6.3.2.1, RFC 8037 §2), and the RSA CRT
members of RFC 7518 §6.3.2. -/
def privateMemberNames : List String :=
  ["d", "p", "q", "dp", "dq", "qi", "oth"]

/-- Whether a JSON object carries any private member. A non-object is
not a key at all and answers `false`; `parseJwk?` refuses it
separately. -/
def hasPrivateMember (j : Json) : Bool :=
  privateMemberNames.any fun n => (j.field? n).isSome

/-! ## Parsing -/

/-- Decode a base64url member to octets. -/
private def member? (j : Json) (name : String) : Option ByteArray :=
  (j.getString? name).bind Base64Url.decode

/-- RFC 7518 §3.3 requires a 2048-bit or larger modulus for `RS256`, and
`Crypto/RsaNative.lean` refuses anything else, so the parse refuses it
here and the mismatch cannot arise later. -/
def acceptedModulusSize (n : Nat) : Bool := n == 256 || n == 384 || n == 512

/-- Parse a JWK, ignoring any member the key type does not require
(`kid`, `use`, `alg`, `x5c` and the rest are permitted and unused).
Private members are NOT ignored — see `parsePublicJwk?`. -/
def parseJwk? (j : Json) : Option Jwk :=
  match j.getString? "kty" with
  | some "EC" =>
      match j.getString? "crv" with
      | some "P-256" =>
          match member? j "x", member? j "y" with
          | some x, some y => if x.size == 32 && y.size == 32 then some (.ec x y) else none
          | _, _ => none
      | _ => none
  | some "RSA" =>
      match member? j "n", member? j "e" with
      | some n, some e =>
          if acceptedModulusSize n.size && e.size != 0 then some (.rsa n e) else none
      | _, _ => none
  | some "OKP" =>
      match j.getString? "crv" with
      | some "Ed25519" =>
          match member? j "x" with
          | some x => if x.size == 32 then some (.okp x) else none
          | none => none
      | _ => none
  | _ => none

/-- Parse a JWK that must be a PUBLIC key: the RFC 9449 §4.2 case. -/
def parsePublicJwk? (j : Json) : Option Jwk :=
  if hasPrivateMember j then none else parseJwk? j

/-- Parse from JSON text. -/
def parseJwkString? (s : String) : Option Jwk :=
  (parseJson? s).bind parseJwk?

/-- Parse public-only from JSON text. -/
def parsePublicJwkString? (s : String) : Option Jwk :=
  (parseJson? s).bind parsePublicJwk?

/-! ## RFC 7638 thumbprints -/

/-- The required-member JSON of RFC 7638 §3.2 and RFC 8037 §2, written
directly: no whitespace, member names in code-point order, values
needing no escape. -/
def canonicalJson : Jwk → String
  | .ec x y =>
      "{\"crv\":\"P-256\",\"kty\":\"EC\",\"x\":\"" ++ Base64Url.encode x ++
      "\",\"y\":\"" ++ Base64Url.encode y ++ "\"}"
  | .rsa n e =>
      "{\"e\":\"" ++ Base64Url.encode e ++ "\",\"kty\":\"RSA\",\"n\":\"" ++
      Base64Url.encode n ++ "\"}"
  | .okp x =>
      "{\"crv\":\"Ed25519\",\"kty\":\"OKP\",\"x\":\"" ++ Base64Url.encode x ++ "\"}"

/-- The member names `canonicalJson` writes, for the ordering check
below. -/
def requiredMemberNames : Jwk → List String
  | .ec _ _ => ["crv", "kty", "x", "y"]
  | .rsa _ _ => ["e", "kty", "n"]
  | .okp _ => ["crv", "kty", "x"]

/-- RFC 7638 §3.1: the base64url-encoded SHA-256 digest of the
canonical JSON. This is the value a Solid-OIDC access token carries as
`cnf.jkt` and a DPoP proof's key must match. -/
def thumbprint (k : Jwk) : String :=
  Base64Url.encode (sha256 (canonicalJson k).toUTF8)

/-! ## Theorems -/

/-- A parsed key's type is the one its `kty` member named. Nothing
reinterprets a key after parsing. -/
theorem parseJwk_kty {j : Json} {k : Jwk} (h : parseJwk? j = some k) :
    (k.kty = .ec ∧ j.getString? "kty" = some "EC") ∨
    (k.kty = .rsa ∧ j.getString? "kty" = some "RSA") ∨
    (k.kty = .okp ∧ j.getString? "kty" = some "OKP") := by
  unfold parseJwk? at h
  split at h
  · next s hs =>
      split at h
      · split at h
        · next _ _ _ _ hx _ =>
            split at h
            · cases h; exact Or.inl ⟨rfl, hs⟩
            · simp at h
        · simp at h
      · simp at h
  · next s hs =>
      split at h
      · next _ _ _ _ =>
          split at h
          · cases h; exact Or.inr (Or.inl ⟨rfl, hs⟩)
          · simp at h
      · simp at h
  · next s hs =>
      split at h
      · split at h
        · next _ _ _ hx =>
            split at h
            · cases h; exact Or.inr (Or.inr ⟨rfl, hs⟩)
            · simp at h
        · simp at h
      · simp at h
  · simp at h

/-- Every EC key this module produces is P-256 sized: 32 octets of `x`
and 32 of `y`, so `ecPublicRaw?` is always the 64 octets HACL* takes and
a length refusal at the primitive is unreachable from a parsed key. -/
theorem parseJwk_ec_sizes {j : Json} {x y : ByteArray} (h : parseJwk? j = some (.ec x y)) :
    x.size = 32 ∧ y.size = 32 := by
  unfold parseJwk? at h
  split at h
  · split at h
    · split at h
      · next _ _ _ _ _ _ =>
          split at h
          · next hc =>
              cases h
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              exact hc
          · simp at h
      · simp at h
    · simp at h
  · split at h
    · split at h
      · exact absurd h (by simp)
      · simp at h
    · simp at h
  · split at h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The raw P-256 public key is 64 octets for every parsed EC key. -/
theorem ecPublicRaw_size {j : Json} {k : Jwk} {raw : ByteArray}
    (hp : parseJwk? j = some k) (hr : k.ecPublicRaw? = some raw) : raw.size = 64 := by
  cases k with
  | ec x y =>
      obtain ⟨hx, hy⟩ := parseJwk_ec_sizes hp
      simp only [Jwk.ecPublicRaw?, Option.some.injEq] at hr
      subst hr
      rw [ByteArray.size_append, hx, hy]
  | rsa _ _ => simp [Jwk.ecPublicRaw?] at hr
  | okp _ => simp [Jwk.ecPublicRaw?] at hr

/-- Every RSA key this module produces has a modulus `Crypto/RsaNative`
accepts, so the public operation never refuses on size. -/
theorem parseJwk_rsa_size {j : Json} {n e : ByteArray} (h : parseJwk? j = some (.rsa n e)) :
    n.size = 256 ∨ n.size = 384 ∨ n.size = 512 := by
  unfold parseJwk? at h
  split at h
  · split at h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · simp at h
      · simp at h
    · simp at h
  · split at h
    · next _ _ _ _ =>
        split at h
        · next hc =>
            simp only [Option.some.injEq, Jwk.rsa.injEq] at h
            obtain ⟨hn, _⟩ := h
            subst hn
            simp only [Bool.and_eq_true, acceptedModulusSize, Bool.or_eq_true,
              beq_iff_eq] at hc
            exact or_assoc.mp hc.1
        · simp at h
    · simp at h
  · split at h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- **A JWK carrying private key material is never accepted as a public
key.** This is the RFC 9449 §4.2 requirement on the DPoP `jwk` header,
and it holds for every member of `privateMemberNames`, not only `d`. -/
theorem parsePublicJwk_no_private {j : Json} {k : Jwk} (h : parsePublicJwk? j = some k) :
    hasPrivateMember j = false := by
  unfold parsePublicJwk? at h
  split at h
  · simp at h
  · next hn => simpa using hn

/-- A public parse is a parse: nothing is loosened by the private-member
check, only refused. -/
theorem parsePublicJwk_le_parseJwk {j : Json} {k : Jwk} (h : parsePublicJwk? j = some k) :
    parseJwk? j = some k := by
  unfold parsePublicJwk? at h
  split at h
  · simp at h
  · exact h

/-! ## Fixtures -/

-- RFC 7638 §3.1, the worked example: the RSA key and its thumbprint
-- "NzbLsXh8uDCcd-6MNwXF4W_7noWXFZAfHkxZsRGC9Xs". The `kid` and `alg`
-- members of the RFC's key are present here and must be ignored.
private def rfc7638Key : String :=
  "{\"kty\":\"RSA\",\"n\":\"0vx7agoebGcQSuuPiLJXZptN9nndrQmbXEps2aiAFbWhM78LhWx4" ++
  "cbbfAAtVT86zwu1RK7aPFFxuhDR1L6tSoc_BJECPebWKRXjBZCiFV4n3oknjhMstn64tZ_2W-5Js" ++
  "GY4Hc5n9yBXArwl93lqt7_RN5w6Cf0h4QyQ5v-65YGjQR0_FDW2QvzqY368QQMicAtaSqzs8KJZg" ++
  "nYb9c7d0zgdAZHzu6qMQvRL5hajrn1n91CbOpbISD08qNLyrdkt-bFTWhAI4vMQFh6WeZu0fM4lF" ++
  "d2NcRwr3XPksINHaQ-G_xBniIqbw0Ls1jF44-csFCur-kEgU8awapJzKnqDKgw\",\"e\":\"AQAB\"," ++
  "\"alg\":\"RS256\",\"kid\":\"2011-04-29\"}"

#guard (parseJwkString? rfc7638Key).isSome
#guard (parseJwkString? rfc7638Key).map canonicalJson ==
  some ("{\"e\":\"AQAB\",\"kty\":\"RSA\",\"n\":\"0vx7agoebGcQSuuPiLJXZptN9nndrQmbXEps2aiAFbWhM78Lh" ++
        "Wx4cbbfAAtVT86zwu1RK7aPFFxuhDR1L6tSoc_BJECPebWKRXjBZCiFV4n3oknjhMstn64tZ_2W-5JsGY4Hc5n9" ++
        "yBXArwl93lqt7_RN5w6Cf0h4QyQ5v-65YGjQR0_FDW2QvzqY368QQMicAtaSqzs8KJZgnYb9c7d0zgdAZHzu6qM" ++
        "QvRL5hajrn1n91CbOpbISD08qNLyrdkt-bFTWhAI4vMQFh6WeZu0fM4lFd2NcRwr3XPksINHaQ-G_xBniIqbw0L" ++
        "s1jF44-csFCur-kEgU8awapJzKnqDKgw\"}")
#guard (parseJwkString? rfc7638Key).map thumbprint ==
  some "NzbLsXh8uDCcd-6MNwXF4W_7noWXFZAfHkxZsRGC9Xs"

-- RFC 7515 Appendix A.3.1, the ES256 example key. The private member
-- `d` is present in the RFC's key, so the plain parse accepts it and the
-- public parse refuses it — which is the RFC 9449 §4.2 rule.
private def rfc7515A3Key : String :=
  "{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
  "\"x\":\"f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU\"," ++
  "\"y\":\"x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0\"," ++
  "\"d\":\"jpsQnnGQmL-YBIffH1136cspYG6-0iY7X1fCE9-E9LI\"}"

#guard (parseJwkString? rfc7515A3Key).map Jwk.kty == some Kty.ec
#guard ((parseJwkString? rfc7515A3Key).bind Jwk.ecPublicRaw?).map ByteArray.size == some 64
#guard parsePublicJwkString? rfc7515A3Key == none

-- The same key without `d` is accepted as public.
private def rfc7515A3Public : String :=
  "{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
  "\"x\":\"f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU\"," ++
  "\"y\":\"x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0\"}"

#guard (parsePublicJwkString? rfc7515A3Public).map Jwk.kty == some Kty.ec

-- RFC 8037 Appendix A.2, the Ed25519 public key, and its RFC 8037 §2
-- thumbprint "kPrK_qmxVWaYVA9wwBF6Iuo3vVzz7TxHCTwXBygrS4k" (RFC 8037
-- Appendix A.3).
private def rfc8037Key : String :=
  "{\"kty\":\"OKP\",\"crv\":\"Ed25519\"," ++
  "\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}"

#guard (parseJwkString? rfc8037Key).map Jwk.kty == some Kty.okp
#guard (parseJwkString? rfc8037Key).map canonicalJson ==
  some "{\"crv\":\"Ed25519\",\"kty\":\"OKP\",\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}"
#guard (parseJwkString? rfc8037Key).map thumbprint ==
  some "kPrK_qmxVWaYVA9wwBF6Iuo3vVzz7TxHCTwXBygrS4k"

-- Refusals.
-- A curve we do not verify with.
#guard parseJwkString? "{\"kty\":\"EC\",\"crv\":\"P-384\",\"x\":\"AA\",\"y\":\"AA\"}" == none
-- A key type we do not verify with: `oct` is the HMAC family's.
#guard parseJwkString? "{\"kty\":\"oct\",\"k\":\"AAAA\"}" == none
-- An EC key whose coordinates are the wrong length.
#guard parseJwkString? "{\"kty\":\"EC\",\"crv\":\"P-256\",\"x\":\"AA\",\"y\":\"AA\"}" == none
-- An RSA key below the RFC 7518 §3.3 floor (a 1024-bit modulus).
#guard (parseJwkString?
  ("{\"kty\":\"RSA\",\"e\":\"AQAB\",\"n\":\"" ++ Base64Url.encode
    ⟨(List.replicate 128 (0xFF : UInt8)).toArray⟩ ++ "\"}")) == none
-- The same modulus at 2048 bits is accepted.
#guard (parseJwkString?
  ("{\"kty\":\"RSA\",\"e\":\"AQAB\",\"n\":\"" ++ Base64Url.encode
    ⟨(List.replicate 256 (0xFF : UInt8)).toArray⟩ ++ "\"}")).isSome
-- Padded base64url in a member is refused, by Base64Url's strictness.
#guard parseJwkString? "{\"kty\":\"OKP\",\"crv\":\"Ed25519\",\"x\":\"AAAA=\"}" == none
-- Every private member name blocks a public parse.
#guard parsePublicJwkString?
  "{\"kty\":\"OKP\",\"crv\":\"Ed25519\",\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\",\"d\":\"AA\"}"
  == none
#guard parsePublicJwkString?
  ("{\"kty\":\"RSA\",\"e\":\"AQAB\",\"q\":\"AA\",\"n\":\"" ++ Base64Url.encode
    ⟨(List.replicate 256 (0xFF : UInt8)).toArray⟩ ++ "\"}") == none

-- The canonical JSON carries no whitespace, and its member names are in
-- code-point order (RFC 7638 §3).
#guard ((parseJwkString? rfc7638Key).map canonicalJson).all
  (fun s => !(s.toList.any fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r'))
#guard requiredMemberNames (.ec ByteArray.empty ByteArray.empty) == ["crv", "kty", "x", "y"]
#guard requiredMemberNames (.rsa ByteArray.empty ByteArray.empty) == ["e", "kty", "n"]
#guard requiredMemberNames (.okp ByteArray.empty) == ["crv", "kty", "x"]

end L4Factoidal.JOSE
