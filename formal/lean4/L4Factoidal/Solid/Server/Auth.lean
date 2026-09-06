/-
L4Factoidal.Solid.Server.Auth — Solid-OIDC authentication for the Solid
server: a WebID from a DPoP-bound access token, decided in Lean.

## What this replaces

Until now the Solid server took the requester's WebID from its handle
configuration: the Node host verified the credential and passed the
answer in. `docs/designissues/2026-09-06-lws-and-solid-protocols.md`
§2 "Authentication is a boundary" recorded that as a deliberate
boundary, with the reason that no JOSE layer existed in the tree. It
does now (`L4Factoidal/JOSE/`), so the decision moves here and the host
keeps only what a host must do: hold the socket, and fetch the
identity provider's keys over the network.

The split is the same one the rest of this project uses. The host
performs I/O. Lean decides. `tools/host-purity-lint` exists to stop the
host deciding, and this module is what it can now point at.

## Off by default

`AuthConfig.enforceAuth` is `false` unless a deployment sets it, exactly
as `ServerConfig.enforceWac` is. With it false, `authenticate` answers
`disabled` and `Methods.requesterOf` keeps taking the WebID from the
handle configuration, so every existing host suite and interop script
behaves as before. With it true, a request carrying no credential is
`anonymous` and a request carrying a bad one is `refused` with the
reason named.

Two switches rather than one, because they are two decisions: whether
the server BELIEVES a claimed identity (this module) and whether it
ENFORCES an access policy over it (`WAC.lean`). A deployment that turns
on authentication without Web Access Control still gets a WebID in
`WAC-Allow`; one that turns on Web Access Control without
authentication enforces a policy over a WebID it was told, which is
what the first slice did.

## What is checked, and in what order

  1. `Authorization` is present. Absent means anonymous, not refused: an
     unauthenticated read of a public resource is a normal Solid
     request.
  2. Its scheme is `DPoP` (RFC 9449 §7.1). A `Bearer` credential is
     REFUSED, not accepted: a token bound to a key, presented without
     the proof, is being used as a bearer token, which is the thing DPoP
     exists to stop.
  3. A `DPoP` header field is present.
  4. The access token is a JWS this project can verify, under one of the
     identity provider's keys the host supplied. The `Jws` allowlist
     applies, so `alg: none` and the HMAC family never reach a key
     (`Jws.hmacFamily_not_allowed`, `Jws.alg_none_not_allowed`).
  5. Its claims validate against the deployment's policy: the pinned
     issuer, this server as the audience, an expiry that has not passed
     (`Jwt.validate_ok_iff`).
  6. It carries `cnf.jkt` (RFC 7800 §3.1, RFC 9449 §6). A token bound to
     no key is refused; accepting it would make it a bearer token again.
  7. The DPoP proof validates for THIS method and THIS URI, its `ath` is
     the hash of THIS token, and its key's thumbprint is the `cnf.jkt`
     (`DPoP.proof_ok_thumbprint_bound`, `DPoP.proof_ok_ath_bound`).
  8. A WebID is available: the Solid-OIDC `webid` claim, or `sub` when
     the deployment has declared the issuer authoritative for its
     subjects.

## What the host still does, and why it cannot be moved

Fetching the identity provider's JWKS is a network read, so it is the
host's, as every other network read in this project is. The host passes
the keys in `AuthConfig.idpKeys` and decides nothing: which key verifies
a token, and whether the token is acceptable, are decided here. The
replay store behind `jtiFresh` is the same shape — the host remembers,
Lean decides what remembering means.
-/
import L4Factoidal.Solid.Server.Methods
import L4Factoidal.Solid.Server.AuthConfig

namespace L4Factoidal.Solid.Server

open L4Factoidal.JOSE
open L4Factoidal.HTTP
open L4Factoidal.JSON

/-! ## Outcome -/

/-- Why a credential was refused. Every constructor names the check that
failed; there is no generic failure. -/
inductive AuthRefusal where
  | malformedAuthorization
  | wrongScheme (scheme : String)
  | missingProof
  | noTrustedKey (outcomes : List Outcome)
  | claimsUnreadable
  | claimsRefused (outcome : ClaimsOutcome)
  | tokenNotBound
  | proofRefused (outcome : ProofOutcome)
  | webIdMissing
  deriving Repr, BEq, DecidableEq

/-- What `authenticate` decided. -/
inductive AuthResult where
  /-- Enforcement is off; the handle configuration's WebID stands. -/
  | disabled
  /-- No credential was presented. Not a refusal: a public read needs
  none. -/
  | anonymous
  /-- A WebID, and the JWK thumbprint the token is bound to. -/
  | authenticated (webId : String) (jkt : String)
  | refused (reason : AuthRefusal)
  deriving Repr, BEq, DecidableEq

/-! ## Reading the request -/

/-- Split an `Authorization` field value into its scheme and the rest
(RFC 9110 §11.4). `none` when there is no space, which is not a
credential of any scheme. -/
def splitScheme (v : String) : Option (String × String) :=
  match v.splitOn " " with
  | [] => none
  | [_] => none
  | s :: rest => some (s, " ".intercalate rest)

/-- The absolute request URI, for the RFC 9449 §4.3 `htu` comparison.
The storage's `baseIri` plus the request path; the query is not
appended, because `htu` ignores it and `DPoP.htuMatches` strips it from
both sides anyway. -/
def requestUri (cfg : ServerConfig) (r : HTTP.Request) : String :=
  let base := cfg.lws.baseIri
  let trimmed := if base.endsWith "/" then (base.dropEnd 1).toString else base
  trimmed ++ r.path

/-- The DPoP request description. -/
def dpopRequest (cfg : ServerConfig) (r : HTTP.Request) : ProofRequest :=
  { method := r.method, uri := requestUri cfg r }

/-- Read the access token's claims. -/
def tokenClaims? (token : String) : Option Claims :=
  match preKey token with
  | .error _ => none
  | .ok (c, _) =>
      (Base64Url.decode c.payloadB64).bind fun b =>
        (String.fromUTF8? b).bind fun s => (parseJson? s).bind parseClaims?

/-- Try each of the identity provider's keys. `none` with the outcome of
every attempt when none verifies — the outcomes are carried so a
deployment can tell "no key matched" from "the algorithm is not
allowed", which are different operational problems. -/
def verifyWithAnyKey (V : Verifiers) : List Jwk → String → Except (List Outcome) Jwk
  | [], _ => .error []
  | k :: ks, token =>
      let o := verifyCompact V k token
      if o == .verified then .ok k
      else match verifyWithAnyKey V ks token with
        | .ok k' => .ok k'
        | .error os => .error (o :: os)

/-- The WebID a validated token carries. The Solid-OIDC `webid` claim
first; `sub` only when the deployment has declared the issuer
authoritative for its subjects. -/
def webIdOf (cfg : AuthConfig) (c : Claims) : Option String :=
  match c.webid with
  | some w => some w
  | none => if cfg.subjectIsWebId then c.sub else none

/-! ## The decision -/

/-- The checks from the access token onward, once the two header fields
have been read. Split out so the theorems below can name it. -/
def checkCredential (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request)
    (token proof : String) : AuthResult :=
  match verifyWithAnyKey V cfg.auth.idpKeys token with
  | .error os => .refused (.noTrustedKey os)
  | .ok _ =>
      match tokenClaims? token with
      | none => .refused .claimsUnreadable
      | some c =>
          match validate cfg.auth.policy c with
          | .ok =>
              match c.cnfJkt with
              | none => .refused .tokenNotBound
              | some jkt =>
                  match validateProof V cfg.auth.proofPolicy (dpopRequest cfg r)
                          (some token.toUTF8) (some jkt) proof with
                  | .ok =>
                      match webIdOf cfg.auth c with
                      | none => .refused .webIdMissing
                      | some w => .authenticated w jkt
                  | po => .refused (.proofRefused po)
          | vo => .refused (.claimsRefused vo)

/-- Solid-OIDC authentication for one request. -/
def authenticate (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request) : AuthResult :=
  if !cfg.auth.enforceAuth then .disabled
  else match r.header? "authorization" with
    | none => .anonymous
    | some authz =>
        match splitScheme authz with
        | none => .refused .malformedAuthorization
        | some (scheme, token) =>
            if scheme.toLower != "dpop" then .refused (.wrongScheme scheme)
            else match r.header? "dpop" with
              | none => .refused .missingProof
              | some proof => checkCredential V cfg r token proof

/-- The requester the Web Access Control decision is made about.

With authentication off this is exactly `Methods.requesterOf`: the WebID
comes from the handle configuration, which is what every existing host
suite depends on (`requesterOf_unchanged_when_auth_off`). With it on,
the WebID is the one this module decided, and an anonymous or refused
request carries none. -/
def authenticatedRequester (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request) : Requester :=
  match authenticate V cfg r with
  | .disabled => requesterOf cfg r
  | .authenticated w _ => { webId := some w, origin := r.header? "origin" }
  | _ => { webId := none, origin := r.header? "origin" }

/-! ## Theorems -/

/-- **Off by default, and off means unchanged.** With `enforceAuth`
false the answer is `disabled` for every request and every set of
verifiers. -/
theorem authenticate_disabled (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request)
    (h : cfg.auth.enforceAuth = false) : authenticate V cfg r = .disabled := by
  simp [authenticate, h]

/-- **With authentication off the requester is the one the server
already computed**, so no existing behaviour changes. -/
theorem requesterOf_unchanged_when_auth_off (V : Verifiers) (cfg : ServerConfig)
    (r : HTTP.Request) (h : cfg.auth.enforceAuth = false) :
    authenticatedRequester V cfg r = requesterOf cfg r := by
  simp [authenticatedRequester, authenticate_disabled V cfg r h]

/-- **A request with no `Authorization` field is anonymous, never
authenticated.** -/
theorem authenticate_no_credential (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request)
    (he : cfg.auth.enforceAuth = true) (h : r.header? "authorization" = none) :
    authenticate V cfg r = .anonymous := by
  simp [authenticate, he, h]

/-- **A `Bearer` credential is refused, not accepted.** An access token
bound to a key, presented without its proof, is being used as a bearer
token; RFC 9449 §7.1 makes `DPoP` the scheme, and this is the check that
a deployment cannot be downgraded past. -/
theorem authenticate_bearer_refused (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request)
    {scheme rest : String}
    (he : cfg.auth.enforceAuth = true)
    (h : r.header? "authorization" = some (scheme ++ " " ++ rest))
    (hsplit : splitScheme (scheme ++ " " ++ rest) = some (scheme, rest))
    (hne : scheme.toLower ≠ "dpop") :
    authenticate V cfg r = .refused (.wrongScheme scheme) := by
  simp [authenticate, he, h, hsplit, hne]

/-- **A DPoP credential with no proof is refused.** -/
theorem authenticate_missing_proof (V : Verifiers) (cfg : ServerConfig) (r : HTTP.Request)
    {authz scheme token : String}
    (he : cfg.auth.enforceAuth = true)
    (h : r.header? "authorization" = some authz)
    (hsplit : splitScheme authz = some (scheme, token))
    (hdpop : scheme.toLower = "dpop")
    (hp : r.header? "dpop" = none) :
    authenticate V cfg r = .refused .missingProof := by
  simp [authenticate, he, h, hsplit, hdpop, hp]

/-- **An authenticated request presented a DPoP proof that validated for
this method and this URI, against the token it presented.** Everything
the RFC 9449 §4.3 and §6.1 checks establish is available from here:
compose with `DPoP.proof_ok_thumbprint_bound` for the key binding and
`DPoP.proof_ok_ath_bound` for the token hash. -/
theorem checkCredential_authenticated_proof_ok {V : Verifiers} {cfg : ServerConfig}
    {r : HTTP.Request} {token proof w jkt : String}
    (h : checkCredential V cfg r token proof = .authenticated w jkt) :
    validateProof V cfg.auth.proofPolicy (dpopRequest cfg r)
      (some token.toUTF8) (some jkt) proof = .ok := by
  unfold checkCredential at h
  repeat' split at h
  all_goals simp_all

/-- **An authenticated request's token was accepted by the claims
policy**, so its issuer is the pinned one and it has not expired
(`Jwt.validate_ok_issuer_pinned`, `Jwt.validate_ok_unexpired`). -/
theorem checkCredential_authenticated_claims_ok {V : Verifiers} {cfg : ServerConfig}
    {r : HTTP.Request} {token proof w jkt : String}
    (h : checkCredential V cfg r token proof = .authenticated w jkt) :
    ∃ c, tokenClaims? token = some c ∧ validate cfg.auth.policy c = .ok := by
  unfold checkCredential at h
  repeat' split at h
  all_goals simp_all

/-- **An authenticated request's token was bound to a key.** A token
with no `cnf.jkt` never authenticates. -/
theorem checkCredential_authenticated_bound {V : Verifiers} {cfg : ServerConfig}
    {r : HTTP.Request} {token proof w jkt : String}
    (h : checkCredential V cfg r token proof = .authenticated w jkt) :
    ∃ c, tokenClaims? token = some c ∧ c.cnfJkt = some jkt := by
  unfold checkCredential at h
  repeat' split at h
  all_goals simp_all

/-- **An authenticated request's WebID came from the token**, either
from the Solid-OIDC `webid` claim or, when the deployment allows it,
from `sub`. It is never invented. -/
theorem checkCredential_authenticated_webid {V : Verifiers} {cfg : ServerConfig}
    {r : HTTP.Request} {token proof w jkt : String}
    (h : checkCredential V cfg r token proof = .authenticated w jkt) :
    ∃ c, tokenClaims? token = some c ∧ webIdOf cfg.auth c = some w := by
  unfold checkCredential at h
  repeat' split at h
  all_goals simp_all

/-- **A key that does not verify the token never authenticates.** With
`Jws.hmacFamily_not_allowed` this is the statement that no HMAC-signed
access token is accepted whatever key the host supplied, and with
`Jws.verify_independent_of_key_before_key_stage` that such a token never
reaches a key at all. -/
theorem checkCredential_no_key_refused {V : Verifiers} {cfg : ServerConfig}
    {r : HTTP.Request} {token proof : String} {os : List Outcome}
    (h : verifyWithAnyKey V cfg.auth.idpKeys token = .error os) :
    checkCredential V cfg r token proof = .refused (.noTrustedKey os) := by
  simp [checkCredential, h]

/-- **An empty key list authenticates nothing.** A deployment that turns
authentication on without configuring its identity provider's keys
refuses every credential; it does not fall open. -/
theorem checkCredential_no_keys {V : Verifiers} {cfg : ServerConfig} {r : HTTP.Request}
    {token proof : String} (h : cfg.auth.idpKeys = []) :
    checkCredential V cfg r token proof = .refused (.noTrustedKey []) := by
  apply checkCredential_no_key_refused
  simp [h, verifyWithAnyKey]

/-! ## Fixtures

The checks that need a real signature are the `solid-oidc` section of
`lake exe l4jose-probe`; an extern does not evaluate at compile time.
What is checked here is the header reading and the two off-by-default
guarantees. -/

private def stubV : Verifiers :=
  { es256 := fun _ _ _ => true, rs256 := fun _ _ _ _ => true, eddsa := fun _ _ _ => true }

private def offCfg : ServerConfig := {}
private def onCfg : ServerConfig := { auth := { enforceAuth := true } }

private def req (headers : List (String × String)) : HTTP.Request :=
  { method := "GET", path := "/r", queryStr := "", headers := headers }

#guard authenticate stubV offCfg (req []) == .disabled
#guard authenticate stubV offCfg (req [("authorization", "DPoP abc"), ("dpop", "x")])
        == .disabled
#guard authenticate stubV onCfg (req []) == .anonymous
#guard authenticate stubV onCfg (req [("authorization", "Bearer abc")])
        == .refused (.wrongScheme "Bearer")
#guard authenticate stubV onCfg (req [("authorization", "Basic dXNlcjpwdw==")])
        == .refused (.wrongScheme "Basic")
#guard authenticate stubV onCfg (req [("authorization", "DPoP abc")])
        == .refused .missingProof
#guard authenticate stubV onCfg (req [("authorization", "DPoP")])
        == .refused .malformedAuthorization
-- The scheme is case insensitive (RFC 9110 §11.1), the token is not.
#guard authenticate stubV onCfg (req [("authorization", "dpop abc")])
        == .refused .missingProof
-- With no identity-provider keys configured, every credential is
-- refused. It does not fall open.
#guard authenticate stubV onCfg (req [("authorization", "DPoP abc"), ("dpop", "y")])
        == .refused (.noTrustedKey [])

-- The `htu` the proof must name.
#guard requestUri offCfg (req []) == "http://localhost/r"
#guard requestUri { lws := { baseIri := "https://storage.example/" } } (req [])
        == "https://storage.example/r"

end L4Factoidal.Solid.Server
