/-
L4Factoidal.JOSE.DPoP — OAuth 2.0 Demonstrating Proof of Possession
(RFC 9449) proof validation, and the binding between a DPoP proof and
the access token it accompanies.

Solid-OIDC requires DPoP: an access token alone is not enough, because a
bearer token that leaks is a bearer token anyone can spend. RFC 9449 §6
binds the token to a key by putting the key's RFC 7638 thumbprint in the
token's `cnf.jkt` claim; the client then proves possession of that key on
every request by signing a short-lived JWT over the method and URI.
`validateProof` is that check, and `proof_ok_thumbprint_bound` is the
theorem that the binding is what makes the proof mean anything.

## The checks, and where each comes from (RFC 9449 §4.3)

  1. The proof is a well-formed JWS with a header, and its `typ` is
     `dpop+jwt` (§4.2). A proof with another `typ`, or none, is refused
     — this is what stops a JWT minted for another purpose from being
     replayed as a proof.
  2. Its `alg` is an asymmetric algorithm the verifier supports. That is
     `JOSE/Jws.lean`'s allowlist, so `alg: none` and the HMAC family are
     already excluded by `Jws.hmacFamily_not_allowed` and
     `Jws.alg_none_not_allowed`.
  3. The header carries a `jwk` (§4.2) and it is a PUBLIC key.
     `Jwk.parsePublicJwk?` refuses any object with a private member, and
     `Jwk.parsePublicJwk_no_private` proves it.
  4. The signature verifies with THAT key. The proof is self-signed by
     construction; step 8 is what stops that from being circular.
  5. `htm` equals the request's HTTP method.
  6. `htu` equals the request URI "without query and fragment parts"
     (§4.3 item 9). `htuMatches_iff` states the comparison is exactly
     between the stripped forms, `htu_query_ignored` and
     `htu_fragment_ignored` that a difference in those parts is
     accepted, and `htuMatches_iff` that a difference anywhere else is
     refused.
  7. `iat` is within an acceptable window of the current time (§4.3
     item 12, §11.1). The window is a parameter; nothing here reads a
     clock.
  8. `jti` is present and has not been seen (§4.3 item 11, §11.1). The
     replay store is not this module's business, so freshness arrives as
     a caller-supplied predicate. It is a `Bool`-valued function, so the
     whole check stays total and decidable.
  9. When an access token is presented, `ath` equals the base64url of
     the SHA-256 of that token's value (§4.3 item 10, §4.1). A proof
     without `ath` is refused whenever a token is presented, so a proof
     captured on one request cannot be attached to another.
 10. The access token's `cnf.jkt` equals the RFC 7638 thumbprint of the
     proof's key (§6.1). Without this the proof proves possession of
     SOME key, which is worth nothing.

## Every check is a total, decidable function

There is no `partial def` in this module, no `IO`, no clock call, and no
exception. `ProofOutcome` derives `DecidableEq`, the freshness oracle is
`String → Bool`, and `validateProof` is a plain `def`, so its result is
computed by `#guard` at build time. The `tools/lean-hygiene-audit.py`
gate is what keeps that true.
-/
import L4Factoidal.JOSE.Jwt

namespace L4Factoidal.JOSE

open L4Factoidal.JSON
open L4Factoidal.Crypto

/-! ## The `htu` comparison -/

/-- RFC 9449 §4.3 item 9 compares `htu` with "the HTTP URI value for the
HTTP request in which the JWT was received, ignoring any query and
fragment parts". RFC 3986 §3 puts the query after the first `?` and the
fragment after the first `#`, and neither character may appear earlier
in a URI without being percent-encoded, so removing everything from the
first occurrence of either removes exactly those two components. -/
def stripQueryAndFragment (u : String) : String :=
  String.ofList (u.toList.takeWhile fun c => c != '?' && c != '#')

/-- Whether a proof's `htu` names the request's URI. -/
def htuMatches (claimed actual : String) : Bool :=
  stripQueryAndFragment claimed == stripQueryAndFragment actual

/-! ## The proof's claims -/

/-- The RFC 9449 §4.2 payload claims. `nonce` (§8) is read but not
enforced here: a server that issues nonces supplies its own predicate
over this field. -/
structure ProofClaims where
  jti : Option String := none
  htm : Option String := none
  htu : Option String := none
  iat : Option Int := none
  ath : Option String := none
  nonce : Option String := none
  deriving Repr, DecidableEq, BEq

/-- Parse the payload. As in `JOSE/Jwt.lean`, a member of the wrong JSON
type fails the parse rather than being read as absent. -/
def parseProofClaims? (j : Json) : Option ProofClaims :=
  match j with
  | .object _ => do
      let str (n : String) : Option (Option String) :=
        match j.field? n with
        | none => some none
        | some (.string s) => some (some s)
        | some _ => none
      let jti ← str "jti"
      let htm ← str "htm"
      let htu ← str "htu"
      let ath ← str "ath"
      let nonce ← str "nonce"
      let iat ←
        match j.field? "iat" with
        | none => some none
        | some v => (numericDate? v).map some
      some { jti, htm, htu, iat, ath, nonce }
  | _ => none

/-! ## Policy and outcome -/

/-- What the verifier must state before a proof can be judged. -/
structure ProofPolicy where
  /-- The instant to judge against (RFC 7519 §2 `NumericDate` seconds). -/
  now : Int
  /-- How far either side of `now` an `iat` may fall (RFC 9449 §11.1
  recommends a brief window). -/
  iatWindow : Int
  /-- Replay detection (RFC 9449 §11.1). `true` means "this `jti` has not
  been seen". Supplied by the caller because the store is the caller's. -/
  jtiFresh : String → Bool

/-- The HTTP request the proof must be about. -/
structure Request where
  method : String
  uri : String
  deriving Repr, DecidableEq

/-- Why a proof was or was not accepted. -/
inductive ProofOutcome where
  | ok
  | jwsRefused (r : Refusal)
  | typMissing
  | typWrong (typ : String)
  | jwkMissing
  | jwkRejected
  | signatureNotVerified (o : Outcome)
  | payloadUnreadable
  | htmMissing
  | htmMismatch
  | htuMissing
  | htuMismatch
  | jtiMissing
  | jtiReplayed
  | iatMissing
  | iatOutOfWindow
  | athMissing
  | athMismatch
  | keyThumbprintMismatch
  | tokenNotBound
  /-- Unreachable: `diagnoseProof` is called only when `proofAccepts`
  already answered `false`. It is a refusal, so no path to `.ok` is
  created by its existence. -/
  | noRefusalFound
  deriving DecidableEq, Repr, BEq

/-- RFC 9449 §4.1: the `ath` value for an access token is the base64url
encoding of the SHA-256 digest of the token's ASCII value. -/
def athFor (accessToken : ByteArray) : String :=
  Base64Url.encode (sha256 accessToken)

/-! ## Validation

The shape is the same as `Jwt.validate`: ONE `Bool` says whether the
proof is accepted, and a separate cascade says which check failed first.
`validateProof` is `if proofAccepts then .ok else diagnoseProof`, and
`diagnoseProof_ne_ok` proves the cascade cannot accept, so there is
exactly one accepting path and it is the `Bool`. -/

/-- The proof's payload claims. -/
def payloadClaims? (c : Compact) : Option ProofClaims :=
  (Base64Url.decode c.payloadB64).bind fun b =>
    (String.fromUTF8? b).bind fun s => (parseJson? s).bind parseProofClaims?

/-- The public key in the proof's `jwk` header (RFC 9449 §4.2). `none`
when the member is absent, is not a key of a supported type, or carries
private material. -/
def proofKey? (hdr : Header) : Option Jwk :=
  (hdr.json.field? "jwk").bind parsePublicJwk?

/-- **The single accepting condition** for a DPoP proof (RFC 9449 §4.3),
and for its binding to an access token (§6.1).

`accessToken` is the token presented with the request, if any; `cnfJkt`
is that token's `cnf.jkt` claim, which the caller has already validated
with `Jwt.validate`. When a token is presented, BOTH `ath` and the
thumbprint binding are required: a proof presented with a token that is
bound to no key is not accepted as an unbound proof. -/
def proofAccepts (V : Verifiers) (pol : ProofPolicy) (req : Request)
    (accessToken : Option ByteArray) (cnfJkt : Option String)
    (proof : String) : Bool :=
  match preKey proof with
  | .error _ => false
  | .ok (c, hdr) =>
      (hdr.json.getString? "typ" == some "dpop+jwt") &&
      (match proofKey? hdr with
       | none => false
       | some key =>
           (verifyCompact V key proof == .verified) &&
           (match payloadClaims? c with
            | none => false
            | some pc =>
                (pc.htm == some req.method) &&
                (match pc.htu with
                 | none => false
                 | some u => htuMatches u req.uri) &&
                (match pc.iat with
                 | none => false
                 | some i => decide (pol.now - i ≤ pol.iatWindow ∧ i - pol.now ≤ pol.iatWindow)) &&
                (match pc.jti with
                 | none => false
                 | some ji => pol.jtiFresh ji) &&
                (match accessToken with
                 | none => true
                 | some tokv =>
                     (pc.ath == some (athFor tokv)) &&
                     (cnfJkt == some (thumbprint key)))))

/-- Which check failed first. Reached only when `proofAccepts` already
said no, so `noRefusalFound` is unreachable; it exists because the
cascade must be total, and it is a refusal, never an acceptance
(`diagnoseProof_ne_ok`). Reordering this changes only which refusal is
reported. -/
def diagnoseProof (V : Verifiers) (pol : ProofPolicy) (req : Request)
    (accessToken : Option ByteArray) (cnfJkt : Option String)
    (proof : String) : ProofOutcome :=
  match preKey proof with
  | .error r => .jwsRefused r
  | .ok (c, hdr) =>
      match hdr.json.getString? "typ" with
      | none => .typMissing
      | some t =>
          if t ≠ "dpop+jwt" then .typWrong t
          else if (hdr.json.field? "jwk").isNone then .jwkMissing
          else match proofKey? hdr with
            | none => .jwkRejected
            | some key =>
                if verifyCompact V key proof ≠ .verified then
                  .signatureNotVerified (verifyCompact V key proof)
                else match payloadClaims? c with
                  | none => .payloadUnreadable
                  | some pc =>
                      match pc.htm with
                      | none => .htmMissing
                      | some m =>
                          if m ≠ req.method then .htmMismatch
                          else match pc.htu with
                            | none => .htuMissing
                            | some u =>
                                if !htuMatches u req.uri then .htuMismatch
                                else match pc.iat with
                                  | none => .iatMissing
                                  | some i =>
                                      if pol.now - i > pol.iatWindow ∨
                                         i - pol.now > pol.iatWindow then .iatOutOfWindow
                                      else match pc.jti with
                                        | none => .jtiMissing
                                        | some ji =>
                                            if !pol.jtiFresh ji then .jtiReplayed
                                            else match accessToken with
                                              | none => .noRefusalFound
                                              | some tokv =>
                                                  match pc.ath with
                                                  | none => .athMissing
                                                  | some a =>
                                                      if a ≠ athFor tokv then .athMismatch
                                                      else match cnfJkt with
                                                        | none => .tokenNotBound
                                                        | some jkt =>
                                                            if jkt ≠ thumbprint key then
                                                              .keyThumbprintMismatch
                                                            else .noRefusalFound

/-- Validate a DPoP proof (RFC 9449 §4.3) and its binding to an access
token (§6.1). -/
def validateProof (V : Verifiers) (pol : ProofPolicy) (req : Request)
    (accessToken : Option ByteArray) (cnfJkt : Option String)
    (proof : String) : ProofOutcome :=
  if proofAccepts V pol req accessToken cnfJkt proof then .ok
  else diagnoseProof V pol req accessToken cnfJkt proof

/-! ## Theorems -/

/-- **The `htu` comparison is exactly the comparison of the stripped
forms.** Two URIs match when, and only when, they agree once the query
and the fragment are removed. -/
theorem htuMatches_iff (claimed actual : String) :
    htuMatches claimed actual = true ↔
      stripQueryAndFragment claimed = stripQueryAndFragment actual := by
  simp [htuMatches]

/-- Stripping removes everything from the first `?`. -/
theorem strip_takeWhile (u : String) :
    (stripQueryAndFragment u).toList =
      u.toList.takeWhile (fun c => c != '?' && c != '#') := by
  simp [stripQueryAndFragment]

/-- `takeWhile` keeps a whole prefix all of whose members satisfy the
predicate. -/
theorem takeWhile_all {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ c ∈ l, p c = true) → l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
      have ha : p a = true := h a (by simp)
      simp [ha, takeWhile_all p l (fun c hc => h c (by simp [hc]))]

/-- `takeWhile` stops at the first member that fails, and keeps exactly
the prefix before it. -/
theorem takeWhile_append_neg {α : Type} (p : α → Bool) (x : α) (r : List α)
    (hx : p x = false) :
    ∀ (l : List α), (∀ c ∈ l, p c = true) → (l ++ x :: r).takeWhile p = l
  | [], _ => by simp [hx]
  | a :: l, h => by
      have ha : p a = true := h a (by simp)
      simp [ha, takeWhile_append_neg p x r hx l (fun c hc => h c (by simp [hc]))]

/-- **A query string is ignored.** If `base` contains neither `?` nor
`#`, then `base` and `base ++ "?" ++ q` have the same stripped form, so
they match for every query `q`. -/
theorem htu_query_ignored (base q : String)
    (h : ∀ c ∈ base.toList, c ≠ '?' ∧ c ≠ '#') :
    htuMatches (base ++ "?" ++ q) base = true := by
  have hall : ∀ c ∈ base.toList, (fun c => c != '?' && c != '#') c = true := by
    intro c hc
    obtain ⟨h1, h2⟩ := h c hc
    simp [h1, h2]
  rw [htuMatches_iff]
  unfold stripQueryAndFragment
  congr 1
  rw [takeWhile_all _ base.toList hall]
  have hcat : (base ++ "?" ++ q).toList = base.toList ++ '?' :: q.toList := by
    simp
  rw [hcat, takeWhile_append_neg _ '?' q.toList (by decide) base.toList hall]

/-- **A fragment is ignored**, by the same argument. -/
theorem htu_fragment_ignored (base f : String)
    (h : ∀ c ∈ base.toList, c ≠ '?' ∧ c ≠ '#') :
    htuMatches (base ++ "#" ++ f) base = true := by
  have hall : ∀ c ∈ base.toList, (fun c => c != '?' && c != '#') c = true := by
    intro c hc
    obtain ⟨h1, h2⟩ := h c hc
    simp [h1, h2]
  rw [htuMatches_iff]
  unfold stripQueryAndFragment
  congr 1
  rw [takeWhile_all _ base.toList hall]
  have hcat : (base ++ "#" ++ f).toList = base.toList ++ '#' :: f.toList := by
    simp
  rw [hcat, takeWhile_append_neg _ '#' f.toList (by decide) base.toList hall]

/-- **A difference outside the query and fragment is refused.** Contrapositive
of `htuMatches_iff`: scheme, authority and path all survive the strip, so a
difference in any of them makes the stripped forms differ and the match
fail. -/
theorem htu_refuses_difference {claimed actual : String}
    (h : stripQueryAndFragment claimed ≠ stripQueryAndFragment actual) :
    htuMatches claimed actual = false := by
  simp [htuMatches, h]

/-- The diagnosis never accepts, so `validateProof` has exactly one path
to `.ok`. -/
theorem diagnoseProof_ne_ok (V : Verifiers) (pol : ProofPolicy) (req : Request)
    (at? : Option ByteArray) (jkt? : Option String) (proof : String) :
    diagnoseProof V pol req at? jkt? proof ≠ .ok := by
  unfold diagnoseProof
  repeat' split
  all_goals simp

/-- **Acceptance is exactly `proofAccepts`.** -/
theorem validateProof_ok_iff (V : Verifiers) (pol : ProofPolicy) (req : Request)
    (at? : Option ByteArray) (jkt? : Option String) (proof : String) :
    validateProof V pol req at? jkt? proof = .ok ↔
      proofAccepts V pol req at? jkt? proof = true := by
  unfold validateProof
  by_cases h : proofAccepts V pol req at? jkt? proof
  · simp [h]
  · simp only [h, Bool.false_eq_true, ite_false, iff_false]
    exact diagnoseProof_ne_ok V pol req at? jkt? proof

/-- The accepting condition, unfolded once the proof's structural parts
are known. Every theorem below reads one conjunct out of it. -/
theorem proofAccepts_parts {V : Verifiers} {pol : ProofPolicy} {req : Request}
    {tok : ByteArray} {jkt : String} {proof : String} {c : Compact} {hdr : Header}
    {key : Jwk} {pc : ProofClaims}
    (hp : preKey proof = .ok (c, hdr)) (hk : proofKey? hdr = some key)
    (hc : payloadClaims? c = some pc)
    (ha : proofAccepts V pol req (some tok) (some jkt) proof = true) :
    pc.ath = some (athFor tok) ∧ jkt = thumbprint key := by
  unfold proofAccepts at ha
  rw [hp] at ha
  simp only at ha
  rw [hk] at ha
  simp only at ha
  rw [hc] at ha
  simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at ha
  exact ⟨ha.2.2.2.1, ha.2.2.2.2⟩

/-- **An accepted proof was signed by a key whose thumbprint is the one
the access token is bound to.** This is the RFC 9449 §6.1 binding: it is
what makes possession of the proof key mean possession of the token's
key. A proof key whose thumbprint differs from `cnf.jkt` is refused. -/
theorem proof_ok_thumbprint_bound {V : Verifiers} {pol : ProofPolicy} {req : Request}
    {tok : ByteArray} {jkt : String} {proof : String}
    (h : validateProof V pol req (some tok) (some jkt) proof = .ok) :
    ∃ c hdr key, preKey proof = .ok (c, hdr) ∧ proofKey? hdr = some key ∧
      jkt = thumbprint key := by
  have ha := (validateProof_ok_iff V pol req (some tok) (some jkt) proof).mp h
  have ha' := ha
  unfold proofAccepts at ha'
  cases hp : preKey proof with
  | error r => rw [hp] at ha'; simp at ha'
  | ok ch =>
      obtain ⟨c, hdr⟩ := ch
      rw [hp] at ha'
      simp only at ha'
      cases hk : proofKey? hdr with
      | none => rw [hk] at ha'; simp at ha'
      | some key =>
          rw [hk] at ha'
          simp only at ha'
          cases hc : payloadClaims? c with
          | none => rw [hc] at ha'; simp at ha'
          | some pc =>
              exact ⟨c, hdr, key, rfl, hk, (proofAccepts_parts hp hk hc ha).2⟩

/-- **An accepted proof carries the `ath` of the token presented with
it** (RFC 9449 §4.3 item 10), so a proof captured on one request cannot
be attached to a request carrying a different token. -/
theorem proof_ok_ath_bound {V : Verifiers} {pol : ProofPolicy} {req : Request}
    {tok : ByteArray} {jkt : String} {proof : String}
    (h : validateProof V pol req (some tok) (some jkt) proof = .ok) :
    ∃ c hdr pc, preKey proof = .ok (c, hdr) ∧ payloadClaims? c = some pc ∧
      pc.ath = some (athFor tok) := by
  have ha := (validateProof_ok_iff V pol req (some tok) (some jkt) proof).mp h
  have ha' := ha
  unfold proofAccepts at ha'
  cases hp : preKey proof with
  | error r => rw [hp] at ha'; simp at ha'
  | ok ch =>
      obtain ⟨c, hdr⟩ := ch
      rw [hp] at ha'
      simp only at ha'
      cases hk : proofKey? hdr with
      | none => rw [hk] at ha'; simp at ha'
      | some key =>
          rw [hk] at ha'
          simp only at ha'
          cases hc : payloadClaims? c with
          | none => rw [hc] at ha'; simp at ha'
          | some pc =>
              exact ⟨c, hdr, pc, rfl, hc, (proofAccepts_parts hp hk hc ha).1⟩

/-- **A proof presented with an access token that is not bound to any key
is refused.** A verifier that accepted it would be treating a
possession proof as a bearer token. -/
theorem proof_unbound_token_refused {V : Verifiers} {pol : ProofPolicy} {req : Request}
    {tok : ByteArray} {proof : String} :
    validateProof V pol req (some tok) none proof ≠ .ok := by
  intro h
  have ha := (validateProof_ok_iff V pol req (some tok) none proof).mp h
  unfold proofAccepts at ha
  cases hp : preKey proof with
  | error r => rw [hp] at ha; simp at ha
  | ok ch =>
      obtain ⟨c, hdr⟩ := ch
      rw [hp] at ha
      simp only at ha
      cases hk : proofKey? hdr with
      | none => rw [hk] at ha; simp at ha
      | some key =>
          rw [hk] at ha
          simp only at ha
          cases hc : payloadClaims? c with
          | none => rw [hc] at ha; simp at ha
          | some pc =>
              rw [hc] at ha
              simp only [Bool.and_eq_true, beq_iff_eq] at ha
              exact absurd ha.2.2.2.2 (by simp)

/-- **A JWS refusal stops a proof.** With `Jws.hmacFamily_not_allowed`
and `Jws.alg_none_not_allowed`, this is the statement that no HMAC or
`none` proof is ever accepted, whatever else it carries. -/
theorem proof_jws_refusal {V : Verifiers} {pol : ProofPolicy} {req : Request}
    {at? : Option ByteArray} {jkt? : Option String} {proof : String} {r : Refusal}
    (h : preKey proof = .error r) :
    validateProof V pol req at? jkt? proof = .jwsRefused r := by
  simp [validateProof, proofAccepts, diagnoseProof, h]

/-! ## Fixtures

RFC 9449 §4.1 gives a DPoP proof and its key. The signature over that
proof is ES256 and needs the HACL* primitive, which does not evaluate at
compile time; that check is a section of `lake exe l4jose-probe`. What is
checked here is everything else the RFC's example fixes: the header, the
key, the claims, the thumbprint, and the `htu` comparison. -/

-- RFC 9449 Figure 2 (§4.1): the example DPoP proof sent with a token
-- request, transcribed from the RFC's own text with its RFC 8792 line
-- wrapping removed.
private def rfc9449Fig2 : String :=
  "eyJ0eXAiOiJkcG9wK2p3dCIsImFsZyI6IkVTMjU2IiwiandrIjp7Imt0eSI6IkVDIiwieCI6Imw4dEZyaHgtMzR0Vj" ++
  "NoUklDUkRZOXpDa0RscEJoRjQyVVFVZldWQVdCRnMiLCJ5IjoiOVZFNGpmX09rX282NHpiVFRsY3VOSmFqSG10NnY5" ++
  "VERWclUwQ2R2R1JEQSIsImNydiI6IlAtMjU2In19.eyJqdGkiOiItQndDM0VTYzZhY2MybFRjIiwiaHRtIjoiUE9TV" ++
  "CIsImh0dSI6Imh0dHBzOi8vc2VydmVyLmV4YW1wbGUuY29tL3Rva2VuIiwiaWF0IjoxNTYyMjYyNjE2fQ.2-GxA6T8" ++
  "lP4vfrg8v-FdWP0A0zdrj8igiMLvqRMUvwnQg4PtFLbdLXiOSsX0x7NVY-FNyJK70nfbV37xRZT3Lg"

-- RFC 9449 Figure 13 (§7.1): the proof sent with a DPoP-bound access
-- token to a protected resource. Figure 14 gives its decoded content.
private def rfc9449Fig13 : String :=
  "eyJ0eXAiOiJkcG9wK2p3dCIsImFsZyI6IkVTMjU2IiwiandrIjp7Imt0eSI6IkVDIiwieCI6Imw4dEZyaHgtMzR0Vj" ++
  "NoUklDUkRZOXpDa0RscEJoRjQyVVFVZldWQVdCRnMiLCJ5IjoiOVZFNGpmX09rX282NHpiVFRsY3VOSmFqSG10NnY5" ++
  "VERWclUwQ2R2R1JEQSIsImNydiI6IlAtMjU2In19.eyJqdGkiOiJlMWozVl9iS2ljOC1MQUVCIiwiaHRtIjoiR0VUI" ++
  "iwiaHR1IjoiaHR0cHM6Ly9yZXNvdXJjZS5leGFtcGxlLm9yZy9wcm90ZWN0ZWRyZXNvdXJjZSIsImlhdCI6MTU2MjI" ++
  "2MjYxOCwiYXRoIjoiZlVIeU8ycjJaM0RaNTNFc05yV0JiMHhXWG9hTnk1OUlpS0NBcWtzbVFFbyJ9.2oW9RP35yRqz" ++
  "hrtNP86L-Ey71EOptxRimPPToA1plemAgR6pxHF8y6-yqyVnmcw6Fy1dqd-jfxSYoMxhAJpLjA"

private def headerOf (t : String) : Json :=
  ((preKey t).toOption.map (fun ch => ch.2.json)).getD .null

private def claimsOf (t : String) : ProofClaims :=
  ((preKey t).toOption.bind fun ch => payloadClaims? ch.1).getD {}

-- Figure 2's header, exactly as Figure 14 prints the same key.
#guard (headerOf rfc9449Fig2).getString? "typ" == some "dpop+jwt"
#guard ((preKey rfc9449Fig2).toOption.map (fun ch => ch.2.alg)) == some Alg.es256
#guard ((((headerOf rfc9449Fig2).field? "jwk").bind parsePublicJwk?).map Jwk.kty)
        == some Kty.ec
-- Figure 2's payload.
#guard (claimsOf rfc9449Fig2).htm == some "POST"
#guard (claimsOf rfc9449Fig2).htu == some "https://server.example.com/token"
#guard (claimsOf rfc9449Fig2).jti == some "-BwC3ESc6acc2lTc"
#guard (claimsOf rfc9449Fig2).iat == some 1562262616
#guard (claimsOf rfc9449Fig2).ath == none

-- Figure 14, the decoded content of Figure 13's proof.
#guard (headerOf rfc9449Fig13).getString? "typ" == some "dpop+jwt"
#guard (claimsOf rfc9449Fig13).htm == some "GET"
#guard (claimsOf rfc9449Fig13).htu == some "https://resource.example.org/protectedresource"
#guard (claimsOf rfc9449Fig13).jti == some "e1j3V_bKic8-LAEB"
#guard (claimsOf rfc9449Fig13).iat == some 1562262618
#guard (claimsOf rfc9449Fig13).ath == some "fUHyO2r2Z3DZ53EsNrWBb0xWXoaNy59IiKCAqksmQEo"

-- RFC 9449 §6.1 Figure 9 prints the thumbprint of that same key as
-- "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I".
#guard (((headerOf rfc9449Fig13).field? "jwk").bind parsePublicJwk?).map thumbprint
        == some "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I"

-- The `htu` comparison. A query or a fragment on the request URI is
-- ignored; a different path, host or scheme is not.
#guard htuMatches "https://server.example.com/token" "https://server.example.com/token?x=1"
#guard htuMatches "https://server.example.com/token" "https://server.example.com/token#f"
#guard htuMatches "https://server.example.com/token?a=1" "https://server.example.com/token?b=2"
#guard !htuMatches "https://server.example.com/tokens" "https://server.example.com/token"
#guard !htuMatches "https://server.example.com/token" "https://evil.example.com/token"
#guard !htuMatches "http://server.example.com/token" "https://server.example.com/token"
#guard !htuMatches "https://server.example.com/" "https://server.example.com/token"

-- RFC 9449 §4.1: `ath` over an access token. The RFC's §6.1 example
-- token value is "Kz~8mXK1EalYznwH-LC-1fBAo.4Ljp~zsPE_NeO.gxU" and its
-- `ath` is "fUHyO2r2Z3DZ53EsNrWBb0xWXoaNy59IiKCAqksmQEo".
#guard athFor "Kz~8mXK1EalYznwH-LC-1fBAo.4Ljp~zsPE_NeO.gxU".toUTF8
        == "fUHyO2r2Z3DZ53EsNrWBb0xWXoaNy59IiKCAqksmQEo"

-- A proof whose header carries a PRIVATE key is refused (RFC 9449 §4.2).
private def stubV : Verifiers :=
  { es256 := fun _ _ _ => true, rs256 := fun _ _ _ _ => true, eddsa := fun _ _ _ => true }
private def alwaysFresh : ProofPolicy :=
  { now := 1562262616, iatWindow := 60, jtiFresh := fun _ => true }
private def alwaysStale : ProofPolicy := { alwaysFresh with jtiFresh := fun _ => false }
private def tokenRequest : Request :=
  { method := "POST", uri := "https://server.example.com/token" }

private def proofWith (header payload : String) : String :=
  Base64Url.encodeUtf8 header ++ "." ++ Base64Url.encodeUtf8 payload ++ "." ++
  Base64Url.encode ⟨#[0x00]⟩

private def pubJwk : String :=
  "{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
  "\"x\":\"l8tFrhx-34tV3hRICRDY9zCkDlpBhF42UQUfWVAWBFs\"," ++
  "\"y\":\"9VE4jf_Ok_o64zbTTlcuNJajHmt6v9TDVrU0CdvGRDA\"}"

private def goodPayload : String :=
  "{\"jti\":\"j1\",\"htm\":\"POST\",\"htu\":\"https://server.example.com/token\"," ++
  "\"iat\":1562262616}"

#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .ok
-- `typ` is checked, and a JWT minted for another purpose cannot stand in.
#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith ("{\"typ\":\"JWT\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .typWrong "JWT"
#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith ("{\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload) == .typMissing
-- A private key in the header is refused.
#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
    "\"x\":\"l8tFrhx-34tV3hRICRDY9zCkDlpBhF42UQUfWVAWBFs\"," ++
    "\"y\":\"9VE4jf_Ok_o64zbTTlcuNJajHmt6v9TDVrU0CdvGRDA\",\"d\":\"AA\"}}") goodPayload)
  == .jwkRejected
-- No `jwk` at all.
#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith "{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\"}" goodPayload) == .jwkMissing
-- Method and URI must be the request's.
#guard validateProof stubV alwaysFresh { tokenRequest with method := "GET" } none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .htmMismatch
#guard validateProof stubV alwaysFresh
  { tokenRequest with uri := "https://server.example.com/other" } none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .htuMismatch
-- A query on the request URI does not break the match.
#guard validateProof stubV alwaysFresh
  { tokenRequest with uri := "https://server.example.com/token?a=1" } none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .ok
-- Replay, and the `iat` window.
#guard validateProof stubV alwaysStale tokenRequest none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .jtiReplayed
#guard validateProof stubV { alwaysFresh with now := 1562262800 } tokenRequest none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .iatOutOfWindow
-- With an access token: `ath` is required, must match, and the token
-- must be bound to this key's thumbprint.
private def tok : ByteArray := "Kz~8mXK1EalYznwH-LC-1fBAo.4Ljp~zsPE_NeO.gxU".toUTF8
private def pubThumb : String :=
  (parsePublicJwkString? pubJwk).map thumbprint |>.getD ""
private def athPayload : String :=
  "{\"jti\":\"j1\",\"htm\":\"POST\",\"htu\":\"https://server.example.com/token\"," ++
  "\"iat\":1562262616,\"ath\":\"fUHyO2r2Z3DZ53EsNrWBb0xWXoaNy59IiKCAqksmQEo\"}"

#guard validateProof stubV alwaysFresh tokenRequest (some tok) (some pubThumb)
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") athPayload)
  == .ok
#guard validateProof stubV alwaysFresh tokenRequest (some tok) (some pubThumb)
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .athMissing
#guard validateProof stubV alwaysFresh tokenRequest (some "another token".toUTF8) (some pubThumb)
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") athPayload)
  == .athMismatch
-- The token is bound to a DIFFERENT key: the proof proves possession of
-- a key, but not of the token's key.
#guard pubThumb == "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I"
#guard validateProof stubV alwaysFresh tokenRequest (some tok)
  (some "kPrK_qmxVWaYVA9wwBF6Iuo3vVzz7TxHCTwXBygrS4k")
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") athPayload)
  == .keyThumbprintMismatch
-- A token with no `cnf.jkt` is not bound at all.
#guard validateProof stubV alwaysFresh tokenRequest (some tok) none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"ES256\",\"jwk\":" ++ pubJwk ++ "}") athPayload)
  == .tokenNotBound
-- Algorithm confusion reaches the proof layer as a JWS refusal.
#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"HS256\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .jwsRefused (.algNotAllowed "HS256")
#guard validateProof stubV alwaysFresh tokenRequest none none
  (proofWith ("{\"typ\":\"dpop+jwt\",\"alg\":\"none\",\"jwk\":" ++ pubJwk ++ "}") goodPayload)
  == .jwsRefused (.algNotAllowed "none")

end L4Factoidal.JOSE
