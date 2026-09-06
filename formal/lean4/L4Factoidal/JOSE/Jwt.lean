/-
L4Factoidal.JOSE.Jwt — JSON Web Token claims (RFC 7519 §4.1) and their
validation, plus the RFC 7800 confirmation claim Solid-OIDC uses to bind
an access token to a DPoP key.

## Time is a parameter

`validate` takes the current time as an argument. Nothing in this module
reads a clock, and nothing in it performs I/O — the module imports no
`IO`. A validator that calls the clock itself cannot be tested at a
chosen instant, cannot be replayed, and cannot be reasoned about: the
`exp` and `nbf` theorems below are statements about `now`, and there is
no `now` to quantify over if the function fetches its own.

## Acceptance is characterised, not merely implemented

`validate_ok_iff` states the exact conjunction of conditions under which
a token is accepted, in both directions. A later change that adds an
accepting path, or that weakens one of the checks, breaks the theorem.
The individual consequences — issuer pinned, audience pinned, not
expired, not used before `nbf` — are corollaries of it, kept separate
because each is the one an auditor asks about.

## Issuer and audience are PINNED, not merely present

RFC 7519 §4.1.1 and §4.1.3 say only what the claims mean. A validator
that checks an `iss` claim is present, or that an `aud` claim exists,
accepts a token minted by anyone. `validate` takes the expected issuer
and the expected audience as arguments and requires equality; there is
no "any issuer" mode.

## NumericDate

RFC 7519 §2 defines `NumericDate` as a JSON number of seconds since
1970-01-01T00:00:00Z, which may be non-integer. This module accepts only
an integer, positive or negative, and refuses a fractional value rather
than truncating it. Truncation is a silent extension of a token's life
by up to a second, and no issuer needs sub-second expiry.

## Leeway

RFC 7519 §4.1.4 permits "a small leeway, usually no more than a few
minutes, to account for clock skew". `leeway` is an explicit parameter,
so a deployment states its skew tolerance rather than inheriting an
undocumented default. It applies symmetrically to `exp` and `nbf`.
-/
import L4Factoidal.JOSE.Jws

namespace L4Factoidal.JOSE

open L4Factoidal.JSON

/-! ## Claims -/

/-- The RFC 7519 §4.1 registered claims this project reads, plus the
RFC 7800 §3.1 `cnf` member `jkt` (RFC 9449 §6), which carries the
JWK thumbprint an access token is bound to.

`aud` is a list because RFC 7519 §4.1.3 allows either a single string or
an array of strings; the single-string form is stored as a one-element
list, so no consumer branches on the JSON shape. -/
structure Claims where
  iss : Option String := none
  sub : Option String := none
  aud : List String := []
  exp : Option Int := none
  nbf : Option Int := none
  iat : Option Int := none
  jti : Option String := none
  cnfJkt : Option String := none
  /-- The Solid-OIDC `webid` claim. NOT an RFC 7519 registered claim:
  Solid-OIDC (Editor's Draft, §6) defines it, and says that when it is
  absent the `sub` claim MAY be the WebID if the issuer is authoritative
  for it. Read here so that `Solid/Server/Auth.lean` can apply that rule
  in one place. -/
  webid : Option String := none
  deriving Repr, DecidableEq, BEq

/-- Read an RFC 7519 §2 `NumericDate`. Integers only; a fractional value
is refused rather than truncated. -/
def numericDate? (j : Json) : Option Int :=
  match j with
  | .number s => s.toInt?
  | _ => none

/-- RFC 7519 §4.1.3: `aud` is a string or an array of strings. An array
holding a non-string member makes the whole claim unreadable rather than
silently dropping that member. -/
def audience? (j : Json) : Option (List String) :=
  match j with
  | .string s => some [s]
  | .array items =>
      items.foldr (fun it acc =>
        match acc, it with
        | some rest, .string s => some (s :: rest)
        | _, _ => none) (some [])
  | _ => none

/-- Parse a claims set from a JSON payload. A member of the wrong JSON
type makes the parse fail rather than being ignored: a token whose `exp`
is the string `"9999999999"` must not be read as a token with no `exp`,
because a missing `exp` and an unreadable `exp` are treated differently
by every validator. -/
def parseClaims? (j : Json) : Option Claims :=
  match j with
  | .object _ => do
      let str (n : String) : Option (Option String) :=
        match j.field? n with
        | none => some none
        | some (.string s) => some (some s)
        | some _ => none
      let num (n : String) : Option (Option Int) :=
        match j.field? n with
        | none => some none
        | some v => (numericDate? v).map some
      let iss ← str "iss"
      let sub ← str "sub"
      let jti ← str "jti"
      let webid ← str "webid"
      let exp ← num "exp"
      let nbf ← num "nbf"
      let iat ← num "iat"
      let aud ←
        match j.field? "aud" with
        | none => some []
        | some v => audience? v
      let cnfJkt ←
        match j.field? "cnf" with
        | none => some none
        | some c =>
            match c.field? "jkt" with
            | none => some none
            | some (.string s) => some (some s)
            | some _ => none
      some { iss, sub, aud, exp, nbf, iat, jti, cnfJkt, webid }
  | _ => none

/-- Parse claims from a JWS payload's octets. -/
def parseClaimsBytes? (b : ByteArray) : Option Claims :=
  (String.fromUTF8? b).bind fun s => (parseJson? s).bind parseClaims?

/-! ## Validation -/

/-- What a deployment must state before a token can be judged. There is
no default issuer and no default audience. -/
structure Policy where
  /-- The instant to judge against, in RFC 7519 §2 `NumericDate` seconds. -/
  now : Int
  /-- Clock-skew tolerance in seconds (RFC 7519 §4.1.4), applied to both
  `exp` and `nbf`. -/
  leeway : Int
  /-- The one issuer whose tokens are accepted. -/
  issuer : String
  /-- The audience this verifier is. -/
  audience : String
  deriving Repr, DecidableEq, Inhabited

/-- Why a claims set was or was not accepted. -/
inductive ClaimsOutcome where
  | ok
  | issuerMissing
  | issuerMismatch
  | subjectMissing
  | audienceMismatch
  | expiryMissing
  | expired
  | notYetValid
  deriving DecidableEq, Repr, BEq

/-- **The single accepting condition.** A claims set is accepted exactly
when this returns `true`; `validate` is `if accepts then .ok else` a
diagnosis that cannot return `.ok` (`diagnose_ne_ok`). There is
therefore one accepting path and it is this expression.

`exp` is REQUIRED. RFC 7519 §4.1.4 makes the claim optional, but a
bearer credential with no expiry is a permanent one, and Solid-OIDC
access tokens always carry it. `sub` is required because a WebID must
come from somewhere. -/
def accepts (p : Policy) (c : Claims) : Bool :=
  (c.iss == some p.issuer) && c.sub.isSome && decide (p.audience ∈ c.aud) &&
  (match c.exp with | none => false | some e => decide (p.now < e + p.leeway)) &&
  (match c.nbf with | none => true | some n => decide (n ≤ p.now + p.leeway))

/-- Which check failed first. This is a DIAGNOSIS, not a decision: it is
reached only when `accepts` already said no, and `diagnose_ne_ok` proves
it can never answer `.ok`. Reordering it changes only which refusal is
reported. -/
def diagnose (p : Policy) (c : Claims) : ClaimsOutcome :=
  if c.iss.isNone then .issuerMissing
  else if c.iss != some p.issuer then .issuerMismatch
  else if c.sub.isNone then .subjectMissing
  else if !decide (p.audience ∈ c.aud) then .audienceMismatch
  else if c.exp.isNone then .expiryMissing
  else if (match c.exp with | none => false | some e => decide (p.now ≥ e + p.leeway))
    then .expired
  else .notYetValid

/-- RFC 7519 §4.1 validation against a stated policy. -/
def validate (p : Policy) (c : Claims) : ClaimsOutcome :=
  if accepts p c then .ok else diagnose p c

/-! ## Theorems -/

/-- The diagnosis never accepts, so `validate` has exactly one path to
`.ok`. -/
theorem diagnose_ne_ok (p : Policy) (c : Claims) : diagnose p c ≠ .ok := by
  unfold diagnose
  repeat' split
  all_goals simp

/-- **The whole acceptance condition, in both directions.** A token is
accepted exactly when its issuer is the pinned one, it names a subject,
its audience list contains this verifier, it carries an expiry the
current time has not reached (with leeway), and it is not held back by
an `nbf` the current time has not reached (with leeway). Adding an
accepting path or weakening a check breaks this. -/
theorem validate_ok_iff (p : Policy) (c : Claims) :
    validate p c = .ok ↔
      c.iss = some p.issuer ∧
      (∃ s, c.sub = some s) ∧
      p.audience ∈ c.aud ∧
      (∃ e, c.exp = some e ∧ p.now < e + p.leeway) ∧
      (∀ n, c.nbf = some n → n ≤ p.now + p.leeway) := by
  unfold validate
  by_cases hacc : accepts p c
  · simp only [hacc, if_pos]
    simp only [accepts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Option.isSome_iff_exists] at hacc
    obtain ⟨⟨⟨⟨hi, hs⟩, ha⟩, hexp⟩, hnbf⟩ := hacc
    refine ⟨fun _ => ⟨hi, ?_, ha, ?_, ?_⟩, fun _ => trivial⟩
    · obtain ⟨s, hs'⟩ := hs; exact ⟨s, hs'⟩
    · cases he : c.exp with
      | none => rw [he] at hexp; simp at hexp
      | some e => rw [he] at hexp; exact ⟨e, rfl, by simpa using hexp⟩
    · intro n hn
      rw [hn] at hnbf
      simpa using hnbf
  · simp only [hacc, Bool.false_eq_true, ite_false]
    constructor
    · intro h; exact absurd h (diagnose_ne_ok p c)
    · rintro ⟨hi, ⟨s, hs⟩, ha, ⟨e, he, hlt⟩, hnbf⟩
      exfalso
      apply hacc
      simp only [accepts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hi, by simp [hs]⟩, ha⟩, ?_⟩, ?_⟩
      · rw [he]; simpa using hlt
      · cases hn : c.nbf with
        | none => simp
        | some n => simpa using hnbf n hn

/-- **An accepted token was minted by the pinned issuer.** -/
theorem validate_ok_issuer_pinned {p : Policy} {c : Claims} (h : validate p c = .ok) :
    c.iss = some p.issuer := ((validate_ok_iff p c).mp h).1

/-- **An accepted token names this verifier in its audience.** -/
theorem validate_ok_audience_pinned {p : Policy} {c : Claims} (h : validate p c = .ok) :
    p.audience ∈ c.aud := ((validate_ok_iff p c).mp h).2.2.1

/-- **An accepted token has an expiry, and it has not been reached.** -/
theorem validate_ok_unexpired {p : Policy} {c : Claims} (h : validate p c = .ok) :
    ∃ e, c.exp = some e ∧ p.now < e + p.leeway := ((validate_ok_iff p c).mp h).2.2.2.1

/-- **A token with no expiry is never accepted.** -/
theorem validate_no_exp_refused {p : Policy} {c : Claims} (h : c.exp = none) :
    validate p c ≠ .ok := by
  intro hok
  obtain ⟨e, he, _⟩ := validate_ok_unexpired hok
  rw [h] at he
  cases he

/-- **A token from another issuer is never accepted**, whatever else it
carries. -/
theorem validate_wrong_issuer_refused {p : Policy} {c : Claims} {i : String}
    (hi : c.iss = some i) (hne : i ≠ p.issuer) : validate p c ≠ .ok := by
  intro hok
  have := validate_ok_issuer_pinned hok
  rw [hi] at this
  exact hne (Option.some.inj this)

/-- **Moving the clock forward past the expiry turns an accepted token
into a refused one.** Stated because a validator that reads `exp` but
compares it to the wrong thing passes every fixed-time test. -/
theorem validate_expires {p : Policy} {c : Claims} {e : Int}
    (he : c.exp = some e) (hlate : p.now ≥ e + p.leeway) : validate p c ≠ .ok := by
  intro hok
  obtain ⟨e', he', hlt⟩ := validate_ok_unexpired hok
  rw [he] at he'
  cases he'
  omega

/-! ## Fixtures -/

private def samplePolicy : Policy :=
  { now := 1_700_000_000, leeway := 60, issuer := "https://idp.example/",
    audience := "https://storage.example/" }

private def sampleClaims : Claims :=
  { iss := some "https://idp.example/", sub := some "https://alice.example/profile/card#me",
    aud := ["https://storage.example/"], exp := some 1_700_000_600,
    iat := some 1_700_000_000, jti := some "abc",
    cnfJkt := some "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I" }

#guard validate samplePolicy sampleClaims == .ok
-- Expired, allowing for the 60-second leeway.
#guard validate { samplePolicy with now := 1_700_000_661 } sampleClaims == .expired
#guard validate { samplePolicy with now := 1_700_000_659 } sampleClaims == .ok
-- Another issuer, another audience.
#guard validate { samplePolicy with issuer := "https://evil.example/" } sampleClaims
        == .issuerMismatch
#guard validate { samplePolicy with audience := "https://other.example/" } sampleClaims
        == .audienceMismatch
-- Missing required claims.
#guard validate samplePolicy { sampleClaims with exp := none } == .expiryMissing
#guard validate samplePolicy { sampleClaims with iss := none } == .issuerMissing
#guard validate samplePolicy { sampleClaims with sub := none } == .subjectMissing
-- `nbf` in the future, beyond the leeway.
#guard validate samplePolicy { sampleClaims with nbf := some 1_700_000_100 } == .notYetValid
#guard validate samplePolicy { sampleClaims with nbf := some 1_700_000_060 } == .ok

-- Parsing. The `aud` claim in both of its RFC 7519 §4.1.3 forms.
#guard ((parseJson? "{\"aud\":\"a\"}").bind parseClaims?).map Claims.aud == some ["a"]
#guard ((parseJson? "{\"aud\":[\"a\",\"b\"]}").bind parseClaims?).map Claims.aud
        == some ["a", "b"]
#guard ((parseJson? "{\"aud\":[\"a\",1]}").bind parseClaims?).isNone
-- A claim of the wrong JSON type fails the parse instead of being
-- ignored: a string `exp` must not read as a token with no expiry.
#guard ((parseJson? "{\"exp\":\"9999999999\"}").bind parseClaims?).isNone
#guard ((parseJson? "{\"iss\":42}").bind parseClaims?).isNone
-- A fractional NumericDate is refused, not truncated.
#guard ((parseJson? "{\"exp\":1700000000.5}").bind parseClaims?).isNone
#guard ((parseJson? "{\"exp\":1700000000}").bind parseClaims?).map Claims.exp
        == some (some 1700000000)
-- The RFC 7800 §3.1 confirmation claim, as RFC 9449 §6 uses it.
#guard ((parseJson? "{\"cnf\":{\"jkt\":\"0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I\"}}").bind
  parseClaims?).map Claims.cnfJkt == some (some "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I")
#guard ((parseJson? "{\"cnf\":{\"x5t#S256\":\"AA\"}}").bind parseClaims?).map Claims.cnfJkt
        == some none

-- The Solid-OIDC `webid` claim.
#guard ((parseJson? "{\"webid\":\"https://alice.example/card#me\"}").bind parseClaims?).map
  Claims.webid == some (some "https://alice.example/card#me")
#guard ((parseJson? "{\"webid\":42}").bind parseClaims?).isNone

-- The RFC 7519 §3.1 example payload.
#guard ((parseJson? "{\"iss\":\"joe\",\"exp\":1300819380,\"http://example.com/is_root\":true}").bind
  parseClaims?).map Claims.iss == some (some "joe")

end L4Factoidal.JOSE
