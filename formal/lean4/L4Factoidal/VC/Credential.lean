/-
L4Factoidal.VC.Credential — the Verifiable Credentials 2.0 data-model
checks, ported from `formal/fstar/VC.Credential.fst`.

Spec: VC Data Model 2.0 (https://www.w3.org/TR/vc-data-model-2.0/)
§4 — `@context`, `type`, `id`, `issuer`, `credentialSubject` and the
validity dates.

Verdicts carry a REASON string rather than being a bare boolean.
A credential-verification failure that says only "false" is
unactionable, and the VC test suite distinguishes failure modes.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.VC

open L4Factoidal.JSON

inductive Verdict where
  | pass
  | fail (reason : String)
deriving Repr, DecidableEq, Inhabited

def Verdict.ok : Verdict → Bool
  | .pass => true
  | .fail _ => false

/-- Both must pass; the FIRST failure's reason is kept, so the
    message names the earliest problem rather than the last. -/
def Verdict.both : Verdict → Verdict → Verdict
  | .fail r, _ => .fail r
  | _, v => v

def all (vs : List Verdict) : Verdict := vs.foldl Verdict.both .pass

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

/-- A cheap IRI shape test: a scheme separator and no whitespace. The
    full grammar lives in `RDF.Core`; this is the structural check the
    F* module makes at this layer. -/
def looksLikeIri (s : String) : Bool :=
  s.toList.contains ':' && !(s.toList.any (fun c => c == ' ' || c == '\t'))

def baseContext : String := "https://www.w3.org/ns/credentials/v2"
def credentialType : String := "VerifiableCredential"
def presentationType : String := "VerifiablePresentation"
def envelopedCredentialType : String := "EnvelopedVerifiableCredential"

/-- One `@context` entry. A string must look like an IRI; an inline
    object or `null` is structurally acceptable per the JSON-LD
    grammar. -/
def contextEntryOk (v : Json) : Bool :=
  match v with
  | .string s => looksLikeIri s
  | .object _ => true
  | .null     => true
  | _         => false

/-- §4.1 `@context`.

    THE RULE THAT MATTERS: the base VC 2.0 context IRI must be the
    FIRST entry, not merely present. JSON-LD context processing is
    ORDER-DEPENDENT — a later entry can redefine terms an earlier one
    established — so a credential listing the base context second has
    different semantics from one listing it first, and accepting both
    would let a crafted context silently redefine `issuer` or
    `credentialSubject`. -/
def checkContext (v : Json) : Verdict :=
  match field? "@context" v with
  | none => .fail "missing @context"
  | some (.string s) =>
      if s == baseContext then .pass
      else .fail "bare-string @context must equal the base VC 2.0 context IRI"
  | some (.array items) =>
      match items with
      | [] => .fail "@context is an empty array"
      | first :: _ =>
          if !(items.all contextEntryOk) then
            .fail "an @context entry is neither a well-formed IRI string, an object, nor null"
          else match first with
            | .string s =>
                if s == baseContext then .pass
                else .fail "the base VC 2.0 context IRI must be the FIRST @context entry"
            | _ => .fail "the first @context entry must be the base VC 2.0 context IRI string"
  | some _ => .fail "@context must be a string or an array"

/-- The `type` value as a list of strings, accepting the string or
    array form. -/
def decodeTypeList (v : Json) : List String :=
  match v with
  | .string s => [s]
  | .array items => items.filterMap (fun i => match i with
      | .string s => some s
      | _ => none)
  | _ => []

/-- §4.2 `type` must include the base type. -/
def checkTypeMembership (v : Json) (required : String) : Verdict :=
  match field? "type" v with
  | none => .fail "missing type"
  | some t =>
      let types := decodeTypeList t
      if types.isEmpty then .fail "type is empty or not string-valued"
      else if types.contains required then .pass
      else .fail ("type must include " ++ required)

/-- §4.3 `id`, when present, must be a single IRI string. Absence is
    allowed unless `required`. -/
def checkIdField (required : Bool) (label : String) (v : Json) : Verdict :=
  match field? "id" v with
  | none => if required then .fail (label ++ " is missing id") else .pass
  | some (.string s) =>
      if looksLikeIri s then .pass else .fail (label ++ " id is not an IRI")
  | some _ => .fail (label ++ " id must be a string")

/-- §4.5 `issuer`: either an IRI string or an object carrying an
    `id`. -/
def checkIssuer (v : Json) : Verdict :=
  match field? "issuer" v with
  | none => .fail "missing issuer"
  | some (.string s) =>
      if looksLikeIri s then .pass else .fail "issuer string is not an IRI"
  | some o =>
      match o with
      | .object _ => checkIdField true "issuer object" o
      | _ => .fail "issuer must be a string or an object"

/-- §4.4 `credentialSubject` must be present and non-empty. An EMPTY
    object is a failure: a credential asserting nothing about anyone
    is not a credential. -/
def checkCredentialSubject (v : Json) : Verdict :=
  match field? "credentialSubject" v with
  | none => .fail "missing credentialSubject"
  | some (.object []) => .fail "credentialSubject is empty"
  | some (.object _) => .pass
  | some (.array []) => .fail "credentialSubject array is empty"
  | some (.array _) => .pass
  | some _ => .fail "credentialSubject must be an object or an array"

/-- §4.6/§4.7 validity dates, when present, must be strings. Their
    ORDERING is checked by the caller against a clock — this module
    stays a total function of its input, so it does not read a clock
    itself. -/
def checkValidityDates (v : Json) : Verdict :=
  let dateOk (k : String) : Verdict :=
    match field? k v with
    | none => .pass
    | some (.string _) => .pass
    | some _ => .fail (k ++ " must be a string")
  Verdict.both (dateOk "validFrom") (dateOk "validUntil")

/-- Whole-credential structural check. -/
def checkCredential (v : Json) : Verdict :=
  all [ checkContext v,
        checkTypeMembership v credentialType,
        checkIdField false "credential" v,
        checkIssuer v,
        checkCredentialSubject v,
        checkValidityDates v ]

/-- A presentation carries `VerifiablePresentation` instead, and has
    no issuer or subject of its own. -/
def checkPresentation (v : Json) : Verdict :=
  all [ checkContext v,
        checkTypeMembership v presentationType,
        checkIdField false "presentation" v ]

end L4Factoidal.VC
