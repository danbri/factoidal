/-
L4Factoidal.VC.CredentialTests — build-time checks for the VC 2.0
data-model rules, with the context-ordering rule pinned.
-/
import L4Factoidal.VC.Credential

namespace L4Factoidal.VC
open L4Factoidal.JSON

private def ctxOk : Json := .array [.string baseContext]
private def subj : Json := .object [("id", .string "did:example:s")]

private def goodVc : Json :=
  .object [("@context", ctxOk),
           ("type", .array [.string credentialType]),
           ("issuer", .string "did:example:issuer"),
           ("credentialSubject", subj)]

#guard (checkCredential goodVc).ok

-- THE CONTEXT-ORDERING RULE. The base context must be FIRST, not
-- merely present: JSON-LD context processing is order-dependent, so
-- a later entry can redefine terms an earlier one established.
-- Accepting a base context in second position would let a crafted
-- context silently redefine `issuer` or `credentialSubject`.
#guard (checkContext (.object [("@context",
          .array [.string baseContext, .string "https://ex.org/c"])])).ok
#guard !(checkContext (.object [("@context",
          .array [.string "https://ex.org/c", .string baseContext])])).ok

-- Other @context shapes.
#guard (checkContext (.object [("@context", .string baseContext)])).ok
#guard !(checkContext (.object [("@context", .string "https://ex.org/other")])).ok
#guard !(checkContext (.object [("@context", .array [])])).ok
#guard !(checkContext (.object [])).ok
-- An inline object entry is structurally fine after the base.
#guard (checkContext (.object [("@context",
          .array [.string baseContext, .object [("x", .string "y")]])])).ok
-- A non-IRI string entry is not.
#guard !(checkContext (.object [("@context",
          .array [.string baseContext, .string "not an iri"])])).ok

-- type membership, accepting the string and array forms.
#guard (checkTypeMembership (.object [("type", .string credentialType)]) credentialType).ok
#guard (checkTypeMembership (.object [("type",
          .array [.string "Other", .string credentialType])]) credentialType).ok
#guard !(checkTypeMembership (.object [("type", .array [.string "Other"])]) credentialType).ok
#guard !(checkTypeMembership (.object []) credentialType).ok

-- issuer: an IRI string or an object with an id.
#guard (checkIssuer (.object [("issuer", .string "did:example:i")])).ok
#guard (checkIssuer (.object [("issuer", .object [("id", .string "did:example:i")])])).ok
#guard !(checkIssuer (.object [("issuer", .object [])])).ok
#guard !(checkIssuer (.object [("issuer", .number "1")])).ok
#guard !(checkIssuer (.object [])).ok

-- An EMPTY credentialSubject fails: a credential asserting nothing
-- about anyone is not a credential.
#guard (checkCredentialSubject (.object [("credentialSubject", subj)])).ok
#guard !(checkCredentialSubject (.object [("credentialSubject", .object [])])).ok
#guard !(checkCredentialSubject (.object [("credentialSubject", .array [])])).ok
#guard !(checkCredentialSubject (.object [])).ok

-- Validity dates are optional but must be strings when present.
#guard (checkValidityDates (.object [])).ok
#guard (checkValidityDates (.object [("validFrom", .string "2026-01-01T00:00:00Z")])).ok
#guard !(checkValidityDates (.object [("validFrom", .number "1")])).ok

-- Verdicts carry a REASON, so a failure is actionable rather than a
-- bare false. The FIRST failure's reason survives a conjunction.
#guard match checkCredential (.object []) with
       | .fail r => r == "missing @context"
       | .pass   => false
#guard match all [.fail "first", .fail "second"] with
       | .fail r => r == "first"
       | .pass   => false

-- A presentation needs its own base type, not the credential's.
#guard (checkPresentation (.object [("@context", ctxOk),
          ("type", .array [.string presentationType])])).ok
#guard !(checkPresentation (.object [("@context", ctxOk),
          ("type", .array [.string credentialType])])).ok

end L4Factoidal.VC
