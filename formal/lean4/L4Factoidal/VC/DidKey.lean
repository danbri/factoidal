/-
L4Factoidal.VC.DidKey — the `did:key` DID method for Ed25519 keys.
Port of `formal/fstar/DID.Key.fst`.

A `did:key:z6Mk…` identifier IS a multibase+multicodec-encoded public key;
"resolving" it is pure function application — no network, no registry,
no I/O. Specification: W3C-CCG did-method-key, the
Ed25519VerificationKey2020 revision
(https://web.archive.org/web/20221117145136/https://w3c-ccg.github.io/did-method-key/),
exactly the revision the F* module targets and whose `publicKeyMultibase`
form the eddsa-rdfc-2022 `verificationMethod` (`did:key:z6Mk…#z6Mk…`)
pairs with.

Scope, as in the F*:
  * Ed25519 public keys only (multicodec `ed 01`, the `z6Mk…` prefix). A
    different multicodec (secp256k1 `zQ3s…`, P-256, BLS, …) makes
    `parseDidKey` return `none`.
  * `keyAgreement` (the X25519 key derived from the Ed25519 key by the
    birational Edwards→Montgomery map) is NOT produced — that is curve
    arithmetic, which this tree never hand-writes (crypto-policy).
    `didKeyDocument` omits it, and the expected documents in `tests/did/`
    omit it for the same reason.

RDF mapping of the DID Document: the predicate and type IRIs below are
the `@id`/`@type` mappings pinned by hand in `DID.Key.fst`'s banner from
the live `https://www.w3.org/ns/did/v1` and
`https://w3id.org/security/suites/ed25519-2020/v1` contexts — copied, not
re-derived by this tree's JSON-LD processor, so the resolver does not
validate itself.

Beyond the F*, this module also has the INVERSE direction
(`didKeyOfPublicKey`, `verificationMethodOfPublicKey`) that the F* tree's
VC-API shim re-implements in JavaScript for lack of an F* export
(`bin/vc-api-shim/server.mjs`, `didKeyFromPublicKeyHex`), and
`VC/Theorems.lean` proves `parseDidKey (didKeyOfPublicKey pk)` recovers
`pk` for every 32-byte key.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.VC.Multibase

namespace L4Factoidal.VC.DidKey

open L4Factoidal.RDF
open L4Factoidal.VC.Multibase

/-- The method prefix, as a character list (the proofs work on lists). -/
def didKeyPrefixChars : List Char := "did:key:".toList

def didKeyPrefix : String := String.ofList didKeyPrefixChars

/-- Drop `pre` from the front of `cs`, if it is there. -/
def stripPrefixChars : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p == c then stripPrefixChars ps cs else none
  | _ :: _, [] => none

/-- A parsed Ed25519 did:key: the identifier, its multibase fragment
(`z6Mk…`, reused verbatim as the `#fragment` and the
`publicKeyMultibase` value), and the 32 raw public-key bytes. Port of
`ed25519_did`. -/
structure Ed25519Did where
  didString : String
  multikey  : String
  pubkey    : Bytes
  deriving Repr, DecidableEq

/-- `parseDidKey` over characters. -/
def parseDidKeyChars (cs : List Char) : Option Ed25519Did :=
  match stripPrefixChars didKeyPrefixChars cs with
  | none => none
  | some mkChars =>
    let mk := String.ofList mkChars
    match multikeyToEd25519PublicKey? mk with
    | some pk => some { didString := String.ofList cs, multikey := mk, pubkey := pk }
    | none => none

/-- Parse a `did:key:z6Mk…` identifier into its Ed25519 public key.
Rejects: a missing `did:key:` prefix, a non-`z` or undecodable
multibase remainder, a non-Ed25519 multicodec prefix, or a decoded
length other than 2 + 32 bytes. Port of `parse_did_key`. -/
def parseDidKey (s : String) : Option Ed25519Did := parseDidKeyChars s.toList

/-- The inverse: a 32-byte public key to its `did:key:z6Mk…` identifier.
Total over any byte list; `VC/Theorems.lean` proves the round trip. -/
def didKeyOfPublicKey (pk : Bytes) : String :=
  didKeyPrefix ++ ed25519PublicKeyToMultikey pk

/-- The `did:key:z6Mk…#z6Mk…` verification-method URL of a public key —
the form eddsa-rdfc-2022 proofs carry in `verificationMethod`. -/
def verificationMethodOfPublicKey (pk : Bytes) : String :=
  let mk := ed25519PublicKeyToMultikey pk
  didKeyPrefix ++ mk ++ "#" ++ mk

/-- Public key behind a `verificationMethod` URL: `did:key:z6Mk…#…` (the
fragment, if any, is dropped) or a bare `did:key:z6Mk…`. `none` for
anything that is not an Ed25519 did:key — a verifier must then FAIL,
never guess. -/
def publicKeyOfVerificationMethod? (vm : String) : Option Bytes :=
  let did := String.ofList (vm.toList.takeWhile (fun c => c != '#'))
  (parseDidKey did).map Ed25519Did.pubkey

/-! ## The DID Document as RDF (vocabulary IRIs pinned in `DID.Key.fst`) -/

def mkIri? (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

def rdfType : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩
def secVerificationMethod : WfIri := ⟨"https://w3id.org/security#verificationMethod", rfl⟩
def secController : WfIri := ⟨"https://w3id.org/security#controller", rfl⟩
def secPublicKeyMultibase : WfIri := ⟨"https://w3id.org/security#publicKeyMultibase", rfl⟩
def secAuthenticationMethod : WfIri := ⟨"https://w3id.org/security#authenticationMethod", rfl⟩
def secAssertionMethod : WfIri := ⟨"https://w3id.org/security#assertionMethod", rfl⟩
def secCapabilityInvocationMethod : WfIri :=
  ⟨"https://w3id.org/security#capabilityInvocationMethod", rfl⟩
def secCapabilityDelegationMethod : WfIri :=
  ⟨"https://w3id.org/security#capabilityDelegationMethod", rfl⟩
def secEd25519VerificationKey2020 : WfIri :=
  ⟨"https://w3id.org/security#Ed25519VerificationKey2020", rfl⟩
/-- The datatype of `publicKeyMultibase` values (`@type sec:multibase` in
the ed25519-2020 context — a typed literal, not `xsd:string`). -/
def secMultibase : WfIri := ⟨"https://w3id.org/security#multibase", rfl⟩

/-- A `sec:multibase`-typed literal. -/
def multibaseLiteral (lex : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := secMultibase, langTag := none, direction := none }, rfl⟩

/-- Resolve a did:key identifier to its DID Document triples — the
did-method-key "Document Creation Algorithm" steps 3–7 (verification
method with `controller` and `publicKeyMultibase`; `authentication`,
`assertionMethod`, `capabilityInvocation`, `capabilityDelegation` each
naming that method). `keyAgreement` omitted (module header). `none` if
`parseDidKey` rejects the input. Port of `did_key_document`. -/
def didKeyDocument (s : String) : Option (List Triple) :=
  match parseDidKey s with
  | none => none
  | some k =>
    let vmId := k.didString ++ "#" ++ k.multikey
    match mkIri? k.didString, mkIri? vmId with
    | some didIri, some vmIri =>
      let didSubj : Subject := .iri didIri
      let vmSubj : Subject := .iri vmIri
      some [
        { s := didSubj, p := secVerificationMethod,         o := .iri vmIri },
        { s := vmSubj,  p := rdfType,                       o := .iri secEd25519VerificationKey2020 },
        { s := vmSubj,  p := secController,                 o := .iri didIri },
        { s := vmSubj,  p := secPublicKeyMultibase,         o := .literal (multibaseLiteral k.multikey) },
        { s := didSubj, p := secAuthenticationMethod,       o := .iri vmIri },
        { s := didSubj, p := secAssertionMethod,            o := .iri vmIri },
        { s := didSubj, p := secCapabilityInvocationMethod, o := .iri vmIri },
        { s := didSubj, p := secCapabilityDelegationMethod, o := .iri vmIri } ]
    | _, _ => none

end L4Factoidal.VC.DidKey
