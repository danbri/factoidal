/-
L4Factoidal.VC.DataIntegrity — Verifiable Credentials Data Integrity,
the `eddsa-rdfc-2022` cryptosuite: proof creation and verification.
Port of `formal/fstar/VC.DataIntegrity.fst`, extended upward to the
JSON-LD document level that the F* tree keeps in consumer glue
(`bin/vc-api-shim/server.mjs`).

Specifications:
  * Verifiable Credential Data Integrity 1.0, W3C Recommendation
    2025-05-15 (https://www.w3.org/TR/vc-data-integrity/): §4.3 Add
    Proof, §4.4 Verify Proof, §2.1 Proofs (required fields).
  * Data Integrity EdDSA Cryptosuites v1.0, W3C Recommendation
    2025-05-15 (https://www.w3.org/TR/vc-di-eddsa/), §3.3
    eddsa-rdfc-2022: §3.3.1 Create Proof, §3.3.2 Verify Proof, §3.3.3
    Transformation (RDFC-1.0), §3.3.4 Hashing (SHA-256 of the proof
    configuration, then of the transformed document, concatenated in
    that order), §3.3.5 Proof Configuration, §3.3.6 Proof Serialization
    (Ed25519 over the hash data), and §3.4 Test Vectors, which
    `VC/Tests.lean` and `Harness/VcProbe.lean` replay.

## Shape

    transform  : Dataset --RDFC-1.0 (RDF/Canonical)--> canonical N-Quads
    hash       : hashBytes alg (proof config) ++ hashBytes alg (document)
    proof      : sign sk hashData  -->  proofValue = "z" ++ base58btc(sig)
    verify     : base58btc⁻¹(proofValue) --> verify pk hashData sig

The F* realises SHA-256 and Ed25519 through four crypto `assume val`s.
Here SHA-256 is pure Lean behind the `HashAlgorithm` dispatcher (hash
agility: the cryptosuite pins SHA-256, the CODE does not), and the
signature primitive is a PARAMETER — `SignFn` / `VerifyFn` function
values — so every definition below is a total function of explicit
inputs and the `#guard`s can drive the whole pipeline with a stub. The
HACL* binding (`Crypto/Ed25519.lean`) is passed in by the executable
edge only. That also keeps the library free of any evaluation of an
`@[extern]` at compile time.

## Document level (not in the F*)

`secureDocument` and `verifyDocument` take a JSON-LD document, build the
proof-options document (the proof minus `proofValue`, under the context
`VC/Context.lean` prescribes), run JSON-LD toRdf on both (the loader is a
parameter), and then the byte-level pipeline. Verification resolves
`verificationMethod` through did:key only (as the shim does), requires
`type = DataIntegrityProof`, `cryptosuite = eddsa-rdfc-2022`, and the
expected `proofPurpose`, and refuses — never guesses — on anything else.
A proof SET (array of proofs) verifies when every member verifies; proof
CHAINS (`previousProof`) are not implemented and are refused.
-/
import L4Factoidal.RDF.Canonical
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.VC.Multibase
import L4Factoidal.VC.DidKey
import L4Factoidal.VC.Context

namespace L4Factoidal.VC.DataIntegrity

open L4Factoidal.RDF
open L4Factoidal.Crypto
open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.VC.Multibase
open L4Factoidal.VC.DidKey
open L4Factoidal.VC.Context

/-- A signing primitive: secret key, message → signature (empty on a
refused key). The HACL* binding `Crypto.Ed25519.sign` has this type. -/
abbrev SignFn := ByteArray → ByteArray → ByteArray

/-- A verifying primitive: public key, message, signature → accepted?
The HACL* binding `Crypto.Ed25519.verify` has this type. -/
abbrev VerifyFn := ByteArray → ByteArray → ByteArray → Bool

/-- The cryptosuite's identifier. -/
def cryptosuiteName : String := "eddsa-rdfc-2022"

/-- The proof type. -/
def proofTypeName : String := "DataIntegrityProof"

/-! ## Transform (§3.3.3) — RDFC-1.0 canonical N-Quads -/

/-- `transformDataset` — the RDFC-1.0 canonical N-Quads document of a
dataset (RDFC-1.0 §4.4, SHA-256 as the canonicalisation hash — that
hash is RDFC's own parameter, separate from the cryptosuite's). Port of
`transform_dataset`. -/
def transformDataset (ds : Dataset) : String := ds.canonicalNQuads .sha256

/-! ## Hash (§3.3.4) — hashData = H(proof config) ++ H(document) -/

/-- Hash data bytes: the digest of the canonical proof configuration
FIRST, then the digest of the canonical document (§3.3.4 step 3). Port
of `hash_data_hex`, over bytes and with the algorithm a parameter. -/
def hashData (alg : HashAlgorithm) (canonicalDoc canonicalProofConfig : String) : ByteArray :=
  hashBytes alg canonicalProofConfig.toUTF8 ++ hashBytes alg canonicalDoc.toUTF8

/-- The same as lowercase hex — what the F* `hash_data_hex` returns and
what the vc-di-eddsa test vectors print. -/
def hashDataHex (alg : HashAlgorithm) (canonicalDoc canonicalProofConfig : String) : String :=
  hexOfByteArray (hashData alg canonicalDoc canonicalProofConfig)

/-! ## Proof serialization / verification over canonical inputs -/

/-- Create the `proofValue` (§3.3.6): sign the hash data, multibase-z
encode the signature. `none` when the primitive refuses the key (empty
signature). Port of `eddsa_rdfc_2022_create_from_canonical`. -/
def createFromCanonical (signF : SignFn) (alg : HashAlgorithm) (sk : ByteArray)
    (canonicalDoc canonicalProofConfig : String) : Option String :=
  let sig := signF sk (hashData alg canonicalDoc canonicalProofConfig)
  if sig.size == 0 then none
  else some (multibaseEncodeBase58btc (ofByteArray sig))

/-- Verify a `proofValue` (§3.3.2 steps 4–6): multibase-decode, recompute
the hash data, ask the primitive. `false` on an undecodable proofValue.
Port of `eddsa_rdfc_2022_verify_from_canonical`. -/
def verifyFromCanonical (verifyF : VerifyFn) (alg : HashAlgorithm) (pk : ByteArray)
    (canonicalDoc canonicalProofConfig proofValue : String) : Bool :=
  match multibaseDecode? proofValue with
  | none => false
  | some sigBytes => verifyF pk (hashData alg canonicalDoc canonicalProofConfig) (toByteArray sigBytes)

/-- Dataset-level create: transform both datasets, then the byte pipeline.
`proofConfig` is the proof-options dataset (the proof block minus
`proofValue`, expanded to RDF). Port of `eddsa_rdfc_2022_create`. -/
def createProofValue (signF : SignFn) (alg : HashAlgorithm) (sk : ByteArray)
    (document proofConfig : Dataset) : Option String :=
  createFromCanonical signF alg sk (transformDataset document) (transformDataset proofConfig)

/-- Dataset-level verify. Port of `eddsa_rdfc_2022_verify`. -/
def verifyProofValue (verifyF : VerifyFn) (alg : HashAlgorithm) (pk : ByteArray)
    (document proofConfig : Dataset) (proofValue : String) : Bool :=
  verifyFromCanonical verifyF alg pk (transformDataset document) (transformDataset proofConfig)
    proofValue

/-! ## The proof block (§2.1 Proofs) -/

/-- A DataIntegrityProof block. Port of `di_proof`. -/
structure DiProof where
  type               : String := proofTypeName
  cryptosuite        : String := cryptosuiteName
  verificationMethod : String
  proofPurpose       : String
  /-- xsd:dateTime; `""` = absent (`created` is OPTIONAL). -/
  created            : String := ""
  proofValue         : String
  deriving Repr, DecidableEq

/-- Port of `make_eddsa_proof`. -/
def makeEddsaProof (verificationMethod proofPurpose created proofValue : String) : DiProof :=
  { verificationMethod, proofPurpose, created, proofValue }

/-- The proof block as JSON, `created` omitted when empty. -/
def DiProof.toJson (p : DiProof) : Json :=
  Json.object (
    [("type", Json.string p.type), ("cryptosuite", Json.string p.cryptosuite),
     ("verificationMethod", Json.string p.verificationMethod),
     ("proofPurpose", Json.string p.proofPurpose)]
    ++ (if p.created.isEmpty then [] else [("created", Json.string p.created)])
    ++ [("proofValue", Json.string p.proofValue)])

/-- Serialise a proof block as compact JSON text. Port of
`serialize_proof` (the F* assembles the same text by hand; the
field order is identical). -/
def serializeProof (p : DiProof) : String := toStringCompact p.toJson

/-! ## JSON helpers (object surgery on `Json.object` field lists) -/

def fieldsOf? : Json → Option (List (String × Json))
  | .object fs => some fs
  | _ => none

/-- The object without the named field(s). -/
def withoutField (name : String) (j : Json) : Json :=
  match j with
  | .object fs => .object (fs.filter (fun kv => kv.1 != name))
  | j => j

/-- The object with `name` set to `v` (existing occurrences removed;
the new field goes last, which is where a `proof` belongs). -/
def setField (name : String) (v : Json) (j : Json) : Json :=
  match j with
  | .object fs => .object (fs.filter (fun kv => kv.1 != name) ++ [(name, v)])
  | _ => .object [(name, v)]

/-- The object with `name` set to `v` FIRST (where `@context` belongs). -/
def setFieldFirst (name : String) (v : Json) (j : Json) : Json :=
  match j with
  | .object fs => .object ((name, v) :: fs.filter (fun kv => kv.1 != name))
  | _ => .object [(name, v)]

/-! ## Document level: proof configuration and canonical forms -/

/-- The proof-options document of a proof (§3.3.5 Proof Configuration):
the proof block minus `proofValue`, under its own `@context` if it has
one, else the context `VC/Context.proofContextFor` derives from the
securing document's. -/
def proofOptionsOf (doc proof : Json) : Json :=
  let ctx := match proof.field? "@context" with
    | some c => c
    | none => proofContextFor (doc.field? "@context")
  setFieldFirst "@context" ctx (withoutField "proofValue" proof)

/-- The unsecured document: the document minus its `proof`. -/
def unsecuredOf (doc : Json) : Json := withoutField "proof" doc

/-- JSON-LD toRdf of a JSON value, then RDFC-1.0. The string round trip
through the compact serialiser is how the JSON-LD entry point takes its
input. -/
def canonicalizeJsonLd (loader : Loader) (j : Json) : Except String String :=
  match parseJsonLd loader (toStringCompact j) none none none none with
  | .error e => .error s!"JSON-LD toRdf failed: {e.code}"
  | .ok ds => .ok (transformDataset ds)

/-- Why a document did not verify. Every constructor is a REFUSAL with a
reason; there is no silent path. -/
inductive VerifyError where
  | noProof
  | proofNotObject
  | wrongType (got : String)
  | wrongCryptosuite (got : String)
  | wrongPurpose (got expected : String)
  | missingField (name : String)
  | unresolvableVerificationMethod (vm : String)
  | proofChainUnsupported
  | canonicalization (what msg : String)
  | signatureRejected
  deriving Repr, DecidableEq

def VerifyError.describe : VerifyError → String
  | .noProof => "document has no proof"
  | .proofNotObject => "proof is not an object"
  | .wrongType got => s!"proof.type is \"{got}\", expected \"{proofTypeName}\""
  | .wrongCryptosuite got => s!"proof.cryptosuite is \"{got}\", expected \"{cryptosuiteName}\""
  | .wrongPurpose got expected => s!"proof.proofPurpose is \"{got}\", expected \"{expected}\""
  | .missingField n => s!"proof is missing required field \"{n}\""
  | .unresolvableVerificationMethod vm =>
    s!"could not resolve verificationMethod \"{vm}\" (only Ed25519 did:key is supported)"
  | .proofChainUnsupported => "proof chains (previousProof) are not supported"
  | .canonicalization what msg => s!"canonicalization of {what} failed: {msg}"
  | .signatureRejected => "signature did not verify"

/-- Verify ONE proof object against the unsecured document's canonical
form (§4.4 Verify Proof + §3.3.2). -/
def verifyOneProof (loader : Loader) (verifyF : VerifyFn) (alg : HashAlgorithm)
    (expectedPurpose : String) (doc : Json) (canonicalDoc : String) (proof : Json) :
    Except VerifyError Unit := do
  let _ ← match fieldsOf? proof with | some fs => pure fs | none => throw .proofNotObject
  if (proof.field? "previousProof").isSome then throw .proofChainUnsupported
  let need (n : String) : Except VerifyError String :=
    match proof.getString? n with
    | some s => if s.isEmpty then throw (.missingField n) else pure s
    | none => throw (.missingField n)
  let ty ← need "type"
  if ty != proofTypeName then throw (.wrongType ty)
  let cs ← need "cryptosuite"
  if cs != cryptosuiteName then throw (.wrongCryptosuite cs)
  let vm ← need "verificationMethod"
  let purpose ← need "proofPurpose"
  if purpose != expectedPurpose then throw (.wrongPurpose purpose expectedPurpose)
  let pv ← need "proofValue"
  let pk ← match publicKeyOfVerificationMethod? vm with
    | some pk => pure (toByteArray pk)
    | none => throw (.unresolvableVerificationMethod vm)
  let canonicalCfg ← match canonicalizeJsonLd loader (proofOptionsOf doc proof) with
    | .ok s => pure s
    | .error m => throw (.canonicalization "proof options" m)
  if verifyFromCanonical verifyF alg pk canonicalDoc canonicalCfg pv then pure ()
  else throw .signatureRejected

/-- Verify a secured document (§4.4): its `proof` is one object or a
proof set (array); every member must verify. -/
def verifyDocument (loader : Loader) (verifyF : VerifyFn) (doc : Json)
    (expectedPurpose : String := "assertionMethod") (alg : HashAlgorithm := .sha256) :
    Except VerifyError Unit := do
  let proofs ← match doc.field? "proof" with
    | none => throw .noProof
    | some (.array ps) => if ps.isEmpty then throw .noProof else pure ps
    | some p => pure [p]
  let canonicalDoc ← match canonicalizeJsonLd loader (unsecuredOf doc) with
    | .ok s => pure s
    | .error m => throw (.canonicalization "document" m)
  for p in proofs do
    verifyOneProof loader verifyF alg expectedPurpose doc canonicalDoc p

/-- Secure a document (§4.3 Add Proof + §3.3.1 Create Proof): build the
proof configuration from the options, canonicalise document and
configuration, sign, and return the document with its `proof` block
attached and its `@context` extended the way `proofContextFor` extends
the proof's (so re-verification derives the same configuration). `sk`
is the 32-byte Ed25519 secret key; `verificationMethod` is normally
`verificationMethodOfPublicKey (secretToPublic sk)`. -/
def secureDocument (loader : Loader) (signF : SignFn) (sk : ByteArray)
    (verificationMethod proofPurpose created : String) (doc : Json)
    (alg : HashAlgorithm := .sha256) : Except String Json := do
  let unsecured := unsecuredOf doc
  let ctx := proofContextFor (doc.field? "@context")
  let options : DiProof := makeEddsaProof verificationMethod proofPurpose created ""
  let proofConfig := setFieldFirst "@context" ctx (withoutField "proofValue" options.toJson)
  let canonicalDoc ← canonicalizeJsonLd loader unsecured
  let canonicalCfg ← canonicalizeJsonLd loader proofConfig
  match createFromCanonical signF alg sk canonicalDoc canonicalCfg with
  | none => throw "signing refused (secret key is not 32 bytes)"
  | some pv =>
    let proof := (makeEddsaProof verificationMethod proofPurpose created pv).toJson
    pure (setField "proof" proof (setFieldFirst "@context" ctx unsecured))

end L4Factoidal.VC.DataIntegrity
