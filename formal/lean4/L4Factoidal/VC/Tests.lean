/-
L4Factoidal.VC.Tests — build-time `#guard`s for the VC Data Integrity
stage: multibase/base58btc vectors, did:key vectors, and the W3C
vc-di-eddsa §3.4 test vectors for everything PURE in the pipeline
(multibase decoding of the published proofValue, the SHA-256 hashes of
the published canonical N-Quads, the hash-data assembly, the proof
block, document-level plumbing with a stub verifier).

What is deliberately NOT here: anything that calls the HACL* extern
(`Crypto/Ed25519.lean`). Externs do not evaluate at compile time, so
the RFC 8032 vectors and the real signature checks run in
`Harness/VcProbe.lean` (`lake exe l4vc-probe`) and print a score line.

Vector provenance:
  * base58: the Bitcoin Core `base58_encode_decode.json` vectors
    (https://github.com/bitcoin/bitcoin/blob/master/src/test/data/base58_encode_decode.json).
  * did:key: `tests/did/*.did` — the did-method-key spec's own examples
    (provenance in `tests/did/README.md`); the raw key bytes below were
    cross-checked with an independent base58 decoder.
  * vc-di-eddsa: https://www.w3.org/TR/vc-di-eddsa/#representation-eddsa-rdfc-2022
    (the spec's test vectors, fetched 2026-08-22).
-/
import L4Factoidal.VC.DataIntegrity
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.VC.Tests

open L4Factoidal.RDF
open L4Factoidal.Crypto
open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.Syntax
open L4Factoidal.VC.Multibase
open L4Factoidal.VC.DidKey
open L4Factoidal.VC.Context
open L4Factoidal.VC.DataIntegrity

/-! ### Hex -/

#guard bytesOfHex? "" == some []
#guard bytesOfHex? "00ff10" == some [0, 255, 16]
#guard bytesOfHex? "00FF10" == some [0, 255, 16]
#guard bytesOfHex? "0" == none
#guard bytesOfHex? "zz" == none
#guard hexOfBytes [0, 255, 16] == "00ff10"
#guard (bytesOfHex? "ed01").map hexOfBytes == some "ed01"
-- agrees with the SHA-2 module's hex renderer on a ByteArray
#guard hexOfByteArray (sha256 "abc".toUTF8) == bytesToHex (sha256 "abc".toUTF8)

/-! ### base58btc (Bitcoin Core vectors) -/

def b58hex (hex : String) : Option String := (bytesOfHex? hex).map base58Encode

#guard b58hex "" == some ""
#guard b58hex "61" == some "2g"
#guard b58hex "626262" == some "a3gV"
#guard b58hex "636363" == some "aPEr"
#guard b58hex "73696d706c792061206c6f6e6720737472696e67" == some "2cFupjhnEsSn59qHXstmK2ffpLv2"
#guard b58hex "00eb15231dfceb60925886b67d065299925915aeb172c06647"
       == some "1NS17iag9jJgTHD1VXjvLCEnZuQ3rJDE9L"
#guard b58hex "516b6fcd0f" == some "ABnLTmg"
#guard b58hex "bf4f89001e670274dd" == some "3SEo3LWLoPntC"
#guard b58hex "572e4794" == some "3EFU7m"
#guard b58hex "ecac89cad93923c02321" == some "EJDM8drfXA6uyA"
#guard b58hex "10c8511e" == some "Rt5zm"
#guard b58hex "00000000000000000000" == some "1111111111"
#guard base58Encode "Hello World!".toUTF8.toList == "2NEpo7TZRRrLZSi2U"

#guard (base58Decode? "2NEpo7TZRRrLZSi2U").map hexOfBytes == some "48656c6c6f20576f726c6421"
#guard (base58Decode? "1111111111").map hexOfBytes == some "00000000000000000000"
#guard (base58Decode? "1NS17iag9jJgTHD1VXjvLCEnZuQ3rJDE9L").map hexOfBytes
       == some "00eb15231dfceb60925886b67d065299925915aeb172c06647"
#guard base58Decode? "" == some []
-- `0`, `O`, `I`, `l` are not in the alphabet
#guard base58Decode? "0" == none
#guard base58Decode? "2NEpo7TZRRrLZSi2Ul" == none

/-! ### Multibase -/

#guard multibaseEncodeBase58btc [] == "z"
#guard multibaseDecode? "z" == some []
#guard multibaseDecode? "2g" == none            -- no prefix
#guard multibaseDecode? "m2g" == none           -- base64 prefix: not accepted
#guard multibaseZToHex? "z2g" == some "61"
#guard hexToMultibaseZ? "61" == some "z2g"

/-! ### did:key vectors (`tests/did/`) and the Ed25519 multicodec prefix -/

def didSpecCanonical := "did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"
def didSpecTestVectors := "did:key:z6MkiTBz1ymuepAQ4HEHYSF1H8quG5GLVVQR3djdX3mDooWp"
def didVendoredSpruce := "did:key:z6MkpTHR8VNsBxYAAWHut2Geadd9jSwuBV8xRoAnwWsdvktH"

-- the decoded multikey is `ed 01` + 32 bytes
#guard (multibaseDecode? "z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK").map hexOfBytes
       == some "ed012e6fcce36701dc791488e0d0b1745cc1e33a4c1c9fcc41c63bd343dbbe0970e6"
#guard (parseDidKey didSpecCanonical).map (fun d => hexOfBytes d.pubkey)
       == some "2e6fcce36701dc791488e0d0b1745cc1e33a4c1c9fcc41c63bd343dbbe0970e6"
#guard (parseDidKey didSpecTestVectors).map (fun d => hexOfBytes d.pubkey)
       == some "3b6a27bcceb6a42d62a3a8d02a6f0d73653215771de243a63ac048a18b59da29"
#guard (parseDidKey didVendoredSpruce).map (fun d => hexOfBytes d.pubkey)
       == some "94966b7c08e405775f8de6cc1c4508f6eb227403e1025b2c8ad2d7477398c5b2"
#guard (parseDidKey didSpecCanonical).map Ed25519Did.multikey
       == some "z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"
-- the inverse reproduces the identifier
#guard ((bytesOfHex? "2e6fcce36701dc791488e0d0b1745cc1e33a4c1c9fcc41c63bd343dbbe0970e6").map
         didKeyOfPublicKey) == some didSpecCanonical
#guard ((bytesOfHex? "2e6fcce36701dc791488e0d0b1745cc1e33a4c1c9fcc41c63bd343dbbe0970e6").map
         verificationMethodOfPublicKey)
       == some (didSpecCanonical ++ "#z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK")
#guard (publicKeyOfVerificationMethod?
          (didSpecCanonical ++ "#z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK")).map hexOfBytes
       == some "2e6fcce36701dc791488e0d0b1745cc1e33a4c1c9fcc41c63bd343dbbe0970e6"

-- the five rejection cases `bin/did-runner` checks
#guard parseDidKey "did:example:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK" == none
#guard parseDidKey "" == none
#guard parseDidKey "did:key:" == none
#guard parseDidKey "did:key:mAbCdEfGhIjKlMnOpQrStUvWxYz" == none
-- secp256k1 (multicodec e7 01): right multibase, wrong multicodec
#guard parseDidKey "did:key:zQ3shokFTS3brHcDQrn82RUDfCZESWL1ZdCEJwekUDPQiYBme" == none

-- the DID Document: eight triples, the spec's canonical example
#guard (didKeyDocument didSpecCanonical).map List.length == some 8
def docLine (did : String) (i : Nat) : Option String :=
  match didKeyDocument did with
  | some ts => match ts[i]? with
    | some t => (Triple.toNTriples .rdf11 t).toOption
    | none => none
  | none => none

#guard docLine didSpecCanonical 3
       == some ("<" ++ didSpecCanonical ++ "#z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK> <https://w3id.org/security#publicKeyMultibase> \"z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK\"^^<https://w3id.org/security#multibase> .\n")
#guard didKeyDocument "did:key:zQ3shokFTS3brHcDQrn82RUDfCZESWL1ZdCEJwekUDPQiYBme" == none

/-! ### W3C vc-di-eddsa §3.4 test vectors — the pure parts -/

/-- The spec's Multikey secret key (`z3u2…` = `80 26` + 32 bytes). -/
def specSkMultikey := "z3u2en7t5LR2WtQH5PfFqMqwVHBeXouLzo6haApm8XHqvjxq"
def specPkMultikey := "z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2"
def specVm := "did:key:" ++ specPkMultikey ++ "#" ++ specPkMultikey

#guard (multikeyToEd25519SecretKey? specSkMultikey).map hexOfBytes
       == some "c96ef9ea10c5e414c471723aff9de72c35fa5b70fae97e8832ecac7d2e2b8ed6"
#guard (multikeyToEd25519PublicKey? specPkMultikey).map hexOfBytes
       == some "b00d8d938e7f773d51565aad36a623f5344f7f5d1960f9cf3e8e12620ea2810f"
-- a public key is not accepted as a secret key, and vice versa
#guard multikeyToEd25519SecretKey? specPkMultikey == none
#guard multikeyToEd25519PublicKey? specSkMultikey == none

/-- The spec's canonical N-Quads of the unsigned credential. -/
def specCanonicalDoc : String :=
  "<did:example:abcdefgh> <https://www.w3.org/ns/credentials/examples#alumniOf> \"The School of Examples\" .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/2018/credentials#VerifiableCredential> .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/ns/credentials/examples#AlumniCredential> .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/description> \"A minimum viable example of an Alumni Credential.\" .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/name> \"Alumni Credential\" .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#credentialSubject> <did:example:abcdefgh> .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#issuer> <https://vc.example/issuers/5678> .\n" ++
  "<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#validFrom> \"2023-01-01T00:00:00Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n"

/-- The spec's canonical N-Quads of the proof options. -/
def specCanonicalCfg : String :=
  "_:c14n0 <http://purl.org/dc/terms/created> \"2023-02-24T23:36:38Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n" ++
  "_:c14n0 <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://w3id.org/security#DataIntegrityProof> .\n" ++
  "_:c14n0 <https://w3id.org/security#cryptosuite> \"eddsa-rdfc-2022\"^^<https://w3id.org/security#cryptosuiteString> .\n" ++
  "_:c14n0 <https://w3id.org/security#proofPurpose> <https://w3id.org/security#assertionMethod> .\n" ++
  "_:c14n0 <https://w3id.org/security#verificationMethod> <" ++ specVm ++ "> .\n"

def specDocHash := "517744132ae165a5349155bef0bb0cf2258fff99dfe1dbd914b938d775a36017"
def specCfgHash := "bea7b7acfbad0126b135104024a5f1733e705108f42d59668b05c0c50004c6b0"
def specSigHex := "4d8e53c2d5b3f2a7891753eb16ca993325bdb0d3cfc5be1093d0a18426f5ef8578cadc0fd4b5f4dd0d1ce0aefd15ab120b7a894d0eb094ffda4e6553cd1ed50d"
def specProofValue := "z2YwC8z3ap7yx1nZYCg4L3j3ApHsF8kgPdSb5xoS1VR7vPG3F561B52hYnQF9iseabecm3ijx4K1FBTQsCZahKZme"

-- §3.3.4 Hashing: SHA-256 of each canonical form, proof config first
#guard hashHex .sha256 specCanonicalDoc == specDocHash
#guard hashHex .sha256 specCanonicalCfg == specCfgHash
#guard hashDataHex .sha256 specCanonicalDoc specCanonicalCfg == specCfgHash ++ specDocHash
#guard (hashData .sha256 specCanonicalDoc specCanonicalCfg).size == 64

-- §3.3.6 Proof Serialization: the published proofValue IS the published signature
#guard multibaseZToHex? specProofValue == some specSigHex
#guard hexToMultibaseZ? specSigHex == some specProofValue

-- The canonical proof options are what the Lean JSON-LD + RDFC stack
-- produces from the spec's proof-options JSON under the vendored
-- contexts; that needs the context files, so it is checked in the
-- probe (`lake exe l4vc-probe`, section "vc-di-eddsa-spec-vectors").

/-! ### The pipeline with a stub verifier — plumbing, not crypto

`stubVerify` accepts exactly the spec's (pk, hashData, signature)
triple, so these guards check that `verifyFromCanonical` decodes the
proofValue, assembles the hash data and hands the RIGHT bytes to the
primitive — the only things this layer is responsible for. -/

def specPk : ByteArray := toByteArray ((multikeyToEd25519PublicKey? specPkMultikey).getD [])
def specSig : ByteArray := toByteArray ((bytesOfHex? specSigHex).getD [])

def stubVerify : VerifyFn := fun pk msg sig =>
  pk == specPk && msg == hashData .sha256 specCanonicalDoc specCanonicalCfg && sig == specSig

#guard verifyFromCanonical stubVerify .sha256 specPk specCanonicalDoc specCanonicalCfg specProofValue
-- swapped roles: the hash data is H(cfg) ++ H(doc), not H(doc) ++ H(cfg)
#guard !verifyFromCanonical stubVerify .sha256 specPk specCanonicalCfg specCanonicalDoc specProofValue
-- one character of the proofValue changed
#guard !verifyFromCanonical stubVerify .sha256 specPk specCanonicalDoc specCanonicalCfg
          "z2YwC8z3ap7yx1nZYCg4L3j3ApHsF8kgPdSb5xoS1VR7vPG3F561B52hYnQF9iseabecm3ijx4K1FBTQsCZahKZmf"
-- not multibase-z at all
#guard !verifyFromCanonical stubVerify .sha256 specPk specCanonicalDoc specCanonicalCfg "u…"
-- a different canonical document (two quads swapped changes NOTHING in
-- RDFC output, but a changed literal does) changes the hash data
#guard hashData .sha256 (specCanonicalDoc ++ "x") specCanonicalCfg
       != hashData .sha256 specCanonicalDoc specCanonicalCfg

/-- A stub signer returning the spec's signature for the spec's hash data. -/
def stubSign : SignFn := fun sk msg =>
  if sk.size == 32 && msg == hashData .sha256 specCanonicalDoc specCanonicalCfg then specSig
  else ByteArray.empty

def specSk : ByteArray := toByteArray ((multikeyToEd25519SecretKey? specSkMultikey).getD [])

#guard createFromCanonical stubSign .sha256 specSk specCanonicalDoc specCanonicalCfg == some specProofValue
-- a refused key (wrong length) yields no proofValue, never an empty one
#guard createFromCanonical stubSign .sha256 ByteArray.empty specCanonicalDoc specCanonicalCfg == none

/-! ### Proof block serialisation (`serialize_proof` parity) -/

#guard serializeProof (makeEddsaProof specVm "assertionMethod" "" "zabc")
       == "{\"type\":\"DataIntegrityProof\",\"cryptosuite\":\"eddsa-rdfc-2022\",\"verificationMethod\":\""
          ++ specVm ++ "\",\"proofPurpose\":\"assertionMethod\",\"proofValue\":\"zabc\"}"
#guard serializeProof (makeEddsaProof specVm "assertionMethod" "2023-02-24T23:36:38Z" "zabc")
       == "{\"type\":\"DataIntegrityProof\",\"cryptosuite\":\"eddsa-rdfc-2022\",\"verificationMethod\":\""
          ++ specVm ++ "\",\"proofPurpose\":\"assertionMethod\",\"created\":\"2023-02-24T23:36:38Z\",\"proofValue\":\"zabc\"}"

/-! ### Proof-options context rule (`VC/Context.lean`) -/

#guard proofContextFor (some (.array [.string vcV2ContextIri]))
       == .array [.string vcV2ContextIri]
#guard proofContextFor (some (.string "https://www.w3.org/2018/credentials/v1"))
       == .array [.string "https://www.w3.org/2018/credentials/v1", .string dataIntegrityV2ContextIri]
#guard proofContextFor none == .array [.string dataIntegrityV2ContextIri]
#guard proofContextFor (some (.array [.string dataIntegrityV2ContextIri]))
       == .array [.string dataIntegrityV2ContextIri]

/-! ### Document-level plumbing: which fields go where -/

def sampleProof : Json := .object [("type", .string "DataIntegrityProof"), ("proofValue", .string "zabc")]
def sampleDoc : Json := .object [("@context", .string vcV2ContextIri), ("id", .string "urn:x"), ("proof", sampleProof)]

#guard unsecuredOf sampleDoc == .object [("@context", .string vcV2ContextIri), ("id", .string "urn:x")]
#guard proofOptionsOf sampleDoc sampleProof
       == .object [("@context", .array [.string vcV2ContextIri]), ("type", .string "DataIntegrityProof")]
-- a proof with its own @context keeps it
#guard proofOptionsOf sampleDoc (.object [("@context", .string "urn:ctx"), ("proofValue", .string "z")])
       == .object [("@context", .string "urn:ctx")]

-- without a proof the verifier refuses with the right reason (no loader needed)
#guard verifyDocument Loader.none stubVerify (unsecuredOf sampleDoc) == .error .noProof
-- a proof chain is refused, before any canonicalisation
#guard (verifyDocument Loader.none stubVerify
         (setField "proof" (.object [("previousProof", .string "urn:p"), ("type", .string "DataIntegrityProof")]) sampleDoc)
       |> fun r => r != .ok ())

end L4Factoidal.VC.Tests
