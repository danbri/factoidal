module VC.DataIntegrity

// ============================================================================
// Verifiable Credentials — Data Integrity `eddsa-rdfc-2022` cryptosuite.
// (docs/designissues/2026-07-05-vc-program-plan.md, module plan / Stage 5.)
//
// The transform -> hash -> proof-serialization pipeline, ALL orchestration in
// F*; the only OCaml-realised seam is the crypto call-out to vendored HACL* C
// (Ed25519 sign/verify + SHA-256, third_party/hacl/) — see the crypto
// assume-vals below and skills/crypto-policy/SKILL.md.
//
//   transform : RDF dataset --RDFC-1.0 (RDF.Canonical)--> canonical N-Quads
//   hash      : SHA-256 (HACL*) of the canonical N-Quads and of the
//               canonical proof-config; hashData = proofConfigHash ++ docHash
//   proof     : Ed25519 (HACL*) over hashData; proofValue = multibase-z
//               (base58btc, VC.Multibase) of the signature bytes
//
// Verify recomputes hashData the same way and Ed25519-verifies the
// multibase-decoded proofValue against the verification-method public key.
//
// NATIVE-ONLY: the crypto seam routes to vendored HACL* C, which does not link
// under wasm_of_ocaml (GitHub #286).  This module is deliberately excluded
// from the js_of_ocaml/wasm bundle; VC.Multibase (pure F*) is safe everywhere.
//
// NO hand-rolled crypto: Ed25519 and SHA-256 come from HACL* only; there is no
// pure-OCaml/F* signature fallback (iron rule + crypto-policy skill).  These
// assume-vals are tracked by GitHub #286 (the #63 family) with a stub patch in
// minimal_regrettable_glue_code_each_with_an_open_issue/.
// ============================================================================

open FStar.List.Tot
module S = FStar.String
module MB = VC.Multibase
module RC = RDF.Canonical
module RGE = RDF.Graph.Executable

// ---------------------------------------------------------------------------
// Crypto seam — realised by fstar_hacl_crypto.ml over vendored HACL* C.
// Hex boundary (lowercase, no 0x): sk/pk are 32 bytes (64 hex chars), a
// signature is 64 bytes (128 hex chars), a SHA-256 digest is 32 bytes.
// ---------------------------------------------------------------------------

// SHA-256 of the UTF-8 bytes of the argument; returns a 64-char hex digest.
assume val hash_sha256_hex : string -> string

// Ed25519 secret key (hex) -> public key (hex).
assume val ed25519_secret_to_public : string -> string

// Ed25519 sign: (secret_key_hex, message_hex) -> signature_hex.
assume val ed25519_sign : string -> string -> string

// Ed25519 verify: (public_key_hex, message_hex, signature_hex) -> bool.
assume val ed25519_verify : string -> string -> string -> bool

// ---------------------------------------------------------------------------
// Transform step — RDFC-1.0 canonical N-Quads (reuses RDF.Canonical).
// ---------------------------------------------------------------------------

let transform_dataset (ds:RGE.rdf_dataset) : string =
  RC.canonicalize_to_nquads ds

// ---------------------------------------------------------------------------
// Hash step — hashData = SHA-256(proofConfig) ++ SHA-256(document), as hex.
// (vc-di-eddsa: proofConfigHash is prepended to the transformed-doc hash.)
// ---------------------------------------------------------------------------

let hash_data_hex (canonical_doc:string) (canonical_proof_config:string) : string =
  let doc_hash = hash_sha256_hex canonical_doc in
  let cfg_hash = hash_sha256_hex canonical_proof_config in
  strcat cfg_hash doc_hash

// ---------------------------------------------------------------------------
// Proof step — create / verify over canonical inputs.
// ---------------------------------------------------------------------------

// Create: sign hashData with the Ed25519 secret key, return the multibase-z
// (base58btc) proofValue string, or None if the signature could not be
// encoded (malformed key length surfaces as an empty signature).
let eddsa_rdfc_2022_create_from_canonical
    (secret_key_hex:string) (canonical_doc:string)
    (canonical_proof_config:string) : option string =
  let hd = hash_data_hex canonical_doc canonical_proof_config in
  let sig_hex = ed25519_sign secret_key_hex hd in
  if sig_hex = "" then None
  else MB.hex_to_multibase_z sig_hex

// Verify: decode the multibase-z proofValue back to signature bytes and
// Ed25519-verify against the verification-method public key.
let eddsa_rdfc_2022_verify_from_canonical
    (public_key_hex:string) (canonical_doc:string)
    (canonical_proof_config:string) (proof_value:string) : bool =
  match MB.multibase_z_to_hex proof_value with
  | None -> false
  | Some sig_hex ->
    let hd = hash_data_hex canonical_doc canonical_proof_config in
    ed25519_verify public_key_hex hd sig_hex

// Dataset-level entry points: run the RDFC-1.0 transform first, then the
// hash+proof pipeline.  `proof_config_ds` is the proof-options dataset
// (the proof block minus proofValue, expanded to RDF).
let eddsa_rdfc_2022_create
    (secret_key_hex:string) (document_ds:RGE.rdf_dataset)
    (proof_config_ds:RGE.rdf_dataset) : option string =
  eddsa_rdfc_2022_create_from_canonical
    secret_key_hex (transform_dataset document_ds) (transform_dataset proof_config_ds)

let eddsa_rdfc_2022_verify
    (public_key_hex:string) (document_ds:RGE.rdf_dataset)
    (proof_config_ds:RGE.rdf_dataset) (proof_value:string) : bool =
  eddsa_rdfc_2022_verify_from_canonical
    public_key_hex (transform_dataset document_ds) (transform_dataset proof_config_ds) proof_value

// ---------------------------------------------------------------------------
// DataIntegrityProof `proof` block — assemble / read the proofValue.
// The proof block is a JSON object; here we build it by string assembly
// (JSON is pure text) and extract the proofValue field for verification.
// ---------------------------------------------------------------------------

noeq type di_proof = {
  di_type : string;                 // always "DataIntegrityProof"
  di_cryptosuite : string;          // "eddsa-rdfc-2022"
  di_verification_method : string;  // did:key / Multikey URL
  di_proof_purpose : string;        // e.g. "assertionMethod"
  di_created : string;              // xsd:dateTime, may be ""
  di_proof_value : string;          // multibase-z signature
}

let json_str_field (name:string) (v:string) : string =
  strcat "\"" (strcat name (strcat "\":\"" (strcat v "\"")))

// Serialize a proof block to a JSON object string.  `created` is omitted
// when empty (it is OPTIONAL in a DataIntegrityProof).
let serialize_proof (p:di_proof) : string =
  let created_part =
    if p.di_created = "" then ""
    else strcat "," (json_str_field "created" p.di_created) in
  strcat "{"
    (strcat (json_str_field "type" p.di_type)
    (strcat "," (strcat (json_str_field "cryptosuite" p.di_cryptosuite)
    (strcat "," (strcat (json_str_field "verificationMethod" p.di_verification_method)
    (strcat "," (strcat (json_str_field "proofPurpose" p.di_proof_purpose)
    (strcat created_part
    (strcat "," (strcat (json_str_field "proofValue" p.di_proof_value) "}"))))))))))

// Build the eddsa-rdfc-2022 proof block for a freshly created proofValue.
let make_eddsa_proof (verification_method:string) (proof_purpose:string)
    (created:string) (proof_value:string) : di_proof =
  { di_type = "DataIntegrityProof";
    di_cryptosuite = "eddsa-rdfc-2022";
    di_verification_method = verification_method;
    di_proof_purpose = proof_purpose;
    di_created = created;
    di_proof_value = proof_value }
