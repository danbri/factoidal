module DID.Key

// ============================================================================
// did:key — the simplest Decentralized Identifier (DID) method: fully
// deterministic, no network, no registry.  A `did:key:z6Mk...` identifier IS
// a multibase+multicodec-encoded public key; "resolving" it is pure function
// application, no I/O.  Spec: W3C-CCG `did-method-key`
// (https://w3c-ccg.github.io/did-method-key/, snapshot
// https://web.archive.org/web/20221117145136/https://w3c-ccg.github.io/did-method-key/
// — the Ed25519VerificationKey2020 revision; the spec's later "Multikey"
// revision at https://w3c-ccg.github.io/did-key-spec/ is NOT what this
// module targets, see the RDF-mapping note below for why).
//
// SCOPE / DEFERRED:
//   - Ed25519 public keys only (multicodec 0xed01, the `z6Mk...` prefix).
//     Reuses VC.Multibase's verified multibase/multicodec codec (base58btc
//     decode + the `ed25519_multicodec_prefix` constant already used by the
//     VC Data Integrity Multikey path) — no new byte-encoding logic here.
//   - `keyAgreement` (the X25519 encryption key implicitly derivable from an
//     Ed25519 signing key) is DEFERRED.  The spec derives it via a
//     birational Edwards<->Montgomery curve map (`options.
//     enableEncryptionKeyDerivation`); that is curve arithmetic, not byte
//     encoding, and does not belong in this module.  `did_key_document`
//     below therefore omits `keyAgreement` entirely.  Tracked for a future
//     module once a verified X25519 conversion primitive exists
//     (crypto-policy skill: HACL* adoption order).
//   - Other multicodec key types (secp256k1 `zQ3s...`, P-256/P-384/P-521,
//     BLS, JWK-format `z...` per the newer draft) are out of scope; a
//     non-Ed25519 multicodec prefix makes `parse_did_key` return `None`.
//
// RDF mapping: did:key's DID Document is JSON-LD; expanding it to RDF
// triples requires the exact predicate/type IRIs the JSON-LD @context files
// assign to each field.  Those were fetched and pinned by hand from the
// live context documents (not re-derived by any of our own code, to avoid
// a circular "our resolver validates itself" trap):
//   - https://www.w3.org/ns/did/v1
//       verificationMethod    -> https://w3id.org/security#verificationMethod
//       controller            -> https://w3id.org/security#controller
//       authentication        -> https://w3id.org/security#authenticationMethod
//       assertionMethod       -> https://w3id.org/security#assertionMethod
//       capabilityInvocation  -> https://w3id.org/security#capabilityInvocationMethod
//       capabilityDelegation  -> https://w3id.org/security#capabilityDelegationMethod
//       keyAgreement          -> https://w3id.org/security#keyAgreementMethod (deferred, unused)
//   - https://w3id.org/security/suites/ed25519-2020/v1
//       Ed25519VerificationKey2020 -> https://w3id.org/security#Ed25519VerificationKey2020
//       publicKeyMultibase         -> https://w3id.org/security#publicKeyMultibase
//         (@type https://w3id.org/security#multibase — a typed literal, not
//         a plain xsd:string)
//   - `type` (JSON-LD keyword) on the verification-method node expands via
//     the ordinary RDF vocabulary to rdf:type
//     (http://www.w3.org/1999/02/22-rdf-syntax-ns#type).
// The DID subject itself (`id`) carries no `rdf:type` triple in the spec's
// canonical example — `id` is the JSON-LD `@id` keyword (the node's own
// IRI), not a predicate.
//
// This is PURE, no I/O, Tot throughout — same character as VC.Multibase.
// ============================================================================

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Triple
module MB = VC.Multibase

// ---------------------------------------------------------------------------
// did:key identifier parsing — strip "did:key:", multibase-decode the
// remainder via VC.Multibase, check the multicodec prefix is Ed25519
// (0xed 0x01), strip it to the 32 raw public-key bytes.
// ---------------------------------------------------------------------------

let did_key_prefix : string = "did:key:"

let has_did_key_prefix (s:string) : bool =
  String.length s >= String.length did_key_prefix &&
  String.sub s 0 (String.length did_key_prefix) = did_key_prefix

// The multibase value after "did:key:" — e.g. "z6Mk...". Total over every
// string (returns "" if `s` is shorter than the prefix); callers gate on
// `has_did_key_prefix s` first so that branch is never actually exercised.
let multikey_of (s:string) : string =
  let len = String.length s in
  let p = String.length did_key_prefix in
  if len >= p then String.sub s p (len - p) else ""

let rec bytes_prefix_eq (pre:list MB.byte) (bs:list MB.byte) : Tot bool (decreases pre) =
  match pre, bs with
  | [], _ -> true
  | ph :: pt, bh :: bt -> ph = bh && bytes_prefix_eq pt bt
  | _, [] -> false

let rec drop_bytes (n:nat) (bs:list MB.byte) : Tot (list MB.byte) (decreases bs) =
  match bs with
  | [] -> []
  | _ :: t -> if n = 0 then bs else drop_bytes (n - 1) t

// A parsed Ed25519 did:key: the original identifier, its multibase fragment
// (the "z6Mk..." string, reused verbatim as the #fragment / publicKeyMultibase
// value), and the raw 32-byte Ed25519 public key.
noeq type ed25519_did = {
  did_string   : string;
  multikey     : string;
  pubkey_bytes : list MB.byte;
}

// Parse a `did:key:z6Mk...` identifier into its Ed25519 public key.
// Rejects: missing "did:key:" prefix, non-multibase-z / undecodable
// remainder (VC.Multibase.multibase_decode rejects anything not starting
// with 'z'), wrong multicodec prefix (not Ed25519 0xed01), or wrong decoded
// length (must be exactly 2 multicodec bytes + 32 raw key bytes = 34).
let parse_did_key (s:string) : option ed25519_did =
  if not (has_did_key_prefix s) then None
  else
    let mk = multikey_of s in
    match MB.multibase_decode mk with
    | None -> None
    | Some bs ->
      if bytes_prefix_eq MB.ed25519_multicodec_prefix bs && length bs = 34
      then Some ({ did_string = s; multikey = mk; pubkey_bytes = drop_bytes 2 bs })
      else None

// ---------------------------------------------------------------------------
// DID Document as RDF — vocabulary IRIs (see module banner for provenance).
// ---------------------------------------------------------------------------

let mk_iri (s:string) : option wf_iri =
  if is_iri s then Some s else None

let rdf_type_pred : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let sec_verificationMethod : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#verificationMethod");
  "https://w3id.org/security#verificationMethod"

let sec_controller : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#controller");
  "https://w3id.org/security#controller"

let sec_publicKeyMultibase : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#publicKeyMultibase");
  "https://w3id.org/security#publicKeyMultibase"

let sec_authenticationMethod : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#authenticationMethod");
  "https://w3id.org/security#authenticationMethod"

let sec_assertionMethod : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#assertionMethod");
  "https://w3id.org/security#assertionMethod"

let sec_capabilityInvocationMethod : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#capabilityInvocationMethod");
  "https://w3id.org/security#capabilityInvocationMethod"

let sec_capabilityDelegationMethod : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#capabilityDelegationMethod");
  "https://w3id.org/security#capabilityDelegationMethod"

let sec_Ed25519VerificationKey2020 : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#Ed25519VerificationKey2020");
  "https://w3id.org/security#Ed25519VerificationKey2020"

let sec_multibase_datatype : wf_iri =
  assert_norm (is_iri "https://w3id.org/security#multibase");
  "https://w3id.org/security#multibase"

// Resolve a `did:key:z6Mk...` identifier to its DID Document as RDF triples
// (the Ed25519VerificationKey2020 case; see module banner for the exact
// spec source and IRI provenance). `None` if `parse_did_key` rejects the
// input. `keyAgreement` is deferred (see module banner) — the returned
// triples cover `verificationMethod`, `authentication`, `assertionMethod`,
// `capabilityInvocation`, and `capabilityDelegation` only.
let did_key_document (s:string) : option (list triple) =
  match parse_did_key s with
  | None -> None
  | Some k ->
    let vm_id = strcat k.did_string (strcat "#" k.multikey) in
    (match mk_iri k.did_string, mk_iri vm_id with
     | Some did_iri, Some vm_iri ->
       let did_subj : subject = S_IRI did_iri in
       let vm_subj  : subject = S_IRI vm_iri in
       let pk_lit : wf_literal =
         { lexical_form = k.multikey; datatype = sec_multibase_datatype; lang_tag = None } in
       Some [
         { s = did_subj; p = sec_verificationMethod;         o = T_IRI vm_iri };
         { s = vm_subj;  p = rdf_type_pred;                  o = T_IRI sec_Ed25519VerificationKey2020 };
         { s = vm_subj;  p = sec_controller;                 o = T_IRI did_iri };
         { s = vm_subj;  p = sec_publicKeyMultibase;         o = T_Literal pk_lit };
         { s = did_subj; p = sec_authenticationMethod;       o = T_IRI vm_iri };
         { s = did_subj; p = sec_assertionMethod;            o = T_IRI vm_iri };
         { s = did_subj; p = sec_capabilityInvocationMethod; o = T_IRI vm_iri };
         { s = did_subj; p = sec_capabilityDelegationMethod; o = T_IRI vm_iri };
       ]
     | _, _ -> None)
