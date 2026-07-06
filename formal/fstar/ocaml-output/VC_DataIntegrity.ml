open Prims
let hash_sha256_hex (s : Prims.string) : Prims.string=
  Fstar_hacl_crypto.sha256_hex s
let ed25519_secret_to_public (sk : Prims.string) : Prims.string=
  Fstar_hacl_crypto.ed25519_secret_to_public sk
let ed25519_sign (sk : Prims.string) (msg : Prims.string) :
  Prims.string= Fstar_hacl_crypto.ed25519_sign sk msg
let ed25519_verify (pk : Prims.string) (msg : Prims.string)
  (sg : Prims.string) : Prims.bool=
  Fstar_hacl_crypto.ed25519_verify pk msg sg
let transform_dataset (ds : RDF_Graph.rdf_dataset) : Prims.string=
  RDF_Canonical.canonicalize_to_nquads ds
let hash_data_hex (canonical_doc : Prims.string)
  (canonical_proof_config : Prims.string) : Prims.string=
  let doc_hash = hash_sha256_hex canonical_doc in
  let cfg_hash = hash_sha256_hex canonical_proof_config in
  Prims.strcat cfg_hash doc_hash
let eddsa_rdfc_2022_create_from_canonical (secret_key_hex : Prims.string)
  (canonical_doc : Prims.string) (canonical_proof_config : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let hd = hash_data_hex canonical_doc canonical_proof_config in
  let sig_hex = ed25519_sign secret_key_hex hd in
  if sig_hex = ""
  then FStar_Pervasives_Native.None
  else VC_Multibase.hex_to_multibase_z sig_hex
let eddsa_rdfc_2022_verify_from_canonical (public_key_hex : Prims.string)
  (canonical_doc : Prims.string) (canonical_proof_config : Prims.string)
  (proof_value : Prims.string) : Prims.bool=
  match VC_Multibase.multibase_z_to_hex proof_value with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some sig_hex ->
      let hd = hash_data_hex canonical_doc canonical_proof_config in
      ed25519_verify public_key_hex hd sig_hex
let eddsa_rdfc_2022_create (secret_key_hex : Prims.string)
  (document_ds : RDF_Graph.rdf_dataset)
  (proof_config_ds : RDF_Graph.rdf_dataset) :
  Prims.string FStar_Pervasives_Native.option=
  eddsa_rdfc_2022_create_from_canonical secret_key_hex
    (transform_dataset document_ds) (transform_dataset proof_config_ds)
let eddsa_rdfc_2022_verify (public_key_hex : Prims.string)
  (document_ds : RDF_Graph.rdf_dataset)
  (proof_config_ds : RDF_Graph.rdf_dataset) (proof_value : Prims.string) :
  Prims.bool=
  eddsa_rdfc_2022_verify_from_canonical public_key_hex
    (transform_dataset document_ds) (transform_dataset proof_config_ds)
    proof_value
type di_proof =
  {
  di_type: Prims.string ;
  di_cryptosuite: Prims.string ;
  di_verification_method: Prims.string ;
  di_proof_purpose: Prims.string ;
  di_created: Prims.string ;
  di_proof_value: Prims.string }
let __proj__Mkdi_proof__item__di_type (projectee : di_proof) : Prims.string=
  match projectee with
  | { di_type; di_cryptosuite; di_verification_method; di_proof_purpose;
      di_created; di_proof_value;_} -> di_type
let __proj__Mkdi_proof__item__di_cryptosuite (projectee : di_proof) :
  Prims.string=
  match projectee with
  | { di_type; di_cryptosuite; di_verification_method; di_proof_purpose;
      di_created; di_proof_value;_} -> di_cryptosuite
let __proj__Mkdi_proof__item__di_verification_method (projectee : di_proof) :
  Prims.string=
  match projectee with
  | { di_type; di_cryptosuite; di_verification_method; di_proof_purpose;
      di_created; di_proof_value;_} -> di_verification_method
let __proj__Mkdi_proof__item__di_proof_purpose (projectee : di_proof) :
  Prims.string=
  match projectee with
  | { di_type; di_cryptosuite; di_verification_method; di_proof_purpose;
      di_created; di_proof_value;_} -> di_proof_purpose
let __proj__Mkdi_proof__item__di_created (projectee : di_proof) :
  Prims.string=
  match projectee with
  | { di_type; di_cryptosuite; di_verification_method; di_proof_purpose;
      di_created; di_proof_value;_} -> di_created
let __proj__Mkdi_proof__item__di_proof_value (projectee : di_proof) :
  Prims.string=
  match projectee with
  | { di_type; di_cryptosuite; di_verification_method; di_proof_purpose;
      di_created; di_proof_value;_} -> di_proof_value
let json_str_field (name : Prims.string) (v : Prims.string) : Prims.string=
  Prims.strcat "\""
    (Prims.strcat name (Prims.strcat "\":\"" (Prims.strcat v "\"")))
let serialize_proof (p : di_proof) : Prims.string=
  let created_part =
    if p.di_created = ""
    then ""
    else Prims.strcat "," (json_str_field "created" p.di_created) in
  Prims.strcat "{"
    (Prims.strcat (json_str_field "type" p.di_type)
       (Prims.strcat ","
          (Prims.strcat (json_str_field "cryptosuite" p.di_cryptosuite)
             (Prims.strcat ","
                (Prims.strcat
                   (json_str_field "verificationMethod"
                      p.di_verification_method)
                   (Prims.strcat ","
                      (Prims.strcat
                         (json_str_field "proofPurpose" p.di_proof_purpose)
                         (Prims.strcat created_part
                            (Prims.strcat ","
                               (Prims.strcat
                                  (json_str_field "proofValue"
                                     p.di_proof_value) "}"))))))))))
let make_eddsa_proof (verification_method : Prims.string)
  (proof_purpose : Prims.string) (created : Prims.string)
  (proof_value : Prims.string) : di_proof=
  {
    di_type = "DataIntegrityProof";
    di_cryptosuite = "eddsa-rdfc-2022";
    di_verification_method = verification_method;
    di_proof_purpose = proof_purpose;
    di_created = created;
    di_proof_value = proof_value
  }
