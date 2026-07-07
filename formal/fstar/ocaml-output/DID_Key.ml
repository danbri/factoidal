open Prims
let did_key_prefix : Prims.string= "did:key:"
let has_did_key_prefix (s : Prims.string) : Prims.bool=
  ((FStar_String.strlen s) >= (FStar_String.strlen did_key_prefix)) &&
    ((FStar_String.sub s Prims.int_zero (FStar_String.strlen did_key_prefix))
       = did_key_prefix)
let multikey_of (s : Prims.string) : Prims.string=
  let len = FStar_String.strlen s in
  let p = FStar_String.strlen did_key_prefix in
  if len >= p then FStar_String.sub s p (len - p) else ""
let rec bytes_prefix_eq (pre : VC_Multibase.byte Prims.list)
  (bs : VC_Multibase.byte Prims.list) : Prims.bool=
  match (pre, bs) with
  | ([], uu___) -> true
  | (ph::pt, bh::bt) -> (ph = bh) && (bytes_prefix_eq pt bt)
  | (uu___, []) -> false
let rec drop_bytes (n : Prims.nat) (bs : VC_Multibase.byte Prims.list) :
  VC_Multibase.byte Prims.list=
  match bs with
  | [] -> []
  | uu___::t ->
      if n = Prims.int_zero then bs else drop_bytes (n - Prims.int_one) t
type ed25519_did =
  {
  did_string: Prims.string ;
  multikey: Prims.string ;
  pubkey_bytes: VC_Multibase.byte Prims.list }
let __proj__Mked25519_did__item__did_string (projectee : ed25519_did) :
  Prims.string=
  match projectee with
  | { did_string; multikey; pubkey_bytes;_} -> did_string
let __proj__Mked25519_did__item__multikey (projectee : ed25519_did) :
  Prims.string=
  match projectee with | { did_string; multikey; pubkey_bytes;_} -> multikey
let __proj__Mked25519_did__item__pubkey_bytes (projectee : ed25519_did) :
  VC_Multibase.byte Prims.list=
  match projectee with
  | { did_string; multikey; pubkey_bytes;_} -> pubkey_bytes
let parse_did_key (s : Prims.string) :
  ed25519_did FStar_Pervasives_Native.option=
  if Prims.op_Negation (has_did_key_prefix s)
  then FStar_Pervasives_Native.None
  else
    (let mk = multikey_of s in
     match VC_Multibase.multibase_decode mk with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some bs ->
         if
           (bytes_prefix_eq VC_Multibase.ed25519_multicodec_prefix bs) &&
             ((FStar_List_Tot_Base.length bs) = (Prims.of_int (34)))
         then
           FStar_Pervasives_Native.Some
             {
               did_string = s;
               multikey = mk;
               pubkey_bytes = (drop_bytes (Prims.of_int (2)) bs)
             }
         else FStar_Pervasives_Native.None)
let mk_iri (s : Prims.string) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  if RDF_Term.is_iri s
  then FStar_Pervasives_Native.Some s
  else FStar_Pervasives_Native.None
let rdf_type_pred : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let sec_verificationMethod : RDF_Term.wf_iri=
  "https://w3id.org/security#verificationMethod"
let sec_controller : RDF_Term.wf_iri= "https://w3id.org/security#controller"
let sec_publicKeyMultibase : RDF_Term.wf_iri=
  "https://w3id.org/security#publicKeyMultibase"
let sec_authenticationMethod : RDF_Term.wf_iri=
  "https://w3id.org/security#authenticationMethod"
let sec_assertionMethod : RDF_Term.wf_iri=
  "https://w3id.org/security#assertionMethod"
let sec_capabilityInvocationMethod : RDF_Term.wf_iri=
  "https://w3id.org/security#capabilityInvocationMethod"
let sec_capabilityDelegationMethod : RDF_Term.wf_iri=
  "https://w3id.org/security#capabilityDelegationMethod"
let sec_Ed25519VerificationKey2020 : RDF_Term.wf_iri=
  "https://w3id.org/security#Ed25519VerificationKey2020"
let sec_multibase_datatype : RDF_Term.wf_iri=
  "https://w3id.org/security#multibase"
let did_key_document (s : Prims.string) :
  RDF_Triple.triple Prims.list FStar_Pervasives_Native.option=
  match parse_did_key s with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some k ->
      let vm_id = Prims.strcat k.did_string (Prims.strcat "#" k.multikey) in
      (match ((mk_iri k.did_string), (mk_iri vm_id)) with
       | (FStar_Pervasives_Native.Some did_iri, FStar_Pervasives_Native.Some
          vm_iri) ->
           let did_subj = RDF_Term.S_IRI did_iri in
           let vm_subj = RDF_Term.S_IRI vm_iri in
           let pk_lit =
             {
               RDF_Term.lexical_form = (k.multikey);
               RDF_Term.datatype = sec_multibase_datatype;
               RDF_Term.lang_tag = FStar_Pervasives_Native.None
             } in
           FStar_Pervasives_Native.Some
             [{
                RDF_Triple.s = did_subj;
                RDF_Triple.p = sec_verificationMethod;
                RDF_Triple.o = (RDF_Term.T_IRI vm_iri)
              };
             {
               RDF_Triple.s = vm_subj;
               RDF_Triple.p = rdf_type_pred;
               RDF_Triple.o = (RDF_Term.T_IRI sec_Ed25519VerificationKey2020)
             };
             {
               RDF_Triple.s = vm_subj;
               RDF_Triple.p = sec_controller;
               RDF_Triple.o = (RDF_Term.T_IRI did_iri)
             };
             {
               RDF_Triple.s = vm_subj;
               RDF_Triple.p = sec_publicKeyMultibase;
               RDF_Triple.o = (RDF_Term.T_Literal pk_lit)
             };
             {
               RDF_Triple.s = did_subj;
               RDF_Triple.p = sec_authenticationMethod;
               RDF_Triple.o = (RDF_Term.T_IRI vm_iri)
             };
             {
               RDF_Triple.s = did_subj;
               RDF_Triple.p = sec_assertionMethod;
               RDF_Triple.o = (RDF_Term.T_IRI vm_iri)
             };
             {
               RDF_Triple.s = did_subj;
               RDF_Triple.p = sec_capabilityInvocationMethod;
               RDF_Triple.o = (RDF_Term.T_IRI vm_iri)
             };
             {
               RDF_Triple.s = did_subj;
               RDF_Triple.p = sec_capabilityDelegationMethod;
               RDF_Triple.o = (RDF_Term.T_IRI vm_iri)
             }]
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
