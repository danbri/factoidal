open Prims
let rec vc_chars_contain (cs : FStar_Char.char Prims.list)
  (target : FStar_Char.char) : Prims.bool=
  match cs with
  | [] -> false
  | c::tl -> (c = target) || (vc_chars_contain tl target)
let vc_string_contains_char (s : Prims.string) (target : FStar_Char.char) :
  Prims.bool= vc_chars_contain (FStar_String.list_of_string s) target
let rec vc_chars_contain_digit (cs : FStar_Char.char Prims.list) :
  Prims.bool=
  match cs with
  | [] -> false
  | c::tl ->
      (let n = FStar_Char.int_of_char c in
       (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))) ||
        (vc_chars_contain_digit tl)
let vc_looks_like_date_attempt (s : Prims.string) : Prims.bool=
  vc_chars_contain_digit (FStar_String.list_of_string s)
let vc_looks_like_iri (s : Prims.string) : Prims.bool=
  (vc_string_contains_char s (FStar_Char.char_of_int (Prims.of_int (0x3A))))
    &&
    (Prims.op_Negation
       (vc_string_contains_char s
          (FStar_Char.char_of_int (Prims.of_int (0x20)))))
type vc_verdict =
  | VC_Pass 
  | VC_Fail of Prims.string 
let uu___is_VC_Pass (projectee : vc_verdict) : Prims.bool=
  match projectee with | VC_Pass -> true | uu___ -> false
let uu___is_VC_Fail (projectee : vc_verdict) : Prims.bool=
  match projectee with | VC_Fail _0 -> true | uu___ -> false
let __proj__VC_Fail__item___0 (projectee : vc_verdict) : Prims.string=
  match projectee with | VC_Fail _0 -> _0
let vc_base_context : Prims.string= "https://www.w3.org/ns/credentials/v2"
let vc_context_entry_ok (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JString s -> vc_looks_like_iri s
  | Parser_JSON.JObject uu___ -> true
  | Parser_JSON.JNull -> true
  | uu___ -> false
let vc_check_context (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "@context" v with
  | FStar_Pervasives_Native.None -> VC_Fail "missing @context"
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if s = vc_base_context
      then VC_Pass
      else
        VC_Fail "bare-string @context must equal the base VC 2.0 context IRI"
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      (match items with
       | [] -> VC_Fail "@context is an empty array"
       | first::uu___ ->
           if
             Prims.op_Negation
               (FStar_List_Tot_Base.for_all vc_context_entry_ok items)
           then
             VC_Fail
               "an @context entry is neither a well-formed IRI string, an object, nor null"
           else
             (match first with
              | Parser_JSON.JString s ->
                  if s = vc_base_context
                  then VC_Pass
                  else
                    VC_Fail
                      "the base VC 2.0 context IRI must be the FIRST @context entry"
              | uu___2 ->
                  VC_Fail
                    "the first @context entry must be the base VC 2.0 context IRI string"))
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail "@context must be a string or an array"
let rec vc_string_items (items : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list=
  match items with
  | [] -> []
  | (Parser_JSON.JString s)::tl -> s :: (vc_string_items tl)
  | uu___::tl -> vc_string_items tl
let vc_decode_type_list (v : Parser_JSON.json_val) : Prims.string Prims.list=
  match Parser_JSON.json_get_field "type" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      vc_string_items items
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) -> [s]
  | uu___ -> []
let vc_credential_type : Prims.string= "VerifiableCredential"
let vc_presentation_type : Prims.string= "VerifiablePresentation"
let vc_enveloped_credential_type : Prims.string=
  "EnvelopedVerifiableCredential"
let vc_check_type_membership (v : Parser_JSON.json_val) : vc_verdict=
  let types = vc_decode_type_list v in
  if
    (FStar_List_Tot_Base.mem vc_credential_type types) ||
      (FStar_List_Tot_Base.mem vc_presentation_type types)
  then VC_Pass
  else
    VC_Fail
      "type array/string is missing the base VerifiableCredential/VerifiablePresentation type"
let vc_check_optional_id_field (required : Prims.bool) (label : Prims.string)
  (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "id" v with
  | FStar_Pervasives_Native.None ->
      if required
      then VC_Fail (Prims.strcat label ": missing id")
      else VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if vc_looks_like_iri s
      then VC_Pass
      else VC_Fail (Prims.strcat label ": id is not IRI-shaped")
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail
        (Prims.strcat label
           ": id must be a single IRI string, not an array/null/other")
let vc_check_required_type_field (label : Prims.string)
  (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "type" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___) -> VC_Pass
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail (Prims.strcat label ": type must be a string")
  | FStar_Pervasives_Native.None ->
      VC_Fail (Prims.strcat label ": missing type")
let vc_then (a : vc_verdict) (b : unit -> vc_verdict) : vc_verdict=
  match a with | VC_Fail r -> VC_Fail r | VC_Pass -> b ()
let vc_check_subject_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject fields ->
      if (FStar_List_Tot_Base.length fields) = Prims.int_zero
      then VC_Fail "credentialSubject has no claims (empty object)"
      else vc_check_optional_id_field false "credentialSubject" v
  | uu___ -> VC_Fail "credentialSubject entry must be an object"
let rec vc_check_all (checker : Parser_JSON.json_val -> vc_verdict)
  (items : Parser_JSON.json_val Prims.list) : vc_verdict=
  match items with
  | [] -> VC_Pass
  | hd::tl -> vc_then (checker hd) (fun uu___ -> vc_check_all checker tl)
let vc_check_credential_subject (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "credentialSubject" v with
  | FStar_Pervasives_Native.None -> VC_Fail "missing credentialSubject"
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      vc_check_subject_object (Parser_JSON.JObject fields)
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray []) ->
      VC_Fail "credentialSubject array is empty"
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      vc_check_all vc_check_subject_object items
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail "credentialSubject must be an object or an array of objects"
let vc_lang_map_keys_ok
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun uu___ ->
       match uu___ with
       | (k, uu___1) ->
           ((k = "@value") || (k = "@language")) || (k = "@direction"))
    fields
let vc_lang_map_entry_ok (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields ->
      (vc_lang_map_keys_ok fields) &&
        ((match Parser_JSON.json_get_field "@value" v with
          | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___) -> true
          | uu___ -> false))
  | uu___ -> false
let vc_check_lang_map_field (field_name : Prims.string)
  (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field field_name v with
  | FStar_Pervasives_Native.None -> VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___) -> VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      if vc_lang_map_entry_ok (Parser_JSON.JObject fields)
      then VC_Pass
      else
        VC_Fail
          (Prims.strcat field_name
             " language-map object has a disallowed property or missing @value")
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      if FStar_List_Tot_Base.for_all vc_lang_map_entry_ok items
      then VC_Pass
      else
        VC_Fail
          (Prims.strcat field_name
             " language-map array contains a malformed entry")
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail
        (Prims.strcat field_name
           " must be a string, a language-map object, or an array of language-map objects")
let vc_check_issuer (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "issuer" v with
  | FStar_Pervasives_Native.None -> VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if vc_looks_like_iri s
      then VC_Pass
      else VC_Fail "issuer must be IRI-shaped"
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      let obj = Parser_JSON.JObject fields in
      vc_then (vc_check_optional_id_field false "issuer" obj)
        (fun uu___ ->
           vc_then (vc_check_lang_map_field "name" obj)
             (fun uu___1 -> vc_check_lang_map_field "description" obj))
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail "issuer must be a string or an object"
let vc_check_holder (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "holder" v with
  | FStar_Pervasives_Native.None -> VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if vc_looks_like_iri s
      then VC_Pass
      else VC_Fail "holder must be IRI-shaped"
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      vc_check_optional_id_field true "holder" (Parser_JSON.JObject fields)
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail "holder must be a string or an object"
let vc_check_status_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ ->
      vc_then (vc_check_required_type_field "credentialStatus" v)
        (fun uu___1 -> vc_check_optional_id_field false "credentialStatus" v)
  | uu___ -> VC_Fail "credentialStatus entry must be an object"
let vc_check_schema_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ ->
      vc_then (vc_check_required_type_field "credentialSchema" v)
        (fun uu___1 -> vc_check_optional_id_field true "credentialSchema" v)
  | uu___ -> VC_Fail "credentialSchema entry must be an object"
let vc_check_termsofuse_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ ->
      vc_then (vc_check_required_type_field "termsOfUse" v)
        (fun uu___1 -> vc_check_optional_id_field false "termsOfUse" v)
  | uu___ -> VC_Fail "termsOfUse entry must be an object"
let vc_check_evidence_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ ->
      vc_then (vc_check_required_type_field "evidence" v)
        (fun uu___1 -> vc_check_optional_id_field false "evidence" v)
  | uu___ -> VC_Fail "evidence entry must be an object"
let vc_check_refresh_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ ->
      vc_then (vc_check_required_type_field "refreshService" v)
        (fun uu___1 -> vc_check_optional_id_field false "refreshService" v)
  | uu___ -> VC_Fail "refreshService entry must be an object"
let vc_check_proof_object (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ -> vc_check_required_type_field "proof" v
  | uu___ -> VC_Fail "proof entry must be an object"
let vc_check_object_or_array_field
  (checker : Parser_JSON.json_val -> vc_verdict) (field_name : Prims.string)
  (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field field_name v with
  | FStar_Pervasives_Native.None -> VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      checker (Parser_JSON.JObject fields)
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      vc_check_all checker items
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail
        (Prims.strcat field_name " must be an object or an array of objects")
let vc_check_credential_status (v : Parser_JSON.json_val) : vc_verdict=
  vc_check_object_or_array_field vc_check_status_object "credentialStatus" v
let vc_check_credential_schema (v : Parser_JSON.json_val) : vc_verdict=
  vc_check_object_or_array_field vc_check_schema_object "credentialSchema" v
let vc_check_terms_of_use (v : Parser_JSON.json_val) : vc_verdict=
  vc_check_object_or_array_field vc_check_termsofuse_object "termsOfUse" v
let vc_check_evidence (v : Parser_JSON.json_val) : vc_verdict=
  vc_check_object_or_array_field vc_check_evidence_object "evidence" v
let vc_check_refresh_service (v : Parser_JSON.json_val) : vc_verdict=
  vc_check_object_or_array_field vc_check_refresh_object "refreshService" v
let vc_check_proof (v : Parser_JSON.json_val) : vc_verdict=
  vc_check_object_or_array_field vc_check_proof_object "proof" v
let vc_check_temporal_lexical (field_name : Prims.string)
  (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field field_name v with
  | FStar_Pervasives_Native.None -> VC_Pass
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if vc_looks_like_date_attempt s
      then
        (match XSD_Datatypes.dt_parse_ms s with
         | FStar_Pervasives_Native.Some uu___ -> VC_Pass
         | FStar_Pervasives_Native.None ->
             VC_Fail
               (Prims.strcat field_name
                  " is not a well-formed xsd:dateTime lexical form"))
      else VC_Pass
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail (Prims.strcat field_name " must be a string")
let vc_check_temporal_ordering (v : Parser_JSON.json_val) : vc_verdict=
  match ((Parser_JSON.json_get_field "validFrom" v),
          (Parser_JSON.json_get_field "validUntil" v))
  with
  | (FStar_Pervasives_Native.Some (Parser_JSON.JString sf),
     FStar_Pervasives_Native.Some (Parser_JSON.JString su)) ->
      if (vc_looks_like_date_attempt sf) && (vc_looks_like_date_attempt su)
      then
        (match XSD_Datatypes.dt_cmp sf su with
         | FStar_Pervasives_Native.Some c ->
             if c <= Prims.int_zero
             then VC_Pass
             else VC_Fail "validFrom must not be after validUntil"
         | FStar_Pervasives_Native.None -> VC_Pass)
      else VC_Pass
  | (uu___, uu___1) -> VC_Pass
let vc_check_validity_period (v : Parser_JSON.json_val) : vc_verdict=
  vc_then (vc_check_temporal_lexical "validFrom" v)
    (fun uu___ ->
       vc_then (vc_check_temporal_lexical "validUntil" v)
         (fun uu___1 -> vc_check_temporal_ordering v))
let vc_check_credential_shaped (v : Parser_JSON.json_val) : vc_verdict=
  vc_then (vc_check_context v)
    (fun uu___ ->
       vc_then (vc_check_type_membership v)
         (fun uu___1 ->
            vc_then (vc_check_optional_id_field false "document" v)
              (fun uu___2 ->
                 vc_then (vc_check_issuer v)
                   (fun uu___3 ->
                      vc_then (vc_check_holder v)
                        (fun uu___4 ->
                           vc_then (vc_check_lang_map_field "name" v)
                             (fun uu___5 ->
                                vc_then
                                  (vc_check_lang_map_field "description" v)
                                  (fun uu___6 ->
                                     vc_then (vc_check_credential_status v)
                                       (fun uu___7 ->
                                          vc_then
                                            (vc_check_credential_schema v)
                                            (fun uu___8 ->
                                               vc_then
                                                 (vc_check_terms_of_use v)
                                                 (fun uu___9 ->
                                                    vc_then
                                                      (vc_check_evidence v)
                                                      (fun uu___10 ->
                                                         vc_then
                                                           (vc_check_refresh_service
                                                              v)
                                                           (fun uu___11 ->
                                                              vc_then
                                                                (vc_check_proof
                                                                   v)
                                                                (fun uu___12
                                                                   ->
                                                                   vc_then
                                                                    (vc_check_validity_period
                                                                    v)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let types
                                                                    =
                                                                    vc_decode_type_list
                                                                    v in
                                                                    if
                                                                    FStar_List_Tot_Base.mem
                                                                    vc_credential_type
                                                                    types
                                                                    then
                                                                    vc_check_credential_subject
                                                                    v
                                                                    else
                                                                    VC_Pass))))))))))))))
let vc_check_embedded_item (v : Parser_JSON.json_val) : vc_verdict=
  match v with
  | Parser_JSON.JObject uu___ ->
      let types = vc_decode_type_list v in
      if FStar_List_Tot_Base.mem vc_enveloped_credential_type types
      then
        (match Parser_JSON.json_get_string "id" v with
         | FStar_Pervasives_Native.Some uu___1 -> VC_Pass
         | FStar_Pervasives_Native.None ->
             VC_Fail "enveloped verifiableCredential entry is missing id")
      else
        if FStar_List_Tot_Base.mem vc_credential_type types
        then vc_check_credential_shaped v
        else
          VC_Fail
            "verifiableCredential entry has neither VerifiableCredential nor EnvelopedVerifiableCredential type"
  | uu___ -> VC_Fail "verifiableCredential entry must be a JSON object"
let rec vc_check_embedded_list (items : Parser_JSON.json_val Prims.list) :
  vc_verdict=
  match items with
  | [] -> VC_Pass
  | hd::tl ->
      (match vc_check_embedded_item hd with
       | VC_Fail r -> VC_Fail r
       | VC_Pass -> vc_check_embedded_list tl)
let vc_check_embedded_credentials (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "verifiableCredential" v with
  | FStar_Pervasives_Native.None -> VC_Pass
  | FStar_Pervasives_Native.Some field_val ->
      (match field_val with
       | Parser_JSON.JArray items -> vc_check_embedded_list items
       | Parser_JSON.JObject uu___ -> vc_check_embedded_item field_val
       | uu___ ->
           VC_Fail
             "verifiableCredential must be an object or an array of objects")
let vc_check_document (v : Parser_JSON.json_val) : vc_verdict=
  match vc_check_credential_shaped v with
  | VC_Fail r -> VC_Fail r
  | VC_Pass ->
      let types = vc_decode_type_list v in
      if FStar_List_Tot_Base.mem vc_presentation_type types
      then vc_check_embedded_credentials v
      else VC_Pass
let vc_check_from_string (input : Prims.string) : vc_verdict=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> VC_Fail "input is not well-formed JSON"
  | FStar_Pervasives_Native.Some v ->
      (match v with
       | Parser_JSON.JObject uu___ -> vc_check_document v
       | uu___ -> VC_Fail "top-level JSON value must be an object")
