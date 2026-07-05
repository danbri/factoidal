open Prims
let rec vc_chars_contain (cs : FStar_Char.char Prims.list)
  (target : FStar_Char.char) : Prims.bool=
  match cs with
  | [] -> false
  | c::tl -> (c = target) || (vc_chars_contain tl target)
let vc_string_contains_char (s : Prims.string) (target : FStar_Char.char) :
  Prims.bool= vc_chars_contain (FStar_String.list_of_string s) target
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
let vc_object_non_empty (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields ->
      (FStar_List_Tot_Base.length fields) > Prims.int_zero
  | uu___ -> false
let vc_check_credential_subject (v : Parser_JSON.json_val) : vc_verdict=
  match Parser_JSON.json_get_field "credentialSubject" v with
  | FStar_Pervasives_Native.None -> VC_Fail "missing credentialSubject"
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      if (FStar_List_Tot_Base.length fields) > Prims.int_zero
      then VC_Pass
      else VC_Fail "credentialSubject has no claims (empty object)"
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray []) ->
      VC_Fail "credentialSubject array is empty"
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      if FStar_List_Tot_Base.for_all vc_object_non_empty items
      then VC_Pass
      else VC_Fail "credentialSubject array contains an empty-object entry"
  | FStar_Pervasives_Native.Some uu___ ->
      VC_Fail "credentialSubject must be an object or an array of objects"
let vc_check_credential_shaped (v : Parser_JSON.json_val) : vc_verdict=
  match vc_check_context v with
  | VC_Fail r -> VC_Fail r
  | VC_Pass ->
      (match vc_check_type_membership v with
       | VC_Fail r -> VC_Fail r
       | VC_Pass ->
           let types = vc_decode_type_list v in
           if FStar_List_Tot_Base.mem vc_credential_type types
           then vc_check_credential_subject v
           else VC_Pass)
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
