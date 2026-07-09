open Prims
let rec vcx_chars_have (cs : FStar_Char.char Prims.list)
  (target : FStar_Char.char) : Prims.bool=
  match cs with
  | [] -> false
  | c::tl -> (c = target) || (vcx_chars_have tl target)
let vcx_has_char (s : Prims.string) (target : FStar_Char.char) : Prims.bool=
  vcx_chars_have (FStar_String.list_of_string s) target
let vcx_is_url (s : Prims.string) : Prims.bool=
  (vcx_has_char s (FStar_Char.char_of_int (Prims.of_int (0x3A)))) &&
    (Prims.op_Negation
       (vcx_has_char s (FStar_Char.char_of_int (Prims.of_int (0x20)))))
let vcx_is_keyword_key (k : Prims.string) : Prims.bool=
  ((FStar_String.strlen k) > Prims.int_zero) &&
    ((FStar_Char.int_of_char (FStar_String.index k Prims.int_zero)) =
       (Prims.of_int (0x40)))
type vcx_term_def =
  {
  vcx_iri: Prims.string FStar_Pervasives_Native.option ;
  vcx_protected: Prims.bool }
let __proj__Mkvcx_term_def__item__vcx_iri (projectee : vcx_term_def) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { vcx_iri; vcx_protected;_} -> vcx_iri
let __proj__Mkvcx_term_def__item__vcx_protected (projectee : vcx_term_def) :
  Prims.bool=
  match projectee with | { vcx_iri; vcx_protected;_} -> vcx_protected
type vcx_vocab =
  | VcxVocabUnset 
  | VcxVocabNull 
  | VcxVocabSet of Prims.string 
let uu___is_VcxVocabUnset (projectee : vcx_vocab) : Prims.bool=
  match projectee with | VcxVocabUnset -> true | uu___ -> false
let uu___is_VcxVocabNull (projectee : vcx_vocab) : Prims.bool=
  match projectee with | VcxVocabNull -> true | uu___ -> false
let uu___is_VcxVocabSet (projectee : vcx_vocab) : Prims.bool=
  match projectee with | VcxVocabSet _0 -> true | uu___ -> false
let __proj__VcxVocabSet__item___0 (projectee : vcx_vocab) : Prims.string=
  match projectee with | VcxVocabSet _0 -> _0
type vcx_state =
  {
  vcx_terms: (Prims.string * vcx_term_def) Prims.list ;
  vcx_vocab: vcx_vocab ;
  vcx_unknown_remote: Prims.bool }
let __proj__Mkvcx_state__item__vcx_terms (projectee : vcx_state) :
  (Prims.string * vcx_term_def) Prims.list=
  match projectee with
  | { vcx_terms; vcx_vocab = vcx_vocab1; vcx_unknown_remote;_} -> vcx_terms
let __proj__Mkvcx_state__item__vcx_vocab (projectee : vcx_state) : vcx_vocab=
  match projectee with
  | { vcx_terms; vcx_vocab = vcx_vocab1; vcx_unknown_remote;_} -> vcx_vocab1
let __proj__Mkvcx_state__item__vcx_unknown_remote (projectee : vcx_state) :
  Prims.bool=
  match projectee with
  | { vcx_terms; vcx_vocab = vcx_vocab1; vcx_unknown_remote;_} ->
      vcx_unknown_remote
type vcx_step =
  | VcxStepOk of vcx_state 
  | VcxStepViolation of Prims.string 
let uu___is_VcxStepOk (projectee : vcx_step) : Prims.bool=
  match projectee with | VcxStepOk _0 -> true | uu___ -> false
let __proj__VcxStepOk__item___0 (projectee : vcx_step) : vcx_state=
  match projectee with | VcxStepOk _0 -> _0
let uu___is_VcxStepViolation (projectee : vcx_step) : Prims.bool=
  match projectee with | VcxStepViolation _0 -> true | uu___ -> false
let __proj__VcxStepViolation__item___0 (projectee : vcx_step) : Prims.string=
  match projectee with | VcxStepViolation _0 -> _0
type vcx_result =
  | VcxOk 
  | VcxViolation of Prims.string 
let uu___is_VcxOk (projectee : vcx_result) : Prims.bool=
  match projectee with | VcxOk -> true | uu___ -> false
let uu___is_VcxViolation (projectee : vcx_result) : Prims.bool=
  match projectee with | VcxViolation _0 -> true | uu___ -> false
let __proj__VcxViolation__item___0 (projectee : vcx_result) : Prims.string=
  match projectee with | VcxViolation _0 -> _0
let rec vcx_field_lookup
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (k : Prims.string) : Parser_JSON.json_val FStar_Pervasives_Native.option=
  match fields with
  | [] -> FStar_Pervasives_Native.None
  | (k', v)::tl ->
      if k' = k
      then FStar_Pervasives_Native.Some v
      else vcx_field_lookup tl k
let vcx_term_iri_of_value (v : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString s -> FStar_Pervasives_Native.Some s
  | Parser_JSON.JObject uu___ ->
      (match Parser_JSON.json_get_field "@id" v with
       | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
           FStar_Pervasives_Native.Some s
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let vcx_obj_protected
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match vcx_field_lookup fields "@protected" with
  | FStar_Pervasives_Native.Some (Parser_JSON.JBool b) -> b
  | uu___ -> false
let rec vcx_terms_of_fields (protected : Prims.bool)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * vcx_term_def) Prims.list=
  match fields with
  | [] -> []
  | (k, valv)::tl ->
      if vcx_is_keyword_key k
      then vcx_terms_of_fields protected tl
      else
        (k,
          { vcx_iri = (vcx_term_iri_of_value valv); vcx_protected = protected
          })
        :: (vcx_terms_of_fields protected tl)
let vcx_base_terms (v2ctx : Parser_JSON.json_val) :
  (Prims.string * vcx_term_def) Prims.list=
  match Parser_JSON.json_get_field "@context" v2ctx with
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
      vcx_terms_of_fields (vcx_obj_protected fields) fields
  | uu___ -> []
let rec vcx_lookup (terms : (Prims.string * vcx_term_def) Prims.list)
  (k : Prims.string) : vcx_term_def FStar_Pervasives_Native.option=
  match terms with
  | [] -> FStar_Pervasives_Native.None
  | (k', d)::tl ->
      if k' = k then FStar_Pervasives_Native.Some d else vcx_lookup tl k
let vcx_set_term (st : vcx_state) (k : Prims.string)
  (iri : Prims.string FStar_Pervasives_Native.option) (prot : Prims.bool) :
  vcx_state=
  {
    vcx_terms = ((k, { vcx_iri = iri; vcx_protected = prot }) ::
      (st.vcx_terms));
    vcx_vocab = (st.vcx_vocab);
    vcx_unknown_remote = (st.vcx_unknown_remote)
  }
let vcx_apply_vocab (cur : vcx_vocab)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : vcx_vocab=
  match vcx_field_lookup fields "@vocab" with
  | FStar_Pervasives_Native.Some (Parser_JSON.JNull) -> VcxVocabNull
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) -> VcxVocabSet s
  | uu___ -> cur
let rec vcx_apply_terms (obj_protected : Prims.bool) (st : vcx_state)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : vcx_step=
  match fields with
  | [] -> VcxStepOk st
  | (k, valv)::tl ->
      if vcx_is_keyword_key k
      then vcx_apply_terms obj_protected st tl
      else
        (let new_iri = vcx_term_iri_of_value valv in
         match vcx_lookup st.vcx_terms k with
         | FStar_Pervasives_Native.Some d ->
             if d.vcx_protected && (d.vcx_iri <> new_iri)
             then
               VcxStepViolation
                 (Prims.strcat "redefinition of protected term '"
                    (Prims.strcat k "'"))
             else
               vcx_apply_terms obj_protected
                 (vcx_set_term st k new_iri
                    (obj_protected || d.vcx_protected)) tl
         | FStar_Pervasives_Native.None ->
             vcx_apply_terms obj_protected
               (vcx_set_term st k new_iri obj_protected) tl)
let vcx_apply_inline (st : vcx_state)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : vcx_step=
  let prot = vcx_obj_protected fields in
  let st1 =
    {
      vcx_terms = (st.vcx_terms);
      vcx_vocab = (vcx_apply_vocab st.vcx_vocab fields);
      vcx_unknown_remote = (st.vcx_unknown_remote)
    } in
  vcx_apply_terms prot st1 fields
let vcx_base_url : Prims.string= "https://www.w3.org/ns/credentials/v2"
let vcx_load_base (st : vcx_state)
  (base : (Prims.string * vcx_term_def) Prims.list) : vcx_state=
  {
    vcx_terms = (FStar_List_Tot_Base.append base st.vcx_terms);
    vcx_vocab = (st.vcx_vocab);
    vcx_unknown_remote = (st.vcx_unknown_remote)
  }
let rec vcx_process_entries (base : (Prims.string * vcx_term_def) Prims.list)
  (st : vcx_state) (entries : Parser_JSON.json_val Prims.list) : vcx_step=
  match entries with
  | [] -> VcxStepOk st
  | e::tl ->
      (match e with
       | Parser_JSON.JString s ->
           if s = vcx_base_url
           then vcx_process_entries base (vcx_load_base st base) tl
           else
             vcx_process_entries base
               {
                 vcx_terms = (st.vcx_terms);
                 vcx_vocab = (st.vcx_vocab);
                 vcx_unknown_remote = true
               } tl
       | Parser_JSON.JObject fields ->
           (match vcx_apply_inline st fields with
            | VcxStepViolation r -> VcxStepViolation r
            | VcxStepOk st' -> vcx_process_entries base st' tl)
       | uu___ -> vcx_process_entries base st tl)
let vcx_build_state (v2ctx : Parser_JSON.json_val)
  (doc : Parser_JSON.json_val) : vcx_step=
  let base = vcx_base_terms v2ctx in
  let st0 =
    { vcx_terms = []; vcx_vocab = VcxVocabUnset; vcx_unknown_remote = false } in
  match Parser_JSON.json_get_field "@context" doc with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray entries) ->
      vcx_process_entries base st0 entries
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      vcx_process_entries base st0 [Parser_JSON.JString s]
  | uu___ -> VcxStepOk st0
let vcx_resolve_type (st : vcx_state) (t : Prims.string) : vcx_result=
  if vcx_is_url t
  then VcxOk
  else
    (match vcx_lookup st.vcx_terms t with
     | FStar_Pervasives_Native.Some d ->
         (match d.vcx_iri with
          | FStar_Pervasives_Native.Some m ->
              if vcx_is_url m
              then VcxOk
              else
                VcxViolation
                  (Prims.strcat "type term '"
                     (Prims.strcat t "' is mapped to a non-URL IRI"))
          | FStar_Pervasives_Native.None -> VcxOk)
     | FStar_Pervasives_Native.None ->
         (match st.vcx_vocab with
          | VcxVocabNull ->
              if st.vcx_unknown_remote
              then VcxOk
              else
                VcxViolation
                  (Prims.strcat "type term '"
                     (Prims.strcat t
                        "' is unmapped (no term definition; @vocab nullified)"))
          | uu___1 -> VcxOk))
let rec vcx_resolve_types (st : vcx_state) (ts : Prims.string Prims.list) :
  vcx_result=
  match ts with
  | [] -> VcxOk
  | t::tl ->
      (match vcx_resolve_type st t with
       | VcxOk -> vcx_resolve_types st tl
       | v -> v)
let vcx_check_types (v2ctx : Parser_JSON.json_val)
  (doc : Parser_JSON.json_val) (type_values : Prims.string Prims.list) :
  vcx_result=
  match vcx_build_state v2ctx doc with
  | VcxStepViolation r -> VcxViolation r
  | VcxStepOk st -> vcx_resolve_types st type_values
