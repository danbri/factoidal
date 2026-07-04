open Prims
type term_def =
  {
  td_iri: Prims.string ;
  td_type_mapping: Prims.string FStar_Pervasives_Native.option ;
  td_container_list: Prims.bool ;
  td_reverse: Prims.bool ;
  td_language:
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option
    }
let __proj__Mkterm_def__item__td_iri (projectee : term_def) : Prims.string=
  match projectee with
  | { td_iri; td_type_mapping; td_container_list; td_reverse; td_language;_}
      -> td_iri
let __proj__Mkterm_def__item__td_type_mapping (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container_list; td_reverse; td_language;_}
      -> td_type_mapping
let __proj__Mkterm_def__item__td_container_list (projectee : term_def) :
  Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container_list; td_reverse; td_language;_}
      -> td_container_list
let __proj__Mkterm_def__item__td_reverse (projectee : term_def) : Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container_list; td_reverse; td_language;_}
      -> td_reverse
let __proj__Mkterm_def__item__td_language (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container_list; td_reverse; td_language;_}
      -> td_language
type active_context =
  {
  ac_terms: (Prims.string * term_def) Prims.list ;
  ac_vocab: Prims.string FStar_Pervasives_Native.option ;
  ac_base: Prims.string FStar_Pervasives_Native.option ;
  ac_language: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkactive_context__item__ac_terms (projectee : active_context) :
  (Prims.string * term_def) Prims.list=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language;_} -> ac_terms
let __proj__Mkactive_context__item__ac_vocab (projectee : active_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language;_} -> ac_vocab
let __proj__Mkactive_context__item__ac_base (projectee : active_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language;_} -> ac_base
let __proj__Mkactive_context__item__ac_language (projectee : active_context)
  : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language;_} -> ac_language
let empty_active_context : active_context=
  {
    ac_terms = [];
    ac_vocab = FStar_Pervasives_Native.None;
    ac_base = FStar_Pervasives_Native.None;
    ac_language = FStar_Pervasives_Native.None
  }
let jldctx_is_keyword (s : Prims.string) : Prims.bool=
  ((Parser_FastString.fs_byte_length s) > Prims.int_zero) &&
    ((Parser_JSON.jbyte_at s Prims.int_zero) = (Prims.of_int (0x40)))
let rec jldctx_find_term (terms : (Prims.string * term_def) Prims.list)
  (name : Prims.string) : term_def FStar_Pervasives_Native.option=
  match terms with
  | [] -> FStar_Pervasives_Native.None
  | (k, td)::rest ->
      if k = name
      then FStar_Pervasives_Native.Some td
      else jldctx_find_term rest name
let rec jldctx_find_colon (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then FStar_Pervasives_Native.None
     else
       if (Parser_JSON.jbyte_at s pos) = (Prims.of_int (0x3A))
       then FStar_Pervasives_Native.Some pos
       else jldctx_find_colon s (pos + Prims.int_one) (fuel - Prims.int_one))
let jldctx_expand_fallback (ac : active_context) (value : Prims.string)
  (vocab : Prims.bool) : Prims.string FStar_Pervasives_Native.option=
  if vocab
  then
    match ac.ac_vocab with
    | FStar_Pervasives_Native.Some v ->
        FStar_Pervasives_Native.Some (FStar_String.concat "" [v; value])
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else
    (match ac.ac_base with
     | FStar_Pervasives_Native.Some b ->
         FStar_Pervasives_Native.Some (FStar_String.concat "" [b; value])
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let expand_iri (ac : active_context) (value : Prims.string)
  (vocab : Prims.bool) : Prims.string FStar_Pervasives_Native.option=
  let n = Parser_FastString.fs_byte_length value in
  if n = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if jldctx_is_keyword value
    then FStar_Pervasives_Native.Some value
    else
      (match jldctx_find_term ac.ac_terms value with
       | FStar_Pervasives_Native.Some td ->
           FStar_Pervasives_Native.Some (td.td_iri)
       | FStar_Pervasives_Native.None ->
           (match jldctx_find_colon value Prims.int_zero (n + Prims.int_one)
            with
            | FStar_Pervasives_Native.None ->
                jldctx_expand_fallback ac value vocab
            | FStar_Pervasives_Native.Some c ->
                if c = Prims.int_zero
                then jldctx_expand_fallback ac value vocab
                else
                  (let prefix =
                     Parser_FastString.fs_byte_sub value Prims.int_zero c in
                   if prefix = "_"
                   then FStar_Pervasives_Native.Some value
                   else
                     if
                       ((Parser_JSON.jbyte_at value (c + Prims.int_one)) =
                          (Prims.of_int (0x2F)))
                         &&
                         ((Parser_JSON.jbyte_at value
                             (c + (Prims.of_int (2))))
                            = (Prims.of_int (0x2F)))
                     then FStar_Pervasives_Native.Some value
                     else
                       (match jldctx_find_term ac.ac_terms prefix with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.Some value
                        | FStar_Pervasives_Native.Some ptd ->
                            if jldctx_is_keyword ptd.td_iri
                            then FStar_Pervasives_Native.None
                            else
                              (let suffix =
                                 Parser_FastString.fs_byte_sub value
                                   (c + Prims.int_one)
                                   ((n - c) - Prims.int_one) in
                               FStar_Pervasives_Native.Some
                                 (FStar_String.concat "" [ptd.td_iri; suffix]))))))
let rec jldctx_container_items_ok (items : Parser_JSON.json_val Prims.list) :
  Prims.bool=
  match items with
  | [] -> true
  | (Parser_JSON.JString s)::rest ->
      ((s = "@list") || (s = "@set")) && (jldctx_container_items_ok rest)
  | uu___ -> false
let rec jldctx_container_has_list (items : Parser_JSON.json_val Prims.list) :
  Prims.bool=
  match items with
  | [] -> false
  | (Parser_JSON.JString s)::rest ->
      (s = "@list") || (jldctx_container_has_list rest)
  | uu___ -> false
let rec jldctx_term_obj_fields (ac : active_context)
  (idf : Prims.string FStar_Pervasives_Native.option)
  (revf : Prims.string FStar_Pervasives_Native.option)
  (typef : Prims.string FStar_Pervasives_Native.option)
  (contlist : Prims.bool)
  (langf :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.bool * Prims.string
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.option=
  match fields with
  | [] -> FStar_Pervasives_Native.Some (idf, revf, typef, contlist, langf)
  | (k, v)::rest ->
      if k = "@id"
      then
        (match v with
         | Parser_JSON.JString s ->
             (match expand_iri ac s true with
              | FStar_Pervasives_Native.Some e ->
                  jldctx_term_obj_fields ac (FStar_Pervasives_Native.Some e)
                    revf typef contlist langf rest
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
      else
        if k = "@reverse"
        then
          (match v with
           | Parser_JSON.JString s ->
               (match expand_iri ac s true with
                | FStar_Pervasives_Native.Some e ->
                    jldctx_term_obj_fields ac idf
                      (FStar_Pervasives_Native.Some e) typef contlist langf
                      rest
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
           | uu___1 -> FStar_Pervasives_Native.None)
        else
          if k = "@type"
          then
            (match v with
             | Parser_JSON.JString s ->
                 (match expand_iri ac s true with
                  | FStar_Pervasives_Native.Some e ->
                      jldctx_term_obj_fields ac idf revf
                        (FStar_Pervasives_Native.Some e) contlist langf rest
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
             | uu___2 -> FStar_Pervasives_Native.None)
          else
            if k = "@container"
            then
              (match v with
               | Parser_JSON.JString s ->
                   if s = "@list"
                   then
                     jldctx_term_obj_fields ac idf revf typef true langf rest
                   else
                     if s = "@set"
                     then
                       jldctx_term_obj_fields ac idf revf typef contlist
                         langf rest
                     else FStar_Pervasives_Native.None
               | Parser_JSON.JArray items ->
                   if jldctx_container_items_ok items
                   then
                     jldctx_term_obj_fields ac idf revf typef
                       (contlist || (jldctx_container_has_list items)) langf
                       rest
                   else FStar_Pervasives_Native.None
               | uu___3 -> FStar_Pervasives_Native.None)
            else
              if k = "@language"
              then
                (match v with
                 | Parser_JSON.JString s ->
                     jldctx_term_obj_fields ac idf revf typef contlist
                       (FStar_Pervasives_Native.Some
                          (FStar_Pervasives_Native.Some s)) rest
                 | Parser_JSON.JNull ->
                     jldctx_term_obj_fields ac idf revf typef contlist
                       (FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None) rest
                 | uu___4 -> FStar_Pervasives_Native.None)
              else FStar_Pervasives_Native.None
let process_term_def_obj (ac : active_context) (key : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match jldctx_term_obj_fields ac FStar_Pervasives_Native.None
          FStar_Pervasives_Native.None FStar_Pervasives_Native.None false
          FStar_Pervasives_Native.None fields
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (idf, revf, typef, contlist, langf) ->
      (match (idf, revf) with
       | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
          uu___1) -> FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.Some iri, FStar_Pervasives_Native.None) ->
           let td =
             {
               td_iri = iri;
               td_type_mapping = typef;
               td_container_list = contlist;
               td_reverse = false;
               td_language = langf
             } in
           FStar_Pervasives_Native.Some
             {
               ac_terms = ((key, td) :: (ac.ac_terms));
               ac_vocab = (ac.ac_vocab);
               ac_base = (ac.ac_base);
               ac_language = (ac.ac_language)
             }
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some iri) ->
           let td =
             {
               td_iri = iri;
               td_type_mapping = typef;
               td_container_list = contlist;
               td_reverse = true;
               td_language = langf
             } in
           FStar_Pervasives_Native.Some
             {
               ac_terms = ((key, td) :: (ac.ac_terms));
               ac_vocab = (ac.ac_vocab);
               ac_base = (ac.ac_base);
               ac_language = (ac.ac_language)
             }
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
           (match expand_iri ac key true with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some iri ->
                let td =
                  {
                    td_iri = iri;
                    td_type_mapping = typef;
                    td_container_list = contlist;
                    td_reverse = false;
                    td_language = langf
                  } in
                FStar_Pervasives_Native.Some
                  {
                    ac_terms = ((key, td) :: (ac.ac_terms));
                    ac_vocab = (ac.ac_vocab);
                    ac_base = (ac.ac_base);
                    ac_language = (ac.ac_language)
                  }))
let context_process_one_field (ac : active_context) (key : Prims.string)
  (value : Parser_JSON.json_val) :
  active_context FStar_Pervasives_Native.option=
  if key = "@base"
  then
    match value with
    | Parser_JSON.JString s ->
        FStar_Pervasives_Native.Some
          {
            ac_terms = (ac.ac_terms);
            ac_vocab = (ac.ac_vocab);
            ac_base = (FStar_Pervasives_Native.Some s);
            ac_language = (ac.ac_language)
          }
    | Parser_JSON.JNull ->
        FStar_Pervasives_Native.Some
          {
            ac_terms = (ac.ac_terms);
            ac_vocab = (ac.ac_vocab);
            ac_base = FStar_Pervasives_Native.None;
            ac_language = (ac.ac_language)
          }
    | uu___ -> FStar_Pervasives_Native.None
  else
    if key = "@vocab"
    then
      (match value with
       | Parser_JSON.JString s ->
           FStar_Pervasives_Native.Some
             {
               ac_terms = (ac.ac_terms);
               ac_vocab = (FStar_Pervasives_Native.Some s);
               ac_base = (ac.ac_base);
               ac_language = (ac.ac_language)
             }
       | Parser_JSON.JNull ->
           FStar_Pervasives_Native.Some
             {
               ac_terms = (ac.ac_terms);
               ac_vocab = FStar_Pervasives_Native.None;
               ac_base = (ac.ac_base);
               ac_language = (ac.ac_language)
             }
       | uu___1 -> FStar_Pervasives_Native.None)
    else
      if key = "@language"
      then
        (match value with
         | Parser_JSON.JString s ->
             FStar_Pervasives_Native.Some
               {
                 ac_terms = (ac.ac_terms);
                 ac_vocab = (ac.ac_vocab);
                 ac_base = (ac.ac_base);
                 ac_language = (FStar_Pervasives_Native.Some s)
               }
         | Parser_JSON.JNull ->
             FStar_Pervasives_Native.Some
               {
                 ac_terms = (ac.ac_terms);
                 ac_vocab = (ac.ac_vocab);
                 ac_base = (ac.ac_base);
                 ac_language = FStar_Pervasives_Native.None
               }
         | uu___2 -> FStar_Pervasives_Native.None)
      else
        if key = "@version"
        then FStar_Pervasives_Native.Some ac
        else
          if jldctx_is_keyword key
          then FStar_Pervasives_Native.None
          else
            (match value with
             | Parser_JSON.JNull -> FStar_Pervasives_Native.Some ac
             | Parser_JSON.JString s ->
                 (match expand_iri ac s true with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some iri ->
                      let td =
                        {
                          td_iri = iri;
                          td_type_mapping = FStar_Pervasives_Native.None;
                          td_container_list = false;
                          td_reverse = false;
                          td_language = FStar_Pervasives_Native.None
                        } in
                      FStar_Pervasives_Native.Some
                        {
                          ac_terms = ((key, td) :: (ac.ac_terms));
                          ac_vocab = (ac.ac_vocab);
                          ac_base = (ac.ac_base);
                          ac_language = (ac.ac_language)
                        })
             | Parser_JSON.JObject termfields ->
                 process_term_def_obj ac key termfields
             | uu___5 -> FStar_Pervasives_Native.None)
let rec context_process (ac : active_context) (ctx : Parser_JSON.json_val) :
  active_context FStar_Pervasives_Native.option=
  match ctx with
  | Parser_JSON.JNull ->
      FStar_Pervasives_Native.Some
        {
          ac_terms = [];
          ac_vocab = FStar_Pervasives_Native.None;
          ac_base = (ac.ac_base);
          ac_language = FStar_Pervasives_Native.None
        }
  | Parser_JSON.JString uu___ -> FStar_Pervasives_Native.None
  | Parser_JSON.JArray items -> context_process_array ac items
  | Parser_JSON.JObject fields -> context_process_fields ac fields
  | uu___ -> FStar_Pervasives_Native.None
and context_process_array (ac : active_context)
  (items : Parser_JSON.json_val Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some ac
  | hd::tl ->
      (match context_process ac hd with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ac1 -> context_process_array ac1 tl)
and context_process_fields (ac : active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match fields with
  | [] -> FStar_Pervasives_Native.Some ac
  | (key, value)::rest ->
      (match context_process_one_field ac key value with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ac1 -> context_process_fields ac1 rest)
