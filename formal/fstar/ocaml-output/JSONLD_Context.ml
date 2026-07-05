open Prims
type container_kind =
  | CK_None 
  | CK_List 
  | CK_Index 
  | CK_Language 
  | CK_Id 
  | CK_Type 
  | CK_Graph 
  | CK_GraphId 
  | CK_GraphIndex 
let uu___is_CK_None (projectee : container_kind) : Prims.bool=
  match projectee with | CK_None -> true | uu___ -> false
let uu___is_CK_List (projectee : container_kind) : Prims.bool=
  match projectee with | CK_List -> true | uu___ -> false
let uu___is_CK_Index (projectee : container_kind) : Prims.bool=
  match projectee with | CK_Index -> true | uu___ -> false
let uu___is_CK_Language (projectee : container_kind) : Prims.bool=
  match projectee with | CK_Language -> true | uu___ -> false
let uu___is_CK_Id (projectee : container_kind) : Prims.bool=
  match projectee with | CK_Id -> true | uu___ -> false
let uu___is_CK_Type (projectee : container_kind) : Prims.bool=
  match projectee with | CK_Type -> true | uu___ -> false
let uu___is_CK_Graph (projectee : container_kind) : Prims.bool=
  match projectee with | CK_Graph -> true | uu___ -> false
let uu___is_CK_GraphId (projectee : container_kind) : Prims.bool=
  match projectee with | CK_GraphId -> true | uu___ -> false
let uu___is_CK_GraphIndex (projectee : container_kind) : Prims.bool=
  match projectee with | CK_GraphIndex -> true | uu___ -> false
let ck_is_none (k : container_kind) : Prims.bool=
  match k with | CK_None -> true | uu___ -> false
let ck_is_list (k : container_kind) : Prims.bool=
  match k with | CK_List -> true | uu___ -> false
type term_def =
  {
  td_iri: Prims.string ;
  td_type_mapping: Prims.string FStar_Pervasives_Native.option ;
  td_container: container_kind ;
  td_reverse: Prims.bool ;
  td_language:
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option
    ;
  td_direction:
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option
    ;
  td_index: Prims.string FStar_Pervasives_Native.option ;
  td_scoped_context: Parser_JSON.json_val FStar_Pervasives_Native.option ;
  td_protected: Prims.bool ;
  td_prefix: Prims.bool }
let __proj__Mkterm_def__item__td_iri (projectee : term_def) : Prims.string=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_iri
let __proj__Mkterm_def__item__td_type_mapping (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_type_mapping
let __proj__Mkterm_def__item__td_container (projectee : term_def) :
  container_kind=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_container
let __proj__Mkterm_def__item__td_reverse (projectee : term_def) : Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_reverse
let __proj__Mkterm_def__item__td_language (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_language
let __proj__Mkterm_def__item__td_direction (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_direction
let __proj__Mkterm_def__item__td_index (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_index
let __proj__Mkterm_def__item__td_scoped_context (projectee : term_def) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_scoped_context
let __proj__Mkterm_def__item__td_protected (projectee : term_def) :
  Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_protected
let __proj__Mkterm_def__item__td_prefix (projectee : term_def) : Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_direction; td_index; td_scoped_context; td_protected; td_prefix;_}
      -> td_prefix
type active_context =
  {
  ac_terms: (Prims.string * term_def) Prims.list ;
  ac_vocab: Prims.string FStar_Pervasives_Native.option ;
  ac_base: Prims.string FStar_Pervasives_Native.option ;
  ac_language: Prims.string FStar_Pervasives_Native.option ;
  ac_direction: Prims.string FStar_Pervasives_Native.option ;
  ac_previous: active_context FStar_Pervasives_Native.option ;
  ac_mode10: Prims.bool }
let __proj__Mkactive_context__item__ac_terms (projectee : active_context) :
  (Prims.string * term_def) Prims.list=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_terms
let __proj__Mkactive_context__item__ac_vocab (projectee : active_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_vocab
let __proj__Mkactive_context__item__ac_base (projectee : active_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_base
let __proj__Mkactive_context__item__ac_language (projectee : active_context)
  : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_language
let __proj__Mkactive_context__item__ac_direction (projectee : active_context)
  : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_direction
let __proj__Mkactive_context__item__ac_previous (projectee : active_context)
  : active_context FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_previous
let __proj__Mkactive_context__item__ac_mode10 (projectee : active_context) :
  Prims.bool=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_direction; ac_previous;
      ac_mode10;_} -> ac_mode10
let empty_active_context : active_context=
  {
    ac_terms = [];
    ac_vocab = FStar_Pervasives_Native.None;
    ac_base = FStar_Pervasives_Native.None;
    ac_language = FStar_Pervasives_Native.None;
    ac_direction = FStar_Pervasives_Native.None;
    ac_previous = FStar_Pervasives_Native.None;
    ac_mode10 = false
  }
let jldctx_is_keyword (s : Prims.string) : Prims.bool=
  ((Parser_FastString.fs_byte_length s) > Prims.int_zero) &&
    ((Parser_JSON.jbyte_at s Prims.int_zero) = (Prims.of_int (0x40)))
let jldctx_actual_keyword (s : Prims.string) : Prims.bool=
  ((((((((((((((((((((((s = "@base") || (s = "@container")) ||
                        (s = "@context"))
                       || (s = "@direction"))
                      || (s = "@graph"))
                     || (s = "@id"))
                    || (s = "@import"))
                   || (s = "@included"))
                  || (s = "@index"))
                 || (s = "@json"))
                || (s = "@language"))
               || (s = "@list"))
              || (s = "@nest"))
             || (s = "@none"))
            || (s = "@prefix"))
           || (s = "@propagate"))
          || (s = "@protected"))
         || (s = "@reverse"))
        || (s = "@set"))
       || (s = "@type"))
      || (s = "@value"))
     || (s = "@version"))
    || (s = "@vocab")
let jldctx_is_alpha_byte (b : Prims.int) : Prims.bool=
  ((b >= (Prims.of_int (0x41))) && (b <= (Prims.of_int (0x5A)))) ||
    ((b >= (Prims.of_int (0x61))) && (b <= (Prims.of_int (0x7A))))
let rec jldctx_all_alpha_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then true
     else
       if jldctx_is_alpha_byte (Parser_JSON.jbyte_at s pos)
       then
         jldctx_all_alpha_from s (pos + Prims.int_one) (fuel - Prims.int_one)
       else false)
let jldctx_is_scheme_char (b : Prims.int) : Prims.bool=
  ((((jldctx_is_alpha_byte b) ||
       ((b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))))
      || (b = (Prims.of_int (0x2B))))
     || (b = (Prims.of_int (0x2D))))
    || (b = (Prims.of_int (0x2E)))
let rec jldctx_all_scheme_chars_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then true
     else
       if jldctx_is_scheme_char (Parser_JSON.jbyte_at s pos)
       then
         jldctx_all_scheme_chars_from s (pos + Prims.int_one)
           (fuel - Prims.int_one)
       else false)
let jldctx_keyword_form (s : Prims.string) : Prims.bool=
  let n = Parser_FastString.fs_byte_length s in
  ((n >= (Prims.of_int (2))) &&
     ((Parser_JSON.jbyte_at s Prims.int_zero) = (Prims.of_int (0x40))))
    && (jldctx_all_alpha_from s Prims.int_one n)
let jldctx_keyword_lookalike (s : Prims.string) : Prims.bool=
  (jldctx_keyword_form s) && (Prims.op_Negation (jldctx_actual_keyword s))
let rec jldctx_find_term (terms : (Prims.string * term_def) Prims.list)
  (name : Prims.string) : term_def FStar_Pervasives_Native.option=
  match terms with
  | [] -> FStar_Pervasives_Native.None
  | (k, td)::rest ->
      if k = name
      then FStar_Pervasives_Native.Some td
      else jldctx_find_term rest name
let rec jldctx_any_protected (terms : (Prims.string * term_def) Prims.list) :
  Prims.bool=
  match terms with
  | [] -> false
  | (uu___, td)::rest -> td.td_protected || (jldctx_any_protected rest)
let rec jldctx_remove_term (terms : (Prims.string * term_def) Prims.list)
  (name : Prims.string) : (Prims.string * term_def) Prims.list=
  match terms with
  | [] -> []
  | (k, td)::rest ->
      if k = name
      then jldctx_remove_term rest name
      else (k, td) :: (jldctx_remove_term rest name)
let rec jldctx_scan_bool_key
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (keyname : Prims.string) (dflt : Prims.bool) : Prims.bool=
  match fields with
  | [] -> dflt
  | (k, Parser_JSON.JBool b)::rest ->
      if k = keyname
      then jldctx_scan_bool_key rest keyname b
      else jldctx_scan_bool_key rest keyname dflt
  | uu___::rest -> jldctx_scan_bool_key rest keyname dflt
let rec jldctx_scan_propagate (ctx : Parser_JSON.json_val)
  (dflt : Prims.bool) : Prims.bool=
  match ctx with
  | Parser_JSON.JObject fields ->
      jldctx_scan_bool_key fields "@propagate" dflt
  | Parser_JSON.JArray items -> jldctx_scan_propagate_items items dflt
  | uu___ -> dflt
and jldctx_scan_propagate_items (items : Parser_JSON.json_val Prims.list)
  (dflt : Prims.bool) : Prims.bool=
  match items with
  | [] -> dflt
  | hd::tl -> jldctx_scan_propagate_items tl (jldctx_scan_propagate hd dflt)
let term_defs_compatible (a : term_def) (b : term_def) : Prims.bool=
  ((((((((a.td_iri = b.td_iri) && (a.td_type_mapping = b.td_type_mapping)) &&
          (a.td_container = b.td_container))
         && (a.td_reverse = b.td_reverse))
        && (a.td_language = b.td_language))
       && (a.td_direction = b.td_direction))
      && (a.td_index = b.td_index))
     && (a.td_scoped_context = b.td_scoped_context))
    && (a.td_prefix = b.td_prefix)
let rec jldctx_slash_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then false
     else
       if (Parser_JSON.jbyte_at s pos) = (Prims.of_int (0x2F))
       then true
       else jldctx_slash_from s (pos + Prims.int_one) (fuel - Prims.int_one))
let jldctx_key_has_slash (s : Prims.string) : Prims.bool=
  jldctx_slash_from s Prims.int_zero
    ((Parser_FastString.fs_byte_length s) + Prims.int_one)
let jldctx_ends_gen_delim (s : Prims.string) : Prims.bool=
  let n = Parser_FastString.fs_byte_length s in
  (n > Prims.int_zero) &&
    (let b = Parser_JSON.jbyte_at s (n - Prims.int_one) in
     ((((((b = (Prims.of_int (0x3A))) || (b = (Prims.of_int (0x2F)))) ||
           (b = (Prims.of_int (0x3F))))
          || (b = (Prims.of_int (0x23))))
         || (b = (Prims.of_int (0x5B))))
        || (b = (Prims.of_int (0x5D))))
       || (b = (Prims.of_int (0x40))))
let jldctx_resolve_redefine (ac : active_context) (key : Prims.string)
  (new_td : term_def) (override_protected : Prims.bool) :
  term_def FStar_Pervasives_Native.option=
  match jldctx_find_term ac.ac_terms key with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some new_td
  | FStar_Pervasives_Native.Some existing ->
      if existing.td_protected && (Prims.op_Negation override_protected)
      then
        (if term_defs_compatible existing new_td
         then FStar_Pervasives_Native.Some existing
         else FStar_Pervasives_Native.None)
      else FStar_Pervasives_Native.Some new_td
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
let jldctx_colon_not_at_edges (s : Prims.string) : Prims.bool=
  let n = Parser_FastString.fs_byte_length s in
  match jldctx_find_colon s Prims.int_zero (n + Prims.int_one) with
  | FStar_Pervasives_Native.Some c ->
      (c > Prims.int_zero) && (c < (n - Prims.int_one))
  | FStar_Pervasives_Native.None -> false
let jldctx_term_needs_self_check (s : Prims.string) : Prims.bool=
  (jldctx_colon_not_at_edges s) || (jldctx_key_has_slash s)
let jldctx_is_bnode_id (s : Prims.string) : Prims.bool=
  (((Parser_FastString.fs_byte_length s) >= (Prims.of_int (2))) &&
     ((Parser_JSON.jbyte_at s Prims.int_zero) = (Prims.of_int (0x5F))))
    && ((Parser_JSON.jbyte_at s Prims.int_one) = (Prims.of_int (0x3A)))
let jldctx_self_cyclic (ac : active_context) (key : Prims.string)
  (raw : Prims.string) : Prims.bool=
  let n = Parser_FastString.fs_byte_length raw in
  match jldctx_find_colon raw Prims.int_zero (n + Prims.int_one) with
  | FStar_Pervasives_Native.Some c ->
      (c > Prims.int_zero) &&
        (let prefix = Parser_FastString.fs_byte_sub raw Prims.int_zero c in
         ((((prefix <> "_") &&
              (jldctx_all_scheme_chars_from prefix Prims.int_zero c))
             &&
             (Prims.op_Negation
                (((Parser_JSON.jbyte_at raw (c + Prims.int_one)) =
                    (Prims.of_int (0x2F)))
                   &&
                   ((Parser_JSON.jbyte_at raw (c + (Prims.of_int (2)))) =
                      (Prims.of_int (0x2F))))))
            && (prefix = key))
           &&
           (FStar_Pervasives_Native.uu___is_None
              (jldctx_find_term ac.ac_terms key)))
  | FStar_Pervasives_Native.None -> false
let jldctx_resolve (base : Prims.string) (relative : Prims.string) :
  Prims.string=
  if RDF_Graph_Executable.is_iri base
  then SPARQL11_IRI_Resolve.resolve_iri base relative
  else base
let jld_remote_context_fuel : Prims.nat= (Prims.of_int (32))
let jldctx_resolve_context_iri (ac : active_context) (raw : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match ac.ac_base with
  | FStar_Pervasives_Native.Some b ->
      FStar_Pervasives_Native.Some (jldctx_resolve b raw)
  | FStar_Pervasives_Native.None ->
      if RDF_Graph_Executable.is_iri raw
      then FStar_Pervasives_Native.Some raw
      else FStar_Pervasives_Native.None
let jldctx_extract_import
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string FStar_Pervasives_Native.option * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  let importval =
    match FStar_List_Tot_Base.find
            (fun kv -> (FStar_Pervasives_Native.fst kv) = "@import") fields
    with
    | FStar_Pervasives_Native.Some (uu___, Parser_JSON.JString s) ->
        FStar_Pervasives_Native.Some s
    | uu___ -> FStar_Pervasives_Native.None in
  let rest =
    FStar_List_Tot_Base.filter
      (fun kv -> (FStar_Pervasives_Native.fst kv) <> "@import") fields in
  (importval, rest)
let jldctx_fetch_remote_context (resolved : Prims.string) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match JSONLD_Loader.jsonld_load_document resolved with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some raw ->
      (match Parser_JSON.parse_json raw with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some doc ->
           Parser_JSON.json_get_field "@context" doc)
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
         FStar_Pervasives_Native.Some (jldctx_resolve b value)
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let expand_iri_gen (ac : active_context) (value : Prims.string)
  (vocab : Prims.bool) (in_ctx : Prims.bool) :
  Prims.string FStar_Pervasives_Native.option=
  let n = Parser_FastString.fs_byte_length value in
  if n = Prims.int_zero
  then
    (if vocab
     then FStar_Pervasives_Native.None
     else jldctx_expand_fallback ac value false)
  else
    if jldctx_actual_keyword value
    then FStar_Pervasives_Native.Some value
    else
      (let term_hit =
         if vocab
         then jldctx_find_term ac.ac_terms value
         else FStar_Pervasives_Native.None in
       match term_hit with
       | FStar_Pervasives_Native.Some td ->
           FStar_Pervasives_Native.Some (td.td_iri)
       | FStar_Pervasives_Native.None ->
           if jldctx_keyword_form value
           then FStar_Pervasives_Native.Some value
           else
             (match jldctx_find_colon value Prims.int_zero
                      (n + Prims.int_one)
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
                         Prims.op_Negation
                           (jldctx_all_scheme_chars_from prefix
                              Prims.int_zero c)
                       then jldctx_expand_fallback ac value vocab
                       else
                         if
                           ((Parser_JSON.jbyte_at value (c + Prims.int_one))
                              = (Prims.of_int (0x2F)))
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
                                  if
                                    Prims.op_Negation
                                      (in_ctx || ptd.td_prefix)
                                  then FStar_Pervasives_Native.Some value
                                  else
                                    (let suffix =
                                       Parser_FastString.fs_byte_sub value
                                         (c + Prims.int_one)
                                         ((n - c) - Prims.int_one) in
                                     FStar_Pervasives_Native.Some
                                       (FStar_String.concat ""
                                          [ptd.td_iri; suffix]))))))
let expand_iri (ac : active_context) (value : Prims.string)
  (vocab : Prims.bool) : Prims.string FStar_Pervasives_Native.option=
  expand_iri_gen ac value vocab false
let jldctx_expand_iri_ctx (ac : active_context) (value : Prims.string)
  (vocab : Prims.bool) : Prims.string FStar_Pervasives_Native.option=
  expand_iri_gen ac value vocab true
let jldctx_container_kind_of_string (s : Prims.string) :
  container_kind FStar_Pervasives_Native.option=
  if s = "@list"
  then FStar_Pervasives_Native.Some CK_List
  else
    if s = "@set"
    then FStar_Pervasives_Native.Some CK_None
    else
      if s = "@index"
      then FStar_Pervasives_Native.Some CK_Index
      else
        if s = "@language"
        then FStar_Pervasives_Native.Some CK_Language
        else
          if s = "@id"
          then FStar_Pervasives_Native.Some CK_Id
          else
            if s = "@type"
            then FStar_Pervasives_Native.Some CK_Type
            else
              if s = "@graph"
              then FStar_Pervasives_Native.Some CK_Graph
              else FStar_Pervasives_Native.None
let rec jldctx_container_flags (items : Parser_JSON.json_val Prims.list)
  (has_graph : Prims.bool) (has_id : Prims.bool) (has_index : Prims.bool)
  (has_lang : Prims.bool) (has_type : Prims.bool) :
  (Prims.bool * Prims.bool * Prims.bool * Prims.bool * Prims.bool)
    FStar_Pervasives_Native.option=
  match items with
  | [] ->
      FStar_Pervasives_Native.Some
        (has_graph, has_id, has_index, has_lang, has_type)
  | (Parser_JSON.JString s)::rest ->
      if s = "@set"
      then
        jldctx_container_flags rest has_graph has_id has_index has_lang
          has_type
      else
        if s = "@graph"
        then
          jldctx_container_flags rest true has_id has_index has_lang has_type
        else
          if s = "@id"
          then
            jldctx_container_flags rest has_graph true has_index has_lang
              has_type
          else
            if s = "@index"
            then
              jldctx_container_flags rest has_graph has_id true has_lang
                has_type
            else
              if s = "@language"
              then
                jldctx_container_flags rest has_graph has_id has_index true
                  has_type
              else
                if s = "@type"
                then
                  jldctx_container_flags rest has_graph has_id has_index
                    has_lang true
                else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let jldctx_container_kind_of_flags (has_graph : Prims.bool)
  (has_id : Prims.bool) (has_index : Prims.bool) (has_lang : Prims.bool)
  (has_type : Prims.bool) : container_kind FStar_Pervasives_Native.option=
  if has_graph
  then
    (if has_id
     then FStar_Pervasives_Native.Some CK_GraphId
     else
       if has_index
       then FStar_Pervasives_Native.Some CK_GraphIndex
       else FStar_Pervasives_Native.Some CK_Graph)
  else
    if has_id
    then FStar_Pervasives_Native.Some CK_Id
    else
      if has_index
      then FStar_Pervasives_Native.Some CK_Index
      else
        if has_lang
        then FStar_Pervasives_Native.Some CK_Language
        else
          if has_type
          then FStar_Pervasives_Native.Some CK_Type
          else FStar_Pervasives_Native.Some CK_None
let jldctx_container_kind_of_items (items : Parser_JSON.json_val Prims.list)
  : container_kind FStar_Pervasives_Native.option=
  match jldctx_container_flags items false false false false false with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (g, i, ix, lg, ty) ->
      jldctx_container_kind_of_flags g i ix lg ty
let rec jldctx_term_obj_fields (ac : active_context)
  (idf : Prims.string FStar_Pervasives_Native.option)
  (revf : Prims.string FStar_Pervasives_Native.option)
  (typef : Prims.string FStar_Pervasives_Native.option)
  (contk : container_kind)
  (langf :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (dirf :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (idxf : Prims.string FStar_Pervasives_Native.option)
  (ctxf : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (protf : Prims.bool FStar_Pervasives_Native.option)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * container_kind * Prims.string
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option *
    Prims.string FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Parser_JSON.json_val
    FStar_Pervasives_Native.option * Prims.bool
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match fields with
  | [] ->
      FStar_Pervasives_Native.Some
        (idf, revf, typef, contk, langf, dirf, idxf, ctxf, protf)
  | (k, v)::rest ->
      if k = "@id"
      then
        (match v with
         | Parser_JSON.JString s ->
             if jldctx_keyword_lookalike s
             then
               jldctx_term_obj_fields ac idf revf typef contk langf dirf idxf
                 ctxf protf rest
             else
               (match jldctx_expand_iri_ctx ac s true with
                | FStar_Pervasives_Native.Some e ->
                    if e = "@context"
                    then FStar_Pervasives_Native.None
                    else
                      jldctx_term_obj_fields ac
                        (FStar_Pervasives_Native.Some e) revf typef contk
                        langf dirf idxf ctxf protf rest
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
         | uu___ -> FStar_Pervasives_Native.None)
      else
        if k = "@reverse"
        then
          (match v with
           | Parser_JSON.JString s ->
               (match jldctx_expand_iri_ctx ac s true with
                | FStar_Pervasives_Native.Some e ->
                    jldctx_term_obj_fields ac idf
                      (FStar_Pervasives_Native.Some e) typef contk langf dirf
                      idxf ctxf protf rest
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None)
           | uu___1 -> FStar_Pervasives_Native.None)
        else
          if k = "@type"
          then
            (match v with
             | Parser_JSON.JString s ->
                 (match jldctx_expand_iri_ctx ac s true with
                  | FStar_Pervasives_Native.Some e ->
                      if ac.ac_mode10 && ((e = "@json") || (e = "@none"))
                      then FStar_Pervasives_Native.None
                      else
                        if
                          (((e = "@id") || (e = "@json")) || (e = "@none"))
                            || (e = "@vocab")
                        then
                          jldctx_term_obj_fields ac idf revf
                            (FStar_Pervasives_Native.Some e) contk langf dirf
                            idxf ctxf protf rest
                        else
                          if jldctx_is_bnode_id e
                          then FStar_Pervasives_Native.None
                          else
                            jldctx_term_obj_fields ac idf revf
                              (FStar_Pervasives_Native.Some e) contk langf
                              dirf idxf ctxf protf rest
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
             | uu___2 -> FStar_Pervasives_Native.None)
          else
            if k = "@container"
            then
              (match v with
               | Parser_JSON.JString s ->
                   (match jldctx_container_kind_of_string s with
                    | FStar_Pervasives_Native.Some ck ->
                        if
                          ac.ac_mode10 &&
                            (((ck = CK_Graph) || (ck = CK_Id)) ||
                               (ck = CK_Type))
                        then FStar_Pervasives_Native.None
                        else
                          jldctx_term_obj_fields ac idf revf typef ck langf
                            dirf idxf ctxf protf rest
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | Parser_JSON.JArray items ->
                   if ac.ac_mode10
                   then FStar_Pervasives_Native.None
                   else
                     (match jldctx_container_kind_of_items items with
                      | FStar_Pervasives_Native.Some ck ->
                          jldctx_term_obj_fields ac idf revf typef ck langf
                            dirf idxf ctxf protf rest
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None)
               | uu___3 -> FStar_Pervasives_Native.None)
            else
              if k = "@language"
              then
                (match v with
                 | Parser_JSON.JString s ->
                     jldctx_term_obj_fields ac idf revf typef contk
                       (FStar_Pervasives_Native.Some
                          (FStar_Pervasives_Native.Some s)) dirf idxf ctxf
                       protf rest
                 | Parser_JSON.JNull ->
                     jldctx_term_obj_fields ac idf revf typef contk
                       (FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None) dirf idxf ctxf protf
                       rest
                 | uu___4 -> FStar_Pervasives_Native.None)
              else
                if k = "@direction"
                then
                  (match v with
                   | Parser_JSON.JString s ->
                       if (s = "ltr") || (s = "rtl")
                       then
                         jldctx_term_obj_fields ac idf revf typef contk langf
                           (FStar_Pervasives_Native.Some
                              (FStar_Pervasives_Native.Some s)) idxf ctxf
                           protf rest
                       else FStar_Pervasives_Native.None
                   | Parser_JSON.JNull ->
                       jldctx_term_obj_fields ac idf revf typef contk langf
                         (FStar_Pervasives_Native.Some
                            FStar_Pervasives_Native.None) idxf ctxf protf
                         rest
                   | uu___5 -> FStar_Pervasives_Native.None)
                else
                  if k = "@index"
                  then
                    (if ac.ac_mode10
                     then FStar_Pervasives_Native.None
                     else
                       (match v with
                        | Parser_JSON.JString s ->
                            if jldctx_is_keyword s
                            then FStar_Pervasives_Native.None
                            else
                              jldctx_term_obj_fields ac idf revf typef contk
                                langf dirf (FStar_Pervasives_Native.Some s)
                                ctxf protf rest
                        | uu___7 -> FStar_Pervasives_Native.None))
                  else
                    if k = "@context"
                    then
                      (if ac.ac_mode10
                       then FStar_Pervasives_Native.None
                       else
                         jldctx_term_obj_fields ac idf revf typef contk langf
                           dirf idxf (FStar_Pervasives_Native.Some v) protf
                           rest)
                    else
                      if k = "@protected"
                      then
                        (if ac.ac_mode10
                         then FStar_Pervasives_Native.None
                         else
                           (match v with
                            | Parser_JSON.JBool b ->
                                jldctx_term_obj_fields ac idf revf typef
                                  contk langf dirf idxf ctxf
                                  (FStar_Pervasives_Native.Some b) rest
                            | uu___9 -> FStar_Pervasives_Native.None))
                      else
                        if k = "@prefix"
                        then
                          (match v with
                           | Parser_JSON.JBool uu___9 ->
                               jldctx_term_obj_fields ac idf revf typef contk
                                 langf dirf idxf ctxf protf rest
                           | uu___9 -> FStar_Pervasives_Native.None)
                        else FStar_Pervasives_Native.None
let process_term_def_obj (ac : active_context) (key : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (default_protected : Prims.bool) (override_protected : Prims.bool) :
  active_context FStar_Pervasives_Native.option=
  let self_ref =
    (match FStar_List_Tot_Base.find
             (fun kv -> (FStar_Pervasives_Native.fst kv) = "@id") fields
     with
     | FStar_Pervasives_Native.Some (uu___, Parser_JSON.JString s) ->
         jldctx_self_cyclic ac key s
     | uu___ -> false) ||
      (match FStar_List_Tot_Base.find
               (fun kv -> (FStar_Pervasives_Native.fst kv) = "@reverse")
               fields
       with
       | FStar_Pervasives_Native.Some (uu___, Parser_JSON.JString s) ->
           jldctx_self_cyclic ac key s
       | uu___ -> false) in
  if self_ref
  then FStar_Pervasives_Native.None
  else
    (match jldctx_term_obj_fields ac FStar_Pervasives_Native.None
             FStar_Pervasives_Native.None FStar_Pervasives_Native.None
             CK_None FStar_Pervasives_Native.None
             FStar_Pervasives_Native.None FStar_Pervasives_Native.None
             FStar_Pervasives_Native.None FStar_Pervasives_Native.None fields
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some
         (idf, revf, typef, contk, langf, dirf, idxf, ctxf, protf) ->
         if
           (FStar_Pervasives_Native.uu___is_Some idxf) &&
             (Prims.op_Negation
                ((contk = CK_Index) || (contk = CK_GraphIndex)))
         then FStar_Pervasives_Native.None
         else
           if
             (((contk = CK_Type) &&
                 (FStar_Pervasives_Native.uu___is_Some typef))
                && (typef <> (FStar_Pervasives_Native.Some "@id")))
               && (typef <> (FStar_Pervasives_Native.Some "@vocab"))
           then FStar_Pervasives_Native.None
           else
             (let protected =
                match protf with
                | FStar_Pervasives_Native.Some b -> b
                | FStar_Pervasives_Native.None -> default_protected in
              let has_prefix_member =
                FStar_List_Tot_Base.existsb
                  (fun kv -> (FStar_Pervasives_Native.fst kv) = "@prefix")
                  fields in
              let prefix_flag = jldctx_scan_bool_key fields "@prefix" false in
              if
                has_prefix_member &&
                  (FStar_Pervasives_Native.uu___is_Some
                     (jldctx_find_colon key Prims.int_zero
                        ((Parser_FastString.fs_byte_length key) +
                           Prims.int_one)))
              then FStar_Pervasives_Native.None
              else
                if has_prefix_member && (jldctx_key_has_slash key)
                then FStar_Pervasives_Native.None
                else
                  (match (idf, revf) with
                   | (FStar_Pervasives_Native.Some uu___5,
                      FStar_Pervasives_Native.Some uu___6) ->
                       FStar_Pervasives_Native.None
                   | (FStar_Pervasives_Native.Some iri,
                      FStar_Pervasives_Native.None) ->
                       if prefix_flag && (jldctx_is_keyword iri)
                       then FStar_Pervasives_Native.None
                       else
                         if
                           ((Prims.op_Negation ac.ac_mode10) &&
                              (jldctx_term_needs_self_check key))
                             &&
                             ((jldctx_expand_iri_ctx
                                 {
                                   ac_terms =
                                     (jldctx_remove_term ac.ac_terms key);
                                   ac_vocab = (ac.ac_vocab);
                                   ac_base = (ac.ac_base);
                                   ac_language = (ac.ac_language);
                                   ac_direction = (ac.ac_direction);
                                   ac_previous = (ac.ac_previous);
                                   ac_mode10 = (ac.ac_mode10)
                                 } key true)
                                <> (FStar_Pervasives_Native.Some iri))
                         then FStar_Pervasives_Native.None
                         else
                           (let td =
                              {
                                td_iri = iri;
                                td_type_mapping = typef;
                                td_container = contk;
                                td_reverse = false;
                                td_language = langf;
                                td_direction = dirf;
                                td_index = idxf;
                                td_scoped_context = ctxf;
                                td_protected = protected;
                                td_prefix = prefix_flag
                              } in
                            match jldctx_resolve_redefine ac key td
                                    override_protected
                            with
                            | FStar_Pervasives_Native.Some final_td ->
                                FStar_Pervasives_Native.Some
                                  {
                                    ac_terms = ((key, final_td) ::
                                      (ac.ac_terms));
                                    ac_vocab = (ac.ac_vocab);
                                    ac_base = (ac.ac_base);
                                    ac_language = (ac.ac_language);
                                    ac_direction = (ac.ac_direction);
                                    ac_previous = (ac.ac_previous);
                                    ac_mode10 = (ac.ac_mode10)
                                  }
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None)
                   | (FStar_Pervasives_Native.None,
                      FStar_Pervasives_Native.Some iri) ->
                       if
                         Prims.op_Negation
                           ((contk = CK_None) || (contk = CK_Index))
                       then FStar_Pervasives_Native.None
                       else
                         (let td =
                            {
                              td_iri = iri;
                              td_type_mapping = typef;
                              td_container = contk;
                              td_reverse = true;
                              td_language = langf;
                              td_direction = dirf;
                              td_index = idxf;
                              td_scoped_context = ctxf;
                              td_protected = protected;
                              td_prefix = prefix_flag
                            } in
                          match jldctx_resolve_redefine ac key td
                                  override_protected
                          with
                          | FStar_Pervasives_Native.Some final_td ->
                              FStar_Pervasives_Native.Some
                                {
                                  ac_terms = ((key, final_td) ::
                                    (ac.ac_terms));
                                  ac_vocab = (ac.ac_vocab);
                                  ac_base = (ac.ac_base);
                                  ac_language = (ac.ac_language);
                                  ac_direction = (ac.ac_direction);
                                  ac_previous = (ac.ac_previous);
                                  ac_mode10 = (ac.ac_mode10)
                                }
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None)
                   | (FStar_Pervasives_Native.None,
                      FStar_Pervasives_Native.None) ->
                       (match jldctx_expand_iri_ctx
                                {
                                  ac_terms =
                                    (jldctx_remove_term ac.ac_terms key);
                                  ac_vocab = (ac.ac_vocab);
                                  ac_base = (ac.ac_base);
                                  ac_language = (ac.ac_language);
                                  ac_direction = (ac.ac_direction);
                                  ac_previous = (ac.ac_previous);
                                  ac_mode10 = (ac.ac_mode10)
                                } key true
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some iri ->
                            let td =
                              {
                                td_iri = iri;
                                td_type_mapping = typef;
                                td_container = contk;
                                td_reverse = false;
                                td_language = langf;
                                td_direction = dirf;
                                td_index = idxf;
                                td_scoped_context = ctxf;
                                td_protected = protected;
                                td_prefix = prefix_flag
                              } in
                            (match jldctx_resolve_redefine ac key td
                                     override_protected
                             with
                             | FStar_Pervasives_Native.Some final_td ->
                                 FStar_Pervasives_Native.Some
                                   {
                                     ac_terms = ((key, final_td) ::
                                       (ac.ac_terms));
                                     ac_vocab = (ac.ac_vocab);
                                     ac_base = (ac.ac_base);
                                     ac_language = (ac.ac_language);
                                     ac_direction = (ac.ac_direction);
                                     ac_previous = (ac.ac_previous);
                                     ac_mode10 = (ac.ac_mode10)
                                   }
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None)))))
let context_process_one_field (ac : active_context) (key : Prims.string)
  (value : Parser_JSON.json_val) (default_protected : Prims.bool)
  (override_protected : Prims.bool) :
  active_context FStar_Pervasives_Native.option=
  if key = "@base"
  then
    match value with
    | Parser_JSON.JString s ->
        let resolved =
          match ac.ac_base with
          | FStar_Pervasives_Native.Some b -> jldctx_resolve b s
          | FStar_Pervasives_Native.None -> s in
        FStar_Pervasives_Native.Some
          {
            ac_terms = (ac.ac_terms);
            ac_vocab = (ac.ac_vocab);
            ac_base = (FStar_Pervasives_Native.Some resolved);
            ac_language = (ac.ac_language);
            ac_direction = (ac.ac_direction);
            ac_previous = (ac.ac_previous);
            ac_mode10 = (ac.ac_mode10)
          }
    | Parser_JSON.JNull ->
        FStar_Pervasives_Native.Some
          {
            ac_terms = (ac.ac_terms);
            ac_vocab = (ac.ac_vocab);
            ac_base = FStar_Pervasives_Native.None;
            ac_language = (ac.ac_language);
            ac_direction = (ac.ac_direction);
            ac_previous = (ac.ac_previous);
            ac_mode10 = (ac.ac_mode10)
          }
    | uu___ -> FStar_Pervasives_Native.None
  else
    if key = "@vocab"
    then
      (match value with
       | Parser_JSON.JString s ->
           (match jldctx_expand_iri_ctx ac s true with
            | FStar_Pervasives_Native.Some iri ->
                FStar_Pervasives_Native.Some
                  {
                    ac_terms = (ac.ac_terms);
                    ac_vocab = (FStar_Pervasives_Native.Some iri);
                    ac_base = (ac.ac_base);
                    ac_language = (ac.ac_language);
                    ac_direction = (ac.ac_direction);
                    ac_previous = (ac.ac_previous);
                    ac_mode10 = (ac.ac_mode10)
                  }
            | FStar_Pervasives_Native.None ->
                (match ac.ac_base with
                 | FStar_Pervasives_Native.Some b ->
                     FStar_Pervasives_Native.Some
                       {
                         ac_terms = (ac.ac_terms);
                         ac_vocab =
                           (FStar_Pervasives_Native.Some (jldctx_resolve b s));
                         ac_base = (ac.ac_base);
                         ac_language = (ac.ac_language);
                         ac_direction = (ac.ac_direction);
                         ac_previous = (ac.ac_previous);
                         ac_mode10 = (ac.ac_mode10)
                       }
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None))
       | Parser_JSON.JNull ->
           FStar_Pervasives_Native.Some
             {
               ac_terms = (ac.ac_terms);
               ac_vocab = FStar_Pervasives_Native.None;
               ac_base = (ac.ac_base);
               ac_language = (ac.ac_language);
               ac_direction = (ac.ac_direction);
               ac_previous = (ac.ac_previous);
               ac_mode10 = (ac.ac_mode10)
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
                 ac_language = (FStar_Pervasives_Native.Some s);
                 ac_direction = (ac.ac_direction);
                 ac_previous = (ac.ac_previous);
                 ac_mode10 = (ac.ac_mode10)
               }
         | Parser_JSON.JNull ->
             FStar_Pervasives_Native.Some
               {
                 ac_terms = (ac.ac_terms);
                 ac_vocab = (ac.ac_vocab);
                 ac_base = (ac.ac_base);
                 ac_language = FStar_Pervasives_Native.None;
                 ac_direction = (ac.ac_direction);
                 ac_previous = (ac.ac_previous);
                 ac_mode10 = (ac.ac_mode10)
               }
         | uu___2 -> FStar_Pervasives_Native.None)
      else
        if key = "@direction"
        then
          (match value with
           | Parser_JSON.JString s ->
               if (s = "ltr") || (s = "rtl")
               then
                 FStar_Pervasives_Native.Some
                   {
                     ac_terms = (ac.ac_terms);
                     ac_vocab = (ac.ac_vocab);
                     ac_base = (ac.ac_base);
                     ac_language = (ac.ac_language);
                     ac_direction = (FStar_Pervasives_Native.Some s);
                     ac_previous = (ac.ac_previous);
                     ac_mode10 = (ac.ac_mode10)
                   }
               else FStar_Pervasives_Native.None
           | Parser_JSON.JNull ->
               FStar_Pervasives_Native.Some
                 {
                   ac_terms = (ac.ac_terms);
                   ac_vocab = (ac.ac_vocab);
                   ac_base = (ac.ac_base);
                   ac_language = (ac.ac_language);
                   ac_direction = FStar_Pervasives_Native.None;
                   ac_previous = (ac.ac_previous);
                   ac_mode10 = (ac.ac_mode10)
                 }
           | uu___3 -> FStar_Pervasives_Native.None)
        else
          if key = "@version"
          then
            (match value with
             | Parser_JSON.JNumber lex ->
                 if lex <> "1.1"
                 then FStar_Pervasives_Native.None
                 else
                   if ac.ac_mode10
                   then FStar_Pervasives_Native.None
                   else FStar_Pervasives_Native.Some ac
             | uu___4 -> FStar_Pervasives_Native.None)
          else
            if key = "@protected"
            then
              (match value with
               | Parser_JSON.JBool uu___5 -> FStar_Pervasives_Native.Some ac
               | uu___5 -> FStar_Pervasives_Native.None)
            else
              if key = "@propagate"
              then
                (if ac.ac_mode10
                 then FStar_Pervasives_Native.None
                 else
                   (match value with
                    | Parser_JSON.JBool uu___7 ->
                        FStar_Pervasives_Native.Some ac
                    | uu___7 -> FStar_Pervasives_Native.None))
              else
                if key = "@type"
                then
                  (if ac.ac_mode10
                   then FStar_Pervasives_Native.None
                   else
                     (match value with
                      | Parser_JSON.JObject tfields ->
                          let non_empty =
                            match tfields with | [] -> false | uu___8 -> true in
                          let shape_ok =
                            non_empty &&
                              (FStar_List_Tot_Base.for_all
                                 (fun kv ->
                                    (((FStar_Pervasives_Native.fst kv) =
                                        "@container")
                                       &&
                                       (match FStar_Pervasives_Native.snd kv
                                        with
                                        | Parser_JSON.JString "@set" -> true
                                        | uu___8 -> false))
                                      ||
                                      (((FStar_Pervasives_Native.fst kv) =
                                          "@protected")
                                         &&
                                         (Parser_JSON.uu___is_JBool
                                            (FStar_Pervasives_Native.snd kv))))
                                 tfields) in
                          if Prims.op_Negation shape_ok
                          then FStar_Pervasives_Native.None
                          else
                            (let has_set =
                               FStar_List_Tot_Base.existsb
                                 (fun kv ->
                                    (FStar_Pervasives_Native.fst kv) =
                                      "@container") tfields in
                             let protected =
                               jldctx_scan_bool_key tfields "@protected"
                                 false in
                             let td =
                               {
                                 td_iri = "@type";
                                 td_type_mapping =
                                   FStar_Pervasives_Native.None;
                                 td_container =
                                   (if has_set then CK_Type else CK_None);
                                 td_reverse = false;
                                 td_language = FStar_Pervasives_Native.None;
                                 td_direction = FStar_Pervasives_Native.None;
                                 td_index = FStar_Pervasives_Native.None;
                                 td_scoped_context =
                                   FStar_Pervasives_Native.None;
                                 td_protected = protected;
                                 td_prefix = false
                               } in
                             match jldctx_resolve_redefine ac "@type" td
                                     override_protected
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some final_td ->
                                 FStar_Pervasives_Native.Some
                                   {
                                     ac_terms = (("@type", final_td) ::
                                       (ac.ac_terms));
                                     ac_vocab = (ac.ac_vocab);
                                     ac_base = (ac.ac_base);
                                     ac_language = (ac.ac_language);
                                     ac_direction = (ac.ac_direction);
                                     ac_previous = (ac.ac_previous);
                                     ac_mode10 = (ac.ac_mode10)
                                   })
                      | uu___8 -> FStar_Pervasives_Native.None))
                else
                  if jldctx_actual_keyword key
                  then FStar_Pervasives_Native.None
                  else
                    if jldctx_keyword_lookalike key
                    then FStar_Pervasives_Native.Some ac
                    else
                      if key = ""
                      then FStar_Pervasives_Native.None
                      else
                        (match value with
                         | Parser_JSON.JNull ->
                             (match jldctx_find_term ac.ac_terms key with
                              | FStar_Pervasives_Native.Some existing ->
                                  if
                                    existing.td_protected &&
                                      (Prims.op_Negation override_protected)
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let td =
                                       {
                                         td_iri = "@null";
                                         td_type_mapping =
                                           FStar_Pervasives_Native.None;
                                         td_container = CK_None;
                                         td_reverse = false;
                                         td_language =
                                           FStar_Pervasives_Native.None;
                                         td_direction =
                                           FStar_Pervasives_Native.None;
                                         td_index =
                                           FStar_Pervasives_Native.None;
                                         td_scoped_context =
                                           FStar_Pervasives_Native.None;
                                         td_protected = default_protected;
                                         td_prefix = false
                                       } in
                                     FStar_Pervasives_Native.Some
                                       {
                                         ac_terms = ((key, td) ::
                                           (jldctx_remove_term ac.ac_terms
                                              key));
                                         ac_vocab = (ac.ac_vocab);
                                         ac_base = (ac.ac_base);
                                         ac_language = (ac.ac_language);
                                         ac_direction = (ac.ac_direction);
                                         ac_previous = (ac.ac_previous);
                                         ac_mode10 = (ac.ac_mode10)
                                       })
                              | FStar_Pervasives_Native.None ->
                                  let td =
                                    {
                                      td_iri = "@null";
                                      td_type_mapping =
                                        FStar_Pervasives_Native.None;
                                      td_container = CK_None;
                                      td_reverse = false;
                                      td_language =
                                        FStar_Pervasives_Native.None;
                                      td_direction =
                                        FStar_Pervasives_Native.None;
                                      td_index = FStar_Pervasives_Native.None;
                                      td_scoped_context =
                                        FStar_Pervasives_Native.None;
                                      td_protected = default_protected;
                                      td_prefix = false
                                    } in
                                  FStar_Pervasives_Native.Some
                                    {
                                      ac_terms = ((key, td) :: (ac.ac_terms));
                                      ac_vocab = (ac.ac_vocab);
                                      ac_base = (ac.ac_base);
                                      ac_language = (ac.ac_language);
                                      ac_direction = (ac.ac_direction);
                                      ac_previous = (ac.ac_previous);
                                      ac_mode10 = (ac.ac_mode10)
                                    })
                         | Parser_JSON.JString s ->
                             if jldctx_keyword_lookalike s
                             then FStar_Pervasives_Native.Some ac
                             else
                               if jldctx_self_cyclic ac key s
                               then FStar_Pervasives_Native.None
                               else
                                 (let ac_lookup =
                                    if s = key
                                    then
                                      {
                                        ac_terms =
                                          (jldctx_remove_term ac.ac_terms key);
                                        ac_vocab = (ac.ac_vocab);
                                        ac_base = (ac.ac_base);
                                        ac_language = (ac.ac_language);
                                        ac_direction = (ac.ac_direction);
                                        ac_previous = (ac.ac_previous);
                                        ac_mode10 = (ac.ac_mode10)
                                      }
                                    else ac in
                                  match jldctx_expand_iri_ctx ac_lookup s
                                          true
                                  with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some iri ->
                                      if
                                        ((Prims.op_Negation ac.ac_mode10) &&
                                           (jldctx_term_needs_self_check key))
                                          &&
                                          ((jldctx_expand_iri_ctx
                                              {
                                                ac_terms =
                                                  (jldctx_remove_term
                                                     ac.ac_terms key);
                                                ac_vocab = (ac.ac_vocab);
                                                ac_base = (ac.ac_base);
                                                ac_language =
                                                  (ac.ac_language);
                                                ac_direction =
                                                  (ac.ac_direction);
                                                ac_previous =
                                                  (ac.ac_previous);
                                                ac_mode10 = (ac.ac_mode10)
                                              } key true)
                                             <>
                                             (FStar_Pervasives_Native.Some
                                                iri))
                                      then FStar_Pervasives_Native.None
                                      else
                                        (let td =
                                           {
                                             td_iri = iri;
                                             td_type_mapping =
                                               FStar_Pervasives_Native.None;
                                             td_container = CK_None;
                                             td_reverse = false;
                                             td_language =
                                               FStar_Pervasives_Native.None;
                                             td_direction =
                                               FStar_Pervasives_Native.None;
                                             td_index =
                                               FStar_Pervasives_Native.None;
                                             td_scoped_context =
                                               FStar_Pervasives_Native.None;
                                             td_protected = default_protected;
                                             td_prefix =
                                               (jldctx_ends_gen_delim iri)
                                           } in
                                         match jldctx_resolve_redefine ac key
                                                 td override_protected
                                         with
                                         | FStar_Pervasives_Native.Some
                                             final_td ->
                                             FStar_Pervasives_Native.Some
                                               {
                                                 ac_terms = ((key, final_td)
                                                   :: (ac.ac_terms));
                                                 ac_vocab = (ac.ac_vocab);
                                                 ac_base = (ac.ac_base);
                                                 ac_language =
                                                   (ac.ac_language);
                                                 ac_direction =
                                                   (ac.ac_direction);
                                                 ac_previous =
                                                   (ac.ac_previous);
                                                 ac_mode10 = (ac.ac_mode10)
                                               }
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None))
                         | Parser_JSON.JObject termfields ->
                             let rev_kw =
                               FStar_List_Tot_Base.existsb
                                 (fun kv ->
                                    ((FStar_Pervasives_Native.fst kv) =
                                       "@reverse")
                                      &&
                                      (match FStar_Pervasives_Native.snd kv
                                       with
                                       | Parser_JSON.JString rs ->
                                           jldctx_keyword_form rs
                                       | uu___11 -> false)) termfields in
                             let id_null =
                               FStar_List_Tot_Base.existsb
                                 (fun kv ->
                                    ((FStar_Pervasives_Native.fst kv) = "@id")
                                      &&
                                      (Parser_JSON.uu___is_JNull
                                         (FStar_Pervasives_Native.snd kv)))
                                 termfields in
                             if rev_kw
                             then FStar_Pervasives_Native.Some ac
                             else
                               if id_null
                               then
                                 (match jldctx_find_term ac.ac_terms key with
                                  | FStar_Pervasives_Native.Some existing ->
                                      if
                                        existing.td_protected &&
                                          (Prims.op_Negation
                                             override_protected)
                                      then FStar_Pervasives_Native.None
                                      else
                                        (let td =
                                           {
                                             td_iri = "@null";
                                             td_type_mapping =
                                               FStar_Pervasives_Native.None;
                                             td_container = CK_None;
                                             td_reverse = false;
                                             td_language =
                                               FStar_Pervasives_Native.None;
                                             td_direction =
                                               FStar_Pervasives_Native.None;
                                             td_index =
                                               FStar_Pervasives_Native.None;
                                             td_scoped_context =
                                               FStar_Pervasives_Native.None;
                                             td_protected = default_protected;
                                             td_prefix = false
                                           } in
                                         FStar_Pervasives_Native.Some
                                           {
                                             ac_terms = ((key, td) ::
                                               (jldctx_remove_term
                                                  ac.ac_terms key));
                                             ac_vocab = (ac.ac_vocab);
                                             ac_base = (ac.ac_base);
                                             ac_language = (ac.ac_language);
                                             ac_direction = (ac.ac_direction);
                                             ac_previous = (ac.ac_previous);
                                             ac_mode10 = (ac.ac_mode10)
                                           })
                                  | FStar_Pervasives_Native.None ->
                                      let td =
                                        {
                                          td_iri = "@null";
                                          td_type_mapping =
                                            FStar_Pervasives_Native.None;
                                          td_container = CK_None;
                                          td_reverse = false;
                                          td_language =
                                            FStar_Pervasives_Native.None;
                                          td_direction =
                                            FStar_Pervasives_Native.None;
                                          td_index =
                                            FStar_Pervasives_Native.None;
                                          td_scoped_context =
                                            FStar_Pervasives_Native.None;
                                          td_protected = default_protected;
                                          td_prefix = false
                                        } in
                                      FStar_Pervasives_Native.Some
                                        {
                                          ac_terms = ((key, td) ::
                                            (ac.ac_terms));
                                          ac_vocab = (ac.ac_vocab);
                                          ac_base = (ac.ac_base);
                                          ac_language = (ac.ac_language);
                                          ac_direction = (ac.ac_direction);
                                          ac_previous = (ac.ac_previous);
                                          ac_mode10 = (ac.ac_mode10)
                                        })
                               else
                                 process_term_def_obj ac key termfields
                                   default_protected override_protected
                         | uu___11 -> FStar_Pervasives_Native.None)
let jldctx_is_special_context_key (k : Prims.string) : Prims.bool=
  (((((k = "@base") || (k = "@vocab")) || (k = "@language")) ||
      (k = "@direction"))
     || (k = "@propagate"))
    || (k = "@version")
let rec jldctx_partition_special
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  ((Prims.string * Parser_JSON.json_val) Prims.list * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  match fields with
  | [] -> ([], [])
  | (k, v)::rest ->
      let uu___ = jldctx_partition_special rest in
      (match uu___ with
       | (sp, ord) ->
           if jldctx_is_special_context_key k
           then (((k, v) :: sp), ord)
           else (sp, ((k, v) :: ord)))
let rec jldctx_merge_import
  (imported_fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (local_fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match imported_fields with
  | [] -> local_fields
  | (k, v)::rest ->
      if
        FStar_List_Tot_Base.existsb
          (fun kv -> (FStar_Pervasives_Native.fst kv) = k) local_fields
      then jldctx_merge_import rest local_fields
      else (k, v) :: (jldctx_merge_import rest local_fields)
let rec jldctx_preview_prefixes (ac : active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  active_context=
  match fields with
  | [] -> ac
  | (k, Parser_JSON.JString s)::rest ->
      if
        (((((jldctx_actual_keyword k) || (jldctx_keyword_lookalike k)) ||
             (jldctx_keyword_lookalike s))
            || (jldctx_is_keyword k))
           || (k = ""))
          ||
          (FStar_Pervasives_Native.uu___is_Some
             (jldctx_find_term ac.ac_terms k))
      then jldctx_preview_prefixes ac rest
      else
        (match jldctx_expand_iri_ctx ac s true with
         | FStar_Pervasives_Native.None -> jldctx_preview_prefixes ac rest
         | FStar_Pervasives_Native.Some iri ->
             if jldctx_is_keyword iri
             then jldctx_preview_prefixes ac rest
             else
               (let td =
                  {
                    td_iri = iri;
                    td_type_mapping = FStar_Pervasives_Native.None;
                    td_container = CK_None;
                    td_reverse = false;
                    td_language = FStar_Pervasives_Native.None;
                    td_direction = FStar_Pervasives_Native.None;
                    td_index = FStar_Pervasives_Native.None;
                    td_scoped_context = FStar_Pervasives_Native.None;
                    td_protected = false;
                    td_prefix = (jldctx_ends_gen_delim iri)
                  } in
                jldctx_preview_prefixes
                  {
                    ac_terms = ((k, td) :: (ac.ac_terms));
                    ac_vocab = (ac.ac_vocab);
                    ac_base = (ac.ac_base);
                    ac_language = (ac.ac_language);
                    ac_direction = (ac.ac_direction);
                    ac_previous = (ac.ac_previous);
                    ac_mode10 = (ac.ac_mode10)
                  } rest))
  | uu___::rest -> jldctx_preview_prefixes ac rest
let rec context_process (ac : active_context) (ctx : Parser_JSON.json_val)
  (override_protected : Prims.bool) (fuel : Prims.nat)
  (visited : Prims.string Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match ctx with
  | Parser_JSON.JNull ->
      if
        (Prims.op_Negation override_protected) &&
          (jldctx_any_protected ac.ac_terms)
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some
          {
            ac_terms = [];
            ac_vocab = FStar_Pervasives_Native.None;
            ac_base = (ac.ac_base);
            ac_language = FStar_Pervasives_Native.None;
            ac_direction = (ac.ac_direction);
            ac_previous = (ac.ac_previous);
            ac_mode10 = (ac.ac_mode10)
          }
  | Parser_JSON.JString s ->
      if fuel = Prims.int_zero
      then FStar_Pervasives_Native.None
      else
        (match jldctx_resolve_context_iri ac s with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some resolved ->
             if FStar_List_Tot_Base.mem resolved visited
             then FStar_Pervasives_Native.None
             else
               (match jldctx_fetch_remote_context resolved with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some inner ->
                    context_process ac inner override_protected
                      (fuel - Prims.int_one) (resolved :: visited)))
  | Parser_JSON.JArray items ->
      context_process_array ac items override_protected fuel visited
  | Parser_JSON.JObject fields ->
      (match jldctx_extract_import fields with
       | (FStar_Pervasives_Native.None, uu___) ->
           let ac_preview = jldctx_preview_prefixes ac fields in
           context_process_fields ac_preview fields
             (jldctx_scan_bool_key fields "@protected" false)
             override_protected fuel visited
       | (FStar_Pervasives_Native.Some importref, restfields) ->
           if ac.ac_mode10
           then FStar_Pervasives_Native.None
           else
             if fuel = Prims.int_zero
             then FStar_Pervasives_Native.None
             else
               (match jldctx_resolve_context_iri ac importref with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some resolved ->
                    if FStar_List_Tot_Base.mem resolved visited
                    then FStar_Pervasives_Native.None
                    else
                      (match jldctx_fetch_remote_context resolved with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some imported_ctx ->
                           (match imported_ctx with
                            | Parser_JSON.JObject imported_fields ->
                                let merged =
                                  jldctx_merge_import imported_fields
                                    restfields in
                                let ac_preview =
                                  jldctx_preview_prefixes ac merged in
                                let uu___3 = jldctx_partition_special merged in
                                (match uu___3 with
                                 | (special, ordinary) ->
                                     let default_protected =
                                       jldctx_scan_bool_key merged
                                         "@protected" false in
                                     (match context_process_fields ac_preview
                                              special default_protected
                                              override_protected
                                              (fuel - Prims.int_one)
                                              (resolved :: visited)
                                      with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some
                                          ac_special ->
                                          context_process_fields ac_special
                                            ordinary default_protected
                                            override_protected
                                            (fuel - Prims.int_one) (resolved
                                            :: visited)))
                            | uu___3 -> FStar_Pervasives_Native.None))))
  | uu___ -> FStar_Pervasives_Native.None
and context_process_array (ac : active_context)
  (items : Parser_JSON.json_val Prims.list) (override_protected : Prims.bool)
  (fuel : Prims.nat) (visited : Prims.string Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some ac
  | hd::tl ->
      (match context_process ac hd override_protected fuel visited with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ac1 ->
           context_process_array ac1 tl override_protected fuel visited)
and context_process_fields (ac : active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (default_protected : Prims.bool) (override_protected : Prims.bool)
  (fuel : Prims.nat) (visited : Prims.string Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match fields with
  | [] -> FStar_Pervasives_Native.Some ac
  | (key, value)::rest ->
      (match context_process_one_field ac key value default_protected
               override_protected
       with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ac1 ->
           context_process_fields ac1 rest default_protected
             override_protected fuel visited)
let apply_context_with_propagate (ac : active_context)
  (ctxval : Parser_JSON.json_val) (default_propagate : Prims.bool)
  (override_protected : Prims.bool) :
  active_context FStar_Pervasives_Native.option=
  match context_process ac ctxval override_protected jld_remote_context_fuel
          []
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ac1 ->
      let propagate = jldctx_scan_propagate ctxval default_propagate in
      FStar_Pervasives_Native.Some
        (if propagate
         then ac1
         else
           {
             ac_terms = (ac1.ac_terms);
             ac_vocab = (ac1.ac_vocab);
             ac_base = (ac1.ac_base);
             ac_language = (ac1.ac_language);
             ac_direction = (ac1.ac_direction);
             ac_previous = (FStar_Pervasives_Native.Some ac);
             ac_mode10 = (ac1.ac_mode10)
           })
let rec jldctx_insert_sorted (x : Prims.string)
  (xs : Prims.string Prims.list) : Prims.string Prims.list=
  match xs with
  | [] -> [x]
  | y::rest ->
      if RDF_Graph_Executable.string_lt x y
      then x :: xs
      else y :: (jldctx_insert_sorted x rest)
let rec jldctx_sort_strings (xs : Prims.string Prims.list) :
  Prims.string Prims.list=
  match xs with
  | [] -> []
  | x::rest -> jldctx_insert_sorted x (jldctx_sort_strings rest)
let rec jldctx_apply_type_scoped (ac0 : active_context)
  (ac_acc : active_context) (types : Prims.string Prims.list)
  (any_non_propagating : Prims.bool) :
  (active_context * Prims.bool) FStar_Pervasives_Native.option=
  match types with
  | [] -> FStar_Pervasives_Native.Some (ac_acc, any_non_propagating)
  | t::rest ->
      (match jldctx_find_term ac0.ac_terms t with
       | FStar_Pervasives_Native.Some td ->
           (match td.td_scoped_context with
            | FStar_Pervasives_Native.Some scoped ->
                (match context_process ac_acc scoped false
                         jld_remote_context_fuel []
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some ac1 ->
                     let propagate = jldctx_scan_propagate scoped false in
                     jldctx_apply_type_scoped ac0 ac1 rest
                       (any_non_propagating || (Prims.op_Negation propagate)))
            | FStar_Pervasives_Native.None ->
                jldctx_apply_type_scoped ac0 ac_acc rest any_non_propagating)
       | FStar_Pervasives_Native.None ->
           jldctx_apply_type_scoped ac0 ac_acc rest any_non_propagating)
let apply_type_scoped_contexts (ac0 : active_context)
  (raw_types : Prims.string Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match jldctx_apply_type_scoped ac0 ac0 (jldctx_sort_strings raw_types)
          false
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ac1, any_non_propagating) ->
      FStar_Pervasives_Native.Some
        (if any_non_propagating
         then
           {
             ac_terms = (ac1.ac_terms);
             ac_vocab = (ac1.ac_vocab);
             ac_base = (ac1.ac_base);
             ac_language = (ac1.ac_language);
             ac_direction = (ac1.ac_direction);
             ac_previous = (FStar_Pervasives_Native.Some ac0);
             ac_mode10 = (ac1.ac_mode10)
           }
         else ac1)
