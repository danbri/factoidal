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
  td_scoped_context: Parser_JSON.json_val FStar_Pervasives_Native.option ;
  td_protected: Prims.bool }
let __proj__Mkterm_def__item__td_iri (projectee : term_def) : Prims.string=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_iri
let __proj__Mkterm_def__item__td_type_mapping (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_type_mapping
let __proj__Mkterm_def__item__td_container (projectee : term_def) :
  container_kind=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_container
let __proj__Mkterm_def__item__td_reverse (projectee : term_def) : Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_reverse
let __proj__Mkterm_def__item__td_language (projectee : term_def) :
  Prims.string FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_language
let __proj__Mkterm_def__item__td_scoped_context (projectee : term_def) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_scoped_context
let __proj__Mkterm_def__item__td_protected (projectee : term_def) :
  Prims.bool=
  match projectee with
  | { td_iri; td_type_mapping; td_container; td_reverse; td_language;
      td_scoped_context; td_protected;_} -> td_protected
type active_context =
  {
  ac_terms: (Prims.string * term_def) Prims.list ;
  ac_vocab: Prims.string FStar_Pervasives_Native.option ;
  ac_base: Prims.string FStar_Pervasives_Native.option ;
  ac_language: Prims.string FStar_Pervasives_Native.option ;
  ac_previous: active_context FStar_Pervasives_Native.option }
let __proj__Mkactive_context__item__ac_terms (projectee : active_context) :
  (Prims.string * term_def) Prims.list=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_previous;_} -> ac_terms
let __proj__Mkactive_context__item__ac_vocab (projectee : active_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_previous;_} -> ac_vocab
let __proj__Mkactive_context__item__ac_base (projectee : active_context) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_previous;_} -> ac_base
let __proj__Mkactive_context__item__ac_language (projectee : active_context)
  : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_previous;_} -> ac_language
let __proj__Mkactive_context__item__ac_previous (projectee : active_context)
  : active_context FStar_Pervasives_Native.option=
  match projectee with
  | { ac_terms; ac_vocab; ac_base; ac_language; ac_previous;_} -> ac_previous
let empty_active_context : active_context=
  {
    ac_terms = [];
    ac_vocab = FStar_Pervasives_Native.None;
    ac_base = FStar_Pervasives_Native.None;
    ac_language = FStar_Pervasives_Native.None;
    ac_previous = FStar_Pervasives_Native.None
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
  (((((a.td_iri = b.td_iri) && (a.td_type_mapping = b.td_type_mapping)) &&
       (a.td_container = b.td_container))
      && (a.td_reverse = b.td_reverse))
     && (a.td_language = b.td_language))
    && (a.td_scoped_context = b.td_scoped_context)
let jldctx_check_redefine (ac : active_context) (key : Prims.string)
  (new_td : term_def) (override_protected : Prims.bool) : Prims.bool=
  match jldctx_find_term ac.ac_terms key with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some existing ->
      if existing.td_protected && (Prims.op_Negation override_protected)
      then term_defs_compatible existing new_td
      else true
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
let jldctx_resolve (base : Prims.string) (relative : Prims.string) :
  Prims.string=
  if RDF_Graph_Executable.is_iri base
  then SPARQL11_IRI_Resolve.resolve_iri base relative
  else base
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
  (ctxf : Parser_JSON.json_val FStar_Pervasives_Native.option)
  (protf : Prims.bool FStar_Pervasives_Native.option)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * container_kind * Prims.string
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option *
    Parser_JSON.json_val FStar_Pervasives_Native.option * Prims.bool
    FStar_Pervasives_Native.option) FStar_Pervasives_Native.option=
  match fields with
  | [] ->
      FStar_Pervasives_Native.Some
        (idf, revf, typef, contk, langf, ctxf, protf)
  | (k, v)::rest ->
      if k = "@id"
      then
        (match v with
         | Parser_JSON.JString s ->
             (match expand_iri ac s true with
              | FStar_Pervasives_Native.Some e ->
                  jldctx_term_obj_fields ac (FStar_Pervasives_Native.Some e)
                    revf typef contk langf ctxf protf rest
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
                      (FStar_Pervasives_Native.Some e) typef contk langf ctxf
                      protf rest
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
                        (FStar_Pervasives_Native.Some e) contk langf ctxf
                        protf rest
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
                        jldctx_term_obj_fields ac idf revf typef ck langf
                          ctxf protf rest
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None)
               | Parser_JSON.JArray items ->
                   (match jldctx_container_kind_of_items items with
                    | FStar_Pervasives_Native.Some ck ->
                        jldctx_term_obj_fields ac idf revf typef ck langf
                          ctxf protf rest
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
                          (FStar_Pervasives_Native.Some s)) ctxf protf rest
                 | Parser_JSON.JNull ->
                     jldctx_term_obj_fields ac idf revf typef contk
                       (FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None) ctxf protf rest
                 | uu___4 -> FStar_Pervasives_Native.None)
              else
                if k = "@context"
                then
                  jldctx_term_obj_fields ac idf revf typef contk langf
                    (FStar_Pervasives_Native.Some v) protf rest
                else
                  if k = "@protected"
                  then
                    (match v with
                     | Parser_JSON.JBool b ->
                         jldctx_term_obj_fields ac idf revf typef contk langf
                           ctxf (FStar_Pervasives_Native.Some b) rest
                     | uu___6 -> FStar_Pervasives_Native.None)
                  else FStar_Pervasives_Native.None
let process_term_def_obj (ac : active_context) (key : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (default_protected : Prims.bool) (override_protected : Prims.bool) :
  active_context FStar_Pervasives_Native.option=
  match jldctx_term_obj_fields ac FStar_Pervasives_Native.None
          FStar_Pervasives_Native.None FStar_Pervasives_Native.None CK_None
          FStar_Pervasives_Native.None FStar_Pervasives_Native.None
          FStar_Pervasives_Native.None fields
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some
      (idf, revf, typef, contk, langf, ctxf, protf) ->
      let protected =
        match protf with
        | FStar_Pervasives_Native.Some b -> b
        | FStar_Pervasives_Native.None -> default_protected in
      (match (idf, revf) with
       | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
          uu___1) -> FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.Some iri, FStar_Pervasives_Native.None) ->
           let td =
             {
               td_iri = iri;
               td_type_mapping = typef;
               td_container = contk;
               td_reverse = false;
               td_language = langf;
               td_scoped_context = ctxf;
               td_protected = protected
             } in
           if jldctx_check_redefine ac key td override_protected
           then
             FStar_Pervasives_Native.Some
               {
                 ac_terms = ((key, td) :: (ac.ac_terms));
                 ac_vocab = (ac.ac_vocab);
                 ac_base = (ac.ac_base);
                 ac_language = (ac.ac_language);
                 ac_previous = (ac.ac_previous)
               }
           else FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some iri) ->
           let td =
             {
               td_iri = iri;
               td_type_mapping = typef;
               td_container = contk;
               td_reverse = true;
               td_language = langf;
               td_scoped_context = ctxf;
               td_protected = protected
             } in
           if jldctx_check_redefine ac key td override_protected
           then
             FStar_Pervasives_Native.Some
               {
                 ac_terms = ((key, td) :: (ac.ac_terms));
                 ac_vocab = (ac.ac_vocab);
                 ac_base = (ac.ac_base);
                 ac_language = (ac.ac_language);
                 ac_previous = (ac.ac_previous)
               }
           else FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
           (match expand_iri ac key true with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some iri ->
                let td =
                  {
                    td_iri = iri;
                    td_type_mapping = typef;
                    td_container = contk;
                    td_reverse = false;
                    td_language = langf;
                    td_scoped_context = ctxf;
                    td_protected = protected
                  } in
                if jldctx_check_redefine ac key td override_protected
                then
                  FStar_Pervasives_Native.Some
                    {
                      ac_terms = ((key, td) :: (ac.ac_terms));
                      ac_vocab = (ac.ac_vocab);
                      ac_base = (ac.ac_base);
                      ac_language = (ac.ac_language);
                      ac_previous = (ac.ac_previous)
                    }
                else FStar_Pervasives_Native.None))
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
            ac_previous = (ac.ac_previous)
          }
    | Parser_JSON.JNull ->
        FStar_Pervasives_Native.Some
          {
            ac_terms = (ac.ac_terms);
            ac_vocab = (ac.ac_vocab);
            ac_base = FStar_Pervasives_Native.None;
            ac_language = (ac.ac_language);
            ac_previous = (ac.ac_previous)
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
               ac_language = (ac.ac_language);
               ac_previous = (ac.ac_previous)
             }
       | Parser_JSON.JNull ->
           FStar_Pervasives_Native.Some
             {
               ac_terms = (ac.ac_terms);
               ac_vocab = FStar_Pervasives_Native.None;
               ac_base = (ac.ac_base);
               ac_language = (ac.ac_language);
               ac_previous = (ac.ac_previous)
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
                 ac_previous = (ac.ac_previous)
               }
         | Parser_JSON.JNull ->
             FStar_Pervasives_Native.Some
               {
                 ac_terms = (ac.ac_terms);
                 ac_vocab = (ac.ac_vocab);
                 ac_base = (ac.ac_base);
                 ac_language = FStar_Pervasives_Native.None;
                 ac_previous = (ac.ac_previous)
               }
         | uu___2 -> FStar_Pervasives_Native.None)
      else
        if key = "@version"
        then FStar_Pervasives_Native.Some ac
        else
          if key = "@protected"
          then
            (match value with
             | Parser_JSON.JBool uu___4 -> FStar_Pervasives_Native.Some ac
             | uu___4 -> FStar_Pervasives_Native.None)
          else
            if key = "@propagate"
            then
              (match value with
               | Parser_JSON.JBool uu___5 -> FStar_Pervasives_Native.Some ac
               | uu___5 -> FStar_Pervasives_Native.None)
            else
              if jldctx_is_keyword key
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
                            FStar_Pervasives_Native.Some
                              {
                                ac_terms =
                                  (jldctx_remove_term ac.ac_terms key);
                                ac_vocab = (ac.ac_vocab);
                                ac_base = (ac.ac_base);
                                ac_language = (ac.ac_language);
                                ac_previous = (ac.ac_previous)
                              }
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some ac)
                 | Parser_JSON.JString s ->
                     (match expand_iri ac s true with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some iri ->
                          let td =
                            {
                              td_iri = iri;
                              td_type_mapping = FStar_Pervasives_Native.None;
                              td_container = CK_None;
                              td_reverse = false;
                              td_language = FStar_Pervasives_Native.None;
                              td_scoped_context =
                                FStar_Pervasives_Native.None;
                              td_protected = default_protected
                            } in
                          if
                            jldctx_check_redefine ac key td
                              override_protected
                          then
                            FStar_Pervasives_Native.Some
                              {
                                ac_terms = ((key, td) :: (ac.ac_terms));
                                ac_vocab = (ac.ac_vocab);
                                ac_base = (ac.ac_base);
                                ac_language = (ac.ac_language);
                                ac_previous = (ac.ac_previous)
                              }
                          else FStar_Pervasives_Native.None)
                 | Parser_JSON.JObject termfields ->
                     process_term_def_obj ac key termfields default_protected
                       override_protected
                 | uu___7 -> FStar_Pervasives_Native.None)
let rec context_process (ac : active_context) (ctx : Parser_JSON.json_val)
  (override_protected : Prims.bool) :
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
            ac_previous = (ac.ac_previous)
          }
  | Parser_JSON.JString uu___ -> FStar_Pervasives_Native.None
  | Parser_JSON.JArray items ->
      context_process_array ac items override_protected
  | Parser_JSON.JObject fields ->
      context_process_fields ac fields
        (jldctx_scan_bool_key fields "@protected" false) override_protected
  | uu___ -> FStar_Pervasives_Native.None
and context_process_array (ac : active_context)
  (items : Parser_JSON.json_val Prims.list) (override_protected : Prims.bool)
  : active_context FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some ac
  | hd::tl ->
      (match context_process ac hd override_protected with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some ac1 ->
           context_process_array ac1 tl override_protected)
and context_process_fields (ac : active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (default_protected : Prims.bool) (override_protected : Prims.bool) :
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
             override_protected)
let apply_context_with_propagate (ac : active_context)
  (ctxval : Parser_JSON.json_val) (default_propagate : Prims.bool)
  (override_protected : Prims.bool) :
  active_context FStar_Pervasives_Native.option=
  match context_process ac ctxval override_protected with
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
             ac_previous = (FStar_Pervasives_Native.Some ac)
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
let rec jldctx_apply_type_scoped (ac : active_context)
  (types : Prims.string Prims.list) (any_non_propagating : Prims.bool) :
  (active_context * Prims.bool) FStar_Pervasives_Native.option=
  match types with
  | [] -> FStar_Pervasives_Native.Some (ac, any_non_propagating)
  | t::rest ->
      (match jldctx_find_term ac.ac_terms t with
       | FStar_Pervasives_Native.Some td ->
           (match td.td_scoped_context with
            | FStar_Pervasives_Native.Some scoped ->
                (match context_process ac scoped true with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some ac1 ->
                     let propagate = jldctx_scan_propagate scoped false in
                     jldctx_apply_type_scoped ac1 rest
                       (any_non_propagating || (Prims.op_Negation propagate)))
            | FStar_Pervasives_Native.None ->
                jldctx_apply_type_scoped ac rest any_non_propagating)
       | FStar_Pervasives_Native.None ->
           jldctx_apply_type_scoped ac rest any_non_propagating)
let apply_type_scoped_contexts (ac0 : active_context)
  (raw_types : Prims.string Prims.list) :
  active_context FStar_Pervasives_Native.option=
  match jldctx_apply_type_scoped ac0 (jldctx_sort_strings raw_types) false
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
             ac_previous = (FStar_Pervasives_Native.Some ac0)
           }
         else ac1)
