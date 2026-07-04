open Prims
let jexp_as_array (v : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match v with | Parser_JSON.JArray items -> items | uu___ -> [v]
let jexp_has_field (name : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun kv -> (FStar_Pervasives_Native.fst kv) = name) fields
let jexp_wrap_scalar (type_map : Prims.string FStar_Pervasives_Native.option)
  (v : Parser_JSON.json_val) : Parser_JSON.json_val=
  match type_map with
  | FStar_Pervasives_Native.Some dt ->
      if (dt = "@id") || (dt = "@vocab")
      then Parser_JSON.JObject [("@value", v)]
      else
        Parser_JSON.JObject
          [("@value", v); ("@type", (Parser_JSON.JString dt))]
  | FStar_Pervasives_Native.None -> Parser_JSON.JObject [("@value", v)]
let jexp_expand_value_object (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun kv -> (FStar_Pervasives_Native.fst kv) = "@value") fields
  with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (uu___, v) ->
      if
        FStar_List_Tot_Base.existsb
          (fun kv -> (FStar_Pervasives_Native.fst kv) = "@direction") fields
      then FStar_Pervasives_Native.None
      else
        (let lang =
           match FStar_List_Tot_Base.find
                   (fun kv -> (FStar_Pervasives_Native.fst kv) = "@language")
                   fields
           with
           | FStar_Pervasives_Native.Some (uu___2, Parser_JSON.JString s) ->
               FStar_Pervasives_Native.Some s
           | uu___2 -> FStar_Pervasives_Native.None in
         let typ =
           match FStar_List_Tot_Base.find
                   (fun kv -> (FStar_Pervasives_Native.fst kv) = "@type")
                   fields
           with
           | FStar_Pervasives_Native.Some (uu___2, Parser_JSON.JString s) ->
               FStar_Pervasives_Native.Some s
           | uu___2 -> FStar_Pervasives_Native.None in
         match (lang, typ) with
         | (FStar_Pervasives_Native.Some uu___2, FStar_Pervasives_Native.Some
            uu___3) -> FStar_Pervasives_Native.None
         | (FStar_Pervasives_Native.Some lg, FStar_Pervasives_Native.None) ->
             FStar_Pervasives_Native.Some
               (Parser_JSON.JObject
                  [("@value", v); ("@language", (Parser_JSON.JString lg))])
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some t) ->
             (match JSONLD_Context.expand_iri ac t true with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some iri ->
                  FStar_Pervasives_Native.Some
                    (Parser_JSON.JObject
                       [("@value", v); ("@type", (Parser_JSON.JString iri))]))
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
             FStar_Pervasives_Native.Some
               (Parser_JSON.JObject [("@value", v)]))
let jexp_extract_context
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Parser_JSON.json_val FStar_Pervasives_Native.option * (Prims.string *
    Parser_JSON.json_val) Prims.list)=
  let ctxval =
    match FStar_List_Tot_Base.find
            (fun kv -> (FStar_Pervasives_Native.fst kv) = "@context") fields
    with
    | FStar_Pervasives_Native.Some (uu___, v) ->
        FStar_Pervasives_Native.Some v
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let rest =
    FStar_List_Tot_Base.filter
      (fun kv -> (FStar_Pervasives_Native.fst kv) <> "@context") fields in
  (ctxval, rest)
let rec jexp_expand_type_items (ac : JSONLD_Context.active_context)
  (items : Parser_JSON.json_val Prims.list) :
  Parser_JSON.json_val Prims.list=
  match items with
  | [] -> []
  | (Parser_JSON.JString t)::rest ->
      (match JSONLD_Context.expand_iri ac t true with
       | FStar_Pervasives_Native.Some iri -> (Parser_JSON.JString iri) ::
           (jexp_expand_type_items ac rest)
       | FStar_Pervasives_Native.None -> jexp_expand_type_items ac rest)
  | uu___::rest -> jexp_expand_type_items ac rest
let expand_type_values (ac : JSONLD_Context.active_context)
  (value : Parser_JSON.json_val) : Parser_JSON.json_val Prims.list=
  jexp_expand_type_items ac (jexp_as_array value)
let rec jexp_flatten_map_entries
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val Prims.list=
  match entries with
  | [] -> []
  | (uu___, v)::rest ->
      FStar_List_Tot_Base.append (jexp_as_array v)
        (jexp_flatten_map_entries rest)
let jexp_language_map_item (key : Prims.string) (v : Parser_JSON.json_val) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString s ->
      if key = "@none"
      then
        FStar_Pervasives_Native.Some
          (Parser_JSON.JObject [("@value", (Parser_JSON.JString s))])
      else
        FStar_Pervasives_Native.Some
          (Parser_JSON.JObject
             [("@value", (Parser_JSON.JString s));
             ("@language", (Parser_JSON.JString key))])
  | uu___ -> FStar_Pervasives_Native.None
let rec jexp_language_map_entry_items (key : Prims.string)
  (items : Parser_JSON.json_val Prims.list) :
  Parser_JSON.json_val Prims.list=
  match items with
  | [] -> []
  | v::rest ->
      (match jexp_language_map_item key v with
       | FStar_Pervasives_Native.Some it -> it ::
           (jexp_language_map_entry_items key rest)
       | FStar_Pervasives_Native.None ->
           jexp_language_map_entry_items key rest)
let rec jexp_expand_language_map
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val Prims.list=
  match entries with
  | [] -> []
  | (k, v)::rest ->
      FStar_List_Tot_Base.append
        (jexp_language_map_entry_items k (jexp_as_array v))
        (jexp_expand_language_map rest)
let jexp_set_id_if_absent (iri : Prims.string) (item : Parser_JSON.json_val)
  : Parser_JSON.json_val=
  match item with
  | Parser_JSON.JObject fields ->
      if jexp_has_field "@value" fields
      then item
      else
        if jexp_has_field "@id" fields
        then item
        else
          Parser_JSON.JObject (("@id", (Parser_JSON.JString iri)) :: fields)
  | uu___ -> item
let jexp_add_type_to_item (kiri : Prims.string) (item : Parser_JSON.json_val)
  : Parser_JSON.json_val=
  match item with
  | Parser_JSON.JObject fields ->
      if jexp_has_field "@value" fields
      then item
      else
        Parser_JSON.JObject
          (("@type", (Parser_JSON.JArray [Parser_JSON.JString kiri])) ::
          fields)
  | uu___ -> item
let jexp_map_key_iri (ac : JSONLD_Context.active_context) (k : Prims.string)
  (vocab : Prims.bool) : Prims.string FStar_Pervasives_Native.option=
  if k = "@none"
  then FStar_Pervasives_Native.None
  else
    (match JSONLD_Context.expand_iri ac k vocab with
     | FStar_Pervasives_Native.Some iri ->
         if iri = "@none"
         then FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.Some iri
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec expand_node (ac : JSONLD_Context.active_context)
  (v : Parser_JSON.json_val) (fuel : Prims.nat) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JObject fields ->
         let uu___1 = jexp_extract_context fields in
         (match uu___1 with
          | (ctxval, fields1) ->
              let ac_eff_opt =
                match ctxval with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.Some ac
                | FStar_Pervasives_Native.Some cv ->
                    JSONLD_Context.context_process ac cv in
              (match ac_eff_opt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ac_eff ->
                   (match expand_fields_list ac_eff fields1
                            (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some outfields ->
                        FStar_Pervasives_Native.Some
                          (Parser_JSON.JObject outfields))))
     | uu___1 -> FStar_Pervasives_Native.None)
and expand_fields_list (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match fields with
     | [] -> FStar_Pervasives_Native.Some []
     | (key, value)::rest ->
         (match expand_one_field ac key value (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
              expand_fields_list ac rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some outkv)
              ->
              (match expand_fields_list ac rest (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restout ->
                   FStar_Pervasives_Native.Some (outkv :: restout))))
and expand_one_field (ac : JSONLD_Context.active_context)
  (key : Prims.string) (value : Parser_JSON.json_val) (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if key = "@id"
    then
      (match value with
       | Parser_JSON.JString s ->
           (match JSONLD_Context.expand_iri ac s false with
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some iri ->
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.Some
                     ("@id", (Parser_JSON.JString iri))))
       | uu___1 -> FStar_Pervasives_Native.None)
    else
      if key = "@type"
      then
        FStar_Pervasives_Native.Some
          (FStar_Pervasives_Native.Some
             ("@type", (Parser_JSON.JArray (expand_type_values ac value))))
      else
        if key = "@graph"
        then
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some
               ("@graph",
                 (Parser_JSON.JArray
                    (expand_graph_items ac (jexp_as_array value)
                       (fuel - Prims.int_one)))))
        else
          if key = "@reverse"
          then
            (match value with
             | Parser_JSON.JObject rfields ->
                 (match expand_reverse_block_fields ac rfields
                          (fuel - Prims.int_one)
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some entries ->
                      FStar_Pervasives_Native.Some
                        (FStar_Pervasives_Native.Some
                           ("@reverse", (Parser_JSON.JObject entries))))
             | uu___4 -> FStar_Pervasives_Native.None)
          else
            if key = "@index"
            then FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
            else
              if key = "@included"
              then FStar_Pervasives_Native.None
              else
                if key = "@nest"
                then FStar_Pervasives_Native.None
                else
                  if JSONLD_Context.jldctx_is_keyword key
                  then FStar_Pervasives_Native.None
                  else
                    (match JSONLD_Context.expand_iri ac key true with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.Some
                           FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some prop_iri ->
                         if JSONLD_Context.jldctx_is_keyword prop_iri
                         then
                           expand_aliased_field ac prop_iri value
                             (fuel - Prims.int_one)
                         else
                           (match JSONLD_Context.jldctx_find_term
                                    ac.JSONLD_Context.ac_terms key
                            with
                            | FStar_Pervasives_Native.Some td ->
                                if td.JSONLD_Context.td_reverse
                                then
                                  expand_reverse_property ac
                                    (FStar_Pervasives_Native.Some td)
                                    prop_iri value (fuel - Prims.int_one)
                                else
                                  expand_ordinary_property ac
                                    (FStar_Pervasives_Native.Some td)
                                    prop_iri value (fuel - Prims.int_one)
                            | FStar_Pervasives_Native.None ->
                                expand_ordinary_property ac
                                  FStar_Pervasives_Native.None prop_iri value
                                  (fuel - Prims.int_one)))
and expand_ordinary_property (ac : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option)
  (prop_iri : Prims.string) (value : Parser_JSON.json_val) (fuel : Prims.nat)
  :
  (Prims.string * Parser_JSON.json_val) FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let is_list =
       match term_opt with
       | FStar_Pervasives_Native.Some td ->
           JSONLD_Context.ck_is_list td.JSONLD_Context.td_container
       | FStar_Pervasives_Native.None -> false in
     match expand_property_items ac term_opt value (fuel - Prims.int_one)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some items ->
         if is_list
         then
           FStar_Pervasives_Native.Some
             (FStar_Pervasives_Native.Some
                (prop_iri,
                  (Parser_JSON.JArray
                     [Parser_JSON.JObject
                        [("@list", (Parser_JSON.JArray items))]])))
         else
           FStar_Pervasives_Native.Some
             (FStar_Pervasives_Native.Some
                (prop_iri, (Parser_JSON.JArray items))))
and expand_reverse_property (ac : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option)
  (prop_iri : Prims.string) (value : Parser_JSON.json_val) (fuel : Prims.nat)
  :
  (Prims.string * Parser_JSON.json_val) FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match expand_property_items ac term_opt value (fuel - Prims.int_one)
     with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some items ->
         FStar_Pervasives_Native.Some
           (FStar_Pervasives_Native.Some
              ("@reverse",
                (Parser_JSON.JObject [(prop_iri, (Parser_JSON.JArray items))]))))
and expand_reverse_block_fields (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match fields with
     | [] -> FStar_Pervasives_Native.Some []
     | (key, value)::rest ->
         if JSONLD_Context.jldctx_is_keyword key
         then FStar_Pervasives_Native.None
         else
           (match JSONLD_Context.expand_iri ac key true with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some prop_iri ->
                if JSONLD_Context.jldctx_is_keyword prop_iri
                then FStar_Pervasives_Native.None
                else
                  (let term_opt =
                     JSONLD_Context.jldctx_find_term
                       ac.JSONLD_Context.ac_terms key in
                   match expand_property_items ac term_opt value
                           (fuel - Prims.int_one)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some items ->
                       (match expand_reverse_block_fields ac rest
                                (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some restout ->
                            FStar_Pervasives_Native.Some
                              ((prop_iri, (Parser_JSON.JArray items)) ::
                              restout)))))
and expand_property_items (ac : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option)
  (value : Parser_JSON.json_val) (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let type_map =
       match term_opt with
       | FStar_Pervasives_Native.Some td -> td.JSONLD_Context.td_type_mapping
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
     let lang_ovr =
       match term_opt with
       | FStar_Pervasives_Native.Some td -> td.JSONLD_Context.td_language
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
     let ck =
       match term_opt with
       | FStar_Pervasives_Native.Some td -> td.JSONLD_Context.td_container
       | FStar_Pervasives_Native.None -> JSONLD_Context.CK_None in
     match (ck, value) with
     | (JSONLD_Context.CK_Index, Parser_JSON.JObject entries) ->
         expand_property ac type_map lang_ovr
           (jexp_flatten_map_entries entries) (fuel - Prims.int_one)
     | (JSONLD_Context.CK_Language, Parser_JSON.JObject entries) ->
         FStar_Pervasives_Native.Some (jexp_expand_language_map entries)
     | (JSONLD_Context.CK_Id, Parser_JSON.JObject entries) ->
         jexp_expand_id_map ac entries (fuel - Prims.int_one)
     | (JSONLD_Context.CK_Type, Parser_JSON.JObject entries) ->
         jexp_expand_type_map ac entries (fuel - Prims.int_one)
     | (uu___1, uu___2) ->
         expand_property ac type_map lang_ovr (jexp_as_array value)
           (fuel - Prims.int_one))
and jexp_expand_id_map (ac : JSONLD_Context.active_context)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match entries with
     | [] -> FStar_Pervasives_Native.Some []
     | (k, v)::rest ->
         (match expand_item ac FStar_Pervasives_Native.None
                  FStar_Pervasives_Native.None v (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
              jexp_expand_id_map ac rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some item)
              ->
              let item1 =
                match jexp_map_key_iri ac k false with
                | FStar_Pervasives_Native.None -> item
                | FStar_Pervasives_Native.Some iri ->
                    jexp_set_id_if_absent iri item in
              (match jexp_expand_id_map ac rest (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restout ->
                   FStar_Pervasives_Native.Some (item1 :: restout))))
and jexp_expand_type_map (ac : JSONLD_Context.active_context)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match entries with
     | [] -> FStar_Pervasives_Native.Some []
     | (k, v)::rest ->
         (match expand_item ac (FStar_Pervasives_Native.Some "@id")
                  FStar_Pervasives_Native.None v (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
              jexp_expand_type_map ac rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some item)
              ->
              let item1 =
                match jexp_map_key_iri ac k true with
                | FStar_Pervasives_Native.None -> item
                | FStar_Pervasives_Native.Some kiri ->
                    jexp_add_type_to_item kiri item in
              (match jexp_expand_type_map ac rest (fuel - Prims.int_one) with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restout ->
                   FStar_Pervasives_Native.Some (item1 :: restout))))
and expand_aliased_field (ac : JSONLD_Context.active_context)
  (canon_key : Prims.string) (value : Parser_JSON.json_val)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else expand_one_field ac canon_key value (fuel - Prims.int_one)
and expand_property (ac : JSONLD_Context.active_context)
  (type_map : Prims.string FStar_Pervasives_Native.option)
  (lang_ovr :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | v::rest ->
         (match expand_item ac type_map lang_ovr v (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
              expand_property ac type_map lang_ovr rest
                (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some one)
              ->
              (match expand_property ac type_map lang_ovr rest
                       (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restout ->
                   FStar_Pervasives_Native.Some (one :: restout))))
and expand_item (ac : JSONLD_Context.active_context)
  (type_map : Prims.string FStar_Pervasives_Native.option)
  (lang_ovr :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (v : Parser_JSON.json_val) (fuel : Prims.nat) :
  Parser_JSON.json_val FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JNull ->
         FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
     | Parser_JSON.JObject fields ->
         if jexp_has_field "@value" fields
         then
           (match jexp_expand_value_object ac fields with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some vo ->
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.Some vo))
         else
           if jexp_has_field "@list" fields
           then
             (match FStar_List_Tot_Base.find
                      (fun kv -> (FStar_Pervasives_Native.fst kv) = "@list")
                      fields
              with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (uu___2, lstval) ->
                  (match expand_property ac type_map lang_ovr
                           (jexp_as_array lstval) (fuel - Prims.int_one)
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some items ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.Some
                            (Parser_JSON.JObject
                               [("@list", (Parser_JSON.JArray items))]))))
           else
             if jexp_has_field "@reverse" fields
             then FStar_Pervasives_Native.None
             else
               (match expand_node ac v (fuel - Prims.int_one) with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some nodeobj ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some nodeobj))
     | Parser_JSON.JString s ->
         (match type_map with
          | FStar_Pervasives_Native.None ->
              let eff_lang =
                match lang_ovr with
                | FStar_Pervasives_Native.Some l -> l
                | FStar_Pervasives_Native.None ->
                    ac.JSONLD_Context.ac_language in
              (match eff_lang with
               | FStar_Pervasives_Native.Some lg ->
                   FStar_Pervasives_Native.Some
                     (FStar_Pervasives_Native.Some
                        (Parser_JSON.JObject
                           [("@value", (Parser_JSON.JString s));
                           ("@language", (Parser_JSON.JString lg))]))
               | FStar_Pervasives_Native.None ->
                   FStar_Pervasives_Native.Some
                     (FStar_Pervasives_Native.Some
                        (Parser_JSON.JObject
                           [("@value", (Parser_JSON.JString s))])))
          | FStar_Pervasives_Native.Some dt ->
              if dt = "@id"
              then
                (match JSONLD_Context.expand_iri ac s false with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some
                       FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some iri ->
                     FStar_Pervasives_Native.Some
                       (FStar_Pervasives_Native.Some
                          (Parser_JSON.JObject
                             [("@id", (Parser_JSON.JString iri))])))
              else
                if dt = "@vocab"
                then
                  (match JSONLD_Context.expand_iri ac s true with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.Some
                         FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some iri ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.Some
                            (Parser_JSON.JObject
                               [("@id", (Parser_JSON.JString iri))])))
                else
                  FStar_Pervasives_Native.Some
                    (FStar_Pervasives_Native.Some
                       (Parser_JSON.JObject
                          [("@value", (Parser_JSON.JString s));
                          ("@type", (Parser_JSON.JString dt))])))
     | Parser_JSON.JBool uu___1 ->
         FStar_Pervasives_Native.Some
           (FStar_Pervasives_Native.Some (jexp_wrap_scalar type_map v))
     | Parser_JSON.JNumber uu___1 ->
         FStar_Pervasives_Native.Some
           (FStar_Pervasives_Native.Some (jexp_wrap_scalar type_map v))
     | Parser_JSON.JArray uu___1 -> FStar_Pervasives_Native.None)
and expand_graph_items (ac : JSONLD_Context.active_context)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | v::rest ->
         (match expand_node ac v (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None ->
              expand_graph_items ac rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some nodeobj -> nodeobj ::
              (expand_graph_items ac rest (fuel - Prims.int_one))))
let expand (ac : JSONLD_Context.active_context) (doc : Parser_JSON.json_val)
  : Parser_JSON.json_val FStar_Pervasives_Native.option=
  let fuel =
    ((Prims.of_int (3)) * (Parser_JSON.json_size doc)) + (Prims.of_int (32)) in
  match doc with
  | Parser_JSON.JObject uu___ ->
      (match expand_node ac doc fuel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (Parser_JSON.JObject []) ->
           FStar_Pervasives_Native.Some (Parser_JSON.JArray [])
       | FStar_Pervasives_Native.Some nodeobj ->
           FStar_Pervasives_Native.Some (Parser_JSON.JArray [nodeobj]))
  | Parser_JSON.JArray items ->
      FStar_Pervasives_Native.Some
        (Parser_JSON.JArray (expand_graph_items ac items fuel))
  | uu___ -> FStar_Pervasives_Native.None
