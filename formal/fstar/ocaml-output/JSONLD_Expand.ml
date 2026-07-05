open Prims
let jexp_as_array (v : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match v with | Parser_JSON.JArray items -> items | uu___ -> [v]
let jexp_has_field (name : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun kv -> (FStar_Pervasives_Native.fst kv) = name) fields
let rec jexp_find_aliased_field (ac : JSONLD_Context.active_context)
  (kw : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) FStar_Pervasives_Native.option=
  match fields with
  | [] -> FStar_Pervasives_Native.None
  | (k, v)::rest ->
      (match JSONLD_Context.expand_iri ac k true with
       | FStar_Pervasives_Native.Some e ->
           if e = kw
           then FStar_Pervasives_Native.Some (k, v)
           else jexp_find_aliased_field ac kw rest
       | FStar_Pervasives_Native.None -> jexp_find_aliased_field ac kw rest)
let jexp_has_aliased_field (ac : JSONLD_Context.active_context)
  (kw : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (jexp_find_aliased_field ac kw fields)
let rec jexp_only_graph_keys
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest -> (k = "@graph") && (jexp_only_graph_keys rest)
let rec jexp_collect_graph_values
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val Prims.list=
  match fields with
  | [] -> []
  | (uu___, v)::rest ->
      FStar_List_Tot_Base.append (jexp_as_array v)
        (jexp_collect_graph_values rest)
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
let rec jexp_value_object_keys_valid (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest ->
      (match JSONLD_Context.expand_iri ac k true with
       | FStar_Pervasives_Native.Some e ->
           ((((e = "@value") || (e = "@language")) || (e = "@type")) ||
              (e = "@direction"))
             || (e = "@index")
       | FStar_Pervasives_Native.None -> false) &&
        (jexp_value_object_keys_valid ac rest)
let jexp_expand_value_object (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match jexp_find_aliased_field ac "@value" fields with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (uu___, v) ->
      if Prims.op_Negation (jexp_value_object_keys_valid ac fields)
      then FStar_Pervasives_Native.None
      else
        if
          (match jexp_find_aliased_field ac "@index" fields with
           | FStar_Pervasives_Native.Some
               (uu___2, Parser_JSON.JString uu___3) -> false
           | FStar_Pervasives_Native.Some uu___2 -> true
           | FStar_Pervasives_Native.None -> false)
        then FStar_Pervasives_Native.None
        else
          if
            (match jexp_find_aliased_field ac "@language" fields with
             | FStar_Pervasives_Native.Some
                 (uu___3, Parser_JSON.JString uu___4) -> false
             | FStar_Pervasives_Native.Some (uu___3, Parser_JSON.JNull) ->
                 false
             | FStar_Pervasives_Native.Some uu___3 -> true
             | FStar_Pervasives_Native.None -> false)
          then FStar_Pervasives_Native.None
          else
            if
              (match jexp_find_aliased_field ac "@type" fields with
               | FStar_Pervasives_Native.Some
                   (uu___4, Parser_JSON.JString uu___5) -> false
               | FStar_Pervasives_Native.Some uu___4 -> true
               | FStar_Pervasives_Native.None -> false)
            then FStar_Pervasives_Native.None
            else
              (let lang =
                 match jexp_find_aliased_field ac "@language" fields with
                 | FStar_Pervasives_Native.Some
                     (uu___5, Parser_JSON.JString s) ->
                     FStar_Pervasives_Native.Some s
                 | uu___5 -> FStar_Pervasives_Native.None in
               let typ =
                 match jexp_find_aliased_field ac "@type" fields with
                 | FStar_Pervasives_Native.Some
                     (uu___5, Parser_JSON.JString s) ->
                     FStar_Pervasives_Native.Some s
                 | uu___5 -> FStar_Pervasives_Native.None in
               if
                 match typ with
                 | FStar_Pervasives_Native.Some t ->
                     (((Parser_FastString.fs_byte_length t) >=
                         (Prims.of_int (2)))
                        &&
                        ((Parser_JSON.jbyte_at t Prims.int_zero) =
                           (Prims.of_int (0x5F))))
                       &&
                       ((Parser_JSON.jbyte_at t Prims.int_one) =
                          (Prims.of_int (0x3A)))
                 | FStar_Pervasives_Native.None -> false
               then FStar_Pervasives_Native.None
               else
                 if
                   (match v with
                    | Parser_JSON.JArray uu___6 ->
                        typ <> (FStar_Pervasives_Native.Some "@json")
                    | Parser_JSON.JObject uu___6 ->
                        typ <> (FStar_Pervasives_Native.Some "@json")
                    | uu___6 -> false)
                 then FStar_Pervasives_Native.None
                 else
                   if
                     (FStar_Pervasives_Native.uu___is_Some lang) &&
                       ((match v with
                         | Parser_JSON.JString uu___7 -> false
                         | Parser_JSON.JNull -> false
                         | uu___7 -> true))
                   then FStar_Pervasives_Native.None
                   else
                     (let dir =
                        match jexp_find_aliased_field ac "@direction" fields
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.Some
                              FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some
                            (uu___8, Parser_JSON.JNull) ->
                            FStar_Pervasives_Native.Some
                              FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some
                            (uu___8, Parser_JSON.JString d) ->
                            if (d = "ltr") || (d = "rtl")
                            then
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.Some d)
                            else FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some uu___8 ->
                            FStar_Pervasives_Native.None in
                      match (dir, typ) with
                      | (FStar_Pervasives_Native.None, uu___8) ->
                          FStar_Pervasives_Native.None
                      | (FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.Some d), uu___8) ->
                          if FStar_Pervasives_Native.uu___is_Some typ
                          then FStar_Pervasives_Native.None
                          else
                            (match lang with
                             | FStar_Pervasives_Native.Some lg ->
                                 FStar_Pervasives_Native.Some
                                   (Parser_JSON.JObject
                                      [("@value", v);
                                      ("@language", (Parser_JSON.JString lg));
                                      ("@direction", (Parser_JSON.JString d))])
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.Some
                                   (Parser_JSON.JObject
                                      [("@value", v);
                                      ("@direction", (Parser_JSON.JString d))]))
                      | (FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.None), uu___8) ->
                          (match (lang, typ) with
                           | (FStar_Pervasives_Native.Some uu___9,
                              FStar_Pervasives_Native.Some uu___10) ->
                               FStar_Pervasives_Native.None
                           | (FStar_Pervasives_Native.Some lg,
                              FStar_Pervasives_Native.None) ->
                               FStar_Pervasives_Native.Some
                                 (Parser_JSON.JObject
                                    [("@value", v);
                                    ("@language", (Parser_JSON.JString lg))])
                           | (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.Some t) ->
                               (match JSONLD_Context.expand_iri ac t true
                                with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some iri ->
                                    FStar_Pervasives_Native.Some
                                      (Parser_JSON.JObject
                                         [("@value", v);
                                         ("@type", (Parser_JSON.JString iri))]))
                           | (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None) ->
                               FStar_Pervasives_Native.Some
                                 (Parser_JSON.JObject [("@value", v)]))))
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
let rec jexp_type_entries_all_strings
  (items : Parser_JSON.json_val Prims.list) : Prims.bool=
  match items with
  | [] -> true
  | (Parser_JSON.JString uu___)::rest -> jexp_type_entries_all_strings rest
  | uu___ -> false
let rec jexp_items_all_node_like (items : Parser_JSON.json_val Prims.list) :
  Prims.bool=
  match items with
  | [] -> true
  | (Parser_JSON.JObject fields)::rest ->
      ((Prims.op_Negation (jexp_has_field "@value" fields)) &&
         (Prims.op_Negation (jexp_has_field "@list" fields)))
        && (jexp_items_all_node_like rest)
  | uu___ -> false
let rec jexp_language_entry_values_valid
  (items : Parser_JSON.json_val Prims.list) : Prims.bool=
  match items with
  | [] -> true
  | (Parser_JSON.JString uu___)::rest ->
      jexp_language_entry_values_valid rest
  | (Parser_JSON.JNull)::rest -> jexp_language_entry_values_valid rest
  | uu___ -> false
let rec jexp_language_map_valid
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match entries with
  | [] -> true
  | (uu___, v)::rest ->
      (jexp_language_entry_values_valid (jexp_as_array v)) &&
        (jexp_language_map_valid rest)
let rec jexp_list_object_keys_valid (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest ->
      (match JSONLD_Context.expand_iri ac k true with
       | FStar_Pervasives_Native.Some e -> (e = "@list") || (e = "@index")
       | FStar_Pervasives_Native.None -> false) &&
        (jexp_list_object_keys_valid ac rest)
let rec jexp_expand_type_items (ac : JSONLD_Context.active_context)
  (items : Parser_JSON.json_val Prims.list) :
  Parser_JSON.json_val Prims.list=
  match items with
  | [] -> []
  | (Parser_JSON.JString t)::rest ->
      (match JSONLD_Context.expand_iri ac t true with
       | FStar_Pervasives_Native.Some iri -> (Parser_JSON.JString iri) ::
           (jexp_expand_type_items ac rest)
       | FStar_Pervasives_Native.None ->
           (match JSONLD_Context.expand_iri ac t false with
            | FStar_Pervasives_Native.Some iri -> (Parser_JSON.JString iri)
                :: (jexp_expand_type_items ac rest)
            | FStar_Pervasives_Native.None -> jexp_expand_type_items ac rest))
  | uu___::rest -> jexp_expand_type_items ac rest
let expand_type_values (ac : JSONLD_Context.active_context)
  (value : Parser_JSON.json_val) : Parser_JSON.json_val Prims.list=
  jexp_expand_type_items ac (jexp_as_array value)
let apply_property_scoped_context (ac : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option) :
  JSONLD_Context.active_context FStar_Pervasives_Native.option=
  match term_opt with
  | FStar_Pervasives_Native.Some td ->
      (match td.JSONLD_Context.td_scoped_context with
       | FStar_Pervasives_Native.Some scoped ->
           (match JSONLD_Context.apply_context_with_propagate ac scoped true
                    true
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some ac_eff ->
                if JSONLD_Context.jldctx_scan_propagate scoped true
                then
                  FStar_Pervasives_Native.Some
                    {
                      JSONLD_Context.ac_terms =
                        (ac_eff.JSONLD_Context.ac_terms);
                      JSONLD_Context.ac_vocab =
                        (ac_eff.JSONLD_Context.ac_vocab);
                      JSONLD_Context.ac_base =
                        (ac_eff.JSONLD_Context.ac_base);
                      JSONLD_Context.ac_language =
                        (ac_eff.JSONLD_Context.ac_language);
                      JSONLD_Context.ac_direction =
                        (ac_eff.JSONLD_Context.ac_direction);
                      JSONLD_Context.ac_previous =
                        FStar_Pervasives_Native.None;
                      JSONLD_Context.ac_mode10 =
                        (ac_eff.JSONLD_Context.ac_mode10)
                    }
                else
                  FStar_Pervasives_Native.Some
                    {
                      JSONLD_Context.ac_terms =
                        (ac_eff.JSONLD_Context.ac_terms);
                      JSONLD_Context.ac_vocab =
                        (ac_eff.JSONLD_Context.ac_vocab);
                      JSONLD_Context.ac_base =
                        (ac_eff.JSONLD_Context.ac_base);
                      JSONLD_Context.ac_language =
                        (ac_eff.JSONLD_Context.ac_language);
                      JSONLD_Context.ac_direction =
                        (ac_eff.JSONLD_Context.ac_direction);
                      JSONLD_Context.ac_previous =
                        (FStar_Pervasives_Native.Some ac);
                      JSONLD_Context.ac_mode10 =
                        (ac_eff.JSONLD_Context.ac_mode10)
                    })
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ac)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some ac
let rec jexp_raw_type_strings_of_items
  (items : Parser_JSON.json_val Prims.list) : Prims.string Prims.list=
  match items with
  | [] -> []
  | (Parser_JSON.JString s)::rest -> s ::
      (jexp_raw_type_strings_of_items rest)
  | uu___::rest -> jexp_raw_type_strings_of_items rest
let rec jexp_raw_type_strings (ac0 : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Prims.string Prims.list=
  match fields with
  | [] -> []
  | (k, v)::rest ->
      let is_type_key =
        (k = "@type") ||
          (match JSONLD_Context.expand_iri ac0 k true with
           | FStar_Pervasives_Native.Some e -> e = "@type"
           | FStar_Pervasives_Native.None -> false) in
      if is_type_key
      then
        FStar_List_Tot_Base.append
          (jexp_raw_type_strings_of_items (jexp_as_array v))
          (jexp_raw_type_strings ac0 rest)
      else jexp_raw_type_strings ac0 rest
let expand_typed_ac (ac0 : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  JSONLD_Context.active_context FStar_Pervasives_Native.option=
  match jexp_raw_type_strings ac0 fields with
  | [] -> FStar_Pervasives_Native.Some ac0
  | types -> JSONLD_Context.apply_type_scoped_contexts ac0 types
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
    (let none_alias =
       match JSONLD_Context.expand_iri ac k true with
       | FStar_Pervasives_Native.Some i -> i = "@none"
       | FStar_Pervasives_Native.None -> false in
     if none_alias
     then FStar_Pervasives_Native.None
     else
       (match JSONLD_Context.expand_iri ac k vocab with
        | FStar_Pervasives_Native.Some iri ->
            if iri = "@none"
            then FStar_Pervasives_Native.None
            else FStar_Pervasives_Native.Some iri
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let jexp_is_graph_object (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields -> jexp_has_field "@graph" fields
  | uu___ -> false
let jexp_ensure_graph_object (nodeobj : Parser_JSON.json_val) :
  Parser_JSON.json_val=
  if jexp_is_graph_object nodeobj
  then nodeobj
  else Parser_JSON.JObject [("@graph", (Parser_JSON.JArray [nodeobj]))]
let jexp_inject_index_field (index_iri : Prims.string)
  (keyval : Parser_JSON.json_val) (item : Parser_JSON.json_val) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match item with
  | Parser_JSON.JObject fields ->
      if jexp_has_field "@value" fields
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some
          (Parser_JSON.JObject
             (FStar_List_Tot_Base.append fields
                [(index_iri, (Parser_JSON.JArray [keyval]))]))
  | uu___ -> FStar_Pervasives_Native.None
let rec jexp_inject_index_items (index_iri : Prims.string)
  (keyval : Parser_JSON.json_val) (items : Parser_JSON.json_val Prims.list) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | it::rest ->
      (match jexp_inject_index_field index_iri keyval it with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some it1 ->
           (match jexp_inject_index_items index_iri keyval rest with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some restout ->
                FStar_Pervasives_Native.Some (it1 :: restout)))
let rec jexp_any_key_expands_to (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (kw : Prims.string) : Prims.bool=
  match fields with
  | [] -> false
  | (k, uu___)::rest ->
      (match JSONLD_Context.expand_iri ac k true with
       | FStar_Pervasives_Native.Some e ->
           (e = kw) || (jexp_any_key_expands_to ac rest kw)
       | FStar_Pervasives_Native.None -> jexp_any_key_expands_to ac rest kw)
let jexp_is_single_id_object (ac : JSONLD_Context.active_context)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | (k, uu___)::[] ->
      (match JSONLD_Context.expand_iri ac k true with
       | FStar_Pervasives_Native.Some e -> e = "@id"
       | FStar_Pervasives_Native.None -> false)
  | uu___ -> false
let rec expand_node (ac : JSONLD_Context.active_context)
  (v : Parser_JSON.json_val) (fuel : Prims.nat) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JObject fields ->
         let ac_popped =
           if
             (jexp_is_single_id_object ac fields) ||
               (jexp_any_key_expands_to ac fields "@value")
           then ac
           else
             (match ac.JSONLD_Context.ac_previous with
              | FStar_Pervasives_Native.Some prev -> prev
              | FStar_Pervasives_Native.None -> ac) in
         let uu___1 = jexp_extract_context fields in
         (match uu___1 with
          | (ctxval, fields1) ->
              let ac0_opt =
                match ctxval with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.Some ac_popped
                | FStar_Pervasives_Native.Some cv ->
                    JSONLD_Context.apply_context_with_propagate ac_popped cv
                      true false in
              (match ac0_opt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ac0 ->
                   (match expand_typed_ac ac0 fields1 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some ac_typed ->
                        (match expand_fields_list ac_typed ac0 fields1
                                 (fuel - Prims.int_one)
                         with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some outfields ->
                             FStar_Pervasives_Native.Some
                               (Parser_JSON.JObject outfields)))))
     | uu___1 -> FStar_Pervasives_Native.None)
and expand_node_from_map (ac : JSONLD_Context.active_context)
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
              let ac0_opt =
                match ctxval with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.Some ac
                | FStar_Pervasives_Native.Some cv ->
                    JSONLD_Context.apply_context_with_propagate ac cv true
                      false in
              (match ac0_opt with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ac0 ->
                   (match expand_typed_ac ac0 fields1 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some ac_typed ->
                        (match expand_fields_list ac_typed ac0 fields1
                                 (fuel - Prims.int_one)
                         with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some outfields ->
                             FStar_Pervasives_Native.Some
                               (Parser_JSON.JObject outfields)))))
     | uu___1 -> FStar_Pervasives_Native.None)
and expand_fields_list (ac : JSONLD_Context.active_context)
  (ac0 : JSONLD_Context.active_context)
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
         (match expand_one_field ac ac0 key value (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
              expand_fields_list ac ac0 rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some
              outkvs) ->
              (match expand_fields_list ac ac0 rest (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restout ->
                   FStar_Pervasives_Native.Some
                     (FStar_List_Tot_Base.append outkvs restout))))
and expand_one_field (ac : JSONLD_Context.active_context)
  (ac0 : JSONLD_Context.active_context) (key : Prims.string)
  (value : Parser_JSON.json_val) (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
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
                     [("@id", (Parser_JSON.JString iri))]))
       | uu___1 -> FStar_Pervasives_Native.None)
    else
      if key = "@type"
      then
        (if jexp_type_entries_all_strings (jexp_as_array value)
         then
           FStar_Pervasives_Native.Some
             (FStar_Pervasives_Native.Some
                [("@type",
                   (Parser_JSON.JArray (expand_type_values ac0 value)))])
         else FStar_Pervasives_Native.None)
      else
        if key = "@graph"
        then
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some
               [("@graph",
                  (Parser_JSON.JArray
                     (expand_graph_items ac (jexp_as_array value)
                        (fuel - Prims.int_one))))])
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
                           [("@reverse", (Parser_JSON.JObject entries))]))
             | uu___4 -> FStar_Pervasives_Native.None)
          else
            if key = "@index"
            then FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
            else
              if key = "@included"
              then
                (match expand_included_items ac (jexp_as_array value)
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some items ->
                     FStar_Pervasives_Native.Some
                       (FStar_Pervasives_Native.Some
                          [("@included", (Parser_JSON.JArray items))]))
              else
                if key = "@nest"
                then
                  (match value with
                   | Parser_JSON.JObject nfields ->
                       (match expand_fields_list ac ac0 nfields
                                (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some outs ->
                            FStar_Pervasives_Native.Some
                              (FStar_Pervasives_Native.Some outs))
                   | Parser_JSON.JArray items ->
                       (match expand_nest_array ac ac0 items
                                (fuel - Prims.int_one)
                        with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some outs ->
                            FStar_Pervasives_Native.Some
                              (FStar_Pervasives_Native.Some outs))
                   | uu___7 -> FStar_Pervasives_Native.None)
                else
                  if JSONLD_Context.jldctx_actual_keyword key
                  then FStar_Pervasives_Native.None
                  else
                    if JSONLD_Context.jldctx_keyword_lookalike key
                    then
                      FStar_Pervasives_Native.Some
                        FStar_Pervasives_Native.None
                    else
                      (match JSONLD_Context.expand_iri ac key true with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.Some
                             FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some prop_iri ->
                           let term_opt =
                             JSONLD_Context.jldctx_find_term
                               ac.JSONLD_Context.ac_terms key in
                           if JSONLD_Context.jldctx_actual_keyword prop_iri
                           then
                             expand_aliased_field ac ac0 term_opt prop_iri
                               value (fuel - Prims.int_one)
                           else
                             if JSONLD_Context.jldctx_keyword_form prop_iri
                             then
                               FStar_Pervasives_Native.Some
                                 FStar_Pervasives_Native.None
                             else
                               (match term_opt with
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
                                      FStar_Pervasives_Native.None prop_iri
                                      value (fuel - Prims.int_one)))
and expand_nest_array (ac : JSONLD_Context.active_context)
  (ac0 : JSONLD_Context.active_context)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | (Parser_JSON.JObject nfields)::rest ->
         (match expand_fields_list ac ac0 nfields (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some outs ->
              (match expand_nest_array ac ac0 rest (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restouts ->
                   FStar_Pervasives_Native.Some
                     (FStar_List_Tot_Base.append outs restouts)))
     | uu___1 -> FStar_Pervasives_Native.None)
and expand_ordinary_property (ac : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option)
  (prop_iri : Prims.string) (value : Parser_JSON.json_val) (fuel : Prims.nat)
  :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match apply_property_scoped_context ac term_opt with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some ac_eff ->
         let is_list =
           match term_opt with
           | FStar_Pervasives_Native.Some td ->
               JSONLD_Context.ck_is_list td.JSONLD_Context.td_container
           | FStar_Pervasives_Native.None -> false in
         (match expand_property_items ac_eff term_opt value
                  (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some items ->
              if is_list
              then
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.Some
                     [(prop_iri,
                        (Parser_JSON.JArray
                           [Parser_JSON.JObject
                              [("@list", (Parser_JSON.JArray items))]]))])
              else
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.Some
                     [(prop_iri, (Parser_JSON.JArray items))])))
and expand_reverse_property (ac : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option)
  (prop_iri : Prims.string) (value : Parser_JSON.json_val) (fuel : Prims.nat)
  :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match apply_property_scoped_context ac term_opt with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some ac_eff ->
         (match expand_property_items ac_eff term_opt value
                  (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some items ->
              if jexp_items_all_node_like items
              then
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.Some
                     [("@reverse",
                        (Parser_JSON.JObject
                           [(prop_iri, (Parser_JSON.JArray items))]))])
              else FStar_Pervasives_Native.None))
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
                       if Prims.op_Negation (jexp_items_all_node_like items)
                       then FStar_Pervasives_Native.None
                       else
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
     let dir_ovr =
       match term_opt with
       | FStar_Pervasives_Native.Some td -> td.JSONLD_Context.td_direction
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
     let idx_prop =
       match term_opt with
       | FStar_Pervasives_Native.Some td -> td.JSONLD_Context.td_index
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
     let ck =
       match term_opt with
       | FStar_Pervasives_Native.Some td -> td.JSONLD_Context.td_container
       | FStar_Pervasives_Native.None -> JSONLD_Context.CK_None in
     if type_map = (FStar_Pervasives_Native.Some "@json")
     then
       FStar_Pervasives_Native.Some
         [Parser_JSON.JObject
            [("@value", value); ("@type", (Parser_JSON.JString "@json"))]]
     else
       (match (ck, value) with
        | (JSONLD_Context.CK_Index, Parser_JSON.JObject entries) ->
            (match idx_prop with
             | FStar_Pervasives_Native.Some name ->
                 jexp_expand_property_index_map ac name type_map lang_ovr
                   dir_ovr entries (fuel - Prims.int_one)
             | FStar_Pervasives_Native.None ->
                 expand_property ac type_map lang_ovr dir_ovr
                   (jexp_flatten_map_entries entries) (fuel - Prims.int_one))
        | (JSONLD_Context.CK_Language, Parser_JSON.JObject entries) ->
            if jexp_language_map_valid entries
            then
              FStar_Pervasives_Native.Some (jexp_expand_language_map entries)
            else FStar_Pervasives_Native.None
        | (JSONLD_Context.CK_Id, Parser_JSON.JObject entries) ->
            jexp_expand_id_map ac entries (fuel - Prims.int_one)
        | (JSONLD_Context.CK_Type, Parser_JSON.JObject entries) ->
            jexp_expand_type_map ac entries (fuel - Prims.int_one)
        | (JSONLD_Context.CK_Graph, uu___2) ->
            FStar_Pervasives_Native.Some
              (expand_graph_container_items_plain ac (jexp_as_array value)
                 (fuel - Prims.int_one))
        | (JSONLD_Context.CK_GraphIndex, Parser_JSON.JObject entries) ->
            (match idx_prop with
             | FStar_Pervasives_Native.Some name ->
                 jexp_expand_graph_index_map ac name entries
                   (fuel - Prims.int_one)
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some
                   (expand_graph_container_items ac
                      (jexp_flatten_map_entries entries)
                      (fuel - Prims.int_one)))
        | (JSONLD_Context.CK_GraphIndex, uu___2) ->
            FStar_Pervasives_Native.Some
              (expand_graph_container_items ac (jexp_as_array value)
                 (fuel - Prims.int_one))
        | (JSONLD_Context.CK_GraphId, Parser_JSON.JObject entries) ->
            FStar_Pervasives_Native.Some
              (expand_graph_id_map ac entries (fuel - Prims.int_one))
        | (JSONLD_Context.CK_GraphId, uu___2) ->
            FStar_Pervasives_Native.Some
              (expand_graph_container_items ac (jexp_as_array value)
                 (fuel - Prims.int_one))
        | (uu___2, uu___3) ->
            expand_property ac type_map lang_ovr dir_ovr
              (jexp_as_array value) (fuel - Prims.int_one)))
and jexp_index_key_field (ac : JSONLD_Context.active_context)
  (index_name : Prims.string) (k : Prims.string) (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match JSONLD_Context.expand_iri ac index_name true with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some index_iri ->
         if JSONLD_Context.jldctx_is_keyword index_iri
         then FStar_Pervasives_Native.None
         else
           (let term_opt2 =
              JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms
                index_name in
            let type_map2 =
              match term_opt2 with
              | FStar_Pervasives_Native.Some td ->
                  td.JSONLD_Context.td_type_mapping
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
            let lang_ovr2 =
              match term_opt2 with
              | FStar_Pervasives_Native.Some td ->
                  td.JSONLD_Context.td_language
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
            let dir_ovr2 =
              match term_opt2 with
              | FStar_Pervasives_Native.Some td ->
                  td.JSONLD_Context.td_direction
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
            match expand_item ac type_map2 lang_ovr2 dir_ovr2 false
                    (Parser_JSON.JString k) (fuel - Prims.int_one)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
                FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some kv)
                -> FStar_Pervasives_Native.Some (index_iri, kv)))
and jexp_expand_property_index_map (ac : JSONLD_Context.active_context)
  (index_name : Prims.string)
  (type_map : Prims.string FStar_Pervasives_Native.option)
  (lang_ovr :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (dir_ovr :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match entries with
     | [] -> FStar_Pervasives_Native.Some []
     | (k, v)::rest ->
         (match expand_property ac type_map lang_ovr dir_ovr
                  (jexp_as_array v) (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some items ->
              (match jexp_expand_property_index_map ac index_name type_map
                       lang_ovr dir_ovr rest (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some restout ->
                   if k = "@none"
                   then
                     FStar_Pervasives_Native.Some
                       (FStar_List_Tot_Base.append items restout)
                   else
                     (match jexp_index_key_field ac index_name k
                              (fuel - Prims.int_one)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (index_iri, keyval) ->
                          (match jexp_inject_index_items index_iri keyval
                                   items
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some items1 ->
                               FStar_Pervasives_Native.Some
                                 (FStar_List_Tot_Base.append items1 restout))))))
and jexp_expand_graph_index_map (ac : JSONLD_Context.active_context)
  (index_name : Prims.string)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match entries with
     | [] -> FStar_Pervasives_Native.Some []
     | (k, v)::rest ->
         let items =
           expand_graph_container_items ac (jexp_as_array v)
             (fuel - Prims.int_one) in
         (match jexp_expand_graph_index_map ac index_name rest
                  (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some restout ->
              if k = "@none"
              then
                FStar_Pervasives_Native.Some
                  (FStar_List_Tot_Base.append items restout)
              else
                (match jexp_index_key_field ac index_name k
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (index_iri, keyval) ->
                     (match jexp_inject_index_items index_iri keyval items
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some items1 ->
                          FStar_Pervasives_Native.Some
                            (FStar_List_Tot_Base.append items1 restout)))))
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
         let ac_popped =
           match ac.JSONLD_Context.ac_previous with
           | FStar_Pervasives_Native.Some prev -> prev
           | FStar_Pervasives_Native.None -> ac in
         (match apply_property_scoped_context ac_popped
                  (JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms
                     k)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some ac_for_value ->
              (match expand_item ac_for_value FStar_Pervasives_Native.None
                       FStar_Pervasives_Native.None
                       FStar_Pervasives_Native.None true v
                       (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
                   -> jexp_expand_id_map ac rest (fuel - Prims.int_one)
               | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some
                   item) ->
                   let item1 =
                     match jexp_map_key_iri ac k false with
                     | FStar_Pervasives_Native.None -> item
                     | FStar_Pervasives_Native.Some iri ->
                         jexp_set_id_if_absent iri item in
                   (match jexp_expand_id_map ac rest (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some restout ->
                        FStar_Pervasives_Native.Some (item1 :: restout)))))
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
         let ac_popped =
           match ac.JSONLD_Context.ac_previous with
           | FStar_Pervasives_Native.Some prev -> prev
           | FStar_Pervasives_Native.None -> ac in
         (match apply_property_scoped_context ac_popped
                  (JSONLD_Context.jldctx_find_term ac.JSONLD_Context.ac_terms
                     k)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some ac_for_value ->
              (match expand_item ac_for_value
                       (FStar_Pervasives_Native.Some "@id")
                       FStar_Pervasives_Native.None
                       FStar_Pervasives_Native.None true v
                       (fuel - Prims.int_one)
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
                   -> jexp_expand_type_map ac rest (fuel - Prims.int_one)
               | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some
                   item) ->
                   let item1 =
                     match jexp_map_key_iri ac k true with
                     | FStar_Pervasives_Native.None -> item
                     | FStar_Pervasives_Native.Some kiri ->
                         jexp_add_type_to_item kiri item in
                   (match jexp_expand_type_map ac rest (fuel - Prims.int_one)
                    with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some restout ->
                        FStar_Pervasives_Native.Some (item1 :: restout)))))
and expand_graph_container_items (ac : JSONLD_Context.active_context)
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
              expand_graph_container_items ac rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some nodeobj ->
              (jexp_ensure_graph_object nodeobj) ::
              (expand_graph_container_items ac rest (fuel - Prims.int_one))))
and expand_graph_container_items_plain (ac : JSONLD_Context.active_context)
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
              expand_graph_container_items_plain ac rest
                (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some nodeobj ->
              (Parser_JSON.JObject
                 [("@graph", (Parser_JSON.JArray [nodeobj]))])
              ::
              (expand_graph_container_items_plain ac rest
                 (fuel - Prims.int_one))))
and expand_graph_id_map (ac : JSONLD_Context.active_context)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) : Parser_JSON.json_val Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match entries with
     | [] -> []
     | (k, v)::rest ->
         FStar_List_Tot_Base.append
           (expand_graph_id_map_one ac k (jexp_as_array v)
              (fuel - Prims.int_one))
           (expand_graph_id_map ac rest (fuel - Prims.int_one)))
and expand_graph_id_map_one (ac : JSONLD_Context.active_context)
  (k : Prims.string) (items : Parser_JSON.json_val Prims.list)
  (fuel : Prims.nat) : Parser_JSON.json_val Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | v::rest ->
         (match expand_node ac v (fuel - Prims.int_one) with
          | FStar_Pervasives_Native.None ->
              expand_graph_id_map_one ac k rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some nodeobj ->
              let graphobj = jexp_ensure_graph_object nodeobj in
              let wrapped =
                match jexp_map_key_iri ac k false with
                | FStar_Pervasives_Native.None -> graphobj
                | FStar_Pervasives_Native.Some iri ->
                    jexp_set_id_if_absent iri graphobj in
              wrapped ::
                (expand_graph_id_map_one ac k rest (fuel - Prims.int_one))))
and expand_aliased_field (ac : JSONLD_Context.active_context)
  (ac0 : JSONLD_Context.active_context)
  (term_opt : JSONLD_Context.term_def FStar_Pervasives_Native.option)
  (canon_key : Prims.string) (value : Parser_JSON.json_val)
  (fuel : Prims.nat) :
  (Prims.string * Parser_JSON.json_val) Prims.list
    FStar_Pervasives_Native.option FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match apply_property_scoped_context ac term_opt with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some ac_eff ->
         expand_one_field ac_eff ac0 canon_key value (fuel - Prims.int_one))
and expand_property (ac : JSONLD_Context.active_context)
  (type_map : Prims.string FStar_Pervasives_Native.option)
  (lang_ovr :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (dir_ovr :
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
         (match expand_item ac type_map lang_ovr dir_ovr false v
                  (fuel - Prims.int_one)
          with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None) ->
              expand_property ac type_map lang_ovr dir_ovr rest
                (fuel - Prims.int_one)
          | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some one)
              ->
              (match expand_property ac type_map lang_ovr dir_ovr rest
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
  (dir_ovr :
    Prims.string FStar_Pervasives_Native.option
      FStar_Pervasives_Native.option)
  (from_map : Prims.bool) (v : Parser_JSON.json_val) (fuel : Prims.nat) :
  Parser_JSON.json_val FStar_Pervasives_Native.option
    FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match v with
     | Parser_JSON.JNull ->
         FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
     | Parser_JSON.JObject fields ->
         if jexp_has_aliased_field ac "@value" fields
         then
           (match jexp_expand_value_object ac fields with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some vo ->
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.Some vo))
         else
           if jexp_has_aliased_field ac "@list" fields
           then
             (if Prims.op_Negation (jexp_list_object_keys_valid ac fields)
              then FStar_Pervasives_Native.None
              else
                (match jexp_find_aliased_field ac "@list" fields with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some (uu___3, lstval) ->
                     (match expand_property ac type_map lang_ovr dir_ovr
                              (jexp_as_array lstval) (fuel - Prims.int_one)
                      with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some items ->
                          FStar_Pervasives_Native.Some
                            (FStar_Pervasives_Native.Some
                               (Parser_JSON.JObject
                                  [("@list", (Parser_JSON.JArray items))])))))
           else
             if jexp_has_aliased_field ac "@reverse" fields
             then FStar_Pervasives_Native.None
             else
               if jexp_has_aliased_field ac "@language" fields
               then FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
               else
                 (match if from_map
                        then expand_node_from_map ac v (fuel - Prims.int_one)
                        else expand_node ac v (fuel - Prims.int_one)
                  with
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
              let eff_dir =
                match dir_ovr with
                | FStar_Pervasives_Native.Some d -> d
                | FStar_Pervasives_Native.None ->
                    ac.JSONLD_Context.ac_direction in
              let base_fields = ("@value", (Parser_JSON.JString s)) ::
                (match eff_lang with
                 | FStar_Pervasives_Native.Some lg ->
                     [("@language", (Parser_JSON.JString lg))]
                 | FStar_Pervasives_Native.None -> []) in
              (match eff_dir with
               | FStar_Pervasives_Native.Some d ->
                   FStar_Pervasives_Native.Some
                     (FStar_Pervasives_Native.Some
                        (Parser_JSON.JObject
                           (FStar_List_Tot_Base.append base_fields
                              [("@direction", (Parser_JSON.JString d))])))
               | FStar_Pervasives_Native.None ->
                   FStar_Pervasives_Native.Some
                     (FStar_Pervasives_Native.Some
                        (Parser_JSON.JObject base_fields)))
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
                   | FStar_Pervasives_Native.Some iri ->
                       FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.Some
                            (Parser_JSON.JObject
                               [("@id", (Parser_JSON.JString iri))]))
                   | FStar_Pervasives_Native.None ->
                       (match JSONLD_Context.expand_iri ac s false with
                        | FStar_Pervasives_Native.Some iri ->
                            FStar_Pervasives_Native.Some
                              (FStar_Pervasives_Native.Some
                                 (Parser_JSON.JObject
                                    [("@id", (Parser_JSON.JString iri))]))
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.Some
                              FStar_Pervasives_Native.None))
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
     | (Parser_JSON.JObject fields)::rest ->
         if
           (jexp_has_aliased_field ac "@value" fields) ||
             (jexp_has_aliased_field ac "@list" fields)
         then expand_graph_items ac rest (fuel - Prims.int_one)
         else
           (match FStar_List_Tot_Base.find
                    (fun kv -> (FStar_Pervasives_Native.fst kv) = "@set")
                    fields
            with
            | FStar_Pervasives_Native.Some (uu___2, setval) ->
                FStar_List_Tot_Base.append
                  (expand_graph_items ac (jexp_as_array setval)
                     (fuel - Prims.int_one))
                  (expand_graph_items ac rest (fuel - Prims.int_one))
            | FStar_Pervasives_Native.None ->
                (match expand_node ac (Parser_JSON.JObject fields)
                         (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     expand_graph_items ac rest (fuel - Prims.int_one)
                 | FStar_Pervasives_Native.Some nodeobj -> nodeobj ::
                     (expand_graph_items ac rest (fuel - Prims.int_one))))
     | uu___1::rest -> expand_graph_items ac rest (fuel - Prims.int_one))
and expand_included_items (ac : JSONLD_Context.active_context)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | (Parser_JSON.JObject fields)::rest ->
         if
           (jexp_has_aliased_field ac "@value" fields) ||
             (jexp_has_aliased_field ac "@list" fields)
         then FStar_Pervasives_Native.None
         else
           (match expand_node ac (Parser_JSON.JObject fields)
                    (fuel - Prims.int_one)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some nodeobj ->
                (match expand_included_items ac rest (fuel - Prims.int_one)
                 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some restout ->
                     FStar_Pervasives_Native.Some (nodeobj :: restout)))
     | uu___1 -> FStar_Pervasives_Native.None)
and expand_top_items (ac : JSONLD_Context.active_context)
  (items : Parser_JSON.json_val Prims.list) (fuel : Prims.nat) :
  Parser_JSON.json_val Prims.list FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (match items with
     | [] -> FStar_Pervasives_Native.Some []
     | (Parser_JSON.JObject fields)::rest ->
         if
           (jexp_has_aliased_field ac "@value" fields) ||
             (jexp_has_aliased_field ac "@list" fields)
         then expand_top_items ac rest (fuel - Prims.int_one)
         else
           (match expand_node ac (Parser_JSON.JObject fields)
                    (fuel - Prims.int_one)
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some nodeobj ->
                (match expand_top_items ac rest (fuel - Prims.int_one) with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some restout ->
                     FStar_Pervasives_Native.Some (nodeobj :: restout)))
     | uu___1::rest -> expand_top_items ac rest (fuel - Prims.int_one))
let expand (ac : JSONLD_Context.active_context) (doc : Parser_JSON.json_val)
  : Parser_JSON.json_val FStar_Pervasives_Native.option=
  let fuel =
    ((Prims.of_int (4)) * (Parser_JSON.json_size doc)) + (Prims.of_int (48)) in
  match doc with
  | Parser_JSON.JObject fields0 ->
      if
        (jexp_has_field "@value" fields0) || (jexp_has_field "@list" fields0)
      then FStar_Pervasives_Native.Some (Parser_JSON.JArray [])
      else
        (match expand_node ac doc fuel with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (Parser_JSON.JObject []) ->
             FStar_Pervasives_Native.Some (Parser_JSON.JArray [])
         | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields1) ->
             if jexp_only_graph_keys fields1
             then
               FStar_Pervasives_Native.Some
                 (Parser_JSON.JArray (jexp_collect_graph_values fields1))
             else
               FStar_Pervasives_Native.Some
                 (Parser_JSON.JArray [Parser_JSON.JObject fields1])
         | FStar_Pervasives_Native.Some nodeobj ->
             FStar_Pervasives_Native.Some (Parser_JSON.JArray [nodeobj]))
  | Parser_JSON.JArray items ->
      (match expand_top_items ac items fuel with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some outs ->
           FStar_Pervasives_Native.Some (Parser_JSON.JArray outs))
  | uu___ -> FStar_Pervasives_Native.None
