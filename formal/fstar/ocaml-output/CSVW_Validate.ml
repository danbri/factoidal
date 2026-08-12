open Prims
let cv_starts_with (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  ((FStar_String.strlen s) >= (FStar_String.strlen pfx)) &&
    ((FStar_String.sub s Prims.int_zero (FStar_String.strlen pfx)) = pfx)
let cv_is_object (v : Parser_JSON.json_val) : Prims.bool=
  match v with | Parser_JSON.JObject uu___ -> true | uu___ -> false
let cv_set_field (k : Prims.string) (nv : Parser_JSON.json_val)
  (obj : Parser_JSON.json_val) : Parser_JSON.json_val=
  match obj with
  | Parser_JSON.JObject fs ->
      Parser_JSON.JObject ((k, nv) ::
        (FStar_List_Tot_Base.filter
           (fun kv -> (FStar_Pervasives_Native.fst kv) <> k) fs))
  | uu___ -> obj
let cv_field (k : Prims.string) (v : Parser_JSON.json_val) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  Parser_JSON.json_get_field k v
let cv_has (k : Prims.string) (v : Parser_JSON.json_val) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (cv_field k v)
let cv_is_alpha (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
    ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122))))
let rec cv_all_alpha (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with | [] -> true | c::tl -> (cv_is_alpha c) && (cv_all_alpha tl)
let rec cv_take_to_dash (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::tl ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (45))
      then []
      else c :: (cv_take_to_dash tl)
let cv_lang_valid (tag : Prims.string) : Prims.bool=
  let prim = cv_take_to_dash (FStar_String.list_of_string tag) in
  let n = FStar_List_Tot_Base.length prim in
  ((n >= (Prims.of_int (2))) && (n <= (Prims.of_int (8)))) &&
    (cv_all_alpha prim)
let cv_check_id (role : Prims.string) (v : Parser_JSON.json_val) :
  Prims.string Prims.list=
  match cv_field "@id" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      if cv_starts_with s "_:"
      then [Prims.strcat role " @id must not be a blank node"]
      else []
  | uu___ -> []
let cv_check_type (role : Prims.string) (v : Parser_JSON.json_val) :
  Prims.string Prims.list=
  match Parser_JSON.json_get_string "@type" v with
  | FStar_Pervasives_Native.Some t ->
      if t = role
      then []
      else
        [Prims.strcat "@type "
           (Prims.strcat t (Prims.strcat " invalid for a " role))]
  | FStar_Pervasives_Native.None -> []
let rec cv_check_lang_keys
  (fs : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Prims.string Prims.list=
  match fs with
  | [] -> []
  | (k, uu___)::tl ->
      let here =
        if cv_lang_valid k
        then []
        else [Prims.strcat "invalid language tag: " k] in
      FStar_List_Tot_Base.op_At here (cv_check_lang_keys tl)
let cv_check_titles (v : Parser_JSON.json_val) : Prims.string Prims.list=
  match cv_field "titles" v with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fs) ->
      cv_check_lang_keys fs
  | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___) -> []
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray uu___) -> []
  | FStar_Pervasives_Native.Some uu___ ->
      ["titles must be a string, array, or language object"]
let cv_known_datatype (n : Prims.string) : Prims.bool=
  ((((((((((((((((((((((((((((((((((((((((((((((n = "anyAtomicType") ||
                                                 (n = "anyURI"))
                                                || (n = "base64Binary"))
                                               || (n = "boolean"))
                                              || (n = "date"))
                                             || (n = "dateTime"))
                                            || (n = "dateTimeStamp"))
                                           || (n = "decimal"))
                                          || (n = "integer"))
                                         || (n = "long"))
                                        || (n = "int"))
                                       || (n = "short"))
                                      || (n = "byte"))
                                     || (n = "nonNegativeInteger"))
                                    || (n = "positiveInteger"))
                                   || (n = "unsignedLong"))
                                  || (n = "unsignedInt"))
                                 || (n = "unsignedShort"))
                                || (n = "unsignedByte"))
                               || (n = "nonPositiveInteger"))
                              || (n = "negativeInteger"))
                             || (n = "double"))
                            || (n = "duration"))
                           || (n = "dayTimeDuration"))
                          || (n = "yearMonthDuration"))
                         || (n = "float"))
                        || (n = "gDay"))
                       || (n = "gMonth"))
                      || (n = "gMonthDay"))
                     || (n = "gYear"))
                    || (n = "gYearMonth"))
                   || (n = "hexBinary"))
                  || (n = "QName"))
                 || (n = "string"))
                || (n = "normalizedString"))
               || (n = "token"))
              || (n = "language"))
             || (n = "Name"))
            || (n = "NMTOKEN"))
           || (n = "xml"))
          || (n = "html"))
         || (n = "json"))
        || (n = "time"))
       || (n = "number"))
      || (n = "binary"))
     || (n = "datetime"))
    || (n = "any")
let _cv_known_datatype_ref : Prims.string -> Prims.bool= cv_known_datatype
let cv_check_column (v : Parser_JSON.json_val) : Prims.string Prims.list=
  FStar_List_Tot_Base.op_At (cv_check_id "Column" v)
    (FStar_List_Tot_Base.op_At (cv_check_type "Column" v) (cv_check_titles v))
let rec cv_check_columns (xs : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list=
  match xs with
  | [] -> []
  | c::tl ->
      FStar_List_Tot_Base.op_At (cv_check_column c) (cv_check_columns tl)
let cv_check_schema (v : Parser_JSON.json_val) : Prims.string Prims.list=
  let base =
    FStar_List_Tot_Base.op_At (cv_check_id "Schema" v)
      (cv_check_type "Schema" v) in
  let cols =
    match cv_field "columns" v with
    | FStar_Pervasives_Native.Some (Parser_JSON.JArray xs) ->
        cv_check_columns xs
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some uu___ -> ["columns must be an array"] in
  FStar_List_Tot_Base.op_At base cols
let cv_check_dialect (v : Parser_JSON.json_val) : Prims.string Prims.list=
  match cv_field "dialect" v with
  | FStar_Pervasives_Native.Some d ->
      FStar_List_Tot_Base.op_At (cv_check_id "Dialect" d)
        (cv_check_type "Dialect" d)
  | FStar_Pervasives_Native.None -> []
let cv_check_table (v : Parser_JSON.json_val) : Prims.string Prims.list=
  let idt =
    FStar_List_Tot_Base.op_At (cv_check_id "Table" v)
      (cv_check_type "Table" v) in
  let url =
    if cv_has "url" v
    then []
    else ["Table is missing the required url property"] in
  let sch =
    match cv_field "tableSchema" v with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some s ->
        (match s with
         | Parser_JSON.JObject uu___ -> cv_check_schema s
         | Parser_JSON.JString uu___ -> []
         | uu___ -> ["tableSchema must be an object or string"]) in
  let dia = cv_check_dialect v in
  FStar_List_Tot_Base.op_At idt
    (FStar_List_Tot_Base.op_At url (FStar_List_Tot_Base.op_At sch dia))
let rec cv_check_tables (xs : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list=
  match xs with
  | [] -> []
  | t::tl ->
      FStar_List_Tot_Base.op_At
        (match t with
         | Parser_JSON.JObject uu___ -> cv_check_table t
         | uu___ -> []) (cv_check_tables tl)
let csvw_validate_metadata_json (root : Parser_JSON.json_val) :
  Prims.string Prims.list=
  if Prims.op_Negation (cv_is_object root)
  then ["metadata is not a JSON object"]
  else
    (match cv_field "tables" root with
     | FStar_Pervasives_Native.Some (Parser_JSON.JArray ts) ->
         let g =
           FStar_List_Tot_Base.op_At (cv_check_id "TableGroup" root)
             (cv_check_type "TableGroup" root) in
         let empty =
           match ts with | [] -> ["TableGroup has no tables"] | uu___1 -> [] in
         FStar_List_Tot_Base.op_At g
           (FStar_List_Tot_Base.op_At empty (cv_check_tables ts))
     | FStar_Pervasives_Native.Some uu___1 -> ["tables must be an array"]
     | FStar_Pervasives_Native.None -> cv_check_table root)
let cv_cell_valid (spec : CSVW_Conversion.csvw_col_spec) (txt : Prims.string)
  : Prims.bool=
  let is_null =
    (txt = "") ||
      (match spec.CSVW_Conversion.cs_null with
       | FStar_Pervasives_Native.Some n -> txt = n
       | FStar_Pervasives_Native.None -> false) in
  if is_null
  then true
  else
    (let dt_str =
       CSVW_Conversion.csvw_datatype_iri spec.CSVW_Conversion.cs_datatype in
     if Prims.op_Negation (RDF_Term.is_iri dt_str)
     then true
     else
       (let base_name =
          CSVW_Conversion.csvw_dt_base_name_of
            spec.CSVW_Conversion.cs_datatype in
        let uu___2 =
          CSVW_Conversion.csvw_dt_format_facets
            spec.CSVW_Conversion.cs_datatype in
        match uu___2 with
        | (fmt_str, pat, grp, dec) ->
            (CSVW_Formats.csvw_string_format_ok base_name fmt_str txt) &&
              ((match CSVW_Formats.csvw_format_convert base_name fmt_str pat
                        grp dec txt
                with
                | CSVW_Formats.FO_Invalid -> false
                | CSVW_Formats.FO_Valid canonical ->
                    (Prims.op_Negation
                       (XSD_Datatypes.literal_ill_formed dt_str canonical))
                      &&
                      (CSVW_Conversion.csvw_value_satisfies base_name
                         canonical spec.CSVW_Conversion.cs_datatype)
                | CSVW_Formats.FO_NoFormat ->
                    (Prims.op_Negation
                       (XSD_Datatypes.literal_ill_formed dt_str txt))
                      &&
                      (CSVW_Conversion.csvw_value_satisfies base_name txt
                         spec.CSVW_Conversion.cs_datatype)))))
let rec cv_check_cells (spec : CSVW_Conversion.csvw_col_spec)
  (cells : Prims.string Prims.list) : Prims.string Prims.list=
  match cells with
  | [] -> []
  | txt::tl ->
      let parts =
        match spec.CSVW_Conversion.cs_separator with
        | FStar_Pervasives_Native.Some sep ->
            CSVW_Conversion.csvw_split_list_cell sep txt
        | FStar_Pervasives_Native.None -> [txt] in
      let here =
        FStar_List_Tot_Base.collect
          (fun part ->
             if cv_cell_valid spec part
             then []
             else
               [Prims.strcat "invalid value in column "
                  (Prims.strcat spec.CSVW_Conversion.cs_name
                     (Prims.strcat ": " part))]) parts in
      FStar_List_Tot_Base.op_At here (cv_check_cells spec tl)
let cv_transpose (specs : CSVW_Conversion.csvw_col_spec Prims.list)
  (rows : Prims.string Prims.list Prims.list) :
  (CSVW_Conversion.csvw_col_spec * Prims.string Prims.list) Prims.list=
  let n = FStar_List_Tot_Base.length specs in
  let indexed = CSVW_Conversion.csvw_index_from Prims.int_zero specs in
  FStar_List_Tot_Base.map
    (fun p ->
       let uu___ = p in
       match uu___ with
       | (i, spec) ->
           (spec,
             (FStar_List_Tot_Base.map
                (fun r ->
                   match FStar_List_Tot_Base.nth r i with
                   | FStar_Pervasives_Native.Some c -> c
                   | FStar_Pervasives_Native.None -> "") rows))) indexed
let rec cv_has_dup (seen : Prims.string Prims.list)
  (xs : Prims.string Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | x::tl -> (FStar_List_Tot_Base.mem x seen) || (cv_has_dup (x :: seen) tl)
let cv_check_primary_key
  (cols :
    (CSVW_Conversion.csvw_col_spec * Prims.string Prims.list) Prims.list)
  (pk : Prims.string FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  match pk with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some name ->
      (match FStar_List_Tot_Base.find
               (fun p ->
                  (FStar_Pervasives_Native.fst p).CSVW_Conversion.cs_name =
                    name) cols
       with
       | FStar_Pervasives_Native.Some (uu___, vals) ->
           if cv_has_dup [] vals
           then [Prims.strcat "duplicate primaryKey value in column " name]
           else []
       | FStar_Pervasives_Native.None -> [])
let cv_col_is_virtual (c : CSVW_Metadata.csvw_column) : Prims.bool=
  match c.CSVW_Metadata.col_virtual with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let cv_col_required (c : CSVW_Metadata.csvw_column) : Prims.bool=
  match c.CSVW_Metadata.col_required with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let rec cv_required_cells (spec : CSVW_Conversion.csvw_col_spec)
  (vals : Prims.string Prims.list) : Prims.string Prims.list=
  match vals with
  | [] -> []
  | v::tl ->
      let is_null =
        (v = "") ||
          (match spec.CSVW_Conversion.cs_null with
           | FStar_Pervasives_Native.Some n -> v = n
           | FStar_Pervasives_Native.None -> false) in
      let here =
        if is_null
        then
          [Prims.strcat "required column "
             (Prims.strcat spec.CSVW_Conversion.cs_name
                " has a null/empty cell")]
        else [] in
      FStar_List_Tot_Base.op_At here (cv_required_cells spec tl)
let rec cv_check_required (cols_meta : CSVW_Metadata.csvw_column Prims.list)
  (cols_data :
    (CSVW_Conversion.csvw_col_spec * Prims.string Prims.list) Prims.list)
  : Prims.string Prims.list=
  match (cols_meta, cols_data) with
  | (c::mt, (spec, vals)::dt) ->
      let here =
        if cv_col_required c then cv_required_cells spec vals else [] in
      FStar_List_Tot_Base.op_At here (cv_check_required mt dt)
  | (uu___, uu___1) -> []
let cv_lang_match (a : Prims.string) (b : Prims.string) : Prims.bool=
  (((a = b) || (a = "und")) || (b = "und")) ||
    (let la = FStar_String.strlen a in
     let lb = FStar_String.strlen b in
     if la <= lb
     then (FStar_String.sub b Prims.int_zero la) = a
     else (FStar_String.sub a Prims.int_zero lb) = b)
let rec cv_title_compat (dl : Prims.string)
  (cols_meta : CSVW_Metadata.csvw_column Prims.list)
  (header : Prims.string Prims.list) : Prims.string Prims.list=
  match (cols_meta, header) with
  | (c::mt, h::ht) ->
      let ht0 = CSVW_Conversion.csvw_trim h in
      let here =
        match c.CSVW_Metadata.col_titles_l with
        | uu___::uu___1 ->
            if
              FStar_List_Tot_Base.existsb
                (fun tl ->
                   let uu___2 = tl in
                   match uu___2 with
                   | (t, lo) ->
                       ((CSVW_Conversion.csvw_trim t) = ht0) &&
                         (cv_lang_match
                            (match lo with
                             | FStar_Pervasives_Native.Some l -> l
                             | FStar_Pervasives_Native.None -> dl) dl))
                c.CSVW_Metadata.col_titles_l
            then []
            else
              [Prims.strcat "column title incompatible with CSV header: " ht0]
        | [] ->
            (match c.CSVW_Metadata.col_name with
             | FStar_Pervasives_Native.Some n ->
                 if n = (CSVW_Conversion.csvw_encode_name ht0)
                 then []
                 else
                   [Prims.strcat "column name incompatible with CSV header: "
                      ht0]
             | FStar_Pervasives_Native.None -> []) in
      FStar_List_Tot_Base.op_At here (cv_title_compat dl mt ht)
  | (uu___, uu___1) -> []
let cv_pk_names_of_raw (tblj : Parser_JSON.json_val) :
  Prims.string Prims.list=
  match cv_field "tableSchema" tblj with
  | FStar_Pervasives_Native.Some ts ->
      (match cv_field "primaryKey" ts with
       | FStar_Pervasives_Native.Some (Parser_JSON.JArray xs) ->
           FStar_List_Tot_Base.choose
             (fun x ->
                match x with
                | Parser_JSON.JString s -> FStar_Pervasives_Native.Some s
                | uu___ -> FStar_Pervasives_Native.None) xs
       | uu___ -> [])
  | FStar_Pervasives_Native.None -> []
let cv_find_raw_table (root : Parser_JSON.json_val)
  (url : Prims.string FStar_Pervasives_Native.option) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match cv_field "tables" root with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray ts) ->
      (match FStar_List_Tot_Base.find
               (fun t ->
                  match ((cv_field "url" t), url) with
                  | (FStar_Pervasives_Native.Some (Parser_JSON.JString u),
                     FStar_Pervasives_Native.Some u2) -> u = u2
                  | (uu___, uu___1) -> false) ts
       with
       | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.Some root
let rec cv_zip_join (fuel : Prims.nat)
  (cols : Prims.string Prims.list Prims.list) : Prims.string Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    if FStar_List_Tot_Base.existsb Prims.uu___is_Nil cols
    then []
    else
      (let heads =
         FStar_List_Tot_Base.map
           (fun c -> match c with | h::uu___2 -> h | [] -> "") cols in
       let tails =
         FStar_List_Tot_Base.map
           (fun c -> match c with | uu___2::t -> t | [] -> []) cols in
       (FStar_String.concat "~|~" heads) ::
         (cv_zip_join (fuel - Prims.int_one) tails))
let cv_check_composite_pk
  (cols :
    (CSVW_Conversion.csvw_col_spec * Prims.string Prims.list) Prims.list)
  (pk_names : Prims.string Prims.list) : Prims.string Prims.list=
  if (FStar_List_Tot_Base.length pk_names) < (Prims.of_int (2))
  then []
  else
    (let pk_val_lists =
       FStar_List_Tot_Base.choose
         (fun name ->
            match FStar_List_Tot_Base.find
                    (fun p ->
                       (FStar_Pervasives_Native.fst p).CSVW_Conversion.cs_name
                         = name) cols
            with
            | FStar_Pervasives_Native.Some (uu___1, vals) ->
                FStar_Pervasives_Native.Some vals
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         pk_names in
     if
       (FStar_List_Tot_Base.length pk_val_lists) <>
         (FStar_List_Tot_Base.length pk_names)
     then []
     else
       (let nrows =
          match pk_val_lists with
          | c::uu___2 -> FStar_List_Tot_Base.length c
          | [] -> Prims.int_zero in
        if cv_has_dup [] (cv_zip_join nrows pk_val_lists)
        then ["duplicate multi-column primaryKey"]
        else []))
let cv_check_data_table (root : Parser_JSON.json_val)
  (default_lang : Prims.string)
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string) (fallback_url : Prims.string)
  (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) : Prims.string Prims.list=
  let table_url_resolved =
    CSVW_Conversion.csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_cols_n = CSVW_Conversion.csvw_skip_columns_count dia in
  let all_rows1 =
    FStar_List_Tot_Base.map (CSVW_Conversion.csvw_drop skip_cols_n) all_rows in
  let after_skip_rows =
    CSVW_Conversion.csvw_drop (CSVW_Conversion.csvw_skip_rows_count dia)
      all_rows1 in
  let data_rows =
    CSVW_Conversion.csvw_drop (CSVW_Conversion.csvw_header_row_count dia)
      after_skip_rows in
  let header_cells =
    if (CSVW_Conversion.csvw_header_row_count dia) > Prims.int_zero
    then match after_skip_rows with | h::uu___ -> h | [] -> []
    else
      (match tbl.CSVW_Metadata.tbl_table_schema with
       | FStar_Pervasives_Native.Some uu___1 -> []
       | FStar_Pervasives_Native.None ->
           (match data_rows with
            | r::uu___1 -> FStar_List_Tot_Base.map (fun uu___2 -> "") r
            | [] -> [])) in
  let col_specs =
    CSVW_Conversion.csvw_build_col_specs grp_inherited
      tbl.CSVW_Metadata.tbl_inherited tbl.CSVW_Metadata.tbl_table_schema
      header_cells in
  let phys_specs =
    FStar_List_Tot_Base.filter
      (fun s -> Prims.op_Negation s.CSVW_Conversion.cs_virtual) col_specs in
  let cols = cv_transpose phys_specs data_rows in
  let cell_errs =
    FStar_List_Tot_Base.collect
      (fun p ->
         cv_check_cells (FStar_Pervasives_Native.fst p)
           (FStar_Pervasives_Native.snd p)) cols in
  let pk =
    match tbl.CSVW_Metadata.tbl_table_schema with
    | FStar_Pervasives_Native.Some ts -> ts.CSVW_Metadata.ts_primary_key
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let pk_names =
    match cv_find_raw_table root tbl.CSVW_Metadata.tbl_url with
    | FStar_Pervasives_Native.Some tj -> cv_pk_names_of_raw tj
    | FStar_Pervasives_Native.None -> [] in
  let composite_pk = cv_check_composite_pk cols pk_names in
  let declared =
    match tbl.CSVW_Metadata.tbl_table_schema with
    | FStar_Pervasives_Native.Some ts -> ts.CSVW_Metadata.ts_columns
    | FStar_Pervasives_Native.None -> [] in
  let declared_nonvirt =
    FStar_List_Tot_Base.filter
      (fun c -> Prims.op_Negation (cv_col_is_virtual c)) declared in
  let actual_width =
    if Prims.uu___is_Cons header_cells
    then FStar_List_Tot_Base.length header_cells
    else
      (match data_rows with
       | r::uu___1 -> FStar_List_Tot_Base.length r
       | [] -> Prims.int_zero) in
  let compat =
    if
      ((Prims.uu___is_Cons declared_nonvirt) &&
         (actual_width > Prims.int_zero))
        && ((FStar_List_Tot_Base.length declared_nonvirt) <> actual_width)
    then
      [Prims.strcat "schema declares "
         (Prims.strcat
            (Prims.string_of_int
               (FStar_List_Tot_Base.length declared_nonvirt))
            (Prims.strcat " non-virtual columns but the data has "
               (Prims.string_of_int actual_width)))]
    else [] in
  let req =
    if compat = [] then cv_check_required declared_nonvirt cols else [] in
  let title_compat =
    if (compat = []) && (Prims.uu___is_Cons header_cells)
    then
      let table_lang =
        match (tbl.CSVW_Metadata.tbl_inherited).CSVW_Metadata.inh_lang with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (match grp_inherited.CSVW_Metadata.inh_lang with
             | FStar_Pervasives_Native.Some l -> l
             | FStar_Pervasives_Native.None -> default_lang) in
      cv_title_compat table_lang declared_nonvirt header_cells
    else [] in
  FStar_List_Tot_Base.op_At cell_errs
    (FStar_List_Tot_Base.op_At (cv_check_primary_key cols pk)
       (FStar_List_Tot_Base.op_At composite_pk
          (FStar_List_Tot_Base.op_At compat
             (FStar_List_Tot_Base.op_At req title_compat))))
let cv_col_ref_names
  (v : Parser_JSON.json_val FStar_Pervasives_Native.option) :
  Prims.string Prims.list=
  match v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) -> [s]
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray xs) ->
      FStar_List_Tot_Base.choose
        (fun x ->
           match x with
           | Parser_JSON.JString s -> FStar_Pervasives_Native.Some s
           | uu___ -> FStar_Pervasives_Native.None) xs
  | uu___ -> []
let rec cv_assoc_j (k : Prims.string)
  (xs : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.None
  | (k2, v)::tl ->
      if k2 = k then FStar_Pervasives_Native.Some v else cv_assoc_j k tl
let cv_inline_one_table
  (schemas : (Prims.string * Parser_JSON.json_val) Prims.list)
  (t : Parser_JSON.json_val) : Parser_JSON.json_val=
  match cv_field "tableSchema" t with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString url) ->
      (match cv_assoc_j url schemas with
       | FStar_Pervasives_Native.Some sj -> cv_set_field "tableSchema" sj t
       | FStar_Pervasives_Native.None -> t)
  | uu___ -> t
let cv_inline_schema_refs (root : Parser_JSON.json_val)
  (schemas : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Parser_JSON.json_val=
  match cv_field "tables" root with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray ts) ->
      cv_set_field "tables"
        (Parser_JSON.JArray
           (FStar_List_Tot_Base.map (cv_inline_one_table schemas) ts)) root
  | uu___ -> cv_inline_one_table schemas root
let cv_basename (s : Prims.string) : Prims.string=
  match FStar_List_Tot_Base.rev (FStar_String.split [47] s) with
  | h::uu___ -> h
  | [] -> s
let rec cv_assoc_s (k : Prims.string)
  (xs : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.None
  | (k2, v)::tl ->
      if k2 = k then FStar_Pervasives_Native.Some v else cv_assoc_s k tl
let cv_read_fks (schemaref_map : (Prims.string * Prims.string) Prims.list)
  (tblj : Parser_JSON.json_val) :
  (Prims.string Prims.list * Prims.string * Prims.string Prims.list)
    Prims.list=
  match cv_field "tableSchema" tblj with
  | FStar_Pervasives_Native.Some ts ->
      (match cv_field "foreignKeys" ts with
       | FStar_Pervasives_Native.Some (Parser_JSON.JArray fks) ->
           FStar_List_Tot_Base.choose
             (fun fk ->
                let local = cv_col_ref_names (cv_field "columnReference" fk) in
                match cv_field "reference" fk with
                | FStar_Pervasives_Native.Some refj ->
                    let refcols =
                      cv_col_ref_names (cv_field "columnReference" refj) in
                    let res =
                      match Parser_JSON.json_get_string "resource" refj with
                      | FStar_Pervasives_Native.Some r ->
                          FStar_Pervasives_Native.Some r
                      | FStar_Pervasives_Native.None ->
                          (match Parser_JSON.json_get_string
                                   "schemaReference" refj
                           with
                           | FStar_Pervasives_Native.Some sr ->
                               cv_assoc_s (cv_basename sr) schemaref_map
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None) in
                    (match res with
                     | FStar_Pervasives_Native.Some r ->
                         FStar_Pervasives_Native.Some (local, r, refcols)
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None)
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None) fks
       | uu___ -> [])
  | FStar_Pervasives_Native.None -> []
let cv_table_cols (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string) (fallback_url : Prims.string)
  (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) :
  (CSVW_Conversion.csvw_col_spec * Prims.string Prims.list) Prims.list=
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_cols_n = CSVW_Conversion.csvw_skip_columns_count dia in
  let all_rows1 =
    FStar_List_Tot_Base.map (CSVW_Conversion.csvw_drop skip_cols_n) all_rows in
  let after_skip_rows =
    CSVW_Conversion.csvw_drop (CSVW_Conversion.csvw_skip_rows_count dia)
      all_rows1 in
  let data_rows =
    CSVW_Conversion.csvw_drop (CSVW_Conversion.csvw_header_row_count dia)
      after_skip_rows in
  let header_cells =
    if (CSVW_Conversion.csvw_header_row_count dia) > Prims.int_zero
    then match after_skip_rows with | h::uu___ -> h | [] -> []
    else
      (match tbl.CSVW_Metadata.tbl_table_schema with
       | FStar_Pervasives_Native.Some uu___1 -> []
       | FStar_Pervasives_Native.None ->
           (match data_rows with
            | r::uu___1 -> FStar_List_Tot_Base.map (fun uu___2 -> "") r
            | [] -> [])) in
  let col_specs =
    CSVW_Conversion.csvw_build_col_specs grp_inherited
      tbl.CSVW_Metadata.tbl_inherited tbl.CSVW_Metadata.tbl_table_schema
      header_cells in
  let phys_specs =
    FStar_List_Tot_Base.filter
      (fun s -> Prims.op_Negation s.CSVW_Conversion.cs_virtual) col_specs in
  cv_transpose phys_specs data_rows
let cv_composite_of
  (cols :
    (CSVW_Conversion.csvw_col_spec * Prims.string Prims.list) Prims.list)
  (names : Prims.string Prims.list) : Prims.string Prims.list=
  let vlists =
    FStar_List_Tot_Base.choose
      (fun name ->
         match FStar_List_Tot_Base.find
                 (fun p ->
                    (FStar_Pervasives_Native.fst p).CSVW_Conversion.cs_name =
                      name) cols
         with
         | FStar_Pervasives_Native.Some (uu___, vals) ->
             FStar_Pervasives_Native.Some vals
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      names in
  if
    ((FStar_List_Tot_Base.length vlists) = (FStar_List_Tot_Base.length names))
      && (Prims.uu___is_Cons vlists)
  then
    cv_zip_join
      (match vlists with
       | c::uu___ -> FStar_List_Tot_Base.length c
       | [] -> Prims.int_zero) vlists
  else []
let cv_find_table_by_resource
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  (resource : Prims.string) :
  (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
    Prims.list) FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun t ->
             let uu___ = t in
             match uu___ with
             | (tbl, uu___1, uu___2) ->
                 (match tbl.CSVW_Metadata.tbl_url with
                  | FStar_Pervasives_Native.Some u -> u = resource
                  | FStar_Pervasives_Native.None -> false)) tables_with_rows
  with
  | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let cv_check_table_fks (root : Parser_JSON.json_val)
  (schemaref_map : (Prims.string * Prims.string) Prims.list)
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string)
  (all_tables :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  (tbl : CSVW_Metadata.csvw_table) (fallback_url : Prims.string)
  (rows : Prims.string Prims.list Prims.list) : Prims.string Prims.list=
  match cv_find_raw_table root tbl.CSVW_Metadata.tbl_url with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some tj ->
      let fks = cv_read_fks schemaref_map tj in
      let local_cols =
        cv_table_cols grp_inherited base_iri fallback_url tbl rows in
      FStar_List_Tot_Base.collect
        (fun fk ->
           let uu___ = fk in
           match uu___ with
           | (local_names, resource, ref_names) ->
               (match cv_find_table_by_resource all_tables resource with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some (ttbl, tfallback, trows) ->
                    let target_cols =
                      cv_table_cols grp_inherited base_iri tfallback ttbl
                        trows in
                    let local_vals = cv_composite_of local_cols local_names in
                    let ref_vals = cv_composite_of target_cols ref_names in
                    FStar_List_Tot_Base.collect
                      (fun lv ->
                         if lv = ""
                         then []
                         else
                           (let n =
                              FStar_List_Tot_Base.length
                                (FStar_List_Tot_Base.filter (fun v -> v = lv)
                                   ref_vals) in
                            if n = Prims.int_zero
                            then
                              [Prims.strcat
                                 "foreign key value has no referenced row: "
                                 lv]
                            else
                              if n > Prims.int_one
                              then
                                [Prims.strcat
                                   "foreign key value references multiple rows: "
                                   lv]
                              else [])) local_vals)) fks
let cv_check_data (root : Parser_JSON.json_val)
  (schemaref_map : (Prims.string * Prims.string) Prims.list)
  (default_lang : Prims.string)
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : Prims.string Prims.list=
  let per_table =
    FStar_List_Tot_Base.collect
      (fun t ->
         let uu___ = t in
         match uu___ with
         | (tbl, fallback_url, rows) ->
             if CSVW_Conversion.csvw_table_suppressed tbl
             then []
             else
               cv_check_data_table root default_lang grp_inherited base_iri
                 fallback_url tbl rows) tables_with_rows in
  let fk_errs =
    FStar_List_Tot_Base.collect
      (fun t ->
         let uu___ = t in
         match uu___ with
         | (tbl, fallback_url, rows) ->
             if CSVW_Conversion.csvw_table_suppressed tbl
             then []
             else
               cv_check_table_fks root schemaref_map grp_inherited base_iri
                 tables_with_rows tbl fallback_url rows) tables_with_rows in
  FStar_List_Tot_Base.op_At per_table fk_errs
