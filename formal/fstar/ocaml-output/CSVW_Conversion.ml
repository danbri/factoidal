open Prims
let csvw_ns : Prims.string= "http://www.w3.org/ns/csvw#"
let csvw_TableGroup : RDF_Term.wf_iri= Prims.strcat csvw_ns "TableGroup"
let csvw_Table : RDF_Term.wf_iri= Prims.strcat csvw_ns "Table"
let csvw_Row : RDF_Term.wf_iri= Prims.strcat csvw_ns "Row"
let csvw_table_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "table"
let csvw_row_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "row"
let csvw_rownum : RDF_Term.wf_iri= Prims.strcat csvw_ns "rownum"
let csvw_url_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "url"
let csvw_describes : RDF_Term.wf_iri= Prims.strcat csvw_ns "describes"
let csvw_note_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "note"
let csvw_base_name_to_iri (n : Prims.string) : Prims.string=
  if n = "html"
  then "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML"
  else
    if n = "xml"
    then "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
    else
      if n = "json"
      then Prims.strcat csvw_ns "JSON"
      else
        if n = "number"
        then "http://www.w3.org/2001/XMLSchema#double"
        else
          if n = "binary"
          then "http://www.w3.org/2001/XMLSchema#base64Binary"
          else
            if n = "datetime"
            then "http://www.w3.org/2001/XMLSchema#dateTime"
            else
              if n = "any"
              then "http://www.w3.org/2001/XMLSchema#anyAtomicType"
              else
                if RDF_Term.string_contains_colon n
                then n
                else Prims.strcat "http://www.w3.org/2001/XMLSchema#" n
let csvw_datatype_iri
  (dt : CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option) :
  Prims.string=
  match dt with
  | FStar_Pervasives_Native.None -> RDF_Term.xsd_string
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Named n) ->
      csvw_base_name_to_iri n
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Object
      (base_opt, uu___, uu___1, uu___2, uu___3, dtid, uu___4, uu___5, uu___6,
       uu___7, uu___8, uu___9, uu___10, uu___11, uu___12))
      ->
      let from_base =
        match base_opt with
        | FStar_Pervasives_Native.Some n -> csvw_base_name_to_iri n
        | FStar_Pervasives_Native.None -> RDF_Term.xsd_string in
      (match dtid with
       | FStar_Pervasives_Native.Some idurl ->
           if RDF_Term.string_contains_colon idurl then idurl else from_base
       | FStar_Pervasives_Native.None -> from_base)
let csvw_dt_base_name_of
  (dt : CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option) :
  Prims.string=
  match dt with
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Named n) -> n
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Object
      (bo, uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6, uu___7,
       uu___8, uu___9, uu___10, uu___11, uu___12, uu___13))
      ->
      (match bo with
       | FStar_Pervasives_Native.Some n -> n
       | FStar_Pervasives_Native.None -> "string")
  | FStar_Pervasives_Native.None -> "string"
let csvw_dt_format_facets
  (dt : CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)=
  match dt with
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Object
      (uu___, fmt, pat, grp, dec, uu___1, uu___2, uu___3, uu___4, uu___5,
       uu___6, uu___7, uu___8, uu___9, uu___10))
      -> (fmt, pat, grp, dec)
  | uu___ ->
      (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
        FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
let csvw_dt_value_facets
  (dt : CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option) :
  (Prims.int FStar_Pervasives_Native.option * Prims.int
    FStar_Pervasives_Native.option * Prims.int FStar_Pervasives_Native.option
    * Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)=
  match dt with
  | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_DT_Object
      (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, len, minl, maxl, mn,
       mx, mni, mxi, mne, mxe))
      -> (len, minl, maxl, mn, mx, mni, mxi, mne, mxe)
  | uu___ ->
      (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
        FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
        FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
        FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
        FStar_Pervasives_Native.None)
let csvw_is_binary_base (n : Prims.string) : Prims.bool=
  ((n = "base64Binary") || (n = "hexBinary")) || (n = "binary")
let csvw_is_numeric_base (n : Prims.string) : Prims.bool=
  ((((((((((((((((n = "number") || (n = "decimal")) || (n = "integer")) ||
                 (n = "long"))
                || (n = "int"))
               || (n = "short"))
              || (n = "byte"))
             || (n = "nonNegativeInteger"))
            || (n = "positiveInteger"))
           || (n = "nonPositiveInteger"))
          || (n = "negativeInteger"))
         || (n = "unsignedLong"))
        || (n = "unsignedInt"))
       || (n = "unsignedShort"))
      || (n = "unsignedByte"))
     || (n = "double"))
    || (n = "float")
let rec csvw_conv_chars_cmp (a : FStar_Char.char Prims.list)
  (b : FStar_Char.char Prims.list) : Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      let ix = FStar_Char.int_of_char x in
      let iy = FStar_Char.int_of_char y in
      if ix < iy
      then (Prims.of_int (-1))
      else if ix > iy then Prims.int_one else csvw_conv_chars_cmp xs ys
let csvw_conv_str_cmp (a : Prims.string) (b : Prims.string) : Prims.int=
  csvw_conv_chars_cmp (FStar_String.list_of_string a)
    (FStar_String.list_of_string b)
let csvw_num_cmp (a : Prims.string) (b : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let pa =
    match XSD_Datatypes.parse_double_to_scaled a with
    | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
    | FStar_Pervasives_Native.None -> XSD_Datatypes.parse_to_scaled a in
  let pb =
    match XSD_Datatypes.parse_double_to_scaled b with
    | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
    | FStar_Pervasives_Native.None -> XSD_Datatypes.parse_to_scaled b in
  match (pa, pb) with
  | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
      FStar_Pervasives_Native.Some (XSD_Datatypes.scaled_cmp sa sb)
  | uu___ -> FStar_Pervasives_Native.None
let csvw_cell_cmp (numeric : Prims.bool) (a : Prims.string)
  (b : Prims.string) : Prims.int FStar_Pervasives_Native.option=
  if numeric
  then csvw_num_cmp a b
  else FStar_Pervasives_Native.Some (csvw_conv_str_cmp a b)
let csvw_value_satisfies (base_name : Prims.string) (text : Prims.string)
  (dt : CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option) :
  Prims.bool=
  let uu___ = csvw_dt_value_facets dt in
  match uu___ with
  | (len, minl, maxl, mn, mx, mni, mxi, mne, mxe) ->
      let n = FStar_String.strlen text in
      let len_ok =
        if csvw_is_binary_base base_name
        then true
        else
          ((match len with
            | FStar_Pervasives_Native.Some l -> n = l
            | FStar_Pervasives_Native.None -> true) &&
             (match minl with
              | FStar_Pervasives_Native.Some l -> n >= l
              | FStar_Pervasives_Native.None -> true))
            &&
            ((match maxl with
              | FStar_Pervasives_Native.Some l -> n <= l
              | FStar_Pervasives_Native.None -> true)) in
      let numeric = csvw_is_numeric_base base_name in
      let eff_min_incl =
        match mni with
        | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some x
        | FStar_Pervasives_Native.None -> mn in
      let eff_max_incl =
        match mxi with
        | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some x
        | FStar_Pervasives_Native.None -> mx in
      let vc_ok =
        (((match eff_min_incl with
           | FStar_Pervasives_Native.Some c ->
               (match csvw_cell_cmp numeric text c with
                | FStar_Pervasives_Native.Some r -> r >= Prims.int_zero
                | FStar_Pervasives_Native.None -> true)
           | FStar_Pervasives_Native.None -> true) &&
            (match eff_max_incl with
             | FStar_Pervasives_Native.Some c ->
                 (match csvw_cell_cmp numeric text c with
                  | FStar_Pervasives_Native.Some r -> r <= Prims.int_zero
                  | FStar_Pervasives_Native.None -> true)
             | FStar_Pervasives_Native.None -> true))
           &&
           (match mne with
            | FStar_Pervasives_Native.Some c ->
                (match csvw_cell_cmp numeric text c with
                 | FStar_Pervasives_Native.Some r -> r > Prims.int_zero
                 | FStar_Pervasives_Native.None -> true)
            | FStar_Pervasives_Native.None -> true))
          &&
          (match mxe with
           | FStar_Pervasives_Native.Some c ->
               (match csvw_cell_cmp numeric text c with
                | FStar_Pervasives_Native.Some r -> r < Prims.int_zero
                | FStar_Pervasives_Native.None -> true)
           | FStar_Pervasives_Native.None -> true) in
      len_ok && vc_ok
let csvw_build_literal (lex : Prims.string) (dt : Prims.string) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if RDF_Term.is_iri dt
  then
    let l =
      {
        RDF_Term.lexical_form = lex;
        RDF_Term.datatype = dt;
        RDF_Term.lang_tag = FStar_Pervasives_Native.None;
        RDF_Term.direction = FStar_Pervasives_Native.None
      } in
    (if RDF_Term.literal_wf l
     then FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let csvw_build_literal_lang (lex : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match (lang, (dt = RDF_Term.xsd_string)) with
  | (FStar_Pervasives_Native.Some l, true) ->
      let lit =
        {
          RDF_Term.lexical_form = lex;
          RDF_Term.datatype = RDF_Term.rdf_lang_string;
          RDF_Term.lang_tag = (FStar_Pervasives_Native.Some l);
          RDF_Term.direction = FStar_Pervasives_Native.None
        } in
      if RDF_Term.literal_wf lit
      then FStar_Pervasives_Native.Some (RDF_Term.T_Literal lit)
      else FStar_Pervasives_Native.None
  | uu___ -> csvw_build_literal lex dt
let rdf_first_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Term.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let csvw_title_pred : RDF_Term.wf_iri= Prims.strcat csvw_ns "title"
let csvw_curie_ns (prefix : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if prefix = "rdf"
  then
    FStar_Pervasives_Native.Some
      "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  else
    if prefix = "rdfs"
    then FStar_Pervasives_Native.Some "http://www.w3.org/2000/01/rdf-schema#"
    else
      if prefix = "xsd"
      then FStar_Pervasives_Native.Some "http://www.w3.org/2001/XMLSchema#"
      else
        if prefix = "dc"
        then FStar_Pervasives_Native.Some "http://purl.org/dc/terms/"
        else
          if prefix = "dcterms"
          then FStar_Pervasives_Native.Some "http://purl.org/dc/terms/"
          else
            if prefix = "dc11"
            then
              FStar_Pervasives_Native.Some "http://purl.org/dc/elements/1.1/"
            else
              if prefix = "dcat"
              then FStar_Pervasives_Native.Some "http://www.w3.org/ns/dcat#"
              else
                if prefix = "schema"
                then FStar_Pervasives_Native.Some "http://schema.org/"
                else
                  if prefix = "foaf"
                  then
                    FStar_Pervasives_Native.Some "http://xmlns.com/foaf/0.1/"
                  else
                    if prefix = "skos"
                    then
                      FStar_Pervasives_Native.Some
                        "http://www.w3.org/2004/02/skos/core#"
                    else
                      if prefix = "owl"
                      then
                        FStar_Pervasives_Native.Some
                          "http://www.w3.org/2002/07/owl#"
                      else
                        if prefix = "org"
                        then
                          FStar_Pervasives_Native.Some
                            "http://www.w3.org/ns/org#"
                        else
                          if prefix = "oa"
                          then
                            FStar_Pervasives_Native.Some
                              "http://www.w3.org/ns/oa#"
                          else
                            if prefix = "prov"
                            then
                              FStar_Pervasives_Native.Some
                                "http://www.w3.org/ns/prov#"
                            else
                              if prefix = "as"
                              then
                                FStar_Pervasives_Native.Some
                                  "https://www.w3.org/ns/activitystreams#"
                              else FStar_Pervasives_Native.None
let rec csvw_split_colon (chars : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (58))
      then FStar_Pervasives_Native.Some ([], rest)
      else
        (match csvw_split_colon rest with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (b, a) ->
             FStar_Pervasives_Native.Some ((c :: b), a))
let csvw_expand_curie (key : Prims.string) : Prims.string=
  match csvw_split_colon (FStar_String.list_of_string key) with
  | FStar_Pervasives_Native.None -> key
  | FStar_Pervasives_Native.Some (b, a) ->
      let local = FStar_String.string_of_list a in
      if
        ((FStar_String.strlen local) >= (Prims.of_int (2))) &&
          ((FStar_String.sub local Prims.int_zero (Prims.of_int (2))) = "//")
      then key
      else
        (match csvw_curie_ns (FStar_String.string_of_list b) with
         | FStar_Pervasives_Native.Some ns -> Prims.strcat ns local
         | FStar_Pervasives_Native.None -> key)
let csvw_builtin_type_term (t : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if
    (((((((((((((t = "TableGroup") || (t = "Table")) || (t = "Schema")) ||
                (t = "Column"))
               || (t = "Row"))
              || (t = "Dialect"))
             || (t = "Template"))
            || (t = "Datatype"))
           || (t = "Direction"))
          || (t = "ForeignKey"))
         || (t = "NumericFormat"))
        || (t = "TableReference"))
       || (t = "Cell"))
      || (t = "JSON")
  then FStar_Pervasives_Native.Some (Prims.strcat csvw_ns t)
  else FStar_Pervasives_Native.None
let csvw_expand_type_token (t : Prims.string) : Prims.string=
  match csvw_builtin_type_term t with
  | FStar_Pervasives_Native.Some iri -> iri
  | FStar_Pervasives_Native.None -> csvw_expand_curie t
type csvw_col_spec =
  {
  cs_name: Prims.string ;
  cs_virtual: Prims.bool ;
  cs_suppress: Prims.bool ;
  cs_datatype: CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option ;
  cs_about_url: Prims.string FStar_Pervasives_Native.option ;
  cs_property_url: Prims.string FStar_Pervasives_Native.option ;
  cs_value_url: Prims.string FStar_Pervasives_Native.option ;
  cs_separator: Prims.string FStar_Pervasives_Native.option ;
  cs_lang: Prims.string FStar_Pervasives_Native.option ;
  cs_null: Prims.string FStar_Pervasives_Native.option ;
  cs_default: Prims.string FStar_Pervasives_Native.option ;
  cs_ordered: Prims.bool }
let __proj__Mkcsvw_col_spec__item__cs_name (projectee : csvw_col_spec) :
  Prims.string=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_name
let __proj__Mkcsvw_col_spec__item__cs_virtual (projectee : csvw_col_spec) :
  Prims.bool=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_virtual
let __proj__Mkcsvw_col_spec__item__cs_suppress (projectee : csvw_col_spec) :
  Prims.bool=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_suppress
let __proj__Mkcsvw_col_spec__item__cs_datatype (projectee : csvw_col_spec) :
  CSVW_Metadata.csvw_datatype FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_datatype
let __proj__Mkcsvw_col_spec__item__cs_about_url (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_about_url
let __proj__Mkcsvw_col_spec__item__cs_property_url
  (projectee : csvw_col_spec) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_property_url
let __proj__Mkcsvw_col_spec__item__cs_value_url (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_value_url
let __proj__Mkcsvw_col_spec__item__cs_separator (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_separator
let __proj__Mkcsvw_col_spec__item__cs_lang (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_lang
let __proj__Mkcsvw_col_spec__item__cs_null (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_null
let __proj__Mkcsvw_col_spec__item__cs_default (projectee : csvw_col_spec) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_default
let __proj__Mkcsvw_col_spec__item__cs_ordered (projectee : csvw_col_spec) :
  Prims.bool=
  match projectee with
  | { cs_name; cs_virtual; cs_suppress; cs_datatype; cs_about_url;
      cs_property_url; cs_value_url; cs_separator; cs_lang; cs_null;
      cs_default; cs_ordered;_} -> cs_ordered
let csvw_opt_bool (o : Prims.bool FStar_Pervasives_Native.option) :
  Prims.bool=
  match o with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let csvw_merge_inherited (specific : CSVW_Metadata.csvw_inherited_props)
  (general : CSVW_Metadata.csvw_inherited_props) :
  CSVW_Metadata.csvw_inherited_props=
  {
    CSVW_Metadata.inh_about_url =
      (match specific.CSVW_Metadata.inh_about_url with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_about_url
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_about_url);
    CSVW_Metadata.inh_property_url =
      (match specific.CSVW_Metadata.inh_property_url with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_property_url
       | FStar_Pervasives_Native.None ->
           general.CSVW_Metadata.inh_property_url);
    CSVW_Metadata.inh_value_url =
      (match specific.CSVW_Metadata.inh_value_url with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_value_url
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_value_url);
    CSVW_Metadata.inh_lang =
      (match specific.CSVW_Metadata.inh_lang with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_lang
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_lang);
    CSVW_Metadata.inh_null =
      (match specific.CSVW_Metadata.inh_null with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_null
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_null);
    CSVW_Metadata.inh_separator =
      (match specific.CSVW_Metadata.inh_separator with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_separator
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_separator);
    CSVW_Metadata.inh_datatype =
      (match specific.CSVW_Metadata.inh_datatype with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_datatype
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_datatype);
    CSVW_Metadata.inh_ordered =
      (match specific.CSVW_Metadata.inh_ordered with
       | FStar_Pervasives_Native.Some uu___ ->
           specific.CSVW_Metadata.inh_ordered
       | FStar_Pervasives_Native.None -> general.CSVW_Metadata.inh_ordered)
  }
let csvw_varname_char_ok (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((((((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
        ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122)))))
       || ((n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))))
      || (n = (Prims.of_int (95))))
     || (n = (Prims.of_int (46))))
    || (n = (Prims.of_int (37)))
let csvw_valid_column_name (s : Prims.string) : Prims.bool=
  match FStar_String.list_of_string s with
  | [] -> false
  | c0::uu___ ->
      ((FStar_Char.int_of_char c0) <> (Prims.of_int (95))) &&
        (FStar_List_Tot_Base.for_all csvw_varname_char_ok
           (FStar_String.list_of_string s))
let csvw_positional_name (i : Prims.int) : Prims.string=
  Prims.strcat "_col." (Prims.string_of_int (i + Prims.int_one))
let csvw_title_lang_ok
  (default : Prims.string FStar_Pervasives_Native.option)
  (title : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  match title with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some tl ->
      (tl = "und") ||
        ((match default with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some dl -> (dl = "und") || (dl = tl)))
let rec csvw_first_matching_title
  (default : Prims.string FStar_Pervasives_Native.option)
  (ts :
    (Prims.string * Prims.string FStar_Pervasives_Native.option) Prims.list)
  : Prims.string FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.None
  | (txt, tl)::rest ->
      if csvw_title_lang_ok default tl
      then FStar_Pervasives_Native.Some txt
      else csvw_first_matching_title default rest
let csvw_name_from_titles (eff : CSVW_Metadata.csvw_inherited_props)
  (i : Prims.int) (c : CSVW_Metadata.csvw_column) : Prims.string=
  match c.CSVW_Metadata.col_titles_l with
  | [] -> ""
  | uu___ ->
      (match csvw_first_matching_title eff.CSVW_Metadata.inh_lang
               c.CSVW_Metadata.col_titles_l
       with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> csvw_positional_name i)
let csvw_col_spec_of_column (eff : CSVW_Metadata.csvw_inherited_props)
  (i : Prims.int) (c : CSVW_Metadata.csvw_column) : csvw_col_spec=
  {
    cs_name =
      (match c.CSVW_Metadata.col_name with
       | FStar_Pervasives_Native.Some n ->
           if csvw_valid_column_name n
           then n
           else csvw_name_from_titles eff i c
       | FStar_Pervasives_Native.None -> csvw_name_from_titles eff i c);
    cs_virtual = (csvw_opt_bool c.CSVW_Metadata.col_virtual);
    cs_suppress = (csvw_opt_bool c.CSVW_Metadata.col_suppress_output);
    cs_datatype =
      (match c.CSVW_Metadata.col_datatype with
       | FStar_Pervasives_Native.Some d -> FStar_Pervasives_Native.Some d
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_datatype);
    cs_about_url =
      (match c.CSVW_Metadata.col_about_url with
       | FStar_Pervasives_Native.Some a -> FStar_Pervasives_Native.Some a
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_about_url);
    cs_property_url =
      (match c.CSVW_Metadata.col_property_url with
       | FStar_Pervasives_Native.Some p -> FStar_Pervasives_Native.Some p
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_property_url);
    cs_value_url =
      (match c.CSVW_Metadata.col_value_url with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_value_url);
    cs_separator =
      (match c.CSVW_Metadata.col_separator with
       | FStar_Pervasives_Native.Some s -> FStar_Pervasives_Native.Some s
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_separator);
    cs_lang =
      (match c.CSVW_Metadata.col_lang with
       | FStar_Pervasives_Native.Some l -> FStar_Pervasives_Native.Some l
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_lang);
    cs_null =
      (match c.CSVW_Metadata.col_null with
       | FStar_Pervasives_Native.Some n -> FStar_Pervasives_Native.Some n
       | FStar_Pervasives_Native.None -> eff.CSVW_Metadata.inh_null);
    cs_default = (c.CSVW_Metadata.col_default);
    cs_ordered =
      (match c.CSVW_Metadata.col_ordered with
       | FStar_Pervasives_Native.Some b -> b
       | FStar_Pervasives_Native.None ->
           (match eff.CSVW_Metadata.inh_ordered with
            | FStar_Pervasives_Native.Some b -> b
            | FStar_Pervasives_Native.None -> false))
  }
let csvw_col_specs_from_header (header_cells : Prims.string Prims.list) :
  csvw_col_spec Prims.list=
  FStar_List_Tot_Base.mapi
    (fun i h ->
       {
         cs_name = (if h = "" then csvw_positional_name i else h);
         cs_virtual = false;
         cs_suppress = false;
         cs_datatype = FStar_Pervasives_Native.None;
         cs_about_url = FStar_Pervasives_Native.None;
         cs_property_url = FStar_Pervasives_Native.None;
         cs_value_url = FStar_Pervasives_Native.None;
         cs_separator = FStar_Pervasives_Native.None;
         cs_lang = FStar_Pervasives_Native.None;
         cs_null = FStar_Pervasives_Native.None;
         cs_default = FStar_Pervasives_Native.None;
         cs_ordered = false
       }) header_cells
let csvw_col_specs_positional (header_cells : Prims.string Prims.list) :
  csvw_col_spec Prims.list=
  FStar_List_Tot_Base.mapi
    (fun i h ->
       {
         cs_name = (csvw_positional_name i);
         cs_virtual = false;
         cs_suppress = false;
         cs_datatype = FStar_Pervasives_Native.None;
         cs_about_url = FStar_Pervasives_Native.None;
         cs_property_url = FStar_Pervasives_Native.None;
         cs_value_url = FStar_Pervasives_Native.None;
         cs_separator = FStar_Pervasives_Native.None;
         cs_lang = FStar_Pervasives_Native.None;
         cs_null = FStar_Pervasives_Native.None;
         cs_default = FStar_Pervasives_Native.None;
         cs_ordered = false
       }) header_cells
let csvw_positional_spec_eff (eff : CSVW_Metadata.csvw_inherited_props)
  (i : Prims.int) : csvw_col_spec=
  {
    cs_name = (csvw_positional_name i);
    cs_virtual = false;
    cs_suppress = false;
    cs_datatype = (eff.CSVW_Metadata.inh_datatype);
    cs_about_url = (eff.CSVW_Metadata.inh_about_url);
    cs_property_url = (eff.CSVW_Metadata.inh_property_url);
    cs_value_url = (eff.CSVW_Metadata.inh_value_url);
    cs_separator = (eff.CSVW_Metadata.inh_separator);
    cs_lang = (eff.CSVW_Metadata.inh_lang);
    cs_null = (eff.CSVW_Metadata.inh_null);
    cs_default = FStar_Pervasives_Native.None;
    cs_ordered =
      (match eff.CSVW_Metadata.inh_ordered with
       | FStar_Pervasives_Native.Some b -> b
       | FStar_Pervasives_Native.None -> false)
  }
let rec csvw_surplus_specs (eff : CSVW_Metadata.csvw_inherited_props)
  (n_described : Prims.nat) (i : Prims.nat)
  (header_cells : Prims.string Prims.list) : csvw_col_spec Prims.list=
  match header_cells with
  | [] -> []
  | uu___::tl ->
      let rest = csvw_surplus_specs eff n_described (i + Prims.int_one) tl in
      if i >= n_described
      then (csvw_positional_spec_eff eff i) :: rest
      else rest
let csvw_build_col_specs (grp : CSVW_Metadata.csvw_inherited_props)
  (tbl : CSVW_Metadata.csvw_inherited_props)
  (ts_opt : CSVW_Metadata.csvw_table_schema FStar_Pervasives_Native.option)
  (header_cells : Prims.string Prims.list) : csvw_col_spec Prims.list=
  match ts_opt with
  | FStar_Pervasives_Native.Some ts ->
      if Prims.uu___is_Cons ts.CSVW_Metadata.ts_columns
      then
        let eff =
          csvw_merge_inherited ts.CSVW_Metadata.ts_inherited
            (csvw_merge_inherited tbl grp) in
        let described =
          FStar_List_Tot_Base.mapi
            (fun i c -> csvw_col_spec_of_column eff i c)
            ts.CSVW_Metadata.ts_columns in
        FStar_List_Tot_Base.op_At described
          (csvw_surplus_specs eff
             (FStar_List_Tot_Base.length ts.CSVW_Metadata.ts_columns)
             Prims.int_zero header_cells)
      else csvw_col_specs_positional header_cells
  | FStar_Pervasives_Native.None -> csvw_col_specs_from_header header_cells
let csvw_header_row_count
  (dia_opt : CSVW_Metadata.csvw_dialect FStar_Pervasives_Native.option) :
  Prims.nat=
  match dia_opt with
  | FStar_Pervasives_Native.None -> Prims.int_one
  | FStar_Pervasives_Native.Some dia ->
      (match dia.CSVW_Metadata.dia_header_row_count with
       | FStar_Pervasives_Native.Some n ->
           if n >= Prims.int_zero then n else Prims.int_one
       | FStar_Pervasives_Native.None ->
           (match dia.CSVW_Metadata.dia_header with
            | FStar_Pervasives_Native.Some false -> Prims.int_zero
            | uu___ -> Prims.int_one))
let csvw_skip_rows_count
  (dia_opt : CSVW_Metadata.csvw_dialect FStar_Pervasives_Native.option) :
  Prims.nat=
  match dia_opt with
  | FStar_Pervasives_Native.None -> Prims.int_zero
  | FStar_Pervasives_Native.Some dia ->
      (match dia.CSVW_Metadata.dia_skip_rows with
       | FStar_Pervasives_Native.Some n ->
           if n >= Prims.int_zero then n else Prims.int_zero
       | FStar_Pervasives_Native.None -> Prims.int_zero)
let rec csvw_drop : 'a . Prims.nat -> 'a Prims.list -> 'a Prims.list =
  fun n l ->
    if n = Prims.int_zero
    then l
    else
      (match l with
       | [] -> []
       | uu___1::tl -> csvw_drop (n - Prims.int_one) tl)
let rec csvw_index_from :
  'a . Prims.nat -> 'a Prims.list -> (Prims.nat * 'a) Prims.list =
  fun n l ->
    match l with
    | [] -> []
    | hd::tl -> (n, hd) :: (csvw_index_from (n + Prims.int_one) tl)
let rec csvw_zip_specs_cells (specs : csvw_col_spec Prims.list)
  (cells : Prims.string Prims.list) :
  (csvw_col_spec * Prims.string) Prims.list=
  match (specs, cells) with
  | (s::srest, c::crest) -> (s, c) :: (csvw_zip_specs_cells srest crest)
  | (uu___, uu___1) -> []
let csvw_effective_table_url (base_iri : Prims.string)
  (fallback_url : Prims.string) (tbl : CSVW_Metadata.csvw_table) :
  Prims.string=
  let raw =
    match tbl.CSVW_Metadata.tbl_url with
    | FStar_Pervasives_Native.Some u -> u
    | FStar_Pervasives_Native.None -> fallback_url in
  RDF_IRI.resolve_iri_v2 base_iri raw
let csvw_row_lookup
  (phys_bindings : (Prims.string * Prims.string) Prims.list)
  (row_num : Prims.nat) (source_row_num : Prims.nat) (v : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if v = "_row"
  then FStar_Pervasives_Native.Some (Prims.string_of_int row_num)
  else
    if v = "_sourceRow"
    then FStar_Pervasives_Native.Some (Prims.string_of_int source_row_num)
    else FStar_List_Tot_Base.assoc v phys_bindings
let csvw_term_of_subject (s : RDF_Term.subject) : RDF_Term.rdf_term=
  match s with
  | RDF_Term.S_IRI i -> RDF_Term.T_IRI i
  | RDF_Term.S_BNode b -> RDF_Term.T_BNode b
let csvw_cell_object (table_url_resolved : Prims.string)
  (spec : csvw_col_spec)
  (cell_text0 : Prims.string FStar_Pervasives_Native.option)
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  let cell_text =
    match ((spec.cs_separator), cell_text0) with
    | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some "") ->
        (match spec.cs_default with
         | FStar_Pervasives_Native.Some d -> FStar_Pervasives_Native.Some d
         | FStar_Pervasives_Native.None -> cell_text0)
    | uu___ -> cell_text0 in
  let phys_null =
    match cell_text with
    | FStar_Pervasives_Native.Some txt ->
        (txt = "") ||
          ((match spec.cs_null with
            | FStar_Pervasives_Native.Some n -> txt = n
            | FStar_Pervasives_Native.None -> false))
    | FStar_Pervasives_Native.None -> false in
  if phys_null
  then FStar_Pervasives_Native.None
  else
    (match spec.cs_value_url with
     | FStar_Pervasives_Native.Some tmpl ->
         let raw =
           csvw_expand_curie
             (CSVW_URITemplate.csvw_expand_template lookup tmpl) in
         let resolved = RDF_IRI.resolve_iri_v2 table_url_resolved raw in
         if RDF_Term.is_iri resolved
         then FStar_Pervasives_Native.Some (RDF_Term.T_IRI resolved)
         else FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.None ->
         (match cell_text with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some txt ->
              let is_null =
                (txt = "") ||
                  (match spec.cs_null with
                   | FStar_Pervasives_Native.Some n -> txt = n
                   | FStar_Pervasives_Native.None -> false) in
              if is_null
              then FStar_Pervasives_Native.None
              else
                (let dt_str = csvw_datatype_iri spec.cs_datatype in
                 let dt_wf =
                   if RDF_Term.is_iri dt_str
                   then FStar_Pervasives_Native.Some dt_str
                   else FStar_Pervasives_Native.None in
                 match dt_wf with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some d ->
                     let base_name = csvw_dt_base_name_of spec.cs_datatype in
                     let uu___2 = csvw_dt_format_facets spec.cs_datatype in
                     (match uu___2 with
                      | (fmt_str, pat, grp, dec) ->
                          let uu___3 =
                            match CSVW_Formats.csvw_format_convert base_name
                                    fmt_str pat grp dec txt
                            with
                            | CSVW_Formats.FO_Invalid ->
                                (txt, RDF_Term.xsd_string)
                            | CSVW_Formats.FO_Valid canonical ->
                                (canonical, d)
                            | CSVW_Formats.FO_NoFormat -> (txt, d) in
                          (match uu___3 with
                           | (lex, dt_eff) ->
                               let violate =
                                 (XSD_Datatypes.literal_ill_formed dt_eff lex)
                                   ||
                                   (Prims.op_Negation
                                      (csvw_value_satisfies base_name lex
                                         spec.cs_datatype)) in
                               let eff =
                                 if violate
                                 then RDF_Term.xsd_string
                                 else dt_eff in
                               csvw_build_literal_lang lex eff spec.cs_lang)))))
let csvw_encode_name (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.concatMap
       (fun c ->
          if (FStar_Char.int_of_char c) = (Prims.of_int (45))
          then
            [FStar_Char.char_of_int (Prims.of_int (37));
            FStar_Char.char_of_int (Prims.of_int (50));
            FStar_Char.char_of_int (Prims.of_int (68))]
          else [c])
       (FStar_String.list_of_string (SPARQL11_Algebra.string_encode_uri s)))
let csvw_char_ws (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n = (Prims.of_int (32))) || (n = (Prims.of_int (9)))) ||
     (n = (Prims.of_int (10))))
    || (n = (Prims.of_int (13)))
let rec csvw_drop_leading_ws (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | c::tl -> if csvw_char_ws c then csvw_drop_leading_ws tl else cs
  | [] -> []
let csvw_trim (s : Prims.string) : Prims.string=
  let front = csvw_drop_leading_ws (FStar_String.list_of_string s) in
  FStar_String.string_of_list
    (FStar_List_Tot_Base.rev
       (csvw_drop_leading_ws (FStar_List_Tot_Base.rev front)))
let csvw_split_list_cell (sep : Prims.string) (s : Prims.string) :
  Prims.string Prims.list=
  match FStar_String.list_of_string sep with
  | sepc::uu___ ->
      FStar_List_Tot_Base.map
        (fun cs -> csvw_trim (FStar_String.string_of_list cs))
        (CSVW_Formats.split_all sepc (FStar_String.list_of_string s))
  | [] -> [s]
let rec csvw_rdf_list (seed : Prims.string) (idx : Prims.nat)
  (objs : RDF_Term.rdf_term Prims.list) :
  (RDF_Term.rdf_term * RDF_Triple.triple Prims.list)=
  match objs with
  | [] -> ((RDF_Term.T_IRI rdf_nil_iri), [])
  | o::tl ->
      let node =
        RDF_Term.S_BNode
          (Prims.strcat seed (Prims.strcat "_" (Prims.string_of_int idx))) in
      let uu___ = csvw_rdf_list seed (idx + Prims.int_one) tl in
      (match uu___ with
       | (rest_head, rest_triples) ->
           ((csvw_term_of_subject node),
             ({
                RDF_Triple.s = node;
                RDF_Triple.p = rdf_first_iri;
                RDF_Triple.o = o
              } ::
             {
               RDF_Triple.s = node;
               RDF_Triple.p = rdf_rest_iri;
               RDF_Triple.o = rest_head
             } :: rest_triples)))
let csvw_process_cell (table_url_resolved : Prims.string)
  (row_seed : Prims.string)
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (default_subject : RDF_Term.subject) (spec : csvw_col_spec)
  (cell_text : Prims.string FStar_Pervasives_Native.option) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list)=
  if spec.cs_suppress
  then (default_subject, [])
  else
    (let cur_lookup v =
       if v = "_name"
       then FStar_Pervasives_Native.Some (spec.cs_name)
       else lookup v in
     let subj =
       match spec.cs_about_url with
       | FStar_Pervasives_Native.Some tmpl ->
           let raw = CSVW_URITemplate.csvw_expand_template cur_lookup tmpl in
           let resolved = RDF_IRI.resolve_iri_v2 table_url_resolved raw in
           if RDF_Term.is_iri resolved
           then RDF_Term.S_IRI resolved
           else default_subject
       | FStar_Pervasives_Native.None -> default_subject in
     let raw =
       match spec.cs_property_url with
       | FStar_Pervasives_Native.Some tmpl ->
           RDF_IRI.resolve_iri_v2 table_url_resolved
             (csvw_expand_curie
                (CSVW_URITemplate.csvw_expand_template cur_lookup tmpl))
       | FStar_Pervasives_Native.None ->
           Prims.strcat table_url_resolved
             (Prims.strcat "#" (csvw_encode_name spec.cs_name)) in
     let pred_valid =
       if RDF_Term.is_iri raw
       then FStar_Pervasives_Native.Some raw
       else FStar_Pervasives_Native.None in
     match pred_valid with
     | FStar_Pervasives_Native.None -> (subj, [])
     | FStar_Pervasives_Native.Some pred_str ->
         (match ((spec.cs_separator), cell_text) with
          | (FStar_Pervasives_Native.Some sep, FStar_Pervasives_Native.Some
             txt) ->
              let parts = csvw_split_list_cell sep txt in
              let objs =
                FStar_List_Tot_Base.choose
                  (fun part ->
                     csvw_cell_object table_url_resolved spec
                       (FStar_Pervasives_Native.Some part) cur_lookup) parts in
              if spec.cs_ordered
              then
                (match objs with
                 | [] -> (subj, [])
                 | uu___1 ->
                     let list_seed =
                       Prims.strcat "csvwL_"
                         (Prims.strcat row_seed
                            (Prims.strcat "_" (csvw_encode_name spec.cs_name))) in
                     let uu___2 = csvw_rdf_list list_seed Prims.int_zero objs in
                     (match uu___2 with
                      | (head, list_triples) ->
                          (subj,
                            ({
                               RDF_Triple.s = subj;
                               RDF_Triple.p = pred_str;
                               RDF_Triple.o = head
                             } :: list_triples))))
              else
                (subj,
                  (FStar_List_Tot_Base.map
                     (fun o ->
                        {
                          RDF_Triple.s = subj;
                          RDF_Triple.p = pred_str;
                          RDF_Triple.o = o
                        }) objs))
          | uu___1 ->
              (match csvw_cell_object table_url_resolved spec cell_text
                       cur_lookup
               with
               | FStar_Pervasives_Native.None -> (subj, [])
               | FStar_Pervasives_Native.Some obj ->
                   (subj,
                     [{
                        RDF_Triple.s = subj;
                        RDF_Triple.p = pred_str;
                        RDF_Triple.o = obj
                      }]))))
let csvw_row_cell_results (table_url_resolved : Prims.string)
  (col_specs : csvw_col_spec Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list) Prims.list=
  let phys_specs =
    FStar_List_Tot_Base.filter (fun s -> Prims.op_Negation s.cs_virtual)
      col_specs in
  let virt_specs =
    FStar_List_Tot_Base.filter (fun s -> s.cs_virtual) col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let phys_bindings =
    FStar_List_Tot_Base.map
      (fun p ->
         (((FStar_Pervasives_Native.fst p).cs_name),
           (FStar_Pervasives_Native.snd p))) phys_pairs in
  let lookup = csvw_row_lookup phys_bindings row_num source_row_num in
  let row_seed =
    Prims.strcat (SPARQL11_Algebra.string_encode_uri table_url_resolved)
      (Prims.strcat "_" (Prims.string_of_int source_row_num)) in
  let default_subject =
    RDF_Term.S_BNode
      (Prims.strcat "csvwrow_"
         (Prims.strcat
            (SPARQL11_Algebra.string_encode_uri table_url_resolved)
            (Prims.strcat "_" (Prims.string_of_int source_row_num)))) in
  FStar_List_Tot_Base.op_At
    (FStar_List_Tot_Base.map
       (fun p ->
          csvw_process_cell table_url_resolved row_seed lookup
            default_subject (FStar_Pervasives_Native.fst p)
            (FStar_Pervasives_Native.Some (FStar_Pervasives_Native.snd p)))
       phys_pairs)
    (FStar_List_Tot_Base.map
       (fun s ->
          csvw_process_cell table_url_resolved row_seed lookup
            default_subject s FStar_Pervasives_Native.None) virt_specs)
let csvw_mk_literal (lex : Prims.string) (dt : RDF_Term.wf_iri)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  let l =
    {
      RDF_Term.lexical_form = lex;
      RDF_Term.datatype = dt;
      RDF_Term.lang_tag = lang;
      RDF_Term.direction = FStar_Pervasives_Native.None
    } in
  if RDF_Term.literal_wf l
  then FStar_Pervasives_Native.Some (RDF_Term.T_Literal l)
  else FStar_Pervasives_Native.None
let csvw_typed_literal_opt (lex : Prims.string) (dt : Prims.string) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if RDF_Term.is_iri dt
  then csvw_mk_literal lex dt FStar_Pervasives_Native.None
  else csvw_mk_literal lex RDF_Term.xsd_string FStar_Pervasives_Native.None
let csvw_number_literal_opt (lex : Prims.string) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if XSD_Datatypes.is_integer_lexical lex
  then csvw_mk_literal lex RDF_Term.xsd_integer FStar_Pervasives_Native.None
  else csvw_mk_literal lex RDF_Term.xsd_double FStar_Pervasives_Native.None
let csvw_opt_to_list (o : 'a FStar_Pervasives_Native.option) : 'a Prims.list=
  match o with
  | FStar_Pervasives_Native.Some x -> [x]
  | FStar_Pervasives_Native.None -> []
let rec csvw_common_value
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (fuel : Prims.nat) (seed : Prims.string) (v : Parser_JSON.json_val) :
  (RDF_Term.rdf_term Prims.list * RDF_Triple.triple Prims.list)=
  if fuel = Prims.int_zero
  then ([], [])
  else
    (match v with
     | Parser_JSON.JNull -> ([], [])
     | Parser_JSON.JString s ->
         let term =
           match default_lang with
           | FStar_Pervasives_Native.Some l ->
               csvw_mk_literal s RDF_Term.rdf_lang_string
                 (FStar_Pervasives_Native.Some l)
           | FStar_Pervasives_Native.None ->
               csvw_mk_literal s RDF_Term.xsd_string
                 FStar_Pervasives_Native.None in
         ((csvw_opt_to_list term), [])
     | Parser_JSON.JBool b ->
         ((csvw_opt_to_list
             (csvw_mk_literal (if b then "true" else "false")
                RDF_Term.xsd_boolean FStar_Pervasives_Native.None)), [])
     | Parser_JSON.JNumber s ->
         ((csvw_opt_to_list (csvw_number_literal_opt s)), [])
     | Parser_JSON.JArray items ->
         csvw_common_array default_lang (fuel - Prims.int_one) seed
           Prims.int_zero items
     | Parser_JSON.JObject fields ->
         (match Parser_JSON.json_get_field "@value" v with
          | FStar_Pervasives_Native.Some (Parser_JSON.JString lex) ->
              let term =
                match Parser_JSON.json_get_string "@type" v with
                | FStar_Pervasives_Native.Some t ->
                    csvw_typed_literal_opt lex (csvw_expand_curie t)
                | FStar_Pervasives_Native.None ->
                    (match Parser_JSON.json_get_string "@language" v with
                     | FStar_Pervasives_Native.Some l ->
                         csvw_mk_literal lex RDF_Term.rdf_lang_string
                           (FStar_Pervasives_Native.Some l)
                     | FStar_Pervasives_Native.None ->
                         csvw_mk_literal lex RDF_Term.xsd_string
                           FStar_Pervasives_Native.None) in
              ((csvw_opt_to_list term), [])
          | uu___1 ->
              (match Parser_JSON.json_get_field "@id" v with
               | FStar_Pervasives_Native.Some (Parser_JSON.JString idv) ->
                   let iri = csvw_expand_curie idv in
                   if RDF_Term.is_iri iri
                   then ([RDF_Term.T_IRI iri], [])
                   else ([], [])
               | uu___2 ->
                   let lbl = Prims.strcat "csvwCP_" seed in
                   let b = RDF_Term.S_BNode lbl in
                   let inner =
                     csvw_common_object_fields default_lang
                       (fuel - Prims.int_one) b lbl fields in
                   ([csvw_term_of_subject b], inner))))
and csvw_common_array
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (fuel : Prims.nat) (seed : Prims.string) (idx : Prims.nat)
  (items : Parser_JSON.json_val Prims.list) :
  (RDF_Term.rdf_term Prims.list * RDF_Triple.triple Prims.list)=
  if fuel = Prims.int_zero
  then ([], [])
  else
    (match items with
     | [] -> ([], [])
     | hd::tl ->
         let uu___1 =
           csvw_common_value default_lang (fuel - Prims.int_one)
             (Prims.strcat seed (Prims.strcat "_" (Prims.string_of_int idx)))
             hd in
         (match uu___1 with
          | (t1, r1) ->
              let uu___2 =
                csvw_common_array default_lang (fuel - Prims.int_one) seed
                  (idx + Prims.int_one) tl in
              (match uu___2 with
               | (t2, r2) ->
                   ((FStar_List_Tot_Base.op_At t1 t2),
                     (FStar_List_Tot_Base.op_At r1 r2)))))
and csvw_common_object_fields
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (fuel : Prims.nat) (subj : RDF_Term.subject) (seed : Prims.string)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  RDF_Triple.triple Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match fields with
     | [] -> []
     | (k, v)::tl ->
         let here =
           if k = "@type"
           then
             match v with
             | Parser_JSON.JString tv ->
                 let ti = csvw_expand_type_token tv in
                 (match if RDF_Term.is_iri ti
                        then FStar_Pervasives_Native.Some ti
                        else FStar_Pervasives_Native.None
                  with
                  | FStar_Pervasives_Native.Some tiw ->
                      let tiw1 = tiw in
                      [{
                         RDF_Triple.s = subj;
                         RDF_Triple.p = RDFS_Closure.rdf_type;
                         RDF_Triple.o = (RDF_Term.T_IRI tiw1)
                       }]
                  | FStar_Pervasives_Native.None -> [])
             | uu___1 -> []
           else
             if RDF_Term.string_contains_colon k
             then
               (let praw = csvw_expand_curie k in
                match if RDF_Term.is_iri praw
                      then FStar_Pervasives_Native.Some praw
                      else FStar_Pervasives_Native.None
                with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some pred ->
                    let pred1 = pred in
                    let uu___2 =
                      csvw_common_value default_lang (fuel - Prims.int_one)
                        (Prims.strcat seed (Prims.strcat "_" k)) v in
                    (match uu___2 with
                     | (terms, sub) ->
                         FStar_List_Tot_Base.op_At
                           (FStar_List_Tot_Base.map
                              (fun t ->
                                 {
                                   RDF_Triple.s = subj;
                                   RDF_Triple.p = pred1;
                                   RDF_Triple.o = t
                                 }) terms) sub))
             else [] in
         FStar_List_Tot_Base.op_At here
           (csvw_common_object_fields default_lang (fuel - Prims.int_one)
              subj seed tl))
let rec csvw_common_fuel
  (common : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.nat=
  match common with
  | [] -> Prims.int_one
  | (uu___, v)::tl ->
      (Prims.int_one + (Parser_JSON.json_size v)) + (csvw_common_fuel tl)
let csvw_table_common_triples
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (subj : RDF_Term.subject) (seed : Prims.string)
  (common : (Prims.string * Parser_JSON.json_val) Prims.list) :
  RDF_Triple.triple Prims.list=
  csvw_common_object_fields default_lang (csvw_common_fuel common) subj seed
    common
let rec csvw_notes_triples
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (subj : RDF_Term.subject) (seed : Prims.string) (idx : Prims.nat)
  (notes : Parser_JSON.json_val Prims.list) : RDF_Triple.triple Prims.list=
  match notes with
  | [] -> []
  | n::tl ->
      let uu___ =
        csvw_common_value default_lang
          ((Parser_JSON.json_size n) + Prims.int_one)
          (Prims.strcat seed
             (Prims.strcat "_note_" (Prims.string_of_int idx))) n in
      (match uu___ with
       | (terms, sub) ->
           FStar_List_Tot_Base.op_At
             (FStar_List_Tot_Base.map
                (fun t ->
                   {
                     RDF_Triple.s = subj;
                     RDF_Triple.p = csvw_note_pred;
                     RDF_Triple.o = t
                   }) terms)
             (FStar_List_Tot_Base.op_At sub
                (csvw_notes_triples default_lang subj seed
                   (idx + Prims.int_one) tl)))
let csvw_row_triples_minimal (table_url_resolved : Prims.string)
  (col_specs : csvw_col_spec Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd
    (csvw_row_cell_results table_url_resolved col_specs row_num
       source_row_num cells)
let csvw_convert_table_minimal
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string) (fallback_url : Prims.string)
  (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) :
  RDF_Triple.triple Prims.list=
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_n = (csvw_skip_rows_count dia) + (csvw_header_row_count dia) in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let header_cells =
    if (csvw_header_row_count dia) > Prims.int_zero
    then match after_skip_rows with | h::uu___ -> h | [] -> []
    else
      (match tbl.CSVW_Metadata.tbl_table_schema with
       | FStar_Pervasives_Native.Some uu___1 -> []
       | FStar_Pervasives_Native.None ->
           (match data_rows with
            | r::uu___1 -> FStar_List_Tot_Base.map (fun uu___2 -> "") r
            | [] -> [])) in
  let col_specs =
    csvw_build_col_specs grp_inherited tbl.CSVW_Metadata.tbl_inherited
      tbl.CSVW_Metadata.tbl_table_schema header_cells in
  let indexed = csvw_index_from Prims.int_zero data_rows in
  FStar_List_Tot_Base.concatMap
    (fun p ->
       let uu___ = p in
       match uu___ with
       | (i, cells) ->
           csvw_row_triples_minimal table_url_resolved col_specs
             (i + Prims.int_one) ((skip_n + i) + Prims.int_one) cells)
    indexed
let csvw_row_url (table_url_resolved : Prims.string)
  (source_row_num : Prims.nat) : Prims.string=
  Prims.strcat table_url_resolved
    (Prims.strcat "#row=" (Prims.string_of_int source_row_num))
let csvw_row_title_triples (row_node : RDF_Term.subject)
  (col_specs : csvw_col_spec Prims.list) (cells : Prims.string Prims.list)
  (row_titles : Prims.string Prims.list) : RDF_Triple.triple Prims.list=
  let phys_specs =
    FStar_List_Tot_Base.filter (fun s -> Prims.op_Negation s.cs_virtual)
      col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let bindings =
    FStar_List_Tot_Base.map
      (fun p ->
         (((FStar_Pervasives_Native.fst p).cs_name),
           (FStar_Pervasives_Native.snd p))) phys_pairs in
  FStar_List_Tot_Base.concatMap
    (fun name ->
       match FStar_List_Tot_Base.assoc name bindings with
       | FStar_Pervasives_Native.Some txt ->
           (match csvw_mk_literal txt RDF_Term.xsd_string
                    FStar_Pervasives_Native.None
            with
            | FStar_Pervasives_Native.Some o ->
                [{
                   RDF_Triple.s = row_node;
                   RDF_Triple.p = csvw_title_pred;
                   RDF_Triple.o = o
                 }]
            | FStar_Pervasives_Native.None -> [])
       | FStar_Pervasives_Native.None -> []) row_titles
let csvw_row_triples_standard (table_url_resolved : Prims.string)
  (row_titles : Prims.string Prims.list)
  (col_specs : csvw_col_spec Prims.list) (row_num : Prims.nat)
  (source_row_num : Prims.nat) (cells : Prims.string Prims.list) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list)=
  let per_col =
    csvw_row_cell_results table_url_resolved col_specs row_num source_row_num
      cells in
  let row_node =
    RDF_Term.S_BNode
      (Prims.strcat "csvwR_"
         (Prims.strcat
            (SPARQL11_Algebra.string_encode_uri table_url_resolved)
            (Prims.strcat "_" (Prims.string_of_int source_row_num)))) in
  let row_url = csvw_row_url table_url_resolved source_row_num in
  let row_meta =
    FStar_List_Tot_Base.op_At
      [{
         RDF_Triple.s = row_node;
         RDF_Triple.p = RDFS_Closure.rdf_type;
         RDF_Triple.o = (RDF_Term.T_IRI csvw_Row)
       };
      {
        RDF_Triple.s = row_node;
        RDF_Triple.p = csvw_rownum;
        RDF_Triple.o =
          (RDF_Term.T_Literal
             {
               RDF_Term.lexical_form = (Prims.string_of_int row_num);
               RDF_Term.datatype = RDF_Term.xsd_integer;
               RDF_Term.lang_tag = FStar_Pervasives_Native.None;
               RDF_Term.direction = FStar_Pervasives_Native.None
             })
      }]
      (if RDF_Term.is_iri row_url
       then
         [{
            RDF_Triple.s = row_node;
            RDF_Triple.p = csvw_url_pred;
            RDF_Triple.o = (RDF_Term.T_IRI row_url)
          }]
       else []) in
  let describes =
    FStar_List_Tot_Base.concatMap
      (fun r ->
         let uu___ = r in
         match uu___ with
         | (subj, ts) ->
             if Prims.uu___is_Nil ts
             then []
             else
               [{
                  RDF_Triple.s = row_node;
                  RDF_Triple.p = csvw_describes;
                  RDF_Triple.o = (csvw_term_of_subject subj)
                }]) per_col in
  let cell_triples =
    FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd per_col in
  let title_triples =
    csvw_row_title_triples row_node col_specs cells row_titles in
  (row_node,
    (FStar_List_Tot_Base.op_At row_meta
       (FStar_List_Tot_Base.op_At title_triples
          (FStar_List_Tot_Base.op_At describes cell_triples))))
let csvw_convert_table_standard
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (base_iri : Prims.string)
  (doc_url : Prims.string FStar_Pervasives_Native.option)
  (fallback_url : Prims.string) (tbl : CSVW_Metadata.csvw_table)
  (all_rows : Prims.string Prims.list Prims.list) :
  (RDF_Term.subject * RDF_Triple.triple Prims.list)=
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.CSVW_Metadata.tbl_dialect in
  let skip_n = (csvw_skip_rows_count dia) + (csvw_header_row_count dia) in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let header_cells =
    if (csvw_header_row_count dia) > Prims.int_zero
    then match after_skip_rows with | h::uu___ -> h | [] -> []
    else
      (match tbl.CSVW_Metadata.tbl_table_schema with
       | FStar_Pervasives_Native.Some uu___1 -> []
       | FStar_Pervasives_Native.None ->
           (match data_rows with
            | r::uu___1 -> FStar_List_Tot_Base.map (fun uu___2 -> "") r
            | [] -> [])) in
  let col_specs =
    csvw_build_col_specs grp_inherited tbl.CSVW_Metadata.tbl_inherited
      tbl.CSVW_Metadata.tbl_table_schema header_cells in
  let row_titles =
    match tbl.CSVW_Metadata.tbl_table_schema with
    | FStar_Pervasives_Native.Some ts -> ts.CSVW_Metadata.ts_row_titles
    | FStar_Pervasives_Native.None -> [] in
  let indexed = csvw_index_from Prims.int_zero data_rows in
  let row_results =
    FStar_List_Tot_Base.map
      (fun p ->
         let uu___ = p in
         match uu___ with
         | (i, cells) ->
             csvw_row_triples_standard table_url_resolved row_titles
               col_specs (i + Prims.int_one) ((skip_n + i) + Prims.int_one)
               cells) indexed in
  let bnode_fallback =
    RDF_Term.S_BNode
      (Prims.strcat "csvwT_"
         (SPARQL11_Algebra.string_encode_uri table_url_resolved)) in
  let t_node =
    match tbl.CSVW_Metadata.tbl_id with
    | CSVW_Metadata.CsvwIdString s ->
        let resolved = RDF_IRI.resolve_iri_v2 base_iri s in
        if RDF_Term.is_iri resolved
        then RDF_Term.S_IRI resolved
        else bnode_fallback
    | CSVW_Metadata.CsvwIdInvalid ->
        (match doc_url with
         | FStar_Pervasives_Native.Some u ->
             if RDF_Term.is_iri u then RDF_Term.S_IRI u else bnode_fallback
         | FStar_Pervasives_Native.None -> bnode_fallback)
    | CSVW_Metadata.CsvwIdNone -> bnode_fallback in
  let row_links =
    FStar_List_Tot_Base.concatMap
      (fun r ->
         [{
            RDF_Triple.s = t_node;
            RDF_Triple.p = csvw_row_pred;
            RDF_Triple.o =
              (csvw_term_of_subject (FStar_Pervasives_Native.fst r))
          }]) row_results in
  let row_all =
    FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd row_results in
  let t_common =
    csvw_table_common_triples default_lang t_node
      (SPARQL11_Algebra.string_encode_uri table_url_resolved)
      tbl.CSVW_Metadata.tbl_common in
  let t_notes =
    csvw_notes_triples default_lang t_node
      (SPARQL11_Algebra.string_encode_uri table_url_resolved) Prims.int_zero
      tbl.CSVW_Metadata.tbl_notes in
  let t_meta =
    FStar_List_Tot_Base.op_At
      [{
         RDF_Triple.s = t_node;
         RDF_Triple.p = RDFS_Closure.rdf_type;
         RDF_Triple.o = (RDF_Term.T_IRI csvw_Table)
       }]
      (if RDF_Term.is_iri table_url_resolved
       then
         [{
            RDF_Triple.s = t_node;
            RDF_Triple.p = csvw_url_pred;
            RDF_Triple.o = (RDF_Term.T_IRI table_url_resolved)
          }]
       else []) in
  (t_node,
    (FStar_List_Tot_Base.op_At t_meta
       (FStar_List_Tot_Base.op_At t_common
          (FStar_List_Tot_Base.op_At t_notes
             (FStar_List_Tot_Base.op_At row_links row_all)))))
let csvw_table_suppressed (tbl : CSVW_Metadata.csvw_table) : Prims.bool=
  match tbl.CSVW_Metadata.tbl_suppress_output with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> false
let csvw_convert_document_minimal
  (grp_inherited : CSVW_Metadata.csvw_inherited_props)
  (base_iri : Prims.string)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : RDF_Triple.triple Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun t ->
       let uu___ = t in
       match uu___ with
       | (tbl, fallback_url, rows) ->
           if csvw_table_suppressed tbl
           then []
           else
             csvw_convert_table_minimal grp_inherited base_iri fallback_url
               tbl rows) tables_with_rows
let csvw_group_node : RDF_Term.subject= RDF_Term.S_BNode "csvwG"
let csvw_convert_document_standard (grp : CSVW_Metadata.csvw_group_meta)
  (default_lang : Prims.string FStar_Pervasives_Native.option)
  (base_iri : Prims.string)
  (doc_url : Prims.string FStar_Pervasives_Native.option)
  (tables_with_rows :
    (CSVW_Metadata.csvw_table * Prims.string * Prims.string Prims.list
      Prims.list) Prims.list)
  : RDF_Triple.triple Prims.list=
  let table_results =
    FStar_List_Tot_Base.map
      (fun t ->
         let uu___ = t in
         match uu___ with
         | (tbl, fallback_url, rows) ->
             csvw_convert_table_standard grp.CSVW_Metadata.grp_inherited
               default_lang base_iri doc_url fallback_url tbl rows)
      (FStar_List_Tot_Base.filter
         (fun t ->
            let uu___ = t in
            match uu___ with
            | (tbl, uu___1, uu___2) ->
                Prims.op_Negation (csvw_table_suppressed tbl))
         tables_with_rows) in
  let g_meta =
    [{
       RDF_Triple.s = csvw_group_node;
       RDF_Triple.p = RDFS_Closure.rdf_type;
       RDF_Triple.o = (RDF_Term.T_IRI csvw_TableGroup)
     }] in
  let g_common =
    csvw_table_common_triples default_lang csvw_group_node "csvwG"
      grp.CSVW_Metadata.grp_common in
  let table_links =
    FStar_List_Tot_Base.concatMap
      (fun r ->
         [{
            RDF_Triple.s = csvw_group_node;
            RDF_Triple.p = csvw_table_pred;
            RDF_Triple.o =
              (csvw_term_of_subject (FStar_Pervasives_Native.fst r))
          }]) table_results in
  let table_all =
    FStar_List_Tot_Base.concatMap FStar_Pervasives_Native.snd table_results in
  FStar_List_Tot_Base.op_At g_meta
    (FStar_List_Tot_Base.op_At g_common
       (FStar_List_Tot_Base.op_At table_links table_all))
let csvw_no_metadata_table : CSVW_Metadata.csvw_table=
  {
    CSVW_Metadata.tbl_url = FStar_Pervasives_Native.None;
    CSVW_Metadata.tbl_dialect = FStar_Pervasives_Native.None;
    CSVW_Metadata.tbl_table_schema = FStar_Pervasives_Native.None;
    CSVW_Metadata.tbl_id = CSVW_Metadata.CsvwIdNone;
    CSVW_Metadata.tbl_notes = [];
    CSVW_Metadata.tbl_common = [];
    CSVW_Metadata.tbl_inherited = CSVW_Metadata.csvw_inherited_empty;
    CSVW_Metadata.tbl_schema_ref = FStar_Pervasives_Native.None;
    CSVW_Metadata.tbl_suppress_output = FStar_Pervasives_Native.None
  }
