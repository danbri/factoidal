open Prims
let csvw_char_to_digit (c : FStar_Char.char) :
  Prims.int FStar_Pervasives_Native.option=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
  then FStar_Pervasives_Native.Some (n - (Prims.of_int (48)))
  else FStar_Pervasives_Native.None
let rec csvw_parse_int_chars (chars : FStar_Char.char Prims.list)
  (acc : Prims.int) : Prims.int FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::rest ->
      (match csvw_char_to_digit c with
       | FStar_Pervasives_Native.Some d ->
           csvw_parse_int_chars rest ((acc * (Prims.of_int (10))) + d)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let csvw_parse_int_string (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | [] -> FStar_Pervasives_Native.None
  | chars ->
      if
        (FStar_List_Tot_Base.hd chars) =
          (FStar_Char.char_of_int (Prims.of_int (45)))
      then
        (match csvw_parse_int_chars (FStar_List_Tot_Base.tl chars)
                 Prims.int_zero
         with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (Prims.int_zero - n)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else csvw_parse_int_chars chars Prims.int_zero
let json_get_number_lexeme (key : Prims.string) (obj : Parser_JSON.json_val)
  : Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field key obj with
  | FStar_Pervasives_Native.Some (Parser_JSON.JNumber s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let json_get_int (key : Prims.string) (obj : Parser_JSON.json_val) :
  Prims.int FStar_Pervasives_Native.option=
  match json_get_number_lexeme key obj with
  | FStar_Pervasives_Native.Some s -> csvw_parse_int_string s
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let json_get_string_or_bool_as_string (key : Prims.string)
  (obj : Parser_JSON.json_val) : Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field key obj with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      FStar_Pervasives_Native.Some s
  | FStar_Pervasives_Native.Some (Parser_JSON.JBool true) ->
      FStar_Pervasives_Native.Some "true"
  | FStar_Pervasives_Native.Some (Parser_JSON.JBool false) ->
      FStar_Pervasives_Native.Some "false"
  | uu___ -> FStar_Pervasives_Native.None
type csvw_datatype =
  | CSVW_DT_Named of Prims.string 
  | CSVW_DT_Object of Prims.string FStar_Pervasives_Native.option *
  Prims.string FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option 
let uu___is_CSVW_DT_Named (projectee : csvw_datatype) : Prims.bool=
  match projectee with | CSVW_DT_Named _0 -> true | uu___ -> false
let __proj__CSVW_DT_Named__item___0 (projectee : csvw_datatype) :
  Prims.string= match projectee with | CSVW_DT_Named _0 -> _0
let uu___is_CSVW_DT_Object (projectee : csvw_datatype) : Prims.bool=
  match projectee with
  | CSVW_DT_Object (base, format, pattern, group_char, decimal_char) -> true
  | uu___ -> false
let __proj__CSVW_DT_Object__item__base (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object (base, format, pattern, group_char, decimal_char) -> base
let __proj__CSVW_DT_Object__item__format (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object (base, format, pattern, group_char, decimal_char) ->
      format
let __proj__CSVW_DT_Object__item__pattern (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object (base, format, pattern, group_char, decimal_char) ->
      pattern
let __proj__CSVW_DT_Object__item__group_char (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object (base, format, pattern, group_char, decimal_char) ->
      group_char
let __proj__CSVW_DT_Object__item__decimal_char (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object (base, format, pattern, group_char, decimal_char) ->
      decimal_char
type csvw_column =
  {
  col_name: Prims.string FStar_Pervasives_Native.option ;
  col_titles: Prims.string Prims.list ;
  col_datatype: csvw_datatype FStar_Pervasives_Native.option ;
  col_virtual: Prims.bool FStar_Pervasives_Native.option ;
  col_suppress_output: Prims.bool FStar_Pervasives_Native.option ;
  col_required: Prims.bool FStar_Pervasives_Native.option ;
  col_about_url: Prims.string FStar_Pervasives_Native.option ;
  col_property_url: Prims.string FStar_Pervasives_Native.option ;
  col_value_url: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcsvw_column__item__col_name (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_name
let __proj__Mkcsvw_column__item__col_titles (projectee : csvw_column) :
  Prims.string Prims.list=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_titles
let __proj__Mkcsvw_column__item__col_datatype (projectee : csvw_column) :
  csvw_datatype FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_datatype
let __proj__Mkcsvw_column__item__col_virtual (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_virtual
let __proj__Mkcsvw_column__item__col_suppress_output
  (projectee : csvw_column) : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_suppress_output
let __proj__Mkcsvw_column__item__col_required (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_required
let __proj__Mkcsvw_column__item__col_about_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_about_url
let __proj__Mkcsvw_column__item__col_property_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_property_url
let __proj__Mkcsvw_column__item__col_value_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;_} ->
      col_value_url
type csvw_dialect =
  {
  dia_delimiter: Prims.string FStar_Pervasives_Native.option ;
  dia_quote_char: Prims.string FStar_Pervasives_Native.option ;
  dia_double_quote: Prims.bool FStar_Pervasives_Native.option ;
  dia_header: Prims.bool FStar_Pervasives_Native.option ;
  dia_header_row_count: Prims.int FStar_Pervasives_Native.option ;
  dia_skip_rows: Prims.int FStar_Pervasives_Native.option ;
  dia_skip_columns: Prims.int FStar_Pervasives_Native.option ;
  dia_skip_blank_rows: Prims.bool FStar_Pervasives_Native.option ;
  dia_skip_initial_space: Prims.bool FStar_Pervasives_Native.option ;
  dia_comment_prefix: Prims.string FStar_Pervasives_Native.option ;
  dia_encoding: Prims.string FStar_Pervasives_Native.option ;
  dia_trim: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcsvw_dialect__item__dia_delimiter (projectee : csvw_dialect) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_delimiter
let __proj__Mkcsvw_dialect__item__dia_quote_char (projectee : csvw_dialect) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_quote_char
let __proj__Mkcsvw_dialect__item__dia_double_quote (projectee : csvw_dialect)
  : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_double_quote
let __proj__Mkcsvw_dialect__item__dia_header (projectee : csvw_dialect) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_header
let __proj__Mkcsvw_dialect__item__dia_header_row_count
  (projectee : csvw_dialect) : Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_header_row_count
let __proj__Mkcsvw_dialect__item__dia_skip_rows (projectee : csvw_dialect) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_skip_rows
let __proj__Mkcsvw_dialect__item__dia_skip_columns (projectee : csvw_dialect)
  : Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_skip_columns
let __proj__Mkcsvw_dialect__item__dia_skip_blank_rows
  (projectee : csvw_dialect) : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_skip_blank_rows
let __proj__Mkcsvw_dialect__item__dia_skip_initial_space
  (projectee : csvw_dialect) : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_skip_initial_space
let __proj__Mkcsvw_dialect__item__dia_comment_prefix
  (projectee : csvw_dialect) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_comment_prefix
let __proj__Mkcsvw_dialect__item__dia_encoding (projectee : csvw_dialect) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_encoding
let __proj__Mkcsvw_dialect__item__dia_trim (projectee : csvw_dialect) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { dia_delimiter; dia_quote_char; dia_double_quote; dia_header;
      dia_header_row_count; dia_skip_rows; dia_skip_columns;
      dia_skip_blank_rows; dia_skip_initial_space; dia_comment_prefix;
      dia_encoding; dia_trim;_} -> dia_trim
type csvw_table_schema =
  {
  ts_columns: csvw_column Prims.list ;
  ts_primary_key: Prims.string FStar_Pervasives_Native.option ;
  ts_about_url: Prims.string FStar_Pervasives_Native.option ;
  ts_property_url: Prims.string FStar_Pervasives_Native.option ;
  ts_value_url: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcsvw_table_schema__item__ts_columns
  (projectee : csvw_table_schema) : csvw_column Prims.list=
  match projectee with
  | { ts_columns; ts_primary_key; ts_about_url; ts_property_url;
      ts_value_url;_} -> ts_columns
let __proj__Mkcsvw_table_schema__item__ts_primary_key
  (projectee : csvw_table_schema) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ts_columns; ts_primary_key; ts_about_url; ts_property_url;
      ts_value_url;_} -> ts_primary_key
let __proj__Mkcsvw_table_schema__item__ts_about_url
  (projectee : csvw_table_schema) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ts_columns; ts_primary_key; ts_about_url; ts_property_url;
      ts_value_url;_} -> ts_about_url
let __proj__Mkcsvw_table_schema__item__ts_property_url
  (projectee : csvw_table_schema) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ts_columns; ts_primary_key; ts_about_url; ts_property_url;
      ts_value_url;_} -> ts_property_url
let __proj__Mkcsvw_table_schema__item__ts_value_url
  (projectee : csvw_table_schema) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ts_columns; ts_primary_key; ts_about_url; ts_property_url;
      ts_value_url;_} -> ts_value_url
type csvw_table =
  {
  tbl_url: Prims.string FStar_Pervasives_Native.option ;
  tbl_dialect: csvw_dialect FStar_Pervasives_Native.option ;
  tbl_table_schema: csvw_table_schema FStar_Pervasives_Native.option }
let __proj__Mkcsvw_table__item__tbl_url (projectee : csvw_table) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema;_} -> tbl_url
let __proj__Mkcsvw_table__item__tbl_dialect (projectee : csvw_table) :
  csvw_dialect FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema;_} -> tbl_dialect
let __proj__Mkcsvw_table__item__tbl_table_schema (projectee : csvw_table) :
  csvw_table_schema FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema;_} -> tbl_table_schema
type csvw_metadata =
  | CSVW_Table of csvw_table 
  | CSVW_TableGroup of csvw_table Prims.list 
let uu___is_CSVW_Table (projectee : csvw_metadata) : Prims.bool=
  match projectee with | CSVW_Table _0 -> true | uu___ -> false
let __proj__CSVW_Table__item___0 (projectee : csvw_metadata) : csvw_table=
  match projectee with | CSVW_Table _0 -> _0
let uu___is_CSVW_TableGroup (projectee : csvw_metadata) : Prims.bool=
  match projectee with | CSVW_TableGroup _0 -> true | uu___ -> false
let __proj__CSVW_TableGroup__item___0 (projectee : csvw_metadata) :
  csvw_table Prims.list= match projectee with | CSVW_TableGroup _0 -> _0
let csvw_titles_value (v : Parser_JSON.json_val) : Prims.string Prims.list=
  match v with
  | Parser_JSON.JString s -> [s]
  | Parser_JSON.JArray items ->
      FStar_List_Tot_Base.concatMap
        (fun item ->
           match item with | Parser_JSON.JString s -> [s] | uu___ -> [])
        items
  | uu___ -> []
let rec csvw_titles_fields
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  Prims.string Prims.list=
  match fields with
  | [] -> []
  | (uu___, v)::tl ->
      FStar_List_Tot_Base.op_At (csvw_titles_value v) (csvw_titles_fields tl)
let csvw_decode_titles (v : Parser_JSON.json_val) : Prims.string Prims.list=
  match v with
  | Parser_JSON.JObject fields -> csvw_titles_fields fields
  | uu___ -> csvw_titles_value v
let csvw_decode_datatype (v : Parser_JSON.json_val) :
  csvw_datatype FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString s -> FStar_Pervasives_Native.Some (CSVW_DT_Named s)
  | Parser_JSON.JObject uu___ ->
      FStar_Pervasives_Native.Some
        (CSVW_DT_Object
           ((Parser_JSON.json_get_string "base" v),
             (Parser_JSON.json_get_string "format" v),
             (Parser_JSON.json_get_string "pattern" v),
             (Parser_JSON.json_get_string "groupChar" v),
             (Parser_JSON.json_get_string "decimalChar" v)))
  | uu___ -> FStar_Pervasives_Native.None
let csvw_decode_column (v : Parser_JSON.json_val) :
  csvw_column FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JObject uu___ ->
      let titles =
        match Parser_JSON.json_get_field "titles" v with
        | FStar_Pervasives_Native.Some tv -> csvw_decode_titles tv
        | FStar_Pervasives_Native.None -> [] in
      let datatype =
        match Parser_JSON.json_get_field "datatype" v with
        | FStar_Pervasives_Native.Some dv -> csvw_decode_datatype dv
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      FStar_Pervasives_Native.Some
        {
          col_name = (Parser_JSON.json_get_string "name" v);
          col_titles = titles;
          col_datatype = datatype;
          col_virtual = (Parser_JSON.json_get_bool "virtual" v);
          col_suppress_output =
            (Parser_JSON.json_get_bool "suppressOutput" v);
          col_required = (Parser_JSON.json_get_bool "required" v);
          col_about_url = (Parser_JSON.json_get_string "aboutUrl" v);
          col_property_url = (Parser_JSON.json_get_string "propertyUrl" v);
          col_value_url = (Parser_JSON.json_get_string "valueUrl" v)
        }
  | uu___ -> FStar_Pervasives_Native.None
let rec csvw_decode_column_list (items : Parser_JSON.json_val Prims.list) :
  csvw_column Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match csvw_decode_column hd with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some c ->
           (match csvw_decode_column_list tl with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rest ->
                FStar_Pervasives_Native.Some (c :: rest)))
let csvw_decode_dialect (v : Parser_JSON.json_val) :
  csvw_dialect FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JObject uu___ ->
      FStar_Pervasives_Native.Some
        {
          dia_delimiter = (Parser_JSON.json_get_string "delimiter" v);
          dia_quote_char = (Parser_JSON.json_get_string "quoteChar" v);
          dia_double_quote = (Parser_JSON.json_get_bool "doubleQuote" v);
          dia_header = (Parser_JSON.json_get_bool "header" v);
          dia_header_row_count = (json_get_int "headerRowCount" v);
          dia_skip_rows = (json_get_int "skipRows" v);
          dia_skip_columns = (json_get_int "skipColumns" v);
          dia_skip_blank_rows = (Parser_JSON.json_get_bool "skipBlankRows" v);
          dia_skip_initial_space =
            (Parser_JSON.json_get_bool "skipInitialSpace" v);
          dia_comment_prefix =
            (Parser_JSON.json_get_string "commentPrefix" v);
          dia_encoding = (Parser_JSON.json_get_string "encoding" v);
          dia_trim = (json_get_string_or_bool_as_string "trim" v)
        }
  | uu___ -> FStar_Pervasives_Native.None
let csvw_decode_table_schema (v : Parser_JSON.json_val) :
  csvw_table_schema FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JObject uu___ ->
      let uu___1 =
        match Parser_JSON.json_get_array "columns" v with
        | FStar_Pervasives_Native.None -> (true, [])
        | FStar_Pervasives_Native.Some items ->
            (match csvw_decode_column_list items with
             | FStar_Pervasives_Native.Some cs -> (true, cs)
             | FStar_Pervasives_Native.None -> (false, [])) in
      (match uu___1 with
       | (columns_ok, columns) ->
           if Prims.op_Negation columns_ok
           then FStar_Pervasives_Native.None
           else
             FStar_Pervasives_Native.Some
               {
                 ts_columns = columns;
                 ts_primary_key =
                   (Parser_JSON.json_get_string "primaryKey" v);
                 ts_about_url = (Parser_JSON.json_get_string "aboutUrl" v);
                 ts_property_url =
                   (Parser_JSON.json_get_string "propertyUrl" v);
                 ts_value_url = (Parser_JSON.json_get_string "valueUrl" v)
               })
  | uu___ -> FStar_Pervasives_Native.None
let csvw_decode_table (v : Parser_JSON.json_val) :
  csvw_table FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JObject uu___ ->
      let dialect =
        match Parser_JSON.json_get_field "dialect" v with
        | FStar_Pervasives_Native.Some dv -> csvw_decode_dialect dv
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu___1 =
        match Parser_JSON.json_get_field "tableSchema" v with
        | FStar_Pervasives_Native.None ->
            (true, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some sv ->
            (match csvw_decode_table_schema sv with
             | FStar_Pervasives_Native.Some ts ->
                 (true, (FStar_Pervasives_Native.Some ts))
             | FStar_Pervasives_Native.None ->
                 (false, FStar_Pervasives_Native.None)) in
      (match uu___1 with
       | (schema_ok, schema) ->
           if Prims.op_Negation schema_ok
           then FStar_Pervasives_Native.None
           else
             FStar_Pervasives_Native.Some
               {
                 tbl_url = (Parser_JSON.json_get_string "url" v);
                 tbl_dialect = dialect;
                 tbl_table_schema = schema
               })
  | uu___ -> FStar_Pervasives_Native.None
let rec csvw_decode_table_list (items : Parser_JSON.json_val Prims.list) :
  csvw_table Prims.list FStar_Pervasives_Native.option=
  match items with
  | [] -> FStar_Pervasives_Native.Some []
  | hd::tl ->
      (match csvw_decode_table hd with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some t ->
           (match csvw_decode_table_list tl with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some rest ->
                FStar_Pervasives_Native.Some (t :: rest)))
let csvw_decode_metadata (v : Parser_JSON.json_val) :
  csvw_metadata FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_array "tables" v with
  | FStar_Pervasives_Native.Some items ->
      (match csvw_decode_table_list items with
       | FStar_Pervasives_Native.Some ts ->
           FStar_Pervasives_Native.Some (CSVW_TableGroup ts)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.None ->
      (match csvw_decode_table v with
       | FStar_Pervasives_Native.Some t ->
           FStar_Pervasives_Native.Some (CSVW_Table t)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let csvw_decode_metadata_text (input : Prims.string) :
  csvw_metadata FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> csvw_decode_metadata v
