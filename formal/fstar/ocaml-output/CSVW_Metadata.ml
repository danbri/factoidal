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
let json_get_num_or_str (key : Prims.string) (obj : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field key obj with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      FStar_Pervasives_Native.Some s
  | FStar_Pervasives_Native.Some (Parser_JSON.JNumber s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
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
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.int FStar_Pervasives_Native.option *
  Prims.int FStar_Pervasives_Native.option * Prims.int
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option * Prims.string
  FStar_Pervasives_Native.option 
let uu___is_CSVW_DT_Named (projectee : csvw_datatype) : Prims.bool=
  match projectee with | CSVW_DT_Named _0 -> true | uu___ -> false
let __proj__CSVW_DT_Named__item___0 (projectee : csvw_datatype) :
  Prims.string= match projectee with | CSVW_DT_Named _0 -> _0
let uu___is_CSVW_DT_Object (projectee : csvw_datatype) : Prims.bool=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> true
  | uu___ -> false
let __proj__CSVW_DT_Object__item__base (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> base
let __proj__CSVW_DT_Object__item__format (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> format
let __proj__CSVW_DT_Object__item__pattern (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> pattern
let __proj__CSVW_DT_Object__item__group_char (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> group_char
let __proj__CSVW_DT_Object__item__decimal_char (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> decimal_char
let __proj__CSVW_DT_Object__item__dt_id (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_id
let __proj__CSVW_DT_Object__item__dt_length (projectee : csvw_datatype) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_length
let __proj__CSVW_DT_Object__item__dt_min_length (projectee : csvw_datatype) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_min_length
let __proj__CSVW_DT_Object__item__dt_max_length (projectee : csvw_datatype) :
  Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_max_length
let __proj__CSVW_DT_Object__item__dt_minimum (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_minimum
let __proj__CSVW_DT_Object__item__dt_maximum (projectee : csvw_datatype) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_maximum
let __proj__CSVW_DT_Object__item__dt_min_inclusive
  (projectee : csvw_datatype) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_min_inclusive
let __proj__CSVW_DT_Object__item__dt_max_inclusive
  (projectee : csvw_datatype) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_max_inclusive
let __proj__CSVW_DT_Object__item__dt_min_exclusive
  (projectee : csvw_datatype) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_min_exclusive
let __proj__CSVW_DT_Object__item__dt_max_exclusive
  (projectee : csvw_datatype) : Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | CSVW_DT_Object
      (base, format, pattern, group_char, decimal_char, dt_id, dt_length,
       dt_min_length, dt_max_length, dt_minimum, dt_maximum,
       dt_min_inclusive, dt_max_inclusive, dt_min_exclusive,
       dt_max_exclusive)
      -> dt_max_exclusive
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
  col_value_url: Prims.string FStar_Pervasives_Native.option ;
  col_separator: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkcsvw_column__item__col_name (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_name
let __proj__Mkcsvw_column__item__col_titles (projectee : csvw_column) :
  Prims.string Prims.list=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_titles
let __proj__Mkcsvw_column__item__col_datatype (projectee : csvw_column) :
  csvw_datatype FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_datatype
let __proj__Mkcsvw_column__item__col_virtual (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_virtual
let __proj__Mkcsvw_column__item__col_suppress_output
  (projectee : csvw_column) : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_suppress_output
let __proj__Mkcsvw_column__item__col_required (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_required
let __proj__Mkcsvw_column__item__col_about_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_about_url
let __proj__Mkcsvw_column__item__col_property_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_property_url
let __proj__Mkcsvw_column__item__col_value_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_value_url
let __proj__Mkcsvw_column__item__col_separator (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator;_} -> col_separator
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
  tbl_table_schema: csvw_table_schema FStar_Pervasives_Native.option ;
  tbl_common: (Prims.string * Parser_JSON.json_val) Prims.list }
let __proj__Mkcsvw_table__item__tbl_url (projectee : csvw_table) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common;_} -> tbl_url
let __proj__Mkcsvw_table__item__tbl_dialect (projectee : csvw_table) :
  csvw_dialect FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common;_} -> tbl_dialect
let __proj__Mkcsvw_table__item__tbl_table_schema (projectee : csvw_table) :
  csvw_table_schema FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common;_} ->
      tbl_table_schema
let __proj__Mkcsvw_table__item__tbl_common (projectee : csvw_table) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common;_} -> tbl_common
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
      let fmt_field = Parser_JSON.json_get_field "format" v in
      let fmt_str =
        match fmt_field with
        | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
            FStar_Pervasives_Native.Some s
        | uu___1 -> FStar_Pervasives_Native.None in
      let fmt_obj =
        match fmt_field with
        | FStar_Pervasives_Native.Some (Parser_JSON.JObject uu___1) ->
            fmt_field
        | uu___1 -> FStar_Pervasives_Native.None in
      let get_in_fmt key =
        match fmt_obj with
        | FStar_Pervasives_Native.Some o -> Parser_JSON.json_get_string key o
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      FStar_Pervasives_Native.Some
        (CSVW_DT_Object
           ((Parser_JSON.json_get_string "base" v), fmt_str,
             (get_in_fmt "pattern"), (get_in_fmt "groupChar"),
             (get_in_fmt "decimalChar"),
             (Parser_JSON.json_get_string "@id" v),
             (json_get_int "length" v), (json_get_int "minLength" v),
             (json_get_int "maxLength" v), (json_get_num_or_str "minimum" v),
             (json_get_num_or_str "maximum" v),
             (json_get_num_or_str "minInclusive" v),
             (json_get_num_or_str "maxInclusive" v),
             (json_get_num_or_str "minExclusive" v),
             (json_get_num_or_str "maxExclusive" v)))
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
          col_value_url = (Parser_JSON.json_get_string "valueUrl" v);
          col_separator = (Parser_JSON.json_get_string "separator" v)
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
let csvw_key_is_common (k : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.existsb
    (fun c -> (FStar_Char.int_of_char c) = (Prims.of_int (58)))
    (FStar_String.list_of_string k)
let csvw_common_fields (v : Parser_JSON.json_val) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match v with
  | Parser_JSON.JObject fields ->
      FStar_List_Tot_Base.filter
        (fun kv -> csvw_key_is_common (FStar_Pervasives_Native.fst kv))
        fields
  | uu___ -> []
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
                 tbl_table_schema = schema;
                 tbl_common = (csvw_common_fields v)
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
let csvw_str_starts_with (pfx : Prims.string) (s : Prims.string) :
  Prims.bool=
  let lp = FStar_String.strlen pfx in
  ((FStar_String.strlen s) >= lp) &&
    ((FStar_String.sub s Prims.int_zero lp) = pfx)
let csvw_is_bnode_ref (s : Prims.string) : Prims.bool=
  csvw_str_starts_with "_:" s
let csvw_char_is_ws (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n = (Prims.of_int (0x20))) || (n = (Prims.of_int (0x09)))) ||
     (n = (Prims.of_int (0x0A))))
    || (n = (Prims.of_int (0x0D)))
let csvw_has_ws (s : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.existsb csvw_char_is_ws (FStar_String.list_of_string s)
let rec csvw_chars_cmp (a : FStar_Char.char Prims.list)
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
      else if ix > iy then Prims.int_one else csvw_chars_cmp xs ys
let csvw_str_cmp (a : Prims.string) (b : Prims.string) : Prims.int=
  csvw_chars_cmp (FStar_String.list_of_string a)
    (FStar_String.list_of_string b)
let csvw_lex_cmp (a : Prims.string) (b : Prims.string) : Prims.int=
  match ((csvw_parse_int_string a), (csvw_parse_int_string b)) with
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
      if x < y
      then (Prims.of_int (-1))
      else if x > y then Prims.int_one else Prims.int_zero
  | uu___ -> csvw_str_cmp a b
let csvw_is_builtin_dt_url (s : Prims.string) : Prims.bool=
  (((csvw_str_starts_with "http://www.w3.org/2001/XMLSchema#" s) ||
      (s = "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML"))
     || (s = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"))
    || (s = "http://www.w3.org/ns/csvw#JSON")
let csvw_is_string_like_base (n : Prims.string) : Prims.bool=
  (((((((((((((((((((n = "string") || (n = "normalizedString")) ||
                     (n = "token"))
                    || (n = "language"))
                   || (n = "Name"))
                  || (n = "NMTOKEN"))
                 || (n = "NMTOKENS"))
                || (n = "xml"))
               || (n = "html"))
              || (n = "json"))
             || (n = "anyAtomicType"))
            || (n = "base64Binary"))
           || (n = "hexBinary"))
          || (n = "binary"))
         || (n = "anyURI"))
        || (n = "QName"))
       || (n = "ENTITY"))
      || (n = "ID"))
     || (n = "IDREF"))
    || (n = "NOTATION")
let csvw_is_ordered_base (n : Prims.string) : Prims.bool=
  (((((((((((((((((((((((((((((n = "number") || (n = "decimal")) ||
                               (n = "integer"))
                              || (n = "long"))
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
                 || (n = "float"))
                || (n = "date"))
               || (n = "dateTime"))
              || (n = "datetime"))
             || (n = "time"))
            || (n = "dateTimeStamp"))
           || (n = "gYear"))
          || (n = "gYearMonth"))
         || (n = "gMonth"))
        || (n = "gMonthDay"))
       || (n = "gDay"))
      || (n = "duration"))
     || (n = "dayTimeDuration"))
    || (n = "yearMonthDuration")
let csvw_valid_iri_token (s : Prims.string) : Prims.bool=
  (Prims.op_Negation (csvw_is_bnode_ref s)) &&
    (Prims.op_Negation (csvw_has_ws s))
let csvw_key_is_at (k : Prims.string) : Prims.bool=
  ((FStar_String.strlen k) >= Prims.int_one) &&
    ((FStar_String.sub k Prims.int_zero Prims.int_one) = "@")
let csvw_reserved_at_key (k : Prims.string) : Prims.bool=
  (((k = "@value") || (k = "@type")) || (k = "@language")) || (k = "@id")
let rec csvw_fields_no_bad_at
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::tl ->
      ((Prims.op_Negation (csvw_key_is_at k)) || (csvw_reserved_at_key k)) &&
        (csvw_fields_no_bad_at tl)
let rec csvw_fields_value_keys_ok
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::tl ->
      (((k = "@value") || (k = "@type")) || (k = "@language")) &&
        (csvw_fields_value_keys_ok tl)
let rec csvw_all_type_tokens_ok (ts : Parser_JSON.json_val Prims.list) :
  Prims.bool=
  match ts with
  | [] -> true
  | (Parser_JSON.JString t)::tl ->
      (csvw_valid_iri_token t) && (csvw_all_type_tokens_ok tl)
  | uu___ -> false
let rec csvw_common_value_valid (fuel : Prims.nat) (v : Parser_JSON.json_val)
  : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (match v with
     | Parser_JSON.JObject fields ->
         let no_bad_at = csvw_fields_no_bad_at fields in
         if Prims.op_Negation no_bad_at
         then false
         else
           (match Parser_JSON.json_get_field "@value" v with
            | FStar_Pervasives_Native.Some valv ->
                let has_type =
                  FStar_Pervasives_Native.uu___is_Some
                    (Parser_JSON.json_get_field "@type" v) in
                let has_lang =
                  FStar_Pervasives_Native.uu___is_Some
                    (Parser_JSON.json_get_field "@language" v) in
                let only_allowed = csvw_fields_value_keys_ok fields in
                let scalar_ok =
                  match valv with
                  | Parser_JSON.JString uu___2 -> true
                  | Parser_JSON.JNumber uu___2 -> true
                  | Parser_JSON.JBool uu___2 -> true
                  | uu___2 -> false in
                let type_ok =
                  match Parser_JSON.json_get_field "@type" v with
                  | FStar_Pervasives_Native.Some (Parser_JSON.JString t) ->
                      csvw_valid_iri_token t
                  | FStar_Pervasives_Native.Some uu___2 -> false
                  | FStar_Pervasives_Native.None -> true in
                let lang_ok =
                  match Parser_JSON.json_get_field "@language" v with
                  | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___2)
                      -> true
                  | FStar_Pervasives_Native.Some uu___2 -> false
                  | FStar_Pervasives_Native.None -> true in
                (((only_allowed && (Prims.op_Negation (has_type && has_lang)))
                    && scalar_ok)
                   && type_ok)
                  && lang_ok
            | FStar_Pervasives_Native.None ->
                let no_lang =
                  FStar_Pervasives_Native.uu___is_None
                    (Parser_JSON.json_get_field "@language" v) in
                let id_ok =
                  match Parser_JSON.json_get_field "@id" v with
                  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
                      Prims.op_Negation (csvw_is_bnode_ref s)
                  | FStar_Pervasives_Native.Some uu___2 -> false
                  | FStar_Pervasives_Native.None -> true in
                let type_ok =
                  match Parser_JSON.json_get_field "@type" v with
                  | FStar_Pervasives_Native.Some (Parser_JSON.JString t) ->
                      csvw_valid_iri_token t
                  | FStar_Pervasives_Native.Some (Parser_JSON.JArray ts) ->
                      csvw_all_type_tokens_ok ts
                  | FStar_Pervasives_Native.Some uu___2 -> false
                  | FStar_Pervasives_Native.None -> true in
                ((no_lang && id_ok) && type_ok) &&
                  (csvw_fields_valid (fuel - Prims.int_one) fields))
     | Parser_JSON.JArray items ->
         csvw_items_valid (fuel - Prims.int_one) items
     | uu___1 -> true)
and csvw_fields_valid (fuel : Prims.nat)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (match fields with
     | [] -> true
     | (k, vv)::tl ->
         (if csvw_key_is_at k
          then true
          else csvw_common_value_valid (fuel - Prims.int_one) vv) &&
           (csvw_fields_valid (fuel - Prims.int_one) tl))
and csvw_items_valid (fuel : Prims.nat)
  (items : Parser_JSON.json_val Prims.list) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (match items with
     | [] -> true
     | hd::tl ->
         (csvw_common_value_valid (fuel - Prims.int_one) hd) &&
           (csvw_items_valid (fuel - Prims.int_one) tl))
let rec csvw_common_props_valid_list
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, vv)::tl ->
      (if csvw_key_is_common k
       then csvw_common_value_valid (Parser_JSON.json_size vv) vv
       else true) && (csvw_common_props_valid_list tl)
let csvw_common_props_valid (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject fields -> csvw_common_props_valid_list fields
  | uu___ -> true
let csvw_obj_id_ok (v : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_field "@id" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      Prims.op_Negation (csvw_is_bnode_ref s)
  | FStar_Pervasives_Native.Some uu___ -> false
  | FStar_Pervasives_Native.None -> true
let csvw_obj_type_ok (v : Parser_JSON.json_val) (expected : Prims.string) :
  Prims.bool=
  match Parser_JSON.json_get_field "@type" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString t) -> t = expected
  | FStar_Pervasives_Native.Some uu___ -> false
  | FStar_Pervasives_Native.None -> true
let csvw_dt_base_name (dt : Parser_JSON.json_val) : Prims.string=
  match Parser_JSON.json_get_field "base" dt with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString b) -> b
  | uu___ -> "string"
let csvw_dt_has (dt : Parser_JSON.json_val) (k : Prims.string) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (Parser_JSON.json_get_field k dt)
let csvw_dt_lex (dt : Parser_JSON.json_val) (k : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field k dt with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      FStar_Pervasives_Native.Some s
  | FStar_Pervasives_Native.Some (Parser_JSON.JNumber s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let csvw_datatype_valid (dt : Parser_JSON.json_val) : Prims.bool=
  match dt with
  | Parser_JSON.JObject uu___ ->
      let idok =
        match Parser_JSON.json_get_field "@id" dt with
        | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
            (Prims.op_Negation (csvw_is_bnode_ref s)) &&
              (Prims.op_Negation (csvw_is_builtin_dt_url s))
        | FStar_Pervasives_Native.Some uu___1 -> false
        | FStar_Pervasives_Native.None -> true in
      let base = csvw_dt_base_name dt in
      let strlike = csvw_is_string_like_base base in
      let ordered = csvw_is_ordered_base base in
      let has_len =
        ((csvw_dt_has dt "length") || (csvw_dt_has dt "minLength")) ||
          (csvw_dt_has dt "maxLength") in
      let has_ord =
        (((((csvw_dt_has dt "minimum") || (csvw_dt_has dt "maximum")) ||
             (csvw_dt_has dt "minInclusive"))
            || (csvw_dt_has dt "maxInclusive"))
           || (csvw_dt_has dt "minExclusive"))
          || (csvw_dt_has dt "maxExclusive") in
      let type_ok =
        ((Prims.op_Negation has_len) || strlike) &&
          ((Prims.op_Negation has_ord) || ordered) in
      let excl_ok =
        (Prims.op_Negation
           ((csvw_dt_has dt "minInclusive") &&
              (csvw_dt_has dt "minExclusive")))
          &&
          (Prims.op_Negation
             ((csvw_dt_has dt "maxInclusive") &&
                (csvw_dt_has dt "maxExclusive"))) in
      let len_ok =
        ((match ((json_get_int "length" dt), (json_get_int "minLength" dt))
          with
          | (FStar_Pervasives_Native.Some l, FStar_Pervasives_Native.Some ml)
              -> l >= ml
          | uu___1 -> true) &&
           (match ((json_get_int "length" dt), (json_get_int "maxLength" dt))
            with
            | (FStar_Pervasives_Native.Some l, FStar_Pervasives_Native.Some
               xl) -> l <= xl
            | uu___1 -> true))
          &&
          (match ((json_get_int "minLength" dt),
                   (json_get_int "maxLength" dt))
           with
           | (FStar_Pervasives_Native.Some ml, FStar_Pervasives_Native.Some
              xl) -> ml <= xl
           | uu___1 -> true) in
      let minI = csvw_dt_lex dt "minInclusive" in
      let minE = csvw_dt_lex dt "minExclusive" in
      let maxI = csvw_dt_lex dt "maxInclusive" in
      let maxE = csvw_dt_lex dt "maxExclusive" in
      let range_ok =
        (((match (maxI, minI) with
           | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
               -> (csvw_lex_cmp a b) >= Prims.int_zero
           | uu___1 -> true) &&
            (match (maxI, minE) with
             | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some
                b) -> (csvw_lex_cmp a b) > Prims.int_zero
             | uu___1 -> true))
           &&
           (match (maxE, minE) with
            | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some
               b) -> (csvw_lex_cmp a b) > Prims.int_zero
            | uu___1 -> true))
          &&
          (match (maxE, minI) with
           | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b)
               -> (csvw_lex_cmp a b) > Prims.int_zero
           | uu___1 -> true) in
      (((idok && type_ok) && excl_ok) && len_ok) && range_ok
  | uu___ -> true
let csvw_col_name_of (c : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  Parser_JSON.json_get_string "name" c
let csvw_col_is_virtual (c : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_bool "virtual" c with
  | FStar_Pervasives_Native.Some true -> true
  | uu___ -> false
let rec csvw_names_unique (seen : Prims.string Prims.list)
  (cols : Parser_JSON.json_val Prims.list) : Prims.bool=
  match cols with
  | [] -> true
  | c::tl ->
      (match csvw_col_name_of c with
       | FStar_Pervasives_Native.Some n ->
           if FStar_List_Tot_Base.mem n seen
           then false
           else csvw_names_unique (n :: seen) tl
       | FStar_Pervasives_Native.None -> csvw_names_unique seen tl)
let rec csvw_virtual_order_ok (seen_virtual : Prims.bool)
  (cols : Parser_JSON.json_val Prims.list) : Prims.bool=
  match cols with
  | [] -> true
  | c::tl ->
      let v = csvw_col_is_virtual c in
      if seen_virtual && (Prims.op_Negation v)
      then false
      else csvw_virtual_order_ok (seen_virtual || v) tl
let rec csvw_columns_meta_ok (cols : Parser_JSON.json_val Prims.list) :
  Prims.bool=
  match cols with
  | [] -> true
  | c::tl ->
      ((((csvw_obj_id_ok c) && (csvw_obj_type_ok c "Column")) &&
          (match Parser_JSON.json_get_field "datatype" c with
           | FStar_Pervasives_Native.Some dt -> csvw_datatype_valid dt
           | FStar_Pervasives_Native.None -> true))
         && (csvw_common_props_valid c))
        && (csvw_columns_meta_ok tl)
let csvw_dialect_valid (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject uu___ ->
      (csvw_obj_id_ok v) && (csvw_obj_type_ok v "Dialect")
  | uu___ -> true
let csvw_transformation_valid (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject uu___ ->
      (csvw_obj_id_ok v) && (csvw_obj_type_ok v "Template")
  | uu___ -> true
let rec csvw_transformations_all_valid
  (items : Parser_JSON.json_val Prims.list) : Prims.bool=
  match items with
  | [] -> true
  | t::tl ->
      (csvw_transformation_valid t) && (csvw_transformations_all_valid tl)
let csvw_transformations_ok (v : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_array "transformations" v with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some items ->
      csvw_transformations_all_valid items
let rec csvw_column_names (cols : Parser_JSON.json_val Prims.list) :
  Prims.string Prims.list=
  match cols with
  | [] -> []
  | c::tl ->
      (match Parser_JSON.json_get_string "name" c with
       | FStar_Pervasives_Native.Some n -> n :: (csvw_column_names tl)
       | FStar_Pervasives_Native.None -> csvw_column_names tl)
let csvw_colref_ok (names : Prims.string Prims.list)
  (v : Parser_JSON.json_val) : Prims.bool=
  if Prims.uu___is_Nil names
  then true
  else
    (match v with
     | Parser_JSON.JString s -> FStar_List_Tot_Base.mem s names
     | Parser_JSON.JArray items ->
         FStar_List_Tot_Base.for_all
           (fun x ->
              match x with
              | Parser_JSON.JString s -> FStar_List_Tot_Base.mem s names
              | uu___1 -> false) items
     | uu___1 -> false)
let csvw_fk_valid (names : Prims.string Prims.list)
  (fk : Parser_JSON.json_val) : Prims.bool=
  match fk with
  | Parser_JSON.JObject fields ->
      ((FStar_List_Tot_Base.for_all
          (fun kv ->
             let k = FStar_Pervasives_Native.fst kv in
             (k = "columnReference") || (k = "reference")) fields)
         &&
         (match Parser_JSON.json_get_field "columnReference" fk with
          | FStar_Pervasives_Native.Some cr -> csvw_colref_ok names cr
          | FStar_Pervasives_Native.None -> false))
        &&
        ((match Parser_JSON.json_get_field "reference" fk with
          | FStar_Pervasives_Native.Some (Parser_JSON.JObject rfields) ->
              (FStar_List_Tot_Base.for_all
                 (fun kv ->
                    let k = FStar_Pervasives_Native.fst kv in
                    ((k = "resource") || (k = "schemaReference")) ||
                      (k = "columnReference")) rfields)
                &&
                (FStar_Pervasives_Native.uu___is_Some
                   (Parser_JSON.json_get_field "columnReference"
                      (Parser_JSON.JObject rfields)))
          | FStar_Pervasives_Native.Some uu___ -> false
          | FStar_Pervasives_Native.None -> false))
  | uu___ -> false
let rec csvw_fks_all_valid (names : Prims.string Prims.list)
  (fks : Parser_JSON.json_val Prims.list) : Prims.bool=
  match fks with
  | [] -> true
  | fk::tl -> (csvw_fk_valid names fk) && (csvw_fks_all_valid names tl)
let csvw_schema_valid (v : Parser_JSON.json_val) : Prims.bool=
  match v with
  | Parser_JSON.JObject uu___ ->
      let names =
        match Parser_JSON.json_get_array "columns" v with
        | FStar_Pervasives_Native.Some cols -> csvw_column_names cols
        | FStar_Pervasives_Native.None -> [] in
      (((csvw_obj_id_ok v) && (csvw_obj_type_ok v "Schema")) &&
         (match Parser_JSON.json_get_array "columns" v with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some cols ->
              ((csvw_names_unique [] cols) &&
                 (csvw_virtual_order_ok false cols))
                && (csvw_columns_meta_ok cols)))
        &&
        ((match Parser_JSON.json_get_array "foreignKeys" v with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some fks -> csvw_fks_all_valid names fks))
  | uu___ -> true
let csvw_table_valid (in_group : Prims.bool) (v : Parser_JSON.json_val) :
  Prims.bool=
  match v with
  | Parser_JSON.JObject uu___ ->
      ((((((csvw_obj_id_ok v) && (csvw_obj_type_ok v "Table")) &&
            (match Parser_JSON.json_get_field "url" v with
             | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___1) ->
                 true
             | FStar_Pervasives_Native.Some uu___1 -> false
             | FStar_Pervasives_Native.None -> Prims.op_Negation in_group))
           &&
           (match Parser_JSON.json_get_field "dialect" v with
            | FStar_Pervasives_Native.Some d -> csvw_dialect_valid d
            | FStar_Pervasives_Native.None -> true))
          &&
          (match Parser_JSON.json_get_field "tableSchema" v with
           | FStar_Pervasives_Native.Some s -> csvw_schema_valid s
           | FStar_Pervasives_Native.None -> true))
         && (csvw_transformations_ok v))
        && (csvw_common_props_valid v)
  | uu___ -> false
let rec csvw_tables_all_valid (items : Parser_JSON.json_val Prims.list) :
  Prims.bool=
  match items with
  | [] -> true
  | t::tl -> (csvw_table_valid true t) && (csvw_tables_all_valid tl)
let csvw_context_valid (v : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_field "@context" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray
      (uu___::(Parser_JSON.JObject fields)::[])) ->
      FStar_List_Tot_Base.for_all
        (fun kv ->
           let k = FStar_Pervasives_Native.fst kv in
           (k = "@base") || (k = "@language")) fields
  | uu___ -> true
let csvw_metadata_valid (v : Parser_JSON.json_val) : Prims.bool=
  ((csvw_context_valid v) && (csvw_obj_id_ok v)) &&
    (match Parser_JSON.json_get_field "tables" v with
     | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
         ((((Prims.uu___is_Cons items) && (csvw_obj_type_ok v "TableGroup"))
             && (csvw_transformations_ok v))
            && (csvw_common_props_valid v))
           && (csvw_tables_all_valid items)
     | FStar_Pervasives_Native.Some uu___ -> false
     | FStar_Pervasives_Native.None -> csvw_table_valid false v)
let csvw_decode_metadata (v : Parser_JSON.json_val) :
  csvw_metadata FStar_Pervasives_Native.option=
  if Prims.op_Negation (csvw_metadata_valid v)
  then FStar_Pervasives_Native.None
  else
    (match Parser_JSON.json_get_array "tables" v with
     | FStar_Pervasives_Native.Some items ->
         (match csvw_decode_table_list items with
          | FStar_Pervasives_Native.Some ts ->
              FStar_Pervasives_Native.Some (CSVW_TableGroup ts)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | FStar_Pervasives_Native.None ->
         (match csvw_decode_table v with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (CSVW_Table t)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let csvw_decode_metadata_text (input : Prims.string) :
  csvw_metadata FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> csvw_decode_metadata v
