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
  col_separator: Prims.string FStar_Pervasives_Native.option ;
  col_lang: Prims.string FStar_Pervasives_Native.option ;
  col_null: Prims.string FStar_Pervasives_Native.option ;
  col_ordered: Prims.bool FStar_Pervasives_Native.option }
let __proj__Mkcsvw_column__item__col_name (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_name
let __proj__Mkcsvw_column__item__col_titles (projectee : csvw_column) :
  Prims.string Prims.list=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_titles
let __proj__Mkcsvw_column__item__col_datatype (projectee : csvw_column) :
  csvw_datatype FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_datatype
let __proj__Mkcsvw_column__item__col_virtual (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_virtual
let __proj__Mkcsvw_column__item__col_suppress_output
  (projectee : csvw_column) : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} ->
      col_suppress_output
let __proj__Mkcsvw_column__item__col_required (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_required
let __proj__Mkcsvw_column__item__col_about_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_about_url
let __proj__Mkcsvw_column__item__col_property_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_property_url
let __proj__Mkcsvw_column__item__col_value_url (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_value_url
let __proj__Mkcsvw_column__item__col_separator (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_separator
let __proj__Mkcsvw_column__item__col_lang (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_lang
let __proj__Mkcsvw_column__item__col_null (projectee : csvw_column) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_null
let __proj__Mkcsvw_column__item__col_ordered (projectee : csvw_column) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { col_name; col_titles; col_datatype; col_virtual; col_suppress_output;
      col_required; col_about_url; col_property_url; col_value_url;
      col_separator; col_lang; col_null; col_ordered;_} -> col_ordered
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
type csvw_inherited_props =
  {
  inh_about_url: Prims.string FStar_Pervasives_Native.option ;
  inh_property_url: Prims.string FStar_Pervasives_Native.option ;
  inh_value_url: Prims.string FStar_Pervasives_Native.option ;
  inh_lang: Prims.string FStar_Pervasives_Native.option ;
  inh_null: Prims.string FStar_Pervasives_Native.option ;
  inh_separator: Prims.string FStar_Pervasives_Native.option ;
  inh_datatype: csvw_datatype FStar_Pervasives_Native.option ;
  inh_ordered: Prims.bool FStar_Pervasives_Native.option }
let __proj__Mkcsvw_inherited_props__item__inh_about_url
  (projectee : csvw_inherited_props) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_about_url
let __proj__Mkcsvw_inherited_props__item__inh_property_url
  (projectee : csvw_inherited_props) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_property_url
let __proj__Mkcsvw_inherited_props__item__inh_value_url
  (projectee : csvw_inherited_props) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_value_url
let __proj__Mkcsvw_inherited_props__item__inh_lang
  (projectee : csvw_inherited_props) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_lang
let __proj__Mkcsvw_inherited_props__item__inh_null
  (projectee : csvw_inherited_props) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_null
let __proj__Mkcsvw_inherited_props__item__inh_separator
  (projectee : csvw_inherited_props) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_separator
let __proj__Mkcsvw_inherited_props__item__inh_datatype
  (projectee : csvw_inherited_props) :
  csvw_datatype FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_datatype
let __proj__Mkcsvw_inherited_props__item__inh_ordered
  (projectee : csvw_inherited_props) :
  Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { inh_about_url; inh_property_url; inh_value_url; inh_lang; inh_null;
      inh_separator; inh_datatype; inh_ordered;_} -> inh_ordered
let csvw_inherited_empty : csvw_inherited_props=
  {
    inh_about_url = FStar_Pervasives_Native.None;
    inh_property_url = FStar_Pervasives_Native.None;
    inh_value_url = FStar_Pervasives_Native.None;
    inh_lang = FStar_Pervasives_Native.None;
    inh_null = FStar_Pervasives_Native.None;
    inh_separator = FStar_Pervasives_Native.None;
    inh_datatype = FStar_Pervasives_Native.None;
    inh_ordered = FStar_Pervasives_Native.None
  }
type csvw_table_schema =
  {
  ts_columns: csvw_column Prims.list ;
  ts_primary_key: Prims.string FStar_Pervasives_Native.option ;
  ts_inherited: csvw_inherited_props ;
  ts_row_titles: Prims.string Prims.list }
let __proj__Mkcsvw_table_schema__item__ts_columns
  (projectee : csvw_table_schema) : csvw_column Prims.list=
  match projectee with
  | { ts_columns; ts_primary_key; ts_inherited; ts_row_titles;_} ->
      ts_columns
let __proj__Mkcsvw_table_schema__item__ts_primary_key
  (projectee : csvw_table_schema) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ts_columns; ts_primary_key; ts_inherited; ts_row_titles;_} ->
      ts_primary_key
let __proj__Mkcsvw_table_schema__item__ts_inherited
  (projectee : csvw_table_schema) : csvw_inherited_props=
  match projectee with
  | { ts_columns; ts_primary_key; ts_inherited; ts_row_titles;_} ->
      ts_inherited
let __proj__Mkcsvw_table_schema__item__ts_row_titles
  (projectee : csvw_table_schema) : Prims.string Prims.list=
  match projectee with
  | { ts_columns; ts_primary_key; ts_inherited; ts_row_titles;_} ->
      ts_row_titles
type csvw_table =
  {
  tbl_url: Prims.string FStar_Pervasives_Native.option ;
  tbl_dialect: csvw_dialect FStar_Pervasives_Native.option ;
  tbl_table_schema: csvw_table_schema FStar_Pervasives_Native.option ;
  tbl_common: (Prims.string * Parser_JSON.json_val) Prims.list ;
  tbl_inherited: csvw_inherited_props ;
  tbl_schema_ref: Prims.string FStar_Pervasives_Native.option ;
  tbl_suppress_output: Prims.bool FStar_Pervasives_Native.option }
let __proj__Mkcsvw_table__item__tbl_url (projectee : csvw_table) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_url
let __proj__Mkcsvw_table__item__tbl_dialect (projectee : csvw_table) :
  csvw_dialect FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_dialect
let __proj__Mkcsvw_table__item__tbl_table_schema (projectee : csvw_table) :
  csvw_table_schema FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_table_schema
let __proj__Mkcsvw_table__item__tbl_common (projectee : csvw_table) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_common
let __proj__Mkcsvw_table__item__tbl_inherited (projectee : csvw_table) :
  csvw_inherited_props=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_inherited
let __proj__Mkcsvw_table__item__tbl_schema_ref (projectee : csvw_table) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_schema_ref
let __proj__Mkcsvw_table__item__tbl_suppress_output (projectee : csvw_table)
  : Prims.bool FStar_Pervasives_Native.option=
  match projectee with
  | { tbl_url; tbl_dialect; tbl_table_schema; tbl_common; tbl_inherited;
      tbl_schema_ref; tbl_suppress_output;_} -> tbl_suppress_output
type csvw_group_meta =
  {
  grp_common: (Prims.string * Parser_JSON.json_val) Prims.list ;
  grp_inherited: csvw_inherited_props }
let __proj__Mkcsvw_group_meta__item__grp_common (projectee : csvw_group_meta)
  : (Prims.string * Parser_JSON.json_val) Prims.list=
  match projectee with | { grp_common; grp_inherited;_} -> grp_common
let __proj__Mkcsvw_group_meta__item__grp_inherited
  (projectee : csvw_group_meta) : csvw_inherited_props=
  match projectee with | { grp_common; grp_inherited;_} -> grp_inherited
let csvw_group_meta_empty : csvw_group_meta=
  { grp_common = []; grp_inherited = csvw_inherited_empty }
type csvw_metadata =
  | CSVW_Table of csvw_table 
  | CSVW_TableGroup of csvw_table Prims.list * csvw_group_meta 
let uu___is_CSVW_Table (projectee : csvw_metadata) : Prims.bool=
  match projectee with | CSVW_Table _0 -> true | uu___ -> false
let __proj__CSVW_Table__item___0 (projectee : csvw_metadata) : csvw_table=
  match projectee with | CSVW_Table _0 -> _0
let uu___is_CSVW_TableGroup (projectee : csvw_metadata) : Prims.bool=
  match projectee with | CSVW_TableGroup (_0, _1) -> true | uu___ -> false
let __proj__CSVW_TableGroup__item___0 (projectee : csvw_metadata) :
  csvw_table Prims.list=
  match projectee with | CSVW_TableGroup (_0, _1) -> _0
let __proj__CSVW_TableGroup__item___1 (projectee : csvw_metadata) :
  csvw_group_meta= match projectee with | CSVW_TableGroup (_0, _1) -> _1
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
let csvw_inh_char_is_alpha (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
    ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122))))
let csvw_inh_char_is_alnum (c : FStar_Char.char) : Prims.bool=
  (csvw_inh_char_is_alpha c) ||
    (let n = FStar_Char.int_of_char c in
     (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57))))
let rec csvw_inh_split_hyphen (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) : FStar_Char.char Prims.list Prims.list=
  match cs with
  | [] -> [FStar_List_Tot_Base.rev acc]
  | c::tl ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (45))
      then (FStar_List_Tot_Base.rev acc) :: (csvw_inh_split_hyphen tl [])
      else csvw_inh_split_hyphen tl (c :: acc)
let csvw_lang_tag_ok (s : Prims.string) : Prims.bool=
  match csvw_inh_split_hyphen (FStar_String.list_of_string s) [] with
  | [] -> false
  | first::rest ->
      let fl = FStar_List_Tot_Base.length first in
      (((fl >= (Prims.of_int (2))) && (fl <= (Prims.of_int (8)))) &&
         (FStar_List_Tot_Base.for_all csvw_inh_char_is_alpha first))
        &&
        (FStar_List_Tot_Base.for_all
           (fun sub ->
              let l = FStar_List_Tot_Base.length sub in
              ((l >= Prims.int_one) && (l <= (Prims.of_int (8)))) &&
                (FStar_List_Tot_Base.for_all csvw_inh_char_is_alnum sub))
           rest)
let csvw_builtin_datatype_names : Prims.string Prims.list=
  ["anyAtomicType";
  "anyURI";
  "base64Binary";
  "boolean";
  "byte";
  "date";
  "dateTime";
  "dateTimeStamp";
  "dayTimeDuration";
  "decimal";
  "double";
  "duration";
  "float";
  "gDay";
  "gMonth";
  "gMonthDay";
  "gYear";
  "gYearMonth";
  "hexBinary";
  "int";
  "integer";
  "language";
  "long";
  "Name";
  "negativeInteger";
  "NMTOKEN";
  "nonNegativeInteger";
  "nonPositiveInteger";
  "normalizedString";
  "positiveInteger";
  "QName";
  "short";
  "string";
  "time";
  "token";
  "unsignedByte";
  "unsignedInt";
  "unsignedLong";
  "unsignedShort";
  "xml";
  "html";
  "json";
  "number";
  "binary";
  "datetime";
  "any";
  "yearMonthDuration"]
let csvw_is_builtin_datatype_name (s : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.mem s csvw_builtin_datatype_names
let csvw_datatype_valid_or_degrade (d : csvw_datatype) :
  csvw_datatype FStar_Pervasives_Native.option=
  match d with
  | CSVW_DT_Named n ->
      if csvw_is_builtin_datatype_name n
      then FStar_Pervasives_Native.Some d
      else FStar_Pervasives_Native.None
  | CSVW_DT_Object
      (base_opt, uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
       uu___7, uu___8, uu___9, uu___10, uu___11, uu___12, uu___13)
      ->
      (match base_opt with
       | FStar_Pervasives_Native.Some b ->
           if csvw_is_builtin_datatype_name b
           then FStar_Pervasives_Native.Some d
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some d)
let csvw_inh_uri_template (key : Prims.string) (v : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field key v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
      FStar_Pervasives_Native.Some s
  | FStar_Pervasives_Native.Some (Parser_JSON.JBool uu___) ->
      FStar_Pervasives_Native.Some ""
  | FStar_Pervasives_Native.Some (Parser_JSON.JNumber uu___) ->
      FStar_Pervasives_Native.Some ""
  | uu___ -> FStar_Pervasives_Native.None
let csvw_decode_inherited (v : Parser_JSON.json_val) : csvw_inherited_props=
  {
    inh_about_url = (csvw_inh_uri_template "aboutUrl" v);
    inh_property_url = (csvw_inh_uri_template "propertyUrl" v);
    inh_value_url = (csvw_inh_uri_template "valueUrl" v);
    inh_lang =
      (match Parser_JSON.json_get_string "lang" v with
       | FStar_Pervasives_Native.Some l ->
           if csvw_lang_tag_ok l
           then FStar_Pervasives_Native.Some l
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None);
    inh_null = (Parser_JSON.json_get_string "null" v);
    inh_separator = (Parser_JSON.json_get_string "separator" v);
    inh_datatype =
      (match Parser_JSON.json_get_field "datatype" v with
       | FStar_Pervasives_Native.Some dv ->
           (match csvw_decode_datatype dv with
            | FStar_Pervasives_Native.Some d ->
                csvw_datatype_valid_or_degrade d
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None);
    inh_ordered = (Parser_JSON.json_get_bool "ordered" v)
  }
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
        | FStar_Pervasives_Native.Some dv ->
            (match csvw_decode_datatype dv with
             | FStar_Pervasives_Native.Some d ->
                 csvw_datatype_valid_or_degrade d
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
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
          col_separator = (Parser_JSON.json_get_string "separator" v);
          col_lang = (Parser_JSON.json_get_string "lang" v);
          col_null = (Parser_JSON.json_get_string "null" v);
          col_ordered = (Parser_JSON.json_get_bool "ordered" v)
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
                 ts_inherited = (csvw_decode_inherited v);
                 ts_row_titles =
                   ((match Parser_JSON.json_get_field "rowTitles" v with
                     | FStar_Pervasives_Native.Some rv ->
                         csvw_titles_value rv
                     | FStar_Pervasives_Native.None -> []))
               })
  | uu___ ->
      FStar_Pervasives_Native.Some
        {
          ts_columns = [];
          ts_primary_key = FStar_Pervasives_Native.None;
          ts_inherited = csvw_inherited_empty;
          ts_row_titles = []
        }
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
      let schema_ref =
        match Parser_JSON.json_get_field "tableSchema" v with
        | FStar_Pervasives_Native.Some (Parser_JSON.JString s) ->
            FStar_Pervasives_Native.Some s
        | uu___1 -> FStar_Pervasives_Native.None in
      let uu___1 =
        match Parser_JSON.json_get_field "tableSchema" v with
        | FStar_Pervasives_Native.None ->
            (true, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some (Parser_JSON.JString uu___2) ->
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
                 tbl_common = (csvw_common_fields v);
                 tbl_inherited = (csvw_decode_inherited v);
                 tbl_schema_ref = schema_ref;
                 tbl_suppress_output =
                   (Parser_JSON.json_get_bool "suppressOutput" v)
               })
  | uu___ -> FStar_Pervasives_Native.None
let csvw_decode_table_schema_text (input : Prims.string) :
  csvw_table_schema FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> csvw_decode_table_schema v
let csvw_table_inline_schema (t : csvw_table) (ts : csvw_table_schema) :
  csvw_table=
  {
    tbl_url = (t.tbl_url);
    tbl_dialect = (t.tbl_dialect);
    tbl_table_schema = (FStar_Pervasives_Native.Some ts);
    tbl_common = (t.tbl_common);
    tbl_inherited = (t.tbl_inherited);
    tbl_schema_ref = FStar_Pervasives_Native.None;
    tbl_suppress_output = (t.tbl_suppress_output)
  }
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
  | FStar_Pervasives_Native.Some uu___ -> true
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
  | fk::tl ->
      (match fk with
       | Parser_JSON.JObject uu___ -> csvw_fk_valid names fk
       | uu___ -> true) && (csvw_fks_all_valid names tl)
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
let csvw_table_fk_objs (t : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match Parser_JSON.json_get_field "tableSchema" t with
  | FStar_Pervasives_Native.Some ts ->
      (match Parser_JSON.json_get_field "foreignKeys" ts with
       | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
           FStar_List_Tot_Base.filter
             (fun i -> Parser_JSON.uu___is_JObject i) items
       | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
           [Parser_JSON.JObject fields]
       | uu___ -> [])
  | uu___ -> []
let csvw_table_inline_names (t : Parser_JSON.json_val) :
  Prims.string Prims.list=
  match Parser_JSON.json_get_field "tableSchema" t with
  | FStar_Pervasives_Native.Some ts ->
      (match Parser_JSON.json_get_array "columns" ts with
       | FStar_Pervasives_Native.Some cols -> csvw_column_names cols
       | FStar_Pervasives_Native.None -> [])
  | uu___ -> []
let csvw_ref_cols (refobj : Parser_JSON.json_val) : Prims.string Prims.list=
  match Parser_JSON.json_get_field "columnReference" refobj with
  | FStar_Pervasives_Native.Some (Parser_JSON.JString s) -> [s]
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
      FStar_List_Tot_Base.concatMap
        (fun i -> match i with | Parser_JSON.JString s -> [s] | uu___ -> [])
        items
  | uu___ -> []
let rec csvw_find_table_by_url (all : Parser_JSON.json_val Prims.list)
  (res : Prims.string) : Parser_JSON.json_val FStar_Pervasives_Native.option=
  match all with
  | [] -> FStar_Pervasives_Native.None
  | t::tl ->
      (match Parser_JSON.json_get_string "url" t with
       | FStar_Pervasives_Native.Some u ->
           if u = res
           then FStar_Pervasives_Native.Some t
           else csvw_find_table_by_url tl res
       | FStar_Pervasives_Native.None -> csvw_find_table_by_url tl res)
let csvw_fk_resolves (all : Parser_JSON.json_val Prims.list)
  (fk : Parser_JSON.json_val) : Prims.bool=
  match Parser_JSON.json_get_field "reference" fk with
  | FStar_Pervasives_Native.Some rf ->
      (match Parser_JSON.json_get_field "resource" rf with
       | FStar_Pervasives_Native.Some (Parser_JSON.JString res) ->
           (match csvw_find_table_by_url all res with
            | FStar_Pervasives_Native.None -> false
            | FStar_Pervasives_Native.Some tgt ->
                (match csvw_table_inline_names tgt with
                 | [] -> true
                 | tnames ->
                     FStar_List_Tot_Base.for_all
                       (fun c -> FStar_List_Tot_Base.mem c tnames)
                       (csvw_ref_cols rf)))
       | uu___ -> true)
  | FStar_Pervasives_Native.None -> true
let rec csvw_fks_resolve_list (all : Parser_JSON.json_val Prims.list)
  (fks : Parser_JSON.json_val Prims.list) : Prims.bool=
  match fks with
  | [] -> true
  | fk::tl -> (csvw_fk_resolves all fk) && (csvw_fks_resolve_list all tl)
let rec csvw_group_fks_resolve (all : Parser_JSON.json_val Prims.list)
  (remaining : Parser_JSON.json_val Prims.list) : Prims.bool=
  match remaining with
  | [] -> true
  | t::tl ->
      (csvw_fks_resolve_list all (csvw_table_fk_objs t)) &&
        (csvw_group_fks_resolve all tl)
let csvw_metadata_valid (v : Parser_JSON.json_val) : Prims.bool=
  ((csvw_context_valid v) && (csvw_obj_id_ok v)) &&
    (match Parser_JSON.json_get_field "tables" v with
     | FStar_Pervasives_Native.Some (Parser_JSON.JArray items) ->
         (((((Prims.uu___is_Cons items) && (csvw_obj_type_ok v "TableGroup"))
              && (csvw_transformations_ok v))
             && (csvw_common_props_valid v))
            && (csvw_tables_all_valid items))
           && (csvw_group_fks_resolve items items)
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
              let grp_dia =
                match Parser_JSON.json_get_field "dialect" v with
                | FStar_Pervasives_Native.Some dv -> csvw_decode_dialect dv
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None in
              let ts_dia =
                FStar_List_Tot_Base.map
                  (fun t ->
                     match t.tbl_dialect with
                     | FStar_Pervasives_Native.Some uu___1 -> t
                     | FStar_Pervasives_Native.None ->
                         {
                           tbl_url = (t.tbl_url);
                           tbl_dialect = grp_dia;
                           tbl_table_schema = (t.tbl_table_schema);
                           tbl_common = (t.tbl_common);
                           tbl_inherited = (t.tbl_inherited);
                           tbl_schema_ref = (t.tbl_schema_ref);
                           tbl_suppress_output = (t.tbl_suppress_output)
                         }) ts in
              FStar_Pervasives_Native.Some
                (CSVW_TableGroup
                   (ts_dia,
                     {
                       grp_common = (csvw_common_fields v);
                       grp_inherited = (csvw_decode_inherited v)
                     }))
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
let csvw_bracketed_url (s : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  let rec after_lt cs =
    match cs with
    | [] -> FStar_Pervasives_Native.None
    | c::tl ->
        if (FStar_Char.int_of_char c) = (Prims.of_int (60))
        then FStar_Pervasives_Native.Some tl
        else after_lt tl in
  let rec until_gt cs acc =
    match cs with
    | [] -> FStar_Pervasives_Native.None
    | c::tl ->
        if (FStar_Char.int_of_char c) = (Prims.of_int (62))
        then FStar_Pervasives_Native.Some (FStar_List_Tot_Base.rev acc)
        else until_gt tl (c :: acc) in
  match after_lt (FStar_String.list_of_string s) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some rest ->
      (match until_gt rest [] with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some url ->
           FStar_Pervasives_Native.Some (FStar_String.string_of_list url))
let rec csvw_chars_has_prefix (needle : FStar_Char.char Prims.list)
  (hay : FStar_Char.char Prims.list) : Prims.bool=
  match (needle, hay) with
  | ([], uu___) -> true
  | (uu___, []) -> false
  | (n::nt, h::ht) ->
      ((FStar_Char.int_of_char n) = (FStar_Char.int_of_char h)) &&
        (csvw_chars_has_prefix nt ht)
let rec csvw_chars_contains (needle : FStar_Char.char Prims.list)
  (hay : FStar_Char.char Prims.list) : Prims.bool=
  if csvw_chars_has_prefix needle hay
  then true
  else
    (match hay with
     | [] -> false
     | uu___1::tl -> csvw_chars_contains needle tl)
let csvw_str_contains (needle : Prims.string) (hay : Prims.string) :
  Prims.bool=
  csvw_chars_contains (FStar_String.list_of_string needle)
    (FStar_String.list_of_string hay)
let csvw_link_header_describedby (link_value : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  if csvw_str_contains "describedby" link_value
  then csvw_bracketed_url link_value
  else FStar_Pervasives_Native.None
let csvw_context_language (v : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field "@context" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray ctx) ->
      (match ctx with
       | uu___::second::[] ->
           (match Parser_JSON.json_get_string "@language" second with
            | FStar_Pervasives_Native.Some l ->
                if csvw_lang_tag_ok l
                then FStar_Pervasives_Native.Some l
                else FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let csvw_metadata_context_language (input : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> csvw_context_language v
let csvw_context_base (v : Parser_JSON.json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field "@context" v with
  | FStar_Pervasives_Native.Some (Parser_JSON.JArray ctx) ->
      (match ctx with
       | uu___::second::[] -> Parser_JSON.json_get_string "@base" second
       | uu___ -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let csvw_metadata_context_base (input : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v -> csvw_context_base v
