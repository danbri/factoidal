open Prims
type query_timing =
  {
  qt_parse_ms_str: Prims.string ;
  qt_eval_ms_str: Prims.string ;
  qt_format_ms_str: Prims.string ;
  qt_total_ms_str: Prims.string ;
  qt_status: Prims.nat ;
  qt_rows: Prims.int ;
  qt_form: Prims.string ;
  qt_body_bytes: Prims.nat }
let __proj__Mkquery_timing__item__qt_parse_ms_str (projectee : query_timing)
  : Prims.string=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_parse_ms_str
let __proj__Mkquery_timing__item__qt_eval_ms_str (projectee : query_timing) :
  Prims.string=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_eval_ms_str
let __proj__Mkquery_timing__item__qt_format_ms_str (projectee : query_timing)
  : Prims.string=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_format_ms_str
let __proj__Mkquery_timing__item__qt_total_ms_str (projectee : query_timing)
  : Prims.string=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_total_ms_str
let __proj__Mkquery_timing__item__qt_status (projectee : query_timing) :
  Prims.nat=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_status
let __proj__Mkquery_timing__item__qt_rows (projectee : query_timing) :
  Prims.int=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_rows
let __proj__Mkquery_timing__item__qt_form (projectee : query_timing) :
  Prims.string=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_form
let __proj__Mkquery_timing__item__qt_body_bytes (projectee : query_timing) :
  Prims.nat=
  match projectee with
  | { qt_parse_ms_str; qt_eval_ms_str; qt_format_ms_str; qt_total_ms_str;
      qt_status; qt_rows; qt_form; qt_body_bytes;_} -> qt_body_bytes
let form_select : Prims.string= "SELECT"
let form_ask : Prims.string= "ASK"
let form_construct : Prims.string= "CONSTRUCT"
let form_describe : Prims.string= "DESCRIBE"
let form_parse_error : Prims.string= "parse-error"
let form_eval_error : Prims.string= "eval-error"
let rows_unknown : Prims.int= (Prims.of_int (-1))
let zero_timing : query_timing=
  {
    qt_parse_ms_str = "0.0";
    qt_eval_ms_str = "0.0";
    qt_format_ms_str = "0.0";
    qt_total_ms_str = "0.0";
    qt_status = Prims.int_zero;
    qt_rows = rows_unknown;
    qt_form = form_parse_error;
    qt_body_bytes = Prims.int_zero
  }
