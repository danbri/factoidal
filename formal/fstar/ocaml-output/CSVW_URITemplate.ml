open Prims
type csvw_template_segment =
  | CT_Literal of Prims.string 
  | CT_Var of Prims.string 
let uu___is_CT_Literal (projectee : csvw_template_segment) : Prims.bool=
  match projectee with | CT_Literal _0 -> true | uu___ -> false
let __proj__CT_Literal__item___0 (projectee : csvw_template_segment) :
  Prims.string= match projectee with | CT_Literal _0 -> _0
let uu___is_CT_Var (projectee : csvw_template_segment) : Prims.bool=
  match projectee with | CT_Var _0 -> true | uu___ -> false
let __proj__CT_Var__item___0 (projectee : csvw_template_segment) :
  Prims.string= match projectee with | CT_Var _0 -> _0
let csvw_flush_template_buf (mode : Prims.bool) (buf : Prims.string)
  (acc : csvw_template_segment Prims.list) :
  csvw_template_segment Prims.list=
  if buf = ""
  then acc
  else if mode then (CT_Var buf) :: acc else (CT_Literal buf) :: acc
let rec csvw_scan_template_acc (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (mode : Prims.bool) (buf : Prims.string)
  (acc : csvw_template_segment Prims.list) :
  csvw_template_segment Prims.list=
  if fuel = Prims.int_zero
  then csvw_flush_template_buf mode buf acc
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then csvw_flush_template_buf mode buf acc
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if (Prims.op_Negation mode) && (c = (Prims.of_int (0x7B)))
        then
          let acc' = if buf = "" then acc else (CT_Literal buf) :: acc in
          csvw_scan_template_acc s (pos + Prims.int_one)
            (fuel - Prims.int_one) true "" acc'
        else
          if mode && (c = (Prims.of_int (0x7D)))
          then
            csvw_scan_template_acc s (pos + Prims.int_one)
              (fuel - Prims.int_one) false "" ((CT_Var buf) :: acc)
          else
            csvw_scan_template_acc s (pos + Prims.int_one)
              (fuel - Prims.int_one) mode
              (Prims.strcat buf (FStar_String.sub s pos Prims.int_one)) acc))
let csvw_parse_template (s : Prims.string) :
  csvw_template_segment Prims.list=
  FStar_List_Tot_Base.rev
    (csvw_scan_template_acc s Prims.int_zero
       ((FStar_String.strlen s) + Prims.int_one) false "" [])
let is_uri_reserved_gen_sub_delim (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((((((((((((code = (Prims.of_int (0x3A))) ||
                    (code = (Prims.of_int (0x2F))))
                   || (code = (Prims.of_int (0x3F))))
                  || (code = (Prims.of_int (0x23))))
                 || (code = (Prims.of_int (0x5B))))
                || (code = (Prims.of_int (0x5D))))
               || (code = (Prims.of_int (0x40))))
              || (code = (Prims.of_int (0x21))))
             || (code = (Prims.of_int (0x24))))
            || (code = (Prims.of_int (0x26))))
           || (code = (Prims.of_int (0x27))))
          || (code = (Prims.of_int (0x28))))
         || (code = (Prims.of_int (0x29))))
        || (code = (Prims.of_int (0x2A))))
       || (code = (Prims.of_int (0x2B))))
      || (code = (Prims.of_int (0x2C))))
     || (code = (Prims.of_int (0x3B))))
    || (code = (Prims.of_int (0x3D)))
let is_uri_reserved_or_unreserved (c : FStar_Char.char) : Prims.bool=
  (SPARQL11_Algebra.is_uri_unreserved c) || (is_uri_reserved_gen_sub_delim c)
let rec csvw_encode_fragment_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if is_uri_reserved_or_unreserved c
      then c :: (csvw_encode_fragment_chars rest)
      else
        FStar_List_Tot_Base.append (SPARQL11_Algebra.percent_encode_char c)
          (csvw_encode_fragment_chars rest)
let csvw_encode_fragment (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (csvw_encode_fragment_chars (FStar_String.list_of_string s))
let csvw_var_is_fragment (v : Prims.string) : Prims.bool=
  ((FStar_String.strlen v) > Prims.int_zero) &&
    ((FStar_String.sub v Prims.int_zero Prims.int_one) = "#")
let csvw_var_name (v : Prims.string) : Prims.string=
  if csvw_var_is_fragment v
  then
    FStar_String.sub v Prims.int_one
      ((FStar_String.strlen v) - Prims.int_one)
  else v
let csvw_expand_segment
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (seg : csvw_template_segment) : Prims.string=
  match seg with
  | CT_Literal l -> l
  | CT_Var v ->
      let raw =
        match lookup (csvw_var_name v) with
        | FStar_Pervasives_Native.Some s -> s
        | FStar_Pervasives_Native.None -> "" in
      if csvw_var_is_fragment v
      then csvw_encode_fragment raw
      else SPARQL11_Algebra.string_encode_uri raw
let rec csvw_expand_segments
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (segs : csvw_template_segment Prims.list) : Prims.string=
  match segs with
  | [] -> ""
  | s::rest ->
      Prims.strcat (csvw_expand_segment lookup s)
        (csvw_expand_segments lookup rest)
let csvw_expand_template
  (lookup : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  (raw : Prims.string) : Prims.string=
  csvw_expand_segments lookup (csvw_parse_template raw)
