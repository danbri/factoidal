open Prims
type source_row =
  | Row_JSON of Parser_JSON.json_val 
  | Row_CSV of (Prims.string * Prims.string) Prims.list 
let uu___is_Row_JSON (projectee : source_row) : Prims.bool=
  match projectee with | Row_JSON _0 -> true | uu___ -> false
let __proj__Row_JSON__item___0 (projectee : source_row) :
  Parser_JSON.json_val= match projectee with | Row_JSON _0 -> _0
let uu___is_Row_CSV (projectee : source_row) : Prims.bool=
  match projectee with | Row_CSV _0 -> true | uu___ -> false
let __proj__Row_CSV__item___0 (projectee : source_row) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with | Row_CSV _0 -> _0
let source_row_json (r : source_row) : Parser_JSON.json_val=
  match r with | Row_JSON v -> v | Row_CSV uu___ -> Parser_JSON.JNull
let source_row_csv (r : source_row) :
  (Prims.string * Prims.string) Prims.list=
  match r with | Row_CSV b -> b | Row_JSON uu___ -> []
type jsonpath_step =
  | JPS_Field of Prims.string 
  | JPS_Wildcard 
let uu___is_JPS_Field (projectee : jsonpath_step) : Prims.bool=
  match projectee with | JPS_Field _0 -> true | uu___ -> false
let __proj__JPS_Field__item___0 (projectee : jsonpath_step) : Prims.string=
  match projectee with | JPS_Field _0 -> _0
let uu___is_JPS_Wildcard (projectee : jsonpath_step) : Prims.bool=
  match projectee with | JPS_Wildcard -> true | uu___ -> false
let rec scan_field_name (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (buf : Prims.string) : Prims.string=
  if fuel = Prims.int_zero
  then buf
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then buf
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if (c = (Prims.of_int (0x2E))) || (c = (Prims.of_int (0x5B)))
        then buf
        else
          scan_field_name s (pos + Prims.int_one) (fuel - Prims.int_one)
            (Prims.strcat buf (FStar_String.sub s pos Prims.int_one))))
let rec field_name_end (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then pos
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if (c = (Prims.of_int (0x2E))) || (c = (Prims.of_int (0x5B)))
        then pos
        else field_name_end s (pos + Prims.int_one) (fuel - Prims.int_one)))
let rec scan_to_quote (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat)
  (q : Prims.int) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then pos
     else
       if (FStar_Char.int_of_char (FStar_String.index s pos)) = q
       then pos
       else scan_to_quote s (pos + Prims.int_one) (fuel - Prims.int_one) q)
let rec scan_jsonpath_acc (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (acc : jsonpath_step Prims.list) :
  jsonpath_step Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then FStar_List_Tot_Base.rev acc
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if c = (Prims.of_int (0x2E))
        then
          let pos1 = pos + Prims.int_one in
          (if
             (pos1 < len) &&
               ((FStar_Char.int_of_char (FStar_String.index s pos1)) =
                  (Prims.of_int (0x2A)))
           then
             scan_jsonpath_acc s (pos1 + Prims.int_one)
               (fuel - Prims.int_one) (JPS_Wildcard :: acc)
           else
             (let e = field_name_end s pos1 (fuel - Prims.int_one) in
              let name = scan_field_name s pos1 (fuel - Prims.int_one) "" in
              if e = pos1
              then FStar_List_Tot_Base.rev acc
              else
                scan_jsonpath_acc s e (fuel - Prims.int_one)
                  ((JPS_Field name) :: acc)))
        else
          if c = (Prims.of_int (0x5B))
          then
            (let pos1 = pos + Prims.int_one in
             if
               (((pos1 + Prims.int_one) < len) &&
                  ((FStar_Char.int_of_char (FStar_String.index s pos1)) =
                     (Prims.of_int (0x2A))))
                 &&
                 ((FStar_Char.int_of_char
                     (FStar_String.index s (pos1 + Prims.int_one)))
                    = (Prims.of_int (0x5D)))
             then
               scan_jsonpath_acc s (pos1 + (Prims.of_int (2)))
                 (fuel - Prims.int_one) (JPS_Wildcard :: acc)
             else
               (let qc =
                  if pos1 < len
                  then FStar_Char.int_of_char (FStar_String.index s pos1)
                  else (Prims.of_int (-1)) in
                if
                  (qc = (Prims.of_int (0x27))) ||
                    (qc = (Prims.of_int (0x22)))
                then
                  let name_start = pos1 + Prims.int_one in
                  let qend =
                    scan_to_quote s name_start (fuel - Prims.int_one) qc in
                  (if
                     ((qend < len) && ((qend + Prims.int_one) < len)) &&
                       ((FStar_Char.int_of_char
                           (FStar_String.index s (qend + Prims.int_one)))
                          = (Prims.of_int (0x5D)))
                   then
                     let name =
                       FStar_String.sub s name_start (qend - name_start) in
                     scan_jsonpath_acc s (qend + (Prims.of_int (2)))
                       (fuel - Prims.int_one) ((JPS_Field name) :: acc)
                   else FStar_List_Tot_Base.rev acc)
                else FStar_List_Tot_Base.rev acc))
          else FStar_List_Tot_Base.rev acc))
let rec jsonpath_scan_end_pos (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then pos
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if c = (Prims.of_int (0x2E))
        then
          let pos1 = pos + Prims.int_one in
          (if
             (pos1 < len) &&
               ((FStar_Char.int_of_char (FStar_String.index s pos1)) =
                  (Prims.of_int (0x2A)))
           then
             jsonpath_scan_end_pos s (pos1 + Prims.int_one)
               (fuel - Prims.int_one)
           else
             (let e = field_name_end s pos1 (fuel - Prims.int_one) in
              if e = pos1
              then pos
              else jsonpath_scan_end_pos s e (fuel - Prims.int_one)))
        else
          if c = (Prims.of_int (0x5B))
          then
            (let pos1 = pos + Prims.int_one in
             if
               (((pos1 + Prims.int_one) < len) &&
                  ((FStar_Char.int_of_char (FStar_String.index s pos1)) =
                     (Prims.of_int (0x2A))))
                 &&
                 ((FStar_Char.int_of_char
                     (FStar_String.index s (pos1 + Prims.int_one)))
                    = (Prims.of_int (0x5D)))
             then
               jsonpath_scan_end_pos s (pos1 + (Prims.of_int (2)))
                 (fuel - Prims.int_one)
             else
               (let qc =
                  if pos1 < len
                  then FStar_Char.int_of_char (FStar_String.index s pos1)
                  else (Prims.of_int (-1)) in
                if
                  (qc = (Prims.of_int (0x27))) ||
                    (qc = (Prims.of_int (0x22)))
                then
                  let name_start = pos1 + Prims.int_one in
                  let qend =
                    scan_to_quote s name_start (fuel - Prims.int_one) qc in
                  (if
                     ((qend < len) && ((qend + Prims.int_one) < len)) &&
                       ((FStar_Char.int_of_char
                           (FStar_String.index s (qend + Prims.int_one)))
                          = (Prims.of_int (0x5D)))
                   then
                     jsonpath_scan_end_pos s (qend + (Prims.of_int (2)))
                       (fuel - Prims.int_one)
                   else pos)
                else pos))
          else pos))
let jsonpath_is_valid (s : Prims.string) : Prims.bool=
  let len = FStar_String.strlen s in
  if len = Prims.int_zero
  then true
  else
    if
      (FStar_Char.int_of_char (FStar_String.index s Prims.int_zero)) =
        (Prims.of_int (0x24))
    then (jsonpath_scan_end_pos s Prims.int_one (len + Prims.int_one)) = len
    else true
let parse_jsonpath (s : Prims.string) : jsonpath_step Prims.list=
  let len = FStar_String.strlen s in
  if len = Prims.int_zero
  then []
  else
    if
      (FStar_Char.int_of_char (FStar_String.index s Prims.int_zero)) =
        (Prims.of_int (0x24))
    then scan_jsonpath_acc s Prims.int_one (len + Prims.int_one) []
    else [JPS_Field s]
let json_field_lookup (name : Prims.string) (v : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match v with
  | Parser_JSON.JObject uu___ ->
      (match Parser_JSON.json_get_field name v with
       | FStar_Pervasives_Native.Some x -> [x]
       | FStar_Pervasives_Native.None -> [])
  | uu___ -> []
let json_wildcard_fanout (v : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match v with
  | Parser_JSON.JArray items -> items
  | Parser_JSON.JObject fields ->
      FStar_List_Tot_Base.map FStar_Pervasives_Native.snd fields
  | uu___ -> []
let rec eval_jsonpath_steps (ctxs : Parser_JSON.json_val Prims.list)
  (steps : jsonpath_step Prims.list) : Parser_JSON.json_val Prims.list=
  match steps with
  | [] -> ctxs
  | (JPS_Field name)::rest ->
      eval_jsonpath_steps
        (FStar_List_Tot_Base.concatMap (json_field_lookup name) ctxs) rest
  | (JPS_Wildcard)::rest ->
      eval_jsonpath_steps
        (FStar_List_Tot_Base.concatMap json_wildcard_fanout ctxs) rest
let eval_jsonpath (root : Parser_JSON.json_val) (path : Prims.string) :
  Parser_JSON.json_val Prims.list=
  eval_jsonpath_steps [root] (parse_jsonpath path)
let json_iterate (json_root : Parser_JSON.json_val) (iterator : Prims.string)
  : source_row Prims.list=
  if Prims.op_Negation (jsonpath_is_valid iterator)
  then []
  else
    FStar_List_Tot_Base.map (fun uu___1 -> Row_JSON uu___1)
      (eval_jsonpath json_root iterator)
let json_reference_values (row : source_row) (path : Prims.string) :
  Parser_JSON.json_val Prims.list= eval_jsonpath (source_row_json row) path
let flush_csv_field (buf : Prims.string) (row_acc : Prims.string Prims.list)
  : Prims.string Prims.list= buf :: row_acc
let flush_csv_row (buf : Prims.string) (row_acc : Prims.string Prims.list)
  (rows_acc : Prims.string Prims.list Prims.list) :
  Prims.string Prims.list Prims.list=
  (FStar_List_Tot_Base.rev (flush_csv_field buf row_acc)) :: rows_acc
let rec csv_scan_acc (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat)
  (in_quotes : Prims.bool) (buf : Prims.string)
  (row_acc : Prims.string Prims.list)
  (rows_acc : Prims.string Prims.list Prims.list) :
  Prims.string Prims.list Prims.list=
  let finish uu___ =
    FStar_List_Tot_Base.rev
      (if (buf <> "") || (row_acc <> [])
       then flush_csv_row buf row_acc rows_acc
       else rows_acc) in
  if fuel = Prims.int_zero
  then finish ()
  else
    (let len = FStar_String.strlen s in
     if pos >= len
     then finish ()
     else
       (let c = FStar_Char.int_of_char (FStar_String.index s pos) in
        if in_quotes
        then
          (if c = (Prims.of_int (0x22))
           then
             (if
                ((pos + Prims.int_one) < len) &&
                  ((FStar_Char.int_of_char
                      (FStar_String.index s (pos + Prims.int_one)))
                     = (Prims.of_int (0x22)))
              then
                csv_scan_acc s (pos + (Prims.of_int (2)))
                  (fuel - Prims.int_one) true (Prims.strcat buf "\"") row_acc
                  rows_acc
              else
                csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
                  false buf row_acc rows_acc)
           else
             csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one) true
               (Prims.strcat buf (FStar_String.sub s pos Prims.int_one))
               row_acc rows_acc)
        else
          if (c = (Prims.of_int (0x22))) && (buf = "")
          then
            csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one) true
              buf row_acc rows_acc
          else
            if c = (Prims.of_int (0x2C))
            then
              csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
                false "" (flush_csv_field buf row_acc) rows_acc
            else
              if c = (Prims.of_int (0x0A))
              then
                csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
                  false "" [] (flush_csv_row buf row_acc rows_acc)
              else
                if c = (Prims.of_int (0x0D))
                then
                  csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
                    false buf row_acc rows_acc
                else
                  csv_scan_acc s (pos + Prims.int_one) (fuel - Prims.int_one)
                    false
                    (Prims.strcat buf (FStar_String.sub s pos Prims.int_one))
                    row_acc rows_acc))
let csv_parse_rows (s : Prims.string) : Prims.string Prims.list Prims.list=
  csv_scan_acc s Prims.int_zero ((FStar_String.strlen s) + Prims.int_one)
    false "" [] []
let rec zip_strings (a : Prims.string Prims.list)
  (b : Prims.string Prims.list) : (Prims.string * Prims.string) Prims.list=
  match (a, b) with
  | (x::xs, y::ys) -> (x, y) :: (zip_strings xs ys)
  | (uu___, uu___1) -> []
let rec all_rows_match_width (n : Prims.nat)
  (rows : Prims.string Prims.list Prims.list) : Prims.bool=
  match rows with
  | [] -> true
  | r::rest ->
      ((FStar_List_Tot_Base.length r) = n) && (all_rows_match_width n rest)
let csv_iterate (csv_text : Prims.string)
  (null_values : Prims.string Prims.list) : source_row Prims.list=
  match csv_parse_rows csv_text with
  | [] -> []
  | header::data_rows ->
      let header_len = FStar_List_Tot_Base.length header in
      if Prims.op_Negation (all_rows_match_width header_len data_rows)
      then []
      else
        FStar_List_Tot_Base.map
          (fun row ->
             let bindings = zip_strings header row in
             Row_CSV
               (FStar_List_Tot_Base.filter
                  (fun p ->
                     Prims.op_Negation
                       (FStar_List_Tot_Base.mem
                          (FStar_Pervasives_Native.snd p) null_values))
                  bindings)) data_rows
let csv_reference_values (row : source_row) (column : Prims.string) :
  Prims.string Prims.list=
  match row with
  | Row_CSV bindings ->
      (match FStar_List_Tot_Base.assoc column bindings with
       | FStar_Pervasives_Native.Some v -> [v]
       | FStar_Pervasives_Native.None -> [])
  | Row_JSON uu___ -> []
