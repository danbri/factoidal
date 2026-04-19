open Prims
type binding_row = (Prims.string * RDF_Graph_Executable.rdf_term) Prims.list
type response_format =
  | RF_Json 
  | RF_Xml 
  | RF_Csv 
  | RF_Tsv 
  | RF_Turtle 
  | RF_NTriples 
  | RF_Text 
let uu___is_RF_Json (projectee : response_format) : Prims.bool=
  match projectee with | RF_Json -> true | uu___ -> false
let uu___is_RF_Xml (projectee : response_format) : Prims.bool=
  match projectee with | RF_Xml -> true | uu___ -> false
let uu___is_RF_Csv (projectee : response_format) : Prims.bool=
  match projectee with | RF_Csv -> true | uu___ -> false
let uu___is_RF_Tsv (projectee : response_format) : Prims.bool=
  match projectee with | RF_Tsv -> true | uu___ -> false
let uu___is_RF_Turtle (projectee : response_format) : Prims.bool=
  match projectee with | RF_Turtle -> true | uu___ -> false
let uu___is_RF_NTriples (projectee : response_format) : Prims.bool=
  match projectee with | RF_NTriples -> true | uu___ -> false
let uu___is_RF_Text (projectee : response_format) : Prims.bool=
  match projectee with | RF_Text -> true | uu___ -> false
type q_priority = Prims.nat
type accept_entry = (response_format * q_priority)
type sparql_request =
  | PR_Query of Prims.string * Prims.string Prims.list * Prims.string
  Prims.list 
  | PR_Update of Prims.string * Prims.string Prims.list * Prims.string
  Prims.list 
  | PR_Bad of Prims.string 
let uu___is_PR_Query (projectee : sparql_request) : Prims.bool=
  match projectee with
  | PR_Query (query_text, default_graph_uris, named_graph_uris) -> true
  | uu___ -> false
let __proj__PR_Query__item__query_text (projectee : sparql_request) :
  Prims.string=
  match projectee with
  | PR_Query (query_text, default_graph_uris, named_graph_uris) -> query_text
let __proj__PR_Query__item__default_graph_uris (projectee : sparql_request) :
  Prims.string Prims.list=
  match projectee with
  | PR_Query (query_text, default_graph_uris, named_graph_uris) ->
      default_graph_uris
let __proj__PR_Query__item__named_graph_uris (projectee : sparql_request) :
  Prims.string Prims.list=
  match projectee with
  | PR_Query (query_text, default_graph_uris, named_graph_uris) ->
      named_graph_uris
let uu___is_PR_Update (projectee : sparql_request) : Prims.bool=
  match projectee with
  | PR_Update (update_text, default_graph_uris, named_graph_uris) -> true
  | uu___ -> false
let __proj__PR_Update__item__update_text (projectee : sparql_request) :
  Prims.string=
  match projectee with
  | PR_Update (update_text, default_graph_uris, named_graph_uris) ->
      update_text
let __proj__PR_Update__item__default_graph_uris (projectee : sparql_request)
  : Prims.string Prims.list=
  match projectee with
  | PR_Update (update_text, default_graph_uris, named_graph_uris) ->
      default_graph_uris
let __proj__PR_Update__item__named_graph_uris (projectee : sparql_request) :
  Prims.string Prims.list=
  match projectee with
  | PR_Update (update_text, default_graph_uris, named_graph_uris) ->
      named_graph_uris
let uu___is_PR_Bad (projectee : sparql_request) : Prims.bool=
  match projectee with | PR_Bad reason -> true | uu___ -> false
let __proj__PR_Bad__item__reason (projectee : sparql_request) : Prims.string=
  match projectee with | PR_Bad reason -> reason
let char_code (c : FStar_Char.char) : Prims.nat= FStar_Char.int_of_char c
let is_hex_digit (c : FStar_Char.char) : Prims.bool=
  let code = char_code c in
  (((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))) ||
     ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))))
    || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66))))
let hex_value (c : FStar_Char.char) : Prims.nat=
  let code = char_code c in
  if (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
  then code - (Prims.of_int (0x30))
  else
    if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))
    then (code - (Prims.of_int (0x41))) + (Prims.of_int (10))
    else
      if (code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66)))
      then (code - (Prims.of_int (0x61))) + (Prims.of_int (10))
      else Prims.int_zero
let char_to_string (c : FStar_Char.char) : Prims.string=
  FStar_String.string_of_list [c]
let ascii_lower_char (c : FStar_Char.char) : FStar_Char.char=
  let cd = char_code c in
  if (cd >= (Prims.of_int (0x41))) && (cd <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (cd + (Prims.of_int (32)))
  else c
let ascii_lower_string (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (FStar_List_Tot_Base.map ascii_lower_char (FStar_String.list_of_string s))
let rec drop_ws_left (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      let code = char_code c in
      if
        (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09))))
           || (code = (Prims.of_int (0x0A))))
          || (code = (Prims.of_int (0x0D)))
      then drop_ws_left rest
      else cs
let trim_ws_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  FStar_List_Tot_Base.rev
    (drop_ws_left (FStar_List_Tot_Base.rev (drop_ws_left cs)))
let trim_ws (s : Prims.string) : Prims.string=
  FStar_String.string_of_list (trim_ws_chars (FStar_String.list_of_string s))
let rec url_decode_chars (plus_is_space : Prims.bool)
  (cs : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      let code = char_code c in
      if code = (Prims.of_int (0x25))
      then
        (match rest with
         | h1::h2::rest' ->
             if (is_hex_digit h1) && (is_hex_digit h2)
             then
               let v =
                 ((hex_value h1) * (Prims.of_int (16))) + (hex_value h2) in
               (FStar_Char.char_of_int v) ::
                 (url_decode_chars plus_is_space rest')
             else c :: (url_decode_chars plus_is_space rest)
         | uu___ -> c :: (url_decode_chars plus_is_space rest))
      else
        if plus_is_space && (code = (Prims.of_int (0x2B)))
        then (FStar_Char.char_of_int (Prims.of_int (0x20))) ::
          (url_decode_chars plus_is_space rest)
        else c :: (url_decode_chars plus_is_space rest)
let url_decode (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (url_decode_chars false (FStar_String.list_of_string s))
let form_decode (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (url_decode_chars true (FStar_String.list_of_string s))
let rec split_once_chars (sep : Prims.nat) (cs : FStar_Char.char Prims.list)
  :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ([], FStar_Pervasives_Native.None)
  | c::rest ->
      if (char_code c) = sep
      then ([], (FStar_Pervasives_Native.Some rest))
      else
        (let uu___1 = split_once_chars sep rest in
         match uu___1 with | (before, after) -> ((c :: before), after))
let split_once_on (s : Prims.string) (sep : FStar_Char.char) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option)=
  let uu___ =
    split_once_chars (char_code sep) (FStar_String.list_of_string s) in
  match uu___ with
  | (before, after) ->
      let before_s = FStar_String.string_of_list before in
      let after_s =
        match after with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some cs ->
            FStar_Pervasives_Native.Some (FStar_String.string_of_list cs) in
      (before_s, after_s)
let rec split_chars_all (sep : Prims.nat) (cs : FStar_Char.char Prims.list)
  (cur : FStar_Char.char Prims.list) : FStar_Char.char Prims.list Prims.list=
  match cs with
  | [] -> [FStar_List_Tot_Base.rev cur]
  | c::rest ->
      if (char_code c) = sep
      then (FStar_List_Tot_Base.rev cur) :: (split_chars_all sep rest [])
      else split_chars_all sep rest (c :: cur)
let split_all_on (s : Prims.string) (sep : FStar_Char.char) :
  Prims.string Prims.list=
  let segs =
    split_chars_all (char_code sep) (FStar_String.list_of_string s) [] in
  FStar_List_Tot_Base.map FStar_String.string_of_list segs
let parse_kv_pair (pair : Prims.string) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match split_once_on pair (FStar_Char.char_of_int (Prims.of_int (0x3D)))
  with
  | (k, FStar_Pervasives_Native.Some v) ->
      FStar_Pervasives_Native.Some ((form_decode k), (form_decode v))
  | (k, FStar_Pervasives_Native.None) ->
      if (FStar_String.strlen k) = Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some ((form_decode k), "")
let parse_query_string (qs : Prims.string) :
  (Prims.string * Prims.string) Prims.list=
  let parts = split_all_on qs (FStar_Char.char_of_int (Prims.of_int (0x26))) in
  FStar_List_Tot_Base.concatMap
    (fun p ->
       match parse_kv_pair p with
       | FStar_Pervasives_Native.Some kv -> [kv]
       | FStar_Pervasives_Native.None -> []) parts
let collect_values (key : Prims.string)
  (kvs : (Prims.string * Prims.string) Prims.list) : Prims.string Prims.list=
  FStar_List_Tot_Base.concatMap
    (fun kv ->
       let uu___ = kv in
       match uu___ with | (k, v) -> if k = key then [v] else []) kvs
let first_value (key : Prims.string)
  (kvs : (Prims.string * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match collect_values key kvs with
  | [] -> FStar_Pervasives_Native.None
  | v::uu___ -> FStar_Pervasives_Native.Some v
let media_type_to_format (mt : Prims.string) :
  response_format FStar_Pervasives_Native.option=
  let lo = ascii_lower_string (trim_ws mt) in
  if lo = "application/sparql-results+json"
  then FStar_Pervasives_Native.Some RF_Json
  else
    if lo = "application/json"
    then FStar_Pervasives_Native.Some RF_Json
    else
      if lo = "application/sparql-results+xml"
      then FStar_Pervasives_Native.Some RF_Xml
      else
        if lo = "application/xml"
        then FStar_Pervasives_Native.Some RF_Xml
        else
          if lo = "text/xml"
          then FStar_Pervasives_Native.Some RF_Xml
          else
            if lo = "text/csv"
            then FStar_Pervasives_Native.Some RF_Csv
            else
              if lo = "text/tab-separated-values"
              then FStar_Pervasives_Native.Some RF_Tsv
              else
                if lo = "text/turtle"
                then FStar_Pervasives_Native.Some RF_Turtle
                else
                  if lo = "application/x-turtle"
                  then FStar_Pervasives_Native.Some RF_Turtle
                  else
                    if lo = "application/n-triples"
                    then FStar_Pervasives_Native.Some RF_NTriples
                    else
                      if lo = "text/plain"
                      then FStar_Pervasives_Native.Some RF_Text
                      else FStar_Pervasives_Native.None
let rec read_digits_acc (cs : FStar_Char.char Prims.list) (acc : Prims.nat) :
  (Prims.nat * FStar_Char.char Prims.list)=
  match cs with
  | [] -> (acc, [])
  | c::rest ->
      let code = char_code c in
      if (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
      then
        read_digits_acc rest
          ((acc * (Prims.of_int (10))) + (code - (Prims.of_int (0x30))))
      else (acc, cs)
let parse_q_value (s : Prims.string) : q_priority=
  let trimmed = trim_ws s in
  let cs = FStar_String.list_of_string trimmed in
  let uu___ = read_digits_acc cs Prims.int_zero in
  match uu___ with
  | (ip, rest) ->
      let uu___1 =
        match rest with
        | [] -> (Prims.int_zero, [])
        | c::rest' ->
            if (char_code c) = (Prims.of_int (0x2E))
            then
              (match rest' with
               | [] -> (Prims.int_zero, [])
               | uu___2 ->
                   let uu___3 = read_digits_acc rest' Prims.int_zero in
                   (match uu___3 with | (d, uu___4) -> (d, [])))
            else (Prims.int_zero, rest) in
      (match uu___1 with
       | (frac3, uu___2) ->
           let raw = (ip * (Prims.of_int (1000))) + frac3 in
           if raw > (Prims.of_int (1000)) then (Prims.of_int (1000)) else raw)
let parse_accept_entry (item : Prims.string) :
  accept_entry FStar_Pervasives_Native.option=
  match split_once_on item (FStar_Char.char_of_int (Prims.of_int (0x3B)))
  with
  | (media, FStar_Pervasives_Native.None) ->
      (match media_type_to_format media with
       | FStar_Pervasives_Native.Some f ->
           FStar_Pervasives_Native.Some (f, (Prims.of_int (1000)))
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | (media, FStar_Pervasives_Native.Some params) ->
      let fmt = media_type_to_format media in
      let param_list =
        split_all_on params (FStar_Char.char_of_int (Prims.of_int (0x3B))) in
      let q =
        match FStar_List_Tot_Base.tryFind
                (fun p ->
                   let lo = ascii_lower_string (trim_ws p) in
                   ((FStar_String.strlen lo) >= (Prims.of_int (2))) &&
                     ((FStar_String.sub lo Prims.int_zero (Prims.of_int (2)))
                        = "q=")) param_list
        with
        | FStar_Pervasives_Native.None -> (Prims.of_int (1000))
        | FStar_Pervasives_Native.Some p ->
            let lo = ascii_lower_string (trim_ws p) in
            if (FStar_String.strlen lo) >= (Prims.of_int (2))
            then
              parse_q_value
                (FStar_String.sub lo (Prims.of_int (2))
                   ((FStar_String.strlen lo) - (Prims.of_int (2))))
            else (Prims.of_int (1000)) in
      (match fmt with
       | FStar_Pervasives_Native.Some f ->
           FStar_Pervasives_Native.Some (f, q)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let parse_accept_header (hdr : Prims.string) : accept_entry Prims.list=
  let items = split_all_on hdr (FStar_Char.char_of_int (Prims.of_int (0x2C))) in
  FStar_List_Tot_Base.concatMap
    (fun it ->
       match parse_accept_entry it with
       | FStar_Pervasives_Native.Some e -> [e]
       | FStar_Pervasives_Native.None -> []) items
let rec pick_best (entries : accept_entry Prims.list)
  (best_so_far : accept_entry FStar_Pervasives_Native.option) :
  accept_entry FStar_Pervasives_Native.option=
  match entries with
  | [] -> best_so_far
  | e::rest ->
      let uu___ = e in
      (match uu___ with
       | (uu___1, q) ->
           let better =
             match best_so_far with
             | FStar_Pervasives_Native.None -> true
             | FStar_Pervasives_Native.Some (uu___2, q_best) -> q > q_best in
           if better
           then pick_best rest (FStar_Pervasives_Native.Some e)
           else pick_best rest best_so_far)
let pick_response_format (entries : accept_entry Prims.list)
  (default_format : response_format) : response_format=
  match pick_best entries FStar_Pervasives_Native.None with
  | FStar_Pervasives_Native.None -> default_format
  | FStar_Pervasives_Native.Some (f, q) ->
      if q = Prims.int_zero then default_format else f
let path_is_update (url_path : Prims.string) : Prims.bool=
  let segments =
    split_all_on url_path (FStar_Char.char_of_int (Prims.of_int (0x2F))) in
  match FStar_List_Tot_Base.rev segments with
  | [] -> false
  | last::uu___ -> (ascii_lower_string last) = "update"
let split_path_qs (url_path : Prims.string) : (Prims.string * Prims.string)=
  match split_once_on url_path (FStar_Char.char_of_int (Prims.of_int (0x3F)))
  with
  | (p, FStar_Pervasives_Native.None) -> (p, "")
  | (p, FStar_Pervasives_Native.Some qs) -> (p, qs)
let content_type_base (ct : Prims.string) : Prims.string=
  match split_once_on ct (FStar_Char.char_of_int (Prims.of_int (0x3B))) with
  | (base, uu___) -> ascii_lower_string (trim_ws base)
let build_from_kvs (is_update_path : Prims.bool)
  (kvs : (Prims.string * Prims.string) Prims.list) : sparql_request=
  let q_opt = first_value "query" kvs in
  let u_opt = first_value "update" kvs in
  let dflt = collect_values "default-graph-uri" kvs in
  let named = collect_values "named-graph-uri" kvs in
  if is_update_path
  then
    match u_opt with
    | FStar_Pervasives_Native.Some u -> PR_Update (u, dflt, named)
    | FStar_Pervasives_Native.None ->
        (match q_opt with
         | FStar_Pervasives_Native.Some uu___ ->
             PR_Bad "expected update= on /update endpoint, got query="
         | FStar_Pervasives_Native.None -> PR_Bad "missing update parameter")
  else
    (match q_opt with
     | FStar_Pervasives_Native.Some q -> PR_Query (q, dflt, named)
     | FStar_Pervasives_Native.None ->
         (match u_opt with
          | FStar_Pervasives_Native.Some uu___1 ->
              PR_Bad "expected query= on /query endpoint, got update="
          | FStar_Pervasives_Native.None -> PR_Bad "missing query parameter"))
let decode_request (http_method : Prims.string) (url_path : Prims.string)
  (url_query : Prims.string) (content_type : Prims.string)
  (body : Prims.string) : sparql_request=
  let uu___ = split_path_qs url_path in
  match uu___ with
  | (clean_path, embedded_qs) ->
      let effective_qs =
        if (FStar_String.strlen url_query) > Prims.int_zero
        then url_query
        else embedded_qs in
      let is_update = path_is_update clean_path in
      let method_upper = ascii_lower_string http_method in
      if method_upper = "get"
      then
        let kvs = parse_query_string effective_qs in
        build_from_kvs is_update kvs
      else
        if method_upper = "post"
        then
          (let ct = content_type_base content_type in
           if ct = "application/sparql-query"
           then PR_Query (body, [], [])
           else
             if ct = "application/sparql-update"
             then PR_Update (body, [], [])
             else
               if ct = "application/x-www-form-urlencoded"
               then
                 (let kvs = parse_query_string body in
                  build_from_kvs is_update kvs)
               else
                 if (FStar_String.strlen ct) = Prims.int_zero
                 then PR_Bad "POST request missing Content-Type"
                 else PR_Bad (Prims.strcat "unsupported Content-Type: " ct))
        else
          if (method_upper = "head") || (method_upper = "options")
          then
            PR_Bad
              (Prims.strcat "method "
                 (Prims.strcat http_method " not supported by decoder"))
          else PR_Bad (Prims.strcat "unsupported HTTP method: " http_method)
let hex_nibble (n : Prims.nat) : Prims.string=
  if n < (Prims.of_int (10))
  then char_to_string (FStar_Char.char_of_int ((Prims.of_int (0x30)) + n))
  else
    char_to_string
      (FStar_Char.char_of_int
         ((Prims.of_int (0x61)) + (n - (Prims.of_int (10)))))
let json_escape_char (c : FStar_Char.char) : Prims.string=
  let code = char_code c in
  if code = (Prims.of_int (0x22))
  then "\\\""
  else
    if code = (Prims.of_int (0x5C))
    then "\\\\"
    else
      if code = (Prims.of_int (0x08))
      then "\\b"
      else
        if code = (Prims.of_int (0x09))
        then "\\t"
        else
          if code = (Prims.of_int (0x0A))
          then "\\n"
          else
            if code = (Prims.of_int (0x0C))
            then "\\f"
            else
              if code = (Prims.of_int (0x0D))
              then "\\r"
              else
                if code < (Prims.of_int (0x20))
                then
                  (let hi = code / (Prims.of_int (16)) in
                   let lo = (mod) code (Prims.of_int (16)) in
                   Prims.strcat "\\u00"
                     (Prims.strcat (hex_nibble hi) (hex_nibble lo)))
                else char_to_string c
let rec json_escape_chars (cs : FStar_Char.char Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::rest -> Prims.strcat (json_escape_char c) (json_escape_chars rest)
let json_escape (s : Prims.string) : Prims.string=
  json_escape_chars (FStar_String.list_of_string s)
let xml_escape_char (c : FStar_Char.char) : Prims.string=
  let code = char_code c in
  if code = (Prims.of_int (0x26))
  then "&amp;"
  else
    if code = (Prims.of_int (0x3C))
    then "&lt;"
    else
      if code = (Prims.of_int (0x3E))
      then "&gt;"
      else
        if code = (Prims.of_int (0x22))
        then "&quot;"
        else
          if code = (Prims.of_int (0x27))
          then "&apos;"
          else
            if code = (Prims.of_int (0x0D))
            then "&#13;"
            else char_to_string c
let rec xml_escape_chars (cs : FStar_Char.char Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::rest -> Prims.strcat (xml_escape_char c) (xml_escape_chars rest)
let xml_escape (s : Prims.string) : Prims.string=
  xml_escape_chars (FStar_String.list_of_string s)
let rec csv_needs_quoting_chars (cs : FStar_Char.char Prims.list) :
  Prims.bool=
  match cs with
  | [] -> false
  | c::rest ->
      let code = char_code c in
      if
        (((code = (Prims.of_int (0x2C))) || (code = (Prims.of_int (0x0A))))
           || (code = (Prims.of_int (0x0D))))
          || (code = (Prims.of_int (0x22)))
      then true
      else csv_needs_quoting_chars rest
let rec csv_double_quotes_chars (cs : FStar_Char.char Prims.list) :
  Prims.string=
  match cs with
  | [] -> ""
  | c::rest ->
      let code = char_code c in
      if code = (Prims.of_int (0x22))
      then Prims.strcat "\"\"" (csv_double_quotes_chars rest)
      else Prims.strcat (char_to_string c) (csv_double_quotes_chars rest)
let csv_escape (s : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string s in
  if csv_needs_quoting_chars cs
  then Prims.strcat "\"" (Prims.strcat (csv_double_quotes_chars cs) "\"")
  else s
let rec nt_escape_chars (cs : FStar_Char.char Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::rest ->
      let code = char_code c in
      if code = (Prims.of_int (0x22))
      then Prims.strcat "\\\"" (nt_escape_chars rest)
      else
        if code = (Prims.of_int (0x5C))
        then Prims.strcat "\\\\" (nt_escape_chars rest)
        else
          if code = (Prims.of_int (0x09))
          then Prims.strcat "\\t" (nt_escape_chars rest)
          else
            if code = (Prims.of_int (0x0A))
            then Prims.strcat "\\n" (nt_escape_chars rest)
            else
              if code = (Prims.of_int (0x0D))
              then Prims.strcat "\\r" (nt_escape_chars rest)
              else Prims.strcat (char_to_string c) (nt_escape_chars rest)
let nt_escape (s : Prims.string) : Prims.string=
  nt_escape_chars (FStar_String.list_of_string s)
let json_term (t : RDF_Graph_Executable.rdf_term) : Prims.string=
  match t with
  | RDF_Graph_Executable.T_IRI i ->
      Prims.strcat "{\"type\":\"uri\",\"value\":\""
        (Prims.strcat (json_escape i) "\"}")
  | RDF_Graph_Executable.T_BNode b ->
      Prims.strcat "{\"type\":\"bnode\",\"value\":\""
        (Prims.strcat (json_escape b) "\"}")
  | RDF_Graph_Executable.T_Literal l ->
      (match l.RDF_Graph_Executable.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "{\"type\":\"literal\",\"value\":\""
             (Prims.strcat (json_escape l.RDF_Graph_Executable.lexical_form)
                (Prims.strcat "\",\"xml:lang\":\""
                   (Prims.strcat (json_escape tag) "\"}")))
       | FStar_Pervasives_Native.None ->
           if
             l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_string
           then
             Prims.strcat "{\"type\":\"literal\",\"value\":\""
               (Prims.strcat
                  (json_escape l.RDF_Graph_Executable.lexical_form) "\"}")
           else
             Prims.strcat "{\"type\":\"literal\",\"value\":\""
               (Prims.strcat
                  (json_escape l.RDF_Graph_Executable.lexical_form)
                  (Prims.strcat "\",\"datatype\":\""
                     (Prims.strcat
                        (json_escape l.RDF_Graph_Executable.datatype) "\"}"))))
let rec json_var_list_body (vars : Prims.string Prims.list)
  (first : Prims.bool) : Prims.string=
  match vars with
  | [] -> ""
  | v::rest ->
      let piece = Prims.strcat "\"" (Prims.strcat (json_escape v) "\"") in
      if first
      then Prims.strcat piece (json_var_list_body rest false)
      else
        Prims.strcat "," (Prims.strcat piece (json_var_list_body rest false))
let json_var_list (vars : Prims.string Prims.list) : Prims.string=
  json_var_list_body vars true
let rec json_row_body (row : binding_row) (first : Prims.bool) :
  Prims.string=
  match row with
  | [] -> ""
  | (v, t)::rest ->
      let piece =
        Prims.strcat "\""
          (Prims.strcat (json_escape v) (Prims.strcat "\":" (json_term t))) in
      if first
      then Prims.strcat piece (json_row_body rest false)
      else Prims.strcat "," (Prims.strcat piece (json_row_body rest false))
let json_row (row : binding_row) : Prims.string=
  Prims.strcat "{" (Prims.strcat (json_row_body row true) "}")
let rec json_rows_body (rows : binding_row Prims.list) (first : Prims.bool) :
  Prims.string=
  match rows with
  | [] -> ""
  | r::rest ->
      let piece = json_row r in
      if first
      then Prims.strcat piece (json_rows_body rest false)
      else Prims.strcat "," (Prims.strcat piece (json_rows_body rest false))
let serialise_response_json (vars : Prims.string Prims.list)
  (rows : binding_row Prims.list) : Prims.string=
  Prims.strcat "{\"head\":{\"vars\":["
    (Prims.strcat (json_var_list vars)
       (Prims.strcat "]},"
          (Prims.strcat "\"results\":{\"bindings\":["
             (Prims.strcat (json_rows_body rows true) "]}}"))))
let serialise_response_boolean_json (b : Prims.bool) : Prims.string=
  if b
  then "{\"head\":{},\"boolean\":true}"
  else "{\"head\":{},\"boolean\":false}"
let rec xml_head_vars_body (vars : Prims.string Prims.list) : Prims.string=
  match vars with
  | [] -> ""
  | v::rest ->
      Prims.strcat "<variable name=\""
        (Prims.strcat (xml_escape v)
           (Prims.strcat "\"/>" (xml_head_vars_body rest)))
let xml_binding (name : Prims.string) (t : RDF_Graph_Executable.rdf_term) :
  Prims.string=
  let open_tag =
    Prims.strcat "<binding name=\"" (Prims.strcat (xml_escape name) "\">") in
  let inner =
    match t with
    | RDF_Graph_Executable.T_IRI i ->
        Prims.strcat "<uri>" (Prims.strcat (xml_escape i) "</uri>")
    | RDF_Graph_Executable.T_BNode b ->
        Prims.strcat "<bnode>" (Prims.strcat (xml_escape b) "</bnode>")
    | RDF_Graph_Executable.T_Literal l ->
        (match l.RDF_Graph_Executable.lang_tag with
         | FStar_Pervasives_Native.Some tag ->
             Prims.strcat "<literal xml:lang=\""
               (Prims.strcat (xml_escape tag)
                  (Prims.strcat "\">"
                     (Prims.strcat
                        (xml_escape l.RDF_Graph_Executable.lexical_form)
                        "</literal>")))
         | FStar_Pervasives_Native.None ->
             if
               l.RDF_Graph_Executable.datatype =
                 RDF_Graph_Executable.xsd_string
             then
               Prims.strcat "<literal>"
                 (Prims.strcat
                    (xml_escape l.RDF_Graph_Executable.lexical_form)
                    "</literal>")
             else
               Prims.strcat "<literal datatype=\""
                 (Prims.strcat (xml_escape l.RDF_Graph_Executable.datatype)
                    (Prims.strcat "\">"
                       (Prims.strcat
                          (xml_escape l.RDF_Graph_Executable.lexical_form)
                          "</literal>")))) in
  Prims.strcat open_tag (Prims.strcat inner "</binding>")
let rec xml_row_body (row : binding_row) : Prims.string=
  match row with
  | [] -> ""
  | (v, t)::rest -> Prims.strcat (xml_binding v t) (xml_row_body rest)
let xml_row (row : binding_row) : Prims.string=
  Prims.strcat "<result>" (Prims.strcat (xml_row_body row) "</result>")
let rec xml_rows_body (rows : binding_row Prims.list) : Prims.string=
  match rows with
  | [] -> ""
  | r::rest -> Prims.strcat (xml_row r) (xml_rows_body rest)
let serialise_response_xml (vars : Prims.string Prims.list)
  (rows : binding_row Prims.list) : Prims.string=
  Prims.strcat "<?xml version=\"1.0\"?>\n"
    (Prims.strcat "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">"
       (Prims.strcat "<head>"
          (Prims.strcat (xml_head_vars_body vars)
             (Prims.strcat "</head>"
                (Prims.strcat "<results>"
                   (Prims.strcat (xml_rows_body rows) "</results></sparql>"))))))
let serialise_response_boolean_xml (b : Prims.bool) : Prims.string=
  let value = if b then "true" else "false" in
  Prims.strcat "<?xml version=\"1.0\"?>\n"
    (Prims.strcat "<sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">"
       (Prims.strcat "<head></head>"
          (Prims.strcat "<boolean>"
             (Prims.strcat value "</boolean></sparql>"))))
let csv_cell
  (t_opt : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  Prims.string=
  match t_opt with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI i) ->
      csv_escape i
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_BNode b) ->
      csv_escape (Prims.strcat "_:" b)
  | FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal l) ->
      csv_escape l.RDF_Graph_Executable.lexical_form
let rec csv_header_body (vars : Prims.string Prims.list) (first : Prims.bool)
  : Prims.string=
  match vars with
  | [] -> ""
  | v::rest ->
      if first
      then Prims.strcat (csv_escape v) (csv_header_body rest false)
      else
        Prims.strcat ","
          (Prims.strcat (csv_escape v) (csv_header_body rest false))
let rec csv_row_body (vars : Prims.string Prims.list) (row : binding_row)
  (first : Prims.bool) : Prims.string=
  match vars with
  | [] -> ""
  | v::rest ->
      let cell = csv_cell (FStar_List_Tot_Base.assoc v row) in
      if first
      then Prims.strcat cell (csv_row_body rest row false)
      else Prims.strcat "," (Prims.strcat cell (csv_row_body rest row false))
let rec csv_rows_body (vars : Prims.string Prims.list)
  (rows : binding_row Prims.list) : Prims.string=
  match rows with
  | [] -> ""
  | r::rest ->
      Prims.strcat (csv_row_body vars r true)
        (Prims.strcat "\r\n" (csv_rows_body vars rest))
let serialise_response_csv (vars : Prims.string Prims.list)
  (rows : binding_row Prims.list) : Prims.string=
  Prims.strcat (csv_header_body vars true)
    (Prims.strcat "\r\n" (csv_rows_body vars rows))
let tsv_term (t : RDF_Graph_Executable.rdf_term) : Prims.string=
  match t with
  | RDF_Graph_Executable.T_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Graph_Executable.T_BNode b -> Prims.strcat "_:" b
  | RDF_Graph_Executable.T_Literal l ->
      let escaped = nt_escape l.RDF_Graph_Executable.lexical_form in
      (match l.RDF_Graph_Executable.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "\"" (Prims.strcat escaped (Prims.strcat "\"@" tag))
       | FStar_Pervasives_Native.None ->
           if
             l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_string
           then Prims.strcat "\"" (Prims.strcat escaped "\"")
           else
             Prims.strcat "\""
               (Prims.strcat escaped
                  (Prims.strcat "\"^^<"
                     (Prims.strcat l.RDF_Graph_Executable.datatype ">"))))
let tsv_cell
  (t_opt : RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option) :
  Prims.string=
  match t_opt with
  | FStar_Pervasives_Native.None -> ""
  | FStar_Pervasives_Native.Some t -> tsv_term t
let rec tsv_header_body (vars : Prims.string Prims.list) (first : Prims.bool)
  : Prims.string=
  match vars with
  | [] -> ""
  | v::rest ->
      let piece = Prims.strcat "?" v in
      if first
      then Prims.strcat piece (tsv_header_body rest false)
      else
        Prims.strcat "\t" (Prims.strcat piece (tsv_header_body rest false))
let rec tsv_row_body (vars : Prims.string Prims.list) (row : binding_row)
  (first : Prims.bool) : Prims.string=
  match vars with
  | [] -> ""
  | v::rest ->
      let cell = tsv_cell (FStar_List_Tot_Base.assoc v row) in
      if first
      then Prims.strcat cell (tsv_row_body rest row false)
      else
        Prims.strcat "\t" (Prims.strcat cell (tsv_row_body rest row false))
let rec tsv_rows_body (vars : Prims.string Prims.list)
  (rows : binding_row Prims.list) : Prims.string=
  match rows with
  | [] -> ""
  | r::rest ->
      Prims.strcat (tsv_row_body vars r true)
        (Prims.strcat "\n" (tsv_rows_body vars rest))
let serialise_response_tsv (vars : Prims.string Prims.list)
  (rows : binding_row Prims.list) : Prims.string=
  Prims.strcat (tsv_header_body vars true)
    (Prims.strcat "\n" (tsv_rows_body vars rows))
let content_type_for (f : response_format) : Prims.string=
  match f with
  | RF_Json -> "application/sparql-results+json"
  | RF_Xml -> "application/sparql-results+xml"
  | RF_Csv -> "text/csv"
  | RF_Tsv -> "text/tab-separated-values"
  | RF_Turtle -> "text/turtle"
  | RF_NTriples -> "application/n-triples"
  | RF_Text -> "text/plain"
let lit_str (s : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  let l =
    {
      RDF_Graph_Executable.lexical_form = s;
      RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string;
      RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
    } in
  if RDF_Graph_Executable.literal_wf l
  then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal l)
  else FStar_Pervasives_Native.None
