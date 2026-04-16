open Prims
type json_value =
  | JNull 
  | JBool of Prims.bool 
  | JString of Prims.string 
  | JNumber of Prims.string 
  | JArray of json_value Prims.list 
  | JObject of (Prims.string * json_value) Prims.list 
let uu___is_JNull (projectee : json_value) : Prims.bool=
  match projectee with | JNull -> true | uu___ -> false
let uu___is_JBool (projectee : json_value) : Prims.bool=
  match projectee with | JBool _0 -> true | uu___ -> false
let __proj__JBool__item___0 (projectee : json_value) : Prims.bool=
  match projectee with | JBool _0 -> _0
let uu___is_JString (projectee : json_value) : Prims.bool=
  match projectee with | JString _0 -> true | uu___ -> false
let __proj__JString__item___0 (projectee : json_value) : Prims.string=
  match projectee with | JString _0 -> _0
let uu___is_JNumber (projectee : json_value) : Prims.bool=
  match projectee with | JNumber _0 -> true | uu___ -> false
let __proj__JNumber__item___0 (projectee : json_value) : Prims.string=
  match projectee with | JNumber _0 -> _0
let uu___is_JArray (projectee : json_value) : Prims.bool=
  match projectee with | JArray _0 -> true | uu___ -> false
let __proj__JArray__item___0 (projectee : json_value) :
  json_value Prims.list= match projectee with | JArray _0 -> _0
let uu___is_JObject (projectee : json_value) : Prims.bool=
  match projectee with | JObject _0 -> true | uu___ -> false
let __proj__JObject__item___0 (projectee : json_value) :
  (Prims.string * json_value) Prims.list=
  match projectee with | JObject _0 -> _0
let json_ws : unit Parser_Combinators.parser=
  fun input pos ->
    match Parser_Combinators.pskip_whitespace input pos with
    | Parser_Combinators.ParseOk (uu___, pos') ->
        Parser_Combinators.ParseOk ((), pos')
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
let hex_digit_val (h : Prims.int) : Prims.int=
  if (h >= (Prims.of_int (0x30))) && (h <= (Prims.of_int (0x39)))
  then h - (Prims.of_int (0x30))
  else
    if (h >= (Prims.of_int (0x41))) && (h <= (Prims.of_int (0x46)))
    then (h - (Prims.of_int (0x41))) + (Prims.of_int (10))
    else
      if (h >= (Prims.of_int (0x61))) && (h <= (Prims.of_int (0x66)))
      then (h - (Prims.of_int (0x61))) + (Prims.of_int (10))
      else Prims.int_zero
let rec json_string_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated JSON string", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated JSON string", pos)
     else
       (let ch = FStar_String.index input pos in
        let code = FStar_Char.int_of_char ch in
        if code = (Prims.of_int (0x22))
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if code = (Prims.of_int (0x5C))
          then
            (if (pos + Prims.int_one) >= len
             then
               Parser_Combinators.ParseFail
                 ("backslash at end of string", pos)
             else
               (let esc = FStar_String.index input (pos + Prims.int_one) in
                let esc_code = FStar_Char.int_of_char esc in
                if esc_code = (Prims.of_int (0x22))
                then
                  json_string_body input (pos + (Prims.of_int (2)))
                    ((FStar_Char.char_of_int (Prims.of_int (0x22))) :: acc)
                    (fuel - Prims.int_one)
                else
                  if esc_code = (Prims.of_int (0x5C))
                  then
                    json_string_body input (pos + (Prims.of_int (2)))
                      ((FStar_Char.char_of_int (Prims.of_int (0x5C))) :: acc)
                      (fuel - Prims.int_one)
                  else
                    if esc_code = (Prims.of_int (0x2F))
                    then
                      json_string_body input (pos + (Prims.of_int (2)))
                        ((FStar_Char.char_of_int (Prims.of_int (0x2F))) ::
                        acc) (fuel - Prims.int_one)
                    else
                      if esc_code = (Prims.of_int (0x6E))
                      then
                        json_string_body input (pos + (Prims.of_int (2)))
                          ((FStar_Char.char_of_int (Prims.of_int (0x0A))) ::
                          acc) (fuel - Prims.int_one)
                      else
                        if esc_code = (Prims.of_int (0x72))
                        then
                          json_string_body input (pos + (Prims.of_int (2)))
                            ((FStar_Char.char_of_int (Prims.of_int (0x0D)))
                            :: acc) (fuel - Prims.int_one)
                        else
                          if esc_code = (Prims.of_int (0x74))
                          then
                            json_string_body input (pos + (Prims.of_int (2)))
                              ((FStar_Char.char_of_int (Prims.of_int (0x09)))
                              :: acc) (fuel - Prims.int_one)
                          else
                            if esc_code = (Prims.of_int (0x62))
                            then
                              json_string_body input
                                (pos + (Prims.of_int (2)))
                                ((FStar_Char.char_of_int
                                    (Prims.of_int (0x08))) :: acc)
                                (fuel - Prims.int_one)
                            else
                              if esc_code = (Prims.of_int (0x66))
                              then
                                json_string_body input
                                  (pos + (Prims.of_int (2)))
                                  ((FStar_Char.char_of_int
                                      (Prims.of_int (0x0C))) :: acc)
                                  (fuel - Prims.int_one)
                              else
                                if esc_code = (Prims.of_int (0x75))
                                then
                                  (if (pos + (Prims.of_int (5))) >= len
                                   then
                                     Parser_Combinators.ParseFail
                                       ("incomplete unicode escape", pos)
                                   else
                                     (let h0 =
                                        FStar_Char.int_of_char
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (2)))) in
                                      let h1 =
                                        FStar_Char.int_of_char
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (3)))) in
                                      let h2 =
                                        FStar_Char.int_of_char
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (4)))) in
                                      let h3 =
                                        FStar_Char.int_of_char
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (5)))) in
                                      let v0 = hex_digit_val h0 in
                                      let v1 = hex_digit_val h1 in
                                      let v2 = hex_digit_val h2 in
                                      let v3 = hex_digit_val h3 in
                                      let codepoint =
                                        (((v0 * (Prims.of_int (4096))) +
                                            (v1 * (Prims.of_int (256))))
                                           + (v2 * (Prims.of_int (16))))
                                          + v3 in
                                      if codepoint <= (Prims.of_int (0x7F))
                                      then
                                        json_string_body input
                                          (pos + (Prims.of_int (6)))
                                          ((FStar_Char.char_of_int codepoint)
                                          :: acc) (fuel - Prims.int_one)
                                      else
                                        if
                                          codepoint <= (Prims.of_int (0x7FF))
                                        then
                                          (let b1 =
                                             FStar_Char.char_of_int
                                               ((Prims.of_int (0xC0)) +
                                                  (codepoint /
                                                     (Prims.of_int (64)))) in
                                           let b2 =
                                             FStar_Char.char_of_int
                                               ((Prims.of_int (0x80)) +
                                                  ((mod) codepoint
                                                     (Prims.of_int (64)))) in
                                           json_string_body input
                                             (pos + (Prims.of_int (6))) (b2
                                             :: b1 :: acc)
                                             (fuel - Prims.int_one))
                                        else
                                          (let b1 =
                                             FStar_Char.char_of_int
                                               ((Prims.of_int (0xE0)) +
                                                  (codepoint /
                                                     (Prims.of_int (4096)))) in
                                           let b2 =
                                             FStar_Char.char_of_int
                                               ((Prims.of_int (0x80)) +
                                                  (((mod) codepoint
                                                      (Prims.of_int (4096)))
                                                     / (Prims.of_int (64)))) in
                                           let b3 =
                                             FStar_Char.char_of_int
                                               ((Prims.of_int (0x80)) +
                                                  ((mod) codepoint
                                                     (Prims.of_int (64)))) in
                                           json_string_body input
                                             (pos + (Prims.of_int (6))) (b3
                                             :: b2 :: b1 :: acc)
                                             (fuel - Prims.int_one))))
                                else
                                  json_string_body input
                                    (pos + (Prims.of_int (2))) (esc :: acc)
                                    (fuel - Prims.int_one)))
          else
            json_string_body input (pos + Prims.int_one) (ch :: acc)
              (fuel - Prims.int_one)))
let parse_json_string (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected JSON string", pos)
  else
    (let ch = FStar_String.index input pos in
     if (FStar_Char.int_of_char ch) = (Prims.of_int (0x22))
     then
       let fuel = len - pos in
       json_string_body input (pos + Prims.int_one) [] fuel
     else Parser_Combinators.ParseFail ("expected opening double-quote", pos))
let parse_json_number (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let is_num_char c =
    let code = FStar_Char.int_of_char c in
    ((((((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39))))
          || (code = (Prims.of_int (0x2D))))
         || (code = (Prims.of_int (0x2B))))
        || (code = (Prims.of_int (0x2E))))
       || (code = (Prims.of_int (0x65))))
      || (code = (Prims.of_int (0x45))) in
  Parser_Combinators.ptake_while1 is_num_char input pos
let safe_index (input : Prims.string) (pos : Prims.nat) :
  FStar_Char.char FStar_Pervasives_Native.option=
  if pos < (FStar_String.strlen input)
  then FStar_Pervasives_Native.Some (FStar_String.index input pos)
  else FStar_Pervasives_Native.None
let rec parse_json_value (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : json_value Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let pos1 =
       match json_ws input pos with
       | Parser_Combinators.ParseOk (uu___1, p) -> p
       | uu___1 -> pos in
     match safe_index input pos1 with
     | FStar_Pervasives_Native.None ->
         Parser_Combinators.ParseFail ("unexpected end of JSON", pos1)
     | FStar_Pervasives_Native.Some ch ->
         let code = FStar_Char.int_of_char ch in
         if code = (Prims.of_int (0x22))
         then
           (match parse_json_string input pos1 with
            | Parser_Combinators.ParseOk (s, pos') ->
                Parser_Combinators.ParseOk ((JString s), pos')
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos))
         else
           if code = (Prims.of_int (0x7B))
           then
             parse_json_object input (pos1 + Prims.int_one)
               (fuel - Prims.int_one)
           else
             if code = (Prims.of_int (0x5B))
             then
               parse_json_array input (pos1 + Prims.int_one)
                 (fuel - Prims.int_one)
             else
               if code = (Prims.of_int (0x74))
               then
                 (match Parser_Combinators.pstring "true" input pos1 with
                  | Parser_Combinators.ParseOk (uu___4, pos') ->
                      Parser_Combinators.ParseOk ((JBool true), pos')
                  | Parser_Combinators.ParseFail (msg, fpos) ->
                      Parser_Combinators.ParseFail (msg, fpos))
               else
                 if code = (Prims.of_int (0x66))
                 then
                   (match Parser_Combinators.pstring "false" input pos1 with
                    | Parser_Combinators.ParseOk (uu___5, pos') ->
                        Parser_Combinators.ParseOk ((JBool false), pos')
                    | Parser_Combinators.ParseFail (msg, fpos) ->
                        Parser_Combinators.ParseFail (msg, fpos))
                 else
                   if code = (Prims.of_int (0x6E))
                   then
                     (match Parser_Combinators.pstring "null" input pos1 with
                      | Parser_Combinators.ParseOk (uu___6, pos') ->
                          Parser_Combinators.ParseOk (JNull, pos')
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos))
                   else
                     if
                       (code = (Prims.of_int (0x2D))) ||
                         ((code >= (Prims.of_int (0x30))) &&
                            (code <= (Prims.of_int (0x39))))
                     then
                       (match parse_json_number input pos1 with
                        | Parser_Combinators.ParseOk (s, pos') ->
                            Parser_Combinators.ParseOk ((JNumber s), pos')
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos))
                     else
                       Parser_Combinators.ParseFail
                         ("unexpected character in JSON", pos1))
and parse_json_object (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : json_value Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let pos1 =
       match json_ws input pos with
       | Parser_Combinators.ParseOk (uu___1, p) -> p
       | uu___1 -> pos in
     match safe_index input pos1 with
     | FStar_Pervasives_Native.None ->
         Parser_Combinators.ParseFail ("unterminated object", pos1)
     | FStar_Pervasives_Native.Some ch ->
         if (FStar_Char.int_of_char ch) = (Prims.of_int (0x7D))
         then
           Parser_Combinators.ParseOk ((JObject []), (pos1 + Prims.int_one))
         else parse_json_object_members input pos1 (fuel - Prims.int_one) [])
and parse_json_object_members (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (acc : (Prims.string * json_value) Prims.list) :
  json_value Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let pos1 =
       match json_ws input pos with
       | Parser_Combinators.ParseOk (uu___1, p) -> p
       | uu___1 -> pos in
     match parse_json_string input pos1 with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (key, pos11) ->
         let pos12 =
           match json_ws input pos11 with
           | Parser_Combinators.ParseOk (uu___1, p) -> p
           | uu___1 -> pos11 in
         (match safe_index input pos12 with
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail ("expected colon", pos12)
          | FStar_Pervasives_Native.Some colon_ch ->
              if (FStar_Char.int_of_char colon_ch) <> (Prims.of_int (0x3A))
              then Parser_Combinators.ParseFail ("expected colon", pos12)
              else
                (match parse_json_value input (pos12 + Prims.int_one)
                         (fuel - Prims.int_one)
                 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk (value, pos2) ->
                     let acc1 = FStar_List_Tot_Base.append acc [(key, value)] in
                     let pos21 =
                       match json_ws input pos2 with
                       | Parser_Combinators.ParseOk (uu___2, p) -> p
                       | uu___2 -> pos2 in
                     (match safe_index input pos21 with
                      | FStar_Pervasives_Native.None ->
                          Parser_Combinators.ParseFail
                            ("unterminated object", pos21)
                      | FStar_Pervasives_Native.Some ch2 ->
                          if
                            (FStar_Char.int_of_char ch2) =
                              (Prims.of_int (0x7D))
                          then
                            Parser_Combinators.ParseOk
                              ((JObject acc1), (pos21 + Prims.int_one))
                          else
                            if
                              (FStar_Char.int_of_char ch2) =
                                (Prims.of_int (0x2C))
                            then
                              parse_json_object_members input
                                (pos21 + Prims.int_one)
                                (fuel - Prims.int_one) acc1
                            else
                              Parser_Combinators.ParseFail
                                ("expected comma or closing brace", pos21)))))
and parse_json_array (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : json_value Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let pos1 =
       match json_ws input pos with
       | Parser_Combinators.ParseOk (uu___1, p) -> p
       | uu___1 -> pos in
     match safe_index input pos1 with
     | FStar_Pervasives_Native.None ->
         Parser_Combinators.ParseFail ("unterminated array", pos1)
     | FStar_Pervasives_Native.Some ch ->
         if (FStar_Char.int_of_char ch) = (Prims.of_int (0x5D))
         then
           Parser_Combinators.ParseOk ((JArray []), (pos1 + Prims.int_one))
         else parse_json_array_items input pos1 (fuel - Prims.int_one) [])
and parse_json_array_items (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (acc : json_value Prims.list) :
  json_value Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (match parse_json_value input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (item, pos1) ->
         let acc1 = FStar_List_Tot_Base.append acc [item] in
         let pos11 =
           match json_ws input pos1 with
           | Parser_Combinators.ParseOk (uu___1, p) -> p
           | uu___1 -> pos1 in
         (match safe_index input pos11 with
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail ("unterminated array", pos11)
          | FStar_Pervasives_Native.Some ch1 ->
              if (FStar_Char.int_of_char ch1) = (Prims.of_int (0x5D))
              then
                Parser_Combinators.ParseOk
                  ((JArray acc1), (pos11 + Prims.int_one))
              else
                if (FStar_Char.int_of_char ch1) = (Prims.of_int (0x2C))
                then
                  parse_json_array_items input (pos11 + Prims.int_one)
                    (fuel - Prims.int_one) acc1
                else
                  Parser_Combinators.ParseFail
                    ("expected comma or closing bracket", pos11)))
let parse_json (input : Prims.string) :
  json_value FStar_Pervasives_Native.option=
  let fuel = FStar_String.strlen input in
  match parse_json_value input Prims.int_zero fuel with
  | Parser_Combinators.ParseOk (v, uu___) -> FStar_Pervasives_Native.Some v
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let json_get_field (key : Prims.string) (obj : json_value) :
  json_value FStar_Pervasives_Native.option=
  match obj with
  | JObject fields ->
      (match FStar_List_Tot_Base.find
               (fun uu___ -> match uu___ with | (k, uu___1) -> k = key)
               fields
       with
       | FStar_Pervasives_Native.Some (uu___, v) ->
           FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let json_get_string (key : Prims.string) (obj : json_value) :
  Prims.string FStar_Pervasives_Native.option=
  match json_get_field key obj with
  | FStar_Pervasives_Native.Some (JString s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let json_get_bool (key : Prims.string) (obj : json_value) :
  Prims.bool FStar_Pervasives_Native.option=
  match json_get_field key obj with
  | FStar_Pervasives_Native.Some (JBool b) -> FStar_Pervasives_Native.Some b
  | uu___ -> FStar_Pervasives_Native.None
let json_get_array (key : Prims.string) (obj : json_value) :
  json_value Prims.list FStar_Pervasives_Native.option=
  match json_get_field key obj with
  | FStar_Pervasives_Native.Some (JArray items) ->
      FStar_Pervasives_Native.Some items
  | uu___ -> FStar_Pervasives_Native.None
let json_get_string_array (key : Prims.string) (obj : json_value) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match json_get_array key obj with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some items ->
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.concatMap
           (fun v -> match v with | JString s -> [s] | uu___ -> []) items)
let mk_literal (lexical : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if RDF_Graph_Executable.is_iri dt
  then
    let lit =
      {
        RDF_Graph_Executable.lexical_form = lexical;
        RDF_Graph_Executable.datatype = dt;
        RDF_Graph_Executable.lang_tag = lang
      } in
    (if RDF_Graph_Executable.literal_wf lit
     then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal lit)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let parse_binding_value (obj : json_value) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match json_get_string "type" obj with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some typ ->
      let val_str =
        match json_get_string "value" obj with
        | FStar_Pervasives_Native.Some s -> s
        | FStar_Pervasives_Native.None -> "" in
      if typ = "uri"
      then
        (if RDF_Graph_Executable.is_iri val_str
         then
           FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI val_str)
         else FStar_Pervasives_Native.None)
      else
        if typ = "bnode"
        then
          FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_BNode val_str)
        else
          if (typ = "literal") || (typ = "typed-literal")
          then
            (let lang = json_get_string "xml:lang" obj in
             let dt = json_get_string "datatype" obj in
             match (lang, dt) with
             | (FStar_Pervasives_Native.Some lang_val, uu___2) ->
                 mk_literal val_str RDF_Graph_Executable.rdf_lang_string
                   (FStar_Pervasives_Native.Some lang_val)
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
                dt_val) ->
                 mk_literal val_str dt_val FStar_Pervasives_Native.None
             | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                 ->
                 mk_literal val_str RDF_Graph_Executable.xsd_string
                   FStar_Pervasives_Native.None)
          else FStar_Pervasives_Native.None
let parse_binding_row (obj : json_value) :
  (Prims.string * RDF_Graph_Executable.rdf_term) Prims.list=
  match obj with
  | JObject fields ->
      FStar_List_Tot_Base.concatMap
        (fun pair ->
           let uu___ = pair in
           match uu___ with
           | (var_name, val_obj) ->
               (match parse_binding_value val_obj with
                | FStar_Pervasives_Native.Some term -> [(var_name, term)]
                | FStar_Pervasives_Native.None -> [])) fields
  | uu___ -> []
let parse_srj_results (input : Prims.string) :
  (Prims.string Prims.list * (Prims.string * RDF_Graph_Executable.rdf_term)
    Prims.list Prims.list) FStar_Pervasives_Native.option=
  match parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      let vars =
        match json_get_field "head" root with
        | FStar_Pervasives_Native.None -> []
        | FStar_Pervasives_Native.Some head ->
            (match json_get_string_array "vars" head with
             | FStar_Pervasives_Native.Some vs -> vs
             | FStar_Pervasives_Native.None -> []) in
      (match json_get_field "results" root with
       | FStar_Pervasives_Native.Some results_obj ->
           (match json_get_array "bindings" results_obj with
            | FStar_Pervasives_Native.Some bindings ->
                let rows = FStar_List_Tot_Base.map parse_binding_row bindings in
                FStar_Pervasives_Native.Some (vars, rows)
            | FStar_Pervasives_Native.None ->
                FStar_Pervasives_Native.Some (vars, []))
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some (vars, []))
let parse_srj_boolean (input : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option=
  match parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root -> json_get_bool "boolean" root
