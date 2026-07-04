open Prims
type json_val =
  | JNull 
  | JBool of Prims.bool 
  | JString of Prims.string 
  | JNumber of Prims.string 
  | JArray of json_val Prims.list 
  | JObject of (Prims.string * json_val) Prims.list 
let uu___is_JNull (projectee : json_val) : Prims.bool=
  match projectee with | JNull -> true | uu___ -> false
let uu___is_JBool (projectee : json_val) : Prims.bool=
  match projectee with | JBool _0 -> true | uu___ -> false
let __proj__JBool__item___0 (projectee : json_val) : Prims.bool=
  match projectee with | JBool _0 -> _0
let uu___is_JString (projectee : json_val) : Prims.bool=
  match projectee with | JString _0 -> true | uu___ -> false
let __proj__JString__item___0 (projectee : json_val) : Prims.string=
  match projectee with | JString _0 -> _0
let uu___is_JNumber (projectee : json_val) : Prims.bool=
  match projectee with | JNumber _0 -> true | uu___ -> false
let __proj__JNumber__item___0 (projectee : json_val) : Prims.string=
  match projectee with | JNumber _0 -> _0
let uu___is_JArray (projectee : json_val) : Prims.bool=
  match projectee with | JArray _0 -> true | uu___ -> false
let __proj__JArray__item___0 (projectee : json_val) : json_val Prims.list=
  match projectee with | JArray _0 -> _0
let uu___is_JObject (projectee : json_val) : Prims.bool=
  match projectee with | JObject _0 -> true | uu___ -> false
let __proj__JObject__item___0 (projectee : json_val) :
  (Prims.string * json_val) Prims.list=
  match projectee with | JObject _0 -> _0
let rec json_size (v : json_val) : Prims.pos=
  match v with
  | JArray items -> Prims.int_one + (json_size_items items)
  | JObject fields -> Prims.int_one + (json_size_fields fields)
  | uu___ -> Prims.int_one
and json_size_items (items : json_val Prims.list) : Prims.nat=
  match items with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (json_size hd)) + (json_size_items tl)
and json_size_fields (fields : (Prims.string * json_val) Prims.list) :
  Prims.nat=
  match fields with
  | [] -> Prims.int_zero
  | (uu___, v)::tl -> (Prims.int_one + (json_size v)) + (json_size_fields tl)
let jbyte_at (input : Prims.string) (pos : Prims.nat) : Prims.int=
  if pos < (Parser_FastString.fs_byte_length input)
  then Parser_FastString.fs_byte_at input pos
  else (Prims.of_int (-1))
let rec json_skip_ws (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let b = jbyte_at input pos in
     if
       (((b = (Prims.of_int (0x20))) || (b = (Prims.of_int (0x09)))) ||
          (b = (Prims.of_int (0x0A))))
         || (b = (Prims.of_int (0x0D)))
     then json_skip_ws input (pos + Prims.int_one) (fuel - Prims.int_one)
     else pos)
let json_hex_val (b : Prims.int) : Prims.nat FStar_Pervasives_Native.option=
  if (b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))
  then FStar_Pervasives_Native.Some (b - (Prims.of_int (0x30)))
  else
    if (b >= (Prims.of_int (0x41))) && (b <= (Prims.of_int (0x46)))
    then
      FStar_Pervasives_Native.Some
        ((b - (Prims.of_int (0x41))) + (Prims.of_int (10)))
    else
      if (b >= (Prims.of_int (0x61))) && (b <= (Prims.of_int (0x66)))
      then
        FStar_Pervasives_Native.Some
          ((b - (Prims.of_int (0x61))) + (Prims.of_int (10)))
      else FStar_Pervasives_Native.None
let json_read_hex4 (input : Prims.string) (pos : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((json_hex_val (jbyte_at input pos)),
          (json_hex_val (jbyte_at input (pos + Prims.int_one))),
          (json_hex_val (jbyte_at input (pos + (Prims.of_int (2))))),
          (json_hex_val (jbyte_at input (pos + (Prims.of_int (3))))))
  with
  | (FStar_Pervasives_Native.Some h0, FStar_Pervasives_Native.Some h1,
     FStar_Pervasives_Native.Some h2, FStar_Pervasives_Native.Some h3) ->
      FStar_Pervasives_Native.Some
        ((((h0 * (Prims.of_int (4096))) + (h1 * (Prims.of_int (256)))) +
            (h2 * (Prims.of_int (16))))
           + h3)
  | (uu___, uu___1, uu___2, uu___3) -> FStar_Pervasives_Native.None
let json_utf8_of_codepoint (cp : Prims.nat) : Prims.string=
  if
    (cp < (Prims.of_int (0xD7FF))) ||
      ((cp >= (Prims.of_int (0xE000))) &&
         (cp <= (Prims.parse_int "0x10FFFF")))
  then FStar_String.string_of_list [FStar_Char.char_of_int cp]
  else
    FStar_String.string_of_list
      [FStar_Char.char_of_int (Prims.of_int (0xFFFD))]
let json_escape_piece (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let esc = jbyte_at input (pos + Prims.int_one) in
  if esc = (Prims.of_int (0x22))
  then
    Parser_Combinators.ParseOk
      ((json_utf8_of_codepoint (Prims.of_int (0x22))),
        (pos + (Prims.of_int (2))))
  else
    if esc = (Prims.of_int (0x5C))
    then
      Parser_Combinators.ParseOk
        ((json_utf8_of_codepoint (Prims.of_int (0x5C))),
          (pos + (Prims.of_int (2))))
    else
      if esc = (Prims.of_int (0x2F))
      then
        Parser_Combinators.ParseOk
          ((json_utf8_of_codepoint (Prims.of_int (0x2F))),
            (pos + (Prims.of_int (2))))
      else
        if esc = (Prims.of_int (0x62))
        then
          Parser_Combinators.ParseOk
            ((json_utf8_of_codepoint (Prims.of_int (0x08))),
              (pos + (Prims.of_int (2))))
        else
          if esc = (Prims.of_int (0x66))
          then
            Parser_Combinators.ParseOk
              ((json_utf8_of_codepoint (Prims.of_int (0x0C))),
                (pos + (Prims.of_int (2))))
          else
            if esc = (Prims.of_int (0x6E))
            then
              Parser_Combinators.ParseOk
                ((json_utf8_of_codepoint (Prims.of_int (0x0A))),
                  (pos + (Prims.of_int (2))))
            else
              if esc = (Prims.of_int (0x72))
              then
                Parser_Combinators.ParseOk
                  ((json_utf8_of_codepoint (Prims.of_int (0x0D))),
                    (pos + (Prims.of_int (2))))
              else
                if esc = (Prims.of_int (0x74))
                then
                  Parser_Combinators.ParseOk
                    ((json_utf8_of_codepoint (Prims.of_int (0x09))),
                      (pos + (Prims.of_int (2))))
                else
                  if esc = (Prims.of_int (0x75))
                  then
                    (match json_read_hex4 input (pos + (Prims.of_int (2)))
                     with
                     | FStar_Pervasives_Native.None ->
                         Parser_Combinators.ParseFail
                           ("invalid hex in unicode escape", pos)
                     | FStar_Pervasives_Native.Some cp ->
                         if
                           (cp >= (Prims.of_int (0xD800))) &&
                             (cp <= (Prims.of_int (0xDBFF)))
                         then
                           (if
                              ((jbyte_at input (pos + (Prims.of_int (6)))) =
                                 (Prims.of_int (0x5C)))
                                &&
                                ((jbyte_at input (pos + (Prims.of_int (7))))
                                   = (Prims.of_int (0x75)))
                            then
                              match json_read_hex4 input
                                      (pos + (Prims.of_int (8)))
                              with
                              | FStar_Pervasives_Native.None ->
                                  Parser_Combinators.ParseFail
                                    ("invalid hex in low surrogate escape",
                                      pos)
                              | FStar_Pervasives_Native.Some lo ->
                                  (if
                                     (lo >= (Prims.of_int (0xDC00))) &&
                                       (lo <= (Prims.of_int (0xDFFF)))
                                   then
                                     let combined =
                                       ((Prims.parse_int "0x10000") +
                                          ((cp - (Prims.of_int (0xD800))) *
                                             (Prims.of_int (0x400))))
                                         + (lo - (Prims.of_int (0xDC00))) in
                                     Parser_Combinators.ParseOk
                                       ((json_utf8_of_codepoint combined),
                                         (pos + (Prims.of_int (12))))
                                   else
                                     Parser_Combinators.ParseFail
                                       ("high surrogate not followed by low surrogate",
                                         pos))
                            else
                              Parser_Combinators.ParseFail
                                ("unpaired high surrogate", pos))
                         else
                           if
                             (cp >= (Prims.of_int (0xDC00))) &&
                               (cp <= (Prims.of_int (0xDFFF)))
                           then
                             Parser_Combinators.ParseFail
                               ("lone low surrogate", pos)
                           else
                             Parser_Combinators.ParseOk
                               ((json_utf8_of_codepoint cp),
                                 (pos + (Prims.of_int (6)))))
                  else
                    Parser_Combinators.ParseFail
                      ("invalid escape sequence in JSON string", pos)
let rec json_string_segments (input : Prims.string) (seg_start : Prims.nat)
  (pos : Prims.nat) (segs : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated JSON string", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated JSON string", pos)
     else
       (let b = Parser_FastString.fs_byte_at input pos in
        if b = (Prims.of_int (0x22))
        then
          let segs_done =
            (Parser_FastString.fs_byte_sub input seg_start (pos - seg_start))
            :: segs in
          Parser_Combinators.ParseOk
            ((FStar_String.concat "" (FStar_List_Tot_Base.rev segs_done)),
              (pos + Prims.int_one))
        else
          if b = (Prims.of_int (0x5C))
          then
            (let raw =
               Parser_FastString.fs_byte_sub input seg_start
                 (pos - seg_start) in
             match json_escape_piece input pos with
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos)
             | Parser_Combinators.ParseOk (piece, npos) ->
                 json_string_segments input npos npos (piece :: raw :: segs)
                   (fuel - Prims.int_one))
          else
            if b < (Prims.of_int (0x20))
            then
              Parser_Combinators.ParseFail
                ("raw control character in JSON string", pos)
            else
              json_string_segments input seg_start (pos + Prims.int_one) segs
                (fuel - Prims.int_one)))
let json_parse_string (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if (jbyte_at input pos) = (Prims.of_int (0x22))
  then
    json_string_segments input (pos + Prims.int_one) (pos + Prims.int_one) []
      ((Parser_FastString.fs_byte_length input) + Prims.int_one)
  else Parser_Combinators.ParseFail ("expected JSON string", pos)
let rec json_scan_digits (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let b = jbyte_at input pos in
     if (b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))
     then json_scan_digits input (pos + Prims.int_one) (fuel - Prims.int_one)
     else pos)
let json_number_frac (input : Prims.string) (p : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if (jbyte_at input p) = (Prims.of_int (0x2E))
  then
    let b = jbyte_at input (p + Prims.int_one) in
    (if (b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))
     then
       FStar_Pervasives_Native.Some
         (json_scan_digits input (p + (Prims.of_int (2)))
            ((Parser_FastString.fs_byte_length input) + Prims.int_one))
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.Some p
let json_number_exp (input : Prims.string) (p : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  let b = jbyte_at input p in
  if (b = (Prims.of_int (0x65))) || (b = (Prims.of_int (0x45)))
  then
    let p1 = p + Prims.int_one in
    let p2 =
      if
        ((jbyte_at input p1) = (Prims.of_int (0x2B))) ||
          ((jbyte_at input p1) = (Prims.of_int (0x2D)))
      then p1 + Prims.int_one
      else p1 in
    let d = jbyte_at input p2 in
    (if (d >= (Prims.of_int (0x30))) && (d <= (Prims.of_int (0x39)))
     then
       FStar_Pervasives_Native.Some
         (json_scan_digits input (p2 + Prims.int_one)
            ((Parser_FastString.fs_byte_length input) + Prims.int_one))
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.Some p
let json_parse_number (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let p1 =
    if (jbyte_at input pos) = (Prims.of_int (0x2D))
    then pos + Prims.int_one
    else pos in
  let b1 = jbyte_at input p1 in
  let ipart_end =
    if b1 = (Prims.of_int (0x30))
    then FStar_Pervasives_Native.Some (p1 + Prims.int_one)
    else
      if (b1 >= (Prims.of_int (0x31))) && (b1 <= (Prims.of_int (0x39)))
      then
        FStar_Pervasives_Native.Some
          (json_scan_digits input (p1 + Prims.int_one)
             ((Parser_FastString.fs_byte_length input) + Prims.int_one))
      else FStar_Pervasives_Native.None in
  match ipart_end with
  | FStar_Pervasives_Native.None ->
      Parser_Combinators.ParseFail ("invalid JSON number", pos)
  | FStar_Pervasives_Native.Some p2 ->
      (match json_number_frac input p2 with
       | FStar_Pervasives_Native.None ->
           Parser_Combinators.ParseFail
             ("invalid fraction in JSON number", pos)
       | FStar_Pervasives_Native.Some p4 ->
           (match json_number_exp input p4 with
            | FStar_Pervasives_Native.None ->
                Parser_Combinators.ParseFail
                  ("invalid exponent in JSON number", pos)
            | FStar_Pervasives_Native.Some p_end ->
                Parser_Combinators.ParseOk
                  ((Parser_FastString.fs_byte_sub input pos (p_end - pos)),
                    p_end)))
let rec json_parse_value (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : json_val Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let p =
       json_skip_ws input pos
         ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
     let b = jbyte_at input p in
     if b = (Prims.of_int (0x22))
     then
       match json_parse_string input p with
       | Parser_Combinators.ParseOk (s, np) ->
           Parser_Combinators.ParseOk ((JString s), np)
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
     else
       if b = (Prims.of_int (0x7B))
       then
         json_parse_object input (p + Prims.int_one) (fuel - Prims.int_one)
       else
         if b = (Prims.of_int (0x5B))
         then
           json_parse_array input (p + Prims.int_one) (fuel - Prims.int_one)
         else
           if b = (Prims.of_int (0x74))
           then
             (match Parser_Combinators.pstring "true" input p with
              | Parser_Combinators.ParseOk (uu___4, np) ->
                  Parser_Combinators.ParseOk ((JBool true), np)
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos))
           else
             if b = (Prims.of_int (0x66))
             then
               (match Parser_Combinators.pstring "false" input p with
                | Parser_Combinators.ParseOk (uu___5, np) ->
                    Parser_Combinators.ParseOk ((JBool false), np)
                | Parser_Combinators.ParseFail (msg, fpos) ->
                    Parser_Combinators.ParseFail (msg, fpos))
             else
               if b = (Prims.of_int (0x6E))
               then
                 (match Parser_Combinators.pstring "null" input p with
                  | Parser_Combinators.ParseOk (uu___6, np) ->
                      Parser_Combinators.ParseOk (JNull, np)
                  | Parser_Combinators.ParseFail (msg, fpos) ->
                      Parser_Combinators.ParseFail (msg, fpos))
               else
                 if
                   (b = (Prims.of_int (0x2D))) ||
                     ((b >= (Prims.of_int (0x30))) &&
                        (b <= (Prims.of_int (0x39))))
                 then
                   (match json_parse_number input p with
                    | Parser_Combinators.ParseOk (s, np) ->
                        Parser_Combinators.ParseOk ((JNumber s), np)
                    | Parser_Combinators.ParseFail (msg, fpos) ->
                        Parser_Combinators.ParseFail (msg, fpos))
                 else
                   Parser_Combinators.ParseFail
                     ("unexpected character in JSON value", p))
and json_parse_object (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : json_val Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let p =
       json_skip_ws input pos
         ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
     if (jbyte_at input p) = (Prims.of_int (0x7D))
     then Parser_Combinators.ParseOk ((JObject []), (p + Prims.int_one))
     else json_parse_members input p (fuel - Prims.int_one) [])
and json_parse_members (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (acc : (Prims.string * json_val) Prims.list) :
  json_val Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let p =
       json_skip_ws input pos
         ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
     match json_parse_string input p with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (key, p1) ->
         let p2 =
           json_skip_ws input p1
             ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
         if (jbyte_at input p2) <> (Prims.of_int (0x3A))
         then
           Parser_Combinators.ParseFail ("expected colon in JSON object", p2)
         else
           (match json_parse_value input (p2 + Prims.int_one)
                    (fuel - Prims.int_one)
            with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (v, p3) ->
                let acc2 = (key, v) :: acc in
                let p4 =
                  json_skip_ws input p3
                    ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
                let b = jbyte_at input p4 in
                if b = (Prims.of_int (0x7D))
                then
                  Parser_Combinators.ParseOk
                    ((JObject (FStar_List_Tot_Base.rev acc2)),
                      (p4 + Prims.int_one))
                else
                  if b = (Prims.of_int (0x2C))
                  then
                    json_parse_members input (p4 + Prims.int_one)
                      (fuel - Prims.int_one) acc2
                  else
                    Parser_Combinators.ParseFail
                      ("expected comma or closing brace in JSON object", p4)))
and json_parse_array (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : json_val Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (let p =
       json_skip_ws input pos
         ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
     if (jbyte_at input p) = (Prims.of_int (0x5D))
     then Parser_Combinators.ParseOk ((JArray []), (p + Prims.int_one))
     else json_parse_items input p (fuel - Prims.int_one) [])
and json_parse_items (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (acc : json_val Prims.list) :
  json_val Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("JSON nesting too deep", pos)
  else
    (match json_parse_value input pos (fuel - Prims.int_one) with
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos)
     | Parser_Combinators.ParseOk (v, p1) ->
         let acc2 = v :: acc in
         let p2 =
           json_skip_ws input p1
             ((Parser_FastString.fs_byte_length input) + Prims.int_one) in
         let b = jbyte_at input p2 in
         if b = (Prims.of_int (0x5D))
         then
           Parser_Combinators.ParseOk
             ((JArray (FStar_List_Tot_Base.rev acc2)), (p2 + Prims.int_one))
         else
           if b = (Prims.of_int (0x2C))
           then
             json_parse_items input (p2 + Prims.int_one)
               (fuel - Prims.int_one) acc2
           else
             Parser_Combinators.ParseFail
               ("expected comma or closing bracket in JSON array", p2))
let parse_json_text (input : Prims.string) :
  json_val Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  match json_parse_value input Prims.int_zero (len + Prims.int_one) with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk (v, p) ->
      let p2 = json_skip_ws input p (len + Prims.int_one) in
      if p2 >= len
      then Parser_Combinators.ParseOk (v, p2)
      else
        Parser_Combinators.ParseFail
          ("trailing content after JSON value", p2)
let parse_json (input : Prims.string) :
  json_val FStar_Pervasives_Native.option=
  match parse_json_text input with
  | Parser_Combinators.ParseOk (v, uu___) -> FStar_Pervasives_Native.Some v
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let json_get_field (key : Prims.string) (obj : json_val) :
  json_val FStar_Pervasives_Native.option=
  match obj with
  | JObject fields ->
      (match FStar_List_Tot_Base.find
               (fun kv -> (FStar_Pervasives_Native.fst kv) = key) fields
       with
       | FStar_Pervasives_Native.Some kv ->
           FStar_Pervasives_Native.Some (FStar_Pervasives_Native.snd kv)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let json_get_string (key : Prims.string) (obj : json_val) :
  Prims.string FStar_Pervasives_Native.option=
  match json_get_field key obj with
  | FStar_Pervasives_Native.Some (JString s) ->
      FStar_Pervasives_Native.Some s
  | uu___ -> FStar_Pervasives_Native.None
let json_get_bool (key : Prims.string) (obj : json_val) :
  Prims.bool FStar_Pervasives_Native.option=
  match json_get_field key obj with
  | FStar_Pervasives_Native.Some (JBool b) -> FStar_Pervasives_Native.Some b
  | uu___ -> FStar_Pervasives_Native.None
let json_get_array (key : Prims.string) (obj : json_val) :
  json_val Prims.list FStar_Pervasives_Native.option=
  match json_get_field key obj with
  | FStar_Pervasives_Native.Some (JArray items) ->
      FStar_Pervasives_Native.Some items
  | uu___ -> FStar_Pervasives_Native.None
