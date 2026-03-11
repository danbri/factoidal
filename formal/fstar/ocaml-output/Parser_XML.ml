open Prims
type xml_attribute = {
  attr_name: Prims.string ;
  attr_value: Prims.string }
let __proj__Mkxml_attribute__item__attr_name (projectee : xml_attribute) :
  Prims.string=
  match projectee with | { attr_name; attr_value;_} -> attr_name
let __proj__Mkxml_attribute__item__attr_value (projectee : xml_attribute) :
  Prims.string=
  match projectee with | { attr_name; attr_value;_} -> attr_value
type xml_node =
  | XText of Prims.string 
  | XElement of Prims.string * xml_attribute Prims.list * xml_node Prims.list
  
  | XComment of Prims.string 
  | XCDATA of Prims.string 
let uu___is_XText (projectee : xml_node) : Prims.bool=
  match projectee with | XText text -> true | uu___ -> false
let __proj__XText__item__text (projectee : xml_node) : Prims.string=
  match projectee with | XText text -> text
let uu___is_XElement (projectee : xml_node) : Prims.bool=
  match projectee with
  | XElement (tag, attrs, children) -> true
  | uu___ -> false
let __proj__XElement__item__tag (projectee : xml_node) : Prims.string=
  match projectee with | XElement (tag, attrs, children) -> tag
let __proj__XElement__item__attrs (projectee : xml_node) :
  xml_attribute Prims.list=
  match projectee with | XElement (tag, attrs, children) -> attrs
let __proj__XElement__item__children (projectee : xml_node) :
  xml_node Prims.list=
  match projectee with | XElement (tag, attrs, children) -> children
let uu___is_XComment (projectee : xml_node) : Prims.bool=
  match projectee with | XComment text -> true | uu___ -> false
let __proj__XComment__item__text (projectee : xml_node) : Prims.string=
  match projectee with | XComment text -> text
let uu___is_XCDATA (projectee : xml_node) : Prims.bool=
  match projectee with | XCDATA text -> true | uu___ -> false
let __proj__XCDATA__item__text (projectee : xml_node) : Prims.string=
  match projectee with | XCDATA text -> text
let is_name_start_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  if code < (Prims.of_int (0x80))
  then
    ((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
        ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
       || (code = (Prims.of_int (0x5F))))
      || (code = (Prims.of_int (0x3A)))
  else code >= (Prims.of_int (0xC0))
let is_name_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  if code < (Prims.of_int (0x80))
  then
    (((((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A))))
           ||
           ((code >= (Prims.of_int (0x61))) &&
              (code <= (Prims.of_int (0x7A)))))
          ||
          ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
         || (code = (Prims.of_int (0x5F))))
        || (code = (Prims.of_int (0x3A))))
       || (code = (Prims.of_int (0x2D))))
      || (code = (Prims.of_int (0x2E)))
  else (code >= (Prims.of_int (0xC0))) || (code = (Prims.of_int (0xB7)))
let is_xml_space (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let parse_xml_name : Prims.string Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected XML name", pos)
    else
      (let ch = FStar_String.index input pos in
       if is_name_start_char ch
       then
         match Parser_Combinators.ptake_while_pos is_name_char input
                 (pos + Prims.int_one)
         with
         | Parser_Combinators.ParseOk (rest, pos') ->
             Parser_Combinators.ParseOk
               ((FStar_String.concat ""
                   [FStar_String.string_of_char ch; rest]), pos')
         | Parser_Combinators.ParseFail (msg, fpos) ->
             Parser_Combinators.ParseFail (msg, fpos)
       else
         Parser_Combinators.ParseFail
           ("expected XML name start character", pos))
let hex_digit_value (c : FStar_Char.char) : Prims.int=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
  then code - (Prims.of_int (0x30))
  else
    if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))
    then (code - (Prims.of_int (0x41))) + (Prims.of_int (10))
    else
      if (code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66)))
      then (code - (Prims.of_int (0x61))) + (Prims.of_int (10))
      else Prims.int_zero
let rec parse_ref_digits (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  FStar_Char.char Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("character reference too long", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then
       Parser_Combinators.ParseFail ("unterminated character reference", pos)
     else
       (let ch = FStar_String.index input pos in
        if ch = 59
        then
          Parser_Combinators.ParseOk
            ((FStar_List_Tot_Base.rev acc), (pos + Prims.int_one))
        else
          parse_ref_digits input (pos + Prims.int_one) (ch :: acc)
            (fuel - Prims.int_one)))
let rec pow10 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec pow16 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (16)) * (pow16 (n - Prims.int_one))
let rec chars_to_dec (cs : FStar_Char.char Prims.list) : Prims.int=
  match cs with
  | [] -> Prims.int_zero
  | c::rest ->
      let digit = (FStar_Char.int_of_char c) - (Prims.of_int (0x30)) in
      (digit * (pow10 (FStar_List_Tot_Base.length rest))) +
        (chars_to_dec rest)
let rec chars_to_hex (cs : FStar_Char.char Prims.list) : Prims.int=
  match cs with
  | [] -> Prims.int_zero
  | c::rest ->
      ((hex_digit_value c) * (pow16 (FStar_List_Tot_Base.length rest))) +
        (chars_to_hex rest)
let codepoint_to_string (cp : Prims.int) : Prims.string=
  if (cp >= Prims.int_zero) && (cp <= (Prims.of_int (127)))
  then FStar_String.string_of_char (FStar_Char.char_of_int cp)
  else
    if (cp > (Prims.of_int (127))) && (cp <= (Prims.parse_int "0xFFFF"))
    then
      FStar_String.string_of_char
        (FStar_Char.char_of_int ((mod) cp (Prims.of_int (256))))
    else "?"
let parse_reference (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("unterminated reference", pos)
  else
    (let ch = FStar_String.index input pos in
     if ch = 35
     then
       (if (pos + Prims.int_one) >= len
        then
          Parser_Combinators.ParseFail
            ("unterminated character reference", pos)
        else
          (let ch2 = FStar_String.index input (pos + Prims.int_one) in
           if (ch2 = 120) || (ch2 = 88)
           then
             match parse_ref_digits input (pos + (Prims.of_int (2))) []
                     (Prims.of_int (10))
             with
             | Parser_Combinators.ParseOk (digits, pos') ->
                 Parser_Combinators.ParseOk
                   ((codepoint_to_string (chars_to_hex digits)), pos')
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos)
           else
             (match parse_ref_digits input (pos + Prims.int_one) []
                      (Prims.of_int (10))
              with
              | Parser_Combinators.ParseOk (digits, pos') ->
                  Parser_Combinators.ParseOk
                    ((codepoint_to_string (chars_to_dec digits)), pos')
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos))))
     else
       (match Parser_Combinators.pstring "amp;" input pos with
        | Parser_Combinators.ParseOk (uu___2, pos') ->
            Parser_Combinators.ParseOk ("&", pos')
        | Parser_Combinators.ParseFail (uu___2, uu___3) ->
            (match Parser_Combinators.pstring "lt;" input pos with
             | Parser_Combinators.ParseOk (uu___4, pos') ->
                 Parser_Combinators.ParseOk ("<", pos')
             | Parser_Combinators.ParseFail (uu___4, uu___5) ->
                 (match Parser_Combinators.pstring "gt;" input pos with
                  | Parser_Combinators.ParseOk (uu___6, pos') ->
                      Parser_Combinators.ParseOk (">", pos')
                  | Parser_Combinators.ParseFail (uu___6, uu___7) ->
                      (match Parser_Combinators.pstring "quot;" input pos
                       with
                       | Parser_Combinators.ParseOk (uu___8, pos') ->
                           Parser_Combinators.ParseOk ("\"", pos')
                       | Parser_Combinators.ParseFail (uu___8, uu___9) ->
                           (match Parser_Combinators.pstring "apos;" input
                                    pos
                            with
                            | Parser_Combinators.ParseOk (uu___10, pos') ->
                                Parser_Combinators.ParseOk ("'", pos')
                            | Parser_Combinators.ParseFail (uu___10, uu___11)
                                ->
                                Parser_Combinators.ParseFail
                                  ("unknown entity reference", pos)))))))
let rec parse_attr_value_body (qch : FStar_Char.char) (input : Prims.string)
  (pos : Prims.nat) (acc : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("attribute value too long", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated attribute value", pos)
     else
       (let ch = FStar_String.index input pos in
        if ch = qch
        then
          Parser_Combinators.ParseOk
            ((FStar_String.concat "" (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if ch = 38
          then
            (match parse_reference input (pos + Prims.int_one) with
             | Parser_Combinators.ParseOk (decoded, pos') ->
                 parse_attr_value_body qch input pos' (decoded :: acc)
                   (fuel - Prims.int_one)
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))
          else
            (match Parser_Combinators.ptake_while_pos
                     (fun c -> (c <> qch) && (c <> 38)) input pos
             with
             | Parser_Combinators.ParseOk (s, pos') ->
                 if (FStar_String.strlen s) > Prims.int_zero
                 then
                   parse_attr_value_body qch input pos' (s :: acc)
                     (fuel - Prims.int_one)
                 else
                   parse_attr_value_body qch input (pos + Prims.int_one)
                     ((FStar_String.string_of_char ch) :: acc)
                     (fuel - Prims.int_one)
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))))
let parse_attr_value (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected attribute value", pos)
  else
    (let qch = FStar_String.index input pos in
     if (qch = 34) || (qch = 39)
     then
       let fuel = len - pos in
       parse_attr_value_body qch input (pos + Prims.int_one) [] fuel
     else
       Parser_Combinators.ParseFail
         ("expected quote to start attribute value", pos))
let skip_xml_space (input : Prims.string) (pos : Prims.nat) :
  unit Parser_Combinators.parse_result=
  match Parser_Combinators.ptake_while_pos is_xml_space input pos with
  | Parser_Combinators.ParseOk (uu___, pos') ->
      Parser_Combinators.ParseOk ((), pos')
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_xml_attribute (input : Prims.string) (pos : Prims.nat) :
  xml_attribute Parser_Combinators.parse_result=
  match parse_xml_name input pos with
  | Parser_Combinators.ParseOk (name, pos1) ->
      (match skip_xml_space input pos1 with
       | Parser_Combinators.ParseOk ((), pos2) ->
           (match Parser_Combinators.pchar 61 input pos2 with
            | Parser_Combinators.ParseOk (uu___, pos3) ->
                (match skip_xml_space input pos3 with
                 | Parser_Combinators.ParseOk ((), pos4) ->
                     (match parse_attr_value input pos4 with
                      | Parser_Combinators.ParseOk (value, pos5) ->
                          Parser_Combinators.ParseOk
                            ({ attr_name = name; attr_value = value }, pos5)
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos))
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos))
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos))
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec parse_attributes (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) :
  xml_attribute Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ([], pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseOk ([], pos)
     else
       (match Parser_Combinators.ptake_while1_pos is_xml_space input pos with
        | Parser_Combinators.ParseOk (uu___2, pos1) ->
            if pos1 < len
            then
              let ch = FStar_String.index input pos1 in
              (if is_name_start_char ch
               then
                 match parse_xml_attribute input pos1 with
                 | Parser_Combinators.ParseOk (attr, pos2) ->
                     (match parse_attributes input pos2
                              (fuel - Prims.int_one)
                      with
                      | Parser_Combinators.ParseOk (attrs, pos3) ->
                          Parser_Combinators.ParseOk ((attr :: attrs), pos3)
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos))
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
               else Parser_Combinators.ParseOk ([], pos1))
            else Parser_Combinators.ParseOk ([], pos1)
        | Parser_Combinators.ParseFail (uu___2, uu___3) ->
            Parser_Combinators.ParseOk ([], pos)))
let rec parse_text_content (input : Prims.string) (pos : Prims.nat)
  (acc : Prims.string Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseOk
      ((FStar_String.concat "" (FStar_List_Tot_Base.rev acc)), pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then
       Parser_Combinators.ParseOk
         ((FStar_String.concat "" (FStar_List_Tot_Base.rev acc)), pos)
     else
       (let ch = FStar_String.index input pos in
        if ch = 60
        then
          Parser_Combinators.ParseOk
            ((FStar_String.concat "" (FStar_List_Tot_Base.rev acc)), pos)
        else
          if ch = 38
          then
            (match parse_reference input (pos + Prims.int_one) with
             | Parser_Combinators.ParseOk (decoded, pos') ->
                 parse_text_content input pos' (decoded :: acc)
                   (fuel - Prims.int_one)
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))
          else
            (match Parser_Combinators.ptake_while_pos
                     (fun c -> (c <> 60) && (c <> 38)) input pos
             with
             | Parser_Combinators.ParseOk (s, pos') ->
                 if (FStar_String.strlen s) > Prims.int_zero
                 then
                   parse_text_content input pos' (s :: acc)
                     (fuel - Prims.int_one)
                 else
                   parse_text_content input (pos + Prims.int_one)
                     ((FStar_String.string_of_char ch) :: acc)
                     (fuel - Prims.int_one)
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))))
let parse_xml_text (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  let len = FStar_String.strlen input in
  let fuel = (len - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then
    match parse_text_content input pos [] fuel with
    | Parser_Combinators.ParseOk (text, pos') ->
        (if (FStar_String.strlen text) > Prims.int_zero
         then Parser_Combinators.ParseOk ((XText text), pos')
         else Parser_Combinators.ParseFail ("empty text node", pos))
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
  else Parser_Combinators.ParseFail ("unexpected position", pos)
let rec parse_comment_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated comment", pos)
  else
    (let len = FStar_String.strlen input in
     if (pos + (Prims.of_int (2))) < len
     then
       let c0 = FStar_String.index input pos in
       let c1 = FStar_String.index input (pos + Prims.int_one) in
       let c2 = FStar_String.index input (pos + (Prims.of_int (2))) in
       (if ((c0 = 45) && (c1 = 45)) && (c2 = 62)
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + (Prims.of_int (3))))
        else
          parse_comment_body input (pos + Prims.int_one) (c0 :: acc)
            (fuel - Prims.int_one))
     else
       if pos < len
       then
         (let c0 = FStar_String.index input pos in
          parse_comment_body input (pos + Prims.int_one) (c0 :: acc)
            (fuel - Prims.int_one))
       else Parser_Combinators.ParseFail ("unterminated comment", pos))
let parse_xml_comment (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<!--" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      let len = FStar_String.strlen input in
      let fuel = (len - pos1) + Prims.int_one in
      (match parse_comment_body input pos1 [] fuel with
       | Parser_Combinators.ParseOk (text, pos2) ->
           Parser_Combinators.ParseOk ((XComment text), pos2)
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec parse_cdata_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated CDATA section", pos)
  else
    (let len = FStar_String.strlen input in
     if (pos + (Prims.of_int (2))) < len
     then
       let c0 = FStar_String.index input pos in
       let c1 = FStar_String.index input (pos + Prims.int_one) in
       let c2 = FStar_String.index input (pos + (Prims.of_int (2))) in
       (if ((c0 = 93) && (c1 = 93)) && (c2 = 62)
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + (Prims.of_int (3))))
        else
          parse_cdata_body input (pos + Prims.int_one) (c0 :: acc)
            (fuel - Prims.int_one))
     else
       if pos < len
       then
         (let c0 = FStar_String.index input pos in
          parse_cdata_body input (pos + Prims.int_one) (c0 :: acc)
            (fuel - Prims.int_one))
       else Parser_Combinators.ParseFail ("unterminated CDATA section", pos))
let parse_xml_cdata (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<![CDATA[" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      let len = FStar_String.strlen input in
      let fuel = (len - pos1) + Prims.int_one in
      (match parse_cdata_body input pos1 [] fuel with
       | Parser_Combinators.ParseOk (text, pos2) ->
           Parser_Combinators.ParseOk ((XCDATA text), pos2)
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let parse_xml_declaration (input : Prims.string) (pos : Prims.nat) :
  xml_attribute Prims.list Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<?xml" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      let len = FStar_String.strlen input in
      let fuel = (len - pos1) + Prims.int_one in
      (match parse_attributes input pos1 fuel with
       | Parser_Combinators.ParseOk (attrs, pos2) ->
           (match skip_xml_space input pos2 with
            | Parser_Combinators.ParseOk ((), pos3) ->
                (match Parser_Combinators.pstring "?>" input pos3 with
                 | Parser_Combinators.ParseOk (uu___1, pos4) ->
                     Parser_Combinators.ParseOk (attrs, pos4)
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos))
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos))
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec parse_children (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xml_node Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ([], pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseOk ([], pos)
     else
       (let ch = FStar_String.index input pos in
        if ch = 60
        then
          (if (pos + Prims.int_one) < len
           then
             let ch2 = FStar_String.index input (pos + Prims.int_one) in
             (if ch2 = 47
              then Parser_Combinators.ParseOk ([], pos)
              else
                if ch2 = 33
                then
                  (match parse_xml_comment input pos with
                   | Parser_Combinators.ParseOk (comment, pos') ->
                       (match parse_children input pos'
                                (fuel - Prims.int_one)
                        with
                        | Parser_Combinators.ParseOk (rest, pos'') ->
                            Parser_Combinators.ParseOk
                              ((comment :: rest), pos'')
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos))
                   | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                       (match parse_xml_cdata input pos with
                        | Parser_Combinators.ParseOk (cdata, pos') ->
                            (match parse_children input pos'
                                     (fuel - Prims.int_one)
                             with
                             | Parser_Combinators.ParseOk (rest, pos'') ->
                                 Parser_Combinators.ParseOk
                                   ((cdata :: rest), pos'')
                             | Parser_Combinators.ParseFail (msg, fpos) ->
                                 Parser_Combinators.ParseFail (msg, fpos))
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos)))
                else
                  (match parse_xml_element input pos (fuel - Prims.int_one)
                   with
                   | Parser_Combinators.ParseOk (elem, pos') ->
                       (match parse_children input pos'
                                (fuel - Prims.int_one)
                        with
                        | Parser_Combinators.ParseOk (rest, pos'') ->
                            Parser_Combinators.ParseOk
                              ((elem :: rest), pos'')
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos))
                   | Parser_Combinators.ParseFail (msg, fpos) ->
                       Parser_Combinators.ParseFail (msg, fpos)))
           else
             Parser_Combinators.ParseFail ("unexpected end after '<'", pos))
        else
          (match parse_xml_text input pos with
           | Parser_Combinators.ParseOk (text_node, pos') ->
               if pos' = pos
               then Parser_Combinators.ParseOk ([], pos)
               else
                 (match parse_children input pos' (fuel - Prims.int_one) with
                  | Parser_Combinators.ParseOk (rest, pos'') ->
                      Parser_Combinators.ParseOk ((text_node :: rest), pos'')
                  | Parser_Combinators.ParseFail (msg, fpos) ->
                      Parser_Combinators.ParseFail (msg, fpos))
           | Parser_Combinators.ParseFail (uu___3, uu___4) ->
               Parser_Combinators.ParseOk ([], pos))))
and parse_xml_element (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : xml_node Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("element nesting too deep (out of fuel)", pos)
  else
    (match Parser_Combinators.pchar 60 input pos with
     | Parser_Combinators.ParseOk (uu___1, pos1) ->
         (match parse_xml_name input pos1 with
          | Parser_Combinators.ParseOk (tag, pos2) ->
              let len = FStar_String.strlen input in
              let attr_fuel =
                if pos2 <= len
                then (len - pos2) + Prims.int_one
                else Prims.int_one in
              (match parse_attributes input pos2 attr_fuel with
               | Parser_Combinators.ParseOk (attrs, pos3) ->
                   (match skip_xml_space input pos3 with
                    | Parser_Combinators.ParseOk ((), pos4) ->
                        (match Parser_Combinators.pstring "/>" input pos4
                         with
                         | Parser_Combinators.ParseOk (uu___2, pos5) ->
                             Parser_Combinators.ParseOk
                               ((XElement (tag, attrs, [])), pos5)
                         | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                             (match Parser_Combinators.pchar 62 input pos4
                              with
                              | Parser_Combinators.ParseOk (uu___4, pos5) ->
                                  (match parse_children input pos5
                                           (fuel - Prims.int_one)
                                   with
                                   | Parser_Combinators.ParseOk
                                       (children, pos6) ->
                                       (match Parser_Combinators.pstring "</"
                                                input pos6
                                        with
                                        | Parser_Combinators.ParseOk
                                            (uu___5, pos7) ->
                                            (match parse_xml_name input pos7
                                             with
                                             | Parser_Combinators.ParseOk
                                                 (close_tag, pos8) ->
                                                 if close_tag = tag
                                                 then
                                                   (match skip_xml_space
                                                            input pos8
                                                    with
                                                    | Parser_Combinators.ParseOk
                                                        ((), pos9) ->
                                                        (match Parser_Combinators.pchar
                                                                 62 input
                                                                 pos9
                                                         with
                                                         | Parser_Combinators.ParseOk
                                                             (uu___6, pos10)
                                                             ->
                                                             Parser_Combinators.ParseOk
                                                               ((XElement
                                                                   (tag,
                                                                    attrs,
                                                                    children)),
                                                                 pos10)
                                                         | Parser_Combinators.ParseFail
                                                             (msg, fpos) ->
                                                             Parser_Combinators.ParseFail
                                                               (msg, fpos))
                                                    | Parser_Combinators.ParseFail
                                                        (msg, fpos) ->
                                                        Parser_Combinators.ParseFail
                                                          (msg, fpos))
                                                 else
                                                   Parser_Combinators.ParseFail
                                                     ((FStar_String.concat ""
                                                         ["closing tag '</";
                                                         close_tag;
                                                         ">' does not match opening '<";
                                                         tag;
                                                         ">'"]), pos7)
                                             | Parser_Combinators.ParseFail
                                                 (msg, fpos) ->
                                                 Parser_Combinators.ParseFail
                                                   (msg, fpos))
                                        | Parser_Combinators.ParseFail
                                            (msg, fpos) ->
                                            Parser_Combinators.ParseFail
                                              (msg, fpos))
                                   | Parser_Combinators.ParseFail (msg, fpos)
                                       ->
                                       Parser_Combinators.ParseFail
                                         (msg, fpos))
                              | Parser_Combinators.ParseFail (msg, fpos) ->
                                  Parser_Combinators.ParseFail (msg, fpos)))
                    | Parser_Combinators.ParseFail (msg, fpos) ->
                        Parser_Combinators.ParseFail (msg, fpos))
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos))
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos))
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos))
let rec skip_misc (input : Prims.string) (pos : Prims.nat) (fuel : Prims.nat)
  : unit Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ((), pos)
  else
    (match skip_xml_space input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         (match parse_xml_comment input pos1 with
          | Parser_Combinators.ParseOk (uu___1, pos2) ->
              skip_misc input pos2 (fuel - Prims.int_one)
          | Parser_Combinators.ParseFail (uu___1, uu___2) ->
              Parser_Combinators.ParseOk ((), pos1))
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos))
let parse_xml_document (input : Prims.string) :
  xml_node FStar_Pervasives_Native.option=
  let len = FStar_String.strlen input in
  let fuel = len + Prims.int_one in
  match skip_xml_space input Prims.int_zero with
  | Parser_Combinators.ParseOk ((), pos0) ->
      let pos1 =
        match parse_xml_declaration input pos0 with
        | Parser_Combinators.ParseOk (_attrs, pos') -> pos'
        | Parser_Combinators.ParseFail (uu___, uu___1) -> pos0 in
      (match skip_misc input pos1 fuel with
       | Parser_Combinators.ParseOk ((), pos2) ->
           (match parse_xml_element input pos2 fuel with
            | Parser_Combinators.ParseOk (root, _pos3) ->
                FStar_Pervasives_Native.Some root
            | Parser_Combinators.ParseFail (uu___, uu___1) ->
                FStar_Pervasives_Native.None)
       | Parser_Combinators.ParseFail (uu___, uu___1) ->
           FStar_Pervasives_Native.None)
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
let element_tag (node : xml_node) :
  Prims.string FStar_Pervasives_Native.option=
  match node with
  | XElement (tag, uu___, uu___1) -> FStar_Pervasives_Native.Some tag
  | uu___ -> FStar_Pervasives_Native.None
let element_attrs (node : xml_node) : xml_attribute Prims.list=
  match node with | XElement (uu___, attrs, uu___1) -> attrs | uu___ -> []
let element_children (node : xml_node) : xml_node Prims.list=
  match node with
  | XElement (uu___, uu___1, children) -> children
  | uu___ -> []
let find_attr (name : Prims.string) (attrs : xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find (fun a -> a.attr_name = name) attrs with
  | FStar_Pervasives_Native.Some a ->
      FStar_Pervasives_Native.Some (a.attr_value)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec text_content (node : xml_node) : Prims.string=
  match node with
  | XText t -> t
  | XCDATA t -> t
  | XComment uu___ -> ""
  | XElement (uu___, uu___1, children) ->
      FStar_String.concat "" (text_content_list children)
and text_content_list (nodes : xml_node Prims.list) :
  Prims.string Prims.list=
  match nodes with
  | [] -> []
  | hd::tl -> (text_content hd) :: (text_content_list tl)
let child_elements (tag : Prims.string) (node : xml_node) :
  xml_node Prims.list=
  match node with
  | XElement (uu___, uu___1, children) ->
      FStar_List_Tot_Base.filter
        (fun child ->
           match child with
           | XElement (t, uu___2, uu___3) -> t = tag
           | uu___2 -> false) children
  | uu___ -> []
let child_element (tag : Prims.string) (node : xml_node) :
  xml_node FStar_Pervasives_Native.option=
  match child_elements tag node with
  | hd::uu___ -> FStar_Pervasives_Native.Some hd
  | [] -> FStar_Pervasives_Native.None
let all_child_elements (node : xml_node) : xml_node Prims.list=
  match node with
  | XElement (uu___, uu___1, children) ->
      FStar_List_Tot_Base.filter
        (fun child ->
           match child with
           | XElement (uu___2, uu___3, uu___4) -> true
           | uu___2 -> false) children
  | uu___ -> []
