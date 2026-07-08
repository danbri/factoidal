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
  | XPI of Prims.string * Prims.string 
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
let uu___is_XPI (projectee : xml_node) : Prims.bool=
  match projectee with | XPI (target, data) -> true | uu___ -> false
let __proj__XPI__item__target (projectee : xml_node) : Prims.string=
  match projectee with | XPI (target, data) -> target
let __proj__XPI__item__data (projectee : xml_node) : Prims.string=
  match projectee with | XPI (target, data) -> data
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
let to_lower_ascii (c : FStar_Char.char) : FStar_Char.char=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (code + (Prims.of_int (0x20)))
  else c
let is_valid_xml_char (cp : Prims.int) : Prims.bool=
  (((((cp = (Prims.of_int (0x9))) || (cp = (Prims.of_int (0xA)))) ||
       (cp = (Prims.of_int (0xD))))
      || ((cp >= (Prims.of_int (0x20))) && (cp <= (Prims.of_int (0xD7FF)))))
     || ((cp >= (Prims.of_int (0xE000))) && (cp <= (Prims.of_int (0xFFFD)))))
    ||
    ((cp >= (Prims.parse_int "0x10000")) &&
       (cp <= (Prims.parse_int "0x10FFFF")))
let is_valid_decoded_char (cp : Prims.int) (adv : Prims.nat) : Prims.bool=
  if (cp = (Prims.of_int (0xFFFD))) && (adv = Prims.int_one)
  then false
  else is_valid_xml_char cp
let is_utf8_continuation_byte (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x80))) && (code <= (Prims.of_int (0xBF)))
let rec scan_chars_valid (input : Prims.string) (pos : Prims.nat)
  (limit : Prims.nat) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    if pos >= limit
    then true
    else
      (let uu___2 = Parser_FastString.fs_cp_at input pos in
       match uu___2 with
       | (cp, adv) ->
           let adv' = if adv = Prims.int_zero then Prims.int_one else adv in
           if is_valid_decoded_char cp adv'
           then
             scan_chars_valid input (pos + adv') limit (fuel - Prims.int_one)
           else false)
let rec bytes_have_double_dash (s : Prims.string) (pos : Prims.nat)
  (limit : Prims.nat) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    if (pos + Prims.int_one) >= limit
    then false
    else
      (let c0 = Parser_FastString.fs_byte_index s pos in
       let c1 = Parser_FastString.fs_byte_index s (pos + Prims.int_one) in
       if (c0 = 45) && (c1 = 45)
       then true
       else
         bytes_have_double_dash s (pos + Prims.int_one) limit
           (fuel - Prims.int_one))
let ends_with_dash (s : Prims.string) : Prims.bool=
  let len = Parser_FastString.fs_byte_length s in
  (len > Prims.int_zero) &&
    ((Parser_FastString.fs_byte_index s (len - Prims.int_one)) = 45)
let rec bytes_have_cdata_close (input : Prims.string) (pos : Prims.nat)
  (limit : Prims.nat) (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    if (pos + (Prims.of_int (2))) >= limit
    then false
    else
      if
        (((Parser_FastString.fs_byte_index input pos) = 93) &&
           ((Parser_FastString.fs_byte_index input (pos + Prims.int_one)) =
              93))
          &&
          ((Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2))))
             = 62)
      then true
      else
        bytes_have_cdata_close input (pos + Prims.int_one) limit
          (fuel - Prims.int_one)
let is_xml_target_name_ci (s : Prims.string) : Prims.bool=
  ((((Parser_FastString.fs_byte_length s) = (Prims.of_int (3))) &&
      ((to_lower_ascii (Parser_FastString.fs_byte_index s Prims.int_zero)) =
         120))
     &&
     ((to_lower_ascii (Parser_FastString.fs_byte_index s Prims.int_one)) =
        109))
    &&
    ((to_lower_ascii (Parser_FastString.fs_byte_index s (Prims.of_int (2))))
       = 108)
let parse_xml_name : Prims.string Parser_Combinators.parser=
  fun input pos ->
    let len = Parser_FastString.fs_byte_length input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected XML name", pos)
    else
      (let ch = Parser_FastString.fs_byte_index input pos in
       if is_name_start_char ch
       then
         let uu___1 = Parser_FastString.fs_cp_at input pos in
         match uu___1 with
         | (cp, _adv) ->
             (if cp = (Prims.of_int (0xB7))
              then
                Parser_Combinators.ParseFail
                  ("a Name cannot start with an Extender", pos)
              else
                (match Parser_Combinators.ptake_while_pos is_name_char input
                         (pos + Prims.int_one)
                 with
                 | Parser_Combinators.ParseOk (rest, pos') ->
                     Parser_Combinators.ParseOk
                       ((FStar_String.concat ""
                           [FStar_String.string_of_char ch; rest]), pos')
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)))
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
let is_dec_digit_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let is_hex_digit_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))) ||
     ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))))
    || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66))))
let rec parse_ref_digits (valid_digit : FStar_Char.char -> Prims.bool)
  (input : Prims.string) (pos : Prims.nat) (acc : FStar_Char.char Prims.list)
  (fuel : Prims.nat) :
  FStar_Char.char Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("character reference too long", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then
       Parser_Combinators.ParseFail ("unterminated character reference", pos)
     else
       (let ch = Parser_FastString.fs_byte_index input pos in
        if ch = 59
        then
          (if (FStar_List_Tot_Base.length acc) = Prims.int_zero
           then
             Parser_Combinators.ParseFail ("empty character reference", pos)
           else
             Parser_Combinators.ParseOk
               ((FStar_List_Tot_Base.rev acc), (pos + Prims.int_one)))
        else
          if valid_digit ch
          then
            parse_ref_digits valid_digit input (pos + Prims.int_one) (ch ::
              acc) (fuel - Prims.int_one)
          else
            Parser_Combinators.ParseFail
              ("invalid character reference digit", pos)))
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
let byte_of_int (b : Prims.int) : Prims.string=
  let b' =
    if b < Prims.int_zero
    then Prims.int_zero
    else if b > (Prims.of_int (255)) then (Prims.of_int (255)) else b in
  FStar_String.string_of_char (FStar_Char.char_of_int b')
let codepoint_to_string (cp : Prims.int) : Prims.string=
  if cp < Prims.int_zero
  then "?"
  else
    if cp < (Prims.of_int (0x80))
    then byte_of_int cp
    else
      if cp < (Prims.of_int (0x800))
      then
        (let b0 = (Prims.of_int (0xC0)) + (cp / (Prims.of_int (64))) in
         let b1 =
           (Prims.of_int (0x80)) +
             (cp - ((cp / (Prims.of_int (64))) * (Prims.of_int (64)))) in
         Prims.strcat (byte_of_int b0) (byte_of_int b1))
      else
        if cp < (Prims.parse_int "0x10000")
        then
          (let b0 = (Prims.of_int (0xE0)) + (cp / (Prims.of_int (4096))) in
           let cp' =
             cp - ((cp / (Prims.of_int (4096))) * (Prims.of_int (4096))) in
           let b1 = (Prims.of_int (0x80)) + (cp' / (Prims.of_int (64))) in
           let b2 =
             (Prims.of_int (0x80)) +
               (cp' - ((cp' / (Prims.of_int (64))) * (Prims.of_int (64)))) in
           Prims.strcat (byte_of_int b0)
             (Prims.strcat (byte_of_int b1) (byte_of_int b2)))
        else
          if cp < (Prims.parse_int "0x110000")
          then
            (let b0 =
               (Prims.of_int (0xF0)) + (cp / (Prims.parse_int "262144")) in
             let r1 =
               cp -
                 ((cp / (Prims.parse_int "262144")) *
                    (Prims.parse_int "262144")) in
             let b1 = (Prims.of_int (0x80)) + (r1 / (Prims.of_int (4096))) in
             let r2 =
               r1 - ((r1 / (Prims.of_int (4096))) * (Prims.of_int (4096))) in
             let b2 = (Prims.of_int (0x80)) + (r2 / (Prims.of_int (64))) in
             let b3 =
               (Prims.of_int (0x80)) +
                 (r2 - ((r2 / (Prims.of_int (64))) * (Prims.of_int (64)))) in
             Prims.strcat (byte_of_int b0)
               (Prims.strcat (byte_of_int b1)
                  (Prims.strcat (byte_of_int b2) (byte_of_int b3))))
          else "?"
let parse_reference (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("unterminated reference", pos)
  else
    (let ch = Parser_FastString.fs_byte_index input pos in
     if ch = 35
     then
       (if (pos + Prims.int_one) >= len
        then
          Parser_Combinators.ParseFail
            ("unterminated character reference", pos)
        else
          (let ch2 =
             Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
           if ch2 = 120
           then
             let fuel = (len - (pos + (Prims.of_int (2)))) + Prims.int_one in
             match parse_ref_digits is_hex_digit_char input
                     (pos + (Prims.of_int (2))) [] fuel
             with
             | Parser_Combinators.ParseOk (digits, pos') ->
                 let cp = chars_to_hex digits in
                 (if is_valid_xml_char cp
                  then
                    Parser_Combinators.ParseOk
                      ((codepoint_to_string cp), pos')
                  else
                    Parser_Combinators.ParseFail
                      ("character reference to a non-Char codepoint", pos'))
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos)
           else
             (let fuel = (len - (pos + Prims.int_one)) + Prims.int_one in
              match parse_ref_digits is_dec_digit_char input
                      (pos + Prims.int_one) [] fuel
              with
              | Parser_Combinators.ParseOk (digits, pos') ->
                  let cp = chars_to_dec digits in
                  if is_valid_xml_char cp
                  then
                    Parser_Combinators.ParseOk
                      ((codepoint_to_string cp), pos')
                  else
                    Parser_Combinators.ParseFail
                      ("character reference to a non-Char codepoint", pos')
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
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated attribute value", pos)
     else
       (let ch = Parser_FastString.fs_byte_index input pos in
        if ch = qch
        then
          Parser_Combinators.ParseOk
            ((FStar_String.concat "" (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if ch = 60
          then
            Parser_Combinators.ParseFail
              ("attribute values exclude '<'", pos)
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
                       (fun c -> ((c <> qch) && (c <> 38)) && (c <> 60))
                       input pos
               with
               | Parser_Combinators.ParseOk (s, pos') ->
                   if (Parser_FastString.fs_byte_length s) > Prims.int_zero
                   then
                     (if
                        Prims.op_Negation
                          (scan_chars_valid input pos pos' (pos' - pos))
                      then
                        Parser_Combinators.ParseFail
                          ("invalid character in attribute value", pos)
                      else
                        parse_attr_value_body qch input pos' (s :: acc)
                          (fuel - Prims.int_one))
                   else
                     parse_attr_value_body qch input (pos + Prims.int_one)
                       ((FStar_String.string_of_char ch) :: acc)
                       (fuel - Prims.int_one)
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos))))
let parse_attr_value (input : Prims.string) (pos : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected attribute value", pos)
  else
    (let qch = Parser_FastString.fs_byte_index input pos in
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
let rec mem_attr_name (name : Prims.string)
  (attrs : xml_attribute Prims.list) : Prims.bool=
  match attrs with
  | [] -> false
  | a::rest -> if a.attr_name = name then true else mem_attr_name name rest
let rec parse_attributes (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) :
  xml_attribute Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ([], pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseOk ([], pos)
     else
       (match Parser_Combinators.ptake_while1_pos is_xml_space input pos with
        | Parser_Combinators.ParseOk (uu___2, pos1) ->
            if pos1 < len
            then
              let ch = Parser_FastString.fs_byte_index input pos1 in
              (if is_name_start_char ch
               then
                 match parse_xml_attribute input pos1 with
                 | Parser_Combinators.ParseOk (attr, pos2) ->
                     (match parse_attributes input pos2
                              (fuel - Prims.int_one)
                      with
                      | Parser_Combinators.ParseOk (attrs, pos3) ->
                          if mem_attr_name attr.attr_name attrs
                          then
                            Parser_Combinators.ParseFail
                              ("duplicate attribute name", pos2)
                          else
                            Parser_Combinators.ParseOk
                              ((attr :: attrs), pos3)
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
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then
       Parser_Combinators.ParseOk
         ((FStar_String.concat "" (FStar_List_Tot_Base.rev acc)), pos)
     else
       (let ch = Parser_FastString.fs_byte_index input pos in
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
                 if (Parser_FastString.fs_byte_length s) > Prims.int_zero
                 then
                   (if
                      Prims.op_Negation
                        (scan_chars_valid input pos pos' (pos' - pos))
                    then
                      Parser_Combinators.ParseFail
                        ("invalid character in text content", pos)
                    else
                      if bytes_have_cdata_close input pos pos' (pos' - pos)
                      then
                        Parser_Combinators.ParseFail
                          ("text may not contain a literal ']]>' sequence",
                            pos)
                      else
                        parse_text_content input pos' (s :: acc)
                          (fuel - Prims.int_one))
                 else
                   parse_text_content input (pos + Prims.int_one)
                     ((FStar_String.string_of_char ch) :: acc)
                     (fuel - Prims.int_one)
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos))))
let parse_xml_text (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len - pos) + Prims.int_one in
  if fuel >= Prims.int_zero
  then
    match parse_text_content input pos [] fuel with
    | Parser_Combinators.ParseOk (text, pos') ->
        (if (Parser_FastString.fs_byte_length text) > Prims.int_zero
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
    (let len = Parser_FastString.fs_byte_length input in
     if (pos + (Prims.of_int (2))) < len
     then
       let c0 = Parser_FastString.fs_byte_index input pos in
       let c1 = Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
       let c2 =
         Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2))) in
       (if ((c0 = 45) && (c1 = 45)) && (c2 = 62)
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + (Prims.of_int (3))))
        else
          if is_utf8_continuation_byte c0
          then
            parse_comment_body input (pos + Prims.int_one) (c0 :: acc)
              (fuel - Prims.int_one)
          else
            (let uu___3 = Parser_FastString.fs_cp_at input pos in
             match uu___3 with
             | (cp, adv) ->
                 if Prims.op_Negation (is_valid_decoded_char cp adv)
                 then
                   Parser_Combinators.ParseFail
                     ("invalid character in comment", pos)
                 else
                   parse_comment_body input (pos + Prims.int_one) (c0 :: acc)
                     (fuel - Prims.int_one)))
     else
       if pos < len
       then
         (let c0 = Parser_FastString.fs_byte_index input pos in
          if is_utf8_continuation_byte c0
          then
            parse_comment_body input (pos + Prims.int_one) (c0 :: acc)
              (fuel - Prims.int_one)
          else
            (let uu___3 = Parser_FastString.fs_cp_at input pos in
             match uu___3 with
             | (cp, adv) ->
                 if Prims.op_Negation (is_valid_decoded_char cp adv)
                 then
                   Parser_Combinators.ParseFail
                     ("invalid character in comment", pos)
                 else
                   parse_comment_body input (pos + Prims.int_one) (c0 :: acc)
                     (fuel - Prims.int_one)))
       else Parser_Combinators.ParseFail ("unterminated comment", pos))
let parse_xml_comment (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<!--" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      let len = Parser_FastString.fs_byte_length input in
      let fuel = (len - pos1) + Prims.int_one in
      (match parse_comment_body input pos1 [] fuel with
       | Parser_Combinators.ParseOk (text, pos2) ->
           if
             (bytes_have_double_dash text Prims.int_zero
                (Parser_FastString.fs_byte_length text)
                (Parser_FastString.fs_byte_length text))
               || (ends_with_dash text)
           then
             Parser_Combinators.ParseFail
               ("comment must not contain '--' or end in '-'", pos1)
           else Parser_Combinators.ParseOk ((XComment text), pos2)
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
    (let len = Parser_FastString.fs_byte_length input in
     if (pos + (Prims.of_int (2))) < len
     then
       let c0 = Parser_FastString.fs_byte_index input pos in
       let c1 = Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
       let c2 =
         Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2))) in
       (if ((c0 = 93) && (c1 = 93)) && (c2 = 62)
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + (Prims.of_int (3))))
        else
          if is_utf8_continuation_byte c0
          then
            parse_cdata_body input (pos + Prims.int_one) (c0 :: acc)
              (fuel - Prims.int_one)
          else
            (let uu___3 = Parser_FastString.fs_cp_at input pos in
             match uu___3 with
             | (cp, adv) ->
                 if Prims.op_Negation (is_valid_decoded_char cp adv)
                 then
                   Parser_Combinators.ParseFail
                     ("invalid character in CDATA section", pos)
                 else
                   parse_cdata_body input (pos + Prims.int_one) (c0 :: acc)
                     (fuel - Prims.int_one)))
     else
       if pos < len
       then
         (let c0 = Parser_FastString.fs_byte_index input pos in
          if is_utf8_continuation_byte c0
          then
            parse_cdata_body input (pos + Prims.int_one) (c0 :: acc)
              (fuel - Prims.int_one)
          else
            (let uu___3 = Parser_FastString.fs_cp_at input pos in
             match uu___3 with
             | (cp, adv) ->
                 if Prims.op_Negation (is_valid_decoded_char cp adv)
                 then
                   Parser_Combinators.ParseFail
                     ("invalid character in CDATA section", pos)
                 else
                   parse_cdata_body input (pos + Prims.int_one) (c0 :: acc)
                     (fuel - Prims.int_one)))
       else Parser_Combinators.ParseFail ("unterminated CDATA section", pos))
let parse_xml_cdata (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<![CDATA[" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      let len = Parser_FastString.fs_byte_length input in
      let fuel = (len - pos1) + Prims.int_one in
      (match parse_cdata_body input pos1 [] fuel with
       | Parser_Combinators.ParseOk (text, pos2) ->
           Parser_Combinators.ParseOk ((XCDATA text), pos2)
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec collect_pi_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail ("unterminated processing instruction", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if (pos + Prims.int_one) < len
     then
       let c0 = Parser_FastString.fs_byte_index input pos in
       let c1 = Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
       (if (c0 = 63) && (c1 = 62)
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + (Prims.of_int (2))))
        else
          if is_utf8_continuation_byte c0
          then
            collect_pi_body input (pos + Prims.int_one) (c0 :: acc)
              (fuel - Prims.int_one)
          else
            (let uu___3 = Parser_FastString.fs_cp_at input pos in
             match uu___3 with
             | (cp, adv) ->
                 if Prims.op_Negation (is_valid_decoded_char cp adv)
                 then
                   Parser_Combinators.ParseFail
                     ("invalid character in processing instruction", pos)
                 else
                   collect_pi_body input (pos + Prims.int_one) (c0 :: acc)
                     (fuel - Prims.int_one)))
     else
       Parser_Combinators.ParseFail
         ("unterminated processing instruction", pos))
let parse_xml_pi (input : Prims.string) (pos : Prims.nat) :
  xml_node Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<?" input pos with
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      (match parse_xml_name input pos1 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (target, pos2) ->
           if is_xml_target_name_ci target
           then
             Parser_Combinators.ParseFail
               ("PI target name 'xml' (any case) is reserved", pos1)
           else
             (let len = Parser_FastString.fs_byte_length input in
              if
                (((pos2 + Prims.int_one) < len) &&
                   ((Parser_FastString.fs_byte_index input pos2) = 63))
                  &&
                  ((Parser_FastString.fs_byte_index input
                      (pos2 + Prims.int_one))
                     = 62)
              then
                Parser_Combinators.ParseOk
                  ((XPI (target, "")), (pos2 + (Prims.of_int (2))))
              else
                (match Parser_Combinators.ptake_while1_pos is_xml_space input
                         pos2
                 with
                 | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                     Parser_Combinators.ParseFail
                       ("S after PITarget is required", pos2)
                 | Parser_Combinators.ParseOk (uu___3, pos_data) ->
                     let fuel = (len - pos_data) + Prims.int_one in
                     (match collect_pi_body input pos_data [] fuel with
                      | Parser_Combinators.ParseOk (data, pos3) ->
                          Parser_Combinators.ParseOk
                            ((XPI (target, data)), pos3)
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)))))
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec check_bytes_from (pred : FStar_Char.char -> Prims.bool)
  (s : Prims.string) (pos : Prims.nat) (limit : Prims.nat) (fuel : Prims.nat)
  : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    if pos >= limit
    then true
    else
      if pred (Parser_FastString.fs_byte_index s pos)
      then
        check_bytes_from pred s (pos + Prims.int_one) limit
          (fuel - Prims.int_one)
      else false
let is_version_num (s : Prims.string) : Prims.bool=
  let len = Parser_FastString.fs_byte_length s in
  (((len >= (Prims.of_int (3))) &&
      ((Parser_FastString.fs_byte_index s Prims.int_zero) = 49))
     && ((Parser_FastString.fs_byte_index s Prims.int_one) = 46))
    && (check_bytes_from is_dec_digit_char s (Prims.of_int (2)) len len)
let is_enc_name_first_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
    ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A))))
let is_enc_name_rest_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
        ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
       ||
       ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
      || (code = (Prims.of_int (0x2E))))
     || (code = (Prims.of_int (0x5F))))
    || (code = (Prims.of_int (0x2D)))
let is_enc_name (s : Prims.string) : Prims.bool=
  let len = Parser_FastString.fs_byte_length s in
  ((len >= Prims.int_one) &&
     (is_enc_name_first_char
        (Parser_FastString.fs_byte_index s Prims.int_zero)))
    && (check_bytes_from is_enc_name_rest_char s Prims.int_one len len)
let is_sd_value (s : Prims.string) : Prims.bool= (s = "yes") || (s = "no")
let try_pseudo_attr (name : Prims.string) (input : Prims.string)
  (pos : Prims.nat) :
  (Prims.string * Prims.nat) FStar_Pervasives_Native.option=
  match Parser_Combinators.ptake_while1_pos is_xml_space input pos with
  | Parser_Combinators.ParseFail (uu___, uu___1) ->
      FStar_Pervasives_Native.None
  | Parser_Combinators.ParseOk (uu___, pos1) ->
      (match Parser_Combinators.pstring name input pos1 with
       | Parser_Combinators.ParseFail (uu___1, uu___2) ->
           FStar_Pervasives_Native.None
       | Parser_Combinators.ParseOk (uu___1, pos2) ->
           (match skip_xml_space input pos2 with
            | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                FStar_Pervasives_Native.None
            | Parser_Combinators.ParseOk ((), pos3) ->
                (match Parser_Combinators.pchar 61 input pos3 with
                 | Parser_Combinators.ParseFail (uu___2, uu___3) ->
                     FStar_Pervasives_Native.None
                 | Parser_Combinators.ParseOk (uu___2, pos4) ->
                     (match skip_xml_space input pos4 with
                      | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                          FStar_Pervasives_Native.None
                      | Parser_Combinators.ParseOk ((), pos5) ->
                          (match parse_attr_value input pos5 with
                           | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                               FStar_Pervasives_Native.None
                           | Parser_Combinators.ParseOk (v, pos6) ->
                               FStar_Pervasives_Native.Some (v, pos6))))))
let finish_xml_decl (input : Prims.string) (pos : Prims.nat)
  (attrs : xml_attribute Prims.list) :
  xml_attribute Prims.list Parser_Combinators.parse_result=
  match skip_xml_space input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk ((), pos1) ->
      (match Parser_Combinators.pstring "?>" input pos1 with
       | Parser_Combinators.ParseOk (uu___, pos2) ->
           Parser_Combinators.ParseOk (attrs, pos2)
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
let parse_xml_declaration (input : Prims.string) (pos : Prims.nat) :
  xml_attribute Prims.list Parser_Combinators.parse_result=
  match Parser_Combinators.pstring "<?xml" input pos with
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
  | Parser_Combinators.ParseOk (uu___, pos0) ->
      (match Parser_Combinators.ptake_while1_pos is_xml_space input pos0 with
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos)
       | Parser_Combinators.ParseOk (uu___1, pos1) ->
           (match Parser_Combinators.pstring "version" input pos1 with
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos)
            | Parser_Combinators.ParseOk (uu___2, pos2) ->
                (match skip_xml_space input pos2 with
                 | Parser_Combinators.ParseFail (msg, fpos) ->
                     Parser_Combinators.ParseFail (msg, fpos)
                 | Parser_Combinators.ParseOk ((), pos3) ->
                     (match Parser_Combinators.pchar 61 input pos3 with
                      | Parser_Combinators.ParseFail (msg, fpos) ->
                          Parser_Combinators.ParseFail (msg, fpos)
                      | Parser_Combinators.ParseOk (uu___3, pos4) ->
                          (match skip_xml_space input pos4 with
                           | Parser_Combinators.ParseFail (msg, fpos) ->
                               Parser_Combinators.ParseFail (msg, fpos)
                           | Parser_Combinators.ParseOk ((), pos5) ->
                               (match parse_attr_value input pos5 with
                                | Parser_Combinators.ParseFail (msg, fpos) ->
                                    Parser_Combinators.ParseFail (msg, fpos)
                                | Parser_Combinators.ParseOk (vernum, pos6)
                                    ->
                                    if
                                      Prims.op_Negation
                                        (is_version_num vernum)
                                    then
                                      Parser_Combinators.ParseFail
                                        ("illegal VersionNum", pos5)
                                    else
                                      (let version_attr =
                                         {
                                           attr_name = "version";
                                           attr_value = vernum
                                         } in
                                       match try_pseudo_attr "encoding" input
                                               pos6
                                       with
                                       | FStar_Pervasives_Native.Some
                                           (encval, pos7) ->
                                           if
                                             Prims.op_Negation
                                               (is_enc_name encval)
                                           then
                                             Parser_Combinators.ParseFail
                                               ("illegal EncName", pos7)
                                           else
                                             (let enc_attr =
                                                {
                                                  attr_name = "encoding";
                                                  attr_value = encval
                                                } in
                                              match try_pseudo_attr
                                                      "standalone" input pos7
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  (sdval, pos8) ->
                                                  if
                                                    Prims.op_Negation
                                                      (is_sd_value sdval)
                                                  then
                                                    Parser_Combinators.ParseFail
                                                      ("illegal SDDecl value",
                                                        pos8)
                                                  else
                                                    (let sd_attr =
                                                       {
                                                         attr_name =
                                                           "standalone";
                                                         attr_value = sdval
                                                       } in
                                                     finish_xml_decl input
                                                       pos8
                                                       [version_attr;
                                                       enc_attr;
                                                       sd_attr])
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  finish_xml_decl input pos7
                                                    [version_attr; enc_attr])
                                       | FStar_Pervasives_Native.None ->
                                           (match try_pseudo_attr
                                                    "standalone" input pos6
                                            with
                                            | FStar_Pervasives_Native.Some
                                                (sdval, pos7) ->
                                                if
                                                  Prims.op_Negation
                                                    (is_sd_value sdval)
                                                then
                                                  Parser_Combinators.ParseFail
                                                    ("illegal SDDecl value",
                                                      pos7)
                                                else
                                                  (let sd_attr =
                                                     {
                                                       attr_name =
                                                         "standalone";
                                                       attr_value = sdval
                                                     } in
                                                   finish_xml_decl input pos7
                                                     [version_attr; sd_attr])
                                            | FStar_Pervasives_Native.None ->
                                                finish_xml_decl input pos6
                                                  [version_attr]))))))))
let rec parse_children (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) (acc : xml_node Prims.list) :
  xml_node Prims.list Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseOk ((FStar_List_Tot_Base.rev acc), pos)
     else
       (let ch = Parser_FastString.fs_byte_index input pos in
        if ch = 60
        then
          (if (pos + Prims.int_one) < len
           then
             let ch2 =
               Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
             (if ch2 = 47
              then
                Parser_Combinators.ParseOk
                  ((FStar_List_Tot_Base.rev acc), pos)
              else
                if ch2 = 33
                then
                  (match parse_xml_comment input pos with
                   | Parser_Combinators.ParseOk (comment, pos') ->
                       parse_children input pos' (fuel - Prims.int_one)
                         (comment :: acc)
                   | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                       (match parse_xml_cdata input pos with
                        | Parser_Combinators.ParseOk (cdata, pos') ->
                            parse_children input pos' (fuel - Prims.int_one)
                              (cdata :: acc)
                        | Parser_Combinators.ParseFail (msg, fpos) ->
                            Parser_Combinators.ParseFail (msg, fpos)))
                else
                  if ch2 = 63
                  then
                    (match parse_xml_pi input pos with
                     | Parser_Combinators.ParseOk (pi_node, pos') ->
                         parse_children input pos' (fuel - Prims.int_one)
                           (pi_node :: acc)
                     | Parser_Combinators.ParseFail (msg, fpos) ->
                         Parser_Combinators.ParseFail (msg, fpos))
                  else
                    (match parse_xml_element input pos (fuel - Prims.int_one)
                     with
                     | Parser_Combinators.ParseOk (elem, pos') ->
                         parse_children input pos' (fuel - Prims.int_one)
                           (elem :: acc)
                     | Parser_Combinators.ParseFail (msg, fpos) ->
                         Parser_Combinators.ParseFail (msg, fpos)))
           else
             Parser_Combinators.ParseFail ("unexpected end after '<'", pos))
        else
          (match parse_xml_text input pos with
           | Parser_Combinators.ParseOk (text_node, pos') ->
               if pos' = pos
               then
                 Parser_Combinators.ParseOk
                   ((FStar_List_Tot_Base.rev acc), pos)
               else
                 parse_children input pos' (fuel - Prims.int_one) (text_node
                   :: acc)
           | Parser_Combinators.ParseFail (uu___3, uu___4) ->
               Parser_Combinators.ParseOk
                 ((FStar_List_Tot_Base.rev acc), pos))))
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
              let len = Parser_FastString.fs_byte_length input in
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
                                           (fuel - Prims.int_one) []
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
let rec skip_epilog_misc (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : unit Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseOk ((), pos)
  else
    (match skip_xml_space input pos with
     | Parser_Combinators.ParseOk ((), pos1) ->
         (match parse_xml_comment input pos1 with
          | Parser_Combinators.ParseOk (uu___1, pos2) ->
              skip_epilog_misc input pos2 (fuel - Prims.int_one)
          | Parser_Combinators.ParseFail (uu___1, uu___2) ->
              (match parse_xml_pi input pos1 with
               | Parser_Combinators.ParseOk (uu___3, pos2) ->
                   skip_epilog_misc input pos2 (fuel - Prims.int_one)
               | Parser_Combinators.ParseFail (uu___3, uu___4) ->
                   Parser_Combinators.ParseOk ((), pos1)))
     | Parser_Combinators.ParseFail (msg, fpos) ->
         Parser_Combinators.ParseFail (msg, fpos))
let parse_xml_document (input : Prims.string) :
  xml_node FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = len + Prims.int_one in
  let pos1 =
    match parse_xml_declaration input Prims.int_zero with
    | Parser_Combinators.ParseOk (_attrs, pos') -> pos'
    | Parser_Combinators.ParseFail (uu___, uu___1) -> Prims.int_zero in
  match skip_misc input pos1 fuel with
  | Parser_Combinators.ParseOk ((), pos2) ->
      (match parse_xml_element input pos2 fuel with
       | Parser_Combinators.ParseOk (root, pos3) ->
           (match skip_epilog_misc input pos3 fuel with
            | Parser_Combinators.ParseOk ((), pos4) ->
                if pos4 >= (Parser_FastString.fs_byte_length input)
                then FStar_Pervasives_Native.Some root
                else FStar_Pervasives_Native.None
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
  | XPI (uu___, uu___1) -> ""
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
