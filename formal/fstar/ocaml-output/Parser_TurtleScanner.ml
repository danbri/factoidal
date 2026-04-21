open Prims
type scan_mode =
  | SM_Normal 
  | SM_Comment 
  | SM_IriRef 
  | SM_String of FStar_Char.char * Prims.bool * Prims.bool * Prims.nat 
let uu___is_SM_Normal (projectee : scan_mode) : Prims.bool=
  match projectee with | SM_Normal -> true | uu___ -> false
let uu___is_SM_Comment (projectee : scan_mode) : Prims.bool=
  match projectee with | SM_Comment -> true | uu___ -> false
let uu___is_SM_IriRef (projectee : scan_mode) : Prims.bool=
  match projectee with | SM_IriRef -> true | uu___ -> false
let uu___is_SM_String (projectee : scan_mode) : Prims.bool=
  match projectee with | SM_String (_0, _1, _2, _3) -> true | uu___ -> false
let __proj__SM_String__item___0 (projectee : scan_mode) : FStar_Char.char=
  match projectee with | SM_String (_0, _1, _2, _3) -> _0
let __proj__SM_String__item___1 (projectee : scan_mode) : Prims.bool=
  match projectee with | SM_String (_0, _1, _2, _3) -> _1
let __proj__SM_String__item___2 (projectee : scan_mode) : Prims.bool=
  match projectee with | SM_String (_0, _1, _2, _3) -> _2
let __proj__SM_String__item___3 (projectee : scan_mode) : Prims.nat=
  match projectee with | SM_String (_0, _1, _2, _3) -> _3
type scanner_state = {
  ss_mode: scan_mode ;
  ss_carry: Prims.string }
let __proj__Mkscanner_state__item__ss_mode (projectee : scanner_state) :
  scan_mode= match projectee with | { ss_mode; ss_carry;_} -> ss_mode
let __proj__Mkscanner_state__item__ss_carry (projectee : scanner_state) :
  Prims.string= match projectee with | { ss_mode; ss_carry;_} -> ss_carry
let empty_scanner_state : scanner_state=
  { ss_mode = SM_Normal; ss_carry = "" }
type span = {
  sp_start: Prims.nat ;
  sp_end: Prims.nat }
let __proj__Mkspan__item__sp_start (projectee : span) : Prims.nat=
  match projectee with | { sp_start; sp_end;_} -> sp_start
let __proj__Mkspan__item__sp_end (projectee : span) : Prims.nat=
  match projectee with | { sp_start; sp_end;_} -> sp_end
type prefixed_name_span = {
  pns_prefix: span ;
  pns_local: span }
let __proj__Mkprefixed_name_span__item__pns_prefix
  (projectee : prefixed_name_span) : span=
  match projectee with | { pns_prefix; pns_local;_} -> pns_prefix
let __proj__Mkprefixed_name_span__item__pns_local
  (projectee : prefixed_name_span) : span=
  match projectee with | { pns_prefix; pns_local;_} -> pns_local
type iri_ref_span = {
  irs_span: span ;
  irs_has_colon: Prims.bool }
let __proj__Mkiri_ref_span__item__irs_span (projectee : iri_ref_span) : 
  span= match projectee with | { irs_span; irs_has_colon;_} -> irs_span
let __proj__Mkiri_ref_span__item__irs_has_colon (projectee : iri_ref_span) :
  Prims.bool=
  match projectee with | { irs_span; irs_has_colon;_} -> irs_has_colon
type short_string_span = {
  sss_quote: FStar_Char.char ;
  sss_content: span }
let __proj__Mkshort_string_span__item__sss_quote
  (projectee : short_string_span) : FStar_Char.char=
  match projectee with | { sss_quote; sss_content;_} -> sss_quote
let __proj__Mkshort_string_span__item__sss_content
  (projectee : short_string_span) : span=
  match projectee with | { sss_quote; sss_content;_} -> sss_content
type token_kind =
  | TK_Dot 
  | TK_Semicolon 
  | TK_Comma 
  | TK_LBracket 
  | TK_RBracket 
  | TK_LParen 
  | TK_RParen 
  | TK_IriRef 
  | TK_PrefixedName 
let uu___is_TK_Dot (projectee : token_kind) : Prims.bool=
  match projectee with | TK_Dot -> true | uu___ -> false
let uu___is_TK_Semicolon (projectee : token_kind) : Prims.bool=
  match projectee with | TK_Semicolon -> true | uu___ -> false
let uu___is_TK_Comma (projectee : token_kind) : Prims.bool=
  match projectee with | TK_Comma -> true | uu___ -> false
let uu___is_TK_LBracket (projectee : token_kind) : Prims.bool=
  match projectee with | TK_LBracket -> true | uu___ -> false
let uu___is_TK_RBracket (projectee : token_kind) : Prims.bool=
  match projectee with | TK_RBracket -> true | uu___ -> false
let uu___is_TK_LParen (projectee : token_kind) : Prims.bool=
  match projectee with | TK_LParen -> true | uu___ -> false
let uu___is_TK_RParen (projectee : token_kind) : Prims.bool=
  match projectee with | TK_RParen -> true | uu___ -> false
let uu___is_TK_IriRef (projectee : token_kind) : Prims.bool=
  match projectee with | TK_IriRef -> true | uu___ -> false
let uu___is_TK_PrefixedName (projectee : token_kind) : Prims.bool=
  match projectee with | TK_PrefixedName -> true | uu___ -> false
type scanned_token = {
  st_kind: token_kind ;
  st_span: span }
let __proj__Mkscanned_token__item__st_kind (projectee : scanned_token) :
  token_kind= match projectee with | { st_kind; st_span;_} -> st_kind
let __proj__Mkscanned_token__item__st_span (projectee : scanned_token) :
  span= match projectee with | { st_kind; st_span;_} -> st_span
let append_carry (st : scanner_state) (chunk : Prims.string) : Prims.string=
  if (FStar_String.strlen st.ss_carry) = Prims.int_zero
  then chunk
  else FStar_String.concat "" [st.ss_carry; chunk]
let clear_carry (st : scanner_state) : scanner_state=
  { ss_mode = (st.ss_mode); ss_carry = "" }
let is_ascii_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let is_ascii_name_start (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
      ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
     || ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
    || (code = (Prims.of_int (0x5F)))
let is_ascii_name_body (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A))))
           ||
           ((code >= (Prims.of_int (0x61))) &&
              (code <= (Prims.of_int (0x7A)))))
          ||
          ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
         || (code = (Prims.of_int (0x5F))))
        || (code = (Prims.of_int (0x2D))))
       || (code = (Prims.of_int (0x2E))))
      || (code = (Prims.of_int (0x3A))))
     || (code = (Prims.of_int (0x25))))
    || (code = (Prims.of_int (0x5C)))
let is_hex_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))) ||
     ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x46)))))
    || ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x66))))
let hex_digit_value (c : FStar_Char.char) : Prims.nat=
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
let decode_hex4 (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let d0 = hex_digit_value (Parser_FastString.fs_byte_index input pos) in
  let d1 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + Prims.int_one)) in
  let d2 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2)))) in
  let d3 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (3)))) in
  (((d0 * (Prims.of_int (4096))) + (d1 * (Prims.of_int (256)))) +
     (d2 * (Prims.of_int (16))))
    + d3
let decode_hex8 (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let d0 = hex_digit_value (Parser_FastString.fs_byte_index input pos) in
  let d1 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + Prims.int_one)) in
  let d2 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (2)))) in
  let d3 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (3)))) in
  let d4 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (4)))) in
  let d5 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (5)))) in
  let d6 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (6)))) in
  let d7 =
    hex_digit_value
      (Parser_FastString.fs_byte_index input (pos + (Prims.of_int (7)))) in
  (((((((d0 * (Prims.parse_int "268435456")) +
          (d1 * (Prims.parse_int "16777216")))
         + (d2 * (Prims.parse_int "1048576")))
        + (d3 * (Prims.parse_int "65536")))
       + (d4 * (Prims.of_int (4096))))
      + (d5 * (Prims.of_int (256))))
     + (d6 * (Prims.of_int (16))))
    + d7
let is_iri_forbidden_codepoint (code : Prims.nat) : Prims.bool=
  (((((((((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x3C))))
           || (code = (Prims.of_int (0x3E))))
          || (code = (Prims.of_int (0x22))))
         || (code = (Prims.of_int (0x7B))))
        || (code = (Prims.of_int (0x7D))))
       || (code = (Prims.of_int (0x7C))))
      || (code = (Prims.of_int (0x5C))))
     || (code = (Prims.of_int (0x5E))))
    || (code = (Prims.of_int (0x60)))
let is_turtle_token_delim (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((((((((((((is_ascii_ws c) || (code = (Prims.of_int (0x23)))) ||
              (code = (Prims.of_int (0x2E))))
             || (code = (Prims.of_int (0x3B))))
            || (code = (Prims.of_int (0x2C))))
           || (code = (Prims.of_int (0x5B))))
          || (code = (Prims.of_int (0x5D))))
         || (code = (Prims.of_int (0x28))))
        || (code = (Prims.of_int (0x29))))
       || (code = (Prims.of_int (0x3C))))
      || (code = (Prims.of_int (0x3E))))
     || (code = (Prims.of_int (0x22))))
    || (code = (Prims.of_int (0x27)))
let rec skip_comment_to_eol (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then pos
     else
       (let c = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char c in
        if (code = (Prims.of_int (0x0A))) || (code = (Prims.of_int (0x0D)))
        then pos
        else
          skip_comment_to_eol input (pos + Prims.int_one)
            (fuel - Prims.int_one)))
let rec scan_ws_comments (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then pos
     else
       (let c = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char c in
        if is_ascii_ws c
        then
          scan_ws_comments input (pos + Prims.int_one) (fuel - Prims.int_one)
        else
          if code = (Prims.of_int (0x23))
          then
            (let pos' =
               skip_comment_to_eol input (pos + Prims.int_one) (len - pos) in
             scan_ws_comments input pos' (fuel - Prims.int_one))
          else pos))
let skip_ws_comments (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = Parser_FastString.fs_byte_length input in
  let fuel = (len - pos) + Prims.int_one in
  if fuel >= Prims.int_zero then scan_ws_comments input pos fuel else pos
let rec scan_name_body_end (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then pos
     else
       (let c = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char c in
        if (code = (Prims.of_int (0x5C))) && ((pos + Prims.int_one) < len)
        then
          scan_name_body_end input (pos + (Prims.of_int (2)))
            (fuel - Prims.int_one)
        else
          if code < (Prims.of_int (0x80))
          then
            (if is_ascii_name_body c
             then
               scan_name_body_end input (pos + Prims.int_one)
                 (fuel - Prims.int_one)
             else pos)
          else
            if is_turtle_token_delim c
            then pos
            else
              scan_name_body_end input (pos + Prims.int_one)
                (fuel - Prims.int_one)))
let scan_prefixed_name_span (input : Prims.string) (pos : Prims.nat) :
  prefixed_name_span Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected prefixed name", pos)
  else
    (let c0 = Parser_FastString.fs_byte_index input pos in
     if (FStar_Char.int_of_char c0) = (Prims.of_int (0x3A))
     then
       let body_end =
         scan_name_body_end input (pos + Prims.int_one)
           ((len - pos) + Prims.int_one) in
       let prefix = { sp_start = pos; sp_end = pos } in
       let local = { sp_start = (pos + Prims.int_one); sp_end = body_end } in
       Parser_Combinators.ParseOk
         ({ pns_prefix = prefix; pns_local = local }, body_end)
     else
       if Prims.op_Negation (is_ascii_name_start c0)
       then Parser_Combinators.ParseFail ("expected prefixed name", pos)
       else
         (let body_end =
            scan_name_body_end input pos ((len - pos) + Prims.int_one) in
          let rec find_colon p fuel =
            if fuel = Prims.int_zero
            then FStar_Pervasives_Native.None
            else
              if p >= body_end
              then FStar_Pervasives_Native.None
              else
                if p >= len
                then FStar_Pervasives_Native.None
                else
                  if
                    (FStar_Char.int_of_char
                       (Parser_FastString.fs_byte_index input p))
                      = (Prims.of_int (0x3A))
                  then FStar_Pervasives_Native.Some p
                  else find_colon (p + Prims.int_one) (fuel - Prims.int_one) in
          let fuel =
            if body_end >= pos
            then (body_end - pos) + Prims.int_one
            else Prims.int_zero in
          match find_colon pos fuel with
          | FStar_Pervasives_Native.None ->
              Parser_Combinators.ParseFail
                ("expected ':' in prefixed name", body_end)
          | FStar_Pervasives_Native.Some colon_pos ->
              let prefix = { sp_start = pos; sp_end = colon_pos } in
              let local =
                { sp_start = (colon_pos + Prims.int_one); sp_end = body_end } in
              Parser_Combinators.ParseOk
                ({ pns_prefix = prefix; pns_local = local }, body_end)))
let rec scan_iri_ref_end (input : Prims.string) (pos : Prims.nat)
  (has_colon : Prims.bool) (fuel : Prims.nat) :
  (Prims.nat * Prims.bool) Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated IRI reference", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated IRI reference", pos)
     else
       (let c = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x3E))
        then
          Parser_Combinators.ParseOk
            ((pos, has_colon), (pos + Prims.int_one))
        else
          if code = (Prims.of_int (0x5C))
          then
            (if (pos + Prims.int_one) >= len
             then
               Parser_Combinators.ParseFail
                 ("backslash at end of IRI reference", pos)
             else
               (let next =
                  Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
                let ncode = FStar_Char.int_of_char next in
                if ncode = (Prims.of_int (0x75))
                then
                  (if (pos + (Prims.of_int (6))) > len
                   then
                     Parser_Combinators.ParseFail
                       ("incomplete \\u escape in IRI reference", pos)
                   else
                     if
                       (((is_hex_digit
                            (Parser_FastString.fs_byte_index input
                               (pos + (Prims.of_int (2)))))
                           &&
                           (is_hex_digit
                              (Parser_FastString.fs_byte_index input
                                 (pos + (Prims.of_int (3))))))
                          &&
                          (is_hex_digit
                             (Parser_FastString.fs_byte_index input
                                (pos + (Prims.of_int (4))))))
                         &&
                         (is_hex_digit
                            (Parser_FastString.fs_byte_index input
                               (pos + (Prims.of_int (5)))))
                     then
                       (let cp = decode_hex4 input (pos + (Prims.of_int (2))) in
                        if
                          (cp >= (Prims.of_int (0xD800))) &&
                            (cp <= (Prims.of_int (0xDFFF)))
                        then
                          Parser_Combinators.ParseFail
                            ("surrogate codepoint in \\u escape", pos)
                        else
                          scan_iri_ref_end input (pos + (Prims.of_int (6)))
                            has_colon (fuel - Prims.int_one))
                     else
                       Parser_Combinators.ParseFail
                         ("invalid hex digit in \\u escape", pos))
                else
                  if ncode = (Prims.of_int (0x55))
                  then
                    (if (pos + (Prims.of_int (10))) > len
                     then
                       Parser_Combinators.ParseFail
                         ("incomplete \\U escape in IRI reference", pos)
                     else
                       if
                         (((((((is_hex_digit
                                  (Parser_FastString.fs_byte_index input
                                     (pos + (Prims.of_int (2)))))
                                 &&
                                 (is_hex_digit
                                    (Parser_FastString.fs_byte_index input
                                       (pos + (Prims.of_int (3))))))
                                &&
                                (is_hex_digit
                                   (Parser_FastString.fs_byte_index input
                                      (pos + (Prims.of_int (4))))))
                               &&
                               (is_hex_digit
                                  (Parser_FastString.fs_byte_index input
                                     (pos + (Prims.of_int (5))))))
                              &&
                              (is_hex_digit
                                 (Parser_FastString.fs_byte_index input
                                    (pos + (Prims.of_int (6))))))
                             &&
                             (is_hex_digit
                                (Parser_FastString.fs_byte_index input
                                   (pos + (Prims.of_int (7))))))
                            &&
                            (is_hex_digit
                               (Parser_FastString.fs_byte_index input
                                  (pos + (Prims.of_int (8))))))
                           &&
                           (is_hex_digit
                              (Parser_FastString.fs_byte_index input
                                 (pos + (Prims.of_int (9)))))
                       then
                         (let cp =
                            decode_hex8 input (pos + (Prims.of_int (2))) in
                          if
                            ((cp >= (Prims.of_int (0xD800))) &&
                               (cp <= (Prims.of_int (0xDFFF))))
                              || (cp > (Prims.parse_int "0x10FFFF"))
                          then
                            Parser_Combinators.ParseFail
                              ("invalid codepoint in \\U escape", pos)
                          else
                            scan_iri_ref_end input
                              (pos + (Prims.of_int (10))) has_colon
                              (fuel - Prims.int_one))
                       else
                         Parser_Combinators.ParseFail
                           ("invalid hex digit in \\U escape", pos))
                  else
                    Parser_Combinators.ParseFail
                      ("invalid escape in IRI reference", pos)))
          else
            if
              (code = (Prims.of_int (0x0A))) ||
                (code = (Prims.of_int (0x0D)))
            then
              Parser_Combinators.ParseFail ("newline in IRI reference", pos)
            else
              if
                (code <= (Prims.of_int (0x20))) ||
                  (is_iri_forbidden_codepoint code)
              then
                Parser_Combinators.ParseFail
                  ("invalid character in IRI reference", pos)
              else
                scan_iri_ref_end input (pos + Prims.int_one)
                  (has_colon || (code = (Prims.of_int (0x3A))))
                  (fuel - Prims.int_one)))
let scan_iri_ref_span (input : Prims.string) (pos : Prims.nat) :
  iri_ref_span Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected IRI reference", pos)
  else
    if
      (FStar_Char.int_of_char (Parser_FastString.fs_byte_index input pos)) <>
        (Prims.of_int (0x3C))
    then Parser_Combinators.ParseFail ("expected '<'", pos)
    else
      (match scan_iri_ref_end input (pos + Prims.int_one) false
               ((len - pos) + Prims.int_one)
       with
       | Parser_Combinators.ParseOk ((gt_pos, has_colon), next) ->
           Parser_Combinators.ParseOk
             ({
                irs_span = { sp_start = pos; sp_end = next };
                irs_has_colon = has_colon
              }, next)
       | Parser_Combinators.ParseFail (msg, fpos) ->
           Parser_Combinators.ParseFail (msg, fpos))
let rec scan_short_string_end (input : Prims.string) (pos : Prims.nat)
  (quote_code : Prims.nat) (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then pos
     else
       (let ch = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char ch in
        if
          (((code = quote_code) || (code = (Prims.of_int (0x5C)))) ||
             (code = (Prims.of_int (0x0A))))
            || (code = (Prims.of_int (0x0D)))
        then pos
        else
          scan_short_string_end input (pos + Prims.int_one) quote_code
            (fuel - Prims.int_one)))
let scan_short_string_span (input : Prims.string) (pos : Prims.nat) :
  short_string_span Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected short string literal", pos)
  else
    (let q = Parser_FastString.fs_byte_index input pos in
     let qcode = FStar_Char.int_of_char q in
     if (qcode <> (Prims.of_int (0x22))) && (qcode <> (Prims.of_int (0x27)))
     then Parser_Combinators.ParseFail ("expected short string literal", pos)
     else
       (let end_pos =
          scan_short_string_end input (pos + Prims.int_one) qcode
            ((len - pos) + Prims.int_one) in
        if
          (end_pos < len) &&
            ((FStar_Char.int_of_char
                (Parser_FastString.fs_byte_index input end_pos))
               = qcode)
        then
          Parser_Combinators.ParseOk
            ({
               sss_quote = q;
               sss_content =
                 { sp_start = (pos + Prims.int_one); sp_end = end_pos }
             }, (end_pos + Prims.int_one))
        else
          Parser_Combinators.ParseFail
            ("short string needs slow path", end_pos)))
let scan_punct (input : Prims.string) (pos : Prims.nat) :
  scanned_token Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected punctuation", pos)
  else
    (let code =
       FStar_Char.int_of_char (Parser_FastString.fs_byte_index input pos) in
     let sp = { sp_start = pos; sp_end = (pos + Prims.int_one) } in
     if code = (Prims.of_int (0x2E))
     then
       Parser_Combinators.ParseOk
         ({ st_kind = TK_Dot; st_span = sp }, (pos + Prims.int_one))
     else
       if code = (Prims.of_int (0x3B))
       then
         Parser_Combinators.ParseOk
           ({ st_kind = TK_Semicolon; st_span = sp }, (pos + Prims.int_one))
       else
         if code = (Prims.of_int (0x2C))
         then
           Parser_Combinators.ParseOk
             ({ st_kind = TK_Comma; st_span = sp }, (pos + Prims.int_one))
         else
           if code = (Prims.of_int (0x5B))
           then
             Parser_Combinators.ParseOk
               ({ st_kind = TK_LBracket; st_span = sp },
                 (pos + Prims.int_one))
           else
             if code = (Prims.of_int (0x5D))
             then
               Parser_Combinators.ParseOk
                 ({ st_kind = TK_RBracket; st_span = sp },
                   (pos + Prims.int_one))
             else
               if code = (Prims.of_int (0x28))
               then
                 Parser_Combinators.ParseOk
                   ({ st_kind = TK_LParen; st_span = sp },
                     (pos + Prims.int_one))
               else
                 if code = (Prims.of_int (0x29))
                 then
                   Parser_Combinators.ParseOk
                     ({ st_kind = TK_RParen; st_span = sp },
                       (pos + Prims.int_one))
                 else
                   Parser_Combinators.ParseFail
                     ("expected Turtle punctuation", pos))
