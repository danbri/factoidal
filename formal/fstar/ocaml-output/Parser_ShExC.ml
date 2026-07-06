open Prims
type shexc_term =
  | ST_Iri of Prims.string * Prims.bool 
  | ST_PName of Prims.string * Prims.string 
  | ST_BNode of Prims.string 
let uu___is_ST_Iri (projectee : shexc_term) : Prims.bool=
  match projectee with | ST_Iri (raw, has_colon) -> true | uu___ -> false
let __proj__ST_Iri__item__raw (projectee : shexc_term) : Prims.string=
  match projectee with | ST_Iri (raw, has_colon) -> raw
let __proj__ST_Iri__item__has_colon (projectee : shexc_term) : Prims.bool=
  match projectee with | ST_Iri (raw, has_colon) -> has_colon
let uu___is_ST_PName (projectee : shexc_term) : Prims.bool=
  match projectee with | ST_PName (ns, local) -> true | uu___ -> false
let __proj__ST_PName__item__ns (projectee : shexc_term) : Prims.string=
  match projectee with | ST_PName (ns, local) -> ns
let __proj__ST_PName__item__local (projectee : shexc_term) : Prims.string=
  match projectee with | ST_PName (ns, local) -> local
let uu___is_ST_BNode (projectee : shexc_term) : Prims.bool=
  match projectee with | ST_BNode _0 -> true | uu___ -> false
let __proj__ST_BNode__item___0 (projectee : shexc_term) : Prims.string=
  match projectee with | ST_BNode _0 -> _0
type shexc_token =
  | TK_TERM of shexc_term 
  | TK_AT_TERM of shexc_term 
  | TK_LANGTAG of Prims.string 
  | TK_STRING of Prims.string 
  | TK_NUMBER of Prims.string * Prims.string 
  | TK_REGEX of Prims.string * Prims.string 
  | TK_SEMACT of shexc_term * Prims.string FStar_Pervasives_Native.option 
  | TK_KW of Prims.string 
  | TK_HATHAT 
  | TK_CARET 
  | TK_TILDE 
  | TK_MINUS 
  | TK_LBRACE 
  | TK_RBRACE 
  | TK_LPAREN 
  | TK_RPAREN 
  | TK_LBRACKET 
  | TK_RBRACKET 
  | TK_SEMI 
  | TK_PIPE 
  | TK_DOT 
  | TK_DOLLAR 
  | TK_AMP 
  | TK_STAR 
  | TK_PLUS 
  | TK_QMARK 
  | TK_SLASH_ANNOT 
  | TK_AT 
  | TK_EQ 
  | TK_REPEAT_RANGE of Prims.int * Prims.int 
  | TK_INVALID of Prims.string 
  | TK_EOF 
let uu___is_TK_TERM (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_TERM _0 -> true | uu___ -> false
let __proj__TK_TERM__item___0 (projectee : shexc_token) : shexc_term=
  match projectee with | TK_TERM _0 -> _0
let uu___is_TK_AT_TERM (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_AT_TERM _0 -> true | uu___ -> false
let __proj__TK_AT_TERM__item___0 (projectee : shexc_token) : shexc_term=
  match projectee with | TK_AT_TERM _0 -> _0
let uu___is_TK_LANGTAG (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_LANGTAG _0 -> true | uu___ -> false
let __proj__TK_LANGTAG__item___0 (projectee : shexc_token) : Prims.string=
  match projectee with | TK_LANGTAG _0 -> _0
let uu___is_TK_STRING (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_STRING _0 -> true | uu___ -> false
let __proj__TK_STRING__item___0 (projectee : shexc_token) : Prims.string=
  match projectee with | TK_STRING _0 -> _0
let uu___is_TK_NUMBER (projectee : shexc_token) : Prims.bool=
  match projectee with
  | TK_NUMBER (lexeme, datatype) -> true
  | uu___ -> false
let __proj__TK_NUMBER__item__lexeme (projectee : shexc_token) : Prims.string=
  match projectee with | TK_NUMBER (lexeme, datatype) -> lexeme
let __proj__TK_NUMBER__item__datatype (projectee : shexc_token) :
  Prims.string=
  match projectee with | TK_NUMBER (lexeme, datatype) -> datatype
let uu___is_TK_REGEX (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_REGEX (pattern, flags) -> true | uu___ -> false
let __proj__TK_REGEX__item__pattern (projectee : shexc_token) : Prims.string=
  match projectee with | TK_REGEX (pattern, flags) -> pattern
let __proj__TK_REGEX__item__flags (projectee : shexc_token) : Prims.string=
  match projectee with | TK_REGEX (pattern, flags) -> flags
let uu___is_TK_SEMACT (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_SEMACT (name, code) -> true | uu___ -> false
let __proj__TK_SEMACT__item__name (projectee : shexc_token) : shexc_term=
  match projectee with | TK_SEMACT (name, code) -> name
let __proj__TK_SEMACT__item__code (projectee : shexc_token) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | TK_SEMACT (name, code) -> code
let uu___is_TK_KW (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_KW _0 -> true | uu___ -> false
let __proj__TK_KW__item___0 (projectee : shexc_token) : Prims.string=
  match projectee with | TK_KW _0 -> _0
let uu___is_TK_HATHAT (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_HATHAT -> true | uu___ -> false
let uu___is_TK_CARET (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_CARET -> true | uu___ -> false
let uu___is_TK_TILDE (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_TILDE -> true | uu___ -> false
let uu___is_TK_MINUS (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_MINUS -> true | uu___ -> false
let uu___is_TK_LBRACE (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_LBRACE -> true | uu___ -> false
let uu___is_TK_RBRACE (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_RBRACE -> true | uu___ -> false
let uu___is_TK_LPAREN (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_LPAREN -> true | uu___ -> false
let uu___is_TK_RPAREN (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_RPAREN -> true | uu___ -> false
let uu___is_TK_LBRACKET (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_LBRACKET -> true | uu___ -> false
let uu___is_TK_RBRACKET (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_RBRACKET -> true | uu___ -> false
let uu___is_TK_SEMI (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_SEMI -> true | uu___ -> false
let uu___is_TK_PIPE (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_PIPE -> true | uu___ -> false
let uu___is_TK_DOT (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_DOT -> true | uu___ -> false
let uu___is_TK_DOLLAR (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_DOLLAR -> true | uu___ -> false
let uu___is_TK_AMP (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_AMP -> true | uu___ -> false
let uu___is_TK_STAR (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_STAR -> true | uu___ -> false
let uu___is_TK_PLUS (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_PLUS -> true | uu___ -> false
let uu___is_TK_QMARK (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_QMARK -> true | uu___ -> false
let uu___is_TK_SLASH_ANNOT (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_SLASH_ANNOT -> true | uu___ -> false
let uu___is_TK_AT (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_AT -> true | uu___ -> false
let uu___is_TK_EQ (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_EQ -> true | uu___ -> false
let uu___is_TK_REPEAT_RANGE (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_REPEAT_RANGE (min, max) -> true | uu___ -> false
let __proj__TK_REPEAT_RANGE__item__min (projectee : shexc_token) : Prims.int=
  match projectee with | TK_REPEAT_RANGE (min, max) -> min
let __proj__TK_REPEAT_RANGE__item__max (projectee : shexc_token) : Prims.int=
  match projectee with | TK_REPEAT_RANGE (min, max) -> max
let uu___is_TK_INVALID (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_INVALID _0 -> true | uu___ -> false
let __proj__TK_INVALID__item___0 (projectee : shexc_token) : Prims.string=
  match projectee with | TK_INVALID _0 -> _0
let uu___is_TK_EOF (projectee : shexc_token) : Prims.bool=
  match projectee with | TK_EOF -> true | uu___ -> false
type shexc_tokens = shexc_token Prims.list
let sc_is_digit (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))
let sc_is_ws_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))) ||
     (code = (Prims.of_int (0x0A))))
    || (code = (Prims.of_int (0x0D)))
let sc_is_alpha (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
    ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A))))
let sc_is_word_char (c : FStar_Char.char) : Prims.bool=
  ((sc_is_alpha c) || (sc_is_digit c)) ||
    ((FStar_Char.int_of_char c) = (Prims.of_int (0x2D)))
let rec sc_skip_block_comment (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = Parser_FastString.fs_byte_length input in
     if (pos + Prims.int_one) < len
     then
       let c0 = Parser_FastString.fs_byte_index input pos in
       let c1 = Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
       (if
          ((FStar_Char.int_of_char c0) = (Prims.of_int (0x2A))) &&
            ((FStar_Char.int_of_char c1) = (Prims.of_int (0x2F)))
        then pos + (Prims.of_int (2))
        else
          sc_skip_block_comment input (pos + Prims.int_one)
            (fuel - Prims.int_one))
     else len)
let rec sc_skip_ws_comments (input : Prims.string) (pos : Prims.nat)
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
        if
          (((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09))))
             || (code = (Prims.of_int (0x0A))))
            || (code = (Prims.of_int (0x0D)))
        then
          sc_skip_ws_comments input (pos + Prims.int_one)
            (fuel - Prims.int_one)
        else
          if code = (Prims.of_int (0x23))
          then
            (let p' = Parser_Turtle.skip_to_eol input pos fuel in
             sc_skip_ws_comments input p' (fuel - Prims.int_one))
          else
            if
              ((code = (Prims.of_int (0x2F))) &&
                 ((pos + Prims.int_one) < len))
                &&
                ((FStar_Char.int_of_char
                    (Parser_FastString.fs_byte_index input
                       (pos + Prims.int_one)))
                   = (Prims.of_int (0x2A)))
            then
              (let p' =
                 sc_skip_block_comment input (pos + (Prims.of_int (2))) fuel in
               sc_skip_ws_comments input p' (fuel - Prims.int_one))
            else pos))
let shexc_ws (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = Parser_FastString.fs_byte_length input in
  if pos > len
  then pos
  else sc_skip_ws_comments input pos ((len - pos) + Prims.int_one)
let rec sc_count_backslash_run (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then Prims.int_zero
  else
    (let len = Parser_FastString.fs_byte_length input in
     if
       (pos < len) &&
         ((FStar_Char.int_of_char (Parser_FastString.fs_byte_index input pos))
            = (Prims.of_int (0x5C)))
     then
       Prims.int_one +
         (sc_count_backslash_run input (pos + Prims.int_one)
            (fuel - Prims.int_one))
     else Prims.int_zero)
let rec sc_emit_n_backslashes (n : Prims.nat)
  (acc : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  if n = Prims.int_zero
  then acc
  else
    sc_emit_n_backslashes (n - Prims.int_one)
      ((FStar_Char.char_of_int (Prims.of_int (0x5C))) :: acc)
let rec sc_scan_regex_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("unterminated regex literal", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated regex literal", pos)
     else
       (let c = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char c in
        if code = (Prims.of_int (0x2F))
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if code = (Prims.of_int (0x5C))
          then
            (let run_len =
               sc_count_backslash_run input pos ((len - pos) + Prims.int_one) in
             let run_end = pos + run_len in
             let escape_kind =
               if run_end >= len
               then FStar_Pervasives_Native.None
               else
                 (let nc =
                    FStar_Char.int_of_char
                      (Parser_FastString.fs_byte_index input run_end) in
                  if nc = (Prims.of_int (0x2F))
                  then FStar_Pervasives_Native.Some (Prims.of_int (0x2F))
                  else
                    if
                      (nc = (Prims.of_int (0x75))) &&
                        ((run_end + (Prims.of_int (5))) <= len)
                    then FStar_Pervasives_Native.Some (Prims.of_int (0x75))
                    else
                      if
                        (nc = (Prims.of_int (0x55))) &&
                          ((run_end + (Prims.of_int (9))) <= len)
                      then FStar_Pervasives_Native.Some (Prims.of_int (0x55))
                      else FStar_Pervasives_Native.None) in
             let escape_applies =
               (FStar_Pervasives_Native.uu___is_Some escape_kind) &&
                 (((mod) run_len (Prims.of_int (2))) = Prims.int_one) in
             if escape_applies
             then
               let kind =
                 match escape_kind with
                 | FStar_Pervasives_Native.Some k -> k
                 | FStar_Pervasives_Native.None -> Prims.int_zero in
               let acc1 = sc_emit_n_backslashes (run_len - Prims.int_one) acc in
               (if kind = (Prims.of_int (0x2F))
                then
                  sc_scan_regex_body input (run_end + Prims.int_one)
                    ((FStar_Char.char_of_int (Prims.of_int (0x2F))) :: acc1)
                    (fuel - Prims.int_one)
                else
                  if kind = (Prims.of_int (0x75))
                  then
                    (let h0 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + Prims.int_one)) in
                     let h1 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (2)))) in
                     let h2 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (3)))) in
                     let h3 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (4)))) in
                     let cp =
                       (((h0 * (Prims.of_int (4096))) +
                           (h1 * (Prims.of_int (256))))
                          + (h2 * (Prims.of_int (16))))
                         + h3 in
                     sc_scan_regex_body input (run_end + (Prims.of_int (5)))
                       ((Parser_NTriples.safe_char_of_int cp) :: acc1)
                       (fuel - Prims.int_one))
                  else
                    (let h0 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + Prims.int_one)) in
                     let h1 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (2)))) in
                     let h2 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (3)))) in
                     let h3 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (4)))) in
                     let h4 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (5)))) in
                     let h5 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (6)))) in
                     let h6 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (7)))) in
                     let h7 =
                       Parser_NTriples.hex_val
                         (Parser_FastString.fs_byte_index input
                            (run_end + (Prims.of_int (8)))) in
                     let cp =
                       (((((((h0 * (Prims.parse_int "268435456")) +
                               (h1 * (Prims.parse_int "16777216")))
                              + (h2 * (Prims.parse_int "1048576")))
                             + (h3 * (Prims.parse_int "65536")))
                            + (h4 * (Prims.of_int (4096))))
                           + (h5 * (Prims.of_int (256))))
                          + (h6 * (Prims.of_int (16))))
                         + h7 in
                     sc_scan_regex_body input (run_end + (Prims.of_int (9)))
                       ((Parser_NTriples.safe_char_of_int cp) :: acc1)
                       (fuel - Prims.int_one)))
             else
               (let acc1 = sc_emit_n_backslashes run_len acc in
                sc_scan_regex_body input run_end acc1 (fuel - Prims.int_one)))
          else
            if code < (Prims.of_int (0x80))
            then
              sc_scan_regex_body input (pos + Prims.int_one) (c :: acc)
                (fuel - Prims.int_one)
            else
              (let uu___5 = Parser_FastString.fs_cp_at input pos in
               match uu___5 with
               | (cp, adv) ->
                   let advance =
                     if adv = Prims.int_zero then Prims.int_one else adv in
                   sc_scan_regex_body input (pos + advance)
                     ((Parser_NTriples.safe_char_of_int cp) :: acc)
                     (fuel - Prims.int_one))))
let rec sc_scan_code_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then
    Parser_Combinators.ParseFail
      ("unterminated semantic action code block", pos)
  else
    (let len = Parser_FastString.fs_byte_length input in
     if pos >= len
     then
       Parser_Combinators.ParseFail
         ("unterminated semantic action code block", pos)
     else
       (let c = Parser_FastString.fs_byte_index input pos in
        let code = FStar_Char.int_of_char c in
        if
          ((code = (Prims.of_int (0x25))) && ((pos + Prims.int_one) < len))
            &&
            ((FStar_Char.int_of_char
                (Parser_FastString.fs_byte_index input (pos + Prims.int_one)))
               = (Prims.of_int (0x7D)))
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + (Prims.of_int (2))))
        else
          if (code = (Prims.of_int (0x5C))) && ((pos + Prims.int_one) < len)
          then
            (let next =
               Parser_FastString.fs_byte_index input (pos + Prims.int_one) in
             let ncode = FStar_Char.int_of_char next in
             if ncode = (Prims.of_int (0x25))
             then
               sc_scan_code_body input (pos + (Prims.of_int (2)))
                 ((FStar_Char.char_of_int (Prims.of_int (0x25))) :: acc)
                 (fuel - Prims.int_one)
             else
               if ncode = (Prims.of_int (0x5C))
               then
                 sc_scan_code_body input (pos + (Prims.of_int (2)))
                   ((FStar_Char.char_of_int (Prims.of_int (0x5C))) :: acc)
                   (fuel - Prims.int_one)
               else
                 if
                   (ncode = (Prims.of_int (0x75))) &&
                     ((pos + (Prims.of_int (6))) <= len)
                 then
                   (let h0 =
                      Parser_NTriples.hex_val
                        (Parser_FastString.fs_byte_index input
                           (pos + (Prims.of_int (2)))) in
                    let h1 =
                      Parser_NTriples.hex_val
                        (Parser_FastString.fs_byte_index input
                           (pos + (Prims.of_int (3)))) in
                    let h2 =
                      Parser_NTriples.hex_val
                        (Parser_FastString.fs_byte_index input
                           (pos + (Prims.of_int (4)))) in
                    let h3 =
                      Parser_NTriples.hex_val
                        (Parser_FastString.fs_byte_index input
                           (pos + (Prims.of_int (5)))) in
                    let cp =
                      (((h0 * (Prims.of_int (4096))) +
                          (h1 * (Prims.of_int (256))))
                         + (h2 * (Prims.of_int (16))))
                        + h3 in
                    sc_scan_code_body input (pos + (Prims.of_int (6)))
                      ((Parser_NTriples.safe_char_of_int cp) :: acc)
                      (fuel - Prims.int_one))
                 else
                   if
                     (ncode = (Prims.of_int (0x55))) &&
                       ((pos + (Prims.of_int (10))) <= len)
                   then
                     (let h0 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (2)))) in
                      let h1 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (3)))) in
                      let h2 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (4)))) in
                      let h3 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (5)))) in
                      let h4 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (6)))) in
                      let h5 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (7)))) in
                      let h6 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (8)))) in
                      let h7 =
                        Parser_NTriples.hex_val
                          (Parser_FastString.fs_byte_index input
                             (pos + (Prims.of_int (9)))) in
                      let cp =
                        (((((((h0 * (Prims.parse_int "268435456")) +
                                (h1 * (Prims.parse_int "16777216")))
                               + (h2 * (Prims.parse_int "1048576")))
                              + (h3 * (Prims.parse_int "65536")))
                             + (h4 * (Prims.of_int (4096))))
                            + (h5 * (Prims.of_int (256))))
                           + (h6 * (Prims.of_int (16))))
                          + h7 in
                      sc_scan_code_body input (pos + (Prims.of_int (10)))
                        ((Parser_NTriples.safe_char_of_int cp) :: acc)
                        (fuel - Prims.int_one))
                   else
                     sc_scan_code_body input (pos + Prims.int_one) (c :: acc)
                       (fuel - Prims.int_one))
          else
            if code < (Prims.of_int (0x80))
            then
              sc_scan_code_body input (pos + Prims.int_one) (c :: acc)
                (fuel - Prims.int_one)
            else
              (let uu___5 = Parser_FastString.fs_cp_at input pos in
               match uu___5 with
               | (cp, adv) ->
                   let advance =
                     if adv = Prims.int_zero then Prims.int_one else adv in
                   sc_scan_code_body input (pos + advance)
                     ((Parser_NTriples.safe_char_of_int cp) :: acc)
                     (fuel - Prims.int_one))))
let sc_is_keyword (w : Prims.string) : Prims.bool=
  (((((((((((((((((((((((((((w = "PREFIX") || (w = "BASE")) || (w = "IMPORT"))
                            || (w = "START"))
                           || (w = "AND"))
                          || (w = "OR"))
                         || (w = "NOT"))
                        || (w = "IRI"))
                       || (w = "BNODE"))
                      || (w = "NONLITERAL"))
                     || (w = "LITERAL"))
                    || (w = "EXTRA"))
                   || (w = "CLOSED"))
                  || (w = "EXTENDS"))
                 || (w = "ABSTRACT"))
                || (w = "EXTERNAL"))
               || (w = "LENGTH"))
              || (w = "MINLENGTH"))
             || (w = "MAXLENGTH"))
            || (w = "MININCLUSIVE"))
           || (w = "MAXINCLUSIVE"))
          || (w = "MINEXCLUSIVE"))
         || (w = "MAXEXCLUSIVE"))
        || (w = "TOTALDIGITS"))
       || (w = "FRACTIONDIGITS"))
      || (w = "PATTERN"))
     || (w = "TRUE"))
    || (w = "FALSE")
let sc_upper_char (c : FStar_Char.char) : FStar_Char.char=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))
  then FStar_Char.char_of_int (code - (Prims.of_int (0x20)))
  else c
let rec sc_upper_acc (chars : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match chars with
  | [] -> []
  | c::rest -> (sc_upper_char c) :: (sc_upper_acc rest)
let sc_upper (s : Prims.string) : Prims.string=
  FStar_String.string_of_list (sc_upper_acc (FStar_String.list_of_string s))
let sc_lower_char (c : FStar_Char.char) : FStar_Char.char=
  let code = FStar_Char.int_of_char c in
  if (code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))
  then FStar_Char.char_of_int (code + (Prims.of_int (0x20)))
  else c
let rec sc_lower_acc (chars : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match chars with
  | [] -> []
  | c::rest -> (sc_lower_char c) :: (sc_lower_acc rest)
let sc_lower (s : Prims.string) : Prims.string=
  FStar_String.string_of_list (sc_lower_acc (FStar_String.list_of_string s))
let rec sc_scan_word_end (input : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let len = Parser_FastString.fs_byte_length input in
     if
       (pos < len) &&
         (sc_is_word_char (Parser_FastString.fs_byte_index input pos))
     then sc_scan_word_end input (pos + Prims.int_one) (fuel - Prims.int_one)
     else pos)
let sc_scan_langtag_end (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = Parser_FastString.fs_byte_length input in
  if pos > len
  then pos
  else sc_scan_word_end input pos ((len - pos) + Prims.int_one)
let sc_try_repeat_range (input : Prims.string) (pos : Prims.nat) :
  (Prims.int * Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  let len = Parser_FastString.fs_byte_length input in
  let rec scan_digits p fuel =
    if fuel = Prims.int_zero
    then p
    else
      if (p < len) && (sc_is_digit (Parser_FastString.fs_byte_index input p))
      then scan_digits (p + Prims.int_one) (fuel - Prims.int_one)
      else p in
  if
    (pos >= len) ||
      ((FStar_Char.int_of_char (Parser_FastString.fs_byte_index input pos))
         <> (Prims.of_int (0x7B)))
  then FStar_Pervasives_Native.None
  else
    (let d0 = scan_digits (pos + Prims.int_one) (len - pos) in
     if d0 = (pos + Prims.int_one)
     then FStar_Pervasives_Native.None
     else
       (match ShEx_Schema.shex_parse_int_string
                (Parser_FastString.fs_byte_sub input (pos + Prims.int_one)
                   ((d0 - pos) - Prims.int_one))
        with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some m ->
            if
              (d0 < len) &&
                ((FStar_Char.int_of_char
                    (Parser_FastString.fs_byte_index input d0))
                   = (Prims.of_int (0x7D)))
            then FStar_Pervasives_Native.Some (m, m, (d0 + Prims.int_one))
            else
              if
                (d0 < len) &&
                  ((FStar_Char.int_of_char
                      (Parser_FastString.fs_byte_index input d0))
                     = (Prims.of_int (0x2C)))
              then
                (if
                   (((d0 + (Prims.of_int (2))) <= len) &&
                      ((FStar_Char.int_of_char
                          (Parser_FastString.fs_byte_index input
                             (d0 + Prims.int_one)))
                         = (Prims.of_int (0x2A))))
                     &&
                     ((FStar_Char.int_of_char
                         (Parser_FastString.fs_byte_index input
                            (d0 + (Prims.of_int (2)))))
                        = (Prims.of_int (0x7D)))
                 then
                   FStar_Pervasives_Native.Some
                     (m, (Prims.of_int (-1)), (d0 + (Prims.of_int (3))))
                 else
                   (let d1 = scan_digits (d0 + Prims.int_one) (len - d0) in
                    if
                      (d1 < len) &&
                        ((FStar_Char.int_of_char
                            (Parser_FastString.fs_byte_index input d1))
                           = (Prims.of_int (0x7D)))
                    then
                      (if d1 = (d0 + Prims.int_one)
                       then
                         FStar_Pervasives_Native.Some
                           (m, (Prims.of_int (-1)), (d1 + Prims.int_one))
                       else
                         (match ShEx_Schema.shex_parse_int_string
                                  (Parser_FastString.fs_byte_sub input
                                     (d0 + Prims.int_one)
                                     ((d1 - d0) - Prims.int_one))
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some n ->
                              FStar_Pervasives_Native.Some
                                (m, n, (d1 + Prims.int_one))))
                    else FStar_Pervasives_Native.None))
              else FStar_Pervasives_Native.None))
let sc_scan_iriref_term (input : Prims.string) (pos : Prims.nat) :
  shexc_term Parser_Combinators.parse_result=
  match Parser_TurtleScanner.scan_iri_ref_span input pos with
  | Parser_Combinators.ParseOk (sp, pos') ->
      let raw = Parser_Turtle.iri_ref_span_to_raw input sp in
      if Parser_Turtle.contains_forbidden_iri_char raw
      then Parser_Combinators.ParseFail ("forbidden character in IRI", pos)
      else
        Parser_Combinators.ParseOk
          ((ST_Iri (raw, (sp.Parser_TurtleScanner.irs_has_colon))), pos')
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let sc_scan_term (input : Prims.string) (pos : Prims.nat) :
  shexc_term Parser_Combinators.parse_result=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then Parser_Combinators.ParseFail ("expected term", pos)
  else
    (let c = Parser_FastString.fs_byte_index input pos in
     if (FStar_Char.int_of_char c) = (Prims.of_int (0x3C))
     then sc_scan_iriref_term input pos
     else
       if
         (((FStar_Char.int_of_char c) = (Prims.of_int (0x5F))) &&
            ((pos + Prims.int_one) < len))
           &&
           ((FStar_Char.int_of_char
               (Parser_FastString.fs_byte_index input (pos + Prims.int_one)))
              = (Prims.of_int (0x3A)))
       then
         (match Parser_NTriples.parse_bnode input pos with
          | Parser_Combinators.ParseOk (label, pos') ->
              Parser_Combinators.ParseOk ((ST_BNode label), pos')
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos))
       else
         (match Parser_Turtle.parse_prefixed_name input pos with
          | Parser_Combinators.ParseOk ((ns, local), pos') ->
              Parser_Combinators.ParseOk ((ST_PName (ns, local)), pos')
          | Parser_Combinators.ParseFail (msg, fpos) ->
              Parser_Combinators.ParseFail (msg, fpos)))
let shexc_next_token (input : Prims.string) (pos : Prims.nat) :
  (shexc_token * Prims.nat)=
  let len = Parser_FastString.fs_byte_length input in
  if pos >= len
  then (TK_EOF, pos)
  else
    (let c = Parser_FastString.fs_byte_index input pos in
     let code = FStar_Char.int_of_char c in
     if code = (Prims.of_int (0x7B))
     then
       match sc_try_repeat_range input pos with
       | FStar_Pervasives_Native.Some (m, n, pos') ->
           ((TK_REPEAT_RANGE (m, n)), pos')
       | FStar_Pervasives_Native.None -> (TK_LBRACE, (pos + Prims.int_one))
     else
       if code = (Prims.of_int (0x7D))
       then (TK_RBRACE, (pos + Prims.int_one))
       else
         if code = (Prims.of_int (0x28))
         then (TK_LPAREN, (pos + Prims.int_one))
         else
           if code = (Prims.of_int (0x29))
           then (TK_RPAREN, (pos + Prims.int_one))
           else
             if code = (Prims.of_int (0x5B))
             then (TK_LBRACKET, (pos + Prims.int_one))
             else
               if code = (Prims.of_int (0x5D))
               then (TK_RBRACKET, (pos + Prims.int_one))
               else
                 if code = (Prims.of_int (0x3B))
                 then (TK_SEMI, (pos + Prims.int_one))
                 else
                   if code = (Prims.of_int (0x7C))
                   then (TK_PIPE, (pos + Prims.int_one))
                   else
                     if code = (Prims.of_int (0x24))
                     then (TK_DOLLAR, (pos + Prims.int_one))
                     else
                       if code = (Prims.of_int (0x26))
                       then (TK_AMP, (pos + Prims.int_one))
                       else
                         if code = (Prims.of_int (0x2A))
                         then (TK_STAR, (pos + Prims.int_one))
                         else
                           if code = (Prims.of_int (0x2B))
                           then (TK_PLUS, (pos + Prims.int_one))
                           else
                             if code = (Prims.of_int (0x3F))
                             then (TK_QMARK, (pos + Prims.int_one))
                             else
                               if code = (Prims.of_int (0x3D))
                               then (TK_EQ, (pos + Prims.int_one))
                               else
                                 if code = (Prims.of_int (0x7E))
                                 then (TK_TILDE, (pos + Prims.int_one))
                                 else
                                   if code = (Prims.of_int (0x5E))
                                   then
                                     (if
                                        ((pos + Prims.int_one) < len) &&
                                          ((FStar_Char.int_of_char
                                              (Parser_FastString.fs_byte_index
                                                 input (pos + Prims.int_one)))
                                             = (Prims.of_int (0x5E)))
                                      then
                                        (TK_HATHAT,
                                          (pos + (Prims.of_int (2))))
                                      else (TK_CARET, (pos + Prims.int_one)))
                                   else
                                     if code = (Prims.of_int (0x2F))
                                     then
                                       (if
                                          ((pos + Prims.int_one) < len) &&
                                            ((FStar_Char.int_of_char
                                                (Parser_FastString.fs_byte_index
                                                   input
                                                   (pos + Prims.int_one)))
                                               = (Prims.of_int (0x2F)))
                                        then
                                          (TK_SLASH_ANNOT,
                                            (pos + (Prims.of_int (2))))
                                        else
                                          (match sc_scan_regex_body input
                                                   (pos + Prims.int_one) []
                                                   ((len - pos) +
                                                      Prims.int_one)
                                           with
                                           | Parser_Combinators.ParseOk
                                               (pat, pos') ->
                                               let flags_end =
                                                 sc_scan_langtag_end input
                                                   pos' in
                                               ((TK_REGEX
                                                   (pat,
                                                     (Parser_FastString.fs_byte_sub
                                                        input pos'
                                                        (flags_end - pos')))),
                                                 flags_end)
                                           | Parser_Combinators.ParseFail
                                               (msg, fpos) ->
                                               ((TK_INVALID msg), fpos)))
                                     else
                                       if code = (Prims.of_int (0x2E))
                                       then
                                         (if
                                            ((pos + Prims.int_one) < len) &&
                                              (sc_is_digit
                                                 (Parser_FastString.fs_byte_index
                                                    input
                                                    (pos + Prims.int_one)))
                                          then
                                            match Parser_Turtle.parse_numeric_literal
                                                    input pos
                                            with
                                            | Parser_Combinators.ParseOk
                                                ((lexeme, dt), pos') ->
                                                ((TK_NUMBER (lexeme, dt)),
                                                  pos')
                                            | Parser_Combinators.ParseFail
                                                (msg, fpos) ->
                                                ((TK_INVALID msg), fpos)
                                          else
                                            (TK_DOT, (pos + Prims.int_one)))
                                       else
                                         if code = (Prims.of_int (0x2D))
                                         then
                                           (if
                                              ((pos + Prims.int_one) < len)
                                                &&
                                                ((sc_is_digit
                                                    (Parser_FastString.fs_byte_index
                                                       input
                                                       (pos + Prims.int_one)))
                                                   ||
                                                   ((((FStar_Char.int_of_char
                                                         (Parser_FastString.fs_byte_index
                                                            input
                                                            (pos +
                                                               Prims.int_one)))
                                                        =
                                                        (Prims.of_int (0x2E)))
                                                       &&
                                                       ((pos +
                                                           (Prims.of_int (2)))
                                                          < len))
                                                      &&
                                                      (sc_is_digit
                                                         (Parser_FastString.fs_byte_index
                                                            input
                                                            (pos +
                                                               (Prims.of_int (2)))))))
                                            then
                                              match Parser_Turtle.parse_numeric_literal
                                                      input pos
                                              with
                                              | Parser_Combinators.ParseOk
                                                  ((lexeme, dt), pos') ->
                                                  ((TK_NUMBER (lexeme, dt)),
                                                    pos')
                                              | Parser_Combinators.ParseFail
                                                  (msg, fpos) ->
                                                  ((TK_INVALID msg), fpos)
                                            else
                                              (TK_MINUS,
                                                (pos + Prims.int_one)))
                                         else
                                           if
                                             (code = (Prims.of_int (0x22)))
                                               ||
                                               (code = (Prims.of_int (0x27)))
                                           then
                                             (match Parser_Turtle.parse_turtle_string
                                                      input pos
                                              with
                                              | Parser_Combinators.ParseOk
                                                  (s, pos') ->
                                                  ((TK_STRING s), pos')
                                              | Parser_Combinators.ParseFail
                                                  (msg, fpos) ->
                                                  ((TK_INVALID msg), fpos))
                                           else
                                             if code = (Prims.of_int (0x3C))
                                             then
                                               (match sc_scan_iriref_term
                                                        input pos
                                                with
                                                | Parser_Combinators.ParseOk
                                                    (t, pos') ->
                                                    ((TK_TERM t), pos')
                                                | Parser_Combinators.ParseFail
                                                    (msg, fpos) ->
                                                    ((TK_INVALID msg), fpos))
                                             else
                                               if
                                                 ((code =
                                                     (Prims.of_int (0x5F)))
                                                    &&
                                                    ((pos + Prims.int_one) <
                                                       len))
                                                   &&
                                                   ((FStar_Char.int_of_char
                                                       (Parser_FastString.fs_byte_index
                                                          input
                                                          (pos +
                                                             Prims.int_one)))
                                                      = (Prims.of_int (0x3A)))
                                               then
                                                 (match Parser_NTriples.parse_bnode
                                                          input pos
                                                  with
                                                  | Parser_Combinators.ParseOk
                                                      (label, pos') ->
                                                      ((TK_TERM
                                                          (ST_BNode label)),
                                                        pos')
                                                  | Parser_Combinators.ParseFail
                                                      (msg, fpos) ->
                                                      ((TK_INVALID msg),
                                                        fpos))
                                               else
                                                 if
                                                   code =
                                                     (Prims.of_int (0x40))
                                                 then
                                                   (if
                                                      ((pos + Prims.int_one)
                                                         < len)
                                                        &&
                                                        ((FStar_Char.int_of_char
                                                            (Parser_FastString.fs_byte_index
                                                               input
                                                               (pos +
                                                                  Prims.int_one)))
                                                           =
                                                           (Prims.of_int (0x3C)))
                                                    then
                                                      match sc_scan_iriref_term
                                                              input
                                                              (pos +
                                                                 Prims.int_one)
                                                      with
                                                      | Parser_Combinators.ParseOk
                                                          (t, pos') ->
                                                          ((TK_AT_TERM t),
                                                            pos')
                                                      | Parser_Combinators.ParseFail
                                                          (msg, fpos) ->
                                                          ((TK_INVALID msg),
                                                            fpos)
                                                    else
                                                      if
                                                        (((pos +
                                                             (Prims.of_int (2)))
                                                            < len)
                                                           &&
                                                           ((FStar_Char.int_of_char
                                                               (Parser_FastString.fs_byte_index
                                                                  input
                                                                  (pos +
                                                                    Prims.int_one)))
                                                              =
                                                              (Prims.of_int (0x5F))))
                                                          &&
                                                          ((FStar_Char.int_of_char
                                                              (Parser_FastString.fs_byte_index
                                                                 input
                                                                 (pos +
                                                                    (Prims.of_int (2)))))
                                                             =
                                                             (Prims.of_int (0x3A)))
                                                      then
                                                        (match Parser_NTriples.parse_bnode
                                                                 input
                                                                 (pos +
                                                                    Prims.int_one)
                                                         with
                                                         | Parser_Combinators.ParseOk
                                                             (label, pos') ->
                                                             ((TK_AT_TERM
                                                                 (ST_BNode
                                                                    label)),
                                                               pos')
                                                         | Parser_Combinators.ParseFail
                                                             (msg, fpos) ->
                                                             ((TK_INVALID msg),
                                                               fpos))
                                                      else
                                                        if
                                                          ((pos +
                                                              Prims.int_one)
                                                             < len)
                                                            &&
                                                            ((sc_is_alpha
                                                                (Parser_FastString.fs_byte_index
                                                                   input
                                                                   (pos +
                                                                    Prims.int_one)))
                                                               ||
                                                               ((FStar_Char.int_of_char
                                                                   (Parser_FastString.fs_byte_index
                                                                    input
                                                                    (pos +
                                                                    Prims.int_one)))
                                                                  =
                                                                  (Prims.of_int (0x3A))))
                                                        then
                                                          (match Parser_Turtle.parse_prefixed_name
                                                                   input
                                                                   (pos +
                                                                    Prims.int_one)
                                                           with
                                                           | Parser_Combinators.ParseOk
                                                               ((ns, local),
                                                                pos')
                                                               ->
                                                               ((TK_AT_TERM
                                                                   (ST_PName
                                                                    (ns,
                                                                    local))),
                                                                 pos')
                                                           | Parser_Combinators.ParseFail
                                                               (uu___25,
                                                                uu___26)
                                                               ->
                                                               let end_pos =
                                                                 sc_scan_langtag_end
                                                                   input
                                                                   (pos +
                                                                    Prims.int_one) in
                                                               ((TK_LANGTAG
                                                                   (sc_lower
                                                                    (Parser_FastString.fs_byte_sub
                                                                    input
                                                                    (pos +
                                                                    Prims.int_one)
                                                                    ((end_pos
                                                                    - pos) -
                                                                    Prims.int_one)))),
                                                                 end_pos))
                                                        else
                                                          if
                                                            ((pos +
                                                                Prims.int_one)
                                                               < len)
                                                              &&
                                                              (sc_is_ws_char
                                                                 (Parser_FastString.fs_byte_index
                                                                    input
                                                                    (
                                                                    pos +
                                                                    Prims.int_one)))
                                                          then
                                                            (TK_AT,
                                                              (pos +
                                                                 Prims.int_one))
                                                          else
                                                            ((TK_LANGTAG ""),
                                                              (pos +
                                                                 Prims.int_one)))
                                                 else
                                                   if
                                                     code =
                                                       (Prims.of_int (0x25))
                                                   then
                                                     (match sc_scan_term
                                                              input
                                                              (pos +
                                                                 Prims.int_one)
                                                      with
                                                      | Parser_Combinators.ParseFail
                                                          (msg, fpos) ->
                                                          ((TK_INVALID msg),
                                                            fpos)
                                                      | Parser_Combinators.ParseOk
                                                          (name, pos1) ->
                                                          if
                                                            (pos1 < len) &&
                                                              ((FStar_Char.int_of_char
                                                                  (Parser_FastString.fs_byte_index
                                                                    input
                                                                    pos1))
                                                                 =
                                                                 (Prims.of_int (0x7B)))
                                                          then
                                                            (match sc_scan_code_body
                                                                    input
                                                                    (pos1 +
                                                                    Prims.int_one)
                                                                    []
                                                                    ((len -
                                                                    pos1) +
                                                                    Prims.int_one)
                                                             with
                                                             | Parser_Combinators.ParseOk
                                                                 (code_str,
                                                                  pos2)
                                                                 ->
                                                                 ((TK_SEMACT
                                                                    (name,
                                                                    (FStar_Pervasives_Native.Some
                                                                    code_str))),
                                                                   pos2)
                                                             | Parser_Combinators.ParseFail
                                                                 (msg, fpos)
                                                                 ->
                                                                 ((TK_INVALID
                                                                    msg),
                                                                   fpos))
                                                          else
                                                            if
                                                              (pos1 < len) &&
                                                                ((FStar_Char.int_of_char
                                                                    (
                                                                    Parser_FastString.fs_byte_index
                                                                    input
                                                                    pos1))
                                                                   =
                                                                   (Prims.of_int (0x25)))
                                                            then
                                                              ((TK_SEMACT
                                                                  (name,
                                                                    FStar_Pervasives_Native.None)),
                                                                (pos1 +
                                                                   Prims.int_one))
                                                            else
                                                              ((TK_INVALID
                                                                  "expected '{' or '%' after semantic action name"),
                                                                pos1))
                                                   else
                                                     if sc_is_digit c
                                                     then
                                                       (match Parser_Turtle.parse_numeric_literal
                                                                input pos
                                                        with
                                                        | Parser_Combinators.ParseOk
                                                            ((lexeme, dt),
                                                             pos')
                                                            ->
                                                            ((TK_NUMBER
                                                                (lexeme, dt)),
                                                              pos')
                                                        | Parser_Combinators.ParseFail
                                                            (msg, fpos) ->
                                                            ((TK_INVALID msg),
                                                              fpos))
                                                     else
                                                       if
                                                         code =
                                                           (Prims.of_int (0x3A))
                                                       then
                                                         (match Parser_Turtle.parse_prefixed_name
                                                                  input pos
                                                          with
                                                          | Parser_Combinators.ParseOk
                                                              ((ns, local),
                                                               pos')
                                                              ->
                                                              ((TK_TERM
                                                                  (ST_PName
                                                                    (ns,
                                                                    local))),
                                                                pos')
                                                          | Parser_Combinators.ParseFail
                                                              (msg, fpos) ->
                                                              ((TK_INVALID
                                                                  msg), fpos))
                                                       else
                                                         if sc_is_alpha c
                                                         then
                                                           (match Parser_Turtle.parse_prefixed_name
                                                                    input pos
                                                            with
                                                            | Parser_Combinators.ParseOk
                                                                ((ns, local),
                                                                 pos')
                                                                ->
                                                                ((TK_TERM
                                                                    (
                                                                    ST_PName
                                                                    (ns,
                                                                    local))),
                                                                  pos')
                                                            | Parser_Combinators.ParseFail
                                                                (uu___27,
                                                                 uu___28)
                                                                ->
                                                                let end_pos =
                                                                  sc_scan_word_end
                                                                    input pos
                                                                    (
                                                                    (len -
                                                                    pos) +
                                                                    Prims.int_one) in
                                                                let raw_word
                                                                  =
                                                                  Parser_FastString.fs_byte_sub
                                                                    input pos
                                                                    (
                                                                    end_pos -
                                                                    pos) in
                                                                if
                                                                  raw_word =
                                                                    "a"
                                                                then
                                                                  ((TK_TERM
                                                                    (ST_Iri
                                                                    (Parser_Turtle.rdf_type_iri,
                                                                    true))),
                                                                    end_pos)
                                                                else
                                                                  (let w =
                                                                    sc_upper
                                                                    raw_word in
                                                                   if
                                                                    sc_is_keyword
                                                                    w
                                                                   then
                                                                    ((TK_KW w),
                                                                    end_pos)
                                                                   else
                                                                    ((TK_INVALID
                                                                    (FStar_String.concat
                                                                    ""
                                                                    ["unrecognized keyword: ";
                                                                    w])),
                                                                    end_pos)))
                                                         else
                                                           ((TK_INVALID
                                                               "unrecognized character"),
                                                             (pos +
                                                                Prims.int_one)))
let rec shexc_tokenize_loop (input : Prims.string) (pos : Prims.nat)
  (acc : shexc_token Prims.list) (fuel : Prims.nat) : shexc_token Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev (TK_EOF :: acc)
  else
    (let pos1 = shexc_ws input pos in
     let len = Parser_FastString.fs_byte_length input in
     if pos1 >= len
     then FStar_List_Tot_Base.rev (TK_EOF :: acc)
     else
       (let uu___2 = shexc_next_token input pos1 in
        match uu___2 with
        | (tok, pos2) ->
            if pos2 <= pos1
            then
              FStar_List_Tot_Base.rev ((TK_INVALID "tokenizer stalled") ::
                acc)
            else
              shexc_tokenize_loop input pos2 (tok :: acc)
                (fuel - Prims.int_one)))
let shexc_tokenize (input : Prims.string) : shexc_token Prims.list=
  shexc_tokenize_loop input Prims.int_zero []
    ((Parser_FastString.fs_byte_length input) + (Prims.of_int (10)))
type 'a sresult =
  | SOk of 'a * shexc_tokens 
  | SErr of Prims.string 
let uu___is_SOk (projectee : 'a sresult) : Prims.bool=
  match projectee with | SOk (v, rest) -> true | uu___ -> false
let __proj__SOk__item__v (projectee : 'a sresult) : 'a=
  match projectee with | SOk (v, rest) -> v
let __proj__SOk__item__rest (projectee : 'a sresult) : shexc_tokens=
  match projectee with | SOk (v, rest) -> rest
let uu___is_SErr (projectee : 'a sresult) : Prims.bool=
  match projectee with | SErr msg -> true | uu___ -> false
let __proj__SErr__item__msg (projectee : 'a sresult) : Prims.string=
  match projectee with | SErr msg -> msg
let resolve_shexc_term (st : Parser_Turtle.turtle_state) (t : shexc_term) :
  Prims.string FStar_Pervasives_Native.option=
  match t with
  | ST_Iri (raw, has_colon) ->
      let r = Parser_Turtle.resolve_iri_hint st raw has_colon in
      if RDF_Term.is_iri r
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
  | ST_PName (ns, local) -> Parser_Turtle.resolve_prefixed_name st ns local
  | ST_BNode label -> FStar_Pervasives_Native.Some (Prims.strcat "_:" label)
let opt_consume (pred : shexc_token -> Prims.bool) (ts : shexc_tokens) :
  (Prims.bool * shexc_tokens)=
  match ts with
  | t::rest -> if pred t then (true, rest) else (false, ts)
  | [] -> (false, ts)
let raw_shexc_term (t : shexc_term) : Prims.string=
  match t with
  | ST_Iri (raw, uu___) -> raw
  | ST_PName (ns, local) -> Prims.strcat ns (Prims.strcat ":" local)
  | ST_BNode label -> Prims.strcat "_:" label
let parse_term (st : Parser_Turtle.turtle_state) (ts : shexc_tokens) :
  Prims.string sresult=
  match ts with
  | (TK_TERM t)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.Some s -> SOk (s, rest)
       | FStar_Pervasives_Native.None ->
           SErr "unresolvable term (undefined prefix?)")
  | uu___ -> SErr "expected an IRI, prefixed name, or blank node"
let rec parse_predicate_list1 (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) : Prims.string Prims.list sresult=
  if fuel = Prims.int_zero
  then SErr "EXTRA predicate list too long"
  else
    (match ts with
     | (TK_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable predicate in EXTRA"
          | FStar_Pervasives_Native.Some s ->
              (match parse_predicate_list1 st rest (fuel - Prims.int_one)
               with
               | SOk (more, rest') -> SOk ((s :: more), rest')
               | SErr uu___1 -> SOk ([s], rest)))
     | uu___1 -> SErr "expected at least one predicate after EXTRA")
let rec parse_semacts (st : Parser_Turtle.turtle_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_sem_act Prims.list sresult=
  if fuel = Prims.int_zero
  then SOk ([], ts)
  else
    (match ts with
     | (TK_SEMACT (name, code))::rest ->
         (match resolve_shexc_term st name with
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable semantic-action extension IRI"
          | FStar_Pervasives_Native.Some n ->
              (match parse_semacts st rest (fuel - Prims.int_one) with
               | SErr m -> SErr m
               | SOk (more, rest') ->
                   SOk
                     (({ ShEx_Schema.sa_name = n; ShEx_Schema.sa_code = code
                       } :: more), rest')))
     | uu___1 -> SOk ([], ts))
let parse_object_value (st : Parser_Turtle.turtle_state) (ts : shexc_tokens)
  : ShEx_Schema.shex_object_value sresult=
  match ts with
  | (TK_STRING s)::(TK_LANGTAG lang)::rest ->
      SOk
        ((ShEx_Schema.ShexOV_Literal
            (s, (FStar_Pervasives_Native.Some lang),
              FStar_Pervasives_Native.None)), rest)
  | (TK_STRING s)::(TK_HATHAT)::(TK_TERM t)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.Some dt ->
           SOk
             ((ShEx_Schema.ShexOV_Literal
                 (s, FStar_Pervasives_Native.None,
                   (FStar_Pervasives_Native.Some dt))), rest)
       | FStar_Pervasives_Native.None -> SErr "unresolvable datatype IRI")
  | (TK_STRING s)::rest ->
      SOk
        ((ShEx_Schema.ShexOV_Literal
            (s, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)),
          rest)
  | (TK_NUMBER (lexeme, dt))::rest ->
      SOk
        ((ShEx_Schema.ShexOV_Literal
            (lexeme, FStar_Pervasives_Native.None,
              (FStar_Pervasives_Native.Some dt))), rest)
  | (TK_KW "TRUE")::rest ->
      SOk
        ((ShEx_Schema.ShexOV_Literal
            ("true", FStar_Pervasives_Native.None,
              (FStar_Pervasives_Native.Some RDF_Term.xsd_boolean))), rest)
  | (TK_KW "FALSE")::rest ->
      SOk
        ((ShEx_Schema.ShexOV_Literal
            ("false", FStar_Pervasives_Native.None,
              (FStar_Pervasives_Native.Some RDF_Term.xsd_boolean))), rest)
  | (TK_TERM t)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.Some iri ->
           SOk ((ShEx_Schema.ShexOV_Iri iri), rest)
       | FStar_Pervasives_Native.None -> SErr "unresolvable IRI value")
  | uu___ -> SErr "expected a value (IRI, literal, or number)"
let rec parse_annotations (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_annotation Prims.list sresult=
  if fuel = Prims.int_zero
  then SOk ([], ts)
  else
    (match ts with
     | (TK_SLASH_ANNOT)::(TK_TERM predt)::rest ->
         (match resolve_shexc_term st predt with
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable annotation predicate"
          | FStar_Pervasives_Native.Some pred ->
              (match parse_object_value st rest with
               | SErr m -> SErr m
               | SOk (obj, rest1) ->
                   (match parse_annotations st rest1 (fuel - Prims.int_one)
                    with
                    | SErr m -> SErr m
                    | SOk (more, rest2) ->
                        SOk
                          (({
                              ShEx_Schema.an_predicate = pred;
                              ShEx_Schema.an_object = obj
                            } :: more), rest2))))
     | uu___1 -> SOk ([], ts))
let parse_exclusion (st : Parser_Turtle.turtle_state)
  (kind : ShEx_Schema.shex_vsv_kind) (ts : shexc_tokens) :
  ShEx_Schema.shex_value_set_value sresult=
  match ts with
  | (TK_MINUS)::rest ->
      let bare_of s = ShEx_Schema.decode_bare_vsv_string kind s in
      (match (kind, rest) with
       | (ShEx_Schema.VSVK_Iri, (TK_TERM t)::(TK_TILDE)::rest') ->
           (match resolve_shexc_term st t with
            | FStar_Pervasives_Native.Some s ->
                SOk
                  ((ShEx_Schema.VSV_IriStem (ShEx_Schema.ShexStemPlain s)),
                    rest')
            | FStar_Pervasives_Native.None ->
                SErr "unresolvable iri exclusion")
       | (ShEx_Schema.VSVK_Iri, (TK_TERM t)::rest') ->
           (match resolve_shexc_term st t with
            | FStar_Pervasives_Native.Some s -> SOk ((bare_of s), rest')
            | FStar_Pervasives_Native.None ->
                SErr "unresolvable iri exclusion")
       | (ShEx_Schema.VSVK_Literal, (TK_STRING s)::(TK_TILDE)::rest') ->
           SOk
             ((ShEx_Schema.VSV_LiteralStem (ShEx_Schema.ShexStemPlain s)),
               rest')
       | (ShEx_Schema.VSVK_Literal, (TK_STRING s)::rest') ->
           SOk ((bare_of s), rest')
       | (ShEx_Schema.VSVK_Language, (TK_LANGTAG s)::(TK_TILDE)::rest') ->
           SOk
             ((ShEx_Schema.VSV_LanguageStem (ShEx_Schema.ShexStemPlain s)),
               rest')
       | (ShEx_Schema.VSVK_Language, (TK_LANGTAG s)::rest') ->
           SOk ((bare_of s), rest')
       | uu___ -> SErr "malformed exclusion in value-set stem range")
  | uu___ -> SErr "expected '-' exclusion"
let rec parse_exclusions (st : Parser_Turtle.turtle_state)
  (kind : ShEx_Schema.shex_vsv_kind) (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_value_set_value Prims.list sresult=
  if fuel = Prims.int_zero
  then SOk ([], ts)
  else
    (match ts with
     | (TK_MINUS)::uu___1 ->
         (match parse_exclusion st kind ts with
          | SErr m -> SErr m
          | SOk (excl, rest) ->
              (match parse_exclusions st kind rest (fuel - Prims.int_one)
               with
               | SErr m -> SErr m
               | SOk (more, rest') -> SOk ((excl :: more), rest')))
     | uu___1 -> SOk ([], ts))
let dot_exclusion_kind (ts : shexc_tokens) : ShEx_Schema.shex_vsv_kind=
  match ts with
  | (TK_MINUS)::(TK_STRING uu___)::uu___1 -> ShEx_Schema.VSVK_Literal
  | (TK_MINUS)::(TK_LANGTAG uu___)::uu___1 -> ShEx_Schema.VSVK_Language
  | uu___ -> ShEx_Schema.VSVK_Iri
let parse_value_set_value (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) : ShEx_Schema.shex_value_set_value sresult=
  match ts with
  | (TK_DOT)::rest ->
      let kind = dot_exclusion_kind rest in
      (match parse_exclusions st kind rest
               ((FStar_List_Tot_Base.length rest) + Prims.int_one)
       with
       | SErr m -> SErr m
       | SOk (excl, rest') ->
           (match excl with
            | [] -> SErr "'.' value-set entry needs at least one exclusion"
            | uu___ ->
                let stem = ShEx_Schema.ShexStemWildcard in
                SOk
                  (((match kind with
                     | ShEx_Schema.VSVK_Iri ->
                         ShEx_Schema.VSV_IriStemRange (stem, excl)
                     | ShEx_Schema.VSVK_Literal ->
                         ShEx_Schema.VSV_LiteralStemRange (stem, excl)
                     | ShEx_Schema.VSVK_Language ->
                         ShEx_Schema.VSV_LanguageStemRange (stem, excl))),
                    rest')))
  | (TK_TERM t)::(TK_TILDE)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.None -> SErr "unresolvable iri stem"
       | FStar_Pervasives_Native.Some s ->
           (match parse_exclusions st ShEx_Schema.VSVK_Iri rest
                    ((FStar_List_Tot_Base.length rest) + Prims.int_one)
            with
            | SErr m -> SErr m
            | SOk ([], rest') ->
                SOk
                  ((ShEx_Schema.VSV_IriStem (ShEx_Schema.ShexStemPlain s)),
                    rest')
            | SOk (excl, rest') ->
                SOk
                  ((ShEx_Schema.VSV_IriStemRange
                      ((ShEx_Schema.ShexStemPlain s), excl)), rest')))
  | (TK_TERM t)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.Some s ->
           SOk ((ShEx_Schema.VSV_Value (ShEx_Schema.ShexOV_Iri s)), rest)
       | FStar_Pervasives_Native.None -> SErr "unresolvable iri value")
  | (TK_STRING s)::(TK_HATHAT)::(TK_TERM t)::(TK_TILDE)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.Some uu___ ->
           SOk
             ((ShEx_Schema.VSV_LiteralStem (ShEx_Schema.ShexStemPlain s)),
               rest)
       | FStar_Pervasives_Native.None -> SErr "unresolvable datatype IRI")
  | (TK_STRING s)::(TK_TILDE)::rest ->
      (match parse_exclusions st ShEx_Schema.VSVK_Literal rest
               ((FStar_List_Tot_Base.length rest) + Prims.int_one)
       with
       | SErr m -> SErr m
       | SOk ([], rest') ->
           SOk
             ((ShEx_Schema.VSV_LiteralStem (ShEx_Schema.ShexStemPlain s)),
               rest')
       | SOk (excl, rest') ->
           SOk
             ((ShEx_Schema.VSV_LiteralStemRange
                 ((ShEx_Schema.ShexStemPlain s), excl)), rest'))
  | (TK_STRING s)::(TK_LANGTAG lang)::rest ->
      SOk
        ((ShEx_Schema.VSV_Value
            (ShEx_Schema.ShexOV_Literal
               (s, (FStar_Pervasives_Native.Some lang),
                 FStar_Pervasives_Native.None))), rest)
  | (TK_STRING s)::(TK_HATHAT)::(TK_TERM t)::rest ->
      (match resolve_shexc_term st t with
       | FStar_Pervasives_Native.Some dt ->
           SOk
             ((ShEx_Schema.VSV_Value
                 (ShEx_Schema.ShexOV_Literal
                    (s, FStar_Pervasives_Native.None,
                      (FStar_Pervasives_Native.Some dt)))), rest)
       | FStar_Pervasives_Native.None -> SErr "unresolvable datatype IRI")
  | (TK_STRING s)::rest ->
      SOk
        ((ShEx_Schema.VSV_Value
            (ShEx_Schema.ShexOV_Literal
               (s, FStar_Pervasives_Native.None,
                 FStar_Pervasives_Native.None))), rest)
  | (TK_NUMBER (lexeme, dt))::rest ->
      SOk
        ((ShEx_Schema.VSV_Value
            (ShEx_Schema.ShexOV_Literal
               (lexeme, FStar_Pervasives_Native.None,
                 (FStar_Pervasives_Native.Some dt)))), rest)
  | (TK_KW "TRUE")::rest ->
      SOk
        ((ShEx_Schema.VSV_Value
            (ShEx_Schema.ShexOV_Literal
               ("true", FStar_Pervasives_Native.None,
                 (FStar_Pervasives_Native.Some RDF_Term.xsd_boolean)))),
          rest)
  | (TK_KW "FALSE")::rest ->
      SOk
        ((ShEx_Schema.VSV_Value
            (ShEx_Schema.ShexOV_Literal
               ("false", FStar_Pervasives_Native.None,
                 (FStar_Pervasives_Native.Some RDF_Term.xsd_boolean)))),
          rest)
  | (TK_LANGTAG lang)::(TK_TILDE)::rest ->
      (match parse_exclusions st ShEx_Schema.VSVK_Language rest
               ((FStar_List_Tot_Base.length rest) + Prims.int_one)
       with
       | SErr m -> SErr m
       | SOk ([], rest') ->
           SOk
             ((ShEx_Schema.VSV_LanguageStem (ShEx_Schema.ShexStemPlain lang)),
               rest')
       | SOk (excl, rest') ->
           SOk
             ((ShEx_Schema.VSV_LanguageStemRange
                 ((ShEx_Schema.ShexStemPlain lang), excl)), rest'))
  | (TK_LANGTAG lang)::rest -> SOk ((ShEx_Schema.VSV_Language lang), rest)
  | uu___ -> SErr "expected a value-set entry"
let rec parse_value_set_values (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_value_set_value Prims.list sresult=
  if fuel = Prims.int_zero
  then SOk ([], ts)
  else
    (match ts with
     | (TK_RBRACKET)::uu___1 -> SOk ([], ts)
     | uu___1 ->
         (match parse_value_set_value st ts with
          | SErr m -> SErr m
          | SOk (v, rest) ->
              (match parse_value_set_values st rest (fuel - Prims.int_one)
               with
               | SErr m -> SErr m
               | SOk (more, rest') -> SOk ((v :: more), rest'))))
let parse_value_set (st : Parser_Turtle.turtle_state) (ts : shexc_tokens) :
  ShEx_Schema.shex_value_set_value Prims.list sresult=
  match ts with
  | (TK_LBRACKET)::rest ->
      (match parse_value_set_values st rest
               ((FStar_List_Tot_Base.length rest) + Prims.int_one)
       with
       | SErr m -> SErr m
       | SOk (vs, rest1) ->
           (match rest1 with
            | (TK_RBRACKET)::rest2 -> SOk (vs, rest2)
            | uu___ -> SErr "expected ']' to close value set"))
  | uu___ -> SErr "expected '['"
let empty_node_constraint : ShEx_Schema.shex_node_constraint=
  {
    ShEx_Schema.nc_node_kind = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_datatype = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_values = [];
    ShEx_Schema.nc_length = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_minlength = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_maxlength = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_pattern = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_flags = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_mininclusive = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_maxinclusive = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_minexclusive = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_maxexclusive = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_totaldigits = FStar_Pervasives_Native.None;
    ShEx_Schema.nc_fractiondigits = FStar_Pervasives_Native.None
  }
let empty_shape : ShEx_Schema.shex_shape=
  {
    ShEx_Schema.sh_closed = false;
    ShEx_Schema.sh_extra = [];
    ShEx_Schema.sh_expression = FStar_Pervasives_Native.None;
    ShEx_Schema.sh_semacts = [];
    ShEx_Schema.sh_annotations = [];
    ShEx_Schema.sh_extends = []
  }
let rec parse_facets (st : Parser_Turtle.turtle_state)
  (nc : ShEx_Schema.shex_node_constraint) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_node_constraint sresult=
  if fuel = Prims.int_zero
  then SOk (nc, ts)
  else
    (match ts with
     | (TK_KW "LENGTH")::(TK_NUMBER (n, uu___1))::rest ->
         (match ShEx_Schema.shex_parse_int_string n with
          | FStar_Pervasives_Native.Some i ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
                  ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
                  ShEx_Schema.nc_length = (FStar_Pervasives_Native.Some i);
                  ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
                  ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
                  ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (nc.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (nc.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (nc.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (nc.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (nc.ShEx_Schema.nc_totaldigits);
                  ShEx_Schema.nc_fractiondigits =
                    (nc.ShEx_Schema.nc_fractiondigits)
                } rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.None -> SErr "LENGTH expects an integer")
     | (TK_KW "MINLENGTH")::(TK_NUMBER (n, uu___1))::rest ->
         (match ShEx_Schema.shex_parse_int_string n with
          | FStar_Pervasives_Native.Some i ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
                  ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
                  ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
                  ShEx_Schema.nc_minlength = (FStar_Pervasives_Native.Some i);
                  ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
                  ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (nc.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (nc.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (nc.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (nc.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (nc.ShEx_Schema.nc_totaldigits);
                  ShEx_Schema.nc_fractiondigits =
                    (nc.ShEx_Schema.nc_fractiondigits)
                } rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.None ->
              SErr "MINLENGTH expects an integer")
     | (TK_KW "MAXLENGTH")::(TK_NUMBER (n, uu___1))::rest ->
         (match ShEx_Schema.shex_parse_int_string n with
          | FStar_Pervasives_Native.Some i ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
                  ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
                  ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
                  ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
                  ShEx_Schema.nc_maxlength = (FStar_Pervasives_Native.Some i);
                  ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (nc.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (nc.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (nc.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (nc.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (nc.ShEx_Schema.nc_totaldigits);
                  ShEx_Schema.nc_fractiondigits =
                    (nc.ShEx_Schema.nc_fractiondigits)
                } rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.None ->
              SErr "MAXLENGTH expects an integer")
     | (TK_KW "TOTALDIGITS")::(TK_NUMBER (n, uu___1))::rest ->
         (match ShEx_Schema.shex_parse_int_string n with
          | FStar_Pervasives_Native.Some i ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
                  ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
                  ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
                  ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
                  ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
                  ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (nc.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (nc.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (nc.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (nc.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (FStar_Pervasives_Native.Some i);
                  ShEx_Schema.nc_fractiondigits =
                    (nc.ShEx_Schema.nc_fractiondigits)
                } rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.None ->
              SErr "TOTALDIGITS expects an integer")
     | (TK_KW "FRACTIONDIGITS")::(TK_NUMBER (n, uu___1))::rest ->
         (match ShEx_Schema.shex_parse_int_string n with
          | FStar_Pervasives_Native.Some i ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
                  ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
                  ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
                  ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
                  ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
                  ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (nc.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (nc.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (nc.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (nc.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (nc.ShEx_Schema.nc_totaldigits);
                  ShEx_Schema.nc_fractiondigits =
                    (FStar_Pervasives_Native.Some i)
                } rest (fuel - Prims.int_one)
          | FStar_Pervasives_Native.None ->
              SErr "FRACTIONDIGITS expects an integer")
     | (TK_KW "MININCLUSIVE")::(TK_NUMBER (n, uu___1))::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
             ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive = (FStar_Pervasives_Native.Some n);
             ShEx_Schema.nc_maxinclusive = (nc.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive = (nc.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive = (nc.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits = (nc.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (nc.ShEx_Schema.nc_fractiondigits)
           } rest (fuel - Prims.int_one)
     | (TK_KW "MAXINCLUSIVE")::(TK_NUMBER (n, uu___1))::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
             ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive = (nc.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive = (FStar_Pervasives_Native.Some n);
             ShEx_Schema.nc_minexclusive = (nc.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive = (nc.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits = (nc.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (nc.ShEx_Schema.nc_fractiondigits)
           } rest (fuel - Prims.int_one)
     | (TK_KW "MINEXCLUSIVE")::(TK_NUMBER (n, uu___1))::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
             ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive = (nc.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive = (nc.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive = (FStar_Pervasives_Native.Some n);
             ShEx_Schema.nc_maxexclusive = (nc.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits = (nc.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (nc.ShEx_Schema.nc_fractiondigits)
           } rest (fuel - Prims.int_one)
     | (TK_KW "MAXEXCLUSIVE")::(TK_NUMBER (n, uu___1))::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
             ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern = (nc.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive = (nc.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive = (nc.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive = (nc.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive = (FStar_Pervasives_Native.Some n);
             ShEx_Schema.nc_totaldigits = (nc.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (nc.ShEx_Schema.nc_fractiondigits)
           } rest (fuel - Prims.int_one)
     | (TK_KW "PATTERN")::(TK_STRING s)::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
             ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern = (FStar_Pervasives_Native.Some s);
             ShEx_Schema.nc_flags = (nc.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive = (nc.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive = (nc.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive = (nc.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive = (nc.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits = (nc.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (nc.ShEx_Schema.nc_fractiondigits)
           } rest (fuel - Prims.int_one)
     | (TK_REGEX (pat, flags))::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind = (nc.ShEx_Schema.nc_node_kind);
             ShEx_Schema.nc_datatype = (nc.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values = (nc.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length = (nc.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength = (nc.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength = (nc.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern = (FStar_Pervasives_Native.Some pat);
             ShEx_Schema.nc_flags =
               (if flags = ""
                then FStar_Pervasives_Native.None
                else FStar_Pervasives_Native.Some flags);
             ShEx_Schema.nc_mininclusive = (nc.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive = (nc.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive = (nc.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive = (nc.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits = (nc.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (nc.ShEx_Schema.nc_fractiondigits)
           } rest (fuel - Prims.int_one)
     | uu___1 -> SOk (nc, ts))
let shexc_grammar_fuel : Prims.nat= (Prims.parse_int "2000000")
let peek_starts_unary (ts : shexc_tokens) : Prims.bool=
  match ts with
  | (TK_DOLLAR)::uu___ -> true
  | (TK_AMP)::uu___ -> true
  | (TK_LPAREN)::uu___ -> true
  | (TK_CARET)::uu___ -> true
  | (TK_TERM uu___)::uu___1 -> true
  | uu___ -> false
let parse_optional_cardinality (ts : shexc_tokens) :
  (Prims.int FStar_Pervasives_Native.option * Prims.int
    FStar_Pervasives_Native.option * shexc_tokens)=
  match ts with
  | (TK_STAR)::rest ->
      ((FStar_Pervasives_Native.Some Prims.int_zero),
        (FStar_Pervasives_Native.Some (Prims.of_int (-1))), rest)
  | (TK_PLUS)::rest ->
      ((FStar_Pervasives_Native.Some Prims.int_one),
        (FStar_Pervasives_Native.Some (Prims.of_int (-1))), rest)
  | (TK_QMARK)::rest ->
      ((FStar_Pervasives_Native.Some Prims.int_zero),
        (FStar_Pervasives_Native.Some Prims.int_one), rest)
  | (TK_REPEAT_RANGE (m, n))::rest ->
      ((FStar_Pervasives_Native.Some m), (FStar_Pervasives_Native.Some n),
        rest)
  | uu___ -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, ts)
let rec parse_shape_expression (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_shape_expr sresult=
  if fuel = Prims.int_zero
  then SErr "shapeExpression recursion limit"
  else parse_shape_or st ts (fuel - Prims.int_one)
and parse_shape_or (st : Parser_Turtle.turtle_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_shape_expr sresult=
  if fuel = Prims.int_zero
  then SErr "shapeOr recursion limit"
  else
    (match parse_shape_and st ts (fuel - Prims.int_one) with
     | SErr m -> SErr m
     | SOk (se, rest) ->
         parse_shape_or_rest st [se] rest (fuel - Prims.int_one))
and parse_shape_or_rest (st : Parser_Turtle.turtle_state)
  (acc : ShEx_Schema.shex_shape_expr Prims.list) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_shape_expr sresult=
  if fuel = Prims.int_zero
  then
    match acc with
    | x::[] -> SOk (x, ts)
    | xs -> SOk ((ShEx_Schema.SE_ShapeOr xs), ts)
  else
    (match ts with
     | (TK_KW "OR")::rest ->
         (match parse_shape_and st rest (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (se, rest') ->
              parse_shape_or_rest st (FStar_List_Tot_Base.op_At acc [se])
                rest' (fuel - Prims.int_one))
     | uu___1 ->
         (match acc with
          | x::[] -> SOk (x, ts)
          | xs -> SOk ((ShEx_Schema.SE_ShapeOr xs), ts)))
and parse_shape_and (st : Parser_Turtle.turtle_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_shape_expr sresult=
  if fuel = Prims.int_zero
  then SErr "shapeAnd recursion limit"
  else
    (match parse_shape_not st ts (fuel - Prims.int_one) with
     | SErr m -> SErr m
     | SOk (xs, rest) ->
         parse_shape_and_rest st xs rest (fuel - Prims.int_one))
and parse_shape_and_rest (st : Parser_Turtle.turtle_state)
  (acc : ShEx_Schema.shex_shape_expr Prims.list) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_shape_expr sresult=
  if fuel = Prims.int_zero
  then
    match acc with
    | x::[] -> SOk (x, ts)
    | xs -> SOk ((ShEx_Schema.SE_ShapeAnd xs), ts)
  else
    (match ts with
     | (TK_KW "AND")::rest ->
         (match parse_shape_not st rest (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (xs, rest') ->
              parse_shape_and_rest st (FStar_List_Tot_Base.op_At acc xs)
                rest' (fuel - Prims.int_one))
     | uu___1 ->
         (match acc with
          | x::[] -> SOk (x, ts)
          | xs -> SOk ((ShEx_Schema.SE_ShapeAnd xs), ts)))
and parse_shape_not (st : Parser_Turtle.turtle_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_shape_expr Prims.list sresult=
  if fuel = Prims.int_zero
  then SErr "shapeNot recursion limit"
  else
    (match ts with
     | (TK_KW "NOT")::rest ->
         (match parse_shape_atom st rest (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (xs, rest') ->
              let flattened =
                match xs with
                | x::[] -> x
                | uu___1 -> ShEx_Schema.SE_ShapeAnd xs in
              SOk ([ShEx_Schema.SE_ShapeNot flattened], rest'))
     | uu___1 -> parse_shape_atom st ts (fuel - Prims.int_one))
and parse_shape_atom (st : Parser_Turtle.turtle_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_shape_expr Prims.list sresult=
  if fuel = Prims.int_zero
  then SErr "shapeAtom recursion limit"
  else
    (match ts with
     | (TK_LPAREN)::rest ->
         (match parse_shape_expression st rest (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (se, rest') ->
              (match rest' with
               | (TK_RPAREN)::rest'' -> SOk ([se], rest'')
               | uu___1 -> SErr "expected ')'"))
     | (TK_DOT)::rest -> SOk ([ShEx_Schema.SE_Shape empty_shape], rest)
     | (TK_AT_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None -> SErr "unresolvable shapeRef"
          | FStar_Pervasives_Native.Some s ->
              SOk ([ShEx_Schema.SE_Ref s], rest))
     | (TK_AT)::(TK_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None -> SErr "unresolvable shapeRef"
          | FStar_Pervasives_Native.Some s ->
              SOk ([ShEx_Schema.SE_Ref s], rest))
     | (TK_KW "EXTERNAL")::rest -> SOk ([ShEx_Schema.SE_ShapeExternal], rest)
     | (TK_KW "IRI")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "BNODE")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "NONLITERAL")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "LITERAL")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_LBRACKET)::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "LENGTH")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "MINLENGTH")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "MAXLENGTH")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "PATTERN")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_REGEX (uu___1, uu___2))::uu___3 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_TERM uu___1)::uu___2 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "MININCLUSIVE")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "MAXINCLUSIVE")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "MINEXCLUSIVE")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "MAXEXCLUSIVE")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "TOTALDIGITS")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "FRACTIONDIGITS")::uu___1 ->
         parse_node_constraint_or_shape st ts (fuel - Prims.int_one)
     | (TK_KW "CLOSED")::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) -> SOk ([ShEx_Schema.SE_Shape sh], rest))
     | (TK_KW "EXTRA")::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) -> SOk ([ShEx_Schema.SE_Shape sh], rest))
     | (TK_KW "EXTENDS")::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) -> SOk ([ShEx_Schema.SE_Shape sh], rest))
     | (TK_LBRACE)::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) -> SOk ([ShEx_Schema.SE_Shape sh], rest))
     | uu___1 -> SErr "expected a shape expression")
and parse_node_constraint_or_shape (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_shape_expr Prims.list sresult=
  if fuel = Prims.int_zero
  then SErr "nodeConstraint recursion limit"
  else
    (match parse_node_constraint_only st ts (fuel - Prims.int_one) with
     | SErr m -> SErr m
     | SOk (nc, rest) ->
         (match parse_optional_shape_or_ref_suffix st rest
                  (fuel - Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (FStar_Pervasives_Native.None, rest') ->
              SOk ([ShEx_Schema.SE_NodeConstraint nc], rest')
          | SOk (FStar_Pervasives_Native.Some se, rest') ->
              SOk ([ShEx_Schema.SE_NodeConstraint nc; se], rest')))
and parse_node_constraint_only (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_node_constraint sresult=
  if fuel = Prims.int_zero
  then SErr "nodeConstraint recursion limit"
  else
    (match ts with
     | (TK_KW "IRI")::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind =
               (FStar_Pervasives_Native.Some ShEx_Schema.ShexNK_Iri);
             ShEx_Schema.nc_datatype =
               (empty_node_constraint.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values =
               (empty_node_constraint.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length =
               (empty_node_constraint.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength =
               (empty_node_constraint.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength =
               (empty_node_constraint.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern =
               (empty_node_constraint.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags =
               (empty_node_constraint.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive =
               (empty_node_constraint.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive =
               (empty_node_constraint.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits =
               (empty_node_constraint.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (empty_node_constraint.ShEx_Schema.nc_fractiondigits)
           } rest ((FStar_List_Tot_Base.length rest) + Prims.int_one)
     | (TK_KW "BNODE")::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind =
               (FStar_Pervasives_Native.Some ShEx_Schema.ShexNK_BNode);
             ShEx_Schema.nc_datatype =
               (empty_node_constraint.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values =
               (empty_node_constraint.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length =
               (empty_node_constraint.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength =
               (empty_node_constraint.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength =
               (empty_node_constraint.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern =
               (empty_node_constraint.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags =
               (empty_node_constraint.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive =
               (empty_node_constraint.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive =
               (empty_node_constraint.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits =
               (empty_node_constraint.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (empty_node_constraint.ShEx_Schema.nc_fractiondigits)
           } rest ((FStar_List_Tot_Base.length rest) + Prims.int_one)
     | (TK_KW "NONLITERAL")::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind =
               (FStar_Pervasives_Native.Some ShEx_Schema.ShexNK_NonLiteral);
             ShEx_Schema.nc_datatype =
               (empty_node_constraint.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values =
               (empty_node_constraint.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length =
               (empty_node_constraint.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength =
               (empty_node_constraint.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength =
               (empty_node_constraint.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern =
               (empty_node_constraint.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags =
               (empty_node_constraint.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive =
               (empty_node_constraint.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive =
               (empty_node_constraint.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits =
               (empty_node_constraint.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (empty_node_constraint.ShEx_Schema.nc_fractiondigits)
           } rest ((FStar_List_Tot_Base.length rest) + Prims.int_one)
     | (TK_KW "LITERAL")::rest ->
         parse_facets st
           {
             ShEx_Schema.nc_node_kind =
               (FStar_Pervasives_Native.Some ShEx_Schema.ShexNK_Literal);
             ShEx_Schema.nc_datatype =
               (empty_node_constraint.ShEx_Schema.nc_datatype);
             ShEx_Schema.nc_values =
               (empty_node_constraint.ShEx_Schema.nc_values);
             ShEx_Schema.nc_length =
               (empty_node_constraint.ShEx_Schema.nc_length);
             ShEx_Schema.nc_minlength =
               (empty_node_constraint.ShEx_Schema.nc_minlength);
             ShEx_Schema.nc_maxlength =
               (empty_node_constraint.ShEx_Schema.nc_maxlength);
             ShEx_Schema.nc_pattern =
               (empty_node_constraint.ShEx_Schema.nc_pattern);
             ShEx_Schema.nc_flags =
               (empty_node_constraint.ShEx_Schema.nc_flags);
             ShEx_Schema.nc_mininclusive =
               (empty_node_constraint.ShEx_Schema.nc_mininclusive);
             ShEx_Schema.nc_maxinclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxinclusive);
             ShEx_Schema.nc_minexclusive =
               (empty_node_constraint.ShEx_Schema.nc_minexclusive);
             ShEx_Schema.nc_maxexclusive =
               (empty_node_constraint.ShEx_Schema.nc_maxexclusive);
             ShEx_Schema.nc_totaldigits =
               (empty_node_constraint.ShEx_Schema.nc_totaldigits);
             ShEx_Schema.nc_fractiondigits =
               (empty_node_constraint.ShEx_Schema.nc_fractiondigits)
           } rest ((FStar_List_Tot_Base.length rest) + Prims.int_one)
     | (TK_LBRACKET)::uu___1 ->
         (match parse_value_set st ts with
          | SErr m -> SErr m
          | SOk (vs, rest) ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind =
                    (empty_node_constraint.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype =
                    (empty_node_constraint.ShEx_Schema.nc_datatype);
                  ShEx_Schema.nc_values = vs;
                  ShEx_Schema.nc_length =
                    (empty_node_constraint.ShEx_Schema.nc_length);
                  ShEx_Schema.nc_minlength =
                    (empty_node_constraint.ShEx_Schema.nc_minlength);
                  ShEx_Schema.nc_maxlength =
                    (empty_node_constraint.ShEx_Schema.nc_maxlength);
                  ShEx_Schema.nc_pattern =
                    (empty_node_constraint.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags =
                    (empty_node_constraint.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (empty_node_constraint.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (empty_node_constraint.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (empty_node_constraint.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (empty_node_constraint.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (empty_node_constraint.ShEx_Schema.nc_totaldigits);
                  ShEx_Schema.nc_fractiondigits =
                    (empty_node_constraint.ShEx_Schema.nc_fractiondigits)
                } rest ((FStar_List_Tot_Base.length rest) + Prims.int_one))
     | (TK_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None -> SErr "unresolvable datatype IRI"
          | FStar_Pervasives_Native.Some dt ->
              parse_facets st
                {
                  ShEx_Schema.nc_node_kind =
                    (empty_node_constraint.ShEx_Schema.nc_node_kind);
                  ShEx_Schema.nc_datatype = (FStar_Pervasives_Native.Some dt);
                  ShEx_Schema.nc_values =
                    (empty_node_constraint.ShEx_Schema.nc_values);
                  ShEx_Schema.nc_length =
                    (empty_node_constraint.ShEx_Schema.nc_length);
                  ShEx_Schema.nc_minlength =
                    (empty_node_constraint.ShEx_Schema.nc_minlength);
                  ShEx_Schema.nc_maxlength =
                    (empty_node_constraint.ShEx_Schema.nc_maxlength);
                  ShEx_Schema.nc_pattern =
                    (empty_node_constraint.ShEx_Schema.nc_pattern);
                  ShEx_Schema.nc_flags =
                    (empty_node_constraint.ShEx_Schema.nc_flags);
                  ShEx_Schema.nc_mininclusive =
                    (empty_node_constraint.ShEx_Schema.nc_mininclusive);
                  ShEx_Schema.nc_maxinclusive =
                    (empty_node_constraint.ShEx_Schema.nc_maxinclusive);
                  ShEx_Schema.nc_minexclusive =
                    (empty_node_constraint.ShEx_Schema.nc_minexclusive);
                  ShEx_Schema.nc_maxexclusive =
                    (empty_node_constraint.ShEx_Schema.nc_maxexclusive);
                  ShEx_Schema.nc_totaldigits =
                    (empty_node_constraint.ShEx_Schema.nc_totaldigits);
                  ShEx_Schema.nc_fractiondigits =
                    (empty_node_constraint.ShEx_Schema.nc_fractiondigits)
                } rest ((FStar_List_Tot_Base.length rest) + Prims.int_one))
     | uu___1 ->
         (match parse_facets st empty_node_constraint ts
                  ((FStar_List_Tot_Base.length ts) + Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (nc, rest) ->
              if
                (FStar_List_Tot_Base.length rest) =
                  (FStar_List_Tot_Base.length ts)
              then SErr "expected a node constraint"
              else SOk (nc, rest)))
and parse_optional_shape_or_ref_suffix (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_shape_expr FStar_Pervasives_Native.option sresult=
  if fuel = Prims.int_zero
  then SErr "shapeOrRef suffix recursion limit"
  else
    (match ts with
     | (TK_AT_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None -> SErr "unresolvable shapeRef"
          | FStar_Pervasives_Native.Some s ->
              SOk
                ((FStar_Pervasives_Native.Some (ShEx_Schema.SE_Ref s)), rest))
     | (TK_AT)::(TK_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None -> SErr "unresolvable shapeRef"
          | FStar_Pervasives_Native.Some s ->
              SOk
                ((FStar_Pervasives_Native.Some (ShEx_Schema.SE_Ref s)), rest))
     | (TK_KW "CLOSED")::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) ->
              SOk
                ((FStar_Pervasives_Native.Some (ShEx_Schema.SE_Shape sh)),
                  rest))
     | (TK_KW "EXTRA")::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) ->
              SOk
                ((FStar_Pervasives_Native.Some (ShEx_Schema.SE_Shape sh)),
                  rest))
     | (TK_KW "EXTENDS")::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) ->
              SOk
                ((FStar_Pervasives_Native.Some (ShEx_Schema.SE_Shape sh)),
                  rest))
     | (TK_LBRACE)::uu___1 ->
         (match parse_shape_definition st ts (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (sh, rest) ->
              SOk
                ((FStar_Pervasives_Native.Some (ShEx_Schema.SE_Shape sh)),
                  rest))
     | uu___1 -> SOk (FStar_Pervasives_Native.None, ts))
and parse_shape_definition (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) : ShEx_Schema.shex_shape sresult=
  if fuel = Prims.int_zero
  then SErr "shapeDefinition recursion limit"
  else parse_shape_modifiers st false [] [] ts (fuel - Prims.int_one)
and parse_shape_modifiers (st : Parser_Turtle.turtle_state)
  (closed : Prims.bool) (extra : Prims.string Prims.list)
  (extends : Prims.string Prims.list) (ts : shexc_tokens) (fuel : Prims.nat)
  : ShEx_Schema.shex_shape sresult=
  if fuel = Prims.int_zero
  then SErr "shapeDefinition modifier recursion limit"
  else
    (match ts with
     | (TK_KW "CLOSED")::rest ->
         parse_shape_modifiers st true extra extends rest
           (fuel - Prims.int_one)
     | (TK_KW "EXTRA")::rest ->
         (match parse_predicate_list1 st rest
                  ((FStar_List_Tot_Base.length rest) + Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (preds, rest') ->
              parse_shape_modifiers st closed
                (FStar_List_Tot_Base.op_At extra preds) extends rest'
                (fuel - Prims.int_one))
     | (TK_KW "EXTENDS")::(TK_AT_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable EXTENDS target"
          | FStar_Pervasives_Native.Some s ->
              parse_shape_modifiers st closed extra
                (FStar_List_Tot_Base.op_At extends [s]) rest
                (fuel - Prims.int_one))
     | (TK_KW "EXTENDS")::(TK_AT)::(TK_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable EXTENDS target"
          | FStar_Pervasives_Native.Some s ->
              parse_shape_modifiers st closed extra
                (FStar_List_Tot_Base.op_At extends [s]) rest
                (fuel - Prims.int_one))
     | (TK_LBRACE)::rest ->
         (match rest with
          | (TK_RBRACE)::rest1 ->
              (match parse_annotations st rest1
                       ((FStar_List_Tot_Base.length rest1) + Prims.int_one)
               with
               | SErr m -> SErr m
               | SOk (annots, rest2) ->
                   (match parse_semacts st rest2
                            ((FStar_List_Tot_Base.length rest2) +
                               Prims.int_one)
                    with
                    | SErr m -> SErr m
                    | SOk (semacts, rest3) ->
                        SOk
                          ({
                             ShEx_Schema.sh_closed = closed;
                             ShEx_Schema.sh_extra = extra;
                             ShEx_Schema.sh_expression =
                               FStar_Pervasives_Native.None;
                             ShEx_Schema.sh_semacts = semacts;
                             ShEx_Schema.sh_annotations = annots;
                             ShEx_Schema.sh_extends = extends
                           }, rest3)))
          | uu___1 ->
              (match parse_one_of_triple_expr st rest (fuel - Prims.int_one)
               with
               | SErr m -> SErr m
               | SOk (te, rest1) ->
                   (match rest1 with
                    | (TK_RBRACE)::rest2 ->
                        (match parse_annotations st rest2
                                 ((FStar_List_Tot_Base.length rest2) +
                                    Prims.int_one)
                         with
                         | SErr m -> SErr m
                         | SOk (annots, rest3) ->
                             (match parse_semacts st rest3
                                      ((FStar_List_Tot_Base.length rest3) +
                                         Prims.int_one)
                              with
                              | SErr m -> SErr m
                              | SOk (semacts, rest4) ->
                                  SOk
                                    ({
                                       ShEx_Schema.sh_closed = closed;
                                       ShEx_Schema.sh_extra = extra;
                                       ShEx_Schema.sh_expression =
                                         (FStar_Pervasives_Native.Some te);
                                       ShEx_Schema.sh_semacts = semacts;
                                       ShEx_Schema.sh_annotations = annots;
                                       ShEx_Schema.sh_extends = extends
                                     }, rest4)))
                    | uu___2 -> SErr "expected '}' to close shape body")))
     | uu___1 ->
         SErr "expected CLOSED / EXTRA / EXTENDS / '{' in shape definition")
and parse_one_of_triple_expr (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_triple_expr sresult=
  if fuel = Prims.int_zero
  then SErr "oneOfTripleExpr recursion limit"
  else
    (match parse_group_triple_expr st ts (fuel - Prims.int_one) with
     | SErr m -> SErr m
     | SOk (te, rest) ->
         parse_one_of_rest st [te] rest (fuel - Prims.int_one))
and parse_one_of_rest (st : Parser_Turtle.turtle_state)
  (acc : ShEx_Schema.shex_triple_expr Prims.list) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_triple_expr sresult=
  if fuel = Prims.int_zero
  then
    match acc with
    | x::[] -> SOk (x, ts)
    | uu___ ->
        SOk
          ((ShEx_Schema.TE_OneOf
              {
                ShEx_Schema.gr_id = FStar_Pervasives_Native.None;
                ShEx_Schema.gr_expressions = (FStar_List_Tot_Base.rev acc);
                ShEx_Schema.gr_min = FStar_Pervasives_Native.None;
                ShEx_Schema.gr_max = FStar_Pervasives_Native.None;
                ShEx_Schema.gr_semacts = [];
                ShEx_Schema.gr_annotations = []
              }), ts)
  else
    (match ts with
     | (TK_PIPE)::rest ->
         (match parse_group_triple_expr st rest (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (te, rest') ->
              parse_one_of_rest st (te :: acc) rest' (fuel - Prims.int_one))
     | uu___1 ->
         (match FStar_List_Tot_Base.rev acc with
          | x::[] -> SOk (x, ts)
          | xs ->
              SOk
                ((ShEx_Schema.TE_OneOf
                    {
                      ShEx_Schema.gr_id = FStar_Pervasives_Native.None;
                      ShEx_Schema.gr_expressions = xs;
                      ShEx_Schema.gr_min = FStar_Pervasives_Native.None;
                      ShEx_Schema.gr_max = FStar_Pervasives_Native.None;
                      ShEx_Schema.gr_semacts = [];
                      ShEx_Schema.gr_annotations = []
                    }), ts)))
and parse_group_triple_expr (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_triple_expr sresult=
  if fuel = Prims.int_zero
  then SErr "groupTripleExpr recursion limit"
  else
    (match parse_unary_triple_expr st ts (fuel - Prims.int_one) with
     | SErr m -> SErr m
     | SOk (te, rest) -> parse_group_rest st [te] rest (fuel - Prims.int_one))
and parse_group_rest (st : Parser_Turtle.turtle_state)
  (acc : ShEx_Schema.shex_triple_expr Prims.list) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_triple_expr sresult=
  if fuel = Prims.int_zero
  then
    match acc with
    | x::[] -> SOk (x, ts)
    | xs ->
        SOk
          ((ShEx_Schema.TE_EachOf
              {
                ShEx_Schema.gr_id = FStar_Pervasives_Native.None;
                ShEx_Schema.gr_expressions = (FStar_List_Tot_Base.rev xs);
                ShEx_Schema.gr_min = FStar_Pervasives_Native.None;
                ShEx_Schema.gr_max = FStar_Pervasives_Native.None;
                ShEx_Schema.gr_semacts = [];
                ShEx_Schema.gr_annotations = []
              }), ts)
  else
    (match ts with
     | (TK_SEMI)::rest ->
         if peek_starts_unary rest
         then
           (match parse_unary_triple_expr st rest (fuel - Prims.int_one) with
            | SErr m -> SErr m
            | SOk (te, rest') ->
                parse_group_rest st (te :: acc) rest' (fuel - Prims.int_one))
         else
           (match FStar_List_Tot_Base.rev acc with
            | x::[] -> SOk (x, rest)
            | xs ->
                SOk
                  ((ShEx_Schema.TE_EachOf
                      {
                        ShEx_Schema.gr_id = FStar_Pervasives_Native.None;
                        ShEx_Schema.gr_expressions = xs;
                        ShEx_Schema.gr_min = FStar_Pervasives_Native.None;
                        ShEx_Schema.gr_max = FStar_Pervasives_Native.None;
                        ShEx_Schema.gr_semacts = [];
                        ShEx_Schema.gr_annotations = []
                      }), rest))
     | uu___1 ->
         (match FStar_List_Tot_Base.rev acc with
          | x::[] -> SOk (x, ts)
          | xs ->
              SOk
                ((ShEx_Schema.TE_EachOf
                    {
                      ShEx_Schema.gr_id = FStar_Pervasives_Native.None;
                      ShEx_Schema.gr_expressions = xs;
                      ShEx_Schema.gr_min = FStar_Pervasives_Native.None;
                      ShEx_Schema.gr_max = FStar_Pervasives_Native.None;
                      ShEx_Schema.gr_semacts = [];
                      ShEx_Schema.gr_annotations = []
                    }), ts)))
and parse_unary_triple_expr (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_triple_expr sresult=
  if fuel = Prims.int_zero
  then SErr "unaryTripleExpr recursion limit"
  else
    (match ts with
     | (TK_AMP)::(TK_AT_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.Some s ->
              SOk ((ShEx_Schema.TE_Ref s), rest)
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable include target")
     | (TK_AMP)::(TK_TERM t)::rest ->
         (match resolve_shexc_term st t with
          | FStar_Pervasives_Native.Some s ->
              SOk ((ShEx_Schema.TE_Ref s), rest)
          | FStar_Pervasives_Native.None ->
              SErr "unresolvable include target")
     | (TK_DOLLAR)::rest ->
         (match rest with
          | (TK_TERM t)::rest1 ->
              (match resolve_shexc_term st t with
               | FStar_Pervasives_Native.None ->
                   SErr "unresolvable triple-expression label"
               | FStar_Pervasives_Native.Some label ->
                   parse_unary_body st (FStar_Pervasives_Native.Some label)
                     rest1 (fuel - Prims.int_one))
          | uu___1 -> SErr "expected label after '$'")
     | uu___1 ->
         parse_unary_body st FStar_Pervasives_Native.None ts
           (fuel - Prims.int_one))
and parse_unary_body (st : Parser_Turtle.turtle_state)
  (label : Prims.string FStar_Pervasives_Native.option) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_triple_expr sresult=
  if fuel = Prims.int_zero
  then SErr "unaryTripleExpr body recursion limit"
  else
    (match ts with
     | (TK_LPAREN)::rest ->
         (match parse_one_of_triple_expr st rest (fuel - Prims.int_one) with
          | SErr m -> SErr m
          | SOk (inner, rest1) ->
              (match rest1 with
               | (TK_RPAREN)::rest2 ->
                   let uu___1 = parse_optional_cardinality rest2 in
                   (match uu___1 with
                    | (card_min, card_max, rest3) ->
                        (match parse_annotations st rest3
                                 ((FStar_List_Tot_Base.length rest3) +
                                    Prims.int_one)
                         with
                         | SErr m -> SErr m
                         | SOk (annots, rest4) ->
                             (match parse_semacts st rest4
                                      ((FStar_List_Tot_Base.length rest4) +
                                         Prims.int_one)
                              with
                              | SErr m -> SErr m
                              | SOk (semacts, rest5) ->
                                  let bare_passthrough =
                                    (((match (card_min, card_max) with
                                       | (FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None) ->
                                           true
                                       | uu___2 -> false) &&
                                        (label = FStar_Pervasives_Native.None))
                                       && (annots = []))
                                      && (semacts = []) in
                                  if bare_passthrough
                                  then SOk (inner, rest5)
                                  else
                                    (match inner with
                                     | ShEx_Schema.TE_EachOf g ->
                                         SOk
                                           ((ShEx_Schema.TE_EachOf
                                               {
                                                 ShEx_Schema.gr_id = label;
                                                 ShEx_Schema.gr_expressions =
                                                   (g.ShEx_Schema.gr_expressions);
                                                 ShEx_Schema.gr_min =
                                                   card_min;
                                                 ShEx_Schema.gr_max =
                                                   card_max;
                                                 ShEx_Schema.gr_semacts =
                                                   semacts;
                                                 ShEx_Schema.gr_annotations =
                                                   annots
                                               }), rest5)
                                     | ShEx_Schema.TE_OneOf g ->
                                         SOk
                                           ((ShEx_Schema.TE_OneOf
                                               {
                                                 ShEx_Schema.gr_id = label;
                                                 ShEx_Schema.gr_expressions =
                                                   (g.ShEx_Schema.gr_expressions);
                                                 ShEx_Schema.gr_min =
                                                   card_min;
                                                 ShEx_Schema.gr_max =
                                                   card_max;
                                                 ShEx_Schema.gr_semacts =
                                                   semacts;
                                                 ShEx_Schema.gr_annotations =
                                                   annots
                                               }), rest5)
                                     | uu___3 ->
                                         let g =
                                           {
                                             ShEx_Schema.gr_id = label;
                                             ShEx_Schema.gr_expressions =
                                               [inner];
                                             ShEx_Schema.gr_min = card_min;
                                             ShEx_Schema.gr_max = card_max;
                                             ShEx_Schema.gr_semacts = semacts;
                                             ShEx_Schema.gr_annotations =
                                               annots
                                           } in
                                         SOk
                                           ((ShEx_Schema.TE_EachOf g), rest5)))))
               | uu___1 ->
                   SErr "expected ')' to close bracketed triple expression"))
     | uu___1 ->
         (match parse_triple_constraint st label ts (fuel - Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (tc, rest) ->
              SOk ((ShEx_Schema.TE_TripleConstraint tc), rest)))
and parse_triple_constraint (st : Parser_Turtle.turtle_state)
  (label : Prims.string FStar_Pervasives_Native.option) (ts : shexc_tokens)
  (fuel : Prims.nat) : ShEx_Schema.shex_triple_constraint sresult=
  if fuel = Prims.int_zero
  then SErr "tripleConstraint recursion limit"
  else
    (let uu___1 = opt_consume (fun t -> t = TK_CARET) ts in
     match uu___1 with
     | (inverse, ts1) ->
         (match ts1 with
          | (TK_TERM t)::rest ->
              (match resolve_shexc_term st t with
               | FStar_Pervasives_Native.None ->
                   SErr "unresolvable predicate"
               | FStar_Pervasives_Native.Some pred ->
                   (match parse_triple_constraint_value_expr st rest
                            (fuel - Prims.int_one)
                    with
                    | SErr m -> SErr m
                    | SOk (value_expr_opt, rest1) ->
                        let uu___2 = parse_optional_cardinality rest1 in
                        (match uu___2 with
                         | (card_min, card_max, rest2) ->
                             (match parse_annotations st rest2
                                      ((FStar_List_Tot_Base.length rest2) +
                                         Prims.int_one)
                              with
                              | SErr m -> SErr m
                              | SOk (annots, rest3) ->
                                  (match parse_semacts st rest3
                                           ((FStar_List_Tot_Base.length rest3)
                                              + Prims.int_one)
                                   with
                                   | SErr m -> SErr m
                                   | SOk (semacts, rest4) ->
                                       SOk
                                         ({
                                            ShEx_Schema.tc_id = label;
                                            ShEx_Schema.tc_inverse = inverse;
                                            ShEx_Schema.tc_predicate = pred;
                                            ShEx_Schema.tc_value_expr =
                                              value_expr_opt;
                                            ShEx_Schema.tc_min =
                                              ((match card_min with
                                                | FStar_Pervasives_Native.Some
                                                    m -> m
                                                | FStar_Pervasives_Native.None
                                                    -> Prims.int_one));
                                            ShEx_Schema.tc_max =
                                              ((match card_max with
                                                | FStar_Pervasives_Native.Some
                                                    m -> m
                                                | FStar_Pervasives_Native.None
                                                    -> Prims.int_one));
                                            ShEx_Schema.tc_semacts = semacts;
                                            ShEx_Schema.tc_annotations =
                                              annots
                                          }, rest4))))))
          | uu___2 -> SErr "expected a predicate"))
and parse_triple_constraint_value_expr (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_shape_expr FStar_Pervasives_Native.option sresult=
  if fuel = Prims.int_zero
  then SErr "tripleConstraint value recursion limit"
  else
    (match ts with
     | (TK_DOT)::(TK_KW "AND")::uu___1 ->
         (match parse_inline_shape_expression st ts (fuel - Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (ve, rest) -> SOk ((FStar_Pervasives_Native.Some ve), rest))
     | (TK_DOT)::(TK_KW "OR")::uu___1 ->
         (match parse_inline_shape_expression st ts (fuel - Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (ve, rest) -> SOk ((FStar_Pervasives_Native.Some ve), rest))
     | (TK_DOT)::after_dot -> SOk (FStar_Pervasives_Native.None, after_dot)
     | uu___1 ->
         (match parse_inline_shape_expression st ts (fuel - Prims.int_one)
          with
          | SErr m -> SErr m
          | SOk (ve, rest) -> SOk ((FStar_Pervasives_Native.Some ve), rest)))
and parse_inline_shape_expression (st : Parser_Turtle.turtle_state)
  (ts : shexc_tokens) (fuel : Prims.nat) :
  ShEx_Schema.shex_shape_expr sresult=
  if fuel = Prims.int_zero
  then SErr "inlineShapeExpression recursion limit"
  else parse_shape_or st ts (fuel - Prims.int_one)
type shexc_parse_state =
  {
  ps_turtle: Parser_Turtle.turtle_state ;
  ps_start: ShEx_Schema.shex_shape_expr FStar_Pervasives_Native.option ;
  ps_start_acts: ShEx_Schema.shex_sem_act Prims.list ;
  ps_shapes: ShEx_Schema.shex_shape_decl Prims.list ;
  ps_imports: Prims.string Prims.list }
let __proj__Mkshexc_parse_state__item__ps_turtle
  (projectee : shexc_parse_state) : Parser_Turtle.turtle_state=
  match projectee with
  | { ps_turtle; ps_start; ps_start_acts; ps_shapes; ps_imports;_} ->
      ps_turtle
let __proj__Mkshexc_parse_state__item__ps_start
  (projectee : shexc_parse_state) :
  ShEx_Schema.shex_shape_expr FStar_Pervasives_Native.option=
  match projectee with
  | { ps_turtle; ps_start; ps_start_acts; ps_shapes; ps_imports;_} ->
      ps_start
let __proj__Mkshexc_parse_state__item__ps_start_acts
  (projectee : shexc_parse_state) : ShEx_Schema.shex_sem_act Prims.list=
  match projectee with
  | { ps_turtle; ps_start; ps_start_acts; ps_shapes; ps_imports;_} ->
      ps_start_acts
let __proj__Mkshexc_parse_state__item__ps_shapes
  (projectee : shexc_parse_state) : ShEx_Schema.shex_shape_decl Prims.list=
  match projectee with
  | { ps_turtle; ps_start; ps_start_acts; ps_shapes; ps_imports;_} ->
      ps_shapes
let __proj__Mkshexc_parse_state__item__ps_imports
  (projectee : shexc_parse_state) : Prims.string Prims.list=
  match projectee with
  | { ps_turtle; ps_start; ps_start_acts; ps_shapes; ps_imports;_} ->
      ps_imports
let sc_is_directive_start (t : shexc_token) : Prims.bool=
  ((t = (TK_KW "PREFIX")) || (t = (TK_KW "BASE"))) || (t = (TK_KW "IMPORT"))
let rec parse_directives (ps : shexc_parse_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : shexc_parse_state sresult=
  if fuel = Prims.int_zero
  then SOk (ps, ts)
  else
    (match ts with
     | (TK_KW "PREFIX")::(TK_TERM (ST_PName (ns, "")))::(TK_TERM t)::rest ->
         (match t with
          | ST_Iri (raw, has_colon) ->
              let iri_val =
                Parser_Turtle.resolve_iri_hint ps.ps_turtle raw has_colon in
              let st' =
                let uu___1 = ps.ps_turtle in
                {
                  Parser_Turtle.prefixes = ((ns, iri_val) ::
                    ((ps.ps_turtle).Parser_Turtle.prefixes));
                  Parser_Turtle.base_iri = (uu___1.Parser_Turtle.base_iri);
                  Parser_Turtle.bnode_counter =
                    (uu___1.Parser_Turtle.bnode_counter)
                } in
              parse_directives
                {
                  ps_turtle = st';
                  ps_start = (ps.ps_start);
                  ps_start_acts = (ps.ps_start_acts);
                  ps_shapes = (ps.ps_shapes);
                  ps_imports = (ps.ps_imports)
                } rest (fuel - Prims.int_one)
          | uu___1 -> SErr "PREFIX expects an IRIREF")
     | (TK_KW "BASE")::(TK_TERM t)::rest ->
         (match t with
          | ST_Iri (raw, has_colon) ->
              let iri_val =
                Parser_Turtle.resolve_iri_hint ps.ps_turtle raw has_colon in
              let st' =
                let uu___1 = ps.ps_turtle in
                {
                  Parser_Turtle.prefixes = (uu___1.Parser_Turtle.prefixes);
                  Parser_Turtle.base_iri = iri_val;
                  Parser_Turtle.bnode_counter =
                    (uu___1.Parser_Turtle.bnode_counter)
                } in
              parse_directives
                {
                  ps_turtle = st';
                  ps_start = (ps.ps_start);
                  ps_start_acts = (ps.ps_start_acts);
                  ps_shapes = (ps.ps_shapes);
                  ps_imports = (ps.ps_imports)
                } rest (fuel - Prims.int_one)
          | uu___1 -> SErr "BASE expects an IRIREF")
     | (TK_KW "IMPORT")::(TK_TERM t)::rest ->
         parse_directives
           {
             ps_turtle = (ps.ps_turtle);
             ps_start = (ps.ps_start);
             ps_start_acts = (ps.ps_start_acts);
             ps_shapes = (ps.ps_shapes);
             ps_imports =
               (FStar_List_Tot_Base.op_At ps.ps_imports [raw_shexc_term t])
           } rest (fuel - Prims.int_one)
     | uu___1 -> SOk (ps, ts))
let parse_statement (ps : shexc_parse_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : shexc_parse_state sresult=
  match ts with
  | (TK_SEMACT (uu___, uu___1))::uu___2 ->
      (match parse_semacts ps.ps_turtle ts
               ((FStar_List_Tot_Base.length ts) + Prims.int_one)
       with
       | SErr m -> SErr m
       | SOk (sa, rest) ->
           SOk
             ({
                ps_turtle = (ps.ps_turtle);
                ps_start = (ps.ps_start);
                ps_start_acts =
                  (FStar_List_Tot_Base.op_At ps.ps_start_acts sa);
                ps_shapes = (ps.ps_shapes);
                ps_imports = (ps.ps_imports)
              }, rest))
  | (TK_KW "START")::(TK_EQ)::rest ->
      (match parse_shape_expression ps.ps_turtle rest shexc_grammar_fuel with
       | SErr m -> SErr m
       | SOk (se, rest1) ->
           SOk
             ({
                ps_turtle = (ps.ps_turtle);
                ps_start = (FStar_Pervasives_Native.Some se);
                ps_start_acts = (ps.ps_start_acts);
                ps_shapes = (ps.ps_shapes);
                ps_imports = (ps.ps_imports)
              }, rest1))
  | (TK_KW "ABSTRACT")::(TK_TERM t)::rest ->
      (match resolve_shexc_term ps.ps_turtle t with
       | FStar_Pervasives_Native.None -> SErr "unresolvable shape label"
       | FStar_Pervasives_Native.Some label ->
           (match rest with
            | (TK_KW "EXTERNAL")::rest1 ->
                SOk
                  ({
                     ps_turtle = (ps.ps_turtle);
                     ps_start = (ps.ps_start);
                     ps_start_acts = (ps.ps_start_acts);
                     ps_shapes =
                       (FStar_List_Tot_Base.op_At ps.ps_shapes
                          [{
                             ShEx_Schema.sd_id = label;
                             ShEx_Schema.sd_is_abstract = true;
                             ShEx_Schema.sd_expr =
                               ShEx_Schema.SE_ShapeExternal
                           }]);
                     ps_imports = (ps.ps_imports)
                   }, rest1)
            | uu___ ->
                (match parse_shape_expression ps.ps_turtle rest
                         shexc_grammar_fuel
                 with
                 | SErr m -> SErr m
                 | SOk (se, rest1) ->
                     SOk
                       ({
                          ps_turtle = (ps.ps_turtle);
                          ps_start = (ps.ps_start);
                          ps_start_acts = (ps.ps_start_acts);
                          ps_shapes =
                            (FStar_List_Tot_Base.op_At ps.ps_shapes
                               [{
                                  ShEx_Schema.sd_id = label;
                                  ShEx_Schema.sd_is_abstract = true;
                                  ShEx_Schema.sd_expr = se
                                }]);
                          ps_imports = (ps.ps_imports)
                        }, rest1))))
  | (TK_TERM t)::rest ->
      (match resolve_shexc_term ps.ps_turtle t with
       | FStar_Pervasives_Native.None -> SErr "unresolvable shape label"
       | FStar_Pervasives_Native.Some label ->
           (match rest with
            | (TK_KW "EXTERNAL")::rest1 ->
                SOk
                  ({
                     ps_turtle = (ps.ps_turtle);
                     ps_start = (ps.ps_start);
                     ps_start_acts = (ps.ps_start_acts);
                     ps_shapes =
                       (FStar_List_Tot_Base.op_At ps.ps_shapes
                          [{
                             ShEx_Schema.sd_id = label;
                             ShEx_Schema.sd_is_abstract = false;
                             ShEx_Schema.sd_expr =
                               ShEx_Schema.SE_ShapeExternal
                           }]);
                     ps_imports = (ps.ps_imports)
                   }, rest1)
            | uu___ ->
                (match parse_shape_expression ps.ps_turtle rest
                         shexc_grammar_fuel
                 with
                 | SErr m -> SErr m
                 | SOk (se, rest1) ->
                     SOk
                       ({
                          ps_turtle = (ps.ps_turtle);
                          ps_start = (ps.ps_start);
                          ps_start_acts = (ps.ps_start_acts);
                          ps_shapes =
                            (FStar_List_Tot_Base.op_At ps.ps_shapes
                               [{
                                  ShEx_Schema.sd_id = label;
                                  ShEx_Schema.sd_is_abstract = false;
                                  ShEx_Schema.sd_expr = se
                                }]);
                          ps_imports = (ps.ps_imports)
                        }, rest1))))
  | uu___ -> SErr "expected a shape declaration, START, or directive"
let rec parse_statements (ps : shexc_parse_state) (ts : shexc_tokens)
  (fuel : Prims.nat) : shexc_parse_state sresult=
  if fuel = Prims.int_zero
  then SOk (ps, ts)
  else
    (match parse_directives ps ts
             ((FStar_List_Tot_Base.length ts) + Prims.int_one)
     with
     | SErr m -> SErr m
     | SOk (ps1, ts1) ->
         (match ts1 with
          | [] -> SOk (ps1, ts1)
          | (TK_EOF)::uu___1 -> SOk (ps1, ts1)
          | uu___1 ->
              (match parse_statement ps1 ts1 (fuel - Prims.int_one) with
               | SErr m -> SErr m
               | SOk (ps2, ts2) ->
                   parse_statements ps2 ts2 (fuel - Prims.int_one))))
let empty_parse_state (base : Prims.string) : shexc_parse_state=
  {
    ps_turtle =
      {
        Parser_Turtle.prefixes =
          (Parser_Turtle.empty_turtle_state.Parser_Turtle.prefixes);
        Parser_Turtle.base_iri = base;
        Parser_Turtle.bnode_counter =
          (Parser_Turtle.empty_turtle_state.Parser_Turtle.bnode_counter)
      };
    ps_start = FStar_Pervasives_Native.None;
    ps_start_acts = [];
    ps_shapes = [];
    ps_imports = []
  }
let parse_shexc_schema (input : Prims.string) (base : Prims.string) :
  ShEx_Schema.shex_schema FStar_Pervasives_Native.option=
  let ts = shexc_tokenize input in
  match parse_statements (empty_parse_state base) ts
          ((FStar_List_Tot_Base.length ts) + Prims.int_one)
  with
  | SErr uu___ -> FStar_Pervasives_Native.None
  | SOk (ps, uu___) ->
      FStar_Pervasives_Native.Some
        {
          ShEx_Schema.sch_start = (ps.ps_start);
          ShEx_Schema.sch_start_acts = (ps.ps_start_acts);
          ShEx_Schema.sch_shapes = (ps.ps_shapes);
          ShEx_Schema.sch_imports = (ps.ps_imports)
        }
