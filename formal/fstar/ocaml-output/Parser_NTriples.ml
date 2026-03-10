open Prims
let hex_val (c : FStar_Char.char) : Prims.int=
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
let valid_codepoint (cp : Prims.int) : Prims.bool=
  (cp >= Prims.int_zero) &&
    ((cp < (Prims.of_int (0xD7FF))) ||
       ((cp >= (Prims.of_int (0xE000))) &&
          (cp <= (Prims.parse_int "0x10FFFF"))))
let safe_char_of_int (cp : Prims.int) : FStar_Char.char=
  if valid_codepoint cp
  then let n = cp in FStar_Char.char_of_int n
  else FStar_Char.char_of_int (Prims.of_int (0xFFFD))
let codepoint_to_string (cp : Prims.int) : Prims.string=
  FStar_String.string_of_char (safe_char_of_int cp)
let is_nt_ws (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x09)))
let pws (input : Prims.string) (pos : Prims.nat) :
  unit Parser_Combinators.parse_result=
  match Parser_Combinators.ptake_while is_nt_ws input pos with
  | Parser_Combinators.ParseOk (uu___, pos') ->
      Parser_Combinators.ParseOk ((), pos')
  | Parser_Combinators.ParseFail (msg, fpos) ->
      Parser_Combinators.ParseFail (msg, fpos)
let rec parse_iri_body_acc (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_String.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("IRI too long", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated IRI", pos)
     else
       (let ch = FStar_String.index input pos in
        let code = FStar_Char.int_of_char ch in
        if code = (Prims.of_int (0x3E))
        then
          Parser_Combinators.ParseOk
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)),
              (pos + Prims.int_one))
        else
          if code = (Prims.of_int (0x5C))
          then
            (if (pos + Prims.int_one) >= len
             then
               Parser_Combinators.ParseFail ("backslash at end of IRI", pos)
             else
               (let next = FStar_String.index input (pos + Prims.int_one) in
                let ncode = FStar_Char.int_of_char next in
                if ncode = (Prims.of_int (0x75))
                then
                  (if (pos + (Prims.of_int (6))) > len
                   then
                     Parser_Combinators.ParseFail
                       ("incomplete \\u escape in IRI", pos)
                   else
                     (let h0 =
                        hex_val
                          (FStar_String.index input
                             (pos + (Prims.of_int (2)))) in
                      let h1 =
                        hex_val
                          (FStar_String.index input
                             (pos + (Prims.of_int (3)))) in
                      let h2 =
                        hex_val
                          (FStar_String.index input
                             (pos + (Prims.of_int (4)))) in
                      let h3 =
                        hex_val
                          (FStar_String.index input
                             (pos + (Prims.of_int (5)))) in
                      let cp =
                        (((h0 * (Prims.of_int (4096))) +
                            (h1 * (Prims.of_int (256))))
                           + (h2 * (Prims.of_int (16))))
                          + h3 in
                      let c = safe_char_of_int cp in
                      parse_iri_body_acc input (pos + (Prims.of_int (6))) (c
                        :: acc) (fuel - Prims.int_one)))
                else
                  if ncode = (Prims.of_int (0x55))
                  then
                    (if (pos + (Prims.of_int (10))) > len
                     then
                       Parser_Combinators.ParseFail
                         ("incomplete \\U escape in IRI", pos)
                     else
                       (let h0 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (2)))) in
                        let h1 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (3)))) in
                        let h2 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (4)))) in
                        let h3 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (5)))) in
                        let h4 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (6)))) in
                        let h5 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (7)))) in
                        let h6 =
                          hex_val
                            (FStar_String.index input
                               (pos + (Prims.of_int (8)))) in
                        let h7 =
                          hex_val
                            (FStar_String.index input
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
                        let c = safe_char_of_int cp in
                        parse_iri_body_acc input (pos + (Prims.of_int (10)))
                          (c :: acc) (fuel - Prims.int_one)))
                  else
                    Parser_Combinators.ParseFail
                      ("invalid escape in IRI", pos)))
          else
            if code <= (Prims.of_int (0x20))
            then
              Parser_Combinators.ParseFail ("invalid character in IRI", pos)
            else
              parse_iri_body_acc input (pos + Prims.int_one) (ch :: acc)
                (fuel - Prims.int_one)))
let parse_iri_raw : RDF_Graph_Executable.iri Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected '<'", pos)
    else
      (let ch = FStar_String.index input pos in
       if (FStar_Char.int_of_char ch) = (Prims.of_int (0x3C))
       then
         let fuel = len - pos in
         parse_iri_body_acc input (pos + Prims.int_one) [] fuel
       else Parser_Combinators.ParseFail ("expected '<'", pos))
let parse_iri : RDF_Graph_Executable.wf_iri Parser_Combinators.parser=
  fun input pos ->
    match parse_iri_raw input pos with
    | Parser_Combinators.ParseOk (i, pos') ->
        if RDF_Graph_Executable.is_iri i
        then Parser_Combinators.ParseOk (i, pos')
        else Parser_Combinators.ParseFail ("invalid IRI", pos)
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
let is_bnode_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((((((((((((((((((code >= (Prims.of_int (0x30))) &&
                     (code <= (Prims.of_int (0x39))))
                    ||
                    ((code >= (Prims.of_int (0x41))) &&
                       (code <= (Prims.of_int (0x5A)))))
                   ||
                   ((code >= (Prims.of_int (0x61))) &&
                      (code <= (Prims.of_int (0x7A)))))
                  || (code = (Prims.of_int (0x5F))))
                 || (code = (Prims.of_int (0x2D))))
                || (code = (Prims.of_int (0x2E))))
               || (code = (Prims.of_int (0xB7))))
              ||
              ((code >= (Prims.of_int (0x00C0))) &&
                 (code <= (Prims.of_int (0x00D6)))))
             ||
             ((code >= (Prims.of_int (0x00D8))) &&
                (code <= (Prims.of_int (0x00F6)))))
            ||
            ((code >= (Prims.of_int (0x00F8))) &&
               (code <= (Prims.of_int (0x02FF)))))
           ||
           ((code >= (Prims.of_int (0x0370))) &&
              (code <= (Prims.of_int (0x037D)))))
          ||
          ((code >= (Prims.of_int (0x037F))) &&
             (code <= (Prims.of_int (0x1FFF)))))
         ||
         ((code >= (Prims.of_int (0x200C))) &&
            (code <= (Prims.of_int (0x200D)))))
        ||
        ((code >= (Prims.of_int (0x2070))) &&
           (code <= (Prims.of_int (0x218F)))))
       ||
       ((code >= (Prims.of_int (0x2C00))) &&
          (code <= (Prims.of_int (0x2FEF)))))
      ||
      ((code >= (Prims.of_int (0x3001))) && (code <= (Prims.of_int (0xD7FF)))))
     ||
     ((code >= (Prims.of_int (0xF900))) && (code <= (Prims.of_int (0xFDCF)))))
    ||
    ((code >= (Prims.of_int (0xFDF0))) && (code <= (Prims.of_int (0xFFFD))))
let is_bnode_start (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  (((((((((((((((code >= (Prims.of_int (0x41))) &&
                  (code <= (Prims.of_int (0x5A))))
                 ||
                 ((code >= (Prims.of_int (0x61))) &&
                    (code <= (Prims.of_int (0x7A)))))
                || (code = (Prims.of_int (0x5F))))
               ||
               ((code >= (Prims.of_int (0x30))) &&
                  (code <= (Prims.of_int (0x39)))))
              ||
              ((code >= (Prims.of_int (0x00C0))) &&
                 (code <= (Prims.of_int (0x00D6)))))
             ||
             ((code >= (Prims.of_int (0x00D8))) &&
                (code <= (Prims.of_int (0x00F6)))))
            ||
            ((code >= (Prims.of_int (0x00F8))) &&
               (code <= (Prims.of_int (0x02FF)))))
           ||
           ((code >= (Prims.of_int (0x0370))) &&
              (code <= (Prims.of_int (0x037D)))))
          ||
          ((code >= (Prims.of_int (0x037F))) &&
             (code <= (Prims.of_int (0x1FFF)))))
         ||
         ((code >= (Prims.of_int (0x200C))) &&
            (code <= (Prims.of_int (0x200D)))))
        ||
        ((code >= (Prims.of_int (0x2070))) &&
           (code <= (Prims.of_int (0x218F)))))
       ||
       ((code >= (Prims.of_int (0x2C00))) &&
          (code <= (Prims.of_int (0x2FEF)))))
      ||
      ((code >= (Prims.of_int (0x3001))) && (code <= (Prims.of_int (0xD7FF)))))
     ||
     ((code >= (Prims.of_int (0xF900))) && (code <= (Prims.of_int (0xFDCF)))))
    ||
    ((code >= (Prims.of_int (0xFDF0))) && (code <= (Prims.of_int (0xFFFD))))
let parse_bnode : RDF_Graph_Executable.bnode_id Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if (pos + (Prims.of_int (2))) > len
    then Parser_Combinators.ParseFail ("expected '_:'", pos)
    else
      (let c0 = FStar_String.index input pos in
       let c1 = FStar_String.index input (pos + Prims.int_one) in
       if
         ((FStar_Char.int_of_char c0) = (Prims.of_int (0x5F))) &&
           ((FStar_Char.int_of_char c1) = (Prims.of_int (0x3A)))
       then
         let start_pos = pos + (Prims.of_int (2)) in
         (if start_pos >= len
          then
            Parser_Combinators.ParseFail
              ("empty blank node label", start_pos)
          else
            (let first = FStar_String.index input start_pos in
             if is_bnode_start first
             then
               match Parser_Combinators.ptake_while is_bnode_char input
                       start_pos
               with
               | Parser_Combinators.ParseOk (label, pos') ->
                   let label_len = FStar_String.strlen label in
                   (if
                      (label_len > Prims.int_zero) && (pos' > Prims.int_zero)
                    then
                      let last_ch =
                        FStar_String.index label (label_len - Prims.int_one) in
                      (if
                         (FStar_Char.int_of_char last_ch) =
                           (Prims.of_int (0x2E))
                       then
                         Parser_Combinators.ParseOk
                           ((FStar_String.sub label Prims.int_zero
                               (label_len - Prims.int_one)),
                             (pos' - Prims.int_one))
                       else Parser_Combinators.ParseOk (label, pos'))
                    else
                      Parser_Combinators.ParseFail
                        ("empty blank node label", start_pos))
               | Parser_Combinators.ParseFail (msg, fpos) ->
                   Parser_Combinators.ParseFail (msg, fpos)
             else
               Parser_Combinators.ParseFail
                 ("invalid blank node label start character", start_pos)))
       else Parser_Combinators.ParseFail ("expected '_:'", pos))
let rec parse_string_body (input : Prims.string) (pos : Prims.nat)
  (acc : FStar_String.char Prims.list) (fuel : Prims.nat) :
  Prims.string Parser_Combinators.parse_result=
  if fuel = Prims.int_zero
  then Parser_Combinators.ParseFail ("string too long", pos)
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then Parser_Combinators.ParseFail ("unterminated string literal", pos)
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
                if esc_code = (Prims.of_int (0x74))
                then
                  parse_string_body input (pos + (Prims.of_int (2)))
                    ((FStar_Char.char_of_int (Prims.of_int (0x09))) :: acc)
                    (fuel - Prims.int_one)
                else
                  if esc_code = (Prims.of_int (0x6E))
                  then
                    parse_string_body input (pos + (Prims.of_int (2)))
                      ((FStar_Char.char_of_int (Prims.of_int (0x0A))) :: acc)
                      (fuel - Prims.int_one)
                  else
                    if esc_code = (Prims.of_int (0x72))
                    then
                      parse_string_body input (pos + (Prims.of_int (2)))
                        ((FStar_Char.char_of_int (Prims.of_int (0x0D))) ::
                        acc) (fuel - Prims.int_one)
                    else
                      if esc_code = (Prims.of_int (0x5C))
                      then
                        parse_string_body input (pos + (Prims.of_int (2)))
                          ((FStar_Char.char_of_int (Prims.of_int (0x5C))) ::
                          acc) (fuel - Prims.int_one)
                      else
                        if esc_code = (Prims.of_int (0x22))
                        then
                          parse_string_body input (pos + (Prims.of_int (2)))
                            ((FStar_Char.char_of_int (Prims.of_int (0x22)))
                            :: acc) (fuel - Prims.int_one)
                        else
                          if esc_code = (Prims.of_int (0x62))
                          then
                            parse_string_body input
                              (pos + (Prims.of_int (2)))
                              ((FStar_Char.char_of_int (Prims.of_int (0x08)))
                              :: acc) (fuel - Prims.int_one)
                          else
                            if esc_code = (Prims.of_int (0x66))
                            then
                              parse_string_body input
                                (pos + (Prims.of_int (2)))
                                ((FStar_Char.char_of_int
                                    (Prims.of_int (0x0C))) :: acc)
                                (fuel - Prims.int_one)
                            else
                              if esc_code = (Prims.of_int (0x75))
                              then
                                (if (pos + (Prims.of_int (6))) > len
                                 then
                                   Parser_Combinators.ParseFail
                                     ("incomplete \\u escape", pos)
                                 else
                                   (let h0 =
                                      hex_val
                                        (FStar_String.index input
                                           (pos + (Prims.of_int (2)))) in
                                    let h1 =
                                      hex_val
                                        (FStar_String.index input
                                           (pos + (Prims.of_int (3)))) in
                                    let h2 =
                                      hex_val
                                        (FStar_String.index input
                                           (pos + (Prims.of_int (4)))) in
                                    let h3 =
                                      hex_val
                                        (FStar_String.index input
                                           (pos + (Prims.of_int (5)))) in
                                    let cp =
                                      (((h0 * (Prims.of_int (4096))) +
                                          (h1 * (Prims.of_int (256))))
                                         + (h2 * (Prims.of_int (16))))
                                        + h3 in
                                    let c = safe_char_of_int cp in
                                    parse_string_body input
                                      (pos + (Prims.of_int (6))) (c :: acc)
                                      (fuel - Prims.int_one)))
                              else
                                if esc_code = (Prims.of_int (0x55))
                                then
                                  (if (pos + (Prims.of_int (10))) > len
                                   then
                                     Parser_Combinators.ParseFail
                                       ("incomplete \\U escape", pos)
                                   else
                                     (let h0 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (2)))) in
                                      let h1 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (3)))) in
                                      let h2 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (4)))) in
                                      let h3 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (5)))) in
                                      let h4 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (6)))) in
                                      let h5 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (7)))) in
                                      let h6 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (8)))) in
                                      let h7 =
                                        hex_val
                                          (FStar_String.index input
                                             (pos + (Prims.of_int (9)))) in
                                      let cp =
                                        (((((((h0 *
                                                 (Prims.parse_int "268435456"))
                                                +
                                                (h1 *
                                                   (Prims.parse_int "16777216")))
                                               +
                                               (h2 *
                                                  (Prims.parse_int "1048576")))
                                              +
                                              (h3 * (Prims.parse_int "65536")))
                                             + (h4 * (Prims.of_int (4096))))
                                            + (h5 * (Prims.of_int (256))))
                                           + (h6 * (Prims.of_int (16))))
                                          + h7 in
                                      let c = safe_char_of_int cp in
                                      parse_string_body input
                                        (pos + (Prims.of_int (10))) (c ::
                                        acc) (fuel - Prims.int_one)))
                                else
                                  Parser_Combinators.ParseFail
                                    ((FStar_String.concat ""
                                        ["invalid escape: \\";
                                        FStar_String.string_of_char esc]),
                                      pos)))
          else
            if
              (code = (Prims.of_int (0x0A))) ||
                (code = (Prims.of_int (0x0D)))
            then
              Parser_Combinators.ParseFail
                ("unescaped newline in string literal", pos)
            else
              parse_string_body input (pos + Prims.int_one) (ch :: acc)
                (fuel - Prims.int_one)))
let parse_string_literal : Prims.string Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected '\"'", pos)
    else
      (let ch = FStar_String.index input pos in
       if (FStar_Char.int_of_char ch) = (Prims.of_int (0x22))
       then
         let fuel = len - pos in
         parse_string_body input (pos + Prims.int_one) [] fuel
       else Parser_Combinators.ParseFail ("expected '\"'", pos))
let is_lang_char (c : FStar_Char.char) : Prims.bool=
  let code = FStar_Char.int_of_char c in
  ((((code >= (Prims.of_int (0x41))) && (code <= (Prims.of_int (0x5A)))) ||
      ((code >= (Prims.of_int (0x61))) && (code <= (Prims.of_int (0x7A)))))
     || ((code >= (Prims.of_int (0x30))) && (code <= (Prims.of_int (0x39)))))
    || (code = (Prims.of_int (0x2D)))
let parse_lang_tag : Prims.string Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected '@'", pos)
    else
      (let ch = FStar_String.index input pos in
       if (FStar_Char.int_of_char ch) = (Prims.of_int (0x40))
       then
         match Parser_Combinators.ptake_while1 is_lang_char input
                 (pos + Prims.int_one)
         with
         | Parser_Combinators.ParseOk (lang, pos') ->
             Parser_Combinators.ParseOk (lang, pos')
         | Parser_Combinators.ParseFail (uu___1, fpos) ->
             Parser_Combinators.ParseFail
               ("expected language tag after '@'", fpos)
       else Parser_Combinators.ParseFail ("expected '@'", pos))
let parse_datatype : RDF_Graph_Executable.wf_iri Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if (pos + (Prims.of_int (2))) > len
    then Parser_Combinators.ParseFail ("expected '^^'", pos)
    else
      (let c0 = FStar_String.index input pos in
       let c1 = FStar_String.index input (pos + Prims.int_one) in
       if
         ((FStar_Char.int_of_char c0) = (Prims.of_int (0x5E))) &&
           ((FStar_Char.int_of_char c1) = (Prims.of_int (0x5E)))
       then parse_iri input (pos + (Prims.of_int (2)))
       else Parser_Combinators.ParseFail ("expected '^^'", pos))
let parse_literal :
  RDF_Graph_Executable.wf_literal Parser_Combinators.parser=
  fun input pos ->
    match parse_string_literal input pos with
    | Parser_Combinators.ParseOk (lexical, pos') ->
        let len = FStar_String.strlen input in
        if pos' >= len
        then
          let lit =
            {
              RDF_Graph_Executable.lexical_form = lexical;
              RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_string;
              RDF_Graph_Executable.lang_tag = FStar_Pervasives_Native.None
            } in
          (if RDF_Graph_Executable.literal_wf lit
           then Parser_Combinators.ParseOk (lit, pos')
           else Parser_Combinators.ParseFail ("invalid literal", pos))
        else
          (let next = FStar_String.index input pos' in
           let next_code = FStar_Char.int_of_char next in
           if next_code = (Prims.of_int (0x40))
           then
             match parse_lang_tag input pos' with
             | Parser_Combinators.ParseOk (lang, pos'') ->
                 let lit =
                   {
                     RDF_Graph_Executable.lexical_form = lexical;
                     RDF_Graph_Executable.datatype =
                       RDF_Graph_Executable.rdf_lang_string;
                     RDF_Graph_Executable.lang_tag =
                       (FStar_Pervasives_Native.Some lang)
                   } in
                 (if RDF_Graph_Executable.literal_wf lit
                  then Parser_Combinators.ParseOk (lit, pos'')
                  else Parser_Combinators.ParseFail ("invalid literal", pos))
             | Parser_Combinators.ParseFail (msg, fpos) ->
                 Parser_Combinators.ParseFail (msg, fpos)
           else
             if next_code = (Prims.of_int (0x5E))
             then
               (match parse_datatype input pos' with
                | Parser_Combinators.ParseOk (dt, pos'') ->
                    let lit =
                      {
                        RDF_Graph_Executable.lexical_form = lexical;
                        RDF_Graph_Executable.datatype = dt;
                        RDF_Graph_Executable.lang_tag =
                          FStar_Pervasives_Native.None
                      } in
                    if RDF_Graph_Executable.literal_wf lit
                    then Parser_Combinators.ParseOk (lit, pos'')
                    else
                      Parser_Combinators.ParseFail ("invalid literal", pos)
                | Parser_Combinators.ParseFail (msg, fpos) ->
                    Parser_Combinators.ParseFail (msg, fpos))
             else
               (let lit =
                  {
                    RDF_Graph_Executable.lexical_form = lexical;
                    RDF_Graph_Executable.datatype =
                      RDF_Graph_Executable.xsd_string;
                    RDF_Graph_Executable.lang_tag =
                      FStar_Pervasives_Native.None
                  } in
                if RDF_Graph_Executable.literal_wf lit
                then Parser_Combinators.ParseOk (lit, pos')
                else Parser_Combinators.ParseFail ("invalid literal", pos)))
    | Parser_Combinators.ParseFail (msg, fpos) ->
        Parser_Combinators.ParseFail (msg, fpos)
let parse_subject : RDF_Graph_Executable.subject Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected subject", pos)
    else
      (let ch = FStar_String.index input pos in
       let code = FStar_Char.int_of_char ch in
       if code = (Prims.of_int (0x3C))
       then
         match parse_iri input pos with
         | Parser_Combinators.ParseOk (i, pos') ->
             Parser_Combinators.ParseOk
               ((RDF_Graph_Executable.S_IRI i), pos')
         | Parser_Combinators.ParseFail (msg, fpos) ->
             Parser_Combinators.ParseFail (msg, fpos)
       else
         if code = (Prims.of_int (0x5F))
         then
           (match parse_bnode input pos with
            | Parser_Combinators.ParseOk (b, pos') ->
                Parser_Combinators.ParseOk
                  ((RDF_Graph_Executable.S_BNode b), pos')
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos))
         else
           Parser_Combinators.ParseFail
             ("expected '<' or '_:' for subject", pos))
let parse_object : RDF_Graph_Executable.rdf_term Parser_Combinators.parser=
  fun input pos ->
    let len = FStar_String.strlen input in
    if pos >= len
    then Parser_Combinators.ParseFail ("expected object", pos)
    else
      (let ch = FStar_String.index input pos in
       let code = FStar_Char.int_of_char ch in
       if code = (Prims.of_int (0x3C))
       then
         match parse_iri input pos with
         | Parser_Combinators.ParseOk (i, pos') ->
             Parser_Combinators.ParseOk
               ((RDF_Graph_Executable.T_IRI i), pos')
         | Parser_Combinators.ParseFail (msg, fpos) ->
             Parser_Combinators.ParseFail (msg, fpos)
       else
         if code = (Prims.of_int (0x5F))
         then
           (match parse_bnode input pos with
            | Parser_Combinators.ParseOk (b, pos') ->
                Parser_Combinators.ParseOk
                  ((RDF_Graph_Executable.T_BNode b), pos')
            | Parser_Combinators.ParseFail (msg, fpos) ->
                Parser_Combinators.ParseFail (msg, fpos))
         else
           if code = (Prims.of_int (0x22))
           then
             (match parse_literal input pos with
              | Parser_Combinators.ParseOk (lit, pos') ->
                  Parser_Combinators.ParseOk
                    ((RDF_Graph_Executable.T_Literal lit), pos')
              | Parser_Combinators.ParseFail (msg, fpos) ->
                  Parser_Combinators.ParseFail (msg, fpos))
           else
             Parser_Combinators.ParseFail
               ("expected '<', '_:', or '\"' for object", pos))
let parse_triple : RDF_Graph_Executable.triple Parser_Combinators.parser=
  fun input pos ->
    match pws input pos with
    | Parser_Combinators.ParseOk ((), pos1) ->
        (match parse_subject input pos1 with
         | Parser_Combinators.ParseOk (subj, pos2) ->
             (match pws input pos2 with
              | Parser_Combinators.ParseOk ((), pos3) ->
                  (match parse_iri input pos3 with
                   | Parser_Combinators.ParseOk (pred, pos4) ->
                       (match pws input pos4 with
                        | Parser_Combinators.ParseOk ((), pos5) ->
                            (match parse_object input pos5 with
                             | Parser_Combinators.ParseOk (obj, pos6) ->
                                 (match pws input pos6 with
                                  | Parser_Combinators.ParseOk ((), pos7) ->
                                      let len = FStar_String.strlen input in
                                      if pos7 >= len
                                      then
                                        Parser_Combinators.ParseFail
                                          ("expected '.'", pos7)
                                      else
                                        (let dot =
                                           FStar_String.index input pos7 in
                                         if
                                           (FStar_Char.int_of_char dot) =
                                             (Prims.of_int (0x2E))
                                         then
                                           Parser_Combinators.ParseOk
                                             ({
                                                RDF_Graph_Executable.s = subj;
                                                RDF_Graph_Executable.p = pred;
                                                RDF_Graph_Executable.o = obj
                                              }, (pos7 + Prims.int_one))
                                         else
                                           Parser_Combinators.ParseFail
                                             ("expected '.'", pos7))
                                  | Parser_Combinators.ParseFail (msg, fpos)
                                      ->
                                      Parser_Combinators.ParseFail
                                        (msg, fpos))
                             | Parser_Combinators.ParseFail (msg, fpos) ->
                                 Parser_Combinators.ParseFail (msg, fpos))
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
let skip_comment (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = FStar_String.strlen input in
  if pos >= len
  then pos
  else
    (let ch = FStar_String.index input pos in
     if (FStar_Char.int_of_char ch) = (Prims.of_int (0x23))
     then
       let rec skip_to_eol p fuel =
         if fuel = Prims.int_zero
         then p
         else
           if p >= len
           then p
           else
             (let c = FStar_String.index input p in
              let cc = FStar_Char.int_of_char c in
              if (cc = (Prims.of_int (0x0A))) || (cc = (Prims.of_int (0x0D)))
              then p
              else skip_to_eol (p + Prims.int_one) (fuel - Prims.int_one)) in
       skip_to_eol (pos + Prims.int_one) (len - pos)
     else pos)
let skip_eol (input : Prims.string) (pos : Prims.nat) : Prims.nat=
  let len = FStar_String.strlen input in
  if pos >= len
  then pos
  else
    (let ch = FStar_String.index input pos in
     let code = FStar_Char.int_of_char ch in
     if code = (Prims.of_int (0x0D))
     then
       (if (pos + Prims.int_one) < len
        then
          let next = FStar_String.index input (pos + Prims.int_one) in
          (if (FStar_Char.int_of_char next) = (Prims.of_int (0x0A))
           then pos + (Prims.of_int (2))
           else pos + Prims.int_one)
        else pos + Prims.int_one)
     else if code = (Prims.of_int (0x0A)) then pos + Prims.int_one else pos)
let rec parse_ntriples_acc (input : Prims.string) (pos : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list) (fuel : Prims.nat) :
  RDF_Graph_Executable.triple Prims.list=
  if fuel = Prims.int_zero
  then FStar_List_Tot_Base.rev acc
  else
    (let len = FStar_String.strlen input in
     if pos >= len
     then FStar_List_Tot_Base.rev acc
     else
       (let pos1 =
          match pws input pos with
          | Parser_Combinators.ParseOk ((), p) -> p
          | uu___2 -> pos in
        if pos1 >= len
        then FStar_List_Tot_Base.rev acc
        else
          (let ch = FStar_String.index input pos1 in
           let code = FStar_Char.int_of_char ch in
           if code = (Prims.of_int (0x23))
           then
             let pos2 = skip_comment input pos1 in
             let pos3 = skip_eol input pos2 in
             (if pos3 = pos1
              then FStar_List_Tot_Base.rev acc
              else parse_ntriples_acc input pos3 acc (fuel - Prims.int_one))
           else
             if
               (code = (Prims.of_int (0x0A))) ||
                 (code = (Prims.of_int (0x0D)))
             then
               (let pos2 = skip_eol input pos1 in
                if pos2 = pos1
                then FStar_List_Tot_Base.rev acc
                else parse_ntriples_acc input pos2 acc (fuel - Prims.int_one))
             else
               (match parse_triple input pos1 with
                | Parser_Combinators.ParseOk (t, pos2) ->
                    let pos3 =
                      match pws input pos2 with
                      | Parser_Combinators.ParseOk ((), p) -> p
                      | uu___5 -> pos2 in
                    let pos4 = skip_comment input pos3 in
                    let pos5 = skip_eol input pos4 in
                    let pos_next =
                      if pos5 > pos1
                      then pos5
                      else if pos4 > pos1 then pos4 else pos2 in
                    parse_ntriples_acc input pos_next (t :: acc)
                      (fuel - Prims.int_one)
                | Parser_Combinators.ParseFail (uu___5, uu___6) ->
                    let rec skip_line p f =
                      if f = Prims.int_zero
                      then p
                      else
                        if p >= len
                        then p
                        else
                          (let c = FStar_String.index input p in
                           let cc = FStar_Char.int_of_char c in
                           if
                             (cc = (Prims.of_int (0x0A))) ||
                               (cc = (Prims.of_int (0x0D)))
                           then skip_eol input p
                           else
                             skip_line (p + Prims.int_one)
                               (f - Prims.int_one)) in
                    let pos2 = skip_line pos1 (len - pos1) in
                    if pos2 = pos1
                    then FStar_List_Tot_Base.rev acc
                    else
                      parse_ntriples_acc input pos2 acc
                        (fuel - Prims.int_one)))))
let parse_ntriples (input : Prims.string) :
  RDF_Graph_Executable.triple Prims.list=
  let len = FStar_String.strlen input in
  parse_ntriples_acc input Prims.int_zero [] (len + Prims.int_one)
