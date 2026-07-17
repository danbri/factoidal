open Prims
let rif_pred_ns : Prims.string=
  "http://www.w3.org/2007/rif-builtin-predicate#"
let rif_func_ns : Prims.string=
  "http://www.w3.org/2007/rif-builtin-function#"
let rif_pred_iri_string : RDF_Term.wf_iri=
  Prims.strcat rif_pred_ns "iri-string"
let xsd_hexBinary : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "hexBinary"
let xsd_base64Binary : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "base64Binary"
let xsd_anyURI : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "anyURI"
let rdf_ns_prefix : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
let rdf_XMLLiteral : RDF_Term.wf_iri= Prims.strcat rdf_ns_prefix "XMLLiteral"
let rdf_PlainLiteral_dt : RDF_Term.wf_iri=
  Prims.strcat rdf_ns_prefix "PlainLiteral"
let xsd_normalizedString : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "normalizedString"
let xsd_token : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "token"
let xsd_language : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "language"
let xsd_lang_nonstandard : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "lang"
let xsd_Name_dt : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "Name"
let xsd_NCName_dt : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "NCName"
let xsd_NMTOKEN_dt : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "NMTOKEN"
let xsd_date : RDF_Term.wf_iri= Prims.strcat OWL_Closure.xsd_ns_prefix "date"
let xsd_dayTimeDuration : RDF_Term.wf_iri=
  Prims.strcat OWL_Closure.xsd_ns_prefix "dayTimeDuration"
let is_hex_digit_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))) ||
     ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (70)))))
    || ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (102))))
let is_hex_binary_lexical (lex : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string lex in
  (((mod) (FStar_List_Tot_Base.length cs) (Prims.of_int (2))) =
     Prims.int_zero)
    && (FStar_List_Tot_Base.for_all is_hex_digit_char cs)
let is_base64_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((((((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
        ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122)))))
       || ((n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))))
      || (n = (Prims.of_int (43))))
     || (n = (Prims.of_int (47))))
    || (n = (Prims.of_int (61)))
let is_base64_binary_lexical (lex : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string lex in
  let len = FStar_List_Tot_Base.length cs in
  ((len > Prims.int_zero) &&
     (((mod) len (Prims.of_int (4))) = Prims.int_zero))
    && (FStar_List_Tot_Base.for_all is_base64_char cs)
let is_crlf_tab_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((n = (Prims.of_int (0x09))) || (n = (Prims.of_int (0x0A)))) ||
    (n = (Prims.of_int (0x0D)))
let is_ascii_alpha_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))) ||
    ((n >= (Prims.of_int (97))) && (n <= (Prims.of_int (122))))
let is_ascii_digit_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let is_name_start_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  ((is_ascii_alpha_char c) || (n = (Prims.of_int (0x5F)))) ||
    (n = (Prims.of_int (0x3A)))
let is_name_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (((is_name_start_char c) || (is_ascii_digit_char c)) ||
     (n = (Prims.of_int (0x2D))))
    || (n = (Prims.of_int (0x2E)))
let is_colon_char (c : FStar_Char.char) : Prims.bool=
  (FStar_Char.int_of_char c) = (Prims.of_int (0x3A))
let is_space_char (c : FStar_Char.char) : Prims.bool=
  (FStar_Char.int_of_char c) = (Prims.of_int (0x20))
let is_normalized_string_value (lex : Prims.string) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun c -> Prims.op_Negation (is_crlf_tab_char c))
    (FStar_String.list_of_string lex)
let rec no_double_space (cs : FStar_Char.char Prims.list) : Prims.bool=
  match cs with
  | [] -> true
  | uu___::[] -> true
  | a::b::rest ->
      if (is_space_char a) && (is_space_char b)
      then false
      else no_double_space (b :: rest)
let is_token_value (lex : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string lex in
  (((is_normalized_string_value lex) &&
      (match cs with
       | [] -> true
       | c::uu___ -> Prims.op_Negation (is_space_char c)))
     &&
     (match FStar_List_Tot_Base.rev cs with
      | [] -> true
      | c::uu___ -> Prims.op_Negation (is_space_char c)))
    && (no_double_space cs)
let rec split_on_dash_aux (cs : FStar_Char.char Prims.list)
  (cur : FStar_Char.char Prims.list) : FStar_Char.char Prims.list Prims.list=
  match cs with
  | [] -> [FStar_List_Tot_Base.rev cur]
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x2D))
      then (FStar_List_Tot_Base.rev cur) :: (split_on_dash_aux rest [])
      else split_on_dash_aux rest (c :: cur)
let split_on_dash (s : Prims.string) : FStar_Char.char Prims.list Prims.list=
  split_on_dash_aux (FStar_String.list_of_string s) []
let is_language_value (lex : Prims.string) : Prims.bool=
  match split_on_dash lex with
  | [] -> false
  | first::rest ->
      let sub_ok alnum sub =
        let len = FStar_List_Tot_Base.length sub in
        ((len >= Prims.int_one) && (len <= (Prims.of_int (8)))) &&
          (FStar_List_Tot_Base.for_all
             (fun c ->
                if alnum
                then (is_ascii_alpha_char c) || (is_ascii_digit_char c)
                else is_ascii_alpha_char c) sub) in
      (sub_ok false first) &&
        (FStar_List_Tot_Base.for_all (sub_ok true) rest)
let is_nmtoken_value (lex : Prims.string) : Prims.bool=
  let cs = FStar_String.list_of_string lex in
  (Prims.uu___is_Cons cs) && (FStar_List_Tot_Base.for_all is_name_char cs)
let is_name_value (lex : Prims.string) : Prims.bool=
  match FStar_String.list_of_string lex with
  | [] -> false
  | c::rest ->
      (is_name_start_char c) &&
        (FStar_List_Tot_Base.for_all is_name_char rest)
let is_ncname_value (lex : Prims.string) : Prims.bool=
  (is_name_value lex) &&
    (FStar_List_Tot_Base.for_all
       (fun c -> Prims.op_Negation (is_colon_char c))
       (FStar_String.list_of_string lex))
let string_family_datatypes : RDF_Term.wf_iri Prims.list=
  [RDF_Term.xsd_string;
  xsd_normalizedString;
  xsd_token;
  xsd_language;
  xsd_lang_nonstandard;
  xsd_Name_dt;
  xsd_NCName_dt;
  xsd_NMTOKEN_dt]
let is_string_family_dt (dt : RDF_Term.wf_iri) : Prims.bool=
  FStar_List_Tot_Base.mem dt string_family_datatypes
let string_value_ok (dt : RDF_Term.wf_iri) (lex : Prims.string) : Prims.bool=
  if dt = xsd_normalizedString
  then is_normalized_string_value lex
  else
    if dt = xsd_token
    then is_token_value lex
    else
      if (dt = xsd_language) || (dt = xsd_lang_nonstandard)
      then is_language_value lex
      else
        if dt = xsd_Name_dt
        then is_name_value lex
        else
          if dt = xsd_NCName_dt
          then is_ncname_value lex
          else if dt = xsd_NMTOKEN_dt then is_nmtoken_value lex else true
let literal_ill_formed_ext (dt : RDF_Term.wf_iri) (lex : Prims.string) :
  Prims.bool=
  if dt = xsd_hexBinary
  then Prims.op_Negation (is_hex_binary_lexical lex)
  else
    if dt = xsd_base64Binary
    then Prims.op_Negation (is_base64_binary_lexical lex)
    else XSD_Datatypes.literal_ill_formed dt lex
let date_lexical_ms (lex : Prims.string) :
  (Prims.int * Prims.bool) FStar_Pervasives_Native.option=
  let len = FStar_String.strlen lex in
  if len < (Prims.of_int (10))
  then FStar_Pervasives_Native.None
  else
    if
      ((FStar_String.sub lex (Prims.of_int (4)) Prims.int_one) <> "-") ||
        ((FStar_String.sub lex (Prims.of_int (7)) Prims.int_one) <> "-")
    then FStar_Pervasives_Native.None
    else
      (match ((SPARQL11_Algebra.parse_int_string
                 (FStar_String.sub lex Prims.int_zero (Prims.of_int (4)))),
               (SPARQL11_Algebra.parse_int_string
                  (FStar_String.sub lex (Prims.of_int (5)) (Prims.of_int (2)))),
               (SPARQL11_Algebra.parse_int_string
                  (FStar_String.sub lex (Prims.of_int (8)) (Prims.of_int (2)))))
       with
       | (FStar_Pervasives_Native.Some y, FStar_Pervasives_Native.Some mo,
          FStar_Pervasives_Native.Some d) ->
           (match XSD_Datatypes.dt_parse_tail
                    (FStar_String.sub lex (Prims.of_int (10))
                       (len - (Prims.of_int (10))))
            with
            | FStar_Pervasives_Native.Some (fms, tzoff, has_tz) ->
                if fms <> Prims.int_zero
                then FStar_Pervasives_Native.None
                else
                  (let days = XSD_Datatypes.days_from_civil y mo d in
                   FStar_Pervasives_Native.Some
                     ((((days * (Prims.parse_int "86400")) - tzoff) *
                         (Prims.of_int (1000))), has_tz))
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | (uu___2, uu___3, uu___4) -> FStar_Pervasives_Native.None)
let dateTime_or_date_ms (lex : Prims.string) :
  (Prims.int * Prims.bool) FStar_Pervasives_Native.option=
  match XSD_Datatypes.dt_parse_ms lex with
  | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
  | FStar_Pervasives_Native.None -> date_lexical_ms lex
let dayTimeDuration_of_ms (delta : Prims.int) : Prims.string=
  let a = if delta < Prims.int_zero then Prims.int_zero - delta else delta in
  let msec = (mod) a (Prims.of_int (1000)) in
  let sec = (mod) (a / (Prims.of_int (1000))) (Prims.of_int (60)) in
  let mi = (mod) (a / (Prims.of_int (60000))) (Prims.of_int (60)) in
  let h = (mod) (a / (Prims.parse_int "3600000")) (Prims.of_int (24)) in
  let d = a / (Prims.parse_int "86400000") in
  let sign = if delta < Prims.int_zero then "-" else "" in
  let d_part =
    if d <> Prims.int_zero
    then FStar_String.concat "" [Prims.string_of_int d; "D"]
    else "" in
  let h_part =
    if h <> Prims.int_zero
    then FStar_String.concat "" [Prims.string_of_int h; "H"]
    else "" in
  let m_part =
    if mi <> Prims.int_zero
    then FStar_String.concat "" [Prims.string_of_int mi; "M"]
    else "" in
  let s_part =
    if msec <> Prims.int_zero
    then
      let pad =
        if msec < (Prims.of_int (10))
        then "00"
        else if msec < (Prims.of_int (100)) then "0" else "" in
      FStar_String.concat ""
        [Prims.string_of_int sec; "."; pad; Prims.string_of_int msec; "S"]
    else
      if sec <> Prims.int_zero
      then FStar_String.concat "" [Prims.string_of_int sec; "S"]
      else "" in
  let t_needed = ((h_part <> "") || (m_part <> "")) || (s_part <> "") in
  if (d_part = "") && (Prims.op_Negation t_needed)
  then "PT0S"
  else
    FStar_String.concat ""
      [sign;
      "P";
      d_part;
      if t_needed then "T" else "";
      h_part;
      m_part;
      s_part]
let rec dur_take_digits (cs : FStar_Char.char Prims.list) (acc : Prims.int) :
  (Prims.int * FStar_Char.char Prims.list)=
  match cs with
  | [] -> (acc, [])
  | c::rest ->
      let n = FStar_Char.int_of_char c in
      if (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
      then
        dur_take_digits rest
          ((acc * (Prims.of_int (10))) + (n - (Prims.of_int (48))))
      else (acc, cs)
let rec dur_components (cs : FStar_Char.char Prims.list)
  (in_time : Prims.bool) (acc_ms : Prims.int) :
  Prims.int FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc_ms
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x54))
      then
        (if in_time
         then FStar_Pervasives_Native.None
         else dur_components rest true acc_ms)
      else
        (let n0 = FStar_Char.int_of_char c in
         if
           Prims.op_Negation
             ((n0 >= (Prims.of_int (48))) && (n0 <= (Prims.of_int (57))))
         then FStar_Pervasives_Native.None
         else
           (let uu___2 = dur_take_digits cs Prims.int_zero in
            match uu___2 with
            | (v, after) ->
                (match after with
                 | [] -> FStar_Pervasives_Native.None
                 | d::rest2 ->
                     let dn = FStar_Char.int_of_char d in
                     if
                       (dn = (Prims.of_int (0x44))) &&
                         (Prims.op_Negation in_time)
                     then
                       (if
                          (FStar_List_Tot_Base.length rest2) <
                            (FStar_List_Tot_Base.length cs)
                        then
                          dur_components rest2 in_time
                            (acc_ms + (v * (Prims.parse_int "86400000")))
                        else FStar_Pervasives_Native.None)
                     else
                       if (dn = (Prims.of_int (0x48))) && in_time
                       then
                         (if
                            (FStar_List_Tot_Base.length rest2) <
                              (FStar_List_Tot_Base.length cs)
                          then
                            dur_components rest2 in_time
                              (acc_ms + (v * (Prims.parse_int "3600000")))
                          else FStar_Pervasives_Native.None)
                       else
                         if (dn = (Prims.of_int (0x4D))) && in_time
                         then
                           (if
                              (FStar_List_Tot_Base.length rest2) <
                                (FStar_List_Tot_Base.length cs)
                            then
                              dur_components rest2 in_time
                                (acc_ms + (v * (Prims.of_int (60000))))
                            else FStar_Pervasives_Native.None)
                         else
                           if (dn = (Prims.of_int (0x53))) && in_time
                           then
                             (if
                                (FStar_List_Tot_Base.length rest2) <
                                  (FStar_List_Tot_Base.length cs)
                              then
                                dur_components rest2 in_time
                                  (acc_ms + (v * (Prims.of_int (1000))))
                              else FStar_Pervasives_Native.None)
                           else
                             if (dn = (Prims.of_int (0x2E))) && in_time
                             then
                               (let uu___7 =
                                  dur_take_digits rest2 Prims.int_zero in
                                match uu___7 with
                                | (frac, after_frac) ->
                                    let frac_ms =
                                      if frac < (Prims.of_int (10))
                                      then frac * (Prims.of_int (100))
                                      else
                                        if frac < (Prims.of_int (100))
                                        then frac * (Prims.of_int (10))
                                        else
                                          if frac < (Prims.of_int (1000))
                                          then frac
                                          else Prims.int_zero in
                                    (match after_frac with
                                     | sm::rest3 ->
                                         if
                                           ((FStar_Char.int_of_char sm) =
                                              (Prims.of_int (0x53)))
                                             &&
                                             ((FStar_List_Tot_Base.length
                                                 rest3)
                                                <
                                                (FStar_List_Tot_Base.length
                                                   cs))
                                         then
                                           dur_components rest3 in_time
                                             ((acc_ms +
                                                 (v * (Prims.of_int (1000))))
                                                + frac_ms)
                                         else FStar_Pervasives_Native.None
                                     | [] -> FStar_Pervasives_Native.None))
                             else FStar_Pervasives_Native.None)))
let parse_dayTimeDuration_ms (lex : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match FStar_String.list_of_string lex with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      let uu___ =
        if (FStar_Char.int_of_char c) = (Prims.of_int (0x2D))
        then (true, rest)
        else (false, (c :: rest)) in
      (match uu___ with
       | (neg, body) ->
           (match body with
            | p::comps ->
                if (FStar_Char.int_of_char p) = (Prims.of_int (0x50))
                then
                  (match dur_components comps false Prims.int_zero with
                   | FStar_Pervasives_Native.Some ms ->
                       FStar_Pervasives_Native.Some
                         (if neg then Prims.int_zero - ms else ms)
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None)
                else FStar_Pervasives_Native.None
            | [] -> FStar_Pervasives_Native.None))
let unconstrained_lexical_space_datatypes : RDF_Term.wf_iri Prims.list=
  [xsd_anyURI; rdf_XMLLiteral]
let is_literal_of_datatype (expected_dt : RDF_Term.wf_iri)
  (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l ->
      if
        FStar_List_Tot_Base.mem expected_dt
          unconstrained_lexical_space_datatypes
      then l.RDF_Term.datatype = expected_dt
      else
        if is_string_family_dt expected_dt
        then
          (is_string_family_dt l.RDF_Term.datatype) &&
            (string_value_ok expected_dt l.RDF_Term.lexical_form)
        else
          if expected_dt = XSD_Datatypes.xsd_dateTime
          then
            FStar_Pervasives_Native.uu___is_Some
              (dateTime_or_date_ms l.RDF_Term.lexical_form)
          else
            if expected_dt = xsd_date
            then
              FStar_Pervasives_Native.uu___is_Some
                (date_lexical_ms l.RDF_Term.lexical_form)
            else
              Prims.op_Negation
                (literal_ill_formed_ext expected_dt l.RDF_Term.lexical_form)
  | uu___ -> false
let is_plain_literal_value (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_Literal l ->
      (l.RDF_Term.datatype = RDF_Term.xsd_string) ||
        (l.RDF_Term.datatype = RDF_Term.rdf_lang_string)
  | uu___ -> false
let is_literal_datatype_table : (Prims.string * RDF_Term.wf_iri) Prims.list=
  [("decimal", RDF_Term.xsd_decimal);
  ("double", RDF_Term.xsd_double);
  ("float", SPARQL11_Algebra.xsd_float);
  ("integer", RDF_Term.xsd_integer);
  ("long", OWL_Closure.xsd_long);
  ("int", OWL_Closure.xsd_int);
  ("short", OWL_Closure.xsd_short);
  ("byte", OWL_Closure.xsd_byte);
  ("negativeInteger", OWL_Closure.xsd_negativeInteger);
  ("nonNegativeInteger", OWL_Closure.xsd_nonNegativeInteger);
  ("nonPositiveInteger", OWL_Closure.xsd_nonPositiveInteger);
  ("positiveInteger", OWL_Closure.xsd_positiveInteger);
  ("unsignedLong", OWL_Closure.xsd_unsignedLong);
  ("unsignedInt", OWL_Closure.xsd_unsignedInt);
  ("unsignedShort", OWL_Closure.xsd_unsignedShort);
  ("unsignedByte", OWL_Closure.xsd_unsignedByte);
  ("hexBinary", xsd_hexBinary);
  ("base64Binary", xsd_base64Binary);
  ("anyURI", xsd_anyURI);
  ("boolean", RDF_Term.xsd_boolean);
  ("XMLLiteral", rdf_XMLLiteral);
  ("string", RDF_Term.xsd_string);
  ("normalizedString", xsd_normalizedString);
  ("token", xsd_token);
  ("language", xsd_language);
  ("Name", xsd_Name_dt);
  ("NCName", xsd_NCName_dt);
  ("NMTOKEN", xsd_NMTOKEN_dt);
  ("dateTime", XSD_Datatypes.xsd_dateTime);
  ("date", xsd_date)]
let rec lookup_datatype (name : Prims.string)
  (tbl : (Prims.string * RDF_Term.wf_iri) Prims.list) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match tbl with
  | [] -> FStar_Pervasives_Native.None
  | (n, dt)::rest ->
      if n = name
      then FStar_Pervasives_Native.Some dt
      else lookup_datatype name rest
let is_literal_pred_shape (local : Prims.string) :
  (RDF_Term.wf_iri * Prims.bool) FStar_Pervasives_Native.option=
  if
    ((FStar_String.strlen local) > (FStar_String.strlen "is-literal-not-"))
      &&
      ((FStar_String.sub local Prims.int_zero
          (FStar_String.strlen "is-literal-not-"))
         = "is-literal-not-")
  then
    let ty =
      FStar_String.sub local (FStar_String.strlen "is-literal-not-")
        ((FStar_String.strlen local) -
           (FStar_String.strlen "is-literal-not-")) in
    match lookup_datatype ty is_literal_datatype_table with
    | FStar_Pervasives_Native.Some dt ->
        FStar_Pervasives_Native.Some (dt, true)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else
    if
      ((FStar_String.strlen local) > (FStar_String.strlen "is-literal-")) &&
        ((FStar_String.sub local Prims.int_zero
            (FStar_String.strlen "is-literal-"))
           = "is-literal-")
    then
      (let ty =
         FStar_String.sub local (FStar_String.strlen "is-literal-")
           ((FStar_String.strlen local) - (FStar_String.strlen "is-literal-")) in
       match lookup_datatype ty is_literal_datatype_table with
       | FStar_Pervasives_Native.Some dt ->
           FStar_Pervasives_Native.Some (dt, false)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    else FStar_Pervasives_Native.None
let term_to_arith_expr (t : RDF_Term.rdf_term) :
  SPARQL11_Algebra.expr FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_integer
      then
        (match SPARQL11_Algebra.parse_int_string l.RDF_Term.lexical_form with
         | FStar_Pervasives_Native.Some n ->
             FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_NumericLit n)
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if l.RDF_Term.datatype = RDF_Term.xsd_decimal
        then
          FStar_Pervasives_Native.Some
            (SPARQL11_Algebra.E_DecimalLit (l.RDF_Term.lexical_form))
        else
          if
            (l.RDF_Term.datatype = RDF_Term.xsd_double) ||
              (l.RDF_Term.datatype = SPARQL11_Algebra.xsd_float)
          then
            FStar_Pervasives_Native.Some
              (SPARQL11_Algebra.E_DoubleLit (l.RDF_Term.lexical_form))
          else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let eval_numeric_binop (op : SPARQL11_Algebra.arith_op)
  (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match ((term_to_arith_expr a), (term_to_arith_expr b)) with
  | (FStar_Pervasives_Native.Some ea, FStar_Pervasives_Native.Some eb) ->
      let result =
        SPARQL11_Algebra.eval_expr_with_base FStar_Pervasives_Native.None
          (SPARQL11_Algebra.E_Arith (op, ea, eb)) SPARQL11_Algebra.sm_empty in
      SPARQL11_Algebra.er_to_term result
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let term_to_er (t : RDF_Term.rdf_term) : SPARQL11_Algebra.eval_result=
  match t with
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_integer
      then
        (match SPARQL11_Algebra.parse_int_string l.RDF_Term.lexical_form with
         | FStar_Pervasives_Native.Some n -> SPARQL11_Algebra.ER_Num n
         | FStar_Pervasives_Native.None -> SPARQL11_Algebra.ER_Term t)
      else
        if l.RDF_Term.datatype = RDF_Term.xsd_decimal
        then SPARQL11_Algebra.ER_Dec (l.RDF_Term.lexical_form)
        else
          if
            (l.RDF_Term.datatype = RDF_Term.xsd_double) ||
              (l.RDF_Term.datatype = SPARQL11_Algebra.xsd_float)
          then SPARQL11_Algebra.ER_Dbl (l.RDF_Term.lexical_form)
          else
            if l.RDF_Term.datatype = RDF_Term.xsd_boolean
            then
              SPARQL11_Algebra.ER_Bool
                ((l.RDF_Term.lexical_form = "true") ||
                   (l.RDF_Term.lexical_form = "1"))
            else SPARQL11_Algebra.ER_Term t
  | uu___ -> SPARQL11_Algebra.ER_Term t
let numeric_predicate (cmp : SPARQL11_Algebra.comp_op)
  (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool FStar_Pervasives_Native.option=
  SPARQL11_Algebra.value_compare (term_to_er a) (term_to_er b) cmp
let term_to_int (t : RDF_Term.rdf_term) :
  Prims.int FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_integer
      then SPARQL11_Algebra.parse_int_string l.RDF_Term.lexical_form
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let trunc_div (a : Prims.int) (b : Prims.int) : Prims.int=
  if b = Prims.int_zero
  then Prims.int_zero
  else
    (let q = a / b in
     let r = a - (q * b) in
     if
       (r <> Prims.int_zero) &&
         ((a < Prims.int_zero) <> (b < Prims.int_zero))
     then q + Prims.int_one
     else q)
let trunc_mod (a : Prims.int) (b : Prims.int) : Prims.int=
  if b = Prims.int_zero then Prims.int_zero else a - ((trunc_div a b) * b)
let mk_int_literal (n : Prims.int) : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = (Prims.string_of_int n);
      RDF_Term.datatype = RDF_Term.xsd_integer;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let rec find_last_hash_aux (cs : FStar_Char.char Prims.list)
  (idx : Prims.nat) (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x23))
      then
        find_last_hash_aux rest (idx + Prims.int_one)
          (FStar_Pervasives_Native.Some idx)
      else find_last_hash_aux rest (idx + Prims.int_one) last
let local_name_of_iri (iri : Prims.string) : Prims.string=
  match find_last_hash_aux (FStar_String.list_of_string iri) Prims.int_zero
          FStar_Pervasives_Native.None
  with
  | FStar_Pervasives_Native.None -> iri
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen iri in
      if (pos + Prims.int_one) >= len
      then ""
      else
        FStar_String.sub iri (pos + Prims.int_one)
          ((len - pos) - Prims.int_one)
let mk_string_literal (s : Prims.string) : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = s;
      RDF_Term.datatype = RDF_Term.xsd_string;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let mk_lang_literal (s : Prims.string) (lang : Prims.string) :
  RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = s;
      RDF_Term.datatype = RDF_Term.rdf_lang_string;
      RDF_Term.lang_tag = (FStar_Pervasives_Native.Some lang);
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let mk_dayTimeDuration_literal (ms : Prims.int) : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = (dayTimeDuration_of_ms ms);
      RDF_Term.datatype = xsd_dayTimeDuration;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let term_string_value (t : RDF_Term.rdf_term) :
  Prims.string FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if
        (is_string_family_dt l.RDF_Term.datatype) ||
          (l.RDF_Term.datatype = RDF_Term.rdf_lang_string)
      then FStar_Pervasives_Native.Some (l.RDF_Term.lexical_form)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let term_string_value2 (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match ((term_string_value a), (term_string_value b)) with
  | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
      FStar_Pervasives_Native.Some (sa, sb)
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let rec list_string_values (ts : RDF_Term.rdf_term Prims.list) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  match ts with
  | [] -> FStar_Pervasives_Native.Some []
  | t::rest ->
      (match ((term_string_value t), (list_string_values rest)) with
       | (FStar_Pervasives_Native.Some sv, FStar_Pervasives_Native.Some ss)
           -> FStar_Pervasives_Native.Some (sv :: ss)
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let string_family_value_equal (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term)
  : Prims.bool FStar_Pervasives_Native.option=
  match (a, b) with
  | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
      if
        (la.RDF_Term.datatype = RDF_Term.rdf_lang_string) ||
          (lb.RDF_Term.datatype = RDF_Term.rdf_lang_string)
      then
        (if
           (la.RDF_Term.datatype = RDF_Term.rdf_lang_string) &&
             (lb.RDF_Term.datatype = RDF_Term.rdf_lang_string)
         then
           FStar_Pervasives_Native.Some
             ((la.RDF_Term.lexical_form = lb.RDF_Term.lexical_form) &&
                (la.RDF_Term.lang_tag = lb.RDF_Term.lang_tag))
         else FStar_Pervasives_Native.Some false)
      else
        if
          (is_string_family_dt la.RDF_Term.datatype) &&
            (is_string_family_dt lb.RDF_Term.datatype)
        then
          FStar_Pervasives_Native.Some
            (la.RDF_Term.lexical_form = lb.RDF_Term.lexical_form)
        else FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let rec chars_compare (a : FStar_Char.char Prims.list)
  (b : FStar_Char.char Prims.list) : Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      let cx = FStar_Char.int_of_char x in
      let cy = FStar_Char.int_of_char y in
      if cx < cy
      then (Prims.of_int (-1))
      else if cx > cy then Prims.int_one else chars_compare xs ys
let string_compare_3way (a : Prims.string) (b : Prims.string) : Prims.int=
  chars_compare (FStar_String.list_of_string a)
    (FStar_String.list_of_string b)
let is_iri_to_uri_escaped_ascii (code : Prims.nat) : Prims.bool=
  (((((((((code = (Prims.of_int (0x20))) || (code = (Prims.of_int (0x22))))
           || (code = (Prims.of_int (0x3C))))
          || (code = (Prims.of_int (0x3E))))
         || (code = (Prims.of_int (0x5C))))
        || (code = (Prims.of_int (0x5E))))
       || (code = (Prims.of_int (0x60))))
      || (code = (Prims.of_int (0x7B))))
     || (code = (Prims.of_int (0x7C))))
    || (code = (Prims.of_int (0x7D)))
let rec escape_non_ascii_chars (also_uri_specials : Prims.bool)
  (cs : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      let code = FStar_Char.int_of_char c in
      let here =
        if code < (Prims.of_int (0x80))
        then
          (if also_uri_specials && (is_iri_to_uri_escaped_ascii code)
           then SPARQL11_Algebra.percent_encode_byte code
           else [c])
        else
          if code < (Prims.of_int (0x100))
          then SPARQL11_Algebra.percent_encode_byte code
          else SPARQL11_Algebra.percent_encode_char c in
      FStar_List_Tot_Base.op_At here
        (escape_non_ascii_chars also_uri_specials rest)
let fn_iri_to_uri (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (escape_non_ascii_chars true (FStar_String.list_of_string s))
let fn_escape_html_uri (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (escape_non_ascii_chars false (FStar_String.list_of_string s))
let rec split_last (xs : Prims.string Prims.list) :
  (Prims.string Prims.list * Prims.string) FStar_Pervasives_Native.option=
  match xs with
  | [] -> FStar_Pervasives_Native.None
  | x::[] -> FStar_Pervasives_Native.Some ([], x)
  | x::rest ->
      (match split_last rest with
       | FStar_Pervasives_Native.Some (init_, last_) ->
           FStar_Pervasives_Native.Some ((x :: init_), last_)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let fn_rif_substring2 (s : Prims.string) (start : Prims.int) : Prims.string=
  let st = if start < Prims.int_zero then Prims.int_zero else start in
  SPARQL11_Algebra.string_substring s st FStar_Pervasives_Native.None
let fn_rif_substring3 (s : Prims.string) (start : Prims.int)
  (len : Prims.int) : Prims.string=
  let startpos = if start < Prims.int_one then Prims.int_one else start in
  let cnt = (start + len) - startpos in
  if cnt <= Prims.int_zero
  then ""
  else
    SPARQL11_Algebra.string_substring s (startpos - Prims.int_one)
      (FStar_Pervasives_Native.Some cnt)
let lower_ascii_char (c : FStar_Char.char) : FStar_Char.char=
  let n = FStar_Char.int_of_char c in
  if (n >= (Prims.of_int (65))) && (n <= (Prims.of_int (90)))
  then FStar_Char.char_of_int (n + (Prims.of_int (32)))
  else c
let lower_ascii (s : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list= FStar_List_Tot_Base.map lower_ascii_char s
let is_star_subtag (s : FStar_Char.char Prims.list) : Prims.bool=
  match s with
  | c::[] -> (FStar_Char.int_of_char c) = (Prims.of_int (0x2A))
  | uu___ -> false
let rec lang_range_match (range : FStar_Char.char Prims.list Prims.list)
  (tag : FStar_Char.char Prims.list Prims.list) : Prims.bool=
  match (range, tag) with
  | ([], uu___) -> true
  | (r::rrest, []) -> (is_star_subtag r) && (lang_range_match rrest [])
  | (r::rrest, t::trest) ->
      if is_star_subtag r
      then (lang_range_match rrest tag) || (lang_range_match range trest)
      else
        ((lower_ascii r) = (lower_ascii t)) && (lang_range_match rrest trest)
let matches_language_range (tag : Prims.string) (range : Prims.string) :
  Prims.bool= lang_range_match (split_on_dash range) (split_on_dash tag)
let rec find_last_char_aux (code : Prims.int)
  (cs : FStar_Char.char Prims.list) (idx : Prims.nat)
  (last : Prims.nat FStar_Pervasives_Native.option) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> last
  | c::rest ->
      if (FStar_Char.int_of_char c) = code
      then
        find_last_char_aux code rest (idx + Prims.int_one)
          (FStar_Pervasives_Native.Some idx)
      else find_last_char_aux code rest (idx + Prims.int_one) last
let decode_plain_literal_packed (lex : Prims.string) : RDF_Term.rdf_term=
  match find_last_char_aux (Prims.of_int (0x40))
          (FStar_String.list_of_string lex) Prims.int_zero
          FStar_Pervasives_Native.None
  with
  | FStar_Pervasives_Native.None -> mk_string_literal lex
  | FStar_Pervasives_Native.Some pos ->
      let len = FStar_String.strlen lex in
      if pos >= len
      then mk_string_literal lex
      else
        (let text = FStar_String.sub lex Prims.int_zero pos in
         let lang =
           FStar_String.sub lex (pos + Prims.int_one)
             ((len - pos) - Prims.int_one) in
         if (FStar_String.strlen lang) = Prims.int_zero
         then mk_string_literal text
         else mk_lang_literal text lang)
let supported_cast_targets : RDF_Term.wf_iri Prims.list=
  FStar_List_Tot_Base.map (fun p -> FStar_Pervasives_Native.snd p)
    is_literal_datatype_table
let xsd_constructor_cast (op : RDF_Term.wf_iri)
  (args : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  match args with
  | (RDF_Term.T_Literal l)::[] ->
      if op = rdf_PlainLiteral_dt
      then
        FStar_Pervasives_Native.Some
          (decode_plain_literal_packed l.RDF_Term.lexical_form)
      else
        if
          ((FStar_List_Tot_Base.mem op supported_cast_targets) &&
             (op <> RDF_Term.rdf_lang_string))
            && (op <> RDF_Term.rdf_dir_lang_string)
        then
          FStar_Pervasives_Native.Some
            (RDF_Term.T_Literal
               {
                 RDF_Term.lexical_form = (l.RDF_Term.lexical_form);
                 RDF_Term.datatype = op;
                 RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                 RDF_Term.direction = FStar_Pervasives_Native.None
               })
        else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let eval_function (op : RDF_Term.wf_iri)
  (args : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term FStar_Pervasives_Native.option=
  if
    Prims.op_Negation
      (((FStar_String.strlen op) > (FStar_String.strlen rif_func_ns)) &&
         ((FStar_String.sub op Prims.int_zero
             (FStar_String.strlen rif_func_ns))
            = rif_func_ns))
  then xsd_constructor_cast op args
  else
    (let local = local_name_of_iri op in
     match (local, args) with
     | ("numeric-add", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Add a b
     | ("numeric-subtract", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Sub a b
     | ("numeric-multiply", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Mul a b
     | ("numeric-divide", a::b::[]) ->
         eval_numeric_binop SPARQL11_Algebra.Div a b
     | ("numeric-integer-divide", a::b::[]) ->
         (match ((term_to_int a), (term_to_int b)) with
          | (FStar_Pervasives_Native.Some ia, FStar_Pervasives_Native.Some
             ib) ->
              if ib = Prims.int_zero
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  (mk_int_literal (trunc_div ia ib))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("numeric-integer-mod", a::b::[]) ->
         (match ((term_to_int a), (term_to_int b)) with
          | (FStar_Pervasives_Native.Some ia, FStar_Pervasives_Native.Some
             ib) ->
              if ib = Prims.int_zero
              then FStar_Pervasives_Native.None
              else
                FStar_Pervasives_Native.Some
                  (mk_int_literal (trunc_mod ia ib))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("compare", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (mk_int_literal (string_compare_3way sa sb))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("string-length", a::[]) ->
         (match term_string_value a with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some
                (mk_int_literal (FStar_String.strlen sv))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("upper-case", a::[]) ->
         (match term_string_value a with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some
                (mk_string_literal
                   (SPARQL11_Algebra.string_uppercase_unicode sv))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("lower-case", a::[]) ->
         (match term_string_value a with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some
                (mk_string_literal
                   (SPARQL11_Algebra.string_lowercase_unicode sv))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("encode-for-uri", a::[]) ->
         (match term_string_value a with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (SPARQL11_Algebra.string_encode_uri sv))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("iri-to-uri", a::[]) ->
         (match term_string_value a with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (fn_iri_to_uri sv))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("escape-html-uri", a::[]) ->
         (match term_string_value a with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (fn_escape_html_uri sv))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("substring-before", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (SPARQL11_Algebra.string_before sa sb))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("substring-after", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (SPARQL11_Algebra.string_after sa sb))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("replace", sarg::parg::rarg::[]) ->
         (match ((term_string_value sarg), (term_string_value2 parg rarg))
          with
          | (FStar_Pervasives_Native.Some sv, FStar_Pervasives_Native.Some
             (pv, rv)) ->
              FStar_Pervasives_Native.Some
                (mk_string_literal
                   (SPARQL11_Algebra.string_replace sv pv rv
                      FStar_Pervasives_Native.None))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("substring", sarg::starg::[]) ->
         (match ((term_string_value sarg), (term_to_int starg)) with
          | (FStar_Pervasives_Native.Some sv, FStar_Pervasives_Native.Some
             stv) ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (fn_rif_substring2 sv stv))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("substring", sarg::starg::lnarg::[]) ->
         (match ((term_string_value sarg), (term_to_int starg),
                  (term_to_int lnarg))
          with
          | (FStar_Pervasives_Native.Some sv, FStar_Pervasives_Native.Some
             stv, FStar_Pervasives_Native.Some lnv) ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (fn_rif_substring3 sv stv lnv))
          | (uu___1, uu___2, uu___3) -> FStar_Pervasives_Native.None)
     | ("concat", cargs) ->
         (match list_string_values cargs with
          | FStar_Pervasives_Native.Some strs ->
              FStar_Pervasives_Native.Some
                (mk_string_literal (FStar_String.concat "" strs))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("string-join", jargs) ->
         (match list_string_values jargs with
          | FStar_Pervasives_Native.Some strs ->
              (match split_last strs with
               | FStar_Pervasives_Native.Some (parts, sep) ->
                   FStar_Pervasives_Native.Some
                     (mk_string_literal (FStar_String.concat sep parts))
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("PlainLiteral-from-string-lang", sarg::lgarg::[]) ->
         (match term_string_value2 sarg lgarg with
          | FStar_Pervasives_Native.Some (sv, lv) ->
              FStar_Pervasives_Native.Some
                (if (FStar_String.strlen lv) = Prims.int_zero
                 then mk_string_literal sv
                 else mk_lang_literal sv lv)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("string-from-PlainLiteral", x::[]) ->
         (match term_string_value x with
          | FStar_Pervasives_Native.Some sv ->
              FStar_Pervasives_Native.Some (mk_string_literal sv)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("lang-from-PlainLiteral", x::[]) ->
         (match x with
          | RDF_Term.T_Literal l ->
              if l.RDF_Term.datatype = RDF_Term.rdf_lang_string
              then
                FStar_Pervasives_Native.Some
                  (mk_string_literal
                     (match l.RDF_Term.lang_tag with
                      | FStar_Pervasives_Native.Some tg -> tg
                      | FStar_Pervasives_Native.None -> ""))
              else
                if is_string_family_dt l.RDF_Term.datatype
                then FStar_Pervasives_Native.Some (mk_string_literal "")
                else FStar_Pervasives_Native.None
          | uu___1 -> FStar_Pervasives_Native.None)
     | ("PlainLiteral-compare", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (mk_int_literal (string_compare_3way sa sb))
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("subtract-dateTimes", a::b::[]) ->
         (match (a, b) with
          | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
              (match ((dateTime_or_date_ms la.RDF_Term.lexical_form),
                       (dateTime_or_date_ms lb.RDF_Term.lexical_form))
               with
               | (FStar_Pervasives_Native.Some (ma, uu___1),
                  FStar_Pervasives_Native.Some (mb, uu___2)) ->
                   FStar_Pervasives_Native.Some
                     (mk_dayTimeDuration_literal (ma - mb))
               | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("days-from-duration", d::[]) ->
         (match d with
          | RDF_Term.T_Literal l ->
              (match parse_dayTimeDuration_ms l.RDF_Term.lexical_form with
               | FStar_Pervasives_Native.Some ms ->
                   FStar_Pervasives_Native.Some
                     (mk_int_literal
                        (trunc_div ms (Prims.parse_int "86400000")))
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          | uu___1 -> FStar_Pervasives_Native.None)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
let eval_predicate (op : RDF_Term.wf_iri)
  (args : RDF_Term.rdf_term Prims.list) :
  Prims.bool FStar_Pervasives_Native.option=
  if
    Prims.op_Negation
      (((FStar_String.strlen op) > (FStar_String.strlen rif_pred_ns)) &&
         ((FStar_String.sub op Prims.int_zero
             (FStar_String.strlen rif_pred_ns))
            = rif_pred_ns))
  then FStar_Pervasives_Native.None
  else
    (let local = local_name_of_iri op in
     match (local, args) with
     | ("numeric-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpEq a b
     | ("numeric-not-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpNe a b
     | ("numeric-less-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpLt a b
     | ("numeric-less-than-or-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpLe a b
     | ("numeric-greater-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpGt a b
     | ("numeric-greater-than-or-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpGe a b
     | ("boolean-equal", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpEq a b
     | ("boolean-less-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpLt a b
     | ("boolean-greater-than", a::b::[]) ->
         numeric_predicate SPARQL11_Algebra.CmpGt a b
     | ("literal-not-identical", a::b::[]) ->
         FStar_Pervasives_Native.Some
           (Prims.op_Negation (RDF_Term.rdf_term_eq a b))
     | ("contains", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (SPARQL11_Algebra.string_contains sa sb)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("starts-with", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (SPARQL11_Algebra.string_starts_with sa sb)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("ends-with", a::b::[]) ->
         (match term_string_value2 a b with
          | FStar_Pervasives_Native.Some (sa, sb) ->
              FStar_Pervasives_Native.Some
                (SPARQL11_Algebra.string_ends_with sa sb)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("matches", sarg::parg::[]) ->
         (match term_string_value2 sarg parg with
          | FStar_Pervasives_Native.Some (sv, pv) ->
              FStar_Pervasives_Native.Some
                (SPARQL11_Algebra.regex_match sv pv
                   FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | ("matches", sarg::parg::farg::[]) ->
         (match ((term_string_value2 sarg parg), (term_string_value farg))
          with
          | (FStar_Pervasives_Native.Some (sv, pv),
             FStar_Pervasives_Native.Some fv) ->
              FStar_Pervasives_Native.Some
                (SPARQL11_Algebra.regex_match sv pv
                   (FStar_Pervasives_Native.Some fv))
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("iri-string", a::b::[]) ->
         (match (a, (term_string_value b)) with
          | (RDF_Term.T_IRI i, FStar_Pervasives_Native.Some sv) ->
              FStar_Pervasives_Native.Some (i = sv)
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("matches-language-range", x::r::[]) ->
         (match (x, (term_string_value r)) with
          | (RDF_Term.T_Literal l, FStar_Pervasives_Native.Some rv) ->
              if l.RDF_Term.datatype = RDF_Term.rdf_lang_string
              then
                FStar_Pervasives_Native.Some
                  ((match l.RDF_Term.lang_tag with
                    | FStar_Pervasives_Native.Some tag ->
                        matches_language_range tag rv
                    | FStar_Pervasives_Native.None -> false))
              else FStar_Pervasives_Native.None
          | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
     | ("is-literal-PlainLiteral", x::[]) ->
         FStar_Pervasives_Native.Some (is_plain_literal_value x)
     | ("is-literal-not-PlainLiteral", x::[]) ->
         FStar_Pervasives_Native.Some
           (Prims.op_Negation (is_plain_literal_value x))
     | (uu___1, x::[]) ->
         (match is_literal_pred_shape local with
          | FStar_Pervasives_Native.Some (dt, negated) ->
              let v = is_literal_of_datatype dt x in
              FStar_Pervasives_Native.Some
                (if negated then Prims.op_Negation v else v)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
