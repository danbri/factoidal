open Prims
let parse_int_string :
  Prims.string -> Prims.int FStar_Pervasives_Native.option=
  SPARQL11_Algebra.parse_int_string
let parse_to_scaled :
  Prims.string -> (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  SPARQL11_Algebra.parse_to_scaled
let parse_double_to_scaled :
  Prims.string -> (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  SPARQL11_Algebra.parse_double_to_scaled
let pow10 : Prims.nat -> Prims.int= SPARQL11_Algebra.pow10
let xsd_dateTime : RDF_Graph_Executable.wf_iri= SPARQL11_Algebra.xsd_dateTime
let xsd_float : RDF_Graph_Executable.wf_iri= SPARQL11_Algebra.xsd_float
let literal_to_scaled (l : RDF_Graph_Executable.literal) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  if l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_double
  then parse_double_to_scaled l.RDF_Graph_Executable.lexical_form
  else
    if
      (l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_integer) ||
        (l.RDF_Graph_Executable.datatype = RDF_Graph_Executable.xsd_decimal)
    then parse_to_scaled l.RDF_Graph_Executable.lexical_form
    else FStar_Pervasives_Native.None
let scaled_cmp (a : (Prims.int * Prims.nat)) (b : (Prims.int * Prims.nat)) :
  Prims.int=
  let uu___ = a in
  match uu___ with
  | (am, asc) ->
      let uu___1 = b in
      (match uu___1 with
       | (bm, bsc) ->
           if asc = bsc
           then
             (if am < bm
              then (Prims.of_int (-1))
              else if am > bm then Prims.int_one else Prims.int_zero)
           else
             if asc < bsc
             then
               (let am' = am * (pow10 (bsc - asc)) in
                if am' < bm
                then (Prims.of_int (-1))
                else if am' > bm then Prims.int_one else Prims.int_zero)
             else
               (let bm' = bm * (pow10 (asc - bsc)) in
                if am < bm'
                then (Prims.of_int (-1))
                else if am > bm' then Prims.int_one else Prims.int_zero))
let days_from_civil (y : Prims.int) (m : Prims.int) (d : Prims.int) :
  Prims.int=
  let y' = if m <= (Prims.of_int (2)) then y - Prims.int_one else y in
  let era =
    (if y' >= Prims.int_zero then y' else y' - (Prims.of_int (399))) /
      (Prims.of_int (400)) in
  let yoe = y' - (era * (Prims.of_int (400))) in
  let mp = (mod) (m + (Prims.of_int (9))) (Prims.of_int (12)) in
  let doy =
    (((((Prims.of_int (153)) * mp) + (Prims.of_int (2))) / (Prims.of_int (5)))
       + d)
      - Prims.int_one in
  let doe =
    (((yoe * (Prims.of_int (365))) + (yoe / (Prims.of_int (4)))) -
       (yoe / (Prims.of_int (100))))
      + doy in
  ((era * (Prims.parse_int "146097")) + doe) - (Prims.parse_int "719468")
let dt_parse_tail (tail : Prims.string) :
  (Prims.int * Prims.int * Prims.bool) FStar_Pervasives_Native.option=
  let len = FStar_String.strlen tail in
  let uu___ =
    if
      (len >= (Prims.of_int (2))) &&
        ((FStar_String.sub tail Prims.int_zero Prims.int_one) = ".")
    then
      let rec frac_end pos =
        if pos < len
        then
          let c = FStar_Char.int_of_char (FStar_String.index tail pos) in
          (if (c >= (Prims.of_int (48))) && (c <= (Prims.of_int (57)))
           then frac_end (pos + Prims.int_one)
           else pos)
        else pos in
      let fe = frac_end Prims.int_one in
      (if fe = Prims.int_one
       then (FStar_Pervasives_Native.None, Prims.int_zero)
       else
         (let dig_len =
            if (fe - Prims.int_one) > (Prims.of_int (3))
            then (Prims.of_int (3))
            else fe - Prims.int_one in
          match parse_int_string
                  (FStar_String.sub tail Prims.int_one dig_len)
          with
          | FStar_Pervasives_Native.Some f ->
              let ms =
                if dig_len = Prims.int_one
                then f * (Prims.of_int (100))
                else
                  if dig_len = (Prims.of_int (2))
                  then f * (Prims.of_int (10))
                  else f in
              ((FStar_Pervasives_Native.Some ms), fe)
          | FStar_Pervasives_Native.None ->
              (FStar_Pervasives_Native.None, Prims.int_zero)))
    else ((FStar_Pervasives_Native.Some Prims.int_zero), Prims.int_zero) in
  match uu___ with
  | (frac_ms, tz_start) ->
      (match frac_ms with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some fms ->
           let rest_len = len - tz_start in
           if rest_len = Prims.int_zero
           then FStar_Pervasives_Native.Some (fms, Prims.int_zero, false)
           else
             if
               (rest_len = Prims.int_one) &&
                 ((FStar_String.sub tail tz_start Prims.int_one) = "Z")
             then FStar_Pervasives_Native.Some (fms, Prims.int_zero, true)
             else
               if rest_len = (Prims.of_int (6))
               then
                 (let sign_s = FStar_String.sub tail tz_start Prims.int_one in
                  if (sign_s = "+") || (sign_s = "-")
                  then
                    match ((parse_int_string
                              (FStar_String.sub tail
                                 (tz_start + Prims.int_one)
                                 (Prims.of_int (2)))),
                            (parse_int_string
                               (FStar_String.sub tail
                                  (tz_start + (Prims.of_int (4)))
                                  (Prims.of_int (2)))))
                    with
                    | (FStar_Pervasives_Native.Some th,
                       FStar_Pervasives_Native.Some tm) ->
                        let off =
                          (th * (Prims.of_int (3600))) +
                            (tm * (Prims.of_int (60))) in
                        FStar_Pervasives_Native.Some
                          (fms,
                            ((if sign_s = "-"
                              then Prims.int_zero - off
                              else off)), true)
                    | (uu___3, uu___4) -> FStar_Pervasives_Native.None
                  else FStar_Pervasives_Native.None)
               else FStar_Pervasives_Native.None)
let dt_parse_ms (s : Prims.string) :
  (Prims.int * Prims.bool) FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    (match ((parse_int_string
               (FStar_String.sub s Prims.int_zero (Prims.of_int (4)))),
             (parse_int_string
                (FStar_String.sub s (Prims.of_int (5)) (Prims.of_int (2)))),
             (parse_int_string
                (FStar_String.sub s (Prims.of_int (8)) (Prims.of_int (2)))),
             (parse_int_string
                (FStar_String.sub s (Prims.of_int (11)) (Prims.of_int (2)))),
             (parse_int_string
                (FStar_String.sub s (Prims.of_int (14)) (Prims.of_int (2)))),
             (parse_int_string
                (FStar_String.sub s (Prims.of_int (17)) (Prims.of_int (2)))))
     with
     | (FStar_Pervasives_Native.Some y, FStar_Pervasives_Native.Some mo,
        FStar_Pervasives_Native.Some d, FStar_Pervasives_Native.Some h,
        FStar_Pervasives_Native.Some mi, FStar_Pervasives_Native.Some se) ->
         (match dt_parse_tail
                  (FStar_String.sub s (Prims.of_int (19))
                     (len - (Prims.of_int (19))))
          with
          | FStar_Pervasives_Native.Some (fms, tzoff, has_tz) ->
              let days = days_from_civil y mo d in
              let secs =
                ((((days * (Prims.parse_int "86400")) +
                     (h * (Prims.of_int (3600))))
                    + (mi * (Prims.of_int (60))))
                   + se)
                  - tzoff in
              FStar_Pervasives_Native.Some
                (((secs * (Prims.of_int (1000))) + fms), has_tz)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
     | (uu___1, uu___2, uu___3, uu___4, uu___5, uu___6) ->
         FStar_Pervasives_Native.None)
let dt_cmp (a : Prims.string) (b : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match ((dt_parse_ms a), (dt_parse_ms b)) with
  | (FStar_Pervasives_Native.Some (ma, tza), FStar_Pervasives_Native.Some
     (mb, tzb)) ->
      if tza = tzb
      then
        FStar_Pervasives_Native.Some
          ((if ma < mb
            then (Prims.of_int (-1))
            else if ma > mb then Prims.int_one else Prims.int_zero))
      else FStar_Pervasives_Native.None
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let both_datetimes (a : RDF_Graph_Executable.literal)
  (b : RDF_Graph_Executable.literal) : Prims.bool=
  (a.RDF_Graph_Executable.datatype = xsd_dateTime) &&
    (b.RDF_Graph_Executable.datatype = xsd_dateTime)
let numeric_cmp_le (a : RDF_Graph_Executable.literal)
  (b : RDF_Graph_Executable.literal) :
  Prims.bool FStar_Pervasives_Native.option=
  if both_datetimes a b
  then
    match dt_cmp a.RDF_Graph_Executable.lexical_form
            b.RDF_Graph_Executable.lexical_form
    with
    | FStar_Pervasives_Native.Some c ->
        FStar_Pervasives_Native.Some (c <= Prims.int_zero)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else
    (match ((literal_to_scaled a), (literal_to_scaled b)) with
     | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
         FStar_Pervasives_Native.Some ((scaled_cmp sa sb) <= Prims.int_zero)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
let numeric_cmp_lt (a : RDF_Graph_Executable.literal)
  (b : RDF_Graph_Executable.literal) :
  Prims.bool FStar_Pervasives_Native.option=
  if both_datetimes a b
  then
    match dt_cmp a.RDF_Graph_Executable.lexical_form
            b.RDF_Graph_Executable.lexical_form
    with
    | FStar_Pervasives_Native.Some c ->
        FStar_Pervasives_Native.Some (c < Prims.int_zero)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else
    (match ((literal_to_scaled a), (literal_to_scaled b)) with
     | (FStar_Pervasives_Native.Some sa, FStar_Pervasives_Native.Some sb) ->
         FStar_Pervasives_Native.Some ((scaled_cmp sa sb) < Prims.int_zero)
     | (uu___1, uu___2) -> FStar_Pervasives_Native.None)
let is_ascii_digit (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let is_signed_digits_chars (chars : FStar_Char.char Prims.list) : Prims.bool=
  match chars with
  | [] -> false
  | c::rest ->
      let ci = FStar_Char.int_of_char c in
      let digits =
        if (ci = (Prims.of_int (43))) || (ci = (Prims.of_int (45)))
        then rest
        else c :: rest in
      (Prims.uu___is_Cons digits) &&
        (FStar_List_Tot_Base.for_all is_ascii_digit digits)
let is_decimal_lexical_chars (chars : FStar_Char.char Prims.list) :
  Prims.bool=
  match chars with
  | [] -> false
  | c::rest ->
      let ci = FStar_Char.int_of_char c in
      let body =
        if (ci = (Prims.of_int (43))) || (ci = (Prims.of_int (45)))
        then rest
        else c :: rest in
      (((Prims.uu___is_Cons body) &&
          (FStar_List_Tot_Base.for_all
             (fun ch ->
                (is_ascii_digit ch) ||
                  ((FStar_Char.int_of_char ch) = (Prims.of_int (46)))) body))
         &&
         ((FStar_List_Tot_Base.length
             (FStar_List_Tot_Base.filter
                (fun ch -> (FStar_Char.int_of_char ch) = (Prims.of_int (46)))
                body))
            <= Prims.int_one))
        && (FStar_List_Tot_Base.existsb is_ascii_digit body)
let is_integer_lexical (lex : Prims.string) : Prims.bool=
  is_signed_digits_chars (FStar_String.list_of_string lex)
let is_decimal_lexical (lex : Prims.string) : Prims.bool=
  is_decimal_lexical_chars (FStar_String.list_of_string lex)
let rec split_at_e (chars : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match chars with
  | [] -> ([], FStar_Pervasives_Native.None)
  | c::rest ->
      let n = FStar_Char.int_of_char c in
      if (n = (Prims.of_int (101))) || (n = (Prims.of_int (69)))
      then ([], (FStar_Pervasives_Native.Some rest))
      else
        (let uu___1 = split_at_e rest in
         match uu___1 with | (before, after) -> ((c :: before), after))
let is_float_lexical (lex : Prims.string) : Prims.bool=
  if ((lex = "NaN") || (lex = "INF")) || (lex = "-INF")
  then true
  else
    (let uu___1 = split_at_e (FStar_String.list_of_string lex) in
     match uu___1 with
     | (mantissa, exp_opt) ->
         (is_decimal_lexical_chars mantissa) &&
           ((match exp_opt with
             | FStar_Pervasives_Native.None -> true
             | FStar_Pervasives_Native.Some e -> is_signed_digits_chars e)))
let strip_leading_plus (lex : Prims.string) : Prims.string=
  if
    ((FStar_String.strlen lex) > Prims.int_zero) &&
      ((FStar_String.sub lex Prims.int_zero Prims.int_one) = "+")
  then
    FStar_String.sub lex Prims.int_one
      ((FStar_String.strlen lex) - Prims.int_one)
  else lex
let int_lexical_in_range (lex : Prims.string)
  (lo : Prims.int FStar_Pervasives_Native.option)
  (hi : Prims.int FStar_Pervasives_Native.option) : Prims.bool=
  (is_integer_lexical lex) &&
    (match parse_int_string (strip_leading_plus lex) with
     | FStar_Pervasives_Native.Some n ->
         (match lo with
          | FStar_Pervasives_Native.Some l -> n >= l
          | FStar_Pervasives_Native.None -> true) &&
           ((match hi with
             | FStar_Pervasives_Native.Some h -> n <= h
             | FStar_Pervasives_Native.None -> true))
     | FStar_Pervasives_Native.None -> true)
let literal_ill_formed (dt : RDF_Graph_Executable.wf_iri)
  (lex : Prims.string) : Prims.bool=
  if dt = RDF_Graph_Executable.xsd_boolean
  then
    Prims.op_Negation
      ((((lex = "true") || (lex = "false")) || (lex = "1")) || (lex = "0"))
  else
    if dt = RDF_Graph_Executable.xsd_integer
    then Prims.op_Negation (is_integer_lexical lex)
    else
      if dt = RDF_Graph_Executable.xsd_decimal
      then Prims.op_Negation (is_decimal_lexical lex)
      else
        if dt = RDF_Graph_Executable.xsd_long
        then
          Prims.op_Negation
            (int_lexical_in_range lex
               (FStar_Pervasives_Native.Some
                  (Prims.parse_int "-9223372036854775808"))
               (FStar_Pervasives_Native.Some
                  (Prims.parse_int "9223372036854775807")))
        else
          if dt = RDF_Graph_Executable.xsd_int
          then
            Prims.op_Negation
              (int_lexical_in_range lex
                 (FStar_Pervasives_Native.Some
                    (Prims.parse_int "-2147483648"))
                 (FStar_Pervasives_Native.Some (Prims.parse_int "2147483647")))
          else
            if dt = RDF_Graph_Executable.xsd_short
            then
              Prims.op_Negation
                (int_lexical_in_range lex
                   (FStar_Pervasives_Native.Some (Prims.of_int (-32768)))
                   (FStar_Pervasives_Native.Some (Prims.of_int (32767))))
            else
              if dt = RDF_Graph_Executable.xsd_byte
              then
                Prims.op_Negation
                  (int_lexical_in_range lex
                     (FStar_Pervasives_Native.Some (Prims.of_int (-128)))
                     (FStar_Pervasives_Native.Some (Prims.of_int (127))))
              else
                if dt = RDF_Graph_Executable.xsd_unsignedLong
                then
                  Prims.op_Negation
                    (int_lexical_in_range lex
                       (FStar_Pervasives_Native.Some Prims.int_zero)
                       (FStar_Pervasives_Native.Some
                          (Prims.parse_int "18446744073709551615")))
                else
                  if dt = RDF_Graph_Executable.xsd_unsignedInt
                  then
                    Prims.op_Negation
                      (int_lexical_in_range lex
                         (FStar_Pervasives_Native.Some Prims.int_zero)
                         (FStar_Pervasives_Native.Some
                            (Prims.parse_int "4294967295")))
                  else
                    if dt = RDF_Graph_Executable.xsd_unsignedShort
                    then
                      Prims.op_Negation
                        (int_lexical_in_range lex
                           (FStar_Pervasives_Native.Some Prims.int_zero)
                           (FStar_Pervasives_Native.Some
                              (Prims.parse_int "65535")))
                    else
                      if dt = RDF_Graph_Executable.xsd_unsignedByte
                      then
                        Prims.op_Negation
                          (int_lexical_in_range lex
                             (FStar_Pervasives_Native.Some Prims.int_zero)
                             (FStar_Pervasives_Native.Some
                                (Prims.of_int (255))))
                      else
                        if dt = RDF_Graph_Executable.xsd_nonNegativeInteger
                        then
                          Prims.op_Negation
                            (int_lexical_in_range lex
                               (FStar_Pervasives_Native.Some Prims.int_zero)
                               FStar_Pervasives_Native.None)
                        else
                          if dt = RDF_Graph_Executable.xsd_positiveInteger
                          then
                            Prims.op_Negation
                              (int_lexical_in_range lex
                                 (FStar_Pervasives_Native.Some Prims.int_one)
                                 FStar_Pervasives_Native.None)
                          else
                            if
                              dt =
                                RDF_Graph_Executable.xsd_nonPositiveInteger
                            then
                              Prims.op_Negation
                                (int_lexical_in_range lex
                                   FStar_Pervasives_Native.None
                                   (FStar_Pervasives_Native.Some
                                      Prims.int_zero))
                            else
                              if
                                dt = RDF_Graph_Executable.xsd_negativeInteger
                              then
                                Prims.op_Negation
                                  (int_lexical_in_range lex
                                     FStar_Pervasives_Native.None
                                     (FStar_Pervasives_Native.Some
                                        (Prims.of_int (-1))))
                              else
                                if dt = xsd_dateTime
                                then
                                  FStar_Pervasives_Native.uu___is_None
                                    (dt_parse_ms lex)
                                else
                                  if
                                    (dt = xsd_float) ||
                                      (dt = RDF_Graph_Executable.xsd_double)
                                  then
                                    Prims.op_Negation (is_float_lexical lex)
                                  else false
let is_decimal_derived_datatype (dt : RDF_Graph_Executable.wf_iri) :
  Prims.bool=
  (((((((((((((dt = RDF_Graph_Executable.xsd_decimal) ||
                (dt = RDF_Graph_Executable.xsd_integer))
               || (dt = RDF_Graph_Executable.xsd_long))
              || (dt = RDF_Graph_Executable.xsd_int))
             || (dt = RDF_Graph_Executable.xsd_short))
            || (dt = RDF_Graph_Executable.xsd_byte))
           || (dt = RDF_Graph_Executable.xsd_unsignedLong))
          || (dt = RDF_Graph_Executable.xsd_unsignedInt))
         || (dt = RDF_Graph_Executable.xsd_unsignedShort))
        || (dt = RDF_Graph_Executable.xsd_unsignedByte))
       || (dt = RDF_Graph_Executable.xsd_nonNegativeInteger))
      || (dt = RDF_Graph_Executable.xsd_positiveInteger))
     || (dt = RDF_Graph_Executable.xsd_nonPositiveInteger))
    || (dt = RDF_Graph_Executable.xsd_negativeInteger)
