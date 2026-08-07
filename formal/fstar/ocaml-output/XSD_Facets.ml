open Prims
let owl_real : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#real"
let owl_rational : RDF_Term.wf_iri= "http://www.w3.org/2002/07/owl#rational"
let xsd_float : RDF_Term.wf_iri= "http://www.w3.org/2001/XMLSchema#float"
let is_float_datatype (dt : RDF_Term.wf_iri) : Prims.bool= dt = xsd_float
let is_dense_numeric_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  ((dt = owl_real) || (dt = owl_rational)) || (dt = RDF_Term.xsd_decimal)
let is_integer_family_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  ((((((((((((dt = RDF_Term.xsd_integer) || (dt = OWL_Closure.xsd_long)) ||
              (dt = OWL_Closure.xsd_int))
             || (dt = OWL_Closure.xsd_short))
            || (dt = OWL_Closure.xsd_byte))
           || (dt = OWL_Closure.xsd_unsignedLong))
          || (dt = OWL_Closure.xsd_unsignedInt))
         || (dt = OWL_Closure.xsd_unsignedShort))
        || (dt = OWL_Closure.xsd_unsignedByte))
       || (dt = OWL_Closure.xsd_nonNegativeInteger))
      || (dt = OWL_Closure.xsd_positiveInteger))
     || (dt = OWL_Closure.xsd_nonPositiveInteger))
    || (dt = OWL_Closure.xsd_negativeInteger)
type xsd_family =
  | Fam_Numeric 
  | Fam_String 
  | Fam_Boolean 
  | Fam_Float 
  | Fam_Double 
let uu___is_Fam_Numeric (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_Numeric -> true | uu___ -> false
let uu___is_Fam_String (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_String -> true | uu___ -> false
let uu___is_Fam_Boolean (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_Boolean -> true | uu___ -> false
let uu___is_Fam_Float (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_Float -> true | uu___ -> false
let uu___is_Fam_Double (projectee : xsd_family) : Prims.bool=
  match projectee with | Fam_Double -> true | uu___ -> false
let xsd_family_eq (a : xsd_family) (b : xsd_family) : Prims.bool=
  match (a, b) with
  | (Fam_Numeric, Fam_Numeric) -> true
  | (Fam_String, Fam_String) -> true
  | (Fam_Boolean, Fam_Boolean) -> true
  | (Fam_Float, Fam_Float) -> true
  | (Fam_Double, Fam_Double) -> true
  | (uu___, uu___1) -> false
let classify_family (dt : RDF_Term.wf_iri) :
  xsd_family FStar_Pervasives_Native.option=
  if (is_integer_family_datatype dt) || (is_dense_numeric_datatype dt)
  then FStar_Pervasives_Native.Some Fam_Numeric
  else
    if dt = RDF_Term.xsd_string
    then FStar_Pervasives_Native.Some Fam_String
    else
      if dt = RDF_Term.xsd_boolean
      then FStar_Pervasives_Native.Some Fam_Boolean
      else
        if dt = xsd_float
        then FStar_Pervasives_Native.Some Fam_Float
        else
          if dt = RDF_Term.xsd_double
          then FStar_Pervasives_Native.Some Fam_Double
          else FStar_Pervasives_Native.None
let is_ascii_digit (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let digit_val (c : FStar_Char.char) : Prims.int=
  (FStar_Char.int_of_char c) - (Prims.of_int (48))
let rec digits_to_int (chars : FStar_Char.char Prims.list) (acc : Prims.int)
  : Prims.int FStar_Pervasives_Native.option=
  match chars with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::tl ->
      if is_ascii_digit c
      then digits_to_int tl ((acc * (Prims.of_int (10))) + (digit_val c))
      else FStar_Pervasives_Native.None
let parse_facet_int (lex : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let chars = FStar_String.list_of_string lex in
  match chars with
  | [] -> FStar_Pervasives_Native.None
  | c::tl ->
      let code = FStar_Char.int_of_char c in
      if code = (Prims.of_int (45))
      then
        (match tl with
         | [] -> FStar_Pervasives_Native.None
         | uu___ ->
             (match digits_to_int tl Prims.int_zero with
              | FStar_Pervasives_Native.Some v ->
                  FStar_Pervasives_Native.Some (Prims.int_zero - v)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
      else
        if code = (Prims.of_int (43))
        then
          (match tl with
           | [] -> FStar_Pervasives_Native.None
           | uu___1 -> digits_to_int tl Prims.int_zero)
        else digits_to_int chars Prims.int_zero
let literal_int_value (l : RDF_Term.literal) :
  Prims.int FStar_Pervasives_Native.option=
  if is_integer_family_datatype l.RDF_Term.datatype
  then parse_facet_int l.RDF_Term.lexical_form
  else FStar_Pervasives_Native.None
let xsd_dateTime : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#dateTime"
let is_datetime_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  dt = xsd_dateTime
let parse_digits_sub (s : Prims.string) (pos : Prims.nat) (n : Prims.nat) :
  Prims.int FStar_Pervasives_Native.option=
  if (pos + n) > (FStar_String.strlen s)
  then FStar_Pervasives_Native.None
  else
    digits_to_int (FStar_String.list_of_string (FStar_String.sub s pos n))
      Prims.int_zero
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
          match parse_digits_sub tail Prims.int_one dig_len with
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
                    match ((parse_digits_sub tail (tz_start + Prims.int_one)
                              (Prims.of_int (2))),
                            (parse_digits_sub tail
                               (tz_start + (Prims.of_int (4)))
                               (Prims.of_int (2))))
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
let dt_parse_utc_ms (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  let len = FStar_String.strlen s in
  if len < (Prims.of_int (19))
  then FStar_Pervasives_Native.None
  else
    if (FStar_String.sub s Prims.int_zero Prims.int_one) = "-"
    then FStar_Pervasives_Native.None
    else
      (match ((parse_digits_sub s Prims.int_zero (Prims.of_int (4))),
               (parse_digits_sub s (Prims.of_int (5)) (Prims.of_int (2))),
               (parse_digits_sub s (Prims.of_int (8)) (Prims.of_int (2))),
               (parse_digits_sub s (Prims.of_int (11)) (Prims.of_int (2))),
               (parse_digits_sub s (Prims.of_int (14)) (Prims.of_int (2))),
               (parse_digits_sub s (Prims.of_int (17)) (Prims.of_int (2))))
       with
       | (FStar_Pervasives_Native.Some y, FStar_Pervasives_Native.Some mo,
          FStar_Pervasives_Native.Some d, FStar_Pervasives_Native.Some h,
          FStar_Pervasives_Native.Some mi, FStar_Pervasives_Native.Some se)
           ->
           (match dt_parse_tail
                    (FStar_String.sub s (Prims.of_int (19))
                       (len - (Prims.of_int (19))))
            with
            | FStar_Pervasives_Native.Some (fms, tzoff, has_tz) ->
                if has_tz
                then
                  let days = days_from_civil y mo d in
                  let secs =
                    ((((days * (Prims.parse_int "86400")) +
                         (h * (Prims.of_int (3600))))
                        + (mi * (Prims.of_int (60))))
                       + se)
                      - tzoff in
                  FStar_Pervasives_Native.Some
                    ((secs * (Prims.of_int (1000))) + fms)
                else FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | uu___2 -> FStar_Pervasives_Native.None)
let literal_datetime_key (l : RDF_Term.literal) :
  Prims.int FStar_Pervasives_Native.option=
  if l.RDF_Term.datatype = xsd_dateTime
  then dt_parse_utc_ms l.RDF_Term.lexical_form
  else FStar_Pervasives_Native.None
let term_datetime_key (t : RDF_Term.rdf_term) :
  Prims.int FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l -> literal_datetime_key l
  | uu___ -> FStar_Pervasives_Native.None
type bound =
  | B_Unbounded 
  | B_Incl of Prims.int 
  | B_Excl of Prims.int 
let uu___is_B_Unbounded (projectee : bound) : Prims.bool=
  match projectee with | B_Unbounded -> true | uu___ -> false
let uu___is_B_Incl (projectee : bound) : Prims.bool=
  match projectee with | B_Incl _0 -> true | uu___ -> false
let __proj__B_Incl__item___0 (projectee : bound) : Prims.int=
  match projectee with | B_Incl _0 -> _0
let uu___is_B_Excl (projectee : bound) : Prims.bool=
  match projectee with | B_Excl _0 -> true | uu___ -> false
let __proj__B_Excl__item___0 (projectee : bound) : Prims.int=
  match projectee with | B_Excl _0 -> _0
type interval = {
  iv_lo: bound ;
  iv_hi: bound }
let __proj__Mkinterval__item__iv_lo (projectee : interval) : bound=
  match projectee with | { iv_lo; iv_hi;_} -> iv_lo
let __proj__Mkinterval__item__iv_hi (projectee : interval) : bound=
  match projectee with | { iv_lo; iv_hi;_} -> iv_hi
let full_interval : interval= { iv_lo = B_Unbounded; iv_hi = B_Unbounded }
let interval_empty (iv : interval) : Prims.bool=
  match ((iv.iv_lo), (iv.iv_hi)) with
  | (B_Incl lo, B_Incl hi) -> lo > hi
  | (B_Incl lo, B_Excl hi) -> lo >= hi
  | (B_Excl lo, B_Incl hi) -> lo >= hi
  | (B_Excl lo, B_Excl hi) -> lo >= (hi - Prims.int_one)
  | (uu___, uu___1) -> false
let interval_empty_dense (iv : interval) : Prims.bool=
  match ((iv.iv_lo), (iv.iv_hi)) with
  | (B_Incl lo, B_Incl hi) -> lo > hi
  | (B_Incl lo, B_Excl hi) -> lo >= hi
  | (B_Excl lo, B_Incl hi) -> lo >= hi
  | (B_Excl lo, B_Excl hi) -> lo >= hi
  | (uu___, uu___1) -> false
let tighter_lo (a : bound) (b : bound) : bound=
  match (a, b) with
  | (B_Unbounded, uu___) -> b
  | (uu___, B_Unbounded) -> a
  | (B_Incl x, B_Incl y) -> if x >= y then a else b
  | (B_Excl x, B_Excl y) -> if x >= y then a else b
  | (B_Incl x, B_Excl y) -> if x > y then a else b
  | (B_Excl x, B_Incl y) -> if x >= y then a else b
let tighter_hi (a : bound) (b : bound) : bound=
  match (a, b) with
  | (B_Unbounded, uu___) -> b
  | (uu___, B_Unbounded) -> a
  | (B_Incl x, B_Incl y) -> if x <= y then a else b
  | (B_Excl x, B_Excl y) -> if x <= y then a else b
  | (B_Incl x, B_Excl y) -> if x < y then a else b
  | (B_Excl x, B_Incl y) -> if x <= y then a else b
let interval_intersect (a : interval) (b : interval) : interval=
  {
    iv_lo = (tighter_lo a.iv_lo b.iv_lo);
    iv_hi = (tighter_hi a.iv_hi b.iv_hi)
  }
let value_in_interval (v : Prims.int) (iv : interval) : Prims.bool=
  (match iv.iv_lo with
   | B_Unbounded -> true
   | B_Incl lo -> v >= lo
   | B_Excl lo -> v > lo) &&
    (match iv.iv_hi with
     | B_Unbounded -> true
     | B_Incl hi -> v <= hi
     | B_Excl hi -> v < hi)
let base_interval_for (dt : RDF_Term.wf_iri) : interval=
  if dt = OWL_Closure.xsd_byte
  then
    {
      iv_lo = (B_Incl (Prims.of_int (-128)));
      iv_hi = (B_Incl (Prims.of_int (127)))
    }
  else
    if dt = OWL_Closure.xsd_unsignedByte
    then
      {
        iv_lo = (B_Incl Prims.int_zero);
        iv_hi = (B_Incl (Prims.of_int (255)))
      }
    else
      if dt = OWL_Closure.xsd_short
      then
        {
          iv_lo = (B_Incl (Prims.of_int (-32768)));
          iv_hi = (B_Incl (Prims.of_int (32767)))
        }
      else
        if dt = OWL_Closure.xsd_unsignedShort
        then
          {
            iv_lo = (B_Incl Prims.int_zero);
            iv_hi = (B_Incl (Prims.parse_int "65535"))
          }
        else
          if dt = OWL_Closure.xsd_int
          then
            {
              iv_lo = (B_Incl (Prims.parse_int "-2147483648"));
              iv_hi = (B_Incl (Prims.parse_int "2147483647"))
            }
          else
            if dt = OWL_Closure.xsd_unsignedInt
            then
              {
                iv_lo = (B_Incl Prims.int_zero);
                iv_hi = (B_Incl (Prims.parse_int "4294967295"))
              }
            else
              if dt = OWL_Closure.xsd_nonNegativeInteger
              then { iv_lo = (B_Incl Prims.int_zero); iv_hi = B_Unbounded }
              else
                if dt = OWL_Closure.xsd_positiveInteger
                then { iv_lo = (B_Incl Prims.int_one); iv_hi = B_Unbounded }
                else
                  if dt = OWL_Closure.xsd_nonPositiveInteger
                  then
                    { iv_lo = B_Unbounded; iv_hi = (B_Incl Prims.int_zero) }
                  else
                    if dt = OWL_Closure.xsd_negativeInteger
                    then
                      {
                        iv_lo = B_Unbounded;
                        iv_hi = (B_Incl (Prims.of_int (-1)))
                      }
                    else full_interval
let facet_min_incl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minInclusive"
let facet_max_incl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxInclusive"
let facet_min_excl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#minExclusive"
let facet_max_excl_iri : RDF_Term.wf_iri=
  "http://www.w3.org/2001/XMLSchema#maxExclusive"
let rec facets_to_interval (base_dt : RDF_Term.wf_iri)
  (facets : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list)
  (acc : interval) : interval=
  match facets with
  | [] -> acc
  | (firi, fval)::tl ->
      let acc' =
        if Prims.op_Negation (is_integer_family_datatype base_dt)
        then acc
        else
          (match fval with
           | RDF_Term.T_Literal l ->
               (match parse_facet_int l.RDF_Term.lexical_form with
                | FStar_Pervasives_Native.None -> acc
                | FStar_Pervasives_Native.Some v ->
                    if firi = facet_min_incl_iri
                    then
                      interval_intersect acc
                        { iv_lo = (B_Incl v); iv_hi = B_Unbounded }
                    else
                      if firi = facet_max_incl_iri
                      then
                        interval_intersect acc
                          { iv_lo = B_Unbounded; iv_hi = (B_Incl v) }
                      else
                        if firi = facet_min_excl_iri
                        then
                          interval_intersect acc
                            { iv_lo = (B_Excl v); iv_hi = B_Unbounded }
                        else
                          if firi = facet_max_excl_iri
                          then
                            interval_intersect acc
                              { iv_lo = B_Unbounded; iv_hi = (B_Excl v) }
                          else acc)
           | uu___1 -> acc) in
      facets_to_interval base_dt tl acc'
let rec datetime_facets_to_interval
  (facets : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list)
  (acc : interval) : interval=
  match facets with
  | [] -> acc
  | (firi, fval)::tl ->
      let acc' =
        match term_datetime_key fval with
        | FStar_Pervasives_Native.None -> acc
        | FStar_Pervasives_Native.Some v ->
            if firi = facet_min_incl_iri
            then
              interval_intersect acc
                { iv_lo = (B_Incl v); iv_hi = B_Unbounded }
            else
              if firi = facet_max_incl_iri
              then
                interval_intersect acc
                  { iv_lo = B_Unbounded; iv_hi = (B_Incl v) }
              else
                if firi = facet_min_excl_iri
                then
                  interval_intersect acc
                    { iv_lo = (B_Excl v); iv_hi = B_Unbounded }
                else
                  if firi = facet_max_excl_iri
                  then
                    interval_intersect acc
                      { iv_lo = B_Unbounded; iv_hi = (B_Excl v) }
                  else acc in
      datetime_facets_to_interval tl acc'
type rational = {
  rn_num: Prims.int ;
  rn_den: Prims.pos }
let __proj__Mkrational__item__rn_num (projectee : rational) : Prims.int=
  match projectee with | { rn_num; rn_den;_} -> rn_num
let __proj__Mkrational__item__rn_den (projectee : rational) : Prims.pos=
  match projectee with | { rn_num; rn_den;_} -> rn_den
let rec pow10 (n : Prims.nat) : Prims.pos=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec pow2i (n : Prims.nat) : Prims.pos=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (2)) * (pow2i (n - Prims.int_one))
let rational_eq (a : rational) (b : rational) : Prims.bool=
  (a.rn_num * b.rn_den) = (b.rn_num * a.rn_den)
let rec span_digits (cs : FStar_Char.char Prims.list) (accv : Prims.int)
  (accn : Prims.nat) : (Prims.int * Prims.nat * FStar_Char.char Prims.list)=
  match cs with
  | c::tl ->
      if is_ascii_digit c
      then
        span_digits tl ((accv * (Prims.of_int (10))) + (digit_val c))
          (accn + Prims.int_one)
      else (accv, accn, cs)
  | [] -> (accv, accn, cs)
let parse_decimal_rational (lex : Prims.string) :
  rational FStar_Pervasives_Native.option=
  let cs0 = FStar_String.list_of_string lex in
  let uu___ =
    match cs0 with
    | c::tl ->
        let n = FStar_Char.int_of_char c in
        if n = (Prims.of_int (45))
        then (true, tl)
        else if n = (Prims.of_int (43)) then (false, tl) else (false, cs0)
    | [] -> (false, cs0) in
  match uu___ with
  | (neg, cs1) ->
      let uu___1 = span_digits cs1 Prims.int_zero Prims.int_zero in
      (match uu___1 with
       | (ipart, ilen, cs2) ->
           let uu___2 =
             match cs2 with
             | c::tl ->
                 if (FStar_Char.int_of_char c) = (Prims.of_int (46))
                 then span_digits tl Prims.int_zero Prims.int_zero
                 else (Prims.int_zero, Prims.int_zero, cs2)
             | [] -> (Prims.int_zero, Prims.int_zero, cs2) in
           (match uu___2 with
            | (fpart, flen, cs3) ->
                let uu___3 =
                  match cs3 with
                  | c::tl ->
                      let ec = FStar_Char.int_of_char c in
                      if
                        (ec = (Prims.of_int (101))) ||
                          (ec = (Prims.of_int (69)))
                      then
                        (match tl with
                         | s::tl2 ->
                             let sn = FStar_Char.int_of_char s in
                             let uu___4 =
                               if sn = (Prims.of_int (45))
                               then (true, tl2)
                               else
                                 if sn = (Prims.of_int (43))
                                 then (false, tl2)
                                 else (false, tl) in
                             (match uu___4 with
                              | (eneg, ed) ->
                                  let uu___5 =
                                    span_digits ed Prims.int_zero
                                      Prims.int_zero in
                                  (match uu___5 with
                                   | (ev, elen, r) ->
                                       if elen = Prims.int_zero
                                       then (false, Prims.int_zero, r)
                                       else
                                         (true,
                                           (if eneg
                                            then Prims.int_zero - ev
                                            else ev), r)))
                         | [] -> (false, Prims.int_zero, cs3))
                      else (true, Prims.int_zero, cs3)
                  | [] -> (true, Prims.int_zero, cs3) in
                (match uu___3 with
                 | (ok_exp, expv, cs4) ->
                     if
                       ((Prims.op_Negation ok_exp) ||
                          (Prims.uu___is_Cons cs4))
                         || ((ilen + flen) = Prims.int_zero)
                     then FStar_Pervasives_Native.None
                     else
                       (let mantissa = (ipart * (pow10 flen)) + fpart in
                        let net = expv - flen in
                        let signed =
                          if neg then Prims.int_zero - mantissa else mantissa in
                        if net >= Prims.int_zero
                        then
                          FStar_Pervasives_Native.Some
                            {
                              rn_num = (signed * (pow10 net));
                              rn_den = Prims.int_one
                            }
                        else
                          FStar_Pervasives_Native.Some
                            {
                              rn_num = signed;
                              rn_den = (pow10 (Prims.int_zero - net))
                            }))))
let rec split_slash (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::tl ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (47))
      then FStar_Pervasives_Native.Some ((FStar_List_Tot_Base.rev acc), tl)
      else split_slash tl (c :: acc)
let parse_rational_lex (lex : Prims.string) :
  rational FStar_Pervasives_Native.option=
  match split_slash (FStar_String.list_of_string lex) [] with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ns, ds) ->
      (match ((parse_facet_int (FStar_String.string_of_list ns)),
               (parse_facet_int (FStar_String.string_of_list ds)))
       with
       | (FStar_Pervasives_Native.Some n, FStar_Pervasives_Native.Some d) ->
           if d > Prims.int_zero
           then FStar_Pervasives_Native.Some { rn_num = n; rn_den = d }
           else FStar_Pervasives_Native.None
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let term_exact_rational (t : RDF_Term.rdf_term) :
  rational FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if is_integer_family_datatype l.RDF_Term.datatype
      then
        (match parse_facet_int l.RDF_Term.lexical_form with
         | FStar_Pervasives_Native.Some v ->
             FStar_Pervasives_Native.Some
               { rn_num = v; rn_den = Prims.int_one }
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
      else
        if l.RDF_Term.datatype = RDF_Term.xsd_decimal
        then parse_decimal_rational l.RDF_Term.lexical_form
        else
          if l.RDF_Term.datatype = owl_rational
          then parse_rational_lex l.RDF_Term.lexical_form
          else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let float_ordinal_of_lexical (lex : Prims.string) :
  Prims.int FStar_Pervasives_Native.option=
  match parse_decimal_rational lex with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some r ->
      if r.rn_num = Prims.int_zero
      then FStar_Pervasives_Native.Some Prims.int_zero
      else
        if r.rn_num < Prims.int_zero
        then FStar_Pervasives_Native.None
        else
          (let n150 = r.rn_num * (pow2i (Prims.of_int (150))) in
           let den = r.rn_den in
           let twoden = (Prims.of_int (2)) * den in
           let k = (n150 + den) / twoden in
           if
             (((k >= Prims.int_one) &&
                 (k <= ((pow2i (Prims.of_int (23))) - Prims.int_one)))
                &&
                (((((Prims.of_int (2)) * k) - Prims.int_one) * den) < n150))
               && (n150 < ((((Prims.of_int (2)) * k) + Prims.int_one) * den))
           then FStar_Pervasives_Native.Some k
           else FStar_Pervasives_Native.None)
let rec float_facets_to_ordinal_interval
  (facets : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list)
  (acc : interval) : interval=
  match facets with
  | [] -> acc
  | (firi, fval)::tl ->
      let acc' =
        match fval with
        | RDF_Term.T_Literal l ->
            (match float_ordinal_of_lexical l.RDF_Term.lexical_form with
             | FStar_Pervasives_Native.None -> acc
             | FStar_Pervasives_Native.Some v ->
                 if firi = facet_min_incl_iri
                 then
                   interval_intersect acc
                     { iv_lo = (B_Incl v); iv_hi = B_Unbounded }
                 else
                   if firi = facet_max_incl_iri
                   then
                     interval_intersect acc
                       { iv_lo = B_Unbounded; iv_hi = (B_Incl v) }
                   else
                     if firi = facet_min_excl_iri
                     then
                       interval_intersect acc
                         { iv_lo = (B_Excl v); iv_hi = B_Unbounded }
                     else
                       if firi = facet_max_excl_iri
                       then
                         interval_intersect acc
                           { iv_lo = B_Unbounded; iv_hi = (B_Excl v) }
                       else acc)
        | uu___ -> acc in
      float_facets_to_ordinal_interval tl acc'
let float_restriction_provably_empty (dt : RDF_Term.wf_iri)
  (facets : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list) : Prims.bool=
  (is_float_datatype dt) &&
    (interval_empty (float_facets_to_ordinal_interval facets full_interval))
type float_special =
  | FSpec_PosInf 
  | FSpec_NegInf 
  | FSpec_NaN 
let uu___is_FSpec_PosInf (projectee : float_special) : Prims.bool=
  match projectee with | FSpec_PosInf -> true | uu___ -> false
let uu___is_FSpec_NegInf (projectee : float_special) : Prims.bool=
  match projectee with | FSpec_NegInf -> true | uu___ -> false
let uu___is_FSpec_NaN (projectee : float_special) : Prims.bool=
  match projectee with | FSpec_NaN -> true | uu___ -> false
let float_special_of_lexical (lex : Prims.string) :
  float_special FStar_Pervasives_Native.option=
  if (lex = "INF") || (lex = "+INF")
  then FStar_Pervasives_Native.Some FSpec_PosInf
  else
    if lex = "-INF"
    then FStar_Pervasives_Native.Some FSpec_NegInf
    else
      if lex = "NaN"
      then FStar_Pervasives_Native.Some FSpec_NaN
      else FStar_Pervasives_Native.None
let is_floating_point_datatype (dt : RDF_Term.wf_iri) : Prims.bool=
  (dt = xsd_float) || (dt = RDF_Term.xsd_double)
let term_float_special (t : RDF_Term.rdf_term) :
  float_special FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if is_floating_point_datatype l.RDF_Term.datatype
      then float_special_of_lexical l.RDF_Term.lexical_form
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let term_in_owl_real (t : RDF_Term.rdf_term) :
  Prims.bool FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      (match classify_family l.RDF_Term.datatype with
       | FStar_Pervasives_Native.Some (Fam_Numeric) ->
           FStar_Pervasives_Native.Some true
       | FStar_Pervasives_Native.Some uu___ ->
           FStar_Pervasives_Native.Some false
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rational_le (a : rational) (b : rational) : Prims.bool=
  (a.rn_num * b.rn_den) <= (b.rn_num * a.rn_den)
let rational_lt (a : rational) (b : rational) : Prims.bool=
  (a.rn_num * b.rn_den) < (b.rn_num * a.rn_den)
type qbound =
  | QB_Unbounded 
  | QB_Incl of rational 
  | QB_Excl of rational 
let uu___is_QB_Unbounded (projectee : qbound) : Prims.bool=
  match projectee with | QB_Unbounded -> true | uu___ -> false
let uu___is_QB_Incl (projectee : qbound) : Prims.bool=
  match projectee with | QB_Incl _0 -> true | uu___ -> false
let __proj__QB_Incl__item___0 (projectee : qbound) : rational=
  match projectee with | QB_Incl _0 -> _0
let uu___is_QB_Excl (projectee : qbound) : Prims.bool=
  match projectee with | QB_Excl _0 -> true | uu___ -> false
let __proj__QB_Excl__item___0 (projectee : qbound) : rational=
  match projectee with | QB_Excl _0 -> _0
type qinterval = {
  qv_lo: qbound ;
  qv_hi: qbound }
let __proj__Mkqinterval__item__qv_lo (projectee : qinterval) : qbound=
  match projectee with | { qv_lo; qv_hi;_} -> qv_lo
let __proj__Mkqinterval__item__qv_hi (projectee : qinterval) : qbound=
  match projectee with | { qv_lo; qv_hi;_} -> qv_hi
let full_qinterval : qinterval=
  { qv_lo = QB_Unbounded; qv_hi = QB_Unbounded }
let rational_in_qinterval (v : rational) (iv : qinterval) : Prims.bool=
  (match iv.qv_lo with
   | QB_Unbounded -> true
   | QB_Incl lo -> rational_le lo v
   | QB_Excl lo -> rational_lt lo v) &&
    (match iv.qv_hi with
     | QB_Unbounded -> true
     | QB_Incl hi -> rational_le v hi
     | QB_Excl hi -> rational_lt v hi)
let qtighter_lo (a : qbound) (b : qbound) : qbound=
  match (a, b) with
  | (QB_Unbounded, uu___) -> b
  | (uu___, QB_Unbounded) -> a
  | (QB_Incl x, QB_Incl y) -> if rational_le y x then a else b
  | (QB_Excl x, QB_Excl y) -> if rational_le y x then a else b
  | (QB_Incl x, QB_Excl y) -> if rational_lt y x then a else b
  | (QB_Excl x, QB_Incl y) -> if rational_le y x then a else b
let qtighter_hi (a : qbound) (b : qbound) : qbound=
  match (a, b) with
  | (QB_Unbounded, uu___) -> b
  | (uu___, QB_Unbounded) -> a
  | (QB_Incl x, QB_Incl y) -> if rational_le x y then a else b
  | (QB_Excl x, QB_Excl y) -> if rational_le x y then a else b
  | (QB_Incl x, QB_Excl y) -> if rational_lt x y then a else b
  | (QB_Excl x, QB_Incl y) -> if rational_le x y then a else b
let qinterval_intersect (a : qinterval) (b : qinterval) : qinterval=
  {
    qv_lo = (qtighter_lo a.qv_lo b.qv_lo);
    qv_hi = (qtighter_hi a.qv_hi b.qv_hi)
  }
let qinterval_empty (iv : qinterval) : Prims.bool=
  match ((iv.qv_lo), (iv.qv_hi)) with
  | (QB_Incl lo, QB_Incl hi) -> rational_lt hi lo
  | (QB_Incl lo, QB_Excl hi) -> rational_le hi lo
  | (QB_Excl lo, QB_Incl hi) -> rational_le hi lo
  | (QB_Excl lo, QB_Excl hi) -> rational_le hi lo
  | (uu___, uu___1) -> false
let rational_floor (r : rational) : Prims.int=
  let q = r.rn_num / r.rn_den in
  if (q * r.rn_den) > r.rn_num then q - Prims.int_one else q
let rational_ceil (r : rational) : Prims.int=
  let q = r.rn_num / r.rn_den in
  if (q * r.rn_den) < r.rn_num then q + Prims.int_one else q
let rational_is_integer (r : rational) : Prims.bool=
  ((rational_floor r) * r.rn_den) = r.rn_num
let qbound_to_int_lo (b : qbound) : bound=
  match b with
  | QB_Unbounded -> B_Unbounded
  | QB_Incl r -> B_Incl (rational_ceil r)
  | QB_Excl r ->
      B_Incl
        (if rational_is_integer r
         then (rational_floor r) + Prims.int_one
         else rational_ceil r)
let qbound_to_int_hi (b : qbound) : bound=
  match b with
  | QB_Unbounded -> B_Unbounded
  | QB_Incl r -> B_Incl (rational_floor r)
  | QB_Excl r ->
      B_Incl
        (if rational_is_integer r
         then (rational_ceil r) - Prims.int_one
         else rational_floor r)
let qinterval_to_int_interval (iv : qinterval) : interval=
  { iv_lo = (qbound_to_int_lo iv.qv_lo); iv_hi = (qbound_to_int_hi iv.qv_hi)
  }
let rec dense_facets_to_qinterval
  (facets : (RDF_Term.wf_iri * RDF_Term.rdf_term) Prims.list)
  (acc : qinterval) : qinterval=
  match facets with
  | [] -> acc
  | (firi, fval)::tl ->
      let acc' =
        match term_exact_rational fval with
        | FStar_Pervasives_Native.None -> acc
        | FStar_Pervasives_Native.Some v ->
            if firi = facet_min_incl_iri
            then
              qinterval_intersect acc
                { qv_lo = (QB_Incl v); qv_hi = QB_Unbounded }
            else
              if firi = facet_max_incl_iri
              then
                qinterval_intersect acc
                  { qv_lo = QB_Unbounded; qv_hi = (QB_Incl v) }
              else
                if firi = facet_min_excl_iri
                then
                  qinterval_intersect acc
                    { qv_lo = (QB_Excl v); qv_hi = QB_Unbounded }
                else
                  if firi = facet_max_excl_iri
                  then
                    qinterval_intersect acc
                      { qv_lo = QB_Unbounded; qv_hi = (QB_Excl v) }
                  else acc in
      dense_facets_to_qinterval tl acc'
type value_set =
  | VS_Unconstrained 
  | VS_Interval of interval 
  | VS_Dense of qinterval 
  | VS_DateInterval of interval 
  | VS_Enum of RDF_Term.rdf_term Prims.list 
  | VS_Family of xsd_family 
  | VS_Empty 
let uu___is_VS_Unconstrained (projectee : value_set) : Prims.bool=
  match projectee with | VS_Unconstrained -> true | uu___ -> false
let uu___is_VS_Interval (projectee : value_set) : Prims.bool=
  match projectee with | VS_Interval _0 -> true | uu___ -> false
let __proj__VS_Interval__item___0 (projectee : value_set) : interval=
  match projectee with | VS_Interval _0 -> _0
let uu___is_VS_Dense (projectee : value_set) : Prims.bool=
  match projectee with | VS_Dense _0 -> true | uu___ -> false
let __proj__VS_Dense__item___0 (projectee : value_set) : qinterval=
  match projectee with | VS_Dense _0 -> _0
let uu___is_VS_DateInterval (projectee : value_set) : Prims.bool=
  match projectee with | VS_DateInterval _0 -> true | uu___ -> false
let __proj__VS_DateInterval__item___0 (projectee : value_set) : interval=
  match projectee with | VS_DateInterval _0 -> _0
let uu___is_VS_Enum (projectee : value_set) : Prims.bool=
  match projectee with | VS_Enum _0 -> true | uu___ -> false
let __proj__VS_Enum__item___0 (projectee : value_set) :
  RDF_Term.rdf_term Prims.list= match projectee with | VS_Enum _0 -> _0
let uu___is_VS_Family (projectee : value_set) : Prims.bool=
  match projectee with | VS_Family _0 -> true | uu___ -> false
let __proj__VS_Family__item___0 (projectee : value_set) : xsd_family=
  match projectee with | VS_Family _0 -> _0
let uu___is_VS_Empty (projectee : value_set) : Prims.bool=
  match projectee with | VS_Empty -> true | uu___ -> false
let term_int_opt (t : RDF_Term.rdf_term) :
  Prims.int FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l -> literal_int_value l
  | uu___ -> FStar_Pervasives_Native.None
let term_family (t : RDF_Term.rdf_term) :
  xsd_family FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l -> classify_family l.RDF_Term.datatype
  | uu___ -> FStar_Pervasives_Native.None
let term_bool_opt (t : RDF_Term.rdf_term) :
  Prims.bool FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_boolean
      then
        (if
           (l.RDF_Term.lexical_form = "true") ||
             (l.RDF_Term.lexical_form = "1")
         then FStar_Pervasives_Native.Some true
         else
           if
             (l.RDF_Term.lexical_form = "false") ||
               (l.RDF_Term.lexical_form = "0")
           then FStar_Pervasives_Native.Some false
           else FStar_Pervasives_Native.None)
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let term_provably_equal (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  ((RDF_Term.rdf_term_eq a b) ||
     (match ((term_int_opt a), (term_int_opt b)) with
      | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
          x = y
      | (uu___, uu___1) ->
          (match ((term_bool_opt a), (term_bool_opt b)) with
           | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y)
               -> x = y
           | (uu___2, uu___3) -> false)))
    ||
    (match ((term_exact_rational a), (term_exact_rational b)) with
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         rational_eq x y
     | (uu___, uu___1) -> false)
let both_string (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.bool=
  match (a, b) with
  | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
      (la.RDF_Term.datatype = RDF_Term.xsd_string) &&
        (lb.RDF_Term.datatype = RDF_Term.xsd_string)
  | (uu___, uu___1) -> false
let string_lex_neq (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  match (a, b) with
  | (RDF_Term.T_Literal la, RDF_Term.T_Literal lb) ->
      la.RDF_Term.lexical_form <> lb.RDF_Term.lexical_form
  | (uu___, uu___1) -> false
let term_provably_distinct (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) :
  Prims.bool=
  (((match ((term_int_opt a), (term_int_opt b)) with
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         x <> y
     | (uu___, uu___1) -> false) ||
      (match ((term_family a), (term_family b)) with
       | (FStar_Pervasives_Native.Some fa, FStar_Pervasives_Native.Some fb)
           -> Prims.op_Negation (xsd_family_eq fa fb)
       | (uu___, uu___1) -> false))
     || ((both_string a b) && (string_lex_neq a b)))
    ||
    (match ((term_bool_opt a), (term_bool_opt b)) with
     | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
         x <> y
     | (uu___, uu___1) -> false)
let rec all_literal_terms (ts : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match ts with
  | [] -> true
  | (RDF_Term.T_Literal uu___)::tl -> all_literal_terms tl
  | uu___ -> false
let rec filter_enum_by (f : RDF_Term.rdf_term -> Prims.bool)
  (xs : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match xs with
  | [] -> []
  | h::tl -> if f h then h :: (filter_enum_by f tl) else filter_enum_by f tl
let rec enum_intersect (xs : RDF_Term.rdf_term Prims.list)
  (ys : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match xs with
  | [] -> []
  | h::tl ->
      if FStar_List_Tot_Base.for_all (term_provably_distinct h) ys
      then enum_intersect tl ys
      else h :: (enum_intersect tl ys)
let provably_outside_interval (iv : interval) (t : RDF_Term.rdf_term) :
  Prims.bool=
  (match term_int_opt t with
   | FStar_Pervasives_Native.Some v ->
       Prims.op_Negation (value_in_interval v iv)
   | FStar_Pervasives_Native.None -> false) ||
    (match term_family t with
     | FStar_Pervasives_Native.Some f ->
         Prims.op_Negation (xsd_family_eq f Fam_Numeric)
     | FStar_Pervasives_Native.None -> false)
let provably_outside_family (f : xsd_family) (t : RDF_Term.rdf_term) :
  Prims.bool=
  match term_family t with
  | FStar_Pervasives_Native.Some g -> Prims.op_Negation (xsd_family_eq f g)
  | FStar_Pervasives_Native.None -> false
let provably_outside_date_interval (iv : interval) (t : RDF_Term.rdf_term) :
  Prims.bool=
  (match term_datetime_key t with
   | FStar_Pervasives_Native.Some v ->
       Prims.op_Negation (value_in_interval v iv)
   | FStar_Pervasives_Native.None -> false) ||
    (FStar_Pervasives_Native.uu___is_Some (term_family t))
let provably_outside_dense (iv : qinterval) (t : RDF_Term.rdf_term) :
  Prims.bool=
  (match term_exact_rational t with
   | FStar_Pervasives_Native.Some q ->
       Prims.op_Negation (rational_in_qinterval q iv)
   | FStar_Pervasives_Native.None -> false) ||
    (match term_family t with
     | FStar_Pervasives_Native.Some f ->
         Prims.op_Negation (xsd_family_eq f Fam_Numeric)
     | FStar_Pervasives_Native.None -> false)
let value_set_intersect (a : value_set) (b : value_set) : value_set=
  match (a, b) with
  | (VS_Empty, uu___) -> VS_Empty
  | (uu___, VS_Empty) -> VS_Empty
  | (VS_Unconstrained, x) -> x
  | (x, VS_Unconstrained) -> x
  | (VS_Dense qa, VS_Dense qb) ->
      let qi = qinterval_intersect qa qb in
      if qinterval_empty qi then VS_Empty else VS_Dense qi
  | (VS_Dense qa, VS_Interval ib) ->
      let ii = interval_intersect (qinterval_to_int_interval qa) ib in
      if interval_empty ii then VS_Empty else VS_Interval ii
  | (VS_Interval ia, VS_Dense qb) ->
      let ii = interval_intersect ia (qinterval_to_int_interval qb) in
      if interval_empty ii then VS_Empty else VS_Interval ii
  | (VS_Dense qa, VS_Enum xs) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_dense qa t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_Dense qb) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_dense qb t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Dense qa, VS_Family f) ->
      if xsd_family_eq f Fam_Numeric then VS_Dense qa else VS_Empty
  | (VS_Family f, VS_Dense qb) ->
      if xsd_family_eq f Fam_Numeric then VS_Dense qb else VS_Empty
  | (VS_Dense uu___, VS_DateInterval uu___1) -> VS_Empty
  | (VS_DateInterval uu___, VS_Dense uu___1) -> VS_Empty
  | (VS_Interval ia, VS_Interval ib) ->
      let ii = interval_intersect ia ib in
      if interval_empty ii then VS_Empty else VS_Interval ii
  | (VS_DateInterval ia, VS_DateInterval ib) ->
      let ii = interval_intersect ia ib in
      if interval_empty_dense ii then VS_Empty else VS_DateInterval ii
  | (VS_DateInterval uu___, VS_Interval uu___1) -> VS_Empty
  | (VS_Interval uu___, VS_DateInterval uu___1) -> VS_Empty
  | (VS_DateInterval uu___, VS_Family uu___1) -> VS_Empty
  | (VS_Family uu___, VS_DateInterval uu___1) -> VS_Empty
  | (VS_DateInterval iv, VS_Enum xs) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_date_interval iv t))
          xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_DateInterval iv) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_date_interval iv t))
          xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_Enum ys) ->
      let e = enum_intersect xs ys in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_Interval iv) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_interval iv t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Interval iv, VS_Enum xs) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_interval iv t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Enum xs, VS_Family f) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_family f t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Family f, VS_Enum xs) ->
      let e =
        filter_enum_by
          (fun t -> Prims.op_Negation (provably_outside_family f t)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (VS_Interval iv, VS_Family f) ->
      if xsd_family_eq f Fam_Numeric then VS_Interval iv else VS_Empty
  | (VS_Family f, VS_Interval iv) ->
      if xsd_family_eq f Fam_Numeric then VS_Interval iv else VS_Empty
  | (VS_Family fa, VS_Family fb) ->
      if xsd_family_eq fa fb then VS_Family fa else VS_Empty
let value_set_is_empty (v : value_set) : Prims.bool=
  match v with
  | VS_Empty -> true
  | VS_Enum [] -> true
  | VS_DateInterval iv -> interval_empty_dense iv
  | VS_Dense qi -> qinterval_empty qi
  | uu___ -> false
let bound_lo_incl (b : bound) : Prims.int FStar_Pervasives_Native.option=
  match b with
  | B_Unbounded -> FStar_Pervasives_Native.None
  | B_Incl x -> FStar_Pervasives_Native.Some x
  | B_Excl x -> FStar_Pervasives_Native.Some (x + Prims.int_one)
let bound_hi_incl (b : bound) : Prims.int FStar_Pervasives_Native.option=
  match b with
  | B_Unbounded -> FStar_Pervasives_Native.None
  | B_Incl x -> FStar_Pervasives_Native.Some x
  | B_Excl x -> FStar_Pervasives_Native.Some (x - Prims.int_one)
let interval_count (iv : interval) :
  Prims.nat FStar_Pervasives_Native.option=
  match ((bound_lo_incl iv.iv_lo), (bound_hi_incl iv.iv_hi)) with
  | (FStar_Pervasives_Native.Some lo, FStar_Pervasives_Native.Some hi) ->
      if hi >= lo
      then FStar_Pervasives_Native.Some ((hi - lo) + Prims.int_one)
      else FStar_Pervasives_Native.Some Prims.int_zero
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let rec drop_provably_equal (h : RDF_Term.rdf_term)
  (xs : RDF_Term.rdf_term Prims.list) : RDF_Term.rdf_term Prims.list=
  match xs with
  | [] -> []
  | x::tl ->
      let rest = drop_provably_equal h tl in
      if term_provably_equal h x then rest else x :: rest
let rec enum_distinct_count (xs : RDF_Term.rdf_term Prims.list) : Prims.nat=
  match xs with
  | [] -> Prims.int_zero
  | h::tl -> Prims.int_one + (enum_distinct_count (drop_provably_equal h tl))
let value_set_max_size (v : value_set) :
  Prims.nat FStar_Pervasives_Native.option=
  match v with
  | VS_Empty -> FStar_Pervasives_Native.Some Prims.int_zero
  | VS_Enum [] -> FStar_Pervasives_Native.Some Prims.int_zero
  | VS_Enum xs -> FStar_Pervasives_Native.Some (enum_distinct_count xs)
  | VS_Interval iv -> interval_count iv
  | VS_DateInterval iv ->
      if interval_empty_dense iv
      then FStar_Pervasives_Native.Some Prims.int_zero
      else FStar_Pervasives_Native.None
  | VS_Dense qi ->
      if qinterval_empty qi
      then FStar_Pervasives_Native.Some Prims.int_zero
      else FStar_Pervasives_Native.None
  | VS_Unconstrained -> FStar_Pervasives_Native.None
  | VS_Family uu___ -> FStar_Pervasives_Native.None
let value_set_subtract (acc : value_set) (remove : value_set) : value_set=
  match (acc, remove) with
  | (VS_Enum xs, VS_Enum ys) ->
      let e =
        filter_enum_by
          (fun t ->
             Prims.op_Negation
               (FStar_List_Tot_Base.existsb (term_provably_equal t) ys)) xs in
      if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
  | (uu___, uu___1) -> acc
let exact_enum_cap : Prims.nat= (Prims.of_int (4096))
let int_literal_term (n : Prims.int) : RDF_Term.rdf_term=
  let l =
    {
      RDF_Term.lexical_form = (Prims.string_of_int n);
      RDF_Term.datatype = RDF_Term.xsd_integer;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    } in
  RDF_Term.T_Literal l
let rec int_range_literals (lo : Prims.int) (n : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  if n = Prims.int_zero
  then []
  else (int_literal_term lo) ::
    (int_range_literals (lo + Prims.int_one) (n - Prims.int_one))
let rec pairwise_provably_distinct (xs : RDF_Term.rdf_term Prims.list) :
  Prims.bool=
  match xs with
  | [] -> true
  | h::tl ->
      (FStar_List_Tot_Base.for_all (term_provably_distinct h) tl) &&
        (pairwise_provably_distinct tl)
let value_set_exact_values (v : value_set) :
  RDF_Term.rdf_term Prims.list FStar_Pervasives_Native.option=
  match v with
  | VS_Empty -> FStar_Pervasives_Native.Some []
  | VS_Enum xs ->
      if pairwise_provably_distinct xs
      then FStar_Pervasives_Native.Some xs
      else FStar_Pervasives_Native.None
  | VS_Interval iv ->
      (match interval_count iv with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some n ->
           if n > exact_enum_cap
           then FStar_Pervasives_Native.None
           else
             (match bound_lo_incl iv.iv_lo with
              | FStar_Pervasives_Native.Some lo ->
                  FStar_Pervasives_Native.Some (int_range_literals lo n)
              | FStar_Pervasives_Native.None ->
                  if n = Prims.int_zero
                  then FStar_Pervasives_Native.Some []
                  else FStar_Pervasives_Native.None))
  | uu___ -> FStar_Pervasives_Native.None
let remove_negated_values (negs : RDF_Term.rdf_term Prims.list)
  (v : value_set) : value_set=
  if Prims.uu___is_Nil negs
  then v
  else
    (match v with
     | VS_Enum xs ->
         let e =
           filter_enum_by
             (fun t ->
                Prims.op_Negation
                  (FStar_List_Tot_Base.existsb (term_provably_equal t) negs))
             xs in
         if Prims.uu___is_Nil e then VS_Empty else VS_Enum e
     | VS_Interval iv ->
         (match interval_count iv with
          | FStar_Pervasives_Native.Some n ->
              if n <= (FStar_List_Tot_Base.length negs)
              then
                (match value_set_exact_values v with
                 | FStar_Pervasives_Native.Some vs ->
                     if
                       FStar_List_Tot_Base.for_all
                         (fun t ->
                            FStar_List_Tot_Base.existsb
                              (term_provably_equal t) negs) vs
                     then VS_Empty
                     else v
                 | FStar_Pervasives_Native.None -> v)
              else v
          | FStar_Pervasives_Native.None -> v)
     | uu___1 -> v)
