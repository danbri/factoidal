open Prims
let chars_of (s : Prims.string) : FStar_Char.char Prims.list=
  FStar_String.list_of_string s
let string_of (l : FStar_Char.char Prims.list) : Prims.string=
  FStar_String.string_of_list l
let code (c : FStar_Char.char) : Prims.int= FStar_Char.int_of_char c
let is_digit (c : FStar_Char.char) : Prims.bool=
  let i = code c in (i >= (Prims.of_int (48))) && (i <= (Prims.of_int (57)))
let char_zero : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (48))
let dot_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (46))
let plus_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (43))
let minus_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (45))
let percent_char : FStar_Char.char=
  FStar_Char.char_of_int (Prims.of_int (37))
let permille_char : FStar_Char.char=
  FStar_Char.char_of_int (Prims.of_int (8240))
let big_e_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (69))
let cap_z_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (90))
let colon_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (58))
let quote_char : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (39))
let first_char (s : Prims.string) :
  FStar_Char.char FStar_Pervasives_Native.option=
  match chars_of s with
  | [] -> FStar_Pervasives_Native.None
  | c::uu___ -> FStar_Pervasives_Native.Some c
let rec all_digits (l : FStar_Char.char Prims.list) : Prims.bool=
  match l with | [] -> true | c::tl -> (is_digit c) && (all_digits tl)
let rec count_char (target : FStar_Char.char)
  (l : FStar_Char.char Prims.list) : Prims.nat=
  match l with
  | [] -> Prims.int_zero
  | c::tl ->
      (if (code c) = (code target) then Prims.int_one else Prims.int_zero) +
        (count_char target tl)
let rec split_first (sep : FStar_Char.char) (l : FStar_Char.char Prims.list)
  :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match l with
  | [] -> FStar_Pervasives_Native.None
  | c::tl ->
      if (code c) = (code sep)
      then FStar_Pervasives_Native.Some ([], tl)
      else
        (match split_first sep tl with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (a, b) ->
             FStar_Pervasives_Native.Some ((c :: a), b))
let rec split_all (sep : FStar_Char.char) (l : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list Prims.list=
  match l with
  | [] -> [[]]
  | c::tl ->
      if (code c) = (code sep)
      then [] :: (split_all sep tl)
      else
        (match split_all sep tl with
         | seg::rest -> (c :: seg) :: rest
         | [] -> [[c]])
let rec drop_leading_zeros (l : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match l with
  | [] -> [char_zero]
  | c::[] -> [c]
  | c::tl ->
      if (code c) = (Prims.of_int (48))
      then drop_leading_zeros tl
      else c :: tl
let rec repeat_char (c : FStar_Char.char) (n : Prims.nat) :
  FStar_Char.char Prims.list=
  if n = Prims.int_zero then [] else c :: (repeat_char c (n - Prims.int_one))
type fmt_outcome =
  | FO_NoFormat 
  | FO_Valid of Prims.string 
  | FO_Invalid 
let uu___is_FO_NoFormat (projectee : fmt_outcome) : Prims.bool=
  match projectee with | FO_NoFormat -> true | uu___ -> false
let uu___is_FO_Valid (projectee : fmt_outcome) : Prims.bool=
  match projectee with | FO_Valid _0 -> true | uu___ -> false
let __proj__FO_Valid__item___0 (projectee : fmt_outcome) : Prims.string=
  match projectee with | FO_Valid _0 -> _0
let uu___is_FO_Invalid (projectee : fmt_outcome) : Prims.bool=
  match projectee with | FO_Invalid -> true | uu___ -> false
let is_integer_base (n : Prims.string) : Prims.bool=
  ((((((((((((n = "integer") || (n = "long")) || (n = "int")) ||
             (n = "short"))
            || (n = "byte"))
           || (n = "nonNegativeInteger"))
          || (n = "positiveInteger"))
         || (n = "nonPositiveInteger"))
        || (n = "negativeInteger"))
       || (n = "unsignedLong"))
      || (n = "unsignedInt"))
     || (n = "unsignedShort"))
    || (n = "unsignedByte")
let is_double_base (n : Prims.string) : Prims.bool=
  ((n = "double") || (n = "float")) || (n = "number")
let is_decimal_base (n : Prims.string) : Prims.bool= n = "decimal"
let is_numeric_base (n : Prims.string) : Prims.bool=
  ((is_integer_base n) || (is_double_base n)) || (is_decimal_base n)
let is_date_base (n : Prims.string) : Prims.bool=
  ((((n = "date") || (n = "time")) || (n = "dateTime")) ||
     (n = "dateTimeStamp"))
    || (n = "datetime")
type num_fmt =
  {
  nf_min_int: Prims.nat ;
  nf_prim_grp: Prims.nat ;
  nf_sec_grp: Prims.nat ;
  nf_grp_req: Prims.bool ;
  nf_min_frac: Prims.nat ;
  nf_max_frac: Prims.nat ;
  nf_has_exp: Prims.bool ;
  nf_group: FStar_Char.char ;
  nf_decimal: FStar_Char.char }
let __proj__Mknum_fmt__item__nf_min_int (projectee : num_fmt) : Prims.nat=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_min_int
let __proj__Mknum_fmt__item__nf_prim_grp (projectee : num_fmt) : Prims.nat=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_prim_grp
let __proj__Mknum_fmt__item__nf_sec_grp (projectee : num_fmt) : Prims.nat=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_sec_grp
let __proj__Mknum_fmt__item__nf_grp_req (projectee : num_fmt) : Prims.bool=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_grp_req
let __proj__Mknum_fmt__item__nf_min_frac (projectee : num_fmt) : Prims.nat=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_min_frac
let __proj__Mknum_fmt__item__nf_max_frac (projectee : num_fmt) : Prims.nat=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_max_frac
let __proj__Mknum_fmt__item__nf_has_exp (projectee : num_fmt) : Prims.bool=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_has_exp
let __proj__Mknum_fmt__item__nf_group (projectee : num_fmt) :
  FStar_Char.char=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_group
let __proj__Mknum_fmt__item__nf_decimal (projectee : num_fmt) :
  FStar_Char.char=
  match projectee with
  | { nf_min_int; nf_prim_grp; nf_sec_grp; nf_grp_req; nf_min_frac;
      nf_max_frac; nf_has_exp; nf_group; nf_decimal;_} -> nf_decimal
let count_zeros (l : FStar_Char.char Prims.list) : Prims.nat=
  count_char char_zero l
let rec count_places (l : FStar_Char.char Prims.list) : Prims.nat=
  match l with
  | [] -> Prims.int_zero
  | c::tl ->
      (if
         ((code c) = (Prims.of_int (48))) || ((code c) = (Prims.of_int (35)))
       then Prims.int_one
       else Prims.int_zero) + (count_places tl)
let grouping_of (grp : FStar_Char.char)
  (int_pat : FStar_Char.char Prims.list) : (Prims.nat * Prims.nat)=
  let segs = split_all grp int_pat in
  match segs with
  | [] -> (Prims.int_zero, Prims.int_zero)
  | uu___::[] -> (Prims.int_zero, Prims.int_zero)
  | uu___ ->
      let n = FStar_List_Tot_Base.length segs in
      let prim =
        count_places (FStar_List_Tot_Base.index segs (n - Prims.int_one)) in
      let sec =
        if n >= (Prims.of_int (3))
        then
          count_places
            (FStar_List_Tot_Base.index segs (n - (Prims.of_int (2))))
        else prim in
      (prim, sec)
let parse_num_fmt (pat : FStar_Char.char Prims.list) (grp : FStar_Char.char)
  (dec : FStar_Char.char) : num_fmt=
  let has_exp = (count_char big_e_char pat) > Prims.int_zero in
  let body =
    match split_first big_e_char pat with
    | FStar_Pervasives_Native.Some (a, uu___) -> a
    | FStar_Pervasives_Native.None -> pat in
  let uu___ =
    match split_first dec body with
    | FStar_Pervasives_Native.Some (a, b) -> (a, b)
    | FStar_Pervasives_Native.None -> (body, []) in
  match uu___ with
  | (int_pat, frac_pat) ->
      let uu___1 = grouping_of grp int_pat in
      (match uu___1 with
       | (prim, sec) ->
           let frac_digits_pat =
             FStar_List_Tot_Base.filter (fun c -> (code c) <> (code grp))
               frac_pat in
           {
             nf_min_int = (count_zeros int_pat);
             nf_prim_grp = prim;
             nf_sec_grp = sec;
             nf_grp_req = (prim > Prims.int_zero);
             nf_min_frac = (count_zeros frac_digits_pat);
             nf_max_frac = (count_places frac_digits_pat);
             nf_has_exp = has_exp;
             nf_group = grp;
             nf_decimal = dec
           })
let default_num_fmt (grp : FStar_Char.char) (dec : FStar_Char.char) :
  num_fmt=
  {
    nf_min_int = Prims.int_zero;
    nf_prim_grp = (Prims.of_int (3));
    nf_sec_grp = (Prims.of_int (3));
    nf_grp_req = false;
    nf_min_frac = Prims.int_zero;
    nf_max_frac = (Prims.parse_int "1000000");
    nf_has_exp = false;
    nf_group = grp;
    nf_decimal = dec
  }
let validate_int_group (prim : Prims.nat) (sec : Prims.nat)
  (grp_req : Prims.bool) (grp : FStar_Char.char)
  (int_chars : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  let segs = split_all grp int_chars in
  match segs with
  | [] -> FStar_Pervasives_Native.Some []
  | only::[] ->
      if Prims.op_Negation (all_digits only)
      then FStar_Pervasives_Native.None
      else
        if prim = Prims.int_zero
        then FStar_Pervasives_Native.Some only
        else
          if Prims.op_Negation grp_req
          then FStar_Pervasives_Native.Some only
          else
            if (FStar_List_Tot_Base.length only) <= prim
            then FStar_Pervasives_Native.Some only
            else FStar_Pervasives_Native.None
  | uu___ ->
      if prim = Prims.int_zero
      then FStar_Pervasives_Native.None
      else
        (let n = FStar_List_Tot_Base.length segs in
         let rec ok i =
           if i >= n
           then true
           else
             (let seg = FStar_List_Tot_Base.index segs i in
              if
                (Prims.op_Negation (all_digits seg)) ||
                  ((FStar_List_Tot_Base.length seg) = Prims.int_zero)
              then false
              else
                (let want =
                   if i = (n - Prims.int_one)
                   then prim
                   else if i = Prims.int_zero then sec else sec in
                 let seg_ok =
                   if i = Prims.int_zero
                   then (FStar_List_Tot_Base.length seg) <= want
                   else (FStar_List_Tot_Base.length seg) = want in
                 if seg_ok then ok (i + Prims.int_one) else false)) in
         if ok Prims.int_zero
         then
           FStar_Pervasives_Native.Some
             (FStar_List_Tot_Base.concatMap (fun s -> s) segs)
         else FStar_Pervasives_Native.None)
let assemble_number (neg : Prims.bool)
  (int_digits : FStar_Char.char Prims.list)
  (frac_digits : FStar_Char.char Prims.list) (shift : Prims.nat) :
  FStar_Char.char Prims.list=
  let sign = if neg then [minus_char] else [] in
  if shift = Prims.int_zero
  then
    let ip = drop_leading_zeros int_digits in
    match frac_digits with
    | [] -> FStar_List_Tot_Base.op_At sign ip
    | uu___ ->
        FStar_List_Tot_Base.op_At sign
          (FStar_List_Tot_Base.op_At ip (dot_char :: frac_digits))
  else
    (let alldigits = FStar_List_Tot_Base.op_At int_digits frac_digits in
     let newfrac = (FStar_List_Tot_Base.length frac_digits) + shift in
     let alllen = FStar_List_Tot_Base.length alldigits in
     let padded =
       if newfrac >= alllen
       then
         FStar_List_Tot_Base.op_At
           (repeat_char char_zero ((newfrac - alllen) + Prims.int_one))
           alldigits
       else alldigits in
     let padlen = FStar_List_Tot_Base.length padded in
     let intlen =
       if padlen >= newfrac then padlen - newfrac else Prims.int_zero in
     let ipart =
       FStar_Pervasives_Native.fst
         (FStar_List_Tot_Base.splitAt intlen padded) in
     let fpart =
       FStar_Pervasives_Native.snd
         (FStar_List_Tot_Base.splitAt intlen padded) in
     let ip = drop_leading_zeros ipart in
     FStar_List_Tot_Base.op_At sign
       (FStar_List_Tot_Base.op_At ip (dot_char :: fpart)))
let parse_number (nf : num_fmt) (base_name : Prims.string)
  (v0 : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  let has_pct = (count_char percent_char v0) > Prims.int_zero in
  let has_pm = (count_char permille_char v0) > Prims.int_zero in
  let shift =
    if has_pct
    then (Prims.of_int (2))
    else if has_pm then (Prims.of_int (3)) else Prims.int_zero in
  let v1 =
    FStar_List_Tot_Base.filter
      (fun c ->
         ((code c) <> (code percent_char)) &&
           ((code c) <> (code permille_char))) v0 in
  let uu___ =
    match v1 with
    | c::rest ->
        if (code c) = (code minus_char)
        then (true, rest)
        else
          if (code c) = (code plus_char) then (false, rest) else (false, v1)
    | uu___1 -> (false, v1) in
  match uu___ with
  | (neg, v2) ->
      let uu___1 =
        if nf.nf_has_exp
        then
          match split_first big_e_char v2 with
          | FStar_Pervasives_Native.Some (a, b) ->
              (a, (FStar_Pervasives_Native.Some b))
          | FStar_Pervasives_Native.None ->
              (v2, FStar_Pervasives_Native.None)
        else (v2, FStar_Pervasives_Native.None) in
      (match uu___1 with
       | (mant, exp_opt) ->
           if nf.nf_has_exp && (exp_opt = FStar_Pervasives_Native.None)
           then FStar_Pervasives_Native.None
           else
             (let uu___3 =
                match split_first nf.nf_decimal mant with
                | FStar_Pervasives_Native.Some (a, b) -> (a, b, true)
                | FStar_Pervasives_Native.None -> (mant, [], false) in
              match uu___3 with
              | (int_chars, frac_chars_raw, has_dec) ->
                  (match validate_int_group nf.nf_prim_grp nf.nf_sec_grp
                           nf.nf_grp_req nf.nf_group int_chars
                   with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some int_digits ->
                       let frac_digits =
                         FStar_List_Tot_Base.filter
                           (fun c -> (code c) <> (code nf.nf_group))
                           frac_chars_raw in
                       if Prims.op_Negation (all_digits frac_digits)
                       then FStar_Pervasives_Native.None
                       else
                         if
                           has_dec &&
                             ((FStar_List_Tot_Base.length frac_digits) =
                                Prims.int_zero)
                         then FStar_Pervasives_Native.None
                         else
                           if
                             (FStar_List_Tot_Base.length int_digits) =
                               Prims.int_zero
                           then FStar_Pervasives_Native.None
                           else
                             (let flen =
                                FStar_List_Tot_Base.length frac_digits in
                              if
                                (is_integer_base base_name) &&
                                  (has_dec || (flen > Prims.int_zero))
                              then FStar_Pervasives_Native.None
                              else
                                if
                                  (FStar_List_Tot_Base.length int_digits) <
                                    nf.nf_min_int
                                then FStar_Pervasives_Native.None
                                else
                                  if flen < nf.nf_min_frac
                                  then FStar_Pervasives_Native.None
                                  else
                                    if flen > nf.nf_max_frac
                                    then FStar_Pervasives_Native.None
                                    else
                                      (let sign_txt =
                                         match v1 with
                                         | c::uu___11 ->
                                             if (code c) = (code plus_char)
                                             then [plus_char]
                                             else
                                               if
                                                 (code c) = (code minus_char)
                                               then [minus_char]
                                               else []
                                         | uu___11 -> [] in
                                       let mant_norm =
                                         FStar_List_Tot_Base.op_At sign_txt
                                           (FStar_List_Tot_Base.op_At
                                              int_digits
                                              (if has_dec
                                               then dot_char :: frac_digits
                                               else [])) in
                                       match exp_opt with
                                       | FStar_Pervasives_Native.Some exp ->
                                           let uu___11 =
                                             match exp with
                                             | c::rest ->
                                                 if
                                                   (code c) =
                                                     (code minus_char)
                                                 then ([minus_char], rest)
                                                 else
                                                   if
                                                     (code c) =
                                                       (code plus_char)
                                                   then ([], rest)
                                                   else ([], exp)
                                             | uu___12 -> ([], exp) in
                                           (match uu___11 with
                                            | (esign, edig) ->
                                                if
                                                  ((FStar_List_Tot_Base.length
                                                      edig)
                                                     = Prims.int_zero)
                                                    ||
                                                    (Prims.op_Negation
                                                       (all_digits edig))
                                                then
                                                  FStar_Pervasives_Native.None
                                                else
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_List_Tot_Base.op_At
                                                       mant_norm
                                                       ((FStar_Char.char_of_int
                                                           (Prims.of_int (101)))
                                                       ::
                                                       (FStar_List_Tot_Base.op_At
                                                          esign edig))))
                                       | FStar_Pervasives_Native.None ->
                                           if shift = Prims.int_zero
                                           then
                                             FStar_Pervasives_Native.Some
                                               mant_norm
                                           else
                                             FStar_Pervasives_Native.Some
                                               (assemble_number neg
                                                  int_digits frac_digits
                                                  shift))))))
type dt_acc =
  {
  d_year: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_mon: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_day: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_hour: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_min: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_sec: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_frac: FStar_Char.char Prims.list FStar_Pervasives_Native.option ;
  d_tz: FStar_Char.char Prims.list FStar_Pervasives_Native.option }
let __proj__Mkdt_acc__item__d_year (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_year
let __proj__Mkdt_acc__item__d_mon (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_mon
let __proj__Mkdt_acc__item__d_day (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_day
let __proj__Mkdt_acc__item__d_hour (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_hour
let __proj__Mkdt_acc__item__d_min (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_min
let __proj__Mkdt_acc__item__d_sec (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_sec
let __proj__Mkdt_acc__item__d_frac (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_frac
let __proj__Mkdt_acc__item__d_tz (projectee : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { d_year; d_mon; d_day; d_hour; d_min; d_sec; d_frac; d_tz;_} -> d_tz
let dt_empty : dt_acc=
  {
    d_year = FStar_Pervasives_Native.None;
    d_mon = FStar_Pervasives_Native.None;
    d_day = FStar_Pervasives_Native.None;
    d_hour = FStar_Pervasives_Native.None;
    d_min = FStar_Pervasives_Native.None;
    d_sec = FStar_Pervasives_Native.None;
    d_frac = FStar_Pervasives_Native.None;
    d_tz = FStar_Pervasives_Native.None
  }
let rec take_digits (maxn : Prims.nat) (v : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match v with
  | [] -> FStar_Pervasives_Native.None
  | c::tl ->
      if Prims.op_Negation (is_digit c)
      then FStar_Pervasives_Native.None
      else
        if maxn <= Prims.int_one
        then FStar_Pervasives_Native.Some ([c], tl)
        else
          (match tl with
           | c2::uu___2 ->
               if is_digit c2
               then
                 (match take_digits (maxn - Prims.int_one) tl with
                  | FStar_Pervasives_Native.Some (ds, rest) ->
                      FStar_Pervasives_Native.Some ((c :: ds), rest)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.Some ([c], tl))
               else FStar_Pervasives_Native.Some ([c], tl)
           | uu___2 -> FStar_Pervasives_Native.Some ([c], tl))
let rec take_exact (n : Prims.nat) (v : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  if n = Prims.int_zero
  then FStar_Pervasives_Native.Some ([], v)
  else
    (match v with
     | c::tl ->
         if is_digit c
         then
           (match take_exact (n - Prims.int_one) tl with
            | FStar_Pervasives_Native.Some (ds, rest) ->
                FStar_Pervasives_Native.Some ((c :: ds), rest)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
         else FStar_Pervasives_Native.None
     | uu___1 -> FStar_Pervasives_Native.None)
let rec take_digits_greedy (v : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match v with
  | c::tl ->
      if is_digit c
      then
        (match take_digits_greedy tl with
         | FStar_Pervasives_Native.Some (ds, rest) ->
             FStar_Pervasives_Native.Some ((c :: ds), rest)
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some ([c], tl))
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let parse_tz (allow_z : Prims.bool) (v : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list)
    FStar_Pervasives_Native.option=
  match v with
  | c::tl ->
      if allow_z && ((code c) = (code cap_z_char))
      then FStar_Pervasives_Native.Some ([cap_z_char], tl)
      else
        if ((code c) = (code plus_char)) || ((code c) = (code minus_char))
        then
          (let sgn = c in
           match take_exact (Prims.of_int (2)) tl with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (hh, r1) ->
               let after_colon =
                 match r1 with
                 | c2::r ->
                     if (code c2) = (code colon_char)
                     then FStar_Pervasives_Native.Some r
                     else FStar_Pervasives_Native.None
                 | uu___1 -> FStar_Pervasives_Native.None in
               let uu___1 =
                 match after_colon with
                 | FStar_Pervasives_Native.Some r ->
                     (match take_exact (Prims.of_int (2)) r with
                      | FStar_Pervasives_Native.Some (m, rr) -> (m, rr)
                      | FStar_Pervasives_Native.None ->
                          ([char_zero; char_zero], r1))
                 | FStar_Pervasives_Native.None ->
                     (match take_exact (Prims.of_int (2)) r1 with
                      | FStar_Pervasives_Native.Some (m, rr) -> (m, rr)
                      | FStar_Pervasives_Native.None ->
                          ([char_zero; char_zero], r1)) in
               (match uu___1 with
                | (mm, r2) ->
                    FStar_Pervasives_Native.Some
                      ((sgn ::
                        (FStar_List_Tot_Base.op_At hh (colon_char :: mm))),
                        r2)))
        else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let pad2 (l : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  if (FStar_List_Tot_Base.length l) >= (Prims.of_int (2))
  then l
  else
    FStar_List_Tot_Base.op_At
      (repeat_char char_zero
         ((Prims.of_int (2)) - (FStar_List_Tot_Base.length l))) l
let is_field_letter (c : FStar_Char.char) : Prims.bool=
  let i = code c in
  ((((((((i = (Prims.of_int (121))) || (i = (Prims.of_int (77)))) ||
          (i = (Prims.of_int (100))))
         || (i = (Prims.of_int (72))))
        || (i = (Prims.of_int (109))))
       || (i = (Prims.of_int (115))))
      || (i = (Prims.of_int (83))))
     || (i = (Prims.of_int (88))))
    || (i = (Prims.of_int (120)))
type dt_token =
  | TkField of FStar_Char.char * Prims.nat 
  | TkLit of FStar_Char.char 
let uu___is_TkField (projectee : dt_token) : Prims.bool=
  match projectee with | TkField (_0, _1) -> true | uu___ -> false
let __proj__TkField__item___0 (projectee : dt_token) : FStar_Char.char=
  match projectee with | TkField (_0, _1) -> _0
let __proj__TkField__item___1 (projectee : dt_token) : Prims.nat=
  match projectee with | TkField (_0, _1) -> _1
let uu___is_TkLit (projectee : dt_token) : Prims.bool=
  match projectee with | TkLit _0 -> true | uu___ -> false
let __proj__TkLit__item___0 (projectee : dt_token) : FStar_Char.char=
  match projectee with | TkLit _0 -> _0
let rec tokenize (pat : FStar_Char.char Prims.list) : dt_token Prims.list=
  match pat with
  | [] -> []
  | c::tl ->
      let rest = tokenize tl in
      if is_field_letter c
      then
        (match rest with
         | (TkField (f, k))::more ->
             if (code f) = (code c)
             then (TkField (f, (k + Prims.int_one))) :: more
             else (TkField (c, Prims.int_one)) :: rest
         | uu___ -> (TkField (c, Prims.int_one)) :: rest)
      else (TkLit c) :: rest
let rec dt_walk (toks : dt_token Prims.list) (v : FStar_Char.char Prims.list)
  (acc : dt_acc) : dt_acc FStar_Pervasives_Native.option=
  match toks with
  | [] ->
      if v = []
      then FStar_Pervasives_Native.Some acc
      else FStar_Pervasives_Native.None
  | (TkLit lc)::more ->
      (match v with
       | vc::vr ->
           if (code vc) = (code lc)
           then dt_walk more vr acc
           else FStar_Pervasives_Native.None
       | uu___ -> FStar_Pervasives_Native.None)
  | (TkField (f, n))::more ->
      let i = code f in
      if i = (Prims.of_int (121))
      then
        (if n <> (Prims.of_int (4))
         then FStar_Pervasives_Native.None
         else
           (match take_exact (Prims.of_int (4)) v with
            | FStar_Pervasives_Native.Some (ds, vr) ->
                dt_walk more vr
                  {
                    d_year = (FStar_Pervasives_Native.Some ds);
                    d_mon = (acc.d_mon);
                    d_day = (acc.d_day);
                    d_hour = (acc.d_hour);
                    d_min = (acc.d_min);
                    d_sec = (acc.d_sec);
                    d_frac = (acc.d_frac);
                    d_tz = (acc.d_tz)
                  }
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
      else
        if (i = (Prims.of_int (88))) || (i = (Prims.of_int (120)))
        then
          (match parse_tz (i = (Prims.of_int (88))) v with
           | FStar_Pervasives_Native.Some (tz, vr) ->
               dt_walk more vr
                 {
                   d_year = (acc.d_year);
                   d_mon = (acc.d_mon);
                   d_day = (acc.d_day);
                   d_hour = (acc.d_hour);
                   d_min = (acc.d_min);
                   d_sec = (acc.d_sec);
                   d_frac = (acc.d_frac);
                   d_tz = (FStar_Pervasives_Native.Some tz)
                 }
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else
          if i = (Prims.of_int (83))
          then
            (match take_exact n v with
             | FStar_Pervasives_Native.Some (ds, vr) ->
                 dt_walk more vr
                   {
                     d_year = (acc.d_year);
                     d_mon = (acc.d_mon);
                     d_day = (acc.d_day);
                     d_hour = (acc.d_hour);
                     d_min = (acc.d_min);
                     d_sec = (acc.d_sec);
                     d_frac = (FStar_Pervasives_Native.Some ds);
                     d_tz = (acc.d_tz)
                   }
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
          else
            (let taken =
               if n >= (Prims.of_int (2))
               then take_exact (Prims.of_int (2)) v
               else take_digits (Prims.of_int (2)) v in
             match taken with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (ds, vr) ->
                 let acc2 =
                   if i = (Prims.of_int (77))
                   then
                     {
                       d_year = (acc.d_year);
                       d_mon = (FStar_Pervasives_Native.Some ds);
                       d_day = (acc.d_day);
                       d_hour = (acc.d_hour);
                       d_min = (acc.d_min);
                       d_sec = (acc.d_sec);
                       d_frac = (acc.d_frac);
                       d_tz = (acc.d_tz)
                     }
                   else
                     if i = (Prims.of_int (100))
                     then
                       {
                         d_year = (acc.d_year);
                         d_mon = (acc.d_mon);
                         d_day = (FStar_Pervasives_Native.Some ds);
                         d_hour = (acc.d_hour);
                         d_min = (acc.d_min);
                         d_sec = (acc.d_sec);
                         d_frac = (acc.d_frac);
                         d_tz = (acc.d_tz)
                       }
                     else
                       if i = (Prims.of_int (72))
                       then
                         {
                           d_year = (acc.d_year);
                           d_mon = (acc.d_mon);
                           d_day = (acc.d_day);
                           d_hour = (FStar_Pervasives_Native.Some ds);
                           d_min = (acc.d_min);
                           d_sec = (acc.d_sec);
                           d_frac = (acc.d_frac);
                           d_tz = (acc.d_tz)
                         }
                       else
                         if i = (Prims.of_int (109))
                         then
                           {
                             d_year = (acc.d_year);
                             d_mon = (acc.d_mon);
                             d_day = (acc.d_day);
                             d_hour = (acc.d_hour);
                             d_min = (FStar_Pervasives_Native.Some ds);
                             d_sec = (acc.d_sec);
                             d_frac = (acc.d_frac);
                             d_tz = (acc.d_tz)
                           }
                         else
                           {
                             d_year = (acc.d_year);
                             d_mon = (acc.d_mon);
                             d_day = (acc.d_day);
                             d_hour = (acc.d_hour);
                             d_min = (acc.d_min);
                             d_sec = (FStar_Pervasives_Native.Some ds);
                             d_frac = (acc.d_frac);
                             d_tz = (acc.d_tz)
                           } in
                 dt_walk more vr acc2)
let build_dt (base_name : Prims.string) (acc : dt_acc) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  let tzc =
    match acc.d_tz with
    | FStar_Pervasives_Native.Some t -> t
    | FStar_Pervasives_Native.None -> [] in
  let fracc =
    match acc.d_frac with
    | FStar_Pervasives_Native.Some f -> dot_char :: f
    | FStar_Pervasives_Native.None -> [] in
  let time_core uu___ =
    match ((acc.d_hour), (acc.d_min)) with
    | (FStar_Pervasives_Native.Some h, FStar_Pervasives_Native.Some m) ->
        let s =
          match acc.d_sec with
          | FStar_Pervasives_Native.Some s1 -> s1
          | FStar_Pervasives_Native.None -> [char_zero; char_zero] in
        FStar_Pervasives_Native.Some
          (FStar_List_Tot_Base.op_At (pad2 h)
             (FStar_List_Tot_Base.op_At (colon_char :: (pad2 m))
                (FStar_List_Tot_Base.op_At (colon_char :: (pad2 s)) fracc)))
    | uu___1 -> FStar_Pervasives_Native.None in
  let date_core uu___ =
    match ((acc.d_year), (acc.d_mon), (acc.d_day)) with
    | (FStar_Pervasives_Native.Some y, FStar_Pervasives_Native.Some mo,
       FStar_Pervasives_Native.Some d) ->
        FStar_Pervasives_Native.Some
          (FStar_List_Tot_Base.op_At y
             (FStar_List_Tot_Base.op_At (minus_char :: (pad2 mo)) (minus_char
                :: (pad2 d))))
    | uu___1 -> FStar_Pervasives_Native.None in
  if base_name = "date"
  then
    match date_core () with
    | FStar_Pervasives_Native.Some d ->
        FStar_Pervasives_Native.Some (FStar_List_Tot_Base.op_At d tzc)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  else
    if base_name = "time"
    then
      (match time_core () with
       | FStar_Pervasives_Native.Some t ->
           FStar_Pervasives_Native.Some (FStar_List_Tot_Base.op_At t tzc)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    else
      (match ((date_core ()), (time_core ())) with
       | (FStar_Pervasives_Native.Some d, FStar_Pervasives_Native.Some t) ->
           FStar_Pervasives_Native.Some
             (FStar_List_Tot_Base.op_At d
                (FStar_List_Tot_Base.op_At
                   ((FStar_Char.char_of_int (Prims.of_int (84))) :: t) tzc))
       | uu___2 -> FStar_Pervasives_Native.None)
let parse_date_time (base_name : Prims.string)
  (fmt : FStar_Char.char Prims.list) (v : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match dt_walk (tokenize fmt) v dt_empty with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some acc -> build_dt base_name acc
let lit_true : FStar_Char.char Prims.list= chars_of "true"
let lit_false : FStar_Char.char Prims.list= chars_of "false"
let parse_bool (fmt : Prims.string FStar_Pervasives_Native.option)
  (v : FStar_Char.char Prims.list) : fmt_outcome=
  match fmt with
  | FStar_Pervasives_Native.None ->
      let s = string_of v in
      if (s = "true") || (s = "1")
      then FO_Valid "true"
      else
        if (s = "false") || (s = "0") then FO_Valid "false" else FO_Invalid
  | FStar_Pervasives_Native.Some f ->
      (match split_first (FStar_Char.char_of_int (Prims.of_int (124)))
               (chars_of f)
       with
       | FStar_Pervasives_Native.None -> FO_Invalid
       | FStar_Pervasives_Native.Some (tv, fv) ->
           if v = tv
           then FO_Valid "true"
           else if v = fv then FO_Valid "false" else FO_Invalid)
let dur_opt_field (designator : FStar_Char.char) (allow_frac : Prims.bool)
  (v : FStar_Char.char Prims.list) :
  (Prims.bool * FStar_Char.char Prims.list)=
  match take_digits_greedy v with
  | FStar_Pervasives_Native.None -> (false, v)
  | FStar_Pervasives_Native.Some (uu___, r1) ->
      let r2 =
        if allow_frac
        then
          match r1 with
          | c::rr ->
              (if (code c) = (code dot_char)
               then
                 match take_digits_greedy rr with
                 | FStar_Pervasives_Native.Some (uu___1, r3) -> r3
                 | FStar_Pervasives_Native.None -> r1
               else r1)
          | uu___1 -> r1
        else r1 in
      (match r2 with
       | c::rest ->
           if (code c) = (code designator) then (true, rest) else (false, v)
       | uu___1 -> (false, v))
let dur_char_Y : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (89))
let dur_char_M : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (77))
let dur_char_D : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (68))
let dur_char_H : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (72))
let dur_char_S : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (83))
let dur_char_T : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (84))
let dur_char_P : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (80))
let dur_time_part (v : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list FStar_Pervasives_Native.option=
  match v with
  | c::rest ->
      if (code c) <> (code dur_char_T)
      then FStar_Pervasives_Native.None
      else
        (let uu___1 = dur_opt_field dur_char_H false rest in
         match uu___1 with
         | (h_ok, r1) ->
             let uu___2 = dur_opt_field dur_char_M false r1 in
             (match uu___2 with
              | (m_ok, r2) ->
                  let uu___3 = dur_opt_field dur_char_S true r2 in
                  (match uu___3 with
                   | (s_ok, r3) ->
                       if (h_ok || m_ok) || s_ok
                       then FStar_Pervasives_Native.Some r3
                       else FStar_Pervasives_Native.None)))
  | uu___ -> FStar_Pervasives_Native.None
let duration_lexical_valid (base_name : Prims.string)
  (v0 : FStar_Char.char Prims.list) : Prims.bool=
  let v1 =
    match v0 with
    | c::rest -> if (code c) = (code minus_char) then rest else v0
    | uu___ -> v0 in
  match v1 with
  | p::rest ->
      if (code p) <> (code dur_char_P)
      then false
      else
        if base_name = "yearMonthDuration"
        then
          (let uu___1 = dur_opt_field dur_char_Y false rest in
           match uu___1 with
           | (y_ok, r1) ->
               let uu___2 = dur_opt_field dur_char_M false r1 in
               (match uu___2 with | (m_ok, r2) -> (y_ok || m_ok) && (r2 = [])))
        else
          if base_name = "dayTimeDuration"
          then
            (let uu___2 = dur_opt_field dur_char_D false rest in
             match uu___2 with
             | (d_ok, r1) ->
                 (match r1 with
                  | [] -> d_ok
                  | uu___3 ->
                      (match dur_time_part r1 with
                       | FStar_Pervasives_Native.Some [] -> true
                       | uu___4 -> false)))
          else
            (let uu___3 = dur_opt_field dur_char_Y false rest in
             match uu___3 with
             | (y_ok, r1) ->
                 let uu___4 = dur_opt_field dur_char_M false r1 in
                 (match uu___4 with
                  | (m_ok, r2) ->
                      let uu___5 = dur_opt_field dur_char_D false r2 in
                      (match uu___5 with
                       | (d_ok, r3) ->
                           (match r3 with
                            | [] -> (y_ok || m_ok) || d_ok
                            | uu___6 ->
                                (match dur_time_part r3 with
                                 | FStar_Pervasives_Native.Some [] -> true
                                 | uu___7 -> false)))))
  | uu___ -> false
let is_duration_base (n : Prims.string) : Prims.bool=
  ((n = "duration") || (n = "dayTimeDuration")) || (n = "yearMonthDuration")
let csvw_format_convert (base_name : Prims.string)
  (format_str : Prims.string FStar_Pervasives_Native.option)
  (pattern : Prims.string FStar_Pervasives_Native.option)
  (group_char : Prims.string FStar_Pervasives_Native.option)
  (decimal_char : Prims.string FStar_Pervasives_Native.option)
  (txt : Prims.string) : fmt_outcome=
  if base_name = "boolean"
  then parse_bool format_str (chars_of txt)
  else
    if is_numeric_base base_name
    then
      (let pat_opt =
         match pattern with
         | FStar_Pervasives_Native.Some p -> FStar_Pervasives_Native.Some p
         | FStar_Pervasives_Native.None -> format_str in
       if
         ((pat_opt = FStar_Pervasives_Native.None) &&
            (group_char = FStar_Pervasives_Native.None))
           && (decimal_char = FStar_Pervasives_Native.None)
       then FO_NoFormat
       else
         (let grp =
            match group_char with
            | FStar_Pervasives_Native.Some g ->
                (match first_char g with
                 | FStar_Pervasives_Native.Some c -> c
                 | FStar_Pervasives_Native.None ->
                     FStar_Char.char_of_int (Prims.of_int (44)))
            | FStar_Pervasives_Native.None ->
                FStar_Char.char_of_int (Prims.of_int (44)) in
          let dec =
            match decimal_char with
            | FStar_Pervasives_Native.Some d ->
                (match first_char d with
                 | FStar_Pervasives_Native.Some c -> c
                 | FStar_Pervasives_Native.None -> dot_char)
            | FStar_Pervasives_Native.None -> dot_char in
          let nf =
            match pat_opt with
            | FStar_Pervasives_Native.Some p ->
                parse_num_fmt (chars_of p) grp dec
            | FStar_Pervasives_Native.None -> default_num_fmt grp dec in
          match parse_number nf base_name (chars_of txt) with
          | FStar_Pervasives_Native.Some lex -> FO_Valid (string_of lex)
          | FStar_Pervasives_Native.None -> FO_Invalid))
    else
      if is_date_base base_name
      then
        (let fmt_opt =
           match format_str with
           | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
           | FStar_Pervasives_Native.None -> pattern in
         match fmt_opt with
         | FStar_Pervasives_Native.None -> FO_NoFormat
         | FStar_Pervasives_Native.Some f ->
             let bn =
               if base_name = "datetime" then "dateTime" else base_name in
             (match parse_date_time bn (chars_of f) (chars_of txt) with
              | FStar_Pervasives_Native.Some lex -> FO_Valid (string_of lex)
              | FStar_Pervasives_Native.None -> FO_Invalid))
      else
        if is_duration_base base_name
        then
          (match format_str with
           | FStar_Pervasives_Native.Some uu___3 -> FO_NoFormat
           | FStar_Pervasives_Native.None ->
               if duration_lexical_valid base_name (chars_of txt)
               then FO_Valid txt
               else FO_Invalid)
        else FO_NoFormat
