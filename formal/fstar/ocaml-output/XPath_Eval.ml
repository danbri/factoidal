open Prims
type xpath_number =
  | XN_NaN 
  | XN_PosInf 
  | XN_NegInf 
  | XN_Finite of Prims.int * Prims.nat 
let uu___is_XN_NaN (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_NaN -> true | uu___ -> false
let uu___is_XN_PosInf (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_PosInf -> true | uu___ -> false
let uu___is_XN_NegInf (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_NegInf -> true | uu___ -> false
let uu___is_XN_Finite (projectee : xpath_number) : Prims.bool=
  match projectee with | XN_Finite (mantissa, scale) -> true | uu___ -> false
let __proj__XN_Finite__item__mantissa (projectee : xpath_number) : Prims.int=
  match projectee with | XN_Finite (mantissa, scale) -> mantissa
let __proj__XN_Finite__item__scale (projectee : xpath_number) : Prims.nat=
  match projectee with | XN_Finite (mantissa, scale) -> scale
let rec xn_pow10 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (xn_pow10 (n - Prims.int_one))
let xn_abs (n : Prims.int) : Prims.int=
  if n >= Prims.int_zero then n else Prims.int_zero - n
let xn_align (v1 : Prims.int) (s1 : Prims.nat) (v2 : Prims.int)
  (s2 : Prims.nat) : (Prims.int * Prims.int * Prims.nat)=
  if s1 >= s2
  then (v1, (v2 * (xn_pow10 (s1 - s2))), s1)
  else ((v1 * (xn_pow10 (s2 - s1))), v2, s2)
let xn_neg (n : xpath_number) : xpath_number=
  match n with
  | XN_NaN -> XN_NaN
  | XN_PosInf -> XN_NegInf
  | XN_NegInf -> XN_PosInf
  | XN_Finite (v, s) -> XN_Finite ((Prims.int_zero - v), s)
let xn_compare (a : xpath_number) (b : xpath_number) :
  Prims.int FStar_Pervasives_Native.option=
  match (a, b) with
  | (XN_NaN, uu___) -> FStar_Pervasives_Native.None
  | (uu___, XN_NaN) -> FStar_Pervasives_Native.None
  | (XN_PosInf, XN_PosInf) -> FStar_Pervasives_Native.Some Prims.int_zero
  | (XN_NegInf, XN_NegInf) -> FStar_Pervasives_Native.Some Prims.int_zero
  | (XN_PosInf, XN_NegInf) -> FStar_Pervasives_Native.Some Prims.int_one
  | (XN_NegInf, XN_PosInf) ->
      FStar_Pervasives_Native.Some (Prims.of_int (-1))
  | (XN_PosInf, XN_Finite (uu___, uu___1)) ->
      FStar_Pervasives_Native.Some Prims.int_one
  | (XN_Finite (uu___, uu___1), XN_PosInf) ->
      FStar_Pervasives_Native.Some (Prims.of_int (-1))
  | (XN_NegInf, XN_Finite (uu___, uu___1)) ->
      FStar_Pervasives_Native.Some (Prims.of_int (-1))
  | (XN_Finite (uu___, uu___1), XN_NegInf) ->
      FStar_Pervasives_Native.Some Prims.int_one
  | (XN_Finite (v1, s1), XN_Finite (v2, s2)) ->
      let uu___ = xn_align v1 s1 v2 s2 in
      (match uu___ with
       | (n1, n2, uu___1) ->
           FStar_Pervasives_Native.Some
             (if n1 < n2
              then (Prims.of_int (-1))
              else if n1 > n2 then Prims.int_one else Prims.int_zero))
let xn_arith (op : Parser_XPath.xp_arith_op) (a : xpath_number)
  (b : xpath_number) : xpath_number=
  match (a, b) with
  | (XN_NaN, uu___) -> XN_NaN
  | (uu___, XN_NaN) -> XN_NaN
  | (XN_PosInf, XN_PosInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_PosInf
       | Parser_XPath.Ar_Sub -> XN_NaN
       | Parser_XPath.Ar_Mul -> XN_PosInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_NegInf, XN_NegInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NegInf
       | Parser_XPath.Ar_Sub -> XN_NaN
       | Parser_XPath.Ar_Mul -> XN_PosInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_PosInf, XN_NegInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NaN
       | Parser_XPath.Ar_Sub -> XN_PosInf
       | Parser_XPath.Ar_Mul -> XN_NegInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_NegInf, XN_PosInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NaN
       | Parser_XPath.Ar_Sub -> XN_NegInf
       | Parser_XPath.Ar_Mul -> XN_NegInf
       | Parser_XPath.Ar_Div -> XN_NaN
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_PosInf, XN_Finite (v, uu___)) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_PosInf
       | Parser_XPath.Ar_Sub -> XN_PosInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_PosInf else XN_NegInf
       | Parser_XPath.Ar_Div ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_PosInf else XN_NegInf
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_NegInf, XN_Finite (v, uu___)) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NegInf
       | Parser_XPath.Ar_Sub -> XN_NegInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_NegInf else XN_PosInf
       | Parser_XPath.Ar_Div ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_NegInf else XN_PosInf
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_Finite (v, uu___), XN_PosInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_PosInf
       | Parser_XPath.Ar_Sub -> XN_NegInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_PosInf else XN_NegInf
       | Parser_XPath.Ar_Div -> XN_Finite (Prims.int_zero, Prims.int_zero)
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_Finite (v, uu___), XN_NegInf) ->
      (match op with
       | Parser_XPath.Ar_Add -> XN_NegInf
       | Parser_XPath.Ar_Sub -> XN_PosInf
       | Parser_XPath.Ar_Mul ->
           if v = Prims.int_zero
           then XN_NaN
           else if v > Prims.int_zero then XN_NegInf else XN_PosInf
       | Parser_XPath.Ar_Div -> XN_Finite (Prims.int_zero, Prims.int_zero)
       | Parser_XPath.Ar_Mod -> XN_NaN)
  | (XN_Finite (v1, s1), XN_Finite (v2, s2)) ->
      (match op with
       | Parser_XPath.Ar_Add ->
           let uu___ = xn_align v1 s1 v2 s2 in
           (match uu___ with | (n1, n2, s) -> XN_Finite ((n1 + n2), s))
       | Parser_XPath.Ar_Sub ->
           let uu___ = xn_align v1 s1 v2 s2 in
           (match uu___ with | (n1, n2, s) -> XN_Finite ((n1 - n2), s))
       | Parser_XPath.Ar_Mul -> XN_Finite ((v1 * v2), (s1 + s2))
       | Parser_XPath.Ar_Div ->
           if v2 = Prims.int_zero
           then
             (if v1 = Prims.int_zero
              then XN_NaN
              else if v1 > Prims.int_zero then XN_PosInf else XN_NegInf)
           else
             (let extra = (Prims.of_int (12)) in
              let scaled = v1 * (xn_pow10 (s2 + extra)) in
              XN_Finite ((scaled / v2), (s1 + extra)))
       | Parser_XPath.Ar_Mod ->
           if v2 = Prims.int_zero
           then XN_NaN
           else
             (let uu___1 = xn_align v1 s1 v2 s2 in
              match uu___1 with
              | (n1, n2, s) ->
                  if n2 = Prims.int_zero
                  then XN_NaN
                  else XN_Finite ((n1 - ((n1 / n2) * n2)), s)))
let rec xn_list_drop_while :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f l ->
    match l with
    | [] -> []
    | x::xs -> if f x then xn_list_drop_while f xs else x :: xs
let string_to_xn (s : Prims.string) : xpath_number=
  let len = FStar_String.strlen s in
  let cs = FStar_String.list_of_string s in
  let is_sp c = (((c = 32) || (c = 9)) || (c = 10)) || (c = 13) in
  let trimmed =
    FStar_List_Tot_Base.rev
      (xn_list_drop_while is_sp
         (FStar_List_Tot_Base.rev (xn_list_drop_while is_sp cs))) in
  match trimmed with
  | [] -> XN_NaN
  | hd::tl ->
      let uu___ = if hd = 45 then (true, tl) else (false, trimmed) in
      (match uu___ with
       | (neg, digits) ->
           let is_ascii_digit c =
             let k = FStar_Char.int_of_char c in
             (k >= (Prims.of_int (0x30))) && (k <= (Prims.of_int (0x39))) in
           if
             Prims.op_Negation
               (FStar_List_Tot_Base.existsb is_ascii_digit digits)
           then XN_NaN
           else
             (let s' = FStar_String.string_of_list digits in
              match Parser_XPath.parse_number_lit s' Prims.int_zero with
              | FStar_Pervasives_Native.Some (v, scale, pos') ->
                  if
                    (pos' = (FStar_String.strlen s')) &&
                      (pos' > Prims.int_zero)
                  then
                    XN_Finite
                      (((if neg then Prims.int_zero - v else v)), scale)
                  else XN_NaN
              | FStar_Pervasives_Native.None -> XN_NaN))
let xn_to_string (n : xpath_number) : Prims.string=
  match n with
  | XN_NaN -> "NaN"
  | XN_PosInf -> "Infinity"
  | XN_NegInf -> "-Infinity"
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then Prims.string_of_int v
      else
        (let neg = v < Prims.int_zero in
         let av = xn_abs v in
         let p = xn_pow10 s in
         let ip = if p = Prims.int_zero then av else av / p in
         let fp =
           if p = Prims.int_zero then Prims.int_zero else av - (ip * p) in
         if fp = Prims.int_zero
         then
           Prims.strcat (if neg && (ip <> Prims.int_zero) then "-" else "")
             (Prims.string_of_int ip)
         else
           (let rec zeros_str k =
              if k = Prims.int_zero
              then ""
              else Prims.strcat "0" (zeros_str (k - Prims.int_one)) in
            let pad n1 target =
              let len = FStar_String.strlen n1 in
              if len >= target
              then n1
              else Prims.strcat (zeros_str (target - len)) n1 in
            let frac_str = pad (Prims.string_of_int fp) s in
            let rev_chars =
              FStar_List_Tot_Base.rev (FStar_String.list_of_string frac_str) in
            let rev_stripped = xn_list_drop_while (fun c -> c = 48) rev_chars in
            let stripped_chars =
              if Prims.uu___is_Nil rev_stripped
              then [48]
              else FStar_List_Tot_Base.rev rev_stripped in
            let stripped = FStar_String.string_of_list stripped_chars in
            Prims.strcat (if neg then "-" else "")
              (Prims.strcat (Prims.string_of_int ip)
                 (Prims.strcat "." stripped))))
let xn_is_zero (n : xpath_number) : Prims.bool=
  match n with
  | XN_Finite (uu___, uu___1) when uu___ = Prims.int_zero -> true
  | uu___ -> false
let xn_to_bool (n : xpath_number) : Prims.bool=
  match n with
  | XN_NaN -> false
  | XN_PosInf -> true
  | XN_NegInf -> true
  | XN_Finite (v, uu___) -> v <> Prims.int_zero
let xn_round (n : xpath_number) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then n
      else
        (let p = xn_pow10 s in
         if p = Prims.int_zero
         then n
         else
           (let half = p / (Prims.of_int (2)) in
            let q =
              if v >= Prims.int_zero
              then (v + half) / p
              else
                Prims.int_zero -
                  (((Prims.int_zero - v) + ((p - half) - Prims.int_one)) / p) in
            XN_Finite (q, Prims.int_zero)))
  | uu___ -> n
let xn_floor (n : xpath_number) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then n
      else
        (let p = xn_pow10 s in
         if p = Prims.int_zero
         then n
         else
           (let q =
              if v >= Prims.int_zero
              then v / p
              else
                Prims.int_zero -
                  ((((Prims.int_zero - v) + p) - Prims.int_one) / p) in
            XN_Finite (q, Prims.int_zero)))
  | uu___ -> n
let xn_ceiling (n : xpath_number) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s = Prims.int_zero
      then n
      else
        (let p = xn_pow10 s in
         if p = Prims.int_zero
         then n
         else
           (let q =
              if v >= Prims.int_zero
              then ((v + p) - Prims.int_one) / p
              else Prims.int_zero - ((Prims.int_zero - v) / p) in
            XN_Finite (q, Prims.int_zero)))
  | uu___ -> n
type decimal_format_symbols =
  {
  dfs_name: Prims.string ;
  dfs_decimal_sep: FStar_Char.char ;
  dfs_grouping_sep: FStar_Char.char ;
  dfs_infinity: Prims.string ;
  dfs_minus_sign: FStar_Char.char ;
  dfs_nan: Prims.string ;
  dfs_percent: FStar_Char.char ;
  dfs_per_mille: FStar_Char.char ;
  dfs_zero_digit: FStar_Char.char ;
  dfs_digit: FStar_Char.char ;
  dfs_pattern_sep: FStar_Char.char }
let __proj__Mkdecimal_format_symbols__item__dfs_name
  (projectee : decimal_format_symbols) : Prims.string=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_name
let __proj__Mkdecimal_format_symbols__item__dfs_decimal_sep
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_decimal_sep
let __proj__Mkdecimal_format_symbols__item__dfs_grouping_sep
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_grouping_sep
let __proj__Mkdecimal_format_symbols__item__dfs_infinity
  (projectee : decimal_format_symbols) : Prims.string=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_infinity
let __proj__Mkdecimal_format_symbols__item__dfs_minus_sign
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_minus_sign
let __proj__Mkdecimal_format_symbols__item__dfs_nan
  (projectee : decimal_format_symbols) : Prims.string=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_nan
let __proj__Mkdecimal_format_symbols__item__dfs_percent
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_percent
let __proj__Mkdecimal_format_symbols__item__dfs_per_mille
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_per_mille
let __proj__Mkdecimal_format_symbols__item__dfs_zero_digit
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_zero_digit
let __proj__Mkdecimal_format_symbols__item__dfs_digit
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_digit
let __proj__Mkdecimal_format_symbols__item__dfs_pattern_sep
  (projectee : decimal_format_symbols) : FStar_Char.char=
  match projectee with
  | { dfs_name; dfs_decimal_sep; dfs_grouping_sep; dfs_infinity;
      dfs_minus_sign; dfs_nan; dfs_percent; dfs_per_mille; dfs_zero_digit;
      dfs_digit; dfs_pattern_sep;_} -> dfs_pattern_sep
let default_decimal_format_symbols : decimal_format_symbols=
  {
    dfs_name = "";
    dfs_decimal_sep = 46;
    dfs_grouping_sep = 44;
    dfs_infinity = "Infinity";
    dfs_minus_sign = 45;
    dfs_nan = "NaN";
    dfs_percent = 37;
    dfs_per_mille = (FStar_Char.char_of_int (Prims.of_int (0x2030)));
    dfs_zero_digit = 48;
    dfs_digit = 35;
    dfs_pattern_sep = 59
  }
let lookup_decimal_format (formats : decimal_format_symbols Prims.list)
  (name : Prims.string) : decimal_format_symbols=
  match FStar_List_Tot_Base.find (fun f -> f.dfs_name = name)
          (FStar_List_Tot_Base.rev formats)
  with
  | FStar_Pervasives_Native.Some f -> f
  | FStar_Pervasives_Native.None -> default_decimal_format_symbols
let char_to_str (c : FStar_Char.char) : Prims.string=
  FStar_String.string_of_list [c]
let nat_abs (v : Prims.int) : Prims.nat=
  if v >= Prims.int_zero then v else Prims.int_zero - v
let rec pow10_nat (n : Prims.nat) : Prims.nat=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10_nat (n - Prims.int_one))
let round_half_even_nat (num : Prims.nat) (den : Prims.nat) : Prims.nat=
  let q = num / den in
  let r = (mod) num den in
  let twice_r = (Prims.of_int (2)) * r in
  if twice_r < den
  then q
  else
    if twice_r > den
    then q + Prims.int_one
    else
      if ((mod) q (Prims.of_int (2))) = Prims.int_zero
      then q
      else q + Prims.int_one
let round_to_scale (v : Prims.int) (s : Prims.nat) (target : Prims.nat) :
  Prims.nat=
  let av = nat_abs v in
  if target >= s
  then av * (pow10_nat (target - s))
  else round_half_even_nat av (pow10_nat (s - target))
let xn_mul_pow10 (n : xpath_number) (k : Prims.nat) : xpath_number=
  match n with
  | XN_Finite (v, s) ->
      if s >= k
      then XN_Finite (v, (s - k))
      else XN_Finite ((v * (pow10_nat (k - s))), Prims.int_zero)
  | other -> other
let rec digits_rev_of_nat (n : Prims.nat) : Prims.nat Prims.list=
  if n = Prims.int_zero
  then []
  else ((mod) n (Prims.of_int (10))) ::
    (digits_rev_of_nat (n / (Prims.of_int (10))))
let int_digits_of_nat (n : Prims.nat) : Prims.nat Prims.list=
  FStar_List_Tot_Base.rev (digits_rev_of_nat n)
let rec zeros_nat (k : Prims.nat) : Prims.nat Prims.list=
  if k = Prims.int_zero
  then []
  else Prims.int_zero :: (zeros_nat (k - Prims.int_one))
let pad_left_zeros (l : Prims.nat Prims.list) (target : Prims.nat) :
  Prims.nat Prims.list=
  let len = FStar_List_Tot_Base.length l in
  if len >= target
  then l
  else FStar_List_Tot_Base.op_At (zeros_nat (target - len)) l
let rec frac_digits_fixed (n : Prims.nat) (width : Prims.nat) :
  Prims.nat Prims.list=
  if width = Prims.int_zero
  then []
  else
    (let p = pow10_nat (width - Prims.int_one) in
     ((mod) (n / p) (Prims.of_int (10))) ::
       (frac_digits_fixed ((mod) n p) (width - Prims.int_one)))
let rec trim_lsb_zeros (l : Prims.nat Prims.list) (min_len : Prims.nat)
  (cur_len : Prims.nat) : Prims.nat Prims.list=
  match l with
  | [] -> []
  | d::rest ->
      if (d = Prims.int_zero) && (cur_len > min_len)
      then trim_lsb_zeros rest min_len (cur_len - Prims.int_one)
      else l
let rec take_while_char (f : FStar_Char.char -> Prims.bool)
  (l : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match l with
  | [] -> []
  | c::rest -> if f c then c :: (take_while_char f rest) else []
let rec drop_while_char (f : FStar_Char.char -> Prims.bool)
  (l : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match l with
  | [] -> []
  | c::rest -> if f c then drop_while_char f rest else l
let rec split_at_char (cs : FStar_Char.char Prims.list)
  (sep : FStar_Char.char) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ([], FStar_Pervasives_Native.None)
  | c::rest ->
      if c = sep
      then ([], (FStar_Pervasives_Native.Some rest))
      else
        (let uu___1 = split_at_char rest sep in
         match uu___1 with | (before, after) -> ((c :: before), after))
let rec count_char (l : FStar_Char.char Prims.list) (c : FStar_Char.char) :
  Prims.nat=
  match l with
  | [] -> Prims.int_zero
  | x::rest ->
      (if x = c then Prims.int_one else Prims.int_zero) + (count_char rest c)
let rec group_size_rev (rev_int_chars : FStar_Char.char Prims.list)
  (dfs : decimal_format_symbols) (acc : Prims.nat) : Prims.nat=
  match rev_int_chars with
  | [] -> Prims.int_zero
  | c::rest ->
      if c = dfs.dfs_grouping_sep
      then acc
      else group_size_rev rest dfs (acc + Prims.int_one)
type subpicture =
  {
  sp_prefix: FStar_Char.char Prims.list ;
  sp_suffix: FStar_Char.char Prims.list ;
  sp_int_min: Prims.nat ;
  sp_group: Prims.nat ;
  sp_frac_min: Prims.nat ;
  sp_frac_max: Prims.nat ;
  sp_has_percent: Prims.bool ;
  sp_has_permille: Prims.bool }
let __proj__Mksubpicture__item__sp_prefix (projectee : subpicture) :
  FStar_Char.char Prims.list=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_prefix
let __proj__Mksubpicture__item__sp_suffix (projectee : subpicture) :
  FStar_Char.char Prims.list=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_suffix
let __proj__Mksubpicture__item__sp_int_min (projectee : subpicture) :
  Prims.nat=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_int_min
let __proj__Mksubpicture__item__sp_group (projectee : subpicture) :
  Prims.nat=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_group
let __proj__Mksubpicture__item__sp_frac_min (projectee : subpicture) :
  Prims.nat=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_frac_min
let __proj__Mksubpicture__item__sp_frac_max (projectee : subpicture) :
  Prims.nat=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_frac_max
let __proj__Mksubpicture__item__sp_has_percent (projectee : subpicture) :
  Prims.bool=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_has_percent
let __proj__Mksubpicture__item__sp_has_permille (projectee : subpicture) :
  Prims.bool=
  match projectee with
  | { sp_prefix; sp_suffix; sp_int_min; sp_group; sp_frac_min; sp_frac_max;
      sp_has_percent; sp_has_permille;_} -> sp_has_permille
let is_numeric_pic_char (dfs : decimal_format_symbols) (c : FStar_Char.char)
  : Prims.bool=
  (((c = dfs.dfs_digit) || (c = dfs.dfs_zero_digit)) ||
     (c = dfs.dfs_grouping_sep))
    || (c = dfs.dfs_decimal_sep)
let parse_subpicture (cs : FStar_Char.char Prims.list)
  (dfs : decimal_format_symbols) : subpicture=
  let is_num = is_numeric_pic_char dfs in
  let prefix = take_while_char (fun c -> Prims.op_Negation (is_num c)) cs in
  let rest1 = drop_while_char (fun c -> Prims.op_Negation (is_num c)) cs in
  let rev_rest1 = FStar_List_Tot_Base.rev rest1 in
  let rev_suffix =
    take_while_char (fun c -> Prims.op_Negation (is_num c)) rev_rest1 in
  let suffix = FStar_List_Tot_Base.rev rev_suffix in
  let body =
    FStar_List_Tot_Base.rev
      (drop_while_char (fun c -> Prims.op_Negation (is_num c)) rev_rest1) in
  let uu___ = split_at_char body dfs.dfs_decimal_sep in
  match uu___ with
  | (int_chars, frac_opt) ->
      let frac_chars =
        match frac_opt with
        | FStar_Pervasives_Native.Some f -> f
        | FStar_Pervasives_Native.None -> [] in
      let int_min = count_char int_chars dfs.dfs_zero_digit in
      let group =
        group_size_rev (FStar_List_Tot_Base.rev int_chars) dfs Prims.int_zero in
      let frac_min = count_char frac_chars dfs.dfs_zero_digit in
      let frac_max = frac_min + (count_char frac_chars dfs.dfs_digit) in
      let has_pct =
        FStar_List_Tot_Base.existsb (fun c -> c = dfs.dfs_percent)
          (FStar_List_Tot_Base.op_At prefix suffix) in
      let has_pm =
        FStar_List_Tot_Base.existsb (fun c -> c = dfs.dfs_per_mille)
          (FStar_List_Tot_Base.op_At prefix suffix) in
      {
        sp_prefix = prefix;
        sp_suffix = suffix;
        sp_int_min = int_min;
        sp_group = group;
        sp_frac_min = frac_min;
        sp_frac_max = frac_max;
        sp_has_percent = has_pct;
        sp_has_permille = has_pm
      }
let parse_picture (picture : Prims.string) (dfs : decimal_format_symbols) :
  (subpicture * subpicture FStar_Pervasives_Native.option)=
  let cs = FStar_String.list_of_string picture in
  let uu___ = split_at_char cs dfs.dfs_pattern_sep in
  match uu___ with
  | (pos_chars, neg_opt) ->
      let pos_sp = parse_subpicture pos_chars dfs in
      (pos_sp,
        ((match neg_opt with
          | FStar_Pervasives_Native.Some nc ->
              FStar_Pervasives_Native.Some (parse_subpicture nc dfs)
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)))
let digit_char_of (dfs : decimal_format_symbols) (d : Prims.nat) :
  FStar_Char.char=
  let z = FStar_Char.int_of_char dfs.dfs_zero_digit in
  let code = z + ((mod) d (Prims.of_int (10))) in
  if code < (Prims.of_int (0xd7ff))
  then FStar_Char.char_of_int code
  else
    if
      (code >= (Prims.of_int (0xe000))) &&
        (code <= (Prims.parse_int "0x10ffff"))
    then FStar_Char.char_of_int code
    else dfs.dfs_zero_digit
let rec render_digits (dfs : decimal_format_symbols)
  (ds : Prims.nat Prims.list) : FStar_Char.char Prims.list=
  match ds with
  | [] -> []
  | d::rest -> (digit_char_of dfs d) :: (render_digits dfs rest)
let rec add_groups_from_right (rev_chars : FStar_Char.char Prims.list)
  (group : Prims.nat) (idx : Prims.nat) (sep : FStar_Char.char) :
  FStar_Char.char Prims.list=
  match rev_chars with
  | [] -> []
  | c::rest ->
      let idx' = idx + Prims.int_one in
      if
        ((group > Prims.int_zero) && (((mod) idx' group) = Prims.int_zero))
          && (Prims.uu___is_Cons rest)
      then c :: sep :: (add_groups_from_right rest group idx' sep)
      else c :: (add_groups_from_right rest group idx' sep)
let render_int_part (dfs : decimal_format_symbols) (n : Prims.nat)
  (min_digits : Prims.nat) (group : Prims.nat) : FStar_Char.char Prims.list=
  let digs = pad_left_zeros (int_digits_of_nat n) min_digits in
  let chars = render_digits dfs digs in
  if group = Prims.int_zero
  then chars
  else
    FStar_List_Tot_Base.rev
      (add_groups_from_right (FStar_List_Tot_Base.rev chars) group
         Prims.int_zero dfs.dfs_grouping_sep)
let render_frac_part (dfs : decimal_format_symbols) (frac_val : Prims.nat)
  (frac_max : Prims.nat) (frac_min : Prims.nat) : FStar_Char.char Prims.list=
  if frac_max = Prims.int_zero
  then []
  else
    (let digs = frac_digits_fixed frac_val frac_max in
     let trimmed =
       FStar_List_Tot_Base.rev
         (trim_lsb_zeros (FStar_List_Tot_Base.rev digs) frac_min frac_max) in
     render_digits dfs trimmed)
let format_number_str (n : xpath_number) (picture : Prims.string)
  (dfs : decimal_format_symbols) : Prims.string=
  match n with
  | XN_NaN -> dfs.dfs_nan
  | XN_PosInf -> dfs.dfs_infinity
  | XN_NegInf ->
      Prims.strcat (char_to_str dfs.dfs_minus_sign) dfs.dfs_infinity
  | XN_Finite (mantissa, scale) ->
      let uu___ = parse_picture picture dfs in
      (match uu___ with
       | (pos_sp, neg_sp_opt) ->
           let is_neg = mantissa < Prims.int_zero in
           let scale_factor =
             if pos_sp.sp_has_percent
             then (Prims.of_int (2))
             else
               if pos_sp.sp_has_permille
               then (Prims.of_int (3))
               else Prims.int_zero in
           (match xn_mul_pow10 (XN_Finite (mantissa, scale)) scale_factor
            with
            | XN_Finite (v2, s2) ->
                let m = round_to_scale v2 s2 pos_sp.sp_frac_max in
                let p = pow10_nat pos_sp.sp_frac_max in
                let int_part = m / p in
                let frac_part = (mod) m p in
                let int_chars =
                  render_int_part dfs int_part pos_sp.sp_int_min
                    pos_sp.sp_group in
                let frac_chars =
                  render_frac_part dfs frac_part pos_sp.sp_frac_max
                    pos_sp.sp_frac_min in
                let show_frac =
                  (pos_sp.sp_frac_max > Prims.int_zero) &&
                    (Prims.uu___is_Cons frac_chars) in
                let uu___1 =
                  if Prims.op_Negation is_neg
                  then ((pos_sp.sp_prefix), (pos_sp.sp_suffix))
                  else
                    (match neg_sp_opt with
                     | FStar_Pervasives_Native.None ->
                         (((dfs.dfs_minus_sign) :: (pos_sp.sp_prefix)),
                           (pos_sp.sp_suffix))
                     | FStar_Pervasives_Native.Some neg_sp ->
                         if
                           (Prims.uu___is_Nil neg_sp.sp_prefix) &&
                             (Prims.uu___is_Nil neg_sp.sp_suffix)
                         then
                           (((dfs.dfs_minus_sign) :: (pos_sp.sp_prefix)),
                             (pos_sp.sp_suffix))
                         else ((neg_sp.sp_prefix), (neg_sp.sp_suffix))) in
                (match uu___1 with
                 | (final_prefix, final_suffix) ->
                     let body =
                       FStar_List_Tot_Base.op_At int_chars
                         (if show_frac
                          then (dfs.dfs_decimal_sep) :: frac_chars
                          else []) in
                     FStar_String.string_of_list
                       (FStar_List_Tot_Base.op_At final_prefix
                          (FStar_List_Tot_Base.op_At body final_suffix)))
            | uu___1 -> dfs.dfs_nan))
type xctx_item =
  | CI_Elem of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node 
  | CI_Attr of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Parser_XML.xml_attribute 
  | CI_Text of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string 
  | CI_Comment of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string 
  | CI_PI of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string * Prims.string 
  | CI_Namespace of Prims.int Prims.list * Parser_XML.xml_node Prims.list *
  Parser_XML.xml_node * Prims.string * Prims.string 
let uu___is_CI_Elem (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Elem (path, ancestors, node) -> true
  | uu___ -> false
let __proj__CI_Elem__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Elem (path, ancestors, node) -> path
let __proj__CI_Elem__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with | CI_Elem (path, ancestors, node) -> ancestors
let __proj__CI_Elem__item__node (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Elem (path, ancestors, node) -> node
let uu___is_CI_Attr (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Attr (path, ancestors, owner, attr) -> true
  | uu___ -> false
let __proj__CI_Attr__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> path
let __proj__CI_Attr__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> ancestors
let __proj__CI_Attr__item__owner (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> owner
let __proj__CI_Attr__item__attr (projectee : xctx_item) :
  Parser_XML.xml_attribute=
  match projectee with | CI_Attr (path, ancestors, owner, attr) -> attr
let uu___is_CI_Text (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Text (path, ancestors, parent, text) -> true
  | uu___ -> false
let __proj__CI_Text__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Text (path, ancestors, parent, text) -> path
let __proj__CI_Text__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with | CI_Text (path, ancestors, parent, text) -> ancestors
let __proj__CI_Text__item__parent (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Text (path, ancestors, parent, text) -> parent
let __proj__CI_Text__item__text (projectee : xctx_item) : Prims.string=
  match projectee with | CI_Text (path, ancestors, parent, text) -> text
let uu___is_CI_Comment (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Comment (path, ancestors, parent, text) -> true
  | uu___ -> false
let __proj__CI_Comment__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with | CI_Comment (path, ancestors, parent, text) -> path
let __proj__CI_Comment__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | CI_Comment (path, ancestors, parent, text) -> ancestors
let __proj__CI_Comment__item__parent (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with | CI_Comment (path, ancestors, parent, text) -> parent
let __proj__CI_Comment__item__text (projectee : xctx_item) : Prims.string=
  match projectee with | CI_Comment (path, ancestors, parent, text) -> text
let uu___is_CI_PI (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> true
  | uu___ -> false
let __proj__CI_PI__item__path (projectee : xctx_item) : Prims.int Prims.list=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> path
let __proj__CI_PI__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> ancestors
let __proj__CI_PI__item__parent (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> parent
let __proj__CI_PI__item__target (projectee : xctx_item) : Prims.string=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> target
let __proj__CI_PI__item__data (projectee : xctx_item) : Prims.string=
  match projectee with
  | CI_PI (path, ancestors, parent, target, data) -> data
let uu___is_CI_Namespace (projectee : xctx_item) : Prims.bool=
  match projectee with
  | CI_Namespace (path, ancestors, element, prefix, uri) -> true
  | uu___ -> false
let __proj__CI_Namespace__item__path (projectee : xctx_item) :
  Prims.int Prims.list=
  match projectee with
  | CI_Namespace (path, ancestors, element, prefix, uri) -> path
let __proj__CI_Namespace__item__ancestors (projectee : xctx_item) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | CI_Namespace (path, ancestors, element, prefix, uri) -> ancestors
let __proj__CI_Namespace__item__element (projectee : xctx_item) :
  Parser_XML.xml_node=
  match projectee with
  | CI_Namespace (path, ancestors, element, prefix, uri) -> element
let __proj__CI_Namespace__item__prefix (projectee : xctx_item) :
  Prims.string=
  match projectee with
  | CI_Namespace (path, ancestors, element, prefix, uri) -> prefix
let __proj__CI_Namespace__item__uri (projectee : xctx_item) : Prims.string=
  match projectee with
  | CI_Namespace (path, ancestors, element, prefix, uri) -> uri
let item_path (it : xctx_item) : Prims.int Prims.list=
  match it with
  | CI_Elem (p, uu___, uu___1) -> p
  | CI_Attr (p, uu___, uu___1, uu___2) -> p
  | CI_Text (p, uu___, uu___1, uu___2) -> p
  | CI_Comment (p, uu___, uu___1, uu___2) -> p
  | CI_PI (p, uu___, uu___1, uu___2, uu___3) -> p
  | CI_Namespace (p, uu___, uu___1, uu___2, uu___3) -> p
let rec path_drop_last (l : Prims.int Prims.list) : Prims.int Prims.list=
  match l with
  | [] -> []
  | uu___::[] -> []
  | x::tl -> x :: (path_drop_last tl)
let attr_owner_path (p : Prims.int Prims.list) : Prims.int Prims.list=
  path_drop_last (path_drop_last p)
let rec path_compare (a : Prims.int Prims.list) (b : Prims.int Prims.list) :
  Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      if x < y
      then (Prims.of_int (-1))
      else if x > y then Prims.int_one else path_compare xs ys
let rec path_is_prefix (a : Prims.int Prims.list) (b : Prims.int Prims.list)
  : Prims.bool=
  match (a, b) with
  | ([], uu___) -> true
  | (uu___, []) -> false
  | (x::xs, y::ys) -> (x = y) && (path_is_prefix xs ys)
let rec children_with_paths (parent_path : Prims.int Prims.list)
  (new_anc : Parser_XML.xml_node Prims.list) (parent : Parser_XML.xml_node)
  (nodes : Parser_XML.xml_node Prims.list) (i : Prims.nat) :
  xctx_item Prims.list=
  match nodes with
  | [] -> []
  | c::rest ->
      let cpath = FStar_List_Tot_Base.op_At parent_path [i] in
      let item =
        match c with
        | Parser_XML.XElement (uu___, uu___1, uu___2) ->
            CI_Elem (cpath, new_anc, c)
        | Parser_XML.XText t -> CI_Text (cpath, new_anc, parent, t)
        | Parser_XML.XCDATA t -> CI_Text (cpath, new_anc, parent, t)
        | Parser_XML.XComment t -> CI_Comment (cpath, new_anc, parent, t)
        | Parser_XML.XPI (tg, d) -> CI_PI (cpath, new_anc, parent, tg, d) in
      item ::
        (children_with_paths parent_path new_anc parent rest
           (i + Prims.int_one))
let child_items (path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (node : Parser_XML.xml_node) :
  xctx_item Prims.list=
  children_with_paths path (node :: ancestors) node
    (Parser_XML.element_children node) Prims.int_zero
let rec attrs_with_paths (owner_path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (owner : Parser_XML.xml_node)
  (attrs : Parser_XML.xml_attribute Prims.list) (j : Prims.nat) :
  xctx_item Prims.list=
  match attrs with
  | [] -> []
  | a::rest ->
      (CI_Attr
         ((FStar_List_Tot_Base.op_At owner_path [(Prims.of_int (-1)); j]),
           ancestors, owner, a))
      ::
      (attrs_with_paths owner_path ancestors owner rest (j + Prims.int_one))
let attribute_items (path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (node : Parser_XML.xml_node) :
  xctx_item Prims.list=
  attrs_with_paths path ancestors node (Parser_XML.element_attrs node)
    Prims.int_zero
let rec descendant_items (path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) (node : Parser_XML.xml_node) :
  xctx_item Prims.list=
  match node with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      descendant_items_children path (node :: ancestors) node children
        Prims.int_zero
  | uu___ -> []
and descendant_items_children (parent_path : Prims.int Prims.list)
  (new_anc : Parser_XML.xml_node Prims.list) (parent : Parser_XML.xml_node)
  (nodes : Parser_XML.xml_node Prims.list) (i : Prims.nat) :
  xctx_item Prims.list=
  match nodes with
  | [] -> []
  | hd::tl ->
      let cpath = FStar_List_Tot_Base.op_At parent_path [i] in
      let self_item =
        match hd with
        | Parser_XML.XElement (uu___, uu___1, uu___2) ->
            [CI_Elem (cpath, new_anc, hd)]
        | Parser_XML.XText t -> [CI_Text (cpath, new_anc, parent, t)]
        | Parser_XML.XCDATA t -> [CI_Text (cpath, new_anc, parent, t)]
        | Parser_XML.XComment t -> [CI_Comment (cpath, new_anc, parent, t)]
        | Parser_XML.XPI (tg, d) -> [CI_PI (cpath, new_anc, parent, tg, d)] in
      FStar_List_Tot_Base.op_At self_item
        (FStar_List_Tot_Base.op_At (descendant_items cpath new_anc hd)
           (descendant_items_children parent_path new_anc parent tl
              (i + Prims.int_one)))
let rec ancestor_items (self_path : Prims.int Prims.list)
  (ancestors : Parser_XML.xml_node Prims.list) : xctx_item Prims.list=
  match ancestors with
  | [] -> []
  | p::rest ->
      let ppath = path_drop_last self_path in (CI_Elem (ppath, rest, p)) ::
        (ancestor_items ppath rest)
let item_ancestors (it : xctx_item) : Parser_XML.xml_node Prims.list=
  match it with
  | CI_Elem (uu___, anc, uu___1) -> anc
  | CI_Attr (uu___, anc, uu___1, uu___2) -> anc
  | CI_Text (uu___, anc, uu___1, uu___2) -> anc
  | CI_Comment (uu___, anc, uu___1, uu___2) -> anc
  | CI_PI (uu___, anc, uu___1, uu___2, uu___3) -> anc
  | CI_Namespace (uu___, anc, uu___1, uu___2, uu___3) -> anc
let parent_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Attr (p, anc, owner, uu___) ->
      [CI_Elem ((attr_owner_path p), anc, owner)]
  | CI_Namespace (p, anc, elem, uu___, uu___1) ->
      [CI_Elem ((attr_owner_path p), anc, elem)]
  | CI_Elem (p, anc, uu___) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
  | CI_Text (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
  | CI_Comment (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
  | CI_PI (p, anc, uu___, uu___1, uu___2) ->
      (match anc with
       | [] -> []
       | q::rest -> [CI_Elem ((path_drop_last p), rest, q)])
let ancestor_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Attr (p, anc, owner, uu___) ->
      let opath = attr_owner_path p in (CI_Elem (opath, anc, owner)) ::
        (ancestor_items opath anc)
  | CI_Namespace (p, anc, elem, uu___, uu___1) ->
      let opath = attr_owner_path p in (CI_Elem (opath, anc, elem)) ::
        (ancestor_items opath anc)
  | CI_Elem (p, anc, uu___) -> ancestor_items p anc
  | CI_Text (p, anc, uu___, uu___1) -> ancestor_items p anc
  | CI_Comment (p, anc, uu___, uu___1) -> ancestor_items p anc
  | CI_PI (p, anc, uu___, uu___1, uu___2) -> ancestor_items p anc
let child_axis (it : xctx_item) : xctx_item Prims.list=
  match it with | CI_Elem (p, anc, n) -> child_items p anc n | uu___ -> []
let descendant_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, n) -> descendant_items p anc n
  | uu___ -> []
let attribute_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, n) -> attribute_items p anc n
  | uu___ -> []
let siblings_of (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, uu___) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_Text (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_Comment (p, anc, uu___, uu___1) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_PI (p, anc, uu___, uu___1, uu___2) ->
      (match anc with
       | [] -> []
       | parent::grand -> child_items (path_drop_last p) grand parent)
  | CI_Attr (uu___, uu___1, uu___2, uu___3) -> []
  | CI_Namespace (uu___, uu___1, uu___2, uu___3, uu___4) -> []
let following_sibling_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.filter
    (fun s -> (path_compare (item_path s) p) > Prims.int_zero)
    (siblings_of it)
let preceding_sibling_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.rev
    (FStar_List_Tot_Base.filter
       (fun s -> (path_compare (item_path s) p) < Prims.int_zero)
       (siblings_of it))
let string_starts_with (s : Prims.string) (prefix : Prims.string) :
  Prims.bool=
  let lp = FStar_String.strlen prefix in
  ((FStar_String.strlen s) >= lp) &&
    ((FStar_String.sub s Prims.int_zero lp) = prefix)
let rec find_char_from (s : Prims.string) (c : FStar_Char.char)
  (pos : Prims.nat) (len : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if pos >= len
  then FStar_Pervasives_Native.None
  else
    if (FStar_String.index s pos) = c
    then FStar_Pervasives_Native.Some pos
    else find_char_from s c (pos + Prims.int_one) len
let local_name_of (qn : Prims.string) : Prims.string=
  match find_char_from qn 58 Prims.int_zero (FStar_String.strlen qn) with
  | FStar_Pervasives_Native.Some i ->
      FStar_String.sub qn (i + Prims.int_one)
        (((FStar_String.strlen qn) - i) - Prims.int_one)
  | FStar_Pervasives_Native.None -> qn
let xpath_xml_ns_uri : Prims.string= "http://www.w3.org/XML/1998/namespace"
let prefix_of (qn : Prims.string) : Prims.string=
  match find_char_from qn 58 Prims.int_zero (FStar_String.strlen qn) with
  | FStar_Pervasives_Native.Some i -> FStar_String.sub qn Prims.int_zero i
  | FStar_Pervasives_Native.None -> ""
let ns_decl_for (pfx : Prims.string) (a : Parser_XML.xml_attribute) :
  Prims.string FStar_Pervasives_Native.option=
  if pfx = ""
  then
    (if a.Parser_XML.attr_name = "xmlns"
     then FStar_Pervasives_Native.Some (a.Parser_XML.attr_value)
     else FStar_Pervasives_Native.None)
  else
    if a.Parser_XML.attr_name = (FStar_String.concat "" ["xmlns:"; pfx])
    then FStar_Pervasives_Native.Some (a.Parser_XML.attr_value)
    else FStar_Pervasives_Native.None
let rec find_ns_in_attrs (pfx : Prims.string)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match attrs with
  | [] -> FStar_Pervasives_Native.None
  | a::rest ->
      (match ns_decl_for pfx a with
       | FStar_Pervasives_Native.Some u -> FStar_Pervasives_Native.Some u
       | FStar_Pervasives_Native.None -> find_ns_in_attrs pfx rest)
let rec resolve_ns_anc (pfx : Prims.string)
  (anc : Parser_XML.xml_node Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match anc with
  | [] ->
      if pfx = "xml"
      then FStar_Pervasives_Native.Some xpath_xml_ns_uri
      else FStar_Pervasives_Native.None
  | e::rest ->
      (match find_ns_in_attrs pfx (Parser_XML.element_attrs e) with
       | FStar_Pervasives_Native.Some u ->
           if u = ""
           then FStar_Pervasives_Native.None
           else FStar_Pervasives_Native.Some u
       | FStar_Pervasives_Native.None -> resolve_ns_anc pfx rest)
let resolve_ns_uri (pfx : Prims.string)
  (own_attrs : Parser_XML.xml_attribute Prims.list)
  (anc : Parser_XML.xml_node Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match find_ns_in_attrs pfx own_attrs with
  | FStar_Pervasives_Native.Some u ->
      if u = ""
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some u
  | FStar_Pervasives_Native.None -> resolve_ns_anc pfx anc
let elem_ns_uri (tag : Prims.string)
  (own_attrs : Parser_XML.xml_attribute Prims.list)
  (anc : Parser_XML.xml_node Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  resolve_ns_uri (prefix_of tag) own_attrs anc
let rec xml_lang_anc (anc : Parser_XML.xml_node Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  match anc with
  | [] -> FStar_Pervasives_Native.None
  | e::rest ->
      (match Parser_XML.find_attr "xml:lang" (Parser_XML.element_attrs e)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc rest)
let item_xml_lang (it : xctx_item) :
  Prims.string FStar_Pervasives_Native.option=
  match it with
  | CI_Elem (uu___, anc, n) ->
      (match Parser_XML.find_attr "xml:lang" (Parser_XML.element_attrs n)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc anc)
  | CI_Attr (uu___, anc, owner, uu___1) ->
      (match Parser_XML.find_attr "xml:lang" (Parser_XML.element_attrs owner)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc anc)
  | CI_Text (uu___, anc, parent, uu___1) ->
      (match Parser_XML.find_attr "xml:lang"
               (Parser_XML.element_attrs parent)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc anc)
  | CI_Comment (uu___, anc, parent, uu___1) ->
      (match Parser_XML.find_attr "xml:lang"
               (Parser_XML.element_attrs parent)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc anc)
  | CI_PI (uu___, anc, parent, uu___1, uu___2) ->
      (match Parser_XML.find_attr "xml:lang"
               (Parser_XML.element_attrs parent)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc anc)
  | CI_Namespace (uu___, anc, elem, uu___1, uu___2) ->
      (match Parser_XML.find_attr "xml:lang" (Parser_XML.element_attrs elem)
       with
       | FStar_Pervasives_Native.Some v -> FStar_Pervasives_Native.Some v
       | FStar_Pervasives_Native.None -> xml_lang_anc anc)
let lang_matches (node_lang : Prims.string) (arg : Prims.string) :
  Prims.bool=
  let nl = FStar_String.lowercase node_lang in
  let al = FStar_String.lowercase arg in
  (nl = al) || (string_starts_with nl (Prims.strcat al "-"))
let ns_decl_of_attr (a : Parser_XML.xml_attribute) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  let n = FStar_String.strlen a.Parser_XML.attr_name in
  if a.Parser_XML.attr_name = "xmlns"
  then FStar_Pervasives_Native.Some ("", (a.Parser_XML.attr_value))
  else
    if
      (n >= (Prims.of_int (6))) &&
        (string_starts_with a.Parser_XML.attr_name "xmlns:")
    then
      FStar_Pervasives_Native.Some
        ((FStar_String.sub a.Parser_XML.attr_name (Prims.of_int (6))
            (n - (Prims.of_int (6)))), (a.Parser_XML.attr_value))
    else FStar_Pervasives_Native.None
let rec mem_str_e (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with | [] -> false | h::t -> if h = x then true else mem_str_e x t
let rec add_elem_ns (seen : Prims.string Prims.list)
  (acc : (Prims.string * Prims.string) Prims.list)
  (attrs : Parser_XML.xml_attribute Prims.list) :
  (Prims.string Prims.list * (Prims.string * Prims.string) Prims.list)=
  match attrs with
  | [] -> (seen, acc)
  | a::rest ->
      (match ns_decl_of_attr a with
       | FStar_Pervasives_Native.Some (pfx, uri) ->
           if mem_str_e pfx seen
           then add_elem_ns seen acc rest
           else
             if uri = ""
             then add_elem_ns (pfx :: seen) acc rest
             else
               add_elem_ns (pfx :: seen)
                 (FStar_List_Tot_Base.op_At acc [(pfx, uri)]) rest
       | FStar_Pervasives_Native.None -> add_elem_ns seen acc rest)
let rec collect_ns (seen : Prims.string Prims.list)
  (acc : (Prims.string * Prims.string) Prims.list)
  (nodes : Parser_XML.xml_node Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match nodes with
  | [] -> acc
  | n::rest ->
      let uu___ = add_elem_ns seen acc (Parser_XML.element_attrs n) in
      (match uu___ with | (seen', acc') -> collect_ns seen' acc' rest)
let rec cp_list_cmp (a : FStar_Char.char Prims.list)
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
      else if cx > cy then Prims.int_one else cp_list_cmp xs ys
let prefix_cmp (a : Prims.string) (b : Prims.string) : Prims.int=
  cp_list_cmp (FStar_String.list_of_string a) (FStar_String.list_of_string b)
let ns_binding_leq (a : (Prims.string * Prims.string))
  (b : (Prims.string * Prims.string)) : Prims.bool=
  let pa = FStar_Pervasives_Native.fst a in
  let pb = FStar_Pervasives_Native.fst b in
  if pa = ""
  then true
  else if pb = "" then false else (prefix_cmp pa pb) <= Prims.int_zero
let rec ns_insert (x : (Prims.string * Prims.string))
  (l : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match l with
  | [] -> [x]
  | y::ys -> if ns_binding_leq x y then x :: l else y :: (ns_insert x ys)
let rec ns_sort (l : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  match l with | [] -> [] | x::xs -> ns_insert x (ns_sort xs)
let inscope_ns_ordered (elem : Parser_XML.xml_node)
  (anc : Parser_XML.xml_node Prims.list) :
  (Prims.string * Prims.string) Prims.list=
  let raw = collect_ns [] [] (elem :: anc) in
  let with_xml =
    if
      mem_str_e "xml"
        (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst raw)
    then raw
    else FStar_List_Tot_Base.op_At raw [("xml", xpath_xml_ns_uri)] in
  ns_sort with_xml
let rec ns_items (p : Prims.int Prims.list)
  (anc : Parser_XML.xml_node Prims.list) (elem : Parser_XML.xml_node)
  (bs : (Prims.string * Prims.string) Prims.list) (k : Prims.nat) :
  xctx_item Prims.list=
  match bs with
  | [] -> []
  | (pfx, uri)::rest ->
      (CI_Namespace
         ((FStar_List_Tot_Base.op_At p [(Prims.of_int (-2)); k]), anc, elem,
           pfx, uri))
      :: (ns_items p anc elem rest (k + Prims.int_one))
let namespace_axis (it : xctx_item) : xctx_item Prims.list=
  match it with
  | CI_Elem (p, anc, n) ->
      ns_items p anc n (inscope_ns_ordered n anc) Prims.int_zero
  | uu___ -> []
let rec lookup_nsctx (nsctx : (Prims.string * Prims.string) Prims.list)
  (pfx : Prims.string) : Prims.string FStar_Pervasives_Native.option=
  match nsctx with
  | [] -> FStar_Pervasives_Native.None
  | (p, u)::rest ->
      if p = pfx
      then FStar_Pervasives_Native.Some u
      else lookup_nsctx rest pfx
let ns_uri_eq (a : Prims.string FStar_Pervasives_Native.option)
  (b : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  match (a, b) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> true
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) -> x = y
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.None) -> x = ""
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some x) -> x = ""
let name_test_matches_elem (nsctx : (Prims.string * Prims.string) Prims.list)
  (nm : Prims.string) (own_attrs : Parser_XML.xml_attribute Prims.list)
  (anc : Parser_XML.xml_node Prims.list) (tag : Prims.string) : Prims.bool=
  let tpfx = prefix_of nm in
  let tlocal = local_name_of nm in
  let elocal = local_name_of tag in
  if tpfx = ""
  then
    (elocal = tlocal) &&
      (FStar_Pervasives_Native.uu___is_None (elem_ns_uri tag own_attrs anc))
  else
    (match lookup_nsctx nsctx tpfx with
     | FStar_Pervasives_Native.None -> tag = nm
     | FStar_Pervasives_Native.Some turi ->
         (elocal = tlocal) &&
           (ns_uri_eq (elem_ns_uri tag own_attrs anc)
              (FStar_Pervasives_Native.Some turi)))
let prefix_test_matches_elem
  (nsctx : (Prims.string * Prims.string) Prims.list) (pfx : Prims.string)
  (own_attrs : Parser_XML.xml_attribute Prims.list)
  (anc : Parser_XML.xml_node Prims.list) (tag : Prims.string) : Prims.bool=
  match lookup_nsctx nsctx pfx with
  | FStar_Pervasives_Native.None ->
      string_starts_with tag (Prims.strcat pfx ":")
  | FStar_Pervasives_Native.Some turi ->
      ns_uri_eq (elem_ns_uri tag own_attrs anc)
        (FStar_Pervasives_Native.Some turi)
let attr_name_test (nsctx : (Prims.string * Prims.string) Prims.list)
  (nm : Prims.string) (anc : Parser_XML.xml_node Prims.list)
  (owner : Parser_XML.xml_node) (a : Parser_XML.xml_attribute) : Prims.bool=
  let tpfx = prefix_of nm in
  if tpfx = ""
  then
    ((prefix_of a.Parser_XML.attr_name) = "") &&
      ((local_name_of a.Parser_XML.attr_name) = (local_name_of nm))
  else
    (match lookup_nsctx nsctx tpfx with
     | FStar_Pervasives_Native.None -> a.Parser_XML.attr_name = nm
     | FStar_Pervasives_Native.Some turi ->
         let apfx = prefix_of a.Parser_XML.attr_name in
         ((apfx <> "") &&
            ((local_name_of a.Parser_XML.attr_name) = (local_name_of nm)))
           &&
           (ns_uri_eq
              (resolve_ns_uri apfx (Parser_XML.element_attrs owner) anc)
              (FStar_Pervasives_Native.Some turi)))
let matches_node_test (nsctx : (Prims.string * Prims.string) Prims.list)
  (test : Parser_XPath.xp_nodetest) (it : xctx_item) : Prims.bool=
  match (test, it) with
  | (Parser_XPath.NT_Node, uu___) -> true
  | (Parser_XPath.NT_Text, CI_Text (uu___, uu___1, uu___2, uu___3)) -> true
  | (Parser_XPath.NT_Text, uu___) -> false
  | (Parser_XPath.NT_Comment, CI_Comment (uu___, uu___1, uu___2, uu___3)) ->
      true
  | (Parser_XPath.NT_Comment, uu___) -> false
  | (Parser_XPath.NT_PI (FStar_Pervasives_Native.None), CI_PI
     (uu___, uu___1, uu___2, uu___3, uu___4)) -> true
  | (Parser_XPath.NT_PI (FStar_Pervasives_Native.Some tgt), CI_PI
     (uu___, uu___1, uu___2, t, uu___3)) -> t = tgt
  | (Parser_XPath.NT_PI uu___, uu___1) -> false
  | (Parser_XPath.NT_Any, CI_Elem (uu___, uu___1, uu___2)) -> true
  | (Parser_XPath.NT_Any, CI_Attr (uu___, uu___1, uu___2, uu___3)) -> true
  | (Parser_XPath.NT_Any, CI_Namespace
     (uu___, uu___1, uu___2, uu___3, uu___4)) -> true
  | (Parser_XPath.NT_Any, uu___) -> false
  | (Parser_XPath.NT_Name nm, CI_Elem (uu___, anc, n)) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t ->
           name_test_matches_elem nsctx nm (Parser_XML.element_attrs n) anc t
       | FStar_Pervasives_Native.None -> false)
  | (Parser_XPath.NT_Name nm, CI_Attr (uu___, anc, owner, a)) ->
      attr_name_test nsctx nm anc owner a
  | (Parser_XPath.NT_Name nm, CI_Namespace
     (uu___, uu___1, uu___2, pfx, uu___3)) -> nm = pfx
  | (Parser_XPath.NT_Name uu___, uu___1) -> false
  | (Parser_XPath.NT_Prefix pfx, CI_Elem (uu___, anc, n)) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t ->
           prefix_test_matches_elem nsctx pfx (Parser_XML.element_attrs n)
             anc t
       | FStar_Pervasives_Native.None -> false)
  | (Parser_XPath.NT_Prefix pfx, CI_Attr (uu___, uu___1, uu___2, a)) ->
      string_starts_with a.Parser_XML.attr_name (Prims.strcat pfx ":")
  | (Parser_XPath.NT_Prefix uu___, uu___1) -> false
let filter_by_node_test (nsctx : (Prims.string * Prims.string) Prims.list)
  (test : Parser_XPath.xp_nodetest) (items : xctx_item Prims.list) :
  xctx_item Prims.list=
  FStar_List_Tot_Base.filter (matches_node_test nsctx test) items
let rec list_last_or (default_val : Parser_XML.xml_node)
  (l : Parser_XML.xml_node Prims.list) : Parser_XML.xml_node=
  match l with
  | [] -> default_val
  | x::[] -> x
  | uu___::tl -> list_last_or default_val tl
let root_of_item (it : xctx_item) : Parser_XML.xml_node=
  let self_node =
    match it with
    | CI_Elem (uu___, uu___1, n) -> n
    | CI_Attr (uu___, uu___1, owner, uu___2) -> owner
    | CI_Text (uu___, uu___1, parent, uu___2) -> parent
    | CI_Comment (uu___, uu___1, parent, uu___2) -> parent
    | CI_PI (uu___, uu___1, parent, uu___2, uu___3) -> parent
    | CI_Namespace (uu___, uu___1, elem, uu___2, uu___3) -> elem in
  list_last_or self_node (item_ancestors it)
let all_document_items (it : xctx_item) : xctx_item Prims.list=
  let root = root_of_item it in (CI_Elem ([], [], root)) ::
    (descendant_items [] [] root)
let doc_node_of (doc_kids : Parser_XML.xml_node Prims.list) : xctx_item=
  CI_Elem ([], [], (Parser_XML.XElement ("", [], doc_kids)))
let doc_child_items (doc_kids : Parser_XML.xml_node Prims.list) :
  xctx_item Prims.list=
  children_with_paths [] [] (Parser_XML.XElement ("", [], doc_kids)) doc_kids
    Prims.int_zero
let following_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.filter
    (fun x ->
       ((path_compare (item_path x) p) > Prims.int_zero) &&
         (Prims.op_Negation (path_is_prefix p (item_path x))))
    (all_document_items it)
let preceding_axis (it : xctx_item) : xctx_item Prims.list=
  let p = item_path it in
  FStar_List_Tot_Base.rev
    (FStar_List_Tot_Base.filter
       (fun x ->
          ((path_compare (item_path x) p) < Prims.int_zero) &&
            (Prims.op_Negation (path_is_prefix (item_path x) p)))
       (all_document_items it))
let apply_axis (ax : Parser_XPath.xp_axis) (it : xctx_item) :
  xctx_item Prims.list=
  match ax with
  | Parser_XPath.Ax_Self -> [it]
  | Parser_XPath.Ax_Child -> child_axis it
  | Parser_XPath.Ax_Descendant -> descendant_axis it
  | Parser_XPath.Ax_DescendantOrSelf -> it :: (descendant_axis it)
  | Parser_XPath.Ax_Parent -> parent_axis it
  | Parser_XPath.Ax_Ancestor -> ancestor_axis it
  | Parser_XPath.Ax_AncestorOrSelf -> it :: (ancestor_axis it)
  | Parser_XPath.Ax_Attribute -> attribute_axis it
  | Parser_XPath.Ax_FollowingSibling -> following_sibling_axis it
  | Parser_XPath.Ax_PrecedingSibling -> preceding_sibling_axis it
  | Parser_XPath.Ax_Following -> following_axis it
  | Parser_XPath.Ax_Preceding -> preceding_axis it
  | Parser_XPath.Ax_Namespace -> namespace_axis it
type xp_value =
  | XV_Nodes of xctx_item Prims.list 
  | XV_Bool of Prims.bool 
  | XV_Num of xpath_number 
  | XV_Str of Prims.string 
let uu___is_XV_Nodes (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Nodes _0 -> true | uu___ -> false
let __proj__XV_Nodes__item___0 (projectee : xp_value) : xctx_item Prims.list=
  match projectee with | XV_Nodes _0 -> _0
let uu___is_XV_Bool (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Bool _0 -> true | uu___ -> false
let __proj__XV_Bool__item___0 (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Bool _0 -> _0
let uu___is_XV_Num (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Num _0 -> true | uu___ -> false
let __proj__XV_Num__item___0 (projectee : xp_value) : xpath_number=
  match projectee with | XV_Num _0 -> _0
let uu___is_XV_Str (projectee : xp_value) : Prims.bool=
  match projectee with | XV_Str _0 -> true | uu___ -> false
let __proj__XV_Str__item___0 (projectee : xp_value) : Prims.string=
  match projectee with | XV_Str _0 -> _0
type key_entry =
  ((Prims.string FStar_Pervasives_Native.option * Prims.string) *
    Prims.string * xctx_item)
type xp_env =
  {
  env_item: xctx_item ;
  env_pos: Prims.nat ;
  env_size: Prims.nat ;
  env_vars: (Prims.string * xp_value) Prims.list ;
  env_nsctx: (Prims.string * Prims.string) Prims.list ;
  env_doc_kids: Parser_XML.xml_node Prims.list ;
  env_id_attrs: (Prims.string * Prims.string) Prims.list ;
  env_style_root: Parser_XML.xml_node ;
  env_decimal_formats: decimal_format_symbols Prims.list ;
  env_key_table: key_entry Prims.list }
let __proj__Mkxp_env__item__env_item (projectee : xp_env) : xctx_item=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_item
let __proj__Mkxp_env__item__env_pos (projectee : xp_env) : Prims.nat=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_pos
let __proj__Mkxp_env__item__env_size (projectee : xp_env) : Prims.nat=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_size
let __proj__Mkxp_env__item__env_vars (projectee : xp_env) :
  (Prims.string * xp_value) Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_vars
let __proj__Mkxp_env__item__env_nsctx (projectee : xp_env) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_nsctx
let __proj__Mkxp_env__item__env_doc_kids (projectee : xp_env) :
  Parser_XML.xml_node Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_doc_kids
let __proj__Mkxp_env__item__env_id_attrs (projectee : xp_env) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_id_attrs
let __proj__Mkxp_env__item__env_style_root (projectee : xp_env) :
  Parser_XML.xml_node=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_style_root
let __proj__Mkxp_env__item__env_decimal_formats (projectee : xp_env) :
  decimal_format_symbols Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_decimal_formats
let __proj__Mkxp_env__item__env_key_table (projectee : xp_env) :
  key_entry Prims.list=
  match projectee with
  | { env_item; env_pos; env_size; env_vars; env_nsctx; env_doc_kids;
      env_id_attrs; env_style_root; env_decimal_formats; env_key_table;_} ->
      env_key_table
let xnode_none : Parser_XML.xml_node= Parser_XML.XElement ("", [], [])
let is_xnode_none (n : Parser_XML.xml_node) : Prims.bool=
  match n with
  | Parser_XML.XElement (t, attrs, kids) ->
      ((t = "") && (Prims.uu___is_Nil attrs)) && (Prims.uu___is_Nil kids)
  | uu___ -> false
let lookup_var (vars : (Prims.string * xp_value) Prims.list)
  (name : Prims.string) : xp_value FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.find
          (fun kv -> (FStar_Pervasives_Native.fst kv) = name) vars
  with
  | FStar_Pervasives_Native.Some (uu___, v) -> FStar_Pervasives_Native.Some v
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let item_string_value (it : xctx_item) : Prims.string=
  match it with
  | CI_Elem (uu___, uu___1, n) -> Parser_XML.text_content n
  | CI_Attr (uu___, uu___1, uu___2, a) -> a.Parser_XML.attr_value
  | CI_Text (uu___, uu___1, uu___2, t) -> t
  | CI_Comment (uu___, uu___1, uu___2, t) -> t
  | CI_PI (uu___, uu___1, uu___2, uu___3, d) -> d
  | CI_Namespace (uu___, uu___1, uu___2, uu___3, uri) -> uri
let nodeset_string_value (items : xctx_item Prims.list) : Prims.string=
  match items with | [] -> "" | hd::uu___ -> item_string_value hd
let to_string_val (v : xp_value) : Prims.string=
  match v with
  | XV_Str s -> s
  | XV_Num n -> xn_to_string n
  | XV_Bool b -> if b then "true" else "false"
  | XV_Nodes items -> nodeset_string_value items
let to_bool_val (v : xp_value) : Prims.bool=
  match v with
  | XV_Bool b -> b
  | XV_Num n -> xn_to_bool n
  | XV_Str s -> (FStar_String.strlen s) > Prims.int_zero
  | XV_Nodes items -> Prims.op_Negation (Prims.uu___is_Nil items)
let to_number_val (v : xp_value) : xpath_number=
  match v with
  | XV_Num n -> n
  | XV_Bool b ->
      XN_Finite
        ((if b then Prims.int_one else Prims.int_zero), Prims.int_zero)
  | XV_Str s -> string_to_xn s
  | XV_Nodes items -> string_to_xn (nodeset_string_value items)
let xn_finite_int (n : xpath_number) :
  Prims.int FStar_Pervasives_Native.option=
  match n with
  | XN_Finite (v, uu___) when uu___ = Prims.int_zero ->
      FStar_Pervasives_Native.Some v
  | XN_Finite (v, s) ->
      let p = xn_pow10 s in
      if p = Prims.int_zero
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (v / p)
  | uu___ -> FStar_Pervasives_Native.None
let apply_comp_bool (op : Parser_XPath.xp_comp_op) (a : Prims.bool)
  (b : Prims.bool) : Prims.bool=
  match op with
  | Parser_XPath.Cmp_Eq -> a = b
  | Parser_XPath.Cmp_Ne -> a <> b
  | Parser_XPath.Cmp_Lt -> (Prims.op_Negation a) && b
  | Parser_XPath.Cmp_Le -> (Prims.op_Negation a) || b
  | Parser_XPath.Cmp_Gt -> a && (Prims.op_Negation b)
  | Parser_XPath.Cmp_Ge -> a || (Prims.op_Negation b)
let apply_comp_num (op : Parser_XPath.xp_comp_op) (a : xpath_number)
  (b : xpath_number) : Prims.bool=
  match xn_compare a b with
  | FStar_Pervasives_Native.None -> op = Parser_XPath.Cmp_Ne
  | FStar_Pervasives_Native.Some c ->
      (match op with
       | Parser_XPath.Cmp_Eq -> c = Prims.int_zero
       | Parser_XPath.Cmp_Ne -> c <> Prims.int_zero
       | Parser_XPath.Cmp_Lt -> c < Prims.int_zero
       | Parser_XPath.Cmp_Le -> c <= Prims.int_zero
       | Parser_XPath.Cmp_Gt -> c > Prims.int_zero
       | Parser_XPath.Cmp_Ge -> c >= Prims.int_zero)
let apply_comp_str (op : Parser_XPath.xp_comp_op) (a : Prims.string)
  (b : Prims.string) : Prims.bool=
  match op with
  | Parser_XPath.Cmp_Eq -> a = b
  | Parser_XPath.Cmp_Ne -> a <> b
  | Parser_XPath.Cmp_Lt -> (FStar_String.compare a b) < Prims.int_zero
  | Parser_XPath.Cmp_Le -> (FStar_String.compare a b) <= Prims.int_zero
  | Parser_XPath.Cmp_Gt -> (FStar_String.compare a b) > Prims.int_zero
  | Parser_XPath.Cmp_Ge -> (FStar_String.compare a b) >= Prims.int_zero
let rec exists_str (pred : Prims.string -> Prims.bool)
  (items : xctx_item Prims.list) : Prims.bool=
  match items with
  | [] -> false
  | hd::tl -> (pred (item_string_value hd)) || (exists_str pred tl)
let is_relational_op (op : Parser_XPath.xp_comp_op) : Prims.bool=
  match op with
  | Parser_XPath.Cmp_Lt -> true
  | Parser_XPath.Cmp_Le -> true
  | Parser_XPath.Cmp_Gt -> true
  | Parser_XPath.Cmp_Ge -> true
  | uu___ -> false
let xp_compare (op : Parser_XPath.xp_comp_op) (a : xp_value) (b : xp_value) :
  Prims.bool=
  match (a, b) with
  | (XV_Nodes na, XV_Nodes nb) ->
      if is_relational_op op
      then
        exists_str
          (fun sa ->
             exists_str
               (fun sb ->
                  apply_comp_num op (string_to_xn sa) (string_to_xn sb)) nb)
          na
      else
        exists_str
          (fun sa -> exists_str (fun sb -> apply_comp_str op sa sb) nb) na
  | (XV_Nodes na, XV_Num nb) ->
      exists_str (fun sa -> apply_comp_num op (string_to_xn sa) nb) na
  | (XV_Num na, XV_Nodes nb) ->
      exists_str (fun sb -> apply_comp_num op na (string_to_xn sb)) nb
  | (XV_Nodes na, XV_Str sb) ->
      if is_relational_op op
      then
        exists_str
          (fun sa -> apply_comp_num op (string_to_xn sa) (string_to_xn sb))
          na
      else exists_str (fun sa -> apply_comp_str op sa sb) na
  | (XV_Str sa, XV_Nodes nb) ->
      if is_relational_op op
      then
        exists_str
          (fun sb -> apply_comp_num op (string_to_xn sa) (string_to_xn sb))
          nb
      else exists_str (fun sb -> apply_comp_str op sa sb) nb
  | (XV_Nodes na, XV_Bool bb) ->
      apply_comp_bool op (Prims.op_Negation (Prims.uu___is_Nil na)) bb
  | (XV_Bool ba, XV_Nodes nb) ->
      apply_comp_bool op ba (Prims.op_Negation (Prims.uu___is_Nil nb))
  | (XV_Bool uu___, uu___1) ->
      apply_comp_bool op (to_bool_val a) (to_bool_val b)
  | (uu___, XV_Bool uu___1) ->
      apply_comp_bool op (to_bool_val a) (to_bool_val b)
  | (XV_Num uu___, uu___1) ->
      apply_comp_num op (to_number_val a) (to_number_val b)
  | (uu___, XV_Num uu___1) ->
      apply_comp_num op (to_number_val a) (to_number_val b)
  | (uu___, uu___1) -> apply_comp_str op (to_string_val a) (to_string_val b)
let rec str_find_from (s : Prims.string) (sub : Prims.string)
  (pos : Prims.nat) (slen : Prims.nat) (sublen : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  if (pos + sublen) > slen
  then FStar_Pervasives_Native.None
  else
    if (FStar_String.sub s pos sublen) = sub
    then FStar_Pervasives_Native.Some pos
    else
      if pos >= slen
      then FStar_Pervasives_Native.None
      else str_find_from s sub (pos + Prims.int_one) slen sublen
let str_find (s : Prims.string) (sub : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  let slen = FStar_String.strlen s in
  let sublen = FStar_String.strlen sub in
  if sublen = Prims.int_zero
  then FStar_Pervasives_Native.Some Prims.int_zero
  else str_find_from s sub Prims.int_zero slen sublen
let string_starts_with2 (s : Prims.string) (prefix : Prims.string) :
  Prims.bool= string_starts_with s prefix
let is_xp_space (c : FStar_Char.char) : Prims.bool=
  (((c = 32) || (c = 9)) || (c = 10)) || (c = 13)
let rec normalize_space_chars (cs : FStar_Char.char Prims.list)
  (in_space : Prims.bool) : FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      if is_xp_space c
      then
        (if in_space
         then normalize_space_chars rest true
         else 32 :: (normalize_space_chars rest true))
      else c :: (normalize_space_chars rest false)
let normalize_space (s : Prims.string) : Prims.string=
  let collapsed = normalize_space_chars (FStar_String.list_of_string s) true in
  let rev = FStar_List_Tot_Base.rev collapsed in
  let rev' = match rev with | 32::rest -> rest | uu___ -> rev in
  FStar_String.string_of_list (FStar_List_Tot_Base.rev rev')
let rec find_char_index (from_cs : FStar_Char.char Prims.list)
  (c : FStar_Char.char) (idx : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match from_cs with
  | [] -> FStar_Pervasives_Native.None
  | h::t ->
      if h = c
      then FStar_Pervasives_Native.Some idx
      else find_char_index t c (idx + Prims.int_one)
let rec nth_char (to_cs : FStar_Char.char Prims.list) (idx : Prims.nat) :
  FStar_Char.char FStar_Pervasives_Native.option=
  match to_cs with
  | [] -> FStar_Pervasives_Native.None
  | h::t ->
      if idx = Prims.int_zero
      then FStar_Pervasives_Native.Some h
      else nth_char t (idx - Prims.int_one)
let translate_char (from_cs : FStar_Char.char Prims.list)
  (to_cs : FStar_Char.char Prims.list) (c : FStar_Char.char) :
  FStar_Char.char FStar_Pervasives_Native.option=
  match find_char_index from_cs c Prims.int_zero with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some c
  | FStar_Pervasives_Native.Some i -> nth_char to_cs i
let rec translate_chars (from_cs : FStar_Char.char Prims.list)
  (to_cs : FStar_Char.char Prims.list) (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest ->
      let tail = translate_chars from_cs to_cs rest in
      (match translate_char from_cs to_cs c with
       | FStar_Pervasives_Native.Some c' -> c' :: tail
       | FStar_Pervasives_Native.None -> tail)
let translate_str (s : Prims.string) (from_s : Prims.string)
  (to_s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (translate_chars (FStar_String.list_of_string from_s)
       (FStar_String.list_of_string to_s) (FStar_String.list_of_string s))
let xn_le_int (a : xpath_number) (k : Prims.int) : Prims.bool=
  match xn_compare a (XN_Finite (k, Prims.int_zero)) with
  | FStar_Pervasives_Native.Some c -> c <= Prims.int_zero
  | FStar_Pervasives_Native.None -> false
let xn_lt_int (k : Prims.int) (a : xpath_number) : Prims.bool=
  match xn_compare (XN_Finite (k, Prims.int_zero)) a with
  | FStar_Pervasives_Native.Some c -> c < Prims.int_zero
  | FStar_Pervasives_Native.None -> false
let rec substring_collect (s : Prims.string) (start_r : xpath_number)
  (end_bound : xpath_number) (p : Prims.nat) (slen : Prims.nat) :
  Prims.string=
  if p > slen
  then ""
  else
    (let rest =
       substring_collect s start_r end_bound (p + Prims.int_one) slen in
     if (xn_le_int start_r p) && (xn_lt_int p end_bound)
     then
       FStar_String.concat ""
         [FStar_String.sub s (p - Prims.int_one) Prims.int_one; rest]
     else rest)
let substring_impl (s : Prims.string) (start_n : xpath_number)
  (len_n : xpath_number) : Prims.string=
  let start_r = xn_round start_n in
  let len_r = xn_round len_n in
  let end_bound = xn_arith Parser_XPath.Ar_Add start_r len_r in
  substring_collect s start_r end_bound Prims.int_one (FStar_String.strlen s)
let item_qname (it : xctx_item) : Prims.string=
  match it with
  | CI_Elem (uu___, uu___1, n) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> "")
  | CI_Attr (uu___, uu___1, uu___2, a) -> a.Parser_XML.attr_name
  | CI_PI (uu___, uu___1, uu___2, tg, uu___3) -> tg
  | CI_Namespace (uu___, uu___1, uu___2, pfx, uu___3) -> pfx
  | uu___ -> ""
let item_namespace_uri (it : xctx_item) : Prims.string=
  match it with
  | CI_Elem (uu___, anc, n) ->
      (match Parser_XML.element_tag n with
       | FStar_Pervasives_Native.Some t ->
           (match elem_ns_uri t (Parser_XML.element_attrs n) anc with
            | FStar_Pervasives_Native.Some u -> u
            | FStar_Pervasives_Native.None -> "")
       | FStar_Pervasives_Native.None -> "")
  | CI_Attr (uu___, anc, owner, a) ->
      let pfx = prefix_of a.Parser_XML.attr_name in
      if pfx = ""
      then ""
      else
        (match resolve_ns_uri pfx (Parser_XML.element_attrs owner) anc with
         | FStar_Pervasives_Native.Some u -> u
         | FStar_Pervasives_Native.None -> "")
  | uu___ -> ""
let rec sum_items (items : xctx_item Prims.list) : xpath_number=
  match items with
  | [] -> XN_Finite (Prims.int_zero, Prims.int_zero)
  | hd::tl ->
      xn_arith Parser_XPath.Ar_Add (string_to_xn (item_string_value hd))
        (sum_items tl)
let rec insert_by_doc (x : xctx_item) (l : xctx_item Prims.list) :
  xctx_item Prims.list=
  match l with
  | [] -> [x]
  | y::ys ->
      let c = path_compare (item_path x) (item_path y) in
      if c < Prims.int_zero
      then x :: l
      else if c = Prims.int_zero then l else y :: (insert_by_doc x ys)
let rec doc_sort_dedup (l : xctx_item Prims.list) : xctx_item Prims.list=
  match l with | [] -> [] | x::xs -> insert_by_doc x (doc_sort_dedup xs)
let rec xp_expr_size (e : Parser_XPath.xp_expr) : Prims.nat=
  match e with
  | Parser_XPath.XE_Path (uu___, steps) ->
      Prims.int_one + (xp_steps_size steps)
  | Parser_XPath.XE_FilterPath (primary, preds, steps) ->
      ((Prims.int_one + (xp_expr_size primary)) + (xp_exprs_size preds)) +
        (xp_steps_size steps)
  | Parser_XPath.XE_Union (a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Or (a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_And (a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Compare (uu___, a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Arith (uu___, a, b) ->
      (Prims.int_one + (xp_expr_size a)) + (xp_expr_size b)
  | Parser_XPath.XE_Neg a -> Prims.int_one + (xp_expr_size a)
  | Parser_XPath.XE_Number (uu___, uu___1) -> Prims.int_one
  | Parser_XPath.XE_Literal uu___ -> Prims.int_one
  | Parser_XPath.XE_VarRef uu___ -> Prims.int_one
  | Parser_XPath.XE_FunCall (uu___, args) ->
      Prims.int_one + (xp_exprs_size args)
and xp_exprs_size (es : Parser_XPath.xp_expr Prims.list) : Prims.nat=
  match es with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (xp_expr_size hd)) + (xp_exprs_size tl)
and xp_steps_size (ss : Parser_XPath.xp_step Prims.list) : Prims.nat=
  match ss with
  | [] -> Prims.int_zero
  | hd::tl -> (Prims.int_one + (xp_step_size hd)) + (xp_steps_size tl)
and xp_step_size (s : Parser_XPath.xp_step) : Prims.nat=
  Prims.int_one + (xp_exprs_size s.Parser_XPath.step_preds)
let rec xml_node_count (n : Parser_XML.xml_node) : Prims.nat=
  match n with
  | Parser_XML.XElement (uu___, uu___1, children) ->
      Prims.int_one + (xml_nodes_count children)
  | uu___ -> Prims.int_one
and xml_nodes_count (ns : Parser_XML.xml_node Prims.list) : Prims.nat=
  match ns with
  | [] -> Prims.int_zero
  | hd::tl -> (xml_node_count hd) + (xml_nodes_count tl)
let initial_eval_fuel (e : Parser_XPath.xp_expr) (doc_nodes : Prims.nat) :
  Prims.nat=
  (((xp_expr_size e) + Prims.int_one) *
     ((doc_nodes + Prims.int_one) * (Prims.of_int (24))))
    + (Prims.of_int (4096))
let is_supported_xpath_function (nm : Prims.string) : Prims.bool=
  (((((((((((((((((((((((((((((((nm = "position") || (nm = "last")) ||
                                 (nm = "count"))
                                || (nm = "name"))
                               || (nm = "local-name"))
                              || (nm = "namespace-uri"))
                             || (nm = "current"))
                            || (nm = "string"))
                           || (nm = "concat"))
                          || (nm = "contains"))
                         || (nm = "starts-with"))
                        || (nm = "substring-before"))
                       || (nm = "substring-after"))
                      || (nm = "substring"))
                     || (nm = "string-length"))
                    || (nm = "normalize-space"))
                   || (nm = "translate"))
                  || (nm = "not"))
                 || (nm = "true"))
                || (nm = "false"))
               || (nm = "boolean"))
              || (nm = "lang"))
             || (nm = "number"))
            || (nm = "sum"))
           || (nm = "floor"))
          || (nm = "ceiling"))
         || (nm = "round"))
        || (nm = "id"))
       || (nm = "document"))
      || (nm = "format-number"))
     || (nm = "key"))
    || (nm = "generate-id")
let rec ws_split_chars (cs : FStar_Char.char Prims.list)
  (cur : FStar_Char.char Prims.list) (acc : Prims.string Prims.list) :
  Prims.string Prims.list=
  match cs with
  | [] ->
      FStar_List_Tot_Base.rev
        (if Prims.uu___is_Nil cur
         then acc
         else (FStar_String.string_of_list (FStar_List_Tot_Base.rev cur)) ::
           acc)
  | c::rest ->
      if (((c = 32) || (c = 9)) || (c = 10)) || (c = 13)
      then
        ws_split_chars rest []
          (if Prims.uu___is_Nil cur
           then acc
           else (FStar_String.string_of_list (FStar_List_Tot_Base.rev cur))
             :: acc)
      else ws_split_chars rest (c :: cur) acc
let ws_tokens (s : Prims.string) : Prims.string Prims.list=
  ws_split_chars (FStar_String.list_of_string s) [] []
let rec id_attr_declared
  (id_attrs : (Prims.string * Prims.string) Prims.list) (tag : Prims.string)
  (attr : Prims.string) : Prims.bool=
  match id_attrs with
  | [] -> false
  | (e, a)::rest ->
      if (e = tag) && (a = attr)
      then true
      else id_attr_declared rest tag attr
let rec str_mem (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with | [] -> false | h::t -> if h = x then true else str_mem x t
let elem_has_id (id_attrs : (Prims.string * Prims.string) Prims.list)
  (wanted : Prims.string Prims.list) (it : xctx_item) : Prims.bool=
  match it with
  | CI_Elem (uu___, uu___1, Parser_XML.XElement (tag, attrs, uu___2)) ->
      FStar_List_Tot_Base.existsb
        (fun a ->
           (id_attr_declared id_attrs tag a.Parser_XML.attr_name) &&
             (str_mem a.Parser_XML.attr_value wanted)) attrs
  | uu___ -> false
let id_wanted_tokens (v : xp_value) : Prims.string Prims.list=
  match v with
  | XV_Nodes items ->
      FStar_List_Tot_Base.collect
        (fun it -> ws_tokens (item_string_value it)) items
  | other -> ws_tokens (to_string_val other)
let path_segment_str (n : Prims.int) : Prims.string=
  if n < Prims.int_zero
  then Prims.strcat "n" (Prims.string_of_int (Prims.int_zero - n))
  else Prims.string_of_int n
let rec path_to_id_string (p : Prims.int Prims.list) : Prims.string=
  match p with
  | [] -> ""
  | x::rest ->
      Prims.strcat "_"
        (Prims.strcat (path_segment_str x) (path_to_id_string rest))
let generate_id_of_item (it : xctx_item) : Prims.string=
  Prims.strcat "genid" (path_to_id_string (item_path it))
let resolve_key_qname (nsctx : (Prims.string * Prims.string) Prims.list)
  (qn : Prims.string) :
  (Prims.string FStar_Pervasives_Native.option * Prims.string)=
  ((lookup_nsctx nsctx (prefix_of qn)), (local_name_of qn))
let rec eval_expr (fuel : Prims.nat) (env : xp_env)
  (e : Parser_XPath.xp_expr) : xp_value=
  if fuel = Prims.int_zero
  then XV_Str ""
  else
    (match e with
     | Parser_XPath.XE_Number (v, s) -> XV_Num (XN_Finite (v, s))
     | Parser_XPath.XE_Literal s -> XV_Str s
     | Parser_XPath.XE_VarRef name ->
         (match lookup_var env.env_vars name with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None -> XV_Str "")
     | Parser_XPath.XE_Neg e1 ->
         XV_Num
           (xn_neg (to_number_val (eval_expr (fuel - Prims.int_one) env e1)))
     | Parser_XPath.XE_Arith (op, a, b) ->
         XV_Num
           (xn_arith op
              (to_number_val (eval_expr (fuel - Prims.int_one) env a))
              (to_number_val (eval_expr (fuel - Prims.int_one) env b)))
     | Parser_XPath.XE_Compare (op, a, b) ->
         XV_Bool
           (xp_compare op (eval_expr (fuel - Prims.int_one) env a)
              (eval_expr (fuel - Prims.int_one) env b))
     | Parser_XPath.XE_And (a, b) ->
         XV_Bool
           ((to_bool_val (eval_expr (fuel - Prims.int_one) env a)) &&
              (to_bool_val (eval_expr (fuel - Prims.int_one) env b)))
     | Parser_XPath.XE_Or (a, b) ->
         XV_Bool
           ((to_bool_val (eval_expr (fuel - Prims.int_one) env a)) ||
              (to_bool_val (eval_expr (fuel - Prims.int_one) env b)))
     | Parser_XPath.XE_Union (a, b) ->
         (match ((eval_expr (fuel - Prims.int_one) env a),
                  (eval_expr (fuel - Prims.int_one) env b))
          with
          | (XV_Nodes na, XV_Nodes nb) ->
              XV_Nodes (doc_sort_dedup (FStar_List_Tot_Base.op_At na nb))
          | (XV_Nodes na, uu___1) -> XV_Nodes (doc_sort_dedup na)
          | (uu___1, XV_Nodes nb) -> XV_Nodes (doc_sort_dedup nb)
          | (uu___1, uu___2) -> XV_Nodes [])
     | Parser_XPath.XE_FunCall (name, args) ->
         eval_funcall (fuel - Prims.int_one) env name args
     | Parser_XPath.XE_Path (absolute, steps) ->
         if absolute
         then
           XV_Nodes
             (eval_absolute_steps (fuel - Prims.int_one) env
                (root_of_item env.env_item) env.env_doc_kids steps)
         else
           XV_Nodes
             (eval_steps (fuel - Prims.int_one) env [env.env_item] steps)
     | Parser_XPath.XE_FilterPath (primary, preds, steps) ->
         let pv = eval_expr (fuel - Prims.int_one) env primary in
         (match pv with
          | XV_Nodes items0 ->
              let items1 =
                filter_items_by_preds (fuel - Prims.int_one) env items0 preds in
              XV_Nodes (eval_steps (fuel - Prims.int_one) env items1 steps)
          | other ->
              if (Prims.uu___is_Nil preds) && (Prims.uu___is_Nil steps)
              then other
              else XV_Nodes []))
and eval_absolute_steps (fuel : Prims.nat) (env : xp_env)
  (root_node : Parser_XML.xml_node)
  (doc_kids : Parser_XML.xml_node Prims.list)
  (steps : Parser_XPath.xp_step Prims.list) : xctx_item Prims.list=
  let vars = env.env_vars in
  let nsctx = env.env_nsctx in
  if fuel = Prims.int_zero
  then []
  else
    if
      (match doc_kids with
       | [] -> false
       | uu___1::[] -> false
       | uu___1 -> true)
    then
      (let doc_node = doc_node_of doc_kids in
       match steps with
       | [] -> [doc_node]
       | uu___1 -> eval_steps (fuel - Prims.int_one) env [doc_node] steps)
    else
      (let root_item = CI_Elem ([], [], root_node) in
       match steps with
       | [] -> [root_item]
       | s::rest ->
           let expansion =
             match s.Parser_XPath.step_axis with
             | Parser_XPath.Ax_Child ->
                 filter_by_node_test nsctx s.Parser_XPath.step_test
                   [root_item]
             | Parser_XPath.Ax_Self ->
                 filter_by_node_test nsctx s.Parser_XPath.step_test
                   [root_item]
             | Parser_XPath.Ax_Descendant ->
                 filter_by_node_test nsctx s.Parser_XPath.step_test
                   (descendant_items [] [] root_node)
             | Parser_XPath.Ax_DescendantOrSelf ->
                 filter_by_node_test nsctx s.Parser_XPath.step_test
                   (root_item :: (descendant_items [] [] root_node))
             | Parser_XPath.Ax_Attribute ->
                 filter_by_node_test nsctx s.Parser_XPath.step_test
                   (apply_axis Parser_XPath.Ax_Attribute root_item)
             | uu___2 -> [] in
           let kept =
             filter_items_by_preds (fuel - Prims.int_one) env expansion
               s.Parser_XPath.step_preds in
           let normal = eval_steps (fuel - Prims.int_one) env kept rest in
           if
             ((s.Parser_XPath.step_axis = Parser_XPath.Ax_DescendantOrSelf)
                && (s.Parser_XPath.step_test = Parser_XPath.NT_Node))
               && (Prims.uu___is_Nil s.Parser_XPath.step_preds)
           then
             (match rest with
              | nxt::rest2 ->
                  if nxt.Parser_XPath.step_axis = Parser_XPath.Ax_Child
                  then
                    let root_as_child =
                      if
                        matches_node_test nsctx nxt.Parser_XPath.step_test
                          root_item
                      then [root_item]
                      else [] in
                    let root_as_child' =
                      filter_items_by_preds (fuel - Prims.int_one) env
                        root_as_child nxt.Parser_XPath.step_preds in
                    let extra =
                      eval_steps (fuel - Prims.int_one) env root_as_child'
                        rest2 in
                    FStar_List_Tot_Base.op_At extra normal
                  else normal
              | [] -> normal)
           else normal)
and eval_steps (fuel : Prims.nat) (env : xp_env)
  (items : xctx_item Prims.list) (steps : Parser_XPath.xp_step Prims.list) :
  xctx_item Prims.list=
  if fuel = Prims.int_zero
  then items
  else
    (match steps with
     | [] -> items
     | s::rest ->
         let expanded =
           expand_step_over_items (fuel - Prims.int_one) env s items in
         eval_steps (fuel - Prims.int_one) env expanded rest)
and expand_step_over_items (fuel : Prims.nat) (env : xp_env)
  (s : Parser_XPath.xp_step) (items : xctx_item Prims.list) :
  xctx_item Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | it::rest ->
         let raw = apply_axis s.Parser_XPath.step_axis it in
         let tested =
           filter_by_node_test env.env_nsctx s.Parser_XPath.step_test raw in
         let kept =
           filter_items_by_preds (fuel - Prims.int_one) env tested
             s.Parser_XPath.step_preds in
         FStar_List_Tot_Base.op_At kept
           (expand_step_over_items (fuel - Prims.int_one) env s rest))
and filter_items_by_preds (fuel : Prims.nat) (env : xp_env)
  (items : xctx_item Prims.list) (preds : Parser_XPath.xp_expr Prims.list) :
  xctx_item Prims.list=
  if fuel = Prims.int_zero
  then items
  else
    (match preds with
     | [] -> items
     | p::rest ->
         let size = FStar_List_Tot_Base.length items in
         let kept =
           filter_one_pred (fuel - Prims.int_one) env p items size
             Prims.int_one in
         filter_items_by_preds (fuel - Prims.int_one) env kept rest)
and filter_one_pred (fuel : Prims.nat) (env : xp_env)
  (p : Parser_XPath.xp_expr) (items : xctx_item Prims.list)
  (size : Prims.nat) (pos : Prims.nat) : xctx_item Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (match items with
     | [] -> []
     | it::rest ->
         let e =
           {
             env_item = it;
             env_pos = pos;
             env_size = size;
             env_vars = (env.env_vars);
             env_nsctx = (env.env_nsctx);
             env_doc_kids = (env.env_doc_kids);
             env_id_attrs = (env.env_id_attrs);
             env_style_root = (env.env_style_root);
             env_decimal_formats = (env.env_decimal_formats);
             env_key_table = (env.env_key_table)
           } in
         let v = eval_expr (fuel - Prims.int_one) e p in
         let keep =
           match v with
           | XV_Num n ->
               (match xn_finite_int (xn_round n) with
                | FStar_Pervasives_Native.Some k -> k = pos
                | FStar_Pervasives_Native.None -> false)
           | uu___1 -> to_bool_val v in
         let tail =
           filter_one_pred (fuel - Prims.int_one) env p rest size
             (pos + Prims.int_one) in
         if keep then it :: tail else tail)
and eval_concat_args (fuel : Prims.nat) (env : xp_env)
  (args : Parser_XPath.xp_expr Prims.list) : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match args with
     | [] -> ""
     | a::rest ->
         Prims.strcat
           (to_string_val (eval_expr (fuel - Prims.int_one) env a))
           (eval_concat_args (fuel - Prims.int_one) env rest))
and eval_funcall (fuel : Prims.nat) (env : xp_env) (name : Prims.string)
  (args : Parser_XPath.xp_expr Prims.list) : xp_value=
  if fuel = Prims.int_zero
  then XV_Str ""
  else
    if name = "position"
    then XV_Num (XN_Finite ((env.env_pos), Prims.int_zero))
    else
      if name = "last"
      then XV_Num (XN_Finite ((env.env_size), Prims.int_zero))
      else
        if name = "count"
        then
          (match args with
           | a::[] ->
               (match eval_expr (fuel - Prims.int_one) env a with
                | XV_Nodes items ->
                    XV_Num
                      (XN_Finite
                         ((FStar_List_Tot_Base.length items), Prims.int_zero))
                | uu___3 ->
                    XV_Num (XN_Finite (Prims.int_zero, Prims.int_zero)))
           | uu___3 -> XV_Num (XN_Finite (Prims.int_zero, Prims.int_zero)))
        else
          if name = "id"
          then
            (match args with
             | a::[] ->
                 let wanted =
                   id_wanted_tokens (eval_expr (fuel - Prims.int_one) env a) in
                 (match wanted with
                  | [] -> XV_Nodes []
                  | uu___4 ->
                      let all = all_document_items env.env_item in
                      XV_Nodes
                        (FStar_List_Tot_Base.filter
                           (elem_has_id env.env_id_attrs wanted) all))
             | uu___4 -> XV_Nodes [])
          else
            if name = "document"
            then
              (match args with
               | a::[] ->
                   let s =
                     to_string_val (eval_expr (fuel - Prims.int_one) env a) in
                   if s = ""
                   then
                     (if is_xnode_none env.env_style_root
                      then XV_Nodes []
                      else XV_Nodes [CI_Elem ([], [], (env.env_style_root))])
                   else XV_Nodes []
               | uu___5 -> XV_Nodes [])
            else
              if (name = "name") || (name = "local-name")
              then
                (let items =
                   match args with
                   | [] -> [env.env_item]
                   | a::uu___6 ->
                       (match eval_expr (fuel - Prims.int_one) env a with
                        | XV_Nodes its -> its
                        | uu___7 -> []) in
                 match items with
                 | [] -> XV_Str ""
                 | it::uu___6 ->
                     let qn = item_qname it in
                     XV_Str
                       (if name = "local-name" then local_name_of qn else qn))
              else
                if name = "namespace-uri"
                then
                  (let items =
                     match args with
                     | [] -> [env.env_item]
                     | a::uu___7 ->
                         (match eval_expr (fuel - Prims.int_one) env a with
                          | XV_Nodes its -> its
                          | uu___8 -> []) in
                   match items with
                   | [] -> XV_Str ""
                   | it::uu___7 -> XV_Str (item_namespace_uri it))
                else
                  if name = "current"
                  then XV_Nodes [env.env_item]
                  else
                    if name = "string"
                    then
                      (match args with
                       | [] -> XV_Str (item_string_value env.env_item)
                       | a::uu___9 ->
                           XV_Str
                             (to_string_val
                                (eval_expr (fuel - Prims.int_one) env a)))
                    else
                      if name = "concat"
                      then
                        XV_Str
                          (eval_concat_args (fuel - Prims.int_one) env args)
                      else
                        if name = "contains"
                        then
                          (match args with
                           | a::b::[] ->
                               let s =
                                 to_string_val
                                   (eval_expr (fuel - Prims.int_one) env a) in
                               let sub =
                                 to_string_val
                                   (eval_expr (fuel - Prims.int_one) env b) in
                               XV_Bool
                                 (FStar_Pervasives_Native.uu___is_Some
                                    (str_find s sub))
                           | uu___11 -> XV_Bool false)
                        else
                          if name = "starts-with"
                          then
                            (match args with
                             | a::b::[] ->
                                 XV_Bool
                                   (string_starts_with2
                                      (to_string_val
                                         (eval_expr (fuel - Prims.int_one)
                                            env a))
                                      (to_string_val
                                         (eval_expr (fuel - Prims.int_one)
                                            env b)))
                             | uu___12 -> XV_Bool false)
                          else
                            if name = "substring-before"
                            then
                              (match args with
                               | a::b::[] ->
                                   let s =
                                     to_string_val
                                       (eval_expr (fuel - Prims.int_one) env
                                          a) in
                                   let sub =
                                     to_string_val
                                       (eval_expr (fuel - Prims.int_one) env
                                          b) in
                                   (match str_find s sub with
                                    | FStar_Pervasives_Native.Some i ->
                                        XV_Str
                                          (FStar_String.sub s Prims.int_zero
                                             i)
                                    | FStar_Pervasives_Native.None ->
                                        XV_Str "")
                               | uu___13 -> XV_Str "")
                            else
                              if name = "substring-after"
                              then
                                (match args with
                                 | a::b::[] ->
                                     let s =
                                       to_string_val
                                         (eval_expr (fuel - Prims.int_one)
                                            env a) in
                                     let sub =
                                       to_string_val
                                         (eval_expr (fuel - Prims.int_one)
                                            env b) in
                                     (match str_find s sub with
                                      | FStar_Pervasives_Native.Some i ->
                                          let sl = FStar_String.strlen sub in
                                          XV_Str
                                            (FStar_String.sub s (i + sl)
                                               (((FStar_String.strlen s) - i)
                                                  - sl))
                                      | FStar_Pervasives_Native.None ->
                                          XV_Str "")
                                 | uu___14 -> XV_Str "")
                              else
                                if name = "substring"
                                then
                                  (match args with
                                   | a::b::[] ->
                                       let s =
                                         to_string_val
                                           (eval_expr (fuel - Prims.int_one)
                                              env a) in
                                       let sv =
                                         to_number_val
                                           (eval_expr (fuel - Prims.int_one)
                                              env b) in
                                       XV_Str (substring_impl s sv XN_PosInf)
                                   | a::b::c::[] ->
                                       let s =
                                         to_string_val
                                           (eval_expr (fuel - Prims.int_one)
                                              env a) in
                                       let sv =
                                         to_number_val
                                           (eval_expr (fuel - Prims.int_one)
                                              env b) in
                                       let lv =
                                         to_number_val
                                           (eval_expr (fuel - Prims.int_one)
                                              env c) in
                                       XV_Str (substring_impl s sv lv)
                                   | uu___15 -> XV_Str "")
                                else
                                  if name = "string-length"
                                  then
                                    (let s =
                                       match args with
                                       | [] -> item_string_value env.env_item
                                       | a::uu___16 ->
                                           to_string_val
                                             (eval_expr
                                                (fuel - Prims.int_one) env a) in
                                     XV_Num
                                       (XN_Finite
                                          ((FStar_String.strlen s),
                                            Prims.int_zero)))
                                  else
                                    if name = "normalize-space"
                                    then
                                      (let s =
                                         match args with
                                         | [] ->
                                             item_string_value env.env_item
                                         | a::uu___17 ->
                                             to_string_val
                                               (eval_expr
                                                  (fuel - Prims.int_one) env
                                                  a) in
                                       XV_Str (normalize_space s))
                                    else
                                      if name = "translate"
                                      then
                                        (match args with
                                         | a::b::c::[] ->
                                             let s =
                                               to_string_val
                                                 (eval_expr
                                                    (fuel - Prims.int_one)
                                                    env a) in
                                             let from_s =
                                               to_string_val
                                                 (eval_expr
                                                    (fuel - Prims.int_one)
                                                    env b) in
                                             let to_s =
                                               to_string_val
                                                 (eval_expr
                                                    (fuel - Prims.int_one)
                                                    env c) in
                                             XV_Str
                                               (translate_str s from_s to_s)
                                         | uu___18 -> XV_Str "")
                                      else
                                        if name = "not"
                                        then
                                          (match args with
                                           | a::[] ->
                                               XV_Bool
                                                 (Prims.op_Negation
                                                    (to_bool_val
                                                       (eval_expr
                                                          (fuel -
                                                             Prims.int_one)
                                                          env a)))
                                           | uu___19 -> XV_Bool true)
                                        else
                                          if name = "true"
                                          then XV_Bool true
                                          else
                                            if name = "false"
                                            then XV_Bool false
                                            else
                                              if name = "boolean"
                                              then
                                                (match args with
                                                 | a::[] ->
                                                     XV_Bool
                                                       (to_bool_val
                                                          (eval_expr
                                                             (fuel -
                                                                Prims.int_one)
                                                             env a))
                                                 | uu___22 -> XV_Bool false)
                                              else
                                                if name = "lang"
                                                then
                                                  (match args with
                                                   | a::[] ->
                                                       let arg =
                                                         to_string_val
                                                           (eval_expr
                                                              (fuel -
                                                                 Prims.int_one)
                                                              env a) in
                                                       (match item_xml_lang
                                                                env.env_item
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            nl ->
                                                            XV_Bool
                                                              (lang_matches
                                                                 nl arg)
                                                        | FStar_Pervasives_Native.None
                                                            -> XV_Bool false)
                                                   | uu___23 -> XV_Bool false)
                                                else
                                                  if name = "number"
                                                  then
                                                    (match args with
                                                     | [] ->
                                                         XV_Num
                                                           (to_number_val
                                                              (XV_Str
                                                                 (item_string_value
                                                                    env.env_item)))
                                                     | a::uu___24 ->
                                                         XV_Num
                                                           (to_number_val
                                                              (eval_expr
                                                                 (fuel -
                                                                    Prims.int_one)
                                                                 env a)))
                                                  else
                                                    if name = "sum"
                                                    then
                                                      (match args with
                                                       | a::[] ->
                                                           (match eval_expr
                                                                    (
                                                                    fuel -
                                                                    Prims.int_one)
                                                                    env a
                                                            with
                                                            | XV_Nodes items
                                                                ->
                                                                XV_Num
                                                                  (sum_items
                                                                    items)
                                                            | uu___25 ->
                                                                XV_Num
                                                                  (XN_Finite
                                                                    (Prims.int_zero,
                                                                    Prims.int_zero)))
                                                       | uu___25 ->
                                                           XV_Num
                                                             (XN_Finite
                                                                (Prims.int_zero,
                                                                  Prims.int_zero)))
                                                    else
                                                      if name = "floor"
                                                      then
                                                        (match args with
                                                         | a::[] ->
                                                             XV_Num
                                                               (xn_floor
                                                                  (to_number_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a)))
                                                         | uu___26 ->
                                                             XV_Num XN_NaN)
                                                      else
                                                        if name = "ceiling"
                                                        then
                                                          (match args with
                                                           | a::[] ->
                                                               XV_Num
                                                                 (xn_ceiling
                                                                    (
                                                                    to_number_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a)))
                                                           | uu___27 ->
                                                               XV_Num XN_NaN)
                                                        else
                                                          if name = "round"
                                                          then
                                                            (match args with
                                                             | a::[] ->
                                                                 XV_Num
                                                                   (xn_round
                                                                    (to_number_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a)))
                                                             | uu___28 ->
                                                                 XV_Num
                                                                   XN_NaN)
                                                          else
                                                            if
                                                              name =
                                                                "function-available"
                                                            then
                                                              (match args
                                                               with
                                                               | a::[] ->
                                                                   XV_Bool
                                                                    (is_supported_xpath_function
                                                                    (to_string_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a)))
                                                               | uu___29 ->
                                                                   XV_Bool
                                                                    false)
                                                            else
                                                              if
                                                                name =
                                                                  "format-number"
                                                              then
                                                                (match args
                                                                 with
                                                                 | a::b::[]
                                                                    ->
                                                                    let num =
                                                                    to_number_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a) in
                                                                    let pic =
                                                                    to_string_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env b) in
                                                                    XV_Str
                                                                    (format_number_str
                                                                    num pic
                                                                    (lookup_decimal_format
                                                                    env.env_decimal_formats
                                                                    ""))
                                                                 | a::b::c::[]
                                                                    ->
                                                                    let num =
                                                                    to_number_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a) in
                                                                    let pic =
                                                                    to_string_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env b) in
                                                                    let nm =
                                                                    to_string_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env c) in
                                                                    XV_Str
                                                                    (format_number_str
                                                                    num pic
                                                                    (lookup_decimal_format
                                                                    env.env_decimal_formats
                                                                    nm))
                                                                 | uu___30 ->
                                                                    XV_Str "")
                                                              else
                                                                if
                                                                  name =
                                                                    "element-available"
                                                                then
                                                                  XV_Bool
                                                                    false
                                                                else
                                                                  if
                                                                    name =
                                                                    "key"
                                                                  then
                                                                    (
                                                                    match args
                                                                    with
                                                                    | 
                                                                    a::b::[]
                                                                    ->
                                                                    let kname
                                                                    =
                                                                    resolve_key_qname
                                                                    env.env_nsctx
                                                                    (to_string_val
                                                                    (eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a)) in
                                                                    let wanted
                                                                    =
                                                                    match 
                                                                    eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env b
                                                                    with
                                                                    | 
                                                                    XV_Nodes
                                                                    items ->
                                                                    FStar_List_Tot_Base.map
                                                                    item_string_value
                                                                    items
                                                                    | 
                                                                    other ->
                                                                    [
                                                                    to_string_val
                                                                    other] in
                                                                    let hits
                                                                    =
                                                                    FStar_List_Tot_Base.filter
                                                                    (fun e ->
                                                                    let uu___32
                                                                    = e in
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    (kn, kv,
                                                                    uu___33)
                                                                    ->
                                                                    (kn =
                                                                    kname) &&
                                                                    (str_mem
                                                                    kv wanted))
                                                                    env.env_key_table in
                                                                    XV_Nodes
                                                                    (doc_sort_dedup
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun e ->
                                                                    let uu___32
                                                                    = e in
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    (uu___33,
                                                                    uu___34,
                                                                    it) -> it)
                                                                    hits))
                                                                    | 
                                                                    uu___32
                                                                    ->
                                                                    XV_Nodes
                                                                    [])
                                                                  else
                                                                    if
                                                                    name =
                                                                    "generate-id"
                                                                    then
                                                                    (match args
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    XV_Str
                                                                    (generate_id_of_item
                                                                    env.env_item)
                                                                    | 
                                                                    a::uu___33
                                                                    ->
                                                                    (match 
                                                                    eval_expr
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    env a
                                                                    with
                                                                    | 
                                                                    XV_Nodes
                                                                    ns ->
                                                                    (match 
                                                                    doc_sort_dedup
                                                                    ns
                                                                    with
                                                                    | 
                                                                    it::uu___34
                                                                    ->
                                                                    XV_Str
                                                                    (generate_id_of_item
                                                                    it)
                                                                    | 
                                                                    [] ->
                                                                    XV_Str "")
                                                                    | 
                                                                    uu___34
                                                                    ->
                                                                    XV_Str ""))
                                                                    else
                                                                    XV_Str ""
let rec find_child_index (nodes : Parser_XML.xml_node Prims.list)
  (target : Parser_XML.xml_node) (i : Prims.nat) : Prims.nat=
  match nodes with
  | [] -> Prims.int_zero
  | x::rest ->
      if x = target
      then i
      else find_child_index rest target (i + Prims.int_one)
let rec path_of_chain (chain : Parser_XML.xml_node Prims.list) :
  Prims.int Prims.list=
  match chain with
  | [] -> []
  | uu___::[] -> []
  | parent::rest ->
      (match rest with
       | [] -> []
       | child::uu___ ->
           let i =
             find_child_index (Parser_XML.element_children parent) child
               Prims.int_zero in
           i :: (path_of_chain rest))
let compute_ctx_path (ancestors : Parser_XML.xml_node Prims.list)
  (ctx : Parser_XML.xml_node) : Prims.int Prims.list=
  path_of_chain
    (FStar_List_Tot_Base.append (FStar_List_Tot_Base.rev ancestors) [ctx])
let eval_xpath_from_root (root_node : Parser_XML.xml_node)
  (vars : (Prims.string * xp_value) Prims.list) (expr_text : Prims.string) :
  xp_value FStar_Pervasives_Native.option=
  match Parser_XPath.parse_xpath expr_text with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some e ->
      let fuel = initial_eval_fuel e (xml_node_count root_node) in
      let env =
        {
          env_item = (CI_Elem ([], [], root_node));
          env_pos = Prims.int_one;
          env_size = Prims.int_one;
          env_vars = vars;
          env_nsctx = [];
          env_doc_kids = [];
          env_id_attrs = [];
          env_style_root = xnode_none;
          env_decimal_formats = [];
          env_key_table = []
        } in
      FStar_Pervasives_Native.Some (eval_expr fuel env e)
let eval_xpath_from_item (ancestors : Parser_XML.xml_node Prims.list)
  (context_node : Parser_XML.xml_node)
  (vars : (Prims.string * xp_value) Prims.list) (expr_text : Prims.string) :
  xp_value FStar_Pervasives_Native.option=
  match Parser_XPath.parse_xpath expr_text with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some e ->
      let doc_nodes =
        (xml_node_count context_node) + (xml_nodes_count ancestors) in
      let fuel = initial_eval_fuel e doc_nodes in
      let env =
        {
          env_item =
            (CI_Elem
               ((compute_ctx_path ancestors context_node), ancestors,
                 context_node));
          env_pos = Prims.int_one;
          env_size = Prims.int_one;
          env_vars = vars;
          env_nsctx = [];
          env_doc_kids = [];
          env_id_attrs = [];
          env_style_root = xnode_none;
          env_decimal_formats = [];
          env_key_table = []
        } in
      FStar_Pervasives_Native.Some (eval_expr fuel env e)
