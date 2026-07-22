open Prims
let rec pow2 (n : Prims.nat) : Prims.pos=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (2)) * (pow2 (n - Prims.int_one))
let rec pow10 (n : Prims.nat) : Prims.pos=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec bitlen (n : Prims.nat) : Prims.nat=
  if n = Prims.int_zero
  then Prims.int_zero
  else Prims.int_one + (bitlen (n / (Prims.of_int (2))))
let mul_pos (a : Prims.pos) (b : Prims.pos) : Prims.pos= a * b
let geq_ratio (num : Prims.pos) (den : Prims.pos) (k : Prims.int) :
  Prims.bool=
  if k >= Prims.int_zero
  then num >= (mul_pos den (pow2 k))
  else (mul_pos num (pow2 (- k))) >= den
let floor_log2_ratio (num : Prims.pos) (den : Prims.pos) : Prims.int=
  let k0 = (bitlen num) - (bitlen den) in
  if geq_ratio num den k0 then k0 else k0 - Prims.int_one
let round_ties_even (n : Prims.nat) (d : Prims.pos) : Prims.nat=
  let q = n / d in
  let r = (mod) n d in
  let twice = (Prims.of_int (2)) * r in
  if twice < d
  then q
  else
    if twice > d
    then q + Prims.int_one
    else
      if ((mod) q (Prims.of_int (2))) = Prims.int_zero
      then q
      else q + Prims.int_one
type fclass =
  | FZero 
  | FInf 
  | FNaN 
  | FFinite of Prims.nat * Prims.int 
let uu___is_FZero (projectee : fclass) : Prims.bool=
  match projectee with | FZero -> true | uu___ -> false
let uu___is_FInf (projectee : fclass) : Prims.bool=
  match projectee with | FInf -> true | uu___ -> false
let uu___is_FNaN (projectee : fclass) : Prims.bool=
  match projectee with | FNaN -> true | uu___ -> false
let uu___is_FFinite (projectee : fclass) : Prims.bool=
  match projectee with | FFinite (mant, bexp) -> true | uu___ -> false
let __proj__FFinite__item__mant (projectee : fclass) : Prims.nat=
  match projectee with | FFinite (mant, bexp) -> mant
let __proj__FFinite__item__bexp (projectee : fclass) : Prims.int=
  match projectee with | FFinite (mant, bexp) -> bexp
type fval = {
  fsign: Prims.bool ;
  fcls: fclass }
let __proj__Mkfval__item__fsign (projectee : fval) : Prims.bool=
  match projectee with | { fsign; fcls;_} -> fsign
let __proj__Mkfval__item__fcls (projectee : fval) : fclass=
  match projectee with | { fsign; fcls;_} -> fcls
let fval_eq (a : fval) (b : fval) : Prims.bool=
  match ((a.fcls), (b.fcls)) with
  | (FNaN, uu___) -> false
  | (uu___, FNaN) -> false
  | (FZero, FZero) -> a.fsign = b.fsign
  | (FInf, FInf) -> a.fsign = b.fsign
  | (FFinite (s1, e1), FFinite (s2, e2)) ->
      ((a.fsign = b.fsign) && (s1 = s2)) && (e1 = e2)
  | (uu___, uu___1) -> false
let round_rational (p : Prims.pos) (emin : Prims.int) (emax : Prims.int)
  (num : Prims.pos) (den : Prims.pos) : fclass=
  let e_norm = floor_log2_ratio num den in
  let e_denorm = emin - (p - Prims.int_one) in
  let e_max_normal = emax - (p - Prims.int_one) in
  let e_tent = e_norm - (p - Prims.int_one) in
  if e_tent > e_max_normal
  then FInf
  else
    (let e = if e_tent < e_denorm then e_denorm else e_tent in
     let bigN = if e >= Prims.int_zero then num else mul_pos num (pow2 (- e)) in
     let bigD = if e >= Prims.int_zero then mul_pos den (pow2 e) else den in
     let s0 = round_ties_even bigN bigD in
     if s0 = Prims.int_zero
     then FZero
     else
       (let twop = pow2 p in
        let s = if s0 >= twop then s0 / (Prims.of_int (2)) else s0 in
        let e2 = if s0 >= twop then e + Prims.int_one else e in
        if e2 > e_max_normal then FInf else FFinite (s, e2)))
let is_digit (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let all_digits (cs : FStar_Char.char Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all is_digit cs
let rec digits_to_nat (acc : Prims.nat) (cs : FStar_Char.char Prims.list) :
  Prims.nat=
  match cs with
  | [] -> acc
  | c::rest ->
      let raw = (FStar_Char.int_of_char c) - (Prims.of_int (48)) in
      let d =
        if raw < Prims.int_zero
        then Prims.int_zero
        else if raw > (Prims.of_int (9)) then Prims.int_zero else raw in
      digits_to_nat ((acc * (Prims.of_int (10))) + d) rest
let rec split_at_code (code : Prims.int) (cs : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ([], FStar_Pervasives_Native.None)
  | c::rest ->
      if (FStar_Char.int_of_char c) = code
      then ([], (FStar_Pervasives_Native.Some rest))
      else
        (let uu___1 = split_at_code code rest in
         match uu___1 with | (before, after) -> ((c :: before), after))
let parse_signed_int (cs : FStar_Char.char Prims.list) :
  Prims.int FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | c::rest ->
      let ci = FStar_Char.int_of_char c in
      let uu___ =
        if ci = (Prims.of_int (43))
        then (false, rest)
        else if ci = (Prims.of_int (45)) then (true, rest) else (false, cs) in
      (match uu___ with
       | (neg, digits) ->
           if (Prims.uu___is_Cons digits) && (all_digits digits)
           then
             let v = digits_to_nat Prims.int_zero digits in
             FStar_Pervasives_Native.Some ((if neg then - v else v))
           else FStar_Pervasives_Native.None)
type parsed =
  | PNum of Prims.bool * Prims.nat * Prims.int 
  | PInf of Prims.bool 
  | PNaN 
let uu___is_PNum (projectee : parsed) : Prims.bool=
  match projectee with | PNum (neg, m, e) -> true | uu___ -> false
let __proj__PNum__item__neg (projectee : parsed) : Prims.bool=
  match projectee with | PNum (neg, m, e) -> neg
let __proj__PNum__item__m (projectee : parsed) : Prims.nat=
  match projectee with | PNum (neg, m, e) -> m
let __proj__PNum__item__e (projectee : parsed) : Prims.int=
  match projectee with | PNum (neg, m, e) -> e
let uu___is_PInf (projectee : parsed) : Prims.bool=
  match projectee with | PInf neg -> true | uu___ -> false
let __proj__PInf__item__neg (projectee : parsed) : Prims.bool=
  match projectee with | PInf neg -> neg
let uu___is_PNaN (projectee : parsed) : Prims.bool=
  match projectee with | PNaN -> true | uu___ -> false
let parse_decimal (neg : Prims.bool) (chars : FStar_Char.char Prims.list) :
  parsed FStar_Pervasives_Native.option=
  let uu___ = split_at_code (Prims.of_int (101)) chars in
  match uu___ with
  | (mant, exp_opt) ->
      let uu___1 =
        if FStar_Pervasives_Native.uu___is_Some exp_opt
        then (mant, exp_opt)
        else split_at_code (Prims.of_int (69)) chars in
      (match uu___1 with
       | (mant1, exp_opt1) ->
           let exp_res =
             match exp_opt1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some Prims.int_zero
             | FStar_Pervasives_Native.Some ec -> parse_signed_int ec in
           (match exp_res with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some exp_val ->
                let uu___2 = split_at_code (Prims.of_int (46)) mant1 in
                (match uu___2 with
                 | (ipart, fopt) ->
                     let fpart =
                       match fopt with
                       | FStar_Pervasives_Native.None -> []
                       | FStar_Pervasives_Native.Some f -> f in
                     if
                       ((all_digits ipart) && (all_digits fpart)) &&
                         (((FStar_List_Tot_Base.length ipart) +
                             (FStar_List_Tot_Base.length fpart))
                            >= Prims.int_one)
                     then
                       let m =
                         digits_to_nat Prims.int_zero
                           (FStar_List_Tot_Base.op_At ipart fpart) in
                       let e = exp_val - (FStar_List_Tot_Base.length fpart) in
                       FStar_Pervasives_Native.Some (PNum (neg, m, e))
                     else FStar_Pervasives_Native.None)))
let parse_lexical (s : Prims.string) : parsed FStar_Pervasives_Native.option=
  if s = "NaN"
  then FStar_Pervasives_Native.Some PNaN
  else
    if (s = "INF") || (s = "+INF")
    then FStar_Pervasives_Native.Some (PInf false)
    else
      if s = "-INF"
      then FStar_Pervasives_Native.Some (PInf true)
      else
        (let chars = FStar_String.list_of_string s in
         match chars with
         | [] -> FStar_Pervasives_Native.None
         | c::rest ->
             let ci = FStar_Char.int_of_char c in
             if ci = (Prims.of_int (43))
             then parse_decimal false rest
             else
               if ci = (Prims.of_int (45))
               then parse_decimal true rest
               else parse_decimal false chars)
let canon (p : Prims.pos) (emin : Prims.int) (emax : Prims.int) (pv : parsed)
  : fval=
  match pv with
  | PNaN -> { fsign = false; fcls = FNaN }
  | PInf neg -> { fsign = neg; fcls = FInf }
  | PNum (neg, m, e) ->
      if m = Prims.int_zero
      then { fsign = neg; fcls = FZero }
      else
        (let mp = m in
         let num = if e >= Prims.int_zero then mul_pos mp (pow10 e) else mp in
         let den = if e >= Prims.int_zero then Prims.int_one else pow10 (- e) in
         { fsign = neg; fcls = (round_rational p emin emax num den) })
let canon_double (pv : parsed) : fval=
  canon (Prims.of_int (53)) (Prims.of_int (-1022)) (Prims.of_int (1023)) pv
let canon_float (pv : parsed) : fval=
  let d64 = canon_double pv in
  match d64.fcls with
  | FNaN -> { fsign = (d64.fsign); fcls = FNaN }
  | FZero -> { fsign = (d64.fsign); fcls = FZero }
  | FInf -> { fsign = (d64.fsign); fcls = FInf }
  | FFinite (s, e) ->
      let sp = if s = Prims.int_zero then Prims.int_one else s in
      let num2 = if e >= Prims.int_zero then mul_pos sp (pow2 e) else sp in
      let den2 = if e >= Prims.int_zero then Prims.int_one else pow2 (- e) in
      {
        fsign = (d64.fsign);
        fcls =
          (round_rational (Prims.of_int (24)) (Prims.of_int (-126))
             (Prims.of_int (127)) num2 den2)
      }
let double_value_eq (a : Prims.string) (b : Prims.string) : Prims.bool=
  match ((parse_lexical a), (parse_lexical b)) with
  | (FStar_Pervasives_Native.Some pa, FStar_Pervasives_Native.Some pb) ->
      fval_eq (canon_double pa) (canon_double pb)
  | (uu___, uu___1) -> a = b
let float_value_eq (a : Prims.string) (b : Prims.string) : Prims.bool=
  match ((parse_lexical a), (parse_lexical b)) with
  | (FStar_Pervasives_Native.Some pa, FStar_Pervasives_Native.Some pb) ->
      fval_eq (canon_float pa) (canon_float pb)
  | (uu___, uu___1) -> a = b
let json_number_eq (a : Prims.string) (b : Prims.string) : Prims.bool=
  double_value_eq a b
