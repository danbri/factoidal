open Prims
type mvalue =
  | MV_Rat of Prims.int * Prims.int 
  | MV_Bool of Prims.bool 
  | MV_Undef of Prims.string 
let uu___is_MV_Rat (projectee : mvalue) : Prims.bool=
  match projectee with | MV_Rat (num, den) -> true | uu___ -> false
let __proj__MV_Rat__item__num (projectee : mvalue) : Prims.int=
  match projectee with | MV_Rat (num, den) -> num
let __proj__MV_Rat__item__den (projectee : mvalue) : Prims.int=
  match projectee with | MV_Rat (num, den) -> den
let uu___is_MV_Bool (projectee : mvalue) : Prims.bool=
  match projectee with | MV_Bool b -> true | uu___ -> false
let __proj__MV_Bool__item__b (projectee : mvalue) : Prims.bool=
  match projectee with | MV_Bool b -> b
let uu___is_MV_Undef (projectee : mvalue) : Prims.bool=
  match projectee with | MV_Undef reason -> true | uu___ -> false
let __proj__MV_Undef__item__reason (projectee : mvalue) : Prims.string=
  match projectee with | MV_Undef reason -> reason
let iabs (n : Prims.int) : Prims.nat=
  if n < Prims.int_zero then Prims.int_zero - n else n
let rec ipow (base : Prims.int) (e : Prims.nat) : Prims.int=
  if e = Prims.int_zero
  then Prims.int_one
  else base * (ipow base (e - Prims.int_one))
let rec pow10 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec nat_gcd (a : Prims.nat) (b : Prims.nat) : Prims.nat=
  if b = Prims.int_zero then a else nat_gcd b ((mod) a b)
let rec ifact (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else n * (ifact (n - Prims.int_one))
let mk_rat (n : Prims.int) (d : Prims.int) : mvalue=
  if d = Prims.int_zero
  then MV_Undef "division-by-zero"
  else
    (let sgn =
       if d < Prims.int_zero then (Prims.of_int (-1)) else Prims.int_one in
     let n' = sgn * n in
     let d' = sgn * d in
     let g0 = nat_gcd (iabs n') (iabs d') in
     let g = if g0 = Prims.int_zero then Prims.int_one else g0 in
     MV_Rat ((n' / g), (d' / g)))
let is_rat (v : mvalue) : Prims.bool= uu___is_MV_Rat v
let rat_bin (f : Prims.int -> Prims.int -> Prims.int -> Prims.int -> mvalue)
  (a : mvalue) (b : mvalue) : mvalue=
  match (a, b) with
  | (MV_Undef r, uu___) -> MV_Undef r
  | (uu___, MV_Undef r) -> MV_Undef r
  | (MV_Rat (n1, d1), MV_Rat (n2, d2)) -> f n1 d1 n2 d2
  | uu___ -> MV_Undef "type-error-expected-number"
let m_add (a : mvalue) (b : mvalue) : mvalue=
  rat_bin (fun n1 d1 n2 d2 -> mk_rat ((n1 * d2) + (n2 * d1)) (d1 * d2)) a b
let m_sub (a : mvalue) (b : mvalue) : mvalue=
  rat_bin (fun n1 d1 n2 d2 -> mk_rat ((n1 * d2) - (n2 * d1)) (d1 * d2)) a b
let m_mul (a : mvalue) (b : mvalue) : mvalue=
  rat_bin (fun n1 d1 n2 d2 -> mk_rat (n1 * n2) (d1 * d2)) a b
let m_div (a : mvalue) (b : mvalue) : mvalue=
  rat_bin
    (fun n1 d1 n2 d2 ->
       if n2 = Prims.int_zero
       then MV_Undef "division-by-zero"
       else mk_rat (n1 * d2) (d1 * n2)) a b
let m_neg (a : mvalue) : mvalue=
  match a with
  | MV_Rat (n, d) -> MV_Rat ((Prims.int_zero - n), d)
  | MV_Undef r -> MV_Undef r
  | uu___ -> MV_Undef "type-error-expected-number"
let m_abs (a : mvalue) : mvalue=
  match a with
  | MV_Rat (n, d) -> MV_Rat ((iabs n), d)
  | MV_Undef r -> MV_Undef r
  | uu___ -> MV_Undef "type-error-expected-number"
let as_int (v : mvalue) : Prims.int FStar_Pervasives_Native.option=
  match v with
  | MV_Rat (n, uu___) when uu___ = Prims.int_one ->
      FStar_Pervasives_Native.Some n
  | uu___ -> FStar_Pervasives_Native.None
let m_pow (base : mvalue) (ex : mvalue) : mvalue=
  match (base, ex) with
  | (MV_Undef r, uu___) -> MV_Undef r
  | (uu___, MV_Undef r) -> MV_Undef r
  | (MV_Rat (p, q), uu___) ->
      (match as_int ex with
       | FStar_Pervasives_Native.None ->
           MV_Undef "non-integer-exponent-not-exact"
       | FStar_Pervasives_Native.Some e ->
           let ke = iabs e in
           let pk = ipow p ke in
           let qk = ipow q ke in
           if e >= Prims.int_zero
           then mk_rat pk qk
           else
             if p = Prims.int_zero
             then MV_Undef "zero-to-negative-power"
             else mk_rat qk pk)
  | uu___ -> MV_Undef "type-error-expected-number"
let rec find_int_root (m : Prims.nat) (k : Prims.nat) (r : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let p = ipow r k in
     if p = m
     then FStar_Pervasives_Native.Some r
     else
       if p > m
       then FStar_Pervasives_Native.None
       else find_int_root m k (r + Prims.int_one) (fuel - Prims.int_one))
let m_root (deg : mvalue) (arg : mvalue) : mvalue=
  match (deg, arg) with
  | (MV_Undef r, uu___) -> MV_Undef r
  | (uu___, MV_Undef r) -> MV_Undef r
  | (uu___, MV_Rat (p, q)) ->
      (match as_int deg with
       | FStar_Pervasives_Native.None -> MV_Undef "non-integer-root-degree"
       | FStar_Pervasives_Native.Some k ->
           if k <= Prims.int_zero
           then MV_Undef "nonpositive-root-degree"
           else
             (let kn = k in
              let neg = p < Prims.int_zero in
              if neg && (((mod) kn (Prims.of_int (2))) = Prims.int_zero)
              then MV_Undef "even-root-of-negative"
              else
                (let ap = iabs p in
                 let aq = iabs q in
                 match ((find_int_root ap kn Prims.int_zero
                           (ap + Prims.int_one)),
                         (find_int_root aq kn Prims.int_zero
                            (aq + Prims.int_one)))
                 with
                 | (FStar_Pervasives_Native.Some rp,
                    FStar_Pervasives_Native.Some rq) ->
                     let rp' = if neg then Prims.int_zero - rp else rp in
                     mk_rat rp' rq
                 | uu___3 -> MV_Undef "root-not-exact")))
  | uu___ -> MV_Undef "type-error-expected-number"
let m_quotient (a : mvalue) (b : mvalue) : mvalue=
  match ((as_int a), (as_int b), a, b) with
  | (uu___, uu___1, MV_Undef r, uu___2) -> MV_Undef r
  | (uu___, uu___1, uu___2, MV_Undef r) -> MV_Undef r
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y, uu___,
     uu___1) ->
      if y = Prims.int_zero
      then MV_Undef "division-by-zero"
      else MV_Rat ((x / y), Prims.int_one)
  | uu___ -> MV_Undef "quotient-requires-integers"
let m_rem (a : mvalue) (b : mvalue) : mvalue=
  match ((as_int a), (as_int b), a, b) with
  | (uu___, uu___1, MV_Undef r, uu___2) -> MV_Undef r
  | (uu___, uu___1, uu___2, MV_Undef r) -> MV_Undef r
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y, uu___,
     uu___1) ->
      if y = Prims.int_zero
      then MV_Undef "division-by-zero"
      else MV_Rat (((mod) x y), Prims.int_one)
  | uu___ -> MV_Undef "rem-requires-integers"
let m_factorial (a : mvalue) : mvalue=
  match a with
  | MV_Undef r -> MV_Undef r
  | uu___ ->
      (match as_int a with
       | FStar_Pervasives_Native.Some x ->
           if x < Prims.int_zero
           then MV_Undef "factorial-of-negative"
           else MV_Rat ((ifact x), Prims.int_one)
       | FStar_Pervasives_Native.None ->
           MV_Undef "factorial-requires-integer")
let m_gcd2 (a : mvalue) (b : mvalue) : mvalue=
  match ((as_int a), (as_int b), a, b) with
  | (uu___, uu___1, MV_Undef r, uu___2) -> MV_Undef r
  | (uu___, uu___1, uu___2, MV_Undef r) -> MV_Undef r
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y, uu___,
     uu___1) -> MV_Rat ((nat_gcd (iabs x) (iabs y)), Prims.int_one)
  | uu___ -> MV_Undef "gcd-requires-integers"
let rat_cmp (a : mvalue) (b : mvalue) :
  Prims.int FStar_Pervasives_Native.option=
  match (a, b) with
  | (MV_Rat (n1, d1), MV_Rat (n2, d2)) ->
      let lhs = n1 * d2 in
      let rhs = n2 * d1 in
      if lhs < rhs
      then FStar_Pervasives_Native.Some (Prims.of_int (-1))
      else
        if lhs = rhs
        then FStar_Pervasives_Native.Some Prims.int_zero
        else FStar_Pervasives_Native.Some Prims.int_one
  | uu___ -> FStar_Pervasives_Native.None
let m_max (a : mvalue) (b : mvalue) : mvalue=
  match rat_cmp a b with
  | FStar_Pervasives_Native.Some c -> if c < Prims.int_zero then b else a
  | FStar_Pervasives_Native.None ->
      (match (a, b) with
       | (MV_Undef r, uu___) -> MV_Undef r
       | (uu___, MV_Undef r) -> MV_Undef r
       | uu___ -> MV_Undef "type-error-expected-number")
let m_min (a : mvalue) (b : mvalue) : mvalue=
  match rat_cmp a b with
  | FStar_Pervasives_Native.Some c -> if c > Prims.int_zero then b else a
  | FStar_Pervasives_Native.None ->
      (match (a, b) with
       | (MV_Undef r, uu___) -> MV_Undef r
       | (uu___, MV_Undef r) -> MV_Undef r
       | uu___ -> MV_Undef "type-error-expected-number")
let is_ws_char (c : FStar_Char.char) : Prims.bool=
  (((c = 32) || (c = 9)) || (c = 10)) || (c = 13)
let rec drop_ws (l : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match l with | c::t -> if is_ws_char c then drop_ws t else l | [] -> []
let trim_chars (l : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  FStar_List_Tot_Base.rev (drop_ws (FStar_List_Tot_Base.rev (drop_ws l)))
let trim_str (s : Prims.string) : Prims.string=
  FStar_String.string_of_list (trim_chars (FStar_String.list_of_string s))
let is_digit_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (0x30))) && (n <= (Prims.of_int (0x39)))
let digit_val (c : FStar_Char.char) : Prims.int=
  (FStar_Char.int_of_char c) - (Prims.of_int (0x30))
let rec read_digits (l : FStar_Char.char Prims.list) (acc : Prims.int)
  (cnt : Prims.nat) : (Prims.int * Prims.nat * FStar_Char.char Prims.list)=
  match l with
  | c::rest ->
      if is_digit_char c
      then
        read_digits rest ((acc * (Prims.of_int (10))) + (digit_val c))
          (cnt + Prims.int_one)
      else (acc, cnt, l)
  | [] -> (acc, cnt, l)
let parse_decimal (s : Prims.string) : mvalue=
  let cs0 = trim_chars (FStar_String.list_of_string s) in
  match cs0 with
  | [] -> MV_Undef "empty-number"
  | uu___ ->
      let uu___1 =
        match cs0 with
        | 45::t -> (true, t)
        | 43::t -> (false, t)
        | uu___2 -> (false, cs0) in
      (match uu___1 with
       | (neg, cs1) ->
           let uu___2 = read_digits cs1 Prims.int_zero Prims.int_zero in
           (match uu___2 with
            | (ip, ipc, cs2) ->
                let uu___3 =
                  match cs2 with
                  | 46::t -> read_digits t Prims.int_zero Prims.int_zero
                  | uu___4 -> (Prims.int_zero, Prims.int_zero, cs2) in
                (match uu___3 with
                 | (fp, fpc, cs3) ->
                     if (ipc + fpc) = Prims.int_zero
                     then MV_Undef "not-a-number"
                     else
                       (let uu___5 =
                          match cs3 with
                          | 101::t ->
                              let uu___6 =
                                match t with
                                | 45::u -> ((Prims.of_int (-1)), u)
                                | 43::u -> (Prims.int_one, u)
                                | uu___7 -> (Prims.int_one, t) in
                              (match uu___6 with
                               | (esgn, t1) ->
                                   let uu___7 =
                                     read_digits t1 Prims.int_zero
                                       Prims.int_zero in
                                   (match uu___7 with
                                    | (ev, evc, t2) ->
                                        if evc = Prims.int_zero
                                        then (Prims.int_zero, cs3)
                                        else ((esgn * ev), t2)))
                          | 69::t ->
                              let uu___6 =
                                match t with
                                | 45::u -> ((Prims.of_int (-1)), u)
                                | 43::u -> (Prims.int_one, u)
                                | uu___7 -> (Prims.int_one, t) in
                              (match uu___6 with
                               | (esgn, t1) ->
                                   let uu___7 =
                                     read_digits t1 Prims.int_zero
                                       Prims.int_zero in
                                   (match uu___7 with
                                    | (ev, evc, t2) ->
                                        if evc = Prims.int_zero
                                        then (Prims.int_zero, cs3)
                                        else ((esgn * ev), t2)))
                          | uu___6 -> (Prims.int_zero, cs3) in
                        match uu___5 with
                        | (exp, cs4) ->
                            (match cs4 with
                             | [] ->
                                 let mant0 = (ip * (pow10 fpc)) + fp in
                                 let mant =
                                   if neg
                                   then Prims.int_zero - mant0
                                   else mant0 in
                                 let net = exp - fpc in
                                 if net >= Prims.int_zero
                                 then
                                   mk_rat (mant * (pow10 net)) Prims.int_one
                                 else
                                   mk_rat mant (pow10 (Prims.int_zero - net))
                             | uu___6 ->
                                 MV_Undef "trailing-garbage-in-number")))))
type expr =
  | E_Int of Prims.int 
  | E_Rat of Prims.int * Prims.int 
  | E_Bool of Prims.bool 
  | E_Sym of Prims.string 
  | E_App of Prims.string * expr Prims.list 
let uu___is_E_Int (projectee : expr) : Prims.bool=
  match projectee with | E_Int n -> true | uu___ -> false
let __proj__E_Int__item__n (projectee : expr) : Prims.int=
  match projectee with | E_Int n -> n
let uu___is_E_Rat (projectee : expr) : Prims.bool=
  match projectee with | E_Rat (num, den) -> true | uu___ -> false
let __proj__E_Rat__item__num (projectee : expr) : Prims.int=
  match projectee with | E_Rat (num, den) -> num
let __proj__E_Rat__item__den (projectee : expr) : Prims.int=
  match projectee with | E_Rat (num, den) -> den
let uu___is_E_Bool (projectee : expr) : Prims.bool=
  match projectee with | E_Bool b -> true | uu___ -> false
let __proj__E_Bool__item__b (projectee : expr) : Prims.bool=
  match projectee with | E_Bool b -> b
let uu___is_E_Sym (projectee : expr) : Prims.bool=
  match projectee with | E_Sym name -> true | uu___ -> false
let __proj__E_Sym__item__name (projectee : expr) : Prims.string=
  match projectee with | E_Sym name -> name
let uu___is_E_App (projectee : expr) : Prims.bool=
  match projectee with | E_App (fn, args) -> true | uu___ -> false
let __proj__E_App__item__fn (projectee : expr) : Prims.string=
  match projectee with | E_App (fn, args) -> fn
let __proj__E_App__item__args (projectee : expr) : expr Prims.list=
  match projectee with | E_App (fn, args) -> args
let e_add (a : expr) (b : expr) : expr= E_App ("plus", [a; b])
let e_mul (a : expr) (b : expr) : expr= E_App ("times", [a; b])
let e_pow (a : expr) (b : expr) : expr= E_App ("power", [a; b])
let e_neg (a : expr) : expr= E_App ("minus", [a])
let value_to_lit (v : mvalue) : expr=
  match v with
  | MV_Rat (n, uu___) when uu___ = Prims.int_one -> E_Int n
  | MV_Rat (n, d) -> E_Rat (n, d)
  | MV_Bool b -> E_Bool b
  | MV_Undef r -> E_App ("number-parse-error", [])
let rec fold_bin (f : mvalue -> mvalue -> mvalue) (acc : mvalue)
  (args : mvalue Prims.list) : mvalue=
  match args with | [] -> acc | a::rest -> fold_bin f (f acc a) rest
let rec relation_chain (ok : Prims.int -> Prims.bool)
  (args : mvalue Prims.list) : mvalue=
  match args with
  | [] -> MV_Bool true
  | uu___::[] -> MV_Bool true
  | a::b::rest ->
      (match rat_cmp a b with
       | FStar_Pervasives_Native.Some c ->
           if ok c then relation_chain ok (b :: rest) else MV_Bool false
       | FStar_Pervasives_Native.None ->
           (match (a, b) with
            | (MV_Undef r, uu___) -> MV_Undef r
            | (uu___, MV_Undef r) -> MV_Undef r
            | uu___ -> MV_Undef "type-error-in-relation"))
let apply_fn (fn : Prims.string) (args : mvalue Prims.list) : mvalue=
  match fn with
  | "plus" -> fold_bin m_add (MV_Rat (Prims.int_zero, Prims.int_one)) args
  | "times" -> fold_bin m_mul (MV_Rat (Prims.int_one, Prims.int_one)) args
  | "minus" ->
      (match args with
       | a::[] -> m_neg a
       | a::b::[] -> m_sub a b
       | uu___ -> MV_Undef "minus-arity")
  | "divide" ->
      (match args with
       | a::b::[] -> m_div a b
       | uu___ -> MV_Undef "divide-arity")
  | "power" ->
      (match args with
       | a::b::[] -> m_pow a b
       | uu___ -> MV_Undef "power-arity")
  | "root" ->
      (match args with
       | x::[] -> m_root (MV_Rat ((Prims.of_int (2)), Prims.int_one)) x
       | d::x::[] -> m_root d x
       | uu___ -> MV_Undef "root-arity")
  | "abs" ->
      (match args with | a::[] -> m_abs a | uu___ -> MV_Undef "abs-arity")
  | "quotient" ->
      (match args with
       | a::b::[] -> m_quotient a b
       | uu___ -> MV_Undef "quotient-arity")
  | "rem" ->
      (match args with
       | a::b::[] -> m_rem a b
       | uu___ -> MV_Undef "rem-arity")
  | "factorial" ->
      (match args with
       | a::[] -> m_factorial a
       | uu___ -> MV_Undef "factorial-arity")
  | "gcd" ->
      (match args with
       | [] -> MV_Rat (Prims.int_zero, Prims.int_one)
       | a::rest -> fold_bin m_gcd2 a rest)
  | "max" ->
      (match args with
       | [] -> MV_Undef "max-empty"
       | a::rest -> fold_bin m_max a rest)
  | "min" ->
      (match args with
       | [] -> MV_Undef "min-empty"
       | a::rest -> fold_bin m_min a rest)
  | "eq" -> relation_chain (fun c -> c = Prims.int_zero) args
  | "neq" ->
      (match args with
       | a::b::[] ->
           (match rat_cmp a b with
            | FStar_Pervasives_Native.Some c -> MV_Bool (c <> Prims.int_zero)
            | FStar_Pervasives_Native.None ->
                (match (a, b) with
                 | (MV_Undef r, uu___) -> MV_Undef r
                 | (uu___, MV_Undef r) -> MV_Undef r
                 | uu___ -> MV_Undef "type-error-in-relation"))
       | uu___ -> MV_Undef "neq-arity")
  | "lt" -> relation_chain (fun c -> c < Prims.int_zero) args
  | "gt" -> relation_chain (fun c -> c > Prims.int_zero) args
  | "leq" -> relation_chain (fun c -> c <= Prims.int_zero) args
  | "geq" -> relation_chain (fun c -> c >= Prims.int_zero) args
  | uu___ -> MV_Undef (FStar_String.concat "" ["unsupported-function:"; fn])
let rec eval (env : (Prims.string * mvalue) Prims.list) (e : expr)
  (fuel : Prims.nat) : mvalue=
  if fuel = Prims.int_zero
  then MV_Undef "fuel-exhausted"
  else
    (match e with
     | E_Int n -> MV_Rat (n, Prims.int_one)
     | E_Rat (n, d) -> mk_rat n d
     | E_Bool b -> MV_Bool b
     | E_Sym name ->
         (match FStar_List_Tot_Base.find
                  (fun kv -> (FStar_Pervasives_Native.fst kv) = name) env
          with
          | FStar_Pervasives_Native.Some (uu___1, v) -> v
          | FStar_Pervasives_Native.None ->
              MV_Undef (FStar_String.concat "" ["unbound-symbol:"; name]))
     | E_App (fn, args) ->
         let vals = eval_args env args (fuel - Prims.int_one) in
         apply_fn fn vals)
and eval_args (env : (Prims.string * mvalue) Prims.list)
  (es : expr Prims.list) (fuel : Prims.nat) : mvalue Prims.list=
  match es with
  | [] -> []
  | hd::tl -> (eval env hd fuel) :: (eval_args env tl fuel)
let eval_fuel : Prims.nat= (Prims.parse_int "100000")
let mk_env (pairs : (Prims.string * Prims.string) Prims.list) :
  (Prims.string * mvalue) Prims.list=
  FStar_List_Tot_Base.map
    (fun kv ->
       ((FStar_Pervasives_Native.fst kv),
         (parse_decimal (FStar_Pervasives_Native.snd kv)))) pairs
let eval_expr (env : (Prims.string * mvalue) Prims.list) (e : expr) : 
  mvalue= eval env e eval_fuel
let value_to_string (v : mvalue) : Prims.string=
  match v with
  | MV_Rat (n, uu___) when uu___ = Prims.int_one -> Prims.string_of_int n
  | MV_Rat (n, d) ->
      FStar_String.concat ""
        [Prims.string_of_int n; "/"; Prims.string_of_int d]
  | MV_Bool b -> if b then "true" else "false"
  | MV_Undef uu___ -> "undef"
let value_reason (v : mvalue) : Prims.string=
  match v with | MV_Undef r -> r | uu___ -> ""
