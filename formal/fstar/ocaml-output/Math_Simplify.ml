open Prims
let rec expr_key (e : Math_Expr.expr) : Prims.string=
  match e with
  | Math_Expr.E_Int n ->
      FStar_String.concat "" ["0i:"; Prims.string_of_int n]
  | Math_Expr.E_Rat (n, d) ->
      FStar_String.concat ""
        ["1r:"; Prims.string_of_int n; "/"; Prims.string_of_int d]
  | Math_Expr.E_Bool b ->
      FStar_String.concat "" ["2b:"; if b then "t" else "f"]
  | Math_Expr.E_Sym s -> FStar_String.concat "" ["3s:"; s]
  | Math_Expr.E_App (fn, args) ->
      FStar_String.concat "" ["4a:"; fn; "("; expr_key_list args; ")"]
and expr_key_list (es : Math_Expr.expr Prims.list) : Prims.string=
  match es with
  | [] -> ""
  | h::t -> FStar_String.concat "" [expr_key h; ","; expr_key_list t]
let rec charlist_cmp (a : FStar_Char.char Prims.list)
  (b : FStar_Char.char Prims.list) : Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (ca::ta, cb::tb) ->
      let na = FStar_Char.int_of_char ca in
      let nb = FStar_Char.int_of_char cb in
      if na < nb
      then (Prims.of_int (-1))
      else if na > nb then Prims.int_one else charlist_cmp ta tb
let str_cmp (a : Prims.string) (b : Prims.string) : Prims.int=
  charlist_cmp (FStar_String.list_of_string a)
    (FStar_String.list_of_string b)
let expr_cmp (a : Math_Expr.expr) (b : Math_Expr.expr) : Prims.int=
  str_cmp (expr_key a) (expr_key b)
let rec insert_sorted (x : Math_Expr.expr) (l : Math_Expr.expr Prims.list) :
  Math_Expr.expr Prims.list=
  match l with
  | [] -> [x]
  | h::t ->
      if (expr_cmp x h) <= Prims.int_zero
      then x :: l
      else h :: (insert_sorted x t)
let rec sort_exprs (l : Math_Expr.expr Prims.list) :
  Math_Expr.expr Prims.list=
  match l with | [] -> [] | h::t -> insert_sorted h (sort_exprs t)
let is_num_lit (e : Math_Expr.expr) : Prims.bool=
  match e with
  | Math_Expr.E_Int uu___ -> true
  | Math_Expr.E_Rat (uu___, uu___1) -> true
  | uu___ -> false
let lit_value (e : Math_Expr.expr) : Math_Expr.mvalue=
  match e with
  | Math_Expr.E_Int n -> Math_Expr.MV_Rat (n, Prims.int_one)
  | Math_Expr.E_Rat (n, d) -> Math_Expr.mk_rat n d
  | uu___ -> Math_Expr.MV_Undef "not-a-literal"
let is_zero_lit (e : Math_Expr.expr) : Prims.bool=
  match e with
  | Math_Expr.E_Int n -> n = Prims.int_zero
  | Math_Expr.E_Rat (n, uu___) -> n = Prims.int_zero
  | uu___ -> false
let rec flatten_op (fn : Prims.string) (args : Math_Expr.expr Prims.list) :
  Math_Expr.expr Prims.list=
  match args with
  | [] -> []
  | h::t ->
      let rest = flatten_op fn t in
      (match h with
       | Math_Expr.E_App (fn2, inner) ->
           if fn2 = fn
           then FStar_List_Tot_Base.append inner rest
           else h :: rest
       | uu___ -> h :: rest)
let base_exp (e : Math_Expr.expr) : (Math_Expr.expr * Prims.int)=
  match e with
  | Math_Expr.E_App ("power", b::(Math_Expr.E_Int n)::[]) -> (b, n)
  | uu___ -> (e, Prims.int_one)
let rec bump_exp (b : Math_Expr.expr) (n : Prims.int)
  (acc : (Math_Expr.expr * Prims.int) Prims.list) :
  (Math_Expr.expr * Prims.int) Prims.list=
  match acc with
  | [] -> [(b, n)]
  | (hb, hn)::rest ->
      if hb = b
      then (hb, (hn + n)) :: rest
      else (hb, hn) :: (bump_exp b n rest)
let rec combine_powers (l : (Math_Expr.expr * Prims.int) Prims.list)
  (acc : (Math_Expr.expr * Prims.int) Prims.list) :
  (Math_Expr.expr * Prims.int) Prims.list=
  match l with | [] -> acc | (b, n)::t -> combine_powers t (bump_exp b n acc)
let rec split_sum (args : Math_Expr.expr Prims.list)
  (constv : Math_Expr.mvalue) (terms : Math_Expr.expr Prims.list) :
  (Math_Expr.mvalue * Math_Expr.expr Prims.list)=
  match args with
  | [] -> (constv, terms)
  | h::t ->
      if is_num_lit h
      then split_sum t (Math_Expr.m_add constv (lit_value h)) terms
      else split_sum t constv (FStar_List_Tot_Base.append terms [h])
let rec split_prod (args : Math_Expr.expr Prims.list)
  (constv : Math_Expr.mvalue) (factors : Math_Expr.expr Prims.list) :
  (Math_Expr.mvalue * Math_Expr.expr Prims.list)=
  match args with
  | [] -> (constv, factors)
  | h::t ->
      if is_num_lit h
      then split_prod t (Math_Expr.m_mul constv (lit_value h)) factors
      else split_prod t constv (FStar_List_Tot_Base.append factors [h])
let split_coeff (e : Math_Expr.expr) :
  (Math_Expr.mvalue * Math_Expr.expr Prims.list)=
  match e with
  | Math_Expr.E_App ("times", factors) ->
      split_prod factors (Math_Expr.MV_Rat (Prims.int_one, Prims.int_one)) []
  | uu___ -> ((Math_Expr.MV_Rat (Prims.int_one, Prims.int_one)), [e])
let core_key (cf : Math_Expr.expr Prims.list) : Prims.string=
  match cf with
  | [] -> ""
  | f::[] -> expr_key f
  | uu___ -> expr_key (Math_Expr.E_App ("times", cf))
let rec bump_core (k : Prims.string) (cf : Math_Expr.expr Prims.list)
  (c : Math_Expr.mvalue)
  (acc :
    (Prims.string * Math_Expr.expr Prims.list * Math_Expr.mvalue) Prims.list)
  : (Prims.string * Math_Expr.expr Prims.list * Math_Expr.mvalue) Prims.list=
  match acc with
  | [] -> [(k, cf, c)]
  | (hk, hcf, hc)::rest ->
      if hk = k
      then (hk, hcf, (Math_Expr.m_add hc c)) :: rest
      else (hk, hcf, hc) :: (bump_core k cf c rest)
let rec collect_coeffs (terms : Math_Expr.expr Prims.list)
  (constv : Math_Expr.mvalue)
  (acc :
    (Prims.string * Math_Expr.expr Prims.list * Math_Expr.mvalue) Prims.list)
  :
  (Math_Expr.mvalue * (Prims.string * Math_Expr.expr Prims.list *
    Math_Expr.mvalue) Prims.list)=
  match terms with
  | [] -> (constv, acc)
  | t::rest ->
      let uu___ = split_coeff t in
      (match uu___ with
       | (c, cf) ->
           (match cf with
            | [] -> collect_coeffs rest (Math_Expr.m_add constv c) acc
            | uu___1 ->
                collect_coeffs rest constv (bump_core (core_key cf) cf c acc)))
let merged_term (cf : Math_Expr.expr Prims.list) (c : Math_Expr.mvalue) :
  Math_Expr.expr Prims.list=
  match c with
  | Math_Expr.MV_Rat (uu___, uu___1) when
      (uu___ = Prims.int_zero) && (uu___1 = Prims.int_one) -> []
  | Math_Expr.MV_Rat (uu___, uu___1) when
      (uu___ = Prims.int_one) && (uu___1 = Prims.int_one) ->
      [(match cf with | f::[] -> f | uu___2 -> Math_Expr.E_App ("times", cf))]
  | uu___ -> [Math_Expr.E_App ("times", ((Math_Expr.value_to_lit c) :: cf))]
let rec emit_merged
  (groups :
    (Prims.string * Math_Expr.expr Prims.list * Math_Expr.mvalue) Prims.list)
  : Math_Expr.expr Prims.list=
  match groups with
  | [] -> []
  | (uu___, cf, c)::rest ->
      FStar_List_Tot_Base.append (merged_term cf c) (emit_merged rest)
let rec emit_factors (pairs : (Math_Expr.expr * Prims.int) Prims.list) :
  Math_Expr.expr Prims.list=
  match pairs with
  | [] -> []
  | (b, n)::rest ->
      if n = Prims.int_zero
      then emit_factors rest
      else
        (let head =
           if n = Prims.int_one
           then b
           else Math_Expr.E_App ("power", [b; Math_Expr.E_Int n]) in
         head :: (emit_factors rest))
let simplify_plus (args : Math_Expr.expr Prims.list) : Math_Expr.expr=
  let flat = flatten_op "plus" args in
  let uu___ =
    split_sum flat (Math_Expr.MV_Rat (Prims.int_zero, Prims.int_one)) [] in
  match uu___ with
  | (constv0, terms) ->
      let uu___1 = collect_coeffs terms constv0 [] in
      (match uu___1 with
       | (constv, groups) ->
           let summands = sort_exprs (emit_merged groups) in
           let const_lit =
             match constv with
             | Math_Expr.MV_Rat (uu___2, uu___3) when
                 (uu___2 = Prims.int_zero) && (uu___3 = Prims.int_one) -> []
             | Math_Expr.MV_Undef uu___2 -> []
             | uu___2 -> [Math_Expr.value_to_lit constv] in
           let all = FStar_List_Tot_Base.append summands const_lit in
           (match all with
            | [] -> Math_Expr.E_Int Prims.int_zero
            | x::[] -> x
            | uu___2 -> Math_Expr.E_App ("plus", all)))
let simplify_times (args : Math_Expr.expr Prims.list) : Math_Expr.expr=
  let flat = flatten_op "times" args in
  if FStar_List_Tot_Base.existsb is_zero_lit flat
  then Math_Expr.E_Int Prims.int_zero
  else
    (let uu___1 =
       split_prod flat (Math_Expr.MV_Rat (Prims.int_one, Prims.int_one)) [] in
     match uu___1 with
     | (constv, factors) ->
         let pairs =
           combine_powers (FStar_List_Tot_Base.map base_exp factors) [] in
         let facs = sort_exprs (emit_factors pairs) in
         let const_lit =
           match constv with
           | Math_Expr.MV_Rat (uu___2, uu___3) when
               (uu___2 = Prims.int_one) && (uu___3 = Prims.int_one) -> []
           | Math_Expr.MV_Undef uu___2 -> []
           | uu___2 -> [Math_Expr.value_to_lit constv] in
         let all = FStar_List_Tot_Base.append const_lit facs in
         (match all with
          | [] -> Math_Expr.E_Int Prims.int_one
          | x::[] -> x
          | uu___2 -> Math_Expr.E_App ("times", all)))
let simplify_other (fn : Prims.string) (args : Math_Expr.expr Prims.list) :
  Math_Expr.expr=
  if FStar_List_Tot_Base.for_all is_num_lit args
  then
    let v = Math_Expr.apply_fn fn (FStar_List_Tot_Base.map lit_value args) in
    match v with
    | Math_Expr.MV_Undef uu___ -> Math_Expr.E_App (fn, args)
    | uu___ -> Math_Expr.value_to_lit v
  else
    (match (fn, args) with
     | ("power", a::(Math_Expr.E_Int uu___1)::[]) when uu___1 = Prims.int_one
         -> a
     | ("divide", a::(Math_Expr.E_Int uu___1)::[]) when
         uu___1 = Prims.int_one -> a
     | ("minus", a::(Math_Expr.E_Int uu___1)::[]) when
         uu___1 = Prims.int_zero -> a
     | uu___1 -> Math_Expr.E_App (fn, args))
let simplify_app (fn : Prims.string) (args : Math_Expr.expr Prims.list) :
  Math_Expr.expr=
  if fn = "plus"
  then simplify_plus args
  else if fn = "times" then simplify_times args else simplify_other fn args
let rec simplify (e : Math_Expr.expr) : Math_Expr.expr=
  match e with
  | Math_Expr.E_Int uu___ -> e
  | Math_Expr.E_Rat (uu___, uu___1) -> e
  | Math_Expr.E_Bool uu___ -> e
  | Math_Expr.E_Sym uu___ -> e
  | Math_Expr.E_App (fn, args) -> simplify_app fn (simplify_list args)
and simplify_list (es : Math_Expr.expr Prims.list) :
  Math_Expr.expr Prims.list=
  match es with | [] -> [] | h::t -> (simplify h) :: (simplify_list t)
