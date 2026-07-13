open Prims
let diff_unknown (e : Math_Expr.expr) : Math_Expr.expr=
  Math_Expr.E_App ("diff_unsupported", [e])
let rec diff (x : Prims.string) (e : Math_Expr.expr) : Math_Expr.expr=
  match e with
  | Math_Expr.E_Int uu___ -> Math_Expr.E_Int Prims.int_zero
  | Math_Expr.E_Rat (uu___, uu___1) -> Math_Expr.E_Int Prims.int_zero
  | Math_Expr.E_Bool uu___ -> Math_Expr.E_Int Prims.int_zero
  | Math_Expr.E_Sym name ->
      if name = x
      then Math_Expr.E_Int Prims.int_one
      else Math_Expr.E_Int Prims.int_zero
  | Math_Expr.E_App ("plus", args) ->
      Math_Expr.E_App ("plus", (diff_list x args))
  | Math_Expr.E_App ("minus", args) ->
      (match args with
       | a::[] -> Math_Expr.e_neg (diff x a)
       | a::b::[] -> Math_Expr.E_App ("minus", [diff x a; diff x b])
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("times", args) ->
      Math_Expr.E_App ("plus", (diff_prod x [] args))
  | Math_Expr.E_App ("divide", args) ->
      (match args with
       | a::b::[] ->
           Math_Expr.E_App
             ("divide",
               [Math_Expr.E_App
                  ("minus",
                    [Math_Expr.e_mul (diff x a) b;
                    Math_Expr.e_mul a (diff x b)]);
               Math_Expr.e_pow b (Math_Expr.E_Int (Prims.of_int (2)))])
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("power", args) ->
      (match args with
       | a::b::[] ->
           (match b with
            | Math_Expr.E_Int n ->
                Math_Expr.e_mul
                  (Math_Expr.e_mul (Math_Expr.E_Int n)
                     (Math_Expr.e_pow a (Math_Expr.E_Int (n - Prims.int_one))))
                  (diff x a)
            | Math_Expr.E_Rat (p, q) ->
                Math_Expr.e_mul
                  (Math_Expr.e_mul (Math_Expr.E_Rat (p, q))
                     (Math_Expr.e_pow a (Math_Expr.E_Rat ((p - q), q))))
                  (diff x a)
            | uu___ ->
                let fg = Math_Expr.e_pow a b in
                Math_Expr.e_mul fg
                  (Math_Expr.e_add
                     (Math_Expr.e_mul (diff x b)
                        (Math_Expr.E_App ("ln", [a])))
                     (Math_Expr.e_mul b
                        (Math_Expr.E_App ("divide", [diff x a; a])))))
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("root", args) ->
      (match args with
       | a::[] ->
           Math_Expr.E_App
             ("divide",
               [diff x a;
               Math_Expr.e_mul (Math_Expr.E_Int (Prims.of_int (2)))
                 (Math_Expr.E_App ("root", [a]))])
       | (Math_Expr.E_Int k)::a::[] ->
           if k > Prims.int_zero
           then
             Math_Expr.e_mul
               (Math_Expr.e_mul (Math_Expr.E_Rat (Prims.int_one, k))
                  (Math_Expr.e_pow a
                     (Math_Expr.E_Rat ((Prims.int_one - k), k)))) (diff x a)
           else diff_unknown e
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("sin", args) ->
      (match args with
       | a::[] -> Math_Expr.e_mul (Math_Expr.E_App ("cos", [a])) (diff x a)
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("cos", args) ->
      (match args with
       | a::[] ->
           Math_Expr.e_mul (Math_Expr.e_neg (Math_Expr.E_App ("sin", [a])))
             (diff x a)
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("exp", args) ->
      (match args with
       | a::[] -> Math_Expr.e_mul (Math_Expr.E_App ("exp", [a])) (diff x a)
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("ln", args) ->
      (match args with
       | a::[] -> Math_Expr.E_App ("divide", [diff x a; a])
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App ("tan", args) ->
      (match args with
       | a::[] ->
           Math_Expr.E_App
             ("divide",
               [diff x a;
               Math_Expr.e_pow (Math_Expr.E_App ("cos", [a]))
                 (Math_Expr.E_Int (Prims.of_int (2)))])
       | uu___ -> diff_unknown e)
  | Math_Expr.E_App (uu___, uu___1) -> diff_unknown e
and diff_list (x : Prims.string) (es : Math_Expr.expr Prims.list) :
  Math_Expr.expr Prims.list=
  match es with | [] -> [] | h::t -> (diff x h) :: (diff_list x t)
and diff_prod (x : Prims.string) (pre : Math_Expr.expr Prims.list)
  (args : Math_Expr.expr Prims.list) : Math_Expr.expr Prims.list=
  match args with
  | [] -> []
  | a::rest ->
      let term =
        Math_Expr.E_App
          ("times", (FStar_List_Tot_Base.append pre ((diff x a) :: rest))) in
      term :: (diff_prod x (FStar_List_Tot_Base.append pre [a]) rest)
