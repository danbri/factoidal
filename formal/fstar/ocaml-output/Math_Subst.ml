open Prims
let rec subst (x : Prims.string) (v : Math_Expr.expr) (e : Math_Expr.expr) :
  Math_Expr.expr=
  match e with
  | Math_Expr.E_Int uu___ -> e
  | Math_Expr.E_Rat (uu___, uu___1) -> e
  | Math_Expr.E_Bool uu___ -> e
  | Math_Expr.E_Sym name -> if name = x then v else e
  | Math_Expr.E_App (fn, args) -> Math_Expr.E_App (fn, (subst_list x v args))
and subst_list (x : Prims.string) (v : Math_Expr.expr)
  (es : Math_Expr.expr Prims.list) : Math_Expr.expr Prims.list=
  match es with | [] -> [] | h::t -> (subst x v h) :: (subst_list x v t)
