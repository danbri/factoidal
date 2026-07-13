open Prims
let series_count (lo : Prims.int) (hi : Prims.int) : Prims.nat=
  if hi < lo then Prims.int_zero else (hi - lo) + Prims.int_one
let rec series_terms_fuel (body : Math_Expr.expr) (idx : Prims.string)
  (lo : Prims.int) (fuel : Prims.nat) : Math_Expr.expr Prims.list=
  if fuel = Prims.int_zero
  then []
  else (Math_Subst.subst idx (Math_Expr.E_Int lo) body) ::
    (series_terms_fuel body idx (lo + Prims.int_one) (fuel - Prims.int_one))
let series_range_terms (body : Math_Expr.expr) (idx : Prims.string)
  (lo : Prims.int) (hi : Prims.int) : Math_Expr.expr Prims.list=
  series_terms_fuel body idx lo (series_count lo hi)
let summation (body : Math_Expr.expr) (idx : Prims.string) (lo : Prims.int)
  (hi : Prims.int) : Math_Expr.expr=
  Math_Simplify.simplify
    (Math_Expr.E_App ("plus", (series_range_terms body idx lo hi)))
let finite_product (body : Math_Expr.expr) (idx : Prims.string)
  (lo : Prims.int) (hi : Prims.int) : Math_Expr.expr=
  Math_Simplify.simplify
    (Math_Expr.E_App ("times", (series_range_terms body idx lo hi)))
