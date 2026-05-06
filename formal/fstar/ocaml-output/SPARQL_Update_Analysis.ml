open Prims
let (is_load_op : SPARQL11_Algebra.update_op -> Prims.bool) =
  fun op ->
    match op with
    | SPARQL11_Algebra.U_Load (uu___, uu___1, uu___2) -> true
    | uu___ -> false
let (update_has_load : SPARQL11_Algebra.sparql_update -> Prims.bool) =
  fun u -> FStar_List_Tot_Base.existsb is_load_op u.SPARQL11_Algebra.u_ops
