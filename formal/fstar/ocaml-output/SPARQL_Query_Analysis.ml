open Prims
let rec collect_bgps_aux (acc : SPARQL11_Algebra.bgp Prims.list)
  (p : SPARQL11_Algebra.group_graph_pattern) :
  SPARQL11_Algebra.bgp Prims.list=
  match p with
  | SPARQL11_Algebra.GP_BGP tps ->
      if Prims.uu___is_Cons tps then tps :: acc else acc
  | SPARQL11_Algebra.GP_Join (p1, p2) ->
      collect_bgps_aux (collect_bgps_aux acc p1) p2
  | SPARQL11_Algebra.GP_LeftJoin (p1, p2, uu___) ->
      collect_bgps_aux (collect_bgps_aux acc p1) p2
  | SPARQL11_Algebra.GP_Union (p1, p2) ->
      collect_bgps_aux (collect_bgps_aux acc p1) p2
  | SPARQL11_Algebra.GP_Minus (p1, p2) ->
      collect_bgps_aux (collect_bgps_aux acc p1) p2
  | SPARQL11_Algebra.GP_Lateral (p1, p2) ->
      collect_bgps_aux (collect_bgps_aux acc p1) p2
  | SPARQL11_Algebra.GP_Filter (uu___, p1) -> collect_bgps_aux acc p1
  | SPARQL11_Algebra.GP_Graph (uu___, p1) -> collect_bgps_aux acc p1
  | SPARQL11_Algebra.GP_Bind (uu___, uu___1, p1) -> collect_bgps_aux acc p1
  | SPARQL11_Algebra.GP_Service (uu___, p1, uu___1) ->
      collect_bgps_aux acc p1
  | SPARQL11_Algebra.GP_ServiceVar (uu___, p1, uu___1) ->
      collect_bgps_aux acc p1
  | SPARQL11_Algebra.GP_SubSelect uu___ -> acc
  | SPARQL11_Algebra.GP_Values (uu___, uu___1) -> acc
  | SPARQL11_Algebra.GP_PropertyPath (uu___, uu___1, uu___2) -> acc
  | SPARQL11_Algebra.GP_Empty -> acc
let bgps_in_query (q : SPARQL11_Algebra.query) :
  SPARQL11_Algebra.bgp Prims.list=
  FStar_List_Tot_Base.rev (collect_bgps_aux [] q.SPARQL11_Algebra.q_pattern)
