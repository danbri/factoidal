open Prims
type node = Prims.string
type edge = (node * node)
let edge_closed (acc : node Prims.list) (e : edge) : Prims.bool=
  let uu___ = e in
  match uu___ with
  | (s, d) ->
      (Prims.op_Negation (FStar_List_Tot_Base.mem s acc)) ||
        (FStar_List_Tot_Base.mem d acc)
let is_closed (edges : edge Prims.list) (acc : node Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all (edge_closed acc) edges
let all_mem (xs : node Prims.list) (acc : node Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all (fun x -> FStar_List_Tot_Base.mem x acc) xs
let step_edge (acc : node Prims.list) (e : edge) : node Prims.list=
  let uu___ = e in
  match uu___ with
  | (s, d) ->
      if
        (FStar_List_Tot_Base.mem s acc) &&
          (Prims.op_Negation (FStar_List_Tot_Base.mem d acc))
      then d :: acc
      else acc
let step (edges : edge Prims.list) (acc : node Prims.list) : node Prims.list=
  FStar_List_Tot_Base.fold_left step_edge acc edges
let rec closure_fuel (edges : edge Prims.list) (acc : node Prims.list)
  (fuel : Prims.nat) : node Prims.list=
  if fuel = Prims.int_zero
  then acc
  else
    (let acc' = step edges acc in
     if (FStar_List_Tot_Base.length acc') = (FStar_List_Tot_Base.length acc)
     then acc
     else closure_fuel edges acc' (fuel - Prims.int_one))
let reachable (edges : edge Prims.list) (roots : node Prims.list) :
  node Prims.list=
  closure_fuel edges roots
    ((FStar_List_Tot_Base.length edges) + Prims.int_one)
type ('edges, 'dummyV0, 'dummyV1) reaches =
  | RRefl of node 
  | RStep of node * node * node * ('edges, Obj.t, Obj.t) reaches * unit 
let uu___is_RRefl (edges : edge Prims.list) (uu___ : node) (uu___1 : node)
  (projectee : (Obj.t, Obj.t, Obj.t) reaches) : Prims.bool=
  match projectee with | RRefl n -> true | uu___2 -> false
let __proj__RRefl__item__n (edges : edge Prims.list) (uu___ : node)
  (uu___1 : node) (projectee : (Obj.t, Obj.t, Obj.t) reaches) : node=
  match projectee with | RRefl n -> n
let uu___is_RStep (edges : edge Prims.list) (uu___ : node) (uu___1 : node)
  (projectee : (Obj.t, Obj.t, Obj.t) reaches) : Prims.bool=
  match projectee with | RStep (a, b, c, _3, _4) -> true | uu___2 -> false
let __proj__RStep__item__a (edges : edge Prims.list) (uu___ : node)
  (uu___1 : node) (projectee : (Obj.t, Obj.t, Obj.t) reaches) : node=
  match projectee with | RStep (a, b, c, _3, _4) -> a
let __proj__RStep__item__b (edges : edge Prims.list) (uu___ : node)
  (uu___1 : node) (projectee : (Obj.t, Obj.t, Obj.t) reaches) : node=
  match projectee with | RStep (a, b, c, _3, _4) -> b
let __proj__RStep__item__c (edges : edge Prims.list) (uu___ : node)
  (uu___1 : node) (projectee : (Obj.t, Obj.t, Obj.t) reaches) : node=
  match projectee with | RStep (a, b, c, _3, _4) -> c
let __proj__RStep__item___3 (edges : edge Prims.list) (uu___ : node)
  (uu___1 : node) (projectee : (Obj.t, Obj.t, Obj.t) reaches) :
  (Obj.t, Obj.t, Obj.t) reaches=
  match projectee with | RStep (a, b, c, _3, _4) -> _3
