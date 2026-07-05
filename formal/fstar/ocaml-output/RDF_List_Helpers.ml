open Prims
let rec append_aux :
  'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun acc xs ys ->
    match xs with
    | [] -> FStar_List_Tot_Base.rev_acc acc ys
    | x::rest -> append_aux (x :: acc) rest ys
let append_tr (xs : 'a Prims.list) (ys : 'a Prims.list) : 'a Prims.list=
  append_aux [] xs ys
let rec concatMap_aux :
  'a 'b .
    ('a -> 'b Prims.list) -> 'a Prims.list -> 'b Prims.list -> 'b Prims.list
  =
  fun f xs acc ->
    match xs with
    | [] -> FStar_List_Tot_Base.rev acc
    | x::rest -> concatMap_aux f rest (FStar_List_Tot_Base.rev_acc (f x) acc)
let concatMap_tr (f : 'a -> 'b Prims.list) (xs : 'a Prims.list) :
  'b Prims.list= concatMap_aux f xs []
let rec assoc_tr :
  'a 'b . 'a -> ('a * 'b) Prims.list -> 'b FStar_Pervasives_Native.option =
  fun x xs ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | (k, v)::rest ->
        if x = k then FStar_Pervasives_Native.Some v else assoc_tr x rest
