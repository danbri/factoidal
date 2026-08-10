open Prims
let rec concat_spec (sep : Prims.string) (l : Prims.string Prims.list) :
  Prims.string=
  match l with
  | [] -> ""
  | x::[] -> x
  | x::rest -> Prims.strcat x (Prims.strcat sep (concat_spec sep rest))
