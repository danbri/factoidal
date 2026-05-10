open Prims
let sparql_protocol_paths : Prims.string Prims.list=
  ["/sparql"; "/query"; "/update"]
let rec mem_string (p : Prims.string) (xs : Prims.string Prims.list) :
  Prims.bool=
  match xs with
  | [] -> false
  | x::rest -> if p = x then true else mem_string p rest
let is_sparql_protocol_path (p : Prims.string) : Prims.bool=
  mem_string p sparql_protocol_paths
