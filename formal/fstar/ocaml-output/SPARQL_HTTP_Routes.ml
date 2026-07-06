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
let gsp_path_prefix : Prims.string= "/data"
let starts_with (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  let pl = FStar_String.strlen pfx in
  let sl = FStar_String.strlen s in
  if sl >= pl then (FStar_String.sub s Prims.int_zero pl) = pfx else false
let is_gsp_path (p : Prims.string) : Prims.bool=
  starts_with p gsp_path_prefix
