open Prims
type row_cap = {
  max_rows: Prims.nat }
let __proj__Mkrow_cap__item__max_rows (projectee : row_cap) : Prims.nat=
  match projectee with | { max_rows;_} -> max_rows
let no_cap : row_cap= { max_rows = Prims.int_zero }
let mk_cap (n : Prims.nat) : row_cap= { max_rows = n }
let is_enabled (c : row_cap) : Prims.bool= c.max_rows <> Prims.int_zero
let cap_reached (c : row_cap) (n_rows : Prims.nat) : Prims.bool=
  (is_enabled c) && (n_rows >= c.max_rows)
let rec take_capped_aux :
  'a . row_cap -> 'a Prims.list -> Prims.nat -> 'a Prims.list =
  fun c rows taken_so_far ->
    match rows with
    | [] -> []
    | x::rest ->
        if (is_enabled c) && (taken_so_far >= c.max_rows)
        then []
        else x :: (take_capped_aux c rest (taken_so_far + Prims.int_one))
let take_capped (c : row_cap) (rows : 'a Prims.list) : 'a Prims.list=
  take_capped_aux c rows Prims.int_zero
