open Prims
type row_cap = {
  max_rows: Prims.nat }
let (__proj__Mkrow_cap__item__max_rows : row_cap -> Prims.nat) =
  fun projectee -> match projectee with | { max_rows;_} -> max_rows
let (no_cap : row_cap) = { max_rows = Prims.int_zero }
let (mk_cap : Prims.nat -> row_cap) = fun n -> { max_rows = n }
let (is_enabled : row_cap -> Prims.bool) =
  fun c -> c.max_rows <> Prims.int_zero
let (cap_reached : row_cap -> Prims.nat -> Prims.bool) =
  fun c -> fun n_rows -> (is_enabled c) && (n_rows >= c.max_rows)
let rec take_capped_aux :
  'a . row_cap -> 'a Prims.list -> Prims.nat -> 'a Prims.list =
  fun c ->
    fun rows ->
      fun taken_so_far ->
        match rows with
        | [] -> []
        | x::rest ->
            if (is_enabled c) && (taken_so_far >= c.max_rows)
            then []
            else x :: (take_capped_aux c rest (taken_so_far + Prims.int_one))
let take_capped : 'a . row_cap -> 'a Prims.list -> 'a Prims.list =
  fun c -> fun rows -> take_capped_aux c rows Prims.int_zero
