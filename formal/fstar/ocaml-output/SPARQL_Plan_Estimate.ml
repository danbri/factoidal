open Prims
type estimate_count =
  | EC_Exact of Prims.nat 
  | EC_Approx of Prims.nat 
  | EC_Unknown 
let (uu___is_EC_Exact : estimate_count -> Prims.bool) =
  fun projectee ->
    match projectee with | EC_Exact _0 -> true | uu___ -> false
let (__proj__EC_Exact__item___0 : estimate_count -> Prims.nat) =
  fun projectee -> match projectee with | EC_Exact _0 -> _0
let (uu___is_EC_Approx : estimate_count -> Prims.bool) =
  fun projectee ->
    match projectee with | EC_Approx _0 -> true | uu___ -> false
let (__proj__EC_Approx__item___0 : estimate_count -> Prims.nat) =
  fun projectee -> match projectee with | EC_Approx _0 -> _0
let (uu___is_EC_Unknown : estimate_count -> Prims.bool) =
  fun projectee -> match projectee with | EC_Unknown -> true | uu___ -> false
let (estimate_count_value : estimate_count -> Prims.nat) =
  fun ec ->
    match ec with
    | EC_Exact n -> n
    | EC_Approx n -> n
    | EC_Unknown -> Prims.int_zero
let (estimate_count_is_exact : estimate_count -> Prims.bool) =
  fun ec -> match ec with | EC_Exact uu___ -> true | uu___ -> false
let (estimate_pattern_in_rgs :
  Prims.nat -> Prims.nat -> Prims.nat -> estimate_count) =
  fun n_candidates ->
    fun total_rgs ->
      fun total_rows ->
        if n_candidates = Prims.int_zero
        then EC_Exact Prims.int_zero
        else
          if total_rgs = Prims.int_zero
          then EC_Exact Prims.int_zero
          else
            if total_rows = Prims.int_zero
            then EC_Exact Prims.int_zero
            else
              (let avg_rows_per_rg = total_rows / total_rgs in
               let prod = n_candidates * avg_rows_per_rg in
               if prod < Prims.int_zero
               then EC_Approx Prims.int_zero
               else EC_Approx prod)
let (estimate_unbound_pattern : Prims.nat -> estimate_count) =
  fun total_rows -> EC_Exact total_rows
let rec (sum_nats : Prims.nat Prims.list -> Prims.nat) =
  fun xs -> match xs with | [] -> Prims.int_zero | x::tl -> x + (sum_nats tl)
let (estimate_aggregate : Prims.nat Prims.list -> estimate_count) =
  fun per_rg -> EC_Approx (sum_nats per_rg)
let (estimate_pattern_in_rgs_nat :
  Prims.nat -> Prims.nat -> Prims.nat -> Prims.nat) =
  fun n_candidates ->
    fun total_rgs ->
      fun total_rows ->
        estimate_count_value
          (estimate_pattern_in_rgs n_candidates total_rgs total_rows)
