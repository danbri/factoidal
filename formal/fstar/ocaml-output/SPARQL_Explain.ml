open Prims
type bound_status =
  | BS_Var of Prims.string 
  | BS_Hit of Prims.string 
  | BS_Miss of Prims.string 
  | BS_Other of Prims.string 
let (uu___is_BS_Var : bound_status -> Prims.bool) =
  fun projectee -> match projectee with | BS_Var _0 -> true | uu___ -> false
let (__proj__BS_Var__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Var _0 -> _0
let (uu___is_BS_Hit : bound_status -> Prims.bool) =
  fun projectee -> match projectee with | BS_Hit _0 -> true | uu___ -> false
let (__proj__BS_Hit__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Hit _0 -> _0
let (uu___is_BS_Miss : bound_status -> Prims.bool) =
  fun projectee -> match projectee with | BS_Miss _0 -> true | uu___ -> false
let (__proj__BS_Miss__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Miss _0 -> _0
let (uu___is_BS_Other : bound_status -> Prims.bool) =
  fun projectee ->
    match projectee with | BS_Other _0 -> true | uu___ -> false
let (__proj__BS_Other__item___0 : bound_status -> Prims.string) =
  fun projectee -> match projectee with | BS_Other _0 -> _0
let (bs_string : bound_status -> Prims.string) =
  fun b ->
    match b with
    | BS_Var v -> Prims.strcat "?" (Prims.strcat v " (free)")
    | BS_Hit s -> Prims.strcat s " [hit]"
    | BS_Miss s ->
        Prims.strcat s
          " [MISS \226\128\148 term not in dictionary; result definitely empty]"
    | BS_Other s -> Prims.strcat s " [non-encodable]"
