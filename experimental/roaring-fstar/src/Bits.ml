open Prims
let rec popcount_aux (n : FStar_UInt64.t) (i : Prims.nat) : Prims.nat=
  if i = Prims.int_zero
  then Prims.int_zero
  else
    (let bit = FStar_UInt64.rem n (Stdint.Uint64.of_int (2)) in
     let rest_count =
       popcount_aux (FStar_UInt64.div n (Stdint.Uint64.of_int (2)))
         (i - Prims.int_one) in
     (if FStar_UInt64.eq bit Stdint.Uint64.zero
      then Prims.int_zero
      else Prims.int_one) + rest_count)
let popcount_u64 (n : FStar_UInt64.t) : Prims.nat=
  popcount_aux n (Prims.of_int (64))
let rec tzcnt_aux (n : FStar_UInt64.t) (i : Prims.nat) : Prims.nat=
  if i = Prims.int_zero
  then Prims.int_zero
  else
    if
      FStar_UInt64.eq (FStar_UInt64.rem n (Stdint.Uint64.of_int (2)))
        Stdint.Uint64.one
    then Prims.int_zero
    else
      Prims.int_one +
        (tzcnt_aux (FStar_UInt64.div n (Stdint.Uint64.of_int (2)))
           (i - Prims.int_one))
let tzcnt_u64 (n : FStar_UInt64.t) : Prims.nat=
  tzcnt_aux n (Prims.of_int (64))
