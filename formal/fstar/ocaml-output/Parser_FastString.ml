open Prims

let fs_cp_at_impl (s : Prims.string) (pos : Prims.nat) : Stdlib.Int.t * Stdlib.Int.t =
  let open Stdlib in
  let p = Z.to_int pos in
  let slen = String.length s in
  if p < 0 || p >= slen then (0xFFFD, 1)
  else
    let b0 = Char.code (String.unsafe_get s p) in
    if b0 < 0x80 then (b0, 1)
    else if b0 < 0xC2 then (0xFFFD, 1)
    else if b0 < 0xE0 then begin
      if p + 1 >= slen then (0xFFFD, 1)
      else
        let b1 = Char.code (String.unsafe_get s (p + 1)) in
        if (b1 land 0xC0) <> 0x80 then (0xFFFD, 1)
        else
          let cp = ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F) in
          (cp, 2)
    end
    else if b0 < 0xF0 then begin
      if p + 2 >= slen then (0xFFFD, 1)
      else
        let b1 = Char.code (String.unsafe_get s (p + 1)) in
        let b2 = Char.code (String.unsafe_get s (p + 2)) in
        if (b1 land 0xC0) <> 0x80 || (b2 land 0xC0) <> 0x80 then (0xFFFD, 1)
        else
          let cp = ((b0 land 0x0F) lsl 12) lor
                   ((b1 land 0x3F) lsl 6) lor
                   (b2 land 0x3F) in
          (* Reject overlong (< 0x800) and UTF-16 surrogates. *)
          if cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF) then (0xFFFD, 1)
          else (cp, 3)
    end
    else if b0 < 0xF5 then begin
      if p + 3 >= slen then (0xFFFD, 1)
      else
        let b1 = Char.code (String.unsafe_get s (p + 1)) in
        let b2 = Char.code (String.unsafe_get s (p + 2)) in
        let b3 = Char.code (String.unsafe_get s (p + 3)) in
        if (b1 land 0xC0) <> 0x80 || (b2 land 0xC0) <> 0x80 ||
           (b3 land 0xC0) <> 0x80 then (0xFFFD, 1)
        else
          let cp = ((b0 land 0x07) lsl 18) lor
                   ((b1 land 0x3F) lsl 12) lor
                   ((b2 land 0x3F) lsl 6) lor
                   (b3 land 0x3F) in
          if cp < 0x10000 || cp > 0x10FFFF then (0xFFFD, 1)
          else (cp, 4)
    end
    else (0xFFFD, 1)
let fs_byte_length (s : Prims.string) : Prims.nat=
  Z.of_int (String.length s)
let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=
  Z.of_int (Char.code (String.unsafe_get s (Z.to_int i)))
let fs_byte_sub (s : Prims.string) (start : Prims.nat) (len : Prims.nat) :
  Prims.string=
  let open Stdlib in
  let slen = String.length s in
  let i = Z.to_int start in
  let n = Z.to_int len in
  if i < 0 || n < 0 || i > slen then ""
  else
    let m = if i + n > slen then slen - i else n in
    String.sub s i m
let fs_find_byte (s : Prims.string) (b : Prims.nat) (start : Prims.nat) :
  Prims.nat=
  let open Stdlib in
  let slen = String.length s in
  let bi = Z.to_int b in
  let si = Z.to_int start in
  let rec loop i =
    if i >= slen then Z.of_int slen
    else if Char.code (String.unsafe_get s i) = bi then Z.of_int i
    else loop (i + 1)
  in
  loop (if si < 0 then 0 else si)
let fs_cp_at (s : Prims.string) (pos : Prims.nat) : (Prims.nat * Prims.nat)=
  let (cp, adv) = fs_cp_at_impl s pos in
  (Z.of_int cp, Z.of_int adv)
let fs_cp_len (s : Prims.string) (pos : Prims.nat) : Prims.nat=
  let (_, adv) = fs_cp_at_impl s pos in
  Z.of_int adv
let fs_byte_index (s : Prims.string) (i : Prims.nat) : FStar_Char.char=
  let b = fs_byte_at s i in
  if b < (Prims.of_int (0xD800))
  then FStar_Char.char_of_int b
  else FStar_Char.char_of_int Prims.int_zero
let fs_char_at (s : Prims.string) (i : Prims.nat) : FStar_Char.char=
  fs_byte_index s i
