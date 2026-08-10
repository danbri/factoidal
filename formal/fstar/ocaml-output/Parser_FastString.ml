open Prims

(* fs_cp_at_impl: parser-shared codepoint decoder, verbatim from the
 * pre-migration patch 89 (FastString re-founding Step 3, 2026-08-10). *)
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
  let open Stdlib in
  let ii = Z.to_int i in
  if ii < 0 || ii >= String.length s then Prims.int_zero
  else Z.of_int (Char.code (String.unsafe_get s ii))
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
let fs_byte_length_spec (s : Prims.string) : Prims.nat=
  FStar_List_Tot_Base.length (Parser_FastString_Spec.utf8_bytes s)
let fs_byte_at_spec (s : Prims.string) (i : Prims.nat) : Prims.nat=
  match Parser_FastString_Spec.nth_byte (Parser_FastString_Spec.utf8_bytes s)
          i
  with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None -> Prims.int_zero
let fs_byte_sub_spec (s : Prims.string) (start : Prims.nat) (len : Prims.nat)
  : Prims.string=
  FStar_String.string_of_list
    (Parser_FastString_Spec.utf8_decode_all
       (Parser_FastString_Spec.slice_bytes
          (Parser_FastString_Spec.utf8_bytes s) start len))
let fs_find_byte_spec (s : Prims.string) (b : Prims.nat) (start : Prims.nat)
  : Prims.nat=
  Parser_FastString_Spec.find_byte (Parser_FastString_Spec.utf8_bytes s) b
    start
let fs_cp_at_spec (s : Prims.string) (pos : Prims.nat) :
  (Prims.nat * Prims.nat)=
  let uu___ =
    Parser_FastString_Spec.utf8_decode_at
      (Parser_FastString_Spec.utf8_bytes s) pos in
  match uu___ with | (cp, adv) -> (cp, adv)
let fs_cp_len_spec (s : Prims.string) (pos : Prims.nat) : Prims.nat=
  let uu___ =
    Parser_FastString_Spec.utf8_decode_at
      (Parser_FastString_Spec.utf8_bytes s) pos in
  match uu___ with | (uu___1, adv) -> adv
let fs_byte_index (s : Prims.string) (i : Prims.nat) : FStar_Char.char=
  let b = fs_byte_at s i in
  if b < (Prims.of_int (0xD800))
  then FStar_Char.char_of_int b
  else FStar_Char.char_of_int Prims.int_zero
let fs_char_at (s : Prims.string) (i : Prims.nat) : FStar_Char.char=
  fs_byte_index s i
let rec fs_codepoints_of_string_aux (s : Prims.string) (slen : Prims.nat)
  (pos : Prims.nat) (acc : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if pos >= slen
  then FStar_List_Tot_Base.rev acc
  else
    (let uu___1 = fs_cp_at s pos in
     match uu___1 with
     | (cp, adv) ->
         let advn = if adv = Prims.int_zero then Prims.int_one else adv in
         let next = pos + advn in
         if next > slen
         then FStar_List_Tot_Base.rev acc
         else
           (let c =
              if cp < (Prims.of_int (0xd7ff))
              then FStar_Char.char_of_int cp
              else
                if
                  (cp >= (Prims.of_int (0xe000))) &&
                    (cp <= (Prims.parse_int "0x10ffff"))
                then FStar_Char.char_of_int cp
                else FStar_Char.char_of_int (Prims.of_int (0xFFFD)) in
            fs_codepoints_of_string_aux s slen next (c :: acc)))
let fs_codepoints_of_string (s : Prims.string) : FStar_Char.char Prims.list=
  fs_codepoints_of_string_aux s (fs_byte_length s) Prims.int_zero []
let fs_utf8_of_codepoint (cp : Prims.int) : Prims.string=
  let c =
    if cp = (Prims.of_int (0xD7FF))
    then Parser_FastString_CharBoundary.unsafe_char_of_d7ff cp
    else
      if
        (cp >= Prims.int_zero) &&
          ((cp < (Prims.of_int (0xD7FF))) ||
             ((cp >= (Prims.of_int (0xE000))) &&
                (cp <= (Prims.parse_int "0x10FFFF"))))
      then (let n = cp in FStar_Char.char_of_int n)
      else FStar_Char.char_of_int (Prims.of_int (0xFFFD)) in
  FStar_String.string_of_list [c]
