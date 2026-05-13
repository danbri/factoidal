open Prims
let fs_byte_length (uu___ : Prims.string) : Prims.nat=
  failwith "Not yet implemented: Parser.FastString.fs_byte_length"
let fs_byte_at (s : Prims.string) (i : Prims.nat) : Prims.nat=
  failwith "Not yet implemented: Parser.FastString.fs_byte_at"
let fs_byte_sub (s : Prims.string) (start : Prims.nat) (len : Prims.nat) :
  Prims.string= failwith "Not yet implemented: Parser.FastString.fs_byte_sub"
let fs_find_byte (s : Prims.string) (b : Prims.nat) (start : Prims.nat) :
  Prims.nat= failwith "Not yet implemented: Parser.FastString.fs_find_byte"
let fs_cp_at (s : Prims.string) (pos : Prims.nat) : (Prims.nat * Prims.nat)=
  failwith "Not yet implemented: Parser.FastString.fs_cp_at"
let fs_cp_len (s : Prims.string) (pos : Prims.nat) : Prims.nat=
  failwith "Not yet implemented: Parser.FastString.fs_cp_len"
let unsafe_char_of_d7ff (i : Prims.int) : FStar_Char.char=
  failwith "Not yet implemented: Parser.FastString.unsafe_char_of_d7ff"
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
