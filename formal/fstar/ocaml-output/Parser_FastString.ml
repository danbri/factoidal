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
let fs_byte_index (s : Prims.string) (i : Prims.nat) : FStar_Char.char=
  let b = fs_byte_at s i in
  if b < (Prims.of_int (0xD800))
  then FStar_Char.char_of_int b
  else FStar_Char.char_of_int Prims.int_zero
let fs_char_at (s : Prims.string) (i : Prims.nat) : FStar_Char.char=
  fs_byte_index s i
