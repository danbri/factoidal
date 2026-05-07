open Prims
let hex_digit_lc (n : Prims.nat) : FStar_Char.char=
  if n < (Prims.of_int (10))
  then FStar_Char.char_of_int ((Prims.of_int (0x30)) + n)
  else
    if n < (Prims.of_int (16))
    then
      FStar_Char.char_of_int
        ((Prims.of_int (0x61)) + (n - (Prims.of_int (10))))
    else FStar_Char.char_of_int (Prims.of_int (0x30))
let push_u_escape (b : Prims.nat) (acc : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  let n3 = (mod) b (Prims.of_int (16)) in
  let r1 = b / (Prims.of_int (16)) in
  let n2 = (mod) r1 (Prims.of_int (16)) in
  let r2 = r1 / (Prims.of_int (16)) in
  let n1 = (mod) r2 (Prims.of_int (16)) in
  let n0 = (mod) (r2 / (Prims.of_int (16))) (Prims.of_int (16)) in
  let acc1 = (hex_digit_lc n3) :: acc in
  let acc2 = (hex_digit_lc n2) :: acc1 in
  let acc3 = (hex_digit_lc n1) :: acc2 in
  let acc4 = (hex_digit_lc n0) :: acc3 in
  let acc5 = (FStar_Char.char_of_int (Prims.of_int (0x75))) :: acc4 in
  let acc6 = (FStar_Char.char_of_int (Prims.of_int (0x5C))) :: acc5 in acc6
let push_escape2 (c : FStar_Char.char) (acc : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  let acc1 = c :: acc in
  let acc2 = (FStar_Char.char_of_int (Prims.of_int (0x5C))) :: acc1 in acc2
let escape_byte (b : Prims.nat) (acc : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  if b = (Prims.of_int (0x5C))
  then push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x5C))) acc
  else
    if b = (Prims.of_int (0x22))
    then push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x22))) acc
    else
      if b = (Prims.of_int (0x0A))
      then push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x6E))) acc
      else
        if b = (Prims.of_int (0x0D))
        then push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x72))) acc
        else
          if b = (Prims.of_int (0x09))
          then
            push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x74))) acc
          else
            if b = (Prims.of_int (0x08))
            then
              push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x62))) acc
            else
              if b = (Prims.of_int (0x0C))
              then
                push_escape2 (FStar_Char.char_of_int (Prims.of_int (0x66)))
                  acc
              else
                if b < (Prims.of_int (0x20))
                then push_u_escape b acc
                else (FStar_Char.char_of_int b) :: acc
let rec walk (s : Prims.string) (len : Prims.nat) (pos : Prims.nat)
  (acc : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  if pos >= len
  then acc
  else
    (let b = Parser_FastString.fs_byte_at s pos in
     let acc' = escape_byte b acc in walk s len (pos + Prims.int_one) acc')
let json_escape (s : Prims.string) : Prims.string=
  let len = Parser_FastString.fs_byte_length s in
  let acc = walk s len Prims.int_zero [] in
  FStar_String.string_of_list (FStar_List_Tot_Base.rev acc)
