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
let json_special (b : Prims.nat) : Prims.bool=
  ((b < (Prims.of_int (0x20))) || (b = (Prims.of_int (0x22)))) ||
    (b = (Prims.of_int (0x5C)))
let escape_string_of_byte (b : Prims.nat) : Prims.string=
  if b = (Prims.of_int (0x5C))
  then "\\\\"
  else
    if b = (Prims.of_int (0x22))
    then "\\\""
    else
      if b = (Prims.of_int (0x0A))
      then "\\n"
      else
        if b = (Prims.of_int (0x0D))
        then "\\r"
        else
          if b = (Prims.of_int (0x09))
          then "\\t"
          else
            if b = (Prims.of_int (0x08))
            then "\\b"
            else
              if b = (Prims.of_int (0x0C))
              then "\\f"
              else
                (let n3 = (mod) b (Prims.of_int (16)) in
                 let n2 = (mod) (b / (Prims.of_int (16))) (Prims.of_int (16)) in
                 FStar_String.string_of_list
                   [FStar_Char.char_of_int (Prims.of_int (0x5C));
                   FStar_Char.char_of_int (Prims.of_int (0x75));
                   FStar_Char.char_of_int (Prims.of_int (0x30));
                   FStar_Char.char_of_int (Prims.of_int (0x30));
                   hex_digit_lc n2;
                   hex_digit_lc n3])
let rec walk_runs (s : Prims.string) (len : Prims.nat)
  (run_start : Prims.nat) (pos : Prims.nat) (acc : Prims.string) :
  Prims.string=
  if pos >= len
  then
    (if pos > run_start
     then
       Prims.strcat acc
         (Parser_FastString.fs_byte_sub s run_start (pos - run_start))
     else acc)
  else
    (let b = Parser_FastString.fs_byte_at s pos in
     if json_special b
     then
       let run =
         if pos > run_start
         then Parser_FastString.fs_byte_sub s run_start (pos - run_start)
         else "" in
       walk_runs s len (pos + Prims.int_one) (pos + Prims.int_one)
         (Prims.strcat acc (Prims.strcat run (escape_string_of_byte b)))
     else walk_runs s len run_start (pos + Prims.int_one) acc)
let json_escape (s : Prims.string) : Prims.string=
  let len = Parser_FastString.fs_byte_length s in
  walk_runs s len Prims.int_zero Prims.int_zero ""
