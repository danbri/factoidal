open Prims
type byte = Prims.nat
let hex_digit_val (c : FStar_Char.char) :
  Prims.nat FStar_Pervasives_Native.option=
  let x = FStar_Char.int_of_char c in
  if (x >= (Prims.of_int (0x30))) && (x <= (Prims.of_int (0x39)))
  then FStar_Pervasives_Native.Some (x - (Prims.of_int (0x30)))
  else
    if (x >= (Prims.of_int (0x61))) && (x <= (Prims.of_int (0x66)))
    then
      FStar_Pervasives_Native.Some
        ((x - (Prims.of_int (0x61))) + (Prims.of_int (10)))
    else
      if (x >= (Prims.of_int (0x41))) && (x <= (Prims.of_int (0x46)))
      then
        FStar_Pervasives_Native.Some
          ((x - (Prims.of_int (0x41))) + (Prims.of_int (10)))
      else FStar_Pervasives_Native.None
let hex_char_of (d : Prims.nat) : FStar_Char.char=
  let digits = "0123456789abcdef" in
  let l = FStar_String.list_of_string digits in
  match FStar_List_Tot_Base.nth l d with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None ->
      FStar_Char.char_of_int (Prims.of_int (0x30))
let rec chars_to_bytes (cs : FStar_Char.char Prims.list) :
  byte Prims.list FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some []
  | uu___::[] -> FStar_Pervasives_Native.None
  | hi::lo::rest ->
      (match ((hex_digit_val hi), (hex_digit_val lo), (chars_to_bytes rest))
       with
       | (FStar_Pervasives_Native.Some h, FStar_Pervasives_Native.Some l,
          FStar_Pervasives_Native.Some tl) ->
           FStar_Pervasives_Native.Some (((h * (Prims.of_int (16))) + l) ::
             tl)
       | (uu___, uu___1, uu___2) -> FStar_Pervasives_Native.None)
let hex_to_bytes (s : Prims.string) :
  byte Prims.list FStar_Pervasives_Native.option=
  chars_to_bytes (FStar_String.list_of_string s)
let byte_to_hex_chars (b : byte) : FStar_Char.char Prims.list=
  [hex_char_of (b / (Prims.of_int (16)));
  hex_char_of ((mod) b (Prims.of_int (16)))]
let rec bytes_to_hex_chars (bs : byte Prims.list) :
  FStar_Char.char Prims.list=
  match bs with
  | [] -> []
  | b::t ->
      FStar_List_Tot_Base.op_At (byte_to_hex_chars b) (bytes_to_hex_chars t)
let bytes_to_hex (bs : byte Prims.list) : Prims.string=
  FStar_String.string_of_list (bytes_to_hex_chars bs)
let rec pow256 (k : Prims.nat) : Prims.nat=
  if k = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (256)) * (pow256 (k - Prims.int_one))
let rec bytes_to_nat (bs : byte Prims.list) : Prims.nat=
  match bs with
  | [] -> Prims.int_zero
  | b::t -> (b * (pow256 (FStar_List_Tot_Base.length t))) + (bytes_to_nat t)
let rec nat_to_bytes_be (n : Prims.nat) : byte Prims.list=
  if n = Prims.int_zero
  then []
  else
    FStar_List_Tot_Base.op_At (nat_to_bytes_be (n / (Prims.of_int (256))))
      [(mod) n (Prims.of_int (256))]
let rec count_leading_zero_bytes (bs : byte Prims.list) : Prims.nat=
  match bs with
  | uu___::t when uu___ = Prims.int_zero ->
      Prims.int_one + (count_leading_zero_bytes t)
  | uu___ -> Prims.int_zero
let rec repeat_byte (b : byte) (k : Prims.nat) : byte Prims.list=
  if k = Prims.int_zero then [] else b :: (repeat_byte b (k - Prims.int_one))
let rec repeat_char (c : FStar_Char.char) (k : Prims.nat) :
  FStar_Char.char Prims.list=
  if k = Prims.int_zero then [] else c :: (repeat_char c (k - Prims.int_one))
let base58_alphabet : Prims.string=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
let base58_char_of (d : Prims.nat) : FStar_Char.char=
  let l = FStar_String.list_of_string base58_alphabet in
  match FStar_List_Tot_Base.nth l d with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None ->
      FStar_Char.char_of_int (Prims.of_int (0x31))
let rec find_index_aux (cs : FStar_Char.char Prims.list)
  (c : FStar_Char.char) (i : Prims.nat) :
  Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.None
  | h::t ->
      if h = c
      then FStar_Pervasives_Native.Some i
      else find_index_aux t c (i + Prims.int_one)
let base58_digit_of (c : FStar_Char.char) :
  Prims.nat FStar_Pervasives_Native.option=
  match find_index_aux (FStar_String.list_of_string base58_alphabet) c
          Prims.int_zero
  with
  | FStar_Pervasives_Native.Some i ->
      if i < (Prims.of_int (58))
      then FStar_Pervasives_Native.Some i
      else FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec nat_to_base58_chars (n : Prims.nat) : FStar_Char.char Prims.list=
  if n = Prims.int_zero
  then []
  else
    FStar_List_Tot_Base.op_At (nat_to_base58_chars (n / (Prims.of_int (58))))
      [base58_char_of ((mod) n (Prims.of_int (58)))]
let base58btc_encode (bs : byte Prims.list) : Prims.string=
  let zeros = count_leading_zero_bytes bs in
  let n = bytes_to_nat bs in
  let body = nat_to_base58_chars n in
  let ones = repeat_char (FStar_Char.char_of_int (Prims.of_int (0x31))) zeros in
  FStar_String.string_of_list (FStar_List_Tot_Base.op_At ones body)
let rec base58_chars_to_nat (cs : FStar_Char.char Prims.list)
  (acc : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  match cs with
  | [] -> FStar_Pervasives_Native.Some acc
  | c::t ->
      (match base58_digit_of c with
       | FStar_Pervasives_Native.Some d ->
           base58_chars_to_nat t ((acc * (Prims.of_int (58))) + d)
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec count_leading_ones (cs : FStar_Char.char Prims.list) : Prims.nat=
  match cs with
  | c::t ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x31))
      then Prims.int_one + (count_leading_ones t)
      else Prims.int_zero
  | [] -> Prims.int_zero
let base58btc_decode (s : Prims.string) :
  byte Prims.list FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  let ones = count_leading_ones cs in
  match base58_chars_to_nat cs Prims.int_zero with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some n ->
      FStar_Pervasives_Native.Some
        (FStar_List_Tot_Base.op_At (repeat_byte Prims.int_zero ones)
           (nat_to_bytes_be n))
let multibase_encode_base58btc (bs : byte Prims.list) : Prims.string=
  FStar_String.string_of_list ((FStar_Char.char_of_int (Prims.of_int (0x7A)))
    :: (FStar_String.list_of_string (base58btc_encode bs)))
let multibase_decode (s : Prims.string) :
  byte Prims.list FStar_Pervasives_Native.option=
  match FStar_String.list_of_string s with
  | c::rest ->
      if (FStar_Char.int_of_char c) = (Prims.of_int (0x7A))
      then base58btc_decode (FStar_String.string_of_list rest)
      else FStar_Pervasives_Native.None
  | [] -> FStar_Pervasives_Native.None
let hex_to_multibase_z (sig_hex : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match hex_to_bytes sig_hex with
  | FStar_Pervasives_Native.Some bs ->
      FStar_Pervasives_Native.Some (multibase_encode_base58btc bs)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let multibase_z_to_hex (mb : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match multibase_decode mb with
  | FStar_Pervasives_Native.Some bs ->
      FStar_Pervasives_Native.Some (bytes_to_hex bs)
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let ed25519_multicodec_prefix : byte Prims.list=
  [(Prims.of_int (0xed)); Prims.int_one]
let ed25519_pubkey_to_multikey (pk_hex : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  match hex_to_bytes pk_hex with
  | FStar_Pervasives_Native.Some pk ->
      FStar_Pervasives_Native.Some
        (multibase_encode_base58btc
           (FStar_List_Tot_Base.op_At ed25519_multicodec_prefix pk))
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
