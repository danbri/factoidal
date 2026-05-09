open Prims
type byte = FStar_Char.char
type bytes = byte Prims.list
let byte_of_int (n : Prims.int) : byte= FStar_Char.char_of_int n
let write_u32_le (n : Prims.nat) : bytes=
  let b0 = (mod) n (Prims.of_int (256)) in
  let b1 = (mod) (n / (Prims.of_int (256))) (Prims.of_int (256)) in
  let b2 = (mod) (n / (Prims.parse_int "65536")) (Prims.of_int (256)) in
  let b3 = (mod) (n / (Prims.parse_int "16777216")) (Prims.of_int (256)) in
  [byte_of_int b0; byte_of_int b1; byte_of_int b2; byte_of_int b3]
let write_u64_le (n : Prims.nat) : bytes=
  let b0 = (mod) n (Prims.of_int (256)) in
  let b1 = (mod) (n / (Prims.of_int (256))) (Prims.of_int (256)) in
  let b2 = (mod) (n / (Prims.parse_int "65536")) (Prims.of_int (256)) in
  let b3 = (mod) (n / (Prims.parse_int "16777216")) (Prims.of_int (256)) in
  let b4 = (mod) (n / (Prims.parse_int "4294967296")) (Prims.of_int (256)) in
  let b5 = (mod) (n / (Prims.parse_int "1099511627776")) (Prims.of_int (256)) in
  let b6 =
    (mod) (n / (Prims.parse_int "281474976710656")) (Prims.of_int (256)) in
  let b7 =
    (mod) (n / (Prims.parse_int "72057594037927936")) (Prims.of_int (256)) in
  [byte_of_int b0;
  byte_of_int b1;
  byte_of_int b2;
  byte_of_int b3;
  byte_of_int b4;
  byte_of_int b5;
  byte_of_int b6;
  byte_of_int b7]
let bytes_of_string (s : Prims.string) : bytes= FStar_String.list_of_string s
let bytes_to_string (bs : bytes) : Prims.string=
  FStar_String.string_of_list bs
let rec sum_lengths_acc (acc : Prims.nat) (xs : Prims.string Prims.list) :
  Prims.nat=
  match xs with
  | [] -> acc
  | x::rest -> sum_lengths_acc (acc + (FStar_String.strlen x)) rest
let sum_lengths (xs : Prims.string Prims.list) : Prims.nat=
  sum_lengths_acc Prims.int_zero xs
let int_of_byte (b : byte) : Prims.int=
  let n = FStar_Char.int_of_char b in
  if (n < Prims.int_zero) || (n >= (Prims.of_int (256)))
  then Prims.int_zero
  else n
let parse_u32_le (bs : bytes) :
  (Prims.nat * bytes) FStar_Pervasives_Native.option=
  match bs with
  | b0::b1::b2::b3::rest ->
      let v0 = int_of_byte b0 in
      let v1 = (int_of_byte b1) * (Prims.of_int (256)) in
      let v2 = (int_of_byte b2) * (Prims.parse_int "65536") in
      let v3 = (int_of_byte b3) * (Prims.parse_int "16777216") in
      let n = ((v0 + v1) + v2) + v3 in FStar_Pervasives_Native.Some (n, rest)
  | uu___ -> FStar_Pervasives_Native.None
let parse_u64_le (bs : bytes) :
  (Prims.nat * bytes) FStar_Pervasives_Native.option=
  match bs with
  | b0::b1::b2::b3::b4::b5::b6::b7::rest ->
      let v0 = int_of_byte b0 in
      let v1 = (int_of_byte b1) * (Prims.of_int (256)) in
      let v2 = (int_of_byte b2) * (Prims.parse_int "65536") in
      let v3 = (int_of_byte b3) * (Prims.parse_int "16777216") in
      let v4 = (int_of_byte b4) * (Prims.parse_int "4294967296") in
      let v5 = (int_of_byte b5) * (Prims.parse_int "1099511627776") in
      let v6 = (int_of_byte b6) * (Prims.parse_int "281474976710656") in
      let v7 = (int_of_byte b7) * (Prims.parse_int "72057594037927936") in
      let n = ((((((v0 + v1) + v2) + v3) + v4) + v5) + v6) + v7 in
      FStar_Pervasives_Native.Some (n, rest)
  | uu___ -> FStar_Pervasives_Native.None
let rec parse_n_bytes (n : Prims.nat) (bs : bytes) :
  (bytes * bytes) FStar_Pervasives_Native.option=
  if n = Prims.int_zero
  then FStar_Pervasives_Native.Some ([], bs)
  else
    (match bs with
     | [] -> FStar_Pervasives_Native.None
     | b::rest ->
         (match parse_n_bytes (n - Prims.int_one) rest with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (taken, remainder) ->
              FStar_Pervasives_Native.Some ((b :: taken), remainder)))
let parse_string_of_length (n : Prims.nat) (bs : bytes) :
  (Prims.string * bytes) FStar_Pervasives_Native.option=
  match parse_n_bytes n bs with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (taken, remainder) ->
      FStar_Pervasives_Native.Some ((bytes_to_string taken), remainder)
