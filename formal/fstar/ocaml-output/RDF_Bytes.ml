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
