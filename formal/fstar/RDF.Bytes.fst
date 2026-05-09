module RDF.Bytes

(* Little-endian byte-layout primitives for companion-file writers.
   Section B of #200's migration epic (writers: .dict, .presence,
   .compound-presence, .p.offsets, etc.).

   Per CLAUDE.md rule #11: byte assembly belongs in F\*. Each
   `serialize : data -> Tot (list u8)` lives here or in a sibling
   F\* module; the OCaml side reduces to `write_bytes` of the
   pre-assembled byte sequence.

   Representation: `list FStar.Char.char` where each `char` is
   constrained to the byte range [0, 255]. The tighter type
   `FStar.UInt8.t` is available but Char gives us cheaper string
   conversion via `String.string_of_list` for the final write step.

   Verification scope: total, pure, no `assume val`, no `--lax`. *)

open FStar.List.Tot

(* --------------------------------------------------------------------
   byte = char restricted to 0..255 (the 256 byte values are a subset
   of valid Unicode codepoints, so `char_of_int` accepts them). We
   alias `char` for ergonomics + downstream string conversion.
   -------------------------------------------------------------------- *)

let byte = FStar.Char.char
let bytes = list byte

let byte_of_int (n : int{n >= 0 /\ n < 256}) : Tot byte =
  FStar.Char.char_of_int n

(* --------------------------------------------------------------------
   write_u32_le n
     Little-endian 4-byte encoding of a non-negative int < 2^32.
     Returns a list of 4 bytes in LE order: [n%256; (n/256)%256;
     (n/65536)%256; (n/16777216)%256].
   -------------------------------------------------------------------- *)

let write_u32_le (n : nat{n < 4294967296}) : Tot (b:bytes{length b == 4}) =
  let b0 = n % 256 in
  let b1 = (n / 256) % 256 in
  let b2 = (n / 65536) % 256 in
  let b3 = (n / 16777216) % 256 in
  [byte_of_int b0; byte_of_int b1; byte_of_int b2; byte_of_int b3]

(* --------------------------------------------------------------------
   write_u64_le n
     Little-endian 8-byte encoding of a non-negative int < 2^64.
     Same pattern as write_u32_le.
   -------------------------------------------------------------------- *)

let write_u64_le (n : nat{n < 18446744073709551616}) : Tot bytes =
  let b0 = n % 256 in
  let b1 = (n / 256) % 256 in
  let b2 = (n / 65536) % 256 in
  let b3 = (n / 16777216) % 256 in
  let b4 = (n / 4294967296) % 256 in
  let b5 = (n / 1099511627776) % 256 in
  let b6 = (n / 281474976710656) % 256 in
  let b7 = (n / 72057594037927936) % 256 in
  [byte_of_int b0; byte_of_int b1; byte_of_int b2; byte_of_int b3;
   byte_of_int b4; byte_of_int b5; byte_of_int b6; byte_of_int b7]

(* --------------------------------------------------------------------
   bytes_of_string s
     Each codepoint becomes one byte iff the string is pure ASCII
     (all codepoints < 128). For the .dict writer, token strings can
     contain any UTF-8, so we use the raw codepoint→char→string path.
     The dict-format spec stores bytes, not codepoints, so this only
     works correctly when the input strings are encoded as the bytes
     the on-disk reader expects. Empirically that's UTF-8 for COTTAS
     tokens, with the F\* string layer being byte-transparent.

     Returns the byte list whose string-of-list reproduces s.
   -------------------------------------------------------------------- *)

let bytes_of_string (s : string) : Tot bytes =
  String.list_of_string s

(* --------------------------------------------------------------------
   bytes_to_string bs
     Inverse of String.list_of_string. The OCaml side uses this on
     the assembled byte sequence as the final atomic write payload.
   -------------------------------------------------------------------- *)

let bytes_to_string (bs : bytes) : Tot string =
  String.string_of_list bs

(* --------------------------------------------------------------------
   sum_lengths_acc / sum_lengths
     Total byte length of a list of strings. Used to size buffers.
   -------------------------------------------------------------------- *)

let rec sum_lengths_acc (acc : nat) (xs : list string)
  : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | x :: rest -> sum_lengths_acc (acc + String.length x) rest

let sum_lengths (xs : list string) : Tot nat =
  sum_lengths_acc 0 xs

(* --------------------------------------------------------------------
   Read primitives — inverse of the write_u32_le / write_u64_le /
   bytes_of_string helpers above. Used by parsers (parse_dict,
   parse_presence, parse_offsets, parse_compound_presence) for the
   round-trip witness pattern: parse (serialize x) == Some x.

   All read primitives are total and pure. Each peels its consumed
   bytes off the FRONT of the input and returns the unread suffix
   alongside the parsed value. Returning [None] means the input was
   shorter than the requested field.
   -------------------------------------------------------------------- *)

let int_of_byte (b : byte) : Tot (n:int{n >= 0 /\ n < 256}) =
  let n = FStar.Char.int_of_char b in
  if n < 0 || n >= 256 then 0 else n

let parse_u32_le (bs : bytes) : Tot (option (nat & bytes)) =
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest ->
    let v0 : nat = int_of_byte b0 in
    let v1 : nat = (int_of_byte b1) `op_Multiply` 256 in
    let v2 : nat = (int_of_byte b2) `op_Multiply` 65536 in
    let v3 : nat = (int_of_byte b3) `op_Multiply` 16777216 in
    let n : nat = v0 + v1 + v2 + v3 in
    Some (n, rest)
  | _ -> None

let parse_u64_le (bs : bytes) : Tot (option (nat & bytes)) =
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest ->
    let v0 : nat = int_of_byte b0 in
    let v1 : nat = (int_of_byte b1) `op_Multiply` 256 in
    let v2 : nat = (int_of_byte b2) `op_Multiply` 65536 in
    let v3 : nat = (int_of_byte b3) `op_Multiply` 16777216 in
    let v4 : nat = (int_of_byte b4) `op_Multiply` 4294967296 in
    let v5 : nat = (int_of_byte b5) `op_Multiply` 1099511627776 in
    let v6 : nat = (int_of_byte b6) `op_Multiply` 281474976710656 in
    let v7 : nat = (int_of_byte b7) `op_Multiply` 72057594037927936 in
    let n : nat = v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 in
    Some (n, rest)
  | _ -> None

let rec parse_n_bytes (n : nat) (bs : bytes)
  : Tot (option (bytes & bytes)) (decreases n) =
  if n = 0 then Some ([], bs)
  else
    match bs with
    | [] -> None
    | b :: rest ->
      match parse_n_bytes (n - 1) rest with
      | None -> None
      | Some (taken, remainder) -> Some (b :: taken, remainder)

let parse_string_of_length (n : nat) (bs : bytes)
  : Tot (option (string & bytes)) =
  match parse_n_bytes n bs with
  | None -> None
  | Some (taken, remainder) -> Some (bytes_to_string taken, remainder)
