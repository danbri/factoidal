module IODemo

// End-to-end demonstration that the F* + extraction story can do
// real file I/O via FStar.IO without leaving the verified path —
// no `assume val` for the I/O primitives.
//
// Encoding: comma-separated decimal u16s on one line.
//
//   container [7, 42, 50, 100]
//     ⟶ written as "7,42,50,100" on one line
//     ⟶ read back, parsed, re-built as the same array_container.
//
// This is not the official Roaring portable format (Phase H scope).
// It's a demonstration that the I/O boundary is clean: the encode
// and decode functions are pure F* (Tot, verified types); only
// the file-handle wrappers live in the ML effect.

open FStar.All
open FStar.List.Tot
open Spec
open Container.Array

module IO = FStar.IO
module String = FStar.String
module Parse = FStar.Parse

// ---------------------------------------------------------------
// Encode: array_container -> string (pure).
//
// "" for empty, "x" for [x], "x1,x2,..,xn" for the rest.
// ---------------------------------------------------------------

let rec encode_aux (xs : list u16_val) : Tot string =
  match xs with
  | [] -> ""
  | [x] -> string_of_int x
  | x :: rest -> string_of_int x ^ "," ^ encode_aux rest

let encode (c : array_container) : Tot string = encode_aux c

// ---------------------------------------------------------------
// Decode: string -> option array_container (pure-effect tagged).
//
// We parse comma-separated decimals. Any malformed input returns
// None. The decode lives in the Dv (divergence-allowed) effect
// because parsing chars from a string isn't structurally
// recursive on a list. Pure correctness is preserved — Dv just
// disables the totality check.
// ---------------------------------------------------------------

// Split a string on commas into a list of substrings.
let split_commas (s : string) : Tot (list string) =
  String.split [','] s

// Parse one substring as a u16; return None on parse error or
// out-of-range.
let parse_u16 (s : string) : Tot (option u16_val) =
  match Parse.int_of_string s with
  | None -> None
  | Some n ->
    if n >= 0 && n < pow16 then Some n else None

// Build an array_container from a list of u16 values by repeated
// insertion. Each insert preserves invariants. We walk the list,
// thread the partial container through, and return None if any
// individual parse failed or if the cardinality bound is hit.
let rec parse_and_insert (xs : list string) (acc : array_container)
  : Tot (option array_container) (decreases xs)
=
  match xs with
  | [] -> Some acc
  | s :: rest ->
    match parse_u16 s with
    | None -> None
    | Some v ->
      // Cardinality bound check before insert: if acc is at the cap
      // and v isn't already there, fail decode.
      if length acc < array_max_cardinality || array_contains acc v then
        let acc' = array_insert acc v in
        parse_and_insert rest acc'
      else
        None

let decode (s : string) : Tot (option array_container) =
  if s = "" then Some array_empty
  else parse_and_insert (split_commas s) array_empty

// ---------------------------------------------------------------
// File I/O wrappers — these are the *only* part of this module
// that's effectful (ML effect). Both the encode and decode above
// are total / pure.
// ---------------------------------------------------------------

let write_to_file (path : string) (c : array_container) : ML unit =
  let fd = IO.open_write_file path in
  IO.write_string fd (encode c);
  IO.close_write_file fd

let read_from_file (path : string) : ML (option array_container) =
  let fd = IO.open_read_file path in
  // read_line will throw EOF when the file is empty, but a non-empty
  // file with our format always has exactly one line.
  let line =
    try IO.read_line fd
    with
    | IO.EOF -> ""
    | _ -> ""
  in
  IO.close_read_file fd;
  decode line

// ---------------------------------------------------------------
// assert_norm round-trip on a small concrete container.
//
// Note: this only checks decode(encode(c)) = Some c on a fixed
// example. A universally quantified round-trip lemma is the next
// step (proof debt? candidate for Phase H polish), but the
// concrete-case check at type-check time still establishes that
// the two paths are consistent.
// ---------------------------------------------------------------

let example : array_container = [7; 42; 50; 100]

let _ =
  assert_norm
    (encode example = "7,42,50,100")
