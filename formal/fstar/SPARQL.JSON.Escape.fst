module SPARQL.JSON.Escape

open FStar.String
open FStar.List.Tot
open Parser.FastString

// Minimal JSON string escaper for the few characters that matter when
// embedding arbitrary SPARQL-query bodies in a JSON literal.
//
// Verification surface: the algorithm itself is verified pure F*. The byte
// access primitives `fs_byte_length` / `fs_byte_at` are declared via
// `assume val` in `Parser.FastString.fst` and realised in OCaml glue
// (patch 89). This module's correctness therefore reduces to those
// primitives' realisation matching their declared specs, which is the
// same trust boundary the rest of the parsers already rely on.
//
// Pure-data byte->byte function. The output is the same byte-for-byte
// as the previous OCaml implementation in factoidal_http.ml:
//   - 0x5C \\        -> \\ \\        (backslash)
//   - 0x22 "         -> \\ "         (double-quote)
//   - 0x0A \n        -> \\ n
//   - 0x0D \r        -> \\ r
//   - 0x09 \t        -> \\ t
//   - 0x08 \b        -> \\ b
//   - 0x0C \f        -> \\ f
//   - other b < 0x20 -> \\ u00XX     (lowercase hex)
//   - any other b    -> b unchanged  (UTF-8 bytes pass through)
//
// Migration of factoidal_http.ml's hand-written json_escape into F*
// (rule #1 — F* is the source of truth).

// One lowercase hex digit (0..15).  Out-of-range mapped to '0' to keep
// the function total.
let hex_digit_lc (n:nat) : FStar.Char.char =
  if n < 10 then FStar.Char.char_of_int (0x30 + n)
  else if n < 16 then FStar.Char.char_of_int (0x61 + (n - 10))
  else FStar.Char.char_of_int 0x30

// Is this byte one JSON string escaping must rewrite? All specials are
// ASCII; everything else (including UTF-8 continuation bytes) passes
// through untouched.
let json_special (b:nat) : bool =
  b < 0x20 || b = 0x22 || b = 0x5C

// The escape STRING for one special byte. Safe to build with
// string_of_list because every char here is ASCII — the extracted
// string_of_list realisation is codepoint-oriented, and for non-ASCII
// content that re-encoding corrupts bytes (see the 2026-07-04 note on
// walk_runs below), but ASCII is a fixed point of it.
let escape_string_of_byte (b:nat{json_special b}) : string =
  if b = 0x5C then "\\\\"
  else if b = 0x22 then "\\\""
  else if b = 0x0A then "\\n"
  else if b = 0x0D then "\\r"
  else if b = 0x09 then "\\t"
  else if b = 0x08 then "\\b"
  else if b = 0x0C then "\\f"
  else
    // Other control bytes: \u00xy, lowercase hex, high nibble first.
    let n3 = b % 16 in
    let n2 = (b / 16) % 16 in
    String.string_of_list [FStar.Char.char_of_int 0x5C;   // '\\'
                           FStar.Char.char_of_int 0x75;   // 'u'
                           FStar.Char.char_of_int 0x30;   // '0'
                           FStar.Char.char_of_int 0x30;   // '0'
                           hex_digit_lc n2;
                           hex_digit_lc n3]

// Copy maximal runs of non-special bytes with fs_byte_sub
// (byte-transparent — multi-byte UTF-8 sequences survive exactly),
// splicing in escape strings at the special bytes.
//
// 2026-07-04 rewrite: the previous implementation pushed every byte
// through a char list finished by string_of_list, which (a) had its
// escape pairs mirrored relative to the final rev ("n\\" instead of
// "\\n" — the npm-entry bundle was the first strict-JSON consumer of
// this output and crashed on it), and (b) double-encoded pass-through
// bytes >= 0x80, because the walk reads BYTES while the extracted
// string_of_list re-encodes each list element as a UTF-8 CODEPOINT
// ("café" became "cafÃ©" — same disease as issue #271). Run-slicing
// removes both failure modes and the O(n^2) list append.
let rec walk_runs (s:string) (len:nat) (run_start:nat) (pos:nat) (acc:string)
  : Tot string (decreases (len - pos)) =
  if pos >= len then
    (if pos > run_start then acc ^ fs_byte_sub s run_start (pos - run_start) else acc)
  else
    let b = fs_byte_at s pos in
    if json_special b then
      let run = if pos > run_start then fs_byte_sub s run_start (pos - run_start) else "" in
      walk_runs s len (pos + 1) (pos + 1) (acc ^ run ^ escape_string_of_byte b)
    else
      walk_runs s len run_start (pos + 1) acc

val json_escape : string -> string
let json_escape s =
  let len = fs_byte_length s in
  walk_runs s len 0 0 ""
