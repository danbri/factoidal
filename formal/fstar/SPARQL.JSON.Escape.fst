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

// Render a byte b (0..255) as four lowercase hex digits, prepended in
// reverse order onto the accumulator (as a byte goes through one nibble
// at a time we emit high nibble first to the resulting string).
//
// We push chars in reverse onto the acc; the caller will rev+concat.
// So to produce "00xy" in the final string, we push 'y','x','0','0'.
let push_u_escape (b:nat) (acc:list FStar.Char.char) : list FStar.Char.char =
  // b expected in [0, 255]; if larger, masked to low 8 bits semantics
  // would be wrong — but callers only pass byte values.
  let n3 = b % 16 in
  let r1 = b / 16 in
  let n2 = r1 % 16 in
  let r2 = r1 / 16 in
  let n1 = r2 % 16 in
  let n0 = (r2 / 16) % 16 in
  // Build the literal "\u" + 4 hex digits, rev-prepended.
  // Final string char order: '\\' 'u' n0 n1 n2 n3
  // Reverse-prepended order: n3 n2 n1 n0 'u' '\\'
  let acc = (hex_digit_lc n3) :: acc in
  let acc = (hex_digit_lc n2) :: acc in
  let acc = (hex_digit_lc n1) :: acc in
  let acc = (hex_digit_lc n0) :: acc in
  let acc = (FStar.Char.char_of_int 0x75) :: acc in   // 'u'
  let acc = (FStar.Char.char_of_int 0x5C) :: acc in   // '\\'
  acc

// Push a literal two-char escape (backslash + c) onto rev acc.
let push_escape2 (c:FStar.Char.char) (acc:list FStar.Char.char) : list FStar.Char.char =
  let acc = c :: acc in
  let acc = (FStar.Char.char_of_int 0x5C) :: acc in
  acc

// Single byte -> reverse-prepended chars in acc.
let escape_byte (b:nat{b < 256}) (acc:list FStar.Char.char) : list FStar.Char.char =
  if b = 0x5C then push_escape2 (FStar.Char.char_of_int 0x5C) acc          // \\
  else if b = 0x22 then push_escape2 (FStar.Char.char_of_int 0x22) acc      // "
  else if b = 0x0A then push_escape2 (FStar.Char.char_of_int 0x6E) acc      // n
  else if b = 0x0D then push_escape2 (FStar.Char.char_of_int 0x72) acc      // r
  else if b = 0x09 then push_escape2 (FStar.Char.char_of_int 0x74) acc      // t
  else if b = 0x08 then push_escape2 (FStar.Char.char_of_int 0x62) acc      // b
  else if b = 0x0C then push_escape2 (FStar.Char.char_of_int 0x66) acc      // f
  else if b < 0x20 then push_u_escape b acc
  else
    // Any other byte: pass through. Bytes 0x80..0xFF are valid F* chars
    // (char_of_int's restriction is < 0xD800).
    (FStar.Char.char_of_int b) :: acc

// Walk the input by byte, building a reversed char list.
let rec walk (s:string) (len:nat) (pos:nat) (acc:list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (len - pos))
  =
  if pos >= len then acc
  else
    let b = fs_byte_at s pos in
    let acc' = escape_byte b acc in
    walk s len (pos + 1) acc'

val json_escape : string -> string
let json_escape s =
  let len = fs_byte_length s in
  let acc = walk s len 0 [] in
  String.string_of_list (List.Tot.rev acc)
