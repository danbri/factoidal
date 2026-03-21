module Utf8

// UTF-8 validation, decoding, and character classification.
// Modeled after Serd's string_utils.h.
//
// Key functions:
//   - utf8_num_bytes: leading byte -> expected sequence length
//   - decode_utf8: byte sequence -> Unicode codepoint
//   - Character classification for Turtle grammar (PN_CHARS_BASE, etc.)
//
// Proof goals:
//   - Valid UTF-8 in -> valid codepoints out
//   - No buffer overruns on decode

module U8 = FStar.UInt8
module U32 = FStar.UInt32

// Number of bytes in a UTF-8 character given the leading byte.
// Returns 0 for invalid leading bytes (continuation bytes 10xxxxxx,
// or overlong 5/6-byte sequences 111111xx).
let utf8_num_bytes (leading: U8.t) : U32.t =
  let v = U8.v leading in
  if v < 0x80 then 1ul           // 0xxxxxxx - ASCII
  else if v < 0xC0 then 0ul      // 10xxxxxx - continuation (invalid as leading)
  else if v < 0xE0 then 2ul      // 110xxxxx
  else if v < 0xF0 then 3ul      // 1110xxxx
  else if v < 0xF8 then 4ul      // 11110xxx
  else 0ul                        // 11111xxx - invalid

// Number of UTF-8 bytes needed to encode a Unicode codepoint.
let utf8_bytes_for_codepoint (cp: U32.t) : U32.t =
  let v = U32.v cp in
  if v <= 0x7F then 1ul
  else if v <= 0x7FF then 2ul
  else if v <= 0xFFFF then 3ul
  else if v <= 0x10FFFF then 4ul
  else 0ul  // out of range

// Is this byte a UTF-8 continuation byte? (10xxxxxx)
let is_continuation (b: U8.t) : bool =
  U8.(b &^ 0xC0uy) = 0x80uy

// Decode a UTF-8 sequence of known length.
// Returns the Unicode codepoint, or 0xFFFD (replacement char) on error.
// Caller must ensure `size` bytes are available.
let decode_counted (b0: U8.t) (b1: U8.t) (b2: U8.t) (b3: U8.t) (size: U32.t) : U32.t =
  let replacement = 0xFFFDul in
  if size = 1ul then
    FStar.Int.Cast.uint8_to_uint32 b0
  else if size = 2ul then
    if not (is_continuation b1) then replacement
    else
      let c0 = U32.uint_to_t (U8.v b0 % 32) in     // low 5 bits
      let c1 = U32.uint_to_t (U8.v b1 % 64) in     // low 6 bits
      U32.((c0 *^ 64ul) +^ c1)
  else if size = 3ul then
    if not (is_continuation b1) || not (is_continuation b2) then replacement
    else
      let c0 = U32.uint_to_t (U8.v b0 % 16) in     // low 4 bits
      let c1 = U32.uint_to_t (U8.v b1 % 64) in
      let c2 = U32.uint_to_t (U8.v b2 % 64) in
      U32.((c0 *^ 4096ul) +^ (c1 *^ 64ul) +^ c2)
  else if size = 4ul then
    if not (is_continuation b1) || not (is_continuation b2) || not (is_continuation b3) then replacement
    else
      let c0 = U32.uint_to_t (U8.v b0 % 8) in      // low 3 bits
      let c1 = U32.uint_to_t (U8.v b1 % 64) in
      let c2 = U32.uint_to_t (U8.v b2 % 64) in
      let c3 = U32.uint_to_t (U8.v b3 % 64) in
      U32.((c0 *^ 262144ul) +^ (c1 *^ 4096ul) +^ (c2 *^ 64ul) +^ c3)
  else replacement

// Validate a decoded codepoint:
//   - Not a surrogate (U+D800..U+DFFF)
//   - Not above U+10FFFF
//   - Not overlong encoding (minimum bytes check)
let is_valid_codepoint (cp: U32.t) (size: U32.t) : bool =
  let v = U32.v cp in
  let s = U32.v size in
  v <= 0x10FFFF &&
  not (v >= 0xD800 && v <= 0xDFFF) &&
  // Overlong check: codepoint must require at least `size` bytes
  (s <> 2 || v >= 0x80) &&
  (s <> 3 || v >= 0x800) &&
  (s <> 4 || v >= 0x10000)

// ---- Character classification for Turtle/SPARQL grammar ----

// ASCII classification
let is_alpha (c: U32.t) : bool =
  let v = U32.v c in
  (v >= 0x41 && v <= 0x5A) ||  // A-Z
  (v >= 0x61 && v <= 0x7A)     // a-z

let is_digit (c: U32.t) : bool =
  let v = U32.v c in
  v >= 0x30 && v <= 0x39       // 0-9

let is_hexdig (c: U32.t) : bool =
  is_digit c ||
  (let v = U32.v c in
   (v >= 0x41 && v <= 0x46) || // A-F
   (v >= 0x61 && v <= 0x66))   // a-f

let is_space (c: U32.t) : bool =
  let v = U32.v c in
  v = 0x20 || v = 0x09 || v = 0x0A || v = 0x0D  // space, tab, LF, CR

// PN_CHARS_BASE per W3C Turtle grammar [163s]
// [A-Z] | [a-z] | [#x00C0-#x00D6] | [#x00D8-#x00F6] | [#x00F8-#x02FF]
// | [#x0370-#x037D] | [#x037F-#x1FFF] | [#x200C-#x200D] | [#x2070-#x218F]
// | [#x2C00-#x2FEF] | [#x3001-#xD7FF] | [#xF900-#xFDCF] | [#xFDF0-#xFFFD]
// | [#x10000-#xEFFFF]
let is_pn_chars_base (c: U32.t) : bool =
  let v = U32.v c in
  is_alpha c ||
  (v >= 0x00C0 && v <= 0x00D6) ||
  (v >= 0x00D8 && v <= 0x00F6) ||
  (v >= 0x00F8 && v <= 0x02FF) ||
  (v >= 0x0370 && v <= 0x037D) ||
  (v >= 0x037F && v <= 0x1FFF) ||
  (v >= 0x200C && v <= 0x200D) ||
  (v >= 0x2070 && v <= 0x218F) ||
  (v >= 0x2C00 && v <= 0x2FEF) ||
  (v >= 0x3001 && v <= 0xD7FF) ||
  (v >= 0xF900 && v <= 0xFDCF) ||
  (v >= 0xFDF0 && v <= 0xFFFD) ||
  (v >= 0x10000 && v <= 0xEFFFF)

// PN_CHARS_U [164s] = PN_CHARS_BASE | '_'
let is_pn_chars_u (c: U32.t) : bool =
  is_pn_chars_base c || U32.v c = 0x5F  // '_'

// PN_CHARS [166s] = PN_CHARS_U | '-' | [0-9] | #x00B7
//                  | [#x0300-#x036F] | [#x203F-#x2040]
let is_pn_chars (c: U32.t) : bool =
  let v = U32.v c in
  is_pn_chars_u c ||
  v = 0x2D ||                            // '-'
  is_digit c ||
  v = 0x00B7 ||
  (v >= 0x0300 && v <= 0x036F) ||
  (v >= 0x203F && v <= 0x2040)

// Hex digit value (0-15), assumes is_hexdig is true
let hex_value (c: U32.t) : U32.t =
  let v = U32.v c in
  if v >= 0x30 && v <= 0x39 then U32.(c -^ 0x30ul)       // 0-9
  else if v >= 0x41 && v <= 0x46 then U32.(c -^ 0x37ul)   // A-F -> 10-15
  else U32.(c -^ 0x57ul)                                    // a-f -> 10-15

// Encode a codepoint as UTF-8 bytes (up to 4 bytes).
// Returns (byte0, byte1, byte2, byte3, num_bytes).
// Unused bytes are 0.
let encode_utf8 (cp: U32.t) : (U8.t & U8.t & U8.t & U8.t & U32.t) =
  let v = U32.v cp in
  if v <= 0x7F then
    (FStar.Int.Cast.uint32_to_uint8 cp, 0uy, 0uy, 0uy, 1ul)
  else if v <= 0x7FF then
    let b0 = U8.uint_to_t (0xC0 + v / 64) in
    let b1 = U8.uint_to_t (0x80 + v % 64) in
    (b0, b1, 0uy, 0uy, 2ul)
  else if v <= 0xFFFF then
    let b0 = U8.uint_to_t (0xE0 + v / 4096) in
    let b1 = U8.uint_to_t (0x80 + (v / 64) % 64) in
    let b2 = U8.uint_to_t (0x80 + v % 64) in
    (b0, b1, b2, 0uy, 3ul)
  else
    let b0 = U8.uint_to_t (0xF0 + v / 262144) in
    let b1 = U8.uint_to_t (0x80 + (v / 4096) % 64) in
    let b2 = U8.uint_to_t (0x80 + (v / 64) % 64) in
    let b3 = U8.uint_to_t (0x80 + v % 64) in
    (b0, b1, b2, b3, 4ul)
