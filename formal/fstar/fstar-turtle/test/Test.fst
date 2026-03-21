module Test

// F*-level tests for the streaming Turtle parser modules.
// These verify properties statically (at typechecking time)
// rather than at runtime.

open Utf8
module U8 = FStar.UInt8
module U32 = FStar.UInt32

// ---- UTF-8 byte count tests ----

// ASCII: 1 byte
let _ = assert_norm (utf8_num_bytes 0x41uy = 1ul)   // 'A'
let _ = assert_norm (utf8_num_bytes 0x00uy = 1ul)   // NUL
let _ = assert_norm (utf8_num_bytes 0x7Fuy = 1ul)   // DEL

// 2-byte: 0xC0-0xDF
let _ = assert_norm (utf8_num_bytes 0xC3uy = 2ul)   // a-umlaut lead
let _ = assert_norm (utf8_num_bytes 0xDFuy = 2ul)   // max 2-byte lead

// 3-byte: 0xE0-0xEF
let _ = assert_norm (utf8_num_bytes 0xE4uy = 3ul)   // CJK lead
let _ = assert_norm (utf8_num_bytes 0xEFuy = 3ul)   // max 3-byte lead

// 4-byte: 0xF0-0xF7
let _ = assert_norm (utf8_num_bytes 0xF0uy = 4ul)   // emoji lead
let _ = assert_norm (utf8_num_bytes 0xF4uy = 4ul)   // max valid 4-byte

// Invalid: continuation bytes
let _ = assert_norm (utf8_num_bytes 0x80uy = 0ul)
let _ = assert_norm (utf8_num_bytes 0xBFuy = 0ul)

// Invalid: 5-byte+ sequences
let _ = assert_norm (utf8_num_bytes 0xF8uy = 0ul)
let _ = assert_norm (utf8_num_bytes 0xFFuy = 0ul)

// ---- UTF-8 bytes for codepoint tests ----

let _ = assert_norm (utf8_bytes_for_codepoint 0x41ul = 1ul)      // 'A'
let _ = assert_norm (utf8_bytes_for_codepoint 0x7Ful = 1ul)      // max ASCII
let _ = assert_norm (utf8_bytes_for_codepoint 0x80ul = 2ul)      // min 2-byte
let _ = assert_norm (utf8_bytes_for_codepoint 0x7FFul = 2ul)     // max 2-byte
let _ = assert_norm (utf8_bytes_for_codepoint 0x800ul = 3ul)     // min 3-byte
let _ = assert_norm (utf8_bytes_for_codepoint 0xFFFFul = 3ul)    // max 3-byte
let _ = assert_norm (utf8_bytes_for_codepoint 0x10000ul = 4ul)   // min 4-byte (emoji)
let _ = assert_norm (utf8_bytes_for_codepoint 0x10FFFFul = 4ul)  // max Unicode
let _ = assert_norm (utf8_bytes_for_codepoint 0x110000ul = 0ul)  // out of range

// ---- Character classification tests ----

// is_alpha
let _ = assert_norm (is_alpha 0x41ul = true)   // 'A'
let _ = assert_norm (is_alpha 0x5Aul = true)   // 'Z'
let _ = assert_norm (is_alpha 0x61ul = true)   // 'a'
let _ = assert_norm (is_alpha 0x7Aul = true)   // 'z'
let _ = assert_norm (is_alpha 0x30ul = false)  // '0'
let _ = assert_norm (is_alpha 0x40ul = false)  // '@'

// is_digit
let _ = assert_norm (is_digit 0x30ul = true)   // '0'
let _ = assert_norm (is_digit 0x39ul = true)   // '9'
let _ = assert_norm (is_digit 0x41ul = false)  // 'A'

// is_hexdig
let _ = assert_norm (is_hexdig 0x30ul = true)   // '0'
let _ = assert_norm (is_hexdig 0x39ul = true)   // '9'
let _ = assert_norm (is_hexdig 0x41ul = true)   // 'A'
let _ = assert_norm (is_hexdig 0x46ul = true)   // 'F'
let _ = assert_norm (is_hexdig 0x61ul = true)   // 'a'
let _ = assert_norm (is_hexdig 0x66ul = true)   // 'f'
let _ = assert_norm (is_hexdig 0x47ul = false)  // 'G'

// is_pn_chars_base: letters and Unicode ranges
let _ = assert_norm (is_pn_chars_base 0x41ul = true)      // 'A'
let _ = assert_norm (is_pn_chars_base 0x30ul = false)     // '0' not base
let _ = assert_norm (is_pn_chars_base 0xC0ul = true)      // Latin ext
let _ = assert_norm (is_pn_chars_base 0x0370ul = true)    // Greek
let _ = assert_norm (is_pn_chars_base 0x3001ul = true)    // CJK

// is_pn_chars_u: base + underscore
let _ = assert_norm (is_pn_chars_u 0x5Ful = true)         // '_'
let _ = assert_norm (is_pn_chars_u 0x41ul = true)         // 'A'
let _ = assert_norm (is_pn_chars_u 0x2Dul = false)        // '-' not in U

// is_pn_chars: U + '-' + digits + special ranges
let _ = assert_norm (is_pn_chars 0x2Dul = true)           // '-'
let _ = assert_norm (is_pn_chars 0x30ul = true)           // '0'
let _ = assert_norm (is_pn_chars 0xB7ul = true)           // middle dot
let _ = assert_norm (is_pn_chars 0x0300ul = true)         // combining
let _ = assert_norm (is_pn_chars 0x203Ful = true)         // undertie

// is_space
let _ = assert_norm (is_space 0x20ul = true)    // space
let _ = assert_norm (is_space 0x09ul = true)    // tab
let _ = assert_norm (is_space 0x0Aul = true)    // LF
let _ = assert_norm (is_space 0x0Dul = true)    // CR
let _ = assert_norm (is_space 0x41ul = false)   // 'A'

// ---- Codepoint validity tests ----

// Valid ASCII
let _ = assert_norm (is_valid_codepoint 0x41ul 1ul = true)
// Valid 2-byte
let _ = assert_norm (is_valid_codepoint 0xE9ul 2ul = true)    // e-acute
// Surrogate (invalid)
let _ = assert_norm (is_valid_codepoint 0xD800ul 3ul = false)
let _ = assert_norm (is_valid_codepoint 0xDFFFul 3ul = false)
// Above max (invalid)
let _ = assert_norm (is_valid_codepoint 0x110000ul 4ul = false)
// Overlong 2-byte for ASCII (invalid)
let _ = assert_norm (is_valid_codepoint 0x41ul 2ul = false)
// Overlong 3-byte for 2-byte range (invalid)
let _ = assert_norm (is_valid_codepoint 0x80ul 3ul = false)

// ---- Hex value tests ----

let _ = assert_norm (hex_value 0x30ul = 0ul)    // '0' -> 0
let _ = assert_norm (hex_value 0x39ul = 9ul)    // '9' -> 9
let _ = assert_norm (hex_value 0x41ul = 10ul)   // 'A' -> 10
let _ = assert_norm (hex_value 0x46ul = 15ul)   // 'F' -> 15
let _ = assert_norm (hex_value 0x61ul = 10ul)   // 'a' -> 10
let _ = assert_norm (hex_value 0x66ul = 15ul)   // 'f' -> 15
