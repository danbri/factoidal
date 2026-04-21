module Parser.FastString

open FStar.Char

// ============================================================================
// Byte-indexed string primitives for the parser hot path.
//
// WHY THIS MODULE EXISTS
// ----------------------
// The F* OCaml runtime's FStar.String maps length/index/sub onto BatUTF8,
// which walks the UTF-8 byte sequence on every call to count codepoints.
// Profiled cost on a 1000-triple full-IRI Turtle file: 99.9 percent of leaf
// CPU samples are inside BatUTF8.length_aux, BatUTF8.nth_aux, BatUTF8.next.
// Every inner-loop call to String.length or String.index in the Turtle
// scanner therefore costs O(n) in the input byte count, turning the
// whole parse into O(n^2).
//
// The fix is this narrow assume-val boundary: four primitives that speak
// bytes, not codepoints, and are wired in OCaml directly to String.length,
// String.unsafe_get, and String.sub. See
// minimal_regrettable_glue_code_each_with_an_open_issue/70_fast_string_primitives.sh
// for the OCaml glue, and the profile at
// docs/designissues/2026-04-20-turtle-parser-profile.md for the measurement.
//
// SAFETY
// ------
// These are byte-level operations. They are ONLY safe for parsers whose
// grammar commits on ASCII bytes and treats any multi-byte UTF-8 as opaque
// bytes inside quoted literal bodies. Turtle, N-Triples, N-Quads, and TriG
// all satisfy this: whitespace, delimiters, keywords, escapes, number
// formats, and IRI-reference brackets are all ASCII. Multi-byte UTF-8
// appears only inside "..." and <...> bodies which we extract as raw
// substrings and hand back to the caller without inspecting the bytes.
//
// If your parser needs codepoint semantics (e.g. to enforce a Unicode
// character-class precondition over the entire input, not just the
// delimiter set), these primitives are the wrong tool. Stay on
// FStar.String for that use.
//
// COST MODEL (in the extracted OCaml)
// -----------------------------------
// fs_byte_length : O(1)          -- reads the OCaml string's byte length
// fs_byte_at     : O(1)          -- one String.unsafe_get
// fs_byte_sub    : O(len)        -- a single String.sub allocation
// fs_find_byte   : O(end - start)-- scans bytes for one specific code
// ============================================================================

// Byte length of the UTF-8 encoding of s. Differs from
// FStar.String.length (codepoint count) by being O(1).
assume val fs_byte_length : string -> nat

// Byte at index i (0 <= i < fs_byte_length s), as a nat in [0, 255].
// NOT a codepoint -- a raw byte. Callers must UTF-8-decode if they
// need codepoint semantics.
assume val fs_byte_at : s:string -> i:nat -> n:nat{n < 256}

// Substring by BYTE indices. start + len must be <= fs_byte_length s;
// we don't encode that as a refinement because the OCaml glue is
// permissive (String.sub clamps via its own bounds check).
assume val fs_byte_sub : s:string -> start:nat -> len:nat -> string

// Find the first occurrence of byte b at or after position start.
// Returns fs_byte_length s if not found.
assume val fs_find_byte : s:string -> b:nat -> start:nat -> nat

// ---------------------------------------------------------------------------
// Convenience: return the byte at position i as an FStar.Char.char, so
// existing call sites that do "let c = String.index input pos in
// let code = int_of_char c in ..." can keep their downstream code by
// using fs_byte_index instead. The char will carry the numeric code in
// its Char.int_of_char representation -- the same way String.index did
// before, for ASCII inputs.
//
// SAFETY: char_of_int's F* precondition is (c < 0xD800). A raw byte is
// always < 256 < 0xD800, so this is total without an explicit refinement
// check. We still write the refinement out to help the SMT solver.
// ---------------------------------------------------------------------------
let fs_byte_index (s: string) (i: nat) : char =
  let b = fs_byte_at s i in
  // b is a byte, so 0 <= b <= 255 < 0xD800; safe for char_of_int.
  if b < 0xD800 then char_of_int b else char_of_int 0

// Convenience: char-returning version for call sites that don't want to
// deal with nat. Matches the String.index surface.
let fs_char_at (s: string) (i: nat) : char = fs_byte_index s i
