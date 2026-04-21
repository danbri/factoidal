(* parser_fast_string_byte_semantics.ml — documents that
   Parser.FastString is a BYTE-level surface, NOT a codepoint surface.

   The fast parsers (Turtle scanner, N-Triples, etc.) rely on this: they
   lex ASCII delimiters (comma, angle bracket, colon, quote) and keywords
   using these primitives. Pretending they were codepoint-aware would
   break the fast path and force UTF-8 decoding on every hot-loop byte.

   These tests are all deliberately PASS — they're an executable
   contract. Anyone refactoring Parser.FastString later sees at a glance
   that callers expect:

     * fs_byte_length returns the number of UTF-8 bytes, not codepoints.
     * fs_byte_at returns an int 0..255 per byte, not a Unicode scalar.
     * fs_byte_sub may slice IN THE MIDDLE of a multi-byte sequence and
       the caller is responsible for only doing this on ASCII positions.
     * fs_find_byte finds a single byte value, useful for locating
       ASCII delimiters.

   If any of these assertions ever flips, the scanner hot loops need to
   be re-audited for codepoint-aware vs byte-aware behaviour. *)

let passed = ref 0
let failed = ref 0
let expected_failures = ref 0

let check ~name ~expected_pass ok_bool =
  if ok_bool then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else if not expected_pass then begin
    incr expected_failures;
    Printf.printf "  XFAIL %s  (documented limitation)\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let () =
  Printf.printf "== parser_fast_string_byte_semantics ==\n";

  (* 1. Byte length, not codepoint count.
     "ä" is U+00E4, encoded as UTF-8 bytes c3 a4 — two bytes, one
     codepoint. fs_byte_length must return 2. *)
  let a_umlaut = "\xc3\xa4" in
  let len = Z.to_int (Parser_FastString.fs_byte_length a_umlaut) in
  check ~name:"fs_byte_length \"ä\" = 2 (UTF-8 byte length, not 1 codepoint)"
    ~expected_pass:true
    (len = 2);

  (* 2. First byte of "ä" is 0xC3 (UTF-8 leading byte for U+0080..U+07FF). *)
  let b0 = Z.to_int (Parser_FastString.fs_byte_at a_umlaut (Z.of_int 0)) in
  check ~name:"fs_byte_at \"ä\" 0 = 0xC3 (UTF-8 leading byte)"
    ~expected_pass:true
    (b0 = 0xC3);

  let b1 = Z.to_int (Parser_FastString.fs_byte_at a_umlaut (Z.of_int 1)) in
  check ~name:"fs_byte_at \"ä\" 1 = 0xA4 (UTF-8 continuation byte)"
    ~expected_pass:true
    (b1 = 0xA4);

  (* 3. Byte slice can land mid-codepoint and that is BY DESIGN. The
     scanner only ever calls fs_byte_sub on ASCII delimiter boundaries
     (quotes, angle brackets, whitespace), so producing invalid UTF-8
     here is not a bug — it is the contract. Asserting this explicitly
     so a future refactor cannot silently "fix" it by decoding. *)
  let ab = "\xc3\xa4" ^ "b" in  (* "äb" = c3 a4 62 *)
  let mid = Parser_FastString.fs_byte_sub ab (Z.of_int 0) (Z.of_int 1) in
  check ~name:"fs_byte_sub \"äb\" 0 1 = \"\\xC3\" (invalid UTF-8, byte-level by design)"
    ~expected_pass:true
    (mid = "\xc3");

  (* 4. fs_find_byte locates an ASCII delimiter by byte value. Finding
     ':' (0x3A) inside "abc:def" should return 3.
     This is how the Turtle / N-Triples scanners locate prefix
     boundaries and lexical-form terminators. *)
  let s = "abc:def" in
  let idx = Z.to_int (Parser_FastString.fs_find_byte s (Z.of_int 0x3A) (Z.of_int 0)) in
  check ~name:"fs_find_byte \"abc:def\" 0x3A 0 = 3 (locate ':' as a byte)"
    ~expected_pass:true
    (idx = 3);

  (* 5. fs_find_byte returns the string length when the byte is absent. *)
  let n = Z.to_int (Parser_FastString.fs_find_byte s (Z.of_int 0x21) (Z.of_int 0)) in
  check ~name:"fs_find_byte \"abc:def\" 0x21 0 = 7 (absent = length)"
    ~expected_pass:true
    (n = String.length s);

  (* 6. A multi-byte character's leading byte is *not* confusable with
     ASCII punctuation. Specifically, 0xC3 is never a colon (0x3A), so a
     fs_find_byte-for-colon scan over Müller stops at length-of-string,
     not at byte 4 (which is 0xC3). Documenting this keeps the scanner
     contract explicit: ASCII-delimiter scans are safe on arbitrary
     UTF-8 input. *)
  let muller = "M\xc3\xbcller" in
  let colon_idx = Z.to_int (Parser_FastString.fs_find_byte muller (Z.of_int 0x3A) (Z.of_int 0)) in
  check ~name:"fs_find_byte over \"Müller\" for ':' = length (no false positive on 0xC3)"
    ~expected_pass:true
    (colon_idx = String.length muller);

  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !passed !expected_failures !failed;
  if !failed > 0 then exit 1
