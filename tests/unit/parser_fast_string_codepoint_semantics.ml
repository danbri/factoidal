(* parser_fast_string_codepoint_semantics.ml -- documents the Pass-2
   Parser.FastString primitives (issue #89).

   Parser.FastString.fs_byte_* stay BYTE-level (see
   parser_fast_string_byte_semantics.ml). The new fs_cp_at / fs_cp_len
   primitives decode UTF-8 codepoints and are used by PN_CHARS validation
   in the Turtle parser so multibyte identifiers (e.g. "ä", "日", "🎵")
   aren't rejected byte-by-byte.

   Invalid or truncated UTF-8 returns (0xFFFD, 1) -- emit the Unicode
   replacement character and advance exactly one byte so caller loops
   always make forward progress.

   All assertions here are deliberately PASS; they are an executable
   contract on the decoder's behaviour. *)

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

let cp_at s pos =
  let (cp, adv) = Parser_FastString.fs_cp_at s (Z.of_int pos) in
  (Z.to_int cp, Z.to_int adv)

let cp_len s pos =
  Z.to_int (Parser_FastString.fs_cp_len s (Z.of_int pos))

let () =
  Printf.printf "== parser_fast_string_codepoint_semantics ==\n";

  (* 1. ASCII: one byte, codepoint = byte value. *)
  let (cp, adv) = cp_at "a" 0 in
  check ~name:"fs_cp_at \"a\" 0 = (0x61, 1)"
    ~expected_pass:true (cp = 0x61 && adv = 1);

  (* 2. Two-byte UTF-8: U+00E4 LATIN SMALL LETTER A WITH DIAERESIS ("\xc3\xa4"). *)
  let (cp, adv) = cp_at "\xc3\xa4" 0 in
  check ~name:"fs_cp_at \"ä\" 0 = (0xE4, 2)"
    ~expected_pass:true (cp = 0xE4 && adv = 2);

  (* 3. Three-byte UTF-8: U+65E5 ("日" = e6 97 a5). *)
  let (cp, adv) = cp_at "\xe6\x97\xa5" 0 in
  check ~name:"fs_cp_at \"日\" 0 = (0x65E5, 3)"
    ~expected_pass:true (cp = 0x65E5 && adv = 3);

  (* 4. Four-byte UTF-8: U+1F3B5 ("🎵" = f0 9f 8e b5). *)
  let (cp, adv) = cp_at "\xf0\x9f\x8e\xb5" 0 in
  check ~name:"fs_cp_at \"🎵\" 0 = (0x1F3B5, 4)"
    ~expected_pass:true (cp = 0x1F3B5 && adv = 4);

  (* 5. Empty input or past-end: replacement char, advance 1. Caller is
     supposed to bounds-check but the decoder must be defensive so loops
     can't run off the end. *)
  let (cp, adv) = cp_at "" 0 in
  check ~name:"fs_cp_at \"\" 0 = (0xFFFD, 1) (empty input fallback)"
    ~expected_pass:true (cp = 0xFFFD && adv = 1);

  (* 6. Invalid leading byte 0xC0 (overlong pair): replacement + advance 1. *)
  let (cp, adv) = cp_at "\xc0" 0 in
  check ~name:"fs_cp_at \"\\xC0\" 0 = (0xFFFD, 1) (invalid leading byte)"
    ~expected_pass:true (cp = 0xFFFD && adv = 1);

  (* 7. Truncated two-byte sequence: leading byte 0xC3 with no
     continuation -> (0xFFFD, 1), so the scanner advances past the
     broken byte without looping forever. *)
  let (cp, adv) = cp_at "\xc3" 0 in
  check ~name:"fs_cp_at \"\\xC3\" 0 = (0xFFFD, 1) (truncated two-byte)"
    ~expected_pass:true (cp = 0xFFFD && adv = 1);

  (* 8. UTF-16 surrogate encoded as raw 3-byte UTF-8 (invalid per RFC
     3629). ed a0 80 decodes to U+D800 which must be rejected. *)
  let (cp, adv) = cp_at "\xed\xa0\x80" 0 in
  check ~name:"fs_cp_at \"\\xED\\xA0\\x80\" 0 = (0xFFFD, 1) (UTF-16 surrogate rejected)"
    ~expected_pass:true (cp = 0xFFFD && adv = 1);

  (* 9. fs_cp_len matches fs_cp_at's second element without paying for
     the codepoint's Z allocation. *)
  let n = cp_len "\xc3\xa4" 0 in
  check ~name:"fs_cp_len \"ä\" 0 = 2"
    ~expected_pass:true (n = 2);

  let n = cp_len "\xf0\x9f\x8e\xb5" 0 in
  check ~name:"fs_cp_len \"🎵\" 0 = 4"
    ~expected_pass:true (n = 4);

  (* 10. Decoding at a mid-byte position is callable; the caller is
     responsible for aligning pos to a codepoint start. This test
     documents that stepping onto a continuation byte yields the
     replacement marker, so a loop that sees an unexpected (0xFFFD, 1)
     can diagnose its own misuse rather than crash. *)
  let (cp, adv) = cp_at "\xc3\xa4" 1 in
  check ~name:"fs_cp_at \"ä\" 1 = (0xFFFD, 1) (starting on a continuation byte)"
    ~expected_pass:true (cp = 0xFFFD && adv = 1);

  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !passed !expected_failures !failed;
  if !failed > 0 then exit 1
