(* regex_match_unit.ml — pins the semantics of
   SPARQL11_Algebra.regex_match (the OCaml realisation of the
   `assume val regex_match` in SPARQL11.Algebra.fst, patched in by
   formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
   63_regex_hash_uuid_stubs.sh).

   Issue #276: the XPath/ECMAScript -> OCaml Str translation
   (xpath_to_str_regex) mistranslated the `?` optional quantifier.
   Reproducer: regex_match "http" "https?" returned false (must be
   true — the trailing "s" is optional).

   Root cause: OCaml's Str module uses the OPPOSITE escaping
   convention from XPath/ECMAScript for two different feature
   classes:
     - Grouping/alternation `( ) |` are LITERAL when bare in Str and
       SPECIAL only when escaped (`\( \) \|`) — same escaped-in-Str
       shape that the XPath/ECMAScript form uses unescaped, so the
       existing swap (bare <-> escaped) is correct for these three.
     - Quantifiers `? + *` are SPECIAL when bare in Str (same as
       XPath/ECMAScript) and LITERAL only when escaped (`\? \+ \*`).
   The old code applied the grouping/alternation swap to ALL seven
   characters, including the quantifiers. That flipped `?` (meant as
   "optional") into `\?` (Str literal question mark) and flipped an
   escaped `\?` (meant as literal) into bare `?` (Str quantifier) —
   backwards in both directions. Same bug for `+` and `*`, and for
   the synthesized `\?` used internally when expanding `{n,m}` bounded
   repetition into repeated-optional atoms.

   Fix (in 63_regex_hash_uuid_stubs.sh's embedded xpath_to_str_regex):
     - bare `?`/`+`/`*` now pass through unescaped (Str quantifier,
       matching XPath/ECMAScript semantics 1:1) instead of being
       escaped into Str literals.
     - escaped `\?`/`\+`/`\*` (literal char desired) now emit the
       escaped Str form (`\?`, `\+`, `\*`) instead of bare chars,
       so they stay literal instead of becoming Str quantifiers.
     - the `{n,m}` bounded-repetition expansion's internal optional
       marker now emits bare `?` instead of `\?`.
   `( ) | { }` handling (grouping/alternation, and brace literals)
   is unchanged — Str has no `{n,m}` syntax at all, so bare `{`/`}`
   were already literal and correctly left alone.

   Known separate limitation (NOT fixed here, out of #276's scope):
   `{0,m}` bounded repetition with a zero minimum does not make the
   underlying atom optional, because the atom is unconditionally
   emitted once by the main loop before the `{...}` quantifier is
   even parsed, and the "for 2 to n" mandatory-copy loop only adds
   *additional* copies beyond that unconditional first one. For
   n=0 that first occurrence should itself have been optional but
   isn't. `{1,m}` and higher work correctly (tested below); `{0,m}`
   is a distinct defect in the mandatory/optional counting, not in
   the quantifier-escaping translation this issue is about. Track
   separately if it needs a fix.

   Contract note (anti-pattern #10): OCaml's Str module matches on
   bytes, not codepoints. regex_match's non-ASCII case below documents
   the current (substring/byte-level) contract rather than asserting
   full codepoint-aware semantics — this glue does not claim Unicode
   character-class correctness beyond what Str's byte matching gives
   for free on literal (non-class) UTF-8 substrings. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %b got %b\n" name expected actual
  end

let m ?flags text pattern =
  let flags =
    match flags with
    | None -> FStar_Pervasives_Native.None
    | Some f -> FStar_Pervasives_Native.Some f
  in
  SPARQL11_Algebra.regex_match text pattern flags

let () =
  (* --- The exact #276 reproducer --- *)
  check ~name:"#276 reproducer: http vs https?" true (m "http" "https?");
  check ~name:"https matches https?" true (m "https" "https?");
  check ~name:"httpsx anchored miss" false (m "httpsx" "^https?$");

  (* --- `?` after a single literal --- *)
  check ~name:"? after literal, present" true (m "abc" "ab?c");
  check ~name:"? after literal, absent" true (m "ac" "ab?c");
  check ~name:"? after literal, doubled (no match)" false (m "abbc" "ab?c");
  check ~name:"colour/color via ?" true (m "color" "colou?r");
  check ~name:"colour/color via ? (long form)" true (m "colour" "colou?r");

  (* --- `?` after a group --- *)
  check ~name:"? after group, present" true (m "abab" "(ab)?ab");
  check ~name:"? after group, absent" true (m "ab" "(ab)?ab");

  (* --- `+` --- *)
  check ~name:"+ one-or-more, matches" true (m "aaa" "a+");
  check ~name:"+ one-or-more, empty fails" false (m "" "a+");

  (* --- `*` --- *)
  check ~name:"* zero-or-more, empty matches" true (m "" "a*");
  check ~name:"* zero-or-more, many matches" true (m "aaa" "a*");

  (* --- alternation --- *)
  check ~name:"alternation left" true (m "cat" "cat|dog");
  check ~name:"alternation right" true (m "dog" "cat|dog");
  check ~name:"alternation miss" false (m "fish" "cat|dog");

  (* --- anchors ^ $ --- *)
  check ~name:"anchored exact match" true (m "abc" "^abc$");
  check ~name:"anchored prefix junk fails" false (m "xabc" "^abc$");
  check ~name:"anchored suffix junk fails" false (m "abcx" "^abc$");

  (* --- character classes --- *)
  check ~name:"character class" true (m "a1_" "[a-z0-9_]+");

  (* --- escaped metacharacters: must stay LITERAL, not become
     Str quantifiers/groups (this is the other half of #276's bug —
     the escaped-input branch mapped `\?`/`\+`/`\*` to bare Str
     quantifiers instead of literal escapes). --- *)
  check ~name:"escaped dot, literal match" true (m "a.b" "a\\.b");
  check ~name:"escaped dot rejects wildcard use" false (m "axb" "a\\.b");
  check ~name:"escaped ? is literal" true (m "a?b" "a\\?b");
  check ~name:"escaped ? does not become optional" false (m "ab" "a\\?b");
  check ~name:"escaped + is literal" true (m "a+b" "a\\+b");
  check ~name:"escaped + does not become quantifier" false (m "ab" "a\\+b");
  check ~name:"escaped * is literal" true (m "a*b" "a\\*b");
  check ~name:"escaped * does not become quantifier" false (m "ab" "a\\*b");

  (* --- non-ASCII subject strings: Str is byte-oriented (anti-pattern
     #10). A literal non-ASCII substring still matches byte-for-byte;
     this documents the current contract rather than asserting
     codepoint-aware class semantics. --- *)
  check ~name:"non-ASCII literal substring (byte-level)"
    true (m "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e" "\xe6\x9c\xac");

  (* --- case-insensitive flag --- *)
  check ~name:"case-insensitive with optional quantifier"
    true (m ~flags:"i" "HTTP" "https?");
  check ~name:"case-insensitive full match"
    true (m ~flags:"i" "HTTPS" "https?");
  check ~name:"case-sensitive default rejects case mismatch"
    false (m "HTTPS" "https?");

  (* --- {n,m} bounded repetition (n >= 1; see the {0,m} limitation
     note above the top of this file for the n=0 case) --- *)
  check ~name:"{n,m} below range" false (m "abc" "a{2,3}");
  check ~name:"{n,m} at minimum" true (m "aab" "a{2,3}b");
  check ~name:"{n,m} at maximum" true (m "aaab" "a{2,3}b");
  check ~name:"{n,m} below minimum with suffix" false (m "ab" "a{2,3}b");
  check ~name:"{1,m} optional-extra works" true (m "aab" "a{1,2}b");

  Printf.printf "regex_match_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
