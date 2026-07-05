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

   Issue #277 (fixed here): `{0,m}` bounded repetition with a zero
   minimum did not make the underlying atom optional, because the
   atom was unconditionally emitted once by the main loop before the
   `{...}` quantifier was even parsed, and the "for 2 to n"
   mandatory-copy loop only added *additional* copies beyond that
   unconditional first one. For n=0 that first occurrence should
   have been optional but wasn't (`ab{0,2}c` rejected `ac`). `{1,m}`
   and higher were already correct (still pinned below).

   Fix: xpath_to_str_regex now tracks `last_atom_start` (the buffer
   position right before the most recently completed atom was
   written) and rolls the eager first copy back
   (`Buffer.truncate buf !last_atom_start`) before rebuilding the
   `{n,m}`/`{n,}`/`{n}` expansion from `n` and `m` directly, instead
   of patching around the pre-existing copy. This also fixes the
   `{0}` exact-count case (previously left one mandatory copy
   behind) and, as a side effect, fixes group-atom text capture:
   `last_atom` for a `(...)` group now holds the group's FULL regex
   text (tracked via a `group_starts` stack, nesting-safe) instead of
   just the closing `\)`, so `(ab){0,2}` correctly re-emits the whole
   group per repeated copy instead of stray close-parens.

   Outside-BMP / surrogate-pair characterization (found while
   triaging ShEx validation mismatches tagged traits
   NumericEquivalence + OutsideBMP, e.g. the shexTest
   `1literalPattern_with_UTF8_boundaries` and `..._REGEXP_escapes`
   fixtures under third_party/testing/shex/validation/): literal
   outside-BMP UTF-8 byte sequences embedded directly in a pattern
   (no `\uXXXX`/`\UXXXXXXXX` escape text — the ShExJ fixtures already
   arrive with the escape resolved to the real codepoint by the JSON
   layer) match correctly with NO change needed, because UTF-8
   lead/continuation bytes (0x80-0xF4) never collide with an ASCII
   regex metacharacter — pinned below. The actual defect the
   "OutsideBMP"-tagged fixtures were tripping over was unrelated to
   BMP-range bytes at all: the XSD/XPath regex SingleCharEsc control
   escapes `\n` `\r` `\t` were not translated to real control bytes.
   OCaml's Str module has no notion of these
   (`Str.regexp "\\t"` matches the literal letter `t`, not a tab
   byte) — without translation, a pattern containing textual `\t`
   never matches data containing an actual tab byte. The
   shexTest "REGEXP_escapes" fixtures combine these control escapes
   with an astral character in one pattern (hence the OutsideBMP
   trait tag on a fixture that isn't really testing BMP-range
   matching). Fixed by translating `\n`/`\r`/`\t` to their real
   control bytes in xpath_to_str_regex; `\-` was already handled
   correctly for free (Str treats an escaped ordinary character as
   that literal character). NOT attempted here: `\b`/`\f` in the
   ShEx `_escaped` fixture family (ambiguous — `\b` is a word-boundary
   assertion in some regex dialects and a backspace ECHAR in Turtle
   strings; XSD/XPath regex's SingleCharEsc doesn't define it at
   all) and ShExC-syntax (`.shex`, not `.json`) `\uXXXX`/`\UXXXXXXXX`
   codepoint-escape decoding, since the current ShExJ-first
   validator (docs/designissues/2026-07-05-shex-program-plan.md)
   never hands xpath_to_str_regex raw ShExC escape text — the JSON
   layer already resolves it before the pattern reaches this glue.
   Tracked as a follow-up in the #277 comment thread.

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

  (* --- {n,m} bounded repetition (n >= 1) --- *)
  check ~name:"{n,m} below range" false (m "abc" "a{2,3}");
  check ~name:"{n,m} at minimum" true (m "aab" "a{2,3}b");
  check ~name:"{n,m} at maximum" true (m "aaab" "a{2,3}b");
  check ~name:"{n,m} below minimum with suffix" false (m "ab" "a{2,3}b");
  check ~name:"{1,m} optional-extra works" true (m "aab" "a{1,2}b");

  (* --- #277: {0,m} bounded repetition with a zero minimum --- *)
  (* atom, with a literal prefix + suffix around the quantified atom *)
  check ~name:"{0,m} atom, absent (min=0 makes it optional)"
    true (m "ac" "ab{0,2}c");
  check ~name:"{0,m} atom, present once" true (m "abc" "ab{0,2}c");
  check ~name:"{0,m} atom, present at max" true (m "abbc" "ab{0,2}c");
  check ~name:"{0,m} atom, over max fails" false (m "abbbc" "ab{0,2}c");

  (* group: last_atom must capture the FULL "(ab)" group text, not
     just the closing "\)", or repeated copies emit stray parens *)
  check ~name:"{0,m} group, absent" true (m "c" "(ab){0,2}c");
  check ~name:"{0,m} group, present once" true (m "abc" "(ab){0,2}c");
  check ~name:"{0,m} group, present at max" true (m "ababc" "(ab){0,2}c");
  (* anchored: regex_match is an unanchored substring search
     (Str.search_forward), so without ^...$ the suffix "ababc" of
     "abababc" would still satisfy "(ab){0,2}c" starting two
     characters in — this isn't an over-max bug, it's what substring
     search means. Anchor to test the over-max rejection itself. *)
  check ~name:"{0,m} group, over max fails"
    false (m "abababc" "^(ab){0,2}c$");

  (* {0,1} must behave identically to `?` *)
  check ~name:"{0,1} absent, same as ?" true (m "b" "a{0,1}b");
  check ~name:"{0,1} present, same as ?" true (m "ab" "a{0,1}b");
  (* anchored: unanchored, "aab"'s suffix "ab" alone would satisfy
     "a{0,1}b" regardless of the leading extra 'a' — substring search,
     not a {0,1} bug. Anchor to test the over-max rejection itself. *)
  check ~name:"{0,1} rejects doubled, same as ?"
    false (m "aab" "^a{0,1}b$");
  check ~name:"? absent (cross-check against {0,1})" true (m "b" "a?b");
  check ~name:"? present (cross-check against {0,1})" true (m "ab" "a?b");

  (* {0,0}: the atom must never appear at all. Rejection cases are
     anchored for the same substring-search reason as above — "ab"
     unanchored still contains the bare "b" substring satisfying
     "a{0,0}b". *)
  check ~name:"{0,0} forces absence" true (m "b" "a{0,0}b");
  check ~name:"{0,0} rejects a single occurrence"
    false (m "ab" "^a{0,0}b$");
  (* exact-count {0} (no comma) shares the same eager-first-copy root
     cause and is fixed by the same rebuild-from-truncate logic *)
  check ~name:"{0} exact-count forces absence" true (m "b" "a{0}b");
  check ~name:"{0} exact-count rejects a single occurrence"
    false (m "ab" "^a{0}b$");

  (* prefix/suffix positioning: quantified atom at the very start or
     very end of the pattern, anchored so an over-count is rejected *)
  check ~name:"{0,m} prefix position, absent" true (m "c" "^a{0,2}c$");
  check ~name:"{0,m} prefix position, at max" true (m "aac" "^a{0,2}c$");
  check ~name:"{0,m} prefix position, over max fails"
    false (m "aaac" "^a{0,2}c$");
  check ~name:"{0,m} suffix position, absent" true (m "b" "^ba{0,2}$");
  check ~name:"{0,m} suffix position, at max" true (m "baa" "^ba{0,2}$");
  check ~name:"{0,m} suffix position, over max fails"
    false (m "baaa" "^ba{0,2}$");

  (* --- outside-BMP / astral characters: characterized while triaging
     ShEx validation mismatches tagged traits NumericEquivalence +
     OutsideBMP (see the file-header comment). A literal multi-byte
     UTF-8 sequence embedded directly in the pattern (no \uXXXX
     escape text) matches correctly with NO change — UTF-8
     lead/continuation bytes never collide with an ASCII regex
     metacharacter. Bytes below are U+1D4B8 MATHEMATICAL SCRIPT SMALL
     C, taken from the real shexTest fixture
     third_party/testing/shex/schemas/1literalPattern_with_UTF8_boundaries.json
     (the ShExJ "pattern" field, already codepoint-resolved). --- *)
  check ~name:"outside-BMP literal astral char matches byte-for-byte"
    true (m "\xf0\x9d\x92\xb8" "^\xf0\x9d\x92\xb8$");
  check ~name:"outside-BMP literal astral char rejects extra suffix"
    false (m "\xf0\x9d\x92\xb8x" "^\xf0\x9d\x92\xb8$");

  (* --- \n \r \t control-char escapes: the actual root cause behind
     the "OutsideBMP"-tagged ShEx REGEXP_escapes mismatches (not
     BMP-range byte matching — that already worked, see above). Str
     has no built-in notion of these XSD/XPath SingleCharEsc escapes,
     so without translation "\t" matches the literal letter 't'
     instead of a tab byte. --- *)
  check ~name:"\\t escape matches an actual TAB byte" true (m "\t" "\\t");
  check ~name:"\\t escape rejects the literal letter t" false (m "t" "\\t");
  check ~name:"\\n escape matches an actual LF byte" true (m "\n" "\\n");
  check ~name:"\\n escape rejects the literal letter n" false (m "n" "\\n");
  check ~name:"\\r escape matches an actual CR byte" true (m "\r" "\\r");
  check ~name:"\\r escape rejects the literal letter r" false (m "r" "\\r");
  (* the real fixture: shexTest 1literalPattern_with_REGEXP_escapes —
     pattern "^/\t\n\r\-\\a<astral>$" (control escapes + a literal
     backslash + astral char) against Turtle-string-unescaped data
     "/" ^ TAB ^ LF ^ CR ^ "-\\a<astral>", both pulled from
     third_party/testing/shex/validation/manifest.ttl's
     "1literalPattern_with_REGEXP_escapes" pass/fail pair. *)
  check ~name:"ShEx REGEXP_escapes fixture: control escapes + astral char"
    true
    (m ("/" ^ "\t" ^ "\n" ^ "\r" ^ "-" ^ "\\" ^ "a" ^ "\xf0\x9d\x92\xb8")
       ("^/" ^ "\\t" ^ "\\n" ^ "\\r" ^ "\\-" ^ "\\\\" ^ "a" ^ "\xf0\x9d\x92\xb8" ^ "$"));
  check ~name:"ShEx REGEXP_escapes fixture: rejects the _999 suffix variant"
    false
    (m ("/" ^ "\t" ^ "\n" ^ "\r" ^ "-" ^ "\\" ^ "a" ^ "\xf0\x9d\x92\xb8" ^ "999")
       ("^/" ^ "\\t" ^ "\\n" ^ "\\r" ^ "\\-" ^ "\\\\" ^ "a" ^ "\xf0\x9d\x92\xb8" ^ "$"));

  Printf.printf "regex_match_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
