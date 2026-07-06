(* ucase_lcase_unicode.ml — pins SPARQL UCASE()/LCASE()'s Unicode-aware
   case mapping (issue #250 fix). Supersedes the retired
   ucase_lcase_ascii_only.ml, which pinned the OLD ASCII-only bug
   (FStar.String.uppercase/lowercase realised as
   BatString.uppercase_ascii/lowercase_ascii — every non-ASCII
   codepoint passed through unchanged, so "Müller" upper-cased to
   "MüLLER").

   SPARQL11.Algebra.string_upper / string_lower now call the assume
   vals string_uppercase_unicode / string_lowercase_unicode, realised
   in minimal_regrettable_glue_code_each_with_an_open_issue/
   250_unicode_case_mapping.sh via the `uucp` opam package
   (uucp.17.0.0, Unicode Character Database case-mapping tables).
   `Uucp.Case.Map.to_upper`/`to_lower` return the Unicode
   Uppercase_Mapping/Lowercase_Mapping property, which already folds
   in SpecialCasing.txt's unconditional multi-character mappings
   (that's why "straße" correctly expands to "STRASSE", not "STRAßE").

   We exercise the underlying primitive the evaluator uses
   (SPARQL11_Algebra.string_upper / string_lower) directly, same as
   the retired ascii-only test did, so this stays a fast native unit
   test with no query-evaluation machinery involved.

   Honest limitation pinned here too, not swept under the rug:
   `Uucp.Case.Map.to_upper`/`to_lower` are *simple* per-codepoint
   mappings, not the full Unicode default case algorithm -- capital
   sigma (Σ) lowercases to regular sigma (σ) even at a word boundary,
   where the context-sensitive rule would produce final sigma (ς).
   SPARQL 1.1 does not specify a collation/locale parameter for
   UCASE/LCASE, so this is in scope with the spec, but it IS a real
   difference from "true" Unicode-aware lowercasing and should not be
   silently assumed away. If this assertion starts failing, either
   uucp gained context-sensitive folding (nice — update the comment)
   or something else changed the sigma mapping (investigate). *)

let passed = ref 0
let failed = ref 0

let check ~name ok_bool =
  if ok_bool then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let hex_of_string s =
  let b = Buffer.create (String.length s * 3) in
  String.iter (fun c ->
    Buffer.add_string b (Printf.sprintf "%02x " (Char.code c))
  ) s;
  String.trim (Buffer.contents b)

let check_eq ~name ~got ~want =
  check ~name (got = want);
  if got <> want then
    Printf.printf "      got:      %s\n      got hex:  %s\n      want hex: %s\n"
      got (hex_of_string got) (hex_of_string want)

let () =
  Printf.printf "== ucase_lcase_unicode ==\n";

  (* 1. Plain ASCII round-trip — baseline, unchanged by the fix. *)
  check_eq ~name:"ucase ascii 'hello' -> 'HELLO'"
    ~got:(SPARQL11_Algebra.string_upper "hello") ~want:"HELLO";
  check_eq ~name:"lcase ascii 'HELLO' -> 'hello'"
    ~got:(SPARQL11_Algebra.string_lower "HELLO") ~want:"hello";

  (* 2. The issue #250 motivating example: "Müller" (ü = U+00FC,
     UTF-8 c3 bc) now correctly upper-cases to "MÜLLER" (Ü = U+00DC,
     UTF-8 c3 9c) instead of the old ASCII-only passthrough. *)
  let input_muller = "Eve M\xc3\xbcller" in (* "Eve Müller" *)
  check_eq ~name:"ucase 'Eve Müller' -> 'EVE MÜLLER' (ü -> Ü)"
    ~got:(SPARQL11_Algebra.string_upper input_muller)
    ~want:"EVE M\xc3\x9cLLER";
  check_eq ~name:"lcase 'Eve Müller' -> 'eve müller' (ü stays ü)"
    ~got:(SPARQL11_Algebra.string_lower input_muller)
    ~want:"eve m\xc3\xbcller";

  (* 3. The hard case from the issue: German ß (U+00DF, UTF-8 c3 9f)
     upper-cases to the TWO-CHARACTER "SS", not the single capital
     sharp-s ẞ (U+1E9E). This is Unicode's own Uppercase_Mapping
     property (folds in SpecialCasing.txt's unconditional multi-char
     mappings) and matches XPath fn:upper-case's expected output for
     "straße". Pin the honest length change (5 codepoints in, 7 ASCII
     bytes out for the STRASSE tail) rather than assuming 1:1. *)
  check_eq ~name:"ucase 'straße' -> 'STRASSE' (ß -> SS, the hard case)"
    ~got:(SPARQL11_Algebra.string_upper "stra\xc3\x9fe")
    ~want:"STRASSE";
  check_eq ~name:"lcase 'STRASSE' -> 'strasse' (no reverse ß-folding — correct, not a bug)"
    ~got:(SPARQL11_Algebra.string_lower "STRASSE")
    ~want:"strasse";

  (* 4. "é" (U+00E9, UTF-8 c3 a9) <-> "É" (U+00C9, UTF-8 c3 89). *)
  check_eq ~name:"ucase 'étude' -> 'ÉTUDE' (é -> É)"
    ~got:(SPARQL11_Algebra.string_upper "\xc3\xa9tude")
    ~want:"\xc3\x89TUDE";
  check_eq ~name:"lcase 'ÉTUDE' -> 'étude' (É -> é)"
    ~got:(SPARQL11_Algebra.string_lower "\xc3\x89TUDE")
    ~want:"\xc3\xa9tude";

  (* 5. Greek sigma: lower-casing standalone capital sigma (Σ, U+03A3,
     UTF-8 ce a3) gives regular sigma (σ, U+03C3, UTF-8 cf 83), NOT
     final sigma (ς, U+03C2, UTF-8 cf 82) — the documented
     simple-vs-context-sensitive-mapping limitation from the module
     banner above. Pinning the ACTUAL behaviour, not the ideal one. *)
  check_eq ~name:"lcase 'Σ' -> 'σ' (regular sigma; NOT context-sensitive final ς — documented limitation)"
    ~got:(SPARQL11_Algebra.string_lower "\xce\xa3")
    ~want:"\xcf\x83";
  (* Sanity: confirm we did NOT accidentally produce final sigma. *)
  check ~name:"lcase 'Σ' does not produce final sigma ς (would mean context-sensitive folding appeared)"
    ((SPARQL11_Algebra.string_lower "\xce\xa3") <> "\xcf\x82");

  (* 6. Full Greek word (mixed case sensitivity across multiple
     codepoints), matching the manual verification done while
     building the #250 fix. *)
  check_eq ~name:"ucase 'Σοφία' -> 'ΣΟΦΊΑ' (Greek multi-codepoint upper)"
    ~got:(SPARQL11_Algebra.string_upper "\xce\xa3\xce\xbf\xcf\x86\xce\xaf\xce\xb1")
    ~want:"\xce\xa3\xce\x9f\xce\xa6\xce\x8a\xce\x91";

  Printf.printf "summary: %d pass, %d fail\n" !passed !failed;
  if !failed > 0 then exit 1
