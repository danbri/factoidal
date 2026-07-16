(* regex_engine_unit.ml — exercises the verified Brzozowski-derivative regex
   core (Regex.Syntax / Regex.Derivative / Regex.Exec), Phase 1 of issue #304.

   These are the EXTRACTED F* functions: matching is `Regex_Exec.matches`
   (which folds the PROVEN `Regex.Derivative.deriv`, so it inherits
   `matches_correct : matches r w <==> mem r w`). Emptiness is
   `Regex_Exec.is_empty` / `intersection_empty` — the operation the OWL facet
   pattern-restriction check (#299) needs.

   Codepoints are F* `nat`, extracted to zarith `Z.t`; the AST is built over
   inclusive codepoint intervals, so this suite includes non-ASCII (astral and
   Latin-1) cases that a byte-oriented engine (the old OCaml Str realisation,
   anti-pattern #10) gets wrong. *)

module S = Regex_Syntax
module E = Regex_Exec
module X = Regex_XSDPattern

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed; Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed; Printf.printf "  FAIL  %s: expected %b got %b\n" name expected actual
  end

(* ---- builders over codepoints ---- *)
let cp (i:int) : Z.t = Z.of_int i
let range (lo:int) (hi:int) : S.regex = S.R_Ranges [(cp lo, cp hi)]
let lit_cp (i:int) : S.regex = range i i
let lit_char (c:char) : S.regex = lit_cp (Char.code c)
let eps : S.regex = S.R_Eps
let cat a b : S.regex = S.R_Cat (a, b)
let alt a b : S.regex = S.R_Alt (a, b)
let star a : S.regex = S.R_Star a
let rand a b : S.regex = S.R_And (a, b)
let rnot a : S.regex = S.R_Not a

(* concatenate a list of regexes *)
let rec cat_list = function [] -> eps | [r] -> r | r :: rs -> cat r (cat_list rs)

(* an ASCII string as a literal-sequence regex *)
let lit_str (s:string) : S.regex =
  cat_list (List.init (String.length s) (fun i -> lit_char s.[i]))

(* a word (list of codepoints) from an ASCII string *)
let word (s:string) : Z.t list =
  List.init (String.length s) (fun i -> cp (Char.code s.[i]))

(* a word from an explicit codepoint list *)
let cword (l:int list) : Z.t list = List.map cp l

(* `matches_norm` is the fast (ACI-normalized, state-finite) path consumers
   use; `Regex_Derivative.matches` is the PROVEN-correct reference
   (matches_correct). We test on the fast path and cross-check the proven path
   on small inputs below (the unnormalized proven deriv is exponential on
   adversarial nullable-heavy patterns, which is exactly why the normalized
   path exists). *)
let m (r:S.regex) (w:Z.t list) : bool = E.matches_norm r w
let msearch (r:S.regex) (w:Z.t list) : bool = E.search r w
let empty_lang (r:S.regex) : bool = E.is_empty r

let () =
  (* ---- literals ---- *)
  check ~name:"literal exact match" true (m (lit_str "abc") (word "abc"));
  check ~name:"literal rejects prefix" false (m (lit_str "abc") (word "ab"));
  check ~name:"literal rejects extra" false (m (lit_str "abc") (word "abcd"));
  check ~name:"empty string vs Eps" true (m eps (word ""));
  check ~name:"nonempty vs Eps" false (m eps (word "a"));

  (* ---- character classes ---- *)
  check ~name:"class [a-z] matches 'm'" true (m (range 0x61 0x7a) (word "m"));
  check ~name:"class [a-z] rejects 'M'" false (m (range 0x61 0x7a) (word "M"));
  check ~name:"class [0-9]+ matches digits" true
    (m (cat (range 0x30 0x39) (star (range 0x30 0x39))) (word "2026"));

  (* ---- star ---- *)
  check ~name:"a* matches empty" true (m (star (lit_char 'a')) (word ""));
  check ~name:"a* matches aaaa" true (m (star (lit_char 'a')) (word "aaaa"));
  check ~name:"a* rejects b" false (m (star (lit_char 'a')) (word "b"));
  check ~name:"(ab)* matches abab" true (m (star (lit_str "ab")) (word "abab"));
  check ~name:"(ab)* rejects aba" false (m (star (lit_str "ab")) (word "aba"));

  (* ---- alternation ---- *)
  check ~name:"cat|dog left" true (m (alt (lit_str "cat") (lit_str "dog")) (word "cat"));
  check ~name:"cat|dog right" true (m (alt (lit_str "cat") (lit_str "dog")) (word "dog"));
  check ~name:"cat|dog miss" false (m (alt (lit_str "cat") (lit_str "dog")) (word "fish"));

  (* the OWL fixture pattern a(b|c): language is exactly {ab, ac} *)
  let a_bc = cat (lit_char 'a') (alt (lit_char 'b') (lit_char 'c')) in
  check ~name:"a(b|c) matches ab" true (m a_bc (word "ab"));
  check ~name:"a(b|c) matches ac" true (m a_bc (word "ac"));
  check ~name:"a(b|c) rejects ad" false (m a_bc (word "ad"));
  check ~name:"a(b|c) rejects a" false (m a_bc (word "a"));

  (* ---- And / Not ---- *)
  (* [a-z]+ AND (not containing only .* with length 1..) : here use
     intersection of two classes to show And narrows the language *)
  let alnum = star (alt (range 0x61 0x7a) (range 0x30 0x39)) in
  let has_len3 = cat_list [ S.R_Ranges [(cp 0, cp 0x10FFFF)];
                            S.R_Ranges [(cp 0, cp 0x10FFFF)];
                            S.R_Ranges [(cp 0, cp 0x10FFFF)] ] in
  check ~name:"And: alnum & (exactly 3 chars) accepts 'a1z'" true
    (m (rand alnum has_len3) (word "a1z"));
  check ~name:"And: alnum & (exactly 3 chars) rejects 'ab' (len 2)" false
    (m (rand alnum has_len3) (word "ab"));
  check ~name:"And: alnum & (exactly 3 chars) rejects 'a b' (space not alnum)" false
    (m (rand alnum has_len3) (word "a b"));

  (* Not: complement of the literal "ab" *)
  check ~name:"Not(ab) rejects 'ab'" false (m (rnot (lit_str "ab")) (word "ab"));
  check ~name:"Not(ab) accepts 'ac'" true (m (rnot (lit_str "ab")) (word "ac"));
  check ~name:"Not(ab) accepts empty" true (m (rnot (lit_str "ab")) (word ""));
  (* double negation collapse still correct *)
  check ~name:"Not(Not(ab)) matches 'ab'" true (m (rnot (rnot (lit_str "ab"))) (word "ab"));

  (* ---- emptiness of an intersection (the #299 operation) ---- *)
  check ~name:"is_empty R_Empty" true (empty_lang S.R_Empty);
  check ~name:"is_empty R_Eps is false" false (empty_lang eps);
  (* a(b|c) INTERSECT literal 'ad'  ->  empty (disjoint) *)
  check ~name:"intersection_empty: a(b|c) & 'ad' is empty" true
    (E.intersection_empty a_bc (lit_str "ad"));
  (* a(b|c) INTERSECT literal 'ab'  ->  NON-empty (ab is common) *)
  check ~name:"intersection_empty: a(b|c) & 'ab' is NON-empty" false
    (E.intersection_empty a_bc (lit_str "ab"));
  (* two disjoint singleton classes *)
  check ~name:"intersection_empty: 'a' & 'b' is empty" true
    (E.intersection_empty (lit_char 'a') (lit_char 'b'));
  (* pattern a(b|c) AND NOT {ab,ac}: the pattern is subsumed, so empty *)
  check ~name:"subsumes: {ab,ac} covers a(b|c)" true
    (E.subsumes (alt (lit_str "ab") (lit_str "ac")) a_bc);

  (* ---- pathological (a?)^n a^n over n a's: the classic NFA-backtracking
     killer. The derivative engine is linear in the word and must NOT blow
     up. n = 25. ---- *)
  let n = 25 in
  let aq = alt (lit_char 'a') eps in
  let patho = cat_list (List.init n (fun _ -> aq) @ List.init n (fun _ -> lit_char 'a')) in
  let input = word (String.make n 'a') in
  check ~name:"(a?)^25 a^25 matches a^25 (no blowup)" true (m patho input);
  check ~name:"(a?)^25 a^25 rejects a^24" false (m patho (word (String.make (n-1) 'a')));

  (* ---- non-ASCII codepoint ranges (true codepoint semantics, not bytes) ---- *)
  (* Latin-1 'ä' = U+00E4, in class [U+00E0-U+00FF] as ONE codepoint *)
  check ~name:"codepoint class [00E0-00FF] matches U+00E4" true
    (m (range 0x00E0 0x00FF) (cword [0x00E4]));
  check ~name:"codepoint class [00E0-00FF] rejects U+0100" false
    (m (range 0x00E0 0x00FF) (cword [0x0100]));
  (* astral: U+1D4B8 MATHEMATICAL SCRIPT SMALL C as a single codepoint *)
  check ~name:"astral single codepoint U+1D4B8 matches its literal" true
    (m (lit_cp 0x1D4B8) (cword [0x1D4B8]));
  check ~name:"astral literal rejects a different astral codepoint" false
    (m (lit_cp 0x1D4B8) (cword [0x1D4B9]));
  (* a codepoint class spanning the BMP boundary *)
  check ~name:"range [FF00-10FFFF] matches U+1F600" true
    (m (range 0xFF00 0x10FFFF) (cword [0x1F600]));

  (* ---- unanchored search ---- *)
  check ~name:"search: 'cat' inside 'the cat sat'" true (msearch (lit_str "cat") (word "the cat sat"));
  check ~name:"search: 'dog' not in 'the cat sat'" false (msearch (lit_str "dog") (word "the cat sat"));

  (* ---- cross-check the PROVEN reference (Regex.Derivative.matches, which
     inherits matches_correct) against the normalized fast path on small
     inputs. Both must agree. ---- *)
  let proven r w = Regex_Derivative.matches r w in
  let agree ~name r w =
    let p = proven r w and f = E.matches_norm r w in
    if p = f then (incr passed; Printf.printf "  PASS  proven==norm %s\n" name)
    else (incr failed; Printf.printf "  FAIL  proven==norm %s: proven=%b norm=%b\n" name p f) in
  agree ~name:"abc" (lit_str "abc") (word "abc");
  agree ~name:"a(b|c) on ab" a_bc (word "ab");
  agree ~name:"a(b|c) on ax" a_bc (word "ax");
  agree ~name:"(ab)* on abab" (star (lit_str "ab")) (word "abab");
  agree ~name:"Not(ab) on ac" (rnot (lit_str "ab")) (word "ac");
  agree ~name:"[a-z]+ on m" (cat (range 0x61 0x7a) (star (range 0x61 0x7a))) (word "m");

  (* ==================================================================== *)
  (* Phase 2: the XSD-flavor pattern PARSER (Regex.XSDPattern), driven on   *)
  (* the ACTUAL measured fixture patterns (design doc 2026-07-15 §2 audit). *)
  (* Parser is F* over codepoints; here we exercise the string entrypoint   *)
  (* parse_xsd_pattern and match the parsed regex with the fast path.        *)
  (* ==================================================================== *)
  let parse (s:string) : S.regex option = X.parse_xsd_pattern s in
  (* record a successful parse and return the regex (R_Empty on failure so
     the run continues and the fail is counted, not aborted) *)
  let must_parse ~name pat =
    match parse pat with
    | Some r -> incr passed; Printf.printf "  PASS  parse %s\n" name; r
    | None -> incr failed; Printf.printf "  FAIL  parse %s: %S failed to parse\n" name pat; S.R_Empty in
  (* parse then match a word, checking the expected membership *)
  let pmatch ~name pat w expect =
    match parse pat with
    | None -> incr failed; Printf.printf "  FAIL  pmatch %s: %S failed to parse\n" name pat
    | Some r -> check ~name expect (m r w) in
  (* a pattern that must cleanly return None (outside the supported fragment) *)
  let parse_none ~name pat =
    match parse pat with
    | None -> incr passed; Printf.printf "  PASS  parse-None %s\n" name
    | Some _ -> incr failed; Printf.printf "  FAIL  parse-None %s: %S unexpectedly parsed\n" name pat in

  (* ---- OWL Inconsistent-pattern fixture (all.rdf:3051), END-TO-END ----
     Parse the ACTUAL fixture pattern "a(b|c)" and the derived dp1-filler
     enumeration "ab|ac", then run the #299 regex-language emptiness check on
     the parsed ASTs: pattern subsumed by enumeration  <=>  is_empty (And pat
     (Not enum)). This is the exact operation the OWL facet consistency check
     needs (the pattern admits only {ab,ac}, both already dp1 fillers). *)
  let owl_pat  = must_parse ~name:"OWL fixture pattern a(b|c)" "a(b|c)" in
  let owl_enum = must_parse ~name:"OWL dp1-enumeration ab|ac" "ab|ac" in
  check ~name:"OWL e2e: parsed a(b|c) matches ab" true (m owl_pat (word "ab"));
  check ~name:"OWL e2e: parsed a(b|c) matches ac" true (m owl_pat (word "ac"));
  check ~name:"OWL e2e: parsed a(b|c) rejects ad" false (m owl_pat (word "ad"));
  check ~name:"OWL e2e: parsed a(b|c) rejects a" false (m owl_pat (word "a"));
  check ~name:"OWL e2e: parsed ab|ac matches ab" true (m owl_enum (word "ab"));
  check ~name:"OWL e2e: parsed ab|ac rejects abc" false (m owl_enum (word "abc"));
  (* the load-bearing intersection-emptiness: L(pat) \ L(enum) = empty *)
  check ~name:"OWL e2e: is_empty(And pat (Not enum)) -- pattern subsumed" true
    (E.is_empty (S.R_And (owl_pat, S.R_Not owl_enum)));
  (* dual: the collision set L(pat) INTERSECT L(enum) is NON-empty *)
  check ~name:"OWL e2e: intersection_empty(pat, enum) is false (ab,ac collide)" false
    (E.intersection_empty owl_pat owl_enum);
  (* and via the Exec.subsumes API on the parsed patterns *)
  check ~name:"OWL e2e: subsumes(enum, pat)" true (E.subsumes owl_enum owl_pat);

  (* ---- CSVW test194 duration format "^.$" (the named phase-3 unblock) ---- *)
  ignore (must_parse ~name:"CSVW test194 duration format ^.$" "^.$");
  pmatch ~name:"^.$ matches single char 'x'" "^.$" (word "x") true;
  pmatch ~name:"^.$ rejects empty" "^.$" (word "") false;
  pmatch ~name:"^.$ rejects two chars" "^.$" (word "ab") false;
  pmatch ~name:"^.$ dot excludes newline" "^.$" (cword [0x0A]) false;

  (* ---- literals, groups, alternation (OWL flavor) ---- *)
  pmatch ~name:"a(b|c) via parser matches ab" "a(b|c)" (word "ab") true;
  pmatch ~name:"a(b|c) via parser rejects ad" "a(b|c)" (word "ad") false;

  (* ---- character classes with ranges (SHACL [2-8][0-9]* flavor) ---- *)
  pmatch ~name:"[0-9]+ matches 2026" "[0-9]+" (word "2026") true;
  pmatch ~name:"[0-9]+ rejects 20a" "[0-9]+" (word "20a") false;
  pmatch ~name:"[2-8][0-9]* matches 5001" "[2-8][0-9]*" (word "5001") true;
  pmatch ~name:"[2-8][0-9]* rejects leading 9" "[2-8][0-9]*" (word "9001") false;
  pmatch ~name:"[Aa]+ matches AaAa" "[Aa]+" (word "AaAa") true;
  pmatch ~name:"[Aa]+ rejects b" "[Aa]+" (word "b") false;

  (* ---- \d escape + {n} counted repetition (SHACL SSN ^\d{3}-\d{2}-\d{4}$) ---- *)
  pmatch ~name:"SSN pattern matches 123-45-6789" "^\\d{3}-\\d{2}-\\d{4}$" (word "123-45-6789") true;
  pmatch ~name:"SSN pattern rejects short group" "^\\d{3}-\\d{2}-\\d{4}$" (word "12-45-6789") false;
  pmatch ~name:"\\d{4} matches 2026" "\\d{4}" (word "2026") true;
  pmatch ~name:"\\d{4} rejects 3 digits" "\\d{4}" (word "202") false;

  (* ---- + on a group (ShEx (ab)+) ---- *)
  pmatch ~name:"(ab)+ matches abab" "(ab)+" (word "abab") true;
  pmatch ~name:"(ab)+ rejects aba" "(ab)+" (word "aba") false;
  pmatch ~name:"(ab)+ rejects empty" "(ab)+" (word "") false;

  (* ---- ? optional (ShEx ^https?://, whole-string here) ---- *)
  pmatch ~name:"https?:// matches http://" "https?://" (word "http://") true;
  pmatch ~name:"https?:// matches https://" "https?://" (word "https://") true;
  pmatch ~name:"https?:// rejects htt://" "https?://" (word "htt://") false;

  (* ---- dot and dot-star: the ShEx contains-cd form ---- *)
  pmatch ~name:".*cd.* matches xxcdyy" ".*cd.*" (word "xxcdyy") true;
  pmatch ~name:".*cd.* matches bare cd" ".*cd.*" (word "cd") true;
  pmatch ~name:".*cd.* rejects xy" ".*cd.*" (word "xy") false;

  (* ---- {n,m} bounded repetition (ShEx {2,3}) ---- *)
  pmatch ~name:"a{2,3} matches aa" "a{2,3}" (word "aa") true;
  pmatch ~name:"a{2,3} matches aaa" "a{2,3}" (word "aaa") true;
  pmatch ~name:"a{2,3} rejects a" "a{2,3}" (word "a") false;
  pmatch ~name:"a{2,3} rejects aaaa" "a{2,3}" (word "aaaa") false;
  pmatch ~name:"a{2,} matches aaaaa" "a{2,}" (word "aaaaa") true;
  pmatch ~name:"a{2,} rejects a" "a{2,}" (word "a") false;

  (* ---- lazy quantifier: same LANGUAGE as greedy (SHACL .*?@) ---- *)
  pmatch ~name:".*?x matches yyx" ".*?x" (word "yyx") true;
  pmatch ~name:".*?x rejects yy" ".*?x" (word "yy") false;

  (* ---- escaped metacharacters (ShEx \^bc\$, bc\$) ---- *)
  pmatch ~name:"\\^bc\\$ matches literal ^bc$" "\\^bc\\$" (word "^bc$") true;
  pmatch ~name:"\\. matches literal dot" "a\\.b" (word "a.b") true;
  pmatch ~name:"\\. rejects any-char use" "a\\.b" (word "axb") false;

  (* ---- Unicode escapes \uHHHH / \UHHHHHHHH (ShEx a, \U0001D4B8) ---- *)
  pmatch ~name:"\\u0061 matches 'a'" "\\u0061" (word "a") true;
  pmatch ~name:"\\u0061 rejects 'b'" "\\u0061" (word "b") false;
  pmatch ~name:"\\U0001D4B8 matches astral 𝒸" "\\U0001D4B8" (cword [0x1D4B8]) true;
  pmatch ~name:"\\U0001D4B8 rejects nearby astral" "\\U0001D4B8" (cword [0x1D4B9]) false;

  (* ---- negated character classes [^...] (#304 phase 4; SPARQL a[^b]c) ---- *)
  pmatch ~name:"[^b] matches 'a'" "[^b]" (word "a") true;
  pmatch ~name:"[^b] rejects 'b'" "[^b]" (word "b") false;
  pmatch ~name:"a[^b]c matches axc" "a[^b]c" (word "axc") true;
  pmatch ~name:"a[^b]c rejects abc" "a[^b]c" (word "abc") false;
  pmatch ~name:"[^0-9]+ matches letters" "[^0-9]+" (word "abc") true;
  pmatch ~name:"[^0-9]+ rejects a digit" "[^0-9]+" (word "a1c") false;

  (* ---- non-capturing group (?:...) ---- *)
  pmatch ~name:"(?:ab)+ matches abab" "(?:ab)+" (word "abab") true;

  (* ---- NEGATIVE cases: clean None outside the measured fragment ---- *)
  parse_none ~name:"unterminated class [" "[";
  parse_none ~name:"bare quantifier +" "+";
  parse_none ~name:"unclosed group a(b" "a(b";
  parse_none ~name:"unbalanced close a)" "a)";
  parse_none ~name:"category escape \\p{L}" "\\p{L}";
  parse_none ~name:"backreference \\1" "(a)\\1";
  parse_none ~name:"lookahead (?=x)" "(?=x)";
  parse_none ~name:"empty brace a{" "a{";
  parse_none ~name:"non-numeric brace a{x}" "a{x}";

  (* cross-check: a parsed pattern agrees on the proven reference path too *)
  let agree2 ~name pat w =
    match parse pat with
    | None -> incr failed; Printf.printf "  FAIL  proven==norm(parsed) %s: %S failed to parse\n" name pat
    | Some r ->
      let p = Regex_Derivative.matches r w and f = E.matches_norm r w in
      if p = f then (incr passed; Printf.printf "  PASS  proven==norm(parsed) %s\n" name)
      else (incr failed; Printf.printf "  FAIL  proven==norm(parsed) %s: proven=%b norm=%b\n" name p f) in
  agree2 ~name:"a(b|c) on ab" "a(b|c)" (word "ab");
  agree2 ~name:"[0-9]+ on 2026" "[0-9]+" (word "2026");
  agree2 ~name:"(ab)+ on abab" "(ab)+" (word "abab");

  Printf.printf "regex_engine_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
