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

  Printf.printf "regex_engine_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
