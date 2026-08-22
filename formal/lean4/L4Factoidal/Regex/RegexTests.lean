/-
L4Factoidal.Regex.RegexTests — build-time checks for the regex engine.

Every `#guard` is evaluated during `lake build`; a wrong answer is a
build failure. Three groups:

  1. the engine-level cases of the F* unit suite
     `tests/unit/regex_engine_unit.ml` (literals, classes, star,
     alternation, intersection / complement, emptiness, the
     `(a?)^n a^n` blow-up, non-ASCII codepoints, search, and the
     XSD-pattern parser cases driven on the measured fixture patterns);
  2. the EXACT pattern / flag / input / expected-output quadruples of
     the W3C SPARQL test suites that reach the regex engine —
     `sparql11/functions/replace01..03` + `replace-case-insensitive`
     (data: `data3.ttl`), `sparql11/functions/uuid01` + `struuid01`,
     `sparql11/service/service05` (data: `data05.ttl`), and the whole
     `sparql10/regex` manifest (`regex-query-001..004` on
     `regex-data-01.ttl`, the 17 quantifier / flag / class / anchor
     tests on `regex-data-quantifiers.ttl`). Each guard names its
     test; wiring them through `SPARQL/Expr.lean` is then mechanical;
  3. the public API's error channel.

None of this is a conformance score (iron rule #6): the W3C files are
not read here. The guards pin the engine on the suite's inputs so the
evaluator wiring inherits them.
-/
import L4Factoidal.Regex.XPath

namespace L4Factoidal.Regex.Tests

open L4Factoidal.Regex
open L4Factoidal.Regex.Exec (acceptsNorm search isEmpty intersectionEmpty subsumes)

/-! ### Builders over codepoints (the F* suite's helpers) -/

def range (lo hi : Nat) : Re := .ranges [(lo, hi)]
def litCp (c : Nat) : Re := range c c
def litChar (c : Char) : Re := litCp c.toNat
def catList : List Re → Re
  | [] => .eps
  | [r] => r
  | r :: rs => .cat r (catList rs)
def litStr (s : String) : Re := catList (s.toList.map litChar)
def word (s : String) : List Nat := cpsOfString s

/-- `acceptsNorm` is the fast path consumers use; `Derivative.accepts` is
the proven reference. -/
def m (r : Re) (w : List Nat) : Bool := acceptsNorm r w

/-! ### 1a. Engine: literals, classes, star, alternation -/

#guard m (litStr "abc") (word "abc") == true
#guard m (litStr "abc") (word "ab") == false
#guard m (litStr "abc") (word "abcd") == false
#guard m .eps (word "") == true
#guard m .eps (word "a") == false
#guard m (range 0x61 0x7a) (word "m") == true
#guard m (range 0x61 0x7a) (word "M") == false
#guard m (.cat (range 0x30 0x39) (.star (range 0x30 0x39))) (word "2026") == true
#guard m (.star (litChar 'a')) (word "") == true
#guard m (.star (litChar 'a')) (word "aaaa") == true
#guard m (.star (litChar 'a')) (word "b") == false
#guard m (.star (litStr "ab")) (word "abab") == true
#guard m (.star (litStr "ab")) (word "aba") == false
#guard m (.alt (litStr "cat") (litStr "dog")) (word "cat") == true
#guard m (.alt (litStr "cat") (litStr "dog")) (word "dog") == true
#guard m (.alt (litStr "cat") (litStr "dog")) (word "fish") == false

/-- The OWL fixture pattern `a(b|c)`: language exactly `{ab, ac}`. -/
def aBC : Re := .cat (litChar 'a') (.alt (litChar 'b') (litChar 'c'))
#guard m aBC (word "ab") == true
#guard m aBC (word "ac") == true
#guard m aBC (word "ad") == false
#guard m aBC (word "a") == false

/-! ### 1b. Engine: intersection / complement -/

def alnum : Re := .star (.alt (range 0x61 0x7a) (range 0x30 0x39))
def hasLen3 : Re := catList [range 0 0x10FFFF, range 0 0x10FFFF, range 0 0x10FFFF]
#guard m (.inter alnum hasLen3) (word "a1z") == true
#guard m (.inter alnum hasLen3) (word "ab") == false
#guard m (.inter alnum hasLen3) (word "a b") == false
#guard m (.compl (litStr "ab")) (word "ab") == false
#guard m (.compl (litStr "ab")) (word "ac") == true
#guard m (.compl (litStr "ab")) (word "") == true
#guard m (.compl (.compl (litStr "ab"))) (word "ab") == true

/-! ### 1c. Engine: emptiness of an intersection (the OWL facet operation) -/

#guard isEmpty .empty == true
#guard isEmpty .eps == false
#guard intersectionEmpty aBC (litStr "ad") == true
#guard intersectionEmpty aBC (litStr "ab") == false
#guard intersectionEmpty (litChar 'a') (litChar 'b') == true
#guard subsumes (.alt (litStr "ab") (litStr "ac")) aBC == true
#guard isEmpty aBC == false
#guard subsumes (litStr "ab") aBC == false
#guard subsumes (.alt (litStr "ab") (litStr "ad")) aBC == false

/-! ### 1d. Engine: the `(a?)^n a^n` NFA-backtracking killer, n = 25 -/

def aq : Re := .alt (litChar 'a') .eps
def patho : Re := catList (List.replicate 25 aq ++ List.replicate 25 (litChar 'a'))
#guard m patho (word (String.ofList (List.replicate 25 'a'))) == true
#guard m patho (word (String.ofList (List.replicate 24 'a'))) == false

/-! ### 1e. Engine: true codepoint semantics (not bytes) -/

#guard m (range 0x00E0 0x00FF) [0x00E4] == true
#guard m (range 0x00E0 0x00FF) [0x0100] == false
#guard m (litCp 0x1D4B8) [0x1D4B8] == true
#guard m (litCp 0x1D4B8) [0x1D4B9] == false
#guard m (range 0xFF00 0x10FFFF) [0x1F600] == true

/-! ### 1f. Engine: unanchored search; proven path agrees with the fast path -/

#guard search (litStr "cat") (word "the cat sat") == true
#guard search (litStr "dog") (word "the cat sat") == false
#guard Derivative.accepts (litStr "abc") (word "abc") == m (litStr "abc") (word "abc")
#guard Derivative.accepts aBC (word "ab") == m aBC (word "ab")
#guard Derivative.accepts aBC (word "ax") == m aBC (word "ax")
#guard Derivative.accepts (.star (litStr "ab")) (word "abab") == m (.star (litStr "ab")) (word "abab")
#guard Derivative.accepts (.compl (litStr "ab")) (word "ac") == m (.compl (litStr "ab")) (word "ac")

/-! ### 1g. XSD-pattern parser on the measured fixture patterns
(`xsdPatternMatches pattern s`: `none` = outside the fragment). -/

def xp (pat s : String) : Option Bool := xsdPatternMatches pat s

-- OWL Inconsistent-pattern fixture (all.rdf:3051), end to end
#guard xp "a(b|c)" "ab" == some true
#guard xp "a(b|c)" "ac" == some true
#guard xp "a(b|c)" "ad" == some false
#guard xp "a(b|c)" "a" == some false
#guard xp "ab|ac" "ab" == some true
#guard xp "ab|ac" "abc" == some false
#guard (match XSDPattern.parseXsdPattern "a(b|c)", XSDPattern.parseXsdPattern "ab|ac" with
        | some pat, some enum => isEmpty (.inter pat (.compl enum)) && !(intersectionEmpty pat enum) && subsumes enum pat
        | _, _ => false) == true
-- CSVW test194 duration format `^.$` and the test193 formats
#guard xp "^.$" "x" == some true
#guard xp "^.$" "" == some false
#guard xp "^.$" "ab" == some false
#guard xp "^.$" "\n" == some false
#guard xp "^.$" "PT130S" == some false
#guard xp "^.$" "P0Y20M" == some false
#guard xp "^-?P.*$" "PT130S" == some true
#guard xp "^-?P.*$" "-P60D" == some true
#guard xp "^-?P.DT.*$" "P1DT2H" == some true
#guard xp "^-?P.Y20M$" "P0Y20M" == some true
#guard xp "^-?P.Y20M$" "P0Y21M" == some false
-- SHACL-flavour classes, `\d`, counted repetition
#guard xp "[0-9]+" "2026" == some true
#guard xp "[0-9]+" "20a" == some false
#guard xp "[2-8][0-9]*" "5001" == some true
#guard xp "[2-8][0-9]*" "9001" == some false
#guard xp "[Aa]+" "AaAa" == some true
#guard xp "[Aa]+" "b" == some false
#guard xp "^\\d{3}-\\d{2}-\\d{4}$" "123-45-6789" == some true
#guard xp "^\\d{3}-\\d{2}-\\d{4}$" "12-45-6789" == some false
#guard xp "\\d{4}" "2026" == some true
#guard xp "\\d{4}" "202" == some false
-- ShEx-flavour groups, optional, dot-star, bounded repetition, lazy
#guard xp "(ab)+" "abab" == some true
#guard xp "(ab)+" "aba" == some false
#guard xp "(ab)+" "" == some false
#guard xp "https?://" "http://" == some true
#guard xp "https?://" "https://" == some true
#guard xp "https?://" "htt://" == some false
#guard xp ".*cd.*" "xxcdyy" == some true
#guard xp ".*cd.*" "cd" == some true
#guard xp ".*cd.*" "xy" == some false
#guard xp "a{2,3}" "aa" == some true
#guard xp "a{2,3}" "aaa" == some true
#guard xp "a{2,3}" "a" == some false
#guard xp "a{2,3}" "aaaa" == some false
#guard xp "a{2,}" "aaaaa" == some true
#guard xp "a{2,}" "a" == some false
#guard xp ".*?x" "yyx" == some true
#guard xp ".*?x" "yy" == some false
-- escaped metacharacters, Unicode escapes
#guard xp "\\^bc\\$" "^bc$" == some true
#guard xp "a\\.b" "a.b" == some true
#guard xp "a\\.b" "axb" == some false
#guard xp "\\u0061" "a" == some true
#guard xp "\\u0061" "b" == some false
#guard xp "\\U0001D4B8" "𝒸" == some true
#guard xp "\\U0001D4B8" (String.singleton (Char.ofNat 0x1D4B9)) == some false
-- negated classes, non-capturing group
#guard xp "[^b]" "a" == some true
#guard xp "[^b]" "b" == some false
#guard xp "a[^b]c" "axc" == some true
#guard xp "a[^b]c" "abc" == some false
#guard xp "[^0-9]+" "abc" == some true
#guard xp "[^0-9]+" "a1c" == some false
#guard xp "(?:ab)+" "abab" == some true
-- clean `none` outside the fragment
#guard xp "[" "x" == none
#guard xp "+" "x" == none
#guard xp "a(b" "ab" == none
#guard xp "a)" "a" == none
#guard xp "\\p{L}" "a" == none
#guard xp "(a)\\1" "aa" == none
#guard xp "(?=x)" "x" == none
#guard xp "a{" "a" == none
#guard xp "a{x}" "a" == none

/-! ### 2. W3C SPARQL suite inputs, exactly as in the `.rq` / data files -/

/-- `REGEX(s, pat, flags)` through the public API; a compile error is
`false` here so a guard can state it. -/
def rm (pat flags s : String) : Bool :=
  match compile pat flags with
  | .ok r => isMatch r s
  | .error _ => false

/-- `REPLACE(s, pat, rep, flags)` through the public API. -/
def rr (pat flags s rep : String) : Option String :=
  match compile pat flags with
  | .ok r => (replace r s rep).toOption
  | .error _ => none

-- sparql11/functions replace01: REPLACE(?str, "[^a-z0-9]", "-") over data3.ttl
#guard rr "[^a-z0-9]" "" "123" "-" == some "123"
#guard rr "[^a-z0-9]" "" "日本語" "-" == some "---"
#guard rr "[^a-z0-9]" "" "English" "-" == some "-nglish"
#guard rr "[^a-z0-9]" "" "Français" "-" == some "-ran-ais"
#guard rr "[^a-z0-9]" "" "abc" "-" == some "abc"
#guard rr "[^a-z0-9]" "" "def" "-" == some "def"
#guard rr "[^a-z0-9]" "" "banana" "-" == some "banana"
#guard rr "[^a-z0-9]" "" "abcd" "-" == some "abcd"
-- replace02: REPLACE(?str, "ana", "*") on :s8
#guard rr "ana" "" "banana" "*" == some "b*na"
-- replace03: REPLACE(?str, "(ab)|(a)", "[1=$1][2=$2]") on :s9
#guard rr "(ab)|(a)" "" "abcd" "[1=$1][2=$2]" == some "[1=ab][2=]cd"
-- replace-case-insensitive: REPLACE("aAbBaC", "a", "~/", "i")
#guard rr "a" "i" "aAbBaC" "~/" == some "~/~/bB~/C"
-- the F*-shaped entry points give the same answers
#guard regexReplace "abcd" "(ab)|(a)" "[1=$1][2=$2]" "" == "[1=ab][2=]cd"
#guard regexReplace "aAbBaC" "a" "~/" "i" == "~/~/bB~/C"
#guard regexReplace "日本語" "[^a-z0-9]" "-" "" == "---"

-- sparql11/service service05: FILTER regex(?projectSubject, "remote") over data05.ttl
#guard rm "remote" "" "Query remote RDF Data" == true
#guard rm "remote" "" "Update remote RDF Data" == true
#guard rm "remote" "" "Query RDF" == false

-- sparql11/functions uuid01 / struuid01 (the runner supplies the UUID; a
-- representative lower-case one is pinned here)
def uuidPat : String := "^[0-9A-F]{8}-[0-9A-F]{4}-[0-9A-F]{4}-[0-9A-F]{4}-[0-9A-F]{12}$"
#guard rm uuidPat "i" "1f4a9c2e-7b3d-4e8f-9a6b-0c1d2e3f4a5b" == true
#guard rm uuidPat "i" "1F4A9C2E-7B3D-4E8F-9A6B-0C1D2E3F4A5B" == true
#guard rm uuidPat "" "1f4a9c2e-7b3d-4e8f-9a6b-0c1d2e3f4a5b" == false
#guard rm uuidPat "i" "1f4a9c2e-7b3d-4e8f-9a6b-0c1d2e3f4a5" == false
#guard rm ("^urn:uuid:" ++ uuidPat.drop 1) "i" "urn:uuid:1f4a9c2e-7b3d-4e8f-9a6b-0c1d2e3f4a5b" == true

-- sparql10/regex regex-query-001..004 over regex-data-01.ttl
def data01 : List String :=
  ["abcDEFghiJKL", "ABCdefGHIjkl", "0123456789", "http://example.com/uri", "http://example.com/literal"]
def filt (pat flags : String) (data : List String) : List String := data.filter (rm pat flags)
#guard filt "GHI" "" data01 == ["ABCdefGHIjkl"]
#guard filt "DeFghI" "i" data01 == ["abcDEFghiJKL", "ABCdefGHIjkl"]
#guard filt "example\\.com" "" data01 == ["http://example.com/uri", "http://example.com/literal"]

-- sparql10/regex quantifier / flag / class / anchor tests over regex-data-quantifiers.ttl
def dataQ : List String :=
  ["ac", "abc", "abbc", "abbbc", "a\nc", "a\nb\nc", "a.c", "ABC", "a?+*.{}()[]c", "b"]
#guard filt "ab?c" "" dataQ == ["ac", "abc"]                                  -- regex-quantifier-optional
#guard filt "ab*c" "" dataQ == ["ac", "abc", "abbc", "abbbc"]                 -- regex-quantifier-zero-or-more
#guard filt "ab+c" "" dataQ == ["abc", "abbc", "abbbc"]                       -- regex-quantifier-one-or-more
#guard filt "ab{2}c" "" dataQ == ["abbc"]                                     -- regex-quantifier-counted-exact
#guard filt "ab{1,}c" "" dataQ == ["abc", "abbc", "abbbc"]                    -- regex-quantifier-counted-lower-bound
#guard filt "ab{1,2}c" "" dataQ == ["abc", "abbc"]                            -- regex-quantifier-counted-lower-upper-bounds
#guard filt "a.c" "" dataQ == ["abc", "a.c"]                                  -- regex-dot
#guard filt "a.c" "s" dataQ == ["abc", "a\nc", "a.c"]                         -- regex-dot-all
#guard filt "abc" "i" dataQ == ["abc", "ABC"]                                 -- regex-case-insensitive
#guard filt "a?+*.{}()[]c" "q" dataQ == ["a?+*.{}()[]c"]                      -- regex-no-metacharacters
#guard filt "a?+*.{}()[]C" "iq" dataQ == ["a?+*.{}()[]c"]                     -- regex-no-metacharacters-case-insensitive
#guard filt "^b$" "" dataQ == ["b"]                                           -- regex-start-end
#guard filt "^b$" "m" dataQ == ["a\nb\nc", "b"]                               -- regex-start-end-multiline
#guard filt "a[b\\n]c" "" dataQ == ["abc", "a\nc"]                            -- regex-char-class-expression
#guard filt "a[^b]c" "" dataQ == ["a\nc", "a.c"]                              -- regex-negative-char-class-expression
#guard filt " a\n\tc " "x" dataQ == ["ac"]                                    -- regex-ignore-whitespaces
#guard filt " a\n\r\t[\\n]c " "x" dataQ == ["a\nc"]                           -- regex-ignore-whitespaces-class-expression
-- the F*-shaped entry point, same answers
#guard dataQ.filter (regexMatch · "^b$" "") == ["b"]
#guard dataQ.filter (regexMatch · "a.c" "s") == ["abc", "a\nc", "a.c"]

/-! ### Anchors compose through alternation (the ShEx `^...$|...` shape) -/

#guard rm "^ab$|cd" "" "ab" == true
#guard rm "^ab$|cd" "" "xab" == false
#guard rm "^ab$|cd" "" "xcdx" == true
#guard rm "a$" "m" "a\nb" == true
#guard rm "a$" "" "a\nb" == false
#guard rm "^b" "m" "a\nb" == true
#guard rm "a.c" "sm" "a\nc" == true
#guard rm "a.c" "m" "a\nc" == false
#guard rm "a.*c" "sm" "a\nb\nc" == true

/-! ### 3. The public API's error channel -/

#guard (compile "a(b" "").isOk == false
#guard (compile "ab" "z").isOk == false
#guard (compile "ab" "ismxq").isOk == true
#guard (match compile "a*" "" with | .ok r => (replace r "aaa" "x").isOk | .error _ => true) == false  -- FORX0003
#guard (match compile "a" "" with | .ok r => (replace r "aaa" "\\x").isOk | .error _ => true) == false -- FORX0004
#guard (match compile "a" "" with | .ok r => (replace r "aaa" "$x").isOk | .error _ => true) == false -- FORX0004
#guard rr "a" "" "aaa" "\\\\" == some "\\\\\\"
#guard rr "a" "" "aaa" "\\$" == some "$$$"
#guard rr "(a)(b)" "" "abab" "$2$1" == some "baba"
#guard rr "b" "" "abcabc" "$0$0" == some "abbcabbc"
#guard rr "(x)|(ab)" "" "ab" "[$1][$2]" == some "[][ab]"

end L4Factoidal.Regex.Tests
