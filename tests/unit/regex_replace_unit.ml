(* regex_replace_unit.ml — pins the semantics of
   SPARQL11_Algebra.regex_replace, the SPARQL REPLACE / XPath-XQuery
   fn:replace realisation. As of #304 phase 5 this is a VERIFIED F*
   function over the Regex.Syntax/Exec/XSDPattern codepoint engine:
   leftmost-longest whole-match SPANS on the verified Brzozowski
   derivative engine + a total, fuel-bounded capturing matcher for
   `$N` group templates. The former OCaml `Str` realisation and its
   byte-level xpath_to_str_regex translator are RETIRED (issue #63;
   anti-pattern #10 — Str matched bytes, splitting multi-byte UTF-8).

   These cases pin: the four W3C sparql11 functions/replace fixtures,
   global non-overlapping replace, `$N` group capture (incl. a
   non-participating group -> ""), `$0` whole-match, the empty-match
   policy (copy one codepoint, no substitution), and CODEPOINT (astral
   / non-BMP) correctness — the property the byte-level Str path could
   not give. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %S got %S\n" name expected actual
  end

let r ?flags text pattern replacement =
  let flags =
    match flags with
    | None -> FStar_Pervasives_Native.None
    | Some f -> FStar_Pervasives_Native.Some f
  in
  SPARQL11_Algebra.regex_replace text pattern replacement flags

let () =
  (* --- The four W3C sparql11 functions/replace fixtures --- *)
  (* replace01: global single-char negated class, codepoint-correct. *)
  check ~name:"replace01 shape: [^a-z0-9] -> - on ascii" "123" (r "123" "[^a-z0-9]" "-");
  check ~name:"replace01 shape: english -> -nglish" "-nglish" (r "English" "[^a-z0-9]" "-");
  check ~name:"replace01 shape: francais accents" "-ran-ais" (r "Fran\xc3\xa7ais" "[^a-z0-9]" "-");
  (* the s2 row: three CJK codepoints, each ONE replacement (not 3 bytes each). *)
  check ~name:"replace01 shape: CJK -> --- (codepoint, not byte)"
    "---" (r "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e" "[^a-z0-9]" "-");

  (* replace02: literal pattern, non-overlapping global. *)
  check ~name:"replace02: banana / ana -> b*na (non-overlapping)"
    "b*na" (r "banana" "ana" "*");

  (* replace03: alternation with two groups + $1/$2 template; group 2
     does not participate -> "". *)
  check ~name:"replace03: (ab)|(a) template [1=$1][2=$2]"
    "[1=ab][2=]cd" (r "abcd" "(ab)|(a)" "[1=$1][2=$2]");

  (* replace-case-insensitive: flag i folds a/A. *)
  check ~name:"replace-ci: aAbBaC / a / ~/ (i)"
    "~/~/bB~/C" (r ~flags:"i" "aAbBaC" "a" "~/");

  (* --- $0 whole-match reference --- *)
  check ~name:"$0 whole match: b -> [b]" "a[b]c" (r "abc" "b" "[$0]");

  (* --- literal escapes in template --- *)
  check ~name:"template literal dollar: \\$ -> $" "a$c" (r "abc" "b" "\\$");
  check ~name:"template literal backslash: \\\\ -> \\" "a\\c" (r "abc" "b" "\\\\");

  (* --- empty-match policy: pattern that matches the empty string copies
     one codepoint through with NO substitution (terminating). --- *)
  check ~name:"empty-match: x* over abc leaves abc unchanged"
    "abc" (r "abc" "x*" "Y");
  check ~name:"empty-match: x* over xxax is greedy where non-empty"
    "-a-" (r "xxax" "x*" "-");
  check ~name:"empty input" "" (r "" "a" "b");

  (* --- CODEPOINT / astral (non-BMP) correctness --- *)
  (* U+1F600 GRINNING FACE (F0 9F 98 80): ONE non-[a-z] codepoint -> ONE dash,
     proving codepoint (not byte) semantics; the Str path produced 4 dashes. *)
  check ~name:"astral: a<emoji>b / [^a-z] -> a-b (one cp, one match)"
    "a-b" (r "a\xf0\x9f\x98\x80b" "[^a-z]" "-");
  (* dot matches a single astral codepoint as a whole. *)
  check ~name:"astral: . matches whole emoji -> X"
    "X" (r "\xf0\x9f\x98\x80" "." "X");
  (* astral in the REPLACEMENT survives round-trip through codepoints. *)
  check ~name:"astral replacement: a -> emoji"
    "\xf0\x9f\x98\x80" (r "a" "a" "\xf0\x9f\x98\x80");

  Printf.printf "\nregex_replace_unit: %d pass, %d fail\n" !passed !failed;
  if !failed > 0 then exit 1
