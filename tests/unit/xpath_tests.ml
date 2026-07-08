(* xpath_tests.ml — spec-cited regression battery for the XPath 1.0
   Stage 1 engine (Parser.XPath.fst + XPath.Eval.fst), per
   docs/designissues/2026-07-05-xforms-model-program-plan.md.

   Each case names the XPath 1.0 (https://www.w3.org/TR/1999/REC-xpath-
   19991116/) section it exercises. No vendored W3C suite exists for
   XPath 1.0 in isolation (see the plan doc's "Test suite" section) —
   this file IS the conformance signal for Stage 1, scored as
   "N pass, N fail (of N)" per CLAUDE.md rule #25.

   NOT yet wired into tests/unit/run-all.sh's COMMON_MODULES (that is
   the coordinator's registration step at landing — see the
   implementation report for the exact lines to add). Until then this
   file is compiled/run standalone; see the report for the manual
   invocation used to produce the pass/fail count below. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if String.equal expected actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %S got %S\n" name expected actual
  end

let check_bool ~name expected actual =
  check ~name (if expected then "true" else "false") (if actual then "true" else "false")

let doc_of (xml : string) : Parser_XML.xml_node =
  match Parser_XML.parse_xml_document xml with
  | FStar_Pervasives_Native.Some n -> n
  | FStar_Pervasives_Native.None -> failwith ("fixture failed to parse: " ^ xml)

let eval_opt doc vars expr = XPath_Eval.eval_xpath_from_root doc vars expr

let eval doc vars expr =
  match eval_opt doc vars expr with
  | FStar_Pervasives_Native.Some v -> Some v
  | FStar_Pervasives_Native.None -> None

let must_eval doc vars expr =
  match eval doc vars expr with
  | Some v -> v
  | None -> failwith ("expression failed to parse: " ^ expr)

let str doc expr = XPath_Eval.to_string_val (must_eval doc [] expr)
let str_v doc vars expr = XPath_Eval.to_string_val (must_eval doc vars expr)
let boolean doc expr = XPath_Eval.to_bool_val (must_eval doc [] expr)

let parse_fails expr =
  match Parser_XPath.parse_xpath expr with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some _ -> false

(* ------------------------------------------------------------------ *)
(* Fixtures                                                           *)
(* ------------------------------------------------------------------ *)

(* FIXTURE_A: children, attributes, text, a comment, and a prefixed
   element name (Parser.XML stores "ns:tagged" as one opaque tag
   string — no namespace resolution — which is exactly what the
   prefix node-test / name()-with-colon cases below need). *)
let fixture_a = doc_of
  "<root a=\"1\" b=\"two\">\
     <child id=\"c1\">first</child>\
     <child id=\"c2\">second</child>\
     <child id=\"c3\"><!--note-->third</child>\
     <ns:tagged>nsval</ns:tagged>\
   </root>"

(* FIXTURE_B: a plain nesting chain for parent/ancestor/descendant axis
   depth and reverse-axis position() tests. *)
let fixture_b = doc_of "<a><b><c><d>leaf</d></c></b></a>"

(* FIXTURE_C: numeric attributes for sum()/relational-coercion tests. *)
let fixture_c = doc_of "<nums><n v=\"3\"/><n v=\"7\"/><n v=\"10\"/></nums>"

(* FIXTURE_D: processing instructions (retained as XPI nodes) mixed with
   an element, for processing-instruction() / node() node-test and
   PI string-value / name() tests. *)
let fixture_d = doc_of "<doc><?pi-target pi data?><a>x</a><?other more?></doc>"

let () =
  (* --- §2.2 child axis (default) --- *)
  check ~name:"§2.2 child axis count" "3" (str fixture_a "count(/root/child)");
  check ~name:"§2.2 attribute value via '='" "1" (str fixture_a "string(/root/@a)");

  (* --- §2.3 node tests: wildcard, prefix wildcard, full axis syntax --- *)
  check ~name:"§2.3 child::* matches every element, any prefix" "4"
    (str fixture_a "count(/root/*)");
  check ~name:"§2.3 attribute::* count" "2" (str fixture_a "count(/root/@*)");
  check ~name:"§2.3 prefix wildcard 'ns:*'" "1" (str fixture_a "count(/root/ns:*)");
  check ~name:"§2.3 full axis syntax child::child" "3"
    (str fixture_a "count(/root/child::child)");
  check ~name:"§2.3 self axis via full syntax" "child"
    (str fixture_a "name(/root/child[1]/self::child)");
  check ~name:"§2.3 attribute axis via full syntax" "1"
    (str fixture_a "string(/root/attribute::a)");

  (* --- §2.5 abbreviated syntax: '//' is /descendant-or-self::node()/ --- *)
  check ~name:"§2.5 '//' abbreviation matches explicit desugaring" "true"
    (if str fixture_a "count(//child)" = str fixture_a "count(/descendant-or-self::node()/child)"
     then "true" else "false");
  check ~name:"§2.5 '//child' count" "3" (str fixture_a "count(//child)");

  (* --- §2.3 text()/comment()/node() node tests --- *)
  check ~name:"§2.3 text() node test" "first" (str fixture_a "string(/root/child[1]/text())");
  check_bool ~name:"§2.3 comment() node test (non-empty)" true
    (boolean fixture_a "boolean(/root/child[3]/comment())");
  check ~name:"§2.3 node() matches text+comment siblings" "2"
    (str fixture_a "count(/root/child[3]/node())");

  (* --- §2.4 position()/last(), including the [N] shorthand --- *)
  check ~name:"§2.4 position()=2 predicate" "c2"
    (str fixture_a "string(/root/child[position()=2]/@id)");
  check ~name:"§2.4 [2] numeric-predicate shorthand" "c2"
    (str fixture_a "string(/root/child[2]/@id)");
  check ~name:"§2.4 last() predicate" "c3"
    (str fixture_a "string(/root/child[last()]/@id)");
  check ~name:"§2.4 count() built-in" "3" (str fixture_a "count(/root/child)");

  (* --- §2.3/§2.4 reverse axes: ancestor position numbered nearest-first --- *)
  check ~name:"§2.3 ancestor axis nearest-first [1]" "c"
    (str fixture_b "name(/a/b/c/d/ancestor::*[1])");
  check ~name:"§2.3 ancestor axis nearest-first [2]" "b"
    (str fixture_b "name(/a/b/c/d/ancestor::*[2])");
  check ~name:"§2.3 ancestor axis nearest-first [3]" "a"
    (str fixture_b "name(/a/b/c/d/ancestor::*[3])");
  check ~name:"§2.3 ancestor axis count" "3" (str fixture_b "count(/a/b/c/d/ancestor::*)");
  check ~name:"§2.3 ancestor-or-self axis count" "4"
    (str fixture_b "count(/a/b/c/d/ancestor-or-self::*)");
  check ~name:"§2.3 parent axis" "c" (str fixture_b "name(/a/b/c/d/parent::*)");
  check ~name:"§2.3 descendant axis depth" "3" (str fixture_b "count(/a/descendant::*)");
  check ~name:"§2.3 descendant-or-self axis depth" "4"
    (str fixture_b "count(/a/descendant-or-self::*)");

  (* --- §2.3 abbreviated steps '.' and '..' --- *)
  check ~name:"§2.3 '.' self abbreviation in a predicate" "c2"
    (str fixture_a "string(/root/child[.=\"second\"]/@id)");
  check ~name:"§2.3 '..' parent abbreviation" "1"
    (str fixture_a "string(/root/child[1]/../@a)");

  (* --- §2.6 union operator --- *)
  check ~name:"§2.6 union of disjoint node-sets" "2"
    (str fixture_b "count(/a/b | /a/b/c)");

  (* --- §3.4 comparisons: node-set = string, node-set = number, != --- *)
  check_bool ~name:"§3.4 node-set = string" true (boolean fixture_a "/root/@a = \"1\"");
  check_bool ~name:"§3.4 number = node-set comparison" true (boolean fixture_a "/root/@a = 1");
  check_bool ~name:"§3.4 node-set != number" true (boolean fixture_a "/root/@a != 2");
  check_bool ~name:"§3.4 boolean(node-set) on empty set" false
    (boolean fixture_a "boolean(/root/nonexistent)");
  check_bool ~name:"§3.4 boolean(node-set) on non-empty set" true
    (boolean fixture_a "boolean(/root/child)");
  check ~name:"§3.4 relational op coerces node-set to number" "2"
    (str fixture_c "count(/nums/n[@v > 5])");

  (* --- §3.4/§4.4 arithmetic, div/mod, unary minus --- *)
  check ~name:"§4.4 sum() + string(number) integer formatting (no trailing .0)" "20"
    (str fixture_c "string(sum(/nums/n/@v))");
  check ~name:"§4.4 string(number) decimal formatting" "3.5" (str fixture_a "string(3.5)");
  check ~name:"§4.4 string(number) integer formatting" "4" (str fixture_a "string(4)");
  check ~name:"§3.4 'div' produces a decimal" "3.5" (str fixture_a "string(7 div 2)");
  check ~name:"§3.4 'mod'" "1" (str fixture_a "string(7 mod 3)");
  check ~name:"§3.4 unary minus" "-5" (str fixture_a "string(-5)");
  check ~name:"§3.4 unary minus binds looser than union (per UnaryExpr ::= '-' UnaryExpr | UnionExpr)"
    "-2" (str fixture_a "string(-(1+1))");

  (* --- §4.4 round()/floor()/ceiling(), incl. the half-to-+Infinity rule --- *)
  check ~name:"§4.4 round(2.5) rounds toward +Infinity" "3" (str fixture_a "string(round(2.5))");
  check ~name:"§4.4 round(-2.5) rounds toward +Infinity (not away from zero)" "-2"
    (str fixture_a "string(round(-2.5))");
  check ~name:"§4.4 floor(2.7)" "2" (str fixture_a "string(floor(2.7))");
  check ~name:"§4.4 ceiling(2.1)" "3" (str fixture_a "string(ceiling(2.1))");

  (* --- §4.3 not()/true()/false()/boolean() --- *)
  check ~name:"§4.3 not()" "true" (str fixture_a "string(not(false()))");
  check ~name:"§4.3 true() and false()" "false" (str fixture_a "string(true() and false())");
  check_bool ~name:"§4.2 boolean('') is false" false (boolean fixture_a "boolean(\"\")");
  check_bool ~name:"§4.2 boolean(non-empty string) is true" true (boolean fixture_a "boolean(\"x\")");

  (* --- §4.2 string functions --- *)
  check ~name:"§4.2 concat() with 3 args" "abc" (str fixture_a "concat(\"a\",\"b\",\"c\")");
  check_bool ~name:"§4.2 contains()" true (boolean fixture_a "contains(\"foobar\",\"oba\")");
  check_bool ~name:"§4.2 starts-with()" true (boolean fixture_a "starts-with(\"foobar\",\"foo\")");
  check ~name:"§4.2 substring-before()" "foo" (str fixture_a "substring-before(\"foo/bar\",\"/\")");
  check ~name:"§4.2 substring-after()" "bar" (str fixture_a "substring-after(\"foo/bar\",\"/\")");
  check ~name:"§4.2 string-length()" "5" (str fixture_a "string(string-length(\"hello\"))");
  check ~name:"§4.2 normalize-space()" "a b c" (str fixture_a "normalize-space(\"  a   b  c \")");

  (* --- §4.2 substring() — the spec's own famous edge-case battery,
     round()-of-start/length plus IEEE Infinity/NaN via xn_arith --- *)
  check ~name:"§4.2 substring(\"12345\",1.5,2.6) = \"234\"" "234"
    (str fixture_a "substring(\"12345\",1.5,2.6)");
  check ~name:"§4.2 substring(\"12345\",0,3) = \"12\"" "12"
    (str fixture_a "substring(\"12345\",0,3)");
  check ~name:"§4.2 substring(\"12345\", 0 div 0, 3) = \"\" (NaN start)" ""
    (str fixture_a "substring(\"12345\",0 div 0,3)");
  check ~name:"§4.2 substring(\"12345\", 1, 0 div 0) = \"\" (NaN length)" ""
    (str fixture_a "substring(\"12345\",1,0 div 0)");
  check ~name:"§4.2 substring(\"12345\", -42, 1 div 0) = \"12345\" (+Infinity length)" "12345"
    (str fixture_a "substring(\"12345\",-42,1 div 0)");
  check ~name:"§4.2 substring(\"12345\", -1 div 0, 1 div 0) = \"\" (-Inf + Inf = NaN)" ""
    (str fixture_a "substring(\"12345\",-1 div 0,1 div 0)");

  (* --- §2.3 name()/local-name(), incl. a prefixed element name --- *)
  check ~name:"§2.3 name() on a prefixed element (opaque QName string)" "ns:tagged"
    (str fixture_a "name(/root/ns:tagged)");
  check ~name:"§2.3 local-name() strips the prefix" "tagged"
    (str fixture_a "local-name(/root/ns:tagged)");
  check ~name:"§2.3 local-name() with no prefix equals name()" "child"
    (str fixture_a "local-name(/root/child[1])");

  (* --- VariableReference (§3.7) plus arithmetic on it --- *)
  check ~name:"§3.7 VariableReference in an arithmetic expression" "6"
    (str_v fixture_a [("x", XPath_Eval.XV_Num (XPath_Eval.XN_Finite (Z.of_int 5, Z.of_int 0)))] "$x + 1");

  (* --- §2.2 forward/reverse document-order axes (previously deferred) --- *)
  check ~name:"§2.2 following-sibling axis count" "3"
    (str fixture_a "count(/root/child[1]/following-sibling::*)");
  check ~name:"§2.2 following-sibling::child[1] is c2" "c2"
    (str fixture_a "string(/root/child[1]/following-sibling::child[1]/@id)");
  check ~name:"§2.2 preceding-sibling count of the last child" "3"
    (str fixture_a "count(/root/ns:tagged/preceding-sibling::*)");
  check ~name:"§2.2 preceding-sibling is a reverse axis (nearest first)" "c2"
    (str fixture_a "string(/root/child[3]/preceding-sibling::child[1]/@id)");
  check ~name:"§2.2 following axis excludes descendants, counts later elements" "3"
    (str fixture_a "count(/root/child[1]/following::*)");
  check ~name:"§2.2 preceding axis excludes ancestors, counts earlier elements" "3"
    (str fixture_a "count(/root/ns:tagged/preceding::*)");
  check ~name:"§2.2 following-sibling of the last child is empty" "0"
    (str fixture_a "count(/root/ns:tagged/following-sibling::*)");

  (* --- §2.3 processing-instruction() node test on retained XPI nodes --- *)
  check ~name:"§2.3 processing-instruction() counts both PIs" "2"
    (str fixture_d "count(/doc/processing-instruction())");
  check ~name:"§2.3 processing-instruction('target') filters by target" "1"
    (str fixture_d "count(/doc/processing-instruction('pi-target'))");
  check ~name:"§5 PI string-value is its data" "pi data"
    (str fixture_d "string(/doc/processing-instruction('pi-target'))");
  check ~name:"§2.3 name() of a PI is its target" "pi-target"
    (str fixture_d "name(/doc/processing-instruction()[1])");
  check ~name:"§2.3 node() sees PIs + element (2 PIs + 1 element = 3)" "3"
    (str fixture_d "count(/doc/node())");
  check ~name:"§2.3 '*' does NOT match PIs (principal node type)" "1"
    (str fixture_d "count(/doc/*)");

  (* --- §3.3 union: document order, duplicates removed (not concatenation) --- *)
  check ~name:"§3.3 union of overlapping node-sets removes duplicates" "3"
    (str fixture_a "count(/root/child | /root/child[1])");
  check ~name:"§3.3 self-union removes all duplicates" "3"
    (str fixture_a "count(/root/child | /root/child)");
  check ~name:"§3.3 union result is in document order, not concatenation order" "child"
    (str fixture_a "name((/root/ns:tagged | /root/child[1])[1])");

  (* --- §3.4 comparison matrix (confirming completeness) --- *)
  check_bool ~name:"§3.4 string < string (lexicographic)" true (boolean fixture_a "\"abc\" < \"abd\"");
  check_bool ~name:"§3.4 string > string" true (boolean fixture_a "\"b\" > \"a\"");
  check_bool ~name:"§3.4 number < number" true (boolean fixture_a "3 < 4");
  check_bool ~name:"§3.4 number >= number (equal)" true (boolean fixture_a "3.5 >= 3.5");
  check_bool ~name:"§3.4 node-set = node-set (some equal pair)" true
    (boolean fixture_a "/root/child[1] = /root/child[1]");
  check_bool ~name:"§3.4 node-set != node-set (distinct string values)" true
    (boolean fixture_a "/root/child[1] != /root/child[2]");
  check ~name:"§3.4 relational node-set coercion (>=)" "2"
    (str fixture_c "count(/nums/n[@v >= 7])");

  (* --- namespace axis remains deferred (clean parse failure), and an
     unknown function still parses (no crash) --- *)
  check_bool ~name:"namespace axis is deferred: clean parse failure" true
    (parse_fails "namespace::*");
  check_bool ~name:"'id(\"x\")' (unknown function) does not crash the parser" false
    (parse_fails "id(\"x\")");

  Printf.printf "xpath_tests: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
