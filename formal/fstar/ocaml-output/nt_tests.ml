(* W3C N-Triples test harness for the F*-extracted parser.
   This reads actual W3C test files and feeds them through
   RDF_Graph_Executable.parse_ntriples — the F*-verified parser.

   Positive tests: must parse successfully (Some _)
   Negative tests: must fail to parse (None) *)

open RDF_Graph_Executable

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0

let test_dir = "../../../tests/w3c/rdf/rdf11/rdf-n-triples/"

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with _ -> None

(* Positive tests: these files must parse successfully *)
let positive_tests = [
  "comment_following_triple.nt";
  "langtagged_string.nt";
  "lantag_with_subtag.nt";
  "literal.nt";
  "literal_all_punctuation.nt";
  "literal_ascii_boundaries.nt";
  "literal_false.nt";
  "literal_true.nt";
  "literal_with_2_dquotes.nt";
  "literal_with_2_squotes.nt";
  "literal_with_BACKSPACE.nt";
  "literal_with_CARRIAGE_RETURN.nt";
  "literal_with_CHARACTER_TABULATION.nt";
  "literal_with_FORM_FEED.nt";
  "literal_with_LINE_FEED.nt";
  "literal_with_REVERSE_SOLIDUS.nt";
  "literal_with_REVERSE_SOLIDUS2.nt";
  "literal_with_UTF8_boundaries.nt";
  "literal_with_dquote.nt";
  "literal_with_numeric_escape4.nt";
  "literal_with_numeric_escape8.nt";
  "literal_with_squote.nt";
  "minimal_whitespace.nt";
  "nt-syntax-bnode-01.nt";
  "nt-syntax-bnode-02.nt";
  "nt-syntax-bnode-03.nt";
  "nt-syntax-datatypes-01.nt";
  "nt-syntax-datatypes-02.nt";
  "nt-syntax-str-esc-01.nt";
  "nt-syntax-str-esc-02.nt";
  "nt-syntax-str-esc-03.nt";
  "nt-syntax-string-01.nt";
  "nt-syntax-string-02.nt";
  "nt-syntax-string-03.nt";
  "nt-syntax-subm-01.nt";
  "nt-syntax-uri-01.nt";
  "nt-syntax-uri-02.nt";
  "nt-syntax-uri-03.nt";
  "nt-syntax-uri-04.nt";
  "literal_all_controls.nt";
]

(* Negative tests: these files must NOT parse successfully *)
let negative_tests = [
  "nt-syntax-bad-base-01.nt";
  "nt-syntax-bad-esc-01.nt";
  "nt-syntax-bad-esc-02.nt";
  "nt-syntax-bad-esc-03.nt";
  "nt-syntax-bad-lang-01.nt";
  "nt-syntax-bad-num-01.nt";
  "nt-syntax-bad-num-02.nt";
  "nt-syntax-bad-num-03.nt";
  "nt-syntax-bad-prefix-01.nt";
  "nt-syntax-bad-string-01.nt";
  "nt-syntax-bad-string-02.nt";
  "nt-syntax-bad-string-03.nt";
  "nt-syntax-bad-string-04.nt";
  "nt-syntax-bad-string-05.nt";
  "nt-syntax-bad-string-06.nt";
  "nt-syntax-bad-string-07.nt";
  "nt-syntax-bad-struct-01.nt";
  "nt-syntax-bad-struct-02.nt";
  "nt-syntax-bad-uri-01.nt";
  "nt-syntax-bad-uri-02.nt";
  "nt-syntax-bad-uri-03.nt";
  "nt-syntax-bad-uri-04.nt";
  "nt-syntax-bad-uri-05.nt";
  "nt-syntax-bad-uri-06.nt";
  "nt-syntax-bad-uri-07.nt";
  "nt-syntax-bad-uri-08.nt";
  "nt-syntax-bad-uri-09.nt";
  "nt-syntax-bad-bnode-01.nt";
  "nt-syntax-bad-bnode-02.nt";
]

let run_positive_test name =
  incr tests_run;
  let path = test_dir ^ name in
  match read_file path with
  | None ->
    incr tests_failed;
    Printf.printf "  FAIL: %s (file not found)\n" name
  | Some content ->
    match parse_ntriples content with
    | Some triples ->
      incr tests_passed;
      Printf.printf "  PASS: %s (%d triples)\n" name (List.length triples)
    | None ->
      incr tests_failed;
      Printf.printf "  FAIL: %s (parse error — expected success)\n" name

let run_negative_test name =
  incr tests_run;
  let path = test_dir ^ name in
  match read_file path with
  | None ->
    incr tests_failed;
    Printf.printf "  FAIL: %s (file not found)\n" name
  | Some content ->
    match parse_ntriples content with
    | None ->
      incr tests_passed;
      Printf.printf "  PASS: %s (correctly rejected)\n" name
    | Some _ ->
      incr tests_failed;
      Printf.printf "  FAIL: %s (parsed but should have been rejected)\n" name

let () =
  Printf.printf "=== W3C N-Triples Tests (F*-extracted parser) ===\n\n";

  Printf.printf "--- Positive tests (must parse) ---\n";
  List.iter run_positive_test positive_tests;
  let pos_pass = !tests_passed in
  let pos_total = !tests_run in
  Printf.printf "  Positive: %d/%d\n\n" pos_pass pos_total;

  Printf.printf "--- Negative tests (must reject) ---\n";
  let neg_before = !tests_passed in
  List.iter run_negative_test negative_tests;
  let neg_pass = !tests_passed - neg_before in
  let neg_total = !tests_run - pos_total in
  Printf.printf "  Negative: %d/%d\n\n" neg_pass neg_total;

  Printf.printf "========================================\n";
  Printf.printf "TOTAL: %d/%d passed (%d failed)\n" !tests_passed !tests_run !tests_failed;
  Printf.printf "========================================\n";

  (* JSON output for browser/CI consumption *)
  Printf.printf "\n<!-- JSON_RESULTS\n";
  Printf.printf "{\"passed\":%d,\"total\":%d,\"failed\":%d,\"suites\":[" !tests_passed !tests_run !tests_failed;
  Printf.printf "{\"name\":\"N-Triples positive\",\"pass\":%d,\"total\":%d}," pos_pass pos_total;
  Printf.printf "{\"name\":\"N-Triples negative\",\"pass\":%d,\"total\":%d}" neg_pass neg_total;
  Printf.printf "]}\n";
  Printf.printf "JSON_RESULTS -->\n";

  if !tests_failed > 0 then exit 1
