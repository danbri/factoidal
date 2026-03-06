(* W3C-style SPARQL algebra tests against F*-extracted OCaml modules.

   These tests mirror W3C SPARQL test suite categories by constructing
   graphs and query patterns programmatically (no parser needed).

   Each test builds the graph + query that corresponds to a W3C test case,
   then checks results match expected output. *)

open RDF_Graph_Executable
open SPARQL11_Algebra

(* --- Test infrastructure --- *)

let tests_run = ref 0
let tests_passed = ref 0
let tests_failed = ref 0
let suite_results : (string * int * int) list ref = ref []

let iri s = T_IRI s
let str_lit s = T_Literal { lexical_form = s; datatype = xsd_string; lang_tag = None }
let int_lit n = T_Literal { lexical_form = string_of_int n; datatype = xsd_integer; lang_tag = None }
let lang_lit s l = T_Literal { lexical_form = s; datatype = "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"; lang_tag = Some l }
let typed_lit s dt = T_Literal { lexical_form = s; datatype = dt; lang_tag = None }
let bool_lit b = T_Literal { lexical_form = (if b then "true" else "false"); datatype = xsd_boolean; lang_tag = None }
let dec_lit s = T_Literal { lexical_form = s; datatype = xsd_decimal; lang_tag = None }
let dbl_lit s = T_Literal { lexical_form = s; datatype = xsd_double; lang_tag = None }
let triple s p o : triple = { s = S_IRI s; p = p; o = o }
let bnode_triple s p o : triple = { s = S_BNode s; p = p; o = o }
let tp_spo s p o : triple_pattern = { tp_s = s; tp_p = p; tp_o = o }
let var_s v = PS_Var v
let var_o v = PT_Var v
let iri_s i = PS_IRI i
let iri_p i = PT_IRI i

let no_modifier : solution_modifier = {
  sm_order_by = None; sm_distinct = false; sm_reduced = false;
  sm_offset = None; sm_limit = None;
}

let term_to_string (t : rdf_term) : string =
  match t with
  | T_IRI i -> Printf.sprintf "<%s>" i
  | T_BNode b -> Printf.sprintf "_:%s" b
  | T_Literal l ->
    (match l.lang_tag with
     | Some lang -> Printf.sprintf "\"%s\"@%s" l.lexical_form lang
     | None -> Printf.sprintf "\"%s\"^^%s" l.lexical_form l.datatype)

let binding_to_string (mu : solution_mapping) : string =
  String.concat ", " (List.map (fun (v, t) -> Printf.sprintf "?%s=%s" v (term_to_string t)) mu)

let check_result_count test_name expected (results : solution_sequence) =
  incr tests_run;
  let actual = List.length results in
  if actual = expected then (
    incr tests_passed;
    Printf.printf "  PASS: %s (%d results)\n" test_name actual
  ) else (
    incr tests_failed;
    Printf.printf "  FAIL: %s (expected %d, got %d)\n" test_name expected actual;
    List.iter (fun mu -> Printf.printf "    -> %s\n" (binding_to_string mu)) results
  )

let check_has_binding test_name var value (results : solution_sequence) =
  incr tests_run;
  let found = List.exists (fun mu ->
    match List.assoc_opt var mu with
    | Some t -> term_to_string t = term_to_string value
    | None -> false
  ) results in
  if found then (
    incr tests_passed;
    Printf.printf "  PASS: %s (found ?%s=%s)\n" test_name var (term_to_string value)
  ) else (
    incr tests_failed;
    Printf.printf "  FAIL: %s (missing ?%s=%s)\n" test_name var (term_to_string value);
    List.iter (fun mu -> Printf.printf "    -> %s\n" (binding_to_string mu)) results
  )

let start_suite name =
  Printf.printf "\n=== %s ===\n" name;
  let before_pass = !tests_passed in
  let before_run = !tests_run in
  (name, before_pass, before_run)

let end_suite (name, before_pass, before_run) =
  let suite_pass = !tests_passed - before_pass in
  let suite_total = !tests_run - before_run in
  suite_results := (name, suite_pass, suite_total) :: !suite_results;
  Printf.printf "  -- %s: %d/%d --\n" name suite_pass suite_total

(* --- Test suites --- *)

(* W3C basic: Simple BGP queries *)
let test_basic () =
  let s = start_suite "basic (BGP)" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"x") (ex^"p") (str_lit "1");
    triple (ex^"x") (ex^"q") (str_lit "2");
    triple (ex^"y") (ex^"p") (str_lit "3");
    triple (ex^"y") (ex^"q") (str_lit "4");
  ] in
  (* Single triple pattern *)
  let r = eval_pattern (GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]) g in
  check_result_count "single-tp" 2 r;
  check_has_binding "single-tp-val1" "o" (str_lit "1") r;
  check_has_binding "single-tp-val2" "o" (str_lit "3") r;
  (* Two triple patterns (join) *)
  let r = eval_pattern (GP_BGP [
    tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "po");
    tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "qo");
  ]) g in
  check_result_count "two-tp-join" 2 r;
  check_has_binding "two-tp-x" "po" (str_lit "1") r;
  check_has_binding "two-tp-y" "po" (str_lit "3") r;
  (* No match *)
  let r = eval_pattern (GP_BGP [tp_spo (iri_s (ex^"z")) (iri_p (ex^"p")) (var_o "o")]) g in
  check_result_count "no-match" 0 r;
  (* All triples *)
  let r = eval_pattern (GP_BGP [tp_spo (var_s "s") (var_o "p") (var_o "o")]) g in
  check_result_count "all-triples" 4 r;
  end_suite s

(* W3C bound: BOUND function *)
let test_bound () =
  let s = start_suite "bound" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"a") (ex^"q") (str_lit "2");
    triple (ex^"b") (ex^"p") (str_lit "3");
  ] in
  (* OPTIONAL + BOUND *)
  let pattern = GP_Filter (
    E_Bound "qo",
    GP_LeftJoin (
      GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "po")],
      GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "qo")],
      E_BoolLit true
    )
  ) in
  let r = eval_pattern pattern g in
  check_result_count "bound-filter" 1 r;
  check_has_binding "bound-filter-val" "po" (str_lit "1") r;
  (* NOT BOUND *)
  let pattern2 = GP_Filter (
    E_Not (E_Bound "qo"),
    GP_LeftJoin (
      GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "po")],
      GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "qo")],
      E_BoolLit true
    )
  ) in
  let r = eval_pattern pattern2 g in
  check_result_count "not-bound-filter" 1 r;
  check_has_binding "not-bound-val" "po" (str_lit "3") r;
  end_suite s

(* W3C distinct *)
let test_distinct () =
  let s = start_suite "distinct" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"b") (ex^"p") (str_lit "1");
    triple (ex^"c") (ex^"p") (str_lit "2");
  ] in
  let q : query = {
    q_base = None; q_prefixes = []; q_dataset = [];
    q_form = QF_Select (Select_Vars [SI_Var "o"]);
    q_pattern = GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")];
    q_group_by = None; q_having = None;
    q_modifier = { no_modifier with sm_distinct = true };
  } in
  let r = eval_select_query q g in
  check_result_count "distinct-values" 2 r;
  end_suite s

(* W3C sort / solution-seq *)
let test_sort () =
  let s = start_suite "sort / solution-seq" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (int_lit 3);
    triple (ex^"b") (ex^"p") (int_lit 1);
    triple (ex^"c") (ex^"p") (int_lit 2);
  ] in
  (* ORDER BY ASC *)
  let q : query = {
    q_base = None; q_prefixes = []; q_dataset = [];
    q_form = QF_Select (Select_Vars [SI_Var "s"; SI_Var "o"]);
    q_pattern = GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")];
    q_group_by = None; q_having = None;
    q_modifier = { no_modifier with sm_order_by = Some [OC_Asc (E_Var "o")] };
  } in
  let r = eval_select_query q g in
  check_result_count "order-by-asc" 3 r;
  (* LIMIT *)
  let q2 = { q with q_modifier = { no_modifier with sm_limit = Some (Z.of_int 2) } } in
  let r = eval_select_query q2 g in
  check_result_count "limit-2" 2 r;
  (* OFFSET *)
  let q3 = { q with q_modifier = { no_modifier with
    sm_order_by = Some [OC_Asc (E_Var "o")];
    sm_offset = Some (Z.of_int 1); sm_limit = Some (Z.of_int 1) } } in
  let r = eval_select_query q3 g in
  check_result_count "offset-1-limit-1" 1 r;
  end_suite s

(* W3C union *)
let test_union () =
  let s = start_suite "union" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"b") (ex^"q") (str_lit "2");
  ] in
  let r = eval_pattern (GP_Union (
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")],
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "o")]
  )) g in
  check_result_count "union-2" 2 r;
  check_has_binding "union-val1" "o" (str_lit "1") r;
  check_has_binding "union-val2" "o" (str_lit "2") r;
  end_suite s

(* W3C optional *)
let test_optional () =
  let s = start_suite "optional" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"a") (ex^"q") (str_lit "opt-a");
    triple (ex^"b") (ex^"p") (str_lit "2");
  ] in
  let r = eval_pattern (GP_LeftJoin (
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")],
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "opt")],
    E_BoolLit true
  )) g in
  check_result_count "optional-2" 2 r;
  (* Check that ?opt is bound for ex:a but not for ex:b *)
  let a_bindings = List.filter (fun mu ->
    match List.assoc_opt "o" mu with Some t -> term_to_string t = term_to_string (str_lit "1") | None -> false
  ) r in
  let has_opt = List.exists (fun mu -> List.assoc_opt "opt" mu <> None) a_bindings in
  incr tests_run;
  if has_opt then (incr tests_passed; Printf.printf "  PASS: optional-bound\n")
  else (incr tests_failed; Printf.printf "  FAIL: optional-bound\n");
  end_suite s

(* W3C regex *)
let test_regex () =
  let s = start_suite "regex" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"name") (str_lit "Alice");
    triple (ex^"b") (ex^"name") (str_lit "Bob");
    triple (ex^"c") (ex^"name") (str_lit "Charlie");
    triple (ex^"d") (ex^"name") (str_lit "alice");
  ] in
  (* REGEX case-sensitive *)
  let r = eval_pattern (GP_Filter (
    E_Regex (E_Var "n", E_Literal { lexical_form = "^A"; datatype = xsd_string; lang_tag = None }, None),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"name")) (var_o "n")]
  )) g in
  check_result_count "regex-starts-A" 1 r;
  check_has_binding "regex-Alice" "n" (str_lit "Alice") r;
  (* REGEX case-insensitive *)
  let r = eval_pattern (GP_Filter (
    E_Regex (E_Var "n", E_Literal { lexical_form = "^a"; datatype = xsd_string; lang_tag = None }, Some (E_Literal { lexical_form = "i"; datatype = xsd_string; lang_tag = None })),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"name")) (var_o "n")]
  )) g in
  check_result_count "regex-case-insensitive" 2 r;
  end_suite s

(* W3C expr-builtin: isIRI, isLiteral, isBlank, STR, LANG, DATATYPE *)
let test_expr_builtin () =
  let s = start_suite "expr-builtin" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (iri (ex^"val"));
    triple (ex^"b") (ex^"p") (str_lit "hello");
    triple (ex^"c") (ex^"p") (lang_lit "bonjour" "fr");
    bnode_triple "bn1" (ex^"p") (str_lit "bnode-val");
  ] in
  (* isIRI *)
  let r = eval_pattern (GP_Filter (
    E_IsIRI (E_Var "o"),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "isIRI" 1 r;
  (* isLiteral *)
  let r = eval_pattern (GP_Filter (
    E_IsLiteral (E_Var "o"),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "isLiteral" 3 r;
  (* LANG *)
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpEq, E_Lang (E_Var "o"), E_Literal { lexical_form = "fr"; datatype = xsd_string; lang_tag = None }),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "lang-fr" 1 r;
  end_suite s

(* W3C bnode-coreference *)
let test_bnode_coreference () =
  let s = start_suite "bnode-coreference" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    bnode_triple "b1" (ex^"p") (str_lit "val1");
    bnode_triple "b1" (ex^"q") (str_lit "val2");
    bnode_triple "b2" (ex^"p") (str_lit "val3");
  ] in
  (* Same bnode in two patterns *)
  let r = eval_pattern (GP_BGP [
    tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "po");
    tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "qo");
  ]) g in
  check_result_count "bnode-coref" 1 r;
  check_has_binding "bnode-coref-p" "po" (str_lit "val1") r;
  check_has_binding "bnode-coref-q" "qo" (str_lit "val2") r;
  end_suite s

(* W3C reduced *)
let test_reduced () =
  let s = start_suite "reduced" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"b") (ex^"p") (str_lit "1");
    triple (ex^"c") (ex^"p") (str_lit "2");
  ] in
  let q : query = {
    q_base = None; q_prefixes = []; q_dataset = [];
    q_form = QF_Select (Select_Vars [SI_Var "o"]);
    q_pattern = GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")];
    q_group_by = None; q_having = None;
    q_modifier = { no_modifier with sm_reduced = true };
  } in
  let r = eval_select_query q g in
  (* REDUCED allows but doesn't require dedup; check result count is between 2 and 3 *)
  let count = List.length r in
  incr tests_run;
  if count >= 2 && count <= 3 then (
    incr tests_passed; Printf.printf "  PASS: reduced (%d results, valid range 2-3)\n" count
  ) else (
    incr tests_failed; Printf.printf "  FAIL: reduced (%d results, expected 2-3)\n" count
  );
  end_suite s

(* W3C expr-equals *)
let test_expr_equals () =
  let s = start_suite "expr-equals" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (int_lit 1);
    triple (ex^"b") (ex^"p") (int_lit 2);
    triple (ex^"c") (ex^"p") (str_lit "hello");
  ] in
  (* Equality filter *)
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpEq, E_Var "o", E_NumericLit (Z.of_int 1)),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "eq-int-1" 1 r;
  (* Not equal *)
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpNe, E_Var "o", E_NumericLit (Z.of_int 1)),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "ne-int-1" 2 r;
  end_suite s

(* W3C expr-ops: arithmetic *)
let test_expr_ops () =
  let s = start_suite "expr-ops" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"val") (int_lit 10);
    triple (ex^"b") (ex^"val") (int_lit 20);
    triple (ex^"c") (ex^"val") (int_lit 5);
  ] in
  (* Filter: ?v > 7 *)
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpGt, E_Var "v", E_NumericLit (Z.of_int 7)),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"val")) (var_o "v")]
  )) g in
  check_result_count "gt-7" 2 r;
  (* Filter: ?v <= 10 *)
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpLe, E_Var "v", E_NumericLit (Z.of_int 10)),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"val")) (var_o "v")]
  )) g in
  check_result_count "le-10" 2 r;
  end_suite s

(* W3C string functions *)
let test_string_functions () =
  let s = start_suite "string-functions (1.1)" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"name") (str_lit "Alice");
    triple (ex^"b") (ex^"name") (str_lit "Bob");
    triple (ex^"c") (ex^"name") (str_lit "Charlie");
  ] in
  (* CONTAINS *)
  let r = eval_pattern (GP_Filter (
    E_Contains (E_Var "n", E_Literal { lexical_form = "li"; datatype = xsd_string; lang_tag = None }),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"name")) (var_o "n")]
  )) g in
  check_result_count "contains-li" 2 r; (* Alice, Charlie *)
  (* STRSTARTS *)
  let r = eval_pattern (GP_Filter (
    E_StrStarts (E_Var "n", E_Literal { lexical_form = "Ch"; datatype = xsd_string; lang_tag = None }),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"name")) (var_o "n")]
  )) g in
  check_result_count "strstarts-Ch" 1 r;
  (* STRENDS *)
  let r = eval_pattern (GP_Filter (
    E_StrEnds (E_Var "n", E_Literal { lexical_form = "ob"; datatype = xsd_string; lang_tag = None }),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"name")) (var_o "n")]
  )) g in
  check_result_count "strends-ob" 1 r;
  end_suite s

(* W3C BIND *)
let test_bind () =
  let s = start_suite "bind" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (int_lit 10);
    triple (ex^"b") (ex^"p") (int_lit 20);
  ] in
  let r = eval_pattern (GP_Bind (
    E_Var "v",
    "bound_val",
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "v")]
  )) g in
  check_result_count "bind-copy" 2 r;
  (* Check that bound_val equals v *)
  let all_match = List.for_all (fun mu ->
    List.assoc_opt "bound_val" mu = List.assoc_opt "v" mu
  ) r in
  incr tests_run;
  if all_match then (incr tests_passed; Printf.printf "  PASS: bind-values-match\n")
  else (incr tests_failed; Printf.printf "  FAIL: bind-values-match\n");
  end_suite s

(* W3C EXISTS / NOT EXISTS *)
let test_exists () =
  let s = start_suite "exists" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"a") (ex^"q") (str_lit "yes");
    triple (ex^"b") (ex^"p") (str_lit "2");
  ] in
  (* EXISTS *)
  let r = eval_pattern (GP_Filter (
    E_Exists (GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "dummy")]),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "exists" 1 r;
  check_has_binding "exists-val" "o" (str_lit "1") r;
  (* NOT EXISTS *)
  let r = eval_pattern (GP_Filter (
    E_NotExists (GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "dummy")]),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")]
  )) g in
  check_result_count "not-exists" 1 r;
  check_has_binding "not-exists-val" "o" (str_lit "2") r;
  end_suite s

(* W3C project-expression *)
let test_project_expression () =
  let s = start_suite "project-expression" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (int_lit 10);
    triple (ex^"b") (ex^"p") (int_lit 20);
  ] in
  let q : query = {
    q_base = None; q_prefixes = []; q_dataset = [];
    q_form = QF_Select (Select_Vars [SI_Var "v"; SI_Expr (E_Var "v", "copy")]);
    q_pattern = GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "v")];
    q_group_by = None; q_having = None;
    q_modifier = no_modifier;
  } in
  let r = eval_select_query q g in
  check_result_count "project-expr" 2 r;
  end_suite s

(* W3C i18n: language-tagged literals *)
let test_i18n () =
  let s = start_suite "i18n" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"label") (lang_lit "chat" "fr");
    triple (ex^"b") (ex^"label") (lang_lit "cat" "en");
    triple (ex^"c") (ex^"label") (str_lit "plain");
  ] in
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpEq, E_Lang (E_Var "l"), E_Literal { lexical_form = "fr"; datatype = xsd_string; lang_tag = None }),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"label")) (var_o "l")]
  )) g in
  check_result_count "lang-filter-fr" 1 r;
  end_suite s

(* W3C MINUS *)
let test_minus () =
  let s = start_suite "negation (MINUS)" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (str_lit "1");
    triple (ex^"a") (ex^"q") (str_lit "x");
    triple (ex^"b") (ex^"p") (str_lit "2");
  ] in
  let r = eval_pattern (GP_Minus (
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "o")],
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"q")) (var_o "dummy")]
  )) g in
  check_result_count "minus" 1 r;
  check_has_binding "minus-val" "o" (str_lit "2") r;
  end_suite s

(* W3C numeric functions *)
let test_numeric_functions () =
  let s = start_suite "numeric-functions (1.1)" in
  let ex = "http://example.org/" in
  let g = List.fold_left (fun g t -> graph_add t g) empty_graph [
    triple (ex^"a") (ex^"p") (int_lit 5);
  ] in
  (* Simple numeric comparison with expression *)
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpGt, E_Var "v", E_NumericLit (Z.of_int 3)),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "v")]
  )) g in
  check_result_count "numeric-gt" 1 r;
  let r = eval_pattern (GP_Filter (
    E_Compare (CmpLt, E_Var "v", E_NumericLit (Z.of_int 3)),
    GP_BGP [tp_spo (var_s "s") (iri_p (ex^"p")) (var_o "v")]
  )) g in
  check_result_count "numeric-lt" 0 r;
  end_suite s

(* --- Main --- *)
let () =
  Printf.printf "=== W3C-style SPARQL Algebra Tests (F*-extracted OCaml) ===\n";
  test_basic ();
  test_bound ();
  test_bnode_coreference ();
  test_distinct ();
  test_reduced ();
  test_sort ();
  test_union ();
  test_optional ();
  test_regex ();
  test_expr_builtin ();
  test_expr_equals ();
  test_expr_ops ();
  test_string_functions ();
  test_bind ();
  test_exists ();
  test_project_expression ();
  test_i18n ();
  test_minus ();
  test_numeric_functions ();

  Printf.printf "\n========================================\n";
  Printf.printf "Suite Results:\n";
  List.iter (fun (name, pass, total) ->
    Printf.printf "  %-30s %d/%d\n" name pass total
  ) (List.rev !suite_results);
  Printf.printf "========================================\n";
  Printf.printf "TOTAL: %d/%d passed (%d failed)\n" !tests_passed !tests_run !tests_failed;
  Printf.printf "========================================\n";
  if !tests_failed > 0 then exit 1
