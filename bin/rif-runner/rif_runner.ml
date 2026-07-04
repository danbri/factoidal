(* RIF Core (rule #11 consumer) — standalone runner for the 4 vendored
   W3C RIF test cases under third_party/testing/rif/tc/.

   !! THIS IS I/O GLUE — NO RDF/SPARQL/RIF SEMANTIC LOGIC !!
   Per CLAUDE.md iron rule #10/#11 and anti-pattern #15, all reasoning
   lives in F*-extracted modules already on the link line:
     - Parser_RIFXML.parse_rif_program_with_imports  (RIF-XML -> AST +
       import URL list)
     - RIF_Core_Eval.fixpoint                        (fuel-bounded
       forward-chaining saturation)
     - SPARQL11_Parser / OWL_QueryEval / SPARQL11_Algebra
       (the SAME query parser + evaluator every other W3C-conformance
       runner in this repo uses — NOT RIF.Core.Tests' simplified
       triple-membership shims, which only check ground-triple
       membership and never run a real SELECT/ASK evaluation).
   This file's job is: locate the four vendored test fixtures, strip
   the XML DOCTYPE/entity prolog Parser.XML doesn't implement, merge
   RIF <Import> companion graphs, and compare the evaluator's answer
   to the expected .srx.

   The four cases (mf:name from the SPARQL 1.1 entailment manifest,
   third_party/testing/w3c/sparql/sparql11/entailment/manifest.ttl):
     :rif01  "RIF Logical Entailment (referencing RIF XML)"
     :rif03  "RIF Core WG tests: Frames"
     :rif04  "RIF Core WG tests: Modeling Brain Anatomy"
     :rif06  "RIF Core WG tests: RDF Combination Blank Node"

   The manifest's qt:data .ttl for each is a one-line pointer triple
   (e.g. `<rif01.rif> rif:usedWithProfile ent:Simple`), sometimes with
   extra ground facts (rif01). The RIF-XML rule document that actually
   drives inference is not bundled with the SPARQL suite; the
   authoritative copy lives in the vendored RIF Test Cases mirror
   under third_party/testing/rif/tc/<TestName>/. A small hardcoded
   lookup table (4 entries — exhaustive, not a general manifest walker
   per this PR's brief) maps each mf:name to its .rif / companion-.rdf
   / .ttl / .rq / .srx quintet.

   Usage:
     ./rif_runner              Run all 4 cases, print per-test PASS/FAIL
                                + a labelled score line.
     ./rif_runner -v|--verbose Print expected/actual on FAIL.
     ./rif_runner --help       Show this help.
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* File I/O helpers. *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let file_to_base_uri path =
  let abs = if Filename.is_relative path
            then Filename.concat (Sys.getcwd ()) path
            else path in
  "file://" ^ abs

(* ------------------------------------------------------------------ *)
(* DOCTYPE / internal-subset entity expansion.

   The F* Parser.XML scanner (Parser.XML.fst) implements only the five
   built-in XML entities; it has no DTD-parsing support at all, so a
   `<!DOCTYPE Document [ <!ENTITY rif "..."> ... ]>` prolog makes
   parse_xml_document return None. Every vendored .rif file (all four
   premise documents) and one companion .rdf (Modeling_Brain_Anatomy-
   import001.rdf) open with such a prolog; RDF_Combination_Blank_Node's
   companion .rdf has no DOCTYPE at all.

   Rather than hardcode two different entity tables (RIF's rif/xs/rdf
   vs. the OWL-catalog-style owl/owl2/xsd/owl2xml/testOntology/rdfs/rdf
   set used by the brain-anatomy import), this scans the internal
   subset itself for `<!ENTITY name "value">` declarations, strips the
   whole `<!DOCTYPE ...[...]>` block, and inline-substitutes every
   `&name;` reference with its declared value. Pure textual
   preprocessing — no RDF/RIF semantics — same category as owl_runner's
   catalog_entities expansion (bin/owl-runner/owl_runner.ml). *)

let entity_ref_re name = Str.regexp_string ("&" ^ name ^ ";")

let extract_entity_defs (subset : string) : (string * string) list =
  let re = Str.regexp
      "<!ENTITY[ \t\r\n]+\\([A-Za-z_][A-Za-z0-9_.-]*\\)[ \t\r\n]+\"\\([^\"]*\\)\"[ \t\r\n]*>" in
  let rec go pos acc =
    match (try Some (Str.search_forward re subset pos) with Not_found -> None) with
    | None -> List.rev acc
    | Some i ->
      let name = Str.matched_group 1 subset in
      let value = Str.matched_group 2 subset in
      go (i + String.length (Str.matched_string subset)) ((name, value) :: acc)
  in
  go 0 []

let find_opt (re : Str.regexp) (s : string) (start : int) : int option =
  try Some (Str.search_forward re s start) with Not_found -> None

let doctype_open_re = Str.regexp_string "<!DOCTYPE"
let doctype_subset_re = Str.regexp "\\[\\([^]]*\\)\\][ \t\r\n]*>"

let expand_doctype_entities (s : string) : string =
  match find_opt doctype_open_re s 0 with
  | None -> s
  | Some start ->
    (match find_opt doctype_subset_re s start with
     | None -> s (* malformed / no internal subset -- leave untouched *)
     | Some _ ->
       let subset = Str.matched_group 1 s in
       let close_idx = Str.match_end () in
       let before = String.sub s 0 start in
       let after = String.sub s close_idx (String.length s - close_idx) in
       let stripped = before ^ after in
       let entities = extract_entity_defs subset in
       List.fold_left
         (fun acc (name, value) -> Str.global_replace (entity_ref_re name) value acc)
         stripped entities)

(* Load a companion data file (Turtle or RDF/XML, auto-detected by
   extension) with a file:// base for relative-IRI resolution. *)
let load_data_file path : triple list =
  match read_file path with
  | None -> []
  | Some raw ->
    let base = file_to_base_uri path in
    if Filename.check_suffix path ".ttl" then
      Parser_Turtle.parse_turtle_with_base raw base
    else
      let raw = expand_doctype_entities raw in
      Parser_RDFXML.parse_rdfxml_with_base base raw

(* ------------------------------------------------------------------ *)
(* Resolve a RIF <Import><location>URL</location></Import> URL to a
   local file under the test's vendored directory. Mirrors the
   basename + extension-fallback heuristic other runners in this repo
   use for the same vendored corpus (rif06's import omits the .rdf
   suffix in its <location>). Consumer-side I/O only (rule #11); the
   verified surface (Parser_RIFXML.extract_document_imports) supplies
   just the URL strings. *)
let resolve_import_local_path (test_dir : string) (url : string) : string option =
  let bn = Filename.basename url in
  let candidates =
    if Filename.check_suffix bn ".rdf" || Filename.check_suffix bn ".ttl"
    then [ bn ]
    else [ bn ^ ".rdf"; bn ^ ".ttl"; bn ]
  in
  let rec first_existing = function
    | [] -> None
    | c :: rest ->
      let p = Filename.concat test_dir c in
      if Sys.file_exists p then Some p else first_existing rest
  in
  first_existing candidates

(* ------------------------------------------------------------------ *)
(* The four vendored test cases (exhaustive lookup table; see module
   comment). *)

(* Closure to apply to a resolved <Import> companion graph before it is
   merged into the RIF premise. The RIF-XML <Import><profile>URL</profile>
   element names the entailment regime the imported document should be
   read under (Parser.RIFXML.fst reads it but does not expose it -- "RIF
   Core's entailment-profile selection is out of scope for this PR" per
   its own comment -- so the profile URL from each vendored .rif is
   hardcoded here alongside the rest of the 4-entry lookup table, not
   invented). Modeling_Brain_Anatomy's import declares
   `http://www.w3.org/ns/entailment/OWL-Direct`: its rule needs
   `rdf:type MaterialAnatomicalEntity` on individuals that the imported
   ontology only asserts via `rdf:type Gyrus` + `Gyrus rdfs:subClassOf
   MaterialAnatomicalEntity` -- without OWL-Direct closure the subclass
   membership never materialises and the rule body never matches.
   RDF_Combination_Blank_Node's import declares plain
   `http://www.w3.org/ns/entailment/RDF` (no subClassOf reasoning
   needed) so it is merged as-is. Both closure functions are existing
   F*-extracted primitives already used for the SPARQL "OWL-Direct" /
   "RDFS" entailment-regime dispatch in bin/w3c-runner/w3c_runner.ml --
   nothing new is added to the verified library for this. *)
type import_closure = No_Closure | OWL_Direct_Closure

let apply_import_closure (mode : import_closure) (g : triple list) : triple list =
  match mode with
  | No_Closure -> g
  | OWL_Direct_Closure ->
    let fuel = Z.of_int 100 in
    let g1 = RDF_Graph_Executable.owl_rl_closure_with_reflexivity g fuel in
    let g2 = Tableau.tableau_materialise g1 in
    RDF_Graph_Executable.owl_rl_closure_with_reflexivity g2 fuel

type rif_test = {
  rt_label      : string;   (* short id used in output, e.g. "rif01" *)
  rt_name       : string;   (* mf:name from the entailment manifest *)
  rt_rif_file   : string;   (* the *-premise.rif rule document *)
  rt_test_dir   : string;   (* dir to resolve <Import> companions in *)
  rt_data_ttl   : string;   (* manifest qt:data .ttl *)
  rt_query      : string;   (* manifest qt:query .rq *)
  rt_expected   : string;   (* manifest mf:result .srx *)
  rt_import_closure : import_closure; (* per <Import><profile>, see above *)
}

let entailment_dir = "third_party/testing/w3c/sparql/sparql11/entailment"
let rif_tc_dir = "third_party/testing/rif/tc"

let tests : rif_test list =
  [ { rt_label = "rif01";
      rt_name = "RIF Logical Entailment (referencing RIF XML)";
      rt_rif_file = Filename.concat rif_tc_dir
          "Logical_entailment_referencing_RIF_XML/rif01-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir
          "Logical_entailment_referencing_RIF_XML";
      rt_data_ttl = Filename.concat entailment_dir "rif01.ttl";
      rt_query    = Filename.concat entailment_dir "rif01.rq";
      rt_expected = Filename.concat entailment_dir "rif01.srx";
      rt_import_closure = No_Closure };
    { rt_label = "rif03";
      rt_name = "RIF Core WG tests: Frames";
      rt_rif_file = Filename.concat rif_tc_dir "Frames/Frames-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir "Frames";
      rt_data_ttl = Filename.concat entailment_dir "rif03.ttl";
      rt_query    = Filename.concat entailment_dir "rif03.rq";
      rt_expected = Filename.concat entailment_dir "rif03.srx";
      rt_import_closure = No_Closure };
    { rt_label = "rif04";
      rt_name = "RIF Core WG tests: Modeling Brain Anatomy";
      rt_rif_file = Filename.concat rif_tc_dir
          "Modeling_Brain_Anatomy/Modeling_Brain_Anatomy-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir "Modeling_Brain_Anatomy";
      rt_data_ttl = Filename.concat entailment_dir "rif04.ttl";
      rt_query    = Filename.concat entailment_dir "rif04.rq";
      rt_expected = Filename.concat entailment_dir "rif04.srx";
      (* <Import><profile>http://www.w3.org/ns/entailment/OWL-Direct</profile> *)
      rt_import_closure = OWL_Direct_Closure };
    { rt_label = "rif06";
      rt_name = "RIF Core WG tests: RDF Combination Blank Node";
      rt_rif_file = Filename.concat rif_tc_dir
          "RDF_Combination_Blank_Node/RDF_Combination_Blank_Node-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir "RDF_Combination_Blank_Node";
      rt_data_ttl = Filename.concat entailment_dir "rif06.ttl";
      rt_query    = Filename.concat entailment_dir "rif06.rq";
      rt_expected = Filename.concat entailment_dir "rif06.srx";
      (* <Import><profile>http://www.w3.org/ns/entailment/RDF</profile> --
         no subClassOf reasoning in this fixture; merged as-is. *)
      rt_import_closure = No_Closure } ]

(* ------------------------------------------------------------------ *)
(* Result comparison (deliberately small — only the two shapes the
   four vendored cases exercise: ASK/boolean and a SELECT with one or
   more fully-ground rows). Numeric-literal fallback mirrors
   bin/w3c-runner/w3c_runner.ml's term_equal so "10"^^xsd:integer
   compares correctly regardless of incidental lexical differences. *)

let xsd_numeric_types =
  [ "http://www.w3.org/2001/XMLSchema#integer";
    "http://www.w3.org/2001/XMLSchema#decimal";
    "http://www.w3.org/2001/XMLSchema#double";
    "http://www.w3.org/2001/XMLSchema#float" ]

let numeric_literal_equal l1 l2 =
  List.mem l1.datatype xsd_numeric_types && List.mem l2.datatype xsd_numeric_types &&
  (try float_of_string l1.lexical_form = float_of_string l2.lexical_form
   with _ -> false)

let lang_tag_equal t1 t2 =
  match t1, t2 with
  | None, None -> true
  | Some a, Some b -> String.lowercase_ascii a = String.lowercase_ascii b
  | _ -> false

let term_equal a b =
  match a, b with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode _, T_BNode _ -> true
  | T_Literal l1, T_Literal l2 ->
    (l1.lexical_form = l2.lexical_form && l1.datatype = l2.datatype
     && lang_tag_equal l1.lang_tag l2.lang_tag)
    || numeric_literal_equal l1 l2
  | _ -> false

let term_to_string = function
  | T_IRI i -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    "\"" ^ l.lexical_form ^ "\"" ^
    (match l.lang_tag with
     | Some lt -> "@" ^ lt
     | None -> "^^<" ^ l.datatype ^ ">")

let row_to_string row =
  String.concat ", " (List.map (fun (v, t) -> "?" ^ v ^ "=" ^ term_to_string t) row)

let binding_row_matches expected actual =
  List.for_all
    (fun (var, exp_val) ->
       match List.assoc_opt var actual with
       | Some act_val -> term_equal exp_val act_val
       | None -> false)
    expected

(* Multiset match: every expected row consumes exactly one distinct
   matching actual row (same convention as w3c_runner's
   results_match_with). *)
let results_match expected_rows actual_rows =
  if List.length expected_rows <> List.length actual_rows then false
  else
    let remaining = ref actual_rows in
    List.for_all
      (fun exp_row ->
         match List.partition (binding_row_matches exp_row) !remaining with
         | (_ :: rest, non) -> remaining := rest @ non; true
         | ([], _) -> false)
      expected_rows

(* ------------------------------------------------------------------ *)
(* Per-test pipeline. *)

type outcome = Pass | Fail of string

exception Test_error of string

let run_test verbose (tc : rif_test) : outcome =
  try
    (* 1. RIF-XML rule document. *)
    let rif_xml_raw =
      match read_file tc.rt_rif_file with
      | Some s -> s
      | None -> raise (Test_error ("cannot read " ^ tc.rt_rif_file))
    in
    let rif_xml = expand_doctype_entities rif_xml_raw in
    let imports, program =
      match Parser_RIFXML.parse_rif_program_with_imports rif_xml with
      | FStar_Pervasives_Native.Some (imports, program) -> (imports, program)
      | FStar_Pervasives_Native.None ->
        raise (Test_error
                 (Printf.sprintf
                    "Parser_RIFXML.parse_rif_program_with_imports failed on %s"
                    tc.rt_rif_file))
    in

    (* 2. Premise: the manifest .ttl (pointer triple, sometimes with
       ground facts as in rif01) plus every resolvable <Import>
       companion graph, merged. *)
    let ttl_triples = load_data_file tc.rt_data_ttl in
    let import_triples =
      List.concat_map
        (fun url ->
           match resolve_import_local_path tc.rt_test_dir url with
           | None ->
             if verbose then
               Printf.eprintf "[%s] import URL did not resolve locally: %s\n"
                 tc.rt_label url;
             []
           | Some path -> apply_import_closure tc.rt_import_closure (load_data_file path))
        imports
    in
    let premise = ttl_triples @ import_triples in

    (* 3. Saturate. Prims.nat is Z.t in this codegen (fstar.lib's
       Prims.ml: `type int = Z.t`, `type nat = int`) -- fuel MUST be
       constructed via Z.of_int, not a bare OCaml int. *)
    let fuel = Z.of_int 100 in
    let saturated = RIF_Core_Eval.fixpoint premise program fuel in

    if verbose then
      Printf.eprintf "[%s] premise=%d imports=%d saturated=%d\n"
        tc.rt_label (List.length premise) (List.length import_triples)
        (List.length saturated);

    (* 4. Run the .rq against the saturated graph through the real
       SPARQL evaluator (OWL_QueryEval wraps SPARQL11_Algebra with the
       OWL query-rewrite pass, which is a structural no-op for these
       plain queries -- same dispatch shape as w3c_runner.ml). *)
    let query_content =
      match read_file tc.rt_query with
      | Some s -> s
      | None -> raise (Test_error ("cannot read " ^ tc.rt_query))
    in
    let query =
      match SPARQL11_Parser.parse_sparql_with_base
              (Some (file_to_base_uri tc.rt_query)) query_content with
      | SPARQL11_Parser.ParseOk (q, _rest) -> q
      | SPARQL11_Parser.ParseErr msg ->
        raise (Test_error ("SPARQL parse error: " ^ msg))
    in
    (* Blank nodes in the query pattern (rif06: `[] a ex:named`) act as
       existential variables under an entailment regime -- same rewrite
       w3c_runner.ml applies for its RDF/RDFS/OWL/RIF regime dispatch. *)
    let query =
      { query with
        SPARQL11_Algebra.q_pattern =
          SPARQL11_Algebra.rewrite_query_bnodes_pattern query.SPARQL11_Algebra.q_pattern }
    in
    let dataset = { ds_default = saturated; ds_named = [] } in

    let expected_content =
      match read_file tc.rt_expected with
      | Some s -> s
      | None -> raise (Test_error ("cannot read " ^ tc.rt_expected))
    in

    (match query.SPARQL11_Algebra.q_form with
     | SPARQL11_Algebra.QF_Ask ->
       let actual = OWL_QueryEval.eval_ask_query_owl query saturated dataset in
       (match Parser_SRX.parse_srx_boolean expected_content with
        | FStar_Pervasives_Native.Some expected ->
          if actual = expected then Pass
          else Fail (Printf.sprintf "ASK mismatch: expected %b, got %b" expected actual)
        | FStar_Pervasives_Native.None ->
          Fail (Printf.sprintf "could not parse expected boolean from %s" tc.rt_expected))
     | _ ->
       let actual_rows = OWL_QueryEval.eval_select_query_owl query saturated dataset in
       (match Parser_SRX.parse_srx_results expected_content with
        | FStar_Pervasives_Native.Some (_vars, expected_rows) ->
          if results_match expected_rows actual_rows then Pass
          else begin
            if verbose then begin
              Printf.eprintf "[%s] EXPECTED (%d rows):\n" tc.rt_label (List.length expected_rows);
              List.iter (fun r -> Printf.eprintf "    %s\n" (row_to_string r)) expected_rows;
              Printf.eprintf "[%s] ACTUAL (%d rows):\n" tc.rt_label (List.length actual_rows);
              List.iter (fun r -> Printf.eprintf "    %s\n" (row_to_string r)) actual_rows
            end;
            Fail (Printf.sprintf "results mismatch: expected %d row(s), got %d"
                    (List.length expected_rows) (List.length actual_rows))
          end
        | FStar_Pervasives_Native.None ->
          Fail (Printf.sprintf "could not parse expected bindings from %s" tc.rt_expected)))
  with
  | Test_error msg -> Fail msg
  | exn -> Fail (Printf.sprintf "exception: %s" (Printexc.to_string exn))

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "RIF Core test runner -- the 4 vendored W3C RIF test cases\n\
     (third_party/testing/rif/tc/), driven end-to-end through\n\
     Parser_RIFXML + RIF_Core_Eval.fixpoint + the real SPARQL 1.1\n\
     evaluator. Covers exactly rif01/rif03/rif04/rif06 from the SPARQL\n\
     1.1 entailment manifest -- a hardcoded 4-entry lookup table, not a\n\
     general manifest walker.\n\
     \n\
     Usage:\n\
     \  ./rif_runner              Run all 4 cases\n\
     \  ./rif_runner -v|--verbose Print expected/actual on FAIL\n\
     \  ./rif_runner --help       Show this help\n"

let () =
  let verbose = ref false in
  Array.to_list Sys.argv |> List.tl |> List.iter (function
    | "-v" | "--verbose" -> verbose := true
    | "--help" | "-h" -> print_help (); exit 0
    | arg ->
      Printf.eprintf "rif_runner: unrecognized argument %s (try --help)\n" arg;
      exit 2);
  let results =
    List.map
      (fun tc ->
         let outcome = run_test !verbose tc in
         (match outcome with
          | Pass -> Printf.printf "PASS %s (%s)\n" tc.rt_label tc.rt_name
          | Fail msg -> Printf.printf "FAIL %s (%s): %s\n" tc.rt_label tc.rt_name msg);
         outcome)
      tests
  in
  let pass, fail =
    List.fold_left
      (fun (p, f) -> function Pass -> (p + 1, f) | Fail _ -> (p, f + 1))
      (0, 0) results
  in
  let total = List.length tests in
  Printf.printf "========================================\n";
  Printf.printf "rif: %d pass, %d fail (out of %d)\n" pass fail total;
  if fail > 0 then exit 1
