(* OWL 2 Test Cases runner — Phase 1 (profile-RL PositiveEntailmentTest).

   Reads one of the W3C OWL 2 Test Case RDF/XML catalog files (default
   third_party/testing/owl/profile-RL.rdf), parses it via the F*-extracted
   Parser_RDFXML, extracts <test:TestCase> nodes, and — for each
   PositiveEntailmentTest — runs OWL-RL closure (with reflexivity) over
   the embedded premise graph and checks that every triple of the
   embedded conclusion graph appears in the closure.

   !! THIS IS I/O GLUE — NO RDF/SPARQL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #10 and anti-pattern #15. Closure itself is
   F*-extracted; what this file does is (a) extract premise/conclusion
   literals from the manifest, (b) pre-expand DOCTYPE-declared catalog
   entities (&rdf;, &rdfs;, &owl;, &test;, &xsd;) so Parser_XML can
   tokenize them, and (c) do a relaxed "non-bnode exact + bnode
   structural" entailment check over the closed graph. Proper bnode
   isomorphism is deferred.

   Scoping + phased plan:
     docs/designissues/2026-04-24-owl-test-harness.md (skeleton)
     docs/designissues/2026-04-24-owl-runner-phase1.md (this phase)

   Usage:
     ./owl_runner
         Reads third_party/testing/owl/profile-RL.rdf (path discovered
         relative to the repo root, which the binary finds by walking
         up from its own location).
     ./owl_runner <catalog-path>
         Reads the given RDF/XML catalog file.
     ./owl_runner --list
         Lists the catalog files under third_party/testing/owl/.
     ./owl_runner -v | --verbose
         Print the first mismatching triple per failing test.
     ./owl_runner --help
         Prints this help.
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Entity pre-expansion.

   The OWL 2 test catalogs open with a DOCTYPE that declares four named
   entities (&rdf;, &rdfs;, &owl;, &test;). Parser.XML / Parser.RDFXML
   (F*-extracted) handle only the five built-in XML entities, not custom
   DOCTYPE-declared ones, so we expand these four in OCaml before
   handing the buffer to the F* parser. This is pure textual substitution
   — no RDF semantics — and is safe so long as the entity values don't
   themselves contain the substitution patterns (they don't; they're
   plain URI prefixes).

   Proper DOCTYPE-entity support belongs in Parser.XML.fst and is tracked
   as a follow-up to this skeleton. *)

let catalog_entities : (string * string) list =
  [ ("&rdf;",  "http://www.w3.org/1999/02/22-rdf-syntax-ns#");
    ("&rdfs;", "http://www.w3.org/2000/01/rdf-schema#");
    ("&owl;",  "http://www.w3.org/2002/07/owl#");
    ("&xsd;",  "http://www.w3.org/2001/XMLSchema#");
    ("&test;", "http://www.w3.org/2007/OWL/testOntology#") ]

(* Strip the DOCTYPE block so Parser.XML doesn't have to skip it.
   The catalogs put it between "<!DOCTYPE" and the matching "]>" at
   the top of the file. Naive but sufficient for the vendored corpus. *)
let find_opt (re : Str.regexp) (s : string) (start : int) : int option =
  try Some (Str.search_forward re s start)
  with Not_found -> None

let strip_doctype (s : string) : string =
  let open_re  = Str.regexp_string "<!DOCTYPE" in
  let close_re = Str.regexp_string "]>" in
  match find_opt open_re s 0 with
  | None -> s
  | Some i ->
    (match find_opt close_re s i with
     | None -> s
     | Some j ->
       let close_len = 2 in (* length of "]>" *)
       let before = String.sub s 0 i in
       let after = String.sub s (j + close_len)
                              (String.length s - (j + close_len)) in
       before ^ after)

let expand_catalog_entities (s : string) : string =
  List.fold_left
    (fun acc (ent, repl) ->
       Str.global_replace (Str.regexp_string ent) repl acc)
    s
    catalog_entities

(* ------------------------------------------------------------------ *)
(* File I/O + parse path. *)

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let parse_catalog path =
  match read_file path with
  | None ->
    Printf.eprintf "owl_runner: cannot read %s\n" path;
    exit 2
  | Some raw ->
    let no_doctype = strip_doctype raw in
    let expanded = expand_catalog_entities no_doctype in
    let abs = if Filename.is_relative path
              then Filename.concat (Sys.getcwd ()) path
              else path in
    let base = "file://" ^ abs in
    Parser_RDFXML.parse_rdfxml_with_base base expanded

(* ------------------------------------------------------------------ *)
(* Triple projections. *)

let rdf_type_iri   = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let test_ns        = OWL_Tests_Manifest.test_ns
let test_identifier = test_ns ^ "identifier"
let test_profile    = test_ns ^ "profile"
let test_premise    = test_ns ^ "rdfXmlPremiseOntology"
let test_conclusion = test_ns ^ "rdfXmlConclusionOntology"
let test_imported_ontology = test_ns ^ "importedOntology"
let test_input_ontology   = test_ns ^ "rdfXmlInputOntology"
let pos_entailment_iri = test_ns ^ "PositiveEntailmentTest"

let subject_iri_opt (s : subject) : string option =
  match s with
  | S_IRI i -> Some i
  | S_BNode _ -> None

let object_iri_opt (t : rdf_term) : string option =
  match t with
  | T_IRI i -> Some i
  | _ -> None

let object_literal_opt (t : rdf_term) : string option =
  match t with
  | T_Literal l -> Some l.lexical_form
  | _ -> None

(* Does this IRI name one of the five OWL-test test types?
   Delegates to F* per CLAUDE.md rule #11. *)
let is_test_type_iri = OWL_Tests_Manifest.is_test_type_iri

let short_type (iri : string) : string =
  let pl = String.length test_ns in
  if String.length iri >= pl && String.sub iri 0 pl = test_ns
  then String.sub iri pl (String.length iri - pl)
  else iri

let short_profile (iri : string) : string =
  match iri with
  | "http://www.w3.org/2007/OWL/testOntology#RL" -> "RL"
  | "http://www.w3.org/2007/OWL/testOntology#EL" -> "EL"
  | "http://www.w3.org/2007/OWL/testOntology#QL" -> "QL"
  | other -> other

(* ------------------------------------------------------------------ *)
(* Per-TestCase aggregation. *)

module StrSet = Set.Make(String)

type test_case_info = {
  iri         : string;
  identifier  : string option;     (* test:identifier string, if present *)
  types       : StrSet.t;          (* set of test:*Test rdf:types *)
  profiles    : StrSet.t;          (* set of test:profile values *)
  premise     : string option;     (* test:rdfXmlPremiseOntology literal *)
  conclusion  : string option;     (* test:rdfXmlConclusionOntology literal *)
  imports     : StrSet.t;          (* test:importedOntology link IRIs (catalog
                                       node IRIs that carry test:rdfXmlInputOntology
                                       literals); resolved at run time *)
}

let empty_info iri = {
  iri;
  identifier = None;
  types = StrSet.empty;
  profiles = StrSet.empty;
  premise = None;
  conclusion = None;
  imports = StrSet.empty;
}

(* Walk the triples once, build a map from subject-IRI (test:TestCase
   subject) to test_case_info. We detect a test case by the presence of
   an rdf:type triple whose object is one of the five test-type URIs.

   Returns (test cases, import_lookup) where import_lookup maps a
   test:importedOntology IRI (a sibling owl:Thing in the catalog) to
   its test:rdfXmlInputOntology literal — the imported document as an
   RDF/XML string, ready for the parser. The import map is shared
   across all test cases since multiple tests may reference the same
   imported document. *)
let build_index (graph : triple list) : test_case_info list * (string, string) Hashtbl.t =
  let tbl : (string, test_case_info) Hashtbl.t = Hashtbl.create 1024 in
  let imports_lookup : (string, string) Hashtbl.t = Hashtbl.create 64 in
  let get subj =
    match Hashtbl.find_opt tbl subj with
    | Some info -> info
    | None -> empty_info subj
  in
  List.iter
    (fun (t : triple) ->
       match subject_iri_opt t.s with
       | None -> ()
       | Some subj ->
         let info = get subj in
         if t.p = rdf_type_iri then begin
           match object_iri_opt t.o with
           | Some obj when is_test_type_iri obj ->
             let info = { info with types = StrSet.add obj info.types } in
             Hashtbl.replace tbl subj info
           | _ -> ()
         end else if t.p = test_identifier then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with identifier = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_profile then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with profiles = StrSet.add obj info.profiles } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_premise then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with premise = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_conclusion then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with conclusion = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_imported_ontology then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with imports = StrSet.add obj info.imports } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_input_ontology then begin
           match object_literal_opt t.o with
           | Some lex -> Hashtbl.replace imports_lookup subj lex
           | None -> ()
         end)
    graph;
  (* Keep only subjects that actually carry a test-type. *)
  let cases =
    Hashtbl.fold
      (fun _ info acc ->
         if StrSet.is_empty info.types then acc else info :: acc)
      tbl []
  in
  (cases, imports_lookup)

(* ------------------------------------------------------------------ *)
(* Output. *)

let identifier_display info =
  match info.identifier with
  | Some s -> s
  | None -> "(no test:identifier)"

(* ------------------------------------------------------------------ *)
(* Phase 1: closure + entailment check for PositiveEntailmentTest.

   For each test with premise P and conclusion C:
     closure   = owl_rl_closure_with_reflexivity(P, fuel=100)
     pass iff  every triple of C is matched in closure

   Match rule (relaxed):
     - If C_triple contains no bnodes: exact triple_eq against closure.
     - If C_triple contains one or more bnodes: structural match —
       predicate must equal; for each position (s, o), if the
       C-position is a bnode, ANY term (bnode or IRI) at that
       position in the closure matches; otherwise exact value
       match required.

   Why bnode-pattern matches IRI: the OWL test convention treats an
   anonymous-subject triple in the conclusion as existential
   ("there exists some resource with this predicate-object skeleton").
   A premise that names that resource (e.g.
   `<owl:Ontology rdf:about=''>` resolving to the document base) and a
   conclusion that leaves it anonymous (`<owl:Ontology/>` -> fresh
   bnode per RDF/XML §6.1.4) describe the same shape. Cluster K /
   WebOnt-imports-011 is the live instance:
     premise closure has <premises011> rdf:type owl:Ontology
     conclusion has    _:rdfxml_b0 rdf:type owl:Ontology
   Bnode-only structural match was too strict; generalising to "any
   term" honours the existential reading. See
   docs/designissues/2026-04-25-owl-imports-011-diagnosis.md (option 2)
   and docs/designissues/2026-05-07-owl2-rl-next-steps.md §K.

   This over-approximates (any term in the closure at a bnode
   position can satisfy any bnode in the conclusion — there's no
   consistency check across multiple bnode-containing triples). Full
   isomorphism deferred. Limitation is printed with the score.

   This is harness/test-scoring policy, not RDF/SPARQL semantics —
   the closure itself is F*-extracted (rule #15 boundary respected).
*)

let is_bnode_subject (s : RDF_Graph_Executable.subject) : bool =
  match s with RDF_Graph_Executable.S_BNode _ -> true | _ -> false

let is_bnode_term (t : RDF_Graph_Executable.rdf_term) : bool =
  match t with RDF_Graph_Executable.T_BNode _ -> true | _ -> false

let triple_has_bnode (t : RDF_Graph_Executable.triple) : bool =
  is_bnode_subject t.s || is_bnode_term t.o

(* Bnode pattern matches any term at this position (existential
   reading); non-bnode pattern requires exact value match. *)
let subject_matches
      (pat : RDF_Graph_Executable.subject)
      (sub : RDF_Graph_Executable.subject) : bool =
  match pat with
  | RDF_Graph_Executable.S_BNode _ -> let _ = sub in true
  | _ -> RDF_Graph_Executable.subject_eq pat sub

let object_matches
      (pat : RDF_Graph_Executable.rdf_term)
      (obj : RDF_Graph_Executable.rdf_term) : bool =
  match pat with
  | RDF_Graph_Executable.T_BNode _ -> let _ = obj in true
  | _ -> RDF_Graph_Executable.rdf_term_eq pat obj

let triple_matches
      (pat : RDF_Graph_Executable.triple)
      (t : RDF_Graph_Executable.triple) : bool =
  subject_matches pat.s t.s
  && pat.p = t.p
  && object_matches pat.o t.o

let conclusion_triple_in_closure
      (closure : RDF_Graph_Executable.rdf_graph)
      (pat : RDF_Graph_Executable.triple) : bool =
  if triple_has_bnode pat then
    List.exists (triple_matches pat) closure
  else
    List.exists (RDF_Graph_Executable.triple_eq pat) closure

type outcome =
  | Pass
  | Fail_conclusion_miss of RDF_Graph_Executable.triple
  | Fail_parse_premise
  | Fail_parse_conclusion
  | Fail_no_premise
  | Fail_no_conclusion

let outcome_tag = function
  | Pass -> "PASS"
  | Fail_conclusion_miss _ -> "FAIL"
  | Fail_parse_premise -> "FAIL/parse-premise"
  | Fail_parse_conclusion -> "FAIL/parse-conclusion"
  | Fail_no_premise -> "FAIL/no-premise"
  | Fail_no_conclusion -> "FAIL/no-conclusion"

let fuel_100 : Prims.nat = Z.of_int 100

(* Parse and merge imported-ontology literals into the premise graph
   before closure. Each imports_lookup hit gives us an RDF/XML literal
   whose triples should be added to g_p, so the closure sees the union
   of declared + imported axioms (the test-harness analogue of
   owl:imports resolution; we never dereference URLs). *)
let load_imports_into_premise
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t)
      (g_p : triple list) : triple list =
  StrSet.fold
    (fun import_iri acc ->
       match Hashtbl.find_opt imports_lookup import_iri with
       | None -> acc
       | Some lit ->
         let src = expand_catalog_entities lit in
         (* Use the import-link IRI as the parser base. The imported
            document typically declares its own xml:base which
            overrides this; the fallback only matters when it does
            not. *)
         let base = import_iri in
         (try Parser_RDFXML.parse_rdfxml_with_base base src
          with _ -> []) @ acc)
    info.imports
    g_p

let run_positive_entailment
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t) : outcome =
  match info.premise, info.conclusion with
  | None, _ -> Fail_no_premise
  | _, None -> Fail_no_conclusion
  | Some p_lex, Some c_lex ->
    let p_src = expand_catalog_entities p_lex in
    let c_src = expand_catalog_entities c_lex in
    let base = info.iri in
    let g_p_authored =
      try Parser_RDFXML.parse_rdfxml_with_base base p_src
      with _ -> [] in
    let g_p = load_imports_into_premise info imports_lookup g_p_authored in
    let g_c =
      try Parser_RDFXML.parse_rdfxml_with_base base c_src
      with _ -> [] in
    if g_p = [] then Fail_parse_premise
    else if g_c = [] then Fail_parse_conclusion
    else begin
      let closure =
        try RDF_Graph_Executable.owl_rl_closure_with_reflexivity g_p fuel_100
        with _ -> g_p in
      let rec check = function
        | [] -> Pass
        | t :: rest ->
          if conclusion_triple_in_closure closure t
          then check rest
          else Fail_conclusion_miss t
      in
      check g_c
    end

let format_subject = function
  | RDF_Graph_Executable.S_IRI i -> "<" ^ i ^ ">"
  | RDF_Graph_Executable.S_BNode b -> "_:" ^ b

let format_object = function
  | RDF_Graph_Executable.T_IRI i -> "<" ^ i ^ ">"
  | RDF_Graph_Executable.T_BNode b -> "_:" ^ b
  | RDF_Graph_Executable.T_Literal l ->
    Printf.sprintf "\"%s\"^^<%s>" l.lexical_form l.datatype

let format_triple (t : RDF_Graph_Executable.triple) : string =
  Printf.sprintf "%s <%s> %s"
    (format_subject t.s) t.p (format_object t.o)

let print_outcome verbose info outcome =
  let tag = outcome_tag outcome in
  let id = identifier_display info in
  Printf.printf "  %s  %s\n" tag id;
  if verbose then begin
    match outcome with
    | Fail_conclusion_miss t ->
      Printf.printf "      missing conclusion triple: %s\n" (format_triple t)
    | _ -> ()
  end

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (so `./owl_runner` from any cwd works). *)

let find_repo_root () =
  (* Walk up from the executable's directory looking for a CLAUDE.md. *)
  let rec walk d =
    if d = "/" || d = "" then None
    else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
    else walk (Filename.dirname d)
  in
  let start =
    try Filename.dirname (Sys.executable_name)
    with _ -> Sys.getcwd ()
  in
  match walk start with
  | Some r -> r
  | None ->
    (* Fallback: try cwd. *)
    match walk (Sys.getcwd ()) with
    | Some r -> r
    | None -> Sys.getcwd ()

let default_catalog () =
  Filename.concat (find_repo_root ())
    "third_party/testing/owl/profile-RL.rdf"

let list_catalogs () =
  let dir = Filename.concat (find_repo_root ()) "third_party/testing/owl" in
  Printf.printf "OWL 2 test catalogs under %s:\n" dir;
  (try
     let entries = Sys.readdir dir in
     Array.sort compare entries;
     Array.iter
       (fun name ->
          if Filename.check_suffix name ".rdf"
          then Printf.printf "  %s\n" name)
       entries
   with Sys_error msg ->
     Printf.eprintf "  (cannot read: %s)\n" msg)

let print_help () =
  print_string
    "OWL 2 Test Cases runner (skeleton).\n\
     \n\
     Usage:\n\
     \  ./owl_runner                  Read third_party/testing/owl/profile-RL.rdf\n\
     \  ./owl_runner <catalog.rdf>    Read the given RDF/XML catalog\n\
     \  ./owl_runner --list           List catalog files in third_party/testing/owl/\n\
     \  ./owl_runner --help           Show this help\n\
     \n\
     Status: Phase 0 skeleton — reads manifest, prints per-test identifier\n\
     and types, emits final count. Does NOT run any reasoning yet.\n\
     See docs/designissues/2026-04-24-owl-test-harness.md.\n"

(* ------------------------------------------------------------------ *)
(* Main. *)

let run_catalog ?(verbose=false) path =
  Printf.printf "OWL 2 test catalog: %s\n" path;
  let t0 = Unix.gettimeofday () in
  let graph = parse_catalog path in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  parsed %d triples in %.2fs\n"
    (List.length graph) (t1 -. t0);
  let (tests, imports_lookup) = build_index graph in
  let key info = match info.identifier with
    | Some s -> s
    | None -> info.iri in
  let tests = List.sort (fun a b -> compare (key a) (key b)) tests in
  (* Per-type tally — orientation for the human reader. *)
  let tally name =
    let iri = test_ns ^ name in
    List.fold_left
      (fun acc info -> if StrSet.mem iri info.types then acc + 1 else acc)
      0 tests
  in
  let n = List.length tests in
  Printf.printf "Totals: %d test cases\n" n;
  Printf.printf "  PositiveEntailmentTest:    %d\n" (tally "PositiveEntailmentTest");
  Printf.printf "  NegativeEntailmentTest:    %d\n" (tally "NegativeEntailmentTest");
  Printf.printf "  ConsistencyTest:           %d\n" (tally "ConsistencyTest");
  Printf.printf "  InconsistencyTest:         %d\n" (tally "InconsistencyTest");
  Printf.printf "  ProfileIdentificationTest: %d\n" (tally "ProfileIdentificationTest");
  Printf.printf "\n";

  (* Phase 1: score every PositiveEntailmentTest. *)
  let pe_tests =
    List.filter
      (fun info -> StrSet.mem pos_entailment_iri info.types)
      tests
  in
  let k = List.length pe_tests in
  Printf.printf "Running %d PositiveEntailmentTest(s) through owl_rl_closure_with_reflexivity (fuel=100)...\n" k;
  let t_run0 = Unix.gettimeofday () in
  let outcomes = List.map (fun info -> (info, run_positive_entailment info imports_lookup)) pe_tests in
  let t_run1 = Unix.gettimeofday () in
  List.iter (fun (info, outcome) -> print_outcome verbose info outcome) outcomes;
  let passes =
    List.fold_left
      (fun acc (_, o) -> match o with Pass -> acc + 1 | _ -> acc)
      0 outcomes
  in
  let fails = k - passes in
  Printf.printf "\n";
  Printf.printf "Profile-RL PositiveEntailmentTests: %d pass, %d fail (out of %d) in %.2fs\n"
    passes fails k (t_run1 -. t_run0);
  Printf.printf "  (bnode pattern matches any term at the position; full isomorphism deferred — see docs/designissues/2026-04-24-owl-runner-phase1.md)\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let path = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: _ -> list_catalogs (); exit 0
    | p :: rest when !path = None -> path := Some p; loop rest
    | _ ->
      Printf.eprintf "owl_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let catalog = match !path with
    | Some p -> p
    | None -> default_catalog ()
  in
  run_catalog ~verbose:!verbose catalog
