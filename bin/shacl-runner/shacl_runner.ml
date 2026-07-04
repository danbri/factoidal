(* SHACL Core W3C test-suite runner — slice 1 (issue #181).

   Walks the vendored W3C data-shapes-test-suite manifest hierarchy
   (third_party/testing/shacl/data-shapes-test-suite/tests/core/),
   following `mf:include` (a repeated triple, not an RDF list, in this
   suite — see core/node/manifest.ttl for the pattern) down to leaf
   test files, each of which declares one or more `sht:Validate`
   entries directly. For each entry:
     - loads the dataGraph / shapesGraph (usually the SAME document,
       self-referenced via `<>`; a few tests split into sibling
       `*-data.ttl` / `*-shapes.ttl` files, resolved by relative IRI);
     - parses the shapes graph via the F*-extracted
       SHACL_Validation.parse_shape_from_graph;
     - runs SHACL_Validation.validate against the data graph;
     - compares ONLY the report's sh:conforms flag against the
       manifest's expected `mf:result [ ... sh:conforms "..."^^xsd:boolean ]`
       (the slice-1 floor from the SHACL brief — full report-detail
       isomorphism, e.g. exact sh:resultPath / sh:sourceConstraintComponent
       matching, is Phase 2 follow-up work; tests that only differ on
       report DETAIL still PASS here as long as conforms matches, and
       tests whose constraint isn't implemented yet FAIL honestly
       because the computed conforms flag won't match).

   !! THIS IS I/O GLUE — NO SHACL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All shape parsing,
   target computation, path evaluation, and constraint evaluation
   live in formal/fstar/SHACL.Validation.fst. This file only does
   file I/O, manifest traversal, and a single boolean comparison.

   Usage:
     ./shacl_runner                Run the default core manifest
     ./shacl_runner <manifest.ttl> Run a specific manifest.ttl
     ./shacl_runner --list         List discovered test entries (no execution)
     ./shacl_runner -v|--verbose   Show skip reasons too (FAIL always shown)
     ./shacl_runner --help         Show this help
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to jsonld_runner.ml / rdfc10_runner.ml). *)

let find_repo_root () =
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
    (match walk (Sys.getcwd ()) with
     | Some r -> r
     | None -> Sys.getcwd ())

let manifest_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root
      "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl";
    "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl"

(* ------------------------------------------------------------------ *)
(* File I/O + Turtle parsing (base-IRI handling parallels rdfc10_runner). *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let b = Bytes.create n in
    really_input ic b 0 n;
    close_in ic;
    Some (Bytes.to_string b)
  with Sys_error _ -> None

let abs_path p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p

let file_uri p = "file://" ^ abs_path p

(* Inverse of file_uri, for resolving a dataGraph/shapesGraph IRI that
   points at a sibling file back to a loadable path. *)
let path_of_file_iri (iri : string) : string option =
  let prefix = "file://" in
  let plen = String.length prefix in
  if String.length iri >= plen && String.sub iri 0 plen = prefix
  then Some (String.sub iri plen (String.length iri - plen))
  else None

let parse_ttl_file (path : string) : (rdf_graph * string) option =
  match read_file path with
  | None -> None
  | Some raw ->
    let base = file_uri path in
    Some (Parser_Turtle.parse_turtle_with_base raw base, base)

(* ------------------------------------------------------------------ *)
(* Thin RDF-graph accessors over an rdf_term "subject". *)

let term_to_subj_opt (t : rdf_term) : subject option =
  match term_to_subject t with
  | FStar_Pervasives_Native.Some s -> Some s
  | FStar_Pervasives_Native.None -> None

let objs_of (g : rdf_graph) (subj_term : rdf_term) (pred : string) : rdf_term list =
  match term_to_subj_opt subj_term with
  | None -> []
  | Some s -> find_objects g s pred

let obj1_of (g : rdf_graph) (subj_term : rdf_term) (pred : string) : rdf_term option =
  match objs_of g subj_term pred with
  | [] -> None
  | h :: _ -> Some h

let iri_str (t : rdf_term) : string option =
  match t with T_IRI i -> Some i | _ -> None

let bool_of_lit (t : rdf_term option) : bool option =
  match t with
  | Some (T_Literal l) -> Some (l.lexical_form = "true" || l.lexical_form = "1")
  | _ -> None

let string_of_lit (t : rdf_term option) : string option =
  match t with
  | Some (T_Literal l) -> Some l.lexical_form
  | _ -> None

(* ------------------------------------------------------------------ *)
(* SHACL test vocabulary. *)

let mf_ns  = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
let sht_ns = "http://www.w3.org/ns/shacl-test#"
let sh_ns  = "http://www.w3.org/ns/shacl#"
let rdf_type_iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let mf_include = mf_ns ^ "include"
let mf_action  = mf_ns ^ "action"
let mf_result  = mf_ns ^ "result"
let mf_name    = mf_ns ^ "name"
(* This suite labels tests with rdfs:label, not mf:name (see any
   core/*.ttl fixture) — try both, mf:name first per the manifest
   vocabulary's own spec. *)
let rdfs_label = "http://www.w3.org/2000/01/rdf-schema#label"
let sht_Validate    = sht_ns ^ "Validate"
let sht_dataGraph   = sht_ns ^ "dataGraph"
let sht_shapesGraph = sht_ns ^ "shapesGraph"
let sh_conforms     = sh_ns ^ "conforms"

(* ------------------------------------------------------------------ *)
(* Per-test record. Fields stay `option` rather than being filtered
   out at collection time, so a malformed/incomplete manifest entry
   surfaces as an honest SKIP with a reason instead of silently
   vanishing from the total (anti-pattern #25 discipline). *)

type test_case = {
  tc_name : string;
  tc_file : string;
  tc_data_graph : rdf_graph option;
  tc_shapes_graph : rdf_graph option;
  tc_expect_conforms : bool option;
}

(* Resolve a dataGraph/shapesGraph object to a parsed graph: reuse the
   current file's own graph when it self-references (`<>`, the
   overwhelmingly common case), else load the sibling file it names
   (e.g. path-complex-002-data.ttl / path-complex-002-shapes.ttl). *)
let resolve_graph_ref ~(own_graph : rdf_graph) ~(own_base : string) (t : rdf_term) : rdf_graph option =
  match iri_str t with
  | None -> None
  | Some iri ->
    if iri = own_base then Some own_graph
    else
      (match path_of_file_iri iri with
       | Some p ->
         (match parse_ttl_file p with
          | Some (g, _) -> Some g
          | None -> None)
       | None -> None)

let subjects_typed (g : rdf_graph) (iri : string) : rdf_term list =
  List.filter_map
    (fun tr -> if tr.p = rdf_type_iri
               then (match tr.o with T_IRI i when i = iri -> Some (subject_to_term tr.s) | _ -> None)
               else None)
    g

let rec collect_from_file (visited : string list ref) (path : string) : test_case list =
  let abs = abs_path path in
  if List.mem abs !visited then []
  else begin
    visited := abs :: !visited;
    match parse_ttl_file path with
    | None ->
      Printf.eprintf "shacl_runner: cannot read %s\n" path;
      []
    | Some (g, base) ->
      let root_term = T_IRI base in
      let included =
        List.concat_map
          (fun inc_term ->
             match iri_str inc_term with
             | None -> []
             | Some inc_iri ->
               (match path_of_file_iri inc_iri with
                | Some inc_path -> collect_from_file visited inc_path
                | None -> []))
          (objs_of g root_term mf_include)
      in
      let own_tests =
        List.map
          (fun t ->
             let name =
               match string_of_lit (obj1_of g t mf_name) with
               | Some n -> n
               | None ->
                 (match string_of_lit (obj1_of g t rdfs_label) with
                  | Some n -> n
                  | None -> (match t with T_IRI i -> i | T_BNode b -> "_:" ^ b | _ -> "<test>"))
             in
             let action = obj1_of g t mf_action in
             let result = obj1_of g t mf_result in
             let dgraph =
               match action with
               | None -> None
               | Some act ->
                 (match obj1_of g act sht_dataGraph with
                  | None -> None
                  | Some dgt -> resolve_graph_ref ~own_graph:g ~own_base:base dgt)
             in
             let sgraph =
               match action with
               | None -> None
               | Some act ->
                 (match obj1_of g act sht_shapesGraph with
                  | None -> None
                  | Some sgt -> resolve_graph_ref ~own_graph:g ~own_base:base sgt)
             in
             let expect =
               match result with
               | None -> None
               | Some res -> bool_of_lit (obj1_of g res sh_conforms)
             in
             { tc_name = name; tc_file = path;
               tc_data_graph = dgraph; tc_shapes_graph = sgraph;
               tc_expect_conforms = expect })
          (subjects_typed g sht_Validate)
      in
      included @ own_tests
  end

(* ------------------------------------------------------------------ *)
(* Per-test execution. *)

type outcome = Pass | Fail of string | Skip of string

let run_test (tc : test_case) : outcome =
  match tc.tc_data_graph, tc.tc_shapes_graph, tc.tc_expect_conforms with
  | None, _, _ -> Skip "no dataGraph resolved from mf:action"
  | _, None, _ -> Skip "no shapesGraph resolved from mf:action"
  | _, _, None -> Skip "mf:result has no sh:conforms boolean"
  | Some data, Some shapes_g, Some expect ->
    (try
       let sg = SHACL_Validation.parse_shape_from_graph shapes_g in
       let report = SHACL_Validation.validate data sg in
       let got = report.SHACL_Validation.conforms in
       if got = expect then Pass
       else Fail (Printf.sprintf "expected sh:conforms %b, got %b" expect got)
     with e -> Fail (Printf.sprintf "exception: %s" (Printexc.to_string e)))

(* ------------------------------------------------------------------ *)
(* Suite run. *)

let run_manifest ~verbose ~list_only manifest_path =
  Printf.printf "=== SHACL Core W3C Test Runner (slice 1, sh:conforms-only) ===\n";
  Printf.printf "Manifest: %s\n\n" manifest_path;
  let tests = collect_from_file (ref []) manifest_path in
  let total = List.length tests in
  Printf.printf "Totals: %d test entries\n\n" total;
  if list_only then
    List.iter (fun tc -> Printf.printf "  %-40s (%s)\n" tc.tc_name tc.tc_file) tests
  else begin
    let n = ref 0 in
    let outcomes =
      List.map
        (fun tc ->
           incr n;
           Printf.eprintf "  [%d/%d] %s%!" !n total tc.tc_name;
           let o = run_test tc in
           let tag = match o with Pass -> "ok" | Fail _ -> "FAIL" | Skip _ -> "skip" in
           Printf.eprintf " %s\n%!" tag;
           (match o with
            | Pass -> Printf.printf "  PASS: %s\n" tc.tc_name
            | Fail msg -> Printf.printf "  FAIL: %s (%s) — %s\n" tc.tc_name tc.tc_file msg
            | Skip msg -> if verbose then Printf.printf "  skip: %s (%s) — %s\n" tc.tc_name tc.tc_file msg);
           o)
        tests
    in
    let pass, fail, skip =
      List.fold_left
        (fun (p, f, s) o ->
           match o with
           | Pass -> (p + 1, f, s)
           | Fail _ -> (p, f + 1, s)
           | Skip _ -> (p, f, s + 1))
        (0, 0, 0) outcomes
    in
    Printf.printf "\n========================================\n";
    Printf.printf "TOTAL: %d pass, %d fail, %d skip (out of %d)\n" pass fail skip total;
    Printf.printf "========================================\n";
    (* Exact final-line format consumed by generate-report.sh's generic
       "N pass, M fail (out of K)" score-line regex — matches the
       jsonld_runner / rdfc10_runner convention. *)
    Printf.printf "shacl-core: %d pass, %d fail, %d skip (out of %d)\n" pass fail skip total;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "SHACL Core W3C test-suite runner — slice 1 (issue #181).\n\
     \n\
     Usage:\n\
     \  ./shacl_runner                Run the default core manifest\n\
     \  ./shacl_runner <manifest.ttl> Run a specific manifest.ttl\n\
     \  ./shacl_runner --list         List discovered test entries (no execution)\n\
     \  ./shacl_runner -v|--verbose   Show skip reasons too (FAIL always shown)\n\
     \  ./shacl_runner --help         Show this help\n\
     \n\
     Slice 1 compares sh:conforms only (not full report isomorphism);\n\
     see formal/fstar/SHACL.Validation.fst section 11 for constraint\n\
     coverage and what is deferred to Phase 2.\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let list_only = ref false in
  let path = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: rest -> list_only := true; loop rest
    | p :: rest when !path = None -> path := Some p; loop rest
    | _ ->
      Printf.eprintf "shacl_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with Some p -> p | None -> default_manifest () in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
