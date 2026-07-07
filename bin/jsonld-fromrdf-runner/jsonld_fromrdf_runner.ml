(* JSON-LD 1.1 fromRdf manifest runner — "Serialize RDF as JSON-LD".

   Reads third_party/testing/json-ld/tests/fromRdf-manifest.jsonld, walks
   its `sequence`, and for each test:
     - loads the `input` .nq file and parses it with the F*-extracted
       Parser_NQuads.parse_nquads into an rdf_dataset;
     - calls the F*-extracted JSONLD_FromRdf.from_rdf on that dataset with
       the manifest's options (useNativeTypes / useRdfType), obtaining an
       expanded-form JSON-LD document as a Parser_JSON.json_val (or None on
       an "invalid JSON literal" error);
     - for PositiveEvaluationTest, parses the `expect` -out.jsonld file with
       the F*-extracted Parser_JSON.parse_json, then compares the two trees
       by JCS canonical serialization (Parser_JSONLD.jcanon_document) — this
       makes the comparison independent of object-key order and JSON number
       spelling;
     - for NegativeEvaluationTest, PASSes iff from_rdf returns None.

   !! THIS IS I/O GLUE — NO JSON-LD SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #7 / #11 / anti-pattern #15. All fromRdf
   serialization semantics live in formal/fstar/JSONLD.FromRdf.fst; all N-Quads
   parsing in formal/fstar/Parser.NQuads.fst; all JCS canonicalization in
   formal/fstar/Parser.JSONLD.fst. This file only does file I/O, manifest
   traversal (via the F*-extracted RFC 8259 parser Parser_JSON.parse_json),
   option extraction, and string comparison of two already-canonicalized JSON
   strings.

   Usage:
     ./jsonld_fromrdf_runner              Run the default fromRdf manifest
     ./jsonld_fromrdf_runner <manifest>   Run a specific manifest.jsonld
     ./jsonld_fromrdf_runner -v|--verbose Show expected-vs-got diff on FAIL
     ./jsonld_fromrdf_runner --help       Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to jsonld_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/json-ld/tests/fromRdf-manifest.jsonld";
    "third_party/testing/json-ld/tests/fromRdf-manifest.jsonld";
    "../../third_party/testing/json-ld/tests/fromRdf-manifest.jsonld";
    "../../../third_party/testing/json-ld/tests/fromRdf-manifest.jsonld" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/json-ld/tests/fromRdf-manifest.jsonld"

(* ------------------------------------------------------------------ *)
(* File I/O. *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let head s n =
  if String.length s <= n then s else String.sub s 0 n ^ " …(truncated)"

(* ------------------------------------------------------------------ *)
(* Thin wrappers over the F*-extracted JSON accessors. *)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)

let bool_field key obj =
  match field key obj with
  | Some (Parser_JSON.JBool b) -> Some b
  | _ -> None

let jld_types entry =
  match field "@type" entry with
  | Some (Parser_JSON.JArray items) ->
    List.filter_map
      (function Parser_JSON.JString s -> Some s | _ -> None)
      items
  | Some (Parser_JSON.JString s) -> [ s ]
  | _ -> []

type test_kind = K_Positive | K_Negative | K_Unknown

let classify types =
  if List.mem "jld:PositiveEvaluationTest" types then K_Positive
  else if List.mem "jld:NegativeEvaluationTest" types then K_Negative
  else K_Unknown

let kind_label = function
  | K_Positive -> "fromRdf-Positive"
  | K_Negative -> "fromRdf-Negative"
  | K_Unknown -> "fromRdf-Unknown"

(* Manifest option extraction (config plumbing, not semantics). *)
let opt_bool entry key =
  match field "option" entry with
  | Some opt_obj -> (match bool_field key opt_obj with Some b -> b | None -> false)
  | None -> false

(* ------------------------------------------------------------------ *)
(* Per-test record. *)

type test_case = {
  id : string;
  name : string;
  kind : test_kind;
  input : string;
  expect : string option;
  use_native_types : bool;
  use_rdf_type : bool;
  manifest_dir : string;
}

let build_test_cases manifest_dir root =
  match arr_field "sequence" root with
  | None -> []
  | Some entries ->
    List.filter_map
      (fun e ->
         match str_field "@id" e, str_field "input" e with
         | Some id, Some input ->
           let name = match str_field "name" e with Some n -> n | None -> id in
           Some {
             id; name;
             kind = classify (jld_types e);
             input;
             expect = str_field "expect" e;
             use_native_types = opt_bool e "useNativeTypes";
             use_rdf_type = opt_bool e "useRdfType";
             manifest_dir;
           }
         | _ -> None)
      entries

(* ------------------------------------------------------------------ *)
(* Outcome + per-test execution. *)

type outcome = Pass | Fail of string | Skip of string

let run_from_rdf tc content =
  let ds = Parser_NQuads.parse_nquads content in
  let opts =
    { JSONLD_FromRdf.use_native_types = tc.use_native_types;
      JSONLD_FromRdf.use_rdf_type = tc.use_rdf_type } in
  opt_of_fs (JSONLD_FromRdf.from_rdf ds opts)

let run_test tc =
  let input_path = Filename.concat tc.manifest_dir tc.input in
  match read_file input_path with
  | None -> Fail (Printf.sprintf "input file not found: %s" input_path)
  | Some content ->
    (match tc.kind with
     | K_Positive ->
       (match tc.expect with
        | None -> Fail "manifest entry has no `expect` file"
        | Some expect_rel ->
          let expect_path = Filename.concat tc.manifest_dir expect_rel in
          (match read_file expect_path with
           | None -> Fail (Printf.sprintf "expected .jsonld file not found: %s" expect_path)
           | Some expect_content ->
             (match run_from_rdf tc content with
              | None -> Fail "from_rdf returned None (expected a valid expanded-form document)"
              | Some got ->
                (match opt_of_fs (Parser_JSON.parse_json expect_content) with
                 | None -> Fail "expected .jsonld file is not valid JSON"
                 | Some expected ->
                   let got_canon = Parser_JSONLD.jcanon_document got in
                   let exp_canon = Parser_JSONLD.jcanon_document expected in
                   if got_canon = exp_canon then Pass
                   else
                     Fail (Printf.sprintf
                             "canonical JSON differs\n      expected:\n%s\n      got:\n%s"
                             (head exp_canon 600) (head got_canon 600))))))
     | K_Negative ->
       (match run_from_rdf tc content with
        | None -> Pass
        | Some _ -> Fail "from_rdf succeeded but an error was expected (invalid JSON literal)")
     | K_Unknown -> Skip "unrecognized @type for a fromRdf test entry")

(* ------------------------------------------------------------------ *)
(* Manifest load + suite run. *)

let load_manifest manifest_path =
  match read_file manifest_path with
  | None ->
    Printf.eprintf "jsonld_fromrdf_runner: cannot read manifest: %s\n" manifest_path;
    exit 2
  | Some raw ->
    match opt_of_fs (Parser_JSON.parse_json raw) with
    | None ->
      Printf.eprintf "jsonld_fromrdf_runner: manifest is not valid JSON: %s\n" manifest_path;
      exit 2
    | Some root ->
      let manifest_dir = Filename.dirname manifest_path in
      build_test_cases manifest_dir root

let () =
  let args = Array.to_list Sys.argv in
  let verbose = List.exists (fun a -> a = "-v" || a = "--verbose") args in
  if List.exists (fun a -> a = "--help") args then begin
    print_string
      "jsonld_fromrdf_runner — JSON-LD 1.1 fromRdf (Serialize RDF as JSON-LD)\n\
      \  ./jsonld_fromrdf_runner              Run the default fromRdf manifest\n\
      \  ./jsonld_fromrdf_runner <manifest>   Run a specific manifest.jsonld\n\
      \  ./jsonld_fromrdf_runner -v|--verbose Show expected-vs-got diff on FAIL\n\
      \  ./jsonld_fromrdf_runner --help       Show this help\n";
    exit 0
  end;
  let manifest_path =
    match List.filter (fun a -> String.length a > 0 && a.[0] <> '-') (List.tl args) with
    | m :: _ -> m
    | [] -> default_manifest ()
  in
  let tests = load_manifest manifest_path in
  let results = List.map (fun tc -> (tc, run_test tc)) tests in
  let pass = List.length (List.filter (fun (_, o) -> o = Pass) results) in
  let fail =
    List.length (List.filter (fun (_, o) -> match o with Fail _ -> true | _ -> false) results) in
  let skip =
    List.length (List.filter (fun (_, o) -> match o with Skip _ -> true | _ -> false) results) in
  let total = List.length results in
  List.iter
    (fun (tc, o) ->
       match o with
       | Pass -> Printf.printf "  PASS  %-8s %s [%s]\n" tc.id tc.name (kind_label tc.kind)
       | Skip r -> Printf.printf "  SKIP  %-8s %s — %s\n" tc.id tc.name r
       | Fail r ->
         Printf.printf "  FAIL  %-8s %s [%s]\n" tc.id tc.name (kind_label tc.kind);
         if verbose then Printf.printf "        %s\n" r)
    results;
  Printf.printf "\n^JSON-LD fromRdf tests: %d pass, %d fail" pass fail;
  if skip > 0 then Printf.printf ", %d skip" skip;
  Printf.printf " (out of %d)\n" total
