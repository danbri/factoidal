(* JSON-LD 1.1 Flattening manifest runner — flatten suite of the JSON-LD
   program (companion to bin/jsonld-compact-runner's compact suite and
   bin/jsonld-expand-runner's expand suite).

   Reads third_party/testing/json-ld/tests/flatten-manifest.jsonld, walks
   its `sequence`, and for each jld:FlattenTest:
     - loads the `input` .jsonld file AND (when the manifest entry has
       one — most flatten tests do not) the `context` .jsonld file;
     - calls the F*-extracted JSONLD_Flatten.flatten_document (the
       JSON-LD 1.1 API flatten() operation: expand the input via
       Parser_JSONLD.expand_document, run Node Map Generation + the
       Flattening Algorithm, and — when a context is supplied — compact
       the flattened array via the JSONLD.Compact machinery, keeping a
       top-level @graph);
     - for jld:PositiveEvaluationTest, parses the `expect` .jsonld file
       to a json_val and compares via Parser_JSONLD.jsonld_expanded_equal
       (JCS-canonical structural equality: object member order ignored,
       array order significant, numbers by canonical value — the whole
       comparison is F*-side);
     - for jld:NegativeEvaluationTest (the suite's one carries
       expectErrorCode "conflicting indexes"), PASSes iff
       flatten_document returns None (this program's option-based error
       model matches "does flattening fail" but not the specific error
       CODE — same convention as the toRdf/expand/compact runners'
       NegativeEvaluationTest handling).

   !! THIS IS I/O GLUE — NO RDF/JSON-LD SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All JSON-LD flattening
   semantics live in formal/fstar/JSONLD.Flatten.fst (plus JSONLD.Compact
   / JSONLD.Context / JSONLD.Expand / Parser.JSONLD underneath it). This
   file only does file I/O, manifest traversal, option threading, and
   boolean/string comparison of two already-F*-computed results.

   Per Iron Rule #7 the manifest itself — a JSON-LD document — is parsed
   with the F*-extracted RFC 8259 parser (Parser_JSON.parse_json), not
   any OCaml JSON library. The `expect` fixtures are likewise parsed with
   Parser_JSON.parse_json. There is no hand-rolled JSON parsing here.

   documentLoader (remote contexts / "@import"): realised exactly as the
   toRdf/expand/compact runners do (issue #275) — map the manifest's
   baseIri prefix (https://w3c.github.io/json-ld-api/tests/) back to
   third_party/testing/json-ld/tests/ on disk and read the file. Rule #11
   ASSUME-IO glue; the F*-extracted JSONLD.Context module decides what to
   DO with the returned bytes.

   Usage:
     ./jsonld_flatten_runner              Run the default flatten manifest
     ./jsonld_flatten_runner <manifest>   Run a specific manifest.jsonld
     ./jsonld_flatten_runner --list       List parsed test entries
     ./jsonld_flatten_runner -v|--verbose Show skip reasons too (FAIL always shown)
     ./jsonld_flatten_runner --help       Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to jsonld_compact_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/json-ld/tests/flatten-manifest.jsonld";
    "third_party/testing/json-ld/tests/flatten-manifest.jsonld";
    "../../third_party/testing/json-ld/tests/flatten-manifest.jsonld";
    "../../../third_party/testing/json-ld/tests/flatten-manifest.jsonld" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/json-ld/tests/flatten-manifest.jsonld"

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
(* documentLoader realisation (issue #275) — identical policy to the
   toRdf/expand/compact runners: map a w3c.github.io test-suite IRI to
   its on-disk fixture and read it; anything else is an honest None. *)

let jsonld_test_base = "https://w3c.github.io/json-ld-api/tests/"

let jsonld_fixture_root () =
  Filename.concat (find_repo_root ()) "third_party/testing/json-ld/tests"

let jsonld_document_loader (iri : string) : string option =
  let prefix = jsonld_test_base in
  let plen = String.length prefix and ilen = String.length iri in
  if ilen >= plen && String.sub iri 0 plen = prefix then
    read_file (Filename.concat (jsonld_fixture_root ()) (String.sub iri plen (ilen - plen)))
  else
    None

let () =
  JSONLD_Loader.jsonld_loader_register
    (fun iri ->
       match jsonld_document_loader iri with
       | Some s -> FStar_Pervasives_Native.Some s
       | None -> FStar_Pervasives_Native.None)

(* ------------------------------------------------------------------ *)
(* Thin wrappers over the F*-extracted JSON accessors. *)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)

let jld_types entry =
  match field "@type" entry with
  | Some (Parser_JSON.JArray items) ->
    List.filter_map
      (function Parser_JSON.JString s -> Some s | _ -> None)
      items
  | Some (Parser_JSON.JString s) -> [ s ]
  | _ -> []

type test_kind =
  | K_Positive
  | K_Negative
  | K_Unknown

let classify types =
  if List.mem "jld:PositiveEvaluationTest" types then K_Positive
  else if List.mem "jld:NegativeEvaluationTest" types then K_Negative
  else K_Unknown

let kind_label = function
  | K_Positive -> "flatten-Positive"
  | K_Negative -> "flatten-Negative"
  | K_Unknown -> "flatten-Unknown"

let opt_str_field key entry =
  match field "option" entry with
  | Some opt_obj -> str_field key opt_obj
  | None -> None

let opt_bool_field key entry =
  match field "option" entry with
  | Some opt_obj ->
    (match field key opt_obj with
     | Some (Parser_JSON.JBool b) -> Some b
     | _ -> None)
  | None -> None

(* ------------------------------------------------------------------ *)
(* Per-test record. *)

type test_case = {
  id : string;
  name : string;
  kind : test_kind;
  input : string;
  context : string option;      (* OPTIONAL for flatten (unlike compact) *)
  expect : string option;
  spec_version : string option;
  base_override : string option;
  compact_arrays : bool;         (* option.compactArrays, default true *)
  processing_mode : string option;
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
             context = str_field "context" e;
             expect = str_field "expect" e;
             spec_version = opt_str_field "specVersion" e;
             base_override = opt_str_field "base" e;
             compact_arrays =
               (match opt_bool_field "compactArrays" e with
                | Some b -> b | None -> true);
             processing_mode = opt_str_field "processingMode" e;
             manifest_dir;
           }
         | _ -> None)
      entries

(* ------------------------------------------------------------------ *)
(* Outcome + per-test execution. *)

type outcome = Pass | Fail of string | Skip of string

let test_base tc =
  match tc.base_override with
  | Some b -> b
  | None -> jsonld_test_base ^ tc.input

let flatten_document_tc tc input_content context_content =
  (* option.processingMode and option.specVersion both mean "run under
     this JSON-LD processing mode"; forward whichever is present
     (processingMode taking precedence) — same convention as the toRdf,
     expand and compact runners. *)
  let fs_processing_mode = match tc.processing_mode, tc.spec_version with
    | Some s, _ -> FStar_Pervasives_Native.Some s
    | None, Some sv -> FStar_Pervasives_Native.Some sv
    | None, None -> FStar_Pervasives_Native.None in
  let fs_ctx_doc = match context_content with
    | Some s -> FStar_Pervasives_Native.Some s
    | None -> FStar_Pervasives_Native.None in
  let fs_ctx_url = match tc.context with
    | Some rel -> FStar_Pervasives_Native.Some (jsonld_test_base ^ rel)
    | None -> FStar_Pervasives_Native.None in
  opt_of_fs
    (JSONLD_Flatten.flatten_document input_content
       fs_ctx_doc
       (FStar_Pervasives_Native.Some (test_base tc))
       fs_ctx_url
       tc.compact_arrays
       fs_processing_mode)

(* Measured per-ID skips (JSON-LD-1.0-only fixtures). Populated only
   after each candidate was RUN and its failure diagnosed as a genuine
   1.0-vs-1.1 semantic gap — never a blanket specVersion check (mirrors
   jsonld_compact_runner.ml's jld_1_0_still_skip policy). JLD_NO_SKIP=1
   re-runs them.

   2026-07-16 skip audit: the list is now EMPTY — both former entries
   (#t0014 "@set of @value objects with keyword aliases", #t0038
   "Flattening blank node labels") flipped to ordinary runs after
   JSONLD.Context.fst's expand_iri_gen learned JSON-LD 1.0's
   prefix rule behind ac_mode10 (1.0 has no prefix flag: EVERY defined
   term — expanded-definition and bnode-valued ones included — is a
   compact-IRI prefix candidate). The mechanism stays so the next
   genuine 1.0-only gap has a place to be recorded (and JLD_NO_SKIP
   keeps working). *)
let jld_1_0_still_skip (id : string) : string option =
  if Sys.getenv_opt "JLD_NO_SKIP" <> None then None else
  match id with
  | _ -> None

let run_test tc =
  match jld_1_0_still_skip tc.id with
  | Some reason -> Skip reason
  | None ->
    let input_path = Filename.concat tc.manifest_dir tc.input in
    (match read_file input_path with
     | None -> Fail (Printf.sprintf "input file not found: %s" input_path)
     | Some input_content ->
       let context_content_res =
         (match tc.context with
          | None -> Ok None
          | Some context_rel ->
            let context_path = Filename.concat tc.manifest_dir context_rel in
            (match read_file context_path with
             | None -> Error (Printf.sprintf "context file not found: %s" context_path)
             | Some c -> Ok (Some c))) in
       (match context_content_res with
        | Error msg -> Fail msg
        | Ok context_content ->
          (match tc.kind with
           | K_Positive ->
             (match tc.expect with
              | None -> Fail "manifest entry has no `expect` file"
              | Some expect_rel ->
                let expect_path = Filename.concat tc.manifest_dir expect_rel in
                (match read_file expect_path with
                 | None -> Fail (Printf.sprintf "expected .jsonld file not found: %s" expect_path)
                 | Some expect_content ->
                   (match opt_of_fs (Parser_JSON.parse_json expect_content) with
                    | None -> Fail "expected .jsonld is not valid JSON"
                    | Some expected_json ->
                      (match flatten_document_tc tc input_content context_content with
                       | None -> Fail "flatten_document returned None (expected a valid flattened document)"
                       | Some got_json ->
                         if Parser_JSONLD.jsonld_expanded_equal got_json expected_json then Pass
                         else
                           Fail (Printf.sprintf
                                   "flattened JSON differs\n      expected:\n%s\n      got:\n%s"
                                   (head (Parser_JSONLD.jcanon_document expected_json) 4000)
                                   (head (Parser_JSONLD.jcanon_document got_json) 4000)))))
             )
           | K_Negative ->
             (match flatten_document_tc tc input_content context_content with
              | None -> Pass
              | Some _ -> Fail "flatten_document succeeded but a failure was expected (see manifest expectErrorCode)")
           | K_Unknown -> Skip "unrecognized @type for a flatten test entry")))

(* ------------------------------------------------------------------ *)
(* Manifest load + suite run. *)

let load_manifest manifest_path =
  match read_file manifest_path with
  | None ->
    Printf.eprintf "jsonld_flatten_runner: cannot read manifest: %s\n" manifest_path;
    exit 2
  | Some raw ->
    match opt_of_fs (Parser_JSON.parse_json raw) with
    | None ->
      Printf.eprintf "jsonld_flatten_runner: manifest is not valid JSON: %s\n" manifest_path;
      exit 2
    | Some root ->
      let manifest_dir = Filename.dirname manifest_path in
      build_test_cases manifest_dir root

let tally_by_kind tests_and_outcomes kind =
  List.fold_left
    (fun (p, f, s) (tc, o) ->
       if tc.kind <> kind then (p, f, s)
       else match o with
         | Pass -> (p + 1, f, s)
         | Fail _ -> (p, f + 1, s)
         | Skip _ -> (p, f, s + 1))
    (0, 0, 0) tests_and_outcomes

let run_manifest ~verbose ~list_only manifest_path =
  Printf.printf "=== JSON-LD 1.1 Flattening Test Runner ===\n";
  Printf.printf "Manifest: %s\n\n" manifest_path;
  let tests = load_manifest manifest_path in
  let total = List.length tests in
  Printf.printf "Totals: %d test entries\n\n" total;
  if list_only then
    List.iter
      (fun tc ->
         Printf.printf "  [%s] %-8s %s\n" (kind_label tc.kind) tc.id tc.name)
      tests
  else begin
    let n = ref 0 in
    let outcomes =
      List.map
        (fun tc ->
           incr n;
           Printf.eprintf "  [%d/%d] %s%!" !n total tc.id;
           let t0 = Unix.gettimeofday () in
           let o = run_test tc in
           let elapsed = Unix.gettimeofday () -. t0 in
           let status_tag = match o with
             | Pass -> "ok" | Fail _ -> "FAIL" | Skip _ -> "skip" in
           Printf.eprintf " %s%s\n%!" status_tag
             (if elapsed >= 1.0 then Printf.sprintf " (%.1fs)" elapsed else "");
           (match o with
            | Pass -> Printf.printf "  PASS: %s\n" tc.name
            | Fail msg -> Printf.printf "  FAIL: %s (%s) — %s\n" tc.name tc.id msg
            | Skip msg -> if verbose then Printf.printf "  skip: %s — %s\n" tc.name msg);
           (tc, o))
        tests
    in
    Printf.printf "\n========================================\n";
    Printf.printf "Suite Results:\n";
    List.iter
      (fun kind ->
         let (p, f, s) = tally_by_kind outcomes kind in
         if p + f + s > 0 then
           Printf.printf "  %-20s pass:%d fail:%d skip:%d\n" (kind_label kind) p f s)
      [ K_Positive; K_Negative; K_Unknown ];
    Printf.printf "========================================\n";
    let pass, fail, skip =
      List.fold_left
        (fun (p, f, s) (_, o) ->
           match o with
           | Pass -> (p + 1, f, s)
           | Fail _ -> (p, f + 1, s)
           | Skip _ -> (p, f, s + 1))
        (0, 0, 0) outcomes
    in
    Printf.printf "TOTAL: %d pass, %d fail, %d skip (out of %d)\n" pass fail skip total;
    Printf.printf "========================================\n";
    (* Exact final-line format consumed by generate-report.sh's generic
       "N pass, M fail (out of K)" score-line regex. *)
    Printf.printf "jsonld-flatten: %d pass, %d fail, %d skip (out of %d)\n"
      pass fail skip total;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "JSON-LD 1.1 Flattening manifest runner — flatten suite.\n\
     \n\
     Usage:\n\
     \  ./jsonld_flatten_runner              Run the default flatten manifest\n\
     \  ./jsonld_flatten_runner <manifest>   Run a specific manifest.jsonld\n\
     \  ./jsonld_flatten_runner --list       List parsed test entries\n\
     \  ./jsonld_flatten_runner -v|--verbose Show skip reasons too (FAIL always shown)\n\
     \  ./jsonld_flatten_runner --help       Show this help\n"

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
      Printf.eprintf "jsonld_flatten_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with
    | Some p -> p
    | None -> default_manifest ()
  in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
