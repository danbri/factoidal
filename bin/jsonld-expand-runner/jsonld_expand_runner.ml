(* JSON-LD 1.1 Expansion manifest runner — expand suite of the JSON-LD
   program (companion to bin/jsonld-runner's toRdf suite and
   bin/jsonld-fromrdf-runner's fromRdf suite).

   Reads third_party/testing/json-ld/tests/expand-manifest.jsonld, walks
   its `sequence`, and for each jld:ExpandTest:
     - loads the `input` .jsonld file;
     - calls the F*-extracted Parser_JSONLD.expand_document (the JSON-LD
       1.1 API Expansion Algorithm — same active-context setup as
       parse_jsonld, stopping BEFORE the RDF-dataset conversion so the
       comparison is expanded-JSON to expanded-JSON, not dataset to
       dataset);
     - for jld:PositiveEvaluationTest, parses the `expect` .jsonld file
       to a json_val and compares via Parser_JSONLD.jsonld_expanded_equal
       (JCS-canonical structural equality: object member order ignored,
       array order significant, numbers by canonical value — the whole
       comparison is F*-side, see that function's banner);
     - for jld:NegativeEvaluationTest (every one carries an
       `expectErrorCode`), PASSes iff expand_document returns None
       (this program's option-based error model matches "does expansion
       fail" but not the specific error CODE — same convention as the
       toRdf runner's NegativeEvaluationTest handling).

   !! THIS IS I/O GLUE — NO RDF/JSON-LD SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All JSON-LD expansion
   semantics live in formal/fstar/JSONLD.Expand.fst + JSONLD.Context.fst;
   the entry point and the comparison both live in
   formal/fstar/Parser.JSONLD.fst (expand_document / jsonld_expanded_
   equal). This file only does file I/O, manifest traversal, option
   threading, and boolean/string comparison of two already-F*-computed
   results.

   Per Iron Rule #7 the manifest itself — a JSON-LD document — is parsed
   with the F*-extracted RFC 8259 parser (Parser_JSON.parse_json), not
   any OCaml JSON library. The `expect` fixtures are likewise parsed with
   Parser_JSON.parse_json. There is no hand-rolled JSON parsing here.

   documentLoader (remote contexts / "@import" / expandContext): realised
   exactly as the toRdf runner does (issue #275) — map the manifest's
   baseIri prefix (https://w3c.github.io/json-ld-api/tests/) back to
   third_party/testing/json-ld/tests/ on disk and read the file. Rule #11
   ASSUME-IO glue; the F*-extracted JSONLD.Context module decides what to
   DO with the returned bytes.

   Usage:
     ./jsonld_expand_runner              Run the default expand manifest
     ./jsonld_expand_runner <manifest>   Run a specific manifest.jsonld
     ./jsonld_expand_runner --list       List parsed test entries
     ./jsonld_expand_runner -v|--verbose Show expected-vs-got diff on FAIL
     ./jsonld_expand_runner --help       Show this help
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
  [ Filename.concat repo_root "third_party/testing/json-ld/tests/expand-manifest.jsonld";
    "third_party/testing/json-ld/tests/expand-manifest.jsonld";
    "../../third_party/testing/json-ld/tests/expand-manifest.jsonld";
    "../../../third_party/testing/json-ld/tests/expand-manifest.jsonld" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/json-ld/tests/expand-manifest.jsonld"

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
   toRdf runner: map a w3c.github.io test-suite IRI to its on-disk
   fixture and read it; anything else is an honest None. *)

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
  | K_Positive -> "expand-Positive"
  | K_Negative -> "expand-Negative"
  | K_Unknown -> "expand-Unknown"

let opt_str_field key entry =
  match field "option" entry with
  | Some opt_obj -> str_field key opt_obj
  | None -> None

let jld_spec_version entry = opt_str_field "specVersion" entry
let jld_base_override entry = opt_str_field "base" entry
let jld_expand_context entry = opt_str_field "expandContext" entry
let jld_processing_mode entry = opt_str_field "processingMode" entry

(* ------------------------------------------------------------------ *)
(* Per-test record. *)

type test_case = {
  id : string;
  name : string;
  kind : test_kind;
  input : string;
  expect : string option;
  spec_version : string option;
  base_override : string option;
  expand_context : string option;
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
             expect = str_field "expect" e;
             spec_version = jld_spec_version e;
             base_override = jld_base_override e;
             expand_context = jld_expand_context e;
             processing_mode = jld_processing_mode e;
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

let expand_document_tc tc content =
  let fs_expand_context = match tc.expand_context with
    | Some rel -> FStar_Pervasives_Native.Some (jsonld_test_base ^ rel)
    | None -> FStar_Pervasives_Native.None in
  (* option.processingMode and option.specVersion both mean "run under
     this JSON-LD processing mode"; forward whichever is present
     (processingMode taking precedence) so expand_document's ac_mode10
     gating sees "json-ld-1.0" for either spelling — same convention as
     the toRdf runner. *)
  let fs_processing_mode = match tc.processing_mode, tc.spec_version with
    | Some s, _ -> FStar_Pervasives_Native.Some s
    | None, Some sv -> FStar_Pervasives_Native.Some sv
    | None, None -> FStar_Pervasives_Native.None in
  opt_of_fs
    (Parser_JSONLD.expand_document content
       (FStar_Pervasives_Native.Some (test_base tc))
       fs_expand_context fs_processing_mode)

(* The specVersion=json-ld-1.0 tests that need GENUINE 1.0-mode
   semantics this 1.1-plus-ac_mode10 engine does not implement — measured
   (not blanket-skipped): each was RUN and produced the wrong result
   because the fixture exercises a 1.0-only behaviour. Kept as an explicit
   ID allowlist (not a blanket specVersion check) so it must be edited,
   not silently widened, per anti-pattern #3. The OTHER 3 specVersion=1.0
   IDs (#t0026, #ter02, #ter03) are NOT here: they were measured to PASS
   under normal comparison and run like any other test. See this file's
   companion in bin/jsonld-runner/jsonld_runner.ml (jld_1_0_still_skip)
   for the toRdf equivalent of this same split.

   2026-07-16 skip audit: five entries flipped to ordinary runs by
   implementing their 1.0-mode semantics in F* behind ac_mode10 —
   #t0038 (JSONLD.Context.fst's expand_iri_gen: 1.0 has no prefix
   flag, every term is a compact-IRI prefix candidate), #t0115 +
   #t0116 (JSONLD.Context.fst's @vocab branch: 1.0 requires an
   absolute-IRI-or-bnode vocab mapping), and #ter24 + #ter32
   (JSONLD.Expand.fst's expand_property: 1.0's "list of lists"
   error).

   2026-07-17 direction wave: #t0071 ("Redefine terms looking like
   compact IRIs") FLIPPED to an ordinary run. Its 1.0-mode redefinition
   of a compact-IRI-shaped term to itself is NOT a 1.0-only semantic at
   all — the same defined[term]=false guard the JSON-LD 1.1 API's Create
   Term Definition already specifies (a term's own @id/@reverse value
   must not resolve through the term's own stale mapping) covers it. The
   object-form @id branch was missing the self-strip the simple string
   form already had; JSONLD.Context.fst's process_term_def_obj now
   applies it, so {"v:termId": {"@id": "v:termId"}} re-resolves via the
   compact-IRI prefix. Measured MATCH afterwards. The allowlist is now
   empty — no expand test needs a documented 1.0-only skip. *)
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
                (match opt_of_fs (Parser_JSON.parse_json expect_content) with
                 | None -> Fail "expected .jsonld is not valid JSON"
                 | Some expected_json ->
                   (match expand_document_tc tc content with
                    | None -> Fail "expand_document returned None (expected a valid expanded document)"
                    | Some got_json ->
                      if Parser_JSONLD.jsonld_expanded_equal got_json expected_json then Pass
                      else
                        Fail (Printf.sprintf
                                "expanded JSON differs\n      expected:\n%s\n      got:\n%s"
                                (head (Parser_JSONLD.jcanon_document expected_json) 4000)
                                (head (Parser_JSONLD.jcanon_document got_json) 4000))))))
        | K_Negative ->
          (match expand_document_tc tc content with
           | None -> Pass
           | Some _ -> Fail "expand_document succeeded but a failure was expected (see manifest expectErrorCode)")
        | K_Unknown -> Skip "unrecognized @type for an expand test entry"))

(* ------------------------------------------------------------------ *)
(* Manifest load + suite run. *)

let load_manifest manifest_path =
  match read_file manifest_path with
  | None ->
    Printf.eprintf "jsonld_expand_runner: cannot read manifest: %s\n" manifest_path;
    exit 2
  | Some raw ->
    match opt_of_fs (Parser_JSON.parse_json raw) with
    | None ->
      Printf.eprintf "jsonld_expand_runner: manifest is not valid JSON: %s\n" manifest_path;
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
  Printf.printf "=== JSON-LD 1.1 Expansion Test Runner ===\n";
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
            | Fail msg -> Printf.printf "  FAIL: %s — %s\n" tc.name msg
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
    Printf.printf "jsonld-expand: %d pass, %d fail, %d skip (out of %d)\n"
      pass fail skip total;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "JSON-LD 1.1 Expansion manifest runner — expand suite.\n\
     \n\
     Usage:\n\
     \  ./jsonld_expand_runner              Run the default expand manifest\n\
     \  ./jsonld_expand_runner <manifest>   Run a specific manifest.jsonld\n\
     \  ./jsonld_expand_runner --list       List parsed test entries\n\
     \  ./jsonld_expand_runner -v|--verbose Show skip reasons too (FAIL always shown)\n\
     \  ./jsonld_expand_runner --help       Show this help\n"

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
      Printf.eprintf "jsonld_expand_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with
    | Some p -> p
    | None -> default_manifest ()
  in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
