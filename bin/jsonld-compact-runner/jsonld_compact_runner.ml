(* JSON-LD 1.1 Compaction manifest runner — compact suite of the JSON-LD
   program (companion to bin/jsonld-expand-runner's expand suite and
   bin/jsonld-runner's toRdf suite).

   Reads third_party/testing/json-ld/tests/compact-manifest.jsonld, walks
   its `sequence`, and for each jld:CompactTest:
     - loads the `input` .jsonld file AND the `context` .jsonld file;
     - calls the F*-extracted JSONLD_Compact.compact_document (the
       JSON-LD 1.1 API compact() operation: expand the input via
       Parser_JSONLD.expand_document, process the supplied context via
       JSONLD_Context.context_process, run the Compaction Algorithm,
       re-attach the original context value);
     - for jld:PositiveEvaluationTest, parses the `expect` .jsonld file
       to a json_val and compares via Parser_JSONLD.jsonld_expanded_equal
       (JCS-canonical structural equality: object member order ignored,
       array order significant, numbers by canonical value — the whole
       comparison is F*-side);
     - for jld:NegativeEvaluationTest (every one carries an
       `expectErrorCode`), PASSes iff compact_document returns None
       (this program's option-based error model matches "does compaction
       fail" but not the specific error CODE — same convention as the
       toRdf and expand runners' NegativeEvaluationTest handling).

   !! THIS IS I/O GLUE — NO RDF/JSON-LD SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All JSON-LD compaction
   semantics live in formal/fstar/JSONLD.Compact.fst (plus JSONLD.Context
   / JSONLD.Expand / Parser.JSONLD underneath it). This file only does
   file I/O, manifest traversal, option threading, and boolean/string
   comparison of two already-F*-computed results.

   Per Iron Rule #7 the manifest itself — a JSON-LD document — is parsed
   with the F*-extracted RFC 8259 parser (Parser_JSON.parse_json), not
   any OCaml JSON library. The `expect` fixtures are likewise parsed with
   Parser_JSON.parse_json. There is no hand-rolled JSON parsing here.

   documentLoader (remote contexts / "@import"): realised exactly as the
   toRdf and expand runners do (issue #275) — map the manifest's baseIri
   prefix (https://w3c.github.io/json-ld-api/tests/) back to
   third_party/testing/json-ld/tests/ on disk and read the file. Rule #11
   ASSUME-IO glue; the F*-extracted JSONLD.Context module decides what to
   DO with the returned bytes.

   Usage:
     ./jsonld_compact_runner              Run the default compact manifest
     ./jsonld_compact_runner <manifest>   Run a specific manifest.jsonld
     ./jsonld_compact_runner --list       List parsed test entries
     ./jsonld_compact_runner -v|--verbose Show skip reasons too (FAIL always shown)
     ./jsonld_compact_runner --help       Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to jsonld_expand_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/json-ld/tests/compact-manifest.jsonld";
    "third_party/testing/json-ld/tests/compact-manifest.jsonld";
    "../../third_party/testing/json-ld/tests/compact-manifest.jsonld";
    "../../../third_party/testing/json-ld/tests/compact-manifest.jsonld" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/json-ld/tests/compact-manifest.jsonld"

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
   toRdf/expand runners: map a w3c.github.io test-suite IRI to its
   on-disk fixture and read it; anything else is an honest None. *)

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

(* ------------------------------------------------------------------ *)
(* Local-override layer — tests/local-overrides/. When we carefully
   disagree with a vendored upstream fixture (a written analysis + an
   upstream provenance link, per that directory's README.md and the
   owner directive of 2026-07-17: "if we carefully disagree with test
   make our own local override of it. Shex Also."), the disputed test
   is reclassified from FAIL to a distinctly-counted local-override —
   NEVER folded into plain pass (the honesty invariant, anti-pattern
   #25). This reads every *.json override file, keeps the entries whose
   `suite` matches "jsonld-compact", and returns the overridden test
   ids. #t0038 lives here: its json-ld-1.0 expected output contradicts
   this suite's OWN 1.1 pin #tp001 (see the override file's rationale
   and JSONLD.Compact.fst's cmp_curie_loop comment). Was formerly a
   per-ID skip; now it RUNS and its output-mismatch failure is
   reclassified. *)
let load_local_overrides (repo_root : string) (suite : string) : string list =
  let dir = Filename.concat repo_root "tests/local-overrides" in
  if not (Sys.file_exists dir) then []
  else
    let entries = try Array.to_list (Sys.readdir dir) with _ -> [] in
    List.filter_map
      (fun fn ->
         if Filename.check_suffix fn ".json" then
           match read_file (Filename.concat dir fn) with
           | None -> None
           | Some txt ->
             (match opt_of_fs (Parser_JSON.parse_json txt) with
              | Some obj ->
                (match str_field "suite" obj, str_field "test_id" obj with
                 | Some s, Some tid when s = suite -> Some tid
                 | _ -> None)
              | None -> None)
         else None)
      entries

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
  | K_Positive -> "compact-Positive"
  | K_Negative -> "compact-Negative"
  | K_Unknown -> "compact-Unknown"

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
  context : string option;
  expect : string option;
  spec_version : string option;
  base_override : string option;
  compact_arrays : bool;         (* option.compactArrays, default true *)
  compact_to_relative : bool;    (* option.compactToRelative, default true *)
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
             compact_to_relative =
               (match opt_bool_field "compactToRelative" e with
                | Some b -> b | None -> true);
             processing_mode = opt_str_field "processingMode" e;
             manifest_dir;
           }
         | _ -> None)
      entries

(* ------------------------------------------------------------------ *)
(* Outcome + per-test execution. *)

type outcome = Pass | Override of string | Fail of string | Skip of string

let test_base tc =
  match tc.base_override with
  | Some b -> b
  | None -> jsonld_test_base ^ tc.input

let compact_document_tc tc input_content context_content =
  (* option.processingMode and option.specVersion both mean "run under
     this JSON-LD processing mode"; forward whichever is present
     (processingMode taking precedence) — same convention as the toRdf
     and expand runners. *)
  let fs_processing_mode = match tc.processing_mode, tc.spec_version with
    | Some s, _ -> FStar_Pervasives_Native.Some s
    | None, Some sv -> FStar_Pervasives_Native.Some sv
    | None, None -> FStar_Pervasives_Native.None in
  let fs_ctx_url = match tc.context with
    | Some rel -> FStar_Pervasives_Native.Some (jsonld_test_base ^ rel)
    | None -> FStar_Pervasives_Native.None in
  opt_of_fs
    (JSONLD_Compact.compact_document input_content context_content
       (FStar_Pervasives_Native.Some (test_base tc))
       fs_ctx_url
       tc.compact_arrays
       tc.compact_to_relative
       fs_processing_mode)

(* #t0038 ("Index map round-tripping") was formerly a measured per-ID
   skip here: its option.specVersion=json-ld-1.0 expected output needs
   every term (expanded-form definitions included) to be a compact-IRI
   prefix candidate, which directly contradicts this suite's OWN 1.1 pin
   #tp001 ("Compact IRI will not use an expanded term definition in
   1.0"). One processingMode-driven engine state cannot satisfy both;
   this program implements the 1.1 API, so tp001 wins and t0038's
   body:/format-style prefix compaction diverges by design (see
   JSONLD.Compact.fst's cmp_curie_loop comment).

   As of the owner directive of 2026-07-17 ("if we carefully disagree
   with test make our own local override of it") that skip is retired in
   favour of the tests/local-overrides/ layer: #t0038 now RUNS, produces
   its output-mismatch failure, and is reclassified to a distinctly-
   counted local-override in run_manifest below (never folded into plain
   pass). No JSON-LD-1.0 skip remains in this runner. *)

let run_test tc =
    let input_path = Filename.concat tc.manifest_dir tc.input in
    (match read_file input_path with
     | None -> Fail (Printf.sprintf "input file not found: %s" input_path)
     | Some input_content ->
       (match tc.context with
        | None -> Fail "manifest entry has no `context` file"
        | Some context_rel ->
          let context_path = Filename.concat tc.manifest_dir context_rel in
          (match read_file context_path with
           | None -> Fail (Printf.sprintf "context file not found: %s" context_path)
           | Some context_content ->
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
                         (match compact_document_tc tc input_content context_content with
                          | None -> Fail "compact_document returned None (expected a valid compacted document)"
                          | Some got_json ->
                            if Parser_JSONLD.jsonld_expanded_equal got_json expected_json then Pass
                            else
                              Fail (Printf.sprintf
                                      "compacted JSON differs\n      expected:\n%s\n      got:\n%s"
                                      (head (Parser_JSONLD.jcanon_document expected_json) 4000)
                                      (head (Parser_JSONLD.jcanon_document got_json) 4000))))))
              | K_Negative ->
                (match compact_document_tc tc input_content context_content with
                 | None -> Pass
                 | Some _ -> Fail "compact_document succeeded but a failure was expected (see manifest expectErrorCode)")
              | K_Unknown -> Skip "unrecognized @type for a compact test entry"))))

(* ------------------------------------------------------------------ *)
(* Manifest load + suite run. *)

let load_manifest manifest_path =
  match read_file manifest_path with
  | None ->
    Printf.eprintf "jsonld_compact_runner: cannot read manifest: %s\n" manifest_path;
    exit 2
  | Some raw ->
    match opt_of_fs (Parser_JSON.parse_json raw) with
    | None ->
      Printf.eprintf "jsonld_compact_runner: manifest is not valid JSON: %s\n" manifest_path;
      exit 2
    | Some root ->
      let manifest_dir = Filename.dirname manifest_path in
      build_test_cases manifest_dir root

let tally_by_kind tests_and_outcomes kind =
  List.fold_left
    (fun (p, ov, f, s) (tc, o) ->
       if tc.kind <> kind then (p, ov, f, s)
       else match o with
         | Pass -> (p + 1, ov, f, s)
         | Override _ -> (p, ov + 1, f, s)
         | Fail _ -> (p, ov, f + 1, s)
         | Skip _ -> (p, ov, f, s + 1))
    (0, 0, 0, 0) tests_and_outcomes

let run_manifest ~verbose ~list_only manifest_path =
  Printf.printf "=== JSON-LD 1.1 Compaction Test Runner ===\n";
  Printf.printf "Manifest: %s\n\n" manifest_path;
  let overrides = load_local_overrides (find_repo_root ()) "jsonld-compact" in
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
           let o0 = run_test tc in
           (* Local-override reclassification (tests/local-overrides/): a
              carefully-disputed fixture whose output legitimately differs
              from the vendored 1.0-pinned expected output is moved out of
              the FAIL bucket into a distinctly-counted local-override —
              never into plain pass (honesty invariant, anti-pattern #25). *)
           let o = match o0 with
             | Fail _ when List.mem tc.id overrides ->
               Override (Printf.sprintf
                           "carefully-disputed fixture (see tests/local-overrides/): \
                            output differs from the vendored expectation by design")
             | _ -> o0 in
           let elapsed = Unix.gettimeofday () -. t0 in
           let status_tag = match o with
             | Pass -> "ok" | Override _ -> "local-override" | Fail _ -> "FAIL" | Skip _ -> "skip" in
           Printf.eprintf " %s%s\n%!" status_tag
             (if elapsed >= 1.0 then Printf.sprintf " (%.1fs)" elapsed else "");
           (match o with
            | Pass -> Printf.printf "  PASS: %s\n" tc.name
            | Override msg -> Printf.printf "  PASS (local-override): %s (%s) — %s\n" tc.name tc.id msg
            | Fail msg -> Printf.printf "  FAIL: %s (%s) — %s\n" tc.name tc.id msg
            | Skip msg -> if verbose then Printf.printf "  skip: %s — %s\n" tc.name msg);
           (tc, o))
        tests
    in
    Printf.printf "\n========================================\n";
    Printf.printf "Suite Results:\n";
    List.iter
      (fun kind ->
         let (p, ov, f, s) = tally_by_kind outcomes kind in
         if p + ov + f + s > 0 then
           Printf.printf "  %-20s pass:%d local-override:%d fail:%d skip:%d\n" (kind_label kind) p ov f s)
      [ K_Positive; K_Negative; K_Unknown ];
    Printf.printf "========================================\n";
    let pass, override, fail, skip =
      List.fold_left
        (fun (p, ov, f, s) (_, o) ->
           match o with
           | Pass -> (p + 1, ov, f, s)
           | Override _ -> (p, ov + 1, f, s)
           | Fail _ -> (p, ov, f + 1, s)
           | Skip _ -> (p, ov, f, s + 1))
        (0, 0, 0, 0) outcomes
    in
    Printf.printf "TOTAL: %d pass, %d fail, %d local-override, %d skip (out of %d)\n" pass fail override skip total;
    Printf.printf "========================================\n";
    (* Exact final-line format consumed by generate-report.sh's generic
       "N pass, M fail (out of K)" score-line regex. Local overrides are
       counted DISTINCTLY — never folded into plain pass. *)
    Printf.printf "jsonld-compact: %d pass, %d fail, %d local-override, %d skip (out of %d)\n"
      pass fail override skip total;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "JSON-LD 1.1 Compaction manifest runner — compact suite.\n\
     \n\
     Usage:\n\
     \  ./jsonld_compact_runner              Run the default compact manifest\n\
     \  ./jsonld_compact_runner <manifest>   Run a specific manifest.jsonld\n\
     \  ./jsonld_compact_runner --list       List parsed test entries\n\
     \  ./jsonld_compact_runner -v|--verbose Show skip reasons too (FAIL always shown)\n\
     \  ./jsonld_compact_runner --help       Show this help\n"

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
      Printf.eprintf "jsonld_compact_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with
    | Some p -> p
    | None -> default_manifest ()
  in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
