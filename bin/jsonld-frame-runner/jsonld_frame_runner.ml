(* JSON-LD 1.1 Framing manifest runner (W3C json-ld-framing test suite).

   Pipeline per test:
     - read the `-in.jsonld` input and `-frame.jsonld` frame documents;
     - call the F*-extracted JSONLD_Frame.frame_document (expand input +
       frame -> flatten input to a node map -> frame-match/embed -> compact
       against the frame's context);
     - compare the result to the `-out.jsonld` oracle via
       Parser_JSONLD.jsonld_expanded_equal;
     - PositiveEvaluationTest passes on a match; NegativeEvaluationTest
       passes when frame_document returns None.

   Consumer only: file I/O, manifest traversal, dispatch. All framing
   semantics live in formal/fstar/JSONLD.Frame.fst (Iron Rules #1/#7).
   Mirrors bin/jsonld-compact-runner. *)

let find_repo_root () =
  let rec walk d =
    if d = "/" || d = "" then None
    else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
    else walk (Filename.dirname d)
  in
  let start = try Filename.dirname (Sys.executable_name) with _ -> Sys.getcwd () in
  match walk start with
  | Some r -> r
  | None -> (match walk (Sys.getcwd ()) with Some r -> r | None -> Sys.getcwd ())

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n; close_in ic; Some (Bytes.to_string s)
  with Sys_error _ -> None

let head s n = if String.length s <= n then s else String.sub s 0 n ^ " …(truncated)"

let jsonld_test_base = "https://w3c.github.io/json-ld-framing/tests/"
let jsonld_fixture_root () =
  Filename.concat (find_repo_root ()) "third_party/testing/json-ld-framing/tests"
let jsonld_document_loader (iri : string) : string option =
  let prefix = jsonld_test_base in
  let plen = String.length prefix and ilen = String.length iri in
  if ilen >= plen && String.sub iri 0 plen = prefix then
    read_file (Filename.concat (jsonld_fixture_root ()) (String.sub iri plen (ilen - plen)))
  else None
let () =
  JSONLD_Loader.jsonld_loader_register
    (fun iri -> match jsonld_document_loader iri with
       | Some s -> FStar_Pervasives_Native.Some s
       | None -> FStar_Pervasives_Native.None)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None
let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)
let opt_str_field key entry =
  match field "option" entry with Some o -> str_field key o | None -> None

let jld_types entry =
  match field "@type" entry with
  | Some (Parser_JSON.JArray items) ->
    List.filter_map (function Parser_JSON.JString s -> Some s | _ -> None) items
  | Some (Parser_JSON.JString s) -> [ s ]
  | _ -> []

type kind = K_Positive | K_Negative | K_Unknown
let classify types =
  if List.mem "jld:PositiveEvaluationTest" types then K_Positive
  else if List.mem "jld:NegativeEvaluationTest" types then K_Negative
  else K_Unknown

type test_case = {
  id : string; name : string; kind : kind;
  input : string; frame : string; expect : string option;
  base_override : string option; processing_mode : string option;
  spec_version : string option; manifest_dir : string;
}

let build_test_cases manifest_dir root =
  match arr_field "sequence" root with
  | None -> []
  | Some entries ->
    List.filter_map (fun e ->
      match str_field "@id" e, str_field "input" e, str_field "frame" e with
      | Some id, Some input, Some frame ->
        let name = match str_field "name" e with Some n -> n | None -> id in
        Some { id; name; kind = classify (jld_types e);
               input; frame; expect = str_field "expect" e;
               base_override = opt_str_field "base" e;
               processing_mode = opt_str_field "processingMode" e;
               spec_version = opt_str_field "specVersion" e;
               manifest_dir }
      | _ -> None) entries

type outcome = Pass | Fail of string | Skip of string

let test_base tc =
  match tc.base_override with Some b -> b | None -> jsonld_test_base ^ tc.input

let fs_processing_mode tc =
  match tc.processing_mode, tc.spec_version with
  | Some s, _ -> FStar_Pervasives_Native.Some s
  | None, Some sv -> FStar_Pervasives_Native.Some sv
  | None, None -> FStar_Pervasives_Native.None

let run_test tc =
  let in_path = Filename.concat tc.manifest_dir tc.input in
  let frame_path = Filename.concat tc.manifest_dir tc.frame in
  match read_file in_path, read_file frame_path with
  | None, _ -> Fail (Printf.sprintf "input not found: %s" in_path)
  | _, None -> Fail (Printf.sprintf "frame not found: %s" frame_path)
  | Some input_c, Some frame_c ->
    let got = opt_of_fs
      (JSONLD_Frame.frame_document input_c frame_c
         (FStar_Pervasives_Native.Some (test_base tc))
         (fs_processing_mode tc)) in
    (match tc.kind with
     | K_Negative -> (match got with None -> Pass | Some _ -> Fail "should reject but framed")
     | K_Unknown -> Skip "unknown evaluation kind"
     | K_Positive ->
       (match tc.expect with
        | None -> Fail "positive test has no `expect` file"
        | Some rel ->
          (match read_file (Filename.concat tc.manifest_dir rel) with
           | None -> Fail (Printf.sprintf "expected .jsonld not found: %s" rel)
           | Some exp_raw ->
             (match got, opt_of_fs (Parser_JSON.parse_json exp_raw) with
              | Some g, Some exp ->
                if Parser_JSONLD.jsonld_expanded_equal g exp then Pass
                else Fail "framed JSON-LD differs from expected"
              | None, _ -> Fail "frame_document returned None on a positive test"
              | _, None -> Fail "could not parse expected .jsonld"))))

let manifest_candidates () =
  let r = find_repo_root () in
  [ Filename.concat r "third_party/testing/json-ld-framing/tests/frame-manifest.jsonld";
    "third_party/testing/json-ld-framing/tests/frame-manifest.jsonld";
    "../../third_party/testing/json-ld-framing/tests/frame-manifest.jsonld";
    "../../../third_party/testing/json-ld-framing/tests/frame-manifest.jsonld" ]
let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ()) "third_party/testing/json-ld-framing/tests/frame-manifest.jsonld"

let run_manifest ~verbose manifest_path =
  match read_file manifest_path with
  | None -> Printf.eprintf "manifest not found: %s\n" manifest_path; exit 2
  | Some raw ->
    (match opt_of_fs (Parser_JSON.parse_json raw) with
     | None -> Printf.eprintf "could not parse manifest JSON\n"; exit 2
     | Some root ->
       let manifest_dir = Filename.dirname manifest_path in
       let tests = build_test_cases manifest_dir root in
       let pass = ref 0 and fail = ref 0 and skip = ref 0 in
       Printf.printf "=== W3C JSON-LD 1.1 Framing Test Runner ===\n";
       Printf.printf "Manifest: %s\n\n" manifest_path;
       List.iter (fun tc ->
         match run_test tc with
         | Pass -> incr pass; Printf.printf "  PASS: %s\n" tc.name
         | Fail m -> incr fail;
           Printf.printf "  FAIL: %s — %s\n" tc.name (if verbose then m else head m 80)
         | Skip m -> incr skip; Printf.printf "  skip: %s — %s\n" tc.name m) tests;
       let total = !pass + !fail + !skip in
       Printf.printf "\n========================================\n";
       Printf.printf "Suite Results:\n";
       Printf.printf "  %-35s pass:%d fail:%d skip:%d unsupported:%d\n" "jsonld-frame" !pass !fail !skip 0;
       Printf.printf "========================================\n";
       Printf.printf "jsonld-frame: %d pass, %d fail, %d skip (out of %d)\n" !pass !fail !skip total;
       if !fail > 0 then exit 1 else exit 0)

let () =
  let verbose = ref false and manifest = ref "" in
  Array.iteri (fun i a ->
    if i > 0 then
      if a = "-v" || a = "--verbose" then verbose := true
      else if String.length a > 0 && a.[0] <> '-' then manifest := a) Sys.argv;
  let m = if !manifest = "" then default_manifest () else !manifest in
  run_manifest ~verbose:!verbose m
