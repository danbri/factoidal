(* JSON-LD 1.1 HTML manifest runner — the html-manifest test suite, whose
   inputs are HTML documents carrying JSON-LD in
   <script type="application/ld+json"> elements.

   Pipeline per test:
     - read the .html input (input field may carry a `#id` fragment);
     - extract the embedded JSON-LD via the F*-extracted
       Parser_JSONLD_Html.extract_jsonld_from_html (fragment-select, or
       extractAllScripts -> JSON array, or first script);
     - dispatch by the entry's second @type:
         jld:ExpandTest -> Parser_JSONLD.expand_document, compared with
                           Parser_JSONLD.jsonld_expanded_equal;
         jld:ToRDFTest  -> Parser_JSONLD.parse_jsonld -> dataset, compared
                           via RDF_Canonical.canonicalize_to_nquads;
       (CompactTest / FlattenTest are reported skip — their algorithms have
        their own runners but are not wired through HTML extraction yet.)
     - PositiveEvaluationTest passes on a matching result; NegativeEvaluation
       passes when extraction/parse yields None (no script / malformed).

   This file is a CONSUMER: file I/O, manifest traversal, HTML-fragment
   splitting, and dispatch only. All HTML extraction, JSON parsing, JSON-LD
   expansion, RDF conversion and canonicalization live in F* (Iron Rules
   #1/#4/#7). Mirrors bin/jsonld-expand-runner and bin/jsonld-runner. *)

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

let jsonld_test_base = "https://w3c.github.io/json-ld-api/tests/"
let jsonld_fixture_root () =
  Filename.concat (find_repo_root ()) "third_party/testing/json-ld/tests"

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

(* ---- thin wrappers over the F*-extracted JSON accessors ---- *)
let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None
let to_fs = function Some x -> FStar_Pervasives_Native.Some x | None -> FStar_Pervasives_Native.None

let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)
let opt_str_field key entry =
  match field "option" entry with Some o -> str_field key o | None -> None
let opt_bool_field key entry =
  match field "option" entry with
  | Some o -> opt_of_fs (Parser_JSON.json_get_bool key o)
  | None -> None

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

type algo = A_Expand | A_ToRdf | A_Compact | A_Flatten | A_Other
let algo_of types =
  if List.mem "jld:ExpandTest" types then A_Expand
  else if List.mem "jld:ToRDFTest" types then A_ToRdf
  else if List.mem "jld:CompactTest" types then A_Compact
  else if List.mem "jld:FlattenTest" types then A_Flatten
  else A_Other

type test_case = {
  id : string;
  name : string;
  kind : kind;
  algo : algo;
  input_path : string;             (* fragment stripped *)
  fragment : string option;
  extract_all : bool;
  expect : string option;
  context : string option;         (* Compact/Flatten compaction context *)
  base_override : string option;
  expand_context : string option;
  processing_mode : string option;
  spec_version : string option;
  manifest_dir : string;
}

(* Split "html/e003-in.html#second" -> ("html/e003-in.html", Some "second"). *)
let split_fragment s =
  match String.index_opt s '#' with
  | None -> (s, None)
  | Some i ->
    (String.sub s 0 i, Some (String.sub s (i + 1) (String.length s - i - 1)))

let build_test_cases manifest_dir root =
  match arr_field "sequence" root with
  | None -> []
  | Some entries ->
    List.filter_map (fun e ->
      match str_field "@id" e, str_field "input" e with
      | Some id, Some input ->
        let name = match str_field "name" e with Some n -> n | None -> id in
        let (path, frag) = split_fragment input in
        let types = jld_types e in
        Some {
          id; name; kind = classify types; algo = algo_of types;
          input_path = path; fragment = frag;
          extract_all = (match opt_bool_field "extractAllScripts" e with Some b -> b | None -> false);
          expect = str_field "expect" e;
          context = str_field "context" e;
          base_override = opt_str_field "base" e;
          expand_context = opt_str_field "expandContext" e;
          processing_mode = opt_str_field "processingMode" e;
          spec_version = opt_str_field "specVersion" e;
          manifest_dir;
        }
      | _ -> None) entries

type outcome = Pass | Fail of string | Skip of string

(* Effective document base IRI. The HTML <base href> element, when present,
   ALWAYS applies, resolved against the fallback base (which is option.base
   if the test sets one, else the document URL). A relative <base href> thus
   resolves against option.base; an absolute one wins outright. With no
   <base> element the fallback stands. *)
let compute_base tc html =
  let fallback = match tc.base_override with
    | Some b -> b | None -> jsonld_test_base ^ tc.input_path in
  match opt_of_fs (Parser_JSONLD_Html.extract_html_base html) with
  | Some hb -> RDF_IRI.resolve_iri_v2 fallback hb
  | None -> fallback

let fs_processing_mode tc =
  match tc.processing_mode, tc.spec_version with
  | Some s, _ -> FStar_Pervasives_Native.Some s
  | None, Some sv -> FStar_Pervasives_Native.Some sv
  | None, None -> FStar_Pervasives_Native.None

let run_expand tc base json =
  let fs_ec = match tc.expand_context with
    | Some rel -> FStar_Pervasives_Native.Some (jsonld_test_base ^ rel)
    | None -> FStar_Pervasives_Native.None in
  let got = opt_of_fs
    (Parser_JSONLD.expand_document json
       (FStar_Pervasives_Native.Some base) fs_ec (fs_processing_mode tc)) in
  match tc.kind with
  | K_Negative -> (match got with None -> Pass | Some _ -> Fail "should reject but expanded")
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
             else Fail "expanded JSON-LD differs from expected"
           | None, _ -> Fail "expand_document returned None on a positive test"
           | _, None -> Fail "could not parse expected .jsonld")))

let run_torqf tc base json =
  let fs_ec = match tc.expand_context with
    | Some rel -> FStar_Pervasives_Native.Some (jsonld_test_base ^ rel)
    | None -> FStar_Pervasives_Native.None in
  let got = opt_of_fs
    (Parser_JSONLD.parse_jsonld json
       (FStar_Pervasives_Native.Some base)
       FStar_Pervasives_Native.None   (* rdfDirection: html tests don't set it *)
       fs_ec (fs_processing_mode tc)) in
  match tc.kind with
  | K_Negative -> (match got with None -> Pass | Some _ -> Fail "should reject but converted")
  | K_Unknown -> Skip "unknown evaluation kind"
  | K_Positive ->
    (match tc.expect with
     | None -> Fail "positive test has no `expect` file"
     | Some rel ->
       (match read_file (Filename.concat tc.manifest_dir rel) with
        | None -> Fail (Printf.sprintf "expected .nq not found: %s" rel)
        | Some exp_raw ->
          (match got with
           | None -> Fail "parse_jsonld returned None on a positive test"
           | Some got_ds ->
             let exp_ds = Parser_NQuads.parse_nquads exp_raw in
             let gc = RDF_Canonical.canonicalize_to_nquads got_ds in
             let ec = RDF_Canonical.canonicalize_to_nquads exp_ds in
             if gc = ec then Pass else Fail "canonical N-Quads differ")))

(* Shared: compare an already-produced json_val result against the parsed
   `expect` .jsonld via jsonld_expanded_equal (the JSON-LD structural
   equality the compact/flatten runners use). *)
let compare_json_result tc got what =
  match tc.kind with
  | K_Negative -> (match got with None -> Pass | Some _ -> Fail ("should reject but " ^ what))
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
             else Fail (what ^ " JSON-LD differs from expected")
           | None, _ -> Fail (what ^ "_document returned None on a positive test")
           | _, None -> Fail "could not parse expected .jsonld")))

(* Read the compaction context doc named by the test's `context` field. *)
let read_context tc =
  match tc.context with
  | None -> None
  | Some rel -> read_file (Filename.concat tc.manifest_dir rel)

let fs_ctx_url tc =
  match tc.context with
  | Some rel -> FStar_Pervasives_Native.Some (jsonld_test_base ^ rel)
  | None -> FStar_Pervasives_Native.None

let run_compact tc base json =
  match read_context tc with
  | None -> Fail "CompactTest has no `context`"
  | Some ctx ->
    let got = opt_of_fs
      (JSONLD_Compact.compact_document json ctx
         (FStar_Pervasives_Native.Some base) (fs_ctx_url tc)
         true true                    (* compactArrays / compactToRelative default true *)
         (fs_processing_mode tc)) in
    compare_json_result tc got "compact"

let run_flatten tc base json =
  let fs_ctx_doc = match read_context tc with
    | Some c -> FStar_Pervasives_Native.Some c
    | None -> FStar_Pervasives_Native.None in
  let got = opt_of_fs
    (JSONLD_Flatten.flatten_document json fs_ctx_doc
       (FStar_Pervasives_Native.Some base) (fs_ctx_url tc)
       true                           (* compactArrays default true *)
       (fs_processing_mode tc)) in
  compare_json_result tc got "flatten"

let dispatch tc base json =
  match tc.algo with
  | A_Expand  -> run_expand tc base json
  | A_ToRdf   -> run_torqf tc base json
  | A_Compact -> run_compact tc base json
  | A_Flatten -> run_flatten tc base json
  | A_Other   -> Skip "unrecognized JSON-LD test type"

let run_test tc =
  match tc.algo with
  | A_Other -> Skip "unrecognized JSON-LD test type"
  | A_Expand | A_ToRdf | A_Compact | A_Flatten ->
    let input_full = Filename.concat tc.manifest_dir tc.input_path in
    (match read_file input_full with
     | None -> (match tc.kind with K_Negative -> Pass
                | _ -> Fail (Printf.sprintf "input file not found: %s" input_full))
     | Some html ->
       (match opt_of_fs
                (Parser_JSONLD_Html.extract_jsonld_from_html html (to_fs tc.fragment) tc.extract_all) with
        | None ->
          (* No script extracted. For a NegativeEvaluation test (e.g. a
             missing fragment target, or expand of a script-less document)
             that IS the expected outcome. For a positive test (e.g. tr006,
             toRdf of a script-less document) the document is empty — feed
             the empty JSON-LD document [] to the algorithm. *)
          (match tc.kind with
           | K_Negative -> Pass
           | _ -> dispatch tc (compute_base tc html) "[]")
        | Some json -> dispatch tc (compute_base tc html) json))

(* ---- manifest driver ---- *)
let manifest_candidates () =
  let r = find_repo_root () in
  [ Filename.concat r "third_party/testing/json-ld/tests/html-manifest.jsonld";
    "third_party/testing/json-ld/tests/html-manifest.jsonld";
    "../../third_party/testing/json-ld/tests/html-manifest.jsonld";
    "../../../third_party/testing/json-ld/tests/html-manifest.jsonld" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ()) "third_party/testing/json-ld/tests/html-manifest.jsonld"

let run_manifest ~verbose manifest_path =
  match read_file manifest_path with
  | None -> Printf.eprintf "manifest not found: %s\n" manifest_path; exit 2
  | Some raw ->
    (match opt_of_fs (Parser_JSON.parse_json raw) with
     | None -> Printf.eprintf "could not parse manifest JSON: %s\n" manifest_path; exit 2
     | Some root ->
       let manifest_dir = Filename.dirname manifest_path in
       let tests = build_test_cases manifest_dir root in
       let pass = ref 0 and fail = ref 0 and skip = ref 0 in
       Printf.printf "=== W3C JSON-LD 1.1 HTML Test Runner ===\n";
       Printf.printf "Manifest: %s\n\n" manifest_path;
       List.iter (fun tc ->
         match run_test tc with
         | Pass -> incr pass; Printf.printf "  PASS: %s\n" tc.name
         | Fail m -> incr fail;
           Printf.printf "  FAIL: %s — %s\n" tc.name (if verbose then m else head m 80)
         | Skip m -> incr skip; Printf.printf "  skip: %s — %s\n" tc.name m) tests;
       Printf.printf "\n========================================\n";
       Printf.printf "Suite Results:\n";
       Printf.printf "  %-35s pass:%d fail:%d skip:%d unsupported:%d\n"
         "jsonld-html" !pass !fail !skip 0;
       Printf.printf "========================================\n";
       (* Final summary line in the `(out of N)` shape the dashboard's
          scrape_last_summary reads. *)
       let total = !pass + !fail + !skip in
       Printf.printf "jsonld-html: %d pass, %d fail, %d skip (out of %d)\n" !pass !fail !skip total;
       if !fail > 0 then exit 1 else exit 0)

let () =
  let verbose = ref false and manifest = ref "" in
  Array.iteri (fun i a ->
    if i > 0 then
      if a = "-v" || a = "--verbose" then verbose := true
      else if String.length a > 0 && a.[0] <> '-' then manifest := a) Sys.argv;
  let m = if !manifest = "" then default_manifest () else !manifest in
  run_manifest ~verbose:!verbose m
