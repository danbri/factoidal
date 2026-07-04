(* JSON-LD 1.1 toRdf manifest runner — Phase 2 of the JSON-LD program.

   Reads third_party/testing/json-ld/tests/toRdf-manifest.jsonld,
   walks its `sequence`, and for each test:
     - loads the `input` .jsonld file;
     - calls the F*-extracted Parser_JSONLD.parse_jsonld (expanded-form
       only — see formal/fstar/Parser.JSONLD.fst module banner);
     - for PositiveEvaluationTest, compares the resulting dataset
       against the `expect` .nq file via RDF_Canonical.canonicalize_to_nquads
       string equality (both sides parsed, then canonicalized — this
       makes the comparison independent of blank-node label choices);
     - for NegativeEvaluationTest, PASSes iff parse_jsonld returns None;
     - for PositiveSyntaxTest, PASSes iff parse_jsonld returns Some _
       (no `expect` file to compare against).

   !! THIS IS I/O GLUE — NO RDF/JSON-LD SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All JSON-LD
   deserialization semantics live in formal/fstar/Parser.JSONLD.fst;
   all canonicalization semantics live in formal/fstar/RDF.Canonical.fst.
   This file only does file I/O, manifest traversal, and string
   comparison of two already-canonicalized N-Quads strings.

   Per Iron Rule #7 (parsers belong in F*), the manifest itself — a
   JSON-LD document — is parsed with the F*-extracted RFC 8259 parser
   (Parser_JSON.parse_json), not any OCaml JSON library. There is no
   hand-rolled JSON parsing in this file.

   Scope (see docs/designissues/2026-07-04-jsonld-program-lessons.md
   and docs/designissues/2026-07-05-jsonld-phase2-runner.md):
     - toRdf manifest only (not compact/flatten/frame/fromRdf/html).
     - Remote-context tests are out of scope until JSONLD.Context /
       JSONLD.Loader land (Phase 3+); every test whose input contains
       "@context" is scored FAIL, not SKIP, so the score reflects the
       real Phase 1 burn-down instead of flattering the number via
       skips (anti-pattern #3/#25).
     - Tests tagged option.specVersion == "json-ld-1.0" are SKIPPED —
       this program targets JSON-LD 1.1 only (CLAUDE.md iron rule #5's
       sibling policy for JSON-LD: never default to a superseded
       version's manifest when a newer one exists).

   Usage:
     ./jsonld_runner                Run the default toRdf manifest
     ./jsonld_runner <manifest>     Run a specific manifest.jsonld
     ./jsonld_runner --list         List parsed test entries (no execution)
     ./jsonld_runner -v|--verbose   Show expected-vs-got diff on FAIL
     ./jsonld_runner --help         Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to rdfc10_runner.ml / owl_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/json-ld/tests/toRdf-manifest.jsonld";
    "third_party/testing/json-ld/tests/toRdf-manifest.jsonld";
    "../../third_party/testing/json-ld/tests/toRdf-manifest.jsonld";
    "../../../third_party/testing/json-ld/tests/toRdf-manifest.jsonld" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/json-ld/tests/toRdf-manifest.jsonld"

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

(* Manual substring search — no external dependency, just enough to
   detect "@context" in raw input bytes. *)
let contains_substring ~needle haystack =
  let nlen = String.length needle and hlen = String.length haystack in
  let rec go i =
    if i + nlen > hlen then false
    else if String.sub haystack i nlen = needle then true
    else go (i + 1)
  in
  nlen = 0 || go 0

let head s n =
  if String.length s <= n then s else String.sub s 0 n ^ " …(truncated)"

(* ------------------------------------------------------------------ *)
(* Thin wrappers over the F*-extracted JSON accessors.

   json_get_field / json_get_string / json_get_array all return
   FStar_Pervasives_Native.option; unwrap once to plain OCaml option
   so the rest of this file reads like ordinary OCaml. *)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)

(* @type is an array of strings for every sequence entry in the toRdf
   manifest (jld:PositiveEvaluationTest / NegativeEvaluationTest /
   PositiveSyntaxTest, each paired with jld:ToRDFTest); be lenient
   about a bare string too, in case a future manifest edit collapses
   it. *)
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
  | K_PositiveSyntax
  | K_Unknown

let classify types =
  if List.mem "jld:PositiveEvaluationTest" types then K_Positive
  else if List.mem "jld:NegativeEvaluationTest" types then K_Negative
  else if List.mem "jld:PositiveSyntaxTest" types then K_PositiveSyntax
  else K_Unknown

let kind_label = function
  | K_Positive -> "toRdf-Positive"
  | K_Negative -> "toRdf-Negative"
  | K_PositiveSyntax -> "toRdf-PositiveSyntax"
  | K_Unknown -> "toRdf-Unknown"

let jld_spec_version entry =
  match field "option" entry with
  | Some opt_obj -> str_field "specVersion" opt_obj
  | None -> None

(* ------------------------------------------------------------------ *)
(* Per-test record. *)

type test_case = {
  id : string;
  name : string;
  kind : test_kind;
  input : string;          (* manifest-relative path, e.g. "toRdf/0001-in.jsonld" *)
  expect : string option;  (* manifest-relative path, e.g. "toRdf/0001-out.nq" (Positive only) *)
  spec_version : string option;
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
             manifest_dir;
           }
         | _ -> None)
      entries

(* ------------------------------------------------------------------ *)
(* Outcome + per-test execution. *)

type outcome = Pass | Fail of string | Skip of string

let run_test tc =
  match tc.spec_version with
  | Some "json-ld-1.0" ->
    Skip "option.specVersion=json-ld-1.0 (this program targets JSON-LD 1.1)"
  | _ ->
    let input_path = Filename.concat tc.manifest_dir tc.input in
    (match read_file input_path with
     | None -> Fail (Printf.sprintf "input file not found: %s" input_path)
     | Some content ->
       if contains_substring ~needle:"@context" content then
         (* Phase 1 (Parser.JSONLD) has no @context processing — see
            the module banner. Scored FAIL, not SKIP: per anti-pattern
            #3/#25 the score must show the real burn-down, and a SKIP
            here would flatter the number. This also correctly covers
            NegativeEvaluationTest inputs whose invalidity depends on
            context processing we cannot detect. *)
         Fail "input requires @context processing (Phase 1: expanded-form only, no context support; Phase 3 JSONLD.Context lands this)"
       else
         match tc.kind with
         | K_Positive ->
           (match tc.expect with
            | None -> Fail "manifest entry has no `expect` file"
            | Some expect_rel ->
              let expect_path = Filename.concat tc.manifest_dir expect_rel in
              (match read_file expect_path with
               | None -> Fail (Printf.sprintf "expected .nq file not found: %s" expect_path)
               | Some expect_content ->
                 (match opt_of_fs (Parser_JSONLD.parse_jsonld content) with
                  | None -> Fail "parse_jsonld returned None (expected a valid expanded-form dataset)"
                  | Some got_ds ->
                    let exp_ds = Parser_NQuads.parse_nquads expect_content in
                    let got_canon = RDF_Canonical.canonicalize_to_nquads got_ds in
                    let exp_canon = RDF_Canonical.canonicalize_to_nquads exp_ds in
                    if got_canon = exp_canon then Pass
                    else
                      Fail (Printf.sprintf
                              "canonical N-Quads differ (dataset isomorphism mismatch)\n      expected:\n%s      got:\n%s"
                              (head exp_canon 400) (head got_canon 400)))))
         | K_PositiveSyntax ->
           (match opt_of_fs (Parser_JSONLD.parse_jsonld content) with
            | Some _ -> Pass
            | None -> Fail "parse_jsonld returned None (input was expected to parse without error)")
         | K_Negative ->
           (match opt_of_fs (Parser_JSONLD.parse_jsonld content) with
            | None -> Pass
            | Some _ -> Fail "parse_jsonld succeeded but a parse failure was expected (see manifest expectErrorCode)")
         | K_Unknown -> Skip "unrecognized @type for a toRdf test entry")

(* ------------------------------------------------------------------ *)
(* Manifest load + suite run. *)

let load_manifest manifest_path =
  match read_file manifest_path with
  | None ->
    Printf.eprintf "jsonld_runner: cannot read manifest: %s\n" manifest_path;
    exit 2
  | Some raw ->
    match opt_of_fs (Parser_JSON.parse_json raw) with
    | None ->
      Printf.eprintf "jsonld_runner: manifest is not valid JSON: %s\n" manifest_path;
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
  Printf.printf "=== JSON-LD 1.1 toRdf Test Runner ===\n";
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
           Printf.printf "  %-25s pass:%d fail:%d skip:%d\n" (kind_label kind) p f s)
      [ K_Positive; K_Negative; K_PositiveSyntax; K_Unknown ];
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
    (* Exact final-line format consumed by generate-report.sh's
       generic "N pass, M fail (out of K)" score-line regex; see
       docs/designissues/2026-07-05-jsonld-phase2-runner.md. *)
    Printf.printf "jsonld-toRdf: %d pass, %d fail, %d skip (out of %d)\n"
      pass fail skip total;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "JSON-LD 1.1 toRdf manifest runner — Phase 2 of the JSON-LD program.\n\
     \n\
     Usage:\n\
     \  ./jsonld_runner                Run the default toRdf manifest\n\
     \  ./jsonld_runner <manifest>     Run a specific manifest.jsonld\n\
     \  ./jsonld_runner --list         List parsed test entries (no execution)\n\
     \  ./jsonld_runner -v|--verbose   Show skip reasons too (FAIL always shown)\n\
     \  ./jsonld_runner --help         Show this help\n\
     \n\
     Status: Phase 2 scaffold. Parser.JSONLD is expanded-form-only\n\
     (no @context processing); every test whose input contains\n\
     \"@context\" scores FAIL, not SKIP, per CLAUDE.md anti-pattern\n\
     #3/#25. See docs/designissues/2026-07-05-jsonld-phase2-runner.md\n\
     for the expected baseline breakdown.\n"

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
      Printf.eprintf "jsonld_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with
    | Some p -> p
    | None -> default_manifest ()
  in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
