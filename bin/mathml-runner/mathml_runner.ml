(* Content MathML evaluation runner.

   Reads third_party/testing/mathml/manifest.json (a REC-cited Content
   MathML evaluation corpus — see that dir's README.md for provenance),
   parses each test's `input` MathML with the F*-extracted
   Parser_XML.parse_xml_document, evaluates the resulting Content MathML
   tree with MathML_Content.eval_doc_env, and compares the computed
   value's canonical string (MathML_Content.value_to_string) against the
   manifest's `expectedValue`.

   !! THIS IS I/O GLUE — NO MATHML SEMANTIC LOGIC LIVES HERE !!
   Every arithmetic/relational decision, every number-literal parse, and
   the value canonicalisation all live in
   formal/fstar/MathML.Content.fst (extracted to MathML_Content); all XML
   parsing lives in formal/fstar/Parser.XML.fst (Parser_XML); the JSON
   manifest is read with the F*-extracted RFC 8259 parser
   Parser_JSON.parse_json. This file only does file I/O, manifest
   traversal, environment plumbing, and exact string comparison.
   Per CLAUDE.md iron rule #7 / #11 / anti-pattern #15.

   Comparison is EXACT: MathML_Content models values as exact rationals,
   so value_to_string yields a canonical form (`n`, `num/den`,
   `true`/`false`, or `undef`) and equality is exact string equality —
   no floating-point tolerance is needed or applied.

   Usage:
     ./mathml_runner                 Run the default corpus
     ./mathml_runner <manifest>      Run a specific manifest.json
     ./mathml_runner -v|--verbose    Print expected-vs-got on FAIL
     ./mathml_runner --help          Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (same pattern as jsonld_fromrdf_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/mathml/manifest.json";
    "third_party/testing/mathml/manifest.json";
    "../../third_party/testing/mathml/manifest.json";
    "../../../third_party/testing/mathml/manifest.json" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ()) "third_party/testing/mathml/manifest.json"

let matrix_manifest_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root "third_party/testing/mathml/matrix-manifest.json";
    "third_party/testing/mathml/matrix-manifest.json";
    "../../third_party/testing/mathml/matrix-manifest.json";
    "../../../third_party/testing/mathml/matrix-manifest.json" ]

(* The default run scores both the scalar corpus and the linear-algebra
   corpus (matrix-manifest.json, REC MathML3 section 4.4.10). *)
let default_manifests () =
  let scalar = default_manifest () in
  match List.find_opt Sys.file_exists (matrix_manifest_candidates ()) with
  | Some m -> [scalar; m]
  | None -> [scalar]

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

(* ------------------------------------------------------------------ *)
(* Thin wrappers over the F*-extracted JSON accessors. *)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)

(* Extract an env object {"x":"41", ...} into an (name, numeric-string)
   assoc list for MathML_Content. Values may be JSON strings or numbers. *)
let env_of entry =
  match field "env" entry with
  | Some (Parser_JSON.JObject kvs) ->
    List.filter_map
      (fun (k, v) ->
         match v with
         | Parser_JSON.JString s -> Some (k, s)
         | Parser_JSON.JNumber s -> Some (k, s)
         | _ -> None)
      kvs
  | _ -> []

(* ------------------------------------------------------------------ *)
(* Per-test record. *)

type test_case = {
  name : string;
  spec : string;
  input : string;
  expected : string;
  env : (string * string) list;
}

let build_test_cases root =
  match arr_field "tests" root with
  | None -> []
  | Some entries ->
    List.filter_map
      (fun e ->
         match str_field "name" e, str_field "input" e, str_field "expectedValue" e with
         | Some name, Some input, Some expected ->
           Some {
             name;
             spec = (match str_field "spec" e with Some s -> s | None -> "");
             input;
             expected;
             env = env_of e;
           }
         | _ -> None)
      entries

(* ------------------------------------------------------------------ *)
(* Outcome + per-test execution. *)

type outcome = Pass | Fail of string

(* Informational: Content vs Presentation classification of the input. *)
let kind_label root =
  match MathML_Content.mathml_kind_of root with
  | MathML_Content.MK_Content -> "Content"
  | MathML_Content.MK_Presentation -> "Presentation"
  | MathML_Content.MK_Unknown -> "Unknown"

let run_test tc =
  match opt_of_fs (Parser_XML.parse_xml_document tc.input) with
  | None -> Fail "input MathML did not parse (Parser_XML returned None)"
  | Some root ->
    (* eval_doc_env_string routes through the matrix-aware evaluation path
       (Math.Matrix.mres): scalars stringify exactly as before, matrices as
       [[..],[..]], vectors as [..], undefined as "undef". All arithmetic,
       shape checking and canonicalisation live in MathML.Content /
       Math.Matrix; this runner only compares strings. *)
    let got = MathML_Content.eval_doc_env_string tc.env root in
    if got = tc.expected then Pass
    else
      let reason = MathML_Content.eval_doc_env_reason tc.env root in
      Fail (Printf.sprintf "expected %s, got %s%s"
              tc.expected got
              (if String.length reason > 0 then " (" ^ reason ^ ")" else ""))

(* ------------------------------------------------------------------ *)
(* Manifest load. *)

let load_manifest manifest_path =
  match read_file manifest_path with
  | None ->
    Printf.eprintf "mathml_runner: cannot read manifest: %s\n" manifest_path;
    exit 2
  | Some raw ->
    match opt_of_fs (Parser_JSON.parse_json raw) with
    | None ->
      Printf.eprintf "mathml_runner: manifest is not valid JSON: %s\n" manifest_path;
      exit 2
    | Some root -> build_test_cases root

(* ------------------------------------------------------------------ *)

let () =
  let args = Array.to_list Sys.argv in
  let verbose = List.exists (fun a -> a = "-v" || a = "--verbose") args in
  if List.exists (fun a -> a = "--help") args then begin
    print_string
      "mathml_runner — Content MathML evaluation corpus runner\n\
      \  ./mathml_runner              Run the default corpus\n\
      \  ./mathml_runner <manifest>   Run a specific manifest.json\n\
      \  ./mathml_runner -v|--verbose Show expected-vs-got on FAIL\n\
      \  ./mathml_runner --help       Show this help\n";
    exit 0
  end;
  let manifest_paths =
    match List.filter (fun a -> String.length a > 0 && a.[0] <> '-') (List.tl args) with
    | m :: _ -> [m]
    | [] -> default_manifests ()
  in
  let tests = List.concat_map load_manifest manifest_paths in
  let results = List.map (fun tc -> (tc, run_test tc)) tests in
  let pass = List.length (List.filter (fun (_, o) -> o = Pass) results) in
  let fail =
    List.length (List.filter (fun (_, o) -> match o with Fail _ -> true | _ -> false) results) in
  let total = List.length results in
  (* Informational Content/Presentation detection tally. *)
  let detect =
    List.filter_map
      (fun (tc, _) ->
         match opt_of_fs (Parser_XML.parse_xml_document tc.input) with
         | Some root -> Some (kind_label root)
         | None -> None)
      results in
  let count lbl = List.length (List.filter (fun k -> k = lbl) detect) in
  List.iter
    (fun (tc, o) ->
       match o with
       | Pass -> Printf.printf "  PASS  %-26s %s\n" tc.name tc.spec
       | Fail r ->
         Printf.printf "  FAIL  %-26s %s\n" tc.name tc.spec;
         if verbose then Printf.printf "        %s\n" r)
    results;
  (* Named failing categories. *)
  let failing =
    List.filter_map
      (fun (tc, o) -> match o with Fail r -> Some (tc.name, r) | _ -> None)
      results in
  if failing <> [] then begin
    Printf.printf "\nFailing tests:\n";
    List.iter (fun (n, r) -> Printf.printf "  - %s: %s\n" n r) failing
  end;
  Printf.printf "\nDetection (informational): %d Content, %d Presentation, %d Unknown\n"
    (count "Content") (count "Presentation") (count "Unknown");
  Printf.printf "Content MathML evaluation: %d pass, %d fail (out of %d)\n"
    pass fail total
