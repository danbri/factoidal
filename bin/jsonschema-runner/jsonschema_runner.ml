(* JSON Schema draft-07 conformance runner.

   Reads the vendored subset of the official JSON Schema Test Suite under
   third_party/testing/jsonschema/tests/draft7/*.json. Each file is a JSON
   array of groups {description, schema, tests: [{description, data, valid}]}.

   For every test the runner parses the file with the F*-extracted RFC 8259
   parser (Parser_JSON.parse_json), then calls
   JSONSchema_Validate.validate schema data and compares its three-valued
   result to the expected `valid` boolean:
     - VPass  -> valid   (pass iff expected valid)
     - VFail  -> invalid (pass iff expected invalid)
     - VUnsupported -> SKIP (keyword outside slice-1: pattern / format /
       remote or anchor $ref). Never counted as a wrong verdict.

   !! THIS IS I/O GLUE — NO JSON SCHEMA SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #7 / #11 / anti-pattern #15. All validation
   semantics live in formal/fstar/JSONSchema.Validate.fst; all JSON parsing
   in formal/fstar/Parser.JSON.fst. This file does file I/O, array traversal
   (via the F*-extracted parser), and boolean comparison only.

   Usage:
     ./jsonschema_runner              Run the whole vendored draft7 subset
     ./jsonschema_runner <file.json>  Run one suite file
     ./jsonschema_runner -v|--verbose Show per-test FAIL detail
     ./jsonschema_runner --help       Show this help
*)

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

let suite_dir () =
  Filename.concat (find_repo_root ()) "third_party/testing/jsonschema/tests/draft7"

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

(* Thin wrappers over the F*-extracted JSON accessors. *)
let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let field key obj = opt_of_fs (Parser_JSON.json_get_field key obj)
let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)

type outcome = Pass | Fail of string | Skip

(* One test case within a group. *)
let run_one schema data expected =
  match JSONSchema_Validate.validate schema data with
  | JSONSchema_Validate.VUnsupported -> Skip
  | JSONSchema_Validate.VPass -> if expected then Pass else Fail "validator: valid, expected invalid"
  | JSONSchema_Validate.VFail -> if not expected then Pass else Fail "validator: invalid, expected valid"

(* Walk a group's `tests` array; returns (pass, fail, skip, fail-details). *)
let run_group verbose group_desc schema tests =
  List.fold_left
    (fun (p, f, s, details) t ->
       match field "data" t, field "valid" t with
       | Some data, Some (Parser_JSON.JBool expected) ->
         let td = match str_field "description" t with Some d -> d | None -> "?" in
         (match run_one schema data expected with
          | Pass -> (p + 1, f, s, details)
          | Skip -> (p, f, s + 1, details)
          | Fail reason ->
            let d = if verbose then Printf.sprintf "    FAIL [%s] %s -- %s" group_desc td reason :: details else details in
            (p, f + 1, s, d))
       | _ -> (p, f, s + 1, details))
    (0, 0, 0, []) tests

let run_file verbose path =
  match read_file path with
  | None -> Printf.eprintf "jsonschema_runner: cannot read %s\n" path; (0, 0, 0)
  | Some raw ->
    (match opt_of_fs (Parser_JSON.parse_json raw) with
     | None -> Printf.eprintf "jsonschema_runner: not valid JSON: %s\n" path; (0, 0, 0)
     | Some (Parser_JSON.JArray groups) ->
       let (p, f, s, details) =
         List.fold_left
           (fun (p, f, s, details) g ->
              match field "schema" g with
              | None -> (p, f, s, details)
              | Some schema ->
                let gd = match str_field "description" g with Some d -> d | None -> "?" in
                (match field "tests" g with
                 | Some (Parser_JSON.JArray tests) ->
                   let (gp, gf, gs, gdet) = run_group verbose gd schema tests in
                   (p + gp, f + gf, s + gs, gdet @ details)
                 | _ -> (p, f, s, details)))
           (0, 0, 0, []) groups
       in
       Printf.printf "  %-28s %4d pass, %3d fail, %3d skip\n"
         (Filename.basename path) p f s;
       List.iter (fun d -> print_endline d) (List.rev details);
       (p, f, s)
     | Some _ -> Printf.eprintf "jsonschema_runner: top-level is not an array: %s\n" path; (0, 0, 0))

let () =
  let args = Array.to_list Sys.argv in
  let verbose = List.exists (fun a -> a = "-v" || a = "--verbose") args in
  if List.exists (fun a -> a = "--help") args then begin
    print_string
      "jsonschema_runner - JSON Schema draft-07 conformance runner\n\
      \  ./jsonschema_runner              Run the whole vendored draft7 subset\n\
      \  ./jsonschema_runner <file.json>  Run one suite file\n\
      \  ./jsonschema_runner -v|--verbose Show per-test FAIL detail\n\
      \  ./jsonschema_runner --help       Show this help\n";
    exit 0
  end;
  let explicit = List.filter (fun a -> String.length a > 0 && a.[0] <> '-') (List.tl args) in
  let files =
    match explicit with
    | [] ->
      let dir = suite_dir () in
      (try
         Sys.readdir dir
         |> Array.to_list
         |> List.filter (fun n -> Filename.check_suffix n ".json")
         |> List.sort compare
         |> List.map (fun n -> Filename.concat dir n)
       with Sys_error _ ->
         Printf.eprintf "jsonschema_runner: cannot list suite dir %s\n" dir; exit 2)
    | fs -> fs
  in
  let (p, f, s) =
    List.fold_left
      (fun (p, f, s) path -> let (fp, ff, fs) = run_file verbose path in (p + fp, f + ff, s + fs))
      (0, 0, 0) files
  in
  let total = p + f + s in
  Printf.printf "\n^JSON Schema (draft7): %d pass, %d fail, %d skip (of %d)\n" p f s total
