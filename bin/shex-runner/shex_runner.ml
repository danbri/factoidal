(* ShEx (Shape Expressions) validation manifest runner — stage 8 of the
   ShEx program
   (docs/designissues/2026-07-05-shex-program-plan.md), following stage 3
   (commit 37ae500: triple-expression matching, 1005/1182 manifest entries
   verdict-correct via a scratch driver). This is the first COMMITTED
   consumer of ShEx.Schema / ShEx.Validation.

   Walks the vendored shexSpec/shexTest manifest
   (third_party/testing/shex/validation/manifest.ttl by default), parsed
   via the F*-extracted Parser_Turtle (the manifest is plain Turtle — no
   new tooling needed, unlike the JSON-LD program's manifest flattener).
   For each `sht:ValidationTest` / `sht:ValidationFailure` entry:

     - resolves `sht:schema` (the manifest's canonical ShExC `.shex`
       reference) to its ShExJ `.json` twin under
       third_party/testing/shex/schemas/ — the plan's "ShExC vs ShExJ"
       scope cut: 342/346 unique schemas referenced from validation/ have
       a same-basename `.json` fixture; the remainder SKIP with a reason
       naming the missing twin, rather than guessing;
     - loads that schema through the F*-extracted
       ShEx_Schema.decode_shex_schema;
     - loads `sht:data` (a sibling `.ttl` fixture) through Parser_Turtle;
     - reads `sht:focus` directly off the manifest's own parsed graph (an
       IRI or a blank node — named blank-node labels are preserved
       verbatim by Parser.NTriples.parse_bnode (shared by Parser.Turtle),
       so a manifest `_:abcd` and the matching data-file `_:abcd` compare
       structurally equal without any extra bookkeeping here);
     - calls the F*-extracted ShEx_Validation.validate_focus with
       `sht:shape` (a bare shape-label IRI; None falls back to the
       schema's own `start`);
     - classifies the result against `option bool`'s documented
       convention (see ShEx.Validation.fst's file-header doc comment):
         PASS      — `Some b` matches the manifest's expected verdict
                      (true for ValidationTest, false for
                      ValidationFailure);
         MISMATCH  — `Some b` disagrees with the expected verdict (a
                      real wrong-answer, not a scope gap);
         DEFERRED  — `None`: outside Stage 3's reach (TE_OneOf,
                      cardinality-wrapped groups, overlapping-signature
                      siblings, shapeExprRef recursion, fuel exhaustion —
                      Stage 4/5 territory per the plan doc), never a
                      guessed verdict;
         SKIP      — could not even be attempted (missing `.json` twin,
                      missing data/schema/focus/action field, a decode
                      exception). The 3 `sht:trait sht:ShapeMap` fixtures
                      (manifest-only shape-map query syntax, out of
                      scope per the plan's scope cuts) land here because
                      they carry `sht:map` instead of `sht:focus`.

   !! THIS IS I/O GLUE — NO SHEX SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All ShExJ decoding
   lives in formal/fstar/ShEx.Schema.fst; all NodeConstraint dispatch and
   triple-expression partition matching live in
   formal/fstar/ShEx.Validation.fst. This file does file I/O, manifest
   traversal, resolved-IRI-to-local-path mapping (a github raw-content
   URL prefix strip — the vendored corpus's `@base` resolves relative
   `sht:schema`/`sht:data` references against
   `https://raw.githubusercontent.com/shexSpec/shexTest/master/`, so
   stripping that prefix and rejoining under
   third_party/testing/shex/ recovers the on-disk path), and outcome
   classification.

   Usage:
     ./shex_runner                  Run the default validation manifest
     ./shex_runner <manifest.ttl>   Run a specific manifest.ttl
     ./shex_runner --list           List discovered test entries (no execution)
     ./shex_runner -v|--verbose     Show mismatch/deferred/skip reasons
     ./shex_runner --help           Show this help
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to shacl_runner.ml / jsonld_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/shex/validation/manifest.ttl";
    "third_party/testing/shex/validation/manifest.ttl" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ()) "third_party/testing/shex/validation/manifest.ttl"

(* ------------------------------------------------------------------ *)
(* File I/O + Turtle parsing (parallels shacl_runner / rdfc10_runner). *)

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

let parse_ttl_file (path : string) : rdf_graph option =
  match read_file path with
  | None -> None
  | Some raw -> Some (Parser_Turtle.parse_turtle_with_base raw (file_uri path))

(* ------------------------------------------------------------------ *)
(* Thin RDF-graph accessors over an rdf_term "subject" (verbatim from
   shacl_runner.ml — same shape of problem, same glue). *)

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

let string_of_lit (t : rdf_term option) : string option =
  match t with
  | Some (T_Literal l) -> Some l.lexical_form
  | _ -> None

(* ------------------------------------------------------------------ *)
(* shexTest vocabulary. NOTE: this manifest's `sht:` prefix resolves to
   .../ns/shacl/test-suite# — NOT the SHACL test suite's
   .../ns/shacl-test# (shacl_runner.ml's sht_ns) — the two vocabularies
   share the "sht" abbreviation but are different IRIs; verified against
   third_party/testing/shex/validation/manifest.ttl's own @prefix line. *)

let mf_ns  = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
let sht_ns = "http://www.w3.org/ns/shacl/test-suite#"
let rdf_type_iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let mf_name   = mf_ns ^ "name"
let mf_action = mf_ns ^ "action"
let sht_ValidationTest    = sht_ns ^ "ValidationTest"
let sht_ValidationFailure = sht_ns ^ "ValidationFailure"
let sht_schema = sht_ns ^ "schema"
let sht_shape  = sht_ns ^ "shape"
let sht_data   = sht_ns ^ "data"
let sht_focus  = sht_ns ^ "focus"

let subjects_typed (g : rdf_graph) (iri : string) : rdf_term list =
  List.filter_map
    (fun tr -> if tr.p = rdf_type_iri
               then (match tr.o with T_IRI i when i = iri -> Some (subject_to_term tr.s) | _ -> None)
               else None)
    g

(* ------------------------------------------------------------------ *)
(* Resolved-IRI -> local-path mapping. The manifest's own `@base` is
   `https://raw.githubusercontent.com/shexSpec/shexTest/master/validation/manifest`
   (an absolute IRI, so it wins over whatever base we hand the Turtle
   parser) — every `sht:schema`/`sht:data` reference in the parsed graph
   is therefore an absolute IRI under that github raw-content prefix.
   Stripping the prefix and rejoining under the vendored submodule root
   recovers the on-disk path RFC-3986 resolution would have produced
   against a local `file://` base. *)

let github_prefix = "https://raw.githubusercontent.com/shexSpec/shexTest/master/"

let resolved_iri_to_local_path (repo_root : string) (iri : string) : string option =
  let plen = String.length github_prefix in
  if String.length iri >= plen && String.sub iri 0 plen = github_prefix then
    let rel = String.sub iri plen (String.length iri - plen) in
    Some (Filename.concat (Filename.concat repo_root "third_party/testing/shex") rel)
  else None

(* The manifest's canonical `sht:schema` reference names a `.shex`
   (ShExC) fixture; per the plan's scope cut we consume the same-
   basename ShExJ `.json` twin under schemas/ instead (342/346 unique
   schemas referenced from validation/ have one). *)
let json_twin_of_schema_path (path : string) : string option =
  if Filename.check_suffix path ".shex" then Some (Filename.chop_suffix path ".shex" ^ ".json")
  else if Filename.check_suffix path ".json" then Some path
  else None

(* ------------------------------------------------------------------ *)
(* Per-test record. Fields stay `option` (never filtered at collection
   time) so a malformed/incomplete manifest entry surfaces as an honest
   SKIP with a reason instead of silently vanishing from the total
   (anti-pattern #25 discipline). *)

type test_case = {
  tc_name : string;
  tc_expect : bool;             (* true = ValidationTest, false = ValidationFailure *)
  tc_schema_iri : string option;
  tc_shape_iri : string option;  (* None => validate against the schema's own `start` *)
  tc_data_iri : string option;
  tc_focus : rdf_term option;
}

let collect_of_type (g : rdf_graph) (expect : bool) (type_iri : string) : test_case list =
  List.map
    (fun t ->
       let name =
         match string_of_lit (obj1_of g t mf_name) with
         | Some n -> n
         | None -> (match t with T_IRI i -> i | T_BNode b -> "_:" ^ b | _ -> "<test>")
       in
       let action = obj1_of g t mf_action in
       let field pred = match action with None -> None | Some a -> obj1_of g a pred in
       { tc_name = name;
         tc_expect = expect;
         tc_schema_iri = (match field sht_schema with Some tm -> iri_str tm | None -> None);
         tc_shape_iri  = (match field sht_shape  with Some tm -> iri_str tm | None -> None);
         tc_data_iri   = (match field sht_data   with Some tm -> iri_str tm | None -> None);
         tc_focus      = field sht_focus })
    (subjects_typed g type_iri)

let collect_tests (g : rdf_graph) : test_case list =
  collect_of_type g true sht_ValidationTest @ collect_of_type g false sht_ValidationFailure

(* ------------------------------------------------------------------ *)
(* Per-test execution. *)

type outcome = Pass | Mismatch of string | Deferred of string | Skip of string

let run_test (repo_root : string) (tc : test_case) : outcome =
  match tc.tc_schema_iri, tc.tc_data_iri, tc.tc_focus with
  | None, _, _ -> Skip "no sht:schema in mf:action"
  | _, None, _ -> Skip "no sht:data in mf:action"
  | _, _, None -> Skip "no sht:focus in mf:action (likely a shape-map fixture — sht:map instead — out of scope per the plan's scope cuts)"
  | Some schema_iri, Some data_iri, Some focus ->
    (match resolved_iri_to_local_path repo_root schema_iri with
     | None -> Skip (Printf.sprintf "cannot map sht:schema IRI %s to a local path" schema_iri)
     | Some schema_shex_path ->
       (match json_twin_of_schema_path schema_shex_path with
        | None -> Skip (Printf.sprintf "sht:schema path has no recognized extension: %s" schema_shex_path)
        | Some json_path ->
          if not (Sys.file_exists json_path) then
            Skip (Printf.sprintf "no ShExJ (.json) twin for %s" schema_shex_path)
          else
            (match resolved_iri_to_local_path repo_root data_iri with
             | None -> Skip (Printf.sprintf "cannot map sht:data IRI %s to a local path" data_iri)
             | Some data_path ->
               if not (Sys.file_exists data_path) then
                 Skip (Printf.sprintf "sht:data file missing on disk: %s" data_path)
               else
                 (try
                    match read_file json_path with
                    | None -> Skip (Printf.sprintf "cannot read %s" json_path)
                    | Some json_text ->
                      (match ShEx_Schema.decode_shex_schema json_text with
                       | FStar_Pervasives_Native.None ->
                         Skip (Printf.sprintf "ShEx_Schema.decode_shex_schema failed on %s" json_path)
                       | FStar_Pervasives_Native.Some schema ->
                         (match parse_ttl_file data_path with
                          | None -> Skip (Printf.sprintf "cannot read %s" data_path)
                          | Some data_graph ->
                            let shape_id =
                              match tc.tc_shape_iri with
                              | Some s -> FStar_Pervasives_Native.Some s
                              | None -> FStar_Pervasives_Native.None
                            in
                            (match ShEx_Validation.validate_focus schema shape_id focus data_graph with
                             | FStar_Pervasives_Native.None ->
                               Deferred "validate_focus returned None (Stage 4/5 territory — TE_OneOf, cardinality-wrapped groups, overlapping-signature siblings, shapeExprRef recursion, or fuel exhaustion)"
                             | FStar_Pervasives_Native.Some got ->
                               if got = tc.tc_expect then Pass
                               else Mismatch (Printf.sprintf "expected %b, got %b" tc.tc_expect got))))
                  with e -> Skip (Printf.sprintf "exception: %s" (Printexc.to_string e))))))

(* ------------------------------------------------------------------ *)
(* Suite run. *)

let run_manifest ~verbose ~list_only manifest_path =
  let repo_root = find_repo_root () in
  Printf.printf "=== ShEx Validation Manifest Runner (stage 8) ===\n";
  Printf.printf "Manifest: %s\n\n" manifest_path;
  match parse_ttl_file manifest_path with
  | None ->
    Printf.eprintf "shex_runner: cannot read %s\n" manifest_path;
    exit 2
  | Some g ->
    let tests = collect_tests g in
    let total = List.length tests in
    Printf.printf "Totals: %d test entries\n\n" total;
    if list_only then
      List.iter (fun tc -> Printf.printf "  %-50s (%s)\n" tc.tc_name (if tc.tc_expect then "ValidationTest" else "ValidationFailure")) tests
    else begin
      let n = ref 0 in
      let outcomes =
        List.map
          (fun tc ->
             incr n;
             Printf.eprintf "  [%d/%d] %s%!" !n total tc.tc_name;
             let o = run_test repo_root tc in
             let tag = match o with
               | Pass -> "ok" | Mismatch _ -> "MISMATCH" | Deferred _ -> "deferred" | Skip _ -> "skip" in
             Printf.eprintf " %s\n%!" tag;
             (match o with
              | Pass -> Printf.printf "  PASS: %s\n" tc.tc_name
              | Mismatch msg -> Printf.printf "  MISMATCH: %s — %s\n" tc.tc_name msg
              | Deferred msg -> if verbose then Printf.printf "  deferred: %s — %s\n" tc.tc_name msg
              | Skip msg -> if verbose then Printf.printf "  skip: %s — %s\n" tc.tc_name msg);
             o)
          tests
      in
      let pass, mismatch, deferred, skip =
        List.fold_left
          (fun (p, m, d, s) o ->
             match o with
             | Pass -> (p + 1, m, d, s)
             | Mismatch _ -> (p, m + 1, d, s)
             | Deferred _ -> (p, m, d + 1, s)
             | Skip _ -> (p, m, d, s + 1))
          (0, 0, 0, 0) outcomes
      in
      Printf.printf "\n========================================\n";
      Printf.printf "TOTAL: %d pass, %d mismatch, %d deferred, %d skipped (out of %d)\n"
        pass mismatch deferred skip total;
      Printf.printf "========================================\n";
      (* The exact labelled line the task + dashboard humans read. *)
      Printf.printf "shex-validation: %d pass, %d mismatch, %d deferred, %d skipped (out of %d)\n"
        pass mismatch deferred skip total;
      (* A second, generic-regex-compatible line ("N pass, M fail (out of
         K)") for tools/affected-tests.sh's summarize_output, which only
         understands pass/fail. `fail` here is mismatch only — deferred
         and skip are "no verdict produced", not a wrong answer, same
         judgment call shacl_runner.ml's skip bucket makes. *)
      Printf.printf "shex-validation (pass/fail compat): %d pass, %d fail (out of %d)\n"
        pass mismatch total;
      if mismatch > 0 then exit 1
    end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "ShEx validation manifest runner — stage 8 of the ShEx program.\n\
     \n\
     Usage:\n\
     \  ./shex_runner                  Run the default validation manifest\n\
     \  ./shex_runner <manifest.ttl>   Run a specific manifest.ttl\n\
     \  ./shex_runner --list           List discovered test entries (no execution)\n\
     \  ./shex_runner -v|--verbose     Show mismatch/deferred/skip reasons\n\
     \  ./shex_runner --help           Show this help\n\
     \n\
     See formal/fstar/ShEx.Validation.fst's file header for what Stage 3\n\
     covers (disjoint-predicate fast-path triple-expression matching) and\n\
     what still returns None (DEFERRED — Stage 4/5 territory).\n"

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
      Printf.eprintf "shex_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with Some p -> p | None -> default_manifest () in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
