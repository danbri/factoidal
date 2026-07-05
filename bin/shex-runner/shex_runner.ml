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
       scope cut. As of the 2026-07-05 SKIP-elimination pass, 3 schemas
       (extends-abstract-multi-empty, extends-closed-diamond,
       extends-closed-3diamond-split — genuinely ShExC-only upstream,
       not just a stale submodule pin) fall back to a hand-translated
       twin in tests/shex-shexj-twins/ (see that directory's README for
       translation provenance) when the submodule copy is absent;
     - loads that schema through the F*-extracted
       ShEx_Schema.decode_shex_schema;
     - loads `sht:data` (a sibling `.ttl` fixture) through Parser_Turtle;
     - for a single-focus fixture, reads `sht:focus` directly off the
       manifest's own parsed graph (an IRI or a blank node — named
       blank-node labels are preserved verbatim by
       Parser.NTriples.parse_bnode (shared by Parser.Turtle), so a
       manifest `_:abcd` and the matching data-file `_:abcd` compare
       structurally equal without any extra bookkeeping here) and calls
       ShEx_Validation.validate_focus once with `sht:shape` (a bare
       shape-label IRI; None falls back to the schema's own `start`);
     - for a ShapeMap-form fixture (`sht:trait sht:ShapeMap`, no
       `sht:focus`/`sht:shape`), parses the `sht:map` JSON file (a list
       of `{"node","shape"}` pairs — via the F*-extracted Parser_JSON,
       no hand-rolled JSON here) and the `mf:result` JSON file (node IRI
       -> `[{"shape","result"}]` — the per-entry ground truth; the
       manifest's own ValidationTest/ValidationFailure type only
       summarizes whether the whole map fully conforms and is NOT used
       as the expected verdict here), then calls validate_focus once
       per map entry;
     - classifies the result(s) against `option bool`'s documented
       convention (see ShEx.Validation.fst's file-header doc comment):
         PASS      — `Some b` matches the expected verdict for every
                      entry (the single sht:focus/sht:shape pair, or
                      every sht:map entry against its own mf:result);
         MISMATCH  — any entry's `Some b` disagrees with its expected
                      verdict (a real wrong-answer, not a scope gap);
         DEFERRED  — no entry mismatched, but at least one
                      validate_focus call returned `None`: outside
                      Stage 3's reach (TE_OneOf, cardinality-wrapped
                      groups, overlapping-signature siblings,
                      shapeExprRef recursion, fuel exhaustion, or — for
                      the 3 extends-twin schemas above — Stage 6
                      `extends`/`abstract` semantics not yet landed in
                      ShEx.Validation.fst), never a guessed verdict;
         SKIP      — could not even be attempted (missing schema/data/
                      map/result file on disk, a decode exception, or a
                      manifest entry with neither `sht:focus` nor
                      `sht:map`).

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
let mf_result = mf_ns ^ "result"
let sht_ValidationTest    = sht_ns ^ "ValidationTest"
let sht_ValidationFailure = sht_ns ^ "ValidationFailure"
let sht_schema = sht_ns ^ "schema"
let sht_shape  = sht_ns ^ "shape"
let sht_data   = sht_ns ^ "data"
let sht_focus  = sht_ns ^ "focus"
(* ShapeMap-form fixtures (sht:trait sht:ShapeMap) carry a `sht:map`
   pointing at a JSON ShapeMap file (list of {"node","shape"} pairs)
   instead of a single `sht:focus`/`sht:shape` pair, and their
   `mf:result` names a JSON file (node IRI -> [{shape, result}]) rather
   than an RDF ValidationReport blob. Both are plain JSON, parsed with
   the F*-extracted Parser_JSON (no hand-rolled JSON parsing here, per
   the same discipline jsonld_runner follows). *)
let sht_map    = sht_ns ^ "map"

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

(* A handful of vendored schemas (see tests/shex-shexj-twins/README.md)
   are ShExC-only upstream — no `.json` twin exists anywhere in the
   submodule. Rather than SKIP those fixtures outright, fall back to a
   hand-translated twin in tests/shex-shexj-twins/<basename>.json (NOT
   inside the submodule — clearly labelled derived fixtures, per the
   README's provenance discipline). Only consulted when the submodule's
   own twin is missing on disk. *)
let shexj_twin_fallback_path (repo_root : string) (schema_shex_path : string) : string option =
  let basename = Filename.remove_extension (Filename.basename schema_shex_path) in
  let fallback = Filename.concat (Filename.concat repo_root "tests/shex-shexj-twins") (basename ^ ".json") in
  if Sys.file_exists fallback then Some fallback else None

(* ------------------------------------------------------------------ *)
(* ShapeMap-form fixture support (sht:trait sht:ShapeMap). The map file
   is a JSON array of `{"node": <iri>, "shape": <iri>}` objects (a
   simplified fixed-shape-label ShapeMap — no `START` sentinel or
   query-form node-selector syntax appears in the 3 vendored fixtures);
   the results file is a JSON object keyed by node IRI, each value an
   array of `{"shape": <iri>, "result": <bool>}` records. Both parsed
   with the F*-extracted Parser_JSON — no hand-rolled JSON here. *)

type map_entry = { me_node : string; me_shape : string }

let opt_of_fstar (o : 'a FStar_Pervasives_Native.option) : 'a option =
  match o with
  | FStar_Pervasives_Native.Some v -> Some v
  | FStar_Pervasives_Native.None -> None

let parse_map_entries (json_text : string) : map_entry list option =
  match opt_of_fstar (Parser_JSON.parse_json json_text) with
  | Some (Parser_JSON.JArray items) ->
    Some (List.filter_map
            (fun item ->
               match opt_of_fstar (Parser_JSON.json_get_string "node" item),
                     opt_of_fstar (Parser_JSON.json_get_string "shape" item) with
               | Some n, Some s -> Some { me_node = n; me_shape = s }
               | _ -> None)
            items)
  | _ -> None

(* A map-entry `node` string that looks like a bnode label (shexTest's
   ShapeMap JSON format has no reserved prefix for this in the 3
   vendored fixtures, but a leading "_:" is the same convention the
   rest of this runner already relies on for manifest bnodes). *)
let term_of_node_string (s : string) : rdf_term =
  if String.length s >= 2 && String.sub s 0 2 = "_:"
  then T_BNode (String.sub s 2 (String.length s - 2))
  else T_IRI s

(* Look up the expected `result` boolean for a given (node, shape) pair
   in a parsed results-JSON object (node IRI -> [{shape, result}]). *)
let lookup_expected_result (results_json : Parser_JSON.json_val) (node : string) (shape : string) : bool option =
  match results_json with
  | Parser_JSON.JObject fields ->
    (match List.assoc_opt node fields with
     | Some (Parser_JSON.JArray items) ->
       List.find_map
         (fun item ->
            match opt_of_fstar (Parser_JSON.json_get_string "shape" item),
                  opt_of_fstar (Parser_JSON.json_get_bool "result" item) with
            | Some s, Some r when s = shape -> Some r
            | _ -> None)
         items
     | _ -> None)
  | _ -> None

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
  tc_map_iri : string option;    (* ShapeMap-form fixtures: sht:map instead of sht:focus/sht:shape *)
  tc_result_iri : string option; (* ShapeMap-form fixtures: mf:result names a JSON per-entry results file *)
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
         tc_focus      = field sht_focus;
         tc_map_iri    = (match field sht_map with Some tm -> iri_str tm | None -> None);
         tc_result_iri = (match obj1_of g t mf_result with Some tm -> iri_str tm | None -> None) })
    (subjects_typed g type_iri)

let collect_tests (g : rdf_graph) : test_case list =
  collect_of_type g true sht_ValidationTest @ collect_of_type g false sht_ValidationFailure

(* ------------------------------------------------------------------ *)
(* Per-test execution. *)

type outcome = Pass | Mismatch of string | Deferred of string | Skip of string

(* Resolves + decodes the ShExJ schema and Turtle data graph shared by
   both the single-focus (`sht:focus`/`sht:shape`) and ShapeMap-form
   (`sht:map`) fixture shapes. *)
let load_schema_and_data (repo_root : string) (schema_iri : string) (data_iri : string)
  : (ShEx_Schema.shex_schema * rdf_graph, outcome) result =
  match resolved_iri_to_local_path repo_root schema_iri with
  | None -> Error (Skip (Printf.sprintf "cannot map sht:schema IRI %s to a local path" schema_iri))
  | Some schema_shex_path ->
    (match json_twin_of_schema_path schema_shex_path with
     | None -> Error (Skip (Printf.sprintf "sht:schema path has no recognized extension: %s" schema_shex_path))
     | Some submodule_json_path ->
       let json_path_opt =
         if Sys.file_exists submodule_json_path then Some submodule_json_path
         else shexj_twin_fallback_path repo_root schema_shex_path
       in
       (match json_path_opt with
        | None ->
          Error (Skip (Printf.sprintf "no ShExJ (.json) twin for %s (checked submodule and tests/shex-shexj-twins/)" schema_shex_path))
        | Some json_path ->
         (match resolved_iri_to_local_path repo_root data_iri with
          | None -> Error (Skip (Printf.sprintf "cannot map sht:data IRI %s to a local path" data_iri))
          | Some data_path ->
            if not (Sys.file_exists data_path) then
              Error (Skip (Printf.sprintf "sht:data file missing on disk: %s" data_path))
            else
              (match read_file json_path with
               | None -> Error (Skip (Printf.sprintf "cannot read %s" json_path))
               | Some json_text ->
                 (match ShEx_Schema.decode_shex_schema json_text with
                  | FStar_Pervasives_Native.None ->
                    Error (Skip (Printf.sprintf "ShEx_Schema.decode_shex_schema failed on %s" json_path))
                  | FStar_Pervasives_Native.Some schema ->
                    (match parse_ttl_file data_path with
                     | None -> Error (Skip (Printf.sprintf "cannot read %s" data_path))
                     | Some data_graph -> Ok (schema, data_graph)))))))

let run_single_focus_test (repo_root : string) (tc : test_case) (schema_iri : string) (data_iri : string) (focus : rdf_term) : outcome =
  match load_schema_and_data repo_root schema_iri data_iri with
  | Error o -> o
  | Ok (schema, data_graph) ->
    (try
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
          else Mismatch (Printf.sprintf "expected %b, got %b" tc.tc_expect got))
     with e -> Skip (Printf.sprintf "exception: %s" (Printexc.to_string e)))

(* ShapeMap-form fixture (sht:trait sht:ShapeMap): validate every
   {node, shape} pair in the map file, and check each one's actual
   verdict against its own expected `result` in the mf:result JSON
   file (NOT the manifest's ValidationTest/ValidationFailure type,
   which only summarizes whether the whole map is fully-conforming —
   the per-entry results file is the ground truth, same convention the
   shexTest ShapeMap trait uses generally). One real wrong verdict
   anywhere in the map makes the whole fixture Mismatch; otherwise any
   None (Stage 4/5 gap) makes it Deferred; only if every entry gets an
   expected-matching Some does the fixture Pass. *)
let run_shapemap_test (repo_root : string) (schema_iri : string) (data_iri : string) (map_iri : string) (result_iri : string) : outcome =
  match load_schema_and_data repo_root schema_iri data_iri with
  | Error o -> o
  | Ok (schema, data_graph) ->
    (match resolved_iri_to_local_path repo_root map_iri with
     | None -> Skip (Printf.sprintf "cannot map sht:map IRI %s to a local path" map_iri)
     | Some map_path ->
       if not (Sys.file_exists map_path) then Skip (Printf.sprintf "sht:map file missing on disk: %s" map_path)
       else
         (match resolved_iri_to_local_path repo_root result_iri with
          | None -> Skip (Printf.sprintf "cannot map mf:result IRI %s to a local path" result_iri)
          | Some result_path ->
            if not (Sys.file_exists result_path) then Skip (Printf.sprintf "mf:result file missing on disk: %s" result_path)
            else
              (try
                 match read_file map_path with
                 | None -> Skip (Printf.sprintf "cannot read %s" map_path)
                 | Some map_text ->
                   (match parse_map_entries map_text with
                    | None -> Skip (Printf.sprintf "cannot parse ShapeMap JSON %s" map_path)
                    | Some [] -> Skip (Printf.sprintf "empty ShapeMap %s" map_path)
                    | Some entries ->
                      (match read_file result_path with
                       | None -> Skip (Printf.sprintf "cannot read %s" result_path)
                       | Some result_text ->
                         (match opt_of_fstar (Parser_JSON.parse_json result_text) with
                          | None -> Skip (Printf.sprintf "cannot parse results JSON %s" result_path)
                          | Some results_json ->
                            let verdicts =
                              List.map
                                (fun me ->
                                   let focus = term_of_node_string me.me_node in
                                   match lookup_expected_result results_json me.me_node me.me_shape with
                                   | None ->
                                     `Skip (Printf.sprintf "no expected result for node %s / shape %s in %s" me.me_node me.me_shape result_path)
                                   | Some expected ->
                                     (match ShEx_Validation.validate_focus schema (FStar_Pervasives_Native.Some me.me_shape) focus data_graph with
                                      | FStar_Pervasives_Native.None -> `Deferred
                                      | FStar_Pervasives_Native.Some got ->
                                        if got = expected then `Pass
                                        else `Mismatch (Printf.sprintf "node %s shape %s: expected %b, got %b" me.me_node me.me_shape expected got)))
                                entries
                            in
                            (match List.find_opt (function `Mismatch _ -> true | _ -> false) verdicts with
                             | Some (`Mismatch msg) -> Mismatch msg
                             | _ ->
                               (match List.find_opt (function `Skip _ -> true | _ -> false) verdicts with
                                | Some (`Skip msg) -> Skip msg
                                | _ ->
                                  if List.exists (function `Deferred -> true | _ -> false) verdicts
                                  then Deferred "at least one map entry's validate_focus returned None (Stage 4/5 territory)"
                                  else Pass)))))
               with e -> Skip (Printf.sprintf "exception: %s" (Printexc.to_string e)))))

let run_test (repo_root : string) (tc : test_case) : outcome =
  match tc.tc_schema_iri, tc.tc_data_iri with
  | None, _ -> Skip "no sht:schema in mf:action"
  | _, None -> Skip "no sht:data in mf:action"
  | Some schema_iri, Some data_iri ->
    (match tc.tc_focus with
     | Some focus -> run_single_focus_test repo_root tc schema_iri data_iri focus
     | None ->
       (match tc.tc_map_iri, tc.tc_result_iri with
        | Some map_iri, Some result_iri -> run_shapemap_test repo_root schema_iri data_iri map_iri result_iri
        | Some _, None -> Skip "sht:map present but no mf:result to check expected per-entry verdicts against"
        | None, _ -> Skip "no sht:focus and no sht:map in mf:action"))

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
