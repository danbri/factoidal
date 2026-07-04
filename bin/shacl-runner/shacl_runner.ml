(* SHACL Core W3C test-suite runner — Phase 3 (issue #181 follow-up).

   Walks the vendored W3C data-shapes-test-suite manifest hierarchy
   (third_party/testing/shacl/data-shapes-test-suite/tests/core/ by
   default, or tests/sparql/ for the SPARQL-based-constraints suite),
   following `mf:include` (a repeated triple, not an RDF list, in this
   suite — see core/node/manifest.ttl for the pattern) down to leaf
   test files, each of which declares one or more `sht:Validate`
   entries directly. For each entry:
     - loads the dataGraph / shapesGraph (usually the SAME document,
       self-referenced via `<>`; a few tests split into sibling
       `*-data.ttl` / `*-shapes.ttl` files, resolved by relative IRI);
     - parses the shapes graph via the F*-extracted
       SHACL_Validation.parse_shape_from_graph;
     - runs SHACL_Validation.validate against the data graph;
     - by DEFAULT (Phase 3), compares the FULL validation report
       against the manifest's expected report, per the suite's own
       "full compliance" isomorphism rule (data-shapes-test-suite/
       index.html, "Submitting Implementation Reports"): canonicalize
       both the `expected` graph (built here from the manifest's own
       `mf:result` blob — R's own triples, each `sh:result` value's
       own triples, and any `sh:resultPath` blank-node structure) and
       the `actual` graph (SHACL_Validation.validation_report_to_graph,
       filtered per the suite's sh:resultMessage carve-out below) via
       RDF_Canonical.canonicalize_to_nquads and compare the resulting
       strings.
     - a manifest entry whose `mf:result` is the bare IRI `sht:Failure`
       (used by the SPARQL suite's `unsupported-sparql-*`/
       `pre-binding-006` fixtures for queries this engine is not
       expected to support, e.g. SERVICE/MINUS/VALUES-block) PASSES
       iff `SHACL_Validation.validate` set `report_failure` (a SPARQL
       query that failed to parse), regardless of `conforms`.
     - `--conforms-only` reverts to the original slice-1 comparison
       (only the boolean `sh:conforms` flag) — the documented floor
       this must never regress below (98 of 98 on the core manifest).

   !! THIS IS I/O GLUE — NO SHACL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All shape parsing,
   target computation, path evaluation, constraint evaluation, and
   report serialization live in formal/fstar/SHACL.Validation.fst.
   This file does file I/O, manifest traversal, a bounded graph
   "describe" closure to build the expected-comparison sub-graph (pure
   reachability walk over already-parsed triples, not SHACL
   semantics — the consumer-tool carve-out CLAUDE.md rule #11
   explicitly allows), and delegates the actual isomorphism check to
   RDF_Canonical (also F*-extracted).

   Usage:
     ./shacl_runner                  Run the default core manifest (report-compare)
     ./shacl_runner <manifest.ttl>   Run a specific manifest.ttl
     ./shacl_runner --conforms-only  Compare only sh:conforms (slice-1 floor)
     ./shacl_runner --list           List discovered test entries (no execution)
     ./shacl_runner -v|--verbose     Show skip reasons + report diffs on FAIL
     ./shacl_runner --help           Show this help
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to jsonld_runner.ml / rdfc10_runner.ml). *)

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
  [ Filename.concat repo_root
      "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl";
    "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl" ]

let default_manifest () =
  try List.find Sys.file_exists (manifest_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ())
      "third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl"

(* ------------------------------------------------------------------ *)
(* File I/O + Turtle parsing (base-IRI handling parallels rdfc10_runner). *)

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

(* Inverse of file_uri, for resolving a dataGraph/shapesGraph IRI that
   points at a sibling file back to a loadable path. *)
let path_of_file_iri (iri : string) : string option =
  let prefix = "file://" in
  let plen = String.length prefix in
  if String.length iri >= plen && String.sub iri 0 plen = prefix
  then Some (String.sub iri plen (String.length iri - plen))
  else None

let parse_ttl_file (path : string) : (rdf_graph * string) option =
  match read_file path with
  | None -> None
  | Some raw ->
    let base = file_uri path in
    Some (Parser_Turtle.parse_turtle_with_base raw base, base)

(* ------------------------------------------------------------------ *)
(* Thin RDF-graph accessors over an rdf_term "subject". *)

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

let bool_of_lit (t : rdf_term option) : bool option =
  match t with
  | Some (T_Literal l) -> Some (l.lexical_form = "true" || l.lexical_form = "1")
  | _ -> None

let string_of_lit (t : rdf_term option) : string option =
  match t with
  | Some (T_Literal l) -> Some l.lexical_form
  | _ -> None

(* ------------------------------------------------------------------ *)
(* SHACL test vocabulary. *)

let mf_ns  = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
let sht_ns = "http://www.w3.org/ns/shacl-test#"
let sh_ns  = "http://www.w3.org/ns/shacl#"
let rdf_type_iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let mf_include = mf_ns ^ "include"
let mf_action  = mf_ns ^ "action"
let mf_result  = mf_ns ^ "result"
let mf_name    = mf_ns ^ "name"
(* This suite labels tests with rdfs:label, not mf:name (see any
   core/*.ttl fixture) — try both, mf:name first per the manifest
   vocabulary's own spec. *)
let rdfs_label = "http://www.w3.org/2000/01/rdf-schema#label"
let sht_Validate    = sht_ns ^ "Validate"
let sht_dataGraph   = sht_ns ^ "dataGraph"
let sht_shapesGraph = sht_ns ^ "shapesGraph"
let sh_conforms     = sh_ns ^ "conforms"
let sht_Failure     = sht_ns ^ "Failure"
let sh_result       = sh_ns ^ "result"
let sh_resultPath   = sh_ns ^ "resultPath"
let sh_resultMessage = sh_ns ^ "resultMessage"

(* ------------------------------------------------------------------ *)
(* Phase 3 (issue #181 follow-up): full report comparison.

   Per the suite's own "full compliance" rule (data-shapes-test-suite/
   index.html): `expected` = R's own triples, plus each value of R's
   sh:result as subject, plus "any triples needed to correctly
   represent the sh:resultPath" (a bounded blank-node-only walk, since
   resultPath structures are RDF lists / sh:inversePath-style wrapper
   bnodes — never a walk into unrelated data-graph triples about a
   focusNode/value IRI that happens to also appear elsewhere in the
   manifest document). This is a plain reachability walk over an
   already-parsed graph — I/O/comparison glue, not SHACL semantics
   (CLAUDE.md rule #11's consumer-tool carve-out). *)

let triples_with_subject (g : rdf_graph) (t : rdf_term) : triple list =
  match term_to_subj_opt t with
  | None -> []
  | Some s -> List.filter (fun (tr : triple) -> subject_eq tr.s s) g

let rec bnode_path_closure (g : rdf_graph) (frontier : rdf_term list) (acc : triple list) (fuel : int)
  : triple list =
  if fuel <= 0 then acc
  else
    match frontier with
    | [] -> acc
    | t :: rest ->
      (match t with
       | T_BNode _ ->
         let ts = triples_with_subject g t in
         let objs = List.map (fun (tr : triple) -> tr.o) ts in
         bnode_path_closure g (rest @ objs) (acc @ ts) (fuel - 1)
       | _ -> bnode_path_closure g rest acc (fuel - 1))

let expected_report_graph (g : rdf_graph) (res_term : rdf_term) : rdf_graph =
  let r_triples = triples_with_subject g res_term in
  let result_values = objs_of g res_term sh_result in
  let result_triples = List.concat_map (fun rv -> triples_with_subject g rv) result_values in
  let path_objs = List.concat_map (fun rv -> objs_of g rv sh_resultPath) result_values in
  let path_triples = bnode_path_closure g path_objs [] 50 in
  r_triples @ result_triples @ path_triples

(* The suite's sh:resultMessage carve-out: drop every actual
   sh:resultMessage triple whose literal object does not ALSO appear
   as a sh:resultMessage object somewhere in `expected` — this is the
   ONE predicate the comparison treats asymmetrically (see the
   section-13 doc comment in SHACL.Validation.fst / the suite's own
   text: "As a general rule, all triples with sh:resultMessage as
   subject need to be removed from the actual graph, except those
   with object ?object for which the expected graph contains a triple
   ?any sh:resultMessage ?object."). *)
let filter_result_messages (expected : rdf_graph) (actual : rdf_graph) : rdf_graph =
  let expected_messages =
    List.filter_map
      (fun (tr : triple) ->
         if tr.p = sh_resultMessage then
           (match tr.o with T_Literal l -> Some l.lexical_form | _ -> None)
         else None)
      expected
  in
  List.filter
    (fun (tr : triple) ->
       if tr.p = sh_resultMessage then
         (match tr.o with
          | T_Literal l -> List.mem l.lexical_form expected_messages
          | _ -> false)
       else true)
    actual

let canon_graph (g : rdf_graph) : string =
  RDF_Canonical.canonicalize_to_nquads { ds_default = g; ds_named = [] }

(* ------------------------------------------------------------------ *)
(* Per-test record. Fields stay `option` rather than being filtered
   out at collection time, so a malformed/incomplete manifest entry
   surfaces as an honest SKIP with a reason instead of silently
   vanishing from the total (anti-pattern #25 discipline). *)

type test_case = {
  tc_name : string;
  tc_file : string;
  tc_data_graph : rdf_graph option;
  tc_shapes_graph : rdf_graph option;
  tc_expect_conforms : bool option;
  (* Phase 3: None when mf:result isn't a full report blob (or is
     sht:Failure — see tc_expect_failure) — the report-compare path
     SKIPs those rather than fabricating a comparison. *)
  tc_expect_report : rdf_graph option;
  (* True iff mf:result is the bare IRI sht:Failure (the SPARQL
     suite's convention for "this engine may legitimately fail on
     this query"). *)
  tc_expect_failure : bool;
}

(* Resolve a dataGraph/shapesGraph object to a parsed graph: reuse the
   current file's own graph when it self-references (`<>`, the
   overwhelmingly common case), else load the sibling file it names
   (e.g. path-complex-002-data.ttl / path-complex-002-shapes.ttl). *)
let resolve_graph_ref ~(own_graph : rdf_graph) ~(own_base : string) (t : rdf_term) : rdf_graph option =
  match iri_str t with
  | None -> None
  | Some iri ->
    if iri = own_base then Some own_graph
    else
      (match path_of_file_iri iri with
       | Some p ->
         (match parse_ttl_file p with
          | Some (g, _) -> Some g
          | None -> None)
       | None -> None)

let subjects_typed (g : rdf_graph) (iri : string) : rdf_term list =
  List.filter_map
    (fun tr -> if tr.p = rdf_type_iri
               then (match tr.o with T_IRI i when i = iri -> Some (subject_to_term tr.s) | _ -> None)
               else None)
    g

let rec collect_from_file (visited : string list ref) (path : string) : test_case list =
  let abs = abs_path path in
  if List.mem abs !visited then []
  else begin
    visited := abs :: !visited;
    match parse_ttl_file path with
    | None ->
      Printf.eprintf "shacl_runner: cannot read %s\n" path;
      []
    | Some (g, base) ->
      let root_term = T_IRI base in
      let included =
        List.concat_map
          (fun inc_term ->
             match iri_str inc_term with
             | None -> []
             | Some inc_iri ->
               (match path_of_file_iri inc_iri with
                | Some inc_path -> collect_from_file visited inc_path
                | None -> []))
          (objs_of g root_term mf_include)
      in
      let own_tests =
        List.map
          (fun t ->
             let name =
               match string_of_lit (obj1_of g t mf_name) with
               | Some n -> n
               | None ->
                 (match string_of_lit (obj1_of g t rdfs_label) with
                  | Some n -> n
                  | None -> (match t with T_IRI i -> i | T_BNode b -> "_:" ^ b | _ -> "<test>"))
             in
             let action = obj1_of g t mf_action in
             let result = obj1_of g t mf_result in
             let dgraph =
               match action with
               | None -> None
               | Some act ->
                 (match obj1_of g act sht_dataGraph with
                  | None -> None
                  | Some dgt -> resolve_graph_ref ~own_graph:g ~own_base:base dgt)
             in
             let sgraph =
               match action with
               | None -> None
               | Some act ->
                 (match obj1_of g act sht_shapesGraph with
                  | None -> None
                  | Some sgt -> resolve_graph_ref ~own_graph:g ~own_base:base sgt)
             in
             let expect =
               match result with
               | None -> None
               | Some res -> bool_of_lit (obj1_of g res sh_conforms)
             in
             let expect_failure =
               match result with
               | Some (T_IRI i) -> i = sht_Failure
               | _ -> false
             in
             let expect_report =
               if expect_failure then None
               else
                 match result with
                 | Some res when Option.is_some expect -> Some (expected_report_graph g res)
                 | _ -> None
             in
             { tc_name = name; tc_file = path;
               tc_data_graph = dgraph; tc_shapes_graph = sgraph;
               tc_expect_conforms = expect;
               tc_expect_report = expect_report;
               tc_expect_failure = expect_failure })
          (subjects_typed g sht_Validate)
      in
      included @ own_tests
  end

(* ------------------------------------------------------------------ *)
(* Per-test execution. *)

type outcome = Pass | Fail of string | Skip of string

(* Slice-1 floor: compare only sh:conforms. Kept as the `--conforms-only`
   fallback — CLAUDE.md's Phase 3 brief requires this mode to stay at
   98/98 on the core manifest even as the default (report-compare)
   mode is free to be stricter and score lower. *)
let run_test_conforms_only (tc : test_case) : outcome =
  match tc.tc_data_graph, tc.tc_shapes_graph, tc.tc_expect_conforms with
  | None, _, _ -> Skip "no dataGraph resolved from mf:action"
  | _, None, _ -> Skip "no shapesGraph resolved from mf:action"
  | _, _, None ->
    if tc.tc_expect_failure then Skip "mf:result is sht:Failure (conforms-only mode ignores it)"
    else Skip "mf:result has no sh:conforms boolean"
  | Some data, Some shapes_g, Some expect ->
    (try
       let sg = SHACL_Validation.parse_shape_from_graph shapes_g in
       let report = SHACL_Validation.validate data sg in
       let got = report.SHACL_Validation.conforms in
       if got = expect then Pass
       else Fail (Printf.sprintf "expected sh:conforms %b, got %b" expect got)
     with e -> Fail (Printf.sprintf "exception: %s" (Printexc.to_string e)))

(* Phase 3 default: full validation-report comparison (or sht:Failure
   acknowledgement) — see the file header + expected_report_graph doc
   comments for exactly what "full compliance" means here. *)
let run_test_report (tc : test_case) : outcome =
  match tc.tc_data_graph, tc.tc_shapes_graph with
  | None, _ -> Skip "no dataGraph resolved from mf:action"
  | _, None -> Skip "no shapesGraph resolved from mf:action"
  | Some data, Some shapes_g ->
    (try
       let sg = SHACL_Validation.parse_shape_from_graph shapes_g in
       let report = SHACL_Validation.validate data sg in
       if tc.tc_expect_failure then
         (match report.SHACL_Validation.report_failure with
          | Some _ -> Pass
          | None ->
            Fail (Printf.sprintf "expected sht:Failure (validation should not have completed); got sh:conforms %b"
                    report.SHACL_Validation.conforms))
       else
         (match tc.tc_expect_report with
          | None -> Skip "mf:result is not a full ValidationReport blob (no sh:conforms present)"
          | Some expected_g ->
            let actual_raw = SHACL_Validation.validation_report_to_graph report in
            let actual_g = filter_result_messages expected_g actual_raw in
            let exp_canon = canon_graph expected_g in
            let act_canon = canon_graph actual_g in
            if exp_canon = act_canon then Pass
            else
              Fail (Printf.sprintf
                      "report not isomorphic to expected\n    expected: %s\n    actual:   %s"
                      exp_canon act_canon))
     with e ->
       if tc.tc_expect_failure then Pass
       else Fail (Printf.sprintf "exception: %s" (Printexc.to_string e)))

(* ------------------------------------------------------------------ *)
(* Suite run. *)

let run_manifest ~verbose ~list_only ~conforms_only manifest_path =
  Printf.printf "=== SHACL W3C Test Runner (%s) ===\n"
    (if conforms_only then "sh:conforms-only" else "full report comparison");
  Printf.printf "Manifest: %s\n\n" manifest_path;
  let tests = collect_from_file (ref []) manifest_path in
  let total = List.length tests in
  Printf.printf "Totals: %d test entries\n\n" total;
  if list_only then
    List.iter (fun tc -> Printf.printf "  %-40s (%s)\n" tc.tc_name tc.tc_file) tests
  else begin
    let run_one = if conforms_only then run_test_conforms_only else run_test_report in
    let n = ref 0 in
    let outcomes =
      List.map
        (fun tc ->
           incr n;
           Printf.eprintf "  [%d/%d] %s%!" !n total tc.tc_name;
           let o = run_one tc in
           let tag = match o with Pass -> "ok" | Fail _ -> "FAIL" | Skip _ -> "skip" in
           Printf.eprintf " %s\n%!" tag;
           (match o with
            | Pass -> Printf.printf "  PASS: %s\n" tc.tc_name
            | Fail msg -> Printf.printf "  FAIL: %s (%s) — %s\n" tc.tc_name tc.tc_file msg
            | Skip msg -> if verbose then Printf.printf "  skip: %s (%s) — %s\n" tc.tc_name tc.tc_file msg);
           o)
        tests
    in
    let pass, fail, skip =
      List.fold_left
        (fun (p, f, s) o ->
           match o with
           | Pass -> (p + 1, f, s)
           | Fail _ -> (p, f + 1, s)
           | Skip _ -> (p, f, s + 1))
        (0, 0, 0) outcomes
    in
    Printf.printf "\n========================================\n";
    Printf.printf "TOTAL: %d pass, %d fail, %d skip (out of %d)\n" pass fail skip total;
    Printf.printf "========================================\n";
    (* Exact final-line format consumed by generate-report.sh's generic
       "N pass, M fail (out of K)" score-line regex — matches the
       jsonld_runner / rdfc10_runner convention. The label names the
       suite section (core vs sparql, derived from the manifest path)
       so the two .github/test-suites manifests get distinct lines. *)
    let section =
      let sub = "/sparql/" in
      let ls = String.length manifest_path and lb = String.length sub in
      let rec has i = i + lb <= ls && (String.sub manifest_path i lb = sub || has (i + 1)) in
      if has 0 then "shacl-sparql" else "shacl-core"
    in
    let label = if conforms_only then section ^ "-conforms-only" else section in
    Printf.printf "%s: %d pass, %d fail, %d skip (out of %d)\n" label pass fail skip total;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "SHACL W3C test-suite runner — Phase 3 (issue #181 follow-up).\n\
     \n\
     Usage:\n\
     \  ./shacl_runner                  Run the default core manifest (report-compare)\n\
     \  ./shacl_runner <manifest.ttl>   Run a specific manifest.ttl\n\
     \  ./shacl_runner --conforms-only  Compare only sh:conforms (slice-1 floor)\n\
     \  ./shacl_runner --list           List discovered test entries (no execution)\n\
     \  ./shacl_runner -v|--verbose     Show skip reasons + report diffs on FAIL\n\
     \  ./shacl_runner --help           Show this help\n\
     \n\
     Default mode canonicalizes the expected and actual validation-report\n\
     graphs (RDF.Canonical) and compares them per the suite's own \"full\n\
     compliance\" isomorphism rule; --conforms-only reverts to comparing\n\
     only the sh:conforms boolean. See formal/fstar/SHACL.Validation.fst\n\
     sections 11/13 for constraint coverage and sh:sparql dispatch scope.\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let list_only = ref false in
  let conforms_only = ref false in
  let path = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: rest -> list_only := true; loop rest
    | "--conforms-only" :: rest -> conforms_only := true; loop rest
    | p :: rest when !path = None -> path := Some p; loop rest
    | _ ->
      Printf.eprintf "shacl_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with Some p -> p | None -> default_manifest () in
  run_manifest ~verbose:!verbose ~list_only:!list_only ~conforms_only:!conforms_only manifest
