(* RML (RDF Mapping Language) test-suite runner — Stage 8 of the RML
   program (docs/designissues/2026-07-05-rml-program-plan.md).

   Reads a module's `metadata.csv` (rml-core primary, rml-io secondary),
   loads each test's `mapping.ttl` via the F*-extracted Turtle parser,
   decodes it with RML_Mapping.decode_mapping_document, resolves every
   triples map's logical-source rows (JSON via Parser_JSON +
   RML_Sources.json_iterate, CSV via RML_Sources.csv_iterate), evaluates
   both the non-join triples (RML_Eval.eval_triples_map) and the
   RefObjectMap/join triples (RML_Eval.eval_join_triples_map, Stage 5),
   and compares the resulting dataset against the expected `output1` .nq
   fixture via RDF_Canonical.canonicalize_to_nquads — the same
   isomorphism-insensitive-to-blank-node-labels comparison
   bin/jsonld-runner and the RML plan's Stage 2-3 scratch drivers used.

   error=true fixtures (metadata.csv's `error` column) PASS iff the
   generated dataset is empty — a data error means "no valid RDF term/
   iteration was produced," not an OCaml exception, per the RML-Core
   spec's term-generation rules (12.2).

   !! THIS IS I/O GLUE — NO RDF/RML SEMANTIC LOGIC !! Per CLAUDE.md iron
   rule #11 / anti-pattern #15: mapping-document decoding lives in
   formal/fstar/RML.Mapping.fst, logical-source iteration in
   formal/fstar/RML.Sources.fst, term-map/triples-map/join evaluation in
   formal/fstar/RML.Eval.fst. This file only does file I/O, metadata.csv
   traversal, join-lookup-table plumbing (an in-memory association list
   built from already-read files — not itself I/O), and N-Quads text
   comparison.

   Per iron rule #7, metadata.csv itself is tokenized with the
   F*-extracted RFC 4180 CSV scanner (RML_Sources.csv_parse_rows) rather
   than a hand-rolled OCaml CSV reader.

   Usage:
     ./rml_runner                Run rml-core (primary conformance target)
     ./rml_runner --io           Run rml-io's RMLSTC0* source tests too
                                 (secondary section; RMLTTC0* logical-
                                 target tests are SKIPped — out of scope,
                                 see the plan's Stage 9 note)
     ./rml_runner --filter P     Only run test IDs starting with P
     ./rml_runner --list         List parsed test entries (no execution)
     ./rml_runner -v|--verbose   Show expected-vs-got diff on FAIL
     ./rml_runner --help         Show this help
*)

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

let core_dir_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root "third_party/testing/rml-modules/rml-core/test-cases";
    "third_party/testing/rml-modules/rml-core/test-cases";
    "../../third_party/testing/rml-modules/rml-core/test-cases";
    "../../../third_party/testing/rml-modules/rml-core/test-cases" ]

let io_dir_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root "third_party/testing/rml-modules/rml-io/test-cases";
    "third_party/testing/rml-modules/rml-io/test-cases";
    "../../third_party/testing/rml-modules/rml-io/test-cases";
    "../../../third_party/testing/rml-modules/rml-io/test-cases" ]

let default_dir candidates =
  try List.find Sys.file_exists candidates
  with Not_found -> List.hd candidates

(* ------------------------------------------------------------------ *)
(* File I/O + FStar option interop. *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let fs_of_opt = function
  | Some x -> FStar_Pervasives_Native.Some x
  | None -> FStar_Pervasives_Native.None

let head s n =
  if String.length s <= n then s else String.sub s 0 n ^ " …(truncated)"

(* ------------------------------------------------------------------ *)
(* metadata.csv reading, via the F*-extracted RFC 4180 CSV tokenizer
   (rule #7 — no hand-rolled CSV parsing here). Header:
   ID,title,description,specification,base_iri,mapping,input_format1,
   input_format2,input_format3,output_format1,output_format2,
   output_format3,input1,input2,input3,output1,output2,output3,error *)

let csv_rows_of_file path =
  match read_file path with
  | None -> []
  | Some content -> RML_Sources.csv_parse_rows content

let col_index header name =
  let rec go i = function
    | [] -> None
    | h :: _ when h = name -> Some i
    | _ :: rest -> go (i + 1) rest
  in
  go 0 header

let get row idx =
  match idx with
  | None -> None
  | Some i -> (try Some (List.nth row i) with _ -> None)

type test_row = {
  tr_id : string;
  tr_title : string;
  tr_mapping : string;
  tr_output : string option;
  tr_error : bool;
  tr_base_iri : string option;
}

let load_metadata dir =
  match csv_rows_of_file (Filename.concat dir "metadata.csv") with
  | [] -> []
  | header :: rows ->
    let idx_id = col_index header "ID" in
    let idx_title = col_index header "title" in
    let idx_mapping = col_index header "mapping" in
    let idx_output1 = col_index header "output1" in
    let idx_error = col_index header "error" in
    let idx_base = col_index header "base_iri" in
    List.filter_map
      (fun row ->
         match get row idx_id with
         | None -> None
         | Some id ->
           let title = match get row idx_title with Some t -> t | None -> id in
           let mapping = match get row idx_mapping with Some m -> m | None -> "mapping.ttl" in
           let output = (match get row idx_output1 with Some "" -> None | o -> o) in
           let error = (match get row idx_error with Some "true" -> true | _ -> false) in
           let base_iri = (match get row idx_base with Some "" -> None | o -> o) in
           Some { tr_id = id; tr_title = title; tr_mapping = mapping;
                  tr_output = output; tr_error = error; tr_base_iri = base_iri })
      rows

(* ------------------------------------------------------------------ *)
(* N-Quads text sanitizing for comparison purposes only (Stage 8 driver
   fix, plan's open decision #6 / Stage 3's RMLTC0027b finding).

   rml:UnsafeIRI deliberately produces IRI-looking terms containing raw
   bytes N-Quads' IRIREF grammar forbids unescaped (RMLTC0027b's
   expected output.nq has a literal space inside
   "<http://example.com/Person/Emily Smith>"). The extracted
   Parser_NQuads.parse_nquads is a CORRECT, spec-conformant N-Quads
   parser — it is supposed to reject that byte inside an IRIREF, and
   changing it to tolerate the vendored fixture's deliberately-illegal
   text would weaken the parser used everywhere else. Fix the
   comparison instead: percent-encode any IRIREF-illegal byte (the
   RFC3987-excluded set, matching RML_Eval's own rml_forbidden_iri_byte
   scope) found literally inside `<...>`, applied identically to the
   raw expected .nq text (so it parses into all 3 triples instead of
   stopping at the first) and to both canonicalized N-Quads strings
   before the equality check (so an UnsafeIRI generated by this
   engine's own evaluation, which also carries the raw byte verbatim,
   compares equal to the now-encoded expected side). Idempotent: a
   byte already spelled "%20" is untouched (its constituent chars are
   all safe ASCII), so running it on both sides is harmless even when
   only one side needed it. Track quoted-string state so a literal '<'
   or '>' inside an N-Quads string literal is never mistaken for an
   IRIREF delimiter. *)
let sanitize_nquads_text (s : string) : string =
  let buf = Buffer.create (String.length s + 16) in
  let n = String.length s in
  let is_forbidden c =
    let b = Char.code c in
    b <= 0x20 || c = '<' || c = '"' || c = '{' || c = '}'
    || c = '|' || c = '\\' || c = '^' || c = '`'
  in
  let rec go i in_iri in_str =
    if i >= n then ()
    else
      let c = s.[i] in
      if in_str then begin
        Buffer.add_char buf c;
        if c = '\\' && i + 1 < n then begin
          Buffer.add_char buf s.[i + 1];
          go (i + 2) in_iri in_str
        end else
          go (i + 1) in_iri (if c = '"' then false else in_str)
      end else if in_iri then begin
        if c = '>' then begin Buffer.add_char buf c; go (i + 1) false false end
        else begin
          (if is_forbidden c then Buffer.add_string buf (Printf.sprintf "%%%02X" (Char.code c))
           else Buffer.add_char buf c);
          go (i + 1) true false
        end
      end else begin
        Buffer.add_char buf c;
        if c = '<' then go (i + 1) true false
        else if c = '"' then go (i + 1) false true
        else go (i + 1) false false
      end
  in
  go 0 false false;
  Buffer.contents buf

(* ------------------------------------------------------------------ *)
(* Logical-source row resolution (I/O + format dispatch only — the
   JSONPath/CSV iteration semantics are RML_Sources.json_iterate /
   csv_iterate). Returns [] for reference formulations this program
   doesn't implement yet (XPath/XML — Stage 4 of the plan, not built;
   SQL2008Table — deferred per the plan's Open Decision #4) or when the
   source file can't be read/parsed — an honest FAIL downstream via an
   empty row list, not a runner crash. *)

let read_source_path test_dir (ls : RML_Mapping.logical_source) =
  match opt_of_fs ls.RML_Mapping.ls_source_path with
  | None -> None
  | Some p -> Some (Filename.concat test_dir p)

let resolve_rows test_dir (ls : RML_Mapping.logical_source) : RML_Sources.source_row list =
  match read_source_path test_dir ls with
  | None -> []
  | Some path ->
    (match opt_of_fs ls.RML_Mapping.ls_reference_formulation with
     | Some RML_Mapping.RF_JSONPath ->
       (match read_file path with
        | None -> []
        | Some content ->
          (match opt_of_fs (Parser_JSON.parse_json content) with
           | None -> []
           | Some root ->
             let iterator = match opt_of_fs ls.RML_Mapping.ls_iterator with Some it -> it | None -> "$" in
             RML_Sources.json_iterate root iterator))
     | Some RML_Mapping.RF_CSV ->
       (match read_file path with
        | None -> []
        | Some content -> RML_Sources.csv_iterate content ls.RML_Mapping.ls_null_values)
     | _ -> [])

(* ------------------------------------------------------------------ *)
(* Whole-document evaluation: build the (triples-map-id -> rows) table
   once (needed for both a triples map's own iteration AND any other
   triples map's join lookup of it as a parent), then fold every
   triples map's non-join + join placed triples into one dataset. *)

let eval_document test_dir (default_base_iri : string option) (doc : RML_Mapping.mapping_document)
  : RDF_Graph_Executable.rdf_dataset =
  let table =
    List.filter_map
      (fun (tmap : RML_Mapping.triples_map) ->
         match opt_of_fs tmap.RML_Mapping.tm_logical_source with
         | None -> None
         | Some ls -> Some (tmap.RML_Mapping.tm_id, (tmap, resolve_rows test_dir ls)))
      doc.RML_Mapping.md_triples_maps
  in
  let lookup_parent (id : RML_Mapping.node_ref) =
    fs_of_opt (List.assoc_opt id table)
  in
  let fs_base_iri = fs_of_opt default_base_iri in
  let all_pts =
    List.concat_map
      (fun (tmap : RML_Mapping.triples_map) ->
         match List.assoc_opt tmap.RML_Mapping.tm_id table with
         | None -> []
         | Some (_, rows) ->
           let non_join = RML_Eval.eval_triples_map tmap rows fs_base_iri in
           let joins = RML_Eval.eval_join_triples_map tmap rows fs_base_iri lookup_parent in
           non_join @ joins)
      doc.RML_Mapping.md_triples_maps
  in
  RML_Eval.place_into_dataset RDF_Graph_Executable.empty_dataset all_pts

(* ------------------------------------------------------------------ *)
(* Per-test execution + outcome. *)

type outcome = Pass | Fail of string | Skip of string

let is_empty_dataset (ds : RDF_Graph_Executable.rdf_dataset) =
  ds.RDF_Graph_Executable.ds_default = [] && ds.RDF_Graph_Executable.ds_named = []

let run_test module_dir (tr : test_row) =
  let test_dir = Filename.concat module_dir tr.tr_id in
  let mapping_path = Filename.concat test_dir tr.tr_mapping in
  match read_file mapping_path with
  | None -> Fail (Printf.sprintf "mapping file not found: %s" mapping_path)
  | Some ttl ->
    let g = Parser_Turtle.parse_turtle ttl in
    let doc = RML_Mapping.decode_mapping_document g in
    let got_ds = eval_document test_dir tr.tr_base_iri doc in
    if tr.tr_error then
      (if is_empty_dataset got_ds then Pass
       else
         Fail (Printf.sprintf "expected empty dataset (error=true) but got:\n%s"
                 (head (RDF_Canonical.canonicalize_to_nquads got_ds) 400)))
    else
      (match tr.tr_output with
       | None -> Fail "no output1 recorded for an error=false row"
       | Some out_rel ->
         let out_path = Filename.concat test_dir out_rel in
         (match read_file out_path with
          | None -> Fail (Printf.sprintf "expected output file not found: %s" out_path)
          | Some exp_content_raw ->
            let exp_content = sanitize_nquads_text exp_content_raw in
            let exp_ds = Parser_NQuads.parse_nquads exp_content in
            let exp_canon = sanitize_nquads_text (RDF_Canonical.canonicalize_to_nquads exp_ds) in
            let got_canon = sanitize_nquads_text (RDF_Canonical.canonicalize_to_nquads got_ds) in
            if got_canon = exp_canon then Pass
            else
              Fail (Printf.sprintf "canonical N-Quads differ\n      expected:\n%s      got:\n%s"
                      (head exp_canon 400) (head got_canon 400))))

(* rml-io's RMLTTC0* fixtures are logical-TARGET (output serialization)
   tests — out of scope (plan's Stage 9, indefinite priority; this
   program only evaluates logical SOURCES). Skip them explicitly rather
   than running them into noisy, uninformative FAILs. *)
let is_target_test id =
  let prefix = "RMLTTC" in
  let plen = String.length prefix in
  String.length id >= plen && String.sub id 0 plen = prefix

let run_test_labelled module_dir (tr : test_row) =
  if is_target_test tr.tr_id then
    Skip "rml-io logical-target (output serialization) test — out of scope, see plan Stage 9"
  else run_test module_dir tr

(* ------------------------------------------------------------------ *)
(* Suite run + reporting. *)

let matches_filter filter id =
  match filter with
  | None -> true
  | Some p -> String.length id >= String.length p && String.sub id 0 (String.length p) = p

let run_suite ~label ~verbose ~list_only ~filter module_dir =
  let all_rows = load_metadata module_dir in
  let rows = List.filter (fun r -> matches_filter filter r.tr_id) all_rows in
  Printf.printf "=== %s: %s (%d test rows) ===\n" label module_dir (List.length rows);
  if list_only then begin
    List.iter (fun tr -> Printf.printf "  %-16s %s\n" tr.tr_id tr.tr_title) rows;
    (0, 0, 0, List.length rows)
  end else begin
    let pass = ref 0 and fail = ref 0 and skip = ref 0 in
    List.iter
      (fun tr ->
         match run_test_labelled module_dir tr with
         | Pass -> incr pass; Printf.printf "PASS %s\n" tr.tr_id
         | Skip msg -> incr skip; if verbose then Printf.printf "SKIP %s — %s\n" tr.tr_id msg
         | Fail msg -> incr fail; Printf.printf "FAIL %s — %s\n" tr.tr_id msg)
      rows;
    Printf.printf "%s: %d pass, %d fail, %d skip (out of %d)\n"
      label !pass !fail !skip (List.length rows);
    (!pass, !fail, !skip, List.length rows)
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "RML (RDF Mapping Language) test-suite runner — Stage 8 of the RML program.\n\
     \n\
     Usage:\n\
     \  ./rml_runner                Run rml-core (primary conformance target)\n\
     \  ./rml_runner --io           Also run rml-io's RMLSTC0* source tests\n\
     \                              (secondary section; RMLTTC0* logical-target\n\
     \                              tests are SKIPped — out of scope)\n\
     \  ./rml_runner --filter P     Only run test IDs starting with P\n\
     \  ./rml_runner --list         List parsed test entries (no execution)\n\
     \  ./rml_runner -v|--verbose   Show skip reasons too (FAIL always shown)\n\
     \  ./rml_runner --help         Show this help\n\
     \n\
     Goal: rml-core 76 pass, 0 fail (of 76) — see\n\
     docs/designissues/2026-07-05-rml-program-plan.md.\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let list_only = ref false in
  let run_io = ref false in
  let filter = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: rest -> list_only := true; loop rest
    | "--io" :: rest -> run_io := true; loop rest
    | "--filter" :: p :: rest -> filter := Some p; loop rest
    | _ ->
      Printf.eprintf "rml_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  Printf.printf "=== RML Test Runner ===\n\n";
  let core_dir = default_dir (core_dir_candidates ()) in
  let (core_pass, core_fail, _core_skip, core_total) =
    run_suite ~label:"rml-core" ~verbose:!verbose ~list_only:!list_only ~filter:!filter core_dir
  in
  Printf.printf "\n";
  let io_pass, io_fail, io_skip, io_total =
    if !run_io then begin
      let io_dir = default_dir (io_dir_candidates ()) in
      let r = run_suite ~label:"rml-io" ~verbose:!verbose ~list_only:!list_only ~filter:!filter io_dir in
      Printf.printf "\n"; r
    end else (0, 0, 0, 0)
  in
  Printf.printf "========================================\n";
  Printf.printf "rml-core: %d pass, %d fail (out of %d)\n" core_pass core_fail core_total;
  if !run_io then
    Printf.printf "rml-io:   %d pass, %d fail, %d skip (out of %d)\n" io_pass io_fail io_skip io_total;
  Printf.printf "========================================\n";
  if (not !list_only) && core_fail > 0 then exit 1
