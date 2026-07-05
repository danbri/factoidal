(* RDF Dataset Canonicalization 1.0 (RDFC-1.0) test runner.

   Reads third_party/testing/rdf-canon/tests/manifest.ttl via the
   F*-extracted Parser_Turtle, extracts each rdfc:RDFC10EvalTest /
   RDFC10MapTest / RDFC10NegativeEvalTest entry, loads the input
   N-Quads file via Parser_NQuads, runs the F*-extracted
   RDF_Canonical.canonicalize_to_nquads, and byte-compares against
   the expected file.

   !! THIS IS I/O GLUE — NO RDF/SPARQL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #10 / anti-pattern #15. The RDFC-1.0
   algorithm (HFDQ + identifier issuer, with HNDQ deferred) lives
   in formal/fstar/RDF.Canonical.fst per
   docs/designissues/2026-04-25-rdfc10-algo-plan.md.

   Usage:
     ./rdfc10_runner            Read default manifest at
                                third_party/testing/rdf-canon/tests/manifest.ttl
     ./rdfc10_runner <path>     Read a specific manifest.ttl
     ./rdfc10_runner --list     List test types in the default manifest
     ./rdfc10_runner -v         Verbose: show first-mismatch diff per failing eval
     ./rdfc10_runner --help     Show this help
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to owl_runner.ml). *)

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

let default_manifest () =
  Filename.concat (find_repo_root ())
    "third_party/testing/rdf-canon/tests/manifest.ttl"

(* ------------------------------------------------------------------ *)
(* File I/O. *)

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

(* ------------------------------------------------------------------ *)
(* Manifest parse. *)

let mf_ns   = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
let rdfc_ns = "https://w3c.github.io/rdf-canon/tests/vocab#"
let rdf_type_iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let mf_action = mf_ns ^ "action"
let mf_result = mf_ns ^ "result"
let mf_name   = mf_ns ^ "name"
let rdfc_eval_test     = RDF_Canonical_Manifest.rdfc_eval_test
let rdfc_neg_eval_test = RDF_Canonical_Manifest.rdfc_neg_eval_test
let rdfc_map_test      = RDF_Canonical_Manifest.rdfc_map_test
let rdfc_hash_algorithm = RDF_Canonical_Manifest.rdfc_hash_algorithm

(* The manifest is a Turtle file; parser yields a list of triples (the
   default graph). All identifiers come out as IRIs. *)
let parse_manifest path =
  match read_file path with
  | None ->
    Printf.eprintf "rdfc10_runner: cannot read %s\n" path;
    exit 2
  | Some raw ->
    let abs = if Filename.is_relative path
              then Filename.concat (Sys.getcwd ()) path
              else path in
    let base = "file://" ^ abs in
    Parser_Turtle.parse_turtle_with_base raw base

(* ------------------------------------------------------------------ *)
(* Per-test record. *)

type test_kind = RDF_Canonical_Manifest.test_kind =
  | TK_Eval
  | TK_NegEval
  | TK_Map
  | TK_Unknown

let kind_of_iri = RDF_Canonical_Manifest.kind_of_iri
let kind_label  = RDF_Canonical_Manifest.kind_label

type rdfc_test = {
  iri        : string;
  kind       : test_kind;
  name       : string option;
  action_iri : string option;   (* mf:action <…/test001-in.nq> *)
  result_iri : string option;   (* mf:result <…/test001-rdfc10.nq> *)
  hash_algo  : string option;   (* rdfc:hashAlgorithm "SHA384", if present *)
}

let empty_test iri = {
  iri; kind = TK_Unknown; name = None;
  action_iri = None; result_iri = None; hash_algo = None;
}

(* Helpers over RDF_Graph_Executable terms. *)
let subj_iri = function
  | S_IRI i -> Some i
  | S_BNode _ -> None

let term_iri = function
  | T_IRI i -> Some i
  | _ -> None

let term_lit = function
  | T_Literal l -> Some l.lexical_form
  | _ -> None

let build_test_index (graph : triple list) : rdfc_test list =
  let tbl : (string, rdfc_test) Hashtbl.t = Hashtbl.create 256 in
  let get s = match Hashtbl.find_opt tbl s with
    | Some r -> r | None -> empty_test s in
  List.iter
    (fun (t : triple) ->
       match subj_iri t.s with
       | None -> ()
       | Some s ->
         let r = get s in
         if t.p = rdf_type_iri then begin
           match term_iri t.o with
           | Some obj ->
             let k = kind_of_iri obj in
             if k <> TK_Unknown then
               Hashtbl.replace tbl s { r with kind = k }
           | None -> ()
         end else if t.p = mf_name then begin
           match term_lit t.o with
           | Some lex ->
             Hashtbl.replace tbl s { r with name = Some lex }
           | None -> ()
         end else if t.p = mf_action then begin
           match term_iri t.o with
           | Some i ->
             Hashtbl.replace tbl s { r with action_iri = Some i }
           | None -> ()
         end else if t.p = mf_result then begin
           match term_iri t.o with
           | Some i ->
             Hashtbl.replace tbl s { r with result_iri = Some i }
           | None -> ()
         end else if t.p = rdfc_hash_algorithm then begin
           match term_lit t.o with
           | Some lex ->
             Hashtbl.replace tbl s { r with hash_algo = Some lex }
           | None -> ()
         end)
    graph;
  Hashtbl.fold
    (fun _ r acc ->
       if r.kind <> TK_Unknown then r :: acc else acc)
    tbl []
  |> List.sort (fun a b -> compare a.iri b.iri)

(* ------------------------------------------------------------------ *)
(* Resolve mf:action / mf:result IRI back to a local file path.

   The manifest's base is `file://<abs-path-to-manifest.ttl>`; relative
   action/result IRIs like `<rdfc10/test001-in.nq>` resolve to
   `file://<abs-dir>/rdfc10/test001-in.nq`. We just strip the file://
   prefix. *)

let iri_to_path (iri : string) : string option =
  let pfx = "file://" in
  let pl = String.length pfx in
  if String.length iri >= pl && String.sub iri 0 pl = pfx
  then Some (String.sub iri pl (String.length iri - pl))
  else None

(* ------------------------------------------------------------------ *)
(* N-Quads serialiser.

   Delegates to RDF.NQuads.Serialize (F-star). Per CLAUDE.md rule #11
   OCaml glue may not carry serialisation logic — the byte-correct
   N-Quads encoding (escapes, IRI/bnode/literal forms, optional
   graph-IRI tail) lives in formal/fstar/RDF.NQuads.Serialize.fst. *)

(* Delegates to F*'s RDF.NQuads.Serialize. Per CLAUDE.md rule #11
   OCaml glue may not carry serialisation logic — the byte-correct
   N-Quads encoding (escapes, IRI/bnode/literal forms, optional
   graph-IRI tail) lives in formal/fstar/RDF.NQuads.Serialize.fst. *)
let escape_literal_lexical : string -> string =
  RDF_NQuads_Serialize.nq_escape_literal

let term_nq : rdf_term -> string = RDF_NQuads_Serialize.nq_term_to_string
let subj_nq : subject  -> string = RDF_NQuads_Serialize.nq_subject_to_string

let triple_nq (graph : string option) (t : triple) : string =
  match graph with
  | Some gi -> RDF_NQuads_Serialize.nq_line_for_triple gi t
  | None    -> RDF_NQuads_Serialize.nq_line_for_triple_default_graph t

(* RDFC-1.0 §3.1: the canonical form sorts the *output* quads
   lexicographically. For Phase 0 we sort to give a fighting chance
   on the trivial no-bnode tests. *)
let dataset_to_canonical_nquads (ds : rdf_dataset) : string =
  let lines : string list ref = ref [] in
  List.iter
    (fun t -> lines := triple_nq None t :: !lines)
    ds.ds_default;
  List.iter
    (fun ng ->
       List.iter
         (fun t ->
            lines := triple_nq (Some ng.ng_name) t :: !lines)
         ng.ng_graph)
    ds.ds_named;
  let sorted = List.sort compare !lines in
  String.concat "" sorted

(* ------------------------------------------------------------------ *)
(* Canonicalisation entry point — F*-extracted RDFC-1.0 (Phase 1: HFDQ).
   See formal/fstar/RDF.Canonical.fst. *)
let canonicalize_ds (ds : rdf_dataset) : rdf_dataset =
  RDF_Canonical.canonicalize ds

(* ------------------------------------------------------------------ *)
(* Map test: render the (original-label → canonical-label) mapping as
   JSON, byte-matching the W3C testNNN-rdfc10map.json fixture format.

   Format (see test003-rdfc10map.json etc.):
     {
       "e0": "c14n0",
       "e1": "c14n1"
     }

   - Outer braces on their own lines.
   - 2-space indent, "<orig>": "<canon>" with comma after every entry
     except the last.
   - Keys/values are bnode LABELS — no "_:" prefix. Parser_NQuads /
     Parser_NTriples already strip "_:" when parsing the input, and
     the canonical labels emitted by the issuer are plain "c14nN".
   - Order: sorted by canonical-value integer (c14n0, c14n1, ...).
   This is the issuance order produced by `assign_full_in_order`,
   so `is_issued` is already in this order; we sort defensively. *)

let canon_int_of (canon : string) : int =
  (* Strip "c14n" prefix and parse the trailing integer. Defensive:
     fall back to max_int if parse fails so unexpected values sort
     last rather than crash the runner. *)
  let pfx = "c14n" in
  let pl = String.length pfx in
  let n = String.length canon in
  if n > pl && String.sub canon 0 pl = pfx
  then
    (try int_of_string (String.sub canon pl (n - pl))
     with _ -> max_int)
  else max_int

let mapping_to_json (m : (string * string) list) : string =
  let arr = Array.of_list m in
  Array.sort (fun (_, a) (_, b) -> compare (canon_int_of a) (canon_int_of b)) arr;
  let n = Array.length arr in
  if n = 0 then "{}\n"
  else begin
    let b = Buffer.create (32 * (n + 2)) in
    Buffer.add_string b "{\n";
    Array.iteri (fun i (orig, canon) ->
      Buffer.add_string b "  \"";
      Buffer.add_string b orig;
      Buffer.add_string b "\": \"";
      Buffer.add_string b canon;
      if i < n - 1
      then Buffer.add_string b "\",\n"
      else Buffer.add_string b "\"\n") arr;
    Buffer.add_string b "}\n";
    Buffer.contents b
  end

(* ------------------------------------------------------------------ *)
(* Per-test runner. *)

type outcome =
  | Pass
  | Fail_diff of string * string  (* (expected, got) *)
  | Fail_no_input
  | Fail_no_expected
  | Fail_parse_error
  | Stub                          (* Map / Negative — not yet wired *)

let outcome_tag = function
  | Pass -> "PASS "
  | Fail_diff _ -> "FAIL "
  | Fail_no_input -> "FAIL "
  | Fail_no_expected -> "FAIL "
  | Fail_parse_error -> "FAIL "
  | Stub -> "STUB "

let run_eval_test (t : rdfc_test) : outcome =
  match t.action_iri, t.result_iri with
  | None, _ -> Fail_no_input
  | _, None -> Fail_no_expected
  | Some a, Some r ->
    let in_path  = iri_to_path a in
    let out_path = iri_to_path r in
    (match in_path, out_path with
     | None, _ | _, None -> Fail_parse_error
     | Some ip, Some op ->
       (match read_file ip, read_file op with
        | None, _ -> Fail_no_input
        | _, None -> Fail_no_expected
        | Some src, Some expected ->
          (try
             let ds = Parser_NQuads.parse_nquads src in
             let alg_str = match t.hash_algo with Some s -> s | None -> "SHA256" in
             let alg = RDF_Canonical.hash_algorithm_of_string alg_str in
             let got = RDF_Canonical.canonicalize_to_nquads_alg alg ds in
             let _ = canonicalize_ds in     (* keep symbol live *)
             let _ = dataset_to_canonical_nquads in (* legacy helper *)
             if got = expected then Pass
             else Fail_diff (expected, got)
           with _ -> Fail_parse_error)))

let run_map_test (t : rdfc_test) : outcome =
  match t.action_iri, t.result_iri with
  | None, _ -> Fail_no_input
  | _, None -> Fail_no_expected
  | Some a, Some r ->
    let in_path  = iri_to_path a in
    let out_path = iri_to_path r in
    (match in_path, out_path with
     | None, _ | _, None -> Fail_parse_error
     | Some ip, Some op ->
       (match read_file ip, read_file op with
        | None, _ -> Fail_no_input
        | _, None -> Fail_no_expected
        | Some src, Some expected ->
          (try
             let ds = Parser_NQuads.parse_nquads src in
             let alg_str = match t.hash_algo with Some s -> s | None -> "SHA256" in
             let alg = RDF_Canonical.hash_algorithm_of_string alg_str in
             let mapping = RDF_Canonical.build_canonical_mapping_alg alg ds in
             let got = mapping_to_json mapping in
             if got = expected then Pass
             else Fail_diff (expected, got)
           with _ -> Fail_parse_error)))

let run_test (t : rdfc_test) : outcome =
  match t.kind with
  | TK_Eval    -> run_eval_test t
  | TK_NegEval -> Stub
  | TK_Map     -> run_map_test t
  | TK_Unknown -> Stub

(* ------------------------------------------------------------------ *)
(* Output. *)

let local_name (iri : string) : string =
  (* Strip "file://…/manifest#" prefix to get :test001c style label. *)
  match String.rindex_opt iri '#' with
  | Some i -> String.sub iri (i + 1) (String.length iri - i - 1)
  | None ->
    (match String.rindex_opt iri '/' with
     | Some i -> String.sub iri (i + 1) (String.length iri - i - 1)
     | None -> iri)

let print_outcome ~verbose (t : rdfc_test) (o : outcome) =
  let id = local_name t.iri in
  let kind = kind_label t.kind in
  let nm = match t.name with Some s -> s | None -> "" in
  Printf.printf "  %s [%s] %-12s  %s\n" (outcome_tag o) kind id nm;
  if verbose then begin
    match o with
    | Fail_diff (expected, got) ->
      let head s n =
        let ln = String.length s in
        if ln <= n then s
        else String.sub s 0 n ^ "…(truncated)\n"
      in
      Printf.printf "      expected (%d bytes):\n%s" (String.length expected) (head expected 400);
      Printf.printf "      got      (%d bytes):\n%s" (String.length got) (head got 400)
    | _ -> ()
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "RDFC-1.0 (RDF Dataset Canonicalization) test runner — Phase 0 skeleton.\n\
     \n\
     Usage:\n\
     \  ./rdfc10_runner               Read default manifest\n\
     \  ./rdfc10_runner <path>        Read a specific manifest.ttl\n\
     \  ./rdfc10_runner --list        List parsed entries (no execution)\n\
     \  ./rdfc10_runner -v|--verbose  Show first-mismatch diff per failing test\n\
     \  ./rdfc10_runner --help        Show this help\n\
     \n\
     Status: Phase 0 — runner skeleton only. canonicalize_noop is a\n\
     placeholder; PASS lines are coincidental (tests with zero blank\n\
     nodes whose serialised round-trip happens to byte-match the\n\
     expected canonical form). The actual RDFC-1.0 algorithm will land\n\
     in F\\* per docs/designissues/2026-04-24-rdfc10-plan.md.\n"

let run_manifest ?(verbose=false) ~list_only path =
  Printf.printf "RDFC-1.0 manifest: %s\n" path;
  let t0 = Unix.gettimeofday () in
  let graph = parse_manifest path in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  parsed %d triples in %.2fs\n"
    (List.length graph) (t1 -. t0);
  let tests = build_test_index graph in
  let n = List.length tests in
  let count_kind k =
    List.fold_left (fun acc t -> if t.kind = k then acc + 1 else acc) 0 tests
  in
  Printf.printf "Totals: %d test entries\n" n;
  Printf.printf "  RDFC10EvalTest:         %d\n" (count_kind TK_Eval);
  Printf.printf "  RDFC10MapTest:          %d\n" (count_kind TK_Map);
  Printf.printf "  RDFC10NegativeEvalTest: %d\n" (count_kind TK_NegEval);
  Printf.printf "\n";
  if list_only then begin
    List.iter
      (fun t ->
         let id = local_name t.iri in
         let nm = match t.name with Some s -> s | None -> "" in
         Printf.printf "  [%s] %-12s  %s\n" (kind_label t.kind) id nm)
      tests
  end else begin
    let outcomes = List.map (fun t -> (t, run_test t)) tests in
    List.iter (fun (t, o) -> print_outcome ~verbose t o) outcomes;
    let pass, fail, stub =
      List.fold_left
        (fun (p, f, s) (_, o) ->
           match o with
           | Pass -> (p + 1, f, s)
           | Stub -> (p, f, s + 1)
           | _ -> (p, f + 1, s))
        (0, 0, 0) outcomes
    in
    Printf.printf "\n";
    Printf.printf "RDFC-1.0 tests: %d pass, %d fail, %d stub (out of %d)\n"
      pass fail stub n;
    Printf.printf "  (Phase 1: HFDQ + simple issuer (F* RDF.Canonical). \
                  HNDQ for collisions and Map / NegEval tests deferred. \
                  See docs/designissues/2026-04-25-rdfc10-algo-plan.md.)\n"
  end

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
      Printf.eprintf "rdfc10_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let manifest = match !path with
    | Some p -> p
    | None -> default_manifest ()
  in
  run_manifest ~verbose:!verbose ~list_only:!list_only manifest
