(* RDF Dataset Canonicalization 1.0 (RDFC-1.0) test runner — Phase 0 skeleton.

   Reads third_party/testing/rdf-canon/tests/manifest.ttl via the
   F*-extracted Parser_Turtle, extracts each rdfc:RDFC10EvalTest /
   RDFC10MapTest / RDFC10NegativeEvalTest entry, loads the input
   N-Quads file via Parser_NQuads, runs a placeholder no-op
   canonicaliser, serialises back to N-Quads, and byte-compares
   against the expected file.

   !! THIS IS I/O GLUE — NO RDF/SPARQL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #10 / anti-pattern #15. The actual
   RDFC-1.0 algorithm (first-degree hash, issuer state, n-degree
   hash) belongs in F\* and lands in Phase 1 per
   docs/designissues/2026-04-24-rdfc10-plan.md.

   Phase 0 (this file): turn the suite from "not running" into
   labelled FAIL-with-diff so the score is visible. Per the
   per-#25 rule we always print a labelled total
   ("N pass, M fail (out of K)") rather than a bare ratio.

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
let rdfc_eval_test         = rdfc_ns ^ "RDFC10EvalTest"
let rdfc_neg_eval_test     = rdfc_ns ^ "RDFC10NegativeEvalTest"
let rdfc_map_test          = rdfc_ns ^ "RDFC10MapTest"

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

type test_kind = TK_Eval | TK_NegEval | TK_Map | TK_Unknown

let kind_of_iri (iri : string) : test_kind =
  if iri = rdfc_eval_test then TK_Eval
  else if iri = rdfc_neg_eval_test then TK_NegEval
  else if iri = rdfc_map_test then TK_Map
  else TK_Unknown

let kind_label = function
  | TK_Eval    -> "Eval"
  | TK_NegEval -> "NegEval"
  | TK_Map     -> "Map"
  | TK_Unknown -> "Unknown"

type rdfc_test = {
  iri        : string;
  kind       : test_kind;
  name       : string option;
  action_iri : string option;   (* mf:action <…/test001-in.nq> *)
  result_iri : string option;   (* mf:result <…/test001-rdfc10.nq> *)
}

let empty_test iri = {
  iri; kind = TK_Unknown; name = None;
  action_iri = None; result_iri = None;
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

   This is intentionally minimal — same shape as factoidal_cli's
   term_to_ntriples plus a graph-name slot. RDFC-1.0 specifies an
   exact canonical N-Quads format (sorted lines, specific escaping);
   we approximate here so byte-comparison can succeed for the trivial
   no-bnode tests in Phase 0. Phase 1+ replaces this with the
   F\*-extracted canonical_nquads serialiser. *)

let escape_literal_lexical (s : string) : string =
  let b = Buffer.create (String.length s + 8) in
  String.iter (fun c ->
    match c with
    | '\\' -> Buffer.add_string b "\\\\"
    | '"'  -> Buffer.add_string b "\\\""
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | _    -> Buffer.add_char b c) s;
  Buffer.contents b

let term_nq (t : rdf_term) : string =
  match t with
  | T_IRI i -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let lex = escape_literal_lexical l.lexical_form in
    (match l.lang_tag with
     | Some tag -> Printf.sprintf "\"%s\"@%s" lex tag
     | None ->
       let xsd_string = "http://www.w3.org/2001/XMLSchema#string" in
       if l.datatype = xsd_string || l.datatype = ""
       then Printf.sprintf "\"%s\"" lex
       else Printf.sprintf "\"%s\"^^<%s>" lex l.datatype)

let subj_nq (s : subject) : string =
  match s with
  | S_IRI i -> "<" ^ i ^ ">"
  | S_BNode b -> "_:" ^ b

let triple_nq (graph : string option) (t : triple) : string =
  let g = match graph with
    | Some gi -> Printf.sprintf " <%s>" gi
    | None -> ""
  in
  Printf.sprintf "%s <%s> %s%s .\n" (subj_nq t.s) t.p (term_nq t.o) g

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
(* No-op canonicaliser (Phase 0 placeholder).

   The real algorithm relabels every blank node `_:e0`, `_:b1`, etc.
   to a deterministic `_:c14n0`, `_:c14n1`, … sequence. For Phase 0
   we do nothing — passes only on tests with no blank nodes.
   When the F\* `canonicalize` extracts, replace the body of this
   function with `RDF_Canon.canonicalize ds`. *)
let canonicalize_noop (ds : rdf_dataset) : rdf_dataset = ds

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
             let canon = canonicalize_noop ds in
             let got = dataset_to_canonical_nquads canon in
             if got = expected then Pass
             else Fail_diff (expected, got)
           with _ -> Fail_parse_error)))

let run_test (t : rdfc_test) : outcome =
  match t.kind with
  | TK_Eval    -> run_eval_test t
  | TK_NegEval -> Stub
  | TK_Map     -> Stub
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
    Printf.printf "  (Phase 0 skeleton; canonicalize_noop placeholder. \
                  Map / Negative tests reported as STUB. \
                  See docs/designissues/2026-04-24-rdfc10-plan.md.)\n"
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
