(* OWL 2 Test Cases runner — SKELETON (Phase 0).

   Reads one of the W3C OWL 2 Test Case RDF/XML catalog files (default
   third_party/testing/owl/profile-RL.rdf), parses it via the F*-extracted
   Parser_RDFXML, extracts <test:TestCase> nodes, and prints per-test
   identifier + rdf:type values. Emits a final count.

   !! THIS IS I/O GLUE — NO RDF/SPARQL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #10 and anti-pattern #15. This file MUST
   never contain entailment logic — that belongs in .fst modules and
   must be extracted. Phase 1 (next commit) will hook up
   RDF_Graph_Executable.owl_rl_closure_with_reflexivity; this commit
   deliberately stops at the manifest-reader skeleton.

   Scoping + phased plan: docs/designissues/2026-04-24-owl-test-harness.md

   Usage:
     ./owl_runner
         Reads third_party/testing/owl/profile-RL.rdf (path discovered
         relative to the repo root, which the binary finds by walking
         up from its own location).
     ./owl_runner <catalog-path>
         Reads the given RDF/XML catalog file.
     ./owl_runner --list
         Lists the catalog files under third_party/testing/owl/.
     ./owl_runner --help
         Prints this help.
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Entity pre-expansion.

   The OWL 2 test catalogs open with a DOCTYPE that declares four named
   entities (&rdf;, &rdfs;, &owl;, &test;). Parser.XML / Parser.RDFXML
   (F*-extracted) handle only the five built-in XML entities, not custom
   DOCTYPE-declared ones, so we expand these four in OCaml before
   handing the buffer to the F* parser. This is pure textual substitution
   — no RDF semantics — and is safe so long as the entity values don't
   themselves contain the substitution patterns (they don't; they're
   plain URI prefixes).

   Proper DOCTYPE-entity support belongs in Parser.XML.fst and is tracked
   as a follow-up to this skeleton. *)

let catalog_entities : (string * string) list =
  [ ("&rdf;",  "http://www.w3.org/1999/02/22-rdf-syntax-ns#");
    ("&rdfs;", "http://www.w3.org/2000/01/rdf-schema#");
    ("&owl;",  "http://www.w3.org/2002/07/owl#");
    ("&test;", "http://www.w3.org/2007/OWL/testOntology#") ]

(* Strip the DOCTYPE block so Parser.XML doesn't have to skip it.
   The catalogs put it between "<!DOCTYPE" and the matching "]>" at
   the top of the file. Naive but sufficient for the vendored corpus. *)
let find_opt (re : Str.regexp) (s : string) (start : int) : int option =
  try Some (Str.search_forward re s start)
  with Not_found -> None

let strip_doctype (s : string) : string =
  let open_re  = Str.regexp_string "<!DOCTYPE" in
  let close_re = Str.regexp_string "]>" in
  match find_opt open_re s 0 with
  | None -> s
  | Some i ->
    (match find_opt close_re s i with
     | None -> s
     | Some j ->
       let close_len = 2 in (* length of "]>" *)
       let before = String.sub s 0 i in
       let after = String.sub s (j + close_len)
                              (String.length s - (j + close_len)) in
       before ^ after)

let expand_catalog_entities (s : string) : string =
  List.fold_left
    (fun acc (ent, repl) ->
       Str.global_replace (Str.regexp_string ent) repl acc)
    s
    catalog_entities

(* ------------------------------------------------------------------ *)
(* File I/O + parse path. *)

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let parse_catalog path =
  match read_file path with
  | None ->
    Printf.eprintf "owl_runner: cannot read %s\n" path;
    exit 2
  | Some raw ->
    let no_doctype = strip_doctype raw in
    let expanded = expand_catalog_entities no_doctype in
    let abs = if Filename.is_relative path
              then Filename.concat (Sys.getcwd ()) path
              else path in
    let base = "file://" ^ abs in
    Parser_RDFXML.parse_rdfxml_with_base base expanded

(* ------------------------------------------------------------------ *)
(* Triple projections. *)

let rdf_type_iri   = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let test_ns        = "http://www.w3.org/2007/OWL/testOntology#"
let test_identifier = test_ns ^ "identifier"
let test_profile    = test_ns ^ "profile"

let subject_iri_opt (s : subject) : string option =
  match s with
  | S_IRI i -> Some i
  | S_BNode _ -> None

let object_iri_opt (t : rdf_term) : string option =
  match t with
  | T_IRI i -> Some i
  | _ -> None

let object_literal_opt (t : rdf_term) : string option =
  match t with
  | T_Literal l -> Some l.lexical_form
  | _ -> None

(* Does this IRI name one of the five OWL-test test types? *)
let is_test_type_iri (iri : string) : bool =
  let prefix = test_ns in
  let pl = String.length prefix in
  let il = String.length iri in
  if il < pl then false
  else if String.sub iri 0 pl <> prefix then false
  else
    match String.sub iri pl (il - pl) with
    | "PositiveEntailmentTest"
    | "NegativeEntailmentTest"
    | "ConsistencyTest"
    | "InconsistencyTest"
    | "ProfileIdentificationTest" -> true
    | _ -> false

let short_type (iri : string) : string =
  let pl = String.length test_ns in
  if String.length iri >= pl && String.sub iri 0 pl = test_ns
  then String.sub iri pl (String.length iri - pl)
  else iri

let short_profile (iri : string) : string =
  match iri with
  | "http://www.w3.org/2007/OWL/testOntology#RL" -> "RL"
  | "http://www.w3.org/2007/OWL/testOntology#EL" -> "EL"
  | "http://www.w3.org/2007/OWL/testOntology#QL" -> "QL"
  | other -> other

(* ------------------------------------------------------------------ *)
(* Per-TestCase aggregation. *)

module StrSet = Set.Make(String)

type test_case_info = {
  iri         : string;
  identifier  : string option;     (* test:identifier string, if present *)
  types       : StrSet.t;          (* set of test:*Test rdf:types *)
  profiles    : StrSet.t;          (* set of test:profile values *)
}

let empty_info iri = {
  iri;
  identifier = None;
  types = StrSet.empty;
  profiles = StrSet.empty;
}

(* Walk the triples once, build a map from subject-IRI (test:TestCase
   subject) to test_case_info. We detect a test case by the presence of
   an rdf:type triple whose object is one of the five test-type URIs. *)
let build_index (graph : triple list) : test_case_info list =
  let tbl : (string, test_case_info) Hashtbl.t = Hashtbl.create 1024 in
  let get subj =
    match Hashtbl.find_opt tbl subj with
    | Some info -> info
    | None -> empty_info subj
  in
  List.iter
    (fun (t : triple) ->
       match subject_iri_opt t.s with
       | None -> ()
       | Some subj ->
         let info = get subj in
         if t.p = rdf_type_iri then begin
           match object_iri_opt t.o with
           | Some obj when is_test_type_iri obj ->
             let info = { info with types = StrSet.add obj info.types } in
             Hashtbl.replace tbl subj info
           | _ -> ()
         end else if t.p = test_identifier then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with identifier = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_profile then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with profiles = StrSet.add obj info.profiles } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end)
    graph;
  (* Keep only subjects that actually carry a test-type. *)
  Hashtbl.fold
    (fun _ info acc ->
       if StrSet.is_empty info.types then acc else info :: acc)
    tbl []

(* ------------------------------------------------------------------ *)
(* Output. *)

let identifier_display info =
  match info.identifier with
  | Some s -> s
  | None -> "(no test:identifier)"

let print_one info =
  let types =
    info.types
    |> StrSet.elements
    |> List.map short_type
    |> String.concat ","
  in
  let profiles =
    info.profiles
    |> StrSet.elements
    |> List.map short_profile
    |> String.concat ","
  in
  let profiles = if profiles = "" then "-" else profiles in
  Printf.printf "  [%s] types=%s profiles=%s  STUB: not yet wired into closure\n"
    (identifier_display info) types profiles;
  Printf.printf "    iri=%s\n" info.iri

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (so `./owl_runner` from any cwd works). *)

let find_repo_root () =
  (* Walk up from the executable's directory looking for a CLAUDE.md. *)
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
    (* Fallback: try cwd. *)
    match walk (Sys.getcwd ()) with
    | Some r -> r
    | None -> Sys.getcwd ()

let default_catalog () =
  Filename.concat (find_repo_root ())
    "third_party/testing/owl/profile-RL.rdf"

let list_catalogs () =
  let dir = Filename.concat (find_repo_root ()) "third_party/testing/owl" in
  Printf.printf "OWL 2 test catalogs under %s:\n" dir;
  (try
     let entries = Sys.readdir dir in
     Array.sort compare entries;
     Array.iter
       (fun name ->
          if Filename.check_suffix name ".rdf"
          then Printf.printf "  %s\n" name)
       entries
   with Sys_error msg ->
     Printf.eprintf "  (cannot read: %s)\n" msg)

let print_help () =
  print_string
    "OWL 2 Test Cases runner (skeleton).\n\
     \n\
     Usage:\n\
     \  ./owl_runner                  Read third_party/testing/owl/profile-RL.rdf\n\
     \  ./owl_runner <catalog.rdf>    Read the given RDF/XML catalog\n\
     \  ./owl_runner --list           List catalog files in third_party/testing/owl/\n\
     \  ./owl_runner --help           Show this help\n\
     \n\
     Status: Phase 0 skeleton — reads manifest, prints per-test identifier\n\
     and types, emits final count. Does NOT run any reasoning yet.\n\
     See docs/designissues/2026-04-24-owl-test-harness.md.\n"

(* ------------------------------------------------------------------ *)
(* Main. *)

let run_catalog path =
  Printf.printf "OWL 2 test catalog: %s\n" path;
  let t0 = Unix.gettimeofday () in
  let graph = parse_catalog path in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  parsed %d triples in %.2fs\n"
    (List.length graph) (t1 -. t0);
  let tests = build_index graph in
  (* Deterministic ordering by identifier (falling back to IRI). *)
  let key info = match info.identifier with
    | Some s -> s
    | None -> info.iri in
  let tests = List.sort (fun a b -> compare (key a) (key b)) tests in
  List.iter print_one tests;
  (* Per-type tally — just the four/five categories we expect. *)
  let tally name =
    let iri = test_ns ^ name in
    List.fold_left
      (fun acc info -> if StrSet.mem iri info.types then acc + 1 else acc)
      0 tests
  in
  let n = List.length tests in
  Printf.printf "\n";
  Printf.printf "Totals: %d test cases\n" n;
  Printf.printf "  PositiveEntailmentTest:    %d\n" (tally "PositiveEntailmentTest");
  Printf.printf "  NegativeEntailmentTest:    %d\n" (tally "NegativeEntailmentTest");
  Printf.printf "  ConsistencyTest:           %d\n" (tally "ConsistencyTest");
  Printf.printf "  InconsistencyTest:         %d\n" (tally "InconsistencyTest");
  Printf.printf "  ProfileIdentificationTest: %d\n" (tally "ProfileIdentificationTest");
  Printf.printf "\n";
  Printf.printf "STUB: 0 pass, 0 fail (out of %d) — reasoning not yet wired.\n" n

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  match args with
  | [] -> run_catalog (default_catalog ())
  | ["--help"] | ["-h"] -> print_help ()
  | ["--list"] -> list_catalogs ()
  | [path] -> run_catalog path
  | _ ->
    Printf.eprintf "owl_runner: unexpected arguments; try --help\n";
    exit 2
