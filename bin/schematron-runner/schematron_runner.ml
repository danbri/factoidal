(* ISO/IEC 19757-3 (Schematron) validator conformance runner for
   formal/fstar/Schematron.Validate.fst (XSLT-1 / XPath-1 query binding).

   Runs the spec-cited corpus vendored under
   third_party/testing/schematron/ (see that directory's README.md for
   provenance: the reference implementation repository ships no
   (schema, instance, expected-report) triples, so the corpus is
   authored from ISO/IEC 19757-3 + the schematron.com tutorial and each
   case cites its source).

   !! THIS IS I/O GLUE -- NO SCHEMATRON SEMANTICS LIVE HERE !! Every
   validation decision comes from the F*-extracted
   Schematron_Validate.validate (formal/fstar/Schematron.Validate.fst),
   run over schema + instance trees produced by the F*-extracted
   Parser_XML.parse_xml_document. The manifest is parsed with the
   F*-extracted Parser_JSON.parse_json (dogfooding our own JSON parser).
   This file does file I/O, manifest traversal, finding-key comparison,
   and tallying only. Per CLAUDE.md iron rule #11 / anti-pattern #15.

   Scoring (owner discipline, anti-pattern #25 -- always labelled): a
   case PASSES when the multiset of produced findings, keyed by
   type|context|test, equals the manifest's expected multiset. The
   count of INDETERMINATE findings (assertions the XPath engine cannot
   parse -- the soundness path) is reported separately so it is never
   silently folded into pass/fail.

   Usage:
     ./schematron_runner            Run the full vendored corpus
     ./schematron_runner -v         Print every FAIL (produced vs expected)
     ./schematron_runner --help     Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (same pattern as bin/xslt-runner). *)

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

let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)
let arr_field key obj = opt_of_fs (Parser_JSON.json_get_array key obj)

(* ------------------------------------------------------------------ *)
(* An expected finding key. Compared as type|context|test (trimmed). *)

let key_of_type_ctx_test t c e =
  String.concat "|" [String.trim t; String.trim c; String.trim e]

let expected_keys (entry : Parser_JSON.json_val) : string list =
  match arr_field "expect" entry with
  | None -> []
  | Some items ->
    List.filter_map
      (fun it ->
         match str_field "type" it, str_field "context" it, str_field "test" it with
         | Some t, Some c, Some e -> Some (key_of_type_ctx_test t c e)
         | _ -> None)
      items

(* ------------------------------------------------------------------ *)
(* Manifest entry. *)

type entry = {
  name : string;
  category : string;
  schema : string;
  instance : string;
  expect : string list;   (* multiset of type|context|test keys *)
}

let entries_of_manifest json : entry list =
  match json with
  | Parser_JSON.JArray items ->
    List.filter_map
      (fun it ->
         match str_field "name" it, str_field "category" it,
               str_field "schema" it, str_field "instance" it with
         | Some name, Some category, Some schema, Some instance ->
           Some { name; category; schema; instance; expect = expected_keys it }
         | _ -> None)
      items
  | _ -> []

(* ------------------------------------------------------------------ *)
(* Produced findings -> keys, via the F*-extracted accessors. *)

let produced_keys findings =
  List.map
    (fun f ->
       key_of_type_ctx_test
         (Schematron_Validate.finding_kind f)
         (Schematron_Validate.finding_context f)
         (Schematron_Validate.finding_test f))
    findings

let count_indeterminate findings =
  List.length
    (List.filter (fun f -> Schematron_Validate.finding_kind f = "indeterminate") findings)

(* ------------------------------------------------------------------ *)
(* Per-test outcome. *)

type outcome =
  | Pass
  | Fail of string        (* short reason *)
  | Skip of string

(* An OCaml list from the F*-extracted list value (they coincide). *)
let list_of_fs (xs : 'a list) : 'a list = xs

let run_one base_dir e : outcome * int =
  let sch_path = Filename.concat base_dir e.schema in
  let inst_path = Filename.concat base_dir e.instance in
  match read_file sch_path, read_file inst_path with
  | None, _ -> (Skip "schema file missing", 0)
  | _, None -> (Skip "instance file missing", 0)
  | Some sch_s, Some inst_s ->
    (match Parser_XML.parse_xml_document sch_s with
     | FStar_Pervasives_Native.None -> (Skip "schema did not parse (Parser_XML)", 0)
     | FStar_Pervasives_Native.Some sch ->
       (match Parser_XML.parse_xml_document inst_s with
        | FStar_Pervasives_Native.None -> (Skip "instance did not parse (Parser_XML)", 0)
        | FStar_Pervasives_Native.Some inst ->
          let findings = list_of_fs (Schematron_Validate.validate sch inst) in
          let indet = count_indeterminate findings in
          let got = List.sort compare (produced_keys findings) in
          let want = List.sort compare e.expect in
          if got = want then (Pass, indet)
          else
            let show l = if l = [] then "(none)" else String.concat " ; " l in
            (Fail (Printf.sprintf "got [%s] vs want [%s]" (show got) (show want)), indet)))

(* ------------------------------------------------------------------ *)

module SMap = Map.Make (String)

let print_help () =
  print_string
    "ISO Schematron validator runner for Schematron.Validate.fst.\n\n\
     Usage:\n\
     \  ./schematron_runner          Run the full vendored corpus\n\
     \  ./schematron_runner -v       Print every FAIL as it runs\n\
     \  ./schematron_runner --help   Show this help\n\n\
     Corpus is spec-cited (ISO/IEC 19757-3 + schematron.com), vendored\n\
     under third_party/testing/schematron/. A case passes when the\n\
     produced findings (type|context|test multiset) match the manifest.\n"

let () =
  let verbose = ref false in
  let args = Array.to_list Sys.argv in
  let rec scan = function
    | [] -> ()
    | ("-v" | "--verbose") :: r -> verbose := true; scan r
    | ("-h" | "--help") :: _ -> print_help (); exit 0
    | _ :: r -> scan r
  in
  (match args with _ :: rest -> scan rest | [] -> ());
  let repo_root = find_repo_root () in
  let base_dir = Filename.concat repo_root "third_party/testing/schematron" in
  let manifest_path = Filename.concat base_dir "manifest.json" in
  Printf.printf "=== ISO Schematron Validator Runner ===\n";
  Printf.printf "suite dir: %s\n\n" base_dir;
  let manifest_s = match read_file manifest_path with
    | Some s -> s
    | None -> Printf.eprintf "schematron_runner: cannot read %s\n" manifest_path; exit 2
  in
  let entries = match Parser_JSON.parse_json manifest_s with
    | FStar_Pervasives_Native.Some j -> entries_of_manifest j
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "schematron_runner: manifest.json did not parse via Parser_JSON\n"; exit 2
  in
  let total = List.length entries in
  if total = 0 then begin
    Printf.eprintf "schematron_runner: zero manifest entries\n"; exit 2
  end;
  Printf.printf "Manifest entries: %d\n\n" total;
  let results =
    List.map
      (fun e ->
         let (o, indet) = run_one base_dir e in
         (match o with
          | Fail msg when !verbose -> Printf.eprintf "FAIL %s (%s): %s\n" e.name e.category msg
          | Skip msg when !verbose -> Printf.eprintf "SKIP %s (%s): %s\n" e.name e.category msg
          | _ -> ());
         (e, o, indet))
      entries
  in
  (* Per-category tally. *)
  let tally =
    List.fold_left
      (fun m (e, o, _) ->
         let (p, f, s) = try SMap.find e.category m with Not_found -> (0,0,0) in
         let cell = match o with
           | Pass -> (p+1, f, s)
           | Fail _ -> (p, f+1, s)
           | Skip _ -> (p, f, s+1)
         in
         SMap.add e.category cell m)
      SMap.empty results
  in
  Printf.printf "-- Per category (pass / fail / skip) --\n";
  SMap.iter
    (fun k (p, f, s) ->
       Printf.printf "  %-30s pass:%-3d fail:%-3d skip:%-3d (of %d)\n" k p f s (p+f+s))
    tally;
  Printf.printf "\n";
  let count pred = List.length (List.filter (fun (_,o,_) -> pred o) results) in
  let pass = count (function Pass -> true | _ -> false) in
  let fail = count (function Fail _ -> true | _ -> false) in
  let skip = count (function Skip _ -> true | _ -> false) in
  let indet_findings = List.fold_left (fun a (_,_,i) -> a + i) 0 results in
  let indet_cases = List.length (List.filter (fun (_,_,i) -> i > 0) results) in
  (* FAIL cluster listing. *)
  let fails = List.filter_map (fun (e,o,_) -> match o with Fail m -> Some (e,m) | _ -> None) results in
  if fails <> [] then begin
    Printf.printf "-- FAIL cases (%d) --\n" (List.length fails);
    List.iter (fun (e,m) -> Printf.printf "  %s (%s): %s\n" e.name e.category m) fails;
    Printf.printf "\n"
  end;
  Printf.printf "-- INDETERMINATE (soundness path) --\n";
  Printf.printf "  %d indeterminate finding(s) surfaced across %d case(s)\n\n"
    indet_findings indet_cases;
  Printf.printf "========================================\n";
  Printf.printf "Schematron: %d pass, %d fail, %d skip (out of %d cases); %d indeterminate finding(s)\n"
    pass fail skip total indet_findings;
  if fail > 0 || skip > 0 || pass = 0 then exit 1
