(* GRDDL Stage 1 test runner (local subset, no network).

   Reads third_party/testing/grddl/grddl-tests-normative.rdf (RDF/XML)
   via the F*-extracted Parser_RDFXML, walks the parsed triples to build
   a per-test index (rdfcore test-schema: t:Test, t:inputDocument,
   t:outputDocument, g:exercisesRule), classifies each test with the
   F*-extracted GRDDL_Discovery.is_networked_type / is_stage2_rule, and
   for the local Stage-1 subset:

     * reads the source document from third_party/testing/grddl/docroot/
       (allowlisted local files -- NO network fetch),
     * parses it with Parser_XML.parse_xml_document,
     * discovers same-document transformation references with
       GRDDL_Discovery.discover_transformations (paths a + b),
     * reads each discovered stylesheet from the same local docroot and
       parses it,
     * computes the GRDDL result graph with GRDDL_Discovery.grddl_result
       (XSLT.Transform + RDF/XML re-parse + rdfxbase, all in F-star),
     * reads and RDF/XML-parses the expected-output document, and
     * compares the two graphs with GRDDL_Discovery.graphs_isomorphic
       (RDFC-1.0 canonicalization -- NOT string diff).

   !! THIS IS I/O GLUE -- NO RDF/SPARQL/GRDDL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. All discovery,
   transformation, parsing, canonicalization, and graph comparison live
   in formal/fstar/GRDDL.Discovery.fst and the modules it composes
   (XSLT.Transform, Parser.XML, Parser.RDFXML, RDF.Canonical). The
   runner does file I/O, the manifest triple-walk (data extraction, same
   pattern as rdfc10_runner's build_test_index), and result bucketing.

   Scope cuts (docs/designissues/2026-07-08-grddl-scoping.md): no
   network (namespace/profile-document paths + NetworkedTest entries are
   skipped as Stage 2), RDF/XML transformation output only, well-formed
   XML/XHTML input only (no HTML tag-soup). Transforms needing
   out-of-scope XSLT 1.0 features (document(), xsl:key, xsl:import, ...)
   FAIL with a known-gap reason -- they are never counted as skips.

   Reporting (CLAUDE.md rule #25): three buckets --
     pass / fail (with reason sub-buckets) / skip-network --
   final line "grddl: X pass, Y fail, Z skip (out of N)".
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Repo-root resolution + file I/O (parallel to rdfc10_runner.ml).     *)

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

let suite_dir () =
  Filename.concat (find_repo_root ()) "third_party/testing/grddl"

let docroot () = Filename.concat (suite_dir ()) "docroot"

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
(* Map an absolute test-suite IRI to a local file under docroot/.      *)
(* The two host trees that Stage-1 tests reference:                    *)
(*   http://www.w3.org/2001/sw/grddl-wg/td/  -> docroot/td/            *)
(*   http(s)://www.w3.org/2003/g/            -> docroot/g/             *)

let td_prefix = "http://www.w3.org/2001/sw/grddl-wg/td/"
let g_prefix_http  = "http://www.w3.org/2003/g/"
let g_prefix_https = "https://www.w3.org/2003/g/"

let starts_with pfx s =
  let lp = String.length pfx and ls = String.length s in
  ls >= lp && String.sub s 0 lp = pfx

let strip_fragment iri =
  match String.index_opt iri '#' with
  | Some i -> String.sub iri 0 i
  | None -> iri

let iri_to_local iri0 =
  let iri = strip_fragment iri0 in
  if starts_with td_prefix iri then
    Some (Filename.concat (Filename.concat (docroot ()) "td")
            (String.sub iri (String.length td_prefix)
               (String.length iri - String.length td_prefix)))
  else if starts_with g_prefix_http iri then
    Some (Filename.concat (Filename.concat (docroot ()) "g")
            (String.sub iri (String.length g_prefix_http)
               (String.length iri - String.length g_prefix_http)))
  else if starts_with g_prefix_https iri then
    Some (Filename.concat (Filename.concat (docroot ()) "g")
            (String.sub iri (String.length g_prefix_https)
               (String.length iri - String.length g_prefix_https)))
  else None

let read_iri iri =
  match iri_to_local iri with
  | None -> None
  | Some path -> read_file path

(* ------------------------------------------------------------------ *)
(* Manifest vocabulary (plain data, like rdfc10_runner's mf_* IRIs).   *)

let rdf_type_iri  = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let ts_ns         = "http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#"
let test_type_iri = ts_ns ^ "Test"
let input_doc_iri  = ts_ns ^ "inputDocument"
let output_doc_iri = ts_ns ^ "outputDocument"
let exercises_rule_iri =
  "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#exercisesRule"

(* Term helpers over the extracted RDF term type. *)
let subj_iri = function
  | RDF_Term.S_IRI i -> Some i
  | RDF_Term.S_BNode _ -> None

let term_iri = function
  | RDF_Term.T_IRI i -> Some i
  | _ -> None

(* ------------------------------------------------------------------ *)
(* Manifest parse + per-test index (data extraction; classification    *)
(* decisions delegated to GRDDL_Discovery).                            *)

type gtest = {
  iri     : string;
  is_test : bool;
  types   : string list;        (* rdf:type objects (for NetworkedTest) *)
  input   : string option;      (* t:inputDocument *)
  output  : string option;      (* t:outputDocument *)
  rules   : string list;        (* g:exercisesRule objects *)
}

let empty_test iri =
  { iri; is_test = false; types = []; input = None; output = None; rules = [] }

let build_test_index (graph : triple list) : gtest list =
  let tbl : (string, gtest) Hashtbl.t = Hashtbl.create 128 in
  let get s = match Hashtbl.find_opt tbl s with Some r -> r | None -> empty_test s in
  List.iter
    (fun (t : triple) ->
       match subj_iri t.s with
       | None -> ()
       | Some s ->
         let r = get s in
         if t.p = rdf_type_iri then begin
           match term_iri t.o with
           | Some obj ->
             let is_test = r.is_test || obj = test_type_iri in
             Hashtbl.replace tbl s { r with types = obj :: r.types; is_test }
           | None -> ()
         end else if t.p = input_doc_iri then begin
           match term_iri t.o with
           | Some i -> Hashtbl.replace tbl s { r with input = Some i }
           | None -> ()
         end else if t.p = output_doc_iri then begin
           match term_iri t.o with
           | Some i -> Hashtbl.replace tbl s { r with output = Some i }
           | None -> ()
         end else if t.p = exercises_rule_iri then begin
           match term_iri t.o with
           | Some i -> Hashtbl.replace tbl s { r with rules = i :: r.rules }
           | None -> ()
         end)
    graph;
  Hashtbl.fold (fun _ r acc -> if r.is_test then r :: acc else acc) tbl []
  |> List.sort (fun a b -> compare a.iri b.iri)

(* Classification -- semantic boundary lives in F-star. *)
let is_networked (t : gtest) : bool =
  List.exists GRDDL_Discovery.is_networked_type t.types

let needs_second_document (t : gtest) : bool =
  List.exists GRDDL_Discovery.is_stage2_rule t.rules

(* ------------------------------------------------------------------ *)
(* Per-test wall-clock cap (CLAUDE.md rule #17 / scoping-doc §5). *)

exception Test_timeout

let with_timeout secs f =
  let prev = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Test_timeout)) in
  ignore (Unix.alarm secs);
  let finish () = ignore (Unix.alarm 0); Sys.set_signal Sys.sigalrm prev in
  (try let r = f () in finish (); r
   with e -> finish (); raise e)

(* ------------------------------------------------------------------ *)
(* Result buckets. *)

type outcome =
  | Pass
  | Fail of string            (* reason bucket *)
  | Skip of string            (* skip sub-reason *)

let some = function FStar_Pervasives_Native.Some x -> Some x | FStar_Pervasives_Native.None -> None

(* Out-of-scope XSLT 1.0 features (XSLT.Transform.fst scope banner):
   used ONLY to give a graph-mismatch fail a more specific reason
   string. Does not change pass/fail counts. *)
let xslt_gap_markers =
  [ "document("; "xsl:key"; "key("; "xsl:import"; "xsl:include";
    "xsl:number"; "format-number"; "disable-output-escaping";
    "xsl:apply-imports"; "generate-id(" ]

let str_contains s m =
  let lm = String.length m and ls = String.length s in
  let rec scan i = i + lm <= ls && (String.sub s i lm = m || scan (i+1)) in
  scan 0

let text_has_gap texts =
  List.exists (fun s -> List.exists (str_contains s) xslt_gap_markers) texts

(* The XSLT engine's name tests are prefix-string based, not
   namespace-URI aware -- XSLT.Transform.fst lists "prefix-aware match
   patterns" as deliberately out of scope. GRDDL stylesheets bind a
   namespace prefix (html:, h:, ...) to the SOURCE's namespace and use
   it in XPath; when the source puts those elements in the DEFAULT
   namespace (an `xmlns="..."` declaration), a prefixed name test never
   matches, so the transform returns empty selections. Detect that
   documented-gap condition on the source. *)
let source_has_default_ns input =
  str_contains input "xmlns=\"" || str_contains input "xmlns='"

(* Run one Stage-1 test: discover, transform, compare. *)
let run_local (t : gtest) : outcome =
  match t.input, t.output with
  | None, _ | _, None -> Fail "fail-manifest-incomplete"
  | Some in_iri, Some out_iri ->
    match read_iri in_iri with
    | None -> Fail "fail-input-missing"
    | Some input ->
      match some (Parser_XML.parse_xml_document input) with
      | None -> Fail "fail-known-gap-xml-parse"
      | Some root ->
        let base = in_iri in
        let xform_iris = GRDDL_Discovery.discover_transformations base root in
        (* Load + parse each discovered stylesheet from local docroot. *)
        let styles_texts =
          List.map (fun xi ->
              match read_iri xi with
              | None -> (None, "")
              | Some sty -> (some (Parser_XML.parse_xml_document sty), sty))
            xform_iris in
        let missing_style = List.exists (fun (o,_) -> o = None) styles_texts in
        let styles = List.filter_map (fun (o,_) -> o) styles_texts in
        let sty_srcs = List.map snd styles_texts in
        (* rdfxbase contributes even with no transforms; if neither a
           transform nor an RDF/XML source is present, discovery found
           nothing to act on. *)
        let is_rdfxml = GRDDL_Discovery.is_rdfxml_root root in
        if xform_iris = [] && not is_rdfxml then
          Fail "fail-discovery"
        else if missing_style then
          Fail "fail-discovery"
        else begin
          match read_iri out_iri with
          | None -> Fail "fail-expected-missing"
          | Some expected_src ->
            (* The GRDDL result graph is relative to the SOURCE document
               (the transform's rdf:about="" denotes the source), so the
               expected-output graph -- which describes the same source
               -- is parsed against the source base too, not the
               output-file URL. *)
            let expected = Parser_RDFXML.parse_rdfxml_with_base base expected_src in
            let result = GRDDL_Discovery.grddl_result base root input styles in
            (match Sys.getenv_opt "GRDDL_DEBUG" with
             | Some dbg when in_iri <> "" &&
                 (let rec ends s sub = let ls=String.length s and lu=String.length sub in
                    ls>=lu && String.sub s (ls-lu) lu = sub in ends in_iri (dbg^".html") || ends in_iri (dbg^".xml") || ends in_iri (dbg^".rdf")) ->
               Printf.eprintf "\n### DEBUG %s\n base=%s\n xform_iris=[%s]\n styles=%d result=%d expected=%d\n"
                 dbg base (String.concat "; " xform_iris)
                 (List.length styles) (List.length result) (List.length expected);
               Printf.eprintf "--- transform raw output (first style) ---\n%s\n"
                 (match styles with s::_ -> XSLT_Transform.transform s root | [] -> "(no style)");
               Printf.eprintf "--- result canonical ---\n%s\n--- expected canonical ---\n%s\n"
                 (GRDDL_Discovery.graph_to_canonical_nquads result)
                 (GRDDL_Discovery.graph_to_canonical_nquads expected)
             | _ -> ());
            if GRDDL_Discovery.graphs_isomorphic result expected then Pass
            else if source_has_default_ns input then Fail "fail-known-gap-xslt-nametest"
            else if text_has_gap sty_srcs then Fail "fail-known-gap-xslt-feature"
            else Fail "fail-graph-mismatch"
        end

let classify (t : gtest) : outcome =
  if is_networked t then Skip "skip-network"
  else if needs_second_document t then Skip "skip-stage2-ns-or-profile-document"
  else
    try with_timeout 60 (fun () -> run_local t)
    with
    | Test_timeout -> Fail "fail-timeout"
    | e -> Fail (Printf.sprintf "fail-exception:%s" (Printexc.to_string e))

(* ------------------------------------------------------------------ *)

let short_id iri =
  match String.rindex_opt iri '#' with
  | Some i -> String.sub iri (i+1) (String.length iri - i - 1)
  | None ->
    (match String.rindex_opt iri '/' with
     | Some i -> String.sub iri (i+1) (String.length iri - i - 1)
     | None -> iri)

let () =
  let manifest_path =
    if Array.length Sys.argv > 1 then Sys.argv.(1)
    else Filename.concat (suite_dir ()) "grddl-tests-normative.rdf" in
  Printf.printf "=== GRDDL Stage 1 Runner (local subset, no network) ===\n";
  Printf.printf "suite dir: %s\n" (suite_dir ());
  Printf.printf "manifest:  %s\n\n" manifest_path;
  (match read_file manifest_path with
   | None ->
     Printf.printf "ERROR: cannot read manifest %s\n" manifest_path; exit 1
   | Some raw ->
     let triples = Parser_RDFXML.parse_rdfxml_with_base
         "http://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.rdf" raw in
     Printf.printf "manifest triples: %d\n" (List.length triples);
     let tests = build_test_index triples in
     let total = List.length tests in
     Printf.printf "test entries: %d\n\n" total;
     let results = List.map (fun t -> (t, classify t)) tests in
     (* Per-bucket tallies. *)
     let bucket : (string, int) Hashtbl.t = Hashtbl.create 16 in
     let bump k = Hashtbl.replace bucket k (1 + (try Hashtbl.find bucket k with Not_found -> 0)) in
     let pass = ref 0 and fail = ref 0 and skip = ref 0 in
     List.iter (fun (_, o) -> match o with
         | Pass -> incr pass
         | Fail r -> incr fail; bump r
         | Skip r -> incr skip; bump r) results;
     (* Pass list. *)
     Printf.printf "-- PASS (%d) --\n" !pass;
     List.iter (fun (t,o) -> match o with Pass -> Printf.printf "  %s\n" (short_id t.iri) | _ -> ()) results;
     (* Fail list with reason. *)
     Printf.printf "\n-- FAIL (%d) --\n" !fail;
     List.iter (fun (t,o) -> match o with Fail r -> Printf.printf "  %-40s %s\n" (short_id t.iri) r | _ -> ()) results;
     (* Skip list with reason. *)
     Printf.printf "\n-- SKIP (%d) --\n" !skip;
     List.iter (fun (t,o) -> match o with Skip r -> Printf.printf "  %-40s %s\n" (short_id t.iri) r | _ -> ()) results;
     (* Reason-bucket summary. *)
     Printf.printf "\n-- reason buckets --\n";
     Hashtbl.fold (fun k n acc -> (k,n) :: acc) bucket []
     |> List.sort (fun (a,_) (b,_) -> compare a b)
     |> List.iter (fun (k,n) -> Printf.printf "  %-38s %d\n" k n);
     Printf.printf "\n========================================\n";
     Printf.printf "grddl: %d pass, %d fail, %d skip (out of %d)\n"
       !pass !fail !skip total;
     if !pass = 0 then exit 1)
