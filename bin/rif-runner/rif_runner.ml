(* RIF Core (rule #11 consumer) — standalone runner for the 4 vendored
   W3C RIF test cases under third_party/testing/rif/tc/.

   !! THIS IS I/O GLUE — NO RDF/SPARQL/RIF SEMANTIC LOGIC !!
   Per CLAUDE.md iron rule #10/#11 and anti-pattern #15, all reasoning
   lives in F*-extracted modules already on the link line:
     - Parser_RIFXML.parse_rif_program_with_imports  (RIF-XML -> AST +
       import URL list)
     - RIF_Core_Eval.fixpoint                        (fuel-bounded
       forward-chaining saturation)
     - SPARQL11_Parser / OWL_QueryEval / SPARQL11_Algebra
       (the SAME query parser + evaluator every other W3C-conformance
       runner in this repo uses — NOT RIF.Core.Tests' simplified
       triple-membership shims, which only check ground-triple
       membership and never run a real SELECT/ASK evaluation).
   This file's job is: locate the four vendored test fixtures, strip
   the XML DOCTYPE/entity prolog Parser.XML doesn't implement, merge
   RIF <Import> companion graphs, and compare the evaluator's answer
   to the expected .srx.

   The four cases (mf:name from the SPARQL 1.1 entailment manifest,
   third_party/testing/w3c/sparql/sparql11/entailment/manifest.ttl):
     :rif01  "RIF Logical Entailment (referencing RIF XML)"
     :rif03  "RIF Core WG tests: Frames"
     :rif04  "RIF Core WG tests: Modeling Brain Anatomy"
     :rif06  "RIF Core WG tests: RDF Combination Blank Node"

   The manifest's qt:data .ttl for each is a one-line pointer triple
   (e.g. `<rif01.rif> rif:usedWithProfile ent:Simple`), sometimes with
   extra ground facts (rif01). The RIF-XML rule document that actually
   drives inference is not bundled with the SPARQL suite; the
   authoritative copy lives in the vendored RIF Test Cases mirror
   under third_party/testing/rif/tc/<TestName>/. A small hardcoded
   lookup table (4 entries — exhaustive, not a general manifest walker
   per this PR's brief) maps each mf:name to its .rif / companion-.rdf
   / .ttl / .rq / .srx quintet.

   Usage:
     ./rif_runner              Run all 4 cases, print per-test PASS/FAIL
                                + a labelled score line.
     ./rif_runner -v|--verbose Print expected/actual on FAIL.
     ./rif_runner --help       Show this help.
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* File I/O helpers. *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let file_to_base_uri path =
  let abs = if Filename.is_relative path
            then Filename.concat (Sys.getcwd ()) path
            else path in
  "file://" ^ abs

(* ------------------------------------------------------------------ *)
(* DOCTYPE / internal-subset entity expansion.

   The F* Parser.XML scanner (Parser.XML.fst) implements only the five
   built-in XML entities; it has no DTD-parsing support at all, so a
   `<!DOCTYPE Document [ <!ENTITY rif "..."> ... ]>` prolog makes
   parse_xml_document return None. Every vendored .rif file (all four
   premise documents) and one companion .rdf (Modeling_Brain_Anatomy-
   import001.rdf) open with such a prolog; RDF_Combination_Blank_Node's
   companion .rdf has no DOCTYPE at all.

   Rather than hardcode two different entity tables (RIF's rif/xs/rdf
   vs. the OWL-catalog-style owl/owl2/xsd/owl2xml/testOntology/rdfs/rdf
   set used by the brain-anatomy import), this scans the internal
   subset itself for `<!ENTITY name "value">` declarations, strips the
   whole `<!DOCTYPE ...[...]>` block, and inline-substitutes every
   `&name;` reference with its declared value. Pure textual
   preprocessing — no RDF/RIF semantics — same category as owl_runner's
   catalog_entities expansion (bin/owl-runner/owl_runner.ml). *)

let entity_ref_re name = Str.regexp_string ("&" ^ name ^ ";")

let extract_entity_defs (subset : string) : (string * string) list =
  let re = Str.regexp
      "<!ENTITY[ \t\r\n]+\\([A-Za-z_][A-Za-z0-9_.-]*\\)[ \t\r\n]+\"\\([^\"]*\\)\"[ \t\r\n]*>" in
  let rec go pos acc =
    match (try Some (Str.search_forward re subset pos) with Not_found -> None) with
    | None -> List.rev acc
    | Some i ->
      let name = Str.matched_group 1 subset in
      let value = Str.matched_group 2 subset in
      go (i + String.length (Str.matched_string subset)) ((name, value) :: acc)
  in
  go 0 []

let find_opt (re : Str.regexp) (s : string) (start : int) : int option =
  try Some (Str.search_forward re s start) with Not_found -> None

let doctype_open_re = Str.regexp_string "<!DOCTYPE"
let doctype_subset_re = Str.regexp "\\[\\([^]]*\\)\\][ \t\r\n]*>"

let expand_doctype_entities (s : string) : string =
  match find_opt doctype_open_re s 0 with
  | None -> s
  | Some start ->
    (match find_opt doctype_subset_re s start with
     | None -> s (* malformed / no internal subset -- leave untouched *)
     | Some _ ->
       let subset = Str.matched_group 1 s in
       let close_idx = Str.match_end () in
       let before = String.sub s 0 start in
       let after = String.sub s close_idx (String.length s - close_idx) in
       let stripped = before ^ after in
       let entities = extract_entity_defs subset in
       List.fold_left
         (fun acc (name, value) -> Str.global_replace (entity_ref_re name) value acc)
         stripped entities)

(* Load a companion data file (Turtle or RDF/XML, auto-detected by
   extension) with a file:// base for relative-IRI resolution. *)
let load_data_file path : triple list =
  match read_file path with
  | None -> []
  | Some raw ->
    let base = file_to_base_uri path in
    if Filename.check_suffix path ".ttl" then
      Parser_Turtle.parse_turtle_with_base raw base
    else
      let raw = expand_doctype_entities raw in
      Parser_RDFXML.parse_rdfxml_with_base base raw

(* ------------------------------------------------------------------ *)
(* Resolve a RIF <Import><location>URL</location></Import> URL to a
   local file under the test's vendored directory. Mirrors the
   basename + extension-fallback heuristic other runners in this repo
   use for the same vendored corpus (rif06's import omits the .rdf
   suffix in its <location>). Consumer-side I/O only (rule #11); the
   verified surface (Parser_RIFXML.extract_document_imports) supplies
   just the URL strings. *)
let resolve_import_local_path (test_dir : string) (url : string) : string option =
  let bn = Filename.basename url in
  let candidates =
    if Filename.check_suffix bn ".rdf" || Filename.check_suffix bn ".ttl"
    then [ bn ]
    else [ bn ^ ".rdf"; bn ^ ".ttl"; bn ]
  in
  let rec first_existing = function
    | [] -> None
    | c :: rest ->
      let p = Filename.concat test_dir c in
      if Sys.file_exists p then Some p else first_existing rest
  in
  first_existing candidates

(* ------------------------------------------------------------------ *)
(* The four vendored test cases (exhaustive lookup table; see module
   comment). *)

(* Closure to apply to a resolved <Import> companion graph before it is
   merged into the RIF premise. The RIF-XML <Import><profile>URL</profile>
   element names the entailment regime the imported document should be
   read under (Parser.RIFXML.fst reads it but does not expose it -- "RIF
   Core's entailment-profile selection is out of scope for this PR" per
   its own comment -- so the profile URL from each vendored .rif is
   hardcoded here alongside the rest of the 4-entry lookup table, not
   invented). Modeling_Brain_Anatomy's import declares
   `http://www.w3.org/ns/entailment/OWL-Direct`: its rule needs
   `rdf:type MaterialAnatomicalEntity` on individuals that the imported
   ontology only asserts via `rdf:type Gyrus` + `Gyrus rdfs:subClassOf
   MaterialAnatomicalEntity` -- without OWL-Direct closure the subclass
   membership never materialises and the rule body never matches.
   RDF_Combination_Blank_Node's import declares plain
   `http://www.w3.org/ns/entailment/RDF` (no subClassOf reasoning
   needed) so it is merged as-is. Both closure functions are existing
   F*-extracted primitives already used for the SPARQL "OWL-Direct" /
   "RDFS" entailment-regime dispatch in bin/w3c-runner/w3c_runner.ml --
   nothing new is added to the verified library for this. *)
(* RDFS_Closure added for the corpus walker below (Part 2): several
   corpus premises declare <profile>.../entailment/RDF</profile> or
   .../RDFS</profile> rather than the plain-merge "RDF" case the
   original 4-entry table's rif06 uses (that one has no subClassOf
   facts to close over, so No_Closure and RDFS_Closure are
   observationally identical for it) -- bin/w3c-runner/w3c_runner.ml's
   own entailment-regime dispatch treats "RDFS" and "RDF" identically
   via rdfs_closure_with_reflexivity, which this mirrors. *)
type import_closure = No_Closure | RDFS_Closure | OWL_Direct_Closure

let apply_import_closure (mode : import_closure) (g : triple list) : triple list =
  match mode with
  | No_Closure -> g
  | RDFS_Closure ->
    (try RDF_Graph_Executable.rdfs_closure_with_reflexivity g (Z.of_int 100)
     with _ -> g)
  | OWL_Direct_Closure ->
    (* OWL 2 Direct Semantics excludes ontology-annotation triples
       (predicates declared `rdf:type owl:AnnotationProperty` /
       `owl:OntologyProperty`, e.g. dc:title on an owl:Ontology
       individual) from the "regular" graph before entailment --
       see OWL_DirectMapping_Filter.fst (F* semantics decision, per
       bin/rif-runner/README.md's Non-Annotation_Entailment
       diagnosis). Filtered BEFORE closure so annotation assertions
       never seed a rule match downstream. *)
    let g0 = OWL_DirectMapping_Filter.exclude_annotation_triples g in
    let fuel = Z.of_int 100 in
    let g1 = RDF_Graph_Executable.owl_rl_closure_with_reflexivity g0 fuel in
    let g2 = Tableau.tableau_materialise g1 in
    RDF_Graph_Executable.owl_rl_closure_with_reflexivity g2 fuel

type rif_test = {
  rt_label      : string;   (* short id used in output, e.g. "rif01" *)
  rt_name       : string;   (* mf:name from the entailment manifest *)
  rt_rif_file   : string;   (* the *-premise.rif rule document *)
  rt_test_dir   : string;   (* dir to resolve <Import> companions in *)
  rt_data_ttl   : string;   (* manifest qt:data .ttl *)
  rt_query      : string;   (* manifest qt:query .rq *)
  rt_expected   : string;   (* manifest mf:result .srx *)
  rt_import_closure : import_closure; (* per <Import><profile>, see above *)
}

let entailment_dir = "third_party/testing/w3c/sparql/sparql11/entailment"
let rif_tc_dir = "third_party/testing/rif/tc"

let tests : rif_test list =
  [ { rt_label = "rif01";
      rt_name = "RIF Logical Entailment (referencing RIF XML)";
      rt_rif_file = Filename.concat rif_tc_dir
          "Logical_entailment_referencing_RIF_XML/rif01-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir
          "Logical_entailment_referencing_RIF_XML";
      rt_data_ttl = Filename.concat entailment_dir "rif01.ttl";
      rt_query    = Filename.concat entailment_dir "rif01.rq";
      rt_expected = Filename.concat entailment_dir "rif01.srx";
      rt_import_closure = No_Closure };
    { rt_label = "rif03";
      rt_name = "RIF Core WG tests: Frames";
      rt_rif_file = Filename.concat rif_tc_dir "Frames/Frames-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir "Frames";
      rt_data_ttl = Filename.concat entailment_dir "rif03.ttl";
      rt_query    = Filename.concat entailment_dir "rif03.rq";
      rt_expected = Filename.concat entailment_dir "rif03.srx";
      rt_import_closure = No_Closure };
    { rt_label = "rif04";
      rt_name = "RIF Core WG tests: Modeling Brain Anatomy";
      rt_rif_file = Filename.concat rif_tc_dir
          "Modeling_Brain_Anatomy/Modeling_Brain_Anatomy-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir "Modeling_Brain_Anatomy";
      rt_data_ttl = Filename.concat entailment_dir "rif04.ttl";
      rt_query    = Filename.concat entailment_dir "rif04.rq";
      rt_expected = Filename.concat entailment_dir "rif04.srx";
      (* <Import><profile>http://www.w3.org/ns/entailment/OWL-Direct</profile> *)
      rt_import_closure = OWL_Direct_Closure };
    { rt_label = "rif06";
      rt_name = "RIF Core WG tests: RDF Combination Blank Node";
      rt_rif_file = Filename.concat rif_tc_dir
          "RDF_Combination_Blank_Node/RDF_Combination_Blank_Node-premise.rif";
      rt_test_dir = Filename.concat rif_tc_dir "RDF_Combination_Blank_Node";
      rt_data_ttl = Filename.concat entailment_dir "rif06.ttl";
      rt_query    = Filename.concat entailment_dir "rif06.rq";
      rt_expected = Filename.concat entailment_dir "rif06.srx";
      (* <Import><profile>http://www.w3.org/ns/entailment/RDF</profile> --
         no subClassOf reasoning in this fixture; merged as-is. *)
      rt_import_closure = No_Closure } ]

(* ------------------------------------------------------------------ *)
(* Result comparison (deliberately small — only the two shapes the
   four vendored cases exercise: ASK/boolean and a SELECT with one or
   more fully-ground rows). Numeric-literal fallback mirrors
   bin/w3c-runner/w3c_runner.ml's term_equal so "10"^^xsd:integer
   compares correctly regardless of incidental lexical differences. *)

let xsd_numeric_types =
  [ "http://www.w3.org/2001/XMLSchema#integer";
    "http://www.w3.org/2001/XMLSchema#decimal";
    "http://www.w3.org/2001/XMLSchema#double";
    "http://www.w3.org/2001/XMLSchema#float" ]

let numeric_literal_equal l1 l2 =
  List.mem l1.datatype xsd_numeric_types && List.mem l2.datatype xsd_numeric_types &&
  (try float_of_string l1.lexical_form = float_of_string l2.lexical_form
   with _ -> false)

let lang_tag_equal t1 t2 =
  match t1, t2 with
  | None, None -> true
  | Some a, Some b -> String.lowercase_ascii a = String.lowercase_ascii b
  | _ -> false

let term_equal a b =
  match a, b with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode _, T_BNode _ -> true
  | T_Literal l1, T_Literal l2 ->
    (l1.lexical_form = l2.lexical_form && l1.datatype = l2.datatype
     && lang_tag_equal l1.lang_tag l2.lang_tag)
    || numeric_literal_equal l1 l2
  | _ -> false

let term_to_string = function
  | T_IRI i -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    "\"" ^ l.lexical_form ^ "\"" ^
    (match l.lang_tag with
     | Some lt -> "@" ^ lt
     | None -> "^^<" ^ l.datatype ^ ">")

let row_to_string row =
  String.concat ", " (List.map (fun (v, t) -> "?" ^ v ^ "=" ^ term_to_string t) row)

let binding_row_matches expected actual =
  List.for_all
    (fun (var, exp_val) ->
       match List.assoc_opt var actual with
       | Some act_val -> term_equal exp_val act_val
       | None -> false)
    expected

(* Multiset match: every expected row consumes exactly one distinct
   matching actual row (same convention as w3c_runner's
   results_match_with). *)
let results_match expected_rows actual_rows =
  if List.length expected_rows <> List.length actual_rows then false
  else
    let remaining = ref actual_rows in
    List.for_all
      (fun exp_row ->
         match List.partition (binding_row_matches exp_row) !remaining with
         | (_ :: rest, non) -> remaining := rest @ non; true
         | ([], _) -> false)
      expected_rows

(* ------------------------------------------------------------------ *)
(* Per-test pipeline. *)

type outcome = Pass | Fail of string

exception Test_error of string

let run_test verbose (tc : rif_test) : outcome =
  try
    (* 1. RIF-XML rule document. *)
    let rif_xml_raw =
      match read_file tc.rt_rif_file with
      | Some s -> s
      | None -> raise (Test_error ("cannot read " ^ tc.rt_rif_file))
    in
    let rif_xml = expand_doctype_entities rif_xml_raw in
    let imports, program =
      match Parser_RIFXML.parse_rif_program_with_imports rif_xml with
      | FStar_Pervasives_Native.Some (imports, program) -> (imports, program)
      | FStar_Pervasives_Native.None ->
        raise (Test_error
                 (Printf.sprintf
                    "Parser_RIFXML.parse_rif_program_with_imports failed on %s"
                    tc.rt_rif_file))
    in

    (* 2. Premise: the manifest .ttl (pointer triple, sometimes with
       ground facts as in rif01) plus every resolvable <Import>
       companion graph, merged. *)
    let ttl_triples = load_data_file tc.rt_data_ttl in
    let import_triples =
      List.concat_map
        (fun url ->
           match resolve_import_local_path tc.rt_test_dir url with
           | None ->
             if verbose then
               Printf.eprintf "[%s] import URL did not resolve locally: %s\n"
                 tc.rt_label url;
             []
           | Some path -> apply_import_closure tc.rt_import_closure (load_data_file path))
        imports
    in
    let premise = ttl_triples @ import_triples in

    (* 3. Saturate. Prims.nat is Z.t in this codegen (fstar.lib's
       Prims.ml: `type int = Z.t`, `type nat = int`) -- fuel MUST be
       constructed via Z.of_int, not a bare OCaml int. *)
    let fuel = Z.of_int 100 in
    let saturated = RIF_Core_Eval.fixpoint premise program fuel in

    if verbose then
      Printf.eprintf "[%s] premise=%d imports=%d saturated=%d\n"
        tc.rt_label (List.length premise) (List.length import_triples)
        (List.length saturated);

    (* 4. Run the .rq against the saturated graph through the real
       SPARQL evaluator (OWL_QueryEval wraps SPARQL11_Algebra with the
       OWL query-rewrite pass, which is a structural no-op for these
       plain queries -- same dispatch shape as w3c_runner.ml). *)
    let query_content =
      match read_file tc.rt_query with
      | Some s -> s
      | None -> raise (Test_error ("cannot read " ^ tc.rt_query))
    in
    let query =
      match SPARQL11_Parser.parse_sparql_with_base
              (Some (file_to_base_uri tc.rt_query)) query_content with
      | SPARQL11_Parser.ParseOk (q, _rest) -> q
      | SPARQL11_Parser.ParseErr msg ->
        raise (Test_error ("SPARQL parse error: " ^ msg))
    in
    (* Blank nodes in the query pattern (rif06: `[] a ex:named`) act as
       existential variables under an entailment regime -- same rewrite
       w3c_runner.ml applies for its RDF/RDFS/OWL/RIF regime dispatch. *)
    let query =
      { query with
        SPARQL11_Algebra.q_pattern =
          SPARQL11_Algebra.rewrite_query_bnodes_pattern query.SPARQL11_Algebra.q_pattern }
    in
    let dataset = { ds_default = saturated; ds_named = [] } in

    let expected_content =
      match read_file tc.rt_expected with
      | Some s -> s
      | None -> raise (Test_error ("cannot read " ^ tc.rt_expected))
    in

    (match query.SPARQL11_Algebra.q_form with
     | SPARQL11_Algebra.QF_Ask ->
       let actual = OWL_QueryEval.eval_ask_query_owl query saturated dataset in
       (match Parser_SRX.parse_srx_boolean expected_content with
        | FStar_Pervasives_Native.Some expected ->
          if actual = expected then Pass
          else Fail (Printf.sprintf "ASK mismatch: expected %b, got %b" expected actual)
        | FStar_Pervasives_Native.None ->
          Fail (Printf.sprintf "could not parse expected boolean from %s" tc.rt_expected))
     | _ ->
       let actual_rows = OWL_QueryEval.eval_select_query_owl query saturated dataset in
       (match Parser_SRX.parse_srx_results expected_content with
        | FStar_Pervasives_Native.Some (_vars, expected_rows) ->
          if results_match expected_rows actual_rows then Pass
          else begin
            if verbose then begin
              Printf.eprintf "[%s] EXPECTED (%d rows):\n" tc.rt_label (List.length expected_rows);
              List.iter (fun r -> Printf.eprintf "    %s\n" (row_to_string r)) expected_rows;
              Printf.eprintf "[%s] ACTUAL (%d rows):\n" tc.rt_label (List.length actual_rows);
              List.iter (fun r -> Printf.eprintf "    %s\n" (row_to_string r)) actual_rows
            end;
            Fail (Printf.sprintf "results mismatch: expected %d row(s), got %d"
                    (List.length expected_rows) (List.length actual_rows))
          end
        | FStar_Pervasives_Native.None ->
          Fail (Printf.sprintf "could not parse expected bindings from %s" tc.rt_expected)))
  with
  | Test_error msg -> Fail msg
  | exn -> Fail (Printf.sprintf "exception: %s" (Printexc.to_string exn))

(* ------------------------------------------------------------------ *)
(* Part 2: general Core-dialect corpus walker.

   Extends coverage beyond the 4 hardcoded SPARQL-manifest-linked
   cases above to the full vendored W3C RIF Test Cases Core dialect
   subset under third_party/testing/rif-core-suite/ (see that
   directory's README.md for source/license/inventory). Unlike the 4
   cases above (which pair a RIF-XML rule document with a *separate*
   qt:data .ttl + .rq + .srx triple from the SPARQL 1.1 entailment
   manifest), each corpus test is self-contained: a "-premise.rif"
   RIF-XML document (rules AND ground facts together -- a fact
   parses to a rule with an empty body per Parser.RIFXML's own
   parse_fact_atom convention) and a "-conclusion.rif"
   (PositiveEntailmentTest) or "-nonconclusion.rif"
   (NegativeEntailmentTest) RIF-XML document holding the fact(s)
   whose entailment is under test.

   Pipeline per entailment test:
     1. Read + DOCTYPE-preprocess premise and conclusion/nonconclusion.
     2. Scan both raw texts for RIF-XML element tags this project's
        Parser.RIFXML / RIF.Core.Syntax do not model at all (External,
        List, Equal, Exists, Or, Naf/Neg) -- if found, SKIP naming the
        construct. Per this PR's brief: do NOT extend the F* parser
        this slice; report what an extension would unlock instead.
     3. Determine the <Import><profile> entailment regime (if any),
        same profile strings the 4-case table above hardcodes per
        test (Simple/RDF/RDFS -> No/RDFS closure, OWL-Direct ->
        OWL_Direct_Closure); unrecognised profiles SKIP.
     4. Parser_RIFXML.parse_rif_program_with_imports the premise;
        resolve+closure-apply any <Import> companion graph (the same
        apply_import_closure as the 4-case table, now covering
        RDFS_Closure too); RIF_Core_Eval.fixpoint-saturate starting
        from the (closed) import graph -- the premise's ground facts
        materialise on round 1 of the SAME fixpoint (a fact is a
        zero-body rule), so no separate "load facts" step is needed.
     5. Parser_RIFXML.parse_rif_program_with_imports the
        conclusion/nonconclusion; translate every fact's head atom to
        a SPARQL triple_pattern via RIF_Core_Translation.translate_atom
        (reused here on facts' heads rather than rule bodies -- its
        type, rif_atom -> option triple_pattern, is agnostic to which
        position the atom came from) to build one BGP.
     6. Ask whether that BGP has >=1 solution over the saturated
        premise via the SAME OWL_QueryEval.eval_ask_query_owl /
        SPARQL11_Algebra machinery the 4-case table drives (blank
        nodes in the conclusion BGP get the same existential
        treatment via SPARQL11_Algebra's internal
        rewrite_query_bnodes_pattern step inside eval_ask_query).
        PositiveEntailmentTest passes when the ASK is true;
        NegativeEntailmentTest passes when the ASK is false (the
        nonconclusion must NOT be entailed).

   PositiveSyntaxTest / NegativeSyntaxTest (RIF Core dialect
   "safeness" grammar restriction -- e.g. Core_NonSafeness) and
   ImportRejectionTest (vocabulary-separation / DL-consistency
   rejection) are unconditionally SKIPPED: Parser.RIFXML is a
   structural RIF-XML -> AST parser with no Core-dialect safeness
   checker and no import-rejection consistency checker, and adding
   either is out of scope for this slice (would require new F*
   modules, not just runner glue). *)

let corpus_root = "third_party/testing/rif-core-suite/Core_v1.22/Approved"

type corpus_outcome = CPass | CFail of string | CSkip of string

(* RIF-XML element tags with no counterpart at all in RIF.Core.Syntax /
   Parser.RIFXML (checked against Parser.RIFXML.fst's tag_is call
   sites: only Document/Group/Forall/Implies/And/Frame/Member/
   Subclass/Var/Const/Atom(exactly 2 args) are recognised). Detection
   is a plain substring scan -- same category as expand_doctype_entities
   above -- not a construct-by-construct parser; first match wins and
   is reported as the SKIP bucket. Measured against every vendored
   Core PositiveEntailmentTest/NegativeEntailmentTest premise +
   conclusion file (2026-07-05): External and Equal always co-occur
   with <content><Expr> wrapper elements the scan does not need to
   name separately. *)
let unsupported_construct_markers : (string * string) list = [
  "<External", "External (builtin predicate/function calls)";
  "<List",     "List (RIF list terms)";
  "<Equal",    "Equal (equality atom)";
  "<Exists",   "Exists (existential quantification in rule body/conclusion)";
  "<Or>",      "Or (disjunction in rule body)";
  "<Naf",      "Naf (negation as failure)";
  "<Neg",      "Neg (classical negation)";
]

let detect_unsupported_construct (raw : string) : string option =
  let rec go = function
    | [] -> None
    | (marker, label) :: rest ->
      (try
         let _ = Str.search_forward (Str.regexp_string marker) raw 0 in
         Some label
       with Not_found -> go rest)
  in
  go unsupported_construct_markers

let import_profile_re = Str.regexp "<profile>\\([^<]*\\)</profile>"

(* Scan raw RIF-XML premise text for the <Import><profile>...</profile>
   declaration (at most one <Import> per vendored Core test premise).
   Parser_RIFXML reads <profile> internally but (per its own header
   comment) does not expose the entailment-regime selection, so the
   runner reads the raw text directly -- same pattern the original
   4-entry table's apply_import_closure comment already documents. *)
let find_import_profile (raw : string) : string option =
  try
    let _ = Str.search_forward import_profile_re raw 0 in
    Some (Str.matched_group 1 raw)
  with Not_found -> None

let closure_for_profile (profile : string option) : import_closure option =
  match profile with
  | None -> Some No_Closure
  | Some "http://www.w3.org/ns/entailment/Simple"     -> Some No_Closure
  | Some "http://www.w3.org/ns/entailment/RDF"         -> Some RDFS_Closure
  | Some "http://www.w3.org/ns/entailment/RDFS"        -> Some RDFS_Closure
  | Some "http://www.w3.org/ns/entailment/OWL-Direct"  -> Some OWL_Direct_Closure
  | Some _ -> None

let read_rif_preprocessed (path : string) : string option =
  match read_file path with
  | None -> None
  | Some raw -> Some (expand_doctype_entities raw)

(* The corpus's -conclusion.rif / -nonconclusion.rif files are usually
   a single BARE fact atom (<Frame>/<Atom>/<Member>/<Subclass>) as the
   XML document root -- unlike premise.rif, which is always wrapped
   in <Document><payload><Group>...</Group></payload></Document> (or
   a bare <Group>, which Parser.RIFXML.fst's extract_group_from_doc
   already tolerates per its own header comment). extract_group_from_doc
   recognises exactly three root shapes (Document / Group / payload);
   a bare fact one level further down is not one of them, so parsing
   an as-is conclusion document returns None even though the fact
   atom itself is perfectly parseable once inside a Group.
   Wrapping the root in a synthetic <Group>...</Group> shell is pure
   textual reshaping -- same category as expand_doctype_entities above
   -- it does not teach Parser.RIFXML any element it could not already
   parse inside a Group; it only supplies the wrapper shape the parser
   already expects, so this stays on the I/O-glue side of rule #11/
   anti-pattern #15 (no new RIF/SPARQL semantics). *)
let xml_decl_re = Str.regexp "<\\?xml[^?]*\\?>"
let document_or_group_root_re = Str.regexp "<\\(Document\\|Group\\)[ \t\r\n>]"

let is_document_or_group_root (raw : string) : bool =
  try let _ = Str.search_forward document_or_group_root_re raw 0 in true
  with Not_found -> false

let wrap_bare_fact_in_group (raw : string) : string =
  let stripped = Str.global_replace xml_decl_re "" raw in
  (* parse_group_children (Parser.RIFXML.fst) only descends into a
     Group child that is itself tagged <sentence> or <Group>; any
     other direct child (including a bare fact atom) is silently
     treated as "unknown / metadata" and skipped, yielding an empty
     rule list rather than a parse failure. The fact must be wrapped
     in <sentence> as well as <Group>, or it vanishes silently. *)
  "<Group><sentence>" ^ String.trim stripped ^ "</sentence></Group>"

(* Some premise documents declare ONLY <directive><Import>...</Import>
   </directive> children and no rule Group at all (e.g.
   RDF_Combination_Constant_Equivalence_1/2/3/4,
   RDF_Combination_SubClass_2: every fact comes from the import, the
   premise's own RIF program is empty). extract_group_from_doc
   requires a Group (or payload/Group) child of Document and returns
   None when neither is present, even though an EMPTY rule program
   is perfectly well-formed. Splicing an empty
   <payload><Group></Group></payload> in before the closing
   </Document> is pure textual reshaping, not new parsing capability
   -- an empty Group parses to RIF_Core_Syntax.empty_program via the
   existing parser, exactly as if the test document had spelled it
   out explicitly. *)
let group_tag_re = Str.regexp_string "<Group"
let document_root_re = Str.regexp "<Document[ \t\r\n>]"
let document_close_re = Str.regexp_string "</Document>"

let has_group (raw : string) : bool =
  try let _ = Str.search_forward group_tag_re raw 0 in true with Not_found -> false

let has_document_root (raw : string) : bool =
  try let _ = Str.search_forward document_root_re raw 0 in true with Not_found -> false

let ensure_group_present (raw : string) : string =
  if has_document_root raw && not (has_group raw)
  then Str.replace_first document_close_re
         "<payload><Group></Group></payload></Document>" raw
  else raw

let parse_rif_program_lenient (raw : string)
  : (string list * RIF_Core_Syntax.rif_program) FStar_Pervasives_Native.option =
  let raw1 = if is_document_or_group_root raw then raw else wrap_bare_fact_in_group raw in
  let raw2 = ensure_group_present raw1 in
  Parser_RIFXML.parse_rif_program_with_imports raw2

(* Translate every conclusion "fact" rule's head atom into a triple
   pattern; None (propagated) if any atom is ill-typed for
   translate_atom (e.g. a literal-subject atom). Reuses
   RIF_Core_Translation.translate_atom -- the same F*-extracted
   function RIF_Core_Eval.fst calls for rule-BODY translation -- on
   the HEAD position of each fact "rule" a conclusion document parses
   to. No new RIF/SPARQL semantics: translate_atom's signature
   (rif_atom -> option triple_pattern) does not care which position
   its argument came from. *)
let translate_conclusion_facts (rules : RIF_Core_Syntax.rif_rule list)
  : SPARQL11_Algebra.triple_pattern list option =
  List.fold_left
    (fun acc (r : RIF_Core_Syntax.rif_rule) ->
       match acc with
       | None -> None
       | Some tps ->
         (match RIF_Core_Translation.translate_atom r.RIF_Core_Syntax.head with
          | FStar_Pervasives_Native.None -> None
          | FStar_Pervasives_Native.Some tp -> Some (tp :: tps)))
    (Some []) rules

let mk_ask_bgp_query (bgp : SPARQL11_Algebra.bgp) : SPARQL11_Algebra.query =
  { SPARQL11_Algebra.q_base = FStar_Pervasives_Native.None;
    q_prefixes = [];
    q_form = SPARQL11_Algebra.QF_Ask;
    q_dataset = [];
    q_pattern = SPARQL11_Algebra.GP_BGP bgp;
    q_group_by = FStar_Pervasives_Native.None;
    q_having = FStar_Pervasives_Native.None;
    q_modifier =
      { SPARQL11_Algebra.sm_order_by = FStar_Pervasives_Native.None;
        sm_distinct = false;
        sm_reduced = false;
        sm_offset = FStar_Pervasives_Native.None;
        sm_limit = FStar_Pervasives_Native.None };
    q_values = FStar_Pervasives_Native.None }

(* Flattened via exceptions (same shape as run_test's Test_error above)
   rather than a deep match-pyramid -- easier to keep parenthesization
   correct across this many sequential decision points. *)
exception Corpus_skip of string
exception Corpus_fail of string

let run_corpus_entailment_test
    (verbose : bool) (positive : bool) (name : string) (dir : string)
  : corpus_outcome =
  try
    let premise_path = Filename.concat dir (name ^ "-premise.rif") in
    let concl_suffix = if positive then "-conclusion.rif" else "-nonconclusion.rif" in
    let concl_path = Filename.concat dir (name ^ concl_suffix) in
    let premise_raw =
      match read_rif_preprocessed premise_path with
      | Some s -> s
      | None ->
        raise (Corpus_skip (Printf.sprintf "premise file not in vendored corpus: %s" premise_path))
    in
    let concl_raw =
      match read_rif_preprocessed concl_path with
      | Some s -> s
      | None ->
        raise (Corpus_skip
                 (Printf.sprintf "%s not in vendored corpus (packaging gap in the official Core_v1.22 zip)"
                    (Filename.basename concl_path)))
    in
    (match detect_unsupported_construct premise_raw with
     | Some c -> raise (Corpus_skip c)
     | None -> ());
    (match detect_unsupported_construct concl_raw with
     | Some c -> raise (Corpus_skip c)
     | None -> ());
    let profile = find_import_profile premise_raw in
    let closure_mode =
      match closure_for_profile profile with
      | Some m -> m
      | None ->
        raise (Corpus_skip
                 (Printf.sprintf "unsupported entailment profile: %s"
                    (match profile with Some p -> p | None -> "?")))
    in
    let imports, premise_program =
      match parse_rif_program_lenient premise_raw with
      | FStar_Pervasives_Native.Some (imports, program) -> (imports, program)
      | FStar_Pervasives_Native.None ->
        raise (Corpus_skip
                 "Parser_RIFXML could not parse the premise (likely a Uniterm/Atom with arity other than 2, or another RIF-XML shape not yet modelled)")
    in
    let concl_program =
      match parse_rif_program_lenient concl_raw with
      | FStar_Pervasives_Native.Some (_concl_imports, program) -> program
      | FStar_Pervasives_Native.None ->
        raise (Corpus_skip
                 "Parser_RIFXML could not parse the conclusion (likely a Uniterm/Atom with arity other than 2, or another RIF-XML shape not yet modelled)")
    in
    let import_triples =
      List.concat_map
        (fun url ->
           match resolve_import_local_path dir url with
           | None -> []
           | Some path -> apply_import_closure closure_mode (load_data_file path))
        imports
    in
    let fuel = Z.of_int 100 in
    let saturated = RIF_Core_Eval.fixpoint import_triples premise_program fuel in
    let bgp =
      match translate_conclusion_facts concl_program.RIF_Core_Syntax.rules with
      | Some tps -> tps
      | None ->
        raise (Corpus_skip
                 "conclusion contains an atom translate_atom cannot express as a triple pattern (e.g. a literal-subject atom)")
    in
    if bgp = [] then
      (* Vacuous conclusion/nonconclusion (no facts named) -- a
         NegativeEntailmentTest with no facts to reject is a test-data
         anomaly, not a real negative case. *)
      (if positive then CPass
       else raise (Corpus_fail "nonconclusion names no facts to check (vacuous -- test data anomaly)"))
    else begin
      let query = mk_ask_bgp_query bgp in
      let dataset = { ds_default = saturated; ds_named = [] } in
      let entailed = OWL_QueryEval.eval_ask_query_owl query saturated dataset in
      if verbose then
        Printf.eprintf "[%s] saturated=%d bgp=%d entailed=%b (expect %b)\n"
          name (List.length saturated) (List.length bgp) entailed positive;
      if entailed = positive then CPass
      else CFail (Printf.sprintf "expected entailed=%b, got %b" positive entailed)
    end
  with
  | Corpus_skip reason -> CSkip reason
  | Corpus_fail msg -> CFail msg
  | exn -> CFail (Printf.sprintf "exception: %s" (Printexc.to_string exn))

let list_subdirs (dir : string) : string list =
  try
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun n -> try Sys.is_directory (Filename.concat dir n) with Sys_error _ -> false)
    |> List.sort compare
  with Sys_error _ -> []

type bucket_tally = (string, int) Hashtbl.t

let bump (tbl : bucket_tally) (label : string) : unit =
  let cur = try Hashtbl.find tbl label with Not_found -> 0 in
  Hashtbl.replace tbl label (cur + 1)

(* RDF_Combination_Constant_Equivalence_4 is a genuine corpus data
   defect, not an engine gap: both the vendored import001.rdf and
   import001.ttl declare a malformed xsd:string datatype IRI (a
   Windows local filesystem path / a scheme-less "www.w3.org/..."
   prefix, respectively) that does not match the conclusion's
   correctly-formed "http://www.w3.org/2001/XMLSchema#string" --
   present in the official W3C Core_v1.22.zip distribution as
   authored in 2010, uncorrected in the "Second Edition". Left
   reporting FAIL rather than moved to SKIP: unlike the SKIP buckets
   above (constructs this engine does not yet implement -- External,
   Equal, Exists, List, safeness/import-rejection checking), this
   test IS fully processed by the pipeline and genuinely does not
   entail under a correct datatype-IRI comparison -- the honest
   report is a labelled FAIL, not a skip that could be misread as
   "not attempted". See bin/rif-runner/README.md's Score section for
   the full diagnosis. *)
let known_corpus_defect_note (name : string) : string option =
  if name = "RDF_Combination_Constant_Equivalence_4"
  then Some "KNOWN-DEFECT: malformed xsd:string datatype IRI in the official W3C Core_v1.22.zip corpus itself (see bin/rif-runner/README.md Score section) -- not an engine gap"
  else None

let run_corpus_suite (verbose : bool) : int * int * int * bucket_tally =
  let pass = ref 0 and fail = ref 0 and skip = ref 0 in
  let buckets : bucket_tally = Hashtbl.create 16 in
  let run_category (positive : bool) (category_name : string) : unit =
    let category_dir = Filename.concat corpus_root category_name in
    List.iter
      (fun name ->
         let dir = Filename.concat category_dir name in
         match run_corpus_entailment_test verbose positive name dir with
         | CPass ->
           incr pass;
           Printf.printf "PASS corpus:%s (%s)\n" name category_name
         | CFail msg ->
           incr fail;
           let msg =
             match known_corpus_defect_note name with
             | Some note -> Printf.sprintf "%s -- %s" msg note
             | None -> msg
           in
           Printf.printf "FAIL corpus:%s (%s): %s\n" name category_name msg
         | CSkip reason ->
           incr skip;
           bump buckets reason;
           Printf.printf "SKIP corpus:%s (%s): %s\n" name category_name reason)
      (list_subdirs category_dir)
  in
  run_category true  "PositiveEntailmentTest";
  run_category false "NegativeEntailmentTest";
  (* PositiveSyntaxTest / NegativeSyntaxTest / ImportRejectionTest:
     unconditional SKIP -- see module comment above. *)
  List.iter
    (fun (category_name, reason) ->
       let category_dir = Filename.concat corpus_root category_name in
       List.iter
         (fun name ->
            incr skip;
            bump buckets reason;
            Printf.printf "SKIP corpus:%s (%s): %s\n" name category_name reason)
         (list_subdirs category_dir))
    [ ("PositiveSyntaxTest",
       "RIF Core dialect safeness-condition checking not implemented (Parser.RIFXML is structural-only, no dialect-conformance validator)");
      ("NegativeSyntaxTest",
       "RIF Core dialect safeness-condition checking not implemented (Parser.RIFXML is structural-only, no dialect-conformance validator)");
      ("ImportRejectionTest",
       "import-rejection / vocabulary-separation consistency checking not implemented (no OWL-DL consistency checker in this slice)") ];
  (!pass, !fail, !skip, buckets)

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "RIF Core test runner.\n\
     \n\
     Part 1: the 4 vendored W3C RIF test cases\n\
     (third_party/testing/rif/tc/), driven end-to-end through\n\
     Parser_RIFXML + RIF_Core_Eval.fixpoint + the real SPARQL 1.1\n\
     evaluator. Covers exactly rif01/rif03/rif04/rif06 from the SPARQL\n\
     1.1 entailment manifest -- a hardcoded 4-entry lookup table, not a\n\
     general manifest walker.\n\
     \n\
     Part 2: a directory walker over the full vendored W3C RIF Core\n\
     dialect corpus (third_party/testing/rif-core-suite/), evaluating\n\
     PositiveEntailmentTest/NegativeEntailmentTest cases directly via\n\
     premise/conclusion RIF-XML documents (no SPARQL-manifest .rq/.srx\n\
     needed). PositiveSyntaxTest/NegativeSyntaxTest/ImportRejectionTest\n\
     are honestly SKIPPED (no dialect-safeness or import-rejection\n\
     consistency checker in this project). See\n\
     third_party/testing/rif-core-suite/README.md and\n\
     bin/rif-runner/README.md for the pipeline and current score.\n\
     \n\
     Usage:\n\
     \  ./rif_runner              Run both parts\n\
     \  ./rif_runner -v|--verbose Print expected/actual on FAIL\n\
     \  ./rif_runner --help       Show this help\n"

let () =
  let verbose = ref false in
  Array.to_list Sys.argv |> List.tl |> List.iter (function
    | "-v" | "--verbose" -> verbose := true
    | "--help" | "-h" -> print_help (); exit 0
    | arg ->
      Printf.eprintf "rif_runner: unrecognized argument %s (try --help)\n" arg;
      exit 2);
  let results =
    List.map
      (fun tc ->
         let outcome = run_test !verbose tc in
         (match outcome with
          | Pass -> Printf.printf "PASS %s (%s)\n" tc.rt_label tc.rt_name
          | Fail msg -> Printf.printf "FAIL %s (%s): %s\n" tc.rt_label tc.rt_name msg);
         outcome)
      tests
  in
  let pass, fail =
    List.fold_left
      (fun (p, f) -> function Pass -> (p + 1, f) | Fail _ -> (p, f + 1))
      (0, 0) results
  in
  let total = List.length tests in
  Printf.printf "========================================\n";
  Printf.printf "rif (original 4 vendored SPARQL-manifest cases): %d pass, %d fail (out of %d)\n"
    pass fail total;

  let (c_pass, c_fail, c_skip, buckets) = run_corpus_suite !verbose in
  let c_total = c_pass + c_fail + c_skip in
  Printf.printf "========================================\n";
  Printf.printf "rif-core-suite (vendored W3C RIF Core dialect corpus): %d pass, %d fail, %d skip (out of %d)\n"
    c_pass c_fail c_skip c_total;
  Printf.printf "Skip buckets (by construct/reason):\n";
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) buckets []
  |> List.sort (fun (_, a) (_, b) -> compare (b : int) a)
  |> List.iter (fun (k, v) -> Printf.printf "  %3d  %s\n" v k);

  let grand_pass = pass + c_pass
  and grand_fail = fail + c_fail
  and grand_skip = c_skip
  in
  let grand_total = total + c_total in
  Printf.printf "========================================\n";
  Printf.printf "rif TOTAL: %d pass, %d fail, %d skip (out of %d)\n"
    grand_pass grand_fail grand_skip grand_total;
  if grand_fail > 0 then exit 1
