(* OWL 2 Test Cases runner — Phase 1 (profile-RL PositiveEntailmentTest).

   Reads one of the W3C OWL 2 Test Case RDF/XML catalog files (default
   third_party/testing/owl/profile-RL.rdf), parses it via the F*-extracted
   Parser_RDFXML, extracts <test:TestCase> nodes, and — for each
   PositiveEntailmentTest — runs OWL-RL closure (with reflexivity) over
   the embedded premise graph and checks that every triple of the
   embedded conclusion graph appears in the closure.

   !! THIS IS I/O GLUE — NO RDF/SPARQL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #10 and anti-pattern #15. Closure itself is
   F*-extracted; what this file does is (a) extract premise/conclusion
   literals from the manifest, (b) pre-expand DOCTYPE-declared catalog
   entities (&rdf;, &rdfs;, &owl;, &test;, &xsd;) so Parser_XML can
   tokenize them, and (c) do a relaxed "non-bnode exact + bnode
   structural" entailment check over the closed graph. Proper bnode
   isomorphism is deferred.

   Scoping + phased plan:
     docs/designissues/2026-04-24-owl-test-harness.md (skeleton)
     docs/designissues/2026-04-24-owl-runner-phase1.md (this phase)

   Usage:
     ./owl_runner
         Reads third_party/testing/owl/profile-RL.rdf (path discovered
         relative to the repo root, which the binary finds by walking
         up from its own location).
     ./owl_runner <catalog-path>
         Reads the given RDF/XML catalog file.
     ./owl_runner --list
         Lists the catalog files under third_party/testing/owl/.
     ./owl_runner -v | --verbose
         Print the first mismatching triple per failing test.
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
    ("&xsd;",  "http://www.w3.org/2001/XMLSchema#");
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
let test_ns        = OWL_Tests_Manifest.test_ns
let test_identifier = test_ns ^ "identifier"
let test_profile    = test_ns ^ "profile"
let test_premise    = test_ns ^ "rdfXmlPremiseOntology"
let test_conclusion = test_ns ^ "rdfXmlConclusionOntology"
(* NegativeEntailmentTest uses rdfXmlNonConclusionOntology — same RDF/XML
   serialization shape, just a different predicate so the catalog
   distinguishes "positive conclusion" from "negative non-conclusion". *)
let test_non_conclusion = test_ns ^ "rdfXmlNonConclusionOntology"
let test_imported_ontology = test_ns ^ "importedOntology"
let test_input_ontology   = test_ns ^ "rdfXmlInputOntology"
(* Some catalog entries carry only a functional-syntax premise
   (test:fsPremiseOntology / test:fsConclusionOntology) instead of an
   RDF/XML one. This runner reads only the rdfXml* literals; when
   test:normativeSyntax names FUNCTIONAL and no rdfXml premise is
   present, run_positive_entailment reports an honest SKIP rather than
   folding the test into FAIL/no-premise. See
   docs/designissues/2026-07-03-owl-rl-pe-fails-fix-sketch.md, 2.7. *)
let test_normative_syntax = test_ns ^ "normativeSyntax"
let test_syntax_functional = test_ns ^ "FUNCTIONAL"
(* OWL 2 Functional Syntax literals — read alongside the rdfXml* ones
   so run_positive_entailment / run_inconsistency_test can attempt the
   Parser_OWLFunctional path when no rdfXml premise/conclusion exists.
   See docs/designissues/2026-07-05-owl-functional-syntax-plan.md. *)
let test_fs_premise    = test_ns ^ "fsPremiseOntology"
let test_fs_conclusion = test_ns ^ "fsConclusionOntology"
let pos_entailment_iri = test_ns ^ "PositiveEntailmentTest"
let neg_entailment_iri = test_ns ^ "NegativeEntailmentTest"
let consistency_iri    = test_ns ^ "ConsistencyTest"
let inconsistency_iri  = test_ns ^ "InconsistencyTest"
(* test:semantics — Direct vs RDF-Based semantics dispatch (2026-07-05).
   Some catalog entries carry BOTH &test;DIRECT and &test;RDF-BASED
   (the two readings agree on that test); a few carry only one. The
   two -Direct/RDF-Based sibling pairs over an identical premise +
   candidate triple (WebOnt-I4.6-005 / -Direct,
   WebOnt-equivalentClass-008 / -Direct) are exactly the case where
   they disagree — see RDF.Graph.Executable.fst's
   owl_rule_named_equivClass_to_sameAs_mode header comment for the RDF
   semantics behind the split. Plumbing only: this runner reads the
   annotation and picks which F* closure entry point to call
   (owl_rl_closure_with_reflexivity vs. its _mode sibling); the
   dispatch RULE (which OWL-RL rule fires under which semantics) is
   entirely in RDF.Graph.Executable.fst, per rule #7 (parsers/logic
   belong in F-star). *)
let test_semantics = test_ns ^ "semantics"
let test_semantics_direct_iri = test_ns ^ "DIRECT"
let test_semantics_rdf_based_iri = test_ns ^ "RDF-BASED"
(* test:species — OWL 2 DL/Full species facet (2026-07-10). Values
   &test;DL and &test;FULL; a case annotated with both is within DL
   (every DL ontology is also a Full ontology). Scored by the
   --species mode below via the F*-extracted OWL2_SyntaxDL checker. *)
let test_species = test_ns ^ "species"
let test_species_dl_iri = test_ns ^ "DL"

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

(* Does this IRI name one of the five OWL-test test types?
   Delegates to F* per CLAUDE.md rule #11. *)
let is_test_type_iri = OWL_Tests_Manifest.is_test_type_iri

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
  premise     : string option;     (* test:rdfXmlPremiseOntology literal *)
  conclusion  : string option;     (* test:rdfXmlConclusionOntology literal *)
  fs_premise    : string option;   (* test:fsPremiseOntology literal (OWL 2
                                       Functional Syntax) — read alongside
                                       rdfXml* so entries with ONLY a
                                       functional-syntax premise can still
                                       be scored via Parser_OWLFunctional
                                       instead of an automatic skip. *)
  fs_conclusion : string option;   (* test:fsConclusionOntology literal *)
  normative_syntax : StrSet.t;     (* test:normativeSyntax objects, e.g.
                                       &test;FUNCTIONAL / &test;RDFXML *)
  semantics   : StrSet.t;          (* test:semantics objects, e.g.
                                       &test;DIRECT / &test;RDF-BASED *)
  species     : StrSet.t;          (* test:species objects, i.e.
                                       &test;DL / &test;FULL *)
  imports     : StrSet.t;          (* test:importedOntology link IRIs (catalog
                                       node IRIs that carry test:rdfXmlInputOntology
                                       literals); resolved at run time *)
}

let empty_info iri = {
  iri;
  identifier = None;
  types = StrSet.empty;
  profiles = StrSet.empty;
  premise = None;
  conclusion = None;
  fs_premise = None;
  fs_conclusion = None;
  normative_syntax = StrSet.empty;
  semantics = StrSet.empty;
  species = StrSet.empty;
  imports = StrSet.empty;
}

(* Walk the triples once, build a map from subject-IRI (test:TestCase
   subject) to test_case_info. We detect a test case by the presence of
   an rdf:type triple whose object is one of the five test-type URIs.

   Returns (test cases, import_lookup) where import_lookup maps a
   test:importedOntology IRI (a sibling owl:Thing in the catalog) to
   its test:rdfXmlInputOntology literal — the imported document as an
   RDF/XML string, ready for the parser. The import map is shared
   across all test cases since multiple tests may reference the same
   imported document. *)
let build_index (graph : triple list) : test_case_info list * (string, string) Hashtbl.t =
  let tbl : (string, test_case_info) Hashtbl.t = Hashtbl.create 1024 in
  let imports_lookup : (string, string) Hashtbl.t = Hashtbl.create 64 in
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
         end else if t.p = test_normative_syntax then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with normative_syntax = StrSet.add obj info.normative_syntax } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_semantics then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with semantics = StrSet.add obj info.semantics } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_species then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with species = StrSet.add obj info.species } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_premise then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with premise = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_conclusion then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with conclusion = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_fs_premise then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with fs_premise = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_fs_conclusion then begin
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with fs_conclusion = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_non_conclusion then begin
           (* NegativeEntailmentTest stores its conclusion under
              rdfXmlNonConclusionOntology. We collapse onto the same
              `conclusion` field; the test-type dispatch decides
              positive-vs-negative interpretation. *)
           match object_literal_opt t.o with
           | Some lex ->
             let info = { info with conclusion = Some lex } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_imported_ontology then begin
           match object_iri_opt t.o with
           | Some obj ->
             let info = { info with imports = StrSet.add obj info.imports } in
             Hashtbl.replace tbl subj info
           | None -> ()
         end else if t.p = test_input_ontology then begin
           match object_literal_opt t.o with
           | Some lex -> Hashtbl.replace imports_lookup subj lex
           | None -> ()
         end)
    graph;
  (* Keep only subjects that actually carry a test-type — or, for the
     species facet (2026-07-10), a test:species annotation: the four
     WebOnt-imports-005..008 cases in syntax-dl.rdf carry species +
     rdfXmlInputOntology but none of the five entailment test-types. *)
  let cases =
    Hashtbl.fold
      (fun _ info acc ->
         if StrSet.is_empty info.types && StrSet.is_empty info.species
         then acc else info :: acc)
      tbl []
  in
  (cases, imports_lookup)

(* ------------------------------------------------------------------ *)
(* Output. *)

let identifier_display info =
  match info.identifier with
  | Some s -> s
  | None -> "(no test:identifier)"

(* ------------------------------------------------------------------ *)
(* Phase 1: closure + entailment check for PositiveEntailmentTest.

   For each test with premise P and conclusion C:
     closure   = owl_rl_closure_with_reflexivity(P, fuel=100)
     pass iff  every triple of C is matched in closure

   Match rule (relaxed):
     - If C_triple contains no bnodes: exact triple_eq against closure.
     - If C_triple contains one or more bnodes: structural match —
       predicate must equal; for each position (s, o), if the
       C-position is a bnode, ANY term (bnode or IRI) at that
       position in the closure matches; otherwise exact value
       match required.

   Why bnode-pattern matches IRI: the OWL test convention treats an
   anonymous-subject triple in the conclusion as existential
   ("there exists some resource with this predicate-object skeleton").
   A premise that names that resource (e.g.
   `<owl:Ontology rdf:about=''>` resolving to the document base) and a
   conclusion that leaves it anonymous (`<owl:Ontology/>` -> fresh
   bnode per RDF/XML §6.1.4) describe the same shape. Cluster K /
   WebOnt-imports-011 is the live instance:
     premise closure has <premises011> rdf:type owl:Ontology
     conclusion has    _:rdfxml_b0 rdf:type owl:Ontology
   Bnode-only structural match was too strict; generalising to "any
   term" honours the existential reading. See
   docs/designissues/2026-04-25-owl-imports-011-diagnosis.md (option 2)
   and docs/designissues/2026-05-07-owl2-rl-next-steps.md §K.

   This over-approximates (any term in the closure at a bnode
   position can satisfy any bnode in the conclusion — there's no
   consistency check across multiple bnode-containing triples). Full
   isomorphism deferred. Limitation is printed with the score.

   This is harness/test-scoring policy, not RDF/SPARQL semantics —
   the closure itself is F*-extracted (rule #15 boundary respected).
*)

let is_bnode_subject (s : RDF_Graph_Executable.subject) : bool =
  match s with RDF_Graph_Executable.S_BNode _ -> true | _ -> false

let is_bnode_term (t : RDF_Graph_Executable.rdf_term) : bool =
  match t with RDF_Graph_Executable.T_BNode _ -> true | _ -> false

let triple_has_bnode (t : RDF_Graph_Executable.triple) : bool =
  is_bnode_subject t.s || is_bnode_term t.o

(* Bnode pattern matches any term at this position (existential
   reading); non-bnode pattern requires exact value match. *)
let subject_matches
      (pat : RDF_Graph_Executable.subject)
      (sub : RDF_Graph_Executable.subject) : bool =
  match pat with
  | RDF_Graph_Executable.S_BNode _ -> let _ = sub in true
  | _ -> RDF_Graph_Executable.subject_eq pat sub

let object_matches
      (pat : RDF_Graph_Executable.rdf_term)
      (obj : RDF_Graph_Executable.rdf_term) : bool =
  match pat with
  | RDF_Graph_Executable.T_BNode _ -> let _ = obj in true
  | _ -> RDF_Graph_Executable.rdf_term_eq pat obj

let triple_matches
      (pat : RDF_Graph_Executable.triple)
      (t : RDF_Graph_Executable.triple) : bool =
  subject_matches pat.s t.s
  && pat.p = t.p
  && object_matches pat.o t.o

let conclusion_triple_in_closure
      (closure : RDF_Graph_Executable.rdf_graph)
      (pat : RDF_Graph_Executable.triple) : bool =
  if triple_has_bnode pat then
    List.exists (triple_matches pat) closure
  else
    List.exists (RDF_Graph_Executable.triple_eq pat) closure

type outcome =
  | Pass
  | Fail_conclusion_miss of RDF_Graph_Executable.triple
  (* NegativeEntailmentTest: closure entailed the assertion-non-conclusion. *)
  | Fail_unexpected_entailment
  (* ConsistencyTest: closure of an asserted-consistent premise contains
     an inconsistency marker (rdf:type owl:Nothing, sameAs+differentFrom
     conflict, disjoint-class instance, ...). *)
  | Fail_unexpected_inconsistency
  (* InconsistencyTest: closure of an asserted-inconsistent premise has
     no inconsistency marker — the engine couldn't see the contradiction. *)
  | Fail_unexpected_consistency
  | Fail_parse_premise
  | Fail_parse_conclusion
  | Fail_no_premise
  | Fail_no_conclusion
  (* Catalog entry provides only a functional-syntax premise
     (test:fsPremiseOntology, test:normativeSyntax FUNCTIONAL) with no
     test:rdfXmlPremiseOntology at all, AND that functional-syntax text
     is either absent or uses a construct beyond Parser_OWLFunctional's
     narrow grammar subset (2026-07-05 — see
     docs/designissues/2026-07-05-owl-functional-syntax-plan.md).
     Distinct from Fail_no_premise so the score reports an honest
     "unsupported input syntax" outcome instead of silently counting a
     syntax gap as a semantic failure. Counted outside the pass/fail
     denominator. *)
  | Skip_functional_syntax_only

let outcome_tag = function
  | Pass -> "PASS"
  | Fail_conclusion_miss _ -> "FAIL"
  | Fail_unexpected_entailment -> "FAIL/unexpected-entailment"
  | Fail_unexpected_inconsistency -> "FAIL/unexpected-inconsistency"
  | Fail_unexpected_consistency -> "FAIL/unexpected-consistency"
  | Fail_parse_premise -> "FAIL/parse-premise"
  | Fail_parse_conclusion -> "FAIL/parse-conclusion"
  | Fail_no_premise -> "FAIL/no-premise"
  | Fail_no_conclusion -> "FAIL/no-conclusion"
  | Skip_functional_syntax_only -> "SKIP/functional-syntax-only"

let fuel_100 : Prims.nat = Z.of_int 100

(* Temporary diagnostic hook (rule #11 territory: outcome plumbing only,
   no semantics). Set FACTOIDAL_OWL_DEBUG=<test:identifier> to dump the
   closure triples for that one test to stderr. Used for the 2026-07
   NegativeEntailmentTests/InconsistencyTests diagnosis; remove once the
   fixes land. Populated below (after format_triple is defined). *)
let debug_target = Sys.getenv_opt "FACTOIDAL_OWL_DEBUG"
let debug_dump_closure_ref : (test_case_info -> RDF_Graph_Executable.rdf_graph -> unit) ref =
  ref (fun _ _ -> ())
let debug_dump_closure info closure = !debug_dump_closure_ref info closure

(* Per-test SIGALRM cap (issue #263). The OWL-RL closure can blow up
   on some test premises (see issue #262). Without a per-test wall-
   clock cap, a single hung test takes the whole catalog down — we
   saw this on profile-RL.rdf and profile-EL.rdf (entire catalogs
   silently consume wall-clock indefinitely). The cap fires raise
   Exit; the surrounding (try _ with _ -> g) returns the un-closed
   graph, and the entailment check below records the test as a
   FAIL/no-closure rather than hanging the catalog. Override via
   FACTOIDAL_OWL_CAP_SEC env var. *)
let owl_closure_cap_seconds : float =
  match Sys.getenv_opt "FACTOIDAL_OWL_CAP_SEC" with
  | Some s -> (try float_of_string s with _ -> 30.0)
  | None -> 30.0

exception Owl_closure_timeout

let with_owl_cap (f : unit -> 'a) : 'a =
  let prev =
    Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Owl_closure_timeout))
  in
  let restore () =
    let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = 0.0 } in
    Sys.set_signal Sys.sigalrm prev
  in
  let _ = Unix.setitimer Unix.ITIMER_REAL
            { Unix.it_interval = 0.0; it_value = owl_closure_cap_seconds }
  in
  match f () with
  | v -> restore (); v
  | exception e -> restore (); raise e

(* Closure regime — Phase 2.3.
   Regime selects which closure operation runs over the premise:
     RL — owl_rl_closure_with_reflexivity (Datalog, sound for OWL 2 RL).
     DL — RL → Tableau.tableau_materialise → RL (sound + extends to a
          DL-sound subset including someValuesFrom / allValuesFrom /
          hasValue / intersectionOf / unionOf class-expression
          membership, mirroring w3c_runner.ml's OWL-Direct dispatch).

   For the profile-RL.rdf catalog the test conclusions are RL-shape, so
   DL agrees with RL; a few RL non-entailments may flip to DL
   entailments (NegativeEntailmentTest scores can drop slightly). For
   the type-* DL catalogs (semantics-direct.rdf, type-positive-
   entailment.rdf, etc.), DL is the right regime.

   Timeout fallback (2026-07-09): the DL path computes the RL closure
   FIRST, under its own SIGALRM cap, then attempts Tableau +
   re-closure under a second cap. On a Tableau cap-trip the fallback
   is the already-computed RL closure — NOT the raw un-closed graph —
   so a DL cap-trip can never score below the RL regime (DL result >=
   RL result on every non-capped-RL test). Before this change a hard
   test that capped under DL fell back to the raw premise and could
   flip an RL PASS to a DL FAIL (observed on WebOnt-someValuesFrom-003
   in type-positive-entailment.rdf) — a timeout artifact, not a
   Tableau (un)soundness disagreement. This is dispatch/fallback
   plumbing only; every closure it calls is F*-extracted (rule #15
   boundary respected). *)
type closure_regime = Regime_RL | Regime_DL

let regime : closure_regime ref = ref Regime_RL

(* --species: score the test:species facet (OWL 2 DL vs FULL) via the
   F*-extracted OWL2_SyntaxDL checker instead of the entailment /
   consistency phases. *)
let species_mode : bool ref = ref false

let regime_label () = match !regime with
  | Regime_RL -> "RL"
  | Regime_DL -> "DL"

(* Tableau refutation fuel (threaded budget inside the F*-extracted
   Tableau_Refute.tableau_consistent — total work is linear in it).
   Override via FACTOIDAL_OWL_REFUTE_FUEL. Plumbing only: the fuel
   value bounds work, it never changes a verdict's soundness (fuel
   exhaustion returns None = indeterminate). *)
let refute_fuel : Prims.nat =
  match Sys.getenv_opt "FACTOIDAL_OWL_REFUTE_FUEL" with
  | Some s -> (try Z.of_int (int_of_string s) with _ -> Z.of_int 20000)
  | None -> Z.of_int 20000

(* Refuter-specific SIGALRM cap, SMALLER than the closure cap: measured
   on type-inconsistency.rdf, every refutation the tableau finds at a
   20s cap it also finds at a 10s cap (clashes close fast; only
   searches that will END indeterminate grind on), while CONSISTENT
   tests pay the full cap as pure overhead — 346 ConsistencyTests x
   20s nearly tripled the type-consistency catalog wall time. Override
   via FACTOIDAL_OWL_REFUTE_CAP_SEC. *)
let refute_cap_seconds : float =
  match Sys.getenv_opt "FACTOIDAL_OWL_REFUTE_CAP_SEC" with
  | Some s -> (try float_of_string s with _ -> 5.0)
  | None -> 5.0

let with_refute_cap (f : unit -> 'a) : 'a =
  let prev =
    Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Owl_closure_timeout))
  in
  let restore () =
    let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = 0.0 } in
    Sys.set_signal Sys.sigalrm prev
  in
  let _ = Unix.setitimer Unix.ITIMER_REAL
            { Unix.it_interval = 0.0; it_value = refute_cap_seconds }
  in
  match f () with
  | v -> restore (); v
  | exception e -> restore (); raise e

(* DL-regime refutation check (2026-07-10): consult the F*-extracted
   clash-detecting tableau (Tableau_Refute.tableau_consistent) over the
   closed graph. `true` ONLY on `Some false` — a genuine clash on every
   branch (soundness argument per rule in Tableau.Refute.fst). Runs
   under its own (smaller) SIGALRM cap; a cap-trip or fuel exhaustion
   falls back to `false`, i.e. exactly the pre-existing RL
   `is_inconsistent` verdict — the DL result can never score below
   the RL baseline. RL regime: never consulted (RL scoring unchanged).
   Dispatch/fallback plumbing only — the satisfiability logic is
   F*-extracted (rule #15 boundary respected). *)
let dl_refutes (closure : RDF_Graph_Executable.rdf_graph) : bool =
  match !regime with
  | Regime_RL -> false
  | Regime_DL ->
    (try with_refute_cap (fun () ->
       match Tableau_Refute.tableau_consistent closure refute_fuel with
       | Some false -> true
       | _ -> false)
     with _ -> false)

(* is_inconsistent under the per-test cap (2026-07-10). The F* marker
   scan is worst-case cubic in closure size (its own header says so);
   with the Collection parser fix + DL materialisation the closures on
   a few WebOnt-description-logic consistency premises grew enough
   that the UNCAPPED scan ground for minutes and took the whole
   catalog down with it (observed on dl-661 in
   type-positive-entailment.rdf) — exactly the failure mode the
   per-test cap exists for (issue #263 / anti-pattern #17). On a
   cap-trip we report "no inconsistency detected": for a
   ConsistencyTest that is the expected verdict; for an
   InconsistencyTest it scores an honest FAIL (detection did not
   complete) rather than hanging. The SHORT (refute) cap is used: on
   every baseline-sized closure the marker scan completes in well
   under a second, so a scan still running at 5s is one of the
   blown-up closures that would not finish at 20s either — and the
   short cap keeps the heavy consistency premises from tripling the
   catalog wall time. Outcome plumbing only. *)
let capped_is_inconsistent (closure : RDF_Graph_Executable.rdf_graph) : bool =
  try with_refute_cap (fun () -> RDF_Graph_Executable.is_inconsistent closure)
  with _ -> false

(* apply_closure_stages returns BOTH the RL-base closure and the final
   (regime-dependent) closure. The split matters for SOUNDNESS of the
   refutation check (2026-07-10): Tableau.tableau_materialise's
   emissions are sound for the corpus's bnode-existential CONCLUSION
   MATCHING but not all are model-theoretically entailed — e.g. its
   is_member answers `Some true` for `max-0 P` when no P-successor is
   KNOWN (its own header documents the k=0 vacuous case), a
   closed-world reading, and it also mints existential witness EDGES.
   Feeding those into the clash-detecting refuter manufactured
   refutations of CONSISTENT premises (WebOnt-description-logic-662/
   665/667: a materialised max-0 membership meeting a real or witness
   successor). The refuter therefore consumes g_rl — author triples +
   RL-sound derivations only — while entailment/consistency marker
   scoring keeps the full DL closure exactly as before. *)
let apply_closure_stages (g : RDF_Graph_Executable.rdf_graph)
  : RDF_Graph_Executable.rdf_graph * RDF_Graph_Executable.rdf_graph =
  match !regime with
  | Regime_RL ->
    let c =
      (try with_owl_cap (fun () ->
         RDF_Graph_Executable.owl_rl_closure_with_reflexivity g fuel_100)
       with
       | Owl_closure_timeout ->
         Printf.eprintf "  [owl_closure_timeout] RL closure exceeded %.0fs cap; falling back to un-closed graph\n%!"
           owl_closure_cap_seconds;
         g
       | _ -> g)
    in
    (c, c)
  | Regime_DL ->
    (* Compute the RL closure first, under its own cap; this is exactly
       the Regime_RL result and is the DL timeout fallback so a Tableau
       cap-trip never scores below RL (DL result >= RL result). *)
    let g_rl =
      (try with_owl_cap (fun () ->
         RDF_Graph_Executable.owl_rl_closure_with_reflexivity g fuel_100)
       with
       | Owl_closure_timeout ->
         Printf.eprintf "  [owl_closure_timeout] DL RL-base closure exceeded %.0fs cap; falling back to un-closed graph\n%!"
           owl_closure_cap_seconds;
         g
       | _ -> g)
    in
    let g_dl =
      (try with_owl_cap (fun () ->
         let g2 = Tableau.tableau_materialise g_rl in
         RDF_Graph_Executable.owl_rl_closure_with_reflexivity g2 fuel_100)
       with
       | Owl_closure_timeout ->
         Printf.eprintf "  [owl_closure_timeout] DL tableau closure exceeded %.0fs cap; falling back to RL closure\n%!"
           owl_closure_cap_seconds;
         g_rl
       | _ -> g_rl)
    in
    (g_rl, g_dl)

let apply_closure (g : RDF_Graph_Executable.rdf_graph)
  : RDF_Graph_Executable.rdf_graph =
  snd (apply_closure_stages g)

(* test:semantics dispatch (2026-07-05) — see the constant definitions
   above and RDF.Graph.Executable.fst's owl_rule_named_equivClass_to_
   sameAs_mode header comment for the RDF semantics this encodes.

   owl_semantics_mode_for reduces a TestCase's test:semantics set to
   the F* dispatch key: RDF-Based ONLY (no DIRECT alongside it) means
   the RDF-Based reading is the one under test, so pass
   owl_semantics_rdf_based; every other case (DIRECT-only, both, or no
   test:semantics annotation at all) keeps the historical default
   (owl_semantics_direct — unconditional rule firing), matching this
   runner's behaviour before this dispatch existed. *)
let owl_semantics_mode_for (info : test_case_info) : string =
  if StrSet.mem test_semantics_rdf_based_iri info.semantics
     && not (StrSet.mem test_semantics_direct_iri info.semantics)
  then RDF_Graph_Executable.owl_semantics_rdf_based
  else RDF_Graph_Executable.owl_semantics_direct

let apply_closure_with_semantics
      (g : RDF_Graph_Executable.rdf_graph) (mode : string)
  : RDF_Graph_Executable.rdf_graph =
  match !regime with
  | Regime_RL ->
    (try with_owl_cap (fun () ->
       RDF_Graph_Executable.owl_rl_closure_with_reflexivity_mode g fuel_100 mode)
     with
     | Owl_closure_timeout ->
       Printf.eprintf "  [owl_closure_timeout] RL closure exceeded %.0fs cap; falling back to un-closed graph\n%!"
         owl_closure_cap_seconds;
       g
     | _ -> g)
  | Regime_DL ->
    (* Mode-aware sibling of apply_closure's DL branch: RL-mode closure
       first (the timeout fallback), then Tableau + RL-mode re-closure. *)
    let g_rl =
      (try with_owl_cap (fun () ->
         RDF_Graph_Executable.owl_rl_closure_with_reflexivity_mode g fuel_100 mode)
       with
       | Owl_closure_timeout ->
         Printf.eprintf "  [owl_closure_timeout] DL RL-base closure exceeded %.0fs cap; falling back to un-closed graph\n%!"
           owl_closure_cap_seconds;
         g
       | _ -> g)
    in
    (try with_owl_cap (fun () ->
       let g2 = Tableau.tableau_materialise g_rl in
       RDF_Graph_Executable.owl_rl_closure_with_reflexivity_mode g2 fuel_100 mode)
     with
     | Owl_closure_timeout ->
       Printf.eprintf "  [owl_closure_timeout] DL tableau closure exceeded %.0fs cap; falling back to RL closure\n%!"
         owl_closure_cap_seconds;
       g_rl
     | _ -> g_rl)

(* Parse and merge imported-ontology literals into the premise graph
   before closure. Each imports_lookup hit gives us an RDF/XML literal
   whose triples should be added to g_p, so the closure sees the union
   of declared + imported axioms (the test-harness analogue of
   owl:imports resolution; we never dereference URLs).

   Bnode renaming (2026-07-10): each imported document is parsed
   INDEPENDENTLY, so the parser's generated bnode ids (rdfxml_b0, ...)
   collide across documents — the union then carries chimera bnodes
   merging unrelated structures (WebOnt-miscellaneous-011: one bnode
   with consistent001's owl:minCardinality AND consistent002's
   owl:cardinality — a garbage restriction the refutation tableau then
   correctly finds inconsistent). Same defect + fix as the species
   registry's rename_doc_bnodes (see that comment); the renaming is
   F*-extracted (RDF_Graph_Executable.rename_triple_bnodes), this is
   plumbing. Prefix is per-import ordinal, so import docs can't
   collide with each other or with the authored premise. *)
(* Parsed-import memo (2026-07-10): the same imported document (e.g.
   the wine/food pair) is referenced by many tests, and each test's PE
   and Consistency phases both merged it — re-running the RDF/XML
   parse of a multi-thousand-triple literal EVERY time dominated the
   catalog wall time (minutes per import-bearing test). Parse each
   import IRI once per process; the bnode-rename prefix is derived
   from a stable per-IRI ordinal at first parse, so distinct imports
   never collide and repeat users get identical (correctly namespaced)
   triples. Pure I/O caching — no semantics. *)
let parsed_imports_cache : (string, triple list) Hashtbl.t = Hashtbl.create 64
let parsed_imports_count = ref 0

let parse_import_cached (import_iri : string) (lit : string) : triple list =
  match Hashtbl.find_opt parsed_imports_cache import_iri with
  | Some g -> g
  | None ->
    let src = expand_catalog_entities lit in
    (* Use the import-link IRI as the parser base. The imported
       document typically declares its own xml:base which overrides
       this; the fallback only matters when it does not. *)
    let g0 =
      (try Parser_RDFXML.parse_rdfxml_with_base import_iri src
       with _ -> []) in
    incr parsed_imports_count;
    let prefix = Printf.sprintf "impm%d_" !parsed_imports_count in
    let g = List.map (RDF_Graph_Executable.rename_triple_bnodes prefix) g0 in
    Hashtbl.replace parsed_imports_cache import_iri g;
    g

let load_imports_into_premise
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t)
      (g_p : triple list) : triple list =
  StrSet.fold
    (fun import_iri acc ->
       match Hashtbl.find_opt imports_lookup import_iri with
       | None -> acc
       | Some lit -> parse_import_cached import_iri lit @ acc)
    info.imports
    g_p

(* OWL 2 Functional Syntax path for PositiveEntailmentTest (2026-07-05).
   See docs/designissues/2026-07-05-owl-functional-syntax-plan.md.
   `Parser_OWLFunctional.parse_functional_syntax` returns `None` on any
   construct outside its narrow grammar subset (clean parse failure,
   rule: no fixture-string special-casing) — that case falls back to
   the pre-existing Skip_functional_syntax_only in the caller, exactly
   preserving today's honest-skip behaviour for fixtures that use more
   of Functional Syntax than this parser covers. `Some outcome` means
   the ontology parsed in-subset and was scored (PASS or FAIL) — a
   parse success is never silently downgraded back to a skip, per
   anti-pattern #3 (misleading test scores). *)
let run_positive_entailment_functional_syntax
      (fs_p_lex : string) (fs_c_lex : string) : outcome option =
  match (try Parser_OWLFunctional.parse_functional_syntax fs_p_lex with _ -> None) with
  | None -> None
  | Some g_p ->
    match (try Parser_OWLFunctional.parse_functional_syntax fs_c_lex with _ -> None) with
    | None -> None
    | Some g_c ->
      let closure = try apply_closure g_p with _ -> g_p in
      let rec check = function
        | [] -> Pass
        | t :: rest ->
          if conclusion_triple_in_closure closure t
          then check rest
          else Fail_conclusion_miss t
      in
      Some (check g_c)

let run_positive_entailment
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t) : outcome =
  Printf.eprintf "  [pe-running] %s\n%!"
    (match info.identifier with Some id -> id | None -> info.iri);
  match info.premise, info.conclusion with
  | None, _ ->
    (match info.fs_premise, info.fs_conclusion with
     | Some fs_p_lex, Some fs_c_lex ->
       (match run_positive_entailment_functional_syntax fs_p_lex fs_c_lex with
        | Some outcome -> outcome
        | None ->
          if StrSet.mem test_syntax_functional info.normative_syntax
          then Skip_functional_syntax_only
          else Fail_no_premise)
     | _ ->
       if StrSet.mem test_syntax_functional info.normative_syntax
       then Skip_functional_syntax_only
       else Fail_no_premise)
  | _, None -> Fail_no_conclusion
  | Some p_lex, Some c_lex ->
    let p_src = expand_catalog_entities p_lex in
    let c_src = expand_catalog_entities c_lex in
    let base = info.iri in
    let g_p_authored =
      try Parser_RDFXML.parse_rdfxml_with_base base p_src
      with _ -> [] in
    let g_p = load_imports_into_premise info imports_lookup g_p_authored in
    let g_c =
      try Parser_RDFXML.parse_rdfxml_with_base base c_src
      with _ -> [] in
    if g_p = [] then Fail_parse_premise
    else if g_c = [] then Fail_parse_conclusion
    else begin
      let closure =
        try apply_closure g_p
        with _ -> g_p in
      let rec check = function
        | [] -> Pass
        | t :: rest ->
          if conclusion_triple_in_closure closure t
          then check rest
          else Fail_conclusion_miss t
      in
      check g_c
    end

(* NegativeEntailmentTest: the conclusion is asserted to NOT be a
   logical consequence of the premise. Pass iff at least one
   conclusion triple is missing from the closure (= conclusion not
   entailed). If every conclusion triple IS in the closure, the
   negative-entailment assertion is refuted and the test fails.

   Same closure path as PositiveEntailmentTest (owl_rl_closure_with_
   reflexivity), except the closure's semantics mode is now dispatched
   per-test from the catalog's test:semantics annotation (see
   owl_semantics_mode_for above) rather than always using the
   historical default. RL-only — to certify a NEGATIVE entailment
   under a stronger regime (DL/EL/QL), the closure must be COMPLETE
   for that regime. RL closure is sound but incomplete for full DL, so
   a "missing triple under RL closure" doesn't necessarily mean
   "non-entailed under DL". For the profile-RL.rdf catalog, the
   tests are scoped to RL semantics, so this is exact. For DL
   catalogs the user should expect false-positives until tableau-
   based negation is wired (Phase 3). *)
let run_negative_entailment
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t) : outcome =
  match info.premise, info.conclusion with
  | None, _ -> Fail_no_premise
  | _, None -> Fail_no_conclusion
  | Some p_lex, Some c_lex ->
    let p_src = expand_catalog_entities p_lex in
    let c_src = expand_catalog_entities c_lex in
    let base = info.iri in
    let g_p_authored =
      try Parser_RDFXML.parse_rdfxml_with_base base p_src
      with _ -> [] in
    let g_p = load_imports_into_premise info imports_lookup g_p_authored in
    let g_c =
      try Parser_RDFXML.parse_rdfxml_with_base base c_src
      with _ -> [] in
    if g_p = [] then Fail_parse_premise
    else if g_c = [] then Fail_parse_conclusion
    else begin
      let sem_mode = owl_semantics_mode_for info in
      let closure =
        try apply_closure_with_semantics g_p sem_mode
        with _ -> g_p in
      debug_dump_closure info closure;
      let any_missing =
        List.exists
          (fun t -> not (conclusion_triple_in_closure closure t))
          g_c
      in
      if any_missing then Pass
      else Fail_unexpected_entailment
    end

(* ConsistencyTest: premise is asserted CONSISTENT. Pass iff closure has
   no inconsistency marker (per F*'s is_inconsistent in
   RDF.Graph.Executable: no rdf:type owl:Nothing, no sameAs/differentFrom
   conflict, no disjoint-class instance). No conclusion expected.

   2026-07-05: New-Feature-ObjectPropertyChain-BJP-002 is a
   ConsistencyTest whose ONLY premise serialization is functional
   syntax (test:fsPremiseOntology / test:normativeSyntax=FUNCTIONAL,
   no test:rdfXmlPremiseOntology). PE and InconsistencyTest already
   attempt Parser_OWLFunctional on the fs_premise literal before
   falling back to Skip_functional_syntax_only; this runner was
   missing that attempt, so the same catalog entry scored
   FAIL/no-premise here while PASSing (via the FS-parser path) in the
   PE run — an inconsistent (and per anti-pattern #3, misleading)
   harness verdict on one test across three runs. Below,
   run_consistency_test_functional_syntax completes that wiring: the
   premise now parses via Parser_OWLFunctional and is scored via
   is_inconsistent exactly like the rdfXml path, so BJP-002 now scores
   Pass (not skip) here too, matching the PE/Inconsistency runs. *)
(* OWL 2 Functional Syntax path for ConsistencyTest (2026-07-05).
   Same contract as run_inconsistency_test_functional_syntax: `None`
   means the premise used a construct outside Parser_OWLFunctional's
   subset (falls back to the honest skip in the caller); `Some outcome`
   means it parsed in-subset and was scored via is_inconsistent, same
   as the rdfXml path below. Completes the wave-9 functional-syntax
   wiring for the ConsistencyTest runner — PE and Inconsistency got
   this path already; BJP-002's ConsistencyTest sibling was the one
   remaining FS skip. *)
let run_consistency_test_functional_syntax (fs_p_lex : string) : outcome option =
  match (try Parser_OWLFunctional.parse_functional_syntax fs_p_lex with _ -> None) with
  | None -> None
  | Some g_p ->
    let (closure_rl, closure) = try apply_closure_stages g_p with _ -> (g_p, g_p) in
    if capped_is_inconsistent closure || dl_refutes closure_rl
    then Some Fail_unexpected_inconsistency
    else Some Pass

let run_consistency_test
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t) : outcome =
  (* Flushed progress marker (same pattern as [pe-running]): keeps the
     log live under block-buffered stdout redirection so a wall-clock
     kill doesn't lose the whole phase's output. *)
  Printf.eprintf "  [cons-running] %s\n%!"
    (match info.identifier with Some id -> id | None -> info.iri);
  match info.premise with
  | None ->
    (match info.fs_premise with
     | Some fs_p_lex ->
       (match run_consistency_test_functional_syntax fs_p_lex with
        | Some outcome -> outcome
        | None ->
          if StrSet.mem test_syntax_functional info.normative_syntax
          then Skip_functional_syntax_only
          else Fail_no_premise)
     | None ->
       if StrSet.mem test_syntax_functional info.normative_syntax
       then Skip_functional_syntax_only
       else Fail_no_premise)
  | Some p_lex ->
    let p_src = expand_catalog_entities p_lex in
    let base = info.iri in
    let g_p_authored =
      try Parser_RDFXML.parse_rdfxml_with_base base p_src
      with _ -> [] in
    let g_p = load_imports_into_premise info imports_lookup g_p_authored in
    if g_p = [] then Fail_parse_premise
    else begin
      let (closure_rl, closure) =
        try apply_closure_stages g_p
        with _ -> (g_p, g_p) in
      (* DL regime additionally consults the clash-detecting tableau —
         the soundness gate for the whole refutation feature: a
         `Some false` here on a test asserted CONSISTENT is a soundness
         bug in Tableau.Refute.fst, never something to paper over. The
         refuter reads the RL-BASE closure (see apply_closure_stages'
         banner) — materialise's corpus-oriented emissions are not all
         model-theoretically entailed and must not feed a refutation. *)
      if capped_is_inconsistent closure || dl_refutes closure_rl
      then Fail_unexpected_inconsistency
      else Pass
    end

(* OWL 2 Functional Syntax path for InconsistencyTest (2026-07-05).
   Same contract as run_positive_entailment_functional_syntax: `None`
   means the premise used a construct outside Parser_OWLFunctional's
   subset (falls back to the honest skip in the caller); `Some outcome`
   means it parsed in-subset and was scored via the same is_inconsistent
   predicate the rdfXml path already uses. *)
let run_inconsistency_test_functional_syntax (fs_p_lex : string) : outcome option =
  match (try Parser_OWLFunctional.parse_functional_syntax fs_p_lex with _ -> None) with
  | None -> None
  | Some g_p ->
    let (closure_rl, closure) = try apply_closure_stages g_p with _ -> (g_p, g_p) in
    if capped_is_inconsistent closure || dl_refutes closure_rl
    then Some Pass
    else Some Fail_unexpected_consistency

(* InconsistencyTest: premise is asserted INCONSISTENT. Pass iff closure
   contains an inconsistency marker.

   Some catalog entries (functionality-clash, string-integer-clash,
   "Plus and Minus Zero are Distinct") provide only test:fsPremiseOntology
   (OWL 2 Functional Syntax) with no test:rdfXmlPremiseOntology. As of
   2026-07-05 these are attempted via Parser_OWLFunctional (see the
   design doc); only a premise that uses a construct beyond that
   parser's narrow subset still falls back to Skip_functional_syntax_only. *)
let run_inconsistency_test
      (info : test_case_info)
      (imports_lookup : (string, string) Hashtbl.t) : outcome =
  Printf.eprintf "  [inc-running] %s\n%!"
    (match info.identifier with Some id -> id | None -> info.iri);
  match info.premise with
  | None ->
    (match info.fs_premise with
     | Some fs_p_lex ->
       (match run_inconsistency_test_functional_syntax fs_p_lex with
        | Some outcome -> outcome
        | None ->
          if StrSet.mem test_syntax_functional info.normative_syntax
          then Skip_functional_syntax_only
          else Fail_no_premise)
     | None ->
       if StrSet.mem test_syntax_functional info.normative_syntax
       then Skip_functional_syntax_only
       else Fail_no_premise)
  | Some p_lex ->
    let p_src = expand_catalog_entities p_lex in
    let base = info.iri in
    let g_p_authored =
      try Parser_RDFXML.parse_rdfxml_with_base base p_src
      with _ -> [] in
    let g_p = load_imports_into_premise info imports_lookup g_p_authored in
    if g_p = [] then Fail_parse_premise
    else begin
      let (closure_rl, closure) =
        try apply_closure_stages g_p
        with _ -> (g_p, g_p) in
      debug_dump_closure info closure;
      (* DL regime: RL inconsistency markers first (cheap), then the
         F*-extracted clash-detecting tableau (Tableau_Refute) for the
         constructs Datalog closure cannot refute — complement/
         disjunction/cardinality clashes. RL regime is unchanged. The
         refuter reads the RL-BASE closure (apply_closure_stages'
         banner: materialise emissions are conclusion-matching-sound,
         not all entailment-sound, and must not feed a refutation). *)
      if capped_is_inconsistent closure || dl_refutes closure_rl
      then Pass
      else Fail_unexpected_consistency
    end

let format_subject = function
  | RDF_Graph_Executable.S_IRI i -> "<" ^ i ^ ">"
  | RDF_Graph_Executable.S_BNode b -> "_:" ^ b

let format_object = function
  | RDF_Graph_Executable.T_IRI i -> "<" ^ i ^ ">"
  | RDF_Graph_Executable.T_BNode b -> "_:" ^ b
  | RDF_Graph_Executable.T_Literal l ->
    Printf.sprintf "\"%s\"^^<%s>" l.lexical_form l.datatype

let format_triple (t : RDF_Graph_Executable.triple) : string =
  Printf.sprintf "%s <%s> %s"
    (format_subject t.s) t.p (format_object t.o)

let () =
  debug_dump_closure_ref :=
    (fun (info : test_case_info) (closure : RDF_Graph_Executable.rdf_graph) ->
       match debug_target, info.identifier with
       | Some want, Some got when want = got ->
         Printf.eprintf "  [debug %s] closure has %d triples\n%!" got (List.length closure);
         List.iter (fun t -> Printf.eprintf "    %s\n%!" (format_triple t)) closure
       | _ -> ())

let print_outcome verbose info outcome =
  let tag = outcome_tag outcome in
  let id = identifier_display info in
  Printf.printf "  %s  %s\n" tag id;
  (match outcome with
   | Skip_functional_syntax_only ->
     (* Reason printed unconditionally (not gated on -v): a SKIP that
        silently omits its cause is exactly the "misleading test score"
        anti-pattern #3 warns about. *)
     Printf.printf
       "      reason: unsupported input syntax — catalog entry provides only test:fsPremiseOntology (OWL 2 Functional Syntax) with test:normativeSyntax FUNCTIONAL, and either no fs premise/conclusion literal is present or it uses Functional-Syntax constructs beyond Parser_OWLFunctional's narrow subset (Prefix/Ontology/Declaration + ~6 axiom forms; see docs/designissues/2026-07-05-owl-functional-syntax-plan.md)\n"
   | _ -> ());
  if verbose then begin
    match outcome with
    | Fail_conclusion_miss t ->
      Printf.printf "      missing conclusion triple: %s\n" (format_triple t)
    | _ -> ()
  end

(* ------------------------------------------------------------------ *)
(* Species mode (--species, 2026-07-10): OWL 2 DL vs FULL species
   identification for the syntax-dl catalog (and any catalog carrying
   test:species annotations). The verdict comes entirely from the
   F*-extracted OWL2_SyntaxDL.species_is_dl; this section is I/O glue
   per rule #11 — literal decoding, DOCTYPE entity expansion (textual,
   same pattern as expand_catalog_entities above), owl:imports
   resolution against the catalog-provided input documents, and score
   printing.

   Species covers ALL documents of a test case: two premise-identical
   cases (WebOnt-I5.5-005 DL vs WebOnt-I5.5-006 FULL) differ only in
   their conclusion documents, so the premise AND the conclusion (or
   non-conclusion) graphs are handed to the checker. *)

(* Some premise literals carry their own DOCTYPE with custom entities
   (&vin;, &food; in WebOnt-miscellaneous-001). Expand any locally
   declared <!ENTITY name "value"> before stripping the DOCTYPE —
   pure textual substitution, no RDF semantics. *)
let expand_local_entities (s : string) : string =
  let ent_re =
    Str.regexp "<!ENTITY[ \t\r\n]+\\([A-Za-z_][A-Za-z0-9_.-]*\\)[ \t\r\n]+[\"']\\([^\"']*\\)[\"']" in
  let rec collect start acc =
    match find_opt ent_re s start with
    | None -> acc
    | Some i ->
      let name = Str.matched_group 1 s in
      let value = Str.matched_group 2 s in
      collect (i + 1) ((("&" ^ name ^ ";"), value) :: acc)
  in
  let ents = collect 0 [] in
  List.fold_left
    (fun acc (ent, repl) ->
       Str.global_replace (Str.regexp_string ent) repl acc)
    s ents

(* Parse one ontology-document literal. Returns Some triples on a
   successful parse (an EMPTY document is a legitimate parse — several
   rdfbased-sem-* premises are just <rdf:RDF/>), None if the parser
   raises. *)
let parse_doc_literal (base : string) (lex : string) : triple list option =
  let src = expand_catalog_entities lex in
  let src = expand_local_entities src in
  let src = strip_doctype src in
  try Some (Parser_RDFXML.parse_rdfxml_with_base base src)
  with _ -> None

(* Registry of catalog-provided imported documents, keyed by every IRI
   they advertise: IRI subjects typed owl:Ontology, plus the xml:base
   attribute (scraped textually — imported documents such as
   imports013 have an xml:base but no header). owl:imports objects are
   resolved against these keys. *)
let owl_ontology_iri = "http://www.w3.org/2002/07/owl#Ontology"
let owl_imports_iri  = "http://www.w3.org/2002/07/owl#imports"

let xml_base_of (lex : string) : string option =
  let re = Str.regexp "xml:base[ \t\r\n]*=[ \t\r\n]*[\"']\\([^\"']*\\)[\"']" in
  match find_opt re lex 0 with
  | None -> None
  | Some _ -> Some (Str.matched_group 1 lex)

(* Each document is parsed independently, so the parser's generated
   bnode ids (rdfxml_b0, ...) collide across documents; a union of two
   docs then has e.g. two rdf:first triples on "one" list node — a
   spurious malformed-list verdict. Rename each doc's bnodes with a
   doc-unique prefix (F*-extracted rename_triple_bnodes) before any
   union. *)
let rename_doc_bnodes (prefix : string) (g : triple list) : triple list =
  List.map (RDF_Graph_Executable.rename_triple_bnodes prefix) g

let species_input_registry
    (imports_lookup : (string, string) Hashtbl.t)
  : (string, triple list) Hashtbl.t =
  let reg : (string, triple list) Hashtbl.t = Hashtbl.create 32 in
  let doc_n = ref 0 in
  Hashtbl.iter
    (fun node_iri lex ->
       match parse_doc_literal node_iri lex with
       | None -> ()
       | Some g0 ->
         incr doc_n;
         let g = rename_doc_bnodes (Printf.sprintf "imp%d_" !doc_n) g0 in
         let keys = ref [node_iri] in
         List.iter
           (fun (t : triple) ->
              if t.p = rdf_type_iri
                 && (match t.o with
                     | RDF_Graph_Executable.T_IRI i -> i = owl_ontology_iri
                     | _ -> false)
              then (match t.s with
                    | RDF_Graph_Executable.S_IRI i -> keys := i :: !keys
                    | _ -> ()))
           g;
         (match xml_base_of lex with
          | Some b -> keys := b :: !keys
          | None -> ());
         List.iter (fun k -> Hashtbl.replace reg k g) !keys)
    imports_lookup;
  reg

(* Transitively merge the owl:imports closure of g, resolving each
   import IRI against the registry. Cycle-safe via the seen set. *)
let rec resolve_species_imports
    (reg : (string, triple list) Hashtbl.t)
    (g : triple list) (seen : StrSet.t) : triple list =
  let targets =
    List.filter_map
      (fun (t : triple) ->
         if t.p = owl_imports_iri then
           (match t.o with
            | RDF_Graph_Executable.T_IRI i
              when (not (StrSet.mem i seen)) && Hashtbl.mem reg i -> Some i
            | _ -> None)
         else None)
      g
    |> List.sort_uniq compare
  in
  match targets with
  | [] -> g
  | _ ->
    let seen = List.fold_left (fun s i -> StrSet.add i s) seen targets in
    let g = List.fold_left (fun acc i -> acc @ Hashtbl.find reg i) g targets in
    resolve_species_imports reg g seen

type species_outcome =
  | Sp_scored of bool * bool * string list
      (* verdict_is_dl, expected_is_dl, violations (for the log) *)
  | Sp_fail_parse of bool  (* expected_is_dl; premise/conclusion unparseable *)
  | Sp_skip_functional     (* functional-syntax-only, outside the FS subset *)

let run_species_case
    (info : test_case_info)
    (reg : (string, triple list) Hashtbl.t) : species_outcome =
  let expected_dl = StrSet.mem test_species_dl_iri info.species in
  let premise_graph =
    match info.premise with
    | Some lex -> parse_doc_literal info.iri lex
    | None ->
      (* imports-005..013 style: the case's own document arrives as
         test:rdfXmlInputOntology (keyed by the case IRI in the
         imports lookup used to build reg). *)
      Hashtbl.find_opt reg info.iri
  in
  match premise_graph with
  | None when info.premise <> None ->
    (* An RDF/XML premise EXISTS but the parser raised on it — an
       honest FAIL, never masked as a functional-syntax skip
       (anti-pattern #3). *)
    Sp_fail_parse expected_dl
  | None ->
    (* No RDF/XML premise: try the Functional Syntax path. *)
    (match info.fs_premise with
     | Some fs_lex ->
       (match (try Parser_OWLFunctional.parse_functional_syntax fs_lex
               with _ -> None) with
        | Some g_p ->
          let (has_c, g_u) =
            (match info.fs_conclusion with
             | Some fs_c ->
               (match (try Parser_OWLFunctional.parse_functional_syntax fs_c
                       with _ -> None) with
                | Some g_c -> (true, g_p @ rename_doc_bnodes "c_" g_c)
                | None -> (false, []))
             | None -> (false, []))
          in
          let verdict = OWL2_SyntaxDL.species_is_dl_functional g_p has_c g_u in
          let viols =
            if verdict then []
            else OWL2_SyntaxDL.species_violations_functional g_p has_c g_u in
          Sp_scored (verdict, expected_dl, viols)
        | None ->
          if StrSet.mem test_syntax_functional info.normative_syntax
          then Sp_skip_functional
          else Sp_fail_parse expected_dl)
     | None -> Sp_fail_parse expected_dl)
  | Some p_doc ->
    let p_merged = resolve_species_imports reg p_doc StrSet.empty in
    let (has_c, c_doc) =
      match info.conclusion with
      | None -> (false, [])
      | Some c_lex ->
        (match parse_doc_literal info.iri c_lex with
         (* Doc-unique bnode prefix so the P∪C union can't conflate
            premise and conclusion bnodes (see rename_doc_bnodes). *)
         | Some g -> (true, rename_doc_bnodes "c_" g)
         | None -> (false, []))
    in
    let u_merged =
      if has_c
      then resolve_species_imports reg (p_doc @ c_doc) StrSet.empty
      else p_merged
    in
    let verdict =
      OWL2_SyntaxDL.species_is_dl p_doc p_merged has_c c_doc u_merged in
    let viols =
      if verdict then []
      else OWL2_SyntaxDL.species_violations p_doc p_merged has_c c_doc u_merged in
    Sp_scored (verdict, expected_dl, viols)

let species_label (is_dl : bool) = if is_dl then "DL" else "FULL"

let run_species_catalog (tests : test_case_info list)
    (imports_lookup : (string, string) Hashtbl.t) : unit =
  let sp_tests =
    List.filter (fun info -> not (StrSet.is_empty info.species)) tests in
  let k = List.length sp_tests in
  Printf.printf
    "Running %d species-annotated test case(s) through OWL2_SyntaxDL.species_is_dl (F*-extracted)...\n" k;
  let reg = species_input_registry imports_lookup in
  let t0 = Unix.gettimeofday () in
  let outcomes =
    List.map (fun info -> (info, run_species_case info reg)) sp_tests in
  let t1 = Unix.gettimeofday () in
  let passes = ref 0 and fails = ref 0 and skips = ref 0 in
  List.iter
    (fun (info, o) ->
       let id = identifier_display info in
       match o with
       | Sp_scored (verdict, expected, viols) ->
         if verdict = expected then begin
           incr passes;
           Printf.printf "  PASS: %s [species] verdict=%s expected=%s\n"
             id (species_label verdict) (species_label expected)
         end else begin
           incr fails;
           Printf.printf "  FAIL: %s [species] verdict=%s expected=%s\n"
             id (species_label verdict) (species_label expected);
           List.iteri
             (fun i v -> if i < 5 then Printf.printf "      violation: %s\n" v)
             viols
         end
       | Sp_fail_parse expected ->
         incr fails;
         Printf.printf
           "  FAIL: %s [species] verdict=(premise/conclusion parse failure) expected=%s\n"
           id (species_label expected)
       | Sp_skip_functional ->
         incr skips;
         Printf.printf "  SKIP: %s [species] functional-syntax-only premise outside Parser_OWLFunctional's subset\n"
           id)
    outcomes;
  Printf.printf "\n";
  Printf.printf
    "OWL2-DL SpeciesTests: %d pass, %d fail (out of %d), %d skipped (functional-syntax-only) in %.2fs\n"
    !passes !fails (!passes + !fails) !skips (t1 -. t0)

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
     \  ./owl_runner <catalog.rdf> --species\n\
     \                                Score the test:species facet (OWL 2 DL vs FULL)\n\
     \                                via the F*-extracted OWL2_SyntaxDL checker\n\
     \  ./owl_runner --help           Show this help\n\
     \n\
     Status: Phase 0 skeleton — reads manifest, prints per-test identifier\n\
     and types, emits final count. Does NOT run any reasoning yet.\n\
     See docs/designissues/2026-04-24-owl-test-harness.md.\n"

(* ------------------------------------------------------------------ *)
(* Main. *)

let run_catalog ?(verbose=false) path =
  Printf.printf "OWL 2 test catalog: %s\n" path;
  let t0 = Unix.gettimeofday () in
  let graph = parse_catalog path in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  parsed %d triples in %.2fs\n"
    (List.length graph) (t1 -. t0);
  let (tests, imports_lookup) = build_index graph in
  let key info = match info.identifier with
    | Some s -> s
    | None -> info.iri in
  let tests = List.sort (fun a b -> compare (key a) (key b)) tests in
  (* Per-type tally — orientation for the human reader. *)
  let tally name =
    let iri = test_ns ^ name in
    List.fold_left
      (fun acc info -> if StrSet.mem iri info.types then acc + 1 else acc)
      0 tests
  in
  let n = List.length tests in
  Printf.printf "Totals: %d test cases\n" n;
  Printf.printf "  PositiveEntailmentTest:    %d\n" (tally "PositiveEntailmentTest");
  Printf.printf "  NegativeEntailmentTest:    %d\n" (tally "NegativeEntailmentTest");
  Printf.printf "  ConsistencyTest:           %d\n" (tally "ConsistencyTest");
  Printf.printf "  InconsistencyTest:         %d\n" (tally "InconsistencyTest");
  Printf.printf "  ProfileIdentificationTest: %d\n" (tally "ProfileIdentificationTest");
  Printf.printf "\n";

  (* Species mode: score test:species (DL vs FULL) via the F*-extracted
     OWL2_SyntaxDL checker and nothing else — no closure, no
     entailment. Selected with --species. *)
  if !species_mode then
    run_species_catalog tests imports_lookup
  else begin

  (* Phase 1: score every PositiveEntailmentTest. *)
  let pe_tests =
    List.filter
      (fun info -> StrSet.mem pos_entailment_iri info.types)
      tests
  in
  let k = List.length pe_tests in
  Printf.printf "Running %d PositiveEntailmentTest(s) through owl_rl_closure_with_reflexivity (fuel=100)...\n" k;
  let t_run0 = Unix.gettimeofday () in
  let outcomes = List.map (fun info -> (info, run_positive_entailment info imports_lookup)) pe_tests in
  let t_run1 = Unix.gettimeofday () in
  List.iter (fun (info, outcome) -> print_outcome verbose info outcome) outcomes;
  let passes =
    List.fold_left
      (fun acc (_, o) -> match o with Pass -> acc + 1 | _ -> acc)
      0 outcomes
  in
  let skips =
    List.fold_left
      (fun acc (_, o) -> match o with Skip_functional_syntax_only -> acc + 1 | _ -> acc)
      0 outcomes
  in
  let scored = k - skips in
  let fails = scored - passes in
  Printf.printf "\n";
  Printf.printf "Profile-RL PositiveEntailmentTests: %d pass, %d fail (out of %d RDF/XML tests), %d skipped (functional-syntax-only) in %.2fs\n"
    passes fails scored skips (t_run1 -. t_run0);
  Printf.printf "  (bnode pattern matches any term at the position; full isomorphism deferred — see docs/designissues/2026-04-24-owl-runner-phase1.md)\n";

  (* Phase 2.1: NegativeEntailmentTest. Same closure path as Phase 1
     but inverts the pass condition. RL-sound; NOT complete for DL —
     a Phase 3 task. *)
  let ne_tests =
    List.filter
      (fun info -> StrSet.mem neg_entailment_iri info.types)
      tests
  in
  let nk = List.length ne_tests in
  if nk > 0 then begin
    Printf.printf "\n";
    Printf.printf "Running %d NegativeEntailmentTest(s) through owl_rl_closure_with_reflexivity (fuel=100)...\n" nk;
    let t_neg0 = Unix.gettimeofday () in
    let n_outcomes = List.map (fun info -> (info, run_negative_entailment info imports_lookup)) ne_tests in
    let t_neg1 = Unix.gettimeofday () in
    List.iter (fun (info, outcome) -> print_outcome verbose info outcome) n_outcomes;
    let n_passes =
      List.fold_left
        (fun acc (_, o) -> match o with Pass -> acc + 1 | _ -> acc)
        0 n_outcomes
    in
    let n_fails = nk - n_passes in
    Printf.printf "\n";
    Printf.printf "Profile-RL NegativeEntailmentTests: %d pass, %d fail (out of %d) in %.2fs\n"
      n_passes n_fails nk (t_neg1 -. t_neg0)
  end;

  (* Phase 2.2: ConsistencyTest + InconsistencyTest. Both use the
     F* `is_inconsistent` predicate over the saturated closure.
     ConsistencyTest passes iff is_inconsistent = false; Inconsistency
     reverses the condition. *)
  let cons_tests =
    List.filter (fun info -> StrSet.mem consistency_iri info.types) tests
  in
  let ck = List.length cons_tests in
  if ck > 0 then begin
    Printf.printf "\n";
    Printf.printf "Running %d ConsistencyTest(s) through is_inconsistent (closure fuel=100)...\n" ck;
    let t_cons0 = Unix.gettimeofday () in
    let c_outcomes = List.map (fun info -> (info, run_consistency_test info imports_lookup)) cons_tests in
    let t_cons1 = Unix.gettimeofday () in
    List.iter (fun (info, outcome) -> print_outcome verbose info outcome) c_outcomes;
    let c_passes =
      List.fold_left
        (fun acc (_, o) -> match o with Pass -> acc + 1 | _ -> acc)
        0 c_outcomes
    in
    let c_skips =
      List.fold_left
        (fun acc (_, o) -> match o with Skip_functional_syntax_only -> acc + 1 | _ -> acc)
        0 c_outcomes
    in
    let c_scored = ck - c_skips in
    let c_fails = c_scored - c_passes in
    Printf.printf "\n";
    Printf.printf "Profile-RL ConsistencyTests: %d pass, %d fail (out of %d), %d skipped (functional-syntax-only) in %.2fs\n"
      c_passes c_fails c_scored c_skips (t_cons1 -. t_cons0)
  end;

  let inc_tests =
    List.filter (fun info -> StrSet.mem inconsistency_iri info.types) tests
  in
  let ik = List.length inc_tests in
  if ik > 0 then begin
    Printf.printf "\n";
    Printf.printf "Running %d InconsistencyTest(s) through is_inconsistent (closure fuel=100)...\n" ik;
    let t_inc0 = Unix.gettimeofday () in
    let i_outcomes = List.map (fun info -> (info, run_inconsistency_test info imports_lookup)) inc_tests in
    let t_inc1 = Unix.gettimeofday () in
    List.iter (fun (info, outcome) -> print_outcome verbose info outcome) i_outcomes;
    let i_passes =
      List.fold_left
        (fun acc (_, o) -> match o with Pass -> acc + 1 | _ -> acc)
        0 i_outcomes
    in
    let i_skips =
      List.fold_left
        (fun acc (_, o) -> match o with Skip_functional_syntax_only -> acc + 1 | _ -> acc)
        0 i_outcomes
    in
    let i_scored = ik - i_skips in
    let i_fails = i_scored - i_passes in
    Printf.printf "\n";
    Printf.printf "Profile-RL InconsistencyTests: %d pass, %d fail (out of %d), %d skipped (functional-syntax-only) in %.2fs\n"
      i_passes i_fails i_scored i_skips (t_inc1 -. t_inc0)
  end
  end (* not species_mode *)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let path = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: _ -> list_catalogs (); exit 0
    | "--species" :: rest -> species_mode := true; loop rest
    | "--regime" :: r :: rest ->
      (match String.lowercase_ascii r with
       | "rl" -> regime := Regime_RL
       | "dl" -> regime := Regime_DL
       | _ ->
         Printf.eprintf "owl_runner: --regime expects rl|dl, got %S\n" r;
         exit 2);
      loop rest
    | p :: rest when !path = None -> path := Some p; loop rest
    | _ ->
      Printf.eprintf "owl_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  Printf.printf "Closure regime: %s\n" (regime_label ());
  let catalog = match !path with
    | Some p -> p
    | None -> default_catalog ()
  in
  run_catalog ~verbose:!verbose catalog
