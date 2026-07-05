module RML.Mapping

// Stage 1 of the RML program plan
// (docs/designissues/2026-07-05-rml-program-plan.md): the RML-Core
// mapping-document AST plus a Turtle-graph decoder. Deliberately
// inert — no evaluation function here (that is RML.Eval, Stage 2+).
// This module answers one question only: "does this mapping.ttl
// document parse into the AST below," the same "does it parse" smoke
// check the ShEx and JSON-LD programs used for their own Stage 1.
//
// Decoder idiom mirrors SHACL.Validation.fst's shape-graph reader
// (find_objects g subject predicate -> list rdf_term, walked subject
// by subject) rather than ShEx.Schema.fst's JSON decoder — RML
// mapping documents are Turtle/RDF, not JSON, per the plan's
// module-plan section ("closer in shape to how SHACL.Validation.fst
// reads shape graphs out of Turtle-parsed triples").
//
// Vocabulary + shape surveyed directly from the vendored rml-core
// suite (third_party/testing/rml-modules/rml-core/test-cases/*/mapping.ttl,
// 76 documents) rather than guessed from the spec text. Constructs
// covered (see the plan's Stage 1 row + module-plan section):
//   - rml:TriplesMap, rml:baseIRI, rml:logicalSource / rml:LogicalSource
//     (rml:iterator, rml:referenceFormulation with rml:JSONPath /
//     rml:XPath / rml:CSV, rml:source / rml:RelativePathSource with
//     rml:root [rml:MappingDirectory | rml:CurrentWorkingDirectory]
//     and rml:path).
//   - rml:subjectMap (and the rml:subject constant-IRI shortcut),
//     rml:class (subject-map class shortcut, list-valued),
//     rml:graph / rml:graphMap (both subject-map and predicateObjectMap
//     level).
//   - rml:predicateObjectMap (list-valued), rml:predicate / rml:predicateMap,
//     rml:object / rml:objectMap (list-valued on both axes — the suite's
//     fixtures use singletons but the spec allows a cross product).
//   - rml:RefObjectMap (rml:parentTriplesMap + rml:joinCondition), with
//     both the child/parent shortcut form (rml:child "expr";
//     rml:parent "expr") and the full term-map form (rml:childMap [...];
//     rml:parentMap [...]) — both appear in the vendored suite
//     (RMLTC0009a vs RMLTC0030a).
//   - Term-map forms: rml:constant / rml:reference / rml:template, with
//     rml:termType (rml:IRI, rml:URI — a distinct term type, not a
//     synonym, see RML.Eval's IRI-safe-vs-URI-safe encoding — rml:UnsafeIRI,
//     rml:BlankNode, rml:Literal), rml:datatype / rml:datatypeMap and
//     rml:language / rml:languageMap — the Map forms are themselves
//     full term maps (RMLTC0022b/c/e's datatypeMap uses rml:template /
//     rml:reference, not just a constant literal), hence the recursive
//     `term_map` shape below.
//   - Template strings are parsed into literal + reference segments
//     (backslash-escaped `{`/`}` handled; see RMLTC0010c/RMLTC0023c-f
//     for the escape-heavy fixtures that exercise this).
//
// Out of scope for Stage 1 (see the plan's staged table):
//   - RML-IO's CSV/XML logical sources beyond the AST fields above
//     (Stages 3-4), RML-CC gather/gatherAs (Stage 6), RML-FNML
//     (Stage 7), RML-star (Stage 11, blocked on an RDF-star term type).
//   - Any evaluation: term-map interpolation, join execution,
//     triple production. That is RML.Eval.fst, Stage 2+.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.All
open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable

// ------------------------------------------------------------------
// 1. RML vocabulary (rml: = http://w3id.org/rml/) — well-formed IRI
//    constants needed at decode time.
// ------------------------------------------------------------------

let rml_TriplesMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/TriplesMap");
  "http://w3id.org/rml/TriplesMap"

let rml_baseIRI : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/baseIRI");
  "http://w3id.org/rml/baseIRI"

let rml_logicalSource : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/logicalSource");
  "http://w3id.org/rml/logicalSource"

let rml_iterator : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/iterator");
  "http://w3id.org/rml/iterator"

let rml_referenceFormulation : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/referenceFormulation");
  "http://w3id.org/rml/referenceFormulation"

let rml_JSONPath : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/JSONPath");
  "http://w3id.org/rml/JSONPath"

let rml_XPath : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/XPath");
  "http://w3id.org/rml/XPath"

let rml_CSV : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/CSV");
  "http://w3id.org/rml/CSV"

let rml_source : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/source");
  "http://w3id.org/rml/source"

let rml_path : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/path");
  "http://w3id.org/rml/path"

let rml_root : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/root");
  "http://w3id.org/rml/root"

// rml:null (RML-IO spec: "zero or more rml:null describes which data
// values inside the source should be considered as NULL. The value
// for this predicate defaults to the default NULL token of the
// underlying data model" — and, verbatim, "CSV does not have a
// default NULL character, so no value is considered NULL"). List-
// valued, and — per the vendored fixtures (RMLSTC0004b/c) — a
// property of the Source node itself (`rml:source [ a rml:FilePath;
// ...; rml:null ""; rml:null "NULL"; ]`), not of the enclosing
// LogicalSource node; decode_logical_source below reads it off
// src_subj accordingly. Defaults to the empty list when absent (per
// the spec quote above, not [""] — RMLSTC0004a's no-rml:null fixture
// emits literal "" for an empty CSV cell, it is NOT treated as null).
let rml_null : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/null");
  "http://w3id.org/rml/null"

let rml_MappingDirectory : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/MappingDirectory");
  "http://w3id.org/rml/MappingDirectory"

let rml_CurrentWorkingDirectory : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/CurrentWorkingDirectory");
  "http://w3id.org/rml/CurrentWorkingDirectory"

let rml_subjectMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/subjectMap");
  "http://w3id.org/rml/subjectMap"

let rml_subject : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/subject");
  "http://w3id.org/rml/subject"

let rml_class : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/class");
  "http://w3id.org/rml/class"

let rml_graph : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/graph");
  "http://w3id.org/rml/graph"

let rml_graphMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/graphMap");
  "http://w3id.org/rml/graphMap"

// The well-known "route to the default graph" sentinel (spec section
// 10 / 12.1's Target graphs column). A subjectMap/predicateObjectMap
// can carry `rml:graph rml:defaultGraph` explicitly (RMLTC0007g,
// RMLTC0028b) — this must land in the dataset's *default* graph, not
// a named graph literally called "http://w3id.org/rml/defaultGraph".
// RML.Eval's place_into_dataset special-cases this IRI.
let rml_defaultGraph : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/defaultGraph");
  "http://w3id.org/rml/defaultGraph"

let rml_predicateObjectMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/predicateObjectMap");
  "http://w3id.org/rml/predicateObjectMap"

let rml_predicate : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/predicate");
  "http://w3id.org/rml/predicate"

let rml_predicateMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/predicateMap");
  "http://w3id.org/rml/predicateMap"

let rml_object : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/object");
  "http://w3id.org/rml/object"

let rml_objectMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/objectMap");
  "http://w3id.org/rml/objectMap"

let rml_parentTriplesMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/parentTriplesMap");
  "http://w3id.org/rml/parentTriplesMap"

let rml_joinCondition : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/joinCondition");
  "http://w3id.org/rml/joinCondition"

let rml_child : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/child");
  "http://w3id.org/rml/child"

let rml_parent : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/parent");
  "http://w3id.org/rml/parent"

let rml_childMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/childMap");
  "http://w3id.org/rml/childMap"

let rml_parentMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/parentMap");
  "http://w3id.org/rml/parentMap"

let rml_constant : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/constant");
  "http://w3id.org/rml/constant"

let rml_reference : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/reference");
  "http://w3id.org/rml/reference"

let rml_template : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/template");
  "http://w3id.org/rml/template"

let rml_termType : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/termType");
  "http://w3id.org/rml/termType"

let rml_IRI : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/IRI");
  "http://w3id.org/rml/IRI"

// rml:URI (seen in RMLTC0027a) is a distinct term type from rml:IRI, not
// a legacy synonym — see the TT_URI comment above.
let rml_URI : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/URI");
  "http://w3id.org/rml/URI"

let rml_UnsafeIRI : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/UnsafeIRI");
  "http://w3id.org/rml/UnsafeIRI"

let rml_BlankNode : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/BlankNode");
  "http://w3id.org/rml/BlankNode"

let rml_Literal : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/Literal");
  "http://w3id.org/rml/Literal"

let rml_datatype : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/datatype");
  "http://w3id.org/rml/datatype"

let rml_datatypeMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/datatypeMap");
  "http://w3id.org/rml/datatypeMap"

let rml_language : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/language");
  "http://w3id.org/rml/language"

let rml_languageMap : wf_iri =
  assert_norm (is_iri "http://w3id.org/rml/languageMap");
  "http://w3id.org/rml/languageMap"

// ------------------------------------------------------------------
// 2. Template-string segments: split "http://ex.org/{$.ID}/{$.Name}"
//    into [Literal "http://ex.org/"; Reference "$.ID"; Literal "/";
//    Reference "$.Name"]. Backslash-escaped `{`/`}` (RMLTC0010c,
//    RMLTC0023c/d/f) are unescaped into literal brace characters
//    rather than treated as delimiters, both outside and inside a
//    reference expression (RMLTC0023f's `{$['\{Name\}']}` needs an
//    escaped brace *inside* the reference body).
// ------------------------------------------------------------------

noeq type template_segment =
  | TSeg_Literal   : string -> template_segment
  | TSeg_Reference : string -> template_segment

// `mode`: false while accumulating a literal run, true while inside an
// unescaped `{ ... }` reference expression. `buf` is the run collected
// so far; `acc` is the reversed list of segments already closed out.
let flush_template_buf (mode : bool) (buf : string) (acc : list template_segment)
  : list template_segment =
  if buf = "" then acc
  else if mode then (TSeg_Reference buf) :: acc  // unterminated reference (malformed template) — keep it, don't drop data
  else (TSeg_Literal buf) :: acc

// Fuel = String.length s + 1 is always sufficient: pos advances by at
// least 1 every call (by 2 only on the two-char escape branch), so the
// number of calls until pos >= len is bounded by len regardless of how
// the +1/+2 steps interleave. Same idiom as
// RDF.Graph.Executable.fst's string_has_colon_from.
let rec scan_template_acc
    (s : string) (pos : nat) (fuel : nat) (mode : bool) (buf : string)
    (acc : list template_segment)
  : Tot (list template_segment) (decreases fuel) =
  if fuel = 0 then flush_template_buf mode buf acc
  else
    let len = String.length s in
    if pos >= len then flush_template_buf mode buf acc
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if c = 0x5C (* backslash *) && pos + 1 < len then
        // Escaped char: consume both bytes, append the escaped char literally.
        scan_template_acc s (pos + 2) (fuel - 1) mode (buf ^ String.sub s (pos + 1) 1) acc
      else if (not mode) && c = 0x7B (* '{' *) then
        let acc' = if buf = "" then acc else (TSeg_Literal buf) :: acc in
        scan_template_acc s (pos + 1) (fuel - 1) true "" acc'
      else if mode && c = 0x7D (* '}' *) then
        scan_template_acc s (pos + 1) (fuel - 1) false "" ((TSeg_Reference buf) :: acc)
      else
        scan_template_acc s (pos + 1) (fuel - 1) mode (buf ^ String.sub s pos 1) acc

let parse_template (s : string) : list template_segment =
  List.Tot.rev (scan_template_acc s 0 (String.length s + 1) false "" [])

// ------------------------------------------------------------------
// 3. Term-map vocabulary enums.
// ------------------------------------------------------------------

type term_type =
  | TT_IRI
  | TT_URI       // distinct from TT_IRI: rml:URI applies "URI-safe" (RFC3986
                 // unreserved, ASCII-only) percent-encoding to template
                 // reference values, vs rml:IRI's "IRI-safe" (RFC3987
                 // iunreserved, most non-ASCII stays unencoded) — spec
                 // section 8.3.1. Corrected from Stage 1's "legacy synonym"
                 // call (see the removed comment at rml_URI below) after
                 // fetching the spec text directly in Stage 2: the two
                 // encodings are observably different (RMLTC0027a's
                 // rml:URI output percent-encodes "Zoë Krüger" to
                 // "Zo%C3%AB%20Kr%C3%BCger", the RFC3986/ASCII-only form).
  | TT_UnsafeIRI
  | TT_BlankNode
  | TT_Literal

type reference_formulation =
  | RF_JSONPath
  | RF_XPath
  | RF_CSV
  | RF_Other : string -> reference_formulation

type source_root =
  | Root_MappingDirectory
  | Root_CurrentWorkingDirectory
  | Root_Other : string -> source_root

let decode_term_type (t : rdf_term) : option term_type =
  match t with
  | T_IRI i ->
    if i = rml_IRI then Some TT_IRI
    else if i = rml_URI then Some TT_URI
    else if i = rml_UnsafeIRI then Some TT_UnsafeIRI
    else if i = rml_BlankNode then Some TT_BlankNode
    else if i = rml_Literal then Some TT_Literal
    else None
  | _ -> None

let decode_reference_formulation (t : rdf_term) : reference_formulation =
  match t with
  | T_IRI i ->
    if i = rml_JSONPath then RF_JSONPath
    else if i = rml_XPath then RF_XPath
    else if i = rml_CSV then RF_CSV
    else RF_Other i
  | _ -> RF_Other ""

let decode_source_root (t : rdf_term) : source_root =
  match t with
  | T_IRI i ->
    if i = rml_MappingDirectory then Root_MappingDirectory
    else if i = rml_CurrentWorkingDirectory then Root_CurrentWorkingDirectory
    else Root_Other i
  | _ -> Root_Other ""

// ------------------------------------------------------------------
// 4. Node references (subject or bnode identifier as a plain string,
//    same idiom as SHACL.Validation.fst's shape_ref — kept as a local
//    type here rather than importing SHACL.Validation, since this
//    module has no other dependency on it).
// ------------------------------------------------------------------

type node_ref = string

let term_to_node_ref (t : rdf_term) : option node_ref =
  match t with
  | T_IRI i -> Some i
  | T_BNode b -> Some ("_:" ^ b)
  | T_Literal _ -> None

let subject_to_node_ref (s : subject) : node_ref =
  match s with
  | S_IRI i -> i
  | S_BNode b -> "_:" ^ b

// All distinct subjects appearing anywhere in the graph (same
// implementation as SHACL.Validation.fst's distinct_subjects; kept
// local for the same reason as node_ref above).
let rec distinct_subjects_acc (g : rdf_graph) (acc : list subject)
  : Tot (list subject) (decreases g) =
  match g with
  | [] -> acc
  | t :: rest ->
    if List.Tot.existsb (subject_eq t.s) acc
    then distinct_subjects_acc rest acc
    else distinct_subjects_acc rest (t.s :: acc)

let distinct_subjects (g : rdf_graph) : list subject =
  distinct_subjects_acc g []

// ------------------------------------------------------------------
// 5. Logical source: iterator + reference formulation + a
//    RelativePathSource's root/path (rml-core's only source shape;
//    other rml-io source shapes decode as None fields here, extended
//    when RML.Sources lands — Stage 3/4 in the plan).
// ------------------------------------------------------------------

noeq type logical_source = {
  ls_iterator              : option string;
  ls_reference_formulation : option reference_formulation;
  ls_source_path           : option string;
  ls_source_root           : option source_root;
  ls_null_values           : list string;
}

let empty_logical_source : logical_source = {
  ls_iterator = None;
  ls_reference_formulation = None;
  ls_source_path = None;
  ls_source_root = None;
  ls_null_values = [];
}

let first_literal (l : list rdf_term) : option string =
  match l with
  | (T_Literal lit) :: _ -> Some lit.lexical_form
  | _ -> None

let literal_strings (l : list rdf_term) : list string =
  List.Tot.concatMap (fun t -> match t with T_Literal lit -> [lit.lexical_form] | _ -> []) l

let decode_logical_source (g : rdf_graph) (s : subject) : option logical_source =
  match find_objects g s rml_logicalSource with
  | [] -> None
  | (ls_term :: _) ->
    (match term_to_subject ls_term with
     | None -> None
     | Some ls_subj ->
       let iterator = first_literal (find_objects g ls_subj rml_iterator) in
       let refform =
         (match find_objects g ls_subj rml_referenceFormulation with
          | (t :: _) -> Some (decode_reference_formulation t)
          | [] -> None) in
       let (path, root, null_values) =
         (match find_objects g ls_subj rml_source with
          | (src_term :: _) ->
            (match term_to_subject src_term with
             | Some src_subj ->
               (first_literal (find_objects g src_subj rml_path),
                (match find_objects g src_subj rml_root with
                 | (t :: _) -> Some (decode_source_root t)
                 | [] -> None),
                // rml:null is a property of the Source node (rml:FilePath —
                // RMLSTC0004b/c: `rml:source [ a rml:FilePath; ...;
                // rml:null ""; rml:null "NULL"; ]`), not of the enclosing
                // LogicalSource node — corrected from an initial mis-read
                // that looked for it on ls_subj (measured: decoded to []
                // for both fixtures, silently dropping the null filter).
                literal_strings (find_objects g src_subj rml_null))
             | None -> (None, None, []))
          | [] -> (None, None, [])) in
       Some ({ ls_iterator = iterator; ls_reference_formulation = refform;
               ls_source_path = path; ls_source_root = root;
               ls_null_values = null_values }))

// ------------------------------------------------------------------
// 6. Term maps. A term map is one of constant/reference/template,
//    optionally refined by a termType, and optionally carrying a
//    datatype or language that is *itself* a full term map (RML-Core
//    lets datatypeMap/languageMap be constant, reference, or template
//    — RMLTC0022b/c/e, RMLTC0031a/b/c) — hence the recursive shape.
// ------------------------------------------------------------------

noeq type term_map_form =
  | TMF_Constant  : rdf_term -> term_map_form
  | TMF_Reference : string -> term_map_form
  | TMF_Template  : string -> term_map_form  // raw template string; call parse_template on demand
  | TMF_Unknown   : term_map_form            // no recognized constant/reference/template triple found

noeq type term_map = {
  tmap_form     : term_map_form;
  tmap_termtype : option term_type;
  tmap_datatype : option term_map;
  tmap_language : option term_map;
}

let unknown_term_map : term_map =
  { tmap_form = TMF_Unknown; tmap_termtype = None; tmap_datatype = None; tmap_language = None }

let const_term_map (t : rdf_term) : term_map =
  { tmap_form = TMF_Constant t; tmap_termtype = None; tmap_datatype = None; tmap_language = None }

let ref_term_map (r : string) : term_map =
  { tmap_form = TMF_Reference r; tmap_termtype = None; tmap_datatype = None; tmap_language = None }

// fuel bounds datatypeMap/languageMap nesting depth; graph_len g + 1
// is always enough (mirrors SHACL.Validation.fst's parse_path fuel
// idiom: `graph_len g + 1` at its one call site).
let rec decode_term_map_from_subject (g : rdf_graph) (s : subject) (fuel : nat)
  : Tot term_map (decreases fuel) =
  if fuel = 0 then unknown_term_map
  else
    let fuel' : nat = fuel - 1 in
    let form =
      (match find_objects g s rml_constant with
       | (t :: _) -> TMF_Constant t
       | [] ->
         (match find_objects g s rml_reference with
          | (T_Literal l) :: _ -> TMF_Reference l.lexical_form
          | _ ->
            (match find_objects g s rml_template with
             | (T_Literal l) :: _ -> TMF_Template l.lexical_form
             | _ -> TMF_Unknown))) in
    let termtype =
      (match find_objects g s rml_termType with
       | (t :: _) -> decode_term_type t
       | [] -> None) in
    let datatype =
      (match find_objects g s rml_datatypeMap with
       | (t :: _) ->
         (match term_to_subject t with
          | Some ds -> Some (decode_term_map_from_subject g ds fuel')
          | None -> None)
       | [] ->
         (match find_objects g s rml_datatype with
          | (t :: _) -> Some (const_term_map t)
          | [] -> None)) in
    let language =
      (match find_objects g s rml_languageMap with
       | (t :: _) ->
         (match term_to_subject t with
          | Some ls -> Some (decode_term_map_from_subject g ls fuel')
          | None -> None)
       | [] ->
         (match find_objects g s rml_language with
          | (t :: _) -> Some (const_term_map t)
          | [] -> None)) in
    { tmap_form = form; tmap_termtype = termtype; tmap_datatype = datatype; tmap_language = language }

// ------------------------------------------------------------------
// 7. Join conditions + RefObjectMap. Both the child/parent literal
//    shortcut (rml:child "expr"; rml:parent "expr" — RMLTC0009a) and
//    the full childMap/parentMap term-map form (RMLTC0030a) appear in
//    the vendored suite; both decode to the same `term_map`-valued
//    fields so RML.Eval (Stage 5) has one shape to evaluate.
// ------------------------------------------------------------------

noeq type join_condition = {
  jc_child  : term_map;
  jc_parent : term_map;
}

noeq type ref_object_map = {
  rom_parent_triples_map : node_ref;
  rom_joins              : list join_condition;
}

let decode_child_or_parent
    (g : rdf_graph) (s : subject) (map_pred : wf_iri) (shortcut_pred : wf_iri) (fuel : nat)
  : term_map =
  match find_objects g s map_pred with
  | (t :: _) ->
    (match term_to_subject t with
     | Some ms -> decode_term_map_from_subject g ms fuel
     | None -> unknown_term_map)
  | [] ->
    (match find_objects g s shortcut_pred with
     | (T_Literal l) :: _ -> ref_term_map l.lexical_form
     | _ -> unknown_term_map)

let decode_join_conditions (g : rdf_graph) (s : subject) (fuel : nat) : list join_condition =
  List.Tot.concatMap
    (fun t ->
       match term_to_subject t with
       | None -> []
       | Some jc_subj ->
         [{ jc_child  = decode_child_or_parent g jc_subj rml_childMap rml_child fuel;
            jc_parent = decode_child_or_parent g jc_subj rml_parentMap rml_parent fuel }])
    (find_objects g s rml_joinCondition)

// ------------------------------------------------------------------
// 8. Predicate-object maps: predicates and objects are each list-
//    valued (the vendored suite only ever uses singletons per block,
//    but rml:predicate/rml:predicateMap and rml:object/rml:objectMap
//    all have cardinality * in the spec — modelled that way so a
//    fixture with a genuine cross product doesn't silently drop
//    entries). An object can be a plain term map or a RefObjectMap
//    (join) — RMLTC0008b's RefObjectMap-as-separate-resource form and
//    RMLTC0009a's inline-blank-node form both decode via
//    rml:parentTriplesMap being present on the objectMap's node.
// ------------------------------------------------------------------

noeq type object_binding =
  | OB_TermMap : term_map -> object_binding
  | OB_Join    : ref_object_map -> object_binding

noeq type predicate_object_map = {
  pom_predicates : list term_map;
  pom_objects    : list object_binding;
  pom_graphs     : list term_map;
}

// Shared by subjectMap and predicateObjectMap: rml:graph is a constant-
// value shortcut, rml:graphMap is a full term map.
let decode_graphs (g : rdf_graph) (s : subject) (fuel : nat) : list term_map =
  let via_map =
    List.Tot.concatMap
      (fun t -> match term_to_subject t with
                | Some gs -> [decode_term_map_from_subject g gs fuel]
                | None -> [])
      (find_objects g s rml_graphMap) in
  let via_shortcut = List.Tot.map const_term_map (find_objects g s rml_graph) in
  via_map @ via_shortcut

let decode_predicates (g : rdf_graph) (s : subject) (fuel : nat) : list term_map =
  let via_map =
    List.Tot.concatMap
      (fun t -> match term_to_subject t with
                | Some ps -> [decode_term_map_from_subject g ps fuel]
                | None -> [])
      (find_objects g s rml_predicateMap) in
  let via_shortcut = List.Tot.map const_term_map (find_objects g s rml_predicate) in
  via_map @ via_shortcut

let decode_object_bindings (g : rdf_graph) (s : subject) (fuel : nat) : list object_binding =
  let via_object_map =
    List.Tot.concatMap
      (fun t ->
         match term_to_subject t with
         | None -> []
         | Some om_subj ->
           (match find_objects g om_subj rml_parentTriplesMap with
            | (ptm :: _) ->
              let parent_ref = (match term_to_node_ref ptm with Some r -> r | None -> "") in
              [OB_Join ({ rom_parent_triples_map = parent_ref;
                          rom_joins = decode_join_conditions g om_subj fuel })]
            | [] -> [OB_TermMap (decode_term_map_from_subject g om_subj fuel)]))
      (find_objects g s rml_objectMap) in
  let via_object_shortcut = List.Tot.map (fun t -> OB_TermMap (const_term_map t)) (find_objects g s rml_object) in
  via_object_map @ via_object_shortcut

let decode_predicate_object_map (g : rdf_graph) (pom_subj : subject) (fuel : nat) : predicate_object_map =
  { pom_predicates = decode_predicates g pom_subj fuel;
    pom_objects    = decode_object_bindings g pom_subj fuel;
    pom_graphs     = decode_graphs g pom_subj fuel }

let decode_predicate_object_maps (g : rdf_graph) (s : subject) (fuel : nat) : list predicate_object_map =
  List.Tot.concatMap
    (fun t -> match term_to_subject t with
              | Some pom_subj -> [decode_predicate_object_map g pom_subj fuel]
              | None -> [])
    (find_objects g s rml_predicateObjectMap)

// ------------------------------------------------------------------
// 9. Subject map: the term map itself, plus rml:class shortcuts
//    (list-valued — RMLTC0009b/RMLTC0030a-f pair rml:class with
//    rml:template on the same subjectMap) and rml:graph/rml:graphMap
//    (RMLTC0006a/RMLTC0009b put the graph on the subjectMap, not the
//    predicateObjectMap). A bare rml:subject <IRI> shortcut at the
//    TriplesMap level (RMLTC0029a) skips the nested subjectMap node
//    entirely and decodes straight to a constant term map with no
//    classes/graphs.
// ------------------------------------------------------------------

noeq type subject_map_t = {
  sm_term    : term_map;
  sm_classes : list wf_iri;
  sm_graphs  : list term_map;
}

// RMLTC0012d: two rml:subjectMap blocks on the same TriplesMap is a
// data error (the spec's cardinality for subjectMap is exactly one,
// per RML-Core's mapping-vocabulary section) — decode to None (same
// outcome as "no subjectMap at all") rather than silently picking the
// first one found, so the whole triples map contributes no triples
// (eval_triples_map's `None -> []` branch already handles that).
let decode_subject_map (g : rdf_graph) (s : subject) (fuel : nat) : option subject_map_t =
  match find_objects g s rml_subjectMap with
  | [] ->
    (match find_objects g s rml_subject with
     | (t :: _) -> Some ({ sm_term = const_term_map t; sm_classes = []; sm_graphs = [] })
     | [] -> None)
  | [sm_term] ->
    (match term_to_subject sm_term with
     | None -> None
     | Some sm_subj ->
       let term = decode_term_map_from_subject g sm_subj fuel in
       let classes =
         List.Tot.concatMap (fun t -> match t with T_IRI i -> [i] | _ -> []) (find_objects g sm_subj rml_class) in
       let graphs = decode_graphs g sm_subj fuel in
       Some ({ sm_term = term; sm_classes = classes; sm_graphs = graphs }))
  | _ :: _ :: _ -> None  // duplicate rml:subjectMap: data error

// ------------------------------------------------------------------
// 10. Triples map + mapping document.
// ------------------------------------------------------------------

noeq type triples_map = {
  tm_id                    : node_ref;
  tm_base_iri              : option string;
  tm_logical_source        : option logical_source;
  tm_subject_map           : option subject_map_t;
  tm_predicate_object_maps : list predicate_object_map;
}

noeq type mapping_document = {
  md_triples_maps : list triples_map;
}

let decode_triples_map (g : rdf_graph) (s : subject) (fuel : nat) : triples_map =
  {
    tm_id = subject_to_node_ref s;
    tm_base_iri =
      (match find_objects g s rml_baseIRI with
       | (T_IRI i) :: _ -> Some i
       | _ -> None);
    tm_logical_source = decode_logical_source g s;
    tm_subject_map = decode_subject_map g s fuel;
    tm_predicate_object_maps = decode_predicate_object_maps g s fuel;
  }

// Every subject that has an (s, rdf:type, rml:TriplesMap) triple is a
// triples map — the RML-Core equivalent of SHACL.Validation.fst's
// is_shape_establishing criterion, specialized to a single fixed type
// rather than "any vocabulary triple" since rml:TriplesMap is the one
// entry point into a mapping document (subjectMap/objectMap/
// logicalSource nodes are only ever reached *from* a TriplesMap, never
// enumerated as top-level documents themselves).
let is_triples_map_subject (g : rdf_graph) (s : subject) : bool =
  List.Tot.existsb
    (fun (t : triple) -> subject_eq t.s s && t.p = rdf_type && rdf_term_eq t.o (T_IRI rml_TriplesMap))
    g

let decode_mapping_document (g : rdf_graph) : mapping_document =
  let subs = distinct_subjects g in
  let tm_subs = List.Tot.filter (is_triples_map_subject g) subs in
  { md_triples_maps = List.Tot.map (fun s -> decode_triples_map g s (graph_len g + 1)) tm_subs }
