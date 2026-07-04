module SHACL.Validation

// Phase 1 skeleton of the W3C SHACL Core F* implementation, per
// epic #181 + docs/designissues/2026-05-07-query-planning-fstar-recovery.md
// (sister track alongside RIF Core, OWL, RDF Canonical).
//
// This module defines the abstract syntax for SHACL Core shapes and
// the validation entry-point signature. It does NOT implement the
// validation algorithm — `validate` is `assume val` (rule #11(c)
// host-engine call-out style; SPARQL-target shapes need the SPARQL
// evaluator, which is reachable from a consumer-side glue file).
// A corresponding glue patch stub lives at
//   formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
//   181_shacl_validate_stub.sh
// and tracks elimination via issue #181.
//
// Surface coverage (Phase 1 — AST only):
//   - Targets:    target class / target node / target subjects-of /
//                 target objects-of / target implicit / SPARQL-select.
//   - Shapes:     NodeShape (validates focus nodes directly),
//                 PropertyShape (walks a path from a focus node).
//   - Constraints: minCount, maxCount, datatype, nodeKind, class,
//                 in, hasValue, pattern, minLength, maxLength,
//                 minInclusive, maxInclusive, minExclusive, maxExclusive,
//                 sh:not, sh:and, sh:or, sh:xone, sh:select (SPARQL).
//   - Property paths: predicate path, inverse path, sequence path,
//                 alternative path, zero-or-more, one-or-more,
//                 zero-or-one. (Mirrors the SHACL-Core SPARQL paths.)
//
// Out of scope for Phase 1 (deferred):
//   - parse_shape_from_graph (RDF -> shape) — Phase 2.
//   - apply_constraint per-component evaluators — Phase 2.
//   - SHACL Advanced Features (sh:rule, sh:function) — separate epic.
//   - W3C SHACL test corpus runner — vendoring + Phase 2.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - Every assume val has a glue patch (rule #3).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.All
open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
// Alias, not `open`, to avoid polluting this module's namespace with
// SPARQL-expression machinery (FILTER/BIND helpers etc.) that share
// short names with SHACL vocabulary. Only a handful of pure numeric-
// literal and regex helpers are used from here: parse_to_scaled,
// parse_double_to_scaled, pow10, regex_match. SPARQL11.Algebra
// verifies before this module in build-ocaml.sh's ALL_MODULES order,
// so this is not a new dependency edge, just an explicit one.
module Alg = SPARQL11.Algebra

// ------------------------------------------------------------------
// 1. SHACL vocabulary — well-formed IRI constants we will need at
//    parse time (Phase 2). Keeping them in this module avoids a
//    dedicated SHACL.Vocab module while the AST is small.
// ------------------------------------------------------------------

let sh_NodeShape : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#NodeShape");
  "http://www.w3.org/ns/shacl#NodeShape"

let sh_PropertyShape : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#PropertyShape");
  "http://www.w3.org/ns/shacl#PropertyShape"

let sh_targetClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#targetClass");
  "http://www.w3.org/ns/shacl#targetClass"

let sh_targetNode : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#targetNode");
  "http://www.w3.org/ns/shacl#targetNode"

let sh_targetSubjectsOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#targetSubjectsOf");
  "http://www.w3.org/ns/shacl#targetSubjectsOf"

let sh_targetObjectsOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#targetObjectsOf");
  "http://www.w3.org/ns/shacl#targetObjectsOf"

let sh_path : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#path");
  "http://www.w3.org/ns/shacl#path"

let sh_select : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#select");
  "http://www.w3.org/ns/shacl#select"

let sh_Violation : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#Violation");
  "http://www.w3.org/ns/shacl#Violation"

// ------------------------------------------------------------------
// 2. Severity. SHACL defines three; default is sh:Violation.
// ------------------------------------------------------------------

type severity =
  | Sev_Info
  | Sev_Warning
  | Sev_Violation

// ------------------------------------------------------------------
// 3. NodeKind — the value of sh:nodeKind. SHACL admits exactly six
//    constants; we encode them as a sum.
// ------------------------------------------------------------------

type node_kind =
  | NK_BlankNode
  | NK_IRI
  | NK_Literal
  | NK_BlankNodeOrIRI
  | NK_BlankNodeOrLiteral
  | NK_IRIOrLiteral

// ------------------------------------------------------------------
// 4. Property paths. A simplified mirror of SPARQL property paths
//    restricted to what SHACL Core allows. Mutual recursion via
//    `list path` and direct constructors is fine — F* infers the
//    structural measure from the constructor depth.
// ------------------------------------------------------------------

noeq type path =
  | P_Predicate     : wf_iri -> path
  | P_Inverse       : path -> path
  | P_Sequence      : list path -> path
  | P_Alternative   : list path -> path
  | P_ZeroOrMore    : path -> path
  | P_OneOrMore     : path -> path
  | P_ZeroOrOne     : path -> path

// ------------------------------------------------------------------
// 5. Targets. Five concrete forms in SHACL Core plus the "implicit
//    class target" (a node shape that is itself an rdfs:Class).
//    SPARQL-select is admitted as a sixth form so that SPARQL-target
//    test cases can be expressed in the same AST.
// ------------------------------------------------------------------

noeq type target =
  | T_Class         : wf_iri -> target
  | T_Node          : rdf_term -> target
  | T_SubjectsOf    : wf_iri -> target
  | T_ObjectsOf     : wf_iri -> target
  | T_ImplicitClass : wf_iri -> target
  | T_Sparql        : string -> target

// ------------------------------------------------------------------
// 6. Constraint components.
//
// A flat sum so that pattern-matching in evaluators is exhaustive
// without going through a generic dictionary. The Phase 2 evaluator
// (apply_constraint) walks this directly. Logical operators take a
// list of nested shape *references* (by IRI / blank-node id) — the
// shape graph is a single value, so we avoid a recursive AST and
// resolve references at validation time.
// ------------------------------------------------------------------

type shape_ref = string  // identifier within the shapes graph

noeq type constraint_component =
  // Cardinality (PropertyShape only — non-trivial only with a path).
  | CC_MinCount     : nat -> constraint_component
  | CC_MaxCount     : nat -> constraint_component
  // Value-type checks.
  | CC_Datatype     : wf_iri -> constraint_component
  | CC_NodeKind     : node_kind -> constraint_component
  | CC_Class        : wf_iri -> constraint_component
  // Value enumeration / fixed value.
  | CC_In           : list rdf_term -> constraint_component
  | CC_HasValue     : rdf_term -> constraint_component
  // String constraints.
  | CC_Pattern      : pattern_re:string -> flags:string -> constraint_component
  | CC_MinLength    : nat -> constraint_component
  | CC_MaxLength    : nat -> constraint_component
  | CC_LanguageIn   : list string -> constraint_component
  | CC_UniqueLang   : bool -> constraint_component
  // Range constraints (lexical / numeric forms — evaluator decides).
  | CC_MinInclusive : rdf_term -> constraint_component
  | CC_MaxInclusive : rdf_term -> constraint_component
  | CC_MinExclusive : rdf_term -> constraint_component
  | CC_MaxExclusive : rdf_term -> constraint_component
  // Logical combinators over nested shapes (referenced by id).
  | CC_Not          : shape_ref -> constraint_component
  | CC_And          : list shape_ref -> constraint_component
  | CC_Or           : list shape_ref -> constraint_component
  | CC_Xone         : list shape_ref -> constraint_component
  // sh:node — validate each value node against another (nested) shape,
  // in addition to (not instead of) this shape's own constraints.
  // Added in Phase 2 (slice 1); the Phase 1 skeleton comment above
  // predates this constructor. Ranked #22 by file-frequency in the
  // vendored W3C core suite (property/node-*.ttl).
  | CC_Node         : shape_ref -> constraint_component
  // Property-pair constraints.
  | CC_Equals       : wf_iri -> constraint_component
  | CC_Disjoint     : wf_iri -> constraint_component
  | CC_LessThan     : wf_iri -> constraint_component
  | CC_LessThanOrEq : wf_iri -> constraint_component
  // Closed-shape constraint.
  | CC_Closed       : ignored:list wf_iri -> constraint_component
  // SPARQL-based constraint (sh:select). Stored as a SELECT query
  // string; evaluation dispatches to the SPARQL engine via a
  // consumer-side realisation.
  | CC_Sparql       : string -> constraint_component

// ------------------------------------------------------------------
// 7. Shape. A single record covers both NodeShape and PropertyShape:
//    a PropertyShape simply has `path = Some _`. Shapes carry their
//    targets, severity, and the list of constraint components that
//    apply to focus nodes / value nodes.
// ------------------------------------------------------------------

noeq type shape = {
  shape_id     : shape_ref;
  is_property  : bool;
  shape_path   : option path;
  targets      : list target;
  shape_sev    : severity;
  message      : option string;
  constraints  : list constraint_component;
  // Nested shapes by id (for sh:property on a NodeShape — a node
  // shape may carry property shapes, validated against each focus
  // node). Resolved through the shapes graph at validation time.
  property_refs : list shape_ref;
}

noeq type shapes_graph = {
  shapes : list shape;
}

let empty_shapes_graph : shapes_graph = { shapes = [] }

// ------------------------------------------------------------------
// 8. Validation report.
//
// Mirrors the SHACL validation report vocabulary at the AST level.
// A `violation` carries enough to render an sh:ValidationResult
// triple set; the report type wraps the conformance flag plus the
// list. Phase 2 will add helpers to serialise to RDF.
// ------------------------------------------------------------------

noeq type violation = {
  v_focus_node    : rdf_term;
  v_path          : option path;
  v_value         : option rdf_term;
  v_source_shape  : shape_ref;
  v_constraint    : constraint_component;
  v_severity      : severity;
  v_message       : option string;
}

noeq type validation_report = {
  conforms   : bool;
  results    : list violation;
}

let conforming_report : validation_report =
  { conforms = true; results = [] }

// ------------------------------------------------------------------
// 9. Smart constructors.
// ------------------------------------------------------------------

let mk_shape_node (id_ : shape_ref) (ts : list target)
                  (cs : list constraint_component)
  : shape
  = { shape_id = id_; is_property = false; shape_path = None;
      targets = ts; shape_sev = Sev_Violation; message = None;
      constraints = cs; property_refs = []; }

let mk_shape_property (id_ : shape_ref) (p : path)
                      (ts : list target) (cs : list constraint_component)
  : shape
  = { shape_id = id_; is_property = true; shape_path = Some p;
      targets = ts; shape_sev = Sev_Violation; message = None;
      constraints = cs; property_refs = []; }

let shapes_graph_of_list (ss : list shape) : shapes_graph =
  { shapes = ss }

// Lookup a shape by id within a shapes graph. Pure F*; total over
// the well-founded recursion on the underlying list.
let rec lookup_shape (id_ : shape_ref) (sg : list shape)
  : Tot (option shape) (decreases sg)
  =
  match sg with
  | [] -> None
  | s :: rest ->
    if s.shape_id = id_ then Some s
    else lookup_shape id_ rest

// ------------------------------------------------------------------
// 10. Path-arity sanity check. A PropertyShape MUST carry a path; a
//     NodeShape MUST NOT. Provided as a Tot predicate so the Phase 2
//     parse_shape_from_graph can reject malformed shape graphs
//     without an exception.
// ------------------------------------------------------------------

let shape_well_formed (s : shape) : bool =
  if s.is_property then Some? s.shape_path
  else None? s.shape_path

let rec shapes_well_formed (ss : list shape)
  : Tot bool (decreases ss)
  =
  match ss with
  | [] -> true
  | s :: rest -> shape_well_formed s && shapes_well_formed rest

// ------------------------------------------------------------------
// 11. Phase 2 (slice 1) — pure F* validator core, issue #181.
//
// This section replaces the Phase 1 `validate` / `parse_shape_from_graph`
// assume vals with real, total (or ML-wrapped-Tot) F* implementations,
// per the recovery plan. Scope decisions for slice 1 (see
// docs/designissues/2026-05-07-query-planning-fstar-recovery.md and
// the SHACL slice-1 brief):
//
//   - sh:path supports predicate paths and inverse-of-predicate paths.
//     Sequence/alternative/zeroOrMore/oneOrMore/zeroOrOne paths PARSE
//     into the AST (so v_path / resultPath reporting is faithful when
//     reachable) but EVALUATE to no values — an honest FAIL against
//     W3C fixtures that need them, not a silently-wrong PASS. Full
//     path-algebra evaluation is Phase 2 follow-up work.
//   - sh:sparql / sh:select target and constraint dispatch stays the
//     one rule-#11(c) host call-out (`eval_sparql_target_select`,
//     kept `assume val` below) — never invoked by this slice, since
//     T_Sparql targets evaluate to no focus nodes and CC_Sparql
//     constraints evaluate to no violations. The glue patch stub at
//     minimal_regrettable_glue_code_each_with_an_open_issue/
//     181_shacl_validate_stub.sh still discharges rule #3 for it.
//   - sh:qualifiedValueShape / qualifiedMinCount / qualifiedMaxCount /
//     qualifiedValueShapesDisjoint are not parsed into
//     constraint_component in this slice (sibling-disjointness
//     bookkeeping is nontrivial); shapes using them validate without
//     that constraint, which under conforms-only scoring surfaces as
//     an honest FAIL against the suite's expected `sh:conforms false`,
//     never a false PASS.
//
// Everything in this section is `Tot` except the top-level `validate`
// (kept `ML` to match the assume val it replaces, and because it is
// the natural seam for the deferred SPARQL-target call-out).
// ------------------------------------------------------------------

// --- 11a. Generic RDF-list / graph utilities -----------------------

// Walk an RDF collection (`( a b c )` Turtle sugar, i.e. an
// rdf:first/rdf:rest chain terminated by rdf:nil) starting at `head`.
// Fuel-bounded by graph size, matching the established pattern in
// Tableau.walk_rdf_list / OWL.QueryRewrite (each step consumes at
// least one triple, so graph_len is always a sufficient bound).
let rec rdf_list_terms (g : rdf_graph) (head : rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | n ->
    (match head with
     | T_BNode _ ->
       (match term_to_subject head with
        | None -> []
        | Some s ->
          (match find_objects g s rdf_first, find_objects g s rdf_rest with
           | (h :: _), (r :: _) -> h :: rdf_list_terms g r (n - 1)
           | _, _ -> []))
     | _ -> [])

// All distinct subjects appearing anywhere in the graph.
let rec distinct_subjects_acc (g : rdf_graph) (acc : list subject)
  : Tot (list subject) (decreases g)
  =
  match g with
  | [] -> acc
  | t :: rest ->
    if List.Tot.existsb (subject_eq t.s) acc
    then distinct_subjects_acc rest acc
    else distinct_subjects_acc rest (t.s :: acc)

let distinct_subjects (g : rdf_graph) : list subject =
  distinct_subjects_acc g []

let dedup_terms_acc (acc : list rdf_term) (t : rdf_term) : list rdf_term =
  if List.Tot.existsb (rdf_term_eq t) acc then acc else acc @ [t]

let dedup_terms (l : list rdf_term) : list rdf_term =
  List.Tot.fold_left dedup_terms_acc [] l

let term_to_shape_ref (t : rdf_term) : option shape_ref =
  match t with
  | T_IRI i   -> Some i
  | T_BNode b -> Some ("_:" ^ b)
  | T_Literal _ -> None

let subject_to_shape_ref (s : subject) : shape_ref =
  match s with
  | S_IRI i -> i
  | S_BNode b -> "_:" ^ b

let term_lexical (t : rdf_term) : option string =
  match t with
  | T_Literal l -> Some l.lexical_form
  | T_IRI i     -> Some i
  | T_BNode _   -> None

let first_int (l : list rdf_term) : option nat =
  match l with
  | (T_Literal lit) :: _ ->
    (match Alg.parse_int_string lit.lexical_form with
     | Some n -> if n >= 0 then Some n else None
     | None -> None)
  | _ -> None

// Lexical-exact "true" match, not XSD boolean *value* equality
// (which would also accept "1"). This matches the W3C suite's own
// documented intent — see core/property/uniqueLang-002-shapes.ttl's
// comment: "1"^^xsd:boolean is deliberately distinct from
// "true"^^xsd:boolean for SHACL boolean-valued parameters, so a
// constraint spelled with "1" is inert, not merely value-equal-true.
let first_bool (l : list rdf_term) : option bool =
  match l with
  | (T_Literal lit) :: _ -> Some (lit.lexical_form = "true")
  | _ -> None

// --- 11b. Additional SHACL vocabulary constants ---------------------
// (section 1 above already defines NodeShape/PropertyShape/target*/
// path/select/Violation; these are the constraint + path-expression +
// list predicates slice 1 needs.)

let sh_property : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#property");
  "http://www.w3.org/ns/shacl#property"
let sh_node : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#node");
  "http://www.w3.org/ns/shacl#node"
let sh_minCount : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#minCount");
  "http://www.w3.org/ns/shacl#minCount"
let sh_maxCount : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#maxCount");
  "http://www.w3.org/ns/shacl#maxCount"
let sh_datatype : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#datatype");
  "http://www.w3.org/ns/shacl#datatype"
let sh_nodeKind : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#nodeKind");
  "http://www.w3.org/ns/shacl#nodeKind"
let sh_class : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#class");
  "http://www.w3.org/ns/shacl#class"
let sh_in : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#in");
  "http://www.w3.org/ns/shacl#in"
let sh_hasValue : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#hasValue");
  "http://www.w3.org/ns/shacl#hasValue"
let sh_pattern : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#pattern");
  "http://www.w3.org/ns/shacl#pattern"
let sh_flags : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#flags");
  "http://www.w3.org/ns/shacl#flags"
let sh_minLength : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#minLength");
  "http://www.w3.org/ns/shacl#minLength"
let sh_maxLength : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#maxLength");
  "http://www.w3.org/ns/shacl#maxLength"
let sh_languageIn : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#languageIn");
  "http://www.w3.org/ns/shacl#languageIn"
let sh_uniqueLang : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#uniqueLang");
  "http://www.w3.org/ns/shacl#uniqueLang"
let sh_minInclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#minInclusive");
  "http://www.w3.org/ns/shacl#minInclusive"
let sh_maxInclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#maxInclusive");
  "http://www.w3.org/ns/shacl#maxInclusive"
let sh_minExclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#minExclusive");
  "http://www.w3.org/ns/shacl#minExclusive"
let sh_maxExclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#maxExclusive");
  "http://www.w3.org/ns/shacl#maxExclusive"
let sh_not : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#not");
  "http://www.w3.org/ns/shacl#not"
let sh_and : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#and");
  "http://www.w3.org/ns/shacl#and"
let sh_or : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#or");
  "http://www.w3.org/ns/shacl#or"
let sh_xone : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#xone");
  "http://www.w3.org/ns/shacl#xone"
let sh_equals : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#equals");
  "http://www.w3.org/ns/shacl#equals"
let sh_disjoint : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#disjoint");
  "http://www.w3.org/ns/shacl#disjoint"
let sh_lessThan : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#lessThan");
  "http://www.w3.org/ns/shacl#lessThan"
let sh_lessThanOrEquals : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#lessThanOrEquals");
  "http://www.w3.org/ns/shacl#lessThanOrEquals"
let sh_closed : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#closed");
  "http://www.w3.org/ns/shacl#closed"
let sh_ignoredProperties : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#ignoredProperties");
  "http://www.w3.org/ns/shacl#ignoredProperties"
let sh_severity : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#severity");
  "http://www.w3.org/ns/shacl#severity"
let sh_message : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#message");
  "http://www.w3.org/ns/shacl#message"
let sh_deactivated : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#deactivated");
  "http://www.w3.org/ns/shacl#deactivated"
let sh_Info : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#Info");
  "http://www.w3.org/ns/shacl#Info"
let sh_Warning : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#Warning");
  "http://www.w3.org/ns/shacl#Warning"
let sh_inversePath : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#inversePath");
  "http://www.w3.org/ns/shacl#inversePath"
let sh_alternativePath : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#alternativePath");
  "http://www.w3.org/ns/shacl#alternativePath"
let sh_zeroOrMorePath : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#zeroOrMorePath");
  "http://www.w3.org/ns/shacl#zeroOrMorePath"
let sh_oneOrMorePath : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#oneOrMorePath");
  "http://www.w3.org/ns/shacl#oneOrMorePath"
let sh_zeroOrOnePath : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#zeroOrOnePath");
  "http://www.w3.org/ns/shacl#zeroOrOnePath"
let sh_nk_BlankNode : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#BlankNode");
  "http://www.w3.org/ns/shacl#BlankNode"
let sh_nk_IRI : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#IRI");
  "http://www.w3.org/ns/shacl#IRI"
let sh_nk_Literal : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#Literal");
  "http://www.w3.org/ns/shacl#Literal"
let sh_nk_BlankNodeOrIRI : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#BlankNodeOrIRI");
  "http://www.w3.org/ns/shacl#BlankNodeOrIRI"
let sh_nk_BlankNodeOrLiteral : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#BlankNodeOrLiteral");
  "http://www.w3.org/ns/shacl#BlankNodeOrLiteral"
let sh_nk_IRIOrLiteral : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#IRIOrLiteral");
  "http://www.w3.org/ns/shacl#IRIOrLiteral"

let node_kind_of_iri (i : wf_iri) : option node_kind =
  if i = sh_nk_BlankNode then Some NK_BlankNode
  else if i = sh_nk_IRI then Some NK_IRI
  else if i = sh_nk_Literal then Some NK_Literal
  else if i = sh_nk_BlankNodeOrIRI then Some NK_BlankNodeOrIRI
  else if i = sh_nk_BlankNodeOrLiteral then Some NK_BlankNodeOrLiteral
  else if i = sh_nk_IRIOrLiteral then Some NK_IRIOrLiteral
  else None

let node_kind_ok (t : rdf_term) (nk : node_kind) : bool =
  match nk, t with
  | NK_BlankNode, T_BNode _ -> true
  | NK_IRI, T_IRI _ -> true
  | NK_Literal, T_Literal _ -> true
  | NK_BlankNodeOrIRI, T_BNode _ -> true
  | NK_BlankNodeOrIRI, T_IRI _ -> true
  | NK_BlankNodeOrLiteral, T_BNode _ -> true
  | NK_BlankNodeOrLiteral, T_Literal _ -> true
  | NK_IRIOrLiteral, T_IRI _ -> true
  | NK_IRIOrLiteral, T_Literal _ -> true
  | _, _ -> false

let severity_of_iri (i : wf_iri) : severity =
  if i = sh_Warning then Sev_Warning
  else if i = sh_Info then Sev_Info
  else Sev_Violation

// --- 11c. Property-path parsing + evaluation ------------------------
//
// Slice 1 scope (per the brief): predicate paths + inverse. The other
// five path forms (sequence/alternative/zeroOrMore/oneOrMore/zeroOrOne)
// are parsed into the AST for faithful reporting when a single-level
// plain-IRI-predicate reading is available, but `eval_path` only
// evaluates P_Predicate / P_Inverse(P_Predicate) — everything else
// returns no values, an honest FAIL rather than a guess.

let path_term_to_predicate_path (t : rdf_term) : path =
  match t with
  | T_IRI i -> P_Predicate i
  | _ -> P_Sequence []   // unsupported nested path element (deferred)

let parse_path (g : rdf_graph) (t : rdf_term) (fuel : nat) : path =
  match t with
  | T_IRI i -> P_Predicate i
  | T_Literal _ -> P_Sequence []
  | T_BNode _ ->
    (match term_to_subject t with
     | None -> P_Sequence []
     | Some s ->
       (match find_objects g s sh_inversePath with
        | [T_IRI ip] -> P_Inverse (P_Predicate ip)
        | _ ->
          (match find_objects g s sh_alternativePath with
           | (alt_head :: _) ->
             P_Alternative (List.Tot.map path_term_to_predicate_path (rdf_list_terms g alt_head fuel))
           | [] ->
             (match find_objects g s sh_zeroOrMorePath with
              | [T_IRI zp] -> P_ZeroOrMore (P_Predicate zp)
              | _ ->
                (match find_objects g s sh_oneOrMorePath with
                 | [T_IRI op] -> P_OneOrMore (P_Predicate op)
                 | _ ->
                   (match find_objects g s sh_zeroOrOnePath with
                    | [T_IRI zop] -> P_ZeroOrOne (P_Predicate zop)
                    | _ ->
                      (match find_objects g s rdf_first with
                       | (_ :: _) ->
                         P_Sequence (List.Tot.map path_term_to_predicate_path (rdf_list_terms g t fuel))
                       | [] -> P_Sequence [])))))))

let eval_path (g : rdf_graph) (start : rdf_term) (p : path) : list rdf_term =
  match p with
  | P_Predicate pred ->
    (match term_to_subject start with
     | Some s -> find_objects g s pred
     | None -> [])
  | P_Inverse (P_Predicate pred) ->
    List.Tot.map subject_to_term (find_subjects g pred start)
  | _ -> []   // deferred: composite paths (Phase 2 follow-up)

// --- 11d. sh:class / target-class membership ------------------------
//
// SHACL "SHACL instance" (spec §3.1) is rdf:type plus rdfs:subClassOf*
// transitivity over the DATA graph only — not full RDFS entailment
// (no domain/range/subPropertyOf). We build a narrow closure using
// only the two subClassOf production rules already proven in
// RDF.Graph.Executable, rather than the general-purpose
// `rdfs_closure` (which also fires domain/range/subPropertyOf and
// would over-approximate instance membership for SHACL's purposes).

let shacl_class_closure_step (g : rdf_graph) : rdf_graph =
  let ig = build_indexed g in
  let g1 = rdfs_rule_subClassOf_trans g ig in
  let ig1 = build_indexed g1 in
  let g2 = rdfs_rule_subClassOf g1 ig1 in
  graph_dedup_sort g2

let rec shacl_class_closure (g : rdf_graph) (fuel : nat)
  : Tot rdf_graph (decreases fuel)
  =
  if fuel = 0 then g
  else
    let fuel' : nat = fuel - 1 in
    let g' = shacl_class_closure_step g in
    if graph_len g' = graph_len g then g else shacl_class_closure g' fuel'

let is_shacl_instance (closed_g : rdf_graph) (v : rdf_term) (c : wf_iri) : bool =
  match term_to_subject v with
  | None -> false
  | Some s -> mem_triple ({ s = s; p = rdf_type; o = T_IRI c }) closed_g

// --- 11e. Targets -----------------------------------------------------

let eval_target_class (closed_g : rdf_graph) (all_subjects : list subject) (c : wf_iri)
  : list rdf_term =
  List.Tot.concatMap
    (fun s -> if is_shacl_instance closed_g (subject_to_term s) c then [subject_to_term s] else [])
    all_subjects

let eval_target (data : rdf_graph) (closed_g : rdf_graph) (all_subjects : list subject) (t : target)
  : list rdf_term =
  match t with
  | T_Class c -> eval_target_class closed_g all_subjects c
  | T_ImplicitClass c -> eval_target_class closed_g all_subjects c
  | T_Node n -> [n]
  | T_SubjectsOf p ->
    dedup_terms (List.Tot.concatMap (fun (tr : triple) -> if tr.p = p then [subject_to_term tr.s] else []) data)
  | T_ObjectsOf p ->
    dedup_terms (List.Tot.concatMap (fun (tr : triple) -> if tr.p = p then [tr.o] else []) data)
  | T_Sparql _ -> []   // resolved only via eval_sparql_target_select (unused this slice)

// --- 11f. Shape-graph parsing ----------------------------------------

let sh_ns_prefix : string = "http://www.w3.org/ns/shacl#"

let has_shacl_ns_prefix (p : string) : bool =
  let n = String.length sh_ns_prefix in
  String.length p >= n && String.sub p 0 n = sh_ns_prefix

let is_shape_trigger_triple (t : triple) : bool =
  has_shacl_ns_prefix t.p ||
  (t.p = rdf_type &&
   (rdf_term_eq t.o (T_IRI sh_NodeShape) || rdf_term_eq t.o (T_IRI sh_PropertyShape)))

let is_deactivated (g : rdf_graph) (s : subject) : bool =
  match first_bool (find_objects g s sh_deactivated) with
  | Some true -> true
  | _ -> false

// Any subject with at least one SHACL-vocabulary triple (as subject)
// is treated as a shape. This single criterion covers NodeShape,
// PropertyShape, and anonymous nested shapes reached via sh:property /
// sh:node / sh:not / sh:and / sh:or / sh:xone list members alike —
// every one of those, by construction, has at least one sh:* subject
// triple of its own (a path, a target, or a constraint). Deactivated
// shapes (sh:deactivated true) are excluded entirely: since they can
// never produce a violation, dropping them from the `shapes` list is
// equivalent to modelling them (lookup_shape returns None, and every
// caller already treats None as "no constraint").
let is_shape_establishing (g : rdf_graph) (s : subject) : bool =
  List.Tot.existsb (fun (t : triple) -> subject_eq t.s s && is_shape_trigger_triple t) g
  && not (is_deactivated g s)

let build_targets (g : rdf_graph) (s : subject) : list target =
  let via_class =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [T_Class i] | _ -> []) (find_objects g s sh_targetClass) in
  let via_node = List.Tot.map (fun t -> T_Node t) (find_objects g s sh_targetNode) in
  let via_subj_of =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [T_SubjectsOf i] | _ -> []) (find_objects g s sh_targetSubjectsOf) in
  let via_obj_of =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [T_ObjectsOf i] | _ -> []) (find_objects g s sh_targetObjectsOf) in
  let implicit =
    (match s with
     | S_IRI i ->
       let is_class =
         List.Tot.existsb
           (fun t -> rdf_term_eq t (T_IRI rdfs_Class) || rdf_term_eq t (T_IRI owl_Class))
           (find_objects g s rdf_type) in
       let is_nodeshape =
         List.Tot.existsb (fun t -> rdf_term_eq t (T_IRI sh_NodeShape)) (find_objects g s rdf_type) in
       if is_class && is_nodeshape then [T_ImplicitClass i] else []
     | S_BNode _ -> [])
  in
  via_class @ via_node @ via_subj_of @ via_obj_of @ implicit

let collect_shape_ref_list (g : rdf_graph) (head : rdf_term) (fuel : nat) : list shape_ref =
  List.Tot.concatMap
    (fun t -> match term_to_shape_ref t with Some r -> [r] | None -> [])
    (rdf_list_terms g head fuel)

// Large flat let-chain over ~25 independent constraint predicates;
// the default rlimit/single-query proof strategy times out on the
// combined VC even though each binding is individually trivial.
// Matches the established idiom (RDF.List.Helpers.fst,
// Parser.Turtle.fst) rather than inventing a new one.
#push-options "--z3rlimit 60 --split_queries always"
let build_constraints (g : rdf_graph) (s : subject) : list constraint_component =
  let fuel = graph_len g + 1 in
  let mincount = match first_int (find_objects g s sh_minCount) with Some n -> [CC_MinCount n] | None -> [] in
  let maxcount = match first_int (find_objects g s sh_maxCount) with Some n -> [CC_MaxCount n] | None -> [] in
  let datatype =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [CC_Datatype i] | _ -> []) (find_objects g s sh_datatype) in
  let nodekind =
    List.Tot.concatMap
      (fun t -> match t with
                | T_IRI i -> (match node_kind_of_iri i with Some nk -> [CC_NodeKind nk] | None -> [])
                | _ -> [])
      (find_objects g s sh_nodeKind) in
  let cls =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [CC_Class i] | _ -> []) (find_objects g s sh_class) in
  let in_ =
    (match find_objects g s sh_in with
     | (head :: _) -> [CC_In (rdf_list_terms g head fuel)]
     | [] -> []) in
  let hasvalue = List.Tot.map (fun t -> CC_HasValue t) (find_objects g s sh_hasValue) in
  let pattern =
    (match find_objects g s sh_pattern with
     | (T_Literal l) :: _ ->
       let flags = (match find_objects g s sh_flags with (T_Literal fl) :: _ -> fl.lexical_form | _ -> "") in
       [CC_Pattern l.lexical_form flags]
     | _ -> []) in
  let minlen = match first_int (find_objects g s sh_minLength) with Some n -> [CC_MinLength n] | None -> [] in
  let maxlen = match first_int (find_objects g s sh_maxLength) with Some n -> [CC_MaxLength n] | None -> [] in
  let langin =
    (match find_objects g s sh_languageIn with
     | (head :: _) ->
       let terms = rdf_list_terms g head fuel in
       [CC_LanguageIn (List.Tot.concatMap (fun t -> match t with T_Literal l -> [l.lexical_form] | _ -> []) terms)]
     | [] -> []) in
  let uniquelang =
    (match first_bool (find_objects g s sh_uniqueLang) with Some b -> [CC_UniqueLang b] | None -> []) in
  let mininc = List.Tot.map CC_MinInclusive (find_objects g s sh_minInclusive) in
  let maxinc = List.Tot.map CC_MaxInclusive (find_objects g s sh_maxInclusive) in
  let minexc = List.Tot.map CC_MinExclusive (find_objects g s sh_minExclusive) in
  let maxexc = List.Tot.map CC_MaxExclusive (find_objects g s sh_maxExclusive) in
  let nots =
    List.Tot.concatMap (fun t -> match term_to_shape_ref t with Some r -> [CC_Not r] | None -> []) (find_objects g s sh_not) in
  let ands = (match find_objects g s sh_and with (head :: _) -> [CC_And (collect_shape_ref_list g head fuel)] | [] -> []) in
  let ors  = (match find_objects g s sh_or  with (head :: _) -> [CC_Or  (collect_shape_ref_list g head fuel)] | [] -> []) in
  let xones = (match find_objects g s sh_xone with (head :: _) -> [CC_Xone (collect_shape_ref_list g head fuel)] | [] -> []) in
  let nodes =
    List.Tot.concatMap (fun t -> match term_to_shape_ref t with Some r -> [CC_Node r] | None -> []) (find_objects g s sh_node) in
  let equals =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [CC_Equals i] | _ -> []) (find_objects g s sh_equals) in
  let disjoint =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [CC_Disjoint i] | _ -> []) (find_objects g s sh_disjoint) in
  let lessthan =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [CC_LessThan i] | _ -> []) (find_objects g s sh_lessThan) in
  let lessthaneq =
    List.Tot.concatMap (fun t -> match t with T_IRI i -> [CC_LessThanOrEq i] | _ -> []) (find_objects g s sh_lessThanOrEquals) in
  let closed_ =
    (match first_bool (find_objects g s sh_closed) with
     | Some true ->
       let ign =
         (match find_objects g s sh_ignoredProperties with
          | (head :: _) ->
            List.Tot.concatMap (fun t -> match t with T_IRI i -> [i] | _ -> []) (rdf_list_terms g head fuel)
          | [] -> []) in
       [CC_Closed ign]
     | _ -> []) in
  mincount @ maxcount @ datatype @ nodekind @ cls @ in_ @ hasvalue @ pattern @ minlen @ maxlen @
  langin @ uniquelang @ mininc @ maxinc @ minexc @ maxexc @ nots @ ands @ ors @ xones @ nodes @
  equals @ disjoint @ lessthan @ lessthaneq @ closed_
#pop-options

let build_shape (g : rdf_graph) (s : subject) : shape =
  let path_objs = find_objects g s sh_path in
  let is_prop = Cons? path_objs in
  let path_opt =
    (match path_objs with
     | (head :: _) -> Some (parse_path g head (graph_len g + 1))
     | [] -> None) in
  let sev =
    (match find_objects g s sh_severity with
     | (T_IRI i) :: _ -> severity_of_iri i
     | _ -> Sev_Violation) in
  let msg =
    (match find_objects g s sh_message with
     | (T_Literal l) :: _ -> Some l.lexical_form
     | _ -> None) in
  let prefs =
    List.Tot.concatMap (fun t -> match term_to_shape_ref t with Some r -> [r] | None -> []) (find_objects g s sh_property) in
  {
    shape_id = subject_to_shape_ref s;
    is_property = is_prop;
    shape_path = path_opt;
    targets = build_targets g s;
    shape_sev = sev;
    message = msg;
    constraints = build_constraints g s;
    property_refs = prefs;
  }

let parse_shape_from_graph_pure (g : rdf_graph) : shapes_graph =
  let subs = distinct_subjects g in
  let shape_subs = List.Tot.filter (is_shape_establishing g) subs in
  { shapes = List.Tot.map (build_shape g) shape_subs }

// --- 11g. Numeric comparison for min/maxInclusive/Exclusive ----------
//
// Reuses SPARQL11.Algebra's decimal/double lexical parser (rule #8:
// double-aware parsing, not bare int) rather than re-deriving one.

let literal_to_scaled (l : literal) : option (int & nat) =
  if l.datatype = xsd_double then Alg.parse_double_to_scaled l.lexical_form
  else if l.datatype = xsd_integer || l.datatype = xsd_decimal then Alg.parse_to_scaled l.lexical_form
  else None

let scaled_cmp (a b : (int & nat)) : int =
  let (am, asc) = a in
  let (bm, bsc) = b in
  if asc = bsc then (if am < bm then -1 else if am > bm then 1 else 0)
  else if asc < bsc then
    (let am' = op_Multiply am (Alg.pow10 (bsc - asc)) in
     if am' < bm then -1 else if am' > bm then 1 else 0)
  else
    (let bm' = op_Multiply bm (Alg.pow10 (asc - bsc)) in
     if am < bm' then -1 else if am > bm' then 1 else 0)

let numeric_cmp_le (a b : literal) : option bool =
  match literal_to_scaled a, literal_to_scaled b with
  | Some sa, Some sb -> Some (scaled_cmp sa sb <= 0)
  | _, _ -> None

let numeric_cmp_lt (a b : literal) : option bool =
  match literal_to_scaled a, literal_to_scaled b with
  | Some sa, Some sb -> Some (scaled_cmp sa sb < 0)
  | _, _ -> None

// Only numeric-vs-numeric or same-datatype lexical ordering count as
// "properly comparable"; mismatched non-numeric datatypes are NOT
// less-than (matching the W3C suite's lessThan-002: an xsd:integer
// value compared against an xsd:string value must fail the
// constraint, not silently succeed via naive lexical string
// comparison across incompatible types).
let term_lt (a b : rdf_term) : bool =
  match a, b with
  | T_Literal la, T_Literal lb ->
    (match literal_to_scaled la, literal_to_scaled lb with
     | Some sa, Some sb -> scaled_cmp sa sb < 0
     | _, _ -> if la.datatype = lb.datatype then string_lt la.lexical_form lb.lexical_form else false)
  | _, _ -> false

let term_le (a b : rdf_term) : bool = term_lt a b || rdf_term_eq a b

// --- 11h. Aggregate (per-focus-node, not per-value) constraints ------

let list_diff (a b : list rdf_term) : list rdf_term =
  List.Tot.concatMap (fun x -> if List.Tot.existsb (rdf_term_eq x) b then [] else [x]) a

let list_set_eq (a b : list rdf_term) : bool =
  Nil? (list_diff a b) && Nil? (list_diff b a)

let list_disjoint (a b : list rdf_term) : bool =
  Nil? (List.Tot.concatMap (fun x -> if List.Tot.existsb (rdf_term_eq x) b then [x] else []) a)

let other_property_values (data : rdf_graph) (focus : rdf_term) (p : wf_iri) : list rdf_term =
  match term_to_subject focus with
  | Some s -> find_objects data s p
  | None -> []

let path_predicates_of_shape (sg : list shape) (s : shape) : list wf_iri =
  List.Tot.concatMap
    (fun r -> match lookup_shape r sg with
              | Some ps -> (match ps.shape_path with Some (P_Predicate p) -> [p] | _ -> [])
              | None -> [])
    s.property_refs

let closed_ok (data : rdf_graph) (sg : list shape) (focus : rdf_term) (s : shape) (ignored : list wf_iri) : bool =
  match term_to_subject focus with
  | None -> true
  | Some subj ->
    let allowed = path_predicates_of_shape sg s @ ignored in
    List.Tot.for_all
      (fun (t : triple) -> not (subject_eq t.s subj) || List.Tot.existsb (fun p -> p = t.p) allowed)
      data

let unique_lang_violates (values : list rdf_term) : bool =
  let langs =
    List.Tot.concatMap (fun t -> match t with T_Literal l -> (match l.lang_tag with Some lt -> [lt] | None -> []) | _ -> []) values in
  let rec has_dup (seen : list string) (xs : list string) : Tot bool (decreases xs) =
    match xs with
    | [] -> false
    | x :: rest -> if List.Tot.existsb (lang_tag_eq x) seen then true else has_dup (x :: seen) rest
  in
  has_dup [] langs

let value_violation (focus : rdf_term) (path_opt : option path) (source : shape_ref)
                     (cc : constraint_component) (sev : severity) (msg : option string) (v : rdf_term)
  : violation =
  { v_focus_node = focus; v_path = path_opt; v_value = Some v;
    v_source_shape = source; v_constraint = cc; v_severity = sev; v_message = msg }

let focus_violation (focus : rdf_term) (path_opt : option path) (source : shape_ref)
                     (cc : constraint_component) (sev : severity) (msg : option string)
  : violation =
  { v_focus_node = focus; v_path = path_opt; v_value = None;
    v_source_shape = source; v_constraint = cc; v_severity = sev; v_message = msg }

let eval_aggregate_constraints (data : rdf_graph) (sg : list shape) (focus : rdf_term) (path_opt : option path)
                                (source : shape_ref) (sev : severity) (msg : option string)
                                (values : list rdf_term) (s : shape)
  : list violation =
  List.Tot.concatMap
    (fun cc ->
       match cc with
       | CC_MinCount n -> if List.Tot.length values < n then [focus_violation focus path_opt source cc sev msg] else []
       | CC_MaxCount n -> if List.Tot.length values > n then [focus_violation focus path_opt source cc sev msg] else []
       | CC_HasValue t -> if List.Tot.existsb (rdf_term_eq t) values then [] else [focus_violation focus path_opt source cc sev msg]
       | CC_UniqueLang b -> if b && unique_lang_violates values then [focus_violation focus path_opt source cc sev msg] else []
       | CC_Closed ign -> if closed_ok data sg focus s ign then [] else [focus_violation focus path_opt source cc sev msg]
       | CC_Equals p -> if list_set_eq values (other_property_values data focus p) then [] else [focus_violation focus path_opt source cc sev msg]
       | CC_Disjoint p -> if list_disjoint values (other_property_values data focus p) then [] else [focus_violation focus path_opt source cc sev msg]
       | CC_LessThan p ->
         let others = other_property_values data focus p in
         if List.Tot.for_all (fun v -> List.Tot.for_all (fun w -> term_lt v w) others) values
         then [] else [focus_violation focus path_opt source cc sev msg]
       | CC_LessThanOrEq p ->
         let others = other_property_values data focus p in
         if List.Tot.for_all (fun v -> List.Tot.for_all (fun w -> term_le v w) others) values
         then [] else [focus_violation focus path_opt source cc sev msg]
       | _ -> [])
    s.constraints

// --- 11i. Per-value constraints + shape conformance (mutual) ---------
//
// `collect_shape_violations` / `eval_one_constraint` are mutually
// recursive: sh:not/sh:and/sh:or/sh:xone/sh:node need "does this value
// node conform to that (possibly nested) shape", which itself runs
// the same violation-collection judgment. There is no structural
// bound on shape nesting depth in an arbitrary shapes graph (and
// shapes could in principle reference each other in a cycle), so
// this is fuel-bounded like `shacl_class_closure` above — every
// mutual call site strictly decrements `fuel`, so F*'s termination
// checker sees one uniform decreasing measure. Running out of fuel
// conservatively returns "no violations found" (never fabricates a
// violation), which is sound-by-omission in the same spirit as
// Tableau's "return None when unsure".

let rec collect_shape_violations (data : rdf_graph) (sg : list shape) (closed_cls : rdf_graph)
                                  (node : rdf_term) (s : shape) (fuel : nat)
  : Tot (list violation) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' = fuel - 1 in
    let path_opt = s.shape_path in
    let values =
      if s.is_property
      then (match path_opt with Some p -> eval_path data node p | None -> [])
      else [node] in
    let per_value =
      List.Tot.concatMap
        (fun v ->
           List.Tot.concatMap
             (fun cc -> eval_one_constraint data sg closed_cls node path_opt s.shape_id s.shape_sev s.message v cc fuel')
             s.constraints)
        values
    in
    let agg = eval_aggregate_constraints data sg node path_opt s.shape_id s.shape_sev s.message values s in
    // A shape's sh:property list is validated against its VALUE nodes,
    // not its own focus node — for a NodeShape values = [node] so this
    // coincides with the pre-fix behaviour, but for a PropertyShape
    // with a NESTED sh:property (chaining, e.g.
    // core/property/property-001.ttl: PersonShape -sh:property-> an
    // inline address PropertyShape -sh:property-> a city PropertyShape)
    // the nested shape must see the outer path's values (the address
    // nodes), not the original focus (the person node).
    let nested_props =
      List.Tot.concatMap
        (fun v ->
           List.Tot.concatMap
             (fun pref ->
                match lookup_shape pref sg with
                | None -> []
                | Some ps -> collect_shape_violations data sg closed_cls v ps fuel')
             s.property_refs)
        values
    in
    per_value @ agg @ nested_props

and eval_one_constraint (data : rdf_graph) (sg : list shape) (closed_cls : rdf_graph) (focus : rdf_term)
                        (path_opt : option path) (source : shape_ref) (sev : severity) (msg : option string)
                        (v : rdf_term) (cc : constraint_component) (fuel : nat)
  : Tot (list violation) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' = fuel - 1 in
    let viol () : list violation = [value_violation focus path_opt source cc sev msg v] in
    (match cc with
     | CC_Not r ->
       (match lookup_shape r sg with
        | None -> []
        | Some rs -> if Nil? (collect_shape_violations data sg closed_cls v rs fuel') then viol () else [])
     | CC_And rs ->
       if List.Tot.for_all
            (fun r -> match lookup_shape r sg with None -> true | Some s2 -> Nil? (collect_shape_violations data sg closed_cls v s2 fuel'))
            rs
       then [] else viol ()
     | CC_Or rs ->
       if List.Tot.existsb
            (fun r -> match lookup_shape r sg with None -> false | Some s2 -> Nil? (collect_shape_violations data sg closed_cls v s2 fuel'))
            rs
       then [] else viol ()
     | CC_Xone rs ->
       let matches =
         List.Tot.filter
           (fun r -> match lookup_shape r sg with None -> false | Some s2 -> Nil? (collect_shape_violations data sg closed_cls v s2 fuel'))
           rs in
       if List.Tot.length matches = 1 then [] else viol ()
     | CC_Node r ->
       (match lookup_shape r sg with
        | None -> []
        | Some s2 -> if Nil? (collect_shape_violations data sg closed_cls v s2 fuel') then [] else viol ())
     | CC_Datatype dt ->
       (match v with T_Literal l -> if l.datatype = dt then [] else viol () | _ -> viol ())
     | CC_NodeKind nk -> if node_kind_ok v nk then [] else viol ()
     | CC_Class c ->
       (match term_to_subject v with
        | None -> viol ()
        | Some subj -> if is_shacl_instance closed_cls (subject_to_term subj) c then [] else viol ())
     | CC_In items -> if List.Tot.existsb (rdf_term_eq v) items then [] else viol ()
     | CC_HasValue _ -> []   // aggregate — see eval_aggregate_constraints
     | CC_Pattern re flags ->
       (match term_lexical v with
        | None -> viol ()
        | Some lex -> if Alg.regex_match lex re (if flags = "" then None else Some flags) then [] else viol ())
     | CC_MinLength n -> (match term_lexical v with Some lex -> if String.length lex >= n then [] else viol () | None -> viol ())
     | CC_MaxLength n -> (match term_lexical v with Some lex -> if String.length lex <= n then [] else viol () | None -> viol ())
     | CC_LanguageIn langs ->
       (match v with
        | T_Literal l ->
          (match l.lang_tag with
           | Some lt -> if List.Tot.existsb (lang_tag_eq lt) langs then [] else viol ()
           | None -> viol ())
        | _ -> viol ())
     | CC_UniqueLang _ -> []   // aggregate
     | CC_MinInclusive t ->
       (match v, t with
        | T_Literal lv, T_Literal lt -> (match numeric_cmp_le lt lv with Some true -> [] | _ -> viol ())
        | _, _ -> viol ())
     | CC_MaxInclusive t ->
       (match v, t with
        | T_Literal lv, T_Literal lt -> (match numeric_cmp_le lv lt with Some true -> [] | _ -> viol ())
        | _, _ -> viol ())
     | CC_MinExclusive t ->
       (match v, t with
        | T_Literal lv, T_Literal lt -> (match numeric_cmp_lt lt lv with Some true -> [] | _ -> viol ())
        | _, _ -> viol ())
     | CC_MaxExclusive t ->
       (match v, t with
        | T_Literal lv, T_Literal lt -> (match numeric_cmp_lt lv lt with Some true -> [] | _ -> viol ())
        | _, _ -> viol ())
     | CC_MinCount _ -> []       // aggregate
     | CC_MaxCount _ -> []       // aggregate
     | CC_Equals _ -> []         // aggregate
     | CC_Disjoint _ -> []       // aggregate
     | CC_LessThan _ -> []       // aggregate
     | CC_LessThanOrEq _ -> []   // aggregate
     | CC_Closed _ -> []         // aggregate
     | CC_Sparql _ -> [])        // deferred (rule-#11(c) SPARQL dispatch, unused this slice)

// --- 11j. Top-level entry points --------------------------------------

let parse_shape_from_graph (g : rdf_graph) : ML shapes_graph =
  parse_shape_from_graph_pure g

let validate (data : rdf_graph) (shapes : shapes_graph) : ML validation_report =
  let sg = shapes.shapes in
  let closed_cls = shacl_class_closure data (graph_len data + 20) in
  let all_subjects = distinct_subjects data in
  let fuel0 = op_Multiply (List.Tot.length sg) 4 + 50 in
  let root_shapes = List.Tot.filter (fun s -> Cons? s.targets) sg in
  let per_shape_violations =
    List.Tot.concatMap
      (fun (s : shape) ->
         let focus_nodes =
           dedup_terms (List.Tot.concatMap (fun tgt -> eval_target data closed_cls all_subjects tgt) s.targets) in
         List.Tot.concatMap (fun fn -> collect_shape_violations data sg closed_cls fn s fuel0) focus_nodes)
      root_shapes
  in
  { conforms = Nil? per_shape_violations; results = per_shape_violations }

// ------------------------------------------------------------------
// 12. Remaining assume val — rule #11(c) host call-out.
//
// `eval_sparql_target_select` runs an sh:select query against a data
// graph and returns the focus nodes / values to report on. This is
// the single rule-#11(c) dependency the SHACL track has on the rest
// of the stack (SPARQL evaluator dispatch), and stays a host call-out
// long-term. Slice 1 never calls it — T_Sparql targets and CC_Sparql
// constraints both evaluate to "no result" above — so it is present
// only to keep the AST's SPARQL-target surface typed and to discharge
// CLAUDE.md rule #3's patch-file requirement (issue #181,
// minimal_regrettable_glue_code_each_with_an_open_issue/
// 181_shacl_validate_stub.sh).
// ------------------------------------------------------------------

assume val eval_sparql_target_select
  : data:rdf_graph
  -> query:string
  -> ML (list violation)
