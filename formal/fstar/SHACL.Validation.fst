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
open RDF.Graph.Executable

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
// 11. Validation entry-point — assume val.
//
// Acceptable per rule #11(c): the SPARQL-target case (sh:select) and
// path evaluation both call into the SPARQL evaluator, which lives
// in a downstream module (SPARQL11.Algebra / SPARQL11.Store). At
// extraction time the OCaml realisation in
//   181_shacl_validate_stub.sh
// wires `validate` to a thin OCaml dispatch that delegates to the
// extracted SPARQL evaluator. The pure-AST helpers above are total
// F*; only the evaluator dispatch requires the rule-#11 escape.
//
// Phase 2 splits this into:
//   - apply_constraint  : pure F* (datatype, in, hasValue, ...)
//   - eval_path         : pure F* (graph walk over path AST)
//   - eval_sparql_target: rule-#11(c) host call-out only for sh:select
// at which point this top-level assume val collapses to a pure
// orchestrator and the glue patch retires.
// ------------------------------------------------------------------

assume val validate
  : data:rdf_graph
  -> shapes:shapes_graph
  -> ML validation_report

// ------------------------------------------------------------------
// 12. Helper assume vals — Phase 2 will replace these with pure F*.
//
// `parse_shape_from_graph` reads the shape vocabulary out of an RDF
// graph and reconstructs the shape AST. Phase 2 makes it Tot.
//
// `eval_sparql_target_select` runs an sh:select query against a data
// graph and returns the focus nodes / values to report on. This one
// stays as a host call-out long-term; it is the single rule-#11(c)
// dependency the SHACL track has on the rest of the stack.
// ------------------------------------------------------------------

assume val parse_shape_from_graph
  : g:rdf_graph
  -> ML shapes_graph

assume val eval_sparql_target_select
  : data:rdf_graph
  -> query:string
  -> ML (list violation)
