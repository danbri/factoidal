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
// Phase 3 (issue #181 follow-up, sh:sparql dispatch): `parse_sparql` is
// the narrowest string -> query entry point (Tot, no ambient state) —
// see the section-13 doc comment below for why the whole dispatch stays
// pure F* rather than the ML host call-out originally planned in
// section 12.
module Parser11 = SPARQL11.Parser

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

// Report-serialization vocabulary (Phase 3, issue #181 follow-up).
// sh_Violation above doubles as both the severity individual AND (not
// needed here) — ValidationReport/ValidationResult are distinct classes.
let sh_ValidationReport : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#ValidationReport");
  "http://www.w3.org/ns/shacl#ValidationReport"
let sh_ValidationResult : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#ValidationResult");
  "http://www.w3.org/ns/shacl#ValidationResult"
let sh_result : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#result");
  "http://www.w3.org/ns/shacl#result"
let sh_conforms_pred : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#conforms");
  "http://www.w3.org/ns/shacl#conforms"
let sh_focusNode : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#focusNode");
  "http://www.w3.org/ns/shacl#focusNode"
let sh_resultPath : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#resultPath");
  "http://www.w3.org/ns/shacl#resultPath"
let sh_resultSeverity : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#resultSeverity");
  "http://www.w3.org/ns/shacl#resultSeverity"
let sh_resultMessage : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#resultMessage");
  "http://www.w3.org/ns/shacl#resultMessage"
let sh_sourceConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#sourceConstraintComponent");
  "http://www.w3.org/ns/shacl#sourceConstraintComponent"
let sh_sourceShape : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#sourceShape");
  "http://www.w3.org/ns/shacl#sourceShape"
let sh_sourceConstraint : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#sourceConstraint");
  "http://www.w3.org/ns/shacl#sourceConstraint"
let sh_value_pred : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#value");
  "http://www.w3.org/ns/shacl#value"

// Constraint-component IRIs (SHACL Core Appendix), one per
// `constraint_component` constructor. Used by report serialization's
// sh:sourceConstraintComponent triple.
let sh_MinCountConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MinCountConstraintComponent");
  "http://www.w3.org/ns/shacl#MinCountConstraintComponent"
let sh_MaxCountConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MaxCountConstraintComponent");
  "http://www.w3.org/ns/shacl#MaxCountConstraintComponent"
let sh_DatatypeConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#DatatypeConstraintComponent");
  "http://www.w3.org/ns/shacl#DatatypeConstraintComponent"
let sh_NodeKindConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#NodeKindConstraintComponent");
  "http://www.w3.org/ns/shacl#NodeKindConstraintComponent"
let sh_ClassConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#ClassConstraintComponent");
  "http://www.w3.org/ns/shacl#ClassConstraintComponent"
let sh_InConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#InConstraintComponent");
  "http://www.w3.org/ns/shacl#InConstraintComponent"
let sh_HasValueConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#HasValueConstraintComponent");
  "http://www.w3.org/ns/shacl#HasValueConstraintComponent"
let sh_PatternConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#PatternConstraintComponent");
  "http://www.w3.org/ns/shacl#PatternConstraintComponent"
let sh_MinLengthConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MinLengthConstraintComponent");
  "http://www.w3.org/ns/shacl#MinLengthConstraintComponent"
let sh_MaxLengthConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MaxLengthConstraintComponent");
  "http://www.w3.org/ns/shacl#MaxLengthConstraintComponent"
let sh_LanguageInConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#LanguageInConstraintComponent");
  "http://www.w3.org/ns/shacl#LanguageInConstraintComponent"
let sh_UniqueLangConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#UniqueLangConstraintComponent");
  "http://www.w3.org/ns/shacl#UniqueLangConstraintComponent"
let sh_MinInclusiveConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MinInclusiveConstraintComponent");
  "http://www.w3.org/ns/shacl#MinInclusiveConstraintComponent"
let sh_MaxInclusiveConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MaxInclusiveConstraintComponent");
  "http://www.w3.org/ns/shacl#MaxInclusiveConstraintComponent"
let sh_MinExclusiveConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MinExclusiveConstraintComponent");
  "http://www.w3.org/ns/shacl#MinExclusiveConstraintComponent"
let sh_MaxExclusiveConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#MaxExclusiveConstraintComponent");
  "http://www.w3.org/ns/shacl#MaxExclusiveConstraintComponent"
let sh_NotConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#NotConstraintComponent");
  "http://www.w3.org/ns/shacl#NotConstraintComponent"
let sh_AndConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#AndConstraintComponent");
  "http://www.w3.org/ns/shacl#AndConstraintComponent"
let sh_OrConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#OrConstraintComponent");
  "http://www.w3.org/ns/shacl#OrConstraintComponent"
let sh_XoneConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#XoneConstraintComponent");
  "http://www.w3.org/ns/shacl#XoneConstraintComponent"
let sh_NodeConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#NodeConstraintComponent");
  "http://www.w3.org/ns/shacl#NodeConstraintComponent"
let sh_QualifiedMinCountConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#QualifiedMinCountConstraintComponent");
  "http://www.w3.org/ns/shacl#QualifiedMinCountConstraintComponent"
let sh_QualifiedMaxCountConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#QualifiedMaxCountConstraintComponent");
  "http://www.w3.org/ns/shacl#QualifiedMaxCountConstraintComponent"
let sh_EqualsConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#EqualsConstraintComponent");
  "http://www.w3.org/ns/shacl#EqualsConstraintComponent"
let sh_DisjointConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#DisjointConstraintComponent");
  "http://www.w3.org/ns/shacl#DisjointConstraintComponent"
let sh_LessThanConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#LessThanConstraintComponent");
  "http://www.w3.org/ns/shacl#LessThanConstraintComponent"
let sh_LessThanOrEqualsConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#LessThanOrEqualsConstraintComponent");
  "http://www.w3.org/ns/shacl#LessThanOrEqualsConstraintComponent"
let sh_ClosedConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#ClosedConstraintComponent");
  "http://www.w3.org/ns/shacl#ClosedConstraintComponent"
let sh_SPARQLConstraintComponent : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#SPARQLConstraintComponent");
  "http://www.w3.org/ns/shacl#SPARQLConstraintComponent"

// sh:sparql / sh:prefixes / sh:declare vocabulary (Phase 3 sh:sparql
// dispatch; sh:select already defined above in section 1 — reused for
// both the SPARQL-target T_Sparql form and this CC_Sparql form).
let sh_sparql : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#sparql");
  "http://www.w3.org/ns/shacl#sparql"
let sh_prefixes : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#prefixes");
  "http://www.w3.org/ns/shacl#prefixes"
let sh_declare : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#declare");
  "http://www.w3.org/ns/shacl#declare"
let sh_decl_prefix : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#prefix");
  "http://www.w3.org/ns/shacl#prefix"
let sh_decl_namespace : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#namespace");
  "http://www.w3.org/ns/shacl#namespace"
// sh:prefixes collects sh:declare nodes TRANSITIVELY through
// owl:imports (SHACL spec, "Prefix Declarations for SPARQL Queries":
// prefix declarations reachable via owl:imports apply too —
// sparql/node/prefixes-001.ttl imports one prefix set from another).
let owl_imports_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#imports");
  "http://www.w3.org/2002/07/owl#imports"

// ------------------------------------------------------------------
// 2. Severity. SHACL defines three; default is sh:Violation.
// ------------------------------------------------------------------

type severity =
  | Sev_Info
  | Sev_Warning
  | Sev_Violation
  // Any other IRI used as the value of sh:severity — the spec places
  // no constraint on severity values beyond being IRIs
  // (core/misc/severity-002.ttl uses a custom ex:MySeverity and the
  // suite expects it back verbatim as sh:resultSeverity).
  | Sev_Custom : wf_iri -> severity

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
  // sh:qualifiedValueShape + sh:qualifiedMinCount / sh:qualifiedMaxCount
  // (Phase 2 slice 2, issue #181 follow-up). Split into two
  // constructors — mirroring CC_MinCount/CC_MaxCount — so a single
  // qualified group that fails BOTH bounds reports two distinct
  // violations, one per constraint component. Each carries: the
  // qualifiedValueShape's shape_ref, the count bound, and the
  // sh:qualifiedValueShapesDisjoint flag (default false when absent).
  // Only constructed when sh:qualifiedValueShape itself resolves to a
  // shape_ref — qualifiedMinCount/MaxCount/Disjoint present WITHOUT a
  // qualifiedValueShape are per-spec not applicable and must not be
  // evaluated as a bare cardinality check on the raw value set (see
  // core/node/qualified-001: a NodeShape with qualifiedMinCount 5 /
  // qualifiedMaxCount 2 / qualifiedValueShapesDisjoint but NO
  // qualifiedValueShape must validate as if none of the three were
  // present).
  | CC_QualifiedMinCount : shape_ref -> nat -> bool -> constraint_component
  | CC_QualifiedMaxCount : shape_ref -> nat -> bool -> constraint_component
  // Property-pair constraints.
  | CC_Equals       : wf_iri -> constraint_component
  | CC_Disjoint     : wf_iri -> constraint_component
  | CC_LessThan     : wf_iri -> constraint_component
  | CC_LessThanOrEq : wf_iri -> constraint_component
  // Closed-shape constraint.
  | CC_Closed       : ignored:list wf_iri -> constraint_component
  // SPARQL-based constraint (sh:sparql / sh:select), Phase 3 (issue
  // #181 follow-up). Carries: the sh:sparql constraint node's own
  // shape_ref (reported as sh:sourceConstraint — distinct from the
  // owning shape, which is sh:sourceShape), the fully prefix-headered
  // SELECT query text (sh:prefixes/sh:declare already resolved to
  // `PREFIX p: <ns>` lines at parse time; `$PATH`/`$this` are NOT yet
  // substituted — that needs the shape's own `shape_path` and the
  // current focus node, both only available at evaluation time, see
  // section 13), and the constraint node's own sh:message (distinct
  // from — and takes priority over — the owning shape's sh:message).
  | CC_Sparql       : constraint_node:shape_ref -> query:string -> message:option wf_literal -> constraint_component

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
  // The full sh:message literal, not just its lexical form —
  // core/misc/message-001.ttl asserts the @en language tag survives
  // into sh:resultMessage verbatim.
  message      : option wf_literal;
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
  v_message       : option wf_literal;
  // sh:sourceConstraint — populated only for CC_Sparql (the sh:sparql
  // constraint node itself, distinct from v_source_shape). None for
  // every built-in constraint component: the suite's own core
  // fixtures never assert sh:sourceConstraint on non-SPARQL results
  // (per the spec's isomorphism-comparison rules, an implementation
  // is not required to produce it at all outside SPARQL constraints).
  v_source_constraint : option rdf_term;
}

noeq type validation_report = {
  conforms   : bool;
  results    : list violation;
  // Phase 3 (issue #181 follow-up): set when evaluating a sh:sparql
  // constraint's SELECT query failed outright (SPARQL parse error —
  // e.g. an unsupported construct like SERVICE or MINUS). Distinct
  // from `results`/`conforms`: a failed sh:sparql evaluation is not
  // the same as "no violation found". Mirrors the W3C SHACL-SPARQL
  // suite's `sht:Failure` expected outcome, which the runner maps
  // this field onto directly rather than raising an OCaml exception
  // (keeping `validate` a total, pure function — see section 13).
  report_failure : option string;
}

let conforming_report : validation_report =
  { conforms = true; results = []; report_failure = None }

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

// Inverse of term_to_shape_ref/subject_to_shape_ref — needed by report
// serialization (section 14) to render sh:sourceShape / sh:sourceConstraint
// as an rdf_term. Every shape_ref in practice comes from one of those two
// functions, so it is always either "_:"-prefixed (a bnode label) or a
// well-formed IRI; the `is_iri` guard makes that provable to F* at the
// `T_IRI` call site instead of needing an assume.
let shape_ref_to_term (r : shape_ref) : rdf_term =
  if String.length r >= 2 && String.sub r 0 2 = "_:"
  then T_BNode (String.sub r 2 (String.length r - 2))
  else if is_iri r then T_IRI r
  else T_BNode r  // defensive fallback; not reachable via the two builders above

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
let sh_qualifiedValueShape : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#qualifiedValueShape");
  "http://www.w3.org/ns/shacl#qualifiedValueShape"
let sh_qualifiedMinCount : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#qualifiedMinCount");
  "http://www.w3.org/ns/shacl#qualifiedMinCount"
let sh_qualifiedMaxCount : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#qualifiedMaxCount");
  "http://www.w3.org/ns/shacl#qualifiedMaxCount"
let sh_qualifiedValueShapesDisjoint : wf_iri =
  assert_norm (is_iri "http://www.w3.org/ns/shacl#qualifiedValueShapesDisjoint");
  "http://www.w3.org/ns/shacl#qualifiedValueShapesDisjoint"
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
  else if i = sh_Violation then Sev_Violation
  else Sev_Custom i

// --- 11c. Property-path parsing + evaluation ------------------------
//
// Phase 2 slice 2 (issue #181 follow-up): full composite-path support.
// `parse_path` recurses into `parse_path_list` for sequence/alternative
// list ELEMENTS (each element can itself be any path expression, e.g.
// an inline `[ sh:inversePath ex:p ]` blank node inside a sequence
// list — core/path/path-complex-002.ttl needs exactly this: a
// two-element `sh:path` list whose elements are both inverse-path
// blank nodes, not plain IRIs). `sh:inversePath`'s own value is
// intentionally kept to the strict "exactly one plain IRI" reading
// (matching the Phase 1 behaviour) rather than being generalised to
// recurse into an arbitrary nested path. When a path node is
// deliberately AMBIGUOUS (both an rdf:first/rdf:rest list structure
// and a sh:*Path predicate on the same blank node —
// core/path/path-strange-001/002.ttl), the list/sequence reading wins:
// see the inline comment at the rdf:first match arm below.
//
// Both functions are fuel-bounded (not structurally recursive, since
// list length and the RDF list `rdf:first`/`rdf:rest` chain are runtime
// graph data, not the F* term's own structure) — same idiom as
// `rdf_list_terms` / `shacl_class_closure` elsewhere in this file.
// Running out of fuel degrades to `P_Sequence []` (an inert, empty-
// valued path), never fabricates a reading.

let rec parse_path (g : rdf_graph) (t : rdf_term) (fuel : nat)
  : Tot path (decreases fuel)
  =
  match fuel with
  | 0 -> P_Sequence []
  | _ ->
    let fuel' : nat = fuel - 1 in
    (match t with
     | T_IRI i -> P_Predicate i
     | T_Literal _ -> P_Sequence []
     | T_BNode _ ->
       (match term_to_subject t with
        | None -> P_Sequence []
        | Some s ->
          // rdf:first is checked FIRST (Phase 3 fix): a path node that
          // is an rdf:first/rdf:rest list is a SEQUENCE path even when
          // extra sh:*Path triples are piled onto the SAME node —
          // core/path/path-strange-001.ttl puts a plain-IRI-valued
          // sh:inversePath on the list head and expects the sequence
          // reading; path-strange-002.ttl puts a list-valued
          // sh:inversePath there and expects the same. (Per the spec a
          // well-formed path node satisfies EXACTLY ONE syntax rule, so
          // for well-formed inputs this ordering is unobservable; for
          // the deliberately ambiguous "strange" fixtures the suite's
          // expected reading is list-wins.)
          (match find_objects g s rdf_first with
           | (_ :: _) ->
             P_Sequence (parse_path_list g (rdf_list_terms g t fuel') fuel')
           | [] ->
             (match find_objects g s sh_inversePath with
              | [T_IRI ip] -> P_Inverse (P_Predicate ip)
              | _ ->
                (match find_objects g s sh_alternativePath with
                 | (alt_head :: _) ->
                   P_Alternative (parse_path_list g (rdf_list_terms g alt_head fuel') fuel')
                 | [] ->
                   (match find_objects g s sh_zeroOrMorePath with
                    | (zp_term :: _) -> P_ZeroOrMore (parse_path g zp_term fuel')
                    | [] ->
                      (match find_objects g s sh_oneOrMorePath with
                       | (op_term :: _) -> P_OneOrMore (parse_path g op_term fuel')
                       | [] ->
                         (match find_objects g s sh_zeroOrOnePath with
                          | (zop_term :: _) -> P_ZeroOrOne (parse_path g zop_term fuel')
                          | [] -> P_Sequence []))))))))

and parse_path_list (g : rdf_graph) (ts : list rdf_term) (fuel : nat)
  : Tot (list path) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' : nat = fuel - 1 in
    (match ts with
     | [] -> []
     | t :: rest -> parse_path g t fuel' :: parse_path_list g rest fuel')

// `path_invert p` computes the path whose forward evaluation from a
// node `x` yields exactly `{ y | y is reachable from x via p in
// reverse }` — i.e. algebraic inversion, used to push `P_Inverse` down
// to `P_Predicate` leaves so `eval_path_fuel` only ever walks the
// graph forwards. Standard property-path identities (De Morgan for
// paths): inverse distributes over sequence with element order
// reversed, distributes elementwise over alternative, commutes with
// the star/plus/optional operators, and inverse-of-inverse cancels.
// Structural recursion on `p` — always terminates (no fuel needed).
// `List.rev` is applied to the COMPLETED recursive result, never fed
// into a further recursive call, so it does not disturb the
// structural decrease that F*'s termination checker requires.
let rec path_invert (p : path) : Tot path (decreases p) =
  match p with
  | P_Predicate i -> P_Inverse (P_Predicate i)
  | P_Inverse p' -> p'
  | P_Sequence ps -> P_Sequence (List.rev (path_invert_list ps))
  | P_Alternative ps -> P_Alternative (path_invert_list ps)
  | P_ZeroOrMore p' -> P_ZeroOrMore (path_invert p')
  | P_OneOrMore p' -> P_OneOrMore (path_invert p')
  | P_ZeroOrOne p' -> P_ZeroOrOne (path_invert p')
and path_invert_list (ps : list path) : Tot (list path) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest -> path_invert p :: path_invert_list rest

// Composite path evaluation, value-node SET semantics (SHACL section
// 2.3.1 — order-insensitive, duplicates deduped). Every mutual call
// site strictly decrements `fuel` (uniform fuel-as-step-budget idiom,
// matching `collect_shape_violations`/`eval_one_constraint` below)
// rather than a structural measure, because the star operators
// (`P_ZeroOrMore`/`P_OneOrMore`) iterate a graph-data-dependent number
// of times with no bound visible in the F* term itself. Running out
// of fuel returns whatever has been accumulated so far — sound-by-
// omission (never fabricates an unreachable value), same spirit as
// `shacl_class_closure`'s fixpoint fallback.
//
// - `eval_seq_fuel` folds a sequence left-to-right over a *set* of
//   starting nodes (a singleton for the top-level call), dedeuping the
//   intermediate node-set after every hop — required by
//   core/path/path-sequence-duplicate-001.ttl, where two distinct
//   blank-node routes both reach the identical literal "value" and the
//   suite expects exactly one violation (NodeKindConstraintComponent),
//   not two, because the deduped value SET has size 1.
// - `eval_alt_fuel` unions the per-branch reachable sets.
// - `eval_plus_fuel` computes the >=1-step transitive closure via
//   fixpoint iteration (frontier growth stops => done); `P_ZeroOrMore`
//   is `{start} UNION OneOrMore-result`, `P_ZeroOrOne` is
//   `{start} UNION (one step)`.
let rec eval_path_fuel (g : rdf_graph) (start : rdf_term) (p : path) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' : nat = fuel - 1 in
    (match p with
     | P_Predicate pred ->
       (match term_to_subject start with
        | Some s -> find_objects g s pred
        | None -> [])
     | P_Inverse (P_Predicate pred) ->
       List.Tot.map subject_to_term (find_subjects g pred start)
     | P_Inverse p' -> eval_path_fuel g start (path_invert p') fuel'
     | P_Sequence ps -> eval_seq_fuel g [start] ps fuel'
     | P_Alternative ps -> eval_alt_fuel g start ps fuel'
     | P_ZeroOrMore p' -> dedup_terms (start :: eval_plus_fuel g (eval_path_fuel g start p' fuel') p' fuel')
     | P_OneOrMore p' -> dedup_terms (eval_plus_fuel g (eval_path_fuel g start p' fuel') p' fuel')
     | P_ZeroOrOne p' -> dedup_terms (start :: eval_path_fuel g start p' fuel'))

and eval_seq_fuel (g : rdf_graph) (starts : list rdf_term) (ps : list path) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' : nat = fuel - 1 in
    (match ps with
     | [] -> dedup_terms starts
     | p :: rest ->
       let nexts = dedup_terms (List.Tot.concatMap (fun s -> eval_path_fuel g s p fuel') starts) in
       eval_seq_fuel g nexts rest fuel')

and eval_alt_fuel (g : rdf_graph) (start : rdf_term) (ps : list path) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' : nat = fuel - 1 in
    dedup_terms (List.Tot.concatMap (fun p -> eval_path_fuel g start p fuel') ps)

and eval_plus_fuel (g : rdf_graph) (frontier : list rdf_term) (p : path) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel)
  =
  match fuel with
  | 0 -> dedup_terms frontier
  | _ ->
    let fuel' : nat = fuel - 1 in
    let nexts = dedup_terms (List.Tot.concatMap (fun s -> eval_path_fuel g s p fuel') frontier) in
    let combined = dedup_terms (frontier @ nexts) in
    if List.Tot.length combined <= List.Tot.length frontier
    then frontier
    else eval_plus_fuel g combined p fuel'

// Plain (non-fuel) entry point used by the shape-conformance walk
// below — sizes the fuel bound off the data graph, matching the
// `graph_len g + K` idiom used by `shacl_class_closure` /
// `parse_shape_from_graph_pure`'s callers.
let eval_path (g : rdf_graph) (start : rdf_term) (p : path) : list rdf_term =
  eval_path_fuel g start p (graph_len g + 50)

// Render a SHACL property path as SPARQL 1.1 property-path syntax
// (Phase 3, issue #181 follow-up — sh:sparql's `$PATH` textual
// substitution; see section 13's doc comment for why $PATH, unlike
// $this, is a textual substitution rather than a variable pre-bind).
// Structurally recursive on `p`/`ps` — no fuel needed, same shape as
// `path_invert`/`path_invert_list` above. `path_to_sparql_atom` is
// `path_to_sparql_expr`'s parenthesized twin (own match, not a
// `"(" ^ path_to_sparql_expr p ^ ")"` delegation — that would call the
// sibling function on the SAME `p`, which does not strictly decrease
// and fails F*'s termination check for a mutual group); every
// non-atomic sub-expression goes through the `_atom` form so the
// substituted text is unambiguous regardless of what surrounds `$PATH`
// in the query.
let rec path_to_sparql_expr (p : path) : Tot string (decreases p) =
  match p with
  | P_Predicate i -> "<" ^ i ^ ">"
  | P_Inverse p' -> "^" ^ path_to_sparql_atom p'
  | P_Sequence ps -> path_list_to_sparql "/" ps
  | P_Alternative ps -> path_list_to_sparql "|" ps
  | P_ZeroOrMore p' -> path_to_sparql_atom p' ^ "*"
  | P_OneOrMore p' -> path_to_sparql_atom p' ^ "+"
  | P_ZeroOrOne p' -> path_to_sparql_atom p' ^ "?"
and path_to_sparql_atom (p : path) : Tot string (decreases p) =
  match p with
  | P_Predicate i -> "<" ^ i ^ ">"
  | P_Inverse p' -> "(^" ^ path_to_sparql_atom p' ^ ")"
  | P_Sequence ps -> "(" ^ path_list_to_sparql "/" ps ^ ")"
  | P_Alternative ps -> "(" ^ path_list_to_sparql "|" ps ^ ")"
  | P_ZeroOrMore p' -> "(" ^ path_to_sparql_atom p' ^ "*)"
  | P_OneOrMore p' -> "(" ^ path_to_sparql_atom p' ^ "+)"
  | P_ZeroOrOne p' -> "(" ^ path_to_sparql_atom p' ^ "?)"
and path_list_to_sparql (sep : string) (ps : list path) : Tot string (decreases ps) =
  match ps with
  | [] -> ""
  | [p] -> path_to_sparql_atom p
  | p :: rest -> path_to_sparql_atom p ^ sep ^ path_list_to_sparql sep rest

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

// Factored out of `build_constraints`'s flat let-chain (own top-level
// VC, own rlimit budget) rather than inlined: the nested match depth
// here (qualifiedValueShape resolution gating three sibling
// predicates) pushed the combined let-chain's per-binding query over
// budget even under `--split_queries always` — see the doc comment on
// CC_QualifiedMinCount/MaxCount for why the gate exists.
let build_qualified_constraints (g : rdf_graph) (s : subject) : list constraint_component =
  match find_objects g s sh_qualifiedValueShape with
  | (qvs_term :: _) ->
    (match term_to_shape_ref qvs_term with
     | Some qref ->
       let qdisjoint =
         (match first_bool (find_objects g s sh_qualifiedValueShapesDisjoint) with
          | Some b -> b
          | None -> false) in
       let qmin_cc =
         (match first_int (find_objects g s sh_qualifiedMinCount) with
          | Some n -> [CC_QualifiedMinCount qref n qdisjoint]
          | None -> []) in
       let qmax_cc =
         (match first_int (find_objects g s sh_qualifiedMaxCount) with
          | Some n -> [CC_QualifiedMaxCount qref n qdisjoint]
          | None -> []) in
       qmin_cc @ qmax_cc
     | None -> [])
  | [] -> []

// --- sh:prefixes / sh:declare resolution (Phase 3 sh:sparql dispatch) -
//
// Builds the `PREFIX p: <ns>\n` header block a sh:sparql constraint's
// sh:select query needs before it can be handed to `Parser11.parse_sparql`
// (that parser has no ambient prefix map — unlike Turtle's `@prefix`,
// SPARQL PREFIX declarations must be textual, inside the query itself).
// sh:prefixes may point at MULTIPLE nodes (an ontology-style IRI, or a
// bnode/IRI carrying its own sh:declare list directly — both forms
// appear in the vendored suite, e.g. node/sparql-002.ttl uses the
// former, pre-binding-001.ttl the latter); each contributes zero or
// more sh:declare prefix-declaration nodes. Structural recursion on the
// declares list — no fuel needed (rdf_list_terms/rdf collection walks
// are the only fuel-bounded traversals in this file; sh:declare is a
// plain (possibly repeated) triple, not an RDF list).
let rec declares_to_header (g : rdf_graph) (decls : list rdf_term) : Tot string (decreases decls) =
  match decls with
  | [] -> ""
  | d :: rest ->
    (match term_to_subject d with
     | None -> declares_to_header g rest
     | Some ds ->
       let pfx = (match find_objects g ds sh_decl_prefix with (T_Literal l) :: _ -> Some l.lexical_form | _ -> None) in
       let ns  = (match find_objects g ds sh_decl_namespace with (T_Literal l) :: _ -> Some l.lexical_form | _ -> None) in
       (match pfx, ns with
        | Some p, Some n -> String.concat "" ["PREFIX "; p; ": <"; n; ">\n"; declares_to_header g rest]
        | _, _ -> declares_to_header g rest))

// Collect every sh:declare node reachable from the sh:prefixes value
// node(s), following owl:imports transitively (fuel-bounded,
// cycle-safe via the visited list) — see owl_imports_iri's doc comment.
let rec collect_declares (g : rdf_graph) (frontier : list rdf_term) (visited : list rdf_term) (fuel : nat)
  : Tot (list rdf_term) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    (match frontier with
     | [] -> []
     | n :: rest ->
       if List.Tot.existsb (rdf_term_eq n) visited
       then collect_declares g rest visited (fuel - 1)
       else
         (match term_to_subject n with
          | None -> collect_declares g rest (n :: visited) (fuel - 1)
          | Some ns ->
            let ds = find_objects g ns sh_declare in
            let imps = find_objects g ns owl_imports_iri in
            ds @ collect_declares g (imps @ rest) (n :: visited) (fuel - 1)))

let prefix_header_for (g : rdf_graph) (constraint_subj : subject) : string =
  let via_nodes = find_objects g constraint_subj sh_prefixes in
  let all_declares = collect_declares g via_nodes [] (graph_len g + 10) in
  declares_to_header g all_declares

// Factored out for the same reason as `build_qualified_constraints`
// (own top-level VC / rlimit budget) — see its doc comment.
let build_sparql_constraints (g : rdf_graph) (s : subject) : list constraint_component =
  List.Tot.concatMap
    (fun t ->
       match term_to_subject t with
       | None -> []
       | Some cs ->
         let cref = subject_to_shape_ref cs in
         (match find_objects g cs sh_select with
          | (T_Literal l) :: _ ->
            let cmsg = (match find_objects g cs sh_message with (T_Literal ml) :: _ -> Some ml | _ -> None) in
            let hdr = prefix_header_for g cs in
            [CC_Sparql cref (hdr ^ l.lexical_form) cmsg]
          | _ -> []))
    (find_objects g s sh_sparql)

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
  // sh:qualifiedValueShape gates sh:qualifiedMinCount/qualifiedMaxCount/
  // qualifiedValueShapesDisjoint entirely: absent a resolvable
  // qualifiedValueShape, the other three MUST NOT be evaluated as a
  // bare cardinality check (core/node/qualified-001 — see the
  // CC_QualifiedMinCount/MaxCount doc comment above). Factored into
  // `build_qualified_constraints` (own top-level VC) — see its doc
  // comment for why.
  let qualified = build_qualified_constraints g s in
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
  let sparqls = build_sparql_constraints g s in
  mincount @ maxcount @ datatype @ nodekind @ cls @ in_ @ hasvalue @ pattern @ minlen @ maxlen @
  langin @ uniquelang @ mininc @ maxinc @ minexc @ maxexc @ nots @ ands @ ors @ xones @ nodes @
  qualified @ equals @ disjoint @ lessthan @ lessthaneq @ closed_ @ sparqls
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
     | (T_Literal l) :: _ -> Some l
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

// --- xsd:dateTime ordering (Phase 3 — core/node/minInclusive-002/003).
//
// Parses "YYYY-MM-DDTHH:MM:SS(.fraction)?(Z|+HH:MM|-HH:MM)?" into a
// millisecond position on the proleptic Gregorian timeline plus a
// has-timezone flag. Two dateTimes are comparable only when both have
// a timezone or neither does — XML Schema's partial order makes
// mixed tz/naive comparison indeterminate (within +/-14h), and the
// min/maxInclusive/Exclusive textual definitions turn "cannot be
// compared" into a violation, which is exactly what the two suite
// fixtures expect. `days_from_civil` is the standard civil-date
// day-count algorithm; every intermediate here is non-negative for
// 4-digit years (the only years XSD's lexical form admits without an
// expanded-year sign), so F*'s int division/modulus never see
// negative operands.

let days_from_civil (y m d : int) : int =
  let y' = if m <= 2 then y - 1 else y in
  let era = (if y' >= 0 then y' else y' - 399) / 400 in
  let yoe = y' - op_Multiply era 400 in
  let mp = (m + 9) % 12 in
  let doy = (op_Multiply 153 mp + 2) / 5 + d - 1 in
  let doe = op_Multiply yoe 365 + yoe / 4 - yoe / 100 + doy in
  op_Multiply era 146097 + doe - 719468

// Parse the fraction+timezone tail (everything after the seconds
// field): optional ".<digits>" then one of "", "Z", "+HH:MM",
// "-HH:MM". Returns (fraction_ms, tz_offset_seconds, has_tz).
let dt_parse_tail (tail : string) : option (int & int & bool) =
  let len = String.length tail in
  // Split off the fraction, if any.
  let (frac_ms, tz_start) =
    if len >= 2 && String.sub tail 0 1 = "." then
      // take up to 3 fraction digits for millisecond precision
      let rec frac_end (pos : nat{pos <= len}) : Tot (r:nat{pos <= r /\ r <= len}) (decreases (len - pos)) =
        if pos < len then
          (let c = FStar.Char.int_of_char (String.index tail pos) in
           if c >= 48 && c <= 57 then frac_end (pos + 1) else pos)
        else pos
      in
      let fe = frac_end 1 in
      if fe = 1 then (None, 0)  // "." with no digits: ill-formed
      else
        let dig_len : nat = if fe - 1 > 3 then 3 else fe - 1 in
        (match Alg.parse_int_string (String.sub tail 1 dig_len) with
         | Some f ->
           let ms = if dig_len = 1 then op_Multiply f 100
                    else if dig_len = 2 then op_Multiply f 10
                    else f in
           (Some ms, fe)
         | None -> (None, 0))
    else (Some 0, 0)
  in
  match frac_ms with
  | None -> None
  | Some fms ->
    let rest_len = len - tz_start in
    if rest_len = 0 then Some (fms, 0, false)
    else if rest_len = 1 && String.sub tail tz_start 1 = "Z" then Some (fms, 0, true)
    else if rest_len = 6 then
      let sign_s = String.sub tail tz_start 1 in
      if sign_s = "+" || sign_s = "-" then
        (match Alg.parse_int_string (String.sub tail (tz_start + 1) 2),
               Alg.parse_int_string (String.sub tail (tz_start + 4) 2) with
         | Some th, Some tm ->
           let off = op_Multiply th 3600 + op_Multiply tm 60 in
           Some (fms, (if sign_s = "-" then 0 - off else off), true)
         | _, _ -> None)
      else None
    else None

let dt_parse_ms (s : string) : option (int & bool) =
  let len = String.length s in
  if len < 19 then None
  else
    match Alg.parse_int_string (String.sub s 0 4),
          Alg.parse_int_string (String.sub s 5 2),
          Alg.parse_int_string (String.sub s 8 2),
          Alg.parse_int_string (String.sub s 11 2),
          Alg.parse_int_string (String.sub s 14 2),
          Alg.parse_int_string (String.sub s 17 2) with
    | Some y, Some mo, Some d, Some h, Some mi, Some se ->
      (match dt_parse_tail (String.sub s 19 (len - 19)) with
       | Some (fms, tzoff, has_tz) ->
         let days = days_from_civil y mo d in
         let secs = op_Multiply days 86400 + op_Multiply h 3600 + op_Multiply mi 60 + se - tzoff in
         Some (op_Multiply secs 1000 + fms, has_tz)
       | None -> None)
    | _, _, _, _, _, _ -> None

let dt_cmp (a b : string) : option int =
  match dt_parse_ms a, dt_parse_ms b with
  | Some (ma, tza), Some (mb, tzb) ->
    if tza = tzb then Some (if ma < mb then -1 else if ma > mb then 1 else 0)
    else None
  | _, _ -> None

let both_datetimes (a b : literal) : bool =
  a.datatype = Alg.xsd_dateTime && b.datatype = Alg.xsd_dateTime

let numeric_cmp_le (a b : literal) : option bool =
  if both_datetimes a b
  then (match dt_cmp a.lexical_form b.lexical_form with Some c -> Some (c <= 0) | None -> None)
  else
    match literal_to_scaled a, literal_to_scaled b with
    | Some sa, Some sb -> Some (scaled_cmp sa sb <= 0)
    | _, _ -> None

let numeric_cmp_lt (a b : literal) : option bool =
  if both_datetimes a b
  then (match dt_cmp a.lexical_form b.lexical_form with Some c -> Some (c < 0) | None -> None)
  else
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

// --- XSD ill-formed literal detection (Phase 3) -----------------------
//
// SHACL sh:datatype: "A literal matches a datatype if the literal's
// datatype has the same IRI and, for the datatypes supported by
// SPARQL 1.1, is not an ill-typed literal." Exercised by
// core/node/datatype-001 ("aldi"^^xsd:integer),
// core/property/datatype-ill-formed ("300"^^xsd:byte, "c"^^xsd:byte)
// and core/property/or-datatypes-001 ("none"^^xsd:boolean).
// Conservative by construction: datatypes not listed are never
// flagged, so this can only ADD violations the spec requires, not
// invent ones it doesn't.

let is_ascii_digit (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in n >= 48 && n <= 57

let is_integer_lexical (lex : string) : bool =
  match String.list_of_string lex with
  | [] -> false
  | c :: rest ->
    let ci = FStar.Char.int_of_char c in
    let digits = if ci = 43 || ci = 45 then rest else c :: rest in
    Cons? digits && List.Tot.for_all is_ascii_digit digits

let is_decimal_lexical (lex : string) : bool =
  match String.list_of_string lex with
  | [] -> false
  | c :: rest ->
    let ci = FStar.Char.int_of_char c in
    let body = if ci = 43 || ci = 45 then rest else c :: rest in
    Cons? body &&
    List.Tot.for_all (fun ch -> is_ascii_digit ch || FStar.Char.int_of_char ch = 46) body &&
    List.Tot.length (List.Tot.filter (fun ch -> FStar.Char.int_of_char ch = 46) body) <= 1 &&
    List.Tot.existsb is_ascii_digit body

// Integer-family range check: well-formed integer lexical whose value
// sits inside [lo, hi] (None = unbounded on that side). parse_int_string
// accepts an optional leading '-' but not '+'; '+'-signed literals are
// flagged conservatively-well-formed by skipping the range check only
// when the parse fails on an is_integer_lexical-accepted string.
let int_lexical_in_range (lex : string) (lo hi : option int) : bool =
  is_integer_lexical lex &&
  (match Alg.parse_int_string lex with
   | Some n ->
     (match lo with Some l -> n >= l | None -> true) &&
     (match hi with Some h -> n <= h | None -> true)
   | None -> true)

let literal_ill_formed (dt : wf_iri) (lex : string) : bool =
  if dt = xsd_boolean then not (lex = "true" || lex = "false" || lex = "1" || lex = "0")
  else if dt = xsd_integer then not (is_integer_lexical lex)
  else if dt = xsd_decimal then not (is_decimal_lexical lex)
  else if dt = xsd_long then not (int_lexical_in_range lex (Some (0 - 9223372036854775808)) (Some 9223372036854775807))
  else if dt = xsd_int then not (int_lexical_in_range lex (Some (0 - 2147483648)) (Some 2147483647))
  else if dt = xsd_short then not (int_lexical_in_range lex (Some (0 - 32768)) (Some 32767))
  else if dt = xsd_byte then not (int_lexical_in_range lex (Some (0 - 128)) (Some 127))
  else if dt = xsd_unsignedLong then not (int_lexical_in_range lex (Some 0) (Some 18446744073709551615))
  else if dt = xsd_unsignedInt then not (int_lexical_in_range lex (Some 0) (Some 4294967295))
  else if dt = xsd_unsignedShort then not (int_lexical_in_range lex (Some 0) (Some 65535))
  else if dt = xsd_unsignedByte then not (int_lexical_in_range lex (Some 0) (Some 255))
  else if dt = xsd_nonNegativeInteger then not (int_lexical_in_range lex (Some 0) None)
  else if dt = xsd_positiveInteger then not (int_lexical_in_range lex (Some 1) None)
  else if dt = xsd_nonPositiveInteger then not (int_lexical_in_range lex None (Some 0))
  else if dt = xsd_negativeInteger then not (int_lexical_in_range lex None (Some (0 - 1)))
  else if dt = Alg.xsd_dateTime then None? (dt_parse_ms lex)
  else false

// --- 11h. Aggregate (per-focus-node) constraint helpers --------------
//
// Phase 3 note: sh:equals / sh:disjoint / sh:lessThan /
// sh:lessThanOrEquals / sh:uniqueLang / sh:closed used to be scored
// per FOCUS NODE (one violation each), which was enough for
// conforms-only comparison. The suite's report-isomorphism comparison
// exposes the real granularity from each component's TEXTUAL
// DEFINITION in the spec: one validation result per offending VALUE
// (equals both directions, disjoint, lessThan/lessThanOrEquals with
// the value node as sh:value), per non-unique LANGUAGE TAG
// (uniqueLang, no sh:value), and per offending TRIPLE (closed, with
// the triple's predicate as sh:resultPath and object as sh:value).
// The per-value emission now lives directly in
// `eval_aggregate_constraints` below.

let other_property_values (data : rdf_graph) (focus : rdf_term) (p : wf_iri) : list rdf_term =
  match term_to_subject focus with
  | Some s -> find_objects data s p
  | None -> []

// Extract the qualifiedValueShape shape_ref carried by a
// CC_QualifiedMinCount/CC_QualifiedMaxCount constraint, if `cc` is
// one of those two constructors.
let qualified_shape_ref_of (cc : constraint_component) : option shape_ref =
  match cc with
  | CC_QualifiedMinCount r _ _ -> Some r
  | CC_QualifiedMaxCount r _ _ -> Some r
  | _ -> None

// Sibling shapes of `self_id`, per SHACL section 4.5.1: any OTHER
// shape_ref that is a value of sh:property of the same parent shape(s)
// `self_id` is also a value of sh:property of. `sg` is the whole
// shapes graph (property_refs lists are populated at parse time), so
// this is a plain reverse lookup — no recursion, no fuel needed.
let sibling_shape_refs (sg : list shape) (self_id : shape_ref) : list shape_ref =
  List.Tot.concatMap
    (fun (parent : shape) ->
       if List.Tot.existsb (fun r -> r = self_id) parent.property_refs
       then List.Tot.filter (fun r -> not (r = self_id)) parent.property_refs
       else [])
    sg

let path_predicates_of_shape (sg : list shape) (s : shape) : list wf_iri =
  List.Tot.concatMap
    (fun r -> match lookup_shape r sg with
              | Some ps -> (match ps.shape_path with Some (P_Predicate p) -> [p] | _ -> [])
              | None -> [])
    s.property_refs

// All distinct language tags used by at least two of `values`
// (case-insensitive per lang_tag_eq; first-seen spelling kept). One
// sh:uniqueLang validation result is emitted per entry — SHACL's
// textual definition: "for each non-unique language tag that is used
// by at least two of the value nodes, there is a validation result"
// (core/property/uniqueLang-001.ttl expects TWO structurally identical
// results for a focus node with duplicated @en AND duplicated @de).
let duplicated_lang_tags (values : list rdf_term) : list string =
  let langs =
    List.Tot.concatMap (fun t -> match t with T_Literal l -> (match l.lang_tag with Some lt -> [lt] | None -> []) | _ -> []) values in
  let count (x : string) : nat = List.Tot.length (List.Tot.filter (lang_tag_eq x) langs) in
  let rec distinct_dups (seen : list string) (xs : list string) : Tot (list string) (decreases xs) =
    match xs with
    | [] -> []
    | x :: rest ->
      if List.Tot.existsb (lang_tag_eq x) seen then distinct_dups seen rest
      else if count x >= 2 then x :: distinct_dups (x :: seen) rest
      else distinct_dups (x :: seen) rest
  in
  distinct_dups [] langs

// sh:languageIn uses BASIC LANGUAGE RANGE matching (the spec's SPARQL
// definition is langMatches(lang(?value), ?lang) — RFC 4647 section
// 3.3.1): the range "en" matches "en" and "en-NZ" but not "enz".
// Case-insensitive, like all language-tag handling.
// core/property/languageIn-001.ttl: "Hill"@en-NZ conforms to
// sh:languageIn ("en" "mi").
let lang_matches_range (tag : string) (range : string) : bool =
  let t = String.lowercase tag in
  let r = String.lowercase range in
  let tl = String.length t in
  let rl = String.length r in
  t = r ||
  (tl > rl && String.sub t 0 rl = r && String.sub t rl 1 = "-")

let value_violation (focus : rdf_term) (path_opt : option path) (source : shape_ref)
                     (cc : constraint_component) (sev : severity) (msg : option wf_literal) (v : rdf_term)
  : violation =
  { v_focus_node = focus; v_path = path_opt; v_value = Some v;
    v_source_shape = source; v_constraint = cc; v_severity = sev; v_message = msg;
    v_source_constraint = None }

let focus_violation (focus : rdf_term) (path_opt : option path) (source : shape_ref)
                     (cc : constraint_component) (sev : severity) (msg : option wf_literal)
  : violation =
  { v_focus_node = focus; v_path = path_opt; v_value = None;
    v_source_shape = source; v_constraint = cc; v_severity = sev; v_message = msg;
    v_source_constraint = None }

// --- 11i. Per-value constraints + shape conformance (mutual) ---------
//
// `collect_shape_violations` / `eval_one_constraint` /
// `eval_aggregate_constraints` are mutually recursive: sh:not/sh:and/
// sh:or/sh:xone/sh:node need "does this value node conform to that
// (possibly nested) shape", which itself runs the same violation-
// collection judgment — and so does sh:qualifiedValueShape's "how many
// value nodes conform to the qualified shape" count
// (eval_aggregate_constraints, folded into this group precisely for
// that reason; it used to be a standalone non-recursive function
// before qualifiedValueShape support required it to call back into
// `collect_shape_violations`). There is no structural bound on shape
// nesting depth in an arbitrary shapes graph (and shapes could in
// principle reference each other in a cycle), so this is fuel-bounded
// like `shacl_class_closure` above — every mutual call site strictly
// decrements `fuel`, so F*'s termination checker sees one uniform
// decreasing measure. Running out of fuel conservatively returns "no
// violations found" (never fabricates a violation), which is
// sound-by-omission in the same spirit as Tableau's "return None when
// unsure".

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
    let agg = eval_aggregate_constraints data sg closed_cls node path_opt s.shape_id s.shape_sev s.message values s fuel' in
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
                        (path_opt : option path) (source : shape_ref) (sev : severity) (msg : option wf_literal)
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
       (match v with
        | T_Literal l ->
          if l.datatype = dt && not (literal_ill_formed dt l.lexical_form) then [] else viol ()
        | _ -> viol ())
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
           | Some lt -> if List.Tot.existsb (lang_matches_range lt) langs then [] else viol ()
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
     | CC_QualifiedMinCount _ _ _ -> []  // aggregate
     | CC_QualifiedMaxCount _ _ _ -> []  // aggregate
     | CC_Sparql _ _ _ -> [])    // per-focus-node, not per-value — real dispatch is section 13's sparql_violations_for_shape, run as a separate pass over `validate`'s root_shapes (never inside this per-value/per-constraint judgment)

// `eval_aggregate_constraints` — folded into this `and` group (see the
// section comment above) because CC_QualifiedMinCount/MaxCount need to
// re-run `collect_shape_violations` per candidate value node, once
// against the qualifiedValueShape itself and once per sibling shape's
// qualifiedValueShape (for the qualifiedValueShapesDisjoint exclusion
// set — SHACL section 4.5.1/4.5.2). `qualifying_count` is a plain
// (non-recursive) local closure over this call's `data`/`sg`/
// `closed_cls`/`fuel'`/`values`/`source`; the two calls it makes into
// `collect_shape_violations` at `fuel'` are what require this function
// to live in the mutual group, exactly like the nested `List.Tot.concatMap`
// closures in `collect_shape_violations` itself call `eval_one_constraint`
// at `fuel'`.
and eval_aggregate_constraints (data : rdf_graph) (sg : list shape) (closed_cls : rdf_graph)
                                (focus : rdf_term) (path_opt : option path)
                                (source : shape_ref) (sev : severity) (msg : option wf_literal)
                                (values : list rdf_term) (s : shape) (fuel : nat)
  : Tot (list violation) (decreases fuel)
  =
  match fuel with
  | 0 -> []
  | _ ->
    let fuel' = fuel - 1 in
    // Count of `values` that conform to `qref`'s shape and — when
    // `qdisjoint` — do NOT also conform to any sibling shape's
    // qualifiedValueShape (siblings = other sh:property values of the
    // same parent shape(s) that `source` is itself a sh:property value
    // of; see `sibling_shape_refs`).
    let qualifying_count (qref : shape_ref) (qdisjoint : bool) : nat =
      match lookup_shape qref sg with
      | None -> 0
      | Some qs ->
        let sibling_refs = sibling_shape_refs sg source in
        let sibling_qrefs =
          List.Tot.concatMap
            (fun r ->
               match lookup_shape r sg with
               | Some sib ->
                 List.Tot.concatMap
                   (fun cc2 -> match qualified_shape_ref_of cc2 with Some sr -> [sr] | None -> [])
                   sib.constraints
               | None -> [])
            sibling_refs
        in
        let conforms_q (v : rdf_term) : bool =
          Nil? (collect_shape_violations data sg closed_cls v qs fuel') in
        let excluded (v : rdf_term) : bool =
          qdisjoint &&
          List.Tot.existsb
            (fun sr ->
               match lookup_shape sr sg with
               | Some sqs -> Nil? (collect_shape_violations data sg closed_cls v sqs fuel')
               | None -> false)
            sibling_qrefs
        in
        List.Tot.length (List.Tot.filter (fun v -> conforms_q v && not (excluded v)) values)
    in
    List.Tot.concatMap
      (fun cc ->
         match cc with
         | CC_MinCount n -> if List.Tot.length values < n then [focus_violation focus path_opt source cc sev msg] else []
         | CC_MaxCount n -> if List.Tot.length values > n then [focus_violation focus path_opt source cc sev msg] else []
         | CC_HasValue t -> if List.Tot.existsb (rdf_term_eq t) values then [] else [focus_violation focus path_opt source cc sev msg]
         // One result per non-unique language tag (spec textual
         // definition; see duplicated_lang_tags' doc comment).
         | CC_UniqueLang b ->
           if b then List.Tot.map (fun _lt -> focus_violation focus path_opt source cc sev msg) (duplicated_lang_tags values)
           else []
         // One result per offending triple, with the triple's
         // predicate as sh:resultPath and object as sh:value (spec:
         // "The validation result MUST have the predicate of the
         // triple as its sh:resultPath, and the object of the triple
         // as its sh:value") — core/node/closed-001/002 and
         // core/complex/personexample assert exactly this shape.
         | CC_Closed ign ->
           (match term_to_subject focus with
            | None -> []
            | Some subj ->
              let allowed = path_predicates_of_shape sg s @ ign in
              List.Tot.concatMap
                (fun (t : triple) ->
                   if subject_eq t.s subj && not (List.Tot.existsb (fun p -> p = t.p) allowed)
                   then [{ v_focus_node = focus; v_path = Some (P_Predicate t.p); v_value = Some t.o;
                           v_source_shape = source; v_constraint = cc; v_severity = sev; v_message = msg;
                           v_source_constraint = None }]
                   else [])
                data)
         // Both directions, one result per mismatched value (spec:
         // "for each value node that does not exist as a value of
         // $equals ... and for each value of $equals ... that is not
         // one of the value nodes").
         | CC_Equals p ->
           let others = other_property_values data focus p in
           List.Tot.concatMap
             (fun v -> if List.Tot.existsb (rdf_term_eq v) others then [] else [value_violation focus path_opt source cc sev msg v])
             values
           @ List.Tot.concatMap
               (fun o -> if List.Tot.existsb (rdf_term_eq o) values then [] else [value_violation focus path_opt source cc sev msg o])
               others
         // One result per shared value.
         | CC_Disjoint p ->
           let others = other_property_values data focus p in
           List.Tot.concatMap
             (fun v -> if List.Tot.existsb (rdf_term_eq v) others then [value_violation focus path_opt source cc sev msg v] else [])
             values
         // One result per failing (or incomparable) PAIR, the value
         // node as sh:value — spec: "for each PAIR of value nodes and
         // the values of the property $lessThan ... where the first
         // value is not less than the second". lessThan-002 expects
         // FOUR structurally identical-but-for-multiplicity results
         // for 2 values x 2 incomparable others, so the per-pair
         // multiplicity is observable and must be preserved.
         | CC_LessThan p ->
           let others = other_property_values data focus p in
           List.Tot.concatMap
             (fun v -> List.Tot.concatMap (fun w -> if term_lt v w then [] else [value_violation focus path_opt source cc sev msg v]) others)
             values
         | CC_LessThanOrEq p ->
           let others = other_property_values data focus p in
           List.Tot.concatMap
             (fun v -> List.Tot.concatMap (fun w -> if term_le v w then [] else [value_violation focus path_opt source cc sev msg v]) others)
             values
         | CC_QualifiedMinCount qref qmin qdisjoint ->
           if qualifying_count qref qdisjoint >= qmin then [] else [focus_violation focus path_opt source cc sev msg]
         | CC_QualifiedMaxCount qref qmax qdisjoint ->
           if qualifying_count qref qdisjoint <= qmax then [] else [focus_violation focus path_opt source cc sev msg]
         | _ -> [])
      s.constraints

// --- 11k. sh:sparql dispatch (Phase 3, issue #181 follow-up) ---------
//
// Section 12 (below) originally reserved `eval_sparql_target_select`
// as an `assume val` ML host call-out, on the assumption that running
// an arbitrary SPARQL SELECT query needed an escape from this module's
// Tot obligations. That assumption no longer holds: both
// `SPARQL11.Parser.parse_sparql` and `SPARQL11.Algebra.eval_select_query`
// are plain Tot functions (string -> parse_result query, and query ->
// rdf_graph -> rdf_dataset -> solution_sequence respectively — no
// ambient state, no I/O). So the whole sh:sparql dispatch below is
// real, total F* — no ML, no assume val, no glue patch. (Section 12's
// `eval_sparql_target_select` stays only for the unrelated SPARQL-
// *target* form `sh:target [ sh:select ... ]` / T_Sparql, which this
// slice still does not implement; see its own doc comment.)
//
// $this is pre-bound via `SPARQL11.Algebra.query_with_prebound_values`
// (a join against the parsed query's WHERE-clause solutions — the
// same mechanism `eval_select_query` already uses for a literal
// trailing VALUES clause), never by serializing the focus node into
// SPARQL surface syntax and re-parsing it.
//
// $PATH is the one spec-sanctioned TEXTUAL substitution (SHACL spec,
// SPARQL-based Constraints section: "the only legal use of the
// variable PATH ... is in the predicate position of a triple
// pattern") — `substitute_path` replaces the literal substring
// "$PATH" with the property shape's own path rendered as SPARQL 1.1
// property-path syntax (`path_to_sparql_expr` above). Node shapes
// have no path (`s.shape_path = None`); a query that uses $PATH
// without a path present is left unsubstituted (an honest, likely
// syntactically-inert token, never a fabricated path).
//
// ?value/?path/?message column defaults follow the vendored suite's
// own fixtures (core/sparql/node/sparql-003.ttl has no ?value column
// and expects sh:value = $this; property/sparql-001.ttl has no ?path
// column and expects sh:resultPath = the property shape's own path):
//   - ?value absent  -> sh:value defaults to the focus node ($this).
//   - ?path  absent  -> sh:resultPath defaults to the shape's own path
//                       (property shapes only; None for node shapes).
//   - ?message absent -> falls back to the sh:sparql constraint node's
//                       own sh:message, then the owning shape's
//                       sh:message, then no message.
//
// NOT wired (both honest FAILs against the suite, never a silent
// wrong PASS — see `pre-binding/shapesGraph-001.ttl`,
// `component/*.ttl`):
//   - $shapesGraph / $currentShape pre-binding (needs a GRAPH-clause-
//     visible copy of the shapes graph threaded into `ds`).
//   - sh:sparql on a shape reached via sh:property (nested shapes) —
//     only ROOT shapes (shapes with their own sh:target*) are
//     dispatched; a nested property shape's sh:sparql constraint is
//     silently skipped (its `values` never get walked for CC_Sparql,
//     though its OTHER constraints still evaluate normally via
//     `collect_shape_violations`'s existing nested_props walk).
//   - sh:validator / sh:nodeValidator / sh:propertyValidator / custom
//     sh:ConstraintComponent (SHACL-SPARQL extensibility, the
//     `component/` test folder) — a distinct, larger mechanism from
//     plain sh:sparql; not attempted this slice.
//
// A SELECT query that fails to parse (SERVICE, MINUS, VALUES-block,
// and other constructs some `unsupported-sparql-*.ttl` fixtures use
// deliberately) surfaces as `report_failure`, not an exception —
// keeping `validate` a total function. `shacl_runner` maps
// `mf:result sht:Failure` test cases onto `Some? report.report_failure`.

let sparql_constraints_of (s : shape) : list (shape_ref & string & option wf_literal) =
  List.Tot.concatMap
    (fun cc -> match cc with CC_Sparql cref q m -> [(cref, q, m)] | _ -> [])
    s.constraints

let substitute_path (q : string) (path_opt : option path) : string =
  match path_opt with
  | Some p -> Alg.string_replace_literal q "$PATH" (path_to_sparql_expr p) None
  | None -> q

// --- $this pre-binding by AST substitution ---------------------------
//
// SHACL section 5.3 pre-binds $this before the query runs, which means
// it must be visible INSIDE the WHERE clause (FILTER/BIND/BGP alike) —
// a post-hoc VALUES join is not enough for FILTER-only queries like
// pre-binding-001's `WHERE { FILTER ($this = ex:InvalidResource) }`.
// We substitute the focus node for the variable `this` throughout the
// parsed AST (`bound($this)` becomes `true`), then ALSO join a
// {this -> focus} row via q_values so a `SELECT $this` projection
// still carries the binding in the result rows. A blank-node focus
// has no expression form; its E_Var occurrences stay unsubstituted
// (the BGP/pattern positions still substitute via PT_BNode/PS_BNode),
// so a FILTER-only query over a bnode focus finds no rows — sound by
// omission.

let subst_this_ps (t : rdf_term) (ps : Alg.pattern_subject) : Alg.pattern_subject =
  match ps with
  | Alg.PS_Var v ->
    if v = "this" then
      (match t with
       | T_IRI i -> Alg.PS_IRI i
       | T_BNode b -> Alg.PS_BNode b
       | T_Literal _ -> ps)   // literal subjects are inexpressible; leave the var
    else ps
  | _ -> ps

let subst_this_pt (t : rdf_term) (pt : Alg.pattern_term) : Alg.pattern_term =
  match pt with
  | Alg.PT_Var v ->
    if v = "this" then
      (match t with
       | T_IRI i -> Alg.PT_IRI i
       | T_BNode b -> Alg.PT_BNode b
       | T_Literal l -> Alg.PT_Literal l)
    else pt
  | _ -> pt

let subst_this_tp (t : rdf_term) (tp : Alg.triple_pattern) : Alg.triple_pattern =
  Alg.Mktriple_pattern
    (subst_this_ps t (Alg.Mktriple_pattern?.tp_s tp))
    (subst_this_pt t (Alg.Mktriple_pattern?.tp_p tp))
    (subst_this_pt t (Alg.Mktriple_pattern?.tp_o tp))

let term_to_expr_opt (t : rdf_term) : option Alg.expr =
  match t with
  | T_IRI i -> Some (Alg.E_IRI i)
  | T_Literal l -> Some (Alg.E_Literal l)
  | T_BNode _ -> None

// Structural walk over the expression/pattern AST. Constructors with
// no expression or pattern children fall through the final wildcard
// unchanged. Mutually recursive with the pattern walk because of
// EXISTS / NOT EXISTS and subqueries; all recursive calls are on
// strict subterms, so no fuel is needed.
let rec subst_this_expr (t : rdf_term) (e : Alg.expr) : Tot Alg.expr (decreases e) =
  match e with
  | Alg.E_Var v -> if v = "this" then (match term_to_expr_opt t with Some e' -> e' | None -> e) else e
  | Alg.E_Bound v -> if v = "this" then Alg.E_BoolLit true else e
  | Alg.E_Arith op a b -> Alg.E_Arith op (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_UnaryMinus a -> Alg.E_UnaryMinus (subst_this_expr t a)
  | Alg.E_UnaryPlus a -> Alg.E_UnaryPlus (subst_this_expr t a)
  | Alg.E_Compare op a b -> Alg.E_Compare op (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_And a b -> Alg.E_And (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_Or a b -> Alg.E_Or (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_Not a -> Alg.E_Not (subst_this_expr t a)
  | Alg.E_IsIRI a -> Alg.E_IsIRI (subst_this_expr t a)
  | Alg.E_IsBlank a -> Alg.E_IsBlank (subst_this_expr t a)
  | Alg.E_IsLiteral a -> Alg.E_IsLiteral (subst_this_expr t a)
  | Alg.E_IsNumeric a -> Alg.E_IsNumeric (subst_this_expr t a)
  | Alg.E_Str a -> Alg.E_Str (subst_this_expr t a)
  | Alg.E_Lang a -> Alg.E_Lang (subst_this_expr t a)
  | Alg.E_Datatype a -> Alg.E_Datatype (subst_this_expr t a)
  | Alg.E_IRI_fn a -> Alg.E_IRI_fn (subst_this_expr t a)
  | Alg.E_StrDt a b -> Alg.E_StrDt (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_StrLang a b -> Alg.E_StrLang (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_If a b c -> Alg.E_If (subst_this_expr t a) (subst_this_expr t b) (subst_this_expr t c)
  | Alg.E_Coalesce es -> Alg.E_Coalesce (subst_this_exprs t es)
  | Alg.E_In a es -> Alg.E_In (subst_this_expr t a) (subst_this_exprs t es)
  | Alg.E_NotIn a es -> Alg.E_NotIn (subst_this_expr t a) (subst_this_exprs t es)
  | Alg.E_StrLen a -> Alg.E_StrLen (subst_this_expr t a)
  | Alg.E_Substr a b c ->
    Alg.E_Substr (subst_this_expr t a) (subst_this_expr t b)
      (match c with Some x -> Some (subst_this_expr t x) | None -> None)
  | Alg.E_UCase a -> Alg.E_UCase (subst_this_expr t a)
  | Alg.E_LCase a -> Alg.E_LCase (subst_this_expr t a)
  | Alg.E_StrStarts a b -> Alg.E_StrStarts (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_StrEnds a b -> Alg.E_StrEnds (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_Contains a b -> Alg.E_Contains (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_StrBefore a b -> Alg.E_StrBefore (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_StrAfter a b -> Alg.E_StrAfter (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_Concat es -> Alg.E_Concat (subst_this_exprs t es)
  | Alg.E_EncodeForUri a -> Alg.E_EncodeForUri (subst_this_expr t a)
  | Alg.E_Replace a b c fl ->
    Alg.E_Replace (subst_this_expr t a) (subst_this_expr t b) (subst_this_expr t c)
      (match fl with Some x -> Some (subst_this_expr t x) | None -> None)
  | Alg.E_Regex a b fl ->
    Alg.E_Regex (subst_this_expr t a) (subst_this_expr t b)
      (match fl with Some x -> Some (subst_this_expr t x) | None -> None)
  | Alg.E_Abs a -> Alg.E_Abs (subst_this_expr t a)
  | Alg.E_Round a -> Alg.E_Round (subst_this_expr t a)
  | Alg.E_Ceil a -> Alg.E_Ceil (subst_this_expr t a)
  | Alg.E_Floor a -> Alg.E_Floor (subst_this_expr t a)
  | Alg.E_SameTerm a b -> Alg.E_SameTerm (subst_this_expr t a) (subst_this_expr t b)
  | Alg.E_Exists p -> Alg.E_Exists (subst_this_gp t p)
  | Alg.E_NotExists p -> Alg.E_NotExists (subst_this_gp t p)
  | Alg.E_FunctionCall f es -> Alg.E_FunctionCall f (subst_this_exprs t es)
  | _ -> e

and subst_this_exprs (t : rdf_term) (es : list Alg.expr) : Tot (list Alg.expr) (decreases es) =
  match es with
  | [] -> []
  | e :: rest -> subst_this_expr t e :: subst_this_exprs t rest

and subst_this_bgp (t : rdf_term) (bgp : list Alg.triple_pattern) : Tot (list Alg.triple_pattern) (decreases bgp) =
  match bgp with
  | [] -> []
  | tp :: rest -> subst_this_tp t tp :: subst_this_bgp t rest

and subst_this_gp (t : rdf_term) (p : Alg.group_graph_pattern) : Tot Alg.group_graph_pattern (decreases p) =
  match p with
  | Alg.GP_BGP bgp -> Alg.GP_BGP (subst_this_bgp t bgp)
  | Alg.GP_Join a b -> Alg.GP_Join (subst_this_gp t a) (subst_this_gp t b)
  | Alg.GP_LeftJoin a b e -> Alg.GP_LeftJoin (subst_this_gp t a) (subst_this_gp t b) (subst_this_expr t e)
  | Alg.GP_Filter e a -> Alg.GP_Filter (subst_this_expr t e) (subst_this_gp t a)
  | Alg.GP_Union a b -> Alg.GP_Union (subst_this_gp t a) (subst_this_gp t b)
  | Alg.GP_Graph pt a -> Alg.GP_Graph (subst_this_pt t pt) (subst_this_gp t a)
  | Alg.GP_Minus a b -> Alg.GP_Minus (subst_this_gp t a) (subst_this_gp t b)
  | Alg.GP_Bind e v a -> Alg.GP_Bind (subst_this_expr t e) v (subst_this_gp t a)
  // The Mkquery?.q_pattern projector (rather than the query_pattern_of
  // accessor) keeps the recursive argument a visible subterm of `q`
  // for the termination checker.
  | Alg.GP_SubSelect q -> Alg.GP_SubSelect (Alg.query_with_pattern q (subst_this_gp t (Alg.Mkquery?.q_pattern q)))
  | Alg.GP_PropertyPath ps pp pt -> Alg.GP_PropertyPath (subst_this_ps t ps) pp (subst_this_pt t pt)
  // VALUES / SERVICE are rejected by prebinding_unsupported before we
  // ever substitute; leave them untouched here.
  | _ -> p

// --- Pre-binding well-formedness (SHACL section 5.3.2) ---------------
//
// "The following features of SPARQL queries are not supported [with
// pre-bound variables] and must be rejected with a failure": MINUS,
// federated queries (SERVICE), VALUES, nested SELECT queries that do
// not project all potentially pre-bound variables, and assignment to
// a pre-bound variable ($this/$value/$path via BIND or SELECT ... AS).
// The sparql/pre-binding/unsupported-sparql-00N.ttl fixtures each
// exercise one of these with `mf:result sht:Failure`; SELECT * in a
// subquery counts as NOT projecting (pre-binding-006 vs -007).

let si_projects_this (si : Alg.select_item) : bool =
  match si with
  | Alg.SI_Var v -> v = "this"
  | _ -> false

let si_assigns_prebound (si : Alg.select_item) : bool =
  match si with
  | Alg.SI_Expr _ v -> v = "this" || v = "value" || v = "path"
  | _ -> false

let rec prebinding_unsupported (p : Alg.group_graph_pattern) : Tot (option string) (decreases p) =
  match p with
  | Alg.GP_Minus _ _ -> Some "MINUS is not supported with pre-bound variables"
  | Alg.GP_Service _ _ _ -> Some "SERVICE is not supported with pre-bound variables"
  | Alg.GP_ServiceVar _ _ _ -> Some "SERVICE is not supported with pre-bound variables"
  | Alg.GP_Values _ _ -> Some "VALUES is not supported with pre-bound variables"
  | Alg.GP_Bind _ v p' ->
    if v = "this" || v = "value" || v = "path"
    then Some "assignment to a pre-bound variable"
    else prebinding_unsupported p'
  | Alg.GP_SubSelect q ->
    (match Alg.Mkquery?.q_form q with
     | Alg.QF_Select (Alg.Select_Vars sis) ->
       if List.Tot.existsb si_assigns_prebound sis
       then Some "assignment to a pre-bound variable in a nested SELECT"
       else if List.Tot.existsb si_projects_this sis
       then prebinding_unsupported (Alg.Mkquery?.q_pattern q)
       else Some "nested SELECT does not project $this"
     | _ -> Some "nested SELECT does not project $this")
  | Alg.GP_Join a b ->
    (match prebinding_unsupported a with Some m -> Some m | None -> prebinding_unsupported b)
  | Alg.GP_LeftJoin a b _ ->
    (match prebinding_unsupported a with Some m -> Some m | None -> prebinding_unsupported b)
  | Alg.GP_Union a b ->
    (match prebinding_unsupported a with Some m -> Some m | None -> prebinding_unsupported b)
  | Alg.GP_Filter _ a -> prebinding_unsupported a
  | Alg.GP_Graph _ a -> prebinding_unsupported a
  | _ -> None

// Evaluate one sh:sparql constraint against one focus node. Returns
// the violations produced (one per non-conforming SELECT solution)
// plus an optional failure message (Some iff the query failed to
// parse — in which case the violation list is always []).
let sparql_violations_for_focus
  (data : rdf_graph) (focus : rdf_term) (s : shape)
  (cref : shape_ref) (query_text : string) (cmsg : option wf_literal)
  : Tot (list violation & option string)
  =
  let substituted = substitute_path query_text s.shape_path in
  match Parser11.parse_sparql substituted with
  | Parser11.ParseErr msg ->
    ([], Some (String.concat "" ["sh:sparql query parse error ("; cref; "): "; msg]))
  | Parser11.ParseOk q _ ->
    // Pre-binding well-formedness first (SHACL section 5.3.2): a
    // trailing VALUES clause (q_values) or an in-pattern unsupported
    // construct is a validation FAILURE, not a conforming run.
    (match (if Some? (Alg.query_values_of q)
            then Some "VALUES is not supported with pre-bound variables"
            else prebinding_unsupported (Alg.query_pattern_of q)) with
     | Some why ->
       ([], Some (String.concat "" ["sh:sparql unsupported query ("; cref; "): "; why]))
     | None ->
    let q_subst = Alg.query_with_pattern q (subst_this_gp focus (Alg.query_pattern_of q)) in
    let q' = Alg.query_with_prebound_values q_subst [[("this", focus)]] in
    let ds = { empty_dataset with ds_default = data } in
    let rows = Alg.eval_select_query q' data ds in
    let mk_violation (mu : solution_mapping) : violation =
      let value = (match Alg.sm_lookup "value" mu with Some v -> v | None -> focus) in
      let path_result =
        (match Alg.sm_lookup "path" mu with
         | Some (T_IRI p) -> Some (P_Predicate p)
         | _ -> s.shape_path) in
      let row_msg =
        (match Alg.sm_lookup "message" mu with
         | Some (T_Literal l) -> Some l
         | _ -> (match cmsg with Some _ -> cmsg | None -> s.message)) in
      { v_focus_node = focus; v_path = path_result; v_value = Some value;
        v_source_shape = s.shape_id; v_constraint = CC_Sparql cref query_text cmsg;
        v_severity = s.shape_sev; v_message = row_msg;
        v_source_constraint = Some (shape_ref_to_term cref) }
    in
    (List.Tot.map mk_violation rows, None))

let rec sparql_violations_for_focus_all
  (data : rdf_graph) (focus : rdf_term) (s : shape)
  (ccs : list (shape_ref & string & option wf_literal))
  : Tot (list violation & option string) (decreases ccs)
  =
  match ccs with
  | [] -> ([], None)
  | (cref, qt, m) :: rest ->
    let (vs1, f1) = sparql_violations_for_focus data focus s cref qt m in
    let (vs2, f2) = sparql_violations_for_focus_all data focus s rest in
    (vs1 @ vs2, (match f1 with Some _ -> f1 | None -> f2))

let rec sparql_violations_for_foci
  (data : rdf_graph) (foci : list rdf_term) (s : shape)
  (ccs : list (shape_ref & string & option wf_literal))
  : Tot (list violation & option string) (decreases foci)
  =
  match foci with
  | [] -> ([], None)
  | fn :: rest ->
    let (vs1, f1) = sparql_violations_for_focus_all data fn s ccs in
    let (vs2, f2) = sparql_violations_for_foci data rest s ccs in
    (vs1 @ vs2, (match f1 with Some _ -> f1 | None -> f2))

let sparql_violations_for_shape
  (data : rdf_graph) (closed_cls : rdf_graph) (all_subjects : list subject) (s : shape)
  : Tot (list violation & option string)
  =
  let ccs = sparql_constraints_of s in
  if Nil? ccs then ([], None)
  else
    let focus_nodes = dedup_terms (List.Tot.concatMap (fun tgt -> eval_target data closed_cls all_subjects tgt) s.targets) in
    sparql_violations_for_foci data focus_nodes s ccs

let rec sparql_violations_for_shapes
  (data : rdf_graph) (closed_cls : rdf_graph) (all_subjects : list subject) (ss : list shape)
  : Tot (list violation & option string) (decreases ss)
  =
  match ss with
  | [] -> ([], None)
  | s :: rest ->
    let (vs1, f1) = sparql_violations_for_shape data closed_cls all_subjects s in
    let (vs2, f2) = sparql_violations_for_shapes data closed_cls all_subjects rest in
    (vs1 @ vs2, (match f1 with Some _ -> f1 | None -> f2))

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
  let (sparql_violations, sparql_failure) =
    sparql_violations_for_shapes data closed_cls all_subjects root_shapes in
  let all_results = per_shape_violations @ sparql_violations in
  { conforms = Nil? all_results; results = all_results; report_failure = sparql_failure }

// ------------------------------------------------------------------
// 12. Remaining assume val (narrowed scope, Phase 3 update).
//
// `eval_sparql_target_select` was originally reserved for ALL SPARQL
// dispatch (both the sh:sparql CONSTRAINT form, CC_Sparql, and the
// sh:target SPARQL-SELECT-based TARGET form, T_Sparql). Section 11k
// above now implements CC_Sparql dispatch as real, total F* (both
// `SPARQL11.Parser.parse_sparql` and `SPARQL11.Algebra.eval_select_query`
// turned out to be plain Tot functions, not ML host call-outs — no
// escape from this module's Tot obligations was actually needed). This
// `assume val` now covers ONLY the separate, still-unimplemented
// SPARQL-SELECT TARGET form (`sh:target [ a sh:SPARQLTarget ; sh:select
// ... ]` / T_Sparql — a shape's *target* computed by a query, distinct
// from a *constraint* evaluated by one). T_Sparql still evaluates to
// "no focus nodes" in `eval_target` above, an honest FAIL against any
// vendored test that needs it, never a silent wrong PASS. Patch stub:
// minimal_regrettable_glue_code_each_with_an_open_issue/
// 181_shacl_validate_stub.sh (still valid — this remains the one
// acknowledged gap under CLAUDE.md rule #3).
// ------------------------------------------------------------------

assume val eval_sparql_target_select
  : data:rdf_graph
  -> query:string
  -> ML (list violation)

// ------------------------------------------------------------------
// 13. Validation report -> RDF serialization (Phase 3, issue #181
//     follow-up).
//
// Renders a `validation_report` as the triples the W3C SHACL test
// suite's "full compliance" comparison needs (data-shapes-test-suite/
// index.html, "Submitting Implementation Reports"): one
// ValidationReport blank node with sh:conforms, one ValidationResult
// blank node per `violation` wired via sh:result, using ONLY the
// predicates the suite's own isomorphism comparison keeps —
// rdf:type, sh:result, sh:conforms, sh:focusNode, sh:resultPath (+
// cloned path structure), sh:resultSeverity, sh:sourceConstraint,
// sh:sourceConstraintComponent, sh:sourceShape, sh:value,
// sh:resultMessage. (No sh:details — this validator never produces
// nested results, so there is nothing to strip.)
//
// Every blank node minted here (the report, each result, each
// resultPath structure) comes from a single counter threaded through
// `violations_to_triples`/`path_to_rdf` — never shared across two
// results — satisfying the suite's precondition that "blank node
// structures representing property paths ... must not be shared
// among multiple results". `shacl_runner` does the actual comparison
// (canonicalize both the expected and this `actual` graph via
// RDF.Canonical.canonicalize_to_nquads and compare the resulting
// strings) — this section only builds the `actual` graph.
// ------------------------------------------------------------------

let fresh_report_bnode (prefix : string) (ctr : nat) : (bnode_id & nat) =
  (String.concat "" [prefix; string_of_int ctr], ctr + 1)

// sh:sourceConstraintComponent value for each constraint kind (SHACL
// Core Appendix — one IRI per built-in component, plus
// sh:SPARQLConstraintComponent for CC_Sparql).
let constraint_component_iri (cc : constraint_component) : wf_iri =
  match cc with
  | CC_MinCount _ -> sh_MinCountConstraintComponent
  | CC_MaxCount _ -> sh_MaxCountConstraintComponent
  | CC_Datatype _ -> sh_DatatypeConstraintComponent
  | CC_NodeKind _ -> sh_NodeKindConstraintComponent
  | CC_Class _ -> sh_ClassConstraintComponent
  | CC_In _ -> sh_InConstraintComponent
  | CC_HasValue _ -> sh_HasValueConstraintComponent
  | CC_Pattern _ _ -> sh_PatternConstraintComponent
  | CC_MinLength _ -> sh_MinLengthConstraintComponent
  | CC_MaxLength _ -> sh_MaxLengthConstraintComponent
  | CC_LanguageIn _ -> sh_LanguageInConstraintComponent
  | CC_UniqueLang _ -> sh_UniqueLangConstraintComponent
  | CC_MinInclusive _ -> sh_MinInclusiveConstraintComponent
  | CC_MaxInclusive _ -> sh_MaxInclusiveConstraintComponent
  | CC_MinExclusive _ -> sh_MinExclusiveConstraintComponent
  | CC_MaxExclusive _ -> sh_MaxExclusiveConstraintComponent
  | CC_Not _ -> sh_NotConstraintComponent
  | CC_And _ -> sh_AndConstraintComponent
  | CC_Or _ -> sh_OrConstraintComponent
  | CC_Xone _ -> sh_XoneConstraintComponent
  | CC_Node _ -> sh_NodeConstraintComponent
  | CC_QualifiedMinCount _ _ _ -> sh_QualifiedMinCountConstraintComponent
  | CC_QualifiedMaxCount _ _ _ -> sh_QualifiedMaxCountConstraintComponent
  | CC_Equals _ -> sh_EqualsConstraintComponent
  | CC_Disjoint _ -> sh_DisjointConstraintComponent
  | CC_LessThan _ -> sh_LessThanConstraintComponent
  | CC_LessThanOrEq _ -> sh_LessThanOrEqualsConstraintComponent
  | CC_Closed _ -> sh_ClosedConstraintComponent
  | CC_Sparql _ _ _ -> sh_SPARQLConstraintComponent

let severity_to_iri (s : severity) : wf_iri =
  match s with
  | Sev_Info -> sh_Info
  | Sev_Warning -> sh_Warning
  | Sev_Violation -> sh_Violation
  | Sev_Custom i -> i

// Render a SHACL path as the RDF term used for sh:resultPath, plus the
// (freshly-blank-noded) triples describing it — the mirror image of
// `parse_path` above. Same mutual-recursion shape as `path_invert`/
// `path_invert_list`, threading a fresh-bnode counter throughout.
let rec path_list_to_rdf (ps : list path) (ctr : nat)
  : Tot (rdf_term & list triple & nat) (decreases ps)
  =
  match ps with
  | [] -> (T_IRI rdf_nil_iri, [], ctr)
  | p :: rest ->
    let (p_term, p_ts, ctr1) = path_to_rdf p ctr in
    let (rest_term, rest_ts, ctr2) = path_list_to_rdf rest ctr1 in
    let (bid, ctr3) = fresh_report_bnode "_shacl_rpl" ctr2 in
    let subj = S_BNode bid in
    (T_BNode bid,
     { s = subj; p = rdf_first; o = p_term } :: { s = subj; p = rdf_rest; o = rest_term } :: (p_ts @ rest_ts),
     ctr3)

and path_to_rdf (p : path) (ctr : nat)
  : Tot (rdf_term & list triple & nat) (decreases p)
  =
  match p with
  | P_Predicate i -> (T_IRI i, [], ctr)
  | P_Inverse p' ->
    let (inner, its, ctr1) = path_to_rdf p' ctr in
    let (bid, ctr2) = fresh_report_bnode "_shacl_rpi" ctr1 in
    (T_BNode bid, { s = S_BNode bid; p = sh_inversePath; o = inner } :: its, ctr2)
  | P_Sequence ps -> path_list_to_rdf ps ctr
  | P_Alternative ps ->
    let (list_term, list_ts, ctr1) = path_list_to_rdf ps ctr in
    let (bid, ctr2) = fresh_report_bnode "_shacl_rpa" ctr1 in
    (T_BNode bid, { s = S_BNode bid; p = sh_alternativePath; o = list_term } :: list_ts, ctr2)
  | P_ZeroOrMore p' ->
    let (inner, its, ctr1) = path_to_rdf p' ctr in
    let (bid, ctr2) = fresh_report_bnode "_shacl_rpzm" ctr1 in
    (T_BNode bid, { s = S_BNode bid; p = sh_zeroOrMorePath; o = inner } :: its, ctr2)
  | P_OneOrMore p' ->
    let (inner, its, ctr1) = path_to_rdf p' ctr in
    let (bid, ctr2) = fresh_report_bnode "_shacl_rpom" ctr1 in
    (T_BNode bid, { s = S_BNode bid; p = sh_oneOrMorePath; o = inner } :: its, ctr2)
  | P_ZeroOrOne p' ->
    let (inner, its, ctr1) = path_to_rdf p' ctr in
    let (bid, ctr2) = fresh_report_bnode "_shacl_rpzo" ctr1 in
    (T_BNode bid, { s = S_BNode bid; p = sh_zeroOrOnePath; o = inner } :: its, ctr2)

// One ValidationResult's triples (see the section comment for exactly
// which predicates). `ctr` in, updated `ctr` out (threaded across the
// whole report by `violations_to_triples` below).
let violation_to_triples (report_subj : subject) (v : violation) (ctr : nat)
  : Tot (list triple & nat)
  =
  let (bid, ctr1) = fresh_report_bnode "_shacl_result" ctr in
  let rsubj = S_BNode bid in
  let base =
    [ { s = rsubj; p = rdf_type; o = T_IRI sh_ValidationResult };
      { s = report_subj; p = sh_result; o = T_BNode bid };
      { s = rsubj; p = sh_focusNode; o = v.v_focus_node };
      { s = rsubj; p = sh_resultSeverity; o = T_IRI (severity_to_iri v.v_severity) };
      { s = rsubj; p = sh_sourceConstraintComponent; o = T_IRI (constraint_component_iri v.v_constraint) };
      { s = rsubj; p = sh_sourceShape; o = shape_ref_to_term v.v_source_shape } ] in
  let (path_ts, ctr2) =
    (match v.v_path with
     | None -> ([], ctr1)
     | Some p ->
       let (pterm, pts, ctr2') = path_to_rdf p ctr1 in
       ({ s = rsubj; p = sh_resultPath; o = pterm } :: pts, ctr2')) in
  let value_ts = (match v.v_value with Some vv -> [{ s = rsubj; p = sh_value_pred; o = vv }] | None -> []) in
  let msg_ts =
    (match v.v_message with
     | Some m -> [{ s = rsubj; p = sh_resultMessage; o = T_Literal m }]
     | None -> []) in
  let sc_ts = (match v.v_source_constraint with Some sc -> [{ s = rsubj; p = sh_sourceConstraint; o = sc }] | None -> []) in
  (base @ path_ts @ value_ts @ msg_ts @ sc_ts, ctr2)

let rec violations_to_triples (report_subj : subject) (vs : list violation) (ctr : nat)
  : Tot (list triple) (decreases vs)
  =
  match vs with
  | [] -> []
  | v :: rest ->
    let (ts, ctr1) = violation_to_triples report_subj v ctr in
    ts @ violations_to_triples report_subj rest ctr1

// Top-level entry point: one ValidationReport blank node
// ("_shacl_report0" — stable/deterministic, harmless since
// canonicalization relabels every blank node anyway) plus its
// sh:conforms and one ValidationResult per violation.
let validation_report_to_graph (r : validation_report) : rdf_graph =
  let report_subj = S_BNode "_shacl_report0" in
  let header =
    [ { s = report_subj; p = rdf_type; o = T_IRI sh_ValidationReport };
      { s = report_subj; p = sh_conforms_pred;
        o = T_Literal ({ lexical_form = (if r.conforms then "true" else "false"); datatype = xsd_boolean; lang_tag = None }) } ] in
  header @ violations_to_triples report_subj r.results 0
