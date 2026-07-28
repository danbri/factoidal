module Tableau.CountingOracle

// Z33kr Phase 0 -- the VERIFIED F* pieces of a runtime counting-fragment
// oracle behind the OWL 2 DL consistency interface. Design:
//   docs/designissues/2026-07-14-z3-entailment-backend.md (Phase 0).
//
// This module is Phase-0 ONLY. It contains, all in total F*:
//   - z3_verdict           : the closed verdict sum (no z3 internals leak)
//   - a small counting AST  : cardinality bounds + differentFrom
//                             distinctness over a finite named domain
//   - extract_counting_fragment : rdf_graph -> counting_ast   (total)
//   - in_counting_fragment      : rdf_graph -> bool           (conservative)
//   - encode_counting_fragment  : counting_ast -> string      (SMT-LIB 2)
//   - z3_check_sat              : the SINGLE assume val (ASSUME-HOST)
//
// z3 is NOT consulted in Phase 0. The `z3_check_sat` realisation
// (minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh)
// returns Z3_Unknown unconditionally, so the extracted engine's
// behaviour is byte-for-byte unchanged -- nothing in the runner calls
// this module yet. Phase 1 wires the native z3 glue and validates that
// an emitted `Unsat` implies inconsistency under Direct Semantics
// against the build-breaking soundness gate BEFORE any test flips.
//
// The clash-detecting refutation tableau `Tableau.Refute.fst` remains
// the default and only VERIFIED consistency path; this oracle is
// additive, for the one fragment (finite-model cardinality counting)
// the tableau provably cannot decide (dl-909 / dl-910 / one=two:
// pigeonhole with cardinality multiplication). The axiom-reading
// conventions here mirror Tableau.fst / Tableau.Refute.fst: cardinality
// values via `cardinality_literal_to_nat` + `find_first_object`,
// differentFrom read straight off the closed graph.

open FStar.List.Tot
open FStar.Mul
open RDF.Graph.Executable
open Tableau

// ============================================================
// 1. z3 verdict -- a closed sum. No z3 internals leak into F*.
// ============================================================

type z3_verdict =
  | Z3_Sat
  | Z3_Unsat
  | Z3_Unknown
  | Z3_Timeout

// ============================================================
// 2. File-local IRI constants.
//
// Same "acknowledged duplication wart" pattern Tableau.fst /
// OWL.QueryRewrite.fst already use for their own extras: defining the
// spec IRIs locally sidesteps the open-ambiguity between OWL.Vocabulary
// and the OWL.Closure constants re-exported through RDF.Graph.Executable
// (owl_minQualifiedCardinality etc. live in BOTH). Every string points
// at the same OWL 2 / RDF / XSD spec IRI, kept in sync by construction.
// ============================================================

let ico_rdf_type : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let ico_owl_onProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onProperty");
  "http://www.w3.org/2002/07/owl#onProperty"

let ico_owl_onClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onClass");
  "http://www.w3.org/2002/07/owl#onClass"

let ico_owl_minCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minCardinality");
  "http://www.w3.org/2002/07/owl#minCardinality"

let ico_owl_maxCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxCardinality");
  "http://www.w3.org/2002/07/owl#maxCardinality"

let ico_owl_cardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#cardinality");
  "http://www.w3.org/2002/07/owl#cardinality"

let ico_owl_minQualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"

let ico_owl_maxQualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"

let ico_owl_qualifiedCardinality : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#qualifiedCardinality");
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"

let ico_owl_FunctionalProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#FunctionalProperty");
  "http://www.w3.org/2002/07/owl#FunctionalProperty"

let ico_owl_InverseFunctionalProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#InverseFunctionalProperty");
  "http://www.w3.org/2002/07/owl#InverseFunctionalProperty"

let ico_owl_differentFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#differentFrom");
  "http://www.w3.org/2002/07/owl#differentFrom"

// -- The REJECT vocabulary: constructs the counting encoder is NOT
//    faithful for. Their presence takes the closure out of fragment.

let ico_owl_complementOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#complementOf");
  "http://www.w3.org/2002/07/owl#complementOf"

let ico_owl_datatypeComplementOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#datatypeComplementOf");
  "http://www.w3.org/2002/07/owl#datatypeComplementOf"

let ico_owl_onDatatype : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onDatatype");
  "http://www.w3.org/2002/07/owl#onDatatype"

let ico_owl_withRestrictions : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#withRestrictions");
  "http://www.w3.org/2002/07/owl#withRestrictions"

let ico_owl_onDataRange : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onDataRange");
  "http://www.w3.org/2002/07/owl#onDataRange"

let ico_owl_DatatypeProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#DatatypeProperty");
  "http://www.w3.org/2002/07/owl#DatatypeProperty"

let ico_xsd_minInclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#minInclusive");
  "http://www.w3.org/2001/XMLSchema#minInclusive"

let ico_xsd_maxInclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#maxInclusive");
  "http://www.w3.org/2001/XMLSchema#maxInclusive"

let ico_xsd_minExclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#minExclusive");
  "http://www.w3.org/2001/XMLSchema#minExclusive"

let ico_xsd_maxExclusive : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#maxExclusive");
  "http://www.w3.org/2001/XMLSchema#maxExclusive"

let ico_xsd_pattern : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#pattern");
  "http://www.w3.org/2001/XMLSchema#pattern"

let ico_xsd_length : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#length");
  "http://www.w3.org/2001/XMLSchema#length"

let ico_xsd_minLength : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#minLength");
  "http://www.w3.org/2001/XMLSchema#minLength"

let ico_xsd_maxLength : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#maxLength");
  "http://www.w3.org/2001/XMLSchema#maxLength"

// ============================================================
// 3. The counting AST.
//
// A finite-model cardinality-counting problem over a finite named
// domain: object-property cardinality bounds (from min/max/exact
// (qualified) cardinality axioms) plus pairwise distinctness (from
// owl:differentFrom). No datatypes, no negation, no general boolean
// class structure -- the recogniser below guarantees inputs stay
// inside this shape.
// ============================================================

type card_bound =
  | CB_Min   : nat -> card_bound   // >= k
  | CB_Max   : nat -> card_bound   // <= k
  | CB_Exact : nat -> card_bound   // = k

// One cardinality bound sitting on `ca_subj` (a class-expression node
// or an individual), over object property `ca_role`, optionally
// qualified by filler class `ca_filler` (None = unqualified restriction).
noeq type count_axiom = {
  ca_subj   : rdf_term;
  ca_role   : wf_iri;
  ca_filler : option wf_iri;
  ca_bound  : card_bound;
}

noeq type counting_ast = {
  cx_individuals : list rdf_term;               // finite named domain
  cx_axioms      : list count_axiom;            // cardinality bounds
  cx_distinct    : list (rdf_term & rdf_term);  // differentFrom pairs
}

// ============================================================
// 4. Extraction : closure rdf_graph -> counting_ast (total).
// ============================================================

let ico_is_card_pred (p : wf_iri) : bool =
  p = ico_owl_minCardinality || p = ico_owl_maxCardinality
  || p = ico_owl_cardinality || p = ico_owl_minQualifiedCardinality
  || p = ico_owl_maxQualifiedCardinality || p = ico_owl_qualifiedCardinality

let ico_bound_of (p : wf_iri) (k : nat) : option card_bound =
  if p = ico_owl_minCardinality || p = ico_owl_minQualifiedCardinality
  then Some (CB_Min k)
  else if p = ico_owl_maxCardinality || p = ico_owl_maxQualifiedCardinality
  then Some (CB_Max k)
  else if p = ico_owl_cardinality || p = ico_owl_qualifiedCardinality
  then Some (CB_Exact k)
  else None

// Read ONE restriction triple (subj <cardPred> "k") into a count_axiom,
// pulling owl:onProperty (required) and owl:onClass (optional filler)
// off the same restriction subject. Mirrors Tableau.parse_class_expr's
// cardinality branch: cardinality_literal_to_nat rejects anything
// outside 0-9 (sound under open world -- an unreadable bound yields no
// axiom rather than a guessed one).
let ico_axiom_of (g : rdf_graph) (t : triple) : option count_axiom =
  if not (ico_is_card_pred t.p) then None
  else
    match t.o with
    | T_Literal l ->
      (match cardinality_literal_to_nat l.lexical_form with
       | None -> None
       | Some k ->
         (match ico_bound_of t.p k with
          | None -> None
          | Some b ->
            (match find_first_object g t.s ico_owl_onProperty with
             | Some (T_IRI role) ->
               let filler =
                 (match find_first_object g t.s ico_owl_onClass with
                  | Some (T_IRI c) -> Some c
                  | _ -> None) in
               Some ({ ca_subj = subject_to_term t.s;
                       ca_role = role;
                       ca_filler = filler;
                       ca_bound = b })
             | _ -> None)))
    | _ -> None

let rec ico_axioms (g : rdf_graph) (ts : list triple)
  : Tot (list count_axiom) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    (match ico_axiom_of g t with Some a -> [a] | None -> [])
    @ ico_axioms g tl

let rec ico_distinct_pairs (ts : list triple)
  : Tot (list (rdf_term & rdf_term)) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    (if t.p = ico_owl_differentFrom
     then [(subject_to_term t.s, t.o)] else [])
    @ ico_distinct_pairs tl

let rec ico_mem_term (t : rdf_term) (xs : list rdf_term)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | h :: tl -> rdf_term_eq h t || ico_mem_term t tl

// Order-preserving dedup, last-occurrence dropped (keeps first).
let rec ico_dedup (xs : list rdf_term)
  : Tot (list rdf_term) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl -> if ico_mem_term h tl then ico_dedup tl else h :: ico_dedup tl

let ico_axiom_subj (a : count_axiom) : rdf_term = a.ca_subj
let ico_fst (p : (rdf_term & rdf_term)) : rdf_term = fst p
let ico_snd (p : (rdf_term & rdf_term)) : rdf_term = snd p

let extract_counting_fragment (g : rdf_graph) : Tot counting_ast =
  let axs = ico_axioms g g in
  let dis = ico_distinct_pairs g in
  let inds =
    ico_dedup
      ((map ico_fst dis) @ (map ico_snd dis) @ (map ico_axiom_subj axs)) in
  { cx_individuals = inds; cx_axioms = axs; cx_distinct = dis }

// ============================================================
// 5. Conservative fragment recogniser.
//
// `in_counting_fragment g` returns true ONLY when the closure's
// inconsistency question falls entirely inside the fragment the
// encoder is faithful for. False means "never consult z3".
//
// ACCEPTED shape (finite-model cardinality counting over a finite
// named domain):
//   - object-property cardinality bounds: owl:minCardinality /
//     maxCardinality / cardinality and their qualified forms, on an
//     owl:onProperty object property, optionally qualified by an
//     owl:onClass named filler;
//   - role machinery that counting needs: owl:FunctionalProperty /
//     InverseFunctionalProperty declarations, inverseOf, someValuesFrom
//     with named fillers, and singleton / small owl:oneOf nominals used
//     to pin a finite domain;
//   - distinctness from owl:differentFrom (and owl:AllDifferent).
//
// REJECTED (=> return false, never consult z3), because the QF_LIA
// encoding is not faithful to them:
//   - DATATYPE FACETS / data-value reasoning: owl:onDatatype,
//     owl:withRestrictions, owl:datatypeComplementOf, owl:onDataRange,
//     the xsd:* facet predicates, or any owl:DatatypeProperty
//     declaration (the inconsistency then lives in a data range, not in
//     object-successor counting);
//   - GENERAL BOOLEAN CLASS STRUCTURE via negation: an AUTHORED
//     owl:complementOf (its subject is not an RL-canonical "__rl_"
//     complement bnode). Union / intersection of named classes and the
//     closure-derived disjointness-complement markers over a finite
//     domain stay linear and are NOT rejected -- they are part of the
//     counting fragment, e.g. one=two's disjoint-union bijection
//     argument (its complementOf triples are all closure-synthesised
//     from owl:disjointWith);
//   - and, structurally, a graph with NO counting construct at all is
//     not a counting problem, so a pure-nominal / boolean-SAT
//     enumeration (e.g. a large owl:oneOf exact-cover with neither a
//     cardinality restriction nor a functional property) is rejected:
//     it carries no cardinality bound and no functional role, so the
//     accept gate below is not met.
//
// The recogniser is a REJECT-scan plus a positive accept-gate. It is
// deliberately conservative: erring toward false is always sound (z3 is
// simply not consulted, and the verified tableau verdict stands).
// ============================================================

let ico_is_facet_pred (p : wf_iri) : bool =
  p = ico_xsd_minInclusive || p = ico_xsd_maxInclusive
  || p = ico_xsd_minExclusive || p = ico_xsd_maxExclusive
  || p = ico_xsd_pattern || p = ico_xsd_length
  || p = ico_xsd_minLength || p = ico_xsd_maxLength

// An AUTHORED owl:complementOf -- general boolean class structure. The
// OWL-RL closure MATERIALISES a canonical complement bnode per named
// class from every owl:disjointWith (OWL.Closure.canonical_complement_
// bnode, id prefix "__rl_"), so a naive `t.p = complementOf` reject
// would drop legitimate disjoint-union counting problems (one=two's
// disjoint b / c). Those closure-derived markers are LINEAR over a
// finite domain and stay in fragment; only complement whose subject is
// NOT an RL-canonical bnode (an authored / nested class expression, as
// in dl-026 / dl-027) is the general-boolean structure to reject.
// PE-negation scaffolding bnodes (Tableau.Refute negation_goals):
// "__factoidal_pe_..." complement bnodes only assert the negated-
// conclusion membership a PE refutation goal is built from. Like the
// RL-canonical complements they are engine-generated, never authored
// boolean class structure, and no row extractor below reads them —
// exempting them from the reject scan is scope-hygiene, not a
// soundness lever (section-8 banner: the Farkas validator + per-row
// entailment carry soundness regardless of gating).
let ico_pe_scaffold_prefix : string = "__factoidal_pe_"
let bnode_is_pe_scaffold (b : bnode_id) : bool =
  let plen = String.length ico_pe_scaffold_prefix in
  if String.length b < plen then false
  else String.sub b 0 plen = ico_pe_scaffold_prefix

let ico_authored_complement (t : triple) : bool =
  t.p = ico_owl_complementOf
  && (match t.s with
      | S_BNode b -> not (bnode_is_rl_canonical b || bnode_is_pe_scaffold b)
      | S_IRI _   -> true)

let ico_reject_triple (t : triple) : bool =
  t.p = ico_owl_onDatatype
  || t.p = ico_owl_withRestrictions
  || t.p = ico_owl_datatypeComplementOf
  || t.p = ico_owl_onDataRange
  || ico_authored_complement t
  || ico_is_facet_pred t.p
  || (t.p = ico_rdf_type
      && (match t.o with
          | T_IRI i -> i = ico_owl_DatatypeProperty
          | _ -> false))

let ico_has_reject (g : rdf_graph) : bool =
  existsb ico_reject_triple g

// A counting construct: at least one cardinality restriction, or one
// functional / inverse-functional property declaration. Its presence is
// what makes the inconsistency a COUNTING problem in the first place.
let ico_counting_triple (t : triple) : bool =
  ico_is_card_pred t.p
  || (t.p = ico_rdf_type
      && (match t.o with
          | T_IRI i ->
            i = ico_owl_FunctionalProperty
            || i = ico_owl_InverseFunctionalProperty
          | _ -> false))

let ico_has_counting (g : rdf_graph) : bool =
  existsb ico_counting_triple g

let in_counting_fragment (g : rdf_graph) : Tot bool =
  (not (ico_has_reject g)) && ico_has_counting g

// ============================================================
// 6. SMT-LIB 2 encoder (QF_LIA), total pure string building.
//
// For each cardinality axiom, an Int successor-count variable is
// declared, constrained >= 0, and bounded by >= / <= / = per the
// min / max / exact bound. Two axioms on the SAME (subject, role,
// filler) key share one count variable, so a min-k above a max-m over
// the same key is `(>= v k)` AND `(<= v m)` -- unsat exactly when
// k > m. Distinctness from owl:differentFrom is encoded by giving each
// named individual an Int identity and asserting distinct pairs
// unequal, the finite-named-domain distinctness the counting argument
// rests on.
//
// Symbol names are index-based (n_s<i>_r<j>_c<k>, id_<i>) computed off
// the AST's own deduped lists, so no IRI text is embedded and no
// SMT-LIB symbol escaping is needed. Unsat implies inconsistency under
// Direct Semantics for inputs `in_counting_fragment` accepts; this is
// the Phase-0 encoder skeleton, sharpened + measured against the
// soundness gate when the native oracle is wired in Phase 1.
// ============================================================

let rec ico_index_of (xs : list rdf_term) (t : rdf_term) (i : nat)
  : Tot nat (decreases xs) =
  match xs with
  | [] -> i   // sentinel: not found -> length of list
  | h :: tl -> if rdf_term_eq h t then i else ico_index_of tl t (i + 1)

let rec ico_iri_index (xs : list wf_iri) (x : wf_iri) (i : nat)
  : Tot nat (decreases xs) =
  match xs with
  | [] -> i
  | h :: tl -> if h = x then i else ico_iri_index tl x (i + 1)

let rec ico_mem_iri (x : wf_iri) (xs : list wf_iri)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | h :: tl -> h = x || ico_mem_iri x tl

let rec ico_dedup_iri (xs : list wf_iri)
  : Tot (list wf_iri) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl -> if ico_mem_iri h tl then ico_dedup_iri tl else h :: ico_dedup_iri tl

let ico_axiom_role (a : count_axiom) : wf_iri = a.ca_role

let rec ico_filler_iris (axs : list count_axiom)
  : Tot (list wf_iri) (decreases axs) =
  match axs with
  | [] -> []
  | a :: tl ->
    (match a.ca_filler with Some c -> [c] | None -> []) @ ico_filler_iris tl

// The count-variable name for an axiom, keyed on (subject, role,
// filler) indices so that co-keyed axioms share a variable.
let ico_var_name (inds : list rdf_term) (roles : list wf_iri)
                 (fillers : list wf_iri) (a : count_axiom) : string =
  "n_s" ^ string_of_int (ico_index_of inds a.ca_subj 0)
  ^ "_r" ^ string_of_int (ico_iri_index roles a.ca_role 0)
  ^ "_c"
  ^ (match a.ca_filler with
     | Some c -> string_of_int (ico_iri_index fillers c 0)
     | None   -> "u")

let ico_bound_assert (name : string) (b : card_bound) : string =
  match b with
  | CB_Min k   -> "(assert (>= " ^ name ^ " " ^ string_of_int k ^ "))\n"
  | CB_Max k   -> "(assert (<= " ^ name ^ " " ^ string_of_int k ^ "))\n"
  | CB_Exact k -> "(assert (= "  ^ name ^ " " ^ string_of_int k ^ "))\n"

let rec ico_str_mem (s : string) (xs : list string)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | h :: tl -> h = s || ico_str_mem s tl

let rec ico_str_dedup (xs : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl -> if ico_str_mem h tl then ico_str_dedup tl else h :: ico_str_dedup tl

// Declare each unique count variable once (>= 0), before any bound.
let rec ico_decls (names : list string)
  : Tot string (decreases names) =
  match names with
  | [] -> ""
  | h :: tl ->
    "(declare-const " ^ h ^ " Int)\n(assert (>= " ^ h ^ " 0))\n"
    ^ ico_decls tl

let rec ico_bound_asserts (inds : list rdf_term) (roles : list wf_iri)
                          (fillers : list wf_iri) (axs : list count_axiom)
  : Tot string (decreases axs) =
  match axs with
  | [] -> ""
  | a :: tl ->
    ico_bound_assert (ico_var_name inds roles fillers a) a.ca_bound
    ^ ico_bound_asserts inds roles fillers tl

let rec ico_id_decls (inds : list rdf_term) (i : nat)
  : Tot string (decreases inds) =
  match inds with
  | [] -> ""
  | _ :: tl ->
    "(declare-const id_" ^ string_of_int i ^ " Int)\n"
    ^ ico_id_decls tl (i + 1)

// A differentFrom pair -> an inequality on the two identity vars. A pair
// whose terms are not in the domain list (index = length) is skipped:
// no spurious constraint.
let rec ico_distinct_asserts (inds : list rdf_term)
                             (pairs : list (rdf_term & rdf_term))
  : Tot string (decreases pairs) =
  match pairs with
  | [] -> ""
  | (a, b) :: tl ->
    let ia = ico_index_of inds a 0 in
    let ib = ico_index_of inds b 0 in
    let n  = length inds in
    (if ia < n && ib < n && ia <> ib
     then "(assert (not (= id_" ^ string_of_int ia
          ^ " id_" ^ string_of_int ib ^ ")))\n"
     else "")
    ^ ico_distinct_asserts inds tl

let rec ico_var_names (inds : list rdf_term) (roles : list wf_iri)
                      (fillers : list wf_iri) (axs : list count_axiom)
  : Tot (list string) (decreases axs) =
  match axs with
  | [] -> []
  | a :: tl ->
    ico_var_name inds roles fillers a :: ico_var_names inds roles fillers tl

let encode_counting_fragment (ast : counting_ast) : Tot string =
  let inds    = ast.cx_individuals in
  let axs     = ast.cx_axioms in
  let roles   = ico_dedup_iri (map ico_axiom_role axs) in
  let fillers = ico_dedup_iri (ico_filler_iris axs) in
  let names   = ico_str_dedup (ico_var_names inds roles fillers axs) in
  "(set-logic QF_LIA)\n"
  ^ "; Z33kr counting-fragment encoding (Phase 0 skeleton)\n"
  ^ ico_id_decls inds 0
  ^ ico_distinct_asserts inds ast.cx_distinct
  ^ ico_decls names
  ^ ico_bound_asserts inds roles fillers axs
  ^ "(check-sat)\n"

// ============================================================
// 6b. Class-size SMT-LIB 2 encoder (QF_LIA) -- Phase 1.
//
// The Phase-0 encoder (encode_counting_fragment above) emits one Int
// successor-count per restriction bnode. That is faithful to a single
// min-above-max clash on one restriction subject, but the residual
// finite-model fails (dl-909 / dl-910 / one=two) are CLASS-SIZE
// multiplication arguments: the contradiction is a linear system over
// the CARDINALITIES of NAMED classes, related by three sound lemmas
// over the counting fragment `in_counting_fragment` accepts.
//
// For each named class C an Int variable |C| >= 0. The linear relations:
//
//   FIBER (functional p, dom D, inv ip, D subclassof (p some X),
//          X equiv (ip exactly k)):  |D| = k * |X|.
//     p total+functional makes p : D -> X a total function; each x in X
//     receives exactly k p-preimages (= its k ip-successors), and the
//     fibers partition D, so |D| = k * |X|. Sound under Direct Semantics.
//
//   BIJECTION (functional+inverse-functional p, inv ip,
//              D subclassof (p some Y), Y subclassof (ip some D)):
//              |D| = |Y|.  p is a total injection both ways -> a bijection.
//
//   DISJOINT UNION (Z equiv unionOf(m1,m2), m1 disjointWith m2):
//              |Z| = |m1| + |m2|.
//
//   ONEOF NONEMPTINESS (C equiv/def oneOf L, L non-empty):  |C| >= 1.
//     A sound lower bound; the finite named domain anchor.
//
// Unsat of the resulting QF_LIA system implies the closure is
// inconsistent under Direct Semantics for inputs `in_counting_fragment`
// accepts. Symbol names are index-based (c<i>, i = position in the
// deduped IRI list) so no SMT-LIB symbol escaping is needed and every
// referenced class is declared. All total pure string building.
// ============================================================

let ico_rdfs_subClassOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#subClassOf");
  "http://www.w3.org/2000/01/rdf-schema#subClassOf"

let ico_owl_equivalentClass : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#equivalentClass");
  "http://www.w3.org/2002/07/owl#equivalentClass"

let ico_owl_someValuesFrom : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#someValuesFrom");
  "http://www.w3.org/2002/07/owl#someValuesFrom"

let ico_owl_inverseOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#inverseOf");
  "http://www.w3.org/2002/07/owl#inverseOf"

let ico_owl_unionOf : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#unionOf");
  "http://www.w3.org/2002/07/owl#unionOf"

let ico_owl_oneOf2 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#oneOf");
  "http://www.w3.org/2002/07/owl#oneOf"

let ico_owl_disjointWith : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#disjointWith");
  "http://www.w3.org/2002/07/owl#disjointWith"

let ico_rdfs_domain : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#domain");
  "http://www.w3.org/2000/01/rdf-schema#domain"

let ico_rdfs_range : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#range");
  "http://www.w3.org/2000/01/rdf-schema#range"

let ico_owl_Thing2 : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Thing");
  "http://www.w3.org/2002/07/owl#Thing"

// A general multi-digit non-negative decimal parser (the Phase-0
// cardinality_literal_to_nat only covers 0-9; dl-910's bounds are
// 20 / 30 / 601). Total, decreasing on the character list.
let ico_digit (c : FStar.Char.char) : option nat =
  if c = '0' then Some 0 else if c = '1' then Some 1
  else if c = '2' then Some 2 else if c = '3' then Some 3
  else if c = '4' then Some 4 else if c = '5' then Some 5
  else if c = '6' then Some 6 else if c = '7' then Some 7
  else if c = '8' then Some 8 else if c = '9' then Some 9
  else None

let rec ico_digits (acc : nat) (cs : list FStar.Char.char)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> Some acc
  | c :: tl ->
    (match ico_digit c with
     | None -> None
     | Some d -> ico_digits (acc * 10 + d) tl)

let ico_parse_nat (s : string) : option nat =
  match FStar.String.list_of_string s with
  | [] -> None
  | cs -> ico_digits 0 cs

// All IRIs appearing as an S_IRI subject or a T_IRI object. Over-
// collecting is harmless (spare declared Int vars are unconstrained);
// it GUARANTEES every class an assertion references is declared.
let rec ico_all_iris (ts : list triple) : Tot (list wf_iri) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    (match t.s with S_IRI i -> [i] | _ -> [])
    @ (match t.o with T_IRI i -> [i] | _ -> [])
    @ ico_all_iris tl

let ico_cvar (classes : list wf_iri) (c : wf_iri) : string =
  "c" ^ string_of_int (ico_iri_index classes c 0)

// Subjects carrying `rdf:type <cls>` (used for FunctionalProperty /
// InverseFunctionalProperty property sets).
let rec ico_props_typed (ts : list triple) (cls : wf_iri)
  : Tot (list wf_iri) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    (if t.p = ico_rdf_type
        && (match t.o with T_IRI i -> i = cls | _ -> false)
     then (match t.s with S_IRI i -> [i] | _ -> [])
     else [])
    @ ico_props_typed tl cls

// First non-Thing rdfs:domain of property p (the closure also asserts
// `p rdfs:domain owl:Thing`, which must be skipped).
let rec ico_find_dom (ts : list triple) (p : wf_iri)
  : Tot (option wf_iri) (decreases ts) =
  match ts with
  | [] -> None
  | t :: tl ->
    if t.p = ico_rdfs_domain && (match t.s with S_IRI i -> i = p | _ -> false)
    then (match t.o with
          | T_IRI i -> if i = ico_owl_Thing2 then ico_find_dom tl p else Some i
          | _ -> ico_find_dom tl p)
    else ico_find_dom tl p

// Inverse of p, either direction of owl:inverseOf.
let rec ico_find_inv (ts : list triple) (p : wf_iri)
  : Tot (option wf_iri) (decreases ts) =
  match ts with
  | [] -> None
  | t :: tl ->
    if t.p = ico_owl_inverseOf
    then (match t.s, t.o with
          | S_IRI a, T_IRI b ->
            if a = p then Some b else if b = p then Some a else ico_find_inv tl p
          | _ -> ico_find_inv tl p)
    else ico_find_inv tl p

// disjointWith either direction.
let rec ico_disjoint (ts : list triple) (a : wf_iri) (b : wf_iri)
  : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: tl ->
    (t.p = ico_owl_disjointWith
     && (match t.s, t.o with
         | S_IRI x, T_IRI y -> (x = a && y = b) || (x = b && y = a)
         | _ -> false))
    || ico_disjoint tl a b

// Among restriction bnodes `bs`, the someValuesFrom target of the first
// one whose onProperty is p (the totality witness D subclassof p-some-X).
let rec ico_svf_via (g : rdf_graph) (bs : list rdf_term) (p : wf_iri)
  : Tot (option wf_iri) (decreases bs) =
  match bs with
  | [] -> None
  | b :: tl ->
    (match term_as_subject b with
     | Some s ->
       (match find_first_object g s ico_owl_onProperty with
        | Some (T_IRI pp) ->
          if pp = p
          then (match find_first_object g s ico_owl_someValuesFrom with
                | Some (T_IRI x) -> Some x
                | _ -> ico_svf_via g tl p)
          else ico_svf_via g tl p
        | _ -> ico_svf_via g tl p)
     | None -> ico_svf_via g tl p)

// Among restriction bnodes `bs`, the exact owl:cardinality of the first
// one whose onProperty is invp (the X equiv (invp exactly k) side).
let rec ico_exactcard_via (g : rdf_graph) (bs : list rdf_term) (invp : wf_iri)
  : Tot (option nat) (decreases bs) =
  match bs with
  | [] -> None
  | b :: tl ->
    (match term_as_subject b with
     | Some s ->
       (match find_first_object g s ico_owl_onProperty with
        | Some (T_IRI pp) ->
          if pp = invp
          then (match find_first_object g s ico_owl_cardinality with
                | Some (T_Literal l) ->
                  (match ico_parse_nat l.lexical_form with
                   | Some k -> Some k
                   | None -> ico_exactcard_via g tl invp)
                | _ -> ico_exactcard_via g tl invp)
          else ico_exactcard_via g tl invp
        | _ -> ico_exactcard_via g tl invp)
     | None -> ico_exactcard_via g tl invp)

// Restriction bnodes a named class C is linked to (either subClassOf or
// equivalentClass -- both directions of an equivalence appear post-closure).
let ico_restr_of (g : rdf_graph) (c : wf_iri) : list rdf_term =
  find_objects g (S_IRI c) ico_rdfs_subClassOf
  @ find_objects g (S_IRI c) ico_owl_equivalentClass

// FIBER lemma emission for one functional property p.
let ico_fiber_of (g : rdf_graph) (classes : list wf_iri) (p : wf_iri) : string =
  match ico_find_dom g p, ico_find_inv g p with
  | Some d, Some ip ->
    (match ico_svf_via g (ico_restr_of g d) p with
     | Some x ->
       (match ico_exactcard_via g (ico_restr_of g x) ip with
        | Some k ->
          "(assert (= " ^ ico_cvar classes d
          ^ " (* " ^ string_of_int k ^ " " ^ ico_cvar classes x ^ ")))\n"
        | None -> "")
     | None -> "")
  | _ -> ""

let rec ico_fiber_asserts (g : rdf_graph) (classes : list wf_iri)
                          (ps : list wf_iri)
  : Tot string (decreases ps) =
  match ps with
  | [] -> ""
  | p :: tl -> ico_fiber_of g classes p ^ ico_fiber_asserts g classes tl

// BIJECTION lemma: for property p (functional+inverse-functional) with
// inverse ip, any class d with d subclassof (p some y) and y subclassof
// (ip some d) forces |d| = |y|.
let rec ico_bij_for_prop (g : rdf_graph) (classes : list wf_iri)
                         (p : wf_iri) (ip : wf_iri) (cs : list wf_iri)
  : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | d :: tl ->
    let this =
      (match ico_svf_via g (ico_restr_of g d) p with
       | Some y ->
         (match ico_svf_via g (ico_restr_of g y) ip with
          | Some dback ->
            if dback = d
            then "(assert (= " ^ ico_cvar classes d ^ " " ^ ico_cvar classes y ^ "))\n"
            else ""
          | None -> "")
       | None -> "")
    in this ^ ico_bij_for_prop g classes p ip tl

let rec ico_bij_asserts (g : rdf_graph) (classes : list wf_iri)
                        (ps : list wf_iri)
  : Tot string (decreases ps) =
  match ps with
  | [] -> ""
  | p :: tl ->
    (match ico_find_inv g p with
     | Some ip -> ico_bij_for_prop g classes p ip classes
     | None -> "")
    ^ ico_bij_asserts g classes tl

// DISJOINT UNION: scan for `z equivalentClass <bnode unionOf(m1,m2)>`
// with m1 disjointWith m2.
let ico_union_of_triple (g : rdf_graph) (classes : list wf_iri) (t : triple) : string =
  if t.p = ico_owl_equivalentClass
  then (match t.s, t.o with
        | S_IRI z, T_BNode _ ->
          (match term_as_subject t.o with
           | Some bs ->
             (match find_first_object g bs ico_owl_unionOf with
              | Some lterm ->
                (match walk_rdf_list g lterm (length g) with
                 | [T_IRI m1; T_IRI m2] ->
                   if ico_disjoint g m1 m2
                   then "(assert (= " ^ ico_cvar classes z
                        ^ " (+ " ^ ico_cvar classes m1 ^ " " ^ ico_cvar classes m2 ^ ")))\n"
                   else ""
                 | _ -> "")
              | None -> "")
           | None -> "")
        | _ -> "")
  else ""

let rec ico_union_asserts (g : rdf_graph) (classes : list wf_iri)
                          (ts : list triple)
  : Tot string (decreases ts) =
  match ts with
  | [] -> ""
  | t :: tl -> ico_union_of_triple g classes t ^ ico_union_asserts g classes tl

// ONEOF NONEMPTINESS.
let ico_list_nonempty (g : rdf_graph) (head : rdf_term) : bool =
  match term_as_subject head with
  | Some s -> (match find_first_object g s rdf_first with Some _ -> true | None -> false)
  | None -> false

let rec ico_any_equiv_oneof (g : rdf_graph) (bs : list rdf_term)
  : Tot bool (decreases bs) =
  match bs with
  | [] -> false
  | b :: tl ->
    (match term_as_subject b with
     | Some s ->
       (match find_first_object g s ico_owl_oneOf2 with
        | Some l -> ico_list_nonempty g l
        | None -> false)
     | None -> false)
    || ico_any_equiv_oneof g tl

let ico_class_has_oneof (g : rdf_graph) (c : wf_iri) : bool =
  (match find_first_object g (S_IRI c) ico_owl_oneOf2 with
   | Some l -> ico_list_nonempty g l
   | None -> false)
  || ico_any_equiv_oneof g (find_objects g (S_IRI c) ico_owl_equivalentClass)

let rec ico_oneof_asserts (g : rdf_graph) (classes : list wf_iri)
                          (cs : list wf_iri)
  : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | c :: tl ->
    (if ico_class_has_oneof g c
     then "(assert (>= " ^ ico_cvar classes c ^ " 1))\n"
     else "")
    ^ ico_oneof_asserts g classes tl

let rec ico_class_decls (classes : list wf_iri) (cs : list wf_iri)
  : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | c :: tl ->
    "(declare-const " ^ ico_cvar classes c ^ " Int)\n"
    ^ "(assert (>= " ^ ico_cvar classes c ^ " 0))\n"
    ^ ico_class_decls classes tl

let rec ico_iri_inter (xs : list wf_iri) (ys : list wf_iri)
  : Tot (list wf_iri) (decreases xs) =
  match xs with
  | [] -> []
  | h :: tl -> (if ico_mem_iri h ys then [h] else []) @ ico_iri_inter tl ys

// The graph-level counting encoder the Phase-1 oracle consults. Builds
// the QF_LIA class-size linear system directly from the RL-base closure.
let encode_counting_smt (g : rdf_graph) : Tot string =
  let classes = ico_dedup_iri (ico_all_iris g) in
  let fprops  = ico_props_typed g ico_owl_FunctionalProperty in
  let ifprops = ico_props_typed g ico_owl_InverseFunctionalProperty in
  let bprops  = ico_iri_inter fprops ifprops in
  "(set-logic QF_LIA)\n"
  ^ "; Z33kr counting-fragment class-size encoding (Phase 1)\n"
  ^ ico_class_decls classes classes
  ^ ico_fiber_asserts g classes fprops
  ^ ico_bij_asserts g classes bprops
  ^ ico_union_asserts g classes g
  ^ ico_oneof_asserts g classes classes
  ^ "(check-sat)\n"

// ============================================================
// 7. The single assume val -- ASSUME-HOST (skills/ocaml-boundary).
//
// Host satisfiability oracle. Its semantics ARE z3's, exactly as
// regex_match's semantics are the host regex engine's -- moving z3 into
// F* would be as wrong as reverifying the regex engine. The `rlimit`
// bounds work deterministically (an instruction-count budget, not
// wall-clock), so the same input yields the same verdict on native and
// wasm. Realised by
//   minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh
// which in Phase 0 returns Z3_Unknown unconditionally (z3 not consulted;
// zero behaviour change). Tracking issue #296.
// ============================================================

assume val z3_check_sat : smtlib:string -> rlimit:nat -> Tot z3_verdict

// ============================================================
// 8. VERIFIED class-size unsat check (Z33kr Phase 2 -- oracle retirement).
//
// The z3 oracle above answers the counting-fragment class-size system
// (section 6b) with an UNVERIFIED host solver. For the systems the
// shipped W3C corpus actually produces (dl-910, one=two) that system is
// a TINY linear system with small integer coefficients whose
// unsatisfiability has a Farkas certificate -- a nonnegative-weighted
// combination of the constraints that sums to `0 >= positive`. This
// section decides those systems INSIDE the verified boundary:
//
//   - `build_lin_system g` : rebuild the SAME class-size relations the
//     section-6b SMT encoder emits (FIBER / BIJECTION / DISJOINT-UNION /
//     ONEOF-nonemptiness), but as an in-memory linear system over
//     per-named-class integer size variables, instead of an SMT string.
//   - `find_lin_cert`      : an UNVERIFIED searcher (integer Gaussian
//     elimination with multiplier tracking) that proposes a Farkas
//     certificate. It needs no proof: it is only ever a candidate.
//   - `farkas_check` + `farkas_sound` : a VERIFIED validator. `farkas_
//     sound` is a build-checked F* Lemma: whenever `farkas_check` accepts
//     a certificate, NO integer assignment satisfies the system. So a
//     `class_size_unsat g = true` verdict is a proven statement about the
//     linear system -- the arithmetic is verified, not trusted to z3.
//
// The remaining (documented, unchanged) trust boundary is the same one
// the section-6b lemmas already carried: that UNSAT of the class-size
// linear system implies the closure is inconsistent under Direct
// Semantics. That model-theoretic step (the FIBER / BIJECTION /
// DISJOINT-UNION / ONEOF soundness arguments) is prose, exactly as
// before; what moves inside F* here is the LIA decision the oracle used
// to delegate to z3. dl-909 is NOT decided by this path: its class-size
// system is genuinely satisfiable (the all-empty assignment with
// |only-d| >= 1 is a model), so no Farkas certificate exists and the
// checker returns false -- deriving |finite| >= 1 would need an UNSOUND
// nonemptiness rule (see the 2026-07-15 refutation note), which we do
// not add.
// ============================================================

// ---- 8a. Linear-system representation + Farkas validator (VERIFIED) ----

// One constraint over the class-size variables c0..c(N-1):
//   lc_is_eq = true  :  (lc_coeffs . x) =  lc_rhs
//   lc_is_eq = false :  (lc_coeffs . x) >= lc_rhs
noeq type lin_constraint = {
  lc_coeffs : list int;
  lc_rhs    : int;
  lc_is_eq  : bool;
}

let rec lin_dot (coeffs : list int) (x : list int) : Tot int (decreases coeffs) =
  match coeffs, x with
  | c :: cs, v :: vs -> c * v + lin_dot cs vs
  | _, _ -> 0

let lin_sat1 (c : lin_constraint) (x : list int) : bool =
  if c.lc_is_eq then lin_dot c.lc_coeffs x = c.lc_rhs
  else lin_dot c.lc_coeffs x >= c.lc_rhs

let rec lin_sat (cs : list lin_constraint) (x : list int)
  : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: tl -> lin_sat1 c x && lin_sat tl x

// A certificate is one integer multiplier per constraint. For a `>=`
// (GEq) constraint the multiplier must be nonnegative; equalities take
// any integer (both directions are available).
let rec valid_mults (cs : list lin_constraint) (ms : list int)
  : Tot bool (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' ->
    (if c.lc_is_eq then true else m >= 0) && valid_mults cs' ms'
  | [], [] -> true
  | _, _ -> false

// Sum_i m_i * (coeffs_i . x)  and  Sum_i m_i * rhs_i.
let rec weighted_lhs (cs : list lin_constraint) (ms : list int) (x : list int)
  : Tot int (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' -> m * lin_dot c.lc_coeffs x + weighted_lhs cs' ms' x
  | _, _ -> 0

let rec weighted_rhs (cs : list lin_constraint) (ms : list int)
  : Tot int (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' -> m * c.lc_rhs + weighted_rhs cs' ms'
  | _, _ -> 0

// Vector helpers over int rows.
let rec zeros (n : nat) : Tot (list int) (decreases n) =
  if n = 0 then [] else 0 :: zeros (n - 1)

let rec vscale (m : int) (v : list int) : Tot (list int) (decreases v) =
  match v with
  | [] -> []
  | h :: t -> (m * h) :: vscale m t

let rec vadd (a b : list int) : Tot (list int) (decreases a) =
  match a, b with
  | ha :: ta, hb :: tb -> (ha + hb) :: vadd ta tb
  | _, _ -> []

// The combined coefficient vector  Sum_i m_i * coeffs_i , length n.
let rec comb_coeffs (n : nat) (cs : list lin_constraint) (ms : list int)
  : Tot (list int) (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' ->
    vadd (vscale m c.lc_coeffs) (comb_coeffs n cs' ms')
  | _, _ -> zeros n

// Every constraint row has length exactly n.
let rec all_len (n : nat) (cs : list lin_constraint) : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: tl -> (List.Tot.length c.lc_coeffs = n) && all_len n tl

// ---- length lemmas ----

let rec zeros_len (n : nat) : Lemma (List.Tot.length (zeros n) = n) =
  if n = 0 then () else zeros_len (n - 1)

let rec vscale_len (m : int) (v : list int)
  : Lemma (ensures List.Tot.length (vscale m v) = List.Tot.length v) (decreases v) =
  match v with [] -> () | _ :: t -> vscale_len m t

let rec vadd_len (a b : list int)
  : Lemma (requires List.Tot.length a = List.Tot.length b)
          (ensures List.Tot.length (vadd a b) = List.Tot.length a)
          (decreases a) =
  match a, b with
  | _ :: ta, _ :: tb -> vadd_len ta tb
  | _, _ -> ()

let rec comb_len (n : nat) (cs : list lin_constraint) (ms : list int)
  : Lemma (requires all_len n cs /\ List.Tot.length ms = List.Tot.length cs)
          (ensures List.Tot.length (comb_coeffs n cs ms) = n)
          (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' ->
    comb_len n cs' ms';
    vscale_len m c.lc_coeffs;
    vadd_len (vscale m c.lc_coeffs) (comb_coeffs n cs' ms')
  | _, _ -> zeros_len n

// ---- dot-product linearity lemmas ----

let rec lin_dot_zeros (n : nat) (x : list int)
  : Lemma (ensures lin_dot (zeros n) x = 0) (decreases n) =
  match x with
  | [] -> ()
  | _ :: xs -> if n = 0 then () else lin_dot_zeros (n - 1) xs

let rec lin_dot_vscale (m : int) (v : list int) (x : list int)
  : Lemma (ensures lin_dot (vscale m v) x = m * lin_dot v x) (decreases v) =
  match v, x with
  | vh :: vt, xh :: xt ->
    lin_dot_vscale m vt xt;
    FStar.Math.Lemmas.paren_mul_right m vh xh
  | _, _ -> ()

let rec lin_dot_vadd (a b : list int) (x : list int)
  : Lemma (requires List.Tot.length a = List.Tot.length b)
          (ensures lin_dot (vadd a b) x = lin_dot a x + lin_dot b x)
          (decreases a) =
  match a, b, x with
  | ah :: at_, bh :: bt, xh :: xt ->
    lin_dot_vadd at_ bt xt;
    FStar.Math.Lemmas.distributivity_add_left ah bh xh
  | _, _, _ -> ()

// lin_dot of the combined vector equals the weighted LHS.
let rec comb_dot (n : nat) (cs : list lin_constraint) (ms : list int) (x : list int)
  : Lemma (requires all_len n cs /\ List.Tot.length ms = List.Tot.length cs)
          (ensures lin_dot (comb_coeffs n cs ms) x = weighted_lhs cs ms x)
          (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' ->
    comb_len n cs' ms';
    vscale_len m c.lc_coeffs;
    lin_dot_vadd (vscale m c.lc_coeffs) (comb_coeffs n cs' ms') x;
    lin_dot_vscale m c.lc_coeffs x;
    comb_dot n cs' ms' x
  | _, _ -> lin_dot_zeros n x

// ---- monotonicity: satisfied constraints + valid mults => weighted >= ----

let mult_mono (m : nat) (a : int) (b : int)
  : Lemma (requires b <= a) (ensures m * b <= m * a) =
  FStar.Math.Lemmas.lemma_mult_le_left m b a

let rec weighted_ge (cs : list lin_constraint) (ms : list int) (x : list int)
  : Lemma (requires lin_sat cs x /\ valid_mults cs ms)
          (ensures weighted_lhs cs ms x >= weighted_rhs cs ms)
          (decreases cs) =
  match cs, ms with
  | c :: cs', m :: ms' ->
    weighted_ge cs' ms' x;
    if c.lc_is_eq
    then ()  // lin_dot = rhs, so m*lin_dot = m*rhs
    else (assert (m >= 0);
          assert (lin_dot c.lc_coeffs x >= c.lc_rhs);
          mult_mono m (lin_dot c.lc_coeffs x) c.lc_rhs)
  | _, _ -> ()

// The validator: accept a certificate iff every row has length n, the
// multipliers line up and respect the GEq sign rule, the combined
// coefficient vector is the zero vector, and the combined RHS is
// strictly positive.
let farkas_check (n : nat) (cs : list lin_constraint) (ms : list int) : bool =
  all_len n cs
  && List.Tot.length ms = List.Tot.length cs
  && valid_mults cs ms
  && comb_coeffs n cs ms = zeros n
  && weighted_rhs cs ms > 0

// SOUNDNESS: an accepted certificate proves the system unsatisfiable
// over ALL integer assignments (hence over nat assignments too). The
// combined coefficient vector is zero, so the combined LHS is 0 for
// every x, yet the combined RHS is > 0 and the weighted combination of
// satisfied constraints would force LHS >= RHS -- contradiction.
let farkas_sound (n : nat) (cs : list lin_constraint) (ms : list int) (x : list int)
  : Lemma (requires farkas_check n cs ms /\ lin_sat cs x)
          (ensures False) =
  weighted_ge cs ms x;
  comb_dot n cs ms x;
  lin_dot_zeros n x

// ---- 8b. Build the class-size linear system from the closure ----
//
// Mirrors section 6b's SMT emission exactly, but emits `lin_constraint`
// records. Variable index of a class = its position in the deduped IRI
// list `classes`; N = length classes. Every coefficient row is built to
// length N by `mk_row`, so `all_len N` holds by construction.

// Sum of the values whose index equals `pos`.
let rec sum_at (pos : nat) (entries : list (nat & int)) : Tot int (decreases entries) =
  match entries with
  | [] -> 0
  | (i, v) :: tl -> (if i = pos then v else 0) + sum_at pos tl

// Length-n coefficient row from an (index, value) association list.
let rec mk_row (n : nat) (pos : nat) (entries : list (nat & int))
  : Tot (list int) (decreases n) =
  if n = 0 then []
  else sum_at pos entries :: mk_row (n - 1) (pos + 1) entries

let rec mk_row_len (n : nat) (pos : nat) (entries : list (nat & int))
  : Lemma (ensures List.Tot.length (mk_row n pos entries) = n) (decreases n) =
  if n = 0 then () else mk_row_len (n - 1) (pos + 1) entries

let cidx (classes : list wf_iri) (c : wf_iri) : nat = ico_iri_index classes c 0

// FIBER: |D| = k*|X|  ->  (+1 at D) + (-k at X) = 0.
let lc_fiber_of (g : rdf_graph) (n : nat) (classes : list wf_iri) (p : wf_iri)
  : list lin_constraint =
  match ico_find_dom g p, ico_find_inv g p with
  | Some d, Some ip ->
    (match ico_svf_via g (ico_restr_of g d) p with
     | Some x ->
       (match ico_exactcard_via g (ico_restr_of g x) ip with
        | Some k ->
          [ { lc_coeffs = mk_row n 0 [(cidx classes d, 1); (cidx classes x, - k)];
              lc_rhs = 0; lc_is_eq = true } ]
        | None -> [])
     | None -> [])
  | _ -> []

let rec lc_fiber_all (g : rdf_graph) (n : nat) (classes : list wf_iri)
                     (ps : list wf_iri)
  : Tot (list lin_constraint) (decreases ps) =
  match ps with
  | [] -> []
  | p :: tl -> lc_fiber_of g n classes p @ lc_fiber_all g n classes tl

// BIJECTION: |D| = |Y|  ->  (+1 at D) + (-1 at Y) = 0.
let rec lc_bij_for_prop (g : rdf_graph) (n : nat) (classes : list wf_iri)
                        (p : wf_iri) (ip : wf_iri) (cs : list wf_iri)
  : Tot (list lin_constraint) (decreases cs) =
  match cs with
  | [] -> []
  | d :: tl ->
    let this =
      (match ico_svf_via g (ico_restr_of g d) p with
       | Some y ->
         (match ico_svf_via g (ico_restr_of g y) ip with
          | Some dback ->
            if dback = d
            then [ { lc_coeffs = mk_row n 0 [(cidx classes d, 1); (cidx classes y, -1)];
                     lc_rhs = 0; lc_is_eq = true } ]
            else []
          | None -> [])
       | None -> [])
    in this @ lc_bij_for_prop g n classes p ip tl

let rec lc_bij_all (g : rdf_graph) (n : nat) (classes : list wf_iri)
                   (ps : list wf_iri)
  : Tot (list lin_constraint) (decreases ps) =
  match ps with
  | [] -> []
  | p :: tl ->
    (match ico_find_inv g p with
     | Some ip -> lc_bij_for_prop g n classes p ip classes
     | None -> [])
    @ lc_bij_all g n classes tl

// DISJOINT-UNION: |Z| = |m1| + |m2|  ->  (+1 Z) + (-1 m1) + (-1 m2) = 0.
let lc_union_of_triple (g : rdf_graph) (n : nat) (classes : list wf_iri) (t : triple)
  : list lin_constraint =
  if t.p = ico_owl_equivalentClass
  then (match t.s, t.o with
        | S_IRI z, T_BNode _ ->
          (match term_as_subject t.o with
           | Some bs ->
             (match find_first_object g bs ico_owl_unionOf with
              | Some lterm ->
                (match walk_rdf_list g lterm (length g) with
                 | [T_IRI m1; T_IRI m2] ->
                   if ico_disjoint g m1 m2
                   then [ { lc_coeffs = mk_row n 0
                              [(cidx classes z, 1); (cidx classes m1, -1);
                               (cidx classes m2, -1)];
                            lc_rhs = 0; lc_is_eq = true } ]
                   else []
                 | _ -> [])
              | None -> [])
           | None -> [])
        | _ -> [])
  else []

let rec lc_union_all (g : rdf_graph) (n : nat) (classes : list wf_iri)
                     (ts : list triple)
  : Tot (list lin_constraint) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl -> lc_union_of_triple g n classes t @ lc_union_all g n classes tl

// ONEOF nonemptiness: |C| >= 1  ->  (+1 at C) >= 1.
let rec lc_oneof_all (g : rdf_graph) (n : nat) (classes : list wf_iri)
                     (cs : list wf_iri)
  : Tot (list lin_constraint) (decreases cs) =
  match cs with
  | [] -> []
  | c :: tl ->
    (if ico_class_has_oneof g c
     then [ { lc_coeffs = mk_row n 0 [(cidx classes c, 1)];
              lc_rhs = 1; lc_is_eq = false } ]
     else [])
    @ lc_oneof_all g n classes tl

// ---- 8b2. Finite-pinned classes + member-nonemptiness rows ----
//
// (owl2-counting-extension wave, design note 2026-07-28 —
// Consistent-but-all-unsat.) The integer class-size variables are
// model-meaningful only for classes whose extension is FINITE in every
// model; the member row below is therefore gated on a PROVABLE
// finiteness pin:
//   - DIRECT pin: the class carries / is equivalent to an owl:oneOf
//     enumeration (ico_class_has_oneof), or has a subClassOf /
//     equivalentClass bound that is an owl:oneOf list or an
//     owl:unionOf list ALL of whose members carry owl:oneOf lists —
//     CEXT(C) is then contained in a finite union of finite
//     enumerations.
//   - PROPAGATION: finiteness transfers along exactly the relations
//     the row builders read. A bijection row |A| = |B| transfers it
//     either way; a fiber row |D| = k·|X| (k >= 1) either way
//     (D finite => X, being in bijection with a subset of D's fibers,
//     finite; X finite => D = k·X finite); a disjoint-union row
//     |Z| = |B| + |C| both up (parts finite => Z finite) and down
//     (parts are subclasses of Z, so Z finite => parts finite).
// MEMBER row: an asserted `x rdf:type C` with x an IRI or bnode
// denotes SOME element of CEXT(C) in every model, so |C| >= 1 —
// emitted only for finite-pinned C, keeping every row about an
// integer that exists. Withholding a row is always sound.

let rec ico_list_members_all_oneof (g : rdf_graph) (ms : list rdf_term)
  : Tot bool (decreases ms) =
  match ms with
  | [] -> true
  | m :: tl ->
    (match term_as_subject m with
     | Some s -> (match find_first_object g s ico_owl_oneOf2 with
                  | Some _ -> ico_list_members_all_oneof g tl
                  | None -> false)
     | None -> false)

let ico_enum_bound_object (g : rdf_graph) (o : rdf_term) : bool =
  match term_as_subject o with
  | Some s ->
    (match find_first_object g s ico_owl_oneOf2 with
     | Some _ -> true
     | None ->
       (match find_first_object g s ico_owl_unionOf with
        | Some l -> ico_list_members_all_oneof g (walk_rdf_list g l (length g))
        | None -> false))
  | None -> false

let rec ico_has_enum_bound (g : rdf_graph) (os : list rdf_term)
  : Tot bool (decreases os) =
  match os with
  | [] -> false
  | o :: tl -> ico_enum_bound_object g o || ico_has_enum_bound g tl

let ico_directly_pinned (g : rdf_graph) (c : wf_iri) : bool =
  ico_class_has_oneof g c
  || ico_has_enum_bound g (ico_restr_of g c)

// Finiteness-transfer edges, mirroring the row builders exactly.
let rec ico_fiber_edges (g : rdf_graph) (ps : list wf_iri)
  : Tot (list (wf_iri & wf_iri)) (decreases ps) =
  match ps with
  | [] -> []
  | p :: tl ->
    (match ico_find_dom g p, ico_find_inv g p with
     | Some d, Some ip ->
       (match ico_svf_via g (ico_restr_of g d) p with
        | Some x ->
          (match ico_exactcard_via g (ico_restr_of g x) ip with
           | Some k -> if k >= 1 then [(d, x)] else []
           | None -> [])
        | None -> [])
     | _, _ -> [])
    @ ico_fiber_edges g tl

let rec ico_bij_edges_for (g : rdf_graph) (p : wf_iri) (ip : wf_iri)
                          (cs : list wf_iri)
  : Tot (list (wf_iri & wf_iri)) (decreases cs) =
  match cs with
  | [] -> []
  | d :: tl ->
    (match ico_svf_via g (ico_restr_of g d) p with
     | Some y ->
       (match ico_svf_via g (ico_restr_of g y) ip with
        | Some dback -> if dback = d then [(d, y)] else []
        | None -> [])
     | None -> [])
    @ ico_bij_edges_for g p ip tl

let rec ico_bij_edges (g : rdf_graph) (classes : list wf_iri) (ps : list wf_iri)
  : Tot (list (wf_iri & wf_iri)) (decreases ps) =
  match ps with
  | [] -> []
  | p :: tl ->
    (match ico_find_inv g p with
     | Some ip -> ico_bij_edges_for g p ip classes
     | None -> [])
    @ ico_bij_edges g classes tl

let rec ico_union_edges (g : rdf_graph) (ts : list triple)
  : Tot (list (wf_iri & wf_iri)) (decreases ts) =
  match ts with
  | [] -> []
  | t :: tl ->
    (if t.p = ico_owl_equivalentClass
     then (match t.s, t.o with
           | S_IRI z, T_BNode _ ->
             (match term_as_subject t.o with
              | Some bs ->
                (match find_first_object g bs ico_owl_unionOf with
                 | Some lterm ->
                   (match walk_rdf_list g lterm (length g) with
                    | [T_IRI m1; T_IRI m2] ->
                      if ico_disjoint g m1 m2 then [(z, m1); (z, m2)] else []
                    | _ -> [])
                 | None -> [])
              | None -> [])
           | _, _ -> [])
     else [])
    @ ico_union_edges g tl

let rec ico_edge_step (edges : list (wf_iri & wf_iri)) (c : wf_iri)
  : Tot (list wf_iri) (decreases edges) =
  match edges with
  | [] -> []
  | (a, b) :: tl ->
    (if a = c then [b] else if b = c then [a] else [])
    @ ico_edge_step tl c

let rec ico_step_all (edges : list (wf_iri & wf_iri)) (frontier : list wf_iri)
  : Tot (list wf_iri) (decreases frontier) =
  match frontier with
  | [] -> []
  | c :: tl -> ico_edge_step edges c @ ico_step_all edges tl

let rec ico_filter_new (visited : list wf_iri) (cands : list wf_iri)
  : Tot (list wf_iri) (decreases cands) =
  match cands with
  | [] -> []
  | c :: tl ->
    let rest = ico_filter_new visited tl in
    if ico_mem_iri c visited || ico_mem_iri c rest then rest else c :: rest

// Fuel-bounded undirected BFS: running out of fuel only WITHHOLDS
// finiteness (fewer member rows) — sound.
let rec ico_finite_bfs (edges : list (wf_iri & wf_iri))
                       (frontier : list wf_iri) (visited : list wf_iri)
                       (fuel : nat)
  : Tot (list wf_iri) (decreases fuel) =
  if fuel = 0 then visited
  else
    match frontier with
    | [] -> visited
    | _ ->
      let fresh = ico_filter_new visited (ico_step_all edges frontier) in
      (match fresh with
       | [] -> visited
       | _ -> ico_finite_bfs edges fresh (visited @ fresh) (fuel - 1))

let rec ico_pinned_of (g : rdf_graph) (cs : list wf_iri)
  : Tot (list wf_iri) (decreases cs) =
  match cs with
  | [] -> []
  | c :: tl ->
    let rest = ico_pinned_of g tl in
    if ico_directly_pinned g c then c :: rest else rest

let ico_finite_classes (g : rdf_graph) (classes : list wf_iri)
                       (fprops : list wf_iri) (bprops : list wf_iri)
  : list wf_iri =
  let pinned = ico_pinned_of g classes in
  let edges = ico_fiber_edges g fprops
              @ ico_bij_edges g classes bprops
              @ ico_union_edges g g in
  ico_finite_bfs edges pinned pinned (List.Tot.length edges + 1)

let rec ico_class_has_member (ts : list triple) (c : wf_iri)
  : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: tl ->
    (t.p = ico_rdf_type
     && (match t.o with T_IRI x -> x = c | _ -> false)
     && (match t.s with S_IRI _ | S_BNode _ -> true))
    || ico_class_has_member tl c

let rec lc_member_all (g : rdf_graph) (n : nat) (classes : list wf_iri)
                      (finite : list wf_iri) (cs : list wf_iri)
  : Tot (list lin_constraint) (decreases cs) =
  match cs with
  | [] -> []
  | c :: tl ->
    (if ico_mem_iri c finite && ico_class_has_member g c
     then [ { lc_coeffs = mk_row n 0 [(cidx classes c, 1)];
              lc_rhs = 1; lc_is_eq = false } ]
     else [])
    @ lc_member_all g n classes finite tl

// The equality rows (FIBER / BIJECTION / DISJOINT-UNION) come first,
// then the ONEOF `>= 1` bound rows. `class_of_sys` returns (N, classes,
// eq-rows, bound-rows) so the searcher and validator share the ordering.
let build_lin_system (g : rdf_graph)
  : (nat & list wf_iri & list lin_constraint & list lin_constraint) =
  let classes = ico_dedup_iri (ico_all_iris g) in
  let n = List.Tot.length classes in
  let fprops  = ico_props_typed g ico_owl_FunctionalProperty in
  let ifprops = ico_props_typed g ico_owl_InverseFunctionalProperty in
  let bprops  = ico_iri_inter fprops ifprops in
  let eqs =
    lc_fiber_all g n classes fprops
    @ lc_bij_all g n classes bprops
    @ lc_union_all g n classes g in
  let finite = ico_finite_classes g classes fprops bprops in
  let bounds = lc_oneof_all g n classes classes
               @ lc_member_all g n classes finite classes in
  (n, classes, eqs, bounds)

// ---- 8c. Certificate searcher (UNVERIFIED -- validated by farkas_check) ----
//
// Integer Gaussian elimination over the equality rows, carrying a
// per-row multiplier vector (`er_cert`, one entry per original equality
// row) so that at all times  er_coeffs = Sum_j er_cert_j * (eq row j).
// After elimination we look for a reduced row that is a single nonzero
// multiple of a bounded variable v (a*e_v = 0), whose attached cert is
// the equality-side of a Farkas certificate; the bound `v >= k` supplies
// the strictly-positive RHS. Pivots are taken only on +/-1 coefficients
// (the class-size rows always carry a unit-coefficient "defined" class),
// keeping the arithmetic fraction-free; if no unit pivot exists the pass
// stops and the searcher returns None (=> no verified flip; falls
// through to the z3 oracle, exactly as before).

noeq type erow = { er_coeffs : list int; er_cert : list int; }

let rec lidx (xs : list int) (i : nat) : Tot int (decreases xs) =
  match xs with
  | [] -> 0
  | h :: tl -> if i = 0 then h else lidx tl (i - 1)

let rec vsub (a b : list int) : Tot (list int) (decreases a) =
  match a, b with
  | ha :: ta, hb :: tb -> (ha - hb) :: vsub ta tb
  | _, _ -> a

let rec vneg (a : list int) : Tot (list int) (decreases a) =
  match a with [] -> [] | h :: t -> (- h) :: vneg t

// Unit basis vector e_i of length len (1 at position i, 0 elsewhere).
let rec unit_basis_from (len : nat) (pos : nat) (i : nat)
  : Tot (list int) (decreases len) =
  if len = 0 then []
  else (if pos = i then 1 else 0) :: unit_basis_from (len - 1) (pos + 1) i

let unit_basis (len : nat) (i : nat) : list int = unit_basis_from len 0 i

let rec erows_of_aux (e : nat) (i : nat) (eqs : list lin_constraint)
  : Tot (list erow) (decreases eqs) =
  match eqs with
  | [] -> []
  | c :: tl ->
    { er_coeffs = c.lc_coeffs; er_cert = unit_basis e i }
    :: erows_of_aux e (i + 1) tl

let erows_of (eqs : list lin_constraint) : list erow =
  erows_of_aux (List.Tot.length eqs) 0 eqs

// Eliminate column j from row r using unit-pivot row piv (piv[j] = 1).
let elim_row (j : nat) (piv : erow) (r : erow) : erow =
  let a = lidx r.er_coeffs j in
  if a = 0 then r
  else { er_coeffs = vsub r.er_coeffs (vscale a piv.er_coeffs);
         er_cert   = vsub r.er_cert   (vscale a piv.er_cert) }

// Find, among `rows`, the first with a +/-1 coefficient at column j,
// normalised so that coefficient becomes +1; return it plus the rest.
let rec find_unit_pivot (j : nat) (rows : list erow)
  : Tot (option (erow & list erow)) (decreases rows) =
  match rows with
  | [] -> None
  | r :: tl ->
    let a = lidx r.er_coeffs j in
    if a = 1 then Some (r, tl)
    else if a = -1
    then Some ({ er_coeffs = vneg r.er_coeffs; er_cert = vneg r.er_cert }, tl)
    else (match find_unit_pivot j tl with
          | Some (p, rest) -> Some (p, r :: rest)
          | None -> None)

let rec elim_cols (cols_left : nat) (j : nat) (active : list erow) (solved : list erow)
  : Tot (list erow) (decreases cols_left) =
  if cols_left = 0 then solved @ active
  else
    match find_unit_pivot j active with
    | None -> elim_cols (cols_left - 1) (j + 1) active solved
    | Some (piv, rest) ->
      let rest'   = List.Tot.map (elim_row j piv) rest in
      let solved' = List.Tot.map (elim_row j piv) solved in
      elim_cols (cols_left - 1) (j + 1) rest' (piv :: solved')

// Is `coeffs` a single nonzero entry a*e_v? Return Some (v, a).
let rec single_nonzero (coeffs : list int) (pos : nat)
  : Tot (option (nat & int)) (decreases coeffs) =
  match coeffs with
  | [] -> None
  | h :: tl ->
    if h = 0 then single_nonzero tl (pos + 1)
    else (match single_nonzero tl (pos + 1) with
          | None -> Some (pos, h)
          | Some _ -> None)   // more than one nonzero => not single

// Lower bound (if any) on variable v from the ONEOF bound rows; also the
// bound row's position among `bounds`.
let rec bound_of_var (bounds : list lin_constraint) (v : nat) (pos : nat)
  : Tot (option (nat & int)) (decreases bounds) =
  match bounds with
  | [] -> None
  | b :: tl ->
    (match single_nonzero b.lc_coeffs 0 with
     | Some (bv, bc) ->
       if bv = v && bc = 1 && b.lc_rhs >= 1 then Some (pos, b.lc_rhs)
       else bound_of_var tl v (pos + 1)
     | None -> bound_of_var tl v (pos + 1))

let iabs (a : int) : nat = if a >= 0 then a else - a

// From a reduced row (cert over eq rows, coeffs = a*e_v with a<>0) and a
// matching bound at position bpos with multiplier need |a|, assemble the
// full multiplier list aligned to (eqs @ bounds).
let assemble_mults (cert : list int) (a : int) (num_bounds : nat) (bpos : nat)
  : list int =
  let t = if a > 0 then (-1) else 1 in
  let eqmults = vscale t cert in
  let rec bmults (k : nat) (i : nat) : Tot (list int) (decreases k) =
    if k = 0 then []
    else (if i = bpos then iabs a else 0) :: bmults (k - 1) (i + 1) in
  eqmults @ bmults num_bounds 0

// Scan reduced rows for a single-nonzero bounded-variable row; assemble.
let rec scan_rows (rows : list erow) (bounds : list lin_constraint)
                  (num_bounds : nat)
  : Tot (option (list int)) (decreases rows) =
  match rows with
  | [] -> None
  | r :: tl ->
    (match single_nonzero r.er_coeffs 0 with
     | Some (v, a) ->
       if a = 0 then scan_rows tl bounds num_bounds
       else (match bound_of_var bounds v 0 with
             | Some (bpos, _k) -> Some (assemble_mults r.er_cert a num_bounds bpos)
             | None -> scan_rows tl bounds num_bounds)
     | None -> scan_rows tl bounds num_bounds)

let find_lin_cert (n : nat) (classes : list wf_iri)
                  (eqs : list lin_constraint) (bounds : list lin_constraint)
  : option (list int) =
  let rows = erows_of eqs in
  let reduced = elim_cols n 0 rows [] in
  scan_rows reduced bounds (List.Tot.length bounds)

// ---- 8d. The verified verdict ----
//
// `class_size_unsat g = true` is a PROVEN statement (via farkas_sound)
// that the class-size linear system built from g has no integer
// assignment -- hence, by the section-6b/8-header soundness of the
// class-size lemmas under Direct Semantics, the closure is inconsistent.
// Gated by `in_counting_fragment` to mirror the z3 oracle's scope; the
// validator makes the verdict sound regardless of gating.
let class_size_unsat (g : rdf_graph) : Tot bool =
  if not (in_counting_fragment g) then false
  else
    let (n, classes, eqs, bounds) = build_lin_system g in
    let sys = eqs @ bounds in
    match find_lin_cert n classes eqs bounds with
    | None -> false
    | Some ms -> farkas_check n sys ms

// The soundness statement F* checks: an accepted verdict means the
// built linear system is unsatisfiable over every integer assignment.
let class_size_unsat_sound (g : rdf_graph) (x : list int)
  : Lemma (requires class_size_unsat g = true)
          (ensures (let (n, _, eqs, bounds) = build_lin_system g in
                    ~(lin_sat (eqs @ bounds) x))) =
  let (n, classes, eqs, bounds) = build_lin_system g in
  let sys = eqs @ bounds in
  match find_lin_cert n classes eqs bounds with
  | None -> ()
  | Some ms ->
    if lin_sat sys x then farkas_sound n sys ms x else ()
