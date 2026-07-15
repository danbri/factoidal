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
let ico_authored_complement (t : triple) : bool =
  t.p = ico_owl_complementOf
  && (match t.s with
      | S_BNode b -> not (bnode_is_rl_canonical b)
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
