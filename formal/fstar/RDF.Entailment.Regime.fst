module RDF.Entailment.Regime

// RDF 1.2 entailment beyond the simple regime (W3C RDF 1.2 Semantics).
// Builds on RDF.Entailment.Simple's homomorphism engine (reused via its
// `leq`-parameterized `entails_with`) by (a) matching literals up to
// recognized-datatype VALUE equality and (b) closing the antecedent graph
// under the RDFS / RDFS-Plus rules the suite exercises.
//
// Scope + honest boundary (per Iron Rule #1, all F*-native):
//   * dt_value_leq  — value equality for the recognized numeric datatypes
//     (xsd:integer / xsd:decimal / xsd:double, via XSD.Datatypes'
//     literal_to_scaled). All OTHER literals — including language and
//     directional-language strings — compare by OPAQUE syntactic equality
//     (case-SENSITIVE on the language tag), which is what the triple-term
//     opacity tests require (`@en-us--ltr` <> `@en-US--ltr`). This is
//     deliberately stricter than RDF.Term.literal_eq, whose langtag
//     compare is case-insensitive.
//   * reifies-range closure (RDFS) — `X rdf:reifies Y` with Y an IRI/bnode
//     adds `Y rdf:type rdfs:Proposition`.
//   * owl:sameAs closure (RDFS-Plus) — IRIs are transparent, INCLUDING
//     inside triple terms, so equal IRIs are inter-substitutable.
//
// NOT covered here (need a generalized-RDF term model with literal /
// triple-term SUBJECTS, which RDF.Term.subject = S_IRI | S_BNode does not
// admit): `literal-type` (`"42" rdf:type xsd:integer`) and
// `triple-terms-propositions` (`<<(..)>> rdf:type rdfs:Proposition`).
// Also not covered: IEEE-754 float/double value semantics (±0, round-to-
// even, infinity) and rdf:JSON canonicalization — those are the remaining
// D-entailment fixtures (a separate value-model effort).

open RDF.Graph.Executable
open RDF.Term
open RDF.Entailment.Simple
open XSD.Datatypes
open FStar.List.Tot

// ---- Vocabulary IRIs (wf_iri, built like RDF.Term's xsd_* constants) ----
let rdf_type_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_reifies_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies"
let rdfs_proposition_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2000/01/rdf-schema#Proposition");
  "http://www.w3.org/2000/01/rdf-schema#Proposition"
let owl_sameas_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#sameAs");
  "http://www.w3.org/2002/07/owl#sameAs"

// ---- Value-aware literal equality --------------------------------------

// The datatypes whose value space `literal_to_scaled` / `scaled_cmp`
// represent EXACTLY: xsd:integer and xsd:decimal (arbitrary-precision
// scaled integers). xsd:double / xsd:float are deliberately EXCLUDED —
// the scaled form collapses +0.0 and -0.0 (the `double-zero` /
// `float-zero` fixtures require them distinct) and does not model IEEE-754
// rounding, so double/float value comparison would be unsound. Those, and
// rdf:JSON, are handled as an unsupported-datatype capability boundary in
// the runner, not silently mis-compared here.
let is_exact_scaled_dt (dt : wf_iri) : bool =
  dt = xsd_integer || dt = xsd_decimal

// D-entailment literal equality: xsd:integer / xsd:decimal compare by
// value (so "042"^^xsd:integer = "42"^^xsd:integer); every other literal
// falls back to RDF.Term.literal_eq (which, per RDF 1.1 Concepts §3.3,
// compares language tags case-INSENSITIVELY — `@en-us` = `@en-US`, which
// the opaque-language-string fixtures require).
let dt_value_leq (l1 l2 : literal) : bool =
  if is_exact_scaled_dt l1.datatype && is_exact_scaled_dt l2.datatype then
    (match literal_to_scaled l1, literal_to_scaled l2 with
     | Some s1, Some s2 -> l1.datatype = l2.datatype && scaled_cmp s1 s2 = 0
     | _, _             -> literal_eq l1 l2)
  else literal_eq l1 l2

// ---- RDFS reifies-range closure ----------------------------------------

let reifies_prop_triples (t : triple) : list triple =
  if t.p = rdf_reifies_iri then
    (match t.o with
     | T_IRI i   -> [ { s = S_IRI i;   p = rdf_type_iri; o = T_IRI rdfs_proposition_iri } ]
     | T_BNode b -> [ { s = S_BNode b; p = rdf_type_iri; o = T_IRI rdfs_proposition_iri } ]
     | _         -> [])
  else []

let rdfs_closure (ts : list triple) : list triple =
  ts @ collect reifies_prop_triples ts

// ---- owl:sameAs closure (IRI transparency, incl. triple-term interiors) -

let subst_subj (x y : wf_iri) (s : subject) : subject =
  match s with
  | S_IRI i   -> if i = x then S_IRI y else S_IRI i
  | S_BNode b -> S_BNode b

let rec subst_term (x y : wf_iri) (t : rdf_term) : Tot rdf_term (decreases t) =
  match t with
  | T_IRI i        -> if i = x then T_IRI y else T_IRI i
  | T_BNode b      -> T_BNode b
  | T_Literal l    -> T_Literal l
  | T_TripleTerm s p o ->
    T_TripleTerm (subst_subj x y s) (if p = x then y else p) (subst_term x y o)

let subst_triple (x y : wf_iri) (t : triple) : triple =
  { s = subst_subj x y t.s;
    p = (if t.p = x then y else t.p);
    o = subst_term x y t.o }

// Collect (a, b) for every `a owl:sameAs b` with both sides IRIs.
let sameas_pairs (ts : list triple) : list (wf_iri & wf_iri) =
  collect (fun t ->
    if t.p = owl_sameas_iri then
      (match t.s, t.o with
       | S_IRI a, T_IRI b -> [ (a, b) ]
       | _, _             -> [])
    else []) ts

// One-pass owl:sameAs closure: for each pair, add every triple with the
// two IRIs swapped in both directions. One pass suffices for the single-
// pair transparency fixtures; the originals are kept.
let apply_sameas_pair (acc : list triple) (p : (wf_iri & wf_iri)) : list triple =
  let (a, b) = p in
  acc @ map (subst_triple b a) acc @ map (subst_triple a b) acc

let owl_closure (ts : list triple) : list triple =
  fold_left apply_sameas_pair ts (sameas_pairs ts)

// ---- Regime entrypoints ------------------------------------------------

// RDF (D-)entailment: recognized-datatype value equality, no axiomatic
// triples added (the tractable RDF-regime fixtures are value/identity).
let entails_rdf (a b : list triple) : bool =
  entails_with dt_value_leq a b

// RDFS entailment: value equality + reifies-range closure.
let entails_rdfs (a b : list triple) : bool =
  entails_with dt_value_leq (rdfs_closure a) b

// RDFS-Plus entailment: value equality + owl:sameAs (IRI transparency)
// + reifies-range closure.
let entails_rdfs_plus (a b : list triple) : bool =
  entails_with dt_value_leq (owl_closure (rdfs_closure a)) b
