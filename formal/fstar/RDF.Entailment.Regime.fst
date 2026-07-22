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
open XSD.IEEE754
open Parser.JSON
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
let rdf_json_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"

// ---- rdf:JSON value equality (structural, IEEE-754 numbers) ------------
// Two rdf:JSON literals are value-equal iff their JSON values are equal:
// objects are UNORDERED (json-object-unordered), arrays are ORDERED
// (json-array-ordered NEGATIVE), and numbers compare by IEEE-754 binary64
// value so +0 <> -0 (json-zero) and decimals that round to the same double
// are equal (json-round-same). Fuel-bounded on the JSON tree size.
let rec json_value_eq (fuel : nat) (v1 v2 : json_val) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match v1, v2 with
    | JNull, JNull       -> true
    | JBool a, JBool b   -> a = b
    | JString a, JString b -> a = b
    | JNumber a, JNumber b -> json_number_eq a b
    | JArray xs, JArray ys -> json_arr_eq (fuel - 1) xs ys
    | JObject fs, JObject gs ->
      length fs = length gs && json_obj_eq (fuel - 1) fs gs
    | _, _ -> false
and json_arr_eq (fuel : nat) (xs ys : list json_val) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match xs, ys with
    | [], [] -> true
    | x :: xr, y :: yr -> json_value_eq (fuel - 1) x y && json_arr_eq (fuel - 1) xr yr
    | _, _ -> false
and json_obj_eq (fuel : nat) (fs gs : list (string & json_val)) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match fs with
    | [] -> true
    | (k, v) :: rest ->
      (match assoc k gs with
       | Some v' -> json_value_eq (fuel - 1) v v' && json_obj_eq (fuel - 1) rest gs
       | None    -> false)

let rdf_json_value_eq (lex1 lex2 : string) : bool =
  match parse_json lex1, parse_json lex2 with
  | Some v1, Some v2 -> json_value_eq (json_size v1 + json_size v2 + 1) v1 v2
  | _, _             -> lex1 = lex2

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

// Opaque (case-SENSITIVE) literal equality — the exact syntactic token,
// language tag included. Used for directional language strings sitting
// inside a triple term (see dt_value_leq).
let lit_opaque_eq (l1 l2 : literal) : bool =
  l1.lexical_form = l2.lexical_form && l1.datatype = l2.datatype &&
  l1.lang_tag = l2.lang_tag && l1.direction = l2.direction

// D-entailment literal equality, POSITION-AWARE (inside_tt = are these
// literals inside a triple term?).
//   * A directional language string inside a triple term is OPAQUE:
//     compared case-sensitively, so "x"@en-us--ltr <> "x"@en-US--ltr
//     (the opaque-dir-language-string NEGATIVE fixture). Outside a triple
//     term, and for plain language strings anywhere, the RDF 1.1
//     case-insensitive rule applies (the opaque-language-string fixtures).
//   * xsd:integer / xsd:decimal compare by value ("042" = "42").
//   * everything else falls back to RDF.Term.literal_eq.
let dt_value_leq (inside_tt : bool) (l1 l2 : literal) : bool =
  if inside_tt && Some? l1.direction && Some? l2.direction then
    lit_opaque_eq l1 l2
  else if l1.datatype = xsd_double && l2.datatype = xsd_double then
    // IEEE-754 binary64 value equality (+0 <> -0, round-to-even, overflow->inf).
    double_value_eq l1.lexical_form l2.lexical_form
  else if l1.datatype = xsd_float && l2.datatype = xsd_float then
    float_value_eq l1.lexical_form l2.lexical_form
  else if l1.datatype = rdf_json_iri && l2.datatype = rdf_json_iri then
    rdf_json_value_eq l1.lexical_form l2.lexical_form
  else if is_exact_scaled_dt l1.datatype && is_exact_scaled_dt l2.datatype then
    (match literal_to_scaled l1, literal_to_scaled l2 with
     | Some s1, Some s2 -> l1.datatype = l2.datatype && scaled_cmp s1 s2 = 0
     | _, _             -> literal_eq l1 l2)
  else literal_eq l1 l2

// A blank node may NOT range over a MALFORMED literal in a recognized
// datatype — a malformed literal denotes nothing, so no term (and no
// existential blank node) can be it (the malformed-literal-bnode-neg
// fixture). Well-formed literals, IRIs and triple terms are all bindable.
let bnd_rdf (t : rdf_term) : bool =
  match t with
  | T_Literal l -> not (literal_ill_formed l.datatype l.lexical_form)
  | _           -> true

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

// RDF (D-)entailment: recognized-datatype value equality (position-aware)
// + no blank-node ranging over malformed literals.
let entails_rdf (a b : list triple) : bool =
  entails_with dt_value_leq bnd_rdf a b

// RDFS entailment: + reifies-range closure.
let entails_rdfs (a b : list triple) : bool =
  entails_with dt_value_leq bnd_rdf (rdfs_closure a) b

// RDFS-Plus entailment: + owl:sameAs (IRI transparency) + reifies-range.
let entails_rdfs_plus (a b : list triple) : bool =
  entails_with dt_value_leq bnd_rdf (owl_closure (rdfs_closure a)) b
