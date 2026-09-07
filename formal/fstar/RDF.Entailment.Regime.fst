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
//   * RDFS closure — the RDFS.Closure rule driver (rdfs2 domain, rdfs3
//     range, rdfs5 subPropertyOf-transitivity, rdfs7 subPropertyOf,
//     rdfs9 subClassOf, rdfs11 subClassOf-transitivity, plus the finite
//     container-membership slice), run to its fixed point, PRECEDED by
//     the RDF 1.2 reifies-range step (`X rdf:reifies Y` with Y an IRI or
//     bnode adds `Y rdf:type rdfs:Proposition`). Before 2026-07-31 the
//     reifies step was named `rdfs_closure` and shadowed the rule driver,
//     so this regime ran that ONE rule — finding RS-4, issue #335.
//   * owl:sameAs closure (RDFS-Plus) — IRIs are transparent, INCLUDING
//     inside triple terms, so equal IRIs are inter-substitutable.
//
// GENERALIZED-RDF ANTECEDENT (added 2026-09-07). RDF 1.2 Semantics states
// its semantic conditions over a term universe in which a triple term or a
// literal can be the SUBJECT of a derived triple -- e.g. "triple terms
// denote instances of rdfs:Proposition" needs `<<( s p o )>> rdf:type
// rdfs:Proposition`. RDF.Term.triple cannot hold that, because
// RDF.Term.subject = S_IRI | S_BNode (which is correct: no RDF 1.2
// concrete syntax can WRITE such a triple). The regime layer therefore
// closes the antecedent into `gtriple` -- a subject-generalized triple --
// and runs the homomorphism against that. The CONSEQUENT stays an
// ordinary `list triple`, because it is always parsed from a concrete
// syntax; a blank node in the consequent may bind to a triple term, which
// is how `triple-terms-propositions` is discharged.
//
// NOT covered here: `literal-type` (`"42"^^xsd:integer rdf:type
// xsd:integer`) -- the gtriple model now admits it, but the vendored
// manifest entry for that test is unreadable (upstream typo, see the
// design record 2026-09-07-rdf12-sparql12-semantics-fstar.md), so the
// rule would be unmeasurable; and the `annotation` / `annotation-unfolded`
// fixtures, whose expected graphs contradict the RDF 1.2 Turtle
// annotation-syntax expansion that the SAME upstream commit's Turtle
// eval oracles define (same design record, tight case TC-1).

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

// ---- RDF 1.2 rdf:reifies range step ------------------------------------

let reifies_prop_triples (t : triple) : list triple =
  if t.p = rdf_reifies_iri then
    (match t.o with
     | T_IRI i   -> [ { s = S_IRI i;   p = rdf_type_iri; o = T_IRI rdfs_proposition_iri } ]
     | T_BNode b -> [ { s = S_BNode b; p = rdf_type_iri; o = T_IRI rdfs_proposition_iri } ]
     | _         -> [])
  else []

// The RDF 1.2 `rdf:reifies` range step ALONE — one rule:
//   X rdf:reifies Y  |-  Y rdf:type rdfs:Proposition   (Y an IRI or bnode)
//
// This function was called `rdfs_closure` until 2026-07-31. Under that
// name it SHADOWED `RDFS.Closure.rdfs_closure` — the real rdfs2 / rdfs3 /
// rdfs5 / rdfs7 / rdfs9 / rdfs11 rule driver, which this module gets in
// scope through `open RDF.Graph.Executable` (that module `include`s
// RDFS.Closure). The shadow made `entails_rdfs` below apply this ONE rule
// and none of rdfs1-rdfs13, so the rdf12 manifests' "RDFS" regime measured
// an engine that did no RDFS reasoning. Recorded as finding RS-4 in
// docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md §4 and
// tracked in #335. The name now says what the function is; the RDFS
// closure below says what it is.
let rdf12_reifies_closure (ts : list triple) : list triple =
  ts @ collect reifies_prop_triples ts

// ---- RDFS-regime antecedent closure ------------------------------------

// Fuel for the RDFS rule driver. 100 everywhere else in the tree that
// calls RDFS.Closure.rdfs_closure (OWL.Closure's entailment_closure
// callers, RIF.Core.Tests.default_fuel, the runner's
// apply_entailment_regime); kept identical here so the rdf12-entailment
// path and the SPARQL-entailment / rdf-mt paths cannot diverge on fuel.
let rdfs_regime_fuel : nat = 100

// The antecedent closure the "RDFS" regime applies: the RDF 1.2
// rdf:reifies range step, then the RDFS.Closure rule driver run to its
// fixed point.
//
// Order: reifies FIRST, so the `rdf:type rdfs:Proposition` triples it
// emits are visible to rdfs9 (subClassOf) / rdfs2 (domain) / rdfs3
// (range) inside the fixed-point loop. Residual incompleteness, stated
// rather than hidden: an `rdf:reifies` triple DERIVED by rdfs7
// (subPropertyOf) does not re-trigger the reifies step, because that step
// runs once before the loop rather than inside `rdfs_closure_step`. No
// fixture in the tree exercises that shape. The clean fix is to seed the
// RDF 1.2 vocabulary axiom `rdf:reifies rdfs:range rdfs:Proposition` and
// let rdfs3 do the work inside the loop — deliberately NOT done here,
// because axiom seeding into a closure is exactly the change that
// regressed OWL-RL consistency once already (see RDFS.Closure.fsti's
// `rdfs_closure_with_reflexivity` banner) and it needs its own commit.
//
// Deliberately the BARE `rdfs_closure`, NOT
// `rdfs_closure_with_reflexivity`: finding RS-1 of the same design note
// gives a machine-checked witness that the reflexivity harvest emits
// triples no RDFS rule licenses (it reads owl:Class / owl:ObjectProperty
// typing, which is an OWL-rung licence). Using it here would make
// NegativeEntailmentTests wrongly pass.
// The RDF 1.2 vocabulary axiom that makes the reifies-range step a
// consequence of rdfs3 rather than a step outside the loop:
//   rdf:reifies rdfs:range rdfs:Proposition
// Seeding it lets an rdf:reifies triple DERIVED inside the fixed point (by
// rdfs7 from a subproperty of rdf:reifies, say) trigger the range
// condition. `rdf12_reifies_closure` is kept as well: rdfs3 as
// RDFS.Closure implements it reads the object as a subject-capable term,
// and the pre-pass is what covers the shapes it cannot.
let rdf12_vocabulary_axioms : list triple =
  [ { s = S_IRI rdf_reifies_iri;
      p = RDFS.Closure.rdfs_range;
      o = T_IRI rdfs_proposition_iri } ]

let rdfs_regime_closure (ts : list triple) : list triple =
  RDFS.Closure.rdfs_closure
    (rdf12_vocabulary_axioms @ rdf12_reifies_closure ts) rdfs_regime_fuel

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

// ---- Generalized-RDF antecedent (RDF 1.2 Semantics) --------------------

// A subject-generalized triple: the subject is an arbitrary rdf_term, so a
// triple term (or a literal) can carry a derived type assertion. Only the
// ANTECEDENT is generalized -- see the module banner.
noeq type gtriple = { gs : rdf_term; gp : wf_iri; go : rdf_term }

let gtriple_of_triple (t : triple) : gtriple =
  { gs = subj_as_term t.s; gp = t.p; go = t.o }

// Subject match against a GENERALIZED ground subject. Same three cases as
// RDF.Entailment.Simple.match_subj, with the ground side widened from
// `subject` to `rdf_term`: a consequent blank node may therefore bind to a
// triple term, and a consequent IRI still matches only the same IRI.
// `bnd` gates what a blank node may range over, exactly as in the
// object-position matcher (a malformed recognized-datatype literal
// denotes nothing, so nothing may range over it).
let match_subj_g (bnd : rdf_term -> bool) (b : binding) (ps : subject) (gs : rdf_term)
  : option binding =
  match ps with
  | S_BNode lbl ->
    (match assoc lbl b with
     | Some t -> if rdf_term_eq t gs then Some b else None
     | None   -> if bnd gs then Some ((lbl, gs) :: b) else None)
  | S_IRI i ->
    (match gs with
     | T_IRI j -> if i = j then Some b else None
     | _       -> None)

let match_gtriple (leq : bool -> literal -> literal -> bool)
                  (bnd : rdf_term -> bool)
                  (b : binding) (tb : triple) (ta : gtriple) : option binding =
  if tb.p = ta.gp then
    (match match_subj_g bnd b tb.s ta.gs with
     | Some b1 -> match_term leq bnd false b1 tb.o ta.go
     | None    -> None)
  else None

// Backtracking search over a generalized antecedent. Structurally the same
// as RDF.Entailment.Simple.try_match / try_alts (same lexicographic
// measure %[remaining consequent triples; remaining candidates]); only the
// candidate type changes.
let rec try_match_g (leq : bool -> literal -> literal -> bool) (bnd : rdf_term -> bool)
                    (bs : list triple) (b : binding) (a : list gtriple)
  : Tot bool (decreases %[length bs; 1 + length a]) =
  match bs with
  | [] -> true
  | tb :: rest -> try_alts_g leq bnd bs tb rest b a a
and try_alts_g (leq : bool -> literal -> literal -> bool) (bnd : rdf_term -> bool)
               (bs : list triple) (tb : triple)
               (rest : list triple { length rest < length bs }) (b : binding)
               (a : list gtriple) (cand : list gtriple)
  : Tot bool (decreases %[length bs; length cand]) =
  match cand with
  | [] -> false
  | ta :: more ->
    (match match_gtriple leq bnd b tb ta with
     | Some b1 -> if try_match_g leq bnd rest b1 a then true
                  else try_alts_g leq bnd bs tb rest b a more
     | None    -> try_alts_g leq bnd bs tb rest b a more)

let entails_g (leq : bool -> literal -> literal -> bool) (bnd : rdf_term -> bool)
              (a : list gtriple) (b : list triple) : bool =
  try_match_g leq bnd b [] a

// ---- RDF 1.2 semantic condition: triple terms denote propositions ------

// Every triple term OCCURRING in the graph, including nested ones. RDF 1.2
// admits a triple term only in object position, so the scan starts at the
// object and recurses through the triple term's own object.
let rec tt_occurrences (t : rdf_term) : Tot (list rdf_term) (decreases t) =
  match t with
  | T_TripleTerm _ _ o -> t :: tt_occurrences o
  | _                  -> []

let graph_tt_occurrences (ts : list triple) : list rdf_term =
  collect (fun (t : triple) -> tt_occurrences t.o) ts

// RDF 1.2 Semantics: a triple term denotes a proposition, so every triple
// term occurring in the graph is an instance of rdfs:Proposition. This is
// the semantic condition the `rdf:reifies` RANGE axiom is a corollary of;
// `rdf12_reifies_closure` above covers the range corollary for IRI /
// blank-node reified objects, and this covers the triple terms themselves,
// which are not expressible as `triple` subjects.
let proposition_gtriples (ts : list triple) : list gtriple =
  map (fun (tt : rdf_term) ->
         { gs = tt; gp = rdf_type_iri; go = T_IRI rdfs_proposition_iri })
      (graph_tt_occurrences ts)


// ---- RDF 1.2 semantic condition: literals denote datatype instances ----

// The datatypes this engine RECOGNIZES: exactly the ones
// XSD.Datatypes.literal_ill_formed decides well-formedness for. For any
// other datatype IRI, `literal_ill_formed` answers false for every lexical
// form, which is the correct answer for an UNrecognized datatype (nothing
// is known to be ill-formed) but is not a licence to assert a type.
let is_recognized_datatype (dt : wf_iri) : bool =
  dt = xsd_boolean || dt = xsd_dateTime || dt = xsd_float || dt = xsd_double ||
  is_decimal_derived_datatype dt

// RDF 1.2 Semantics, D-interpretation condition: a well-formed literal with
// a recognized datatype d denotes a value in the value space of d, so it is
// an instance of d. Emitted only for literals in ASSERTED object position,
// not for literals inside a triple term: a triple term does not assert its
// component triple, so no type assertion about its object is licensed.
let literal_type_gtriples (ts : list triple) : list gtriple =
  collect (fun (t : triple) ->
    match t.o with
    | T_Literal l ->
      if is_recognized_datatype l.datatype
         && not (literal_ill_formed l.datatype l.lexical_form)
      then [ ({ gs = T_Literal l; gp = rdf_type_iri; go = T_IRI l.datatype } <: gtriple) ]
      else []
    | _ -> []) ts

// The "RDF" regime antecedent, generalized: the graph itself plus the
// datatype-instance assertions and the triple-term proposition assertions.
// (Triple terms denote propositions under every regime that recognizes the
// RDF 1.2 vocabulary; the RDFS regime adds the RDFS rule driver on top.)
let rdf_regime_gclosure (ts : list triple) : list gtriple =
  map gtriple_of_triple ts @ literal_type_gtriples ts @ proposition_gtriples ts

// ---- RDFS rules over the generalized layer ------------------------------
//
// RDFS.Closure works on `triple`, so the two RDFS rules whose CONCLUSION
// can be about a triple term or a literal are unreachable to it:
//   rdfs3  `s p o` with `p rdfs:range D` gives `o rdf:type D` -- and `o`
//          may be a triple term or a literal;
//   rdfs9  `x rdf:type c` with `c rdfs:subClassOf d` gives `x rdf:type d`
//          -- and `x` is a triple term for every proposition assertion,
//          or a literal for every datatype-instance assertion.
// Both are applied here, over gtriples, against the already-closed
// antecedent.

// Objects of `c rdfs:subClassOf ?d` in the closed antecedent. rdfs11
// (subClassOf transitivity) has already run inside `rdfs_regime_closure`,
// so this one lookup returns every superclass, not just the direct ones.
let subclass_targets (closed : list triple) (c : wf_iri) : list wf_iri =
  collect (fun (t : triple) ->
    if t.p = RDFS.Closure.rdfs_subClassOf then
      (match t.s, t.o with
       | S_IRI a, T_IRI b -> if a = c then [b] else []
       | _, _             -> [])
    else []) closed

// rdfs9 over gtriples: for every `x rdf:type c` at the generalized layer,
// add `x rdf:type d` for every superclass d of c.
let rdfs9_over_gtriples (closed : list triple) (gts : list gtriple) : list gtriple =
  collect (fun (g : gtriple) ->
    if g.gp = rdf_type_iri then
      (match g.go with
       | T_IRI c -> map (fun (d : wf_iri) -> ({ gs = g.gs; gp = rdf_type_iri; go = T_IRI d } <: gtriple))
                        (subclass_targets closed c)
       | _       -> [])
    else []) gts

// Objects of `p rdfs:range ?d` in the closed antecedent.
let range_targets (closed : list triple) (p : wf_iri) : list wf_iri =
  collect (fun (t : triple) ->
    if t.p = RDFS.Closure.rdfs_range then
      (match t.s, t.o with
       | S_IRI a, T_IRI b -> if a = p then [b] else []
       | _, _             -> [])
    else []) closed

// rdfs3 for the objects RDFS.Closure cannot type: triple terms and
// literals. IRI and blank-node objects are already handled inside the
// fixed point, so they are skipped here rather than duplicated.
let rdfs3_over_gtriples (closed : list triple) : list gtriple =
  collect (fun (t : triple) ->
    match t.o with
    | T_TripleTerm _ _ _ | T_Literal _ ->
      map (fun (d : wf_iri) -> ({ gs = t.o; gp = rdf_type_iri; go = T_IRI d } <: gtriple))
          (range_targets closed t.p)
    | _ -> []) closed

// The RDFS-regime antecedent, generalized: the ordinary RDFS closure
// embedded as gtriples, plus the RDF 1.2 semantic conditions, plus one
// pass of rdfs3 and rdfs9 over the generalized layer.
//
// One pass of rdfs9 is enough for the class hierarchy, because rdfs11 ran
// to its fixed point inside `rdfs_regime_closure`, so `subclass_targets`
// already returns the transitive superclasses. What one pass does NOT
// reach is a class derived from a generalized type assertion by a rule
// other than rdfs9 -- there is no such rule in the RDFS rule set whose
// premise can be a generalized triple, so this is a completeness statement
// about the RDFS rules, not an admission about them.
let rdfs_regime_gclosure (ts : list triple) : list gtriple =
  let closed = rdfs_regime_closure ts in
  let base = rdf_regime_gclosure closed @ rdfs3_over_gtriples closed in
  base @ rdfs9_over_gtriples closed base

// ---- RDF 1.2 D-inconsistency -------------------------------------------

// A literal that is ill-formed for its (recognized) datatype denotes
// nothing, so a graph asserting one has no model: it is D-inconsistent and
// D-entails every graph. RDF 1.2 Semantics keeps this true for a malformed
// literal sitting INSIDE a triple term (the `malformed-literal` fixture --
// "Malformed literals are allowed in triple terms, but cause
// inconsistency"), so the scan recurses into triple-term objects.
//
// This is a SEPARATE predicate, deliberately NOT folded into `entails_rdf`.
// The vendored suite grades `malformed-literal-bnode-neg` and
// `malformed-literal-no-spurious` as NegativeEntailmentTests over the same
// inconsistent graph; making `entails_rdf` return true for everything on
// an inconsistent antecedent would make those two contradictory. The
// suite's `mf:result false` entries are the ones that ask about
// inconsistency, and only those consult this function.
let rec term_ill_formed (t : rdf_term) : Tot bool (decreases t) =
  match t with
  | T_Literal l        -> literal_ill_formed l.datatype l.lexical_form
  | T_TripleTerm _ _ o -> term_ill_formed o
  | _                  -> false

let rdf_inconsistent (ts : list triple) : bool =
  existsb (fun (t : triple) -> term_ill_formed t.o) ts

// ---- Regime entrypoints ------------------------------------------------

// RDF (D-)entailment: recognized-datatype value equality (position-aware)
// + no blank-node ranging over malformed literals.
let entails_rdf (a b : list triple) : bool =
  entails_g dt_value_leq bnd_rdf (rdf_regime_gclosure a) b

// RDFS entailment: + the RDFS rule driver (rdfs2/3/5/7/9/11 + the
// container-membership slice) + the RDF 1.2 reifies-range step.
let entails_rdfs (a b : list triple) : bool =
  entails_g dt_value_leq bnd_rdf (rdfs_regime_gclosure a) b

// RDFS-Plus entailment: the RDFS-regime closure + owl:sameAs (IRI
// transparency, including inside triple terms).
let entails_rdfs_plus (a b : list triple) : bool =
  let closed = owl_closure (rdfs_regime_closure a) in
  entails_g dt_value_leq bnd_rdf (rdf_regime_gclosure closed) b
