module RDF.Entailment.RDFS.DatatypeClash

// ===================================================================
// D-INCONSISTENCY DETECTION under RDFS D-entailment — issue #333.
//
// BASELINE: RDF 1.1 Semantics, W3C Recommendation 25 February 2014
// (https://www.w3.org/TR/rdf11-mt/) section 7 ("Datatyped
// interpretations") and section 9 ("RDFS interpretations"): a
// datatype map D fixes, for every recognized datatype IRI, a value
// space and a lexical-to-value mapping. A D-interpretation is
// D-INCONSISTENT (has no model) when the graph forces a term into two
// incompatible positions in that scheme — the two shapes this module
// decides:
//
//   (a) ILL-FORMED LITERAL. A literal typed with a recognized
//       datatype whose lexical form is not in that datatype's lexical
//       space denotes nothing (RDF 1.1 Semantics section 7, "if E is
//       not in the lexical space of a recognized datatype ... every
//       triple containing lit is false"; the rdf-mt test suite's own
//       framing: an implementation "configured to recognize" a
//       datatype must treat a badly-formed literal of that datatype
//       as a contradiction, not silently pass it through). Gated on
//       the RECOGNIZED-datatypes list the test supplies (`mf:
//       recognizedDatatypes` / the caller's configuration) — an
//       unrecognized datatype's lexical form is not checked, per the
//       W3C rdf-mt README: "for tests that have false as output,
//       [pass if] configured to recognize all the datatypes in the
//       list of recognized datatypes."
//
//   (b) RANGE / TYPE CLASH. rdfs3 ("aaa rdfs:range xxx . yyy aaa zzz
//       . |= zzz rdf:type xxx .", RDF.Entailment.RDFS.Spec.fst)
//       forces every object of a range-restricted property into the
//       range class's extension. When the range class IS a
//       recognized datatype IRI `C` and the object is ITSELF a
//       literal already typed with a DIFFERENT datatype `D <> C`,
//       rdfs3 demands membership in C's value space while the
//       literal's own typing fixes it in D's — RDF 1.1 Semantics
//       section 7 keeps every recognized datatype's value space
//       disjoint from any literal not of that datatype (a plain /
//       xsd:string-typed literal like "25" is not a member of
//       xsd:integer's value space merely because a range assertion
//       says it must be), so the two demands contradict.
//
// Deliberately NOT covered here (an acknowledged gap, not a silent
// hole — see the module-level note at `rdfs_d_inconsistent` below):
// rdf:XMLLiteral well-formedness (rdf-mt's rdfs-entailment-test001).
// RDF 1.1 section 5.1 makes XMLLiteral support optional ("no longer
// mandatory" per that test's own comment) and this tree has no
// general "is this string well-formed XML content" checker —
// XML.Wellformedness.fst covers only the RDF/XML *parser's*
// structural rules (NCName validity, attribute conflicts), not
// arbitrary XMLLiteral lexical well-formedness.
//
// Consumer: bin/w3c-runner/w3c_runner.ml's PositiveEntailmentTest /
// NegativeEntailmentTest dispatch (rule #15 boundary — the runner
// only calls `rdfs_d_inconsistent`, decides nothing itself).
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Vocabulary.Axioms
open XSD.Datatypes

/// Membership on `wf_iri` lists, spelled explicitly (mirrors
/// `XML.Wellformedness.mem_string`'s rationale: structural-equality
/// membership on `string`-like types rather than leaning on
/// `List.Tot.mem`'s eqtype inference).
let rec mem_wf_iri (x : wf_iri) (xs : list wf_iri) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | y :: rest -> if x = y then true else mem_wf_iri x rest

// -------------------------------------------------------------------
// (a) Ill-formed literal under a recognized datatype.
// -------------------------------------------------------------------

/// True iff some triple in `g` has a literal object typed with a
/// datatype in `recognized` whose lexical form
/// `XSD.Datatypes.literal_ill_formed` rejects. Reuses that function
/// verbatim (not re-derived) — it already carries the whitespace-
/// strict xsd:integer/xsd:int lexical grammar the xmlsch-02
/// whitespace-facet tests need (XSD.Datatypes.fst's
/// `is_signed_digits_chars` admits no non-digit character, including
/// leading/trailing space, unlike full XSD's whitespace-collapse
/// preprocessing — exactly the distinction those tests probe).
let rec has_ill_formed_recognized_literal (g : rdf_graph) (recognized : list wf_iri)
  : Tot bool (decreases g) =
  match g with
  | [] -> false
  | t :: rest ->
    (match t.o with
     | T_Literal l ->
       if mem_wf_iri l.datatype recognized && literal_ill_formed l.datatype l.lexical_form
       then true
       else has_ill_formed_recognized_literal rest recognized
     | _ -> has_ill_formed_recognized_literal rest recognized)

// -------------------------------------------------------------------
// (b) Range / datatype clash.
// -------------------------------------------------------------------

/// Does `g` contain a triple `_ p_described o` whose object is a
/// literal typed with a datatype other than `c`? Walks the WHOLE
/// graph `g` (not a shrinking suffix) because it is invoked once per
/// candidate `rdfs:range` triple found by the caller below, each time
/// needing to see every triple again.
let rec exists_range_literal_mismatch (g : rdf_graph) (p_described c : wf_iri)
  : Tot bool (decreases g) =
  match g with
  | [] -> false
  | t :: rest ->
    if t.p = p_described then
      (match t.o with
       | T_Literal l ->
         if l.datatype <> c then true
         else exists_range_literal_mismatch rest p_described c
       | _ -> exists_range_literal_mismatch rest p_described c)
    else exists_range_literal_mismatch rest p_described c

/// True iff `g` contains an `rdfs:range` declaration onto a recognized
/// datatype IRI whose described property is used with a literal typed
/// with a DIFFERENT datatype. Gated on `C` (the range's target) being
/// recognized only — the literal's own datatype need not independently
/// be in `recognized` (rdf-mt's datatypes-test010 declares only
/// `xsd:integer` recognized; its plain-literal object types as
/// `xsd:string` per RDF 1.1's abstract syntax, which is not itself
/// listed, and the clash still holds: the fact being decided is
/// membership in `C`'s value space, and `C` IS recognized).
///
/// `full` is the WHOLE graph, threaded unchanged through the
/// recursion so `exists_range_literal_mismatch` always searches every
/// triple regardless of how deep the scan over `remaining` has gone —
/// searching `remaining` instead (the shrinking recursion suffix)
/// would silently miss a clash whenever the matching literal triple
/// sorts BEFORE the `rdfs:range` declaration in `g`, which is exactly
/// rdf-mt's datatypes-range-clash / datatypes-test010 fixture order.
/// Caught by this module's own vacuity-guard `assert_norm`s below
/// (`clash_action_range`/`clash_action_range_plain` failed to verify
/// against an earlier single-parameter version of this function).
let rec has_range_datatype_clash_aux (full remaining : rdf_graph) (recognized : list wf_iri)
  : Tot bool (decreases remaining) =
  match remaining with
  | [] -> false
  | t :: rest ->
    if t.p = i_rdfs_range then
      (match t.s, t.o with
       | S_IRI p_described, T_IRI c ->
         if mem_wf_iri c recognized && exists_range_literal_mismatch full p_described c
         then true
         else has_range_datatype_clash_aux full rest recognized
       | _, _ -> has_range_datatype_clash_aux full rest recognized)
    else has_range_datatype_clash_aux full rest recognized

let has_range_datatype_clash (g : rdf_graph) (recognized : list wf_iri) : bool =
  has_range_datatype_clash_aux g g recognized

// -------------------------------------------------------------------
// Top-level detector.
// -------------------------------------------------------------------

/// D-inconsistency under RDFS D-entailment, restricted to the two
/// decidable shapes (a)/(b) above. Conservative by construction, same
/// promise as `XSD.Datatypes.literal_ill_formed`'s banner: this can
/// only ADD clashes the RDF 1.1 Semantics requires, never invent ones
/// it doesn't — an unrecognized datatype is never checked (rule (a)'s
/// gate), and rule (b) only fires where rdfs3's premise triple is
/// actually present in `g`. NOT a complete D-inconsistency decision
/// procedure: rdf:XMLLiteral ill-formedness is out of scope (see the
/// file banner) — a graph whose only inconsistency is a malformed
/// XMLLiteral will be (correctly, not silently) reported as "not
/// proven inconsistent" by this predicate, which the caller must not
/// paper over as a Pass.
let rdfs_d_inconsistent (g : rdf_graph) (recognized : list wf_iri) : bool =
  has_ill_formed_recognized_literal g recognized ||
  has_range_datatype_clash g recognized

// ===================================================================
// VACUITY GUARD — issue #333's own requirement (measuring-inference
// skill rule 3: "a negative test passes for free when the engine
// derives nothing"). These are machine-checked at F* verification
// time via `assert_norm`, not merely asserted in prose: if the
// detector degenerated to "always true" or "always false" these
// `assert_norm`s would fail to typecheck and `make verify` would
// reject the module.
// ===================================================================

// The witnesses below reduce a hand-recursive boolean function over
// concrete small lists to a literal true/false via `assert_norm`; the
// default fuel/ifuel assert_norm affords is too low to unfold that
// recursion fully (observed: "incomplete quantifiers" at default
// rlimit=5). Raised locally, popped at the section's end — this does
// not affect any other module's verification budget.
#push-options "--fuel 20 --ifuel 20 --z3rlimit 200"

private let wex_foo : wf_iri = assert_norm (is_iri "http://example.org/foo"); "http://example.org/foo"
private let wex_bar : wf_iri = assert_norm (is_iri "http://example.org/bar"); "http://example.org/bar"

private let lit_flargh_integer : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "flargh"; datatype = xsd_integer; lang_tag = None; direction = None }));
  { lexical_form = "flargh"; datatype = xsd_integer; lang_tag = None; direction = None }

private let lit_25_integer : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "25"; datatype = xsd_integer; lang_tag = None; direction = None }));
  { lexical_form = "25"; datatype = xsd_integer; lang_tag = None; direction = None }

private let lit_25_string : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "25"; datatype = xsd_string; lang_tag = None; direction = None }));
  { lexical_form = "25"; datatype = xsd_string; lang_tag = None; direction = None }

/// POSITIVE control 1 (mirrors rdf-mt datatypes-non-well-formed-literal-2):
/// "flargh"^^xsd:integer, xsd:integer recognized -> the detector MUST fire.
private let clash_action_ill_formed : rdf_graph =
  [ { s = S_IRI wex_foo; p = wex_bar; o = T_Literal lit_flargh_integer } ]

let _ = assert_norm (rdfs_d_inconsistent clash_action_ill_formed [xsd_integer] = true)

/// NEGATIVE control 1 (mirrors rdf-mt datatypes-non-well-formed-literal-1):
/// the SAME ill-formed literal, but xsd:integer is NOT in the recognized
/// list -> the detector must NOT fire. Proves rule (a)'s gate is load-
/// bearing, not decorative.
let _ = assert_norm (rdfs_d_inconsistent clash_action_ill_formed [] = false)

/// NEGATIVE control 2 (the "not trivially true" witness the task
/// requires): a WELL-FORMED xsd:integer literal, recognized, no range
/// triple at all -> the detector must NOT fire. If rule (a) or (b)
/// degenerated to "always true," this assert_norm would fail to verify.
private let consistent_action_well_formed : rdf_graph =
  [ { s = S_IRI wex_foo; p = wex_bar; o = T_Literal lit_25_integer } ]

let _ = assert_norm (rdfs_d_inconsistent consistent_action_well_formed [xsd_integer] = false)

/// POSITIVE control 2 (mirrors rdf-mt datatypes-range-clash): xsd:integer
/// value on a property range-restricted to xsd:string, both recognized
/// -> the detector MUST fire.
private let clash_action_range : rdf_graph =
  [ { s = S_IRI wex_foo; p = wex_bar; o = T_Literal lit_25_integer };
    { s = S_IRI wex_bar; p = i_rdfs_range; o = T_IRI xsd_string } ]

let _ = assert_norm (rdfs_d_inconsistent clash_action_range [xsd_integer; xsd_string] = true)

/// NEGATIVE control 3: the property's range MATCHES the literal's own
/// datatype (both xsd:integer) -> no clash, even with the rdfs:range
/// triple present and both recognized. Proves rule (b) checks the
/// actual datatype disagreement, not merely "a range triple exists."
private let consistent_action_range_matches : rdf_graph =
  [ { s = S_IRI wex_foo; p = wex_bar; o = T_Literal lit_25_integer };
    { s = S_IRI wex_bar; p = i_rdfs_range; o = T_IRI xsd_integer } ]

let _ = assert_norm (rdfs_d_inconsistent consistent_action_range_matches [xsd_integer] = false)

/// NEGATIVE control 4: the range triple is present and mismatched, but
/// its target datatype is NOT recognized -> no clash. Proves rule (b)'s
/// gate (on `C`, the range target) is load-bearing too.
let _ = assert_norm (rdfs_d_inconsistent clash_action_range [] = false)

/// NEGATIVE control 5 (mirrors rdf-mt datatypes-intensional-xsd-integer-
/// decimal-compatible): a subClassOf assertion BETWEEN two datatype
/// IRIs is not an rdfs:range triple at all, so it can never trip rule
/// (b) — no literal is even present.
private let ex_datatype_subclassof : rdf_graph =
  [ { s = S_IRI xsd_integer; p = i_rdfs_subClassOf; o = T_IRI xsd_decimal } ]

let _ = assert_norm (rdfs_d_inconsistent ex_datatype_subclassof [xsd_integer; xsd_decimal] = false)

/// POSITIVE control 3 (mirrors rdf-mt datatypes-test010 exactly): a
/// PLAIN literal — which this tree's N-Triples parser types as
/// xsd:string per RDF 1.1's abstract syntax, see
/// `Parser.NTriples.fst` — on a property range-restricted to
/// xsd:integer, with ONLY xsd:integer (not xsd:string) recognized ->
/// the detector MUST fire. Proves rule (b)'s gate is on `C` alone, as
/// documented above, not on both sides of the mismatch.
private let clash_action_range_plain : rdf_graph =
  [ { s = S_IRI wex_foo; p = wex_bar; o = T_Literal lit_25_string };
    { s = S_IRI wex_bar; p = i_rdfs_range; o = T_IRI xsd_integer } ]

let _ = assert_norm (rdfs_d_inconsistent clash_action_range_plain [xsd_integer] = true)

#pop-options
