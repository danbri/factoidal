module RDF.Term

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.1/§3.3 step 5. This is the tree's THIRD `.fsti` (after
// RDF.Vocabulary and RDF.Indexed) and the first written for a human
// reader before a compiler: one RDF concept per block, a one-line
// prose definition citing RDF 1.1 Concepts (https://www.w3.org/TR/
// rdf11-concepts/) §3, then the F* type or function that realizes it.
// If you know RDF but not F*, skim the `///` comments top to bottom
// and skip the code.
//
// Every declaration below is a *transparent* `let`/`type` (not an
// abstract `val`), same discipline as RDF.Vocabulary.fsti and
// RDF.Indexed.fsti: 53+ modules pattern-match directly on `T_IRI`/
// `S_IRI`/etc., and per §1.6 of the design doc, plain transparent
// variants are also what extracts cleanest to C via KaRaMeL. Hiding
// these behind a signature would force every call site through
// accessor functions for no correctness gain (design doc §2.9, Open
// decision 3) — revisit only if a genuine abstraction need appears.
//
// This is a copy-move from RDF.Graph.Executable.fst lines 1-159 (plus
// the xsd:*/rdf:langString term-algebra constants at lines 36-50,
// which RDF.Vocabulary.fsti's own banner already earmarks for "the
// future RDF.Term module" rather than the RDFS/OWL vocabulary table)
// — no new proof obligations, no behavior change.
//
// Deliberately NOT here (still assigned elsewhere, so a reader isn't
// left wondering where they went):
//   - `datatype_value_eq` (XSD value-space equality) and the two
//     lexical-normalization helpers it depends on — `XSD.Datatypes.fst`'s
//     job per docs/designissues/2026-07-05-xsd-datatypes-module.md
//     §Migration order item 1.
//   - `add_triple_if_new`/`add_triple_unchecked` and every other graph
//     operation (`graph_add`, `graph_remove`, `find_by_subject`, the
//     `rename_*_bnodes` family, `graph_bnodes`) — those stay in
//     `RDF.Graph.Executable.fst` for now. This slice moves only the
//     type tier + its decidable-equality/reflexivity lemmas (design
//     doc §2.1's literal scope); the remaining accessor/algorithm
//     functions are a candidate for a later, separately-gated slice,
//     same "narrower-than-planned, ship what's achievable" call step 3
//     made for `RDF.Indexed`.
//   - The `indexed_graph`/bucket-map acceleration structure
//     (`RDF.Indexed.fst`) and the RDFS/OWL-RL closure rules
//     (`RDFS.Closure`/`OWL.Closure`, design doc step 6) — both still
//     consume these types via `RDF.Graph.Executable.fst`'s shim.

open FStar.String

(** ------------------------------------------------------------------ *)
(** Blank nodes — RDF 1.1 Concepts §3.4                                *)
(** ------------------------------------------------------------------ *)

/// A blank node is a locally-scoped identifier, disjoint from IRIs and
/// literals, denoting some resource without naming it globally. We
/// represent its label as a plain string so it extracts as a simple
/// value with no allocation overhead.
type bnode_id = string

(** ------------------------------------------------------------------ *)
(** IRIs — RDF 1.1 Concepts §3.2                                       *)
(** ------------------------------------------------------------------ *)

/// An IRI (RFC 3987) identifies a resource. Represented as a plain
/// string; `wf_iri` below refines it to the subset this tree treats
/// as syntactically well-formed.
type iri = string

/// Direct indexed traversal (not an intermediate char list) checking
/// for a `:` — the one syntactic property this tree's cheap `is_iri`
/// check demands of every IRI (full RFC 3987 grammar conformance is
/// `RDF.IRI.fst`'s job; this is the fast, total, structural gate every
/// term constructor runs).
let rec string_has_colon_from (s: string) (pos: nat) (fuel: nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    let len = String.length s in
    if pos >= len then false
    else if FStar.Char.int_of_char (String.index s pos) = 0x3A then true
    else string_has_colon_from s (pos + 1) (fuel - 1)

let string_contains_colon (s : string) : bool =
  string_has_colon_from s 0 (String.length s + 1)

/// The well-formedness predicate `wf_iri` below refines against:
/// non-empty and contains a colon (the minimal syntactic bar an IRI
/// must clear before RFC 3987 resolution logic ever sees it).
let is_iri (s : string) : bool =
  String.length s > 0 && string_contains_colon s

/// A well-formed IRI — the type every term constructor and predicate
/// position actually requires.
type wf_iri = s:iri{is_iri s}

/// `rdf:langString` — the fixed datatype IRI RDF 1.1 assigns to every
/// language-tagged literal (RDF 1.1 Concepts §3.3).
let rdf_lang_string : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"

/// `xsd:string` — the datatype every plain (un-language-tagged, not
/// explicitly typed) literal carries per RDF 1.1's abstract syntax.
/// Part of the term algebra (literal construction), not the RDFS/OWL
/// vocabulary table — see RDF.Vocabulary.fsti's banner for why these
/// five XSD constants live here instead of there.
let xsd_string : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#string");
  "http://www.w3.org/2001/XMLSchema#string"

/// `xsd:integer` — used to type unsuffixed integer literals wherever
/// this tree constructs them directly (SPARQL numeric literals, XSD
/// value-space code).
let xsd_integer : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#integer");
  "http://www.w3.org/2001/XMLSchema#integer"

/// `xsd:decimal`.
let xsd_decimal : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#decimal");
  "http://www.w3.org/2001/XMLSchema#decimal"

/// `xsd:double`.
let xsd_double : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#double");
  "http://www.w3.org/2001/XMLSchema#double"

/// `xsd:boolean`.
let xsd_boolean : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#boolean");
  "http://www.w3.org/2001/XMLSchema#boolean"

(** ------------------------------------------------------------------ *)
(** Literals — RDF 1.1 Concepts §3.3                                   *)
(** ------------------------------------------------------------------ *)

/// A literal is a lexical form plus a datatype IRI, and — only when
/// the datatype is `rdf:langString` — a language tag. This record
/// carries all three fields unconditionally; `literal_wf` below is
/// the well-formedness predicate RDF 1.1 actually imposes on the
/// combination (langString iff a language tag is present).
noeq type literal = {
  lexical_form : string;
  datatype     : wf_iri;
  lang_tag     : option string;
}

/// RDF 1.1's rule: a literal has a language tag if and only if its
/// datatype is `rdf:langString`. Every literal this tree constructs
/// must satisfy this before it is treated as a term.
let literal_wf (l:literal) : bool =
  match l.lang_tag with
  | None   -> l.datatype <> rdf_lang_string
  | Some _ -> l.datatype = rdf_lang_string

/// A well-formed literal — the type `rdf_term`'s `T_Literal` case
/// actually carries.
type wf_literal = l:literal{literal_wf l}

(** ------------------------------------------------------------------ *)
(** RDF terms — RDF 1.1 Concepts §3 (IRI / literal / blank node)       *)
(** ------------------------------------------------------------------ *)

/// An RDF term is exactly one of: an IRI, a blank node, or a literal —
/// the three disjoint term kinds RDF 1.1 recognizes. `rdf_term` is
/// what appears in object position of a triple; `subject` below is
/// the strictly smaller set (no literal) that appears in subject
/// position.
noeq type rdf_term =
  | T_IRI     : wf_iri -> rdf_term
  | T_BNode   : bnode_id -> rdf_term
  | T_Literal : wf_literal -> rdf_term

/// A triple's subject (RDF 1.1 Concepts §3.1: "the subject ... is
/// either an IRI or a blank node" — never a literal).
noeq type subject =
  | S_IRI : wf_iri -> subject
  | S_BNode : bnode_id -> subject

(** ------------------------------------------------------------------ *)
(** Decidable equality + reflexivity                                   *)
(** ------------------------------------------------------------------ *)

/// Structural equality on subjects: same constructor, same underlying
/// string. Both `wf_iri` and `bnode_id` are plain `string` (an
/// `eqtype`), so this is a straight pattern match.
let subject_eq (s1 s2 : subject) : bool =
  match s1, s2 with
  | S_IRI i1, S_IRI i2 -> i1 = i2
  | S_BNode b1, S_BNode b2 -> b1 = b2
  | _, _ -> false

/// Case-insensitive language-tag comparison (RDF 1.1 Concepts §3.3:
/// `@en-US` and `@en-us` denote the same tag).
let lang_tag_eq (t1 t2 : string) : bool =
  String.lowercase t1 = String.lowercase t2

let lang_tag_option_eq (t1 t2 : option string) : bool =
  match t1, t2 with
  | None, None -> true
  | Some s1, Some s2 -> lang_tag_eq s1 s2
  | _, _ -> false

/// Structural equality on literals: lexical form and datatype compare
/// exactly; the language tag (if any) compares case-insensitively.
let literal_eq (l1 l2 : literal) : bool =
  l1.lexical_form = l2.lexical_form &&
  l1.datatype = l2.datatype &&
  lang_tag_option_eq l1.lang_tag l2.lang_tag

/// Structural equality on RDF terms.
let rdf_term_eq (t1 t2 : rdf_term) : bool =
  match t1, t2 with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode b1, T_BNode b2 -> b1 = b2
  | T_Literal l1, T_Literal l2 -> literal_eq l1 l2
  | _, _ -> false

/// RDF 1.1 *value* equality for literals (distinct from `literal_eq`'s
/// structural equality): a plain literal `"foo"` and `"foo"^^xsd:string`
/// are the same value, because RDF 1.1's abstract syntax already
/// assigns `xsd:string` to plain literals — so both sides of this
/// comparison already carry `xsd:string` as their datatype in a
/// well-formed representation, and comparing datatypes directly is
/// sufficient.
let literal_value_eq (l1 l2 : literal) : bool =
  l1.lexical_form = l2.lexical_form &&
  lang_tag_option_eq l1.lang_tag l2.lang_tag &&
  l1.datatype = l2.datatype

/// `subject_eq` is reflexive.
let lemma_subject_eq_refl (s : subject) : Lemma (subject_eq s s = true) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

/// `literal_eq` is reflexive.
let lemma_literal_eq_refl (l : literal) : Lemma (literal_eq l l = true) = ()

/// `rdf_term_eq` is reflexive.
let lemma_rdf_term_eq_refl (t : rdf_term) : Lemma (rdf_term_eq t t = true) =
  match t with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal l -> lemma_literal_eq_refl l
