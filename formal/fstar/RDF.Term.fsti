module RDF.Term

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.1/§3.3 step 5; restructured 2026-07-05 per the owner's
// reading-order critique — see skills/fstar-module-style/SKILL.md's
// ".fsti reading-order convention". Full history/exclusion-list in
// RDF.Term.fst's banner.
// If you know RDF but not F*: skim the `///` comments; concepts run
// uninterrupted from "Blank nodes" to the "Appendix" divider below.

open FStar.String

(** ------------------------------------------------------------------ *)
(** Preamble: IRI well-formedness machinery (mechanical — skip on      *)
(** first read; concepts start at "Blank nodes" below). This has to    *)
(** sit here, not in the Appendix, because `wf_iri`'s refinement       *)
(** needs `is_iri` already declared — F* transparent `let`s can't      *)
(** forward-reference (fstar-module-style skill, reading-order note).  *)
(** ------------------------------------------------------------------ *)

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

(** ==================================================================== *)
(** Concepts — read top to bottom, uninterrupted, to the Appendix.       *)
(** ==================================================================== *)

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
/// as syntactically well-formed, via the preamble's `is_iri` above.
type iri = string

/// A well-formed IRI — the type every term constructor and predicate
/// position actually requires.
type wf_iri = s:iri{is_iri s}

/// `rdf:langString` — the fixed datatype IRI RDF 1.1 assigns to every
/// language-tagged literal (RDF 1.1 Concepts §3.3). Defined here,
/// ahead of its xsd:* siblings in the Appendix, because the Literals
/// concept just below needs it for `literal_wf`.
let rdf_lang_string : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"

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

(** ==================================================================== *)
(** Appendix: mechanical definitions. Nothing below this line is a new  *)
(** RDF concept — xsd:* constant ceremony, structural equality, and     *)
(** reflexivity lemmas for the types declared above.                    *)
(** ==================================================================== *)

(** ------------------------------------------------------------------ *)
(** xsd:* term-algebra constants — the datatypes RDF 1.1's abstract     *)
(** syntax assigns to plain/numeric/boolean literals. Not RDFS/OWL      *)
(** vocabulary — see RDF.Vocabulary.fsti's banner for that boundary.    *)
(** ------------------------------------------------------------------ *)

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
