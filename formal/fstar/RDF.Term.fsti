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

/// `rdf:dirLangString` — RDF 1.2's datatype for a *directional*
/// language-tagged string (RDF 1.2 Concepts §3.3, CR 2026-04-07): a
/// literal carrying a BCP47 language tag AND a base text direction.
/// N-Triples 1.2 lexical form `"..."@en--ltr`. Defined here alongside
/// `rdf:langString` because `literal_wf`'s RDF 1.2 three-way rule below
/// needs it. Adding this datatype breaks the RDF 1.1 invariant "language
/// tag iff rdf:langString" — see `literal_wf`.
let rdf_dir_lang_string : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#dirLangString");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#dirLangString"

(** ------------------------------------------------------------------ *)
(** Base direction — RDF 1.2 Concepts §3.3                             *)
(** ------------------------------------------------------------------ *)

/// The base direction of a directional language-tagged string: either
/// left-to-right or right-to-left (RDF 1.2 Concepts §3.3). An eqtype (a
/// plain two-constructor enum), so `option text_direction` compares with
/// `=` and `literal_eq`/`literal_value_eq` stay total.
type text_direction =
  | Dir_LTR
  | Dir_RTL

(** ------------------------------------------------------------------ *)
(** Literals — RDF 1.1 Concepts §3.3 / RDF 1.2 Concepts §3.3           *)
(** ------------------------------------------------------------------ *)

/// A literal is a lexical form plus a datatype IRI, and — only when the
/// datatype is `rdf:langString` or `rdf:dirLangString` — a language tag,
/// and — only when the datatype is `rdf:dirLangString` — a base
/// direction. This record carries all four fields unconditionally;
/// `literal_wf` below is the well-formedness predicate imposed on the
/// combination.
///
/// RDF 1.2 design (epic #305): `direction` is an *optional field* rather
/// than a new literal kind or a fourth `rdf_term` constructor.  Rationale:
/// (a) an optional field defaults to `None` for every RDF 1.1 literal, so
/// `literal_eq`/`literal_value_eq`/hashing extend by exactly one clause
/// and remain total; (b) a new literal *kind* would duplicate all literal
/// machinery and force a second arm at every match site including
/// wildcard-covered ones; (c) serializers emit the `--dir` suffix only
/// when `direction = Some`, so every RDF 1.1 document round-trips
/// byte-identically.
noeq type literal = {
  lexical_form : string;
  datatype     : wf_iri;
  lang_tag     : option string;
  direction    : option text_direction;
}

/// The well-formedness rule on a literal, extended for RDF 1.2's
/// directional language strings. The RDF 1.1 two-way rule ("language
/// tag iff rdf:langString") becomes a three-way rule:
///   - no lang tag, no direction        <-> datatype is neither
///                                          langString nor dirLangString
///   - lang tag, no direction           <-> datatype is rdf:langString
///   - lang tag AND direction           <-> datatype is rdf:dirLangString
///   - direction without a lang tag      is always ill-formed
/// Every RDF 1.1 literal (direction = None) still satisfies exactly the
/// original rule, so the tightening rejects no pre-1.2 literal.
let literal_wf (l:literal) : bool =
  match l.lang_tag, l.direction with
  | None,   None   -> l.datatype <> rdf_lang_string && l.datatype <> rdf_dir_lang_string
  | Some _, None   -> l.datatype = rdf_lang_string
  | Some _, Some _ -> l.datatype = rdf_dir_lang_string
  | None,   Some _ -> false

/// A well-formed literal — the type `rdf_term`'s `T_Literal` case
/// actually carries.
type wf_literal = l:literal{literal_wf l}

(** ------------------------------------------------------------------ *)
(** RDF terms — RDF 1.1 Concepts §3 / RDF 1.2 Concepts §3              *)
(** ------------------------------------------------------------------ *)

/// A triple's subject (RDF 1.1 Concepts §3.1: "the subject ... is
/// either an IRI or a blank node" — never a literal). Declared ahead of
/// `rdf_term` because RDF 1.2's triple-term constructor names it in the
/// subject slot; `subject` itself is non-recursive.
noeq type subject =
  | S_IRI : wf_iri -> subject
  | S_BNode : bnode_id -> subject

/// An RDF term is one of: an IRI, a blank node, a literal (RDF 1.1
/// Concepts §3), or — added in RDF 1.2 Concepts §3 (CR 2026-04-07) — a
/// *triple term* `<<( s p o )>>`, a triple used as a term. `rdf_term` is
/// what appears in object position of a triple.
///
/// The triple term carries a `subject` (IRI or blank node), a predicate
/// `wf_iri`, and an object `rdf_term`. This mirrors the RDF triple shape
/// and bakes in two RDF 1.2 constraints structurally: a triple term's
/// subject is never a literal (it is a `subject`), and its predicate is
/// always an IRI. Only the object slot is recursive, so termination
/// proofs over `rdf_term` decrease on that sub-term.
///
/// NOTE — object-position-only is a SYNTAX constraint, not a term-model
/// one. The abstract term model here permits a `T_TripleTerm` anywhere an
/// `rdf_term` is accepted; that a triple term may appear only in object
/// position of an asserted triple is enforced by the concrete-syntax
/// parsers (an asserted triple's subject has type `subject`, which has no
/// triple-term constructor, so the constraint holds automatically for the
/// outer triple) — see `Parser.NTriples`.
noeq type rdf_term =
  | T_IRI        : wf_iri -> rdf_term
  | T_BNode      : bnode_id -> rdf_term
  | T_Literal    : wf_literal -> rdf_term
  | T_TripleTerm : subject -> wf_iri -> rdf_term -> rdf_term

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

(** ------------------------------------------------------------------ *)
(** XMLLiteral value equality — RDF 1.1 section 5.1                    *)
(**                                                                    *)
(** RDF 1.1 defines the value space of rdf:XMLLiteral via exclusive    *)
(** canonical XML: two XMLLiterals denote the same value iff their     *)
(** exclusive-c14n forms are equal. Comparing lexical forms as plain   *)
(** strings is UNSOUND for functional-property counting — two          *)
(** whitespace / attribute-order variants of one markup are one value, *)
(** not two (WebOnt-miscellaneous-202: a false clash). The RDF/XML     *)
(** parser's parseType="Literal" serializer already normalises         *)
(** self-closing tags and intra-tag whitespace; the one remaining      *)
(** c14n-insignificant difference it leaves is ATTRIBUTE ORDER (XML    *)
(** infosets treat attributes as an unordered set). This canonicaliser *)
(** sorts the attributes of every start tag and is otherwise verbatim: *)
(**   - text content (incl. whitespace) preserved exactly              *)
(**   - end tags, comments (!), PIs (?) emitted verbatim               *)
(**   - self-closing start tags expand to open+close (same infoset)    *)
(** Only genuinely-insignificant aspects are normalised, so two        *)
(** DISTINCT XMLLiterals never canonicalise equal (no completeness     *)
(** hole in clash detection); equal-value variants do (removes the     *)
(** false clash). Char-list based; totality by structural recursion    *)
(** on list length or an explicit fuel bound.                          *)
(** ------------------------------------------------------------------ *)

/// `rdf:XMLLiteral` — the datatype whose value space is exclusive
/// canonical XML (RDF 1.1 section 5.1).
let rdf_XMLLiteral : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"

let xmlc_is_ws (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  n = 0x20 || n = 0x09 || n = 0x0A || n = 0x0D

/// Lexicographic comparison of two char lists by codepoint.
let rec xmlc_chars_lt (a b : list FStar.Char.char) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> false
  | [], _ :: _ -> true
  | _ :: _, [] -> false
  | x :: xs, y :: ys ->
    let nx = FStar.Char.int_of_char x in
    let ny = FStar.Char.int_of_char y in
    if nx < ny then true
    else if nx > ny then false
    else xmlc_chars_lt xs ys

/// Read a tag/attribute name: up to whitespace, `/`, `=`, or end.
/// Returns (name, remainder-at-delimiter).
let rec xmlc_take_name (cs acc : list FStar.Char.char)
  : Tot (list FStar.Char.char * list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, [])
  | c :: rest ->
    if xmlc_is_ws c || c = '/' || c = '=' then (List.Tot.rev acc, cs)
    else xmlc_take_name rest (c :: acc)

/// Drop leading whitespace.
let rec xmlc_drop_ws (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | c :: rest -> if xmlc_is_ws c then xmlc_drop_ws rest else cs
  | [] -> []

/// Position just past the `=` between an attribute name and its value.
let xmlc_drop_to_value (cs : list FStar.Char.char) : list FStar.Char.char =
  let cs1 = xmlc_drop_ws cs in
  match cs1 with
  | c :: rest -> if c = '=' then xmlc_drop_ws rest else cs1
  | [] -> cs1

/// Read chars up to (and consuming) the closing quote `q`.
let rec xmlc_take_until (q : FStar.Char.char) (cs acc : list FStar.Char.char)
  : Tot (list FStar.Char.char * list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, [])
  | c :: rest -> if c = q then (List.Tot.rev acc, rest)
                 else xmlc_take_until q rest (c :: acc)

/// Read one quoted attribute value; returns (value, remainder).
let xmlc_take_quoted (cs : list FStar.Char.char)
  : (list FStar.Char.char * list FStar.Char.char) =
  match cs with
  | c :: rest -> if c = '"' || c = '\'' then xmlc_take_until c rest []
                 else ([], cs)
  | [] -> ([], [])

/// Parse a start tag's attributes into (name, value) pairs, reporting
/// whether the tag self-closes (`/>`). Fuel-bounded.
let rec xmlc_parse_attrs (fuel : nat) (cs : list FStar.Char.char)
                          (acc : list (list FStar.Char.char * list FStar.Char.char))
  : Tot (list (list FStar.Char.char * list FStar.Char.char) * bool)
        (decreases fuel) =
  if fuel = 0 then (List.Tot.rev acc, false)
  else match cs with
    | [] -> (List.Tot.rev acc, false)
    | c :: rest ->
      if xmlc_is_ws c then xmlc_parse_attrs (fuel - 1) rest acc
      else if c = '/' then (List.Tot.rev acc, true)
      else
        let (nm, r1) = xmlc_take_name cs [] in
        let r2 = xmlc_drop_to_value r1 in
        let (v, r3) = xmlc_take_quoted r2 in
        xmlc_parse_attrs (fuel - 1) r3 ((nm, v) :: acc)

/// Insertion sort of attribute pairs by name (codepoint lexicographic).
let rec xmlc_insert_attr (p : (list FStar.Char.char * list FStar.Char.char))
                          (xs : list (list FStar.Char.char * list FStar.Char.char))
  : Tot (list (list FStar.Char.char * list FStar.Char.char)) (decreases xs) =
  match xs with
  | [] -> [p]
  | q :: rest ->
    if xmlc_chars_lt (fst p) (fst q) then p :: xs
    else q :: xmlc_insert_attr p rest

let rec xmlc_sort_attrs (xs : list (list FStar.Char.char * list FStar.Char.char))
  : Tot (list (list FStar.Char.char * list FStar.Char.char)) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> xmlc_insert_attr x (xmlc_sort_attrs rest)

/// Render sorted attributes as ` name="value"` fragments.
let rec xmlc_render_attrs (xs : list (list FStar.Char.char * list FStar.Char.char))
  : Tot (list FStar.Char.char) (decreases xs) =
  match xs with
  | [] -> []
  | (nm, v) :: rest ->
    List.Tot.append [' ']
      (List.Tot.append nm
        (List.Tot.append ['='; '"']
          (List.Tot.append v
            (List.Tot.append ['"'] (xmlc_render_attrs rest)))))

/// Canonicalise a single tag body (chars strictly between `<` and `>`),
/// returning the canonical tag WITH its angle brackets. End tags,
/// comments (!), and PIs (?) are verbatim; start tags get their
/// attributes sorted and any self-close expanded to open+close.
let xmlc_canon_tag (body : list FStar.Char.char) : list FStar.Char.char =
  match body with
  | [] -> ['<'; '>']
  | '/' :: _ -> List.Tot.append ['<'] (List.Tot.append body ['>'])
  | '!' :: _ -> List.Tot.append ['<'] (List.Tot.append body ['>'])
  | '?' :: _ -> List.Tot.append ['<'] (List.Tot.append body ['>'])
  | _ ->
    let (nm, r1) = xmlc_take_name body [] in
    let (attrs, self_close) = xmlc_parse_attrs (List.Tot.length r1 + 1) r1 [] in
    let sorted = xmlc_sort_attrs attrs in
    let open_tag =
      List.Tot.append ['<']
        (List.Tot.append nm
          (List.Tot.append (xmlc_render_attrs sorted) ['>'])) in
    if self_close
    then List.Tot.append open_tag
           (List.Tot.append ['<'; '/'] (List.Tot.append nm ['>']))
    else open_tag

/// Scan up to (and consuming) the closing `>`; returns
/// (body-without-brackets, remainder-after-`>`).
let rec xmlc_split_tag (cs acc : list FStar.Char.char)
  : Tot (list FStar.Char.char * list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, [])
  | c :: rest -> if c = '>' then (List.Tot.rev acc, rest)
                 else xmlc_split_tag rest (c :: acc)

/// Walk the char stream: text verbatim; a `<` begins a tag that is
/// canonicalised by `xmlc_canon_tag`. Fuel-bounded.
let rec xmlc_walk (fuel : nat) (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases fuel) =
  if fuel = 0 then []
  else match cs with
    | [] -> []
    | c :: rest ->
      if c = '<' then
        let (body, remainder) = xmlc_split_tag rest [] in
        List.Tot.append (xmlc_canon_tag body) (xmlc_walk (fuel - 1) remainder)
      else c :: xmlc_walk (fuel - 1) rest

let xmlc_canonicalize (s : string) : list FStar.Char.char =
  let cs = String.list_of_string s in
  xmlc_walk (List.Tot.length cs + 1) cs

/// XMLLiteral value equality: equal iff canonical char-streams match.
/// Reflexive by construction (`f x = f x`).
let xml_canon_eq (s1 s2 : string) : bool =
  xmlc_canonicalize s1 = xmlc_canonicalize s2

/// Structural equality on literals: lexical form and datatype compare
/// exactly; the language tag (if any) compares case-insensitively.
/// Exception: when both literals are rdf:XMLLiteral-typed, lexical
/// forms compare via `xml_canon_eq` (RDF 1.1 exclusive-c14n value
/// equality) rather than as raw strings — the sound fix for the
/// WebOnt-miscellaneous-202 false functional-property clash. Reflexive:
/// the XMLLiteral branch reduces to `f x = f x`.
let literal_eq (l1 l2 : literal) : bool =
  (if l1.datatype = rdf_XMLLiteral && l2.datatype = rdf_XMLLiteral
   then xml_canon_eq l1.lexical_form l2.lexical_form
   else l1.lexical_form = l2.lexical_form) &&
  l1.datatype = l2.datatype &&
  lang_tag_option_eq l1.lang_tag l2.lang_tag &&
  l1.direction = l2.direction

/// STRICT literal TERM equality — RDF 1.1 Concepts §3.3 / RDF 1.2
/// Concepts §3.3: "Two literals are term-equal (the same RDF literal)
/// if and only if the two lexical forms, the two datatype IRIs, and
/// the two language tags (if any) compare equal, character by
/// character." Every field compares exactly: no language-tag case
/// folding (that is RDF 1.1's PERMITTED lowercasing of the value
/// space, not a term-equality rule) and no rdf:XMLLiteral
/// exclusive-canonical-XML comparison (an RDF-interpretation /
/// D-entailment value condition — RDF 2004 §3.1 places it on
/// *rdf*-interpretations, and RDF 1.1 Concepts §5.3 marks
/// rdf:XMLLiteral non-normative). `literal_eq` above is deliberately
/// COARSER than this for that reason; do not substitute one for the
/// other. Issue #324 (SE-1): simple entailment (RDF 1.1 Semantics §5)
/// matches literals by TERM equality, so the simple-entailment engine
/// must use this predicate, not `literal_eq`. Reflexive by
/// construction (every conjunct is `f x = f x`).
let literal_term_eq (l1 l2 : literal) : bool =
  l1.lexical_form = l2.lexical_form &&
  l1.datatype = l2.datatype &&
  l1.lang_tag = l2.lang_tag &&
  l1.direction = l2.direction

let lemma_literal_term_eq_refl (l : literal) : Lemma (literal_term_eq l l == true) = ()

/// The strict test decides literal term IDENTITY unconditionally — no
/// `lit_exact` side condition needed, unlike `literal_eq`.
let lemma_literal_term_eq_identity (l1 l2 : literal)
  : Lemma (requires literal_term_eq l1 l2 == true) (ensures l1 == l2) =
  assert (l1.lexical_form == l2.lexical_form);
  assert (l1.datatype == l2.datatype);
  assert (l1.lang_tag == l2.lang_tag);
  assert (l1.direction == l2.direction)

/// ---- #337 (SR-2): the canonical form the JOIN KEY serialises -------------
///
/// A hash join is semantics-preserving only when key equality is NO
/// FINER than the acceptance test (`sm_compatible`, which accepts on
/// `rdf_term_eq`). `rdf_term_eq` folds exactly two things a byte-level
/// key does not: language-tag case (`lang_tag_eq`) and XMLLiteral
/// exclusive-canonical form (`xml_canon_eq`). `join_canon_term` applies
/// those same two foldings to the term itself, so serialising the
/// canonical term gives a key with the required coarseness --
/// established by `lemma_join_canon_term_eq` below, not by a banner
/// comment (the previous banner ASSERTED the superset property and was
/// wrong; issue #337 is the machine-checked refutation).
let join_canon_literal (l : literal) : literal =
  { l with
    lexical_form =
      (if l.datatype = rdf_XMLLiteral
       then String.string_of_list (xmlc_canonicalize l.lexical_form)
       else l.lexical_form);
    lang_tag =
      (match l.lang_tag with
       | Some t -> Some (String.lowercase t)
       | None -> None) }

let rec join_canon_term (t : rdf_term) : Tot rdf_term (decreases t) =
  match t with
  | T_IRI _ | T_BNode _ -> t
  | T_Literal l -> T_Literal (join_canon_literal l)
  | T_TripleTerm s p o -> T_TripleTerm s p (join_canon_term o)

/// Structural equality on RDF terms. Recursive: a triple term compares
/// structurally in each of its three positions, recursing into the
/// object sub-term (which strictly decreases). `decreases t1`.
let rec rdf_term_eq (t1 t2 : rdf_term) : Tot bool (decreases t1) =
  match t1, t2 with
  | T_IRI i1, T_IRI i2 -> i1 = i2
  | T_BNode b1, T_BNode b2 -> b1 = b2
  | T_Literal l1, T_Literal l2 -> literal_eq l1 l2
  | T_TripleTerm s1 p1 o1, T_TripleTerm s2 p2 o2 ->
    subject_eq s1 s2 && p1 = p2 && rdf_term_eq o1 o2
  | _, _ -> false

/// The coarseness guarantee: terms the acceptance test identifies get
/// IDENTICAL canonical forms, hence identical keys under any
/// deterministic serialiser. Structural recursion mirroring
/// `rdf_term_eq`; every conjunct of `literal_eq` maps onto one field
/// of the canonical literal.
let rec lemma_join_canon_term_eq (t1 t2 : rdf_term)
  : Lemma (requires rdf_term_eq t1 t2 == true)
          (ensures  join_canon_term t1 == join_canon_term t2)
          (decreases t1) =
  match t1, t2 with
  | T_Literal _, T_Literal _ -> ()
  | T_TripleTerm _ _ o1, T_TripleTerm _ _ o2 -> lemma_join_canon_term_eq o1 o2
  | _, _ -> ()

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
  l1.datatype = l2.datatype &&
  l1.direction = l2.direction

/// `subject_eq` is reflexive.
let lemma_subject_eq_refl (s : subject) : Lemma (subject_eq s s = true) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

/// `literal_eq` is reflexive.
let lemma_literal_eq_refl (l : literal) : Lemma (literal_eq l l = true) = ()

/// `rdf_term_eq` is reflexive. Recursive over the triple term's object
/// sub-term (`decreases t`).
let rec lemma_rdf_term_eq_refl (t : rdf_term) : Lemma (ensures rdf_term_eq t t = true) (decreases t) =
  match t with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal l -> lemma_literal_eq_refl l
  | T_TripleTerm s _ o -> lemma_subject_eq_refl s; lemma_rdf_term_eq_refl o
