module Parser.RIFXML

// Phase 3 of the RIF Core F* engine, per
// docs/designissues/2026-05-07-rif-fstar-investigation.md.
//
// Concrete-syntax parser for RIF Core's XML serialization:
//
//   string -> option Syntax.rif_program
//
// The pipeline is two-stage:
//   1. Parser.XML.parse_xml_document : string -> option xml_node
//      (the existing F* DOM-style XML scanner — do NOT touch it).
//   2. This module: walk the resulting XML tree and build the typed
//      RIF.Core.Syntax ADT.
//
// W3C RIF Core XML serialization spec:
//   https://www.w3.org/TR/rif-core/#XML_Serialization
//
// Default namespace is "http://www.w3.org/2007/rif#"; the W3C test
// suite emits elements under that namespace. The element grammar we
// recognise (per the user-supplied scope plus the wrapper elements
// the spec actually uses):
//
//   Document   - top-level container
//     directive*  payload?
//   payload    - wrapper around the rule Group
//     formula : Group
//   Group      - a (flat) collection of rules
//     sentence*
//   sentence   - wrapper around a Forall, Implies, or atom
//   Forall     - universal quantifier (we strip the wrapper; vars
//                appearing free in the rule are quantified implicitly,
//                matching SPARQL BGP semantics)
//     declare*  formula : (Implies | atom)
//   Implies    - rule definition: head if body
//     if : <body>   then : <head>           // RIF-XML conventional
//   if / then / head / body — element wrappers around a body or atom.
//   And        - body conjunction
//     formula+
//   Atom       - atomic formula op(args)
//     op : Const   args : list term
//   Frame      - object[slot1->v1; ...]
//     object : term   slot* : (key,value) pairs
//   slot       - one frame slot
//     <key term>   <value term>
//   Member     - t # c
//     instance : term   class : term
//   Subclass   - sub ## super
//     sub : term   super : term
//   Const      - constant term: IRI or literal
//     attr type=...   text content : the lexical form
//   Var        - variable
//     text content : the variable name (no leading '?')
//   declare    - variable declaration in Forall (we ignore the body
//                since variables are tracked implicitly by free
//                occurrence in atoms)
//   id / meta  - rule annotation (we read the id, ignore richer meta)
//
// Anything we encounter outside this grammar parses to a clean
// failure (the top-level returns None) rather than a silent gap.
// Per iron rule 4: parsers belong in F*; per iron rule 10: no
// --lax / no assume val. The four W3C SPARQL RIF Core test inputs
// are not vendored in this repo (the
// third_party/testing/w3c/sparql/sparql11/entailment/ directory is
// empty); the scope here matches the W3C RIF Core test suite at
// https://www.w3.org/2005/rules/wiki/RIF_Test_Cases as documented
// in the design doc's open-question 2 ("test-driven subset").
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.
//   - No reserved-word let-bindings (`total`, `in_mem`, ...).

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open Parser.XML
module Syn = RIF.Core.Syntax

// ------------------------------------------------------------------
// 1. Namespace constants and tag stripping.
//
// The W3C RIF tests use the default-namespace form, so element tags
// may arrive either bare ("Document") or prefixed ("rif:Document"
// or with a default-namespace expansion). Our XML scanner does NOT
// expand namespaces — it returns the tag as written. We strip a
// known prefix or anything before the last colon to get the local
// name, then compare against the RIF element vocabulary.
// ------------------------------------------------------------------

let rif_ns : string = "http://www.w3.org/2007/rif#"

// RDF namespace, needed to recognise the rdf:PlainLiteral type
// marker (see is_plain_literal_type_marker below).
let rdf_ns : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

// Find the position of the LAST colon, if any. RIF-XML never uses
// hierarchical names with more than one colon, but tag inputs of
// the form "rif:Atom" need the local name "Atom".
let rec find_last_colon_aux (cs : list FStar.Char.char) (idx : nat) (last : option nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> last
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x3A
    then find_last_colon_aux rest (idx + 1) (Some idx)
    else find_last_colon_aux rest (idx + 1) last

let find_last_colon (s : string) : option nat =
  find_last_colon_aux (String.list_of_string s) 0 None

let local_name (tag : string) : string =
  match find_last_colon tag with
  | None -> tag
  | Some pos ->
    let len = String.length tag in
    if pos + 1 >= len then ""
    else String.sub tag (pos + 1) (len - pos - 1)

let tag_is (expected : string) (tag : string) : bool =
  local_name tag = expected

// ------------------------------------------------------------------
// 2. Generic XML walking helpers.
//
// We work on Parser.XML.xml_node values. A few shapes are common:
//   - "extract the first child element with local name X"
//   - "extract all child elements with local name X"
//   - "the first XText child, decoded"
// ------------------------------------------------------------------

let rec first_child_with_local_name (name : string) (children : list xml_node)
  : Tot (option xml_node) (decreases children) =
  match children with
  | [] -> None
  | hd :: rest ->
    (match hd with
     | XElement t _ _ -> if tag_is name t then Some hd
                         else first_child_with_local_name name rest
     | _ -> first_child_with_local_name name rest)

let rec children_with_local_name (name : string) (children : list xml_node)
  : Tot (list xml_node) (decreases children) =
  match children with
  | [] -> []
  | hd :: rest ->
    (match hd with
     | XElement t _ _ ->
       if tag_is name t
       then hd :: children_with_local_name name rest
       else children_with_local_name name rest
     | _ -> children_with_local_name name rest)

let rec child_elements_only (children : list xml_node)
  : Tot (list xml_node) (decreases children) =
  match children with
  | [] -> []
  | hd :: rest ->
    (match hd with
     | XElement _ _ _ -> hd :: child_elements_only rest
     | _ -> child_elements_only rest)

// Decoded-text content of an element: concatenates XText / XCDATA
// children, ignoring nested elements. The RIF XML serialization
// only puts text inside <Const> / <Var> leaf elements, so this is
// what we need for term lexical forms and variable names.
let rec collect_leaf_text (children : list xml_node)
  : Tot string (decreases children) =
  match children with
  | [] -> ""
  | hd :: rest ->
    let here =
      match hd with
      | XText t -> t
      | XCDATA t -> t
      | _ -> ""
    in
    String.concat "" [here; collect_leaf_text rest]

let element_text (n : xml_node) : string =
  match n with
  | XElement _ _ children -> collect_leaf_text children
  | _ -> ""

// ------------------------------------------------------------------
// 3. Term parsing: Const and Var.
//
// RIF-XML constant elements carry a `type` attribute that names the
// kind of constant. The two we handle here are the IRI ("rif:iri")
// and plain-literal cases, plus the typed-literal form where the
// `type` attribute is the datatype IRI.
//
//   <Const type="&rif;iri">http://example.org/foo</Const>
//   <Const type="&xs;string">hello</Const>
//   <Const type="&xs;integer">42</Const>
//
// We accept both the `&prefix;localname` shorthand (an XML entity
// reference, decoded to the namespace + local form by Parser.XML)
// and the fully-resolved IRI.
//
// Variables look like:
//   <Var>x</Var>
//
// The leading "?" is omitted in the XML form; var_name stores the
// bare name.
// ------------------------------------------------------------------

let trim_ws (s : string) : string =
  // Strip leading/trailing ASCII whitespace. The text content of
  // <Const>/<Var> often has surrounding indentation. The Parser.XML
  // scanner already decoded character references, so trimming is
  // codepoint-safe at the byte level for whitespace bytes.
  let cs = String.list_of_string s in
  let rec drop_left (xs : list FStar.Char.char)
    : Tot (list FStar.Char.char) (decreases xs) =
    match xs with
    | [] -> []
    | c :: rest ->
      let code = FStar.Char.int_of_char c in
      if code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D
      then drop_left rest
      else xs
  in
  let trimmed = drop_left cs in
  let reversed = List.Tot.rev trimmed in
  let trimmed_back = drop_left reversed in
  String.string_of_list (List.Tot.rev trimmed_back)

// "iri" type marker, in any of the forms a serialiser might produce.
// The RIF Core XML serialization mandates the full IRI form
// "http://www.w3.org/2007/rif#iri", but writers in the wild also
// emit the bare local name "iri" (after default-namespace expansion
// is applied externally) or the prefixed "rif:iri". Accept all three.
let is_iri_type_marker (ty : string) : bool =
  ty = String.concat "" [rif_ns; "iri"]
  || ty = "iri"
  || local_name ty = "iri"

// "local" / plain-string is the other RIF term type marker we accept
// uniformly as an IRI. RIF Core also defines "rif:local" which acts
// as a constant local-scope IRI.
let is_local_type_marker (ty : string) : bool =
  ty = String.concat "" [rif_ns; "local"]
  || ty = "local"
  || local_name ty = "local"

// Try to build a RIF constant term from a (type, lexical) pair.
// Build a synthetic "urn:rif-local:..." IRI for rif:local constants.
// Always produces an IRI containing a colon; we still gate on is_iri
// to satisfy the wf_iri refinement.
let local_to_iri (lex : string) : option Syn.rif_term =
  let urn_iri = String.concat "" ["urn:rif-local:"; lex] in
  if is_iri urn_iri
  then Some (Syn.mk_const (T_IRI urn_iri))
  else None

let typed_literal_const (ty : string) (lex : string) : option Syn.rif_term =
  if is_iri ty && ty <> rdf_lang_string
  then
    Some (Syn.mk_const (T_Literal ({
      lexical_form = lex;
      datatype = ty;
      lang_tag = None;
    })))
  else None

// rdf:PlainLiteral marker — the RIF-in-RDF compatibility mapping
// (https://www.w3.org/TR/rif-rdf-owl/#Data_Types), section on the
// rdf:PlainLiteral datatype: its lexical space packs a text/language
// pair as "text@lang", with the empty-tag case "text@" denoting a
// plain (no language) string. Accept the fully-resolved IRI, the
// bare local name, and any "prefix:PlainLiteral" form, mirroring
// is_iri_type_marker / is_local_type_marker above.
let is_plain_literal_type_marker (ty : string) : bool =
  ty = String.concat "" [rdf_ns; "PlainLiteral"]
  || ty = "PlainLiteral"
  || local_name ty = "PlainLiteral"

// Find the position of the LAST '@', if any — the language-tag
// separator. Same traversal shape as find_last_colon_aux above.
let rec find_last_at_aux (cs : list FStar.Char.char) (idx : nat) (last : option nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> last
  | c :: rest ->
    if FStar.Char.int_of_char c = 0x40
    then find_last_at_aux rest (idx + 1) (Some idx)
    else find_last_at_aux rest (idx + 1) last

let find_last_at (s : string) : option nat =
  find_last_at_aux (String.list_of_string s) 0 None

// Decode an rdf:PlainLiteral lexical form "text@lang" (or "text@",
// empty tag) into the RIF term for the RDF literal it denotes: a
// language-tagged literal when the tag is non-empty, else a plain
// xsd:string literal. No '@' at all is not valid rdf:PlainLiteral
// lexical form (the compatibility mapping always includes the
// separator, even for the empty tag), so that case fails cleanly
// rather than guessing.
let plain_literal_const (lex : string) : option Syn.rif_term =
  match find_last_at lex with
  | None -> None
  | Some pos ->
    let len = String.length lex in
    // find_last_at's result carries no refinement tying it back to
    // String.length lex, so re-establish the bound explicitly (same
    // pattern as local_name's "if pos + 1 >= len then ..." guard
    // above) before the String.sub calls below can typecheck.
    if pos >= len then None
    else
      let text = String.sub lex 0 pos in
      let lang = String.sub lex (pos + 1) (len - pos - 1) in
      if String.length lang = 0
      then Some (Syn.mk_const (T_Literal ({
             lexical_form = text;
             datatype = xsd_string;
             lang_tag = None;
           })))
      else Some (Syn.mk_const (T_Literal ({
             lexical_form = text;
             datatype = rdf_lang_string;
             lang_tag = Some lang;
           })))

let const_from_type (ty : string) (lex : string) : option Syn.rif_term =
  if is_iri_type_marker ty then
    if is_iri lex
    then Some (Syn.mk_const (T_IRI lex))
    else None
  else if is_local_type_marker ty then
    // rif:local — treat as an IRI keyed in a synthetic "rif-local:"
    // namespace so it is at least well-formed. The W3C combination
    // spec maps rif:local to fresh blank nodes per document, but
    // none of the four target tests rely on the more elaborate
    // semantics.
    local_to_iri lex
  else if is_plain_literal_type_marker ty then
    plain_literal_const lex
  else
    typed_literal_const ty lex

let parse_const (n : xml_node) : option Syn.rif_term =
  match n with
  | XElement _ attrs children ->
    let ty_opt = find_attr "type" attrs in
    let lex = trim_ws (collect_leaf_text children) in
    (match ty_opt with
     | Some ty -> const_from_type ty lex
     | None ->
       // No `type` attribute: default to a plain string literal.
       // The RIF spec strictly requires `type`; we accept the
       // missing-type case as xsd:string for robustness.
       Some (Syn.mk_const (T_Literal ({
         lexical_form = lex;
         datatype = xsd_string;
         lang_tag = None;
       }))))
  | _ -> None

let parse_var (n : xml_node) : option Syn.rif_term =
  match n with
  | XElement _ _ children ->
    let raw = trim_ws (collect_leaf_text children) in
    if String.length raw = 0 then None
    else Some (Syn.mk_var raw)
  | _ -> None

// Dispatch on element local name to parse a term.
let parse_term (n : xml_node) : option Syn.rif_term =
  match n with
  | XElement tag _ _ ->
    if tag_is "Const" tag then parse_const n
    else if tag_is "Var" tag then parse_var n
    else None
  | _ -> None

// Parse a term wrapped in a single-element host (<object>, <op>,
// <slot>'s key/value, ...). The host element typically contains
// one Const/Var child; we find that child and decode it.
let parse_term_host (n : xml_node) : option Syn.rif_term =
  match n with
  | XElement _ _ children ->
    (match child_elements_only children with
     | [] -> None
     | first :: _ -> parse_term first)
  | _ -> None

// ------------------------------------------------------------------
// 4. Atom-shape parsers.
//
// Each of these consumes one xml_node (the corresponding element)
// and produces an atom or a list of atoms.
// ------------------------------------------------------------------

// <Atom>
//   <op><Const type="...">predIRI</Const></op>
//   <args>
//     <Const ...>subj</Const>
//     <Const ...>obj</Const>
//   </args>
// </Atom>
//
// Per the RIF/RDF combination spec, a binary atom p(s,o) maps to
// the triple (s, p, o). Higher-arity atoms are out of RIF Core's
// RDF profile and we surface them as None.
let parse_atom_element (n : xml_node) : option Syn.rif_atom =
  match n with
  | XElement _ _ children ->
    let op_n = first_child_with_local_name "op" children in
    let args_n = first_child_with_local_name "args" children in
    (match op_n, args_n with
     | Some op_node, Some args_node ->
       (match parse_term_host op_node with
        | None -> None
        | Some pred ->
          let arg_terms =
            List.Tot.fold_right
              (fun (c:xml_node) (acc:list (option Syn.rif_term)) ->
                 match c with
                 | XElement _ _ _ -> parse_term c :: acc
                 | _ -> acc)
              (element_children args_node)
              []
          in
          // Require exactly two arguments (subject, object) and
          // both must have parsed.
          (match arg_terms with
           | [Some s; Some o] -> Some (Syn.RIF_Triple s pred o)
           | _ -> None))
     | _, _ -> None)
  | _ -> None

// <Frame>
//   <object>...term...</object>
//   <slot>
//     <Const ...>predIRI</Const>     // key
//     <Const ...>val</Const>         // value
//   </slot>
//   <slot>...</slot>
// </Frame>
//
// Multi-slot frames decompose into one RIF_Frame atom per slot,
// returned as a list. Single-slot is the degenerate case.
let parse_slot_pair (slot : xml_node) (obj : Syn.rif_term)
  : option Syn.rif_atom =
  match slot with
  | XElement _ _ children ->
    (match child_elements_only children with
     | [k; v] ->
       (match parse_term k, parse_term v with
        | Some kt, Some vt -> Some (Syn.RIF_Frame obj kt vt)
        | _, _ -> None)
     | _ -> None)
  | _ -> None

let rec list_collect_some (xs : list (option 'a))
  : Tot (option (list 'a)) (decreases xs) =
  match xs with
  | [] -> Some []
  | None :: _ -> None
  | Some x :: rest ->
    (match list_collect_some rest with
     | None -> None
     | Some ys -> Some (x :: ys))

let parse_frame_element (n : xml_node) : option (list Syn.rif_atom) =
  match n with
  | XElement _ _ children ->
    let obj_n = first_child_with_local_name "object" children in
    let slots = children_with_local_name "slot" children in
    (match obj_n with
     | None -> None
     | Some obj_node ->
       (match parse_term_host obj_node with
        | None -> None
        | Some obj ->
          let slot_atoms =
            List.Tot.map (fun (s : xml_node) -> parse_slot_pair s obj) slots
          in
          list_collect_some slot_atoms))
  | _ -> None

// <Member>
//   <instance>...term...</instance>
//   <class>...term...</class>
// </Member>
let parse_member_element (n : xml_node) : option Syn.rif_atom =
  match n with
  | XElement _ _ children ->
    let inst_n = first_child_with_local_name "instance" children in
    let cls_n = first_child_with_local_name "class" children in
    (match inst_n, cls_n with
     | Some i_node, Some c_node ->
       (match parse_term_host i_node, parse_term_host c_node with
        | Some i, Some c -> Some (Syn.RIF_Member i c)
        | _, _ -> None)
     | _, _ -> None)
  | _ -> None

// <Subclass>
//   <sub>...term...</sub>
//   <super>...term...</super>
// </Subclass>
let parse_subclass_element (n : xml_node) : option Syn.rif_atom =
  match n with
  | XElement _ _ children ->
    let sub_n = first_child_with_local_name "sub" children in
    let sup_n = first_child_with_local_name "super" children in
    (match sub_n, sup_n with
     | Some s_node, Some u_node ->
       (match parse_term_host s_node, parse_term_host u_node with
        | Some sb, Some su -> Some (Syn.RIF_Sub sb su)
        | _, _ -> None)
     | _, _ -> None)
  | _ -> None

// Parse any single atom element. Frames produce multiple atoms
// (one per slot); the caller wraps the result in RIF_BodyAnd if
// there is more than one. We surface that by returning a list.
let parse_atom_node (n : xml_node) : option (list Syn.rif_atom) =
  match n with
  | XElement tag _ _ ->
    if tag_is "Atom" tag then
      (match parse_atom_element n with
       | None -> None
       | Some a -> Some [a])
    else if tag_is "Frame" tag then
      parse_frame_element n
    else if tag_is "Member" tag then
      (match parse_member_element n with
       | None -> None
       | Some a -> Some [a])
    else if tag_is "Subclass" tag then
      (match parse_subclass_element n with
       | None -> None
       | Some a -> Some [a])
    else
      None
  | _ -> None

// ------------------------------------------------------------------
// 5. Body parsing.
//
// A body is either a single atomic formula, an And of formulas, or
// the wrapper element <if> / <body> / <formula> containing one of
// the above. We unwrap wrappers transparently.
// ------------------------------------------------------------------

let is_body_wrapper_tag (tag : string) : bool =
  tag_is "if" tag
  || tag_is "body" tag
  || tag_is "formula" tag

let is_atom_tag (tag : string) : bool =
  tag_is "Atom" tag
  || tag_is "Frame" tag
  || tag_is "Member" tag
  || tag_is "Subclass" tag

// Forward declaration via mutual recursion below.
let rec parse_body_node (n : xml_node) (fuel : nat)
  : Tot (option Syn.rif_body) (decreases fuel) =
  if fuel = 0 then None
  else
    match n with
    | XElement tag _ children ->
      if tag_is "And" tag then
        let kids = child_elements_only children in
        let bodies = parse_body_list kids (fuel - 1) in
        (match bodies with
         | None -> None
         | Some bs -> Some (Syn.RIF_BodyAnd bs))
      else if is_body_wrapper_tag tag then
        // Unwrap and recurse into the first element child.
        (match child_elements_only children with
         | [] -> None
         | first :: _ -> parse_body_node first (fuel - 1))
      else if is_atom_tag tag then
        (match parse_atom_node n with
         | None -> None
         | Some [a] -> Some (Syn.RIF_BodyAtom a)
         | Some atoms ->
           // Multi-atom frame: conjoin.
           Some (Syn.RIF_BodyAnd
             (List.Tot.map (fun (a:Syn.rif_atom) -> Syn.RIF_BodyAtom a) atoms)))
      else
        None
    | _ -> None

and parse_body_list (xs : list xml_node) (fuel : nat)
  : Tot (option (list Syn.rif_body)) (decreases fuel) =
  if fuel = 0 then None
  else
    match xs with
    | [] -> Some []
    | hd :: rest ->
      (match parse_body_node hd (fuel - 1) with
       | None -> None
       | Some b ->
         (match parse_body_list rest (fuel - 1) with
          | None -> None
          | Some bs -> Some (b :: bs)))

// ------------------------------------------------------------------
// 6. Head parsing.
//
// The head of an Implies is exactly one atom (RIF Core forbids head
// disjunction and head function symbols). Head Frames with multiple
// slots are illegal at the rif_atom level; we surface that as None.
// The head element wrapper may be <then> or <head>.
// ------------------------------------------------------------------

let is_head_wrapper_tag (tag : string) : bool =
  tag_is "then" tag
  || tag_is "head" tag
  || tag_is "formula" tag

let rec unwrap_head_node (n : xml_node) (fuel : nat)
  : Tot (option xml_node) (decreases fuel) =
  if fuel = 0 then None
  else
    match n with
    | XElement tag _ children ->
      if is_atom_tag tag then Some n
      else if is_head_wrapper_tag tag then
        (match child_elements_only children with
         | [] -> None
         | first :: _ -> unwrap_head_node first (fuel - 1))
      else
        None
    | _ -> None

let parse_head_node (n : xml_node) (fuel : nat) : option Syn.rif_atom =
  match unwrap_head_node n fuel with
  | None -> None
  | Some atom_node ->
    (match parse_atom_node atom_node with
     | Some [a] -> Some a
     | _ -> None)

// ------------------------------------------------------------------
// 7. Implies (rule body).
//
// <Implies>
//   <if>   ... body ...   </if>
//   <then> ... head ...   </then>
// </Implies>
//
// Some serializations emit <body>/<head> instead of <if>/<then>.
// We accept either pair. The order of <if>/<then> in the XML is
// fixed by the spec; we still scan by name for robustness.
// ------------------------------------------------------------------

let find_first_named (names : list string) (children : list xml_node)
  : option xml_node =
  let rec go (ns : list string)
    : Tot (option xml_node) (decreases ns) =
    match ns with
    | [] -> None
    | name :: rest ->
      (match first_child_with_local_name name children with
       | Some n -> Some n
       | None -> go rest)
  in
  go names

let parse_implies (n : xml_node) (fuel : nat) : option Syn.rif_rule =
  if fuel = 0 then None
  else
    match n with
    | XElement _ _ children ->
      let if_node = find_first_named ["if"; "body"] children in
      let then_node = find_first_named ["then"; "head"] children in
      (match if_node, then_node with
       | Some i, Some t ->
         (match parse_body_node i fuel, parse_head_node t fuel with
          | Some body_, Some head_ ->
            Some (Syn.mk_rule head_ body_)
          | _, _ -> None)
       | _, _ -> None)
    | _ -> None

// ------------------------------------------------------------------
// 8. Forall and sentence parsing.
//
// <Forall>
//   <declare><Var>x</Var></declare>
//   <declare><Var>y</Var></declare>
//   <formula>
//     <Implies> ... </Implies>
//   </formula>
// </Forall>
//
// We strip the Forall wrapper: the variables it declares are picked
// up automatically as free variables in the rule body and head, per
// the comment block in RIF.Core.Syntax.fst §4.
//
// A <sentence> can directly contain an Implies (when there is no
// Forall) or a bare atom (a fact, with empty body). We handle both.
// ------------------------------------------------------------------

let parse_fact_atom (n : xml_node) : option Syn.rif_rule =
  match parse_atom_node n with
  | Some [a] ->
    // Body-less fact: empty conjunction.
    Some (Syn.mk_rule a (Syn.RIF_BodyAnd []))
  | Some _atoms ->
    // Multi-atom Frame as a fact: turn each slot into a separate
    // fact rule. Caller will spread these across the rule list.
    None
  | None -> None

// A sentence may contain a Forall, an Implies, an Atom/Frame/Member/
// Subclass (treated as a fact), or a wrapper element <formula>.
let rec parse_sentence_content (n : xml_node) (fuel : nat)
  : Tot (option (list Syn.rif_rule)) (decreases fuel) =
  if fuel = 0 then None
  else
    match n with
    | XElement tag _ children ->
      if tag_is "Forall" tag then
        (match first_child_with_local_name "formula" children with
         | None ->
           // Some serialisers omit the formula wrapper inside Forall.
           // Find the first Implies child directly.
           (match first_child_with_local_name "Implies" children with
            | Some imp_node ->
              (match parse_implies imp_node fuel with
               | None -> None
               | Some rule_ -> Some [rule_])
            | None -> None)
         | Some f_node ->
           parse_sentence_content f_node (fuel - 1))
      else if tag_is "Implies" tag then
        (match parse_implies n fuel with
         | None -> None
         | Some rule_ -> Some [rule_])
      else if tag_is "formula" tag then
        (match child_elements_only children with
         | [] -> None
         | first :: _ -> parse_sentence_content first (fuel - 1))
      else if tag_is "sentence" tag then
        (match child_elements_only children with
         | [] -> None
         | first :: _ -> parse_sentence_content first (fuel - 1))
      else if is_atom_tag tag then
        // Body-less fact.
        (match parse_atom_node n with
         | None -> None
         | Some [a] ->
           Some [Syn.mk_rule a (Syn.RIF_BodyAnd [])]
         | Some atoms ->
           // Multi-slot frame as a fact: emit one fact per slot.
           Some (List.Tot.map
             (fun (a : Syn.rif_atom) ->
                Syn.mk_rule a (Syn.RIF_BodyAnd []))
             atoms))
      else
        None
    | _ -> None

// ------------------------------------------------------------------
// 9. Group parsing.
//
// <Group>
//   <sentence> ... </sentence>
//   <sentence> ... </sentence>
// </Group>
//
// A Group groups a flat list of rules (RIF Core supports nested
// Groups but the four W3C target tests do not exercise nesting; we
// still walk recursively into nested Groups for safety).
// ------------------------------------------------------------------

let rec parse_group_children (xs : list xml_node) (fuel : nat)
  : Tot (option (list Syn.rif_rule)) (decreases fuel) =
  if fuel = 0 then None
  else
    match xs with
    | [] -> Some []
    | hd :: rest ->
      (match hd with
       | XElement tag _ children ->
         if tag_is "sentence" tag then
           // sentence may wrap any of: Forall, Implies, atom, formula,
           // or even a nested Group.
           (match child_elements_only children with
            | [] ->
              parse_group_children rest (fuel - 1)
            | first :: _ ->
              if (match first with
                  | XElement t _ _ -> tag_is "Group" t
                  | _ -> false) then
                (match parse_group_node first (fuel - 1) with
                 | None -> None
                 | Some these ->
                   (match parse_group_children rest (fuel - 1) with
                    | None -> None
                    | Some more -> Some (these @ more)))
              else
                (match parse_sentence_content first (fuel - 1) with
                 | None -> None
                 | Some these ->
                   (match parse_group_children rest (fuel - 1) with
                    | None -> None
                    | Some more -> Some (these @ more))))
         else if tag_is "Group" tag then
           (match parse_group_node hd (fuel - 1) with
            | None -> None
            | Some these ->
              (match parse_group_children rest (fuel - 1) with
               | None -> None
               | Some more -> Some (these @ more)))
         else
           // Unknown / metadata element: skip silently. We deliberately
           // do not fail on `<id>`, `<meta>`, or comments inside a
           // Group, because those are annotations rather than rules.
           parse_group_children rest (fuel - 1)
       | _ -> parse_group_children rest (fuel - 1))

and parse_group_node (n : xml_node) (fuel : nat)
  : Tot (option (list Syn.rif_rule)) (decreases fuel) =
  if fuel = 0 then None
  else
    match n with
    | XElement tag _ children ->
      if tag_is "Group" tag then
        parse_group_children children (fuel - 1)
      else
        None
    | _ -> None

// ------------------------------------------------------------------
// 10. Document parsing.
//
// <Document>
//   <directive>
//     <Import>
//       <location>http://example.org/foo</location>
//       <profile>http://www.w3.org/ns/entailment/Simple</profile>
//     </Import>
//   </directive>
//   <payload>
//     <Group> ... </Group>
//   </payload>
// </Document>
//
// We tolerate the absence of <payload> (some test inputs put the
// Group directly under <Document>) and the absence of <Document>
// (some test fragments are bare <Group> elements).
//
// The directive list is collected separately by extract_imports
// below and exposed alongside the rule program; this is what the
// rif04 / rif06 tests need so the OCaml glue can resolve the
// referenced data graphs onto the local third_party/testing/rif
// vendor mirror before saturation runs.
// ------------------------------------------------------------------

let extract_group_from_doc (root : xml_node) (fuel : nat)
  : Tot (option xml_node) (decreases fuel) =
  if fuel = 0 then None
  else
    match root with
    | XElement tag _ children ->
      if tag_is "Document" tag then
        (match first_child_with_local_name "payload" children with
         | Some payload_node ->
           (match payload_node with
            | XElement _ _ pchildren ->
              first_child_with_local_name "Group" pchildren
            | _ -> None)
         | None ->
           // No payload: Group might be a direct child.
           first_child_with_local_name "Group" children)
      else if tag_is "Group" tag then
        Some root
      else if tag_is "payload" tag then
        first_child_with_local_name "Group" children
      else
        None
    | _ -> None

let parse_rif_document (root : xml_node) : option Syn.rif_program =
  let fuel : nat = 1000 in
  match extract_group_from_doc root fuel with
  | None -> None
  | Some group_node ->
    (match parse_group_node group_node fuel with
     | None -> None
     | Some rules_ -> Some (Syn.program_of_rules rules_))

// ------------------------------------------------------------------
// 11. Top-level entry point.
//
//   parse_rif_program : string -> option Syn.rif_program
//
// Pipes the input through Parser.XML.parse_xml_document and walks
// the resulting tree.
// ------------------------------------------------------------------

let parse_rif_program (input : string) : option Syn.rif_program =
  match parse_xml_document input with
  | None -> None
  | Some root -> parse_rif_document root

// ------------------------------------------------------------------
// 12. <Import> directive resolution.
//
// RIF Core <directive><Import><location>URL</location></Import></directive>
// declares an external data graph that the rule body refers to. The
// SPARQL 1.1 entailment tests rif04 / rif06 use Imports to point at
// .rdf companion files: without loading those files into the premise
// graph, rule bodies that only mention imported facts never fire and
// saturation produces nothing useful.
//
// This module returns the import URLs as plain strings; the OCaml
// runner glue is responsible for mapping the URL back to a local
// path under third_party/testing/rif/tc/<TestName>/, parsing the
// data with Parser.RDFXML / Parser.Turtle as appropriate, and
// merging the triples into the premise graph before saturation.
// Resolution is consumer-side I/O (rule #11), not in F*.
//
// Optional <profile> children are read but ignored: RIF Core's
// entailment-profile selection is out of scope for this PR; the
// four target SPARQL tests only ever use Simple / RDF profiles
// which the saturation engine already subsumes.
// ------------------------------------------------------------------

// Decoded text inside an <Import><location>...</location> child.
let parse_import_location (import_node : xml_node) : option string =
  match import_node with
  | XElement _ _ children ->
    (match first_child_with_local_name "location" children with
     | None -> None
     | Some loc_node ->
       let raw = trim_ws (element_text loc_node) in
       if String.length raw = 0 then None else Some raw)
  | _ -> None

// Walk one <directive> element, returning the import URL if it
// contains an <Import><location>...</location>; None otherwise.
let parse_directive_import (directive_node : xml_node) : option string =
  match directive_node with
  | XElement _ _ children ->
    (match first_child_with_local_name "Import" children with
     | None -> None
     | Some imp_node -> parse_import_location imp_node)
  | _ -> None

// Collect the URLs from every <directive>/<Import>/<location> child
// of a <Document> element. Directives that don't carry an Import or
// don't carry a location are silently skipped -- the test suite only
// uses the import form. Order is preserved so callers may rely on
// the source-document ordering for diagnostics.
let rec extract_imports_from_directives (children : list xml_node)
  : Tot (list string) (decreases children) =
  match children with
  | [] -> []
  | hd :: rest ->
    (match hd with
     | XElement t _ _ ->
       if tag_is "directive" t then
         (match parse_directive_import hd with
          | None -> extract_imports_from_directives rest
          | Some url -> url :: extract_imports_from_directives rest)
       else
         extract_imports_from_directives rest
     | _ -> extract_imports_from_directives rest)

// Top-level helper: given a <Document> root (or a bare <Group>),
// return the imports declared at the document level. A bare Group
// has no directives so we return [].
let extract_document_imports (root : xml_node) : list string =
  match root with
  | XElement tag _ children ->
    if tag_is "Document" tag
    then extract_imports_from_directives children
    else []
  | _ -> []

// Public entry: parse the RIF-XML, returning the import URLs and
// the program in one pass. The OCaml glue can then resolve URLs
// to local files and merge the data into the premise graph before
// invoking RIF.Core.Eval.fixpoint.
let parse_rif_program_with_imports (input : string)
  : option (list string * Syn.rif_program) =
  match parse_xml_document input with
  | None -> None
  | Some root ->
    (match parse_rif_document root with
     | None -> None
     | Some prog -> Some (extract_document_imports root, prog))
