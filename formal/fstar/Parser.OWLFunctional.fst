module Parser.OWLFunctional

(* ================================================================ *)
(* OWL 2 Functional-Syntax Parser — narrow subset, F*-verified        *)
(*                                                                    *)
(* Scope: docs/designissues/2026-07-05-owl-functional-syntax-plan.md. *)
(* This is NOT a general OWL 2 Functional Syntax parser. It covers    *)
(* exactly the grammar the currently-skipped catalog entries need     *)
(* (originally 4 profile-RL.rdf entries; widened 2026-07-13/Wave D to *)
(* cover the 11 functional-syntax-only entries in                     *)
(* type-inconsistency.rdf's DL regime — datatype-facet inconsistency   *)
(* tests):                                                             *)
(*                                                                    *)
(*   Prefix( pfx = <IRI> )            zero or more, before Ontology   *)
(*   Ontology( Declaration/Axiom* )                                   *)
(*   Declaration(ObjectProperty(IRI))                                 *)
(*   Declaration(DataProperty(IRI))                                   *)
(*   Declaration(NamedIndividual(IRI))                                *)
(*   Declaration(Class(IRI))                                          *)
(*   TransitiveObjectProperty(IRI)                                    *)
(*   FunctionalDataProperty(IRI)                                      *)
(*   DataPropertyRange(IRI IRI)                                       *)
(*   DataPropertyAssertion(IRI IRI Literal)                           *)
(*   NegativeDataPropertyAssertion(IRI IRI Literal)                   *)
(*   DisjointDataProperties(IRI IRI)          exactly 2 args           *)
(*   SubClassOf(ClassExpr ClassExpr)                                   *)
(*   ClassAssertion(ClassExpr IRI)                                     *)
(*   SubObjectPropertyOf(ObjectPropertyChain(IRI IRI) IRI)             *)
(*                                                                    *)
(*   ClassExpr ::= IRI                                                 *)
(*              |  DataHasValue(IRI Literal)                           *)
(*              |  DataSomeValuesFrom(IRI DataRange)                   *)
(*              |  DataAllValuesFrom(IRI DataRange)                    *)
(*              |  ObjectComplementOf(ClassExpr)                       *)
(*              |  DataExactCardinality(n IRI [DataRange])             *)
(*              |  DataMinCardinality(n IRI [DataRange])               *)
(*              |  DataMaxCardinality(n IRI [DataRange])               *)
(*                                                                    *)
(*   DataRange ::= IRI                                                 *)
(*              |  DataOneOf(Literal+)                                 *)
(*              |  DataComplementOf(DataRange)                         *)
(*              |  DatatypeRestriction(IRI (IRI Literal)+)             *)
(*                                                                    *)
(* Any other construct (object-property expressions beyond a 2-link    *)
(* chain, annotations, other axiom/class-expression/data-range kinds)  *)
(* is a clean parse failure (`None`) — the caller (owl_runner.ml)      *)
(* treats that as "unsupported input syntax", the same honest skip     *)
(* it already reports today, never a silent wrong answer. No fixture-  *)
(* string special-casing: every production below is a general grammar  *)
(* rule, not a literal match on one test's text.                       *)
(*                                                                    *)
(* Axiom-to-triple mapping follows the OWL 2 Mapping to RDF Graphs     *)
(* spec's per-axiom / per-class-expression / per-data-range tables     *)
(* (e.g. TransitiveObjectProperty(:p) -> :p rdf:type                   *)
(* owl:TransitiveProperty; DataHasValue(P v) -> a fresh owl:Restriction *)
(* bnode with owl:onProperty/owl:hasValue; DataSomeValuesFrom/          *)
(* DataAllValuesFrom(P DR) -> a fresh owl:Restriction bnode with        *)
(* owl:onProperty/owl:someValuesFrom|owl:allValuesFrom T(DR);           *)
(* ObjectComplementOf(CE) -> a fresh owl:Class bnode with               *)
(* owl:complementOf T(CE); DataOneOf(v1..vn) -> a fresh rdfs:Datatype   *)
(* bnode with owl:oneOf pointing at an rdf:first/rdf:rest literal list; *)
(* DataComplementOf(DR) -> a fresh rdfs:Datatype bnode with             *)
(* owl:datatypeComplementOf T(DR); DatatypeRestriction(DT F1 v1 ...) -> *)
(* a fresh rdfs:Datatype bnode with owl:onDatatype DT and               *)
(* owl:withRestrictions pointing at a list of facet bnodes, each        *)
(* `_:f <Fi> vi`; ObjectPropertyChain(P1 P2) -> an rdf:first/rdf:rest   *)
(* list bound via owl:propertyChainAxiom). This is the real            *)
(* translation, not an ad-hoc shortcut — whether the existing OWL-RL   *)
(* closure / DL tableau in RDF.Graph.Executable.fst / Tableau.Refute.fst*)
(* can already see through a given encoding to detect a clash is a      *)
(* closure/tableau-completeness question, tracked separately (datatype  *)
(* facet VALUE reasoning — min/maxInclusive interval checks, pattern    *)
(* matching, oneOf/complementOf value-space arithmetic — is NOT         *)
(* implemented anywhere in this tree as of 2026-07-13; this module only *)
(* produces the RDF encoding of the axioms, it never touches the        *)
(* closure/tableau rule sets) and out of this module's territory.       *)
(* ================================================================ *)

open FStar.String
open FStar.List.Tot
open Parser.FastString
open Parser.Combinators
open RDF.Graph.Executable

(* ------------------------------------------------------------------ *)
(* Character-class helpers                                            *)
(* ------------------------------------------------------------------ *)

// Punctuation code points used throughout the grammar.
let lparen_code : int = 0x28  // '('
let rparen_code : int = 0x29  // ')'
let langle_code : int = 0x3C  // '<'
let rangle_code : int = 0x3E  // '>'
let quote_code  : int = 0x22  // '"'
let colon_code  : int = 0x3A  // ':'
let eq_code     : int = 0x3D  // '='
let caret_code  : int = 0x5E  // '^'

let char_at_code (input:string) (pos:nat) : int =
  if pos < fs_byte_length input then FStar.Char.int_of_char (fs_byte_index input pos)
  else -1

// Whitespace: space, tab, LF, CR — the fixtures use plain ASCII layout.
let is_fs_ws (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let skip_ws (input:string) (pos:nat) : nat =
  match ptake_while_pos is_fs_ws input pos with
  | ParseOk _ pos' -> pos'
  | ParseFail _ fpos -> fpos

// Identifier characters: used both for keywords (Prefix, Ontology, ...)
// and for PNAME_NS / PN_LOCAL segments of abbreviated IRIs. Kept to the
// ASCII subset the vendored fixtures actually use (rule: general grammar
// over this alphabet, not a per-fixture whitelist).
let is_ident_char (c:FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  (code >= 0x30 && code <= 0x39) ||  // 0-9
  (code >= 0x41 && code <= 0x5A) ||  // A-Z
  (code >= 0x61 && code <= 0x7A) ||  // a-z
  code = 0x5F || code = 0x2D        // '_' '-'

// try_match_word: read a maximal identifier run at pos and compare it
// against `kw`. Maximal munch means a longer identifier sharing `kw` as
// a prefix (there are none among our keywords, but this keeps the rule
// general) never falsely matches.
let try_match_word (input:string) (pos:nat) (kw:string) : option nat =
  match ptake_while1_pos is_ident_char input pos with
  | ParseFail _ _ -> None
  | ParseOk w pos' -> if w = kw then Some pos' else None

(* ------------------------------------------------------------------ *)
(* IRI scanning: <full IRI> or prefixed-name curies                    *)
(* ------------------------------------------------------------------ *)

let rec scan_angle_iri_end (input:string) (pos:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = fs_byte_length input in
    if pos >= len then None
    else
      let code = char_at_code input pos in
      if code = rangle_code then Some pos
      else scan_angle_iri_end input (pos + 1) (fuel - 1)

// Scans from just after the opening '<'. Returns (content, pos-after-'>').
let scan_angle_iri (input:string) (start:nat) (fuel:nat) : option (string & nat) =
  match scan_angle_iri_end input start fuel with
  | None -> None
  | Some gt_pos ->
    if gt_pos >= start then Some (fs_byte_sub input start (gt_pos - start), gt_pos + 1)
    else None

let rec lookup_prefix (prefixes:list (string & string)) (pfx:string) : option string =
  match prefixes with
  | [] -> None
  | (p, ns) :: rest -> if p = pfx then Some ns else lookup_prefix rest pfx

// PNAME_NS ':' PN_LOCAL, e.g. ":a" (empty prefix) or "xsd:integer".
let parse_curie (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (wf_iri & nat) =
  match ptake_while_pos is_ident_char input pos with
  | ParseFail _ _ -> None
  | ParseOk pfx pos1 ->
    if char_at_code input pos1 <> colon_code then None
    else
      let pos2 = pos1 + 1 in
      match ptake_while1_pos is_ident_char input pos2 with
      | ParseFail _ _ -> None
      | ParseOk local pos3 ->
        (match lookup_prefix prefixes pfx with
         | None -> None
         | Some ns ->
           let full = String.concat "" [ns; local] in
           if is_iri full then Some (full, pos3) else None)

let parse_fs_iri (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (wf_iri & nat) =
  if char_at_code input pos = langle_code then
    (match scan_angle_iri input (pos + 1) (fs_byte_length input - pos) with
     | None -> None
     | Some (s, pos') -> if is_iri s then Some (s, pos') else None)
  else
    parse_curie prefixes input pos

(* ------------------------------------------------------------------ *)
(* Literal scanning: "lexical"^^datatype-IRI (no plain/lang literals    *)
(* appear in the target fixtures — every literal carries a datatype).   *)
(* ------------------------------------------------------------------ *)

let rec scan_quote_end (input:string) (pos:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let len = fs_byte_length input in
    if pos >= len then None
    else
      let code = char_at_code input pos in
      if code = quote_code then Some pos
      else scan_quote_end input (pos + 1) (fuel - 1)

let parse_fs_literal (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (wf_literal & nat) =
  if char_at_code input pos <> quote_code then None
  else
    match scan_quote_end input (pos + 1) (fs_byte_length input - pos) with
    | None -> None
    | Some end_pos ->
      if end_pos < pos + 1 then None
      else
        let lexical = fs_byte_sub input (pos + 1) (end_pos - (pos + 1)) in
        let pos1 = skip_ws input (end_pos + 1) in
        if char_at_code input pos1 = caret_code && char_at_code input (pos1 + 1) = caret_code
        then
          (match parse_fs_iri prefixes input (pos1 + 2) with
           | None -> None
           | Some (dt, pos2) ->
             let lit : literal = { lexical_form = lexical; datatype = dt; lang_tag = None; direction = None } in
             if literal_wf lit then Some (lit, pos2) else None)
        else None

(* ------------------------------------------------------------------ *)
(* OWL IRI constants not already reachable via `open RDF.Graph.        *)
(* Executable`'s `include RDFS.Closure` / `include OWL.Closure` chain.  *)
(* Local to this file, same pattern OWL.QueryRewrite.fst uses for its   *)
(* own file-local extras (acknowledged duplication wart — see           *)
(* CLAUDE.md's "Known sound-but-narrow rewrites"; promoting all of these*)
(* to a shared OWL.Vocabulary.fst is issue #209's still-open checklist  *)
(* item, not part of this module's scope).                              *)
(* ------------------------------------------------------------------ *)

let owl_onDatatype_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onDatatype");
  "http://www.w3.org/2002/07/owl#onDatatype"

let owl_withRestrictions_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#withRestrictions");
  "http://www.w3.org/2002/07/owl#withRestrictions"

let owl_datatypeComplementOf_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#datatypeComplementOf");
  "http://www.w3.org/2002/07/owl#datatypeComplementOf"

let owl_NegativePropertyAssertion_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#NegativePropertyAssertion");
  "http://www.w3.org/2002/07/owl#NegativePropertyAssertion"

// owl:onDataRange — the OWL 2 Mapping to RDF Graphs predicate that binds
// a DATA-range filler to a qualified cardinality restriction, exactly as
// owl:onClass binds a class filler to an object one. The cardinality
// predicates themselves (owl:cardinality, owl:qualifiedCardinality, ...)
// already arrive through RDF.Graph.Executable's `include OWL.Closure`.
let owl_onDataRange_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onDataRange");
  "http://www.w3.org/2002/07/owl#onDataRange"

// A class-expression / data-range term is always T_IRI or T_BNode
// (never T_Literal — no production below ever returns a literal as a
// class-expression or data-range term), so this conversion to the
// strictly-smaller `subject` type is total over the terms this module
// actually constructs. Returns `None` only for the T_Literal case,
// which no caller here can reach.
let term_to_subject (t:rdf_term) : option subject =
  match t with
  | T_IRI i -> Some (S_IRI i)
  | T_BNode b -> Some (S_BNode b)
  | T_Literal _ -> None
  // No production here ever returns a triple term; object-only anyway.
  | T_TripleTerm _ _ _ -> None

(* ------------------------------------------------------------------ *)
(* Prefix( pfx = <IRI> ) — zero or more, collected before Ontology(...) *)
(* ------------------------------------------------------------------ *)

let rec parse_prefixes_acc
    (input:string) (pos:nat) (acc:list (string & string)) (fuel:nat)
  : Tot (option (list (string & string) & nat)) (decreases fuel) =
  if fuel = 0 then Some (acc, pos)
  else
    let fuel1 : nat = fuel - 1 in
    let pos0 = skip_ws input pos in
    match try_match_word input pos0 "Prefix" with
    | None -> Some (acc, pos0)
    | Some pos1 ->
      let pos2 = skip_ws input pos1 in
      if char_at_code input pos2 <> lparen_code then None
      else
        let pos3 = skip_ws input (pos2 + 1) in
        match ptake_while_pos is_ident_char input pos3 with
        | ParseFail _ _ -> None
        | ParseOk pfx pos4 ->
          if char_at_code input pos4 <> colon_code then None
          else
            let pos5 = skip_ws input (pos4 + 1) in
            if char_at_code input pos5 <> eq_code then None
            else
              let pos6 = skip_ws input (pos5 + 1) in
              if char_at_code input pos6 <> langle_code then None
              else
                match scan_angle_iri input (pos6 + 1) (fs_byte_length input - pos6) with
                | None -> None
                | Some (ns, pos7) ->
                  let pos8 = skip_ws input pos7 in
                  if char_at_code input pos8 <> rparen_code then None
                  else parse_prefixes_acc input (pos8 + 1) ((pfx, ns) :: acc) fuel1

(* ------------------------------------------------------------------ *)
(* Declaration(EntityKind(IRI))                                        *)
(* ------------------------------------------------------------------ *)

let parse_declaration
    (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (triple & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    let entity_kind : option (nat & wf_iri) =
      match try_match_word input pos2 "ObjectProperty" with
      | Some p -> Some (p, owl_ObjectProperty)
      | None ->
        match try_match_word input pos2 "DataProperty" with
        | Some p -> Some (p, owl_DatatypeProperty)
        | None ->
          match try_match_word input pos2 "NamedIndividual" with
          | Some p -> Some (p, owl_NamedIndividual)
          | None ->
            match try_match_word input pos2 "Class" with
            | Some p -> Some (p, owl_Class)
            | None -> None
    in
    match entity_kind with
    | None -> None
    | Some (pos3, type_iri) ->
      let pos4 = skip_ws input pos3 in
      if char_at_code input pos4 <> lparen_code then None
      else
        let pos5 = skip_ws input (pos4 + 1) in
        match parse_fs_iri prefixes input pos5 with
        | None -> None
        | Some (iri, pos6) ->
          let pos7 = skip_ws input pos6 in
          if char_at_code input pos7 <> rparen_code then None  // close EntityKind(...)
          else
            let pos8 = skip_ws input (pos7 + 1) in
            if char_at_code input pos8 <> rparen_code then None  // close Declaration(...)
            else Some ({ s = S_IRI iri; p = rdf_type; o = T_IRI type_iri }, pos8 + 1)

(* ------------------------------------------------------------------ *)
(* Unary "type" axioms: TransitiveObjectProperty(IRI), FunctionalData-  *)
(* Property(IRI) — both map to `IRI rdf:type <marker>`.                *)
(* ------------------------------------------------------------------ *)

let parse_unary_type_axiom
    (prefixes:list (string & string)) (input:string) (pos:nat) (type_iri:wf_iri)
  : option (triple & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (iri, pos3) ->
      let pos4 = skip_ws input pos3 in
      if char_at_code input pos4 <> rparen_code then None
      else Some ({ s = S_IRI iri; p = rdf_type; o = T_IRI type_iri }, pos4 + 1)

(* ------------------------------------------------------------------ *)
(* DataPropertyRange(IRI IRI)                                          *)
(* ------------------------------------------------------------------ *)

let parse_data_property_range
    (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (triple & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (prop, pos3) ->
      let pos4 = skip_ws input pos3 in
      match parse_fs_iri prefixes input pos4 with
      | None -> None
      | Some (dt, pos5) ->
        let pos6 = skip_ws input pos5 in
        if char_at_code input pos6 <> rparen_code then None
        else Some ({ s = S_IRI prop; p = rdfs_range; o = T_IRI dt }, pos6 + 1)

(* ------------------------------------------------------------------ *)
(* DataPropertyAssertion(IRI IRI Literal)                               *)
(* ------------------------------------------------------------------ *)

let parse_data_property_assertion
    (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (triple & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (prop, pos3) ->
      let pos4 = skip_ws input pos3 in
      match parse_fs_iri prefixes input pos4 with
      | None -> None
      | Some (ind, pos5) ->
        let pos6 = skip_ws input pos5 in
        match parse_fs_literal prefixes input pos6 with
        | None -> None
        | Some (lit, pos7) ->
          let pos8 = skip_ws input pos7 in
          if char_at_code input pos8 <> rparen_code then None
          else Some ({ s = S_IRI ind; p = prop; o = T_Literal lit }, pos8 + 1)

(* ------------------------------------------------------------------ *)
(* Literal lists / facet lists — shared list-building helpers for       *)
(* DataOneOf and DatatypeRestriction below. Same rdf:first/rdf:rest     *)
(* list-of-fresh-bnodes shape as `parse_sub_object_property_of`'s       *)
(* 2-element chain, generalized to n elements and structurally          *)
(* decreasing on the input list (`Tot`, no fuel parameter needed).      *)
(* ------------------------------------------------------------------ *)

let rec parse_literal_list_acc
    (prefixes:list (string & string)) (input:string) (pos:nat)
    (acc:list wf_literal) (fuel:nat)
  : Tot (option (list wf_literal & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel1 : nat = fuel - 1 in
    let pos0 = skip_ws input pos in
    if char_at_code input pos0 = rparen_code then
      (if List.Tot.length acc = 0 then None  // DataOneOf requires >= 1 literal
       else Some (List.Tot.rev acc, pos0))
    else
      match parse_fs_literal prefixes input pos0 with
      | None -> None
      | Some (lit, pos1) -> parse_literal_list_acc prefixes input pos1 (lit :: acc) fuel1

let rec build_literal_list (lits:list wf_literal) (bc:nat)
  : Tot (list triple & rdf_term & nat) (decreases lits) =
  match lits with
  | [] -> ([], T_IRI rdf_nil_iri, bc)
  | l :: rest ->
    let (rest_triples, rest_term, bc1) = build_literal_list rest bc in
    let node_label = String.concat "" ["owlfs_lst"; string_of_int bc1] in
    let t_first : triple = { s = S_BNode node_label; p = rdf_first; o = T_Literal l } in
    let t_rest  : triple = { s = S_BNode node_label; p = rdf_rest;  o = rest_term } in
    (t_first :: t_rest :: rest_triples, T_BNode node_label, bc1 + 1)

let rec parse_facet_list_acc
    (prefixes:list (string & string)) (input:string) (pos:nat)
    (acc:list (wf_iri & wf_literal)) (fuel:nat)
  : Tot (option (list (wf_iri & wf_literal) & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel1 : nat = fuel - 1 in
    let pos0 = skip_ws input pos in
    if char_at_code input pos0 = rparen_code then
      (if List.Tot.length acc = 0 then None  // DatatypeRestriction requires >= 1 facet pair
       else Some (List.Tot.rev acc, pos0))
    else
      match parse_fs_iri prefixes input pos0 with
      | None -> None
      | Some (facet, pos1) ->
        let pos2 = skip_ws input pos1 in
        match parse_fs_literal prefixes input pos2 with
        | None -> None
        | Some (lit, pos3) ->
          parse_facet_list_acc prefixes input pos3 ((facet, lit) :: acc) fuel1

// Each (facet, value) pair becomes its own bnode `_:f <facet> value`
// (no rdf:type marker — per the OWL 2 Mapping to RDF Graphs spec, a
// facet-restriction node carries exactly one triple), collected into
// an rdf:first/rdf:rest list. Two fresh bnode ids per element (one for
// the facet node, one for the list cell), threaded the same way
// `parse_sub_object_property_of` threads its 2-per-chain-link ids.
let rec build_facet_list (facets:list (wf_iri & wf_literal)) (bc:nat)
  : Tot (list triple & rdf_term & nat) (decreases facets) =
  match facets with
  | [] -> ([], T_IRI rdf_nil_iri, bc)
  | (facet, lit) :: rest ->
    let (rest_triples, rest_term, bc1) = build_facet_list rest bc in
    let fnode_label = String.concat "" ["owlfs_facet"; string_of_int bc1] in
    let vnode_label = String.concat "" ["owlfs_flst"; string_of_int (bc1 + 1)] in
    let t_val   : triple = { s = S_BNode fnode_label; p = facet;    o = T_Literal lit } in
    let t_first : triple = { s = S_BNode vnode_label; p = rdf_first; o = T_BNode fnode_label } in
    let t_rest  : triple = { s = S_BNode vnode_label; p = rdf_rest;  o = rest_term } in
    (t_val :: t_first :: t_rest :: rest_triples, T_BNode vnode_label, bc1 + 2)

(* ------------------------------------------------------------------ *)
(* Class expressions and data ranges — mutually recursive, fuel-bounded *)
(* by remaining input length (never by the outer axiom-loop fuel; a     *)
(* generous per-call budget since nesting depth is trivially bounded by *)
(* input length — every level consumes at least "X(" before recursing). *)
(*                                                                      *)
(*   ClassExpr ::= IRI | DataHasValue(P Lit)                            *)
(*              |  DataSomeValuesFrom(P DataRange)                      *)
(*              |  DataAllValuesFrom(P DataRange)                       *)
(*              |  ObjectComplementOf(ClassExpr)                        *)
(*   DataRange ::= IRI | DataOneOf(Lit+) | DataComplementOf(DataRange)  *)
(*              |  DatatypeRestriction(IRI (IRI Lit)+)                  *)
(*                                                                      *)
(* Each production returns (term-denoting-the-expression, triples that  *)
(* define it, position after the closing ')', updated bnode counter).   *)
(* Per the OWL 2 Mapping to RDF Graphs spec's per-expression tables.    *)
(* ------------------------------------------------------------------ *)

// DataHasValue(P Lit) -> _:x rdf:type owl:Restriction ;
//                          owl:onProperty P ; owl:hasValue Lit .
// Not part of the class-expr/data-range mutual-recursion group below
// (it never recurses into either), so it is a plain non-recursive
// `let`, defined first so `parse_class_expr` can call it.
let parse_data_has_value_expr
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (rdf_term & list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (prop, pos3) ->
      let pos4 = skip_ws input pos3 in
      match parse_fs_literal prefixes input pos4 with
      | None -> None
      | Some (lit, pos5) ->
        let pos6 = skip_ws input pos5 in
        if char_at_code input pos6 <> rparen_code then None
        else
          let bnode_label = String.concat "" ["owlfs_restr"; string_of_int bc] in
          let restr = S_BNode bnode_label in
          let t1 : triple = { s = restr; p = rdf_type; o = T_IRI owl_Restriction_iri } in
          let t2 : triple = { s = restr; p = owl_onProperty_iri; o = T_IRI prop } in
          let t3 : triple = { s = restr; p = owl_hasValue_iri; o = T_Literal lit } in
          Some (T_BNode bnode_label, [t1; t2; t3], pos6 + 1, bc + 1)

// A bare non-negative decimal integer, the `nonNegativeInteger` of the
// OWL 2 Functional-Style Syntax cardinality productions (written
// unquoted and untyped there, unlike every literal this module's
// `parse_fs_literal` handles). Consumes a maximal ASCII digit run and
// returns its value plus the position after it; `None` when there is no
// digit at `pos`, so a malformed cardinality drops the whole axiom
// rather than guessing a count.
let rec scan_fs_digits (input:string) (pos:nat) (acc:nat) (seen:nat) (budget:nat)
  : Tot (option (nat & nat)) (decreases budget) =
  if budget = 0 then (if seen = 0 then None else Some (acc, pos))
  else
    let code = char_at_code input pos in
    if code >= 48 && code <= 57
    then scan_fs_digits input (pos + 1) (op_Multiply acc 10 + (code - 48)) (seen + 1) (budget - 1)
    else (if seen = 0 then None else Some (acc, pos))

let parse_fs_nonneg_int (input:string) (pos:nat) : option (nat & nat) =
  let p = skip_ws input pos in
  scan_fs_digits input p 0 0 (fs_byte_length input + 1)

// The cardinality value as the xsd:nonNegativeInteger literal the OWL 2
// Mapping to RDF Graphs writes on the restriction node.
let fs_cardinality_literal (n:nat) : option wf_literal =
  let lit : literal = { lexical_form = string_of_int n; datatype = xsd_nonNegativeInteger;
                        lang_tag = None; direction = None } in
  if literal_wf lit then Some lit else None

// Deterministic bnode label for a cardinality restriction node, in the
// same "owlfs_<kind><counter>" shape every other production here uses.
let fs_card_bnode_label (bcx:nat) : string =
  String.concat "" ["owlfs_cardrestr"; string_of_int bcx]

// DataOneOf(v1..vn) -> _:x rdf:type rdfs:Datatype ; owl:oneOf T([v1..vn]) .
// Also a leaf (calls only the standalone list-accumulator above, never
// recurses into the class-expr/data-range group) — plain `let`,
// defined ahead of `parse_data_range` for the same reason.
let parse_data_one_of
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (rdf_term & list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_literal_list_acc prefixes input pos2 [] (fs_byte_length input + 1) with
    | None -> None
    | Some (lits, pos3) ->
      let pos4 = skip_ws input pos3 in
      if char_at_code input pos4 <> rparen_code then None
      else
        let (list_triples, list_head, bc1) = build_literal_list lits bc in
        let dt_label = String.concat "" ["owlfs_dtoneof"; string_of_int bc1] in
        let dt = S_BNode dt_label in
        let t1 : triple = { s = dt; p = rdf_type; o = T_IRI rdfs_Datatype } in
        let t2 : triple = { s = dt; p = owl_oneOf_iri; o = list_head } in
        Some (T_BNode dt_label, list_triples @ [t1; t2], pos4 + 1, bc1 + 1)

// DatatypeRestriction(DT F1 v1 F2 v2 ...) ->
//   _:x rdf:type rdfs:Datatype ; owl:onDatatype DT ;
//   owl:withRestrictions T([{F1:v1} {F2:v2} ...]) .
// Also a leaf (calls only the standalone facet-list-accumulator above,
// never the mutual group) — plain `let`.
let parse_datatype_restriction
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (rdf_term & list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (base_dt, pos3) ->
      match parse_facet_list_acc prefixes input pos3 [] (fs_byte_length input + 1) with
      | None -> None
      | Some (facets, pos4) ->
        let pos5 = skip_ws input pos4 in
        if char_at_code input pos5 <> rparen_code then None
        else
          let (facet_triples, facet_head, bc1) = build_facet_list facets bc in
          let dt_label = String.concat "" ["owlfs_dtrestr"; string_of_int bc1] in
          let dt = S_BNode dt_label in
          let t1 : triple = { s = dt; p = rdf_type; o = T_IRI rdfs_Datatype } in
          let t2 : triple = { s = dt; p = owl_onDatatype_iri; o = T_IRI base_dt } in
          let t3 : triple = { s = dt; p = owl_withRestrictions_iri; o = facet_head } in
          Some (T_BNode dt_label, facet_triples @ [t1; t2; t3], pos5 + 1, bc1 + 1)

(* ------------------------------------------------------------------ *)
(* The genuine mutual-recursion cycle: parse_class_expr <->             *)
(* parse_data_range (via parse_data_values_from / parse_object_        *)
(* complement_of / parse_data_complement_of). All five members share    *)
(* the `fuel` decreases measure; the three leaves above are called      *)
(* from inside this group but are not themselves part of it.            *)
(* ------------------------------------------------------------------ *)

let rec parse_class_expr
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat) (fuel:nat)
  : Tot (option (rdf_term & list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel1 : nat = fuel - 1 in
    let pos0 = skip_ws input pos in
    match parse_fs_iri prefixes input pos0 with
    | Some (iri, pos1) -> Some (T_IRI iri, [], pos1, bc)
    | None ->
    match try_match_word input pos0 "DataHasValue" with
    | Some pos1 -> parse_data_has_value_expr prefixes input pos1 bc
    | None ->
    match try_match_word input pos0 "DataSomeValuesFrom" with
    | Some pos1 -> parse_data_values_from prefixes input pos1 bc fuel1 owl_someValuesFrom_iri
    | None ->
    match try_match_word input pos0 "DataAllValuesFrom" with
    | Some pos1 -> parse_data_values_from prefixes input pos1 bc fuel1 owl_allValuesFrom_iri
    | None ->
    match try_match_word input pos0 "ObjectComplementOf" with
    | Some pos1 -> parse_object_complement_of prefixes input pos1 bc fuel1
    | None ->
    // Data{Exact,Min,Max}Cardinality(n DP [DR]). Each is passed the pair
    // of predicates the OWL 2 Mapping to RDF Graphs uses for it: the
    // QUALIFIED one when a data range follows the property, the plain
    // one when it does not.
    match try_match_word input pos0 "DataExactCardinality" with
    | Some pos1 ->
      parse_data_cardinality prefixes input pos1 bc fuel1
        owl_qualifiedCardinality_iri owl_cardinality_iri
    | None ->
    match try_match_word input pos0 "DataMinCardinality" with
    | Some pos1 ->
      parse_data_cardinality prefixes input pos1 bc fuel1
        owl_minQualifiedCardinality_iri owl_minCardinality_iri
    | None ->
    match try_match_word input pos0 "DataMaxCardinality" with
    | Some pos1 ->
      parse_data_cardinality prefixes input pos1 bc fuel1
        owl_maxQualifiedCardinality_iri owl_maxCardinality_iri
    | None -> None

// Data{Exact,Min,Max}Cardinality(n DP)     ->
//   _:x rdf:type owl:Restriction ; owl:onProperty DP ;
//       owl:{,min,max}Cardinality "n"^^xsd:nonNegativeInteger .
// Data{Exact,Min,Max}Cardinality(n DP DR)  ->
//   _:x rdf:type owl:Restriction ; owl:onProperty DP ;
//       owl:{,min,max}QualifiedCardinality "n"^^xsd:nonNegativeInteger ;
//       owl:onDataRange T(DR) .
// (OWL 2 Mapping to RDF Graphs, the Data Property Cardinality
// Restrictions rows.) The data range is OPTIONAL: after the property we
// try `parse_data_range`, and a failure means the unqualified form, so
// the closing ')' must then follow immediately.
and parse_data_cardinality
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat) (fuel:nat)
    (qual_iri:wf_iri) (plain_iri:wf_iri)
  : Tot (option (rdf_term & list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel1 : nat = fuel - 1 in
    let pos1 = skip_ws input pos in
    if char_at_code input pos1 <> lparen_code then None
    else
      match parse_fs_nonneg_int input (pos1 + 1) with
      | None -> None
      | Some (card, pos2) ->
        let pos3 = skip_ws input pos2 in
        match parse_fs_iri prefixes input pos3 with
        | None -> None
        | Some (prop, pos4) ->
          match fs_cardinality_literal card with
          | None -> None
          | Some card_lit ->
            let pos5 = skip_ws input pos4 in
            (match parse_data_range prefixes input pos5 bc fuel1 with
             | Some (dr_term, dr_triples, pos6, bc1) ->
               let pos7 = skip_ws input pos6 in
               if char_at_code input pos7 <> rparen_code then None
               else
                 let lbl = fs_card_bnode_label bc1 in
                 let restr = S_BNode lbl in
                 let t1 : triple = { s = restr; p = rdf_type; o = T_IRI owl_Restriction_iri } in
                 let t2 : triple = { s = restr; p = owl_onProperty_iri; o = T_IRI prop } in
                 let t3 : triple = { s = restr; p = qual_iri; o = T_Literal card_lit } in
                 let t4 : triple = { s = restr; p = owl_onDataRange_iri; o = dr_term } in
                 Some (T_BNode lbl, dr_triples @ [t1; t2; t3; t4], pos7 + 1, bc1 + 1)
             | None ->
               // Unqualified form: nothing but ')' may follow the property.
               if char_at_code input pos5 <> rparen_code then None
               else
                 let lbl = fs_card_bnode_label bc in
                 let restr = S_BNode lbl in
                 let t1 : triple = { s = restr; p = rdf_type; o = T_IRI owl_Restriction_iri } in
                 let t2 : triple = { s = restr; p = owl_onProperty_iri; o = T_IRI prop } in
                 let t3 : triple = { s = restr; p = plain_iri; o = T_Literal card_lit } in
                 Some (T_BNode lbl, [t1; t2; t3], pos5 + 1, bc + 1))

// DataSomeValuesFrom(P DR) / DataAllValuesFrom(P DR) ->
//   _:x rdf:type owl:Restriction ; owl:onProperty P ;
//   owl:someValuesFrom|owl:allValuesFrom T(DR) .
// `rel_iri` picks which of the two relation IRIs the caller wants.
and parse_data_values_from
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat) (fuel:nat)
    (rel_iri:wf_iri)
  : Tot (option (rdf_term & list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let pos1 = skip_ws input pos in
    if char_at_code input pos1 <> lparen_code then None
    else
      let pos2 = skip_ws input (pos1 + 1) in
      match parse_fs_iri prefixes input pos2 with
      | None -> None
      | Some (prop, pos3) ->
        let pos4 = skip_ws input pos3 in
        match parse_data_range prefixes input pos4 bc (fuel - 1) with
        | None -> None
        | Some (dr_term, dr_triples, pos5, bc1) ->
          let pos6 = skip_ws input pos5 in
          if char_at_code input pos6 <> rparen_code then None
          else
            let bnode_label = String.concat "" ["owlfs_restr"; string_of_int bc1] in
            let restr = S_BNode bnode_label in
            let t1 : triple = { s = restr; p = rdf_type; o = T_IRI owl_Restriction_iri } in
            let t2 : triple = { s = restr; p = owl_onProperty_iri; o = T_IRI prop } in
            let t3 : triple = { s = restr; p = rel_iri; o = dr_term } in
            Some (T_BNode bnode_label, dr_triples @ [t1; t2; t3], pos6 + 1, bc1 + 1)

// ObjectComplementOf(CE) -> _:x rdf:type owl:Class ; owl:complementOf T(CE) .
and parse_object_complement_of
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat) (fuel:nat)
  : Tot (option (rdf_term & list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let pos1 = skip_ws input pos in
    if char_at_code input pos1 <> lparen_code then None
    else
      let pos2 = skip_ws input (pos1 + 1) in
      match parse_class_expr prefixes input pos2 bc (fuel - 1) with
      | None -> None
      | Some (ce_term, ce_triples, pos3, bc1) ->
        let pos4 = skip_ws input pos3 in
        if char_at_code input pos4 <> rparen_code then None
        else
          let bnode_label = String.concat "" ["owlfs_comp"; string_of_int bc1] in
          let comp = S_BNode bnode_label in
          let t1 : triple = { s = comp; p = rdf_type; o = T_IRI owl_Class } in
          let t2 : triple = { s = comp; p = owl_complementOf_iri; o = ce_term } in
          Some (T_BNode bnode_label, ce_triples @ [t1; t2], pos4 + 1, bc1 + 1)

and parse_data_range
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat) (fuel:nat)
  : Tot (option (rdf_term & list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel1 : nat = fuel - 1 in
    let pos0 = skip_ws input pos in
    match parse_fs_iri prefixes input pos0 with
    | Some (iri, pos1) -> Some (T_IRI iri, [], pos1, bc)
    | None ->
    match try_match_word input pos0 "DataOneOf" with
    | Some pos1 -> parse_data_one_of prefixes input pos1 bc
    | None ->
    match try_match_word input pos0 "DataComplementOf" with
    | Some pos1 -> parse_data_complement_of prefixes input pos1 bc fuel1
    | None ->
    match try_match_word input pos0 "DatatypeRestriction" with
    | Some pos1 -> parse_datatype_restriction prefixes input pos1 bc
    | None -> None

// DataComplementOf(DR) -> _:x rdf:type rdfs:Datatype ;
//                           owl:datatypeComplementOf T(DR) .
and parse_data_complement_of
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat) (fuel:nat)
  : Tot (option (rdf_term & list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let pos1 = skip_ws input pos in
    if char_at_code input pos1 <> lparen_code then None
    else
      let pos2 = skip_ws input (pos1 + 1) in
      match parse_data_range prefixes input pos2 bc (fuel - 1) with
      | None -> None
      | Some (dr_term, dr_triples, pos3, bc1) ->
        let pos4 = skip_ws input pos3 in
        if char_at_code input pos4 <> rparen_code then None
        else
          let dt_label = String.concat "" ["owlfs_dtcomp"; string_of_int bc1] in
          let dt = S_BNode dt_label in
          let t1 : triple = { s = dt; p = rdf_type; o = T_IRI rdfs_Datatype } in
          let t2 : triple = { s = dt; p = owl_datatypeComplementOf_iri; o = dr_term } in
          Some (T_BNode dt_label, dr_triples @ [t1; t2], pos4 + 1, bc1 + 1)

(* ------------------------------------------------------------------ *)
(* SubClassOf(ClassExpr ClassExpr) -> T(CE1) rdfs:subClassOf T(CE2) .   *)
(* ------------------------------------------------------------------ *)

let parse_subclass_of
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    let fuel = fs_byte_length input + 1 in
    match parse_class_expr prefixes input pos2 bc fuel with
    | None -> None
    | Some (ce1_term, ce1_triples, pos3, bc1) ->
      let pos4 = skip_ws input pos3 in
      match parse_class_expr prefixes input pos4 bc1 fuel with
      | None -> None
      | Some (ce2_term, ce2_triples, pos5, bc2) ->
        let pos6 = skip_ws input pos5 in
        if char_at_code input pos6 <> rparen_code then None
        else
          match term_to_subject ce1_term with
          | None -> None
          | Some ce1_subj ->
            let t_sco : triple = { s = ce1_subj; p = rdfs_subClassOf; o = ce2_term } in
            Some (ce1_triples @ ce2_triples @ [t_sco], pos6 + 1, bc2)

(* ------------------------------------------------------------------ *)
(* ClassAssertion(ClassExpr IRI) -> IRI rdf:type T(ClassExpr) .         *)
(* Generalizes the original DataHasValue-only shape to any ClassExpr    *)
(* this module's grammar covers (named class, DataHasValue,             *)
(* DataSomeValuesFrom/DataAllValuesFrom, ObjectComplementOf).           *)
(* ------------------------------------------------------------------ *)

let parse_class_assertion
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_class_expr prefixes input pos2 bc (fs_byte_length input + 1) with
    | None -> None
    | Some (ce_term, ce_triples, pos3, bc1) ->
      let pos4 = skip_ws input pos3 in
      match parse_fs_iri prefixes input pos4 with
      | None -> None
      | Some (ind, pos5) ->
        let pos6 = skip_ws input pos5 in
        if char_at_code input pos6 <> rparen_code then None
        else
          let t_assert : triple = { s = S_IRI ind; p = rdf_type; o = ce_term } in
          Some (ce_triples @ [t_assert], pos6 + 1, bc1)

(* ------------------------------------------------------------------ *)
(* DisjointDataProperties(IRI IRI) -> IRI1 owl:propertyDisjointWith     *)
(* IRI2 . Only the exactly-2-argument shape is supported (the fixtures  *)
(* that need this axiom all have exactly 2); per the OWL 2 Mapping to   *)
(* RDF Graphs spec, n=2 is the direct-triple case, n>2 needs an          *)
(* owl:AllDisjointProperties/owl:members encoding this module does not  *)
(* produce.                                                              *)
(* ------------------------------------------------------------------ *)

let parse_disjoint_data_properties
    (prefixes:list (string & string)) (input:string) (pos:nat)
  : option (triple & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (p1, pos3) ->
      let pos4 = skip_ws input pos3 in
      match parse_fs_iri prefixes input pos4 with
      | None -> None
      | Some (p2, pos5) ->
        let pos6 = skip_ws input pos5 in
        if char_at_code input pos6 <> rparen_code then None  // exactly 2 args
        else Some ({ s = S_IRI p1; p = owl_propertyDisjointWith; o = T_IRI p2 }, pos6 + 1)

(* ------------------------------------------------------------------ *)
(* NegativeDataPropertyAssertion(IRI IRI Literal) ->                    *)
(*   _:x rdf:type owl:NegativePropertyAssertion ;                       *)
(*   owl:sourceIndividual Ind ; owl:assertionProperty P ;                *)
(*   owl:targetValue Lit .                                              *)
(* ------------------------------------------------------------------ *)

let parse_negative_data_property_assertion
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match parse_fs_iri prefixes input pos2 with
    | None -> None
    | Some (prop, pos3) ->
      let pos4 = skip_ws input pos3 in
      match parse_fs_iri prefixes input pos4 with
      | None -> None
      | Some (ind, pos5) ->
        let pos6 = skip_ws input pos5 in
        match parse_fs_literal prefixes input pos6 with
        | None -> None
        | Some (lit, pos7) ->
          let pos8 = skip_ws input pos7 in
          if char_at_code input pos8 <> rparen_code then None
          else
            let bnode_label = String.concat "" ["owlfs_npa"; string_of_int bc] in
            let npa = S_BNode bnode_label in
            let t1 : triple = { s = npa; p = rdf_type; o = T_IRI owl_NegativePropertyAssertion_iri } in
            let t2 : triple = { s = npa; p = owl_sourceIndividual; o = T_IRI ind } in
            let t3 : triple = { s = npa; p = owl_assertionProperty; o = T_IRI prop } in
            let t4 : triple = { s = npa; p = owl_targetValue; o = T_Literal lit } in
            Some ([t1; t2; t3; t4], pos8 + 1, bc + 1)

(* ------------------------------------------------------------------ *)
(* SubObjectPropertyOf(ObjectPropertyChain(IRI IRI) IRI)                 *)
(*                                                                      *)
(* Only the 2-property-chain shape is supported (the one fixture that   *)
(* needs this axiom form — BJP-002's conclusion — has exactly 2). Per    *)
(* the OWL 2 Mapping to RDF Graphs spec, ObjectPropertyChain(P1 P2)      *)
(* becomes an rdf:first/rdf:rest list, bound to the super-property via   *)
(* owl:propertyChainAxiom.                                               *)
(* ------------------------------------------------------------------ *)

let parse_sub_object_property_of
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match try_match_word input pos2 "ObjectPropertyChain" with
    | None -> None
    | Some pos3 ->
      let pos4 = skip_ws input pos3 in
      if char_at_code input pos4 <> lparen_code then None
      else
        let pos5 = skip_ws input (pos4 + 1) in
        match parse_fs_iri prefixes input pos5 with
        | None -> None
        | Some (p1, pos6) ->
          let pos7 = skip_ws input pos6 in
          match parse_fs_iri prefixes input pos7 with
          | None -> None
          | Some (p2, pos8) ->
            let pos9 = skip_ws input pos8 in
            if char_at_code input pos9 <> rparen_code then None  // close ObjectPropertyChain(...)
            else
              let pos10 = skip_ws input (pos9 + 1) in
              match parse_fs_iri prefixes input pos10 with
              | None -> None
              | Some (q, pos11) ->
                let pos12 = skip_ws input pos11 in
                if char_at_code input pos12 <> rparen_code then None  // close SubObjectPropertyOf(...)
                else
                  let b1 = String.concat "" ["owlfs_chain"; string_of_int bc] in
                  let b2 = String.concat "" ["owlfs_chain"; string_of_int (bc + 1)] in
                  let t1 : triple = { s = S_BNode b1; p = rdf_first; o = T_IRI p1 } in
                  let t2 : triple = { s = S_BNode b1; p = rdf_rest;  o = T_BNode b2 } in
                  let t3 : triple = { s = S_BNode b2; p = rdf_first; o = T_IRI p2 } in
                  let t4 : triple = { s = S_BNode b2; p = rdf_rest;  o = T_IRI rdf_nil_iri } in
                  let t5 : triple = { s = S_IRI q; p = owl_propertyChainAxiom; o = T_BNode b1 } in
                  Some ([t1; t2; t3; t4; t5], pos12 + 1, bc + 2)

(* ------------------------------------------------------------------ *)
(* Ontology body: zero or more Declaration/Axiom forms until ')'.       *)
(* ------------------------------------------------------------------ *)

let rec parse_axioms_acc
    (prefixes:list (string & string))
    (input:string) (pos:nat) (bc:nat)
    (acc:list triple) (fuel:nat)
  : Tot (option (list triple & nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let fuel1 : nat = fuel - 1 in
    let pos0 = skip_ws input pos in
    if char_at_code input pos0 = rparen_code then
      Some (List.Tot.rev acc, pos0, bc)
    else
      match try_match_word input pos0 "Declaration" with
      | Some pos1 ->
        (match parse_declaration prefixes input pos1 with
         | None -> None
         | Some (t, pos2) -> parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
      | None ->
      match try_match_word input pos0 "TransitiveObjectProperty" with
      | Some pos1 ->
        (match parse_unary_type_axiom prefixes input pos1 owl_TransitiveProperty with
         | None -> None
         | Some (t, pos2) -> parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
      | None ->
      match try_match_word input pos0 "FunctionalDataProperty" with
      | Some pos1 ->
        (match parse_unary_type_axiom prefixes input pos1 owl_FunctionalProperty with
         | None -> None
         | Some (t, pos2) -> parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
      | None ->
      match try_match_word input pos0 "DataPropertyRange" with
      | Some pos1 ->
        (match parse_data_property_range prefixes input pos1 with
         | None -> None
         | Some (t, pos2) -> parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
      | None ->
      match try_match_word input pos0 "DataPropertyAssertion" with
      | Some pos1 ->
        (match parse_data_property_assertion prefixes input pos1 with
         | None -> None
         | Some (t, pos2) -> parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
      | None ->
      match try_match_word input pos0 "ClassAssertion" with
      | Some pos1 ->
        (match parse_class_assertion prefixes input pos1 bc with
         | None -> None
         | Some (ts, pos2, bc') -> parse_axioms_acc prefixes input pos2 bc' (List.Tot.rev_acc ts acc) fuel1)
      | None ->
      match try_match_word input pos0 "SubObjectPropertyOf" with
      | Some pos1 ->
        (match parse_sub_object_property_of prefixes input pos1 bc with
         | None -> None
         | Some (ts, pos2, bc') -> parse_axioms_acc prefixes input pos2 bc' (List.Tot.rev_acc ts acc) fuel1)
      | None ->
      match try_match_word input pos0 "SubClassOf" with
      | Some pos1 ->
        (match parse_subclass_of prefixes input pos1 bc with
         | None -> None
         | Some (ts, pos2, bc') -> parse_axioms_acc prefixes input pos2 bc' (List.Tot.rev_acc ts acc) fuel1)
      | None ->
      match try_match_word input pos0 "DisjointDataProperties" with
      | Some pos1 ->
        (match parse_disjoint_data_properties prefixes input pos1 with
         | None -> None
         | Some (t, pos2) -> parse_axioms_acc prefixes input pos2 bc (t :: acc) fuel1)
      | None ->
      match try_match_word input pos0 "NegativeDataPropertyAssertion" with
      | Some pos1 ->
        (match parse_negative_data_property_assertion prefixes input pos1 bc with
         | None -> None
         | Some (ts, pos2, bc') -> parse_axioms_acc prefixes input pos2 bc' (List.Tot.rev_acc ts acc) fuel1)
      | None -> None  // unknown construct — clean parse failure

(* ------------------------------------------------------------------ *)
(* Top-level entry point.                                              *)
(* ------------------------------------------------------------------ *)

let parse_functional_syntax (input:string) : option (list triple) =
  let len = fs_byte_length input in
  match parse_prefixes_acc input 0 [] (len + 1) with
  | None -> None
  | Some (prefixes, pos_after_prefixes) ->
    let pos1 = skip_ws input pos_after_prefixes in
    match try_match_word input pos1 "Ontology" with
    | None -> None
    | Some pos2 ->
      let pos3 = skip_ws input pos2 in
      if char_at_code input pos3 <> lparen_code then None
      else
        let pos4 = skip_ws input (pos3 + 1) in
        match parse_axioms_acc prefixes input pos4 0 [] (len + 1) with
        | None -> None
        | Some (triples, pos5, _bc) ->
          if char_at_code input pos5 = rparen_code then Some triples else None
