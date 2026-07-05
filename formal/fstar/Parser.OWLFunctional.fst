module Parser.OWLFunctional

(* ================================================================ *)
(* OWL 2 Functional-Syntax Parser — narrow subset, F*-verified        *)
(*                                                                    *)
(* Scope: docs/designissues/2026-07-05-owl-functional-syntax-plan.md. *)
(* This is NOT a general OWL 2 Functional Syntax parser. It covers    *)
(* exactly the grammar the 4 currently-skipped profile-RL.rdf catalog *)
(* entries need (1 PositiveEntailmentTest, 3 InconsistencyTest — see  *)
(* the design doc for the fixture inventory):                        *)
(*                                                                    *)
(*   Prefix( pfx = <IRI> )            zero or more, before Ontology   *)
(*   Ontology( Declaration/Axiom* )                                   *)
(*   Declaration(ObjectProperty(IRI))                                 *)
(*   Declaration(DataProperty(IRI))                                   *)
(*   Declaration(NamedIndividual(IRI))                                *)
(*   TransitiveObjectProperty(IRI)                                    *)
(*   FunctionalDataProperty(IRI)                                      *)
(*   DataPropertyRange(IRI IRI)                                       *)
(*   DataPropertyAssertion(IRI IRI Literal)                           *)
(*   ClassAssertion(DataHasValue(IRI Literal) IRI)                    *)
(*   SubObjectPropertyOf(ObjectPropertyChain(IRI IRI) IRI)             *)
(*                                                                    *)
(* Any other construct (class expressions, object-property            *)
(* expressions, annotations, other axiom kinds, chains of length != 2) *)
(* is a clean parse failure (`None`) — the caller (owl_runner.ml)      *)
(* treats that as "unsupported input syntax", the same honest skip     *)
(* it already reports today, never a silent wrong answer. No fixture-  *)
(* string special-casing: every production below is a general grammar  *)
(* rule, not a literal match on one test's text.                       *)
(*                                                                    *)
(* Axiom-to-triple mapping follows the OWL 2 Mapping to RDF Graphs     *)
(* spec's per-axiom / per-class-expression tables (e.g.                *)
(* TransitiveObjectProperty(:p) -> :p rdf:type owl:TransitiveProperty; *)
(* DataHasValue(P v) -> a fresh owl:Restriction bnode with              *)
(* owl:onProperty/owl:hasValue; ObjectPropertyChain(P1 P2) -> an        *)
(* rdf:first/rdf:rest list bound via owl:propertyChainAxiom). This is   *)
(* the real translation, not an ad-hoc shortcut — whether the existing  *)
(* OWL-RL closure in RDF.Graph.Executable.fst can already see through   *)
(* the Restriction/list encoding to detect a clash is a closure-        *)
(* completeness question, tracked separately (see the design doc's      *)
(* follow-up note on owl_rule_chain_to_transitive) and out of this       *)
(* module's territory: this file only produces triples, it never        *)
(* touches RDF.Graph.Executable.fst's rule set.                         *)
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
             let lit : literal = { lexical_form = lexical; datatype = dt; lang_tag = None } in
             if literal_wf lit then Some (lit, pos2) else None)
        else None

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
(* ClassAssertion(DataHasValue(IRI Literal) IRI)                        *)
(*                                                                      *)
(* Per the OWL 2 Mapping to RDF Graphs spec, DataHasValue(P v) is a      *)
(* class expression translated to a fresh owl:Restriction bnode:        *)
(*   _:x rdf:type owl:Restriction ; owl:onProperty P ; owl:hasValue v .  *)
(* and ClassAssertion(CE a) is `a rdf:type T(CE)`, so the four triples   *)
(* below are the real per-table translation, not a shortcut straight to  *)
(* a DataPropertyAssertion-shaped triple.                                *)
(* ------------------------------------------------------------------ *)

let parse_class_assertion
    (prefixes:list (string & string)) (input:string) (pos:nat) (bc:nat)
  : option (list triple & nat & nat) =
  let pos1 = skip_ws input pos in
  if char_at_code input pos1 <> lparen_code then None
  else
    let pos2 = skip_ws input (pos1 + 1) in
    match try_match_word input pos2 "DataHasValue" with
    | None -> None
    | Some pos3 ->
      let pos4 = skip_ws input pos3 in
      if char_at_code input pos4 <> lparen_code then None
      else
        let pos5 = skip_ws input (pos4 + 1) in
        match parse_fs_iri prefixes input pos5 with
        | None -> None
        | Some (prop, pos6) ->
          let pos7 = skip_ws input pos6 in
          match parse_fs_literal prefixes input pos7 with
          | None -> None
          | Some (lit, pos8) ->
            let pos9 = skip_ws input pos8 in
            if char_at_code input pos9 <> rparen_code then None  // close DataHasValue(...)
            else
              let pos10 = skip_ws input (pos9 + 1) in
              match parse_fs_iri prefixes input pos10 with
              | None -> None
              | Some (ind, pos11) ->
                let pos12 = skip_ws input pos11 in
                if char_at_code input pos12 <> rparen_code then None  // close ClassAssertion(...)
                else
                  let bnode_label = String.concat "" ["owlfs_restr"; string_of_int bc] in
                  let restr : subject = S_BNode bnode_label in
                  let t1 : triple = { s = restr; p = rdf_type; o = T_IRI owl_Restriction_iri } in
                  let t2 : triple = { s = restr; p = owl_onProperty_iri; o = T_IRI prop } in
                  let t3 : triple = { s = restr; p = owl_hasValue_iri; o = T_Literal lit } in
                  let t4 : triple = { s = S_IRI ind; p = rdf_type; o = T_BNode bnode_label } in
                  Some ([t1; t2; t3; t4], pos12 + 1, bc + 1)

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
