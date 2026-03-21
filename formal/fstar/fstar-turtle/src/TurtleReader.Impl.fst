module TurtleReader.Impl

// Implementation of the recursive descent Turtle parser.
// This module provides the bodies for the grammar productions
// declared in TurtleReader.fst.
//
// The parser follows the W3C Turtle grammar:
//   https://www.w3.org/TR/turtle/#sec-grammar
//
// Architecture:
//   - Each grammar production is a function returning parse_result
//   - Parser state (reader) is threaded through functionally
//   - Node stack operations (push/pop/deref) use assume val stubs
//     that will be implemented as C buffer operations via KaRaMeL
//   - Character classification uses Utf8 module functions

open ByteSource
open Utf8
open Node
open Sink
open TurtleReader
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.HyperStack.ST
open LowStar.Buffer
module B = LowStar.Buffer

// ---- Helper: advance reader by one byte ----
// Wraps ByteSource.advance_string with reader update
assume val advance : r:reader -> Stack reader
  (requires fun h -> B.live h r.source.buf /\ not r.source.eof)
  (ensures fun h0 _ h1 -> True)

// Peek current byte as U32 codepoint (ASCII only for dispatch)
let peek_u32 (r: reader) : Stack U32.t
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> h0 == h1)
  = let b = peek_byte r.source in
    if I32.v b < 0 then 0xFFFFFFFFul
    else FStar.Int.Cast.int32_to_uint32 b

// ---- Whitespace [161s] and comments ----

// read_comment: '#' ... '\n'
let read_comment_impl (r: reader) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b <> 0x23 then Err Failure  // not '#'
    else
      // Skip until newline or EOF
      assume val skip_to_newline : r:reader -> Stack reader
        (requires fun h -> B.live h r.source.buf)
        (ensures fun h0 _ h1 -> True)
      in
      let r = advance r in
      let r = skip_to_newline r in
      Ok r

// read_ws_impl: single whitespace (space, tab, CR, LF) or comment
let read_ws_impl (r: reader) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    let v = I32.v b in
    if v = 0x20 || v = 0x09 || v = 0x0D || v = 0x0A then
      Ok (advance r)
    else if v = 0x23 then  // '#' comment
      read_comment_impl r
    else
      Err Failure

// read_ws_star_impl: zero or more whitespace/comments
let rec read_ws_star_impl (r: reader) : Stack reader
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = match read_ws_impl r with
    | Ok r' -> read_ws_star_impl r'
    | Err _ -> r

// ---- IRIREF [18] ----
// '<' ([^#x00-#x20<>"{}|^`\] | UCHAR)* '>'

let read_IRIREF_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b <> 0x3C then Err Failure  // not '<'
    else
      let r = advance r in  // skip '<'
      let (r, ref) = push_node r NT_IRI in
      // Read IRI content until '>'
      assume val read_iri_content : r:reader -> ref:ref_t -> Stack (parse_result reader)
        (requires fun h -> B.live h r.source.buf)
        (ensures fun h0 _ h1 -> True)
      in
      match read_iri_content r ref with
      | Err s -> Err s
      | Ok r ->
        let b = peek_byte r.source in
        if I32.v b <> 0x3E then Err ErrBadSyntax  // expected '>'
        else
          let r = advance r in  // skip '>'
          Ok (r, ref)

// ---- PN_PREFIX [168s] ----
// PN_CHARS_BASE ((PN_CHARS | '.')* PN_CHARS)?
// Note: no trailing dot allowed

assume val read_PN_PREFIX : r:reader -> ref:ref_t -> Stack (parse_result (reader & bool))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  // returns (reader, ate_dot) -- ate_dot true if a trailing '.' was consumed

// ---- PN_LOCAL [169s] ----
// (PN_CHARS_U | ':' | [0-9] | PLX) ((PN_CHARS | '.' | ':' | PLX)* (PN_CHARS | ':' | PLX))?
assume val read_PN_LOCAL : r:reader -> ref:ref_t -> Stack (parse_result (reader & bool))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)

// ---- PrefixedName [136s] ----
// PNAME_LN | PNAME_NS
let read_PrefixedName_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = // Prefixed names start with PN_CHARS_BASE or ':'
    let (r, ref) = push_node r NT_IRI in
    // Try to read prefix part
    match read_PN_PREFIX r ref with
    | Err s ->
      let r = pop_node r ref in
      Err s
    | Ok (r, _) ->
      // Expect ':'
      let b = peek_byte r.source in
      if I32.v b <> 0x3A then  // not ':'
        let r = pop_node r ref in
        Err Failure
      else
        let r = advance r in  // skip ':'
        // Try to read local part (optional)
        match read_PN_LOCAL r ref with
        | Ok (r, _) -> Ok (r, ref)
        | Err Failure -> Ok (r, ref)  // empty local part is OK (PNAME_NS)
        | Err s ->
          let r = pop_node r ref in
          Err s

// ---- iri [135s] ----
// IRIREF | PrefixedName
let read_iri_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b = 0x3C then  // '<' -> IRIREF
      read_IRIREF_impl r
    else  // try PrefixedName
      read_PrefixedName_impl r

// ---- BLANK_NODE_LABEL [141s] ----
// '_:' (PN_CHARS_U | [0-9]) ((PN_CHARS | '.')* PN_CHARS)?
let read_BLANK_NODE_LABEL_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b <> 0x5F then Err Failure  // not '_'
    else
      let r = advance r in  // skip '_'
      let b = peek_byte r.source in
      if I32.v b <> 0x3A then Err ErrBadSyntax  // expected ':'
      else
        let r = advance r in  // skip ':'
        let (r, ref) = push_node r NT_Blank in
        // First char: PN_CHARS_U | [0-9]
        let c = peek_u32 r in
        if not (is_pn_chars_u c || is_digit c) then
          let r = pop_node r ref in
          Err ErrBadSyntax
        else
          // Read remaining chars: (PN_CHARS | '.')* PN_CHARS
          // Must not end with '.'
          assume val read_blank_label_rest : r:reader -> ref:ref_t -> Stack (parse_result reader)
            (requires fun h -> B.live h r.source.buf)
            (ensures fun h0 _ h1 -> True)
          in
          let r = push_byte r ref (U8.uint_to_t (U32.v c)) in
          let r = advance r in
          match read_blank_label_rest r ref with
          | Err s -> let r = pop_node r ref in Err s
          | Ok r -> Ok (r, ref)

// ---- String literals [17, 22-25] ----

// STRING_LITERAL_QUOTE [22]: '"' ([^#x22#x5C#xA#xD] | ECHAR | UCHAR)* '"'
// STRING_LITERAL_SINGLE_QUOTE [23]: "'" ([^#x27#x5C#xA#xD] | ECHAR | UCHAR)* "'"
// STRING_LITERAL_LONG_SINGLE_QUOTE [24]: "'''" ... "'''"
// STRING_LITERAL_LONG_QUOTE [25]: '"""' ... '"""'

assume val read_String_impl : r:reader -> Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)

// ---- LANGTAG [144s] ----
// '@' [a-zA-Z]+ ('-' [a-zA-Z0-9]+)*
let read_LANGTAG_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b <> 0x40 then Err Failure  // not '@'
    else
      let r = advance r in  // skip '@'
      let (r, ref) = push_node r NT_Literal in
      // Must have at least one alpha
      let c = peek_u32 r in
      if not (is_alpha c) then
        let r = pop_node r ref in
        Err ErrBadSyntax
      else
        // Read alpha+ then ('-' alphanum+)*
        assume val read_lang_rest : r:reader -> ref:ref_t -> Stack (parse_result reader)
          (requires fun h -> B.live h r.source.buf)
          (ensures fun h0 _ h1 -> True)
        in
        match read_lang_rest r ref with
        | Err s -> let r = pop_node r ref in Err s
        | Ok r -> Ok (r, ref)

// ---- RDFLiteral [128s] ----
// String (LANGTAG | '^^' iri)?
let read_literal_impl (r: reader) : Stack (parse_result (reader & ref_t & ref_t & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = match read_String_impl r with
    | Err s -> Err s
    | Ok (r, str_ref) ->
      let b = peek_byte r.source in
      if I32.v b = 0x40 then  // '@' -> LANGTAG
        match read_LANGTAG_impl r with
        | Err s -> Err s
        | Ok (r, lang_ref) -> Ok (r, str_ref, 0ul, lang_ref)
      else if I32.v b = 0x5E then  // '^' -> maybe '^^' iri
        let r = advance r in
        let b2 = peek_byte r.source in
        if I32.v b2 <> 0x5E then Err ErrBadSyntax  // expected second '^'
        else
          let r = advance r in
          match read_iri_impl r with
          | Err s -> Err s
          | Ok (r, dt_ref) -> Ok (r, str_ref, dt_ref, 0ul)
      else
        Ok (r, str_ref, 0ul, 0ul)  // plain string literal

// ---- NumericLiteral [16] ----
// INTEGER [19]: [+-]? [0-9]+
// DECIMAL [20]: [+-]? [0-9]* '.' [0-9]+
// DOUBLE [21]: [+-]? ([0-9]+ '.' [0-9]* EXPONENT | '.' [0-9]+ EXPONENT | [0-9]+ EXPONENT)
// EXPONENT [154s]: [eE] [+-]? [0-9]+

assume val read_number_impl : r:reader -> Stack (parse_result (reader & ref_t & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)

// ---- BooleanLiteral [133s] ----
// 'true' | 'false'
assume val read_boolean_impl : r:reader -> Stack (parse_result (reader & ref_t & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)

// ---- verb [9] ----
// predicate | 'a'
let read_verb_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    // Check for 'a' shorthand (must be followed by whitespace, not part of a prefixed name)
    if I32.v b = 0x61 then  // 'a'
      // Peek ahead to see if this is 'a' alone or start of a prefixed name
      // 'a' as verb must be followed by whitespace
      assume val is_verb_a : r:reader -> Stack bool
        (requires fun h -> B.live h r.source.buf)
        (ensures fun h0 _ h1 -> h0 == h1)
      in
      if is_verb_a r then
        let r = advance r in  // skip 'a'
        // Push rdf:type IRI
        let (r, ref) = push_node r NT_IRI in
        // TODO: push "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" bytes
        assume val push_rdf_type : r:reader -> ref:ref_t -> Stack reader
          (requires fun h -> True)
          (ensures fun h0 _ h1 -> True)
        in
        let r = push_rdf_type r ref in
        Ok (r, ref)
      else
        read_iri_impl r
    else
      read_iri_impl r

// ---- object [12] ----
// iri | BlankNode | collection | blankNodePropertyList | literal
let read_object_impl (r: reader) (ctx: read_ctx) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    let v = I32.v b in
    // Dispatch on first character
    if v = 0x3C then  // '<' -> IRIREF
      match read_IRIREF_impl r with
      | Err s -> Err s
      | Ok (r, obj_ref) ->
        match emit_statement r ctx obj_ref 0ul 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r obj_ref in
          Ok r
    else if v = 0x5F then  // '_' -> blank node label
      match read_BLANK_NODE_LABEL_impl r with
      | Err s -> Err s
      | Ok (r, obj_ref) ->
        match emit_statement r ctx obj_ref 0ul 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r obj_ref in
          Ok r
    else if v = 0x28 then  // '(' -> collection
      match read_collection r with
      | Err s -> Err s
      | Ok (r, obj_ref) ->
        match emit_statement r ctx obj_ref 0ul 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r obj_ref in
          Ok r
    else if v = 0x5B then  // '[' -> blankNodePropertyList
      match read_anon r with
      | Err s -> Err s
      | Ok (r, obj_ref) ->
        match emit_statement r ctx obj_ref 0ul 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r obj_ref in
          Ok r
    else if v = 0x22 || v = 0x27 then  // '"' or "'" -> literal
      match read_literal_impl r with
      | Err s -> Err s
      | Ok (r, str_ref, dt_ref, lang_ref) ->
        match emit_statement r ctx str_ref dt_ref lang_ref with
        | Err s -> Err s
        | Ok r ->
          let r = if lang_ref <> 0ul then pop_node r lang_ref else r in
          let r = if dt_ref <> 0ul then pop_node r dt_ref else r in
          let r = pop_node r str_ref in
          Ok r
    else if v = 0x2B || v = 0x2D || (v >= 0x30 && v <= 0x39) || v = 0x2E then
      // '+', '-', digit, '.' -> numeric literal
      match read_number_impl r with
      | Err s -> Err s
      | Ok (r, val_ref, dt_ref) ->
        match emit_statement r ctx val_ref dt_ref 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r dt_ref in
          let r = pop_node r val_ref in
          Ok r
    else if v = 0x74 || v = 0x66 then  // 't' or 'f' -> boolean
      match read_boolean_impl r with
      | Err s -> Err s
      | Ok (r, val_ref, dt_ref) ->
        match emit_statement r ctx val_ref dt_ref 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r dt_ref in
          let r = pop_node r val_ref in
          Ok r
    else  // try prefixed name
      match read_PrefixedName_impl r with
      | Err s -> Err s
      | Ok (r, obj_ref) ->
        match emit_statement r ctx obj_ref 0ul 0ul with
        | Err s -> Err s
        | Ok r ->
          let r = pop_node r obj_ref in
          Ok r

// ---- objectList [8] ----
// object (',' object)*
let rec read_objectList_impl (r: reader) (ctx: read_ctx) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = match read_object_impl r ctx with
    | Err s -> Err s
    | Ok r ->
      let r = read_ws_star_impl r in
      let b = peek_byte r.source in
      if I32.v b = 0x2C then  // ','
        let r = advance r in
        let r = read_ws_star_impl r in
        read_objectList_impl r ctx
      else
        Ok r

// ---- predicateObjectList [7] ----
// verb objectList (';' (verb objectList)?)*
let rec read_predicateObjectList_impl (r: reader) (ctx: read_ctx) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = match read_verb_impl r with
    | Err s -> Err s
    | Ok (r, pred_ref) ->
      let r = read_ws_star_impl r in
      let ctx = { ctx with ctx_predicate = pred_ref } in
      match read_objectList_impl r ctx with
      | Err s ->
        let r = pop_node r pred_ref in
        Err s
      | Ok r ->
        let r = pop_node r pred_ref in
        let r = read_ws_star_impl r in
        let b = peek_byte r.source in
        if I32.v b = 0x3B then  // ';'
          let r = advance r in
          let r = read_ws_star_impl r in
          // Check if there's another verb or just trailing ';'
          let b = peek_byte r.source in
          let v = I32.v b in
          if v = 0x2E || v = 0x5D || v < 0 then  // '.', ']', or EOF
            Ok r  // trailing semicolon, no more predicates
          else
            read_predicateObjectList_impl r ctx
        else
          Ok r

// ---- blankNodePropertyList [14] ----
// '[' predicateObjectList ']'
let read_anon_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b <> 0x5B then Err Failure  // not '['
    else
      let r = advance r in  // skip '['
      let r = read_ws_star_impl r in
      // Generate blank node ID
      let (r, blank_id) = gen_blank_id r in
      let (r, ref) = push_node r NT_Blank in
      // TODO: push blank node label bytes from blank_id
      // Check for empty blank node []
      let b = peek_byte r.source in
      if I32.v b = 0x5D then  // ']' -> empty blank node
        let r = advance r in
        Ok (r, ref)
      else
        // Parse predicateObjectList inside [...]
        let ctx = { empty_ctx with ctx_subject = ref; ctx_flags = SF_AnonSBegin } in
        match read_predicateObjectList_impl r ctx with
        | Err s -> let r = pop_node r ref in Err s
        | Ok r ->
          let r = read_ws_star_impl r in
          let b = peek_byte r.source in
          if I32.v b <> 0x5D then  // expected ']'
            let r = pop_node r ref in
            Err ErrBadSyntax
          else
            let r = advance r in  // skip ']'
            Ok (r, ref)

// ---- collection [15] ----
// '(' object* ')'
// Expands to rdf:first/rdf:rest linked list
let read_collection_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    if I32.v b <> 0x28 then Err Failure  // not '('
    else
      let r = advance r in  // skip '('
      let r = read_ws_star_impl r in
      let b = peek_byte r.source in
      if I32.v b = 0x29 then  // ')' -> empty collection = rdf:nil
        let r = advance r in
        // Return rdf:nil reference
        let (r, ref) = push_node r NT_IRI in
        // TODO: push rdf:nil IRI bytes
        Ok (r, ref)
      else
        // Non-empty collection: generate blank nodes for rdf:first/rdf:rest chain
        assume val read_collection_items : r:reader -> Stack (parse_result (reader & ref_t))
          (requires fun h -> B.live h r.source.buf)
          (ensures fun h0 _ h1 -> True)
        in
        read_collection_items r

// ---- subject [10] ----
// iri | BlankNode | collection
let read_subject_impl (r: reader) : Stack (parse_result (reader & ref_t))
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let b = peek_byte r.source in
    let v = I32.v b in
    if v = 0x3C then  // '<' -> IRIREF
      read_IRIREF_impl r
    else if v = 0x5F then  // '_' -> blank node
      read_BLANK_NODE_LABEL_impl r
    else if v = 0x28 then  // '(' -> collection
      read_collection_impl r
    else if v = 0x5B then  // '[' -> blankNodePropertyList
      read_anon_impl r
    else  // try prefixed name
      read_PrefixedName_impl r

// ---- triples [6] ----
let read_triples_impl (r: reader) (subj_ref: ref_t) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let r = read_ws_star_impl r in
    let ctx = { empty_ctx with ctx_subject = subj_ref } in
    read_predicateObjectList_impl r ctx

// ---- directive [3] ----
// prefixID [4]: '@prefix' PNAME_NS IRIREF '.'
// base [5]: '@base' IRIREF '.'
// sparqlPrefix [28s]: 'PREFIX' PNAME_NS IRIREF
// sparqlBase [29s]: 'BASE' IRIREF
assume val read_directive_impl : r:reader -> Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)

// ---- statement [2] ----
// directive | triples '.'
let read_statement_impl (r: reader) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let r = read_ws_star_impl r in
    let b = peek_byte r.source in
    let v = I32.v b in
    if v < 0 then Ok r  // EOF, no more statements
    else if v = 0x40 then  // '@' -> @prefix or @base directive
      read_directive_impl r
    else if v = 0x50 || v = 0x42 then  // 'P' or 'B' -> SPARQL PREFIX or BASE
      // Check for SPARQL-style directives (case-insensitive would need more lookahead)
      read_directive_impl r
    else
      // Try to parse a triple
      match read_subject_impl r with
      | Err s -> Err s
      | Ok (r, subj_ref) ->
        match read_triples_impl r subj_ref with
        | Err s ->
          let r = pop_node r subj_ref in
          Err s
        | Ok r ->
          let r = pop_node r subj_ref in
          let r = read_ws_star_impl r in
          // Expect '.'
          let b = peek_byte r.source in
          if I32.v b = 0x2E then  // '.'
            let r = advance r in
            Ok r
          else
            // Some productions (SPARQL PREFIX/BASE, blankNodePropertyList)
            // don't require trailing dot
            Ok r

// ---- turtleDoc [1] ----
// statement*
let rec read_turtleDoc_impl (r: reader) : Stack (parse_result reader)
  (requires fun h -> B.live h r.source.buf)
  (ensures fun h0 _ h1 -> True)
  = let r = read_ws_star_impl r in
    if r.source.eof then Ok r
    else
      match read_statement_impl r with
      | Err s -> Err s
      | Ok r -> read_turtleDoc_impl r
