module RDF.NQuads.Serialize

// N-Quads / N-Triples wire-format serializers.
//
// Migrated from factoidal_http.ml's nq_escape_literal,
// nq_term_to_string, nq_subject_to_string, and nq_line_for_triple.
// All four are pure character / string mappings that encode the
// N-Quads serialization rules from the W3C spec; per Iron Rule #1
// they belong in F*.
//
// This is the *byte-correct* serializer (escapes \" and control
// characters in literals). The Turtle-style abbreviated rendering
// for human-facing output lives in RDF.Pretty.fst; that file has
// `term_to_ntriples` which is intentionally lossy on literal
// escaping (it's for display, not wire). Both functions exist
// because the call sites have different correctness requirements.

open RDF.Graph.Executable

module S = FStar.String

// ---------------------------------------------------------------
// nq_escape_literal: escape the lexical form of an RDF literal for
// embedding in an N-Triples / N-Quads / Turtle quoted string.
//
// Bytes escaped:
//   0x5C  '\\'  ->  \\
//   0x22  '"'   ->  \"
//   0x0A  '\n'  ->  \n
//   0x0D  '\r'  ->  \r
//   0x09  '\t'  ->  \t
// All other bytes pass through unchanged.
//
// Note: this matches the legacy OCaml nq_escape_literal byte-for-byte.
// A more conservative escape-anything-< 0x20 form would be more
// rigorously NT-compliant, but the existing OCaml impl is what the
// downstream consumers (the /sandbox/dump output, w3c_runner output
// comparison) currently expect — preserve.
// ---------------------------------------------------------------

let escape_char (c : FStar.Char.char) : Tot string =
  let n = FStar.Char.int_of_char c in
  if n = 0x5C then "\\\\"
  else if n = 0x22 then "\\\""
  else if n = 0x0A then "\\n"
  else if n = 0x0D then "\\r"
  else if n = 0x09 then "\\t"
  else S.string_of_char c

let rec escape_chars_aux (cs : list FStar.Char.char)
  : Tot string (decreases cs) =
  match cs with
  | [] -> ""
  | c :: rest -> escape_char c ^ escape_chars_aux rest

let nq_escape_literal (s : string) : Tot string =
  escape_chars_aux (S.list_of_string s)

// ---------------------------------------------------------------
// nq_term_to_string : serialize an RDF term in N-Quads object form.
//
// Output:
//   T_IRI i           ->  "<i>"
//   T_BNode b         ->  "_:b"
//   T_Literal { lex; lang_tag = Some t }                   ->  "\"<esc>\"@t"
//   T_Literal { lex; datatype = xsd_string; lang = None }  ->  "\"<esc>\""
//   T_Literal { lex; datatype = d; lang = None }           ->  "\"<esc>\"^^<d>"
//
// where <esc> = nq_escape_literal lex.
//
// xsd:string is the implicit default datatype per the RDF 1.1 spec,
// so omit "^^<...>" for a literal whose datatype is already xsd:string.
//
// (The legacy OCaml had a defensive `l.datatype = ""` check that the
// F* wf_iri refinement makes unreachable; it's dropped here.)
// ---------------------------------------------------------------

let nq_term_to_string (t : rdf_term) : Tot string =
  match t with
  | T_IRI i   -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let esc = nq_escape_literal l.lexical_form in
    (match l.lang_tag with
     | Some tag -> "\"" ^ esc ^ "\"@" ^ tag
     | None ->
       if l.datatype = xsd_string then
         "\"" ^ esc ^ "\""
       else
         "\"" ^ esc ^ "\"^^<" ^ l.datatype ^ ">")

// ---------------------------------------------------------------
// nq_subject_to_string : serialize a subject (IRI or blank node).
// ---------------------------------------------------------------

let nq_subject_to_string (s : subject) : Tot string =
  match s with
  | S_IRI i   -> "<" ^ i ^ ">"
  | S_BNode b -> "_:" ^ b

// ---------------------------------------------------------------
// nq_line_for_triple : full N-Quads line for a triple in a named
// graph. Caller passes the graph IRI as a string (already-validated
// upstream).
//
//   <subject> <predicate> <object> <graph> .\n
// ---------------------------------------------------------------

let nq_line_for_triple (graph_iri : string) (t : triple) : Tot string =
  nq_subject_to_string t.s ^ " <" ^ t.p ^ "> "
  ^ nq_term_to_string t.o ^ " <" ^ graph_iri ^ "> .\n"
