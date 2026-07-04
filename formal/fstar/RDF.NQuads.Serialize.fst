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
open Parser.FastString

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
//
// 2026-07-04 rewrite (issue #272): walk the literal BYTE-by-byte with
// fs_byte_at / fs_byte_length (Parser.FastString — the same
// primitives the Turtle / N-Triples / N-Quads *parsers* already use
// on their hot loop; see that module's banner for the byte-vs-
// codepoint safety argument) and copy maximal runs of non-special
// bytes with one fs_byte_sub each, instead of the previous per-
// CHARACTER `^` fold over an FStar.Char list. Same run-slicing shape
// as SPARQL.JSON.Escape's walk_runs (the json_escape fix earlier the
// same day). Two wins:
//   1. O(specials + total run length) instead of O(n^2) in the
//      literal's length for long literals.
//   2. Byte-transparent copying means multi-byte UTF-8 sequences pass
//      through as raw bytes, so this no longer needs the
//      string_of_list codepoint-safety workaround the old
//      per-char passthrough arm required (string_of_char is
//      byte-oriented and crashes/mojibakes above 0x7F; string_of_list
//      re-encodes each element as a codepoint — byte-copying skips
//      both problems by never decoding to a FStar.Char in the first
//      place).
// ---------------------------------------------------------------

let nq_special_byte (b : nat) : bool =
  b = 0x5C || b = 0x22 || b = 0x0A || b = 0x0D || b = 0x09

let nq_escape_byte (b : nat{nq_special_byte b}) : string =
  if b = 0x5C then "\\\\"
  else if b = 0x22 then "\\\""
  else if b = 0x0A then "\\n"
  else if b = 0x0D then "\\r"
  else "\\t"

// Copy maximal runs of non-special bytes with fs_byte_sub, splicing
// escape strings in at special bytes. `run_start` marks the start of
// the current unescaped run; `pos` is the scan cursor.
let rec nq_escape_walk (s : string) (len : nat) (run_start : nat) (pos : nat) (acc : string)
  : Tot string (decreases (len - pos)) =
  if pos >= len then
    (if pos > run_start then acc ^ fs_byte_sub s run_start (pos - run_start) else acc)
  else
    let b = fs_byte_at s pos in
    if nq_special_byte b then
      let run = if pos > run_start then fs_byte_sub s run_start (pos - run_start) else "" in
      nq_escape_walk s len (pos + 1) (pos + 1) (acc ^ run ^ nq_escape_byte b)
    else
      nq_escape_walk s len run_start (pos + 1) acc

let nq_escape_literal (s : string) : Tot string =
  nq_escape_walk s (fs_byte_length s) 0 0 ""

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

// ---------------------------------------------------------------
// nq_line_for_triple_default_graph : N-Triples-style line for a
// triple in the default (unnamed) graph. Same as
// nq_line_for_triple but without the trailing graph IRI.
//
// Output:  <subject> <predicate> <object> .\n
// ---------------------------------------------------------------

let nq_line_for_triple_default_graph (t : triple) : Tot string =
  nq_subject_to_string t.s ^ " <" ^ t.p ^ "> "
  ^ nq_term_to_string t.o ^ " .\n"
