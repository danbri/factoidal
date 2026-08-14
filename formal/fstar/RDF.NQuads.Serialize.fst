module RDF.NQuads.Serialize

// N-Quads / N-Triples wire-format serializers.
//
// Migrated from factoidal_http.ml's nq_escape_literal,
// nq_term_to_string, nq_subject_to_string, and nq_line_for_triple.
// All four are pure character / string mappings that encode the
// N-Quads serialization rules from the W3C spec; per Iron Rule #1
// they belong in F*.
//
// This is the ONLY N-Triples / N-Quads term renderer in the tree,
// and it is byte-correct (it escapes \" and control characters in
// literals). The Turtle-style ABBREVIATED rendering for human-facing
// output lives in RDF.Pretty.fst, but that file no longer carries an
// N-Triples renderer of its own.
//
// It used to. `RDF.Pretty.term_to_ntriples` wrote lexical forms
// verbatim and was justified as "display, not wire" -- while every
// consumer of it was a wire path. That cost issues #339 (our own
// parser could not read our own `--dump` output) and #443 (an
// import -> query round trip DESTROYED any literal containing a
// quote, a newline or a backslash, because the COTTAS object cell
// no longer re-parsed). Deleted 2026-08-14; a serializer whose
// output is re-parsed belongs here, next to the round-trip proofs.

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

let rec nq_term_to_string (t : rdf_term) : Tot string (decreases t) =
  match t with
  | T_IRI i   -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let esc = nq_escape_literal l.lexical_form in
    (match l.lang_tag with
     | Some tag ->
       // RDF 1.2: a directional language string appends `--ltr`/`--rtl`
       // to the language tag. RDF 1.1 langString literals have
       // direction = None, so this suffix is empty and the output is
       // byte-identical to before.
       let dir_suffix = (match l.direction with
                         | Some Dir_LTR -> "--ltr"
                         | Some Dir_RTL -> "--rtl"
                         | None -> "") in
       "\"" ^ esc ^ "\"@" ^ tag ^ dir_suffix
     | None ->
       if l.datatype = xsd_string then
         "\"" ^ esc ^ "\""
       else
         "\"" ^ esc ^ "\"^^<" ^ l.datatype ^ ">")
  | T_TripleTerm s p o ->
    // RDF 1.2 triple term in object position: `<<( s p o )>>`.
    let subj_str = (match s with
                    | S_IRI i   -> "<" ^ i ^ ">"
                    | S_BNode b -> "_:" ^ b) in
    "<<( " ^ subj_str ^ " <" ^ p ^ "> " ^ nq_term_to_string o ^ " )>>"

// ---------------------------------------------------------------
// Processing-mode guard (epic #305, wave 2).
//
// The serializer above is EMIT-MINIMAL: it renders `<<( )>>` and the
// `--ltr`/`--rtl` direction suffix ONLY for terms that actually carry
// a triple term or a base direction, so a purely-1.1 term is already
// byte-identical in both modes. `nq_term_to_string_mode` adds the
// honest-failure half of the contract: under Mode_11 a term that
// requires RDF 1.2 lexical syntax returns None (a typed error the
// caller must handle) instead of being silently emitted. Under
// Mode_12 every term serializes.
// ---------------------------------------------------------------

let term_requires_rdf12 (t : rdf_term) : bool =
  match t with
  | T_TripleTerm _ _ _ -> true
  | T_Literal l -> Some? l.direction
  | _ -> false

let nq_term_to_string_mode (mode : Parser.NTriples.rdf_syntax_mode) (t : rdf_term)
  : option string =
  match mode with
  | Parser.NTriples.Mode_12 -> Some (nq_term_to_string t)
  | Parser.NTriples.Mode_11 ->
    if term_requires_rdf12 t then None else Some (nq_term_to_string t)

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

// ---------------------------------------------------------------
// RDF 1.2 CANONICAL N-Triples / N-Quads serialization (#305 P5).
//
// Canonical form as exercised by the W3C RDF 1.2 c14n suite: single
// space between terms (by construction), CANONICAL literal escaping,
// language tags lowercased, triple-term spacing `<<( s p o )>>`, blank
// nodes and statement order PRESERVED (this is canonical serialization,
// NOT RDFC-1.0 blank-node relabelling — the parser already decoded input
// escapes into raw codepoints in lexical_form, so this only re-escapes).
// ---------------------------------------------------------------

// Uppercase hex digit for a nibble.
let canon_hex_upper (n : nat) : string =
  if n = 0 then "0" else if n = 1 then "1" else if n = 2 then "2"
  else if n = 3 then "3" else if n = 4 then "4" else if n = 5 then "5"
  else if n = 6 then "6" else if n = 7 then "7" else if n = 8 then "8"
  else if n = 9 then "9" else if n = 10 then "A" else if n = 11 then "B"
  else if n = 12 then "C" else if n = 13 then "D" else if n = 14 then "E"
  else "F"

// \u00XX for a single byte (uppercase hex, canonical form).
let canon_byte_uchar (b : nat) : string =
  "\\u00" ^ canon_hex_upper (b / 16) ^ canon_hex_upper (b % 16)

// A byte needing an escape in canonical N-Triples: every C0 control, the
// quote, the backslash, and DEL (0x7F).
let nq_canon_special_byte (b : nat) : bool =
  b < 0x20 || b = 0x22 || b = 0x5C || b = 0x7F

let nq_canon_escape_byte (b : nat) : string =
  if b = 0x08 then "\\b"
  else if b = 0x09 then "\\t"
  else if b = 0x0A then "\\n"
  else if b = 0x0C then "\\f"
  else if b = 0x0D then "\\r"
  else if b = 0x22 then "\\\""
  else if b = 0x5C then "\\\\"
  else canon_byte_uchar b   // 0x00-0x07, 0x0B, 0x0E-0x1F, 0x7F

// Byte walk: copy runs of ordinary bytes with fs_byte_sub, splice in an
// escape at a special byte, and detect the BMP non-characters U+FFFE /
// U+FFFF (UTF-8 EF BF BE / EF BF BF) -> ￾ / ￿.
let rec nq_canon_walk (s : string) (len : nat) (run_start : nat) (pos : nat) (acc : string)
  : Tot string (decreases (len - pos)) =
  if pos >= len then
    (if pos > run_start then acc ^ fs_byte_sub s run_start (pos - run_start) else acc)
  else
    let b = fs_byte_at s pos in
    if b = 0xEF && pos + 2 < len && fs_byte_at s (pos + 1) = 0xBF
       && (fs_byte_at s (pos + 2) = 0xBE || fs_byte_at s (pos + 2) = 0xBF) then
      let run = if pos > run_start then fs_byte_sub s run_start (pos - run_start) else "" in
      let esc = if fs_byte_at s (pos + 2) = 0xBE then "\\uFFFE" else "\\uFFFF" in
      nq_canon_walk s len (pos + 3) (pos + 3) (acc ^ run ^ esc)
    else if nq_canon_special_byte b then
      let run = if pos > run_start then fs_byte_sub s run_start (pos - run_start) else "" in
      nq_canon_walk s len (pos + 1) (pos + 1) (acc ^ run ^ nq_canon_escape_byte b)
    else
      nq_canon_walk s len run_start (pos + 1) acc

let nq_canon_escape_literal (s : string) : Tot string =
  nq_canon_walk s (fs_byte_length s) 0 0 ""

let rec nq_canon_term (t : rdf_term) : Tot string (decreases t) =
  match t with
  | T_IRI i   -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let esc = nq_canon_escape_literal l.lexical_form in
    (match l.lang_tag with
     | Some tag ->
       let dir_suffix = (match l.direction with
                         | Some Dir_LTR -> "--ltr"
                         | Some Dir_RTL -> "--rtl"
                         | None -> "") in
       // Language tags are ASCII (BCP47), so FStar.String.lowercase is
       // byte-safe here and produces the canonical lowercase form.
       "\"" ^ esc ^ "\"@" ^ FStar.String.lowercase tag ^ dir_suffix
     | None ->
       if l.datatype = xsd_string then "\"" ^ esc ^ "\""
       else "\"" ^ esc ^ "\"^^<" ^ l.datatype ^ ">")
  | T_TripleTerm s p o ->
    let subj_str = (match s with
                    | S_IRI i   -> "<" ^ i ^ ">"
                    | S_BNode b -> "_:" ^ b) in
    "<<( " ^ subj_str ^ " <" ^ p ^ "> " ^ nq_canon_term o ^ " )>>"

let nq_canon_line_default (t : triple) : Tot string =
  nq_subject_to_string t.s ^ " <" ^ t.p ^ "> " ^ nq_canon_term t.o ^ " .\n"

let nq_canon_line_graph (graph_iri : string) (t : triple) : Tot string =
  nq_subject_to_string t.s ^ " <" ^ t.p ^ "> " ^ nq_canon_term t.o
  ^ " <" ^ graph_iri ^ "> .\n"

// Canonical N-Triples document: one line per triple, input order.
let rec canonical_nt_document (ts : list triple) : Tot string (decreases ts) =
  match ts with
  | [] -> ""
  | t :: rest -> nq_canon_line_default t ^ canonical_nt_document rest

let rec canon_nq_named_lines (name : string) (ts : list triple) : Tot string (decreases ts) =
  match ts with
  | [] -> ""
  | t :: rest -> nq_canon_line_graph name t ^ canon_nq_named_lines name rest

let rec canon_nq_named (ngs : list named_graph) : Tot string (decreases ngs) =
  match ngs with
  | [] -> ""
  | ng :: rest -> canon_nq_named_lines ng.ng_name ng.ng_graph ^ canon_nq_named rest

// Canonical N-Quads document: default-graph lines then named-graph lines.
let canonical_nq_document (ds : rdf_dataset) : string =
  canonical_nt_document ds.ds_default ^ canon_nq_named ds.ds_named
