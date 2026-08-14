module RDF.Pretty

// Pretty-printing of RDF terms and SPARQL pattern terms.
//
// Migration of three duplicated/divergent surfaces from OCaml glue:
//   factoidal_cli.ml :: term_to_ntriples / term_to_turtle / subject_to_string
//   factoidal_explain.ml :: term_short / pattern_term_short
//                           / pattern_subject_short / triple_pattern_short
//
// Both files implemented essentially the same algorithm with two
// hand-maintained prefix tables (CLI's general-purpose foaf/dc/schema
// flavour vs. explain's parliament-corpus-specific flavour). Putting
// the algorithm here in F\* and exposing both prefix tables as
// constants stops the drift and centralises the rendering rules.
//
// All functions are total. The output is byte-for-byte identical to
// the legacy OCaml functions on inputs that the OCaml type system
// already required to be well-formed (wf_iri, wf_literal). The one
// behaviour change is that the legacy `term_to_ntriples` had a
// dead-code branch for `l.datatype = ""` — the refinement
// `datatype : wf_iri` makes that branch unreachable, so it's dropped
// here.

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

module S = FStar.String

// ---------------------------------------------------------------
// 1. N-Triples-style rendering: NOT HERE. See RDF.NQuads.Serialize.
//
// This module used to carry `term_to_ntriples`, a second N-Triples
// term renderer that wrote a literal's lexical form VERBATIM. It was
// described as "for display, not wire", but every consumer treated
// its output as wire: `factoidal --dump` and the COTTAS store's object
// column both went through it.
//
// The result was issue #339 (dump emitted output our own parser
// rejected) and issue #443 (import -> query DESTROYED any literal
// containing a quote, a newline or a backslash -- the store cell did
// not re-parse, so the reader returned the sentinel
// `_:cottas_decode_oor`).
//
// The function is deleted rather than fixed. Making it escape would
// have made it a byte-identical copy of
// `RDF.NQuads.Serialize.nq_term_to_string`, and a second name for the
// same rendering is what let the two drift apart in the first place.
// One notion of how a literal is written; it lives in
// RDF.NQuads.Serialize with the round-trip proofs that reference it.
//
// Callers wanting an N-Triples term use
// `RDF.NQuads.Serialize.nq_term_to_string`; callers wanting a whole
// line use `nq_line_for_triple_default_graph` / `nq_line_for_triple`.
// What remains below is the Turtle-style ABBREVIATED rendering, which
// is genuinely display-only and has no wire consumer.
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// 2. Prefix-table support.
//
// A prefix_table is a list of (full IRI namespace, abbreviation
// prefix) pairs, e.g. ("http://schema.org/", "schema:"). Lookups
// match on the IRI being a strict prefix of the namespace; the
// caller's order determines which prefix wins on overlap (we keep
// the legacy "first match wins" behaviour).
// ---------------------------------------------------------------

type prefix_table = list (string * string)

// "Strict" prefix: pfx must be both a prefix of s AND shorter than s.
// The strictness avoids matching the entire IRI (which would leave
// an empty rest, producing nonsense like "rdf:" for the namespace
// IRI itself).
let starts_with_strict (s : string) (pfx : string) : Tot bool =
  let pl = S.length pfx in
  let sl = S.length s in
  if sl > pl then S.sub s 0 pl = pfx
  else false

let rec find_prefix (table : prefix_table) (iri : string) :
  Tot (option (string * string)) (decreases table) =
  match table with
  | [] -> None
  | (ns, abbr) :: rest ->
    if starts_with_strict iri ns then Some (ns, abbr)
    else find_prefix rest iri

let abbreviate_iri (table : prefix_table) (iri : string) : Tot string =
  match find_prefix table iri with
  | Some (ns, abbr) ->
    let nsl = S.length ns in
    let il = S.length iri in
    // starts_with_strict ensures nsl < il, but the Some-payload type
    // here has lost that refinement; check defensively.
    if nsl < il then abbr ^ S.sub iri nsl (il - nsl)
    else "<" ^ iri ^ ">"
  | None -> "<" ^ iri ^ ">"

// ---------------------------------------------------------------
// 3. Term rendering with prefix abbreviation.
//
// IRIs are abbreviated via the table; blank nodes and literals are
// rendered the same as in N-Triples (literal datatypes are *not*
// abbreviated — that's a Turtle 1.1 thing we deliberately don't do
// in either OCaml caller, and we preserve the legacy behaviour).
//
// This rendering is display-only: `term_with_prefixes` output is read
// by a human, never re-parsed, so it keeps the verbatim lexical form.
// Anything whose output is re-parsed must use RDF.NQuads.Serialize --
// see the banner in section 1 and issues #339 / #443.
// ---------------------------------------------------------------

// RDF 1.2 base-direction suffix for a directional language string.
// Empty for every RDF 1.1 literal (direction = None), so output stays
// byte-identical for pre-1.2 data.
let dir_suffix (d : option text_direction) : Tot string =
  match d with
  | Some Dir_LTR -> "--ltr"
  | Some Dir_RTL -> "--rtl"
  | None -> ""

let rec term_with_prefixes (table : prefix_table) (t : rdf_term) : Tot string (decreases t) =
  match t with
  | T_IRI i   -> abbreviate_iri table i
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    (match l.lang_tag with
     | Some tag -> "\"" ^ l.lexical_form ^ "\"@" ^ tag ^ dir_suffix l.direction
     | None ->
       if l.datatype = xsd_string then
         "\"" ^ l.lexical_form ^ "\""
       else
         "\"" ^ l.lexical_form ^ "\"^^<" ^ l.datatype ^ ">")
  | T_TripleTerm s p o ->
    let subj_str = (match s with
                    | S_IRI i   -> abbreviate_iri table i
                    | S_BNode b -> "_:" ^ b) in
    "<<( " ^ subj_str ^ " <" ^ p ^ "> " ^ term_with_prefixes table o ^ " )>>"

// ---------------------------------------------------------------
// 4. Subject rendering.
// ---------------------------------------------------------------

let subject_with_prefixes (table : prefix_table) (s : subject) : Tot string =
  match s with
  | S_IRI i   -> abbreviate_iri table i
  | S_BNode b -> "_:" ^ b

// ---------------------------------------------------------------
// 5. Predefined prefix tables.
//
// Two tables, matching the two legacy OCaml hand-maintained lists.
// They overlap on rdf:/rdfs:/xsd:/owl: and diverge after that.
// Adding a new prefix means extending one (or both) of these lists,
// in F\*, in this file. Stops the drift between the two .ml files.
// ---------------------------------------------------------------

// CLI / Turtle output, general-purpose.
let cli_turtle_prefixes : prefix_table = [
  ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#",           "xsd:");
  ("http://www.w3.org/2002/07/owl#",              "owl:");
  ("http://xmlns.com/foaf/0.1/",                  "foaf:");
  ("http://purl.org/dc/terms/",                   "dcterms:");
  ("http://purl.org/dc/elements/1.1/",            "dc:");
  ("http://schema.org/",                          "schema:");
]

// --explain dump, parliament-corpus-aware.
let explain_prefixes : prefix_table = [
  ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#",           "xsd:");
  ("http://www.w3.org/2002/07/owl#",              "owl:");
  ("http://www.opengis.net/ont/geosparql#",       "geo:");
  ("https://id.parliament.uk/schema/",            ":");
]

// ---------------------------------------------------------------
// 6. Convenience aliases — partial applications of the parameterised
// core, eta-expanded so they extract cleanly to OCaml functions
// rather than top-level closures.
// ---------------------------------------------------------------

// Used by factoidal_cli.ml as `term_to_turtle t`.
let term_to_turtle (t : rdf_term) : Tot string =
  term_with_prefixes cli_turtle_prefixes t

// Used by factoidal_cli.ml as `subject_to_string s`.
let subject_to_turtle (s : subject) : Tot string =
  subject_with_prefixes cli_turtle_prefixes s

// Used by factoidal_explain.ml as `term_short t`.
let term_short_explain (t : rdf_term) : Tot string =
  term_with_prefixes explain_prefixes t

// ---------------------------------------------------------------
// 7. SPARQL pattern-term rendering (used by factoidal_explain.ml).
// ---------------------------------------------------------------

let rec pattern_term_short (table : prefix_table) (pt : pattern_term) : Tot string (decreases pt) =
  match pt with
  | PT_Var v     -> "?" ^ v
  | PT_IRI i     -> abbreviate_iri table i
  | PT_BNode b   -> "_:" ^ b
  | PT_Literal l -> term_with_prefixes table (T_Literal l)
  | PT_TripleTerm s p o ->
    "<<( " ^ pattern_term_short table s ^ " " ^ pattern_term_short table p
           ^ " " ^ pattern_term_short table o ^ " )>>"

let pattern_subject_short (table : prefix_table) (ps : pattern_subject) : Tot string =
  match ps with
  | PS_Var v   -> "?" ^ v
  | PS_IRI i   -> abbreviate_iri table i
  | PS_BNode b -> "_:" ^ b
  | PS_TripleTerm s p o ->
    "<<( " ^ pattern_term_short table s ^ " " ^ pattern_term_short table p
           ^ " " ^ pattern_term_short table o ^ " )>>"

let triple_pattern_short (table : prefix_table) (tp : triple_pattern) : Tot string =
  pattern_subject_short table tp.tp_s ^ " " ^
  pattern_term_short table tp.tp_p ^ " " ^
  pattern_term_short table tp.tp_o

// Eta-expanded aliases for the explain dump.
let pattern_term_short_explain (pt : pattern_term) : Tot string =
  pattern_term_short explain_prefixes pt

let pattern_subject_short_explain (ps : pattern_subject) : Tot string =
  pattern_subject_short explain_prefixes ps

let triple_pattern_short_explain (tp : triple_pattern) : Tot string =
  triple_pattern_short explain_prefixes tp
