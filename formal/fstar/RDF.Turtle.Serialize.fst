module RDF.Turtle.Serialize

// Turtle pretty-printer: prefix-compacted, subject-grouped output.
//
// Owner directive: "ensure serializers are not gratuitously ugly." The
// wire-correct serializers (RDF.NQuads.Serialize, RDF.Canonical) exist
// for round-trip / hashing fidelity; this module targets a human-facing
// rendering of the same graph — `@prefix` header, `;`-joined predicate
// lists, `,`-joined object lists, one block per subject.
//
// Correctness anchor: parse(turtle_of_graph(table, g)) must round-trip
// to a graph isomorphic to g. That means every abbreviation this module
// performs (prefixed names, the `a` keyword for rdf:type) must only be
// emitted when Parser.Turtle would actually accept it back — hence this
// module reuses the SAME PN_PREFIX / PN_LOCAL validators the parser
// uses (validate_pname_ns, validate_pn_local from Parser.Turtle) rather
// than re-deriving an approximation of the Turtle grammar.
//
// Reuse, not reinvention:
//   - Literal escaping: RDF.NQuads.Serialize.nq_escape_literal (the
//     2026-07-04 run-slicing byte-walker). Its escape set (backslash,
//     quote, LF, CR, tab) is a safe superset of what Turtle's
//     STRING_LITERAL_QUOTE strictly requires escaped (quote/backslash/
//     LF/CR only), so the shared function is correct here too.
//   - Sort/group key: RDF.Graph.Executable.triple_cmp / subject_eq,
//     the exact comparator+equality the RDFS/OWL-RL closure's own
//     O(n log n) dedup path already relies on (issue #259 followup).
//     No new ad hoc key scheme.
//   - Accumulation: every multi-piece string this module builds goes
//     through one `String.concat "" (list string)` at the end of its
//     scope (mirrors the RDF.Canonical concat_strings fix, issue #272)
//     — never a per-element `^` fold over a growing accumulator.

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open RDF.NQuads.Serialize
open Parser.FastString
open Parser.Turtle

// ---------------------------------------------------------------
// 0. Small helpers.
// ---------------------------------------------------------------

// One final linear-time join: reverse-accumulate then concat once.
// Used for both "obj , obj , obj" and "pred ... ;\n    pred ..." joins;
// bounding this to O(n) (rather than a right-fold `^`) means even a
// pathological single-subject/single-predicate graph (all triples
// sharing one (s,p) pair) stays linear instead of quadratic.
let rec join_with_acc (sep : string) (xs : list string) (acc : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> acc
  | [x] -> x :: acc
  | x :: rest -> join_with_acc sep rest (sep :: x :: acc)

let join_with (sep : string) (xs : list string) : Tot string =
  String.concat "" (List.Tot.rev (join_with_acc sep xs []))

// ---------------------------------------------------------------
// 1. Prefix table + spec-safe abbreviation.
//
// A prefix_table is (namespace_iri, "label:") pairs — same convention
// as RDF.Pretty.prefix_table (abbr already carries the trailing ':').
// Unlike RDF.Pretty.abbreviate_iri (built for display only), this
// abbreviator additionally checks the remainder is PN_LOCAL-safe via
// Parser.Turtle.validate_pn_local before compacting, falling back to
// the full "<iri>" form otherwise — abbreviating an unsafe remainder
// would emit Turtle the parser can't read back.
// ---------------------------------------------------------------

type prefix_table = list (string * string)

let ts_starts_with_strict (s : string) (pfx : string) : Tot bool =
  let pl = fs_byte_length pfx in
  let sl = fs_byte_length s in
  sl > pl && fs_byte_sub s 0 pl = pfx

let rec ts_find_prefix (table : prefix_table) (iri : string)
  : Tot (option (string * string)) (decreases table) =
  match table with
  | [] -> None
  | (ns, abbr) :: rest ->
    if ts_starts_with_strict iri ns then Some (ns, abbr)
    else ts_find_prefix rest iri

// PN_LOCAL may legally be empty (PNAME_NS alone, e.g. "ex:"); anything
// non-empty must satisfy Parser.Turtle.validate_pn_local.
let ts_local_ok (local : string) : bool =
  fs_byte_length local = 0 || validate_pn_local local

let ts_abbreviate_iri (table : prefix_table) (iri : string) : Tot string =
  match ts_find_prefix table iri with
  | Some (ns, abbr) ->
    let nsl = fs_byte_length ns in
    let il = fs_byte_length iri in
    if nsl < il then
      let local = fs_byte_sub iri nsl (il - nsl) in
      if ts_local_ok local then abbr ^ local
      else "<" ^ iri ^ ">"
    else "<" ^ iri ^ ">"
  | None -> "<" ^ iri ^ ">"

// Refines the banner comment above (lines 65-69) — "checks the
// remainder is PN_LOCAL-safe ... falling back to the full <iri> form
// otherwise" — into a checked type instead of leaving it as prose
// (the #445 template: a comment-claimed invariant becomes a `Type0`
// a Lemma is checked against). `compacts_to_pname_safe` is a
// DECLARATIVE RELATION (Type0-returning, not extracted): it names the
// exact PNAME_LN shape `ts_abbreviate_iri` is allowed to produce —
// the same namespace/abbr pair `ts_find_prefix` found, spliced with a
// `local` remainder that `ts_local_ok` accepts. The relation lives
// beside the code it constrains (an internal invariant of THIS
// module's own abbreviator, not an independent formalisation of
// Turtle's PNAME_LN grammar living in a separate pure-formalisation
// module) — that is `tools/assurance_inventory.py`'s internal-
// refinement class, one step short of a W3C-refinement theorem.
val compacts_to_pname_safe (table : prefix_table) (iri : string) : Type0
let compacts_to_pname_safe table iri =
  match ts_find_prefix table iri with
  | None -> False
  | Some (ns, abbr) ->
    let nsl = fs_byte_length ns in
    let il = fs_byte_length iri in
    nsl < il /\
    (let local = fs_byte_sub iri nsl (il - nsl) in
     ts_local_ok local == true /\
     ts_abbreviate_iri table iri == abbr ^ local)

// The actual theorem: for EVERY table and iri, `ts_abbreviate_iri`
// either fell back to the unabbreviated "<iri>" form, or the compact
// form it produced satisfies `compacts_to_pname_safe` — i.e. every
// abbreviation this module ever emits is one `Parser.Turtle.
// validate_pn_local` (via `ts_local_ok`) already certified as
// PN_LOCAL-safe. Proved by following `ts_abbreviate_iri`'s own
// case split — no FastString VALUE computation needed (unlike a
// concrete round-trip witness, this is a universally-quantified
// structural fact, so the SMT context never has to reduce
// `fs_byte_sub`/`fs_byte_length` on a concrete string; see the
// ROUND-TRIP SCOPE note before `render_triples` below for why the
// concrete-witness route is blocked).
val lemma_ts_abbreviate_iri_pname_safe (table : prefix_table) (iri : string)
  : Lemma (ensures ts_abbreviate_iri table iri == "<" ^ iri ^ ">" \/
                    compacts_to_pname_safe table iri)
let lemma_ts_abbreviate_iri_pname_safe table iri =
  match ts_find_prefix table iri with
  | None -> ()
  | Some (ns, abbr) ->
    let nsl = fs_byte_length ns in
    let il = fs_byte_length iri in
    if nsl < il then
      let local = fs_byte_sub iri nsl (il - nsl) in
      if ts_local_ok local then ()
      else ()
    else ()

// ---------------------------------------------------------------
// 1a. Render options (issue #681): a caller-supplied prefix table that
// wins over the auto-derived one, and grammar-guarded bare-literal
// shorthand for INTEGER / DECIMAL / DOUBLE / BooleanLiteral.
// ---------------------------------------------------------------

noeq type turtle_render_options = {
  tro_prefixes : prefix_table;       // caller-supplied (namespace, "label:") pairs; win over auto-derived ones
  tro_literal_shorthand : bool;      // bare INTEGER / DECIMAL / DOUBLE / BooleanLiteral when the lexical form qualifies
}

// https://github.com/danbri/factoidal/issues/681 — shorthand ON by
// default. Supersedes the 2026-07-04 quoted-only decision this module
// carried until now (see the section-2 banner below).
let turtle_render_defaults : turtle_render_options =
  { tro_prefixes = []; tro_literal_shorthand = true }

// Turtle terminals (https://www.w3.org/TR/turtle/#sec-grammar-grammar):
//   INTEGER        ::= [+-]? [0-9]+
//   DECIMAL        ::= [+-]? [0-9]* '.' [0-9]+
//   DOUBLE         ::= [+-]? ( [0-9]+ '.' [0-9]* EXPONENT | '.' [0-9]+ EXPONENT | [0-9]+ EXPONENT )
//   EXPONENT       ::= [eE] [+-]? [0-9]+
//   BooleanLiteral ::= 'true' | 'false'
// Each checker below is a total byte-level scan over the whole lexical
// form (fs_byte_length / fs_byte_at, the same FastString primitives
// last_ns_split_from below uses) and accepts it only when the terminal
// consumes the ENTIRE string — a leading/trailing space, or any byte
// left over past the matched terminal, falls through to false.

let ts_digit_byte (b : nat) : bool = b >= 0x30 && b <= 0x39

// [0-9]* starting at pos; returns the position one past the last digit
// consumed (== pos itself when no digit sits there).
let rec ts_scan_digits (s : string) (len : nat) (pos : nat) : Tot nat (decreases (len - pos)) =
  if pos >= len then pos
  else if ts_digit_byte (fs_byte_at s pos) then ts_scan_digits s len (pos + 1)
  else pos

// EXPONENT ::= [eE] [+-]? [0-9]+ , anchored at pos and required to
// consume exactly to len (no byte left over after the exponent).
let ts_exponent_suffix (s : string) (len : nat) (pos : nat) : bool =
  if pos >= len then false
  else
    let e = fs_byte_at s pos in
    if not (e = 0x65 || e = 0x45) then false             // 'e' or 'E'
    else
      let spos = pos + 1 in
      if spos >= len then false
      else
        let sb = fs_byte_at s spos in
        let dpos = if sb = 0x2B || sb = 0x2D then spos + 1 else spos in
        if dpos >= len then false
        else ts_scan_digits s len dpos = len

// End position of an optional leading '+'/'-' (0 when the string is
// empty or has no sign byte).
let ts_optional_sign_end (s : string) (len : nat) : nat =
  if len = 0 then 0
  else
    let b0 = fs_byte_at s 0 in
    if b0 = 0x2B || b0 = 0x2D then 1 else 0

let is_turtle_integer_lexical (s : string) : Tot bool =
  let len = fs_byte_length s in
  let dpos = ts_optional_sign_end s len in
  if len = 0 || dpos >= len then false
  else ts_scan_digits s len dpos = len

let is_turtle_decimal_lexical (s : string) : Tot bool =
  let len = fs_byte_length s in
  let dpos = ts_optional_sign_end s len in
  if len = 0 || dpos >= len then false
  else
    let ipos = ts_scan_digits s len dpos in                    // [0-9]*
    if ipos >= len || fs_byte_at s ipos <> 0x2E then false     // needs a '.'
    else
      let fpos = ipos + 1 in
      let fend = ts_scan_digits s len fpos in                  // [0-9]+
      fend > fpos && fend = len

let is_turtle_double_lexical (s : string) : Tot bool =
  let len = fs_byte_length s in
  let dpos = ts_optional_sign_end s len in
  if len = 0 || dpos >= len then false
  else
    let c = fs_byte_at s dpos in
    if c = 0x2E then
      // '.' [0-9]+ EXPONENT
      let fpos = dpos + 1 in
      if fpos >= len then false
      else
        let fend = ts_scan_digits s len fpos in
        fend > fpos && ts_exponent_suffix s len fend
    else if ts_digit_byte c then
      // [0-9]+ ( '.' [0-9]* )? EXPONENT — covers both the digit+ '.'
      // digit* EXPONENT and the digit+ EXPONENT (no dot) alternatives.
      let iend = ts_scan_digits s len dpos in
      if iend < len && fs_byte_at s iend = 0x2E then
        let fpos = iend + 1 in
        let fend = ts_scan_digits s len fpos in
        ts_exponent_suffix s len fend
      else
        ts_exponent_suffix s len iend
    else false

let is_turtle_boolean_lexical (s : string) : Tot bool =
  s = "true" || s = "false"

// Some bare text when the datatype is xsd:integer / xsd:decimal /
// xsd:double / xsd:boolean AND the lexical form matches the matching
// terminal; None otherwise (the caller prints the quoted form).
// https://github.com/danbri/factoidal/issues/681
let literal_shorthand (l : literal) : option string =
  if l.datatype = xsd_integer && is_turtle_integer_lexical l.lexical_form then
    Some l.lexical_form
  else if l.datatype = xsd_decimal && is_turtle_decimal_lexical l.lexical_form then
    Some l.lexical_form
  else if l.datatype = xsd_double && is_turtle_double_lexical l.lexical_form then
    Some l.lexical_form
  else if l.datatype = xsd_boolean && is_turtle_boolean_lexical l.lexical_form then
    Some l.lexical_form
  else None

// ---------------------------------------------------------------
// 2. Term / subject / predicate rendering.
//
// Numeric and boolean literals ARE sugared to the bare Turtle form
// (`42`, `true`) when `shorthand` is set AND the lexical form matches
// the grammar terminal for the literal's datatype (`literal_shorthand`
// above) — https://github.com/danbri/factoidal/issues/681, superseding
// this module's 2026-07-04 quoted-only decision. When the lexical form
// does not qualify (e.g. `"5."^^xsd:decimal`, or a value with a
// leading/trailing space) the quoted+datatype form is printed
// unchanged, so the printed text always reads back to the same
// (lexical form, datatype) pair. The datatype IRI itself IS
// prefix-abbreviated in the quoted form, since that's pure compaction
// with no ambiguity risk.
// ---------------------------------------------------------------

let rec ts_term_to_turtle (table : prefix_table) (shorthand : bool) (t : rdf_term) : Tot string (decreases t) =
  match t with
  | T_IRI i -> ts_abbreviate_iri table i
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let esc = nq_escape_literal l.lexical_form in
    (match l.lang_tag with
     | Some tag ->
       // RDF 1.2 directional language string: append `--ltr`/`--rtl`.
       // Empty for RDF 1.1 langString (direction = None).
       let ds = (match l.direction with
                 | Some Dir_LTR -> "--ltr"
                 | Some Dir_RTL -> "--rtl"
                 | None -> "") in
       "\"" ^ esc ^ "\"@" ^ tag ^ ds
     | None ->
       if l.datatype = xsd_string then "\"" ^ esc ^ "\""
       else
         match (if shorthand then literal_shorthand l else None) with
         | Some bare -> bare
         | None -> "\"" ^ esc ^ "\"^^" ^ ts_abbreviate_iri table l.datatype)
  | T_TripleTerm s p o ->
    // RDF 1.2 triple term `<<( s p o )>>` (Turtle 1.2 object position).
    let subj_str = (match s with
                    | S_IRI i   -> ts_abbreviate_iri table i
                    | S_BNode b -> "_:" ^ b) in
    let pred_str = (if p = rdf_type then "a" else ts_abbreviate_iri table p) in
    "<<( " ^ subj_str ^ " " ^ pred_str ^ " " ^ ts_term_to_turtle table shorthand o ^ " )>>"

let ts_subject_to_turtle (table : prefix_table) (s : subject) : Tot string =
  match s with
  | S_IRI i -> ts_abbreviate_iri table i
  | S_BNode b -> "_:" ^ b

// `a` is Turtle's built-in shorthand for rdf:type (Parser.Turtle.
// parse_a_keyword accepts it back), used unconditionally when the
// predicate is rdf:type — no prefix-table entry needed for it at all.
let ts_predicate_to_turtle (table : prefix_table) (p : wf_iri) : Tot string =
  if p = rdf_type then "a"
  else ts_abbreviate_iri table p

// ---------------------------------------------------------------
// ROUND-TRIP SCOPE (issue #448 assurance triage, module 3). The
// natural correctness anchor for a wire serializer this module's
// banner names is `parse_term (serialize_term t) == Some t`. That
// full term-level theorem, and even a concrete `assert_norm` WITNESS
// BATTERY over specific literals (the brief's own fallback), are
// BOTH currently out of reach for this module — verified empirically
// this session, not merely inherited from precedent:
//
//   `let probe () : Lemma (nq_escape_literal "a" == "a") = ()`
//   -- Error 19, "Could not prove post-condition", even for the
//      TRIVIAL escape-free single-ASCII-char case.
//
// Root cause (matches RDF.NTriples.RoundTrip.fst's FINDING 1/2,
// confirmed still true post the 2026-08-10 FastString re-founding —
// Parser.FastString.fsti's six hot primitives are Spec-BACKED now
// but remain OPAQUE `val`s to every consumer; only an explicit
// `fs_*_eq` bridging-lemma invocation (not the normalizer, and not
// `assert_norm`, which never touches SMT) gives a caller computational
// power over them): `ts_term_to_turtle`'s literal branch calls
// `RDF.NQuads.Serialize.nq_escape_literal` (see banner above, "Reuse,
// not reinvention"), which walks its input via `fs_byte_at`/
// `fs_byte_length` unconditionally — so the SERIALIZER side already
// fails to reduce on a concrete literal, before `Parser.Turtle.
// parse_turtle_literal` (built on the same primitives) is even
// reached. A full SMT-driven proof through the `fs_*_eq` bridging
// lemmas is possible in principle (that is exactly what
// `SPARQL11.Parser.TokenRoundTrip.fst` does for the SPARQL tokenizer)
// but that module's own commissioning note records "4+ hours burned,
// only the delimiter-token fragment landed" for a narrower, non-
// escape-processing grammar — properly out of this module's scope
// per the task brief's own escape valve ("if term-level proof is out
// of reach in the time... report as a finding").
//
// What IS proved instead, honestly scoped to what does NOT need
// concrete FastString reduction: `lemma_ts_abbreviate_iri_pname_safe`
// above is a UNIVERSALLY QUANTIFIED structural fact about
// `ts_abbreviate_iri` — it never needs the SMT context to know what
// `fs_byte_sub`/`fs_byte_length` COMPUTE on a specific string, only
// that `ts_abbreviate_iri`'s own case split matches its own
// postcondition, which is closed by unfolding definitions, not by
// primitive-VALUE reasoning. Wire correctness of the literal path is
// instead pinned at the CLI level (re-parse through the compiled
// binary, `tests/local/turtle_pretty_serialize_roundtrip.sh`) — a
// real end-to-end check, just not a machine-checked F* proof.
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// 3. Subject-grouped body rendering.
//
// Sort the graph with RDF.Graph.Executable.triple_cmp (same key
// discipline as the closure-path dedup: subject key, unit-sep,
// predicate, unit-sep, object key — 0x1F is documented there as
// forbidden in IRIs, so no ambiguity), then walk the sorted list once,
// grouping runs of equal subject (via subject_eq) into one block and
// runs of equal predicate within a subject (via wf_iri string
// equality) into one `;`-separated entry with a `,`-separated object
// list. One pass, no re-scans.
// ---------------------------------------------------------------

noeq type subj_state = {
  ss_subj : subject;              // raw subject, for subject_eq boundary test
  ss_subj_text : string;          // rendered (compacted) subject
  ss_cur_pred : wf_iri;           // raw predicate of the in-progress run
  ss_cur_pred_text : string;      // rendered predicate ("a" or compacted)
  ss_cur_objs : list string;      // objects of the in-progress run, reverse order
  ss_pred_chunks : list string;   // finished "pred obj , obj" groups, reverse order
}

let finish_pred (st : subj_state) : list string =
  let objs = List.Tot.rev st.ss_cur_objs in
  let group = st.ss_cur_pred_text ^ " " ^ join_with " , " objs in
  group :: st.ss_pred_chunks

let finish_subj (st : subj_state) : string =
  let chunks = List.Tot.rev (finish_pred st) in
  st.ss_subj_text ^ " " ^ join_with " ;\n    " chunks ^ " .\n\n"

let rec walk_triples (table : prefix_table) (shorthand : bool) (sorted : rdf_graph)
    (st : option subj_state) (acc : list string)
  : Tot (list string) (decreases sorted) =
  match sorted with
  | [] ->
    (match st with
     | None -> acc
     | Some s -> finish_subj s :: acc)
  | t :: rest ->
    let obj_text = ts_term_to_turtle table shorthand t.o in
    (match st with
     | None ->
       let st' = { ss_subj = t.s; ss_subj_text = ts_subject_to_turtle table t.s;
                   ss_cur_pred = t.p; ss_cur_pred_text = ts_predicate_to_turtle table t.p;
                   ss_cur_objs = [obj_text]; ss_pred_chunks = [] } in
       walk_triples table shorthand rest (Some st') acc
     | Some s ->
       if subject_eq s.ss_subj t.s then
         if s.ss_cur_pred = t.p then
           let s' = { s with ss_cur_objs = obj_text :: s.ss_cur_objs } in
           walk_triples table shorthand rest (Some s') acc
         else
           let pred_chunks' = finish_pred s in
           let s' = { s with ss_cur_pred = t.p;
                             ss_cur_pred_text = ts_predicate_to_turtle table t.p;
                             ss_cur_objs = [obj_text];
                             ss_pred_chunks = pred_chunks' } in
           walk_triples table shorthand rest (Some s') acc
       else
         let block = finish_subj s in
         let st' = { ss_subj = t.s; ss_subj_text = ts_subject_to_turtle table t.s;
                     ss_cur_pred = t.p; ss_cur_pred_text = ts_predicate_to_turtle table t.p;
                     ss_cur_objs = [obj_text]; ss_pred_chunks = [] } in
         walk_triples table shorthand rest (Some st') (block :: acc))

let render_triples (table : prefix_table) (shorthand : bool) (g : rdf_graph) : Tot string =
  let sorted = List.Tot.sortWith triple_cmp g in
  let blocks = walk_triples table shorthand sorted None [] in
  String.concat "" (List.Tot.rev blocks)

// ---------------------------------------------------------------
// 4. `@prefix` header + top-level entry point.
// ---------------------------------------------------------------

let rec render_prefix_header (table : prefix_table) : Tot (list string) (decreases table) =
  match table with
  | [] -> []
  | (ns, abbr) :: rest ->
    ("@prefix " ^ abbr ^ " <" ^ ns ^ "> .\n") :: render_prefix_header rest

val turtle_of_graph : list (string * string) -> bool -> rdf_graph -> Tot string
let turtle_of_graph table shorthand g =
  let header_lines = render_prefix_header table in
  let header = String.concat "" header_lines in
  let sep = (match header_lines with [] -> "" | _ -> "\n") in
  let body = render_triples table shorthand g in
  header ^ sep ^ body

// ---------------------------------------------------------------
// 5. Auto prefix-table derivation.
//
// "Split at last # or /, top ~8 namespaces by count" (owner brief).
// A namespace only counts toward the frequency table when the IRI's
// remainder past the split point is itself PN_LOCAL-safe — a
// namespace whose IRIs never compact cleanly isn't worth a header
// line (the per-term fallback in ts_abbreviate_iri already covers the
// individual-IRI case regardless of what's in the table). Common
// well-known namespaces (rdf/rdfs/xsd/owl/foaf/dcterms/dc/schema) are
// preferred over auto-numbered "nsN:" labels when they're actually
// present, since real graphs are dominated by rdf:type / xsd datatypes
// and a numbered prefix for those would be needless ugliness — the
// same "not gratuitously ugly" goal this whole module serves.
// ---------------------------------------------------------------

// Find the LAST '#' (0x23) or '/' (0x2F) byte position in s.
let rec last_ns_split_from (s : string) (len : nat) (pos : nat) (best : option nat)
  : Tot (option nat) (decreases (len - pos)) =
  if pos >= len then best
  else
    let b = fs_byte_at s pos in
    if b = 0x23 || b = 0x2F then last_ns_split_from s len (pos + 1) (Some pos)
    else last_ns_split_from s len (pos + 1) best

let last_ns_split (s : string) : option nat =
  last_ns_split_from s (fs_byte_length s) 0 None

// Split at the last '#'/'/' into (namespace-including-delimiter, local).
// None when the IRI has neither (can't be namespace-compacted at all).
let ns_split (iri : string) : option (string * string) =
  match last_ns_split iri with
  | None -> None
  | Some idx ->
    let len = fs_byte_length iri in
    // Guard makes the subtraction provably a nat; last_ns_split
    // returns an in-bounds index but carries no refinement saying so.
    if idx + 1 <= len then
      let ns = fs_byte_sub iri 0 (idx + 1) in
      let local = fs_byte_sub iri (idx + 1) (len - (idx + 1)) in
      Some (ns, local)
    else None

// Every IRI occurring anywhere in the graph: subjects, predicates,
// object IRIs, and literal datatypes (skipping the implicit
// xsd:string / rdf:langString cases, which are never printed with a
// datatype suffix). Cons-only accumulation — O(n) total.
let rec collect_iris_acc (g : rdf_graph) (acc : list string)
  : Tot (list string) (decreases g) =
  match g with
  | [] -> acc
  | t :: rest ->
    let acc1 = t.p :: acc in
    let acc2 = (match t.s with S_IRI i -> i :: acc1 | S_BNode _ -> acc1) in
    let acc3 =
      (match t.o with
       | T_IRI i -> i :: acc2
       | T_BNode _ -> acc2
       | T_Literal l ->
         (match l.lang_tag with
          | Some _ -> acc2
          | None -> if l.datatype = xsd_string then acc2 else l.datatype :: acc2)
       // RDF 1.2 triple term: conservatively skip collecting the IRIs
       // nested inside it — correctness is preserved (those IRIs simply
       // print un-abbreviated), which is acceptable for the pretty path.
       | T_TripleTerm _ _ _ -> acc2)
    in
    collect_iris_acc rest acc3

// Namespaces worth counting: split succeeds, remainder non-empty and
// PN_LOCAL-safe.
let rec candidate_namespaces_acc (iris : list string) (acc : list string)
  : Tot (list string) (decreases iris) =
  match iris with
  | [] -> acc
  | i :: rest ->
    (match ns_split i with
     | None -> candidate_namespaces_acc rest acc
     | Some (ns, local) ->
       if fs_byte_length local > 0 && validate_pn_local local then
         candidate_namespaces_acc rest (ns :: acc)
       else
         candidate_namespaces_acc rest acc)

// Run-length count a SORTED string list into (value, count) pairs.
let rec count_runs (sorted : list string) : Tot (list (string * nat)) (decreases sorted) =
  match sorted with
  | [] -> []
  | [x] -> [(x, 1)]
  | x :: y :: rest ->
    if x = y then
      (match count_runs (y :: rest) with
       | (y', n) :: more -> (y', n + 1) :: more
       | [] -> [(x, 1)])
    else
      (x, 1) :: count_runs (y :: rest)

let count_desc_compare (a b : (string * nat)) : int =
  if snd a = snd b then 0
  else if snd a > snd b then -1
  else 1

// Single-digit label suffix — the table is capped at 8 entries, so the
// auto-numbered slots ("ns1:".."ns8:") never need more than one digit.
let digit_char (n : nat{n < 10}) : string =
  match n with
  | 0 -> "0" | 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
  | 5 -> "5" | 6 -> "6" | 7 -> "7" | 8 -> "8" | _ -> "9"

// NOT List.Tot.splitAt: F-star's splitAt is total for any n, but it
// extracts to BatList.split_nth, which THROWS when n exceeds the
// list length (crashed live 2026-07-04 on graphs with fewer than 8
// fresh namespaces). take_at_most is total in both worlds.
let rec take_at_most (n : nat) (l : list (string * nat))
  : Tot (list (string * nat)) (decreases l) =
  if n = 0 then []
  else match l with
       | [] -> []
       | hd :: tl -> hd :: take_at_most (n - 1) tl

// Auto-numbered labels "ns1:".."ns8:", skipping any label already
// reserved by the caller's table or the well-known-prefix table
// (issue #681) — so a caller label "ns1:" is never reassigned to a
// different namespace. `reserved` and `idx` both stay fixed across the
// skip-a-reserved-label retry, so the decreases metric combines the
// namespace list shrinking (every successful assignment) with the
// idx<10 bound shrinking (every retry) into one strictly-decreasing nat.
let rec assign_labels_avoiding (reserved : list string) (idx : nat{idx < 10})
    (namespaces : list (string * nat))
  : Tot (list (string * string)) (decreases (List.Tot.length namespaces + (9 - idx))) =
  match namespaces with
  | [] -> []
  | (ns, _) :: rest ->
    if idx >= 9 then []  // table is capped well below 9 entries; defensive stop
    else
      let label = "ns" ^ digit_char idx ^ ":" in
      if List.Tot.mem label reserved then
        assign_labels_avoiding reserved (idx + 1) namespaces
      else
        (ns, label) :: assign_labels_avoiding reserved (idx + 1) rest

// Does any IRI in the graph fall under namespace `ns`?
let rec ts_any_iri_uses_ns (iris : list string) (ns : string) : Tot bool (decreases iris) =
  match iris with
  | [] -> false
  | i :: rest -> if ts_starts_with_strict i ns then true else ts_any_iri_uses_ns rest ns

// The caller's pairs whose namespace some IRI of the graph uses, kept
// in the caller's order; first occurrence of a namespace wins (a
// namespace repeated later in the caller's table is dropped even if
// the first occurrence went unused), and a namespace no IRI uses is
// not emitted at all.
let rec ts_user_used (iris : list string) (caller : prefix_table) (seen_ns : list string)
  : Tot prefix_table (decreases caller) =
  match caller with
  | [] -> []
  | (ns, label) :: rest ->
    if List.Tot.mem ns seen_ns then ts_user_used iris rest seen_ns
    else if ts_any_iri_uses_ns iris ns then (ns, label) :: ts_user_used iris rest (ns :: seen_ns)
    else ts_user_used iris rest (ns :: seen_ns)

// A small, self-contained set of well-known namespaces, preferred over
// auto-numbered labels when present in the graph. Deliberately NOT
// shared with RDF.Pretty.cli_turtle_prefixes: that table serves a
// display-only (non-round-trip) caller and pulling it in would add an
// unrelated SPARQL11.Algebra dependency edge to this module for eight
// string literals.
let well_known_prefixes : prefix_table = [
  ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#",           "xsd:");
  ("http://www.w3.org/2002/07/owl#",              "owl:");
  ("http://xmlns.com/foaf/0.1/",                  "foaf:");
  ("http://purl.org/dc/terms/",                   "dcterms:");
  ("http://purl.org/dc/elements/1.1/",            "dc:");
  ("http://schema.org/",                          "schema:");
]

let known_prefixes_used (present_namespaces : list string) : list (string * string) =
  List.Tot.filter (fun (ns, _) -> List.Tot.mem ns present_namespaces) well_known_prefixes

// The generalisation of turtle_of_graph_auto (issue #681):
// opts.tro_prefixes wins over the auto-derived table, and
// opts.tro_literal_shorthand switches bare numeric/boolean printing
// on or off.
let turtle_of_graph_opts (opts : turtle_render_options) (g : rdf_graph) : Tot string =
  let iris = collect_iris_acc g [] in
  let candidates = candidate_namespaces_acc iris [] in
  let sorted_candidates = List.Tot.sortWith String.compare candidates in
  let counted = count_runs sorted_candidates in
  let present_ns = List.Tot.map fst counted in
  let user_used = ts_user_used iris opts.tro_prefixes [] in
  let user_used_ns = List.Tot.map fst user_used in
  let user_used_labels = List.Tot.map snd user_used in
  let known0 = known_prefixes_used present_ns in
  let known = List.Tot.filter
    (fun (ns, label) -> not (List.Tot.mem ns user_used_ns) && not (List.Tot.mem label user_used_labels))
    known0 in
  let known_ns = List.Tot.map fst known in
  let known_labels = List.Tot.map snd known in
  let covered_ns = user_used_ns @ known_ns in
  let counted_by_freq = List.Tot.sortWith count_desc_compare counted in
  let fresh = List.Tot.filter (fun (ns, _) -> not (List.Tot.mem ns covered_ns)) counted_by_freq in
  let covered_len = List.Tot.length user_used + List.Tot.length known in
  let budget : nat = if covered_len >= 8 then 0 else 8 - covered_len in
  let fresh_top = take_at_most budget fresh in
  let reserved_labels = user_used_labels @ known_labels in
  let auto = assign_labels_avoiding reserved_labels 1 fresh_top in
  let table = user_used @ known @ auto in
  turtle_of_graph table opts.tro_literal_shorthand g

let turtle_of_graph_auto (g : rdf_graph) : Tot string =
  turtle_of_graph_opts turtle_render_defaults g
