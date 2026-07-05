module RML.Sources

// Stages 2-3 of the RML program plan
// (docs/designissues/2026-07-05-rml-program-plan.md): the logical-source
// iterator model. Stage 2 (JSON): the JSONPath subset evaluator walking
// Parser.JSON's json_val tree. Stage 3 (CSV, this module's newest
// section, part 5 below): an RFC 4180 tokenizer + the CSV logical
// source's row-binding model. XML (Stage 4) is deliberately not
// modelled here yet — RML.Mapping's reference_formulation/source_root
// enums already anticipate it.
//
// Per the plan's module-plan section, the CSV tokenizer lives HERE
// (RML.Sources.fst), not in a new Parser.CSV.fst — the plan's own
// module-plan text says "RML.Sources.fst — ... and a small new CSV
// tokenizer", and separately rules out reusing Parser.CSVResults.fst
// (the SPARQL 1.1 CSV/TSV *results* format — a different dialect:
// bare IRIs / typed-literal lexical conventions belong to that format,
// not to arbitrary RFC 4180 tabular data).
//
// JSONPath subset surveyed directly from the vendored rml-core suite (see
// the plan's "JSONPath/XPath: F* subset, not assume-val" section): "$",
// dotted field steps ("$.Name", "$.manager.name"), array wildcards
// ("$.amounts[*]", "$.companies[*].departments[*].employees[*]"), and
// field wildcards ("$.v1.*"). No filter expressions, no recursive
// descent, no slices, no unions appear anywhere in the corpus, so none
// are implemented here. The one root-is-an-array shape ("$[*]", no field
// step before the bracket — RMLTC0012e) is also covered.
//
// IRON RULES:
//   - F* is the source of truth (rule #1); this is mapping semantics
//     (path matching), not I/O, so it belongs in F* per rule #4/#7/#11 —
//     see the plan's rationale for why this isn't an assume-val.
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open Parser.JSON

// ------------------------------------------------------------------
// 1. Logical-source rows. Only the JSON variant is populated this
//    stage; CSV/XML join the sum type in Stages 3/4.
// ------------------------------------------------------------------

noeq type source_row =
  | Row_JSON : json_val -> source_row
  | Row_CSV  : list (string & string) -> source_row

let source_row_json (r : source_row) : json_val =
  match r with
  | Row_JSON v -> v
  | Row_CSV _ -> JNull

let source_row_csv (r : source_row) : list (string & string) =
  match r with
  | Row_CSV b -> b
  | Row_JSON _ -> []

// ------------------------------------------------------------------
// 2. JSONPath subset AST + tokenizer.
// ------------------------------------------------------------------

type jsonpath_step =
  | JPS_Field    : string -> jsonpath_step
  | JPS_Wildcard : jsonpath_step

// Position after a run of characters that are neither '.' (0x2E) nor
// '[' (0x5B) — a field-name run.
let rec scan_field_name (s : string) (pos : nat) (fuel : nat) (buf : string)
  : Tot string (decreases fuel) =
  if fuel = 0 then buf
  else
    let len = String.length s in
    if pos >= len then buf
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if c = 0x2E || c = 0x5B then buf
      else scan_field_name s (pos + 1) (fuel - 1) (buf ^ String.sub s pos 1)

let rec field_name_end (s : string) (pos : nat) (fuel : nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length s in
    if pos >= len then pos
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if c = 0x2E || c = 0x5B then pos
      else field_name_end s (pos + 1) (fuel - 1)

// Position of the next occurrence of the quote byte `q` at or after
// `pos`, or `len` if it doesn't occur (matches field_name_end's "not
// found -> end of string" convention). Used for bracket-quoted field
// names ("$['Country Code']", "$['ISO 3166']" — RMLTC0010a/b/c survey
// missed this bracket form in the plan's initial grep; corrected here).
let rec scan_to_quote (s : string) (pos : nat) (fuel : nat) (q : int)
  : Tot (p : nat { p >= pos }) (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length s in
    if pos >= len then pos
    else if FStar.Char.int_of_char (String.index s pos) = q then pos
    else scan_to_quote s (pos + 1) (fuel - 1) q

// Scan the token stream after the leading "$". Fuel = remaining string
// length + 1 is always sufficient: every branch advances pos by at
// least 1 (field-name runs advance by their length, which is >= 1 since
// scan_field_name only returns early with an empty buffer if pos hasn't
// moved — guarded by the field-name-end computation below advancing
// pos strictly).
let rec scan_jsonpath_acc (s : string) (pos : nat) (fuel : nat) (acc : list jsonpath_step)
  : Tot (list jsonpath_step) (decreases fuel) =
  if fuel = 0 then List.Tot.rev acc
  else
    let len = String.length s in
    if pos >= len then List.Tot.rev acc
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if c = 0x2E (* '.' *) then
        let pos1 = pos + 1 in
        if pos1 < len && FStar.Char.int_of_char (String.index s pos1) = 0x2A (* '*' *) then
          scan_jsonpath_acc s (pos1 + 1) (fuel - 1) (JPS_Wildcard :: acc)
        else
          let e = field_name_end s pos1 (fuel - 1) in
          let name = scan_field_name s pos1 (fuel - 1) "" in
          if e = pos1 then List.Tot.rev acc  // malformed: dot not followed by a name or '*'; stop
          else scan_jsonpath_acc s e (fuel - 1) (JPS_Field name :: acc)
      else if c = 0x5B (* '[' *) then
        let pos1 = pos + 1 in
        if pos1 + 1 < len
           && FStar.Char.int_of_char (String.index s pos1) = 0x2A (* '*' *)
           && FStar.Char.int_of_char (String.index s (pos1 + 1)) = 0x5D (* ']' *)
        then scan_jsonpath_acc s (pos1 + 2) (fuel - 1) (JPS_Wildcard :: acc)
        else
          let qc = if pos1 < len then FStar.Char.int_of_char (String.index s pos1) else (-1) in
          if qc = 0x27 (* ''' *) || qc = 0x22 (* '"' *) then
            // Bracket-quoted field name: $['Country Code'], $["ISO 3166"].
            // Needed for field names dotted notation can't express (spaces,
            // punctuation) — RMLTC0010a/b/c, RMLTC0010b's "ISO 3166".
            let name_start = pos1 + 1 in
            let qend = scan_to_quote s name_start (fuel - 1) qc in
            if qend < len && qend + 1 < len
               && FStar.Char.int_of_char (String.index s (qend + 1)) = 0x5D (* ']' *)
            then
              let name = String.sub s name_start (qend - name_start) in
              scan_jsonpath_acc s (qend + 2) (fuel - 1) (JPS_Field name :: acc)
            else List.Tot.rev acc  // unterminated quote; malformed, stop
          else List.Tot.rev acc  // malformed / unsupported bracket form; stop (narrow subset only)
      else List.Tot.rev acc  // unrecognized character; stop (narrow subset only)

// Position reached after scanning s from `pos`, mirroring
// scan_jsonpath_acc's exact transition rules but only tracking how far
// a well-formed JSONPath-subset expression extends (no step list built)
// — used to detect malformed paths. RMLTC0002g's iterator
// "$.students[*]]" (an extra, unmatched trailing "]") is exactly the
// case scan_jsonpath_acc's original design silently stops on rather
// than treats as an error (its `else -> stop` branches were written
// for "return what parsed so far", the right behavior for a step
// evaluator that must always terminate, but wrong for a validity
// check). Duplicates scan_jsonpath_acc's transition logic rather than
// refactoring that function's return type — the two "malformed, stop"
// branches below are the only ones that matter: whenever a real scan
// would bail out early (pos < len still), this validator's caller
// (jsonpath_is_valid) sees pos < len at the end and reports false.
let rec jsonpath_scan_end_pos (s : string) (pos : nat) (fuel : nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let len = String.length s in
    if pos >= len then pos
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if c = 0x2E (* '.' *) then
        let pos1 = pos + 1 in
        if pos1 < len && FStar.Char.int_of_char (String.index s pos1) = 0x2A (* '*' *) then
          jsonpath_scan_end_pos s (pos1 + 1) (fuel - 1)
        else
          let e = field_name_end s pos1 (fuel - 1) in
          if e = pos1 then pos  // dot not followed by a name or '*': malformed, stop here
          else jsonpath_scan_end_pos s e (fuel - 1)
      else if c = 0x5B (* '[' *) then
        let pos1 = pos + 1 in
        if pos1 + 1 < len
           && FStar.Char.int_of_char (String.index s pos1) = 0x2A (* '*' *)
           && FStar.Char.int_of_char (String.index s (pos1 + 1)) = 0x5D (* ']' *)
        then jsonpath_scan_end_pos s (pos1 + 2) (fuel - 1)
        else
          let qc = if pos1 < len then FStar.Char.int_of_char (String.index s pos1) else (-1) in
          if qc = 0x27 (* ''' *) || qc = 0x22 (* '"' *) then
            let name_start = pos1 + 1 in
            let qend = scan_to_quote s name_start (fuel - 1) qc in
            if qend < len && qend + 1 < len
               && FStar.Char.int_of_char (String.index s (qend + 1)) = 0x5D (* ']' *)
            then jsonpath_scan_end_pos s (qend + 2) (fuel - 1)
            else pos  // unterminated quote: malformed, stop here
          else pos  // malformed / unsupported bracket form: stop here
      else pos  // unrecognized character (e.g. a stray trailing ']'): stop here

// A JSONPath expression is well-formed (within this narrow subset) if
// scanning it consumes the whole string. The bare-field-name form (no
// leading "$") has no scanner to run against — it is always well-formed
// by construction (parse_jsonpath treats it as one literal field name).
let jsonpath_is_valid (s : string) : bool =
  let len = String.length s in
  if len = 0 then true
  else if FStar.Char.int_of_char (String.index s 0) = 0x24 (* '$' *) then
    jsonpath_scan_end_pos s 1 (len + 1) = len
  else true

// Parse a JSONPath expression. Leading "$" is required and stripped;
// everything after is tokenized by scan_jsonpath_acc. An empty
// reference yields no steps (identity — the context itself), a safe,
// inert default rather than a crash. A non-empty reference with no
// leading "$" is treated as a single bare field-name step (JPS_Field
// s verbatim, no further dot-splitting) — surveyed directly from
// rml-io's own suite (RMLSTC0011b/c's `rml:template
// "http://example.org/{name}"` against a `$.companies[*]`-iterated
// row: the subject map's bare "name" must resolve to that row's own
// "name" field, i.e. the same as "$.name" would). Stage 1/2's
// original JSONPath survey only grepped rml-core, which always uses
// a leading "$"; this corrects the gap once rml-io's suite is in
// scope (Stage 3).
let parse_jsonpath (s : string) : list jsonpath_step =
  let len = String.length s in
  if len = 0 then []
  else if FStar.Char.int_of_char (String.index s 0) = 0x24 (* '$' *) then
    scan_jsonpath_acc s 1 (len + 1) []
  else [JPS_Field s]

// ------------------------------------------------------------------
// 3. JSONPath subset evaluator: fan out a context set through a step
//    list. Structural recursion on `steps` — no fuel needed.
// ------------------------------------------------------------------

let json_field_lookup (name : string) (v : json_val) : list json_val =
  match v with
  | JObject _ ->
    (match json_get_field name v with
     | Some x -> [x]
     | None -> [])
  | _ -> []

let json_wildcard_fanout (v : json_val) : list json_val =
  match v with
  | JArray items -> items
  | JObject fields -> List.Tot.map snd fields
  | _ -> []

let rec eval_jsonpath_steps (ctxs : list json_val) (steps : list jsonpath_step)
  : Tot (list json_val) (decreases steps) =
  match steps with
  | [] -> ctxs
  | JPS_Field name :: rest ->
    eval_jsonpath_steps (List.Tot.concatMap (json_field_lookup name) ctxs) rest
  | JPS_Wildcard :: rest ->
    eval_jsonpath_steps (List.Tot.concatMap json_wildcard_fanout ctxs) rest

// Evaluate a JSONPath expression against a single root/context value,
// returning every matching leaf (0, 1, or many, depending on wildcards).
let eval_jsonpath (root : json_val) (path : string) : list json_val =
  eval_jsonpath_steps [root] (parse_jsonpath path)

// ------------------------------------------------------------------
// 4. Logical-source iteration: rml:iterator evaluated against the
//    parsed document root produces the row set. json_root is supplied
//    by the (OCaml-side, rule #11) caller that read + parsed the
//    logical source's file — reading files is I/O, this function is
//    pure path evaluation over an already-parsed tree.
// ------------------------------------------------------------------

// RMLTC0002g: an invalid iterator JSONPath ("$.students[*]]") means the
// logical source itself is malformed — a data error, per the spec's
// term-generation rules 12.2's "a valid RDF term cannot be produced" ->
// no iterations, not a best-effort partial parse of the well-formed
// prefix.
let json_iterate (json_root : json_val) (iterator : string) : list source_row =
  if not (jsonpath_is_valid iterator) then []
  else List.Tot.map Row_JSON (eval_jsonpath json_root iterator)

// rml:reference / template-reference-segment evaluation against one row.
let json_reference_values (row : source_row) (path : string) : list json_val =
  eval_jsonpath (source_row_json row) path

// ------------------------------------------------------------------
// 5. Stage 3: CSV logical source. An RFC 4180 tokenizer (quoted
//    fields via a leading `"` on an empty field buffer, `""` as the
//    in-quote escape for a literal `"`, embedded commas/newlines
//    inside a quoted field, bare `\r` dropped so both `\r\n` and
//    lone-`\n` line endings tokenize the same way) plus the
//    header-row -> per-row column-binding model rml:reference /
//    rml:template look up column names against (RMLSTC0007b,
//    RMLSTC0009a-10b, RMLSTC0004a-c's rml:null surveyed above).
//
//    Dialect surveyed directly from the vendored rml-io suite
//    (third_party/testing/rml-modules/rml-io/test-cases/RMLSTC00*):
//    header cells are unquoted in every fixture except RMLSTC0009a
//    (whose header is fully quoted, `"id","name","age"`, and is a
//    metadata.csv error=true fixture — "Source with quoted columns"),
//    and RMLSTC0010a/b (metadata.csv error=true, "invalid CSV
//    source") ship a data row with fewer fields than the header
//    (`id,name,age` vs a data row `6,Phoebe Buffay 37` — one field
//    short), which `all_rows_match_width` below treats as an invalid
//    source (no rows at all), not a truncated-binding row.
// ------------------------------------------------------------------

// Close out the field currently being scanned (push `buf` onto the
// reversed field-accumulator for the current row).
let flush_csv_field (buf : string) (row_acc : list string) : list string =
  buf :: row_acc

// Close out the row currently being scanned (push the field
// accumulator, un-reversed, onto the reversed row-accumulator).
let flush_csv_row (buf : string) (row_acc : list string) (rows_acc : list (list string))
  : list (list string) =
  (List.Tot.rev (flush_csv_field buf row_acc)) :: rows_acc

// Single-pass RFC 4180 scan. Fuel = String.length s + 1 is always
// sufficient — every branch advances `pos` by at least 1 (by 2 only
// on the doubled-quote-escape branch), same idiom as
// RML.Mapping.fst's scan_template_acc.
let rec csv_scan_acc
    (s : string) (pos : nat) (fuel : nat) (in_quotes : bool)
    (buf : string) (row_acc : list string) (rows_acc : list (list string))
  : Tot (list (list string)) (decreases fuel) =
  let finish () : list (list string) =
    List.Tot.rev (if buf <> "" || row_acc <> [] then flush_csv_row buf row_acc rows_acc else rows_acc) in
  if fuel = 0 then finish ()
  else
    let len = String.length s in
    if pos >= len then finish ()
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if in_quotes then
        if c = 0x22 (* '"' *) then
          if pos + 1 < len && FStar.Char.int_of_char (String.index s (pos + 1)) = 0x22
          then csv_scan_acc s (pos + 2) (fuel - 1) true (buf ^ "\"") row_acc rows_acc  // "" -> literal "
          else csv_scan_acc s (pos + 1) (fuel - 1) false buf row_acc rows_acc          // closing quote
        else
          csv_scan_acc s (pos + 1) (fuel - 1) true (buf ^ String.sub s pos 1) row_acc rows_acc
      else
        if c = 0x22 (* '"' *) && buf = "" then
          csv_scan_acc s (pos + 1) (fuel - 1) true buf row_acc rows_acc  // opening quote (only at field start)
        else if c = 0x2C (* ',' *) then
          csv_scan_acc s (pos + 1) (fuel - 1) false "" (flush_csv_field buf row_acc) rows_acc
        else if c = 0x0A (* '\n' *) then
          csv_scan_acc s (pos + 1) (fuel - 1) false "" [] (flush_csv_row buf row_acc rows_acc)
        else if c = 0x0D (* '\r' *) then
          csv_scan_acc s (pos + 1) (fuel - 1) false buf row_acc rows_acc  // drop CR; \r\n and lone \n both work
        else
          csv_scan_acc s (pos + 1) (fuel - 1) false (buf ^ String.sub s pos 1) row_acc rows_acc

// Tokenize a whole CSV document into rows of raw (unquoted, escape-
// resolved) cell strings. The first row (if any) is the header.
let csv_parse_rows (s : string) : list (list string) =
  csv_scan_acc s 0 (String.length s + 1) false "" [] []

let rec zip_strings (a : list string) (b : list string) : Tot (list (string & string)) (decreases a) =
  match a, b with
  | x :: xs, y :: ys -> (x, y) :: zip_strings xs ys
  | _, _ -> []

let rec all_rows_match_width (n : nat) (rows : list (list string)) : Tot bool (decreases rows) =
  match rows with
  | [] -> true
  | r :: rest -> (List.Tot.length r = n) && all_rows_match_width n rest

// Logical-source iteration for CSV: header row -> column names, every
// subsequent row -> a Row_CSV binding list with the `rml:null`-listed
// values (RMLSTC0004b/c) filtered out entirely (a filtered-out column
// makes csv_reference_values below return [], the same "no RDF term
// generated" outcome RML.Eval already gives a missing JSON field).
// A data row whose field count doesn't match the header's (RMLSTC0010a/
// b) invalidates the whole source — no rows at all — rather than
// silently truncating/padding the mismatched row.
let csv_iterate (csv_text : string) (null_values : list string) : list source_row =
  match csv_parse_rows csv_text with
  | [] -> []
  | header :: data_rows ->
    let header_len = List.Tot.length header in
    if not (all_rows_match_width header_len data_rows) then []
    else
      List.Tot.map
        (fun row ->
           let bindings = zip_strings header row in
           Row_CSV (List.Tot.filter (fun p -> not (List.Tot.mem (snd p) null_values)) bindings))
        data_rows

// rml:reference / template-reference-segment evaluation against one
// CSV row: a plain column-name lookup (CSV references are bare column
// names, not JSONPath — RMLSTC0007b's `rml:reference "name"`).
let csv_reference_values (row : source_row) (column : string) : list string =
  match row with
  | Row_CSV bindings ->
    (match List.Tot.assoc column bindings with
     | Some v -> [v]
     | None -> [])
  | Row_JSON _ -> []
