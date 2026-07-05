module RML.Sources

// Stage 2 of the RML program plan
// (docs/designissues/2026-07-05-rml-program-plan.md): the logical-source
// iterator model for JSON sources, plus a JSONPath subset evaluator
// walking Parser.JSON's json_val tree. CSV (Stage 3) and XML (Stage 4)
// logical sources are deliberately not modelled here yet — RML.Mapping's
// reference_formulation/source_root enums already anticipate them, but
// this module only implements the JSON path per the plan's staged table.
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

let source_row_json (r : source_row) : json_val =
  match r with
  | Row_JSON v -> v

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

// Parse a JSONPath expression. Leading "$" is required and stripped;
// everything after is tokenized by scan_jsonpath_acc. A path with no
// leading "$" (malformed per the narrow subset) yields no steps, which
// evaluates to the identity (the context itself) — a safe, inert default
// rather than a crash.
let parse_jsonpath (s : string) : list jsonpath_step =
  let len = String.length s in
  if len = 0 then []
  else if FStar.Char.int_of_char (String.index s 0) = 0x24 (* '$' *) then
    scan_jsonpath_acc s 1 (len + 1) []
  else []

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

let json_iterate (json_root : json_val) (iterator : string) : list source_row =
  List.Tot.map Row_JSON (eval_jsonpath json_root iterator)

// rml:reference / template-reference-segment evaluation against one row.
let json_reference_values (row : source_row) (path : string) : list json_val =
  eval_jsonpath (source_row_json row) path
