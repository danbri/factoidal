module CSVW.URITemplate

// Stage 3 of the CSVW program plan
// (docs/designissues/2026-07-05-csvw-program-plan.md): the RFC 6570
// URI Template subset the vendored csv2rdf/csv2json corpus actually
// exercises for aboutUrl/propertyUrl/valueUrl — confirmed by the
// plan's own corpus survey ("URI templates: RFC 6570 Levels 1-2 only,
// confirmed by corpus survey, not guessed"): plain `{var}` simple
// string expansion (Level 1) and `{#var}` fragment expansion (the
// fragment half of Level 2). No reserved-string expansion (`{+var}`),
// no query-form (`{?var}`), no path-segment (`{/var}`), no
// multi-variable lists, no prefix/explode modifiers — extend this
// module's grammar if a future fixture needs more (plan's Open
// decision 3), rather than reaching for a general RFC 6570 library.
//
// CSVW's own special row-scoped variables (`_row`, `_sourceRow`,
// `_name` — the leading underscore is CSVW's convention, not an RFC
// 6570 feature) are resolved the same way as ordinary column-name
// variables: via the caller-supplied `lookup` function. This module
// has no CSVW-specific knowledge of what those names mean — that is
// CSVW.Conversion.fst's job (it builds the `lookup` closure per row/
// column).
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open SPARQL11.Algebra   // reused: is_uri_unreserved, percent_encode_char, string_encode_uri

// ------------------------------------------------------------------
// 1. Tokenizing a template string into literal runs and `{...}`
//    variable references. Mirrors RML.Mapping.fst's
//    scan_template_acc/parse_template idiom (mode = inside braces or
//    not); no backslash-escape handling — RFC 6570 templates don't
//    define brace-escaping, and the corpus survey found none needed.
// ------------------------------------------------------------------

// A variable reference's raw text between `{` and `}`, VERBATIM
// (including a leading '#' for the fragment-operator form, if
// present) — split into "is this a fragment expansion" and "the bare
// variable name" only at expansion time (csvw_var_is_fragment /
// csvw_var_name below), mirroring how RML.Mapping keeps
// TSeg_Reference's body raw until eval time.
noeq type csvw_template_segment =
  | CT_Literal : string -> csvw_template_segment
  | CT_Var     : string -> csvw_template_segment

// Fuel = String.length s + 1 is always sufficient: pos advances by
// exactly 1 every call, so the number of calls until pos >= len is
// bounded by len. Same idiom as RDF.Term.fsti's string_has_colon_from
// and RML.Mapping.fst's scan_template_acc.
let csvw_flush_template_buf (mode : bool) (buf : string) (acc : list csvw_template_segment)
  : list csvw_template_segment =
  if buf = "" then acc
  else if mode then (CT_Var buf) :: acc       // unterminated "{...": keep the partial var, don't drop data
  else (CT_Literal buf) :: acc

let rec csvw_scan_template_acc
    (s : string) (pos : nat) (fuel : nat) (mode : bool) (buf : string)
    (acc : list csvw_template_segment)
  : Tot (list csvw_template_segment) (decreases fuel) =
  if fuel = 0 then csvw_flush_template_buf mode buf acc
  else
    let len = String.length s in
    if pos >= len then csvw_flush_template_buf mode buf acc
    else
      let c = FStar.Char.int_of_char (String.index s pos) in
      if (not mode) && c = 0x7B (* '{' *) then
        let acc' = if buf = "" then acc else (CT_Literal buf) :: acc in
        csvw_scan_template_acc s (pos + 1) (fuel - 1) true "" acc'
      else if mode && c = 0x7D (* '}' *) then
        csvw_scan_template_acc s (pos + 1) (fuel - 1) false "" ((CT_Var buf) :: acc)
      else
        csvw_scan_template_acc s (pos + 1) (fuel - 1) mode (buf ^ String.sub s pos 1) acc

let csvw_parse_template (s : string) : list csvw_template_segment =
  List.Tot.rev (csvw_scan_template_acc s 0 (String.length s + 1) false "" [])

// ------------------------------------------------------------------
// 2. Fragment-operator percent-encoding (RFC 6570 section 3.2.3's
//    "reserved" expansion): unreserved chars (already exactly
//    SPARQL11.Algebra's is_uri_unreserved set — ALPHA/DIGIT/-._~,
//    also RFC 6570's "unreserved" production) PLUS the gen-delims and
//    sub-delims stay raw; everything else is percent-encoded. This is
//    a strictly larger pass-through set than Level 1's plain
//    substitution (string_encode_uri, reused as-is below), matching
//    "#gid-{GID}"-style templates where the fragment body may itself
//    carry a literal '#'/':' etc. from the referenced column value.
// ------------------------------------------------------------------

let is_uri_reserved_gen_sub_delim (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code = 0x3A (* : *) || code = 0x2F (* / *) || code = 0x3F (* ? *) || code = 0x23 (* # *) ||
  code = 0x5B (* [ *) || code = 0x5D (* ] *) || code = 0x40 (* @ *) ||
  code = 0x21 (* ! *) || code = 0x24 (* $ *) || code = 0x26 (* & *) || code = 0x27 (* ' *) ||
  code = 0x28 (* ( *) || code = 0x29 (* ) *) || code = 0x2A (* * *) || code = 0x2B (* + *) ||
  code = 0x2C (* , *) || code = 0x3B (* ; *) || code = 0x3D (* = *)

let is_uri_reserved_or_unreserved (c : FStar.Char.char) : bool =
  is_uri_unreserved c || is_uri_reserved_gen_sub_delim c

let rec csvw_encode_fragment_chars (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: rest ->
    if is_uri_reserved_or_unreserved c then c :: csvw_encode_fragment_chars rest
    else List.Tot.append (percent_encode_char c) (csvw_encode_fragment_chars rest)

let csvw_encode_fragment (s : string) : string =
  String.string_of_list (csvw_encode_fragment_chars (String.list_of_string s))

// ------------------------------------------------------------------
// 3. Variable-reference shape: does this `{...}` body use the
//    fragment operator, and what is the bare variable name.
// ------------------------------------------------------------------

let csvw_var_is_fragment (v : string) : bool =
  String.length v > 0 && String.sub v 0 1 = "#"

let csvw_var_name (v : string) : string =
  if csvw_var_is_fragment v then String.sub v 1 (String.length v - 1) else v

// ------------------------------------------------------------------
// 4. Expansion. `lookup` resolves a bare variable name (column name,
//    or one of CSVW's `_row`/`_sourceRow`/`_name` special variables —
//    this module has no opinion on which) to its current string
//    value; `None` (undefined variable) expands to the empty string,
//    per RFC 6570's "undefined variables ... produce no output for
//    that expression" — CSVW.Conversion.fst's lookup closures only
//    return `None` for a variable that genuinely has no binding in
//    the current row/column context.
// ------------------------------------------------------------------

let csvw_expand_segment (lookup : string -> option string) (seg : csvw_template_segment) : string =
  match seg with
  | CT_Literal l -> l
  | CT_Var v ->
    let raw = (match lookup (csvw_var_name v) with Some s -> s | None -> "") in
    if csvw_var_is_fragment v then csvw_encode_fragment raw else string_encode_uri raw

let rec csvw_expand_segments (lookup : string -> option string) (segs : list csvw_template_segment)
  : Tot string (decreases segs) =
  match segs with
  | [] -> ""
  | s :: rest -> csvw_expand_segment lookup s ^ csvw_expand_segments lookup rest

// Top-level entry point: expand a raw template string (as stored
// verbatim in CSVW.Metadata's col_about_url/col_property_url/
// col_value_url/ts_about_url/... fields) against a row/column-scoped
// variable lookup, producing a (possibly still relative) URI
// reference string. Resolving that reference against a base IRI is
// CSVW.Conversion.fst's job (it depends on the document's base IRI,
// which this module doesn't know about).
let csvw_expand_template (lookup : string -> option string) (raw : string) : string =
  csvw_expand_segments lookup (csvw_parse_template raw)
