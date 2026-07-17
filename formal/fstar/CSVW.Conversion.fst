module CSVW.Conversion

// Stage 6+ of the CSVW program plan
// (docs/designissues/2026-07-05-csvw-program-plan.md): csv2rdf. Takes
// CSVW.Metadata's decoded AST plus already-tokenized CSV rows (via
// RML.Sources' shared RFC 4180 tokenizer — csv_parse_rows, coordinated
// with the RML program rather than forked) and produces RDF triples
// per the csv2rdf Recommendation's "Generating RDF" algorithm
// (w3.org/TR/csv2rdf §6, vendored at
// third_party/testing/csvw/csv2rdf/index.html, fetched directly and
// quoted inline below rather than guessed).
//
// STANDARD VS MINIMAL MODE — corrected against the vendored suite,
// not against the program plan's own guess. The plan's Fit section
// read the csv2rdf manifest's `noProv: true` on 270/270 entries as
// "the suite tests minimal-shaped output almost exclusively" and
// recommended building minimal mode first. Reading the actual checked
// -in fixtures (test001.ttl et al.) shows this is wrong: `noProv`
// suppresses PROV-vocabulary triples (never present in ANY fixture,
// minimal or standard), not the csvw:TableGroup/Table/Row wrapper —
// only 7 of 270 manifest-rdf.jsonld entries carry `minimal: true`
// (test027/029/031/033/035/037 family); the other 263 expect the FULL
// standard-mode wrapper (test001.ttl: csvw:TableGroup > csvw:table >
// csvw:row > csvw:describes > cell triples, with csvw:rownum/csvw:url
// provenance on each row). Both modes are implemented here
// (csvw_convert_table_standard / csvw_convert_table_minimal) since the
// suite genuinely needs both, not just the minimal target the plan
// predicted — see the runner's per-test mode selection.
//
// SCOPE / KNOWN GAPS (all deliberate, not oversights — see
// docs/designissues/2026-07-05-csvw-program-plan.md's stage table for
// what a later stage should pick up):
//   - Inherited properties (Stage 2): the full table-group -> table ->
//     tableSchema -> column chain is now built (csvw_merge_inherited /
//     csvw_build_col_specs below, over CSVW.Metadata's
//     csvw_inherited_props/csvw_group_meta) for seven of the eleven
//     tabular-metadata 5.1.1 properties — aboutUrl/propertyUrl/
//     valueUrl/datatype/lang/null/separator. `default`/`ordered`/
//     `required`/`textDirection` remain undecoded at any level (no
//     consumer here reads them yet) — a narrower slice than the full
//     eleven, not a claim of completeness.
//   - Table-group-level shared dialect/tableSchema (a table inside a
//     "tables": [...] array that has NO tableSchema/dialect of its
//     own, relying on the group's) is not decoded by CSVW.Metadata at
//     all yet, so such tables convert with no columns (empty output),
//     not a crash — an honest gap, not a defect.
//   - Datatype `format` facets (custom date patterns, groupChar/
//     decimalChar-driven numeric parsing, Y/N-style booleans — Stage 4
//     of the plan, XSD.Datatypes extension) are NOT applied: a cell's
//     raw text is used verbatim as the literal's lexical form, with
//     only the datatype IRI mapped from the `base` facet name. This
//     matches the spec's OWN algorithm text ("a datatype's format
//     annotation is irrelevant to the conversion procedure ... the
//     cell value has already been parsed according to the format
//     annotation" — Stage 4's job, upstream of this module) but this
//     module doesn't yet call into that upstream parse, so any fixture
//     whose expected output depends on format-driven reformatting
//     (not just passthrough) will not match.
//   - List-valued cells (the `separator`/`ordered` column facets) are
//     out of scope: CSVW.Metadata's csvw_column doesn't decode those
//     facets yet, so every cell is treated as a single scalar value.
//   - `commentPrefix`/`skipBlankRows`/`skipColumns` dialect options are
//     decoded by CSVW.Metadata but not applied here (only
//     `skipRows` + header-row-count are consumed) — a fixture relying
//     on comment-line skipping will misalign rows, not crash.
//   - Row/table/group node IDENTITY (an explicit `@id` on a table or
//     table group) is not decoded by CSVW.Metadata, so every table/
//     group/row node is a synthesized blank node — fine for the
//     isomorphism-insensitive-to-blank-node-labels comparison the
//     runner uses (matches bin/rml-runner's precedent), wrong if a
//     future consumer needed the node identified by a real IRI.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable   // triple/subject/rdf_term/literal, rdf_type, xsd_string/xsd_integer
open RDF.IRI                // resolve_iri_v2
open CSVW.Metadata
open CSVW.URITemplate
open CSVW.Formats             // UAX-35 number / date-time / boolean format engines
open SPARQL11.Algebra       // string_encode_uri (default propertyUrl's column-name encoding)
open Parser.JSON            // json_val + accessors, for common-property emission

// ================================================================
// csvw: vocabulary constants (w3.org/ns/csvw#). Local to this module
// — CSVW.Metadata has no vocabulary-table concept of its own (it only
// decodes the metadata JSON grammar), and this is the only module
// that emits csvw: triples.
// ================================================================

let csvw_ns : string = "http://www.w3.org/ns/csvw#"

let csvw_TableGroup : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "TableGroup")); csvw_ns ^ "TableGroup"
let csvw_Table : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "Table")); csvw_ns ^ "Table"
let csvw_Row : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "Row")); csvw_ns ^ "Row"
let csvw_table_pred : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "table")); csvw_ns ^ "table"
let csvw_row_pred : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "row")); csvw_ns ^ "row"
let csvw_rownum : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "rownum")); csvw_ns ^ "rownum"
let csvw_url_pred : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "url")); csvw_ns ^ "url"
let csvw_describes : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "describes")); csvw_ns ^ "describes"

// ================================================================
// Datatype-name -> RDF datatype IRI (csv2rdf §"Interpreting
// datatypes" table, quoted verbatim in the banner above). Every
// entry in the spec's table is literally "xsd:<name>" except three:
// html -> rdf:HTML, xml -> rdf:XMLLiteral, json -> csvw:JSON.
// ================================================================

// The four CSVW built-in datatype names that are NOT literally an
// xsd:<name> (tabular-metadata section 5.11.1 "Built-in datatypes"):
//   number  -> xsd:double        binary -> xsd:base64Binary
//   datetime-> xsd:dateTime      any    -> xsd:anyAtomicType
// plus the three non-XSD ones (html/xml/json). A `base`/`datatype`
// value that is itself an absolute URL (contains ':') — the
// datatype-@id-is-an-absolute-URL cases — is used verbatim.
let csvw_base_name_to_iri (n : string) : string =
  if n = "html" then "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML"
  else if n = "xml" then "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
  else if n = "json" then csvw_ns ^ "JSON"
  else if n = "number" then "http://www.w3.org/2001/XMLSchema#double"
  else if n = "binary" then "http://www.w3.org/2001/XMLSchema#base64Binary"
  else if n = "datetime" then "http://www.w3.org/2001/XMLSchema#dateTime"
  else if n = "any" then "http://www.w3.org/2001/XMLSchema#anyAtomicType"
  else if string_contains_colon n then n
  else "http://www.w3.org/2001/XMLSchema#" ^ n

// The datatype's own @id (object form) is the RDF datatype IRI when it
// is present and IRI-shaped (test242); otherwise the base facet's name
// maps through csvw_base_name_to_iri, defaulting to xsd:string.
let csvw_datatype_iri (dt : option csvw_datatype) : string =
  match dt with
  | None -> xsd_string
  | Some (CSVW_DT_Named n) -> csvw_base_name_to_iri n
  | Some (CSVW_DT_Object base_opt _ _ _ _ dtid _ _ _ _ _ _ _ _ _) ->
    let from_base = (match base_opt with Some n -> csvw_base_name_to_iri n | None -> xsd_string) in
    (match dtid with
     | Some idurl -> if string_contains_colon idurl then idurl else from_base
     | None -> from_base)

// Base-name of a datatype (object or shorthand), defaulting to "string".
let csvw_dt_base_name_of (dt : option csvw_datatype) : string =
  match dt with
  | Some (CSVW_DT_Named n) -> n
  | Some (CSVW_DT_Object bo _ _ _ _ _ _ _ _ _ _ _ _ _ _) ->
    (match bo with Some n -> n | None -> "string")
  | None -> "string"

// The UAX-35 format facets of a datatype, as a tuple:
// (format-string, number-pattern, groupChar, decimalChar). The
// string-form `format` (dates, boolean trueVal|falseVal, string-form
// number pattern) and the object-form numeric members are threaded into
// CSVW.Formats.csvw_format_convert by csvw_cell_object.
let csvw_dt_format_facets (dt : option csvw_datatype)
  : (option string & option string & option string & option string) =
  match dt with
  | Some (CSVW_DT_Object _ fmt pat grp dec _ _ _ _ _ _ _ _ _ _) -> (fmt, pat, grp, dec)
  | _ -> (None, None, None, None)

// The length + value constraint facets of a datatype, as a tuple:
// (length, minLength, maxLength, minimum, maximum, minInclusive,
//  maxInclusive, minExclusive, maxExclusive).
let csvw_dt_value_facets (dt : option csvw_datatype)
  : (option int & option int & option int & option string & option string &
     option string & option string & option string & option string) =
  match dt with
  | Some (CSVW_DT_Object _ _ _ _ _ _ len minl maxl mn mx mni mxi mne mxe) ->
    (len, minl, maxl, mn, mx, mni, mxi, mne, mxe)
  | _ -> (None, None, None, None, None, None, None, None, None)

// Length constraints on binary base types (base64Binary/hexBinary)
// count DECODED bytes, not lexical characters (tabular-metadata 4.6.1);
// decoding is out of scope here, so the char-length check is skipped for
// binary bases (fail open — keep the datatype) rather than mis-measured
// (test195: a 28-char base64 lexeme decodes to the constrained 19 bytes).
let csvw_is_binary_base (n : string) : bool =
  n = "base64Binary" || n = "hexBinary" || n = "binary"

let csvw_is_numeric_base (n : string) : bool =
  n = "number" || n = "decimal" || n = "integer" || n = "long" || n = "int" ||
  n = "short" || n = "byte" || n = "nonNegativeInteger" || n = "positiveInteger" ||
  n = "nonPositiveInteger" || n = "negativeInteger" || n = "unsignedLong" ||
  n = "unsignedInt" || n = "unsignedShort" || n = "unsignedByte" ||
  n = "double" || n = "float"

let rec csvw_conv_chars_cmp (a b : list FStar.Char.char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let ix = FStar.Char.int_of_char x in
    let iy = FStar.Char.int_of_char y in
    if ix < iy then -1 else if ix > iy then 1 else csvw_conv_chars_cmp xs ys

let csvw_conv_str_cmp (a b : string) : int =
  csvw_conv_chars_cmp (String.list_of_string a) (String.list_of_string b)

// Double-aware then plain scaled parse (rule #8) for numeric constraint
// comparison; None when either side is not a parseable number.
let csvw_num_cmp (a b : string) : option int =
  let pa = (match XSD.Datatypes.parse_double_to_scaled a with Some s -> Some s | None -> XSD.Datatypes.parse_to_scaled a) in
  let pb = (match XSD.Datatypes.parse_double_to_scaled b with Some s -> Some s | None -> XSD.Datatypes.parse_to_scaled b) in
  match pa, pb with
  | Some sa, Some sb -> Some (XSD.Datatypes.scaled_cmp sa sb)
  | _ -> None

// Numeric compare for numeric base types; equal-width ISO date/time
// strings order correctly under lexicographic compare.
let csvw_cell_cmp (numeric : bool) (a b : string) : option int =
  if numeric then csvw_num_cmp a b else Some (csvw_conv_str_cmp a b)

// Does the cell text satisfy the datatype's length and value constraints
// (minimum aliases minInclusive; maximum aliases maxInclusive)? An
// unparseable / incomparable value fails open (treated as satisfying) so
// a comparison gap never silently drops an otherwise-valid literal.
let csvw_value_satisfies (base_name : string) (text : string) (dt : option csvw_datatype) : bool =
  let (len, minl, maxl, mn, mx, mni, mxi, mne, mxe) = csvw_dt_value_facets dt in
  let n = String.length text in
  let len_ok =
    if csvw_is_binary_base base_name then true
    else
      (match len with Some l -> n = l | None -> true) &&
      (match minl with Some l -> n >= l | None -> true) &&
      (match maxl with Some l -> n <= l | None -> true) in
  let numeric = csvw_is_numeric_base base_name in
  let eff_min_incl = (match mni with Some x -> Some x | None -> mn) in
  let eff_max_incl = (match mxi with Some x -> Some x | None -> mx) in
  let vc_ok =
    (match eff_min_incl with Some c -> (match csvw_cell_cmp numeric text c with Some r -> r >= 0 | None -> true) | None -> true) &&
    (match eff_max_incl with Some c -> (match csvw_cell_cmp numeric text c with Some r -> r <= 0 | None -> true) | None -> true) &&
    (match mne with Some c -> (match csvw_cell_cmp numeric text c with Some r -> r > 0 | None -> true) | None -> true) &&
    (match mxe with Some c -> (match csvw_cell_cmp numeric text c with Some r -> r < 0 | None -> true) | None -> true) in
  len_ok && vc_ok

// Build a literal term, guarding the dynamically-computed datatype IRI
// with `is_iri` the same way RML.Eval.fst's build_literal_opt does —
// csvw_datatype_iri's output always contains a colon in practice (every
// branch prepends a fixed IRI-scheme prefix), but the guard keeps the
// F* typechecker honest about wf_iri's refinement rather than assuming it.
let csvw_build_literal (lex : string) (dt : string) : option rdf_term =
  if is_iri dt then
    let l : literal = { lexical_form = lex; datatype = dt; lang_tag = None; direction = None } in
    if literal_wf l then Some (T_Literal l) else None
  else None

// Stage 2's inherited "lang" property (tabular-metadata section
// 5.1.1): a cell whose column has an effective `lang` gets that
// language tag ONLY when the cell's resulting value is a plain string
// (datatype xsd:string, csv2rdf's own default) — a typed value
// (xsd:date, xsd:integer, ...) is never language-tagged. RDF 1.1
// requires datatype = rdf:langString exactly when a language tag is
// present (literal_wf above), so tagging also swaps the datatype.
let csvw_build_literal_lang (lex : string) (dt : string) (lang : option string) : option rdf_term =
  match lang, dt = xsd_string with
  | Some l, true ->
    let lit : literal = { lexical_form = lex; datatype = rdf_lang_string; lang_tag = Some l; direction = None } in
    if literal_wf lit then Some (T_Literal lit) else None
  | _ -> csvw_build_literal lex dt

// ================================================================
// rdf: List vocabulary + csvw:title, as wf_iri constants (RDF.Vocabulary
// exposes the plain-string forms; the triple builders here need the
// refinement, same pattern as the csvw: constants above). Used by the
// `ordered` list-valued cell path (test306/307) and rowTitles
// (test235/236) respectively.
// ================================================================

let rdf_first_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let csvw_title_pred : wf_iri =
  assert_norm (is_iri (csvw_ns ^ "title")); csvw_ns ^ "title"

// ================================================================
// CURIE / prefixed-name expansion. Used both for common-property keys
// and @type/@id tokens (below) AND for URI-template valueUrl results
// (test038 `schema:about`, test039 `rdf:value`) — a prefixed name that
// survives URI-template expansion must expand to its absolute IRI
// before being resolved against the table URL. Defined here (before
// the per-cell conversion) so csvw_cell_object can call it.
// ================================================================

// CURIE prefix table — the subset of the CSVW default context (which
// imports the RDFa 1.1 initial context) that the csv2rdf corpus's
// common properties actually use. An unknown prefix leaves the key
// unexpanded (dropped downstream by the is_iri guard).
let csvw_curie_ns (prefix : string) : option string =
  if prefix = "rdf" then Some "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  else if prefix = "rdfs" then Some "http://www.w3.org/2000/01/rdf-schema#"
  else if prefix = "xsd" then Some "http://www.w3.org/2001/XMLSchema#"
  else if prefix = "dc" then Some "http://purl.org/dc/terms/"
  else if prefix = "dcterms" then Some "http://purl.org/dc/terms/"
  else if prefix = "dc11" then Some "http://purl.org/dc/elements/1.1/"
  else if prefix = "dcat" then Some "http://www.w3.org/ns/dcat#"
  else if prefix = "schema" then Some "http://schema.org/"
  else if prefix = "foaf" then Some "http://xmlns.com/foaf/0.1/"
  else if prefix = "skos" then Some "http://www.w3.org/2004/02/skos/core#"
  else if prefix = "owl" then Some "http://www.w3.org/2002/07/owl#"
  else if prefix = "org" then Some "http://www.w3.org/ns/org#"
  else if prefix = "oa" then Some "http://www.w3.org/ns/oa#"
  else if prefix = "prov" then Some "http://www.w3.org/ns/prov#"
  else if prefix = "as" then Some "https://www.w3.org/ns/activitystreams#"
  else None

// Split a key at its FIRST ':' into (before-chars, after-chars).
let rec csvw_split_colon (chars : list FStar.Char.char)
  : Tot (option (list FStar.Char.char & list FStar.Char.char)) (decreases chars) =
  match chars with
  | [] -> None
  | c :: rest ->
    if FStar.Char.int_of_char c = 58 (* ':' *) then Some ([], rest)
    else (match csvw_split_colon rest with
          | None -> None
          | Some (b, a) -> Some (c :: b, a))

// Expand a prefixed name to an absolute IRI. A key whose part after the
// first ':' begins with "//" (i.e. scheme://...) is an absolute URL and
// returned verbatim; a known prefix expands; anything else is returned
// unchanged (dropped downstream if not a well-formed IRI).
let csvw_expand_curie (key : string) : string =
  match csvw_split_colon (String.list_of_string key) with
  | None -> key
  | Some (b, a) ->
    let local = String.string_of_list a in
    if String.length local >= 2 && String.sub local 0 2 = "//" then key
    else (match csvw_curie_ns (String.string_of_list b) with
          | Some ns -> ns ^ local
          | None -> key)

// The CSVW built-in @type terms (class names) defined in the CSVW
// context, for the "@type is a bare built-in term" case (test263:
// `"@type": "Table"` -> csvw:Table). A bare token (no ':') that names
// one of these expands to the csvw: namespace; anything else is left
// to csvw_expand_curie (prefixed name / absolute URL).
let csvw_builtin_type_term (t : string) : option string =
  if t = "TableGroup" || t = "Table" || t = "Schema" || t = "Column" ||
     t = "Row" || t = "Dialect" || t = "Template" || t = "Datatype" ||
     t = "Direction" || t = "ForeignKey" || t = "NumericFormat" ||
     t = "TableReference" || t = "Cell" || t = "JSON"
  then Some (csvw_ns ^ t) else None

// Expand an @type token: a bare built-in CSVW term first (test263),
// else the ordinary CURIE / absolute-URL expansion.
let csvw_expand_type_token (t : string) : string =
  match csvw_builtin_type_term t with
  | Some iri -> iri
  | None -> csvw_expand_curie t

// ================================================================
// Column specs: CSVW.Metadata's csvw_column merged with the FULL
// table-group -> table -> tableSchema -> column inherited-property
// chain (Stage 2 — csvw_inherited_props/csvw_group_meta in
// CSVW.Metadata; the module banner's old "ONE-LEVEL" note is
// superseded, kept there only as history), or synthesized straight
// from a header row when no schema was given at all.
// ================================================================

noeq type csvw_col_spec = {
  cs_name         : string;
  cs_virtual      : bool;
  cs_suppress     : bool;
  cs_datatype     : option csvw_datatype;
  cs_about_url    : option string;
  cs_property_url : option string;
  cs_value_url    : option string;
  cs_separator    : option string;   // list-valued cell separator (test228-230)
  cs_lang         : option string;   // Stage 2 inherited "lang"
  cs_null         : option string;   // Stage 2 inherited "null"
  cs_ordered      : bool;            // "ordered" -> rdf:List cell (test306/307)
}

let csvw_opt_bool (o : option bool) : bool = match o with Some b -> b | None -> false

// More-specific-wins merge of two inherited-property records — used
// to fold table-group -> table -> tableSchema into ONE effective
// record before a column's own (most-specific) values are applied on
// top of it in csvw_col_spec_of_column.
let csvw_merge_inherited (specific general : csvw_inherited_props) : csvw_inherited_props = {
  inh_about_url    = (match specific.inh_about_url with    Some _ -> specific.inh_about_url    | None -> general.inh_about_url);
  inh_property_url = (match specific.inh_property_url with Some _ -> specific.inh_property_url | None -> general.inh_property_url);
  inh_value_url    = (match specific.inh_value_url with    Some _ -> specific.inh_value_url    | None -> general.inh_value_url);
  inh_lang         = (match specific.inh_lang with         Some _ -> specific.inh_lang         | None -> general.inh_lang);
  inh_null         = (match specific.inh_null with         Some _ -> specific.inh_null         | None -> general.inh_null);
  inh_separator    = (match specific.inh_separator with    Some _ -> specific.inh_separator    | None -> general.inh_separator);
  inh_datatype     = (match specific.inh_datatype with     Some _ -> specific.inh_datatype     | None -> general.inh_datatype);
  inh_ordered      = (match specific.inh_ordered with      Some _ -> specific.inh_ordered      | None -> general.inh_ordered);
}

// A column `name` that is not a valid URI-Template variable name must be
// treated as if absent (tabular-metadata section 5.6: "column names are
// restricted as defined in Variables in [URI-TEMPLATE]"; and "names
// beginning with '_' are reserved by this specification and MUST NOT be
// used"). RFC 6570 varname = varchar *( ["."] varchar ), varchar =
// ALPHA / DIGIT / "_" / pct-encoded — so a space (test130 "G I D") or a
// leading '_' (test131 "_GID") makes the name invalid; the column then
// falls back to its percent-encoded title, exactly as the absent-name
// case already does.
let csvw_varname_char_ok (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  (n >= 65 && n <= 90) || (n >= 97 && n <= 122) ||  // A-Z a-z
  (n >= 48 && n <= 57) ||                            // 0-9
  n = 95 || n = 46 || n = 37                         // '_' '.' '%'
let csvw_valid_column_name (s : string) : bool =
  match String.list_of_string s with
  | [] -> false
  | c0 :: _ ->
    FStar.Char.int_of_char c0 <> 95 (* not leading '_' *)
    && List.Tot.for_all csvw_varname_char_ok (String.list_of_string s)

let csvw_col_spec_of_column (eff : csvw_inherited_props) (c : csvw_column) : csvw_col_spec = {
  cs_name = (match c.col_name with
             | Some n -> if csvw_valid_column_name n then n
                         else (match c.col_titles with t :: _ -> t | [] -> "")
             | None -> (match c.col_titles with t :: _ -> t | [] -> ""));
  cs_virtual = csvw_opt_bool c.col_virtual;
  cs_suppress = csvw_opt_bool c.col_suppress_output;
  cs_datatype = (match c.col_datatype with Some d -> Some d | None -> eff.inh_datatype);
  cs_about_url = (match c.col_about_url with Some a -> Some a | None -> eff.inh_about_url);
  cs_property_url = (match c.col_property_url with Some p -> Some p | None -> eff.inh_property_url);
  cs_value_url = (match c.col_value_url with Some v -> Some v | None -> eff.inh_value_url);
  cs_separator = (match c.col_separator with Some s -> Some s | None -> eff.inh_separator);
  cs_lang = (match c.col_lang with Some l -> Some l | None -> eff.inh_lang);
  cs_null = (match c.col_null with Some n -> Some n | None -> eff.inh_null);
  cs_ordered = (match c.col_ordered with Some b -> b | None -> (match eff.inh_ordered with Some b -> b | None -> false));
}

// Positional default column name when neither a schema nor a header
// cell gives one — csv2rdf's own "_col.N" fallback (1-based).
// `List.Tot.mapi`'s index callback type is plain `int` (FStar.List.Tot.Base),
// not `nat` — take `int` here to match, even though the actual values
// mapi ever supplies are always >= 0.
let csvw_positional_name (i : int) : string = "_col." ^ string_of_int (i + 1)

// Schema absent entirely ("no metadata document at all" — test001):
// column names come from the CSV file's own header row text (the
// "embedded metadata" the Model for Tabular Data derives purely from
// the header when no user metadata exists at all).
let csvw_col_specs_from_header (header_cells : list string) : list csvw_col_spec =
  List.Tot.mapi
    (fun i (h : string) -> {
       cs_name = (if h = "" then csvw_positional_name i else h);
       cs_virtual = false; cs_suppress = false; cs_datatype = None;
       cs_about_url = None; cs_property_url = None; cs_value_url = None;
       cs_separator = None; cs_lang = None; cs_null = None; cs_ordered = false;
     })
    header_cells

// A tableSchema WAS supplied by user metadata but decoded to zero
// column descriptions — either "columns" was validly omitted, or it
// was present with the wrong JSON shape and graceful degradation
// (tabular-metadata section 4, CSVW.Metadata.csvw_decode_table_schema)
// reduced it to empty. Once a user schema exists at all, the header
// row's own text no longer supplies column names (test100/test107):
// every column falls straight to the positional "_col.N" default,
// never the CSV header cell's literal text — unlike the "no schema
// object at all" case above, which DOES use header text.
let csvw_col_specs_positional (header_cells : list string) : list csvw_col_spec =
  List.Tot.mapi
    (fun i (h : string) -> {
       cs_name = csvw_positional_name i;
       cs_virtual = false; cs_suppress = false; cs_datatype = None;
       cs_about_url = None; cs_property_url = None; cs_value_url = None;
       cs_separator = None; cs_lang = None; cs_null = None; cs_ordered = false;
     })
    header_cells

// `grp`/`tbl` are the already-decoded table-group and table level
// inherited-property records (csvw_convert_table_*'s callers own the
// group one; the table itself carries its own via tbl.tbl_inherited).
// Merge order group -> table -> tableSchema, most specific last, then
// let each column override on top of that (csvw_col_spec_of_column).
// A default positional column ("_col.N") for a CSV header cell that the
// user schema did not describe (test278: the CSV has MORE headers than
// the schema has non-virtual columns; the surplus become extra columns
// named _col.N, inheriting the effective schema/table/group props but
// carrying no per-column overrides). Index is 0-based; csvw_positional_
// name turns it into the 1-based "_col.(i+1)".
let csvw_positional_spec_eff (eff : csvw_inherited_props) (i : int) : csvw_col_spec = {
  cs_name = csvw_positional_name i;
  cs_virtual = false; cs_suppress = false;
  cs_datatype = eff.inh_datatype;
  cs_about_url = eff.inh_about_url;
  cs_property_url = eff.inh_property_url;
  cs_value_url = eff.inh_value_url;
  cs_separator = eff.inh_separator;
  cs_lang = eff.inh_lang;
  cs_null = eff.inh_null;
  cs_ordered = (match eff.inh_ordered with Some b -> b | None -> false);
}

// Append "_col.N" specs for header cells at positions beyond the last
// described column (test278). `n_described` is the schema's column
// count; only header indices >= n_described produce a surplus spec, in
// order, so the CSV columns the schema DID describe keep their own spec.
let rec csvw_surplus_specs (eff : csvw_inherited_props) (n_described : nat) (i : nat) (header_cells : list string)
  : Tot (list csvw_col_spec) (decreases header_cells) =
  match header_cells with
  | [] -> []
  | _ :: tl ->
    let rest = csvw_surplus_specs eff n_described (i + 1) tl in
    if i >= n_described then csvw_positional_spec_eff eff i :: rest else rest

let csvw_build_col_specs
    (grp tbl : csvw_inherited_props) (ts_opt : option csvw_table_schema) (header_cells : list string)
  : list csvw_col_spec =
  match ts_opt with
  | Some ts ->
    if Cons? ts.ts_columns then
      let eff = csvw_merge_inherited ts.ts_inherited (csvw_merge_inherited tbl grp) in
      let described = List.Tot.map (csvw_col_spec_of_column eff) ts.ts_columns in
      // CSV headers beyond the described columns become surplus _col.N
      // columns (test278). A schema with as many or more columns than
      // headers adds nothing here.
      described @ csvw_surplus_specs eff (List.Tot.length ts.ts_columns) 0 header_cells
    else csvw_col_specs_positional header_cells
  | None -> csvw_col_specs_from_header header_cells

// ================================================================
// Dialect-driven row skipping (skipRows + header-row-count only —
// see the banner's scope note on commentPrefix/skipBlankRows).
// ================================================================

let csvw_header_row_count (dia_opt : option csvw_dialect) : nat =
  match dia_opt with
  | None -> 1
  | Some dia ->
    (match dia.dia_header_row_count with
     | Some n -> if n >= 0 then n else 1
     | None -> (match dia.dia_header with Some false -> 0 | _ -> 1))

let csvw_skip_rows_count (dia_opt : option csvw_dialect) : nat =
  match dia_opt with
  | None -> 0
  | Some dia -> (match dia.dia_skip_rows with Some n -> (if n >= 0 then n else 0) | None -> 0)

let rec csvw_drop (#a:Type) (n : nat) (l : list a) : Tot (list a) (decreases n) =
  if n = 0 then l
  else match l with
       | [] -> []
       | _ :: tl -> csvw_drop (n - 1) tl

// `List.Tot.mapi`'s index callback is typed `int` (FStar.List.Tot.Base),
// which doesn't match this module's `nat`-typed row_num/source_row_num
// parameters without an unprovable int->nat cast. A direct structural
// recursion starting the counter at a caller-supplied `nat` sidesteps
// that entirely.
let rec csvw_index_from (#a:Type) (n : nat) (l : list a) : Tot (list (nat & a)) (decreases l) =
  match l with
  | [] -> []
  | hd :: tl -> (n, hd) :: csvw_index_from (n + 1) tl

// Truncating zip (mirrors RML.Sources.fst's zip_strings) — structural
// on the spec list, so a malformed CSV row (wrong width) never crashes
// or loops, just contributes fewer paired cells.
let rec csvw_zip_specs_cells (specs : list csvw_col_spec) (cells : list string)
  : Tot (list (csvw_col_spec & string)) (decreases specs) =
  match specs, cells with
  | s :: srest, c :: crest -> (s, c) :: csvw_zip_specs_cells srest crest
  | _, _ -> []

// ================================================================
// Table URL resolution: the metadata's own tableSchema-independent
// `url` annotation if given, else the fallback URL the caller supplies
// (the CSV file referenced directly by the test's mf:action, when no
// metadata document names one), resolved against the document's base
// IRI. A relative fallback/url (the overwhelmingly common case — bare
// CSV filenames) only becomes a well-formed IRI once resolved; an
// already-absolute value round-trips through resolve_iri_v2 unchanged.
// ================================================================

let csvw_effective_table_url (base_iri : string) (fallback_url : string) (tbl : csvw_table) : string =
  let raw = (match tbl.tbl_url with Some u -> u | None -> fallback_url) in
  resolve_iri_v2 base_iri raw

// ================================================================
// Row-scoped template variable lookup: ordinary column names bind to
// that column's raw cell text (physical columns only — a virtual
// column contributes no cell), plus CSVW's special `_row`/`_sourceRow`
// variables. `_name` (the CURRENT column's own annotated name, used
// within that column's own url templates) is layered on per-column by
// the caller, not here.
// ================================================================

let csvw_row_lookup (phys_bindings : list (string & string)) (row_num : nat) (source_row_num : nat)
  : (string -> option string) =
  fun (v : string) ->
    if v = "_row" then Some (string_of_int row_num)
    else if v = "_sourceRow" then Some (string_of_int source_row_num)
    else List.Tot.assoc v phys_bindings

// ================================================================
// Per-cell conversion: subject, predicate, object for ONE column of
// ONE row. Returns the cell's resulting subject (needed by standard
// mode's csvw:describes bookkeeping even when no value triple was
// produced — an empty triple list with a valid subject still lets the
// caller decide whether to link it) plus the triples this cell
// contributes (0 when suppressed, when the predicate doesn't resolve
// to a valid IRI, or when the object is null/unresolvable).
// ================================================================

let csvw_term_of_subject (s : subject) : rdf_term =
  match s with S_IRI i -> T_IRI i | S_BNode b -> T_BNode b

// aboutUrl/propertyUrl/valueUrl templates resolve against the CURRENT
// TABLE's own (already base_iri-resolved) URL, not the outer document
// base — csv2rdf's URI Template Properties (tabular-data-model §5.1.1):
// "the resulting IRI reference is resolved against the URL of the
// table". `csvw_effective_table_url` is the one place base_iri itself
// resolves a (possibly relative) table `url` annotation; every
// per-cell template downstream of that resolves against the result,
// not against base_iri a second time.
let csvw_cell_object
    (table_url_resolved : string) (spec : csvw_col_spec) (cell_text : option string)
    (lookup : string -> option string)
  : option rdf_term =
  // A PHYSICAL cell (cell_text = Some _) whose text matches the column's
  // effective `null` value (or is "") is null and produces NO object,
  // even when a valueUrl template is present (test035: the reportsTo
  // column declares `null: "xx"`, so the "xx" cell emits no
  // org:reportsTo triple). VIRTUAL columns (cell_text = None) are exempt
  // — their value comes entirely from the valueUrl template (test032's
  // rdf:type / schema:location virtual columns).
  let phys_null = (match cell_text with
                   | Some txt -> txt = "" || (match spec.cs_null with Some n -> txt = n | None -> false)
                   | None -> false) in
  if phys_null then None
  else
  match spec.cs_value_url with
  | Some tmpl ->
    // A valueUrl template may itself be (or expand to) a prefixed name
    // — `schema:about` (test038), `rdf:value` (test039) — which must
    // expand to its absolute IRI via the CSVW context before being
    // resolved against the table URL. csvw_expand_curie is a no-op on a
    // template with no known prefix (fragment refs, absolute URLs).
    let raw = csvw_expand_curie (csvw_expand_template lookup tmpl) in
    let resolved = resolve_iri_v2 table_url_resolved raw in
    if is_iri resolved then Some (T_IRI resolved) else None
  | None ->
    (match cell_text with
     | None -> None                      // virtual column with no valueUrl: nothing to emit
     | Some txt ->
       // Stage 2 inherited "null": a cell whose raw text matches the
       // column's effective `null` value is null too, same as the
       // default "" case (tabular-metadata 5.1.1 / test126).
       let is_null = txt = "" || (match spec.cs_null with Some n -> txt = n | None -> false) in
       if is_null then None
       else
         // A cell whose text is not a valid lexical form for its declared
         // datatype does NOT get that datatype (tabular-data-model
         // section 6.4.2 step: an invalid value is a validation error;
         // the cell's value keeps the datatype's LEXICAL string but is
         // emitted as a plain string literal — the csv2rdf "invalid X"
         // fixtures, test172-182, expect e.g. "1z" not "1z"^^xsd:double).
         let dt_str = csvw_datatype_iri spec.cs_datatype in
         let dt_wf : option wf_iri = if is_iri dt_str then Some dt_str else None in
         (match dt_wf with
          | None -> None
          | Some d ->
            // A value that is ill-formed for its datatype OR violates a
            // length / value constraint keeps its lexical form but drops
            // to a plain string literal (tabular-data-model 6.4.2;
            // test172-182 for ill-formed, test196-198/test203-215 for
            // constraint violations).
            let base_name = csvw_dt_base_name_of spec.cs_datatype in
            // UAX-35 format facets first: a `format`/`pattern` (numbers,
            // dates) or a boolean base converts the raw cell to a
            // canonical lexical, or rejects it (keeping the raw string).
            let (fmt_str, pat, grp, dec) = csvw_dt_format_facets spec.cs_datatype in
            let lex, dt_eff =
              (match csvw_format_convert base_name fmt_str pat grp dec txt with
               | FO_Invalid -> txt, xsd_string
               | FO_Valid canonical -> canonical, d
               | FO_NoFormat -> txt, d) in
            // Re-check the (possibly reformatted) lexical against the
            // datatype's own lexical space + length/value constraints;
            // a still-ill-formed value falls back to a plain string.
            let violate = XSD.Datatypes.literal_ill_formed dt_eff lex
                       || not (csvw_value_satisfies base_name lex spec.cs_datatype) in
            let eff : wf_iri = if violate then xsd_string else dt_eff in
            csvw_build_literal_lang lex eff spec.cs_lang))

// Default-propertyUrl column-name encoding. csv2rdf builds a column's
// default propertyUrl as `<tableUrl>#<name>` where the name is the
// column's percent-encoded title. SPARQL11.Algebra.string_encode_uri
// uses the RFC 3986 UNRESERVED set (which keeps `-` `.` `_` `~`), but
// the CSVW corpus's canonical output percent-encodes `-` too (test188
// `M-d-yyyy` -> `M%2Dd%2Dyyyy`) while STILL keeping `.` (`M.d.yyyy`
// stays). Post-encode any surviving `-` as %2D — a literal `-` in
// string_encode_uri's output can only come from an input `-` (every
// other reserved char is already percent-escaped), so this is a safe
// targeted fixup rather than a re-implementation of the encoder.
let csvw_encode_name (s : string) : string =
  String.string_of_list
    (List.Tot.concatMap
       (fun (c : FStar.Char.char) ->
          if FStar.Char.int_of_char c = 45  // '-'
          then [FStar.Char.char_of_int 37; FStar.Char.char_of_int 50; FStar.Char.char_of_int 68]  // %2D
          else [c])
       (String.list_of_string (string_encode_uri s)))

// Split a list-valued cell (tabular-metadata `separator`) on the first
// character of the separator string. Empty elements survive so the
// caller's "" -> no triple rule drops them (matches the null-value
// handling in csvw_cell_object).
let csvw_split_list_cell (sep : string) (s : string) : list string =
  match String.list_of_string sep with
  | sepc :: _ -> List.Tot.map String.string_of_list (split_all sepc (String.list_of_string s))
  | [] -> [s]

// Build an rdf:List (rdf:first/rdf:rest/rdf:nil chain) from a list of
// object terms — the `ordered` list-valued cell (test306/307). Returns
// the list HEAD term (a fresh blank node, or rdf:nil for the empty
// list) plus every rdf:first/rdf:rest triple. `seed` must be unique per
// (row, column) so distinct cells never collide their blank-node labels
// (the isomorphism comparison relabels them, but they must stay
// distinct within the graph).
let rec csvw_rdf_list (seed : string) (idx : nat) (objs : list rdf_term)
  : Tot (rdf_term & list triple) (decreases objs) =
  match objs with
  | [] -> (T_IRI rdf_nil_iri, [])
  | o :: tl ->
    let node : subject = S_BNode (seed ^ "_" ^ string_of_int idx) in
    let (rest_head, rest_triples) = csvw_rdf_list seed (idx + 1) tl in
    (csvw_term_of_subject node,
       { s = node; p = rdf_first_iri; o = o }
       :: { s = node; p = rdf_rest_iri; o = rest_head }
       :: rest_triples)

let csvw_process_cell
    (table_url_resolved : string) (row_seed : string)
    (lookup : string -> option string) (default_subject : subject)
    (spec : csvw_col_spec) (cell_text : option string)
  : (subject & list triple) =
  if spec.cs_suppress then (default_subject, [])
  else
    let cur_lookup (v : string) = if v = "_name" then Some spec.cs_name else lookup v in
    let subj =
      match spec.cs_about_url with
      | Some tmpl ->
        let raw = csvw_expand_template cur_lookup tmpl in
        let resolved = resolve_iri_v2 table_url_resolved raw in
        if is_iri resolved then S_IRI resolved else default_subject
      | None -> default_subject
    in
    // Annotating the option's inner type as `wf_iri` (rather than plain
    // `string`) keeps the `is_iri raw` refinement attached through the
    // `Some`/destructure round-trip — a bare `if is_iri pred_str then ...
    // else ...` around a separately let-bound plain string does NOT
    // reliably re-derive the refinement for a record field several
    // constructs downstream (observed directly: F* reported the `None`
    // branch of the raw-string match itself failing the wf_iri subtyping
    // check even though it is only ever used inside the guarded branch).
    let raw : string =
      match spec.cs_property_url with
      // A propertyUrl template may itself be (or expand to) a prefixed
      // name — `schema:name`, `rdf:type` (test032/033) — expanded to its
      // absolute IRI via the CSVW context before being resolved against
      // the table URL, exactly as the valueUrl path (csvw_cell_object)
      // already does. csvw_expand_curie is a no-op on a template with no
      // known prefix (fragment refs, absolute URLs).
      | Some tmpl -> resolve_iri_v2 table_url_resolved (csvw_expand_curie (csvw_expand_template cur_lookup tmpl))
      | None -> table_url_resolved ^ "#" ^ csvw_encode_name spec.cs_name
    in
    let pred_valid : option wf_iri = if is_iri raw then Some raw else None in
    match pred_valid with
    | None -> (subj, [])
    | Some pred_str ->
      (match spec.cs_separator, cell_text with
       | Some sep, Some txt ->
         // List-valued cell: one triple per element, each converted
         // through the same datatype / format / constraint logic.
         let parts = csvw_split_list_cell sep txt in
         let objs = List.Tot.choose
           (fun (part : string) -> csvw_cell_object table_url_resolved spec (Some part) cur_lookup)
           parts in
         if spec.cs_ordered then
           // `ordered`: the values form an rdf:List, linked once from the
           // subject via the property (test306/307).
           (match objs with
            | [] -> (subj, [])
            | _ ->
              let list_seed = "csvwL_" ^ row_seed ^ "_" ^ csvw_encode_name spec.cs_name in
              let (head, list_triples) = csvw_rdf_list list_seed 0 objs in
              (subj, { s = subj; p = pred_str; o = head } :: list_triples))
         else
           (subj, List.Tot.map (fun (o : rdf_term) -> ({ s = subj; p = pred_str; o = o } <: triple)) objs)
       | _ ->
         (match csvw_cell_object table_url_resolved spec cell_text cur_lookup with
          | None -> (subj, [])
          | Some obj -> (subj, [ { s = subj; p = pred_str; o = obj } ])))

// One row's every processed (non-suppressed-at-the-suppress-check)
// column: physical columns zipped positionally against the row's
// cells, virtual columns processed with no cell text at all (their
// value can only come from a valueUrl template).
let csvw_row_cell_results
    (table_url_resolved : string)
    (col_specs : list csvw_col_spec) (row_num : nat) (source_row_num : nat) (cells : list string)
  : list (subject & list triple) =
  let phys_specs = List.Tot.filter (fun (s : csvw_col_spec) -> not s.cs_virtual) col_specs in
  let virt_specs = List.Tot.filter (fun (s : csvw_col_spec) -> s.cs_virtual) col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let phys_bindings = List.Tot.map (fun (p : (csvw_col_spec & string)) -> (fst p).cs_name, snd p) phys_pairs in
  let lookup = csvw_row_lookup phys_bindings row_num source_row_num in
  // Per-row seed for any list-valued (ordered) cell's blank nodes —
  // unique across rows AND tables (a shared aboutUrl can repeat a
  // subject across rows, test306, so the SUBJECT alone is not a safe
  // discriminator; the physical source-row number is).
  let row_seed = string_encode_uri table_url_resolved ^ "_" ^ string_of_int source_row_num in
  let default_subject =
    S_BNode ("csvwrow_" ^ string_encode_uri table_url_resolved ^ "_" ^ string_of_int source_row_num) in
  List.Tot.map
    (fun (p : (csvw_col_spec & string)) ->
       csvw_process_cell table_url_resolved row_seed lookup default_subject (fst p) (Some (snd p)))
    phys_pairs
  @ List.Tot.map
      (fun (s : csvw_col_spec) -> csvw_process_cell table_url_resolved row_seed lookup default_subject s None)
      virt_specs

// ================================================================
// Common properties -> RDF (tabular-metadata section 5.8 / csv2rdf
// "Generating RDF" step for a table's common properties). A metadata
// object's prefixed-name / absolute-URL members (captured verbatim by
// CSVW.Metadata as tbl_common) become RDF triples on that object's
// node (here: the table node, standard mode only — minimal mode emits
// cell triples only, so this section is unused there). Value forms:
//   - JString / JNumber / JBool -> a plain typed literal.
//   - {"@value": s, "@type": t} / {"@value": s, "@language": l}
//     -> a typed / language-tagged literal.
//   - {"@id": iri}  -> an IRI node reference.
//   - a nested object (no @value/@id) -> a fresh blank node carrying
//     its own members (recursively), with an optional "@type" member
//     emitted as an rdf:type triple.
//   - an array -> one object per element, same predicate.
//   - JNull / anything unresolvable -> nothing.
// ================================================================

// Guarded literal builder (same discipline as csvw_build_literal, but
// with an optional language tag): only a well-formed literal is emitted.
let csvw_mk_literal (lex : string) (dt : wf_iri) (lang : option string) : option rdf_term =
  let l : literal = { lexical_form = lex; datatype = dt; lang_tag = lang; direction = None } in
  if literal_wf l then Some (T_Literal l) else None

let csvw_typed_literal_opt (lex : string) (dt : string) : option rdf_term =
  if is_iri dt then csvw_mk_literal lex dt None else csvw_mk_literal lex xsd_string None

// A JSON number lexeme -> xsd:integer if it is an integer lexeme, else
// xsd:double (JSON-LD's native-number typing).
let csvw_number_literal_opt (lex : string) : option rdf_term =
  if XSD.Datatypes.is_integer_lexical lex
  then csvw_mk_literal lex xsd_integer None
  else csvw_mk_literal lex xsd_double None

let csvw_opt_to_list (#a:Type) (o : option a) : list a =
  match o with Some x -> [x] | None -> []

// Emit the term(s) for a common-property value plus any triples its
// nested structure contributes. `seed` seeds fresh blank-node labels
// for nested objects/array elements; termination is by fuel decrease,
// with the top-level caller supplying fuel >= the value forest's total
// json_size so a well-formed document never truncates.
let rec csvw_common_value (default_lang : option string) (fuel : nat) (seed : string) (v : json_val)
  : Tot (list rdf_term & list triple) (decreases fuel) =
  if fuel = 0 then ([], [])
  else
    match v with
    | JNull -> ([], [])
    | JString s ->
      // A plain common-property string takes the document's default
      // language from @context (test259/260: dc:title/dcat:keyword/
      // schema:name become @en); with no default language it is a plain
      // xsd:string (unchanged for every fixture without @context
      // @language, and for test073 whose @context language is invalid
      // and so resolves to None).
      let term = (match default_lang with
                  | Some l -> csvw_mk_literal s rdf_lang_string (Some l)
                  | None -> csvw_mk_literal s xsd_string None) in
      (csvw_opt_to_list term, [])
    | JBool b -> (csvw_opt_to_list (csvw_mk_literal (if b then "true" else "false") xsd_boolean None), [])
    | JNumber s -> (csvw_opt_to_list (csvw_number_literal_opt s), [])
    | JArray items -> csvw_common_array default_lang (fuel - 1) seed 0 items
    | JObject fields ->
      (match json_get_field "@value" v with
       | Some (JString lex) ->
         let term =
           (match json_get_string "@type" v with
            | Some t -> csvw_typed_literal_opt lex (csvw_expand_curie t)
            | None ->
              (match json_get_string "@language" v with
               | Some l -> csvw_mk_literal lex rdf_lang_string (Some l)
               | None -> csvw_mk_literal lex xsd_string None)) in
         (csvw_opt_to_list term, [])
       | _ ->
         (match json_get_field "@id" v with
          | Some (JString idv) ->
            let iri = csvw_expand_curie idv in
            if is_iri iri then ([T_IRI iri], []) else ([], [])
          | _ ->
            let lbl = "csvwCP_" ^ seed in
            let b : subject = S_BNode lbl in
            let inner = csvw_common_object_fields default_lang (fuel - 1) b lbl fields in
            ([csvw_term_of_subject b], inner)))

and csvw_common_array (default_lang : option string) (fuel : nat) (seed : string) (idx : nat) (items : list json_val)
  : Tot (list rdf_term & list triple) (decreases fuel) =
  if fuel = 0 then ([], [])
  else
    match items with
    | [] -> ([], [])
    | hd :: tl ->
      let (t1, r1) = csvw_common_value default_lang (fuel - 1) (seed ^ "_" ^ string_of_int idx) hd in
      let (t2, r2) = csvw_common_array default_lang (fuel - 1) seed (idx + 1) tl in
      (t1 @ t2, r1 @ r2)

and csvw_common_object_fields (default_lang : option string) (fuel : nat) (subj : subject) (seed : string)
    (fields : list (string & json_val))
  : Tot (list triple) (decreases fuel) =
  if fuel = 0 then []
  else
    match fields with
    | [] -> []
    | (k, v) :: tl ->
      let here : list triple =
        if k = "@type" then
          (match v with
           | JString tv ->
             // A bare CSVW built-in term (`Table`, test263), a prefixed
             // name, or an absolute URL — expand accordingly.
             let ti = csvw_expand_type_token tv in
             (match (if is_iri ti then Some ti else None) with
              | Some (tiw:wf_iri) -> [ { s = subj; p = rdf_type; o = T_IRI tiw } ]
              | None -> [])
           | _ -> [])
        else if string_contains_colon k then
          let praw = csvw_expand_curie k in
          (match (if is_iri praw then Some praw else None) with
           | None -> []
           | Some (pred:wf_iri) ->
             let (terms, sub) = csvw_common_value default_lang (fuel - 1) (seed ^ "_" ^ k) v in
             List.Tot.map (fun (t:rdf_term) -> ({ s = subj; p = pred; o = t } <: triple)) terms @ sub)
        else [] in
      here @ csvw_common_object_fields default_lang (fuel - 1) subj seed tl

// Total json_size budget across a common-property list — a fuel bound
// generous enough that csvw_common_object_fields never truncates a
// well-formed document (see csvw_common_value's termination note).
let rec csvw_common_fuel (common : list (string & json_val)) : Tot nat (decreases common) =
  match common with
  | [] -> 1
  | (_, v) :: tl -> 1 + json_size v + csvw_common_fuel tl

let csvw_table_common_triples (default_lang : option string) (subj : subject) (seed : string) (common : list (string & json_val))
  : list triple =
  csvw_common_object_fields default_lang (csvw_common_fuel common) subj seed common

// ================================================================
// Minimal mode: bare cell-value triples only, no wrapper nodes.
// ================================================================

let csvw_row_triples_minimal
    (table_url_resolved : string)
    (col_specs : list csvw_col_spec) (row_num : nat) (source_row_num : nat) (cells : list string)
  : list triple =
  List.Tot.concatMap snd
    (csvw_row_cell_results table_url_resolved col_specs row_num source_row_num cells)

let csvw_convert_table_minimal
    (grp_inherited : csvw_inherited_props)
    (base_iri : string) (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : list triple =
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.tbl_dialect in
  let skip_n = csvw_skip_rows_count dia + csvw_header_row_count dia in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  // See csvw_convert_table_standard: a header-less, schema-less table
  // gets positional `_col.N` names from an empty header of the data
  // row's width (test023 minimal variant).
  let header_cells =
    if csvw_header_row_count dia > 0 then (match after_skip_rows with h :: _ -> h | [] -> [])
    else (match tbl.tbl_table_schema with
          | Some _ -> []
          | None -> (match data_rows with r :: _ -> List.Tot.map (fun (_:string) -> "") r | [] -> [])) in
  let col_specs = csvw_build_col_specs grp_inherited tbl.tbl_inherited tbl.tbl_table_schema header_cells in
  let indexed = csvw_index_from 0 data_rows in
  List.Tot.concatMap
    (fun (p : (nat & list string)) ->
       let (i, cells) = p in
       csvw_row_triples_minimal table_url_resolved col_specs (i + 1) (skip_n + i + 1) cells)
    indexed

// ================================================================
// Standard mode: csvw:TableGroup > csvw:table > csvw:row >
// csvw:describes > cell triples, plus csvw:rownum/csvw:url provenance
// per row (csv2rdf §"Generating RDF", quoted in the banner). Returns
// each level's own node so the caller (table for rows, group for
// tables) can link upward without recomputing it.
// ================================================================

// RFC 7111-style fragment identifier for a physical row's position in
// the source file ("#row=N", N 1-based counting every physical row
// including header/skipped rows) — used for csvw:url on a row node.
let csvw_row_url (table_url_resolved : string) (source_row_num : nat) : string =
  table_url_resolved ^ "#row=" ^ string_of_int source_row_num

// rowTitles (tabular-metadata): for each column name listed in the
// schema's rowTitles annotation, emit a csvw:title triple on the row
// node carrying that column's cell value as a plain string literal
// (test235/236). A rowTitles name that matches no physical column
// contributes nothing.
let csvw_row_title_triples
    (row_node : subject) (col_specs : list csvw_col_spec) (cells : list string) (row_titles : list string)
  : list triple =
  let phys_specs = List.Tot.filter (fun (s : csvw_col_spec) -> not s.cs_virtual) col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let bindings = List.Tot.map (fun (p : (csvw_col_spec & string)) -> (fst p).cs_name, snd p) phys_pairs in
  List.Tot.concatMap
    (fun (name : string) ->
       match List.Tot.assoc name bindings with
       | Some txt ->
         (match csvw_mk_literal txt xsd_string None with
          | Some o -> [ ({ s = row_node; p = csvw_title_pred; o = o } <: triple) ]
          | None -> [])
       | None -> [])
    row_titles

let csvw_row_triples_standard
    (table_url_resolved : string) (row_titles : list string)
    (col_specs : list csvw_col_spec) (row_num : nat) (source_row_num : nat) (cells : list string)
  : (subject & list triple) =
  let per_col = csvw_row_cell_results table_url_resolved col_specs row_num source_row_num cells in
  let row_node = S_BNode ("csvwR_" ^ string_encode_uri table_url_resolved ^ "_" ^ string_of_int source_row_num) in
  let row_url = csvw_row_url table_url_resolved source_row_num in
  let row_meta =
    [ { s = row_node; p = rdf_type; o = T_IRI csvw_Row };
      { s = row_node; p = csvw_rownum;
        o = T_Literal ({ lexical_form = string_of_int row_num; datatype = xsd_integer; lang_tag = None; direction = None }) } ]
    @ (if is_iri row_url then [ { s = row_node; p = csvw_url_pred; o = T_IRI row_url } ] else []) in
  let describes =
    List.Tot.concatMap
      (fun (r : (subject & list triple)) ->
         let (subj, ts) = r in
         if Nil? ts then [] else [ { s = row_node; p = csvw_describes; o = csvw_term_of_subject subj } ])
      per_col in
  let cell_triples = List.Tot.concatMap snd per_col in
  let title_triples = csvw_row_title_triples row_node col_specs cells row_titles in
  (row_node, row_meta @ title_triples @ describes @ cell_triples)

let csvw_convert_table_standard
    (grp_inherited : csvw_inherited_props) (default_lang : option string)
    (base_iri : string) (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : (subject & list triple) =
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.tbl_dialect in
  let skip_n = csvw_skip_rows_count dia + csvw_header_row_count dia in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  // With no header row (`header: false` / `headerRowCount: 0`, test023)
  // and no user schema, positional `_col.N` names still need a header of
  // the right WIDTH: an all-empty-cell header of the first data row's
  // width makes csvw_col_specs_from_header emit `_col.1.._col.N`. When a
  // header row IS present it supplies the names as before; a user schema
  // drives the specs regardless (empty header adds no surplus columns).
  let header_cells =
    if csvw_header_row_count dia > 0 then (match after_skip_rows with h :: _ -> h | [] -> [])
    else (match tbl.tbl_table_schema with
          | Some _ -> []
          | None -> (match data_rows with r :: _ -> List.Tot.map (fun (_:string) -> "") r | [] -> [])) in
  let col_specs = csvw_build_col_specs grp_inherited tbl.tbl_inherited tbl.tbl_table_schema header_cells in
  let row_titles = (match tbl.tbl_table_schema with Some ts -> ts.ts_row_titles | None -> []) in
  let indexed = csvw_index_from 0 data_rows in
  let row_results =
    List.Tot.map
      (fun (p : (nat & list string)) ->
         let (i, cells) = p in
         csvw_row_triples_standard table_url_resolved row_titles col_specs (i + 1) (skip_n + i + 1) cells)
      indexed in
  let t_node = S_BNode ("csvwT_" ^ string_encode_uri table_url_resolved) in
  let row_links =
    List.Tot.concatMap
      (fun (r : (subject & list triple)) -> [ { s = t_node; p = csvw_row_pred; o = csvw_term_of_subject (fst r) } ])
      row_results in
  let row_all = List.Tot.concatMap snd row_results in
  let t_common = csvw_table_common_triples default_lang t_node (string_encode_uri table_url_resolved) tbl.tbl_common in
  let t_meta =
    [ { s = t_node; p = rdf_type; o = T_IRI csvw_Table } ]
    @ (if is_iri table_url_resolved then [ { s = t_node; p = csvw_url_pred; o = T_IRI table_url_resolved } ] else []) in
  (t_node, t_meta @ t_common @ row_links @ row_all)

// ================================================================
// Whole-document entry points. `tables_with_rows` pairs each table in
// document order with its already-tokenized CSV rows (the OCaml
// runner reads + RML.Sources.csv_parse_rows's each table's own CSV
// file — I/O only, per rule #11) and the fallback URL to use when
// that particular table's own metadata carries no `url` annotation
// (normally the CSV file the test's mf:action names directly).
// ================================================================

// `grp_inherited` is the table-group's own inherited-property defaults
// (CSVW.Metadata.csvw_group_meta.grp_inherited) — the runner passes
// CSVW.Metadata.csvw_inherited_empty for a CSVW_Table document (no
// separate group-level JSON object exists in that case, so there is
// nothing to inherit from at this level; the table's own tbl_inherited
// still applies inside csvw_convert_table_minimal).
// A table with `suppressOutput` true contributes nothing to the output
// (tabular-metadata; test034/035's lookup tables). Filtered at the
// document level so neither its cell triples (minimal) nor its
// csvw:Table node / row links (standard) are emitted.
let csvw_table_suppressed (tbl : csvw_table) : bool =
  match tbl.tbl_suppress_output with Some b -> b | None -> false

let csvw_convert_document_minimal
    (grp_inherited : csvw_inherited_props)
    (base_iri : string) (tables_with_rows : list (csvw_table & string & list (list string)))
  : list triple =
  List.Tot.concatMap
    (fun (t : (csvw_table & string & list (list string))) ->
       let (tbl, fallback_url, rows) = t in
       if csvw_table_suppressed tbl then []
       else csvw_convert_table_minimal grp_inherited base_iri fallback_url tbl rows)
    tables_with_rows

let csvw_group_node : subject = S_BNode "csvwG"

// `grp` carries both the inherited-property defaults (threaded into
// every table's column-spec build) AND the group's own common
// properties (rdfs:label/rdfs:comment/... test275-278 family),
// attached directly to the csvw:TableGroup node the same way
// csvw_convert_table_standard already attaches tbl_common to its
// csvw:Table node.
let csvw_convert_document_standard
    (grp : csvw_group_meta) (default_lang : option string)
    (base_iri : string) (tables_with_rows : list (csvw_table & string & list (list string)))
  : list triple =
  let table_results =
    List.Tot.map
      (fun (t : (csvw_table & string & list (list string))) ->
         let (tbl, fallback_url, rows) = t in
         csvw_convert_table_standard grp.grp_inherited default_lang base_iri fallback_url tbl rows)
      (List.Tot.filter
         (fun (t : (csvw_table & string & list (list string))) ->
            let (tbl, _, _) = t in not (csvw_table_suppressed tbl))
         tables_with_rows) in
  let g_meta = [ { s = csvw_group_node; p = rdf_type; o = T_IRI csvw_TableGroup } ] in
  let g_common = csvw_table_common_triples default_lang csvw_group_node "csvwG" grp.grp_common in
  let table_links =
    List.Tot.concatMap
      (fun (r : (subject & list triple)) -> [ { s = csvw_group_node; p = csvw_table_pred; o = csvw_term_of_subject (fst r) } ])
      table_results in
  let table_all = List.Tot.concatMap snd table_results in
  g_meta @ g_common @ table_links @ table_all

// Convenience: a synthetic "no metadata document at all" table — the
// mf:action-is-a-bare-CSV-file case (schema inferred purely from the
// CSV's own header row, no dialect overrides). Kept here (not in
// CSVW.Metadata) since it's a CONVERSION-layer default, not a decoded
// value.
let csvw_no_metadata_table : csvw_table = {
  tbl_url = None;
  tbl_dialect = None;
  tbl_table_schema = None;
  tbl_common = [];
  tbl_inherited = csvw_inherited_empty;
  tbl_schema_ref = None;
  tbl_suppress_output = None;
}
