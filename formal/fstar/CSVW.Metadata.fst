module CSVW.Metadata

// Stage 1 of the CSVW program plan
// (docs/designissues/2026-07-05-csvw-program-plan.md): the metadata-
// document decoder. Deliberately a skeleton — dialect options plus
// tableSchema.columns[] decode only, NO inherited-property propagation
// (table group -> table -> schema -> column, Stage 2), NO URI-template
// resolution (Stage 3, CSVW.URITemplate), NO datatype/format-facet
// interpretation (Stage 4, XSD.Datatypes extension), NO CSV/RDF
// conversion (Stage 6+, CSVW.Convert). This module answers one
// question only: "does this metadata document parse into the AST
// below" — the same "does it parse" smoke check RML.Mapping and
// ShEx.Schema used for their own Stage 1s.
//
// JSON-LD context handling is deliberately absent: per the plan's Fit
// section, every metadata document in the vendored corpus that
// declares "@context" uses either the bare-string sentinel
// "http://www.w3.org/ns/csvw" or the two-element array form
// [sentinel, {"@language": ...}] (test027-user-metadata.json) — never
// an arbitrary remote context needing JSON-LD expansion. This decoder
// never looks at "@context" at all; the CSVW metadata vocabulary's own
// closed property table (walked below) is the whole of what Stage 1
// needs.
//
// Decoder idiom mirrors ShEx.Schema.fst's json_val-tree walk
// (json_get_field/json_get_string/json_get_array over an already-
// Parser.JSON-parsed tree) rather than RML.Mapping.fst's Turtle-graph
// reader — CSVW metadata documents are JSON, not RDF, per the plan's
// module-plan section ("mirror image of RML.Mapping.fst's decoder,
// but over JSON instead of RDF"). Unlike ShEx.Schema, nothing here is
// self- or mutually-recursive through json_val (columns/tables are
// flat lists, not a shapeExpr-style recursive grammar), so no fuel
// parameter is threaded anywhere — every decoder recurses structurally
// on a list argument and terminates on that list's own decrease.
//
// Leniency policy (an explicit design choice, not an oversight): a
// field whose JSON type does not match the vocabulary's declared type
// for that field (e.g. "trim": 1, an int where the spec wants a
// string/bool) decodes to None for THAT field only and does not fail
// the surrounding object — matching the corpus survey's finding that
// malformed-typed leaf values are common in the validation manifest's
// negative fixtures, and Stage 1's job is a structural "does the
// document's shape parse," not full spec-conformance validation of
// leaf facets (that is CSVW.Validate.fst, Stage 9). A "columns" array
// ELEMENT that is not a JSON object DOES fail the surrounding decode,
// mirroring ShEx.Schema.fst's decode_shape_decl_list /
// decode_string_list discipline of "None propagates out of a
// structurally-wrong list" — but a container-valued property whose
// WHOLE value has the wrong JSON type (a non-object `tableSchema`,
// test107; a non-object item in a `foreignKeys` array, test097)
// degrades to empty/ignored per tabular-metadata section 4's "MUST
// act as if it was an empty object" / "items ... that are not valid
// objects of the type expected are ignored" (2026-07-15, burndown
// round 2).
//
// Reference: Metadata Vocabulary for Tabular Data (w3.org/TR/tabular-
// metadata, Rec. 2015-12-17). Corpus:
// third_party/testing/csvw (w3c/csvw, gh-pages branch, pinned commit
// 2bc84f937be1), specifically the tests/*.json metadata fixtures.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.String
open FStar.List.Tot
open Parser.JSON

// ================================================================
// Small local integer-lexeme decoder (NOT a JSON parser — Parser.JSON
// already tokenized the number; this only turns that lexeme string
// into an F-star int). Mirrors ShEx.Schema.fst's local
// shex_parse_int_string, kept local rather than shared so this module
// stays a lightweight leaf module (same discipline ShEx.Schema and
// JSONLD.Context document for themselves).
// ================================================================

let csvw_char_to_digit (c:FStar.Char.char) : option int =
  let n = FStar.Char.int_of_char c in
  if n >= 48 && n <= 57 then Some (n - 48) else None

let rec csvw_parse_int_chars (chars:list FStar.Char.char) (acc:int)
  : Tot (option int) (decreases chars) =
  match chars with
  | [] -> Some acc
  | c :: rest ->
    (match csvw_char_to_digit c with
     | Some d -> csvw_parse_int_chars rest (op_Multiply acc 10 + d)
     | None -> None)

// Decodes a JSON-number lexeme (as produced by Parser.JSON's JNumber)
// into an int. Only integer lexemes (no '.', no exponent) succeed —
// exactly the shape CSVW's headerRowCount/skipRows/skipColumns fields
// use in the corpus.
let csvw_parse_int_string (s:string) : option int =
  match String.list_of_string s with
  | [] -> None
  | chars ->
    if List.Tot.hd chars = FStar.Char.char_of_int 45 (* '-' *)
    then (match csvw_parse_int_chars (List.Tot.tl chars) 0 with
          | Some n -> Some (0 - n)
          | None -> None)
    else csvw_parse_int_chars chars 0

// ================================================================
// json_val field-reading conveniences beyond Parser.JSON's own
// accessors.
// ================================================================

let json_get_number_lexeme (key:string) (obj:json_val) : option string =
  match json_get_field key obj with
  | Some (JNumber s) -> Some s
  | _ -> None

let json_get_int (key:string) (obj:json_val) : option int =
  match json_get_number_lexeme key obj with
  | Some s -> csvw_parse_int_string s
  | None -> None

// A value-constraint facet lexeme is a number (numeric datatypes) or a
// string (ISO date/time datatypes) — kept verbatim either way.
let json_get_num_or_str (key:string) (obj:json_val) : option string =
  match json_get_field key obj with
  | Some (JString s) -> Some s
  | Some (JNumber s) -> Some s
  | _ -> None

// The dialect "trim" property is documented as a string enum
// ("true"/"false"/"start"/"end") but the corpus also carries plain
// JSON booleans (test-suite shorthand seen in the survey: "trim":
// true/false alongside "trim": "start"). Accept both, canonicalizing
// booleans to their string form; anything else (e.g. a stray JNumber
// in a malformed fixture) decodes to None for this field only.
let json_get_string_or_bool_as_string (key:string) (obj:json_val) : option string =
  match json_get_field key obj with
  | Some (JString s) -> Some s
  | Some (JBool true) -> Some "true"
  | Some (JBool false) -> Some "false"
  | _ -> None

// ================================================================
// AST — leaf types
// ================================================================

// A datatype descriptor: either the bare-string shorthand ("string",
// "date", "decimal", ...) or the full object form with facets. Facet
// values are kept as VERBATIM strings, not interpreted here — same
// discipline ShEx.Schema and JSON-LD keep for numeric lexemes
// (anti-pattern #8: don't parse_to_scaled before parse_double_to_
// scaled). Interpreting "base"/"format" against XSD.Datatypes is
// Stage 4's job, not this decoder's.
// The object form additionally carries the datatype's @id (used as the
// RDF datatype IRI when present, test242) and the length + value
// constraint facets (length/minLength/maxLength; minimum/maximum and
// min|maxInclusive/min|maxExclusive) that the conversion layer checks a
// cell value against — a violating value keeps its lexical form but is
// emitted as a plain string (test196-198/test203-215). Length facets are
// kept as ints; value-constraint facets keep their verbatim lexeme
// (a number or an ISO date/time string).
type csvw_datatype =
  | CSVW_DT_Named  : string -> csvw_datatype
  | CSVW_DT_Object :
      base:option string ->
      format:option string ->
      pattern:option string ->
      group_char:option string ->
      decimal_char:option string ->
      dt_id:option string ->
      dt_length:option int ->
      dt_min_length:option int ->
      dt_max_length:option int ->
      dt_minimum:option string ->
      dt_maximum:option string ->
      dt_min_inclusive:option string ->
      dt_max_inclusive:option string ->
      dt_min_exclusive:option string ->
      dt_max_exclusive:option string ->
      csvw_datatype

type csvw_column = {
  col_name             : option string;
  // Best-effort flattened display titles: the corpus's "titles" value
  // is a bare string, an array of strings, or a language-map object
  // (lang code -> string | array of strings) — flattened here without
  // preserving which language tag went with which title, since Stage 1
  // has no consumer that needs the tag (display/labeling is out of
  // scope for csv2rdf/csv2json's own conformance signal).
  col_titles           : list string;
  col_datatype         : option csvw_datatype;
  col_virtual          : option bool;
  col_suppress_output  : option bool;
  col_required         : option bool;
  col_about_url        : option string;   // template string, unresolved (Stage 3)
  col_property_url     : option string;   // template string, unresolved (Stage 3)
  col_value_url        : option string;   // template string, unresolved (Stage 3)
  // `separator`: when present, the cell is a LIST value — split on this
  // string, each element converted + emitted as its own triple
  // (tabular-metadata section "separator"; test228-230).
  col_separator        : option string;
  // Stage 2 (inherited properties, tabular-metadata section 5.1.1):
  // `lang`/`null` are two more of the eleven inherited properties
  // (aboutUrl/datatype/default/lang/null/ordered/propertyUrl/required/
  // separator/textDirection/valueUrl); `default`/`ordered`/
  // `textDirection` are not modeled yet (no consumer in
  // CSVW.Conversion reads them) — a narrower slice than the full
  // eleven, not a claim of completeness.
  col_lang             : option string;
  col_null             : option string;
  // `ordered` at column level (test307: one column ordered, its sibling
  // not) — same rdf:List semantics as the inherited default above.
  col_ordered          : option bool;
}

type csvw_dialect = {
  dia_delimiter          : option string;
  dia_quote_char         : option string;
  dia_double_quote       : option bool;
  dia_header             : option bool;
  dia_header_row_count   : option int;
  dia_skip_rows          : option int;
  dia_skip_columns       : option int;
  dia_skip_blank_rows    : option bool;
  dia_skip_initial_space : option bool;
  dia_comment_prefix     : option string;
  dia_encoding           : option string;
  dia_trim               : option string;
}

// Stage 2: the inherited-property SUBSET this decoder carries at every
// level above a column (tableSchema / table / table-group) — the same
// six properties csvw_column itself carries (aboutUrl/propertyUrl/
// valueUrl/lang/null/separator) plus datatype, so a value set on the
// table-group or table object directly (sibling of "url"/"tables",
// not nested inside tableSchema/columns) is no longer silently
// dropped. One record shared by all three levels so CSVW.Conversion
// can merge them with one fallback function instead of three
// hand-written ones. `default`/`ordered`/`required`/`textDirection`
// remain undecoded at this level too (matching csvw_column's own
// scope note above).
type csvw_inherited_props = {
  inh_about_url    : option string;
  inh_property_url : option string;
  inh_value_url    : option string;
  inh_lang         : option string;
  inh_null         : option string;
  inh_separator    : option string;
  inh_datatype     : option csvw_datatype;
  // `ordered` (one of the eleven inherited properties): when true a
  // separator-split cell becomes an rdf:List rather than repeated
  // triples (test306/307). Only consulted by CSVW.Conversion when a
  // `separator` is also in effect.
  inh_ordered      : option bool;
}

let csvw_inherited_empty : csvw_inherited_props = {
  inh_about_url = None; inh_property_url = None; inh_value_url = None;
  inh_lang = None; inh_null = None; inh_separator = None; inh_datatype = None;
  inh_ordered = None;
}

// csvw_decode_inherited (needs csvw_decode_datatype, defined below) is
// declared just after it — see "Inherited-property decode" below.

type csvw_table_schema = {
  ts_columns      : list csvw_column;
  // primaryKey/foreignKeys may be a bare column-name string or a list
  // of column names per the spec; Stage 1 keeps only the bare-string
  // shorthand (the corpus's dominant form) — a JArray-valued
  // primaryKey decodes to None here, not a decode failure, per the
  // leniency policy above (list-valued composite keys are a follow-on,
  // not this stage's job).
  ts_primary_key  : option string;
  ts_inherited    : csvw_inherited_props;
  // `rowTitles` (tabular-metadata): a column NAME or list of column
  // names whose per-row cell values are emitted as csvw:title triples
  // on that row's node (test235/236). A bare-string value is a
  // one-element list; anything but a string or string array decodes to
  // the empty list (feature absent).
  ts_row_titles   : list string;
}

type csvw_table = {
  tbl_url          : option string;
  tbl_dialect      : option csvw_dialect;
  tbl_table_schema : option csvw_table_schema;
  // Common properties (tabular-metadata section 5.8): every top-level
  // member of the table object whose name is a prefixed name or an
  // absolute URL (heuristic: contains a ':') rather than a reserved
  // CSVW keyword — kept as the VERBATIM json_val so the conversion
  // layer (CSVW.Conversion) can emit them as RDF triples on the table
  // node. Reserved CSVW keys (url, tableSchema, dialect, notes, ...)
  // never contain ':', so this simple filter never captures one; the
  // '@'-prefixed JSON-LD keywords (@context/@id/@type) likewise carry
  // no ':' and are excluded. Interpreting these into RDF (CURIE
  // expansion, @value/@id/@language node forms) is CSVW.Conversion's
  // job, not this decoder's.
  tbl_common       : list (string & json_val);
  // Stage 2: inherited properties set directly on the table object
  // (sibling of "url"/"tableSchema"), e.g. `{"url": "x.csv", "aboutUrl":
  // "#row-{_row}", "tableSchema": {...}}` — test038/test126/test305-307
  // family.
  tbl_inherited    : csvw_inherited_props;
  // Schema-by-reference (tabular-metadata: `tableSchema` MAY be a string
  // that is a URL of an external schema document, test034/035): when the
  // `tableSchema` value is a bare JSON string this holds that (unresolved)
  // URL and `tbl_table_schema` stays None. The consumer (runner I/O) reads
  // the referenced local file and calls csvw_table_inline_schema to fold
  // the decoded schema in, as if it had been written inline.
  tbl_schema_ref   : option string;
  // Table-level `suppressOutput` (tabular-metadata): a table with
  // suppressOutput=true contributes NO output at all — no csvw:Table
  // node, no rows, no cell triples (test034/035: the professions and
  // organizations lookup tables are suppressed; only senior/junior
  // roles reach the output).
  tbl_suppress_output : option bool;
}

// Stage 2: a table group's own top-level annotations — common
// properties (rdfs:label/rdfs:comment/... test275-278 family) and
// inherited-property defaults (test039 family: aboutUrl/propertyUrl/
// lang/etc set once at the top of a "tables": [...] document, meant
// to cascade into every table that doesn't override them).
type csvw_group_meta = {
  grp_common    : list (string & json_val);
  grp_inherited : csvw_inherited_props;
}

let csvw_group_meta_empty : csvw_group_meta = {
  grp_common = []; grp_inherited = csvw_inherited_empty;
}

// A metadata document is either a single annotated table (top-level
// "url"/"tableSchema"/"dialect" — its own tbl_common/tbl_inherited
// already carry whatever the top object set directly) or a table
// group ("tables": [...] plus the group's own csvw_group_meta: common
// properties + inherited-property defaults, Stage 2). A group's
// shared dialect/tableSchema (a table inside "tables" with NO
// tableSchema/dialect of its own) is still not decoded — that remains
// a separate, narrower gap from inherited-property propagation.
type csvw_metadata =
  | CSVW_Table      : csvw_table -> csvw_metadata
  | CSVW_TableGroup : list csvw_table -> csvw_group_meta -> csvw_metadata

// ================================================================
// Titles: string | list string | lang-map object -> flattened list
// ================================================================

// One titles-property VALUE position: a bare string, or an array of
// strings (non-string array elements are skipped, not fatal — the
// leniency policy). Anything else (object, number, bool, null)
// contributes no titles.
let csvw_titles_value (v:json_val) : list string =
  match v with
  | JString s -> [s]
  | JArray items ->
    List.Tot.concatMap
      (fun (item:json_val) -> match item with | JString s -> [s] | _ -> [])
      items
  | _ -> []

// A lang-map object's fields: each field's value is itself a
// titles-value (string or array of strings); flatten all of them,
// dropping the language-tag key.
let rec csvw_titles_fields (fields:list (string & json_val))
  : Tot (list string) (decreases fields) =
  match fields with
  | [] -> []
  | (_, v) :: tl -> csvw_titles_value v @ csvw_titles_fields tl

let csvw_decode_titles (v:json_val) : list string =
  match v with
  | JObject fields -> csvw_titles_fields fields
  | _ -> csvw_titles_value v

// ================================================================
// Datatype decode
// ================================================================

let csvw_decode_datatype (v:json_val) : option csvw_datatype =
  match v with
  | JString s -> Some (CSVW_DT_Named s)
  | JObject _ ->
    // `format` is either a bare string (date pattern, boolean
    // trueVal|falseVal, or a number pattern given as a string) or an
    // object carrying `pattern`/`groupChar`/`decimalChar` (numeric
    // types). Read the string form and, when it is an object, pull the
    // nested numeric-format members from IT rather than the datatype
    // object's top level (tabular-metadata section "Formats for numeric
    // types").
    let fmt_field = json_get_field "format" v in
    let fmt_str = (match fmt_field with Some (JString s) -> Some s | _ -> None) in
    let fmt_obj = (match fmt_field with Some (JObject _) -> fmt_field | _ -> None) in
    let get_in_fmt (key:string) : option string =
      (match fmt_obj with Some o -> json_get_string key o | None -> None) in
    Some (CSVW_DT_Object
            (json_get_string "base" v)
            fmt_str
            (get_in_fmt "pattern")
            (get_in_fmt "groupChar")
            (get_in_fmt "decimalChar")
            (json_get_string "@id" v)
            (json_get_int "length" v)
            (json_get_int "minLength" v)
            (json_get_int "maxLength" v)
            (json_get_num_or_str "minimum" v)
            (json_get_num_or_str "maximum" v)
            (json_get_num_or_str "minInclusive" v)
            (json_get_num_or_str "maxInclusive" v)
            (json_get_num_or_str "minExclusive" v)
            (json_get_num_or_str "maxExclusive" v))
  | _ -> None

// ================================================================
// Inherited-property decode (Stage 2) — the csvw_inherited_props
// subset, read directly off an already-parsed object `v`. Used
// identically at tableSchema, table, and table-group level (each
// passes its own json_val); csvw_decode_table_schema/csvw_decode_table
// and the top-level table-group decode below each call this once.
//
// Graceful degradation (tabular-metadata section 4, quoted verbatim
// in test041/test046's manifest comments): "If a property has a value
// that is not permitted by this specification ... compliant
// applications MUST generate a warning and behave as if the property
// had not been specified." An invalid `lang` (not BCP47-shaped —
// test041's "notavalidlanguagetag") or a non-built-in `datatype` name
// (test046's "anySimpleType") therefore decodes to None here, exactly
// as if absent, rather than propagating an illegal value into every
// cell literal.
// ================================================================

let csvw_inh_char_is_alpha (c:FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  (n >= 65 && n <= 90) || (n >= 97 && n <= 122)

let csvw_inh_char_is_alnum (c:FStar.Char.char) : bool =
  csvw_inh_char_is_alpha c ||
  (let n = FStar.Char.int_of_char c in n >= 48 && n <= 57)

// Split a char list on '-' (0x2D). Total on the list structure.
let rec csvw_inh_split_hyphen (cs : list FStar.Char.char) (acc : list FStar.Char.char)
  : Tot (list (list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> [List.Tot.rev acc]
  | c :: tl ->
    if FStar.Char.int_of_char c = 45
    then (List.Tot.rev acc) :: csvw_inh_split_hyphen tl []
    else csvw_inh_split_hyphen tl (c :: acc)

// BCP47 plausibility: primary subtag 2-8 ASCII letters; each further
// '-'-separated subtag 1-8 ASCII alphanumerics. Accepts every tag the
// corpus uses ("de", "en", "en-US"); rejects test041's 20-letter
// non-tag. Deliberately a syntactic shape check, not a registry
// lookup — same depth as the SPARQL LANGMATCHES machinery needs.
let csvw_lang_tag_ok (s : string) : bool =
  match csvw_inh_split_hyphen (String.list_of_string s) [] with
  | [] -> false
  | first :: rest ->
    let fl = List.Tot.length first in
    fl >= 2 && fl <= 8 && List.Tot.for_all csvw_inh_char_is_alpha first &&
    List.Tot.for_all
      (fun (sub : list FStar.Char.char) ->
         let l = List.Tot.length sub in
         l >= 1 && l <= 8 && List.Tot.for_all csvw_inh_char_is_alnum sub)
      rest

// tabular-metadata section 5.11.1 "Built-in Datatypes" — the closed
// name list a string-valued `datatype` may use (note: anySimpleType
// is NOT in it, test046).
let csvw_builtin_datatype_names : list string = [
  "anyAtomicType"; "anyURI"; "base64Binary"; "boolean"; "byte"; "date";
  "dateTime"; "dateTimeStamp"; "dayTimeDuration"; "decimal"; "double";
  "duration"; "float"; "gDay"; "gMonth"; "gMonthDay"; "gYear";
  "gYearMonth"; "hexBinary"; "int"; "integer"; "language"; "long";
  "Name"; "negativeInteger"; "NMTOKEN"; "nonNegativeInteger";
  "nonPositiveInteger"; "normalizedString"; "positiveInteger"; "QName";
  "short"; "string"; "time"; "token"; "unsignedByte"; "unsignedInt";
  "unsignedLong"; "unsignedShort"; "xml"; "html"; "json"; "number";
  "binary"; "datetime"; "any"; "yearMonthDuration" ]

let csvw_is_builtin_datatype_name (s:string) : bool =
  List.Tot.mem s csvw_builtin_datatype_names

// Graceful degradation for a decoded datatype whose NAME (string form)
// or object `base` is not one of the section 5.11.1 built-in datatypes
// (tabular-metadata section 4): "a string ... MUST be one of the
// built-in datatypes ... or an absolute URL" — the reference processor
// nonetheless treats a non-built-in string value (test150 "foo",
// test238 an absolute URL that does not resolve) as a warning and
// behaves as if the datatype were absent; likewise an object whose
// `base` names a non-built-in type (test151 `{"base": "foo"}`). An
// object with NO `base` (format-only / @id-only) is left untouched.
let csvw_datatype_valid_or_degrade (d : csvw_datatype) : option csvw_datatype =
  match d with
  | CSVW_DT_Named n ->
    if csvw_is_builtin_datatype_name n then Some d else None
  | CSVW_DT_Object base_opt _ _ _ _ _ _ _ _ _ _ _ _ _ _ ->
    (match base_opt with
     | Some b -> if csvw_is_builtin_datatype_name b then Some d else None
     | None -> Some d)

// A URI-template inherited property (aboutUrl/propertyUrl/valueUrl):
// a string is the template; a NON-string present value (a JSON bool or
// number — test047/048/049's `"aboutUrl": true` etc.) is not a valid
// template, and per the reference processor degrades to the EMPTY
// template "" (which expands to the table's own base URL), NOT to
// absent (which would fall back to the blank-node / default-property
// behaviour). JNull / absent stays None.
let csvw_inh_uri_template (key:string) (v:json_val) : option string =
  match json_get_field key v with
  | Some (JString s) -> Some s
  | Some (JBool _) | Some (JNumber _) -> Some ""
  | _ -> None

let csvw_decode_inherited (v:json_val) : csvw_inherited_props = {
  inh_about_url    = csvw_inh_uri_template "aboutUrl" v;
  inh_property_url = csvw_inh_uri_template "propertyUrl" v;
  inh_value_url    = csvw_inh_uri_template "valueUrl" v;
  inh_lang         = (match json_get_string "lang" v with
                       | Some l -> if csvw_lang_tag_ok l then Some l else None
                       | None -> None);
  inh_null         = json_get_string "null" v;
  inh_separator    = json_get_string "separator" v;
  inh_datatype     = (match json_get_field "datatype" v with
                       | Some dv ->
                         (match csvw_decode_datatype dv with
                          | Some d -> csvw_datatype_valid_or_degrade d
                          | None -> None)
                       | None -> None);
  inh_ordered      = json_get_bool "ordered" v;
}

// ================================================================
// Column decode
// ================================================================

let csvw_decode_column (v:json_val) : option csvw_column =
  match v with
  | JObject _ ->
    let titles =
      match json_get_field "titles" v with
      | Some tv -> csvw_decode_titles tv
      | None -> [] in
    let datatype =
      match json_get_field "datatype" v with
      | Some dv -> (match csvw_decode_datatype dv with
                    | Some d -> csvw_datatype_valid_or_degrade d
                    | None -> None)
      | None -> None in
    Some ({
      col_name             = json_get_string "name" v;
      col_titles           = titles;
      col_datatype         = datatype;
      col_virtual          = json_get_bool "virtual" v;
      col_suppress_output  = json_get_bool "suppressOutput" v;
      col_required         = json_get_bool "required" v;
      col_about_url        = json_get_string "aboutUrl" v;
      col_property_url     = json_get_string "propertyUrl" v;
      col_value_url        = json_get_string "valueUrl" v;
      col_separator        = json_get_string "separator" v;
      col_lang             = json_get_string "lang" v;
      col_null             = json_get_string "null" v;
      col_ordered          = json_get_bool "ordered" v;
    })
  | _ -> None

// All-or-nothing over the column list: a non-object array element is
// a structurally-wrong shape (not a leaf-facet mismatch), so it
// propagates None out, mirroring ShEx.Schema.fst's
// decode_shape_decl_list discipline.
let rec csvw_decode_column_list (items:list json_val)
  : Tot (option (list csvw_column)) (decreases items) =
  match items with
  | [] -> Some []
  | hd :: tl ->
    (match csvw_decode_column hd with
     | None -> None
     | Some c ->
       (match csvw_decode_column_list tl with
        | None -> None
        | Some rest -> Some (c :: rest)))

// ================================================================
// Dialect decode
// ================================================================

let csvw_decode_dialect (v:json_val) : option csvw_dialect =
  match v with
  | JObject _ ->
    Some ({
      dia_delimiter          = json_get_string "delimiter" v;
      dia_quote_char         = json_get_string "quoteChar" v;
      dia_double_quote       = json_get_bool "doubleQuote" v;
      dia_header             = json_get_bool "header" v;
      dia_header_row_count   = json_get_int "headerRowCount" v;
      dia_skip_rows          = json_get_int "skipRows" v;
      dia_skip_columns       = json_get_int "skipColumns" v;
      dia_skip_blank_rows    = json_get_bool "skipBlankRows" v;
      dia_skip_initial_space = json_get_bool "skipInitialSpace" v;
      dia_comment_prefix     = json_get_string "commentPrefix" v;
      dia_encoding           = json_get_string "encoding" v;
      dia_trim               = json_get_string_or_bool_as_string "trim" v;
    })
  | _ -> None

// ================================================================
// tableSchema decode
// ================================================================

let csvw_decode_table_schema (v:json_val) : option csvw_table_schema =
  match v with
  | JObject _ ->
    let columns_ok, columns =
      match json_get_array "columns" v with
      | None -> true, []   // "columns" is optional (schema inferred from header row)
      | Some items ->
        (match csvw_decode_column_list items with
         | Some cs -> true, cs
         | None -> false, []) in
    if not columns_ok then None
    else
      Some ({
        ts_columns      = columns;
        ts_primary_key  = json_get_string "primaryKey" v;
        ts_inherited    = csvw_decode_inherited v;
        ts_row_titles   = (match json_get_field "rowTitles" v with
                            | Some rv -> csvw_titles_value rv
                            | None -> []);
      })
  | _ ->
    // tabular-metadata section 4 graceful degradation ("MUST act as if
    // it was an empty object"), quoted verbatim in test107's manifest
    // comment: a tableSchema value that is not even a JSON object at
    // all (test107: "tableSchema": 1) decodes to an EMPTY schema, not
    // a decode failure — distinct from columns_ok=false above (a
    // structurally-wrong "columns" array element inside an otherwise
    // valid object), which still propagates None.
    Some ({ ts_columns = []; ts_primary_key = None; ts_inherited = csvw_inherited_empty; ts_row_titles = [] })

// ================================================================
// Table decode
// ================================================================

// A metadata key names a common property when it is a prefixed name or
// an absolute URL — heuristically, when it contains a ':'. Reserved CSVW
// keywords (url, tableSchema, dialect, ...) and the JSON-LD keywords
// (@context/@id/@type) contain no ':' and are therefore never captured.
let csvw_key_is_common (k:string) : bool =
  List.Tot.existsb (fun (c:FStar.Char.char) -> FStar.Char.int_of_char c = 58 (* ':' *))
    (String.list_of_string k)

let csvw_common_fields (v:json_val) : list (string & json_val) =
  match v with
  | JObject fields -> List.Tot.filter (fun (kv:(string & json_val)) -> csvw_key_is_common (fst kv)) fields
  | _ -> []

let csvw_decode_table (v:json_val) : option csvw_table =
  match v with
  | JObject _ ->
    let dialect =
      match json_get_field "dialect" v with
      | Some dv -> csvw_decode_dialect dv
      | None -> None in
    // A `tableSchema` given as a bare STRING is a URL reference to an
    // external schema document (test034/035): defer it to `tbl_schema_ref`
    // and leave `tbl_table_schema` None for the consumer to resolve; any
    // other (object or degrade-to-empty) form decodes inline as before.
    let schema_ref = match json_get_field "tableSchema" v with
                     | Some (JString s) -> Some s | _ -> None in
    let schema_ok, schema =
      match json_get_field "tableSchema" v with
      | None -> true, None
      | Some (JString _) -> true, None
      | Some sv ->
        (match csvw_decode_table_schema sv with
         | Some ts -> true, Some ts
         | None -> false, None) in
    if not schema_ok then None
    else
      Some ({
        tbl_url          = json_get_string "url" v;
        tbl_dialect      = dialect;
        tbl_table_schema = schema;
        tbl_common       = csvw_common_fields v;
        tbl_inherited    = csvw_decode_inherited v;
        tbl_schema_ref   = schema_ref;
        tbl_suppress_output = json_get_bool "suppressOutput" v;
      })
  | _ -> None

// Schema-by-reference resolution (tabular-metadata, test034/035): parse
// an external schema document's TEXT (the runner reads the referenced
// local file) into a table schema, then fold it into a table that
// carried only a `tbl_schema_ref`, as if it had been written inline.
let csvw_decode_table_schema_text (input:string) : option csvw_table_schema =
  match parse_json input with
  | None -> None
  | Some v -> csvw_decode_table_schema v

let csvw_table_inline_schema (t:csvw_table) (ts:csvw_table_schema) : csvw_table =
  { t with tbl_table_schema = Some ts; tbl_schema_ref = None }

// All-or-nothing over the table-group's "tables" list — same
// structural-shape discipline as csvw_decode_column_list.
let rec csvw_decode_table_list (items:list json_val)
  : Tot (option (list csvw_table)) (decreases items) =
  match items with
  | [] -> Some []
  | hd :: tl ->
    (match csvw_decode_table hd with
     | None -> None
     | Some t ->
       (match csvw_decode_table_list tl with
        | None -> None
        | Some rest -> Some (t :: rest)))

// ================================================================
// Metadata validation (NegativeRdfTest support). The Metadata
// Vocabulary spec lists consistency conditions a conforming processor
// MUST reject; the csv2rdf suite's NegativeRdfTest fixtures each quote
// the exact condition in their rdfs:comment. This is a pure validation
// pass over the raw json_val tree (returning false => the decoder
// yields None => the runner records "no RDF produced", the negative
// tests' PASS criterion). Kept separate from the AST decoders above so
// the decoded AST and CSVW.Conversion stay untouched. Cited tests are
// third_party/testing/csvw/tests/manifest-rdf entries.
// ================================================================

let csvw_str_starts_with (pfx s : string) : bool =
  let lp = String.length pfx in
  String.length s >= lp && String.sub s 0 lp = pfx

let csvw_is_bnode_ref (s : string) : bool = csvw_str_starts_with "_:" s

let csvw_char_is_ws (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  n = 0x20 || n = 0x09 || n = 0x0A || n = 0x0D

let csvw_has_ws (s : string) : bool =
  List.Tot.existsb csvw_char_is_ws (String.list_of_string s)

// Lexicographic char-list compare (-1 / 0 / 1).
let rec csvw_chars_cmp (a b : list FStar.Char.char) : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: xs, y :: ys ->
    let ix = FStar.Char.int_of_char x in
    let iy = FStar.Char.int_of_char y in
    if ix < iy then -1 else if ix > iy then 1 else csvw_chars_cmp xs ys

let csvw_str_cmp (a b : string) : int =
  csvw_chars_cmp (String.list_of_string a) (String.list_of_string b)

// Compare two constraint lexemes: numeric when both are integer lexemes,
// else lexicographic (equal-width ISO date/time strings order correctly
// this way, which every date-range fixture in the suite uses).
let csvw_lex_cmp (a b : string) : int =
  match csvw_parse_int_string a, csvw_parse_int_string b with
  | Some x, Some y -> if x < y then -1 else if x > y then 1 else 0
  | _ -> csvw_str_cmp a b

// A datatype @id MUST NOT be the URL of a built-in datatype (test244)
// nor a blank node (test243/test267).
let csvw_is_builtin_dt_url (s : string) : bool =
  csvw_str_starts_with "http://www.w3.org/2001/XMLSchema#" s ||
  s = "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML" ||
  s = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral" ||
  s = "http://www.w3.org/ns/csvw#JSON"

// length / minLength / maxLength apply only to string- or binary-derived
// base datatypes (test201: length on date => reject).
let csvw_is_string_like_base (n : string) : bool =
  n = "string" || n = "normalizedString" || n = "token" || n = "language" ||
  n = "Name" || n = "NMTOKEN" || n = "NMTOKENS" || n = "xml" || n = "html" ||
  n = "json" || n = "anyAtomicType" || n = "base64Binary" || n = "hexBinary" ||
  n = "binary" || n = "anyURI" || n = "QName" || n = "ENTITY" || n = "ID" ||
  n = "IDREF" || n = "NOTATION"

// minimum / maximum / min|maxInclusive / min|maxExclusive apply only to
// numeric, date/time, or duration base datatypes (test222-227: such a
// constraint on the string base => reject).
let csvw_is_ordered_base (n : string) : bool =
  n = "number" || n = "decimal" || n = "integer" || n = "long" || n = "int" ||
  n = "short" || n = "byte" || n = "nonNegativeInteger" || n = "positiveInteger" ||
  n = "nonPositiveInteger" || n = "negativeInteger" || n = "unsignedLong" ||
  n = "unsignedInt" || n = "unsignedShort" || n = "unsignedByte" || n = "double" ||
  n = "float" ||
  n = "date" || n = "dateTime" || n = "datetime" || n = "time" ||
  n = "dateTimeStamp" || n = "gYear" || n = "gYearMonth" || n = "gMonth" ||
  n = "gMonthDay" || n = "gDay" ||
  n = "duration" || n = "dayTimeDuration" || n = "yearMonthDuration"

// A valid @id / @type token inside a common-property value object: a
// string that is neither a blank-node reference nor whitespace-bearing
// (tests 137-141). A non-string @type/@id (e.g. an integer, test140) is
// rejected by the caller before reaching here.
let csvw_valid_iri_token (s : string) : bool =
  not (csvw_is_bnode_ref s) && not (csvw_has_ws s)

let csvw_key_is_at (k : string) : bool =
  String.length k >= 1 && String.sub k 0 1 = "@"

let csvw_reserved_at_key (k : string) : bool =
  k = "@value" || k = "@type" || k = "@language" || k = "@id"

// List-only helpers (structural recursion on their own argument, no
// call back into the value walker, so kept out of the fuel-threaded
// mutual group below).
let rec csvw_fields_no_bad_at (fields : list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: tl -> (not (csvw_key_is_at k) || csvw_reserved_at_key k) && csvw_fields_no_bad_at tl

let rec csvw_fields_value_keys_ok (fields : list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: tl -> (k = "@value" || k = "@type" || k = "@language") && csvw_fields_value_keys_ok tl

let rec csvw_all_type_tokens_ok (ts : list json_val) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | (JString t) :: tl -> csvw_valid_iri_token t && csvw_all_type_tokens_ok tl
  | _ -> false

// Recursive JSON-LD value-object validation for common-property values
// (tabular-metadata section 5.8 + section 6 note on value objects).
// Rejects: @-prefixed keys other than @value/@type/@language/@id
// (test146 @faux, test134 @context, test135 @list, test136 @set); a
// @value object carrying anything but @type/@language, or both @type and
// @language, or a non-scalar @value (test142/test143); a @language with
// no @value (test144); a blank-node or malformed @id/@type (test137-141).
let rec csvw_common_value_valid (fuel:nat) (v:json_val) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else match v with
       | JObject fields ->
         let no_bad_at =
           csvw_fields_no_bad_at fields in
         if not no_bad_at then false
         else
           (match json_get_field "@value" v with
            | Some valv ->
              let has_type = Some? (json_get_field "@type" v) in
              let has_lang = Some? (json_get_field "@language" v) in
              let only_allowed = csvw_fields_value_keys_ok fields in
              let scalar_ok = (match valv with JString _ | JNumber _ | JBool _ -> true | _ -> false) in
              let type_ok = (match json_get_field "@type" v with
                             | Some (JString t) -> csvw_valid_iri_token t
                             | Some _ -> false
                             | None -> true) in
              let lang_ok = (match json_get_field "@language" v with
                             | Some (JString _) -> true | Some _ -> false | None -> true) in
              only_allowed && not (has_type && has_lang) && scalar_ok && type_ok && lang_ok
            | None ->
              let no_lang = None? (json_get_field "@language" v) in
              let id_ok = (match json_get_field "@id" v with
                           | Some (JString s) -> not (csvw_is_bnode_ref s)
                           | Some _ -> false | None -> true) in
              let type_ok = (match json_get_field "@type" v with
                             | Some (JString t) -> csvw_valid_iri_token t
                             | Some (JArray ts) -> csvw_all_type_tokens_ok ts
                             | Some _ -> false | None -> true) in
              no_lang && id_ok && type_ok && csvw_fields_valid (fuel - 1) fields)
       | JArray items -> csvw_items_valid (fuel - 1) items
       | _ -> true

and csvw_fields_valid (fuel:nat) (fields : list (string & json_val)) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else match fields with
       | [] -> true
       | (k, vv) :: tl ->
         (if csvw_key_is_at k then true else csvw_common_value_valid (fuel - 1) vv)
         && csvw_fields_valid (fuel - 1) tl

and csvw_items_valid (fuel:nat) (items : list json_val) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else match items with
       | [] -> true
       | hd :: tl -> csvw_common_value_valid (fuel - 1) hd && csvw_items_valid (fuel - 1) tl

// Validate every common-property member (a top-level key containing ':')
// of an object as a JSON-LD value.
let rec csvw_common_props_valid_list (fields : list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, vv) :: tl ->
    (if csvw_key_is_common k then csvw_common_value_valid (json_size vv) vv else true)
    && csvw_common_props_valid_list tl

let csvw_common_props_valid (v:json_val) : bool =
  match v with
  | JObject fields -> csvw_common_props_valid_list fields
  | _ -> true

// --- structural @id / @type checks (blank-node @id => reject, test077-
//     082/141; wrong structural @type => reject, test083-088) ---

// A non-string @id (test102: "@id": 1) is graceful degradation ("act
// as if the property had not been specified"), NOT a rejection — only
// a STRING @id that is itself a blank-node reference (test077-082/141)
// is a hard reject.
let csvw_obj_id_ok (v:json_val) : bool =
  match json_get_field "@id" v with
  | Some (JString s) -> not (csvw_is_bnode_ref s)
  | Some _ -> true
  | None -> true

let csvw_obj_type_ok (v:json_val) (expected:string) : bool =
  match json_get_field "@type" v with
  | Some (JString t) -> t = expected
  | Some _ -> false
  | None -> true

// --- datatype consistency (test199-201, test216-227, test243/244/261/267) ---

let csvw_dt_base_name (dt:json_val) : string =
  match json_get_field "base" dt with Some (JString b) -> b | _ -> "string"

let csvw_dt_has (dt:json_val) (k:string) : bool = Some? (json_get_field k dt)

let csvw_dt_lex (dt:json_val) (k:string) : option string =
  match json_get_field k dt with Some (JString s) -> Some s | Some (JNumber s) -> Some s | _ -> None

let csvw_datatype_valid (dt:json_val) : bool =
  match dt with
  | JObject _ ->
    let idok = (match json_get_field "@id" dt with
                | Some (JString s) -> not (csvw_is_bnode_ref s) && not (csvw_is_builtin_dt_url s)
                | Some _ -> false | None -> true) in
    let base = csvw_dt_base_name dt in
    let strlike = csvw_is_string_like_base base in
    let ordered = csvw_is_ordered_base base in
    let has_len = csvw_dt_has dt "length" || csvw_dt_has dt "minLength" || csvw_dt_has dt "maxLength" in
    let has_ord = csvw_dt_has dt "minimum" || csvw_dt_has dt "maximum" ||
                  csvw_dt_has dt "minInclusive" || csvw_dt_has dt "maxInclusive" ||
                  csvw_dt_has dt "minExclusive" || csvw_dt_has dt "maxExclusive" in
    let type_ok = (not has_len || strlike) && (not has_ord || ordered) in
    let excl_ok = not (csvw_dt_has dt "minInclusive" && csvw_dt_has dt "minExclusive")
               && not (csvw_dt_has dt "maxInclusive" && csvw_dt_has dt "maxExclusive") in
    let len_ok =
      (match json_get_int "length" dt, json_get_int "minLength" dt with
       | Some l, Some ml -> l >= ml | _ -> true) &&
      (match json_get_int "length" dt, json_get_int "maxLength" dt with
       | Some l, Some xl -> l <= xl | _ -> true) &&
      (match json_get_int "minLength" dt, json_get_int "maxLength" dt with
       | Some ml, Some xl -> ml <= xl | _ -> true) in
    let minI = csvw_dt_lex dt "minInclusive" in
    let minE = csvw_dt_lex dt "minExclusive" in
    let maxI = csvw_dt_lex dt "maxInclusive" in
    let maxE = csvw_dt_lex dt "maxExclusive" in
    let range_ok =
      (match maxI, minI with Some a, Some b -> csvw_lex_cmp a b >= 0 | _ -> true) &&
      (match maxI, minE with Some a, Some b -> csvw_lex_cmp a b > 0 | _ -> true) &&
      (match maxE, minE with Some a, Some b -> csvw_lex_cmp a b > 0 | _ -> true) &&
      (match maxE, minI with Some a, Some b -> csvw_lex_cmp a b > 0 | _ -> true) in
    idok && type_ok && excl_ok && len_ok && range_ok
  | _ -> true

// --- column list: unique names (test128), virtual-after-nonvirtual
//     (test133), per-column @id/@type/datatype ---

let csvw_col_name_of (c:json_val) : option string = json_get_string "name" c
let csvw_col_is_virtual (c:json_val) : bool =
  match json_get_bool "virtual" c with Some true -> true | _ -> false

let rec csvw_names_unique (seen : list string) (cols : list json_val) : Tot bool (decreases cols) =
  match cols with
  | [] -> true
  | c :: tl ->
    (match csvw_col_name_of c with
     | Some n -> if List.Tot.mem n seen then false else csvw_names_unique (n :: seen) tl
     | None -> csvw_names_unique seen tl)

let rec csvw_virtual_order_ok (seen_virtual : bool) (cols : list json_val) : Tot bool (decreases cols) =
  match cols with
  | [] -> true
  | c :: tl ->
    let v = csvw_col_is_virtual c in
    if seen_virtual && not v then false else csvw_virtual_order_ok (seen_virtual || v) tl

let rec csvw_columns_meta_ok (cols : list json_val) : Tot bool (decreases cols) =
  match cols with
  | [] -> true
  | c :: tl ->
    csvw_obj_id_ok c && csvw_obj_type_ok c "Column" &&
    (match json_get_field "datatype" c with Some dt -> csvw_datatype_valid dt | None -> true) &&
    csvw_common_props_valid c &&
    csvw_columns_meta_ok tl

let csvw_dialect_valid (v:json_val) : bool =
  match v with
  | JObject _ -> csvw_obj_id_ok v && csvw_obj_type_ok v "Dialect"
  | _ -> true

// --- transformations: blank-node @id => reject (test082); a
//     transformation's @type, if present, MUST be "Template" (test088) ---

let csvw_transformation_valid (v:json_val) : bool =
  match v with
  | JObject _ -> csvw_obj_id_ok v && csvw_obj_type_ok v "Template"
  | _ -> true

let rec csvw_transformations_all_valid (items:list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> true
  | t :: tl -> csvw_transformation_valid t && csvw_transformations_all_valid tl

let csvw_transformations_ok (v:json_val) : bool =
  match json_get_array "transformations" v with
  | None -> true
  | Some items -> csvw_transformations_all_valid items

// --- foreign keys: a foreign key definition contains ONLY
//     columnReference + reference (test271); its reference contains ONLY
//     resource|schemaReference + columnReference and MUST be an object
//     (test108/test272); and its (local) columnReference MUST name an
//     existing column (test104). ---

let rec csvw_column_names (cols:list json_val) : Tot (list string) (decreases cols) =
  match cols with
  | [] -> []
  | c :: tl ->
    (match json_get_string "name" c with
     | Some n -> n :: csvw_column_names tl
     | None -> csvw_column_names tl)

let csvw_colref_ok (names:list string) (v:json_val) : bool =
  if Nil? names then true   // columns inferred from header: no name set to check against
  else match v with
       | JString s -> List.Tot.mem s names
       | JArray items ->
         List.Tot.for_all (fun (x:json_val) -> match x with JString s -> List.Tot.mem s names | _ -> false) items
       | _ -> false

let csvw_fk_valid (names:list string) (fk:json_val) : bool =
  match fk with
  | JObject fields ->
    List.Tot.for_all
      (fun (kv:(string&json_val)) -> let k = fst kv in k = "columnReference" || k = "reference") fields &&
    (match json_get_field "columnReference" fk with Some cr -> csvw_colref_ok names cr | None -> false) &&
    (match json_get_field "reference" fk with
     | Some (JObject rfields) ->
       List.Tot.for_all
         (fun (kv:(string&json_val)) -> let k = fst kv in
            k = "resource" || k = "schemaReference" || k = "columnReference") rfields
       && Some? (json_get_field "columnReference" (JObject rfields))
     | Some _ -> false
     | None -> false)
  | _ -> false

// A foreignKeys array item that is not even a JSON object at all
// (test097: `[{...valid FK...}, 1]`) is IGNORED per tabular-metadata's
// "any items within an array that are not valid objects of the type
// expected are ignored" (test097's own manifest comment, verbatim) —
// distinct from a JObject item with the wrong INTERNAL shape (extra
// keys, non-object `reference`; test108/271/272), which csvw_fk_valid
// still rejects.
let rec csvw_fks_all_valid (names:list string) (fks:list json_val) : Tot bool (decreases fks) =
  match fks with
  | [] -> true
  | fk :: tl ->
    (match fk with
     | JObject _ -> csvw_fk_valid names fk
     | _ -> true)
    && csvw_fks_all_valid names tl

let csvw_schema_valid (v:json_val) : bool =
  match v with
  | JObject _ ->
    let names = (match json_get_array "columns" v with Some cols -> csvw_column_names cols | None -> []) in
    csvw_obj_id_ok v && csvw_obj_type_ok v "Schema" &&
    (match json_get_array "columns" v with
     | None -> true
     | Some cols ->
       csvw_names_unique [] cols && csvw_virtual_order_ok false cols && csvw_columns_meta_ok cols) &&
    (match json_get_array "foreignKeys" v with
     | None -> true
     | Some fks -> csvw_fks_all_valid names fks)
  | _ -> true

// `in_group` = this table is an element of a table group's "tables"
// array, where url is mandatory (test090). A url present but non-string
// is always invalid (test103).
let csvw_table_valid (in_group:bool) (v:json_val) : bool =
  match v with
  | JObject _ ->
    csvw_obj_id_ok v &&
    csvw_obj_type_ok v "Table" &&
    (match json_get_field "url" v with
     | Some (JString _) -> true
     | Some _ -> false
     | None -> not in_group) &&
    (match json_get_field "dialect" v with Some d -> csvw_dialect_valid d | None -> true) &&
    (match json_get_field "tableSchema" v with Some s -> csvw_schema_valid s | None -> true) &&
    csvw_transformations_ok v &&
    csvw_common_props_valid v
  | _ -> false

let rec csvw_tables_all_valid (items : list json_val) : Tot bool (decreases items) =
  match items with
  | [] -> true
  | t :: tl -> csvw_table_valid true t && csvw_tables_all_valid tl

// @context (if present in the array form) restricted to a string sentinel
// followed by an object holding only @base / @language (test274).
let csvw_context_valid (v:json_val) : bool =
  match json_get_field "@context" v with
  | Some (JArray [_; JObject fields]) ->
    List.Tot.for_all
      (fun (kv:(string & json_val)) -> let k = fst kv in k = "@base" || k = "@language")
      fields
  | _ -> true

// ================================================================
// Cross-table foreignKey referential integrity (Stage 9, test252/253).
// A foreignKey's `reference` given by `resource` (a sibling table's URL)
// MUST name an existing sibling table AND, when that table's schema is
// inline, an existing column in it. A dangling reference — missing
// target table (test253) or missing target column (test252) — is a
// metadata error: the whole document is rejected (both fixtures are
// NegativeRdfTest, expecting no output). This is distinct from a
// DATA-level FK violation (a row value with no matching target row —
// test034's organization.csv), which is a validation warning and still
// produces output; that is never checked here.
//
// Only `resource`-based references are checked. A `schemaReference`-based
// reference (test034/035) points at an EXTERNAL schema document whose
// columns are not visible at this pre-resolution layer, so it is treated
// as satisfied to avoid false negatives on those positive fixtures.
// ================================================================

// The foreignKeys of a table's inline schema, normalising the
// single-object form (test101) and skipping non-object array items
// (test097's trailing `1`).
let csvw_table_fk_objs (t:json_val) : list json_val =
  match json_get_field "tableSchema" t with
  | Some ts ->
    (match json_get_field "foreignKeys" ts with
     | Some (JArray items) -> List.Tot.filter (fun (i:json_val) -> JObject? i) items
     | Some (JObject fields) -> [JObject fields]
     | _ -> [])
  | _ -> []

// A table's inline column names ([] when the schema is a URL string —
// schema-by-reference, resolved later by the consumer, so its columns
// are invisible here and a reference into it stays unchecked).
let csvw_table_inline_names (t:json_val) : list string =
  match json_get_field "tableSchema" t with
  | Some ts -> (match json_get_array "columns" ts with Some cols -> csvw_column_names cols | None -> [])
  | _ -> []

// A reference object's target column name(s) (string or array form).
let csvw_ref_cols (refobj:json_val) : list string =
  match json_get_field "columnReference" refobj with
  | Some (JString s) -> [s]
  | Some (JArray items) ->
    List.Tot.concatMap (fun (i:json_val) -> match i with JString s -> [s] | _ -> []) items
  | _ -> []

let rec csvw_find_table_by_url (all:list json_val) (res:string)
  : Tot (option json_val) (decreases all) =
  match all with
  | [] -> None
  | t :: tl ->
    (match json_get_string "url" t with
     | Some u -> if u = res then Some t else csvw_find_table_by_url tl res
     | None -> csvw_find_table_by_url tl res)

let csvw_fk_resolves (all:list json_val) (fk:json_val) : bool =
  match json_get_field "reference" fk with
  | Some rf ->
    (match json_get_field "resource" rf with
     | Some (JString res) ->
       (match csvw_find_table_by_url all res with
        | None -> false   // missing destination table (test253)
        | Some tgt ->
          (match csvw_table_inline_names tgt with
           | [] -> true   // target schema external / no inline columns: unchecked
           | tnames -> List.Tot.for_all (fun (c:string) -> List.Tot.mem c tnames) (csvw_ref_cols rf)))
     | _ -> true)   // schemaReference / no resource: unchecked here
  | None -> true

let rec csvw_fks_resolve_list (all fks:list json_val) : Tot bool (decreases fks) =
  match fks with
  | [] -> true
  | fk :: tl -> csvw_fk_resolves all fk && csvw_fks_resolve_list all tl

let rec csvw_group_fks_resolve (all remaining:list json_val) : Tot bool (decreases remaining) =
  match remaining with
  | [] -> true
  | t :: tl -> csvw_fks_resolve_list all (csvw_table_fk_objs t) && csvw_group_fks_resolve all tl

// Whole-document consistency gate. A "tables" member that is an empty
// array (test074) or not an array at all (test098) is rejected; a
// present "tables" makes the top object a table group whose @type, if
// given, MUST be "TableGroup" (test083).
let csvw_metadata_valid (v:json_val) : bool =
  csvw_context_valid v &&
  csvw_obj_id_ok v &&
  (match json_get_field "tables" v with
   | Some (JArray items) ->
     Cons? items &&
     csvw_obj_type_ok v "TableGroup" &&
     csvw_transformations_ok v &&
     csvw_common_props_valid v &&
     csvw_tables_all_valid items &&
     csvw_group_fks_resolve items items
   | Some _ -> false
   | None -> csvw_table_valid false v)

// ================================================================
// Top level
// ================================================================

// Decodes an already-Parser.JSON-parsed metadata document. A "tables"
// array at the top level means a table group (decoded via
// csvw_decode_table_list); otherwise the whole document is decoded as
// a single table (csvw_decode_table). Returns None on any structural
// mismatch — an honest parse failure, never a silently-dropped field —
// or when csvw_metadata_valid rejects a spec consistency condition.
let csvw_decode_metadata (v:json_val) : option csvw_metadata =
  if not (csvw_metadata_valid v) then None
  else
  match json_get_array "tables" v with
  | Some items ->
    (match csvw_decode_table_list items with
     | Some ts ->
       // A `dialect` set at the table-GROUP level (sibling of "tables",
       // test023's `header: false`/`headerRowCount: 0`) cascades to every
       // table that does not declare its own dialect — tabular-metadata's
       // inherited-dialect rule; test058 (a table WITH its own dialect)
       // keeps it, so the cascade only fills the None slots.
       let grp_dia = (match json_get_field "dialect" v with
                      | Some dv -> csvw_decode_dialect dv | None -> None) in
       let ts_dia = List.Tot.map
         (fun (t:csvw_table) ->
            match t.tbl_dialect with Some _ -> t | None -> { t with tbl_dialect = grp_dia }) ts in
       Some (CSVW_TableGroup ts_dia { grp_common = csvw_common_fields v; grp_inherited = csvw_decode_inherited v })
     | None -> None)
  | None ->
    (match csvw_decode_table v with
     | Some t -> Some (CSVW_Table t)
     | None -> None)

// Convenience: parse raw metadata-document text straight to the AST
// in one call.
let csvw_decode_metadata_text (input:string) : option csvw_metadata =
  match parse_json input with
  | None -> None
  | Some v -> csvw_decode_metadata v

// ================================================================
// Simulated HTTP Link-header parsing (metadata discovery step 2,
// tabular-data-model section 5.8). The csv2rdf test harness injects
// the would-be `Link:` response header via the manifest's
// `csvt:httpLink` annotation (there is no live server); its value has
// the RFC 8288 shape `<url>; rel="describedby"`. This parser extracts
// the bracketed URL, but only when a `describedby` relation is present
// — a Link with any other rel is not metadata for the tabular file.
// Pure string work (a parser, per rule #4), so it lives here rather
// than in the runner; the runner reads the annotation string and
// resolves the returned relative URL against the CSV's directory.
// ================================================================

// Characters strictly between the first '<' (0x3C) and the next '>'
// (0x3E), as a string; None if the brackets are absent.
let csvw_bracketed_url (s:string) : option string =
  let rec after_lt (cs:list FStar.Char.char) : Tot (option (list FStar.Char.char)) (decreases cs) =
    match cs with
    | [] -> None
    | c :: tl -> if FStar.Char.int_of_char c = 60 then Some tl else after_lt tl in
  let rec until_gt (cs:list FStar.Char.char) (acc:list FStar.Char.char)
    : Tot (option (list FStar.Char.char)) (decreases cs) =
    match cs with
    | [] -> None
    | c :: tl -> if FStar.Char.int_of_char c = 62 then Some (List.Tot.rev acc)
                 else until_gt tl (c :: acc) in
  match after_lt (String.list_of_string s) with
  | None -> None
  | Some rest ->
    (match until_gt rest [] with
     | None -> None
     | Some url -> Some (String.string_of_list url))

// Does the char-list [hay] contain [needle] as a contiguous sublist?
let rec csvw_chars_has_prefix (needle hay : list FStar.Char.char) : Tot bool (decreases needle) =
  match needle, hay with
  | [], _ -> true
  | _, [] -> false
  | n :: nt, h :: ht -> FStar.Char.int_of_char n = FStar.Char.int_of_char h && csvw_chars_has_prefix nt ht

let rec csvw_chars_contains (needle hay : list FStar.Char.char) : Tot bool (decreases hay) =
  if csvw_chars_has_prefix needle hay then true
  else match hay with
       | [] -> false
       | _ :: tl -> csvw_chars_contains needle tl

let csvw_str_contains (needle hay : string) : bool =
  csvw_chars_contains (String.list_of_string needle) (String.list_of_string hay)

let csvw_link_header_describedby (link_value:string) : option string =
  if csvw_str_contains "describedby" link_value
  then csvw_bracketed_url link_value
  else None

// The document's default language, declared by the @context array's
// second element ({"@language": "en"} in the [sentinel, {...}] form).
// Validated as a BCP47-plausible tag (csvw_lang_tag_ok) — test073's
// "a-bad-language" is rejected and resolves to None, so its common
// properties stay language-free. Used by CSVW.Conversion to
// language-tag common-property natural-language string VALUES
// (test259/260's dc:title/dcat:keyword/schema:name become @en); it is
// deliberately NOT the inherited `lang` for cell values (those stay
// untagged unless the explicit `lang` inherited property is set).
let csvw_context_language (v:json_val) : option string =
  match json_get_field "@context" v with
  | Some (JArray ctx) ->
    (match ctx with
     | [_; second] ->
       (match json_get_string "@language" second with
        | Some l -> if csvw_lang_tag_ok l then Some l else None
        | None -> None)
     | _ -> None)
  | _ -> None

// Convenience: extract the @context default language straight from raw
// metadata-document text (the runner already holds the text; this saves
// it re-parsing the JSON itself, keeping @context interpretation in F*).
let csvw_metadata_context_language (input:string) : option string =
  match parse_json input with
  | None -> None
  | Some v -> csvw_context_language v

// The document's base-URL override, declared by the @context array's
// second element ({"@base": "test273/"} in the [sentinel, {...}] form,
// tabular-metadata section "The `@context` ..."): "a string that is
// interpreted as a URL which is resolved against the location of the
// metadata document to provide the base URL for other URLs" (test273).
// A bare string value (no BCP47 shape check — this is a URL, not a
// language tag). The runner resolves it against the metadata-document
// location and uses the result as the base for table/cell IRIs.
let csvw_context_base (v:json_val) : option string =
  match json_get_field "@context" v with
  | Some (JArray ctx) ->
    (match ctx with
     | [_; second] -> json_get_string "@base" second
     | _ -> None)
  | _ -> None

let csvw_metadata_context_base (input:string) : option string =
  match parse_json input with
  | None -> None
  | Some v -> csvw_context_base v
