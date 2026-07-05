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
// leaf facets (that is CSVW.Validate.fst, Stage 9). A field whose
// declared JSON *shape* is wrong at the container level (a "columns"
// key that in the JSON is anything but an array, an array element that
// is not a JSON object) DOES fail the surrounding decode, mirroring
// ShEx.Schema.fst's decode_shape_decl_list / decode_string_list
// discipline of "None propagates out of a structurally-wrong list."
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
type csvw_datatype =
  | CSVW_DT_Named  : string -> csvw_datatype
  | CSVW_DT_Object :
      base:option string ->
      format:option string ->
      pattern:option string ->
      group_char:option string ->
      decimal_char:option string ->
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

type csvw_table_schema = {
  ts_columns      : list csvw_column;
  // primaryKey/foreignKeys may be a bare column-name string or a list
  // of column names per the spec; Stage 1 keeps only the bare-string
  // shorthand (the corpus's dominant form) — a JArray-valued
  // primaryKey decodes to None here, not a decode failure, per the
  // leniency policy above (list-valued composite keys are a follow-on,
  // not this stage's job).
  ts_primary_key  : option string;
  ts_about_url    : option string;
  ts_property_url : option string;
  ts_value_url    : option string;
}

type csvw_table = {
  tbl_url          : option string;
  tbl_dialect      : option csvw_dialect;
  tbl_table_schema : option csvw_table_schema;
}

// A metadata document is either a single annotated table (top-level
// "url"/"tableSchema"/"dialect") or a table group ("tables": [...],
// optionally with its own shared dialect/tableSchema — NOT decoded
// here, since propagating those down is Stage 2's inherited-property
// work).
type csvw_metadata =
  | CSVW_Table      : csvw_table -> csvw_metadata
  | CSVW_TableGroup : list csvw_table -> csvw_metadata

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
    Some (CSVW_DT_Object
            (json_get_string "base" v)
            (json_get_string "format" v)
            (json_get_string "pattern" v)
            (json_get_string "groupChar" v)
            (json_get_string "decimalChar" v))
  | _ -> None

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
      | Some dv -> csvw_decode_datatype dv
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
        ts_about_url    = json_get_string "aboutUrl" v;
        ts_property_url = json_get_string "propertyUrl" v;
        ts_value_url    = json_get_string "valueUrl" v;
      })
  | _ -> None

// ================================================================
// Table decode
// ================================================================

let csvw_decode_table (v:json_val) : option csvw_table =
  match v with
  | JObject _ ->
    let dialect =
      match json_get_field "dialect" v with
      | Some dv -> csvw_decode_dialect dv
      | None -> None in
    let schema_ok, schema =
      match json_get_field "tableSchema" v with
      | None -> true, None
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
      })
  | _ -> None

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
// Top level
// ================================================================

// Decodes an already-Parser.JSON-parsed metadata document. A "tables"
// array at the top level means a table group (decoded via
// csvw_decode_table_list); otherwise the whole document is decoded as
// a single table (csvw_decode_table). Returns None on any structural
// mismatch — an honest parse failure, never a silently-dropped field.
let csvw_decode_metadata (v:json_val) : option csvw_metadata =
  match json_get_array "tables" v with
  | Some items ->
    (match csvw_decode_table_list items with
     | Some ts -> Some (CSVW_TableGroup ts)
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
