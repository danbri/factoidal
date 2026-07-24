module CSVW.Validate

// Stage 9 of the CSVW program plan
// (docs/designissues/2026-07-05-csvw-program-plan.md): validation mode.
// The manifest-validation suite asks a yes/no question per test — does
// the (metadata + tabular data) pair CONFORM? — rather than comparing an
// output document. A PositiveValidationTest / WarningValidationTest
// conforms (warnings do not fail); a NegativeValidationTest MUST be
// caught as non-conforming.
//
// This module collects VALIDATION ERRORS. An empty error list means the
// document conforms. It works in two layers:
//   1. METADATA-STRUCTURAL checks over the raw metadata JSON tree
//      (tabular-metadata's own constraints the lenient decoder in
//      CSVW.Metadata deliberately tolerates for conversion): an `@id`
//      that is a blank node or non-string, an `@type` that does not
//      match the object's role, a Table with no `url`, a TableGroup
//      with no tables, a natural-language property keyed by an invalid
//      language tag.
//   2. DATA-LEVEL checks over the converted table (cell values that are
//      ill-formed for their declared datatype, a required column with an
//      empty cell, a duplicated primaryKey) — shared with the csv2rdf
//      cell machinery in CSVW.Conversion.
//
// IRON RULES: F* is the source of truth (rule #1); no --lax /
// --admit_smt_queries (rule #10); no "(" star / star ")" inside block
// comments (rule #12) — use //.

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Graph.Executable
open CSVW.Metadata
open CSVW.Conversion
open CSVW.Formats           // FO_Invalid/FO_Valid/FO_NoFormat, csvw_format_convert
open Parser.JSON

module Str = FStar.String
module L = FStar.List.Tot

// ================================================================
// Small helpers over the raw metadata JSON tree.
// ================================================================

let cv_starts_with (s pfx : string) : bool =
  Str.length s >= Str.length pfx && Str.sub s 0 (Str.length pfx) = pfx

let cv_is_object (v : json_val) : bool = match v with JObject _ -> true | _ -> false

// Replace (or add) a field in a JSON object.
let cv_set_field (k : string) (nv : json_val) (obj : json_val) : json_val =
  match obj with
  | JObject fs -> JObject ((k, nv) :: L.filter (fun (kv : (string & json_val)) -> fst kv <> k) fs)
  | _ -> obj

let cv_field (k : string) (v : json_val) : option json_val = json_get_field k v

let cv_has (k : string) (v : json_val) : bool = Some? (cv_field k v)

// ---- language-tag well-formedness (BCP47, the subset the suite uses)
// A primary language subtag is 2-8 ASCII letters (1-letter subtags are
// reserved / grandfathered and not used by any fixture). test109's
// "a-bad-language" fails on the 1-letter primary subtag.
let cv_is_alpha (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in (n >= 65 && n <= 90) || (n >= 97 && n <= 122)

let rec cv_all_alpha (cs : list FStar.Char.char) : Tot bool (decreases cs) =
  match cs with [] -> true | c :: tl -> cv_is_alpha c && cv_all_alpha tl

// First '-'-separated segment of a language tag.
let rec cv_take_to_dash (cs : list FStar.Char.char) : Tot (list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: tl -> if FStar.Char.int_of_char c = 45 (* '-' *) then [] else c :: cv_take_to_dash tl

let cv_lang_valid (tag : string) : bool =
  let prim = cv_take_to_dash (Str.list_of_string tag) in
  let n = L.length prim in
  n >= 2 && n <= 8 && cv_all_alpha prim

// ================================================================
// @id / @type role checks.
// ================================================================

// An `@id` member must not be a blank-node reference ("_:...")
// (test077-082, all "_:foo"). A NON-string @id (test102's integer) is a
// warning-level graceful degradation, not a validation error, so it is
// not flagged here.
let cv_check_id (role : string) (v : json_val) : list string =
  match cv_field "@id" v with
  | Some (JString s) -> if cv_starts_with s "_:" then [ role ^ " @id must not be a blank node" ] else []
  | _ -> []

// An `@type` member, when present, must equal the object's role class
// (test083-088). A missing @type is fine (it is inferred).
let cv_check_type (role : string) (v : json_val) : list string =
  match json_get_string "@type" v with
  | Some t -> if t = role then [] else [ "@type " ^ t ^ " invalid for a " ^ role ]
  | None -> []

// ================================================================
// titles natural-language check: a titles object keys its values by
// language tag, each of which must be well-formed (test109).
// ================================================================

let rec cv_check_lang_keys (fs : list (string & json_val)) : Tot (list string) (decreases fs) =
  match fs with
  | [] -> []
  | (k, _) :: tl ->
    let here = if cv_lang_valid k then [] else [ "invalid language tag: " ^ k ] in
    here @ cv_check_lang_keys tl

// A titles value must be a string, an array, or a language-keyed object;
// any other JSON type is a validation error (test111). A titles object's
// keys must be well-formed language tags (test109).
let cv_check_titles (v : json_val) : list string =
  match cv_field "titles" v with
  | None -> []
  | Some (JObject fs) -> cv_check_lang_keys fs
  | Some (JString _) -> []
  | Some (JArray _) -> []
  | Some _ -> [ "titles must be a string, array, or language object" ]

// ================================================================
// Per-object walks. The metadata's fixed nesting (group -> tables[] ->
// tableSchema -> columns[] / dialect) means a shallow, explicit walk
// suffices — no recursion depth to bound.
// ================================================================

// A `datatype` given as a string must name a built-in datatype
// (tabular-metadata 5.11.1) — a bare URL or unknown token is invalid
// (test308: "http://example.org/bad/datatype").
let cv_known_datatype (n : string) : bool =
  n = "anyAtomicType" || n = "anyURI" || n = "base64Binary" || n = "boolean"
  || n = "date" || n = "dateTime" || n = "dateTimeStamp" || n = "decimal"
  || n = "integer" || n = "long" || n = "int" || n = "short" || n = "byte"
  || n = "nonNegativeInteger" || n = "positiveInteger" || n = "unsignedLong"
  || n = "unsignedInt" || n = "unsignedShort" || n = "unsignedByte"
  || n = "nonPositiveInteger" || n = "negativeInteger" || n = "double"
  || n = "duration" || n = "dayTimeDuration" || n = "yearMonthDuration"
  || n = "float" || n = "gDay" || n = "gMonth" || n = "gMonthDay" || n = "gYear"
  || n = "gYearMonth" || n = "hexBinary" || n = "QName" || n = "string"
  || n = "normalizedString" || n = "token" || n = "language" || n = "Name"
  || n = "NMTOKEN" || n = "xml" || n = "html" || n = "json" || n = "time"
  // csvw aliases
  || n = "number" || n = "binary" || n = "datetime" || n = "any"

// NOTE: a datatype STRING that is not a built-in name is a WARNING
// (graceful degradation), not an error — test150 (non-builtin) and
// test238 (absolute URL) are WarningValidationTests — so it is NOT
// flagged here. cv_known_datatype is retained for potential future use.
let _cv_known_datatype_ref = cv_known_datatype

let cv_check_column (v : json_val) : list string =
  cv_check_id "Column" v @ cv_check_type "Column" v @ cv_check_titles v

let rec cv_check_columns (xs : list json_val) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | c :: tl -> cv_check_column c @ cv_check_columns tl

let cv_check_schema (v : json_val) : list string =
  let base = cv_check_id "Schema" v @ cv_check_type "Schema" v in
  // columns, when present, MUST be an array (test100: a single column
  // object is invalid).
  let cols = (match cv_field "columns" v with
              | Some (JArray xs) -> cv_check_columns xs
              | None -> []
              | Some _ -> [ "columns must be an array" ]) in
  base @ cols

let cv_check_dialect (v : json_val) : list string =
  match cv_field "dialect" v with
  | Some d -> cv_check_id "Dialect" d @ cv_check_type "Dialect" d
  | None -> []

// A Table object: needs a `url`, an optional valid @id/@type, and its
// schema/dialect are checked in turn.
let cv_check_table (v : json_val) : list string =
  let idt = cv_check_id "Table" v @ cv_check_type "Table" v in
  let url = if cv_has "url" v then [] else [ "Table is missing the required url property" ] in
  // tableSchema, when present, MUST be an object (inline schema) or a
  // string (schema reference); any other type is invalid (test107).
  let sch = (match cv_field "tableSchema" v with
             | None -> []
             | Some s -> (match s with
                          | JObject _ -> cv_check_schema s
                          | JString _ -> []
                          | _ -> [ "tableSchema must be an object or string" ])) in
  let dia = cv_check_dialect v in
  idt @ url @ sch @ dia

// A non-object element of the "tables" array is ignored (section 4,
// test094), not a structural error.
let rec cv_check_tables (xs : list json_val) : Tot (list string) (decreases xs) =
  match xs with
  | [] -> []
  | t :: tl -> (match t with JObject _ -> cv_check_table t | _ -> []) @ cv_check_tables tl

// ================================================================
// Top-level metadata validation. A document is either a TableGroup
// (has "tables") or a single Table.
// ================================================================

let csvw_validate_metadata_json (root : json_val) : list string =
  if not (cv_is_object root) then [ "metadata is not a JSON object" ]
  else match cv_field "tables" root with
       | Some (JArray ts) ->
         let g = cv_check_id "TableGroup" root @ cv_check_type "TableGroup" root in
         let empty = (match ts with [] -> [ "TableGroup has no tables" ] | _ -> []) in
         g @ empty @ cv_check_tables ts
       | Some _ -> [ "tables must be an array" ]
       | None ->
         // A single-table document: the root itself is the Table.
         cv_check_table root

// ================================================================
// Data-level checks over the converted tables (shared cell machinery).
// ================================================================

// Is a physical cell text a valid value for its column's datatype?
// Mirrors the `violate` computation inside csvw_cell_object: an empty /
// null cell is vacuously fine here (required-ness is a separate check).
let cv_cell_valid (spec : csvw_col_spec) (txt : string) : bool =
  let is_null = txt = "" || (match spec.cs_null with Some n -> txt = n | None -> false) in
  if is_null then true
  else
    let dt_str = csvw_datatype_iri spec.cs_datatype in
    if not (is_iri dt_str) then true
    else
      let base_name = csvw_dt_base_name_of spec.cs_datatype in
      let (fmt_str, pat, grp, dec) = csvw_dt_format_facets spec.cs_datatype in
      (match csvw_format_convert base_name fmt_str pat grp dec txt with
       | FO_Invalid -> false
       | FO_Valid canonical ->
         not (XSD.Datatypes.literal_ill_formed dt_str canonical)
         && csvw_value_satisfies base_name canonical spec.cs_datatype
       | FO_NoFormat ->
         not (XSD.Datatypes.literal_ill_formed dt_str txt)
         && csvw_value_satisfies base_name txt spec.cs_datatype)

// One physical column's cells across all data rows: report an error on
// each value that is ill-formed for its declared datatype.
let rec cv_check_cells (spec : csvw_col_spec) (cells : list string) : Tot (list string) (decreases cells) =
  match cells with
  | [] -> []
  | txt :: tl ->
    // A list-valued (separator) cell validates each split part against
    // the datatype (and its facets), not the whole raw cell (test228).
    let parts = (match spec.cs_separator with
                 | Some sep -> csvw_split_list_cell sep txt
                 | None -> [ txt ]) in
    let here = L.collect
      (fun (part : string) ->
         if cv_cell_valid spec part then [] else [ "invalid value in column " ^ spec.cs_name ^ ": " ^ part ])
      parts in
    here @ cv_check_cells spec tl

// Column-major cell lists for a table's data rows, paired with each
// physical column's spec.
let cv_transpose (specs : list csvw_col_spec) (rows : list (list string)) : list (csvw_col_spec & list string) =
  let n = L.length specs in
  let indexed = csvw_index_from 0 specs in
  L.map (fun (p : (nat & csvw_col_spec)) ->
           let (i, spec) = p in
           (spec, L.map (fun (r : list string) -> match L.nth r i with Some c -> c | None -> "") rows))
        indexed

let rec cv_has_dup (seen : list string) (xs : list string) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | x :: tl -> L.mem x seen || cv_has_dup (x :: seen) tl

// Single-column primaryKey uniqueness (tabular-data-model 6.4.9): more
// than one row with the same primary-key value is an error (test232).
let cv_check_primary_key (cols : list (csvw_col_spec & list string)) (pk : option string) : list string =
  match pk with
  | None -> []
  | Some name ->
    (match L.find (fun (p : (csvw_col_spec & list string)) -> (fst p).cs_name = name) cols with
     | Some (_, vals) -> if cv_has_dup [] vals then [ "duplicate primaryKey value in column " ^ name ] else []
     | None -> [])

let cv_col_is_virtual (c : csvw_column) : bool = match c.col_virtual with Some b -> b | None -> false
let cv_col_required (c : csvw_column) : bool = match c.col_required with Some b -> b | None -> false

// A required column MUST have a non-null value in every data row
// (tabular-data-model 6.4.9): an empty cell, or one matching the column's
// null value, is an error (test125/126).
let rec cv_required_cells (spec : csvw_col_spec) (vals : list string) : Tot (list string) (decreases vals) =
  match vals with
  | [] -> []
  | v :: tl ->
    let is_null = v = "" || (match spec.cs_null with Some n -> v = n | None -> false) in
    let here = if is_null then [ "required column " ^ spec.cs_name ^ " has a null/empty cell" ] else [] in
    here @ cv_required_cells spec tl

let rec cv_check_required
    (cols_meta : list csvw_column) (cols_data : list (csvw_col_spec & list string))
  : Tot (list string) (decreases cols_meta) =
  match cols_meta, cols_data with
  | c :: mt, (spec, vals) :: dt ->
    let here = if cv_col_required c then cv_required_cells spec vals else [] in
    here @ cv_check_required mt dt
  | _, _ -> []

// BCP47 language match (the subset the suite needs): equal, "und"
// matches anything, or one is the other truncated to a subtag boundary
// (approximated as a prefix). test148: title language "en" vs the header
// default "de" does NOT match.
let cv_lang_match (a b : string) : bool =
  a = b || a = "und" || b = "und"
  || (let la = Str.length a in let lb = Str.length b in
      if la <= lb then Str.sub b 0 la = a else Str.sub a 0 lb = b)

// Title compatibility (tabular-data-model 5.4.2): a declared column that
// HAS titles must have a case-sensitive, LANGUAGE-matching intersection
// with the CSV header cell (which carries the default language) at the
// same index — test147 (case: "gid" vs "GID"), test148 (language: "en"
// title vs "de" default). A column with only a name must have that name
// equal the header title's encoded name (test124). `dl` is the effective
// default language.
let rec cv_title_compat (dl : string) (cols_meta : list csvw_column) (header : list string)
  : Tot (list string) (decreases cols_meta) =
  match cols_meta, header with
  | c :: mt, h :: ht ->
    // The default dialect trims header cells, so compare trimmed forms
    // (test032's header " Start Date" vs title "Start Date").
    let ht0 = csvw_trim h in
    let here = (match c.col_titles_l with
                | _ :: _ ->
                  // A titled column: some title must match the header text
                  // AND have a language matching the header default.
                  if L.existsb (fun (tl : (string & option string)) ->
                                  let (t, lo) = tl in
                                  csvw_trim t = ht0
                                  && cv_lang_match (match lo with Some l -> l | None -> dl) dl)
                               c.col_titles_l
                  then []
                  else [ "column title incompatible with CSV header: " ^ ht0 ]
                | [] ->
                  // A column with a name but no titles must have that name
                  // equal the name the header title encodes to (test124:
                  // metadata name "GID1" vs header "GID" -> name "GID").
                  (match c.col_name with
                   | Some n -> if n = csvw_encode_name ht0 then []
                              else [ "column name incompatible with CSV header: " ^ ht0 ]
                   | None -> [])) in
    here @ cv_title_compat dl mt ht
  | _, _ -> []

// Multi-column primaryKey names for a table, read from the RAW metadata
// JSON (the decoder only captures the single-string form): a "primaryKey"
// that is a JArray of strings. Kept in F* (rule #4) rather than the OCaml
// runner.
let cv_pk_names_of_raw (tblj : json_val) : list string =
  match cv_field "tableSchema" tblj with
  | Some ts ->
    (match cv_field "primaryKey" ts with
     | Some (JArray xs) -> L.choose (fun (x : json_val) -> match x with JString s -> Some s | _ -> None) xs
     | _ -> [])
  | None -> []

// Locate the raw JSON object for a table by its (unresolved) url.
let cv_find_raw_table (root : json_val) (url : option string) : option json_val =
  match cv_field "tables" root with
  | Some (JArray ts) ->
    (match L.find (fun (t : json_val) ->
                     match cv_field "url" t, url with
                     | Some (JString u), Some u2 -> u = u2
                     | _, _ -> false) ts with
     | Some t -> Some (t <: json_val)
     | None -> None)
  | _ -> Some root

// Join a list of equal-length column value-lists into one composite
// string per row (for multi-column primaryKey uniqueness). `fuel` bounds
// the row count.
let rec cv_zip_join (fuel : nat) (cols : list (list string)) : Tot (list string) (decreases fuel) =
  if fuel = 0 then []
  else if L.existsb Nil? cols then []
  else
    let heads = L.map (fun (c : list string) -> match c with h :: _ -> h | [] -> "") cols in
    let tails = L.map (fun (c : list string) -> match c with _ :: t -> t | [] -> []) cols in
    Str.concat "~|~" heads :: cv_zip_join (fuel - 1) tails

// Composite (multi-column) primaryKey uniqueness (test234). Single-column
// PK is handled by cv_check_primary_key; this covers >= 2 columns.
let cv_check_composite_pk (cols : list (csvw_col_spec & list string)) (pk_names : list string) : list string =
  if L.length pk_names < 2 then []
  else
    let pk_val_lists = L.choose
      (fun (name : string) ->
         match L.find (fun (p : (csvw_col_spec & list string)) -> (fst p).cs_name = name) cols with
         | Some (_, vals) -> Some vals
         | None -> None)
      pk_names in
    if L.length pk_val_lists <> L.length pk_names then []
    else
      let nrows = (match pk_val_lists with c :: _ -> L.length c | [] -> 0) in
      if cv_has_dup [] (cv_zip_join nrows pk_val_lists)
      then [ "duplicate multi-column primaryKey" ] else []

let cv_check_data_table
    (root : json_val) (default_lang : string) (grp_inherited : csvw_inherited_props) (base_iri : string)
    (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : list string =
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.tbl_dialect in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let header_cells =
    if csvw_header_row_count dia > 0 then (match after_skip_rows with h :: _ -> h | [] -> [])
    else (match tbl.tbl_table_schema with
          | Some _ -> []
          | None -> (match data_rows with r :: _ -> L.map (fun (_:string) -> "") r | [] -> [])) in
  let col_specs = csvw_build_col_specs grp_inherited tbl.tbl_inherited tbl.tbl_table_schema header_cells in
  let phys_specs = L.filter (fun (s : csvw_col_spec) -> not s.cs_virtual) col_specs in
  let cols = cv_transpose phys_specs data_rows in
  let cell_errs = L.collect (fun (p : (csvw_col_spec & list string)) -> cv_check_cells (fst p) (snd p)) cols in
  let pk = (match tbl.tbl_table_schema with Some ts -> ts.ts_primary_key | None -> None) in
  // Multi-column primaryKey (from the raw JSON, since the decoder keeps
  // only the single-string form).
  let pk_names = (match cv_find_raw_table root tbl.tbl_url with Some tj -> cv_pk_names_of_raw tj | None -> []) in
  let composite_pk = cv_check_composite_pk cols pk_names in
  // Schema / CSV compatibility (tabular-data-model 5.4.2 / test278): an
  // explicit schema's non-virtual column count MUST equal the data width.
  let declared = (match tbl.tbl_table_schema with Some ts -> ts.ts_columns | None -> []) in
  let declared_nonvirt = L.filter (fun (c : csvw_column) -> not (cv_col_is_virtual c)) declared in
  let actual_width =
    if Cons? header_cells then L.length header_cells
    else (match data_rows with r :: _ -> L.length r | [] -> 0) in
  let compat =
    if Cons? declared_nonvirt && actual_width > 0 && L.length declared_nonvirt <> actual_width
    then [ "schema declares " ^ string_of_int (L.length declared_nonvirt)
           ^ " non-virtual columns but the data has " ^ string_of_int actual_width ]
    else [] in
  // Required-column checks align the non-virtual metadata columns with
  // the (non-virtual) per-column data lists — only meaningful when the
  // counts already match (compat empty).
  let req = if compat = [] then cv_check_required declared_nonvirt cols else [] in
  // Title compatibility only when a header row is present and the column
  // counts already match (so index alignment is sound).
  let title_compat =
    if compat = [] && Cons? header_cells then
      // The header cells carry the table's effective (inherited) language;
      // titles must match on it (test148: title "en" vs table lang "de").
      let table_lang =
        (match tbl.tbl_inherited.inh_lang with
         | Some l -> l
         | None -> (match grp_inherited.inh_lang with Some l -> l | None -> default_lang)) in
      cv_title_compat table_lang declared_nonvirt header_cells
    else [] in
  cell_errs @ cv_check_primary_key cols pk @ composite_pk @ compat @ req @ title_compat

// ================================================================
// Foreign-key referential integrity (cross-table, test257/258). Read
// from the raw metadata JSON (the decoder does not capture foreignKeys).
// ================================================================

// A columnReference is a single name or an array of names.
let cv_col_ref_names (v : option json_val) : list string =
  match v with
  | Some (JString s) -> [ s ]
  | Some (JArray xs) -> L.choose (fun (x : json_val) -> match x with JString s -> Some s | _ -> None) xs
  | _ -> []

// Inline referenced table schemas (tableSchema given as a URL string)
// into the raw metadata JSON, using a runner-supplied (url -> schema
// JSON) map, so downstream FK reading (test034/035) sees the foreignKeys
// that live in the external schema files. The runner does the file I/O
// (rule #11); this only substitutes into the tree.
let rec cv_assoc_j (k : string) (xs : list (string & json_val)) : option json_val =
  match xs with
  | [] -> None
  | (k2, v) :: tl -> if k2 = k then Some v else cv_assoc_j k tl

let cv_inline_one_table (schemas : list (string & json_val)) (t : json_val) : json_val =
  match cv_field "tableSchema" t with
  | Some (JString url) -> (match cv_assoc_j url schemas with
                           | Some sj -> cv_set_field "tableSchema" sj t
                           | None -> t)
  | _ -> t

let cv_inline_schema_refs (root : json_val) (schemas : list (string & json_val)) : json_val =
  match cv_field "tables" root with
  | Some (JArray ts) -> cv_set_field "tables" (JArray (L.map (cv_inline_one_table schemas) ts)) root
  | _ -> cv_inline_one_table schemas root

// Last path segment of a slash-separated URL.
let cv_basename (s : string) : string =
  match L.rev (Str.split ['/'] s) with h :: _ -> h | [] -> s

let rec cv_assoc_s (k : string) (xs : list (string & string)) : option string =
  match xs with
  | [] -> None
  | (k2, v) :: tl -> if k2 = k then Some v else cv_assoc_s k tl

// (local columns, referenced resource url, referenced columns) per
// foreignKey of a table's raw JSON. A reference is either by `resource`
// (a table url, test257/258) or by `schemaReference` (a schema url whose
// table is found via `schemaref_map`: schema basename -> table url,
// test034/035).
let cv_read_fks (schemaref_map : list (string & string)) (tblj : json_val)
  : list (list string & string & list string) =
  match cv_field "tableSchema" tblj with
  | Some ts ->
    (match cv_field "foreignKeys" ts with
     | Some (JArray fks) ->
       L.choose
         (fun (fk : json_val) ->
            let local = cv_col_ref_names (cv_field "columnReference" fk) in
            match cv_field "reference" fk with
            | Some refj ->
              let refcols = cv_col_ref_names (cv_field "columnReference" refj) in
              let res =
                (match json_get_string "resource" refj with
                 | Some r -> Some r
                 | None -> (match json_get_string "schemaReference" refj with
                            | Some sr -> cv_assoc_s (cv_basename sr) schemaref_map
                            | None -> None)) in
              (match res with Some r -> Some (local, r, refcols) | None -> None)
            | None -> None)
         fks
     | _ -> [])
  | None -> []

// A table's non-virtual columns as (spec, values) — same construction as
// cv_check_data_table, reused for both sides of a foreign key.
let cv_table_cols
    (grp_inherited : csvw_inherited_props) (base_iri : string)
    (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : list (csvw_col_spec & list string) =
  let dia = tbl.tbl_dialect in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let header_cells =
    if csvw_header_row_count dia > 0 then (match after_skip_rows with h :: _ -> h | [] -> [])
    else (match tbl.tbl_table_schema with
          | Some _ -> []
          | None -> (match data_rows with r :: _ -> L.map (fun (_:string) -> "") r | [] -> [])) in
  let col_specs = csvw_build_col_specs grp_inherited tbl.tbl_inherited tbl.tbl_table_schema header_cells in
  let phys_specs = L.filter (fun (s : csvw_col_spec) -> not s.cs_virtual) col_specs in
  cv_transpose phys_specs data_rows

// Composite value per row over the named columns.
let cv_composite_of (cols : list (csvw_col_spec & list string)) (names : list string) : list string =
  let vlists = L.choose
    (fun (name : string) ->
       match L.find (fun (p : (csvw_col_spec & list string)) -> (fst p).cs_name = name) cols with
       | Some (_, vals) -> Some vals
       | None -> None)
    names in
  if L.length vlists = L.length names && Cons? vlists
  then cv_zip_join (match vlists with c :: _ -> L.length c | [] -> 0) vlists
  else []

let cv_find_table_by_resource
    (tables_with_rows : list (csvw_table & string & list (list string))) (resource : string)
  : option (csvw_table & string & list (list string)) =
  match L.find (fun (t : (csvw_table & string & list (list string))) ->
                  let (tbl, _, _) = t in
                  match tbl.tbl_url with Some u -> u = resource | None -> false)
               tables_with_rows with
  | Some t -> Some (t <: (csvw_table & string & list (list string)))
  | None -> None

let cv_check_table_fks
    (root : json_val) (schemaref_map : list (string & string))
    (grp_inherited : csvw_inherited_props) (base_iri : string)
    (all_tables : list (csvw_table & string & list (list string)))
    (tbl : csvw_table) (fallback_url : string) (rows : list (list string))
  : list string =
  match cv_find_raw_table root tbl.tbl_url with
  | None -> []
  | Some tj ->
    let fks = cv_read_fks schemaref_map tj in
    let local_cols = cv_table_cols grp_inherited base_iri fallback_url tbl rows in
    L.collect
      (fun (fk : (list string & string & list string)) ->
         let (local_names, resource, ref_names) = fk in
         match cv_find_table_by_resource all_tables resource with
         | None -> []
         | Some (ttbl, tfallback, trows) ->
           let target_cols = cv_table_cols grp_inherited base_iri tfallback ttbl trows in
           let local_vals = cv_composite_of local_cols local_names in
           let ref_vals = cv_composite_of target_cols ref_names in
           L.collect
             (fun (lv : string) ->
                if lv = "" then []
                else
                  let n = L.length (L.filter (fun (v : string) -> v = lv) ref_vals) in
                  if n = 0 then [ "foreign key value has no referenced row: " ^ lv ]
                  else if n > 1 then [ "foreign key value references multiple rows: " ^ lv ]
                  else [])
             local_vals)
      fks

let cv_check_data
    (root : json_val) (schemaref_map : list (string & string)) (default_lang : string)
    (grp_inherited : csvw_inherited_props) (base_iri : string)
    (tables_with_rows : list (csvw_table & string & list (list string)))
  : list string =
  let per_table =
    L.collect (fun (t : (csvw_table & string & list (list string))) ->
                 let (tbl, fallback_url, rows) = t in
                 if csvw_table_suppressed tbl then []
                 else cv_check_data_table root default_lang grp_inherited base_iri fallback_url tbl rows)
              tables_with_rows in
  let fk_errs =
    L.collect (fun (t : (csvw_table & string & list (list string))) ->
                 let (tbl, fallback_url, rows) = t in
                 if csvw_table_suppressed tbl then []
                 else cv_check_table_fks root schemaref_map grp_inherited base_iri tables_with_rows tbl fallback_url rows)
              tables_with_rows in
  per_table @ fk_errs
