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
//   - Inherited properties (Stage 2, not yet built in CSVW.Metadata):
//     this module approximates ONE level of aboutUrl/propertyUrl/
//     valueUrl inheritance itself (column overrides table-schema),
//     not the full table-group -> table -> schema -> column chain.
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
open SPARQL11.Algebra       // string_encode_uri (default propertyUrl's column-name encoding)

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

let csvw_base_name_to_iri (n : string) : string =
  if n = "html" then "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML"
  else if n = "xml" then "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
  else if n = "json" then csvw_ns ^ "JSON"
  else "http://www.w3.org/2001/XMLSchema#" ^ n

let csvw_datatype_iri (dt : option csvw_datatype) : string =
  match dt with
  | None -> xsd_string
  | Some (CSVW_DT_Named n) -> csvw_base_name_to_iri n
  | Some (CSVW_DT_Object base_opt _ _ _ _) ->
    (match base_opt with Some n -> csvw_base_name_to_iri n | None -> xsd_string)

// Build a literal term, guarding the dynamically-computed datatype IRI
// with `is_iri` the same way RML.Eval.fst's build_literal_opt does —
// csvw_datatype_iri's output always contains a colon in practice (every
// branch prepends a fixed IRI-scheme prefix), but the guard keeps the
// F* typechecker honest about wf_iri's refinement rather than assuming it.
let csvw_build_literal (lex : string) (dt : string) : option rdf_term =
  if is_iri dt then
    let l : literal = { lexical_form = lex; datatype = dt; lang_tag = None } in
    if literal_wf l then Some (T_Literal l) else None
  else None

// ================================================================
// Column specs: CSVW.Metadata's csvw_column merged with a ONE-LEVEL
// table-schema fallback for aboutUrl/propertyUrl/valueUrl (see the
// banner's "Scope / known gaps" note on inheritance), or synthesized
// straight from a header row when no schema was given at all.
// ================================================================

noeq type csvw_col_spec = {
  cs_name         : string;
  cs_virtual      : bool;
  cs_suppress     : bool;
  cs_datatype     : option csvw_datatype;
  cs_about_url    : option string;
  cs_property_url : option string;
  cs_value_url    : option string;
}

let csvw_opt_bool (o : option bool) : bool = match o with Some b -> b | None -> false

let csvw_col_spec_of_column (ts : csvw_table_schema) (c : csvw_column) : csvw_col_spec = {
  cs_name = (match c.col_name with
             | Some n -> n
             | None -> (match c.col_titles with t :: _ -> t | [] -> ""));
  cs_virtual = csvw_opt_bool c.col_virtual;
  cs_suppress = csvw_opt_bool c.col_suppress_output;
  cs_datatype = c.col_datatype;
  cs_about_url = (match c.col_about_url with Some a -> Some a | None -> ts.ts_about_url);
  cs_property_url = (match c.col_property_url with Some p -> Some p | None -> ts.ts_property_url);
  cs_value_url = (match c.col_value_url with Some v -> Some v | None -> ts.ts_value_url);
}

// Positional default column name when neither a schema nor a header
// cell gives one — csv2rdf's own "_col.N" fallback (1-based).
// `List.Tot.mapi`'s index callback type is plain `int` (FStar.List.Tot.Base),
// not `nat` — take `int` here to match, even though the actual values
// mapi ever supplies are always >= 0.
let csvw_positional_name (i : int) : string = "_col." ^ string_of_int (i + 1)

// Schema absent entirely, or present but with an empty column list
// (both mean "infer purely from the header row").
let csvw_col_specs_from_header (header_cells : list string) : list csvw_col_spec =
  List.Tot.mapi
    (fun i (h : string) -> {
       cs_name = (if h = "" then csvw_positional_name i else h);
       cs_virtual = false; cs_suppress = false; cs_datatype = None;
       cs_about_url = None; cs_property_url = None; cs_value_url = None;
     })
    header_cells

let csvw_build_col_specs (ts_opt : option csvw_table_schema) (header_cells : list string)
  : list csvw_col_spec =
  match ts_opt with
  | Some ts ->
    if Cons? ts.ts_columns then List.Tot.map (csvw_col_spec_of_column ts) ts.ts_columns
    else csvw_col_specs_from_header header_cells
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
  match spec.cs_value_url with
  | Some tmpl ->
    let raw = csvw_expand_template lookup tmpl in
    let resolved = resolve_iri_v2 table_url_resolved raw in
    if is_iri resolved then Some (T_IRI resolved) else None
  | None ->
    (match cell_text with
     | None -> None                      // virtual column with no valueUrl: nothing to emit
     | Some txt ->
       if txt = "" then None             // default null value ("") -> no cell triple
       else csvw_build_literal txt (csvw_datatype_iri spec.cs_datatype))

let csvw_process_cell
    (table_url_resolved : string)
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
      | Some tmpl -> resolve_iri_v2 table_url_resolved (csvw_expand_template cur_lookup tmpl)
      | None -> table_url_resolved ^ "#" ^ string_encode_uri spec.cs_name
    in
    let pred_valid : option wf_iri = if is_iri raw then Some raw else None in
    match pred_valid with
    | None -> (subj, [])
    | Some pred_str ->
      (match csvw_cell_object table_url_resolved spec cell_text cur_lookup with
       | None -> (subj, [])
       | Some obj -> (subj, [ { s = subj; p = pred_str; o = obj } ]))

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
  let default_subject =
    S_BNode ("csvwrow_" ^ string_encode_uri table_url_resolved ^ "_" ^ string_of_int source_row_num) in
  List.Tot.map
    (fun (p : (csvw_col_spec & string)) ->
       csvw_process_cell table_url_resolved lookup default_subject (fst p) (Some (snd p)))
    phys_pairs
  @ List.Tot.map
      (fun (s : csvw_col_spec) -> csvw_process_cell table_url_resolved lookup default_subject s None)
      virt_specs

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
    (base_iri : string) (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : list triple =
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.tbl_dialect in
  let skip_n = csvw_skip_rows_count dia + csvw_header_row_count dia in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let header_cells =
    if csvw_header_row_count dia > 0 then (match after_skip_rows with h :: _ -> h | [] -> [])
    else [] in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let col_specs = csvw_build_col_specs tbl.tbl_table_schema header_cells in
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

let csvw_row_triples_standard
    (table_url_resolved : string)
    (col_specs : list csvw_col_spec) (row_num : nat) (source_row_num : nat) (cells : list string)
  : (subject & list triple) =
  let per_col = csvw_row_cell_results table_url_resolved col_specs row_num source_row_num cells in
  let row_node = S_BNode ("csvwR_" ^ string_encode_uri table_url_resolved ^ "_" ^ string_of_int source_row_num) in
  let row_url = csvw_row_url table_url_resolved source_row_num in
  let row_meta =
    [ { s = row_node; p = rdf_type; o = T_IRI csvw_Row };
      { s = row_node; p = csvw_rownum;
        o = T_Literal ({ lexical_form = string_of_int row_num; datatype = xsd_integer; lang_tag = None }) } ]
    @ (if is_iri row_url then [ { s = row_node; p = csvw_url_pred; o = T_IRI row_url } ] else []) in
  let describes =
    List.Tot.concatMap
      (fun (r : (subject & list triple)) ->
         let (subj, ts) = r in
         if Nil? ts then [] else [ { s = row_node; p = csvw_describes; o = csvw_term_of_subject subj } ])
      per_col in
  let cell_triples = List.Tot.concatMap snd per_col in
  (row_node, row_meta @ describes @ cell_triples)

let csvw_convert_table_standard
    (base_iri : string) (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : (subject & list triple) =
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.tbl_dialect in
  let skip_n = csvw_skip_rows_count dia + csvw_header_row_count dia in
  let after_skip_rows = csvw_drop (csvw_skip_rows_count dia) all_rows in
  let header_cells =
    if csvw_header_row_count dia > 0 then (match after_skip_rows with h :: _ -> h | [] -> [])
    else [] in
  let data_rows = csvw_drop (csvw_header_row_count dia) after_skip_rows in
  let col_specs = csvw_build_col_specs tbl.tbl_table_schema header_cells in
  let indexed = csvw_index_from 0 data_rows in
  let row_results =
    List.Tot.map
      (fun (p : (nat & list string)) ->
         let (i, cells) = p in
         csvw_row_triples_standard table_url_resolved col_specs (i + 1) (skip_n + i + 1) cells)
      indexed in
  let t_node = S_BNode ("csvwT_" ^ string_encode_uri table_url_resolved) in
  let row_links =
    List.Tot.concatMap
      (fun (r : (subject & list triple)) -> [ { s = t_node; p = csvw_row_pred; o = csvw_term_of_subject (fst r) } ])
      row_results in
  let row_all = List.Tot.concatMap snd row_results in
  let t_meta =
    [ { s = t_node; p = rdf_type; o = T_IRI csvw_Table } ]
    @ (if is_iri table_url_resolved then [ { s = t_node; p = csvw_url_pred; o = T_IRI table_url_resolved } ] else []) in
  (t_node, t_meta @ row_links @ row_all)

// ================================================================
// Whole-document entry points. `tables_with_rows` pairs each table in
// document order with its already-tokenized CSV rows (the OCaml
// runner reads + RML.Sources.csv_parse_rows's each table's own CSV
// file — I/O only, per rule #11) and the fallback URL to use when
// that particular table's own metadata carries no `url` annotation
// (normally the CSV file the test's mf:action names directly).
// ================================================================

let csvw_convert_document_minimal
    (base_iri : string) (tables_with_rows : list (csvw_table & string & list (list string)))
  : list triple =
  List.Tot.concatMap
    (fun (t : (csvw_table & string & list (list string))) ->
       let (tbl, fallback_url, rows) = t in
       csvw_convert_table_minimal base_iri fallback_url tbl rows)
    tables_with_rows

let csvw_group_node : subject = S_BNode "csvwG"

let csvw_convert_document_standard
    (base_iri : string) (tables_with_rows : list (csvw_table & string & list (list string)))
  : list triple =
  let table_results =
    List.Tot.map
      (fun (t : (csvw_table & string & list (list string))) ->
         let (tbl, fallback_url, rows) = t in
         csvw_convert_table_standard base_iri fallback_url tbl rows)
      tables_with_rows in
  let g_meta = [ { s = csvw_group_node; p = rdf_type; o = T_IRI csvw_TableGroup } ] in
  let table_links =
    List.Tot.concatMap
      (fun (r : (subject & list triple)) -> [ { s = csvw_group_node; p = csvw_table_pred; o = csvw_term_of_subject (fst r) } ])
      table_results in
  let table_all = List.Tot.concatMap snd table_results in
  g_meta @ table_links @ table_all

// Convenience: a synthetic "no metadata document at all" table — the
// mf:action-is-a-bare-CSV-file case (schema inferred purely from the
// CSV's own header row, no dialect overrides). Kept here (not in
// CSVW.Metadata) since it's a CONVERSION-layer default, not a decoded
// value.
let csvw_no_metadata_table : csvw_table = {
  tbl_url = None;
  tbl_dialect = None;
  tbl_table_schema = None;
}
