module CSVW.Json

// Stage 8 of the CSVW program plan
// (docs/designissues/2026-07-05-csvw-program-plan.md): csv2json. Shares
// the annotated-table machinery already built for csv2rdf
// (CSVW.Conversion) — cell-value computation, datatype/format/null
// handling, aboutUrl/propertyUrl/valueUrl templates, list-valued
// (separator) cells — and re-serializes it as a JSON document per the
// "Generating JSON from Tabular Data on the Web" Recommendation
// (w3.org/TR/csv2json, vendored at third_party/testing/csvw/csv2json/
// index.html, quoted inline below rather than guessed).
//
// The JSON output differs from the RDF output in three ways, all handled
// here on top of CSVW.Conversion's shared per-cell value:
//   1. VALUE TYPE. A cell value's JSON primitive type is fixed by the
//      base annotation of its (effective) datatype: the numeric xsd
//      families -> JSON number, boolean -> JSON boolean, everything else
//      (strings, dates, gYear, anyURI, html, json, ...) -> JSON string
//      (csv2json section "Interpreting datatypes"). An ill-formed value
//      that CSVW.Conversion already demoted to xsd:string is therefore a
//      JSON string, exactly as the RDF path demotes it to a plain
//      literal.
//   2. PROPERTY KEY. If propertyUrl is set the key is that URL COMPACTED
//      (schema:name, not http://schema.org/name) per URL Compaction in
//      tabular-metadata; otherwise the key is the URI-decoded column
//      name.
//   3. NESTING. Within one row, a cell whose valueUrl matches another
//      cell's aboutUrl (and that value URL occurs only once in the row)
//      nests the referenced subject's object inside the referencing
//      property, replacing the string value (csv2json "Generating Nested
//      Objects" / the nesting algorithm). Cross-row references stay
//      strings (the URL-list is per-row).
//
// Standard mode wraps rows in {tables:[{url, row:[{url, rownum,
// describes:[...]}]}]}; minimal mode is the flat array of all root
// objects. Both are needed by the manifest-json suite (the same 7
// minimal-mode fixtures csv2rdf flags — test027/029/031/033/035/037 —
// carry minimal:true here too).
//
// IRON RULES: F* is the source of truth (rule #1); no --lax /
// --admit_smt_queries (rule #10); no "(" star / star ")" inside block
// comments (rule #12) — use //.

open FStar.Mul             // integer * (else * is the tuple-type operator)
open FStar.String
open FStar.List.Tot
open RDF.Term               // subject, subject_eq, S_IRI/S_BNode
open RDF.Graph.Executable   // triple/subject/rdf_term/literal, xsd_string
open RDF.IRI                // resolve_iri_v2, is_iri
open CSVW.Metadata
open CSVW.URITemplate
open CSVW.Conversion        // the shared csv2rdf machinery
open Parser.JSON            // json_val

module Str = FStar.String
module L = FStar.List.Tot

// ================================================================
// Small string helpers (local — kept out of CSVW.Conversion so its big
// .checked file is untouched by this stage).
// ================================================================

let cj_starts_with (s pfx : string) : bool =
  Str.length s >= Str.length pfx && Str.sub s 0 (Str.length pfx) = pfx

// ================================================================
// Percent-decoding for the default (propertyUrl-less) key, which is the
// URI-decoded column name (csv2json: "URI decoding is necessary as name
// may have been encoded if it was taken from a supplied title"). Mirrors
// SPARQL.Protocol.url_decode without pulling that whole module in.
// ================================================================

let cj_is_hex (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  (n >= 48 && n <= 57) || (n >= 65 && n <= 70) || (n >= 97 && n <= 102)

let cj_hexv (c : FStar.Char.char) : nat =
  let n = FStar.Char.int_of_char c in
  if n >= 48 && n <= 57 then n - 48
  else if n >= 65 && n <= 70 then n - 55
  else if n >= 97 && n <= 102 then n - 87
  else 0

#push-options "--z3rlimit 60"
let rec cj_url_decode_chars (cs : list FStar.Char.char)
  : Tot (list FStar.Char.char) (decreases (L.length cs)) =
  match cs with
  | [] -> []
  | c :: rest ->
    if FStar.Char.int_of_char c = 37 (* percent *) then
      (match rest with
       | h1 :: h2 :: rest' ->
         if cj_is_hex h1 && cj_is_hex h2 then
           let v : nat = cj_hexv h1 * 16 + cj_hexv h2 in
           FStar.Char.char_of_int v :: cj_url_decode_chars rest'
         else c :: cj_url_decode_chars rest
       | _ -> c :: cj_url_decode_chars rest)
    else c :: cj_url_decode_chars rest
#pop-options

let cj_url_decode (s : string) : string =
  Str.string_of_list (cj_url_decode_chars (Str.list_of_string s))

// ================================================================
// URL compaction (csv2json property keys / @type value URLs). Inverse of
// CSVW.Conversion.csvw_curie_ns over the same CSVW-context prefix subset
// the corpus uses, plus csvw:. First namespace that is a proper prefix of
// the URL wins.
// ================================================================

let cj_prefixes : list (string & string) =
  [ ("csvw", "http://www.w3.org/ns/csvw#");
    ("rdf",  "http://www.w3.org/1999/02/22-rdf-syntax-ns#");
    ("rdfs", "http://www.w3.org/2000/01/rdf-schema#");
    ("xsd",  "http://www.w3.org/2001/XMLSchema#");
    ("dcat", "http://www.w3.org/ns/dcat#");
    ("dc",   "http://purl.org/dc/terms/");
    ("dc11", "http://purl.org/dc/elements/1.1/");
    ("schema", "http://schema.org/");
    ("foaf", "http://xmlns.com/foaf/0.1/");
    ("skos", "http://www.w3.org/2004/02/skos/core#");
    ("owl",  "http://www.w3.org/2002/07/owl#");
    ("org",  "http://www.w3.org/ns/org#");
    ("oa",   "http://www.w3.org/ns/oa#");
    ("prov", "http://www.w3.org/ns/prov#");
    ("as",   "https://www.w3.org/ns/activitystreams#") ]

let rec cj_compact_try (u : string) (ps : list (string & string))
  : Tot string (decreases ps) =
  match ps with
  | [] -> u
  | (pfx, ns) :: tl ->
    if cj_starts_with u ns && Str.length u > Str.length ns
    then pfx ^ ":" ^ Str.sub u (Str.length ns) (Str.length u - Str.length ns)
    else cj_compact_try u tl

let cj_compact_url (u : string) : string = cj_compact_try u cj_prefixes

// ================================================================
// Cell VALUE -> json_val (csv2json "Interpreting datatypes"). The
// effective datatype IRI on the produced literal (CSVW.Conversion has
// already demoted an ill-formed value to xsd:string) fixes the JSON
// primitive type.
// ================================================================

let cj_xsd_ns : string = "http://www.w3.org/2001/XMLSchema#"

let cj_dt_local (dt : string) : string =
  if cj_starts_with dt cj_xsd_ns
  then Str.sub dt (Str.length cj_xsd_ns) (Str.length dt - Str.length cj_xsd_ns)
  else dt

let cj_is_numeric_dt (dt : string) : bool =
  let n = cj_dt_local dt in
  n = "decimal" || n = "integer" || n = "long" || n = "int" || n = "short"
  || n = "byte" || n = "nonNegativeInteger" || n = "positiveInteger"
  || n = "unsignedLong" || n = "unsignedInt" || n = "unsignedShort"
  || n = "unsignedByte" || n = "nonPositiveInteger" || n = "negativeInteger"
  || n = "double" || n = "float"

let cj_is_boolean_dt (dt : string) : bool = cj_dt_local dt = "boolean"

// A leading '+' is not part of a JSON number lexeme (RFC 8259); a
// number-format pattern may emit one (test283's "+0" sign pattern), so
// strip it before treating the lexical as a JSON number.
let cj_strip_plus (s : string) : string =
  if Str.length s >= 1 && Str.sub s 0 1 = "+" then Str.sub s 1 (Str.length s - 1) else s

// xsd:double / xsd:float special values have no JSON number form, so the
// csv2json output expresses them as strings (test155: "NaN"/"INF"/"-INF").
let cj_is_special_num (s : string) : bool = s = "NaN" || s = "INF" || s = "-INF"

let cj_json_of_term (t : rdf_term) : json_val =
  match t with
  | T_IRI i -> JString i
  | T_BNode b -> JString b
  | T_Literal l ->
    if cj_is_numeric_dt l.datatype then
      (if cj_is_special_num l.lexical_form then JString l.lexical_form
       else JNumber (cj_strip_plus l.lexical_form))
    else if cj_is_boolean_dt l.datatype then JBool (l.lexical_form = "true")
    else JString l.lexical_form
  | T_TripleTerm _ _ _ -> JNull   // csv2rdf/json cells never yield a triple term

// ================================================================
// Per-cell JSON contribution: the subject the cell is about, and (when
// the cell has a non-null value / value URL) its key + values. `cjp_url`
// records that the value(s) are value-URL IRI references — the only cells
// eligible to nest another subject (csv2json: literal cell values are
// ignored by the nesting algorithm).
// ================================================================

noeq type cj_pair = {
  cjp_key  : string;
  cjp_url  : bool;          // values came from a valueUrl (IRI refs)
  cjp_list : bool;          // list-valued (separator) cell -> always a JSON array
  cjp_vals : list json_val;
}

// The JSON key for a column's cell. propertyUrl is expanded exactly as
// the RDF path (csvw_process_cell) does, then COMPACTED; propertyUrl-less
// columns use the URI-decoded column name.
// JSON value for an @type cell: its value URL is compacted (csv2json:
// "If N is @type, compact V url ...").
let cj_type_value (o : rdf_term) : json_val =
  match o with
  | T_IRI i -> JString (cj_compact_url i)
  | _ -> cj_json_of_term o

let cj_cell_key (table_url_resolved : string) (cur_lookup : string -> option string)
                (spec : csvw_col_spec) : string =
  match spec.cs_property_url with
  | Some tmpl ->
    let raw = resolve_iri_v2 table_url_resolved
                (csvw_expand_curie (csvw_expand_template cur_lookup tmpl)) in
    let k = cj_compact_url raw in
    // rdf:type as a property is expressed as JSON-LD's @type keyword, and
    // its value URL is itself compacted (csv2json: "If N is @type, compact
    // V url ...").
    if k = "rdf:type" then "@type" else k
  | None ->
    // cs_name is already the DECODED column name in this codebase (the
    // RDF path percent-ENCODES it for the default propertyUrl — see
    // csvw_encode_name), so it is used verbatim as the JSON key; no
    // corpus column ships an explicitly percent-encoded `name`.
    spec.cs_name

let cj_process_cell
    (table_url_resolved : string) (cur_lookup : string -> option string)
    (default_subject : subject) (spec : csvw_col_spec) (cell_text : option string)
  : (subject & option cj_pair) =
  if spec.cs_suppress then (default_subject, None)
  else
    let subj =
      match spec.cs_about_url with
      | Some tmpl ->
        let raw = csvw_expand_template cur_lookup tmpl in
        let resolved = resolve_iri_v2 table_url_resolved raw in
        if is_iri resolved then S_IRI resolved else default_subject
      | None -> default_subject in
    let key0 = cj_cell_key table_url_resolved cur_lookup spec in
    // A value that is @type carries a compacted value URL rather than the
    // raw resolved one.
    let is_type = key0 = "@type" in
    let has_value_url = Some? spec.cs_value_url in
    (match spec.cs_separator, cell_text with
     | Some sep, Some txt ->
       let parts = csvw_split_list_cell sep txt in
       let objs = L.choose
         (fun (part : string) -> csvw_cell_object table_url_resolved spec (Some part) cur_lookup)
         parts in
       (match objs with
        | [] -> (subj, None)
        | _ ->
          let vals = L.map (fun (o : rdf_term) ->
                              if is_type then cj_type_value o
                              else cj_json_of_term o) objs in
          (subj, Some ({ cjp_key = key0; cjp_url = has_value_url; cjp_list = true; cjp_vals = vals })))
     | _ ->
       (match csvw_cell_object table_url_resolved spec cell_text cur_lookup with
        | None -> (subj, None)
        | Some obj ->
          let v = if is_type then cj_type_value obj else cj_json_of_term obj in
          (subj, Some ({ cjp_key = key0; cjp_url = has_value_url; cjp_list = false; cjp_vals = [v] }))))

// ================================================================
// One row's cells -> flat sequence of subject objects (before nesting).
// A subject contributes an object only when at least one of its cells
// yields a non-null value / value URL (csv2json "Generating Objects").
// ================================================================

// The distinct subjects of a row, in first-appearance order, restricted
// to those with at least one value-bearing cell.
let rec cj_subject_present (s : subject) (rest : list (subject & option cj_pair)) : bool =
  match rest with
  | [] -> false
  | (s2, p) :: tl -> (subject_eq s s2 && Some? p) || cj_subject_present s tl

let rec cj_distinct_subjects (seen : list subject) (cells : list (subject & option cj_pair))
  : Tot (list subject) (decreases cells) =
  match cells with
  | [] -> []
  | (s, p) :: tl ->
    if Some? p && not (L.existsb (fun x -> subject_eq x s) seen)
    then s :: cj_distinct_subjects (s :: seen) tl
    else cj_distinct_subjects seen tl

// Merge one subject's pairs (in column order) into name-value entries,
// combining a repeated key into a flattened array (csv2json: "If name N
// occurs more than once ... compacted to ... an array ... arrays of
// values are flattened").
noeq type cj_acc = { ca_key : string; ca_url : bool; ca_forcearr : bool; ca_vals : list json_val }

let rec cj_acc_find (k : string) (acc : list cj_acc) : option cj_acc =
  match acc with
  | [] -> None
  | a :: tl -> if a.ca_key = k then Some a else cj_acc_find k tl

let rec cj_acc_update (k : string) (p : cj_pair) (acc : list cj_acc) : Tot (list cj_acc) (decreases acc) =
  match acc with
  | [] -> [ { ca_key = k; ca_url = p.cjp_url; ca_forcearr = p.cjp_list; ca_vals = p.cjp_vals } ]
  | a :: tl ->
    if a.ca_key = k
    then { a with ca_forcearr = true; ca_vals = a.ca_vals @ p.cjp_vals } :: tl
    else a :: cj_acc_update k p tl

let rec cj_collect_pairs (subj : subject) (cells : list (subject & option cj_pair)) (acc : list cj_acc)
  : Tot (list cj_acc) (decreases cells) =
  match cells with
  | [] -> acc
  | (s, p) :: tl ->
    (match p with
     | Some pr -> if subject_eq s subj
                 then cj_collect_pairs subj tl (cj_acc_update pr.cjp_key pr acc)
                 else cj_collect_pairs subj tl acc
     | None -> cj_collect_pairs subj tl acc)

let cj_acc_to_pair (a : cj_acc) : (string & json_val) =
  match a.ca_vals with
  | [ v ] -> if a.ca_forcearr then (a.ca_key, JArray [v]) else (a.ca_key, v)
  | vs -> (a.ca_key, JArray vs)

// A subject's object as (id, url-valued-keys, name-value pairs). The
// url-key list feeds the nesting pass (which keys hold nestable IRI
// refs).
noeq type cj_obj = { co_id : option string; co_pairs : list (string & json_val); co_urlkeys : list string }

let cj_build_obj (subj : subject) (cells : list (subject & option cj_pair)) : cj_obj =
  let accs = cj_collect_pairs subj cells [] in
  let id = match subj with S_IRI i -> Some i | S_BNode _ -> None in
  let pairs = L.map cj_acc_to_pair accs in
  let urlkeys = L.map (fun (a : cj_acc) -> a.ca_key)
                      (L.filter (fun (a : cj_acc) -> a.ca_url) accs) in
  { co_id = id; co_pairs = pairs; co_urlkeys = urlkeys }

let cj_row_objects (cells : list (subject & option cj_pair)) : list cj_obj =
  let subs = cj_distinct_subjects [] cells in
  L.map (fun (s : subject) -> cj_build_obj s cells) subs

// ================================================================
// Nesting (csv2json nesting algorithm). Within a row: a URL value that
// occurs exactly once across all cells (the URL-list) and matches the
// @id of another object in the row is replaced by that object, nested.
// Cross-row references (target subject not in this row) stay strings.
// ================================================================

// Every url-valued scalar string across the row's objects.
let rec cj_all_url_values (objs : list cj_obj) : Tot (list string) (decreases objs) =
  match objs with
  | [] -> []
  | o :: tl ->
    L.choose (fun (kv : (string & json_val)) ->
                let (k, v) = kv in
                if L.mem k o.co_urlkeys then (match v with JString s -> Some s | _ -> None) else None)
             o.co_pairs
    @ cj_all_url_values tl

let cj_count (x : string) (xs : list string) : nat =
  L.length (L.filter (fun y -> y = x) xs)

let rec cj_find_obj_by_id (i : string) (objs : list cj_obj) : option cj_obj =
  match objs with
  | [] -> None
  | o :: tl -> (match o.co_id with Some j -> if j = i then Some o else cj_find_obj_by_id i tl
                                 | None -> cj_find_obj_by_id i tl)

// json_val for an object.
let cj_obj_to_json (o : cj_obj) : json_val =
  match o.co_id with
  | Some i -> JObject (("@id", JString i) :: o.co_pairs)
  | None -> JObject o.co_pairs

// Replace, in object `o`, any url-valued scalar whose value is a
// once-occurring @id of another row object, by that object's JSON
// (recursively nested). `depth` bounds the recursion by the object count.
let rec cj_nest_obj (depth : nat) (urllist : list string) (all : list cj_obj) (o : cj_obj)
  : Tot json_val (decreases depth) =
  if depth = 0 then cj_obj_to_json o
  else
    let pairs' =
      L.map (fun (kv : (string & json_val)) ->
               let (k, v) = kv in
               if L.mem k o.co_urlkeys then
                 (match v with
                  | JString s ->
                    if L.mem s urllist then
                      (match cj_find_obj_by_id s all with
                       | Some target ->
                         if (match target.co_id, o.co_id with Some a, Some b -> a = b | _ -> false)
                         then (k, v)   // do not nest an object into itself
                         else (k, cj_nest_obj (depth - 1) urllist all target)
                       | None -> (k, v))
                    else (k, v)
                  | _ -> (k, v))
               else (k, v))
            o.co_pairs in
    (match o.co_id with
     | Some i -> JObject (("@id", JString i) :: pairs')
     | None -> JObject pairs')

// The set of ids that get nested under another object (so they drop out
// of the root list).
let rec cj_nested_ids (urllist : list string) (all : list cj_obj) (objs : list cj_obj)
  : Tot (list string) (decreases objs) =
  match objs with
  | [] -> []
  | o :: tl ->
    L.choose (fun (kv : (string & json_val)) ->
                let (k, v) = kv in
                if L.mem k o.co_urlkeys then
                  (match v with
                   | JString s ->
                     if L.mem s urllist && Some? (cj_find_obj_by_id s all)
                        && not (match o.co_id with Some b -> b = s | None -> false)
                     then Some s else None
                   | _ -> None)
                else None)
             o.co_pairs
    @ cj_nested_ids urllist all tl

// Row -> the sequence of ROOT objects as json_val (nesting applied).
let cj_row_roots (cells : list (subject & option cj_pair)) : list json_val =
  let objs = cj_row_objects cells in
  let allvals = cj_all_url_values objs in
  let urllist = L.filter (fun (s : string) -> cj_count s allvals = 1) allvals in
  let nested = cj_nested_ids urllist objs objs in
  let roots = L.filter (fun (o : cj_obj) ->
                          match o.co_id with Some i -> not (L.mem i nested) | None -> true) objs in
  L.map (fun (o : cj_obj) -> cj_nest_obj (L.length objs) urllist objs o) roots

// ================================================================
// JSON-LD-to-JSON transform for notes and non-core (common) annotations
// (csv2json "JSON-LD to JSON"): copied verbatim except an object using
// @value collapses to that value (dropping @language/@type), an object
// using @id collapses to the IRI string, and a value that was the object
// of an @type is URL-compacted. Property-URL keys are compacted too.
// ================================================================

let rec cj_assoc (k : string) (fs : list (string & json_val)) : option json_val =
  match fs with
  | [] -> None
  | (k2, v) :: tl -> if k2 = k then Some v else cj_assoc k tl

let rec cj_compact_json (fuel : nat) (v : json_val) : Tot json_val (decreases fuel) =
  if fuel = 0 then v
  else match v with
       | JString s -> JString (cj_compact_url s)
       | JArray xs -> JArray (cj_map_compact (fuel - 1) xs)
       | _ -> v
and cj_map_compact (fuel : nat) (xs : list json_val) : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then xs
  else match xs with
       | [] -> []
       | x :: tl -> cj_compact_json (fuel - 1) x :: cj_map_compact (fuel - 1) tl

let rec cj_ld_to_json (fuel : nat) (v : json_val) : Tot json_val (decreases fuel) =
  if fuel = 0 then v
  else match v with
       | JObject fields ->
         (match cj_assoc "@value" fields with
          | Some vv -> vv
          | None ->
            (match cj_assoc "@id" fields with
             | Some (JString s) -> JString s
             | Some other -> other
             | None -> JObject (cj_ld_fields (fuel - 1) fields)))
       | JArray xs -> JArray (cj_ld_items (fuel - 1) xs)
       | _ -> v
and cj_ld_fields (fuel : nat) (fs : list (string & json_val)) : Tot (list (string & json_val)) (decreases fuel) =
  if fuel = 0 then fs
  else match fs with
       | [] -> []
       | (k, x) :: tl ->
         let x' = if k = "@type" then cj_compact_json (json_size x) x else cj_ld_to_json (fuel - 1) x in
         (k, x') :: cj_ld_fields (fuel - 1) tl
and cj_ld_items (fuel : nat) (xs : list json_val) : Tot (list json_val) (decreases fuel) =
  if fuel = 0 then xs
  else match xs with
       | [] -> []
       | x :: tl -> cj_ld_to_json (fuel - 1) x :: cj_ld_items (fuel - 1) tl

// Common (non-core) annotation members -> JSON name-value pairs: key
// compacted (a metadata-authored prefixed name round-trips to itself),
// value JSON-LD-to-JSON transformed.
let cj_common_pairs (common : list (string & json_val)) : list (string & json_val) =
  L.map (fun (kv : (string & json_val)) ->
           let (k, v) = kv in
           (cj_compact_url (csvw_expand_curie k), cj_ld_to_json (json_size v + 1) v))
        common

// A table's explicit @id (tabular-metadata) as a JSON name-value pair: a
// valid string @id (base-resolved) becomes the table object's "@id"
// (test036); an invalid @id degrades to the metadata-document URL
// (test102, same rule as csvw_convert_table_standard); an absent @id
// contributes nothing.
let cj_table_id_pairs (base_iri : string) (doc_url : option string) (tbl : csvw_table)
  : list (string & json_val) =
  match tbl.tbl_id with
  | CsvwIdString s ->
    let r = resolve_iri_v2 base_iri s in
    if is_iri r then [ ("@id", JString r) ] else []
  | CsvwIdInvalid ->
    (match doc_url with Some u -> if is_iri u then [ ("@id", JString u) ] else [] | None -> [])
  | CsvwIdNone -> []

// The "notes" member, present only when the object carries notes.
let cj_notes_pairs (notes : list json_val) : list (string & json_val) =
  match notes with
  | [] -> []
  | _ -> [ ("notes", JArray (L.map (fun (n : json_val) -> cj_ld_to_json (json_size n + 1) n) notes)) ]

// ================================================================
// Row / table / document assembly. Mirrors CSVW.Conversion's standard-
// and minimal-mode document entry points, but building json_val.
// ================================================================

// The per-row (subject, pair) cells — same physical/virtual column setup
// as csvw_row_cell_results, but producing cj_pairs.
let cj_row_cells
    (table_url_resolved : string) (col_specs : list csvw_col_spec)
    (row_num : nat) (source_row_num : nat) (cells : list string)
  : list (subject & option cj_pair) =
  let phys_specs = L.filter (fun (s : csvw_col_spec) -> not s.cs_virtual) col_specs in
  let virt_specs = L.filter (fun (s : csvw_col_spec) -> s.cs_virtual) col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let phys_bindings = L.map (fun (p : (csvw_col_spec & string)) -> (fst p).cs_name, snd p) phys_pairs in
  let base_lookup = csvw_row_lookup phys_bindings row_num source_row_num in
  // Grouping is per-row, so a row-local default-subject label suffices.
  let default_subject = S_BNode ("cjrow_" ^ string_of_int source_row_num) in
  let cur (spec : csvw_col_spec) (v : string) = if v = "_name" then Some spec.cs_name else base_lookup v in
  L.map
    (fun (p : (csvw_col_spec & string)) ->
       cj_process_cell table_url_resolved (cur (fst p)) default_subject (fst p) (Some (snd p)))
    phys_pairs
  @ L.map
      (fun (s : csvw_col_spec) -> cj_process_cell table_url_resolved (cur s) default_subject s None)
      virt_specs

// The row's "titles" member (tabular-metadata rowTitles): for each
// column named in rowTitles, that column's cell value as a string. A
// single title is a bare string; multiple are an array (test235/236).
let cj_row_titles (col_specs : list csvw_col_spec) (cells : list string) (row_titles : list string)
  : list (string & json_val) =
  let phys_specs = L.filter (fun (s : csvw_col_spec) -> not s.cs_virtual) col_specs in
  let phys_pairs = csvw_zip_specs_cells phys_specs cells in
  let bindings = L.map (fun (p : (csvw_col_spec & string)) -> (fst p).cs_name, snd p) phys_pairs in
  let vals = L.choose
    (fun (name : string) -> match L.assoc name bindings with
                            | Some txt -> Some (JString txt)
                            | None -> None)
    row_titles in
  match vals with
  | [] -> []
  | [ v ] -> [ ("titles", v) ]
  | _ -> [ ("titles", JArray vals) ]

// One standard-mode row object: {url, rownum, titles?, describes:[roots]}.
let cj_row_json_standard
    (table_url_resolved : string) (col_specs : list csvw_col_spec) (row_titles : list string)
    (row_num : nat) (source_row_num : nat) (cells : list string)
  : json_val =
  let row_cells = cj_row_cells table_url_resolved col_specs row_num source_row_num cells in
  let roots = cj_row_roots row_cells in
  let row_url = csvw_row_url table_url_resolved source_row_num in
  JObject
    ( [ ("url", JString row_url);
        ("rownum", JNumber (string_of_int row_num)) ]
      @ cj_row_titles col_specs cells row_titles
      @ [ ("describes", JArray roots) ] )

// The table-level `rdfs:comment` member (csv+ syntax REC "Parsing
// Tabular Data" — comment-prefix-matched / skip-rows-zone rows, per
// CSVW.Conversion.csvw_classify_table_rows): present only when the
// table actually produced at least one comment ("If M.rdfs:comment is
// an empty array, remove the rdfs:comment property from M", quoted
// verbatim in the REC's own parsing algorithm).
let cj_comment_pairs (comments : list string) : list (string & json_val) =
  match comments with
  | [] -> []
  | _ -> [ ("rdfs:comment", JArray (L.map (fun (c:string) -> JString c) comments)) ]

// One table's data rows -> (table json object for standard mode, list
// of all root objects for minimal mode, table-level rdfs:comment
// strings).
let cj_table_rows
    (grp_inherited : csvw_inherited_props) (base_iri : string)
    (fallback_url : string) (tbl : csvw_table) (all_rows : list (list string))
  : (string & list json_val & list json_val & list string) =
  // (table_url, standard-row-objs, minimal-root-objs, comments)
  let table_url_resolved = csvw_effective_table_url base_iri fallback_url tbl in
  let dia = tbl.tbl_dialect in
  let skip_cols_n = csvw_skip_columns_count dia in
  let (comments, header_row_opt, data_entries) = csvw_classify_table_rows dia all_rows in
  let header_cells_raw =
    match header_row_opt with
    | Some h -> h
    | None ->
      (match tbl.tbl_table_schema with
       | Some _ -> []
       | None -> (match data_entries with (_, _, r) :: _ -> L.map (fun (_:string) -> "") r | [] -> [])) in
  let header_cells = csvw_drop skip_cols_n header_cells_raw in
  let col_specs = csvw_build_col_specs grp_inherited tbl.tbl_inherited tbl.tbl_table_schema header_cells in
  let row_titles = (match tbl.tbl_table_schema with Some ts -> ts.ts_row_titles | None -> []) in
  let std_rows =
    L.map (fun (p : (nat & nat & list string)) ->
             let (row_num, source_row_num, raw_cells) = p in
             cj_row_json_standard table_url_resolved col_specs row_titles row_num source_row_num (csvw_drop skip_cols_n raw_cells))
          data_entries in
  let min_roots =
    L.collect (fun (p : (nat & nat & list string)) ->
                 let (row_num, source_row_num, raw_cells) = p in
                 let row_cells = cj_row_cells table_url_resolved col_specs row_num source_row_num (csvw_drop skip_cols_n raw_cells) in
                 cj_row_roots row_cells)
              data_entries in
  (table_url_resolved, std_rows, min_roots, comments)

// Minimal mode: the flat array of every root object across every table.
let cj_document_json_minimal
    (grp_inherited : csvw_inherited_props)
    (base_iri : string) (tables_with_rows : list (csvw_table & string & list (list string)))
  : json_val =
  JArray
    (L.collect
       (fun (t : (csvw_table & string & list (list string))) ->
          let (tbl, fallback_url, rows) = t in
          if csvw_table_suppressed tbl then []
          else let (_, _, mins, _) = cj_table_rows grp_inherited base_iri fallback_url tbl rows in mins)
       tables_with_rows)

// Standard mode: {<group common>, tables:[{url, <table common>, notes,
// row:[...], rdfs:comment?}]}. Group- and table-level non-core
// annotations / notes are emitted alongside the core url/row structure
// (csv2json standard mode).
let cj_document_json_standard
    (grp : csvw_group_meta) (doc_url : option string)
    (base_iri : string) (tables_with_rows : list (csvw_table & string & list (list string)))
  : json_val =
  let tables =
    L.map
      (fun (t : (csvw_table & string & list (list string))) ->
         let (tbl, fallback_url, rows) = t in
         let (turl, std_rows, _, comments) = cj_table_rows grp.grp_inherited base_iri fallback_url tbl rows in
         JObject ( cj_table_id_pairs base_iri doc_url tbl
                   @ [ ("url", JString turl) ]
                   @ cj_common_pairs tbl.tbl_common
                   @ cj_notes_pairs tbl.tbl_notes
                   @ [ ("row", JArray std_rows) ]
                   @ cj_comment_pairs comments ))
      (L.filter (fun (t : (csvw_table & string & list (list string))) ->
                   let (tbl, _, _) = t in not (csvw_table_suppressed tbl))
                tables_with_rows) in
  JObject ( cj_common_pairs grp.grp_common @ [ ("tables", JArray tables) ] )
