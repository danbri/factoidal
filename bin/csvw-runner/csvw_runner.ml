(* CSVW (CSV on the Web) csv2rdf test-suite runner — Stage 10 of the
   CSVW program (docs/designissues/2026-07-05-csvw-program-plan.md).

   Reads the vendored csv2rdf manifest (third_party/testing/csvw/tests/
   manifest-rdf.ttl — the Turtle mirror of manifest-rdf.jsonld, same
   mf:/csvt: vocabulary the RDF/SPARQL test manifests already use),
   loads each test's metadata document (if any) via
   CSVW_Metadata.csvw_decode_metadata_text, reads the referenced CSV
   file(s), runs CSVW_Conversion.csvw_convert_document_minimal or
   _standard (mode selected per-test from the manifest's `csvt:minimal`
   option), and compares the resulting triples against the expected
   `.ttl` fixture via RDF_Canonical.canonicalize_to_nquads — the same
   isomorphism-insensitive-to-blank-node-labels comparison
   bin/jsonld-runner and bin/rml-runner already use.

   NegativeRdfTest fixtures PASS iff conversion produces an empty
   triple set OR the metadata document fails to decode — a data error
   means "no RDF term/table was produced," matching bin/rml-runner's
   error=true handling.

   !! THIS IS I/O GLUE — NO CSVW/RDF SEMANTIC LOGIC !! Per CLAUDE.md
   iron rule #11 / anti-pattern #15: metadata decoding lives in
   formal/fstar/CSVW.Metadata.fst, URI-template expansion in
   formal/fstar/CSVW.URITemplate.fst, csv2rdf conversion in
   formal/fstar/CSVW.Conversion.fst, CSV tokenizing in
   formal/fstar/RML.Sources.fst (shared with the RML program, not
   forked — rule #7). This file only does file I/O, manifest-graph
   triple-pattern lookups (queries over an already-parsed graph, not
   itself I/O), and N-Quads comparison.

   Usage:
     ./csvw_runner                Run the csv2rdf manifest (manifest-rdf.ttl)
     ./csvw_runner --filter P     Only run test IDs starting with P
     ./csvw_runner --list         List parsed test entries (no execution)
     ./csvw_runner -v|--verbose   Show expected-vs-got diff on FAIL
     ./csvw_runner --help         Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to rml_runner.ml / jsonld_runner.ml). *)

let find_repo_root () =
  let rec walk d =
    if d = "/" || d = "" then None
    else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
    else walk (Filename.dirname d)
  in
  let start =
    try Filename.dirname (Sys.executable_name)
    with _ -> Sys.getcwd ()
  in
  match walk start with
  | Some r -> r
  | None ->
    (match walk (Sys.getcwd ()) with
     | Some r -> r
     | None -> Sys.getcwd ())

let tests_dir_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root "third_party/testing/csvw/tests";
    "third_party/testing/csvw/tests";
    "../../third_party/testing/csvw/tests";
    "../../../third_party/testing/csvw/tests" ]

let default_dir candidates =
  try List.find Sys.file_exists candidates
  with Not_found -> List.hd candidates

(* ------------------------------------------------------------------ *)
(* File I/O + FStar option interop (same idiom as rml_runner.ml). *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let fs_of_opt = function
  | Some x -> FStar_Pervasives_Native.Some x
  | None -> FStar_Pervasives_Native.None

let head s n =
  if String.length s <= n then s else String.sub s 0 n ^ " …(truncated)"

let abs_path p =
  if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p

(* The CSVW test suite's canonical expected outputs (test*.ttl) were
   generated against the suite's published location,
   http://www.w3.org/2013/csvw/tests/ — some fixtures embed that base
   as ABSOLUTE IRIs (test263-304: number-format / datatype fixtures),
   while most embed only relative references (test001.csv#... ). A
   local file:// base makes every base-dependent subject/predicate IRI
   (table URLs, cell propertyUrls) come out as file://... , which
   matches the relative-ref fixtures but NEVER the absolute-ref ones.
   Presenting the local checkout under its canonical web base is
   standard CSVW-harness configuration (map local dir -> published
   URL): it is NOT conversion logic (the pure conversion in
   CSVW.Conversion is a function of whatever base_iri it is handed).
   Both the conversion output AND the expected-ttl parse use the same
   base here, so relative-ref fixtures keep matching and absolute-ref
   fixtures start matching. *)
let csvw_web_base = "http://www.w3.org/2013/csvw/tests"
let csvw_tests_marker = "third_party/testing/csvw/tests"

(* Return the index just AFTER the first occurrence of [needle] in
   [hay], or None. *)
let substr_end_index hay needle =
  let hl = String.length hay and nl = String.length needle in
  let rec go i =
    if i + nl > hl then None
    else if String.sub hay i nl = needle then Some (i + nl)
    else go (i + 1)
  in
  go 0

(* Map an absolute local directory under .../third_party/testing/csvw/tests
   to its canonical web base (with trailing slash), keeping any
   per-test subdirectory suffix (test032/, test116/, ...). Falls back
   to a file:// base if the marker is absent (out-of-tree run). *)
let web_base_of_dir file_dir =
  match substr_end_index file_dir csvw_tests_marker with
  | Some i -> csvw_web_base ^ String.sub file_dir i (String.length file_dir - i) ^ "/"
  | None -> "file://" ^ file_dir ^ "/"

(* ------------------------------------------------------------------ *)
(* csvt:/mf: vocabulary IRIs, resolved against the manifest's own
   namespace (`@prefix csvt: <http://www.w3.org/2013/csvw/tests/vocab#>`,
   `@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#>`,
   `@prefix rdf: <...#>`), read directly from manifest-rdf.ttl's own
   prefix declarations rather than hand-copied, so a suite update that
   changes a prefix can't silently desync this file. *)

let rdf_type_iri = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let csvt_ns = "http://www.w3.org/2013/csvw/tests/vocab#"
let mf_ns = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#"
let p_to_rdf_test = csvt_ns ^ "ToRdfTest"
let p_to_rdf_test_warn = csvt_ns ^ "ToRdfTestWithWarnings"
let p_negative_rdf_test = csvt_ns ^ "NegativeRdfTest"
let p_action = mf_ns ^ "action"
let p_result = mf_ns ^ "result"
let p_name = mf_ns ^ "name"
let p_option = csvt_ns ^ "option"
let p_minimal = csvt_ns ^ "minimal"
let p_metadata = csvt_ns ^ "metadata"
(* csvt:httpLink — the simulated HTTP `Link:` response header the suite
   injects for metadata discovery step 2 (there is no live server). Its
   value is a string literal of RFC 8288 shape `<url>; rel="describedby"`. *)
let p_http_link = csvt_ns ^ "httpLink"

(* ------------------------------------------------------------------ *)
(* Minimal triple-pattern lookups over an already-parsed manifest graph.
   Blank nodes and IRIs are both reduced to a plain string "node key"
   (an IRI's own string, or "_:<label>" for a blank node) so subject/
   object matching doesn't need to case on RDF_Graph_Executable's
   constructors at every call site. *)

let node_key_of_subject (s : RDF_Graph_Executable.subject) =
  match s with
  | RDF_Graph_Executable.S_IRI i -> i
  | RDF_Graph_Executable.S_BNode b -> "_:" ^ b

let node_key_of_term (t : RDF_Graph_Executable.rdf_term) =
  match t with
  | RDF_Graph_Executable.T_IRI i -> Some i
  | RDF_Graph_Executable.T_BNode b -> Some ("_:" ^ b)
  | RDF_Graph_Executable.T_Literal _ -> None

let objects_of (g : RDF_Graph_Executable.triple list) (subj_key : string) (pred : string) =
  List.filter_map
    (fun (t : RDF_Graph_Executable.triple) ->
       if node_key_of_subject t.RDF_Graph_Executable.s = subj_key
          && t.RDF_Graph_Executable.p = pred
       then Some t.RDF_Graph_Executable.o
       else None)
    g

let object_of (g : RDF_Graph_Executable.triple list) (subj_key : string) (pred : string) =
  match objects_of g subj_key pred with o :: _ -> Some o | [] -> None

let object_iri_of (g : RDF_Graph_Executable.triple list) (subj_key : string) (pred : string) =
  match object_of g subj_key pred with
  | Some t -> node_key_of_term t
  | None -> None

let object_bool_of (g : RDF_Graph_Executable.triple list) (subj_key : string) (pred : string) =
  match object_of g subj_key pred with
  | Some (RDF_Graph_Executable.T_Literal l) -> l.RDF_Graph_Executable.lexical_form = "true"
  | _ -> false

let subjects_with_type (g : RDF_Graph_Executable.triple list) (ty_iri : string) =
  List.filter_map
    (fun (t : RDF_Graph_Executable.triple) ->
       match t.RDF_Graph_Executable.o with
       | RDF_Graph_Executable.T_IRI i when t.RDF_Graph_Executable.p = rdf_type_iri && i = ty_iri ->
         Some (node_key_of_subject t.RDF_Graph_Executable.s)
       | _ -> None)
    g

(* A "file://" IRI produced by resolving a manifest-relative reference
   against `manifest_base` (see `run_suite`) round-trips cleanly back
   to a filesystem path by stripping the scheme — the base is always
   `file://<abs tests dir>/...`, and none of this suite's relative
   references use "../" segments that `resolve_iri_v2` would otherwise
   normalize away. *)
let file_iri_to_path (iri : string) =
  let prefix = "file://" in
  let plen = String.length prefix in
  if String.length iri >= plen && String.sub iri 0 plen = prefix
  then String.sub iri plen (String.length iri - plen)
  else iri

(* Family F (query-string discovery edge cases, test116/test118): an
   `mf:action` may itself carry a `?query` (or, in principle, a `#frag`)
   component — e.g. `test116.csv?query`. That component is part of the
   LOGICAL table URL (it must survive into the IRIs the conversion
   layer builds — csvw:url <test116.csv?query>, table subject IRIs,
   ...) but is NOT part of the on-disk filename: the real file is
   `test116.csv`, with no literal '?' in its name. Every actual
   filesystem access (CSV data read, metadata-file read) strips the
   query/fragment first; every IRI-construction path (base_iri,
   fallback_url, tbl_url, discover_metadata's file-metadata candidate
   name) keeps it, since a "file metadata" lookup for a query-bearing
   URL is a genuinely different (and, per test116, absent) resource
   location than the query-free one. *)
let strip_query_frag (s : string) =
  let cut c = try Some (String.index s c) with Not_found -> None in
  match cut '?', cut '#' with
  | Some q, Some h -> String.sub s 0 (min q h)
  | Some q, None -> String.sub s 0 q
  | None, Some h -> String.sub s 0 h
  | None, None -> s

(* The file extension (no leading '.'), from a query/fragment-stripped
   path — used to build the "directory metadata" discovery candidate
   name below. Defaults to "csv" (this corpus's only tabular-file
   extension) when the action has none. *)
let file_ext_no_dot (path : string) =
  match Filename.extension (strip_query_frag path) with
  | "" -> "csv"
  | e -> String.sub e 1 (String.length e - 1)

(* ------------------------------------------------------------------ *)
(* Test-entry extraction. *)

type test_kind = Positive | PositiveWithWarnings | Negative

type test_entry = {
  te_id : string;
  te_name : string;
  te_kind : test_kind;
  te_action : string;       (* resolved file:// IRI *)
  te_result : string option;(* resolved file:// IRI; None for negative tests with no expected output *)
  te_minimal : bool;
  te_metadata_override : string option; (* csvt:option's csvt:metadata, if given *)
  te_http_link : string option;         (* csvt:httpLink literal value, if given *)
}

let load_entries (g : RDF_Graph_Executable.triple list) =
  let of_kind kind ty_iri =
    List.filter_map
      (fun subj_key ->
         match object_iri_of g subj_key p_action with
         | None -> None
         | Some action ->
           let result = object_iri_of g subj_key p_result in
           let name = (match object_of g subj_key p_name with
                       | Some (RDF_Graph_Executable.T_Literal l) -> l.RDF_Graph_Executable.lexical_form
                       | _ -> subj_key) in
           let minimal, metadata_override =
             (match object_of g subj_key p_option with
              | Some t ->
                (match node_key_of_term t with
                 | Some opt_key -> (object_bool_of g opt_key p_minimal, object_iri_of g opt_key p_metadata)
                 | None -> (false, None))
              | None -> (false, None)) in
           let http_link =
             (match object_of g subj_key p_http_link with
              | Some (RDF_Graph_Executable.T_Literal l) -> Some l.RDF_Graph_Executable.lexical_form
              | _ -> None) in
           Some { te_id = subj_key; te_name = name; te_kind = kind; te_action = action;
                  te_result = result; te_minimal = minimal; te_metadata_override = metadata_override;
                  te_http_link = http_link })
      (subjects_with_type g ty_iri)
  in
  of_kind Positive p_to_rdf_test
  @ of_kind PositiveWithWarnings p_to_rdf_test_warn
  @ of_kind Negative p_negative_rdf_test

(* Sort by the numeric suffix of the test's own IRI fragment (test001,
   test005, ... ) purely for readable, stable output ordering — the
   manifest's own mf:entries list order, which this driver doesn't
   walk (see module banner: it queries by rdf:type instead). *)
let test_number (te : test_entry) =
  let id = te.te_id in
  let rec last_hash i = if i < 0 then 0 else if id.[i] = '#' then i + 1 else last_hash (i - 1) in
  let start = last_hash (String.length id - 1) in
  let rec digits_only i acc =
    if i >= String.length id then acc
    else if id.[i] >= '0' && id.[i] <= '9' then digits_only (i + 1) (acc ^ String.make 1 id.[i])
    else digits_only (i + 1) acc
  in
  try int_of_string (digits_only start "") with _ -> 0

(* ------------------------------------------------------------------ *)
(* Per-test conversion: build the (table, fallback_csv_path, rows) list
   CSVW_Conversion's document-level entry points need, from a decoded
   metadata document (or the "no metadata at all" synthetic table). *)

let read_rows (path : string) : string list list =
  match read_file path with
  | None -> []
  | Some content -> RML_Sources.csv_parse_rows content

(* `fallback_url` is only consulted by CSVW_Conversion when a table's
   own `tbl_url` is absent — normally true only for the "no metadata
   document at all" synthetic table, where the CSV named directly by
   mf:action IS the table. *)
let tables_with_rows (test_dir : string) (action_path : string) (meta_opt : CSVW_Metadata.csvw_metadata option)
  : (CSVW_Metadata.csvw_table * string * string list list) list =
  let read_table (tbl : CSVW_Metadata.csvw_table) (fallback_url : string) =
    let rel = (match opt_of_fs tbl.CSVW_Metadata.tbl_url with Some u -> u | None -> fallback_url) in
    (* `rel` may carry a `?query`/`#frag` (test118: tbl_url itself is
       "action.csv?query"; test116: fallback_url is "test116.csv?query")
       — strip it for the actual disk read only; `fallback_url` (passed
       through unchanged to CSVW_Conversion for IRI construction) keeps it. *)
    let path = Filename.concat test_dir (strip_query_frag rel) in
    (tbl, fallback_url, read_rows path)
  in
  match meta_opt with
  | None ->
    (* mf:action IS the CSV file directly — schema inferred from its own header row. *)
    let fallback = Filename.basename action_path in
    [ read_table CSVW_Conversion.csvw_no_metadata_table fallback ]
  | Some (CSVW_Metadata.CSVW_Table t) ->
    [ read_table t (Filename.basename action_path) ]
  | Some (CSVW_Metadata.CSVW_TableGroup (ts, _)) ->
    List.map (fun t -> read_table t (Filename.basename action_path)) ts

(* ------------------------------------------------------------------ *)
(* Per-test execution + outcome. *)

type outcome = Pass | Fail of string | Skip of string

(* CSVW metadata discovery (tabular-data-model §5.8, "Metadata
   Discovery"), the subset the suite's own test names exercise
   ("user metadata" / "file metadata" / "directory metadata"), tried
   in the spec's priority order after an explicit override:
     1. `csvt:option`'s `csvt:metadata` (an explicit user-supplied
        metadata document — te_metadata_override, checked by the
        caller before this function runs).
     2. `mf:action` itself, when it already IS a metadata document.
     3. `<tabular file name>-metadata.json` next to the CSV ("file
        metadata" — test011/tree-ops.csv-metadata.json). Built from the
        UN-stripped action path, so a query-bearing action (test116:
        `test116.csv?query`) genuinely fails to find a same-named file
        — a query-suffixed URL is a distinct resource per tabular-
        data-model, and this corpus's own fixtures never ship a
        literal `?`-containing filename.
     4. `<extension>-metadata.json` in the same directory ("directory
        metadata" — test012/csv-metadata.json, test118/csv-metadata.json,
        test123/csv-metadata.json). The vendored corpus's own naming
        convention for this candidate is the ACTION's file extension
        (always "csv" here), not the spec-literal "metadata.json" — no
        fixture in the corpus ever uses that literal name (confirmed:
        zero `metadata.json` files under third_party/testing/csvw/tests).
   Link-header simulation (`csvt:httpLink`) and site-wide
   `/.well-known/csvm` are out of scope — no HTTP layer in this
   runner (test014/test016's `csvt:httpLink` fixtures stay unhandled by
   design, per the owner directive parking HTTP-based discovery
   alongside SPARQL Protocol). *)
let decode_metadata_file (p : string) : CSVW_Metadata.csvw_metadata option =
  match read_file p with
  | None -> None
  | Some content -> opt_of_fs (CSVW_Metadata.csvw_decode_metadata_text content)

(* A DISCOVERED (not explicitly requested) metadata document is only
   used when at least one of its tables actually names the requested
   tabular file — tabular-data-model §5.8: "if the metadata file found
   at this location does not explicitly include a reference to the
   requested tabular data file then it MUST be ignored" (test117's own
   fixture comment, verbatim). An explicit `csvt:metadata` override or
   an `mf:action` that IS the metadata document skips this check
   entirely — the user/test asked for that document by name, not by
   discovery. *)
let metadata_references_file (action_basename : string) (meta : CSVW_Metadata.csvw_metadata) =
  let tbl_matches (t : CSVW_Metadata.csvw_table) =
    match opt_of_fs t.CSVW_Metadata.tbl_url with
    | Some u -> Filename.basename u = action_basename
    | None -> false
  in
  match meta with
  | CSVW_Metadata.CSVW_Table t -> tbl_matches t
  | CSVW_Metadata.CSVW_TableGroup (ts, _) -> List.exists tbl_matches ts

let discover_metadata (test_dir : string) (action_path : string) =
  let action_basename = Filename.basename action_path in
  let try_candidate p =
    if Sys.file_exists p then
      match decode_metadata_file p with
      | Some meta when metadata_references_file action_basename meta -> Some (p, meta)
      | _ -> None
    else None
  in
  match try_candidate (action_path ^ "-metadata.json") with
  | Some r -> Some r
  | None ->
    (match try_candidate (Filename.concat test_dir (file_ext_no_dot action_path ^ "-metadata.json")) with
     | Some r -> Some r
     | None ->
       (* Site-wide-configuration templates (tabular-data-model §5.8,
          "the metadata located through site-wide configuration" served
          at w3.org/.well-known/csvm): the `{+url}.json` template
          (test260: tree-ops.csv.json) and the fixed-name `csvm.json`
          (test259). No live HTTP — these are ordinary local files here.
          Both are guarded by the same references-file check as the
          file/directory candidates above, and only two files in the
          whole corpus match either name (test259/csvm.json,
          test260/tree-ops.csv.json), so they never misfire elsewhere. *)
       (match try_candidate (action_path ^ ".json") with
        | Some r -> Some r
        | None -> try_candidate (Filename.concat test_dir "csvm.json")))

(* Metadata discovery step 2 (tabular-data-model §5.8): the metadata
   referenced by the simulated HTTP `Link:` header (csvt:httpLink). The
   Link value is parsed in F* (CSVW_Metadata.csvw_link_header_describedby
   — a parser, per rule #4); this glue only reads the annotation string,
   resolves the returned (relative) URL against the CSV's directory,
   reads it, and applies the SAME references-file check the file/
   directory candidates use: a linked document that does not reference
   the requested tabular file MUST be ignored (test120/122 keep passing
   because their linked docs don't reference the file, so discovery
   falls through to file/directory metadata). Higher priority than
   file/directory discovery, so a describing linked document wins over
   directory metadata (test016: linked-metadata.json beats
   csv-metadata.json). *)
let discover_via_http_link (test_dir : string) (action_path : string) (link_opt : string option) =
  match link_opt with
  | None -> None
  | Some link ->
    (match opt_of_fs (CSVW_Metadata.csvw_link_header_describedby link) with
     | None -> None
     | Some rel_url ->
       let action_basename = Filename.basename action_path in
       let p = Filename.concat test_dir (strip_query_frag rel_url) in
       if Sys.file_exists p then
         (match decode_metadata_file p with
          | Some meta when metadata_references_file action_basename meta -> Some (p, meta)
          | _ -> None)
       else None)

(* The per-test working directory is the ACTION file's own directory,
   not the shared manifest directory — most tests sit flat in
   `tests/`, but a handful (test032/035/118/119, ...) put their
   fixtures under `tests/testNNN/`, and mf:action's own resolved path
   (via the manifest's base IRI) already reflects that. Deriving
   test_dir from action_path here (rather than threading the
   manifest's directory through) makes subdirectory tests fall out
   for free instead of needing a special case per fixture. *)
(* Schema-by-reference resolution (tabular-metadata, test034/035): a
   table whose `tableSchema` was a bare URL string carries a
   CSVW_Metadata.tbl_schema_ref instead of an inline schema. Read the
   referenced local file (resolved against the metadata document's
   directory) and fold its decoded schema into the table via the F*
   csvw_table_inline_schema — I/O glue only; the JSON decode itself stays
   in CSVW.Metadata (csvw_decode_table_schema_text, rule #4/#11). *)
let resolve_schema_refs (dir : string) (meta : CSVW_Metadata.csvw_metadata)
  : CSVW_Metadata.csvw_metadata =
  let inline_one (t : CSVW_Metadata.csvw_table) =
    match opt_of_fs t.CSVW_Metadata.tbl_schema_ref with
    | None -> t
    | Some url ->
      let p = Filename.concat dir (strip_query_frag url) in
      (match read_file p with
       | None -> t
       | Some content ->
         (match opt_of_fs (CSVW_Metadata.csvw_decode_table_schema_text content) with
          | None -> t
          | Some ts -> CSVW_Metadata.csvw_table_inline_schema t ts))
  in
  match meta with
  | CSVW_Metadata.CSVW_Table t -> CSVW_Metadata.CSVW_Table (inline_one t)
  | CSVW_Metadata.CSVW_TableGroup (ts, g) ->
    CSVW_Metadata.CSVW_TableGroup (List.map inline_one ts, g)

let run_test (te : test_entry) =
  let action_path = file_iri_to_path te.te_action in
  let test_dir = Filename.dirname action_path in
  let base_iri0 = web_base_of_dir (abs_path test_dir) in
  let explicit_metadata_path =
    match te.te_metadata_override with
    | Some m -> Some (file_iri_to_path m)
    | None -> if Filename.check_suffix action_path ".json" then Some action_path else None
  in
  let metadata_path, meta_opt =
    match explicit_metadata_path with
    | Some p -> (Some p, decode_metadata_file p)
    | None ->
      (match discover_via_http_link test_dir action_path te.te_http_link with
       | Some (p, meta) -> (Some p, Some meta)
       | None ->
         (match discover_metadata test_dir action_path with
          | Some (p, meta) -> (Some p, Some meta)
          | None -> (None, None)))
  in
  let decode_failed = (metadata_path <> None && meta_opt = None) in
  (* `@base` override in the @context array (test273): a string resolved
     against the metadata-document location, becoming the base URL for
     every other URL in the document (table `url`, cell templates). The
     @context is interpreted in F* (CSVW_Metadata.csvw_metadata_context_
     base — a parser, rule #4); this glue only folds the result into the
     base IRI and, for a RELATIVE override, into the directory the CSV
     files are physically read from (the referenced CSV moves with the
     base — test273's action.csv sits under tests/test273/, not tests/).
     An absolute override changes only the logical base, not disk paths. *)
  let ctx_base =
    match metadata_path with
    | Some p ->
      (match read_file p with
       | Some content -> opt_of_fs (CSVW_Metadata.csvw_metadata_context_base content)
       | None -> None)
    | None -> None
  in
  let base_iri, csv_dir =
    match ctx_base with
    | Some b when String.length b >= 1 ->
      (* Absolute (has a "scheme://") overrides only the logical base;
         relative resolves against the metadata-document location and
         also relocates the CSV read directory. *)
      if substr_end_index b "://" <> None
      then (b, test_dir)
      else (base_iri0 ^ b, Filename.concat test_dir b)
    | _ -> (base_iri0, test_dir)
  in
  (* Fold any external schema references (test034/035) in before building
     the table/row list — the referenced schema files live under the same
     directory the CSVs are read from (csv_dir). *)
  let meta_opt = match meta_opt with
    | Some m -> Some (resolve_schema_refs csv_dir m)
    | None -> None in
  let tables = tables_with_rows csv_dir action_path meta_opt in
  (* Group-level inherited-property defaults + common properties
     (Stage 2 — test038/039/275-278/305-307 family): present only when
     the document actually IS a table group ("tables": [...] at the
     top level); a bare CSVW_Table document has no separate group-level
     JSON object to inherit from, so csvw_group_meta_empty is correct
     there, not a stand-in for a missing feature. *)
  let grp_meta =
    match meta_opt with
    | Some (CSVW_Metadata.CSVW_TableGroup (_, g)) -> g
    | _ -> CSVW_Metadata.csvw_group_meta_empty
  in
  (* The metadata document's @context default language (test259/260):
     applied by CSVW.Conversion to common-property string values only.
     Interpreting @context stays in F* (csvw_metadata_context_language);
     this glue only feeds it the already-read document text. *)
  let default_lang =
    match metadata_path with
    | Some p ->
      (match read_file p with
       | Some content -> opt_of_fs (CSVW_Metadata.csvw_metadata_context_language content)
       | None -> None)
    | None -> None
  in
  let triples =
    if decode_failed then []
    else if te.te_minimal then
      CSVW_Conversion.csvw_convert_document_minimal grp_meta.CSVW_Metadata.grp_inherited base_iri tables
    else CSVW_Conversion.csvw_convert_document_standard grp_meta (fs_of_opt default_lang) base_iri tables
  in
  let got_ds : RDF_Graph_Executable.rdf_dataset = { RDF_Graph_Executable.ds_default = triples; ds_named = [] } in
  match te.te_kind with
  | Negative ->
    if decode_failed || triples = [] then Pass
    else
      Fail (Printf.sprintf "expected no output (NegativeRdfTest) but got:\n%s"
              (head (RDF_Canonical.canonicalize_to_nquads got_ds) 400))
  | Positive | PositiveWithWarnings ->
    (match te.te_result with
     | None -> Fail "no mf:result recorded for a positive test"
     | Some result_iri ->
       let result_path = file_iri_to_path result_iri in
       (match read_file result_path with
        | None -> Fail (Printf.sprintf "expected output file not found: %s" result_path)
        | Some exp_ttl ->
          let exp_triples = Parser_Turtle.parse_turtle_with_base exp_ttl base_iri in
          let exp_ds : RDF_Graph_Executable.rdf_dataset = { RDF_Graph_Executable.ds_default = exp_triples; ds_named = [] } in
          let exp_canon = RDF_Canonical.canonicalize_to_nquads exp_ds in
          let got_canon = RDF_Canonical.canonicalize_to_nquads got_ds in
          if got_canon = exp_canon then Pass
          else
            Fail (Printf.sprintf "canonical N-Quads differ\n      expected:\n%s      got:\n%s"
                    (head exp_canon 400) (head got_canon 400))))

(* ------------------------------------------------------------------ *)
(* Suite run + reporting. *)

let matches_filter filter id =
  match filter with
  | None -> true
  | Some p ->
    (* match against the test's local name (after '#'), not the full IRI *)
    let rec last_hash i = if i < 0 then 0 else if id.[i] = '#' then i + 1 else last_hash (i - 1) in
    let start = last_hash (String.length id - 1) in
    let local = String.sub id start (String.length id - start) in
    String.length local >= String.length p && String.sub local 0 (String.length p) = p

let kind_label = function
  | Positive -> "ToRdfTest"
  | PositiveWithWarnings -> "ToRdfTestWithWarnings"
  | Negative -> "NegativeRdfTest"

let print_help () =
  print_string
    "CSVW (CSV on the Web) csv2rdf test-suite runner — Stage 10 of the CSVW program.\n\
     \n\
     Usage:\n\
     \  ./csvw_runner                Run the csv2rdf manifest\n\
     \  ./csvw_runner --filter P     Only run test IDs whose local name starts with P\n\
     \  ./csvw_runner --list         List parsed test entries (no execution)\n\
     \  ./csvw_runner -v|--verbose   Show expected-vs-got diff on FAIL\n\
     \  ./csvw_runner --help         Show this help\n\
     \n\
     See docs/designissues/2026-07-05-csvw-program-plan.md for scope/gaps.\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let list_only = ref false in
  let filter = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: rest -> list_only := true; loop rest
    | "--filter" :: p :: rest -> filter := Some p; loop rest
    | _ -> Printf.eprintf "csvw_runner: unexpected arguments; try --help\n"; exit 2
  in
  loop args;
  let test_dir = default_dir (tests_dir_candidates ()) in
  let manifest_path = Filename.concat test_dir "manifest-rdf.ttl" in
  Printf.printf "=== CSVW csv2rdf Test Runner ===\n";
  Printf.printf "manifest: %s\n\n" manifest_path;
  match read_file manifest_path with
  | None -> Printf.eprintf "csvw_runner: cannot read manifest at %s\n" manifest_path; exit 2
  | Some manifest_ttl ->
    let manifest_base = "file://" ^ abs_path test_dir ^ "/manifest-rdf.ttl" in
    let g = Parser_Turtle.parse_turtle_with_base manifest_ttl manifest_base in
    let all_entries = load_entries g in
    let entries =
      List.filter (fun te -> matches_filter !filter te.te_id) all_entries
      |> List.sort (fun a b -> compare (test_number a) (test_number b))
    in
    Printf.printf "%d test entries (of %d in manifest)\n\n" (List.length entries) (List.length all_entries);
    if !list_only then begin
      List.iter
        (fun te -> Printf.printf "  %-10s %-24s %s\n" (kind_label te.te_kind) te.te_id te.te_name)
        entries;
      exit 0
    end;
    let pass = ref 0 and fail = ref 0 in
    let fail_buckets = Hashtbl.create 8 in
    List.iter
      (fun te ->
         match run_test te with
         | Pass -> incr pass; Printf.printf "PASS %-10s %s\n" (kind_label te.te_kind) te.te_id
         | Fail msg ->
           incr fail;
           Printf.printf "FAIL %-10s %s — %s\n" (kind_label te.te_kind) te.te_id
             (if !verbose then msg else List.hd (String.split_on_char '\n' msg));
           let bucket = kind_label te.te_kind in
           Hashtbl.replace fail_buckets bucket (1 + (try Hashtbl.find fail_buckets bucket with Not_found -> 0))
         | Skip _ -> ())
      entries;
    Printf.printf "\n========================================\n";
    Printf.printf "csv2rdf: %d pass, %d fail (out of %d)\n" !pass !fail (List.length entries);
    Hashtbl.iter (fun k v -> Printf.printf "  fail bucket %-24s %d\n" k v) fail_buckets;
    Printf.printf "========================================\n";
    if !fail > 0 then exit 1
