(* entry_jsoo — js_of_ocaml / wasm_of_ocaml entry point for the npm package.

   This is a CONSUMER (rule #11): hand-written OCaml glue that exposes the
   F*-extracted engine to JavaScript via a small, stable, string/JSON ABI.
   No RDF or SPARQL semantics live here — every semantic operation
   delegates to an F*-extracted module:

     parse        -> Parser_NTriples / Parser_Turtle / Parser_NQuads /
                     Parser_TriG / Parser_RDFXML (+ RDF_Format dispatch,
                     RDF_Dataset_Merge.rename_dataset_bnodes for
                     per-document blank-node scoping)
     query        -> SPARQL11_Parser.parse_sparql, OWL_QueryRewrite,
                     SPARQL11_Store.run_select_query_backend_dataset /
                     run_ask_query_backend_dataset (fallback:
                     SPARQL11_Algebra.eval_select_query / eval_ask_query),
                     SPARQL11_Algebra.eval_construct_query
     update       -> SPARQL11_Parser.parse_sparql_update,
                     SPARQL11_Algebra.apply_update
     serialize    -> RDF_Canonical.canonical_nquads (sorted N-Quads)
     canonicalize -> RDF_Canonical.canonicalize_to_nquads (RDFC-1.0)
     serialize (turtle) -> RDF_Turtle_Serialize.turtle_of_graph_auto
                     (prefix-compacted, subject-grouped pretty-print;
                     human-facing, not the round-trip/hash-fidelity path)
     SRJ terms    -> SPARQL_Protocol.json_term, SPARQL_JSON_Escape

   ABI contract (all arguments and results are strings; structure is JSON):

     factoidalNpmEntry.abiVersion
       "1" — bump when a signature or JSON shape changes.
     factoidalNpmEntry.parseToDatasetJson(text, format, baseIri)
       -> {"ok":true,"nquads":"...","count":N} | {"ok":false,"error":"..."}
       format: "turtle"|"ntriples"|"nquads"|"trig"|"rdfxml" (aliases as in
       RDF_Format.format_of_string); baseIri "" means none. The dataset
       handle IS the returned N-Quads string.
     factoidalNpmEntry.queryDataset(nquads, sparql)
       -> {"ok":true,"kind":"select","srj":{...SPARQL results JSON...}}
        | {"ok":true,"kind":"ask","boolean":true|false}
        | {"ok":true,"kind":"construct","nquads":"..."}
        | {"ok":false,"error":"..."}
     factoidalNpmEntry.askDataset(nquads, sparql)
       -> {"ok":true,"boolean":true|false} | {"ok":false,"error":"..."}
     factoidalNpmEntry.updateDataset(nquads, sparqlUpdate)
       -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
     factoidalNpmEntry.serializeNQuads(nquads)
       -> {"ok":true,"nquads":"..."} (parse + sorted re-serialization)
     factoidalNpmEntry.canonicalizeToNQuads(nquads)
       -> {"ok":true,"nquads":"..."} (RDFC-1.0 canonical labels + sort)
     factoidalNpmEntry.serializeTurtle(nquads)
       -> {"ok":true,"turtle":"..."} (prefix-compacted, subject-grouped
          pretty-print; parse(result) round-trips to the input graph,
          but the exact text is NOT stable/canonical the way nquads is)
     factoidalNpmEntry.rifSmoke()
       -> {"ok":true,"inputNquads":"...","saturatedNquads":"...",
           "inputCount":N,"derivedCount":N,"rounds":N,"fuel":N,
           "engineMs":F} | {"ok":false,"error":"..."}
       Live re-run of RIF.Core.Eval.fst's own smoke_input_graph /
       smoke_program via RIF_Core_Eval.fixpoint -- no user input, a
       fixed capability probe (issue #274).
     factoidalNpmEntry.rifEval(rifXml, dataNQuads)
       -> {"ok":true,"inputNquads":"...","saturatedNquads":"...",
           "inputCount":N,"derivedCount":N,"rounds":N,"fuel":N,
           "engineMs":F} | {"ok":false,"error":"..."}
       General entry point: rifXml is a RIF Core XML document (any
       DOCTYPE + &rif;/&xs;/&rdf; entities are stripped/inlined first
       via rif_xml_preprocess -- real vendored RIF-XML uses this
       convention universally; a no-op on a document that has none --
       then parsed by Parser_RIFXML.parse_rif_program), dataNQuads is
       the premise graph (parsed by Parser_NQuads.parse_nquads, default
       graph only). Saturated via RIF_Core_Eval.fixpoint, fuel=100.
       Import directives are not resolved (Parser_RIFXML.
       parse_rif_program ignores them; RIF_Core_Tests.
       saturate_with_program has the same limitation) -- rules
       referencing an <Import>'d graph will not see those triples
       unless the caller merges them into dataNQuads first.
     factoidalNpmEntry.jsonldToRdf(jsonldText, optionsJson)
       -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
       Parser_JSONLD.parse_jsonld, with per-document blank-node scoping
       (same rename_dataset_bnodes pass parseToDatasetJson applies).
       optionsJson is a JSON object (or "" for defaults) with optional
       string fields "base", "rdfDirection", "expandContext",
       "processingMode" -- passed straight through to parse_jsonld's
       matching parameters. Remote contexts / "@import" are an honest
       FAIL (no documentLoader registered for this consumer -- see the
       jsonld_loader_register call below, same choice
       bin/factoidal-cli/bin/factoidal-http make).
       NOTE: parseToDatasetJson(text, "jsonld", baseIri) now also works
       (the format-dispatch gap is fixed below) -- jsonldToRdf exists
       for the extra options parseToDatasetJson's 3-string-arg ABI has
       no room for.
     factoidalNpmEntry.shaclValidate(dataNQuads, shapesNQuads)
       -> {"ok":true,"conforms":true|false,"reportNquads":"..."}
        | {"ok":false,"error":"..."}
       dataNQuads/shapesNQuads are dataset handles (same convention as
       queryDataset et al) -- only the default graph's triples are
       used (SHACL operates over a plain rdf_graph). SHACL_Validation.
       parse_shape_from_graph + .validate (the same call path
       bin/shacl-runner/shacl_runner.ml drives); reportNquads is
       SHACL_Validation.validation_report_to_graph serialized as
       default-graph N-Triples-per-line text.
     factoidalNpmEntry.shexValidate(dataNQuads, schemaJson, focus, shapeLabel)
       -> {"ok":true,"verdict":true|false,"deferred":false}
        | {"ok":true,"verdict":null,"deferred":true}
        | {"ok":false,"error":"..."}
       dataNQuads is a dataset handle (default graph only, same cut as
       shaclValidate). ShEx_Schema.decode_shex_schema (base "") +
       ShEx_Validation.validate_focus. `focus` is an IRI, or "_:label"
       for a blank node; `shapeLabel` "" means "validate against the
       schema's own start". `deferred:true` (verdict null) means
       validate_focus returned None -- outside this engine's decidable
       fragment (see ShEx.Validation.fst's file header), never a
       guessed answer.
     factoidalNpmEntry.owlClosure(dataNQuads, mode)
       -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
       dataNQuads is a dataset handle; only the default graph is
       closed over. mode is "RDFS"
       (RDF_Graph_Executable.rdfs_closure_with_reflexivity) or "OWL-RL"
       (.owl_rl_closure_with_reflexivity), fuel=100 -- the same
       closures bin/w3c-runner drives for entailment-regime tests.
       Result is the closure graph (input + derived triples) as
       default-graph N-Quads text.
     factoidalNpmEntry.rmlMap(mappingNQuads, sourceData, sourceKind)
       -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
       mappingNQuads is a dataset handle for the RML mapping GRAPH
       (default graph only); sourceData is the RML logical source's
       raw data (JSON or CSV text, per sourceKind), not RDF.
       RML_Mapping.decode_mapping_document + RML_Eval.
       eval_triples_map_json / eval_triples_map_csv (sourceKind is
       "json" or "csv") for every triples map in the document, placed
       into one dataset via RML_Eval.place_into_dataset and serialized
       with RDF_Canonical.canonical_nquads. Scope limitation (documented,
       not silent): every triples map reads the SAME sourceData single-
       document handle -- RefObjectMap/join triples spanning two
       DIFFERENT logical sources (RML_Eval.eval_join_triples_map's
       lookup_parent hook) are not reachable through this one-document
       entry point; see bin/rml-runner/rml_runner.ml for the full
       multi-source join driver this does not attempt to replicate.
     factoidalNpmEntry.deltaBatchToHex(sparqlUpdate, seq, epoch)
       -> {"ok":true,"hex":"...","opCount":N} | {"ok":false,"error":"..."}
       Browser-persistence prototype (issue #282's browser realisation,
       docs/designissues/2026-07-06-browser-persistence.md). Translates
       one SPARQL Update -- INSERT DATA / DELETE DATA / CLEAR / DROP /
       CREATE only, the same subset RDF_Store_Columnar_DeltaMerge.
       update_ops_to_delta_entries covers and bin/factoidal-http/
       factoidal_http.ml's --rw commit path already accepts -- into one
       framed `delta_batch` (RDF_Store_Columnar_DeltaLog.
       serialize_delta_batch, the same verified byte format the native
       on-disk delta log uses), hex-encoded for the caller to persist
       as one record in IndexedDB/OPFS. `seq`/`epoch` are decimal
       strings (the caller owns log ordering/compaction bookkeeping --
       e.g. an IndexedDB autoIncrement-style counter); DELETE/INSERT
       WHERE, COPY, MOVE, ADD are not yet translatable and return
       ok:false rather than silently no-op'ing (rule #26).
     factoidalNpmEntry.deltaMergeApplyBrowser(nquads, hexBlobsNewlineJoined)
       -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
       The read-back half: `nquads` is the pre-update dataset handle;
       `hexBlobsNewlineJoined` is every persisted delta_batch hex blob,
       one per line, in ANY order (sorted here by db_seq). Each line is
       independently parsed (RDF_Store_Columnar_DeltaLog.
       parse_delta_batch -- self-framed: magic+version+length+
       checksum); a blob that fails to parse (a torn/corrupted record)
       is SKIPPED, never partially decoded -- the per-record analogue
       of the on-disk log's "accept a prefix, never a torn entry"
       contract. Surviving batches are merged onto the base dataset via
       RDF_Store_Columnar_DeltaMerge.apply_entries_ref, one call per
       graph (default graph plus every named graph the base or the
       delta batches mention -- DeltaMerge.delta_batches_named_graphs
       discovers CREATE-only graphs with no base rows of their own).
     factoidalNpmEntry.openCottas(bytesHex)
       -> {"ok":true,"handle":"npmcottas:N"} | {"ok":false,"error":"..."}
       In-memory COTTAS bytes store (docs/designissues/2026-07-06-
       inmemory-bytes-store.md stage 5). bytesHex is a whole `.cottas`
       (COTTAS/Parquet) artifact, hex-encoded. Registers the bytes under
       a fresh synthetic handle (Parquet_Footer.register_memory_buffer
       -- the same cache the native CLI's `--data-cottas-mem` populates,
       RDF.CottasStore.fst:344's `cottas_ondisk_open` never distinguishes
       a synthetic handle from a real path) and opens it as a
       cottas_ondisk_store, kept in a process-wide registry keyed by the
       returned handle string. `cottas_ondisk_open`'s OCaml realization
       is LAZY (issue Bet7 -- see RDF.CottasStore.LazyDict.fst's own
       banner): opening never eagerly decodes the footer or any column,
       so a malformed/truncated artifact usually still returns ok:true
       here -- the honest failure surfaces on the FIRST queryCottas()
       call that actually needs to touch a column, as ok:false (this
       function's own `guarded` wrapper still turns any exception
       load_handle itself cannot tolerate into ok:false, so a caller
       never sees an uncaught throw either way). This is a QUERY-ONLY
       store: no delta-log overlay, no --rw -- see queryCottas's doc
       comment for what query shapes are actually reachable.
     factoidalNpmEntry.queryCottas(handle, sparql)
       -> {"ok":true,"kind":"select","srj":{...}}
        | {"ok":true,"kind":"ask","boolean":true|false}
        | {"ok":true,"kind":"construct","nquads":"..."}
        | {"ok":false,"error":"..."}
       Runs sparql against the store opened by openCottas(handle) via
       the SAME SPARQL11_Store backend-executor path (`cottas_ondisk_
       dataset_backend` / `run_select_query_backend_dataset` /
       `run_ask_query_backend_dataset`) the native `--data-cottas` CLI
       query path uses -- no triple is ever fully materialized into a
       heap `rdf_dataset` for SELECT/ASK; only the rows the query
       actually touches are decoded (the whole point of the bytes-store
       design: O(quad-cardinality-touched), not O(dataset-size), memory).
       A query SHAPE the backend executor cannot handle (same honest-
       failure posture factoidal_cli.ml's `run_select_query_backend_
       dataset`/`run_ask_query_backend_dataset` None case has, no silent
       fallback) returns ok:false rather than materializing anyway.
       CONSTRUCT is the one exception: it goes through `materialize_
       dataset_backend` (a full decode of the matched rows into an
       `rdf_dataset`, same cost as the native CLI's CONSTRUCT-over-
       COTTAS path) before `eval_construct_query`, since there is no
       backend-executor CONSTRUCT path yet (issue #103, same gap the
       native CLI documents). DESCRIBE is not supported (ok:false).
       Divergence from queryDataset (the heap-store ABI): no entailment
       parameter (bare COTTAS bytes carry no closure step), and no
       --delta-log/write overlay -- read-only, matching design doc
       §2.4's "write/delta-overlay story" (the overlay composes at the
       NATIVE store_caps layer; wiring it into this browser ABI is not
       done here, tracked as an open gap, not a silent omission).
     factoidalNpmEntry.closeCottas(handle)
       -> {"ok":true} | {"ok":false,"error":"..."}
       Drops `handle` from this entry point's own registry so a later
       queryCottas(handle, ...) fails cleanly ("unknown handle") instead
       of silently reusing a store the caller considers closed. Does
       NOT evict the underlying `__mim2_file_bytes_cache` entry
       (Parquet_Footer.ml's process-wide cache has no eviction API --
       design doc §"Open decisions" item 1); a long-lived page that
       opens many short-lived stores still grows that cache for the tab's
       lifetime. Documented divergence, not a silent leak: the design
       doc flags this as an open decision, not a solved one.
     factoidalNpmEntry.toCottas(nquads)
       -> {"ok":true,"cottasHex":"...","quadCount":N} | {"ok":false,"error":"..."}
       The write half (design doc §2.3/§3 stage 3's "parse -> serialize
       -> buffer -> query, entirely in one process" composition, minus
       the buffer/query steps -- those are openCottas/queryCottas
       above). nquads is a dataset handle (N-Quads text, same convention
       as every other ABI call); quads are sorted (s,p,o,g) and encoded
       via the pure `Tot` F* serializer RDF.CottasStore.BaseWriter.
       serialize_cottas_v2 -- the SAME function `factoidal compact
       --native-writer` / `factoidal import` call natively, so a
       browser-produced .cottas is byte-for-byte the same writer's
       output, not a parallel encoder. cottasHex is the resulting
       artifact, hex-encoded, for the caller to persist (IndexedDB/OPFS,
       or offer as a browser download) and later feed back into
       openCottas verbatim -- toCottas + openCottas round-trip through
       the exact same reader/writer pair the native CLI's `factoidal
       compact --native-writer` and `--data-cottas-mem` already use in
       production, so this is a compatibility guarantee, not a hope.
     factoidalNpmEntry.csvwToRdf(csvText, metadataJson, optionsJson)
       -> {"ok":true,"nquads":"..."} | {"ok":false,"error":"..."}
       CSVW csv2rdf conversion (w3.org/TR/csv2rdf). csvText is the raw
       tabular data (RFC 4180, tokenized by the F-star-extracted
       RML_Sources.csv_parse_rows -- the same shared tokenizer rmlMap's
       csv path uses); metadataJson is a CSVW metadata document
       (tabular-metadata JSON), or "" to infer the schema from the
       CSV's own header row. optionsJson is a JSON object (or "" for
       defaults) with optional string fields:
         "mode": "standard" (default -- full csvw:TableGroup/Table/Row
                 wrapper, the shape 263/270 of the vendored W3C csv2rdf
                 fixtures expect) or "minimal" (bare cell triples).
         "base": base IRI for resolving the metadata's `url` and any
                 aboutUrl/propertyUrl/valueUrl templates
                 (default "file:///").
         "url":  the tabular file's own URL, used when metadataJson has
                 no `url` of its own; cell predicates default to
                 `<tableUrl>#<colName>` so this shapes every emitted
                 predicate IRI (default "table.csv", i.e.
                 file:///table.csv under the default base).
       Decoding is CSVW_Metadata.csvw_decode_metadata_text; conversion
       is CSVW_Conversion.csvw_convert_document_standard/_minimal --
       the same call path bin/csvw-runner/csvw_runner.ml drives.
       Scope limitation (documented, not silent -- mirrors rmlMap's
       one-source cut): every table in a multi-table `tables` group
       reads the SAME csvText; per-table separate CSV sources need the
       runner's file-per-table driver. Datatype `format` facets,
       list-valued (`separator`) cells, and full inherited-property
       propagation are not yet implemented -- see
       docs/designissues/2026-07-05-csvw-program-plan.md's stage table
       for measured coverage (19 pass, 251 fail of 270 vendored
       csv2rdf fixtures at this stage).

   Rich types (RDF/JS terms, Dataset objects, Maps of bindings) live on
   the JavaScript side (npm/factoidal/rdfjs.js); the js_of_ocaml string
   bridge is the stable part, so the ABI stays strings + JSON.

   Build wiring: see bin/npm-entry/README.md — the `js` step of
   formal/fstar/build-ocaml.sh compiles this file (after FSTAR_MODULES,
   with -package js_of_ocaml) into npm_entry.byte, then js_of_ocaml /
   wasm_of_ocaml emit docs/fstar-extracted/factoidal-npm-entry{.js,.wasm.js}. *)

open RDF_Graph_Executable
open SPARQL11_Algebra

module Js = Js_of_ocaml.Js

let abi_version = "1"

(* Issue #275 (rule #11 ASSUME-IO): explicitly realise the JSON-LD
   documentLoader seam as an honest "no remote loading" for this entry
   point -- same choice bin/factoidal-cli, bin/factoidal-http, and
   bin/factoidal-dump-nq each make explicitly (the ref cell's own
   default is the same `fun _ -> None`; this line exists for rule-#11
   auditability, not because behavior would differ without it). *)
let () = JSONLD_Loader.jsonld_loader_register (fun _ -> FStar_Pervasives_Native.None)

(* ---------------------------------------------------------------------
   JSON envelope helpers. Escaping delegates to the F*-extracted
   SPARQL_JSON_Escape so the byte-level JSON rules stay verified.
   --------------------------------------------------------------------- *)

let jstr (s : string) : string =
  "\"" ^ SPARQL_JSON_Escape.json_escape s ^ "\""

let err_json (msg : string) : string =
  "{\"ok\":false,\"error\":" ^ jstr msg ^ "}"

let ok_nquads_json (nq : string) : string =
  "{\"ok\":true,\"nquads\":" ^ jstr nq ^ "}"

let ok_turtle_json (ttl : string) : string =
  "{\"ok\":true,\"turtle\":" ^ jstr ttl ^ "}"

(* Run a thunk, mapping any exception into the error envelope. *)
let guarded (f : unit -> string) : string =
  try f () with
  | e -> err_json (Printexc.to_string e)

(* ---------------------------------------------------------------------
   Parsing (dataset handle = N-Quads text)
   --------------------------------------------------------------------- *)

(* Per-document blank-node scope counter. RDF 1.1 scopes _:labels to the
   document; each parse call is one document. The renaming itself is the
   F* function RDF_Dataset_Merge.rename_dataset_bnodes — this counter is
   only the per-call salt (same pattern as factoidal_cli.ml). *)
let bnode_scope_counter = ref 0

let scope_dataset_bnodes ds =
  let n = !bnode_scope_counter in
  incr bnode_scope_counter;
  RDF_Dataset_Merge.rename_dataset_bnodes (Printf.sprintf "d%d_" n) ds

let dataset_of_nquads (nq : string) : rdf_dataset =
  Parser_NQuads.parse_nquads nq

let parse_text_to_dataset (text : string) (format_tag : string)
    (base_iri : string) : (rdf_dataset, string) result =
  let base = if base_iri = "" then None else Some base_iri in
  let fmt =
    if format_tag = "" then Some RDF_Format.Turtle
    else
      match RDF_Format.format_of_string format_tag with
      | FStar_Pervasives_Native.Some f -> Some f
      | FStar_Pervasives_Native.None -> None
  in
  match fmt with
  | None -> Error (Printf.sprintf "unknown format tag '%s'" format_tag)
  | Some fmt ->
    let ds =
      match fmt with
      | RDF_Format.NQuads -> Parser_NQuads.parse_nquads text
      | RDF_Format.TriG ->
        (match base with
         | Some b -> Parser_TriG.parse_trig_with_base_lenient text b
         | None -> Parser_TriG.parse_trig_lenient text)
      | RDF_Format.NT ->
        { ds_default = Parser_NTriples.parse_ntriples text; ds_named = [] }
      | RDF_Format.Turtle ->
        let triples =
          match base with
          | Some b -> Parser_Turtle.parse_turtle_with_base text b
          | None -> Parser_Turtle.parse_turtle text
        in
        { ds_default = triples; ds_named = [] }
      | RDF_Format.RDFXML ->
        let triples =
          match base with
          | Some b -> Parser_RDFXML.parse_rdfxml_with_base b text
          | None -> Parser_RDFXML.parse_rdfxml text
        in
        { ds_default = triples; ds_named = [] }
      | RDF_Format.JSONLD ->
        (* Parser_JSONLD.parse_jsonld returns a whole rdf_dataset
           (JSON-LD @graph can produce named graphs), unlike the
           triple-list branches above. Remote contexts / "@import" fail
           honestly (no loader registered -- see jsonld_loader_register
           above); this was previously an unhandled match case (a
           latent Match_failure any caller reaching this branch would
           have hit -- see jsonldToRdf's ABI doc comment). *)
        let fs_base =
          match base with
          | Some b -> FStar_Pervasives_Native.Some b
          | None -> FStar_Pervasives_Native.None
        in
        (match Parser_JSONLD.parse_jsonld text fs_base
                 FStar_Pervasives_Native.None FStar_Pervasives_Native.None
                 FStar_Pervasives_Native.None with
         | FStar_Pervasives_Native.Some ds -> ds
         | FStar_Pervasives_Native.None ->
           failwith ("invalid or unsupported JSON-LD (parse error, or a " ^
                     "feature needing a remote-context loader this entry " ^
                     "does not have)"))
    in
    Ok (scope_dataset_bnodes ds)

let parse_to_dataset_json (text : string) (format_tag : string)
    (base_iri : string) : string =
  guarded (fun () ->
    match parse_text_to_dataset text format_tag base_iri with
    | Error msg -> err_json msg
    | Ok ds ->
      let nq = RDF_Canonical.canonical_nquads ds in
      let count = Z.to_string (SPARQL11_Algebra.dataset_triple_count ds) in
      "{\"ok\":true,\"count\":" ^ count ^ ",\"nquads\":" ^ jstr nq ^ "}")

(* ---------------------------------------------------------------------
   SPARQL results JSON (SELECT) — same rendering as factoidal_cli.ml's
   print_results_json, but into a Buffer instead of stdout. Term-level
   JSON comes from the F*-extracted SPARQL_Protocol.json_term.
   --------------------------------------------------------------------- *)

let srj_of_rows (vars : string list)
    (rows : (string * rdf_term) list list) : string =
  let buf = Buffer.create 1024 in
  Buffer.add_string buf "{\"head\":{\"vars\":[";
  List.iteri
    (fun i v ->
       if i > 0 then Buffer.add_char buf ',';
       Buffer.add_string buf (jstr v))
    vars;
  Buffer.add_string buf "]},\"results\":{\"bindings\":[";
  List.iteri
    (fun i row ->
       if i > 0 then Buffer.add_char buf ',';
       Buffer.add_char buf '{';
       let first = ref true in
       List.iter
         (fun v ->
            match List.assoc_opt v row with
            | None -> ()
            | Some t ->
              if !first then first := false else Buffer.add_char buf ',';
              Buffer.add_string buf (jstr v);
              Buffer.add_char buf ':';
              Buffer.add_string buf (SPARQL_Protocol.json_term t))
         vars;
       Buffer.add_char buf '}')
    rows;
  Buffer.add_string buf "]}}";
  Buffer.contents buf

(* Variable list: declared projection for SELECT ?x ?y, first-seen order
   of bound vars for SELECT * (same logic as factoidal_cli.ml). *)
let vars_of_query_or_rows (q : query)
    (rows : (string * rdf_term) list list) : string list =
  match q.q_form with
  | QF_Select (Select_Vars items) ->
    List.filter_map
      (fun item ->
         match item with
         | SI_Var v -> Some v
         | SI_Expr (_, v) -> Some v)
      items
  | _ ->
    let seen = Hashtbl.create 16 in
    List.concat_map
      (fun row ->
         List.filter_map
           (fun (v, _) ->
              if Hashtbl.mem seen v then None
              else (Hashtbl.add seen v (); Some v))
           row)
      rows

(* ---------------------------------------------------------------------
   Query evaluation over the N-Quads dataset handle
   --------------------------------------------------------------------- *)

let construct_triples_to_ntriples (triples : triple list) : string =
  let buf = Buffer.create 1024 in
  List.iter
    (fun t ->
       Buffer.add_string buf
         (RDF_NQuads_Serialize.nq_line_for_triple_default_graph t))
    triples;
  Buffer.contents buf

let query_dataset (nq : string) (sparql : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    match SPARQL11_Parser.parse_sparql sparql with
    | SPARQL11_Parser.ParseErr msg -> err_json ("SPARQL parse error: " ^ msg)
    | SPARQL11_Parser.ParseOk (q, _) ->
      let q = OWL_QueryRewrite.rewrite_query q in
      let dsb () = SPARQL11_Store.indexed_dataset_backend ds in
      (match q.q_form with
       | QF_Ask ->
         let b =
           match SPARQL11_Store.run_ask_query_backend_dataset q (dsb ()) with
           | FStar_Pervasives_Native.Some b -> b
           | FStar_Pervasives_Native.None ->
             SPARQL11_Algebra.eval_ask_query q ds.ds_default ds
         in
         "{\"ok\":true,\"kind\":\"ask\",\"boolean\":"
         ^ (if b then "true" else "false") ^ "}"
       | QF_Select _ ->
         let rows =
           match SPARQL11_Store.run_select_query_backend_dataset q (dsb ()) with
           | FStar_Pervasives_Native.Some rows -> rows
           | FStar_Pervasives_Native.None ->
             SPARQL11_Algebra.eval_select_query q ds.ds_default ds
         in
         let vars = vars_of_query_or_rows q rows in
         "{\"ok\":true,\"kind\":\"select\",\"srj\":"
         ^ srj_of_rows vars rows ^ "}"
       | QF_Construct _ ->
         let triples =
           SPARQL11_Algebra.eval_construct_query q ds.ds_default ds
         in
         "{\"ok\":true,\"kind\":\"construct\",\"nquads\":"
         ^ jstr (construct_triples_to_ntriples triples) ^ "}"
       | QF_Describe _ ->
         err_json "DESCRIBE is not supported by the npm entry yet"))

let ask_dataset (nq : string) (sparql : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    match SPARQL11_Parser.parse_sparql sparql with
    | SPARQL11_Parser.ParseErr msg -> err_json ("SPARQL parse error: " ^ msg)
    | SPARQL11_Parser.ParseOk (q, _) ->
      (match q.q_form with
       | QF_Ask ->
         let q = OWL_QueryRewrite.rewrite_query q in
         let b =
           match
             SPARQL11_Store.run_ask_query_backend_dataset q
               (SPARQL11_Store.indexed_dataset_backend ds)
           with
           | FStar_Pervasives_Native.Some b -> b
           | FStar_Pervasives_Native.None ->
             SPARQL11_Algebra.eval_ask_query q ds.ds_default ds
         in
         "{\"ok\":true,\"boolean\":" ^ (if b then "true" else "false") ^ "}"
       | _ -> err_json "askDataset: query is not an ASK query"))

let update_dataset (nq : string) (update_text : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    match SPARQL11_Parser.parse_sparql_update update_text with
    | SPARQL11_Parser.ParseErr msg ->
      err_json ("SPARQL update parse error: " ^ msg)
    | SPARQL11_Parser.ParseOk (u, _) ->
      let ds' = SPARQL11_Algebra.apply_update ds u in
      ok_nquads_json (RDF_Canonical.canonical_nquads ds'))

let serialize_nquads (nq : string) : string =
  guarded (fun () ->
    ok_nquads_json (RDF_Canonical.canonical_nquads (dataset_of_nquads nq)))

let canonicalize_to_nquads (nq : string) : string =
  guarded (fun () ->
    ok_nquads_json (RDF_Canonical.canonicalize_to_nquads (dataset_of_nquads nq)))

(* RDF_Turtle_Serialize.turtle_of_graph_auto takes a single rdf_graph,
   not a dataset — named graphs are flattened into the default graph
   for this pretty-print path (the fidelity-preserving path is
   serializeNQuads / canonicalizeToNQuads, which keep graph structure). *)
let serialize_turtle (nq : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    let g = ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named in
    ok_turtle_json (RDF_Turtle_Serialize.turtle_of_graph_auto g))

(* ---------------------------------------------------------------------
   RIF Core (rule #11 consumer -- exports only). All semantics come
   from F*-extracted modules already on the link line
   (formal/fstar/build-ocaml.sh's FSTAR_MODULES): RIF_Core_Eval.fixpoint
   / one_round (the same verified functions the RIF.Core.Eval.fst smoke
   test and RIF_Core_Tests.saturate_with_program use), Parser_RIFXML.
   parse_rif_program for the XML -> rif_program parse. Body-to-BGP
   translation (RIF_Core_Translation) happens inside RIF_Core_Eval.
   fire_rule already, so it is not called directly here.
   --------------------------------------------------------------------- *)

(* Real-world RIF-XML documents (every fixture in
   third_party/testing/rif/tc/, per the RIF Core spec's own convention)
   declare a DOCTYPE with internal-subset entities (&rif;/&xs;/&rdf;)
   that expand to the RIF/XSD/RDF namespace IRIs; Parser_RIFXML.
   parse_rif_program is a plain XML parser with no DTD/entity-expansion
   step (by design -- that is XML infrastructure, not RIF Core
   semantics), so it cannot see through them unless this is done first.
   Ported verbatim from bin/w3c-runner/w3c_runner.ml's rif_xml_preprocess
   (the exact same problem, same fix) so callers can hand this ABI a
   real, unmodified RIF-XML document instead of hand-stripping the
   DOCTYPE themselves. Consumer-side text preprocessing, not RIF
   semantics -- rule #11 stays satisfied. *)
let rif_xml_preprocess (s : string) : string =
  let drop_doctype s =
    match Str.search_forward (Str.regexp_string "<!DOCTYPE") s 0 with
    | exception Not_found -> s
    | start ->
      let close_with_subset =
        try Some (Str.search_forward (Str.regexp_string "]>") s start)
        with Not_found -> None in
      let close_idx =
        match close_with_subset with
        | Some i -> i + 2
        | None ->
          (try (Str.search_forward (Str.regexp_string ">") s start) + 1
           with Not_found -> String.length s)
      in
      let pre = String.sub s 0 start in
      let post = String.sub s close_idx (String.length s - close_idx) in
      pre ^ post
  in
  let inline_entities s =
    s
    |> Str.global_replace (Str.regexp_string "&rif;")
         "http://www.w3.org/2007/rif#"
    |> Str.global_replace (Str.regexp_string "&xs;")
         "http://www.w3.org/2001/XMLSchema#"
    |> Str.global_replace (Str.regexp_string "&rdf;")
         "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  in
  s |> drop_doctype |> inline_entities

let rif_graph_to_nquads (g : triple list) : string =
  let buf = Buffer.create 1024 in
  List.iter
    (fun t ->
       Buffer.add_string buf
         (RDF_NQuads_Serialize.nq_line_for_triple_default_graph t))
    g;
  Buffer.contents buf

(* Telemetry only -- NOT part of the saturation answer. Counts rounds
   to fixpoint by driving RIF_Core_Eval.one_round directly: the exact
   verified primitive that RIF_Core_Eval.fixpoint composes internally
   (see RIF.Core.Eval.fst section 5). The saturated graph reported to
   the caller always comes from calling RIF_Core_Eval.fixpoint itself,
   below; this loop's own graph output is discarded once the round
   count is known. `cap` is a defensive bound so a pathological input
   cannot spin forever counting rounds (fixpoint's own fuel parameter
   is the real termination guarantee for the answer). *)
let rif_rounds_to_fixpoint g program cap =
  let rec go g n =
    if n >= cap then n
    else
      let g', changed = RIF_Core_Eval.one_round g program in
      if changed then go g' (n + 1) else n
  in
  go g 0

let rif_result_json
    (input : triple list) (saturated : triple list)
    (rounds : int) (fuel : int) (engine_ms : float) : string =
  let derived = List.length saturated - List.length input in
  "{\"ok\":true"
  ^ ",\"inputNquads\":" ^ jstr (rif_graph_to_nquads input)
  ^ ",\"saturatedNquads\":" ^ jstr (rif_graph_to_nquads saturated)
  ^ ",\"inputCount\":" ^ string_of_int (List.length input)
  ^ ",\"derivedCount\":" ^ string_of_int derived
  ^ ",\"rounds\":" ^ string_of_int rounds
  ^ ",\"fuel\":" ^ string_of_int fuel
  ^ ",\"engineMs\":" ^ Printf.sprintf "%.3f" engine_ms
  ^ "}"

(* rifSmoke() -- live re-run of RIF.Core.Eval.fst's own smoke program.
   No user input; a fixed capability probe demonstrating the bundle
   actually calls the verified engine rather than replaying a canned
   value baked in at F* compile time. *)
let rif_smoke_json () : string =
  guarded (fun () ->
    let input = RIF_Core_Eval.smoke_input_graph in
    let program = RIF_Core_Eval.smoke_program in
    let fuel = 8 in
    let t0 = Sys.time () in
    let saturated = RIF_Core_Eval.fixpoint input program (Z.of_int fuel) in
    let t1 = Sys.time () in
    let rounds = rif_rounds_to_fixpoint input program 64 in
    rif_result_json input saturated rounds fuel ((t1 -. t0) *. 1000.0))

(* rifEval(rifXml, dataNQuads) -- general entry point: parse arbitrary
   RIF-XML rules, saturate against an arbitrary N-Quads premise graph
   (default graph only -- RIF Core has no named-graph notion).
   rif_xml_preprocess strips any DOCTYPE + inlines &rif;/&xs;/&rdf;
   entities first (a no-op on a document that has none), so this
   accepts real vendored RIF-XML unmodified, not just a hand-stripped
   variant. *)
let rif_eval_json (rif_xml : string) (data_nquads : string) : string =
  guarded (fun () ->
    let rif_xml = rif_xml_preprocess rif_xml in
    let ds = dataset_of_nquads data_nquads in
    let premise = ds.ds_default in
    match Parser_RIFXML.parse_rif_program rif_xml with
    | FStar_Pervasives_Native.None ->
      err_json
        "RIF-XML parse error (Parser_RIFXML.parse_rif_program returned None)"
    | FStar_Pervasives_Native.Some program ->
      let fuel = 100 in
      let t0 = Sys.time () in
      let saturated = RIF_Core_Eval.fixpoint premise program (Z.of_int fuel) in
      let t1 = Sys.time () in
      let rounds = rif_rounds_to_fixpoint premise program 256 in
      rif_result_json premise saturated rounds fuel ((t1 -. t0) *. 1000.0))

(* ---------------------------------------------------------------------
   JSON-LD (rule #11 consumer -- exports only). Semantics come entirely
   from Parser_JSONLD.parse_jsonld (+ JSONLD_Context / JSONLD_Expand it
   calls internally); this wraps it with the same per-document
   blank-node scoping parseToDatasetJson applies and an options-JSON
   ABI for the parameters parseToDatasetJson's 3-string-arg shape has
   no room for. See jsonldToRdf's doc comment (file header) for the
   optionsJson field names.
   --------------------------------------------------------------------- *)

let jsonld_to_rdf_json (jsonld_text : string) (options_json : string) : string =
  guarded (fun () ->
    let root_opt =
      if options_json = "" then FStar_Pervasives_Native.None
      else Parser_JSON.parse_json options_json
    in
    let field key =
      match root_opt with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some root -> Parser_JSON.json_get_string key root
    in
    let base = field "base" in
    let rdf_direction = field "rdfDirection" in
    let expand_context = field "expandContext" in
    let processing_mode = field "processingMode" in
    match Parser_JSONLD.parse_jsonld jsonld_text base rdf_direction
            expand_context processing_mode with
    | FStar_Pervasives_Native.None ->
      err_json ("invalid or unsupported JSON-LD (parse error, or a " ^
                "feature needing a remote-context loader this entry " ^
                "does not have)")
    | FStar_Pervasives_Native.Some ds ->
      ok_nquads_json (RDF_Canonical.canonical_nquads (scope_dataset_bnodes ds)))

(* ---------------------------------------------------------------------
   SHACL (rule #11 consumer -- exports only). All shape parsing, target
   computation, constraint evaluation and report serialization live in
   formal/fstar/SHACL.Validation.fst -- the same call path
   bin/shacl-runner/shacl_runner.ml drives (parse_shape_from_graph +
   validate + validation_report_to_graph).
   --------------------------------------------------------------------- *)

(* dataNQuads/shapesNQuads are dataset handles (same convention as
   queryDataset/canonicalizeToNQuads/etc.) -- the default graph's
   triples only (SHACL operates over a plain rdf_graph; a caller with
   named-graph data/shapes should pick the graph it means before
   calling, same documented scope cut fn.js's entail() already makes
   for RDFS/OWL-RL closure). *)
let shacl_validate_json (data_nquads : string) (shapes_nquads : string) : string =
  guarded (fun () ->
    let data_graph = (dataset_of_nquads data_nquads).ds_default in
    let shapes_graph = (dataset_of_nquads shapes_nquads).ds_default in
    let sg = SHACL_Validation.parse_shape_from_graph shapes_graph in
    let report = SHACL_Validation.validate data_graph shapes_graph sg in
    let report_graph = SHACL_Validation.validation_report_to_graph report in
    "{\"ok\":true,\"conforms\":"
    ^ (if report.SHACL_Validation.conforms then "true" else "false")
    ^ ",\"reportNquads\":" ^ jstr (construct_triples_to_ntriples report_graph)
    ^ "}")

(* ---------------------------------------------------------------------
   ShEx (rule #11 consumer -- exports only). ShExJ decoding lives in
   formal/fstar/ShEx.Schema.fst; NodeConstraint dispatch and
   triple-expression matching live in formal/fstar/ShEx.Validation.fst
   -- the same call path bin/shex-runner/shex_runner.ml drives
   (decode_shex_schema + validate_focus).
   --------------------------------------------------------------------- *)

(* A focus/shape-label string is an IRI, or "_:label" for a blank node
   -- same convention shex_runner.ml's shape_label_str /
   term_of_node_string helpers use, so a caller round-tripping a
   shex_runner-style ShapeMap entry gets the identical term. *)
let term_of_focus_string (s : string) : rdf_term =
  if String.length s >= 2 && String.sub s 0 2 = "_:"
  then T_BNode (String.sub s 2 (String.length s - 2))
  else T_IRI s

(* ShExJ-vs-ShExC schema-text dispatch (Stage 9, Parser.ShExC.fst): the
   first non-whitespace character of a ShExJ document is always '{' (a
   JSON object); ShExC schemas never start that way (a ShExC document
   starts with a directive keyword, a shape label, or START). Both
   decoders live in F* (ShEx_Schema.decode_shex_schema / Parser_ShExC.
   parse_shexc_schema) -- this is pure I/O-adjacent dispatch, not
   semantic logic, per iron rule #11. Documented in npm/factoidal's
   shexValidate jsdoc and README as the sniffing rule callers can rely
   on. *)
let first_non_ws_char (s : string) : char option =
  let len = String.length s in
  let rec go i =
    if i >= len then None
    else match s.[i] with
      | ' ' | '\t' | '\n' | '\r' -> go (i + 1)
      | c -> Some c
  in
  go 0

let decode_shex_schema_text (schema_text : string) : ShEx_Schema.shex_schema FStar_Pervasives_Native.option =
  match first_non_ws_char schema_text with
  | Some '{' -> ShEx_Schema.decode_shex_schema schema_text ""
  | _ -> Parser_ShExC.parse_shexc_schema schema_text ""

(* dataNQuads is a dataset handle (see shaclValidate's comment above for
   the default-graph-only scope cut this shares). schemaText accepts
   EITHER ShExJ (JSON) or ShExC (compact syntax) text -- see
   decode_shex_schema_text's dispatch rule above. *)
let shex_validate_json (data_nquads : string) (schema_text : string)
    (focus : string) (shape_label : string) : string =
  guarded (fun () ->
    match decode_shex_schema_text schema_text with
    | FStar_Pervasives_Native.None ->
      err_json "could not decode schema (tried ShExJ then ShExC)"
    | FStar_Pervasives_Native.Some schema ->
      let data_graph = (dataset_of_nquads data_nquads).ds_default in
      let focus_term = term_of_focus_string focus in
      let shape_id =
        if shape_label = "" then FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.Some shape_label
      in
      (match ShEx_Validation.validate_focus schema shape_id focus_term data_graph with
       | FStar_Pervasives_Native.None ->
         "{\"ok\":true,\"verdict\":null,\"deferred\":true}"
       | FStar_Pervasives_Native.Some b ->
         "{\"ok\":true,\"verdict\":" ^ (if b then "true" else "false")
         ^ ",\"deferred\":false}"))

(* ---------------------------------------------------------------------
   RDFS / OWL-RL entailment closure (rule #11 consumer -- exports
   only). Both closures live in formal/fstar/RDF.Graph.Executable.fst;
   this is the same fuel=100 call bin/w3c-runner/w3c_runner.ml makes
   for RDFS/OWL-RL entailment-regime tests.
   --------------------------------------------------------------------- *)

(* dataNQuads is a dataset handle; only the default graph is closed
   over (see shaclValidate's comment above). *)
let owl_closure_json (data_nquads : string) (mode : string) : string =
  guarded (fun () ->
    let graph = (dataset_of_nquads data_nquads).ds_default in
    let fuel = Z.of_int 100 in
    match mode with
    | "RDFS" | "rdfs" ->
      ok_nquads_json (construct_triples_to_ntriples
        (RDF_Graph_Executable.rdfs_closure_with_reflexivity graph fuel))
    | "OWL-RL" | "owl-rl" | "owl_rl" ->
      ok_nquads_json (construct_triples_to_ntriples
        (RDF_Graph_Executable.owl_rl_closure_with_reflexivity graph fuel))
    | _ ->
      err_json (Printf.sprintf
        "owlClosure: unknown mode '%s' (expected 'RDFS' or 'OWL-RL')" mode))

(* ---------------------------------------------------------------------
   RML (rule #11 consumer -- exports only). Mapping-document decoding
   lives in formal/fstar/RML.Mapping.fst, logical-source iteration in
   formal/fstar/RML.Sources.fst, term-map/triples-map evaluation in
   formal/fstar/RML.Eval.fst -- the eval_triples_map_json/_csv
   convenience wrappers bin/rml-runner/rml_runner.ml's eval_document
   also composes, minus that driver's multi-source join-lookup table
   (see rmlMap's doc comment, file header, for the resulting scope cut).
   --------------------------------------------------------------------- *)

(* mappingNQuads is a dataset handle for the RML mapping GRAPH (the
   TriplesMap/LogicalSource/etc. RDF description) -- default graph
   only, same convention as shaclValidate above. sourceData is the RML
   logical source's raw data (JSON or CSV text, per sourceKind), not
   RDF -- passed straight through to RML.Sources' iterators. *)
let rml_map_json (mapping_nquads : string) (source_data : string)
    (source_kind : string) : string =
  guarded (fun () ->
    match source_kind with
    | "json" | "csv" ->
      let mapping_graph = (dataset_of_nquads mapping_nquads).ds_default in
      let doc = RML_Mapping.decode_mapping_document mapping_graph in
      let eval_one (tmap : RML_Mapping.triples_map) : RML_Eval.placed_triple list =
        match source_kind with
        | "json" ->
          (match Parser_JSON.parse_json source_data with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some root ->
             RML_Eval.eval_triples_map_json tmap root FStar_Pervasives_Native.None)
        | _ (* "csv" *) ->
          RML_Eval.eval_triples_map_csv tmap source_data FStar_Pervasives_Native.None
      in
      let all_pts = List.concat_map eval_one doc.RML_Mapping.md_triples_maps in
      let ds = RML_Eval.place_into_dataset RDF_Graph_Executable.empty_dataset all_pts in
      ok_nquads_json (RDF_Canonical.canonical_nquads ds)
    | _ ->
      err_json (Printf.sprintf
        "rmlMap: unknown sourceKind '%s' (expected 'json' or 'csv')" source_kind))

(* ---------------------------------------------------------------------
   CSVW csv2rdf (rule #11 consumer -- exports only). Metadata-document
   decoding lives in formal/fstar/CSVW.Metadata.fst, URI-template
   expansion in formal/fstar/CSVW.URITemplate.fst, the conversion
   algorithm (standard + minimal modes) in
   formal/fstar/CSVW.Conversion.fst, CSV tokenization in
   formal/fstar/RML.Sources.fst -- the same call path
   bin/csvw-runner/csvw_runner.ml drives. See csvwToRdf's doc comment
   (file header) for the optionsJson fields and the one-source scope
   cut this shares with rmlMap.
   --------------------------------------------------------------------- *)

let csvw_to_rdf_json (csv_text : string) (metadata_json : string)
    (options_json : string) : string =
  guarded (fun () ->
    let root_opt =
      if options_json = "" then FStar_Pervasives_Native.None
      else Parser_JSON.parse_json options_json
    in
    let field key dflt =
      match root_opt with
      | FStar_Pervasives_Native.None -> dflt
      | FStar_Pervasives_Native.Some root ->
        (match Parser_JSON.json_get_string key root with
         | FStar_Pervasives_Native.Some s -> s
         | FStar_Pervasives_Native.None -> dflt)
    in
    let mode = field "mode" "standard" in
    let base_iri = field "base" "file:///" in
    let fallback_url = field "url" "table.csv" in
    match mode with
    | "standard" | "minimal" ->
      let tables_opt =
        if metadata_json = "" then
          FStar_Pervasives_Native.Some [ CSVW_Conversion.csvw_no_metadata_table ]
        else
          (match CSVW_Metadata.csvw_decode_metadata_text metadata_json with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_Table t) ->
             FStar_Pervasives_Native.Some [ t ]
           | FStar_Pervasives_Native.Some (CSVW_Metadata.CSVW_TableGroup ts) ->
             FStar_Pervasives_Native.Some ts)
      in
      (match tables_opt with
       | FStar_Pervasives_Native.None ->
         err_json "csvwToRdf: metadataJson is not a decodable CSVW metadata document"
       | FStar_Pervasives_Native.Some tables ->
         let rows = RML_Sources.csv_parse_rows csv_text in
         let tables_with_rows =
           List.map (fun t -> (t, fallback_url, rows)) tables in
         let triples =
           if mode = "minimal"
           then CSVW_Conversion.csvw_convert_document_minimal base_iri tables_with_rows
           else CSVW_Conversion.csvw_convert_document_standard base_iri tables_with_rows
         in
         let ds : RDF_Graph_Executable.rdf_dataset =
           { RDF_Graph_Executable.ds_default = triples; ds_named = [] } in
         ok_nquads_json (RDF_Canonical.canonical_nquads (scope_dataset_bnodes ds)))
    | _ ->
      err_json (Printf.sprintf
        "csvwToRdf: unknown mode '%s' (expected 'standard' or 'minimal')" mode))

(* ---------------------------------------------------------------------
   Durable-UPDATE browser persistence (rule #11 consumer -- exports
   only). Issue #282's browser realisation of the five delta-log I/O
   primitives; see docs/designissues/2026-07-06-browser-persistence.md
   for the v1 architecture decision (IndexedDB, not OPFS -- OPFS sync
   access handles are worker-only and this entry point runs on the
   main thread inside a hub cell). Every semantic/byte-layout decision
   below is F*: RDF_Store_Columnar_DeltaLog.{serialize_delta_batch,
   parse_delta_batch} (the verified, checksummed, self-framed delta-
   batch format the native on-disk log already uses) and
   RDF_Store_Columnar_DeltaMerge.{update_ops_to_delta_entries,
   apply_entries_ref, delta_batches_named_graphs} (the same verified
   translator/merge functions bin/factoidal-http/factoidal_http.ml's
   --rw commit path drives natively). This OCaml layer moves opaque
   bytes and dispatches per-graph loops only -- no RDF/SPARQL
   semantics of its own.
   --------------------------------------------------------------------- *)

module DLog = RDF_Store_Columnar_DeltaLog
module DMerge = RDF_Store_Columnar_DeltaMerge

(* Wire transport: RDF_Bytes.bytes is `int list` (each element 0..255 --
   FStar.Char.char extracts to plain OCaml int, see FStar_Char.ml).
   Hex-encode/decode directly against that int list rather than routing
   through RDF_Bytes.bytes_to_string/bytes_of_string, which round-trip
   through BatUTF8 (FStar_String.ml) and can raise BatUChar.Out_of_range
   on an arbitrary byte >= 128 that doesn't happen to start a valid
   UTF-8 sequence -- the exact trap bin/delta-log-probe/probe.ml's own
   header comment documents for this same byte type. Hex sidesteps any
   string-encoding question entirely; this is ABI wire-transport
   encoding at a bin/<consumer> boundary, not delta-log byte-LAYOUT
   logic (rule #11 scopes the latter to F*, not the former). *)
let hex_of_bytes (bs : RDF_Bytes.bytes) : string =
  let buf = Buffer.create (List.length bs * 2) in
  List.iter (fun b -> Buffer.add_string buf (Printf.sprintf "%02x" b)) bs;
  Buffer.contents buf

let bytes_of_hex (s : string) : RDF_Bytes.bytes option =
  let n = String.length s in
  if n mod 2 <> 0 then None
  else
    let rec go i acc =
      if i >= n then Some (List.rev acc)
      else
        match (try Some (int_of_string ("0x" ^ String.sub s i 2)) with _ -> None) with
        | None -> None
        | Some b -> go (i + 2) (b :: acc)
    in
    go 0 []

(* Per-call request salt for the same insert-data-same-bnode uniqueness
   discipline SPARQL11_Algebra's apply_insert_data/apply_delete_data
   already use (mirrors bnode_scope_counter above and factoidal-http's
   own `next_seq`/`Unix.gettimeofday` salt -- this entry point has no
   process-uptime clock worth reading, so a plain counter is the
   simplest per-call-unique salt available here). *)
let delta_salt_counter = ref 0
let next_delta_salt () =
  let n = !delta_salt_counter in
  incr delta_salt_counter;
  Printf.sprintf "browser_%d" n

let delta_batch_to_hex (sparql_update : string) (seq : string) (epoch : string) : string =
  guarded (fun () ->
    match SPARQL11_Parser.parse_sparql_update sparql_update with
    | SPARQL11_Parser.ParseErr msg -> err_json ("SPARQL update parse error: " ^ msg)
    | SPARQL11_Parser.ParseOk (u, _rest) ->
      let salt = next_delta_salt () in
      (match DMerge.update_ops_to_delta_entries salt u.u_ops with
       | FStar_Pervasives_Native.None ->
         err_json
           ("unsupported update op for the delta log (supported: INSERT " ^
            "DATA, DELETE DATA, CLEAR, DROP, CREATE; DELETE/INSERT WHERE, " ^
            "COPY, MOVE, ADD are not yet translatable)")
       | FStar_Pervasives_Native.Some entries ->
         let batch : DLog.delta_batch =
           { DLog.db_seq = Z.of_string seq; DLog.db_epoch = Z.of_string epoch;
             DLog.db_ops = entries }
         in
         let hex = hex_of_bytes (DLog.serialize_delta_batch batch) in
         let op_count = string_of_int (List.length entries) in
         "{\"ok\":true,\"hex\":" ^ jstr hex ^ ",\"opCount\":" ^ op_count ^ "}"))

let delta_merge_apply_browser (nquads : string) (hex_blobs : string) : string =
  guarded (fun () ->
    let ds0 = dataset_of_nquads nquads in
    let lines =
      String.split_on_char '\n' hex_blobs
      |> List.filter (fun s -> String.length (String.trim s) > 0)
    in
    (* Each line independently parsed; a torn/corrupt blob is skipped,
       never partially decoded (see the ABI doc comment above). *)
    let batches =
      List.filter_map
        (fun line ->
           match bytes_of_hex (String.trim line) with
           | None -> None
           | Some bs ->
             (match DLog.parse_delta_batch bs with
              | FStar_Pervasives_Native.Some (b, _leftover) -> Some b
              | FStar_Pervasives_Native.None -> None))
        lines
    in
    let sorted =
      List.sort (fun a b -> Z.compare a.DLog.db_seq b.DLog.db_seq) batches
    in
    let all_ops = List.concat_map (fun b -> b.DLog.db_ops) sorted in
    let existing_names = List.map (fun ng -> ng.ng_name) ds0.ds_named in
    let delta_names = DMerge.delta_batches_named_graphs sorted in
    let all_names = List.sort_uniq compare (existing_names @ delta_names) in
    let base_graph_for name =
      match List.find_opt (fun ng -> ng.ng_name = name) ds0.ds_named with
      | Some ng -> ng.ng_graph
      | None -> []
    in
    let new_default =
      DMerge.apply_entries_ref FStar_Pervasives_Native.None ds0.ds_default all_ops
    in
    let new_named =
      List.map
        (fun name ->
           { ng_name = name;
             ng_graph =
               DMerge.apply_entries_ref (FStar_Pervasives_Native.Some name)
                 (base_graph_for name) all_ops })
        all_names
    in
    let ds' : rdf_dataset = { ds_default = new_default; ds_named = new_named } in
    ok_nquads_json (RDF_Canonical.canonical_nquads ds'))

(* ---------------------------------------------------------------------
   In-memory COTTAS bytes store (rule #11 consumer -- exports only;
   docs/designissues/2026-07-06-inmemory-bytes-store.md, stage 5 "the
   browser call site"). Read path: Parquet_Footer.register_memory_buffer
   (experimental_ocaml_glue/parquet_footer_zz_register_memory_buffer.sh)
   + RDF.CottasStore.cottas_ondisk_open (both already linked into every
   js_of_ocaml/wasm_of_ocaml bundle this file builds into -- see
   formal/fstar/build-ocaml.sh's FSTAR_MODULES list, which has carried
   RDF_CottasStore*/Parquet_Footer/RDF_Store_Capabilities_Cottas since
   Phase 2, 2026-04-20) + SPARQL11_Store.cottas_ondisk_dataset_backend /
   run_select_query_backend_dataset / run_ask_query_backend_dataset --
   the EXACT same reader the native `--data-cottas`/`--data-cottas-mem`
   CLI paths use (bin/factoidal-cli/factoidal_cli.ml's
   open_cottas_ondisk_store / build_dataset_backend). No new decode or
   query logic lives here: this is the browser call site the design
   doc's stage list asked for, not a new engine.

   Write path: RDF.CottasStore.BaseWriter.serialize_cottas_v2 is a pure
   `Tot` function (no I/O, no assume val) already linked into this same
   bundle -- toCottas below is argv-free orchestration around it,
   mirroring bin/factoidal-cli/factoidal_cli.ml's
   native_write_base_and_sidecars (quad conversion + consumer-side sort
   + serialize), minus the sidecar/self-query prewarm step (out of
   scope for a browser bytes handle -- sidecars are an on-disk-file
   optimization; a buffer opened via openCottas has no sidecar files to
   build).
   --------------------------------------------------------------------- *)

(* Registry: JS-visible handle string -> the opened on-disk-shaped
   store. Process-wide (module-level ref), matching the same-lifetime
   contract Parquet_Footer.ml's own __mim2_file_bytes_cache already
   has (design doc "Open decisions" item 1: no eviction of the
   underlying byte cache; closeCottas below only drops OUR registry
   entry, disclosed in its own ABI doc comment above). *)
let cottas_registry : (string, RDF_CottasStore.cottas_ondisk_store) Hashtbl.t =
  Hashtbl.create 16

let cottas_mem_counter = ref 0

(* Hex -> raw OCaml string (binary-safe, unlike RDF_Bytes.bytes's
   int-list-then-BatUTF8 round trip -- see hex_of_bytes's own comment
   above for why that path is avoided for arbitrary bytes). None on
   odd length or a non-hex-digit character; openCottas turns this into
   an honest ok:false rather than an OCaml exception. *)
let raw_string_of_hex (s : string) : string option =
  let n = String.length s in
  if n mod 2 <> 0 then None
  else
    let hex_digit c =
      match c with
      | '0'..'9' -> Some (Char.code c - Char.code '0')
      | 'a'..'f' -> Some (Char.code c - Char.code 'a' + 10)
      | 'A'..'F' -> Some (Char.code c - Char.code 'A' + 10)
      | _ -> None
    in
    let out = Bytes.create (n / 2) in
    let rec go i =
      if i >= n / 2 then true
      else
        match hex_digit s.[2 * i], hex_digit s.[2 * i + 1] with
        | Some hi, Some lo -> Bytes.set out i (Char.chr (hi * 16 + lo)); go (i + 1)
        | _, _ -> false
    in
    if go 0 then Some (Bytes.unsafe_to_string out) else None

let open_cottas (bytes_hex : string) : string =
  guarded (fun () ->
    match raw_string_of_hex bytes_hex with
    | None ->
      err_json "openCottas: bytesHex is not a valid hex string (odd length or non-hex digit)"
    | Some raw_bytes ->
      incr cottas_mem_counter;
      let handle = Printf.sprintf "npmcottas:%d" !cottas_mem_counter in
      Parquet_Footer.register_memory_buffer handle raw_bytes;
      (match RDF_CottasStore.cottas_ondisk_open handle with
       | FStar_Pervasives_Native.None ->
         err_json
           "openCottas: could not open COTTAS artifact from bytes \
            (bad/missing Parquet footer, or truncated data)"
       | FStar_Pervasives_Native.Some store ->
         Hashtbl.replace cottas_registry handle store;
         "{\"ok\":true,\"handle\":" ^ jstr handle ^ "}"))

let close_cottas (handle : string) : string =
  guarded (fun () ->
    if Hashtbl.mem cottas_registry handle then begin
      Hashtbl.remove cottas_registry handle;
      "{\"ok\":true}"
    end else
      err_json (Printf.sprintf "closeCottas: unknown handle %s" handle))

let query_cottas (handle : string) (sparql : string) : string =
  guarded (fun () ->
    match Hashtbl.find_opt cottas_registry handle with
    | None -> err_json (Printf.sprintf "queryCottas: unknown handle %s" handle)
    | Some cods ->
      match SPARQL11_Parser.parse_sparql sparql with
      | SPARQL11_Parser.ParseErr msg -> err_json ("SPARQL parse error: " ^ msg)
      | SPARQL11_Parser.ParseOk (q, _) ->
        let q = OWL_QueryRewrite.rewrite_query q in
        let dsb = SPARQL11_Store.cottas_ondisk_dataset_backend cods in
        (match q.q_form with
         | QF_Ask ->
           (match SPARQL11_Store.run_ask_query_backend_dataset q dsb with
            | FStar_Pervasives_Native.Some b ->
              "{\"ok\":true,\"kind\":\"ask\",\"boolean\":"
              ^ (if b then "true" else "false") ^ "}"
            | FStar_Pervasives_Native.None ->
              err_json "queryCottas: backend ASK path unavailable for this query shape")
         | QF_Select _ ->
           (match SPARQL11_Store.run_select_query_backend_dataset q dsb with
            | FStar_Pervasives_Native.Some rows ->
              let vars = vars_of_query_or_rows q rows in
              "{\"ok\":true,\"kind\":\"select\",\"srj\":" ^ srj_of_rows vars rows ^ "}"
            | FStar_Pervasives_Native.None ->
              err_json "queryCottas: backend SELECT path unavailable for this query shape")
         | QF_Construct _ ->
           let ds0 = SPARQL11_Store.materialize_dataset_backend dsb in
           let triples = SPARQL11_Algebra.eval_construct_query q ds0.ds_default ds0 in
           "{\"ok\":true,\"kind\":\"construct\",\"nquads\":"
           ^ jstr (construct_triples_to_ntriples triples) ^ "}"
         | QF_Describe _ ->
           err_json "queryCottas: DESCRIBE is not supported"))

(* Mirrors bin/factoidal-cli/factoidal_cli.ml's subject_to_cottas_string /
   cottas_quad_of_triple_graph / cottas_quad_key -- duplicated here
   (rule #11 consumer code, not shared library code) rather than
   factored into a shared module, same pattern this file's rif_xml_
   preprocess already follows relative to bin/w3c-runner/w3c_runner.ml. *)
let subject_to_cottas_string (s : RDF_Graph_Executable.subject) : string =
  match s with
  | S_IRI i -> Printf.sprintf "<%s>" i
  | S_BNode b -> Printf.sprintf "_:%s" b

let cottas_quad_of_triple_graph
    (t : RDF_Graph_Executable.triple) (g : string option)
    : RDF_CottasStore_BaseWriter.cottas_quad =
  { RDF_CottasStore_BaseWriter.cq_s = subject_to_cottas_string t.s;
    RDF_CottasStore_BaseWriter.cq_p = Printf.sprintf "<%s>" t.p;
    RDF_CottasStore_BaseWriter.cq_o = RDF_Pretty.term_to_ntriples t.o;
    RDF_CottasStore_BaseWriter.cq_g =
      (match g with Some iri -> Printf.sprintf "<%s>" iri | None -> "DEFAULT") }

let cottas_quad_key (q : RDF_CottasStore_BaseWriter.cottas_quad) =
  (q.RDF_CottasStore_BaseWriter.cq_s, q.RDF_CottasStore_BaseWriter.cq_p,
   q.RDF_CottasStore_BaseWriter.cq_o, q.RDF_CottasStore_BaseWriter.cq_g)

(* Anti-pattern #9-adjacent: stdlib `List.map`/`List.concat_map` are
   NOT tail-recursive (each recursive call must `::` the result of the
   one after it) and, per bin/factoidal-cli/factoidal_cli.ml's own
   native_write_base_and_sidecars comment, blow the stack on a
   large-enough input even natively (888,949 quads there); under
   js_of_ocaml the effective call-stack budget is far smaller than
   native OCaml's, so the SAME non-tail construction overflows at only
   tens of thousands of quads (measured: 50,000 quads threw
   `RangeError`/`Stack overflow` here before this fix). Build the
   quad list with `List.iter` + a mutable accumulator (properly
   tail-recursive; no result-consing after the recursive call) instead,
   mirroring the CLI's own `Array.of_list`+`Array.sort` fix for the
   same reason. *)
let to_cottas (nq : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    let acc = ref [] in
    List.iter (fun t -> acc := cottas_quad_of_triple_graph t None :: !acc) ds.ds_default;
    List.iter
      (fun (ng : RDF_Graph_Executable.named_graph) ->
         List.iter
           (fun t -> acc := cottas_quad_of_triple_graph t (Some ng.ng_name) :: !acc)
           ng.ng_graph)
      ds.ds_named;
    let arr = Array.of_list !acc in
    Array.sort (fun a b -> compare (cottas_quad_key a) (cottas_quad_key b)) arr;
    let sorted = Array.to_list arr in
    let bytes = RDF_CottasStore_BaseWriter.serialize_cottas_v2 sorted in
    "{\"ok\":true,\"cottasHex\":" ^ jstr (hex_of_bytes bytes)
    ^ ",\"quadCount\":" ^ string_of_int (List.length sorted) ^ "}")

(* ---------------------------------------------------------------------
   Js.export — the only js_of_ocaml-specific code. Strings cross the
   boundary via Js.to_string / Js.string (UTF-16 JS <-> UTF-8 OCaml).
   --------------------------------------------------------------------- *)

let s0 (f : unit -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun () -> Js.string (f ())))

let s1 (f : string -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun a -> Js.string (f (Js.to_string a))))

let s2 (f : string -> string -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun a b ->
       Js.string (f (Js.to_string a) (Js.to_string b))))

let s3 (f : string -> string -> string -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun a b c ->
       Js.string (f (Js.to_string a) (Js.to_string b) (Js.to_string c))))

let s4 (f : string -> string -> string -> string -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun a b c d ->
       Js.string (f (Js.to_string a) (Js.to_string b) (Js.to_string c)
                    (Js.to_string d))))

let () =
  Js.export "factoidalNpmEntry"
    (Js.Unsafe.obj
       [| ("abiVersion", Js.Unsafe.inject (Js.string abi_version));
          ("parseToDatasetJson", s3 parse_to_dataset_json);
          ("queryDataset", s2 query_dataset);
          ("askDataset", s2 ask_dataset);
          ("updateDataset", s2 update_dataset);
          ("serializeNQuads", s1 serialize_nquads);
          ("canonicalizeToNQuads", s1 canonicalize_to_nquads);
          ("serializeTurtle", s1 serialize_turtle);
          ("rifSmoke", s0 rif_smoke_json);
          ("rifEval", s2 rif_eval_json);
          ("jsonldToRdf", s2 jsonld_to_rdf_json);
          ("shaclValidate", s2 shacl_validate_json);
          ("shexValidate", s4 shex_validate_json);
          ("owlClosure", s2 owl_closure_json);
          ("rmlMap", s3 rml_map_json);
          ("csvwToRdf", s3 csvw_to_rdf_json);
          ("deltaBatchToHex", s3 delta_batch_to_hex);
          ("deltaMergeApplyBrowser", s2 delta_merge_apply_browser);
          ("openCottas", s1 open_cottas);
          ("queryCottas", s2 query_cottas);
          ("closeCottas", s1 close_cottas);
          ("toCottas", s1 to_cottas)
       |])
