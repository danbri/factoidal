(* entry_jsoo — js_of_ocaml / wasm_of_ocaml FULL entry point for the
   npm package (`factoidal-npm-entry.js` / `.wasm.js`).

   This is a CONSUMER (rule #11): it links entry_core.ml (the
   parse/query/update/serialize/handle surface) and entry_extras.ml
   (RIF, JSON-LD, XML, XPath, SHACL, ShEx, closures, tableau, OWL DL,
   RML, CSVW, delta log, COTTAS, VC crypto, DID, XSLT, MathML, XForms,
   JSON Schema, Schematron, TOAN, matrix, sigmoid) and exports the
   union under the JS global `factoidalNpmEntry`. It contains no RDF/
   SPARQL/OWL/etc. semantics of its own — every semantic operation
   delegates to an F*-extracted module named in entry_core.ml's or
   entry_extras.ml's own header/section comments.

   A second, smaller export table — entry_lite_jsoo.ml, built as
   `factoidal-npm-entry-lite.js` / `.wasm.js` — links entry_core.ml
   ALONE (no entry_extras.ml) under the SAME global name, with
   `profile: "lite"` in place of this file's `profile: "full"` and
   without the entry_extras-only names below. Module split + lite
   bundle: https://github.com/danbri/factoidal/issues/684. Design
   record: docs/designissues/2026-07-05-bundle-modularity.md.

   ABI contract (all arguments and results are strings; structure is
   JSON):

     factoidalNpmEntry.abiVersion
       "2" — bumped from "1" for the strict-by-default parse envelope,
       dataset handles, and prefix-aware Turtle serialization below
       (https://github.com/danbri/factoidal/issues/344,
       https://github.com/danbri/factoidal/issues/680,
       https://github.com/danbri/factoidal/issues/681). Bump again
       when a signature or JSON shape changes.
     factoidalNpmEntry.profile
       "full" in this bundle, "lite" in factoidal-npm-entry-lite.js.

     --- Strict parsing (https://github.com/danbri/factoidal/issues/344) ---

     factoidalNpmEntry.parseToDatasetJson(text, format, baseIri)
       -> {"ok":true,"count":N,"nquads":"...","prefixes":{"ex":"http://example.org/",...}}
        | {"ok":false,"error":"<message>[ at line L, column C]",
           "offset"?:N,"line"?:N,"column"?:N,"format":"turtle"}
       format: "turtle"|"ntriples"|"nquads"|"trig"|"rdfxml"|"jsonld"
       (aliases as in RDF_Format.format_of_string, plus the "*12" RDF
       1.2 opt-in tags below); baseIri "" means none. Strict by
       default: a syntax error, an undeclared prefix, or an
       unresolvable relative IRI (no baseIri in effect) rejects the
       WHOLE parse — nothing is silently dropped any more. "prefixes"
       is `{}` for syntaxes that carry none (N-Triples, N-Quads,
       RDF/XML, JSON-LD). "offset"/"line"/"column" are present only
       when the parser reports a position (Turtle, TriG, N-Triples,
       N-Quads); RDF/XML and JSON-LD failures carry a message only.
       The dataset handle IS the returned N-Quads string, as before —
       for a cached/indexed handle use datasetOpen instead.
     factoidalNpmEntry.parseDocument(text, format, baseIri, optionsJson)
       -> optionsJson "" or a JSON object. `{"lenient":true}` answers
          {"ok":true,"count":N,"nquads":"...","prefixes":{...},
           "diagnostics":[{"message":"...","offset":N,"line":L,"column":C},...]}
          with whatever the parser recovered (statements before AND
          after the first error, for Turtle/TriG; N-Triples/N-Quads
          have no partial-recovery channel, so an empty dataset on
          error) and `diagnostics` empty when there was no error.
          Any other optionsJson (including "") answers exactly as
          parseToDatasetJson.
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
     factoidalNpmEntry.serializeTurtleWith(nquads, optionsJson)
       (https://github.com/danbri/factoidal/issues/681)
       -> {"ok":true,"turtle":"..."} | {"ok":false,"error":"..."}
       optionsJson is "" or {"prefixes":{"ex":"http://example.org/"},
       "literalShorthand":true|false}. Caller prefix pairs win, in the
       caller's order; unused caller namespaces are not emitted; auto
       `nsN:` labels skip caller labels. "literalShorthand" (default
       true) controls whether xsd:integer/decimal/double/boolean
       literals with a Turtle-grammar-matching lexical form print bare.

     --- Dataset handles (https://github.com/danbri/factoidal/issues/680,
         mirroring formal/lean4/Wasm/Ops/Handles.lean's op names and
         envelopes) — parse and index ONCE, query/update/serialize many
         times by handle instead of re-parsing N-Quads text and
         rebuilding the SPARQL index on every call. Handles are
         process-local strings "h1", "h2", ... in open order, never
         reused. ---

     factoidalNpmEntry.datasetOpen(text, format, baseIri)
       -> {"ok":true,"handle":"h1","count":N,"prefixes":{...}}
        | the parseToDatasetJson error envelope above (strict; the
          dataset is not opened on a parse error).
     factoidalNpmEntry.datasetQuery(handle, sparql)
     factoidalNpmEntry.datasetQuery12(handle, sparql)
       -> the queryDataset envelope family, evaluated against the
          stored dataset and its CACHED indexed backend (no re-parse,
          no backend rebuild) | {"ok":false,"error":"unknown dataset
          handle: h9"}.
     factoidalNpmEntry.datasetUpdate(handle, sparqlUpdate)
       -> {"ok":true,"count":N} — the stored dataset is REPLACED and
          its backend rebuilt. On a parse or evaluation error the
          stored dataset is unchanged.
     factoidalNpmEntry.datasetSerialize(handle, format)
       -> {"ok":true,"nquads":"..."} | {"ok":true,"turtle":"..."}
          ("nquads" | "turtle"; the Turtle path uses the prefixes
          datasetOpen recorded from the parse).
     factoidalNpmEntry.datasetSerializeWith(handle, format, optionsJson)
       -> same as datasetSerialize, but optionsJson (same shape as
          serializeTurtleWith's) overrides the handle's own prefixes/
          shorthand when given; "prefixes" absent means the handle's
          own prefixes.
     factoidalNpmEntry.datasetClose(handle)
       -> {"ok":true} | {"ok":false,"error":"unknown dataset handle: ..."}

     --- SPARQL 1.2 opt-in variants (issue #… tokenize_12 parser family) ---

     factoidalNpmEntry.queryDataset12 / askDataset12 / updateDataset12
       -> same envelopes as the 1.1 forms; select the RDF 1.2 grammar
          (TRIPLE/isTRIPLE/SUBJECT/PREDICATE/OBJECT/VERSION/lang-dir
          builtins, <<( )>> triple-term patterns). The 1.1 forms above
          stay byte-identical.

     --- Everything below is FULL-BUNDLE ONLY (entry_extras.ml; absent
         from factoidal-npm-entry-lite.js — a lite-bundle call to a
         format needing RDF/XML or JSON-LD parsing, e.g.
         parseToDatasetJson(x,"rdfxml",...), answers a routing error
         naming this bundle instead). ---

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
       jsonld_loader_register call in entry_extras.ml, same choice
       bin/factoidal-cli/bin/factoidal-http make).
       NOTE: parseToDatasetJson(text, "jsonld", baseIri) now also works
       (the format-dispatch gap is fixed via the extra_parsers hook) --
       jsonldToRdf exists for the extra options parseToDatasetJson's
       4-string-arg ABI has no room for.
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
       (RDF_Graph_Executable.rdfs_closure_with_reflexivity_dispatch) or
       "OWL-RL" (.owl_rl_closure_with_reflexivity), fuel=100 -- the same
       closures bin/w3c-runner drives for entailment-regime tests.
       Result is the closure graph (input + derived triples) as
       default-graph N-Quads text.
     factoidalNpmEntry.rhoDfClosure(dataNQuads) / rhoDfFragmentCheck(dataNQuads)
       / rdfsPlusClosure(dataNQuads)
       -> see RDF.Entailment.RDFS.RhoDFClosure.fst /
       RDF.Entailment.RDFSPlus.fst's module banners; entry_extras.ml's
       own section comments carry the full envelope shapes.
     factoidalNpmEntry.tableauMaterialise(dataNQuads)
       / tableauDlInconsistent(dataNQuads)
       -> Tableau.fst's model-construction reasoner (0 assume val,
       verified); see entry_extras.ml's own section comment.
     factoidalNpmEntry.owlIsConsistent(dataNquads, optsJson)
       / owlEntails(premiseNquads, conclusionNquads, optsJson)
       -> the verified clash-detecting tableau (Tableau.Refute.fst),
       three-valued (true/false/null=budget-out, never a guessed
       false); see entry_extras.ml's own section comment.
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
     factoidalNpmEntry.didKeyResolve(did)
       -> {"ok":true,"did":"...","nquads":"..."} | {"ok":false,"error":"..."}
       DID_Key.did_key_document -- see entry_extras.ml's own comment.
     factoidalNpmEntry.vc*(...) -- VC Data Integrity crypto + VCDM 2.0
       structural conformance checks; see entry_extras.ml's VC section
       comment for each function's envelope.
     factoidalNpmEntry.xsltTransform / mathmlEval / xformsRecalc /
       jsonSchemaValidate / schematronValidate / toan* / matrix* /
       sigmoid* -- typed engine functions (#74 npm FP surface); see
       entry_extras.ml's "Typed engine functions" section for every
       envelope shape.

   Rich types (RDF/JS terms, Dataset objects, Maps of bindings) live on
   the JavaScript side (npm/factoidal/rdfjs.js); the js_of_ocaml string
   bridge is the stable part, so the ABI stays strings + JSON.

   Build wiring: see bin/npm-entry/README.md — the `js` step of
   formal/fstar/build-ocaml.sh compiles entry_core.ml, entry_extras.ml
   and this file (in that order, after FSTAR_MODULES, with -package
   js_of_ocaml) into npm_entry.byte, then js_of_ocaml / wasm_of_ocaml
   emit docs/fstar-extracted/factoidal-npm-entry{.js,.wasm.js}. The
   same step separately links entry_core.ml + entry_lite_jsoo.ml
   (WITHOUT entry_extras.ml, and without -linkall) into
   npm_entry_lite.byte, emitting factoidal-npm-entry-lite{.js,.wasm.js}. *)

module Js = Js_of_ocaml.Js

let () =
  Js.export "factoidalNpmEntry"
    (Js.Unsafe.obj
       [| ("abiVersion", Js.Unsafe.inject (Js.string Entry_core.abi_version));
          ("profile", Js.Unsafe.inject (Js.string "full"));
          ("parseToDatasetJson", Entry_core.s3 Entry_core.parse_to_dataset_json);
          ("parseDocument", Entry_core.s4 Entry_core.parse_document_json);
          ("queryDataset", Entry_core.s2 Entry_core.query_dataset);
          ("askDataset", Entry_core.s2 Entry_core.ask_dataset);
          ("updateDataset", Entry_core.s2 Entry_core.update_dataset);
          (* SPARQL 1.2 variants (tokenize_12 parser); selected by
             api.js when {sparql12:true}/{version:"1.2"} is requested. *)
          ("queryDataset12", Entry_core.s2 Entry_core.query_dataset_12);
          ("askDataset12", Entry_core.s2 Entry_core.ask_dataset_12);
          ("updateDataset12", Entry_core.s2 Entry_core.update_dataset_12);
          ("serializeNQuads", Entry_core.s1 Entry_core.serialize_nquads);
          ("canonicalizeToNQuads", Entry_core.s1 Entry_core.canonicalize_to_nquads);
          ("serializeTurtle", Entry_core.s1 Entry_core.serialize_turtle);
          ("serializeTurtleWith", Entry_core.s2 Entry_core.serialize_turtle_with);
          (* Dataset handles (https://github.com/danbri/factoidal/issues/680). *)
          ("datasetOpen", Entry_core.s3 Entry_core.dataset_open);
          ("datasetQuery", Entry_core.s2 Entry_core.dataset_query);
          ("datasetQuery12", Entry_core.s2 Entry_core.dataset_query_12);
          ("datasetUpdate", Entry_core.s2 Entry_core.dataset_update);
          ("datasetSerialize", Entry_core.s2 Entry_core.dataset_serialize);
          ("datasetSerializeWith", Entry_core.s3 Entry_core.dataset_serialize_with);
          ("datasetClose", Entry_core.s1 Entry_core.dataset_close);
          ("didKeyResolve", Entry_core.s1 Entry_extras.did_key_resolve);
          ("vcSha256Hex", Entry_core.s1 Entry_extras.vc_sha256_hex);
          ("vcEd25519SecretToPublic", Entry_core.s1 Entry_extras.vc_ed25519_secret_to_public);
          ("vcEd25519Sign", Entry_core.s2 Entry_extras.vc_ed25519_sign);
          ("vcEd25519Verify", Entry_core.s3 Entry_extras.vc_ed25519_verify);
          ("vcEddsaCreateFromCanonical", Entry_core.s3 Entry_extras.vc_eddsa_create_from_canonical);
          ("vcEddsaVerifyFromCanonical", Entry_core.s4 Entry_extras.vc_eddsa_verify_from_canonical);
          ("vcCheckCredential", Entry_core.s2 Entry_extras.vc_check_credential_json);
          ("vcCheckCredentialSubject", Entry_core.s1 Entry_extras.vc_check_credential_subject_json);
          ("vcCheckNoDataLoss", Entry_core.s1 Entry_extras.vc_check_no_data_loss_json);
          ("vcCheckRelatedResourceDigests", Entry_core.s2 Entry_extras.vc_check_related_resource_digests_json);
          ("xsltTransform", Entry_core.s2 Entry_extras.xslt_transform_json);
          ("mathmlEval", Entry_core.s2 Entry_extras.mathml_eval_json);
          ("xformsRecalc", Entry_core.s2 Entry_extras.xforms_recalc_json);
          ("jsonSchemaValidate", Entry_core.s2 Entry_extras.json_schema_validate_json);
          ("schematronValidate", Entry_core.s2 Entry_extras.schematron_validate_json);
          ("toanSummation", Entry_core.s4 Entry_extras.toan_summation_json);
          ("toanProduct", Entry_core.s4 Entry_extras.toan_product_json);
          ("toanSimplify", Entry_core.s1 Entry_extras.toan_simplify_json);
          ("toanDiff", Entry_core.s2 Entry_extras.toan_diff_json);
          ("toanSubst", Entry_core.s3 Entry_extras.toan_subst_json);
          ("matrixDeterminant", Entry_core.s1 Entry_extras.matrix_determinant_json);
          ("matrixScalarProduct", Entry_core.s2 Entry_extras.matrix_scalarproduct_json);
          ("matrixVectorProduct", Entry_core.s2 Entry_extras.matrix_vectorproduct_json);
          ("matrixOuterProduct", Entry_core.s2 Entry_extras.matrix_outerproduct_json);
          ("sigmoidPoints", Entry_core.s1 Entry_extras.sigmoid_points_json);
          ("sigmoidFormulaMathml", Entry_core.s0 Entry_extras.sigmoid_formula_mathml_json);
          ("rifSmoke", Entry_core.s0 Entry_extras.rif_smoke_json);
          ("rifEval", Entry_core.s2 Entry_extras.rif_eval_json);
          ("jsonldToRdf", Entry_core.s2 Entry_extras.jsonld_to_rdf_json);
          ("jsonldFromRdf", Entry_core.s2 Entry_extras.jsonld_from_rdf_json);
          ("xmlWellformed", Entry_core.s1 Entry_extras.xml_wellformed_json);
          ("xpathEval", Entry_core.s2 Entry_extras.xpath_eval_json);
          ("shaclValidate", Entry_core.s2 Entry_extras.shacl_validate_json);
          ("shexValidate", Entry_core.s4 Entry_extras.shex_validate_json);
          ("owlClosure", Entry_core.s2 Entry_extras.owl_closure_json);
          ("rhoDfClosure", Entry_core.s1 Entry_extras.rho_df_closure_json);
          ("rhoDfFragmentCheck", Entry_core.s1 Entry_extras.rho_df_fragment_check_json);
          ("rdfsPlusClosure", Entry_core.s1 Entry_extras.rdfs_plus_closure_json);
          ("tableauMaterialise", Entry_core.s1 Entry_extras.tableau_materialise_json);
          ("tableauDlInconsistent", Entry_core.s1 Entry_extras.tableau_dl_inconsistent_json);
          ("owlIsConsistent", Entry_core.s2 Entry_extras.owl_is_consistent_json);
          ("owlEntails", Entry_core.s3 Entry_extras.owl_entails_json);
          ("rmlMap", Entry_core.s3 Entry_extras.rml_map_json);
          ("csvwToRdf", Entry_core.s3 Entry_extras.csvw_to_rdf_json);
          ("deltaBatchToHex", Entry_core.s3 Entry_extras.delta_batch_to_hex);
          ("deltaMergeApplyBrowser", Entry_core.s2 Entry_extras.delta_merge_apply_browser);
          ("openCottas", Entry_core.s1 Entry_extras.open_cottas);
          ("queryCottas", Entry_core.s2 Entry_extras.query_cottas);
          ("closeCottas", Entry_core.s1 Entry_extras.close_cottas);
          ("toCottas", Entry_core.s1 Entry_extras.to_cottas);
          (* SPARQL 1.1 s17.6 extension functions (issue #463). The
             callback is a JS function, not a string — registered
             directly rather than through the sN string helpers. *)
          ("registerExtensionFunction",
             Js.Unsafe.inject (Js.wrap_callback Entry_core.ext_register));
          ("unregisterExtensionFunction", Entry_core.s1 Entry_core.ext_unregister);
          ("clearExtensionFunctions", Entry_core.s0 Entry_core.ext_clear);
          ("registerServiceEndpoint", Entry_core.s2 Entry_core.register_service_endpoint);
          ("clearServiceEndpoints", Entry_core.s0 Entry_core.clear_service_endpoints)
       |])
