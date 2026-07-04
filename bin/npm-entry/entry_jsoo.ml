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
       General entry point: rifXml is a RIF Core XML document (parsed
       by Parser_RIFXML.parse_rif_program), dataNQuads is the premise
       graph (parsed by Parser_NQuads.parse_nquads, default graph
       only). Saturated via RIF_Core_Eval.fixpoint, fuel=100. Import
       directives are not resolved (Parser_RIFXML.parse_rif_program
       ignores them; RIF_Core_Tests.saturate_with_program has the same
       limitation) -- rules referencing an <Import>'d graph will not
       see those triples unless the caller merges them into dataNQuads
       first.

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
   (default graph only -- RIF Core has no named-graph notion). *)
let rif_eval_json (rif_xml : string) (data_nquads : string) : string =
  guarded (fun () ->
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
          ("rifEval", s2 rif_eval_json)
       |])
