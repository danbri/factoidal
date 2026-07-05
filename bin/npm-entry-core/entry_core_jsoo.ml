(* entry_core_jsoo — parse/serialize-only js_of_ocaml entry point.

   Pilot for the bundle-modularity design
   (docs/designissues/2026-07-05-bundle-modularity.md): js_of_ocaml
   performs whole-program dead-code elimination per entry point, so an
   entry that links only the parse/serialize surface should produce a
   much smaller bundle than the full factoidal-npm-entry.js. This file
   measures that lever.

   Like bin/npm-entry/entry_jsoo.ml this is a CONSUMER (rule #11):
   hand-written OCaml glue exposing F-star-extracted modules over a
   string/JSON ABI. No RDF semantics live here; every semantic
   operation delegates to an extracted module:

     parse        -> Parser_NTriples / Parser_Turtle / Parser_NQuads /
                     Parser_TriG (+ RDF_Format dispatch,
                     RDF_Dataset_Merge.rename_dataset_bnodes for
                     per-document blank-node scoping)
     serialize    -> RDF_Canonical.canonical_nquads (sorted N-Quads)
     serialize (turtle) -> RDF_Turtle_Serialize.turtle_of_graph_auto
     JSON escaping -> SPARQL_JSON_Escape

   Deliberately NOT linked (that is the point of the pilot):
   SPARQL11_Parser / SPARQL11_Algebra / SPARQL11_Store (query, update),
   OWL_*, SHACL_Validation, ShEx_*, RIF_*, Parser_RDFXML (drags in the
   XML stack), Parser_JSONLD, RDF_Canonical.canonicalize_to_nquads
   (RDFC-1.0 labelling; canonical_nquads alone only sorts), the COTTAS
   / Parquet storage layer.

   ABI (subset of factoidalNpmEntry, same JSON envelopes, so the npm
   wrapper can route to either bundle):

     factoidalNpmEntryCore.abiVersion
       "1" — matches bin/npm-entry/entry_jsoo.ml.
     factoidalNpmEntryCore.parseToDatasetJson(text, format, baseIri)
       -> {"ok":true,"nquads":"...","count":N} | {"ok":false,"error":"..."}
       format: "turtle"|"ntriples"|"nquads"|"trig" (aliases as in
       RDF_Format.format_of_string). "rdfxml" and "jsonld" parse to an
       error envelope directing callers at the full bundle.
     factoidalNpmEntryCore.serializeNQuads(nquads)
       -> {"ok":true,"nquads":"..."} (parse + sorted re-serialization)
     factoidalNpmEntryCore.serializeTurtle(nquads)
       -> {"ok":true,"turtle":"..."} (pretty-print; not canonical)

   Build wiring: NOT yet in build-ocaml.sh — see README.md in this
   directory for the manual compile used for the pilot measurement.
   Wiring lands with the bundle-modularity implementation wave. *)

open RDF_Graph_Executable

module Js = Js_of_ocaml.Js

let abi_version = "1"

(* JSON envelope helpers — escaping delegates to the F-star-extracted
   SPARQL_JSON_Escape so the byte-level JSON rules stay verified. *)

let jstr (s : string) : string =
  "\"" ^ SPARQL_JSON_Escape.json_escape s ^ "\""

let err_json (msg : string) : string =
  "{\"ok\":false,\"error\":" ^ jstr msg ^ "}"

let ok_nquads_json (nq : string) : string =
  "{\"ok\":true,\"nquads\":" ^ jstr nq ^ "}"

let ok_turtle_json (ttl : string) : string =
  "{\"ok\":true,\"turtle\":" ^ jstr ttl ^ "}"

let guarded (f : unit -> string) : string =
  try f () with
  | e -> err_json (Printexc.to_string e)

(* Per-document blank-node scope counter — same pattern as
   bin/npm-entry/entry_jsoo.ml; the renaming itself is the F-star
   function RDF_Dataset_Merge.rename_dataset_bnodes. *)
let bnode_scope_counter = ref 0

let scope_dataset_bnodes ds =
  let n = !bnode_scope_counter in
  incr bnode_scope_counter;
  RDF_Dataset_Merge.rename_dataset_bnodes (Printf.sprintf "d%d_" n) ds

let dataset_of_nquads (nq : string) : rdf_dataset =
  Parser_NQuads.parse_nquads nq

(* Envelope statistic only (not semantics): total triple count across
   default + named graphs. The full entry uses
   SPARQL11_Algebra.dataset_triple_count, but linking SPARQL11_Algebra
   for a List.length sum would defeat the pilot. *)
let dataset_triple_count (ds : rdf_dataset) : int =
  List.length ds.ds_default
  + List.fold_left (fun acc ng -> acc + List.length ng.ng_graph) 0 ds.ds_named

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
    (match fmt with
     | RDF_Format.NQuads -> Ok (Parser_NQuads.parse_nquads text)
     | RDF_Format.TriG ->
       Ok
         (match base with
          | Some b -> Parser_TriG.parse_trig_with_base_lenient text b
          | None -> Parser_TriG.parse_trig_lenient text)
     | RDF_Format.NT ->
       Ok { ds_default = Parser_NTriples.parse_ntriples text; ds_named = [] }
     | RDF_Format.Turtle ->
       let triples =
         match base with
         | Some b -> Parser_Turtle.parse_turtle_with_base text b
         | None -> Parser_Turtle.parse_turtle text
       in
       Ok { ds_default = triples; ds_named = [] }
     | _ ->
       Error
         (Printf.sprintf
            "format '%s' is not in the core bundle; use the full \
             factoidal-npm-entry bundle" format_tag))

let parse_to_dataset_json (text : string) (format_tag : string)
    (base_iri : string) : string =
  guarded (fun () ->
    match parse_text_to_dataset text format_tag base_iri with
    | Error msg -> err_json msg
    | Ok ds ->
      let ds = scope_dataset_bnodes ds in
      let nq = RDF_Canonical.canonical_nquads ds in
      let count = string_of_int (dataset_triple_count ds) in
      "{\"ok\":true,\"count\":" ^ count ^ ",\"nquads\":" ^ jstr nq ^ "}")

let serialize_nquads (nq : string) : string =
  guarded (fun () ->
    ok_nquads_json (RDF_Canonical.canonical_nquads (dataset_of_nquads nq)))

(* Named graphs are flattened into the default graph for this
   pretty-print path — same caveat as the full entry. *)
let serialize_turtle (nq : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    let g = ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named in
    ok_turtle_json (RDF_Turtle_Serialize.turtle_of_graph_auto g))

(* Js.export — the only js_of_ocaml-specific code. *)

let s1 (f : string -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun a -> Js.string (f (Js.to_string a))))

let s3 (f : string -> string -> string -> string) =
  Js.Unsafe.inject
    (Js.wrap_callback (fun a b c ->
       Js.string (f (Js.to_string a) (Js.to_string b) (Js.to_string c))))

let () =
  Js.export "factoidalNpmEntryCore"
    (Js.Unsafe.obj
       [| ("abiVersion", Js.Unsafe.inject (Js.string abi_version));
          ("parseToDatasetJson", s3 parse_to_dataset_json);
          ("serializeNQuads", s1 serialize_nquads);
          ("serializeTurtle", s1 serialize_turtle)
       |])
