(* entry_core — the parse/query/update/serialize surface shared by both
   npm-entry bundles (full and lite).

   This is a CONSUMER (rule #11): hand-written OCaml glue that exposes
   F*-extracted engine functions over a string/JSON ABI. No RDF or
   SPARQL semantics live here — every semantic operation delegates to
   an F*-extracted module. This module references only:

     Parser_Diagnostics (+ the Parser_* modules behind it: Parser_Turtle,
       Parser_TriG, Parser_NTriples, Parser_NQuads, Parser_Combinators,
       Parser_FastString, ...), SPARQL11_Parser, SPARQL11_Algebra,
       SPARQL11_Store, OWL_QueryRewrite (query_dataset_mode applies
       rewrite_query, same as before the split — query semantics do not
       change between the full and lite bundles), RDF_Canonical,
       RDF_Dataset_Merge, RDF_Turtle_Serialize, RDF_NQuads_Serialize,
       SPARQL_Protocol, SPARQL_JSON_Escape, Parser_JSON, RDF_Format,
       RDF_Graph_Executable, RDF_Term (a dependency of
       RDF_Graph_Executable), Js_of_ocaml.Js (the extension-function
       bridge and the sN export helpers need JS interop directly).

   It must NOT reference Parser_RDFXML, Parser_JSONLD, JSONLD_Loader,
   Parquet_Footer, RDF_CottasStore*, SHACL_*, ShEx_*, OWL_Closure,
   Tableau*, RIF_*, RML_*, CSVW_*, VC_*, DID_Key, XSLT_*, XPath_*,
   XML_*, MathML_*, Math_*, XForms_*, JSONSchema_*, Schematron_*,
   HDT_*, the delta-log modules, or fstar_hacl_crypto — those live in
   entry_extras.ml, reachable through this module's `extra_parsers`
   hook (RDF/XML and JSON-LD parsing) or not reachable from the lite
   bundle at all. This split is what makes the lite bundle small:
   without `-linkall`, the OCaml linker only pulls in the compilation
   units this file (and whichever export table links with it)
   transitively reference.

   Full ABI documentation lives in entry_jsoo.ml's header comment
   (bundle-assembly bug fixes and additions get: full-bundle only vs.
   also-in-lite noted there). This header only orients the module
   split — see docs/designissues/2026-07-05-bundle-modularity.md for
   the design record.

   Strict-by-default parsing (https://github.com/danbri/factoidal/issues/344,
   https://github.com/danbri/factoidal/issues/681) and dataset handles
   (https://github.com/danbri/factoidal/issues/680) are implemented
   here, mirroring formal/lean4/Wasm/Ops/Handles.lean's op names and
   envelopes (https://github.com/danbri/factoidal/issues/585). *)

open RDF_Graph_Executable
open SPARQL11_Algebra

module Js = Js_of_ocaml.Js

let abi_version = "2"

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

(* Mode-aware dataset handle: a SPARQL 1.2 query's input N-Quads may
   carry <<( )>> triple terms (the JS side serialises a Quad term that
   way), which the Mode_11 parse_nquads would silently drop -- so the
   query would see a triple-term-free dataset and match nothing. Parse
   the handle in the matching mode. *)
let dataset_of_nquads_mode (sparql12 : bool) (nq : string) : rdf_dataset =
  Parser_NQuads.parse_nquads_mode
    (if sparql12 then Parser_NTriples.Mode_12 else Parser_NTriples.Mode_11)
    nq

(* ---------------------------------------------------------------------
   Strict-by-default document parsing with positions and prefixes
   (https://github.com/danbri/factoidal/issues/344,
   https://github.com/danbri/factoidal/issues/680,
   https://github.com/danbri/factoidal/issues/681). Turtle/TriG/
   N-Triples/N-Quads route through Parser_Diagnostics -- the same
   extracted module for every caller in this file, so parseToDatasetJson,
   parseDocument and datasetOpen agree by construction. RDF/XML and
   JSON-LD have no position-reporting entry point (their grammars are
   not walked the same offset-tracked way) and route through the
   extra_parsers hook below; their failures carry no position.
   --------------------------------------------------------------------- *)

type parse_outcome = {
  po_ds : rdf_dataset;
  po_prefixes : (string * string) list;
  po_error : (string * int) option;
}

type parse_failure = {
  pf_message : string;
  pf_offset : int option;
  pf_line : int option;
  pf_column : int option;
}

(* Installed by entry_extras.ml (`Entry_core.extra_parsers := Some ...`)
   when it is linked. Arguments: text, canonical format tag ("rdfxml" |
   "jsonld"), base IRI ("" for none). None (the lite bundle, which does
   not link entry_extras.ml) means "not installed": rule #11 holds
   because the hook itself carries no parsing logic, only a hand-off. *)
let extra_parsers
    : (string -> string -> string -> (rdf_dataset, string) result) option ref =
  ref None

(* "*12" format tags select Mode_12 and resolve to their Mode_11 base
   tag, exactly as the pre-#344 parse_text_to_dataset did; every other
   tag keeps the Mode_11 path byte-identical. *)
let resolve_mode_and_tag (format_tag : string)
    : Parser_NTriples.rdf_syntax_mode * string =
  match String.lowercase_ascii format_tag with
  | "ttl12" | "turtle12"   -> (Parser_NTriples.Mode_12, "ttl")
  | "nt12"  | "ntriples12" -> (Parser_NTriples.Mode_12, "nt")
  | "nq12"  | "nquads12"   -> (Parser_NTriples.Mode_12, "nq")
  | "trig12"               -> (Parser_NTriples.Mode_12, "trig")
  | _ -> (Parser_NTriples.Mode_11, format_tag)

(* A do_prefixes value (Parser.Diagnostics.fst) is most-recently-declared
   first and can repeat a label (Parser_Turtle.ml's `@prefix` handler
   prepends -- (prefix, iri_val) :: st.prefixes -- with no removal of an
   earlier entry for the same label). Scanning most-recent-first and
   keeping only the first occurrence of each label keeps each label's
   LATEST iri; reversing that deduplicated list orders the survivors by
   where their surviving (latest) declaration falls in the document. *)
let declaration_order_prefixes
    (do_prefixes : (string * string) list) : (string * string) list =
  let seen = Hashtbl.create 8 in
  let latest_first =
    List.filter
      (fun (label, _iri) ->
         if Hashtbl.mem seen label then false
         else (Hashtbl.add seen label (); true))
      do_prefixes
  in
  List.rev latest_first

let prefixes_json (prefixes : (string * string) list) : string =
  "{" ^ String.concat ","
          (List.map (fun (label, iri) -> jstr label ^ ":" ^ jstr iri) prefixes)
  ^ "}"

let parse_document (text : string) (format_tag : string) (base_iri : string)
    : (parse_outcome, parse_failure) result =
  let mode, tag = resolve_mode_and_tag format_tag in
  let fmt =
    if tag = "" then Some RDF_Format.Turtle
    else
      match RDF_Format.format_of_string tag with
      | FStar_Pervasives_Native.Some f -> Some f
      | FStar_Pervasives_Native.None -> None
  in
  let no_position (message : string) : parse_failure =
    { pf_message = message; pf_offset = None; pf_line = None; pf_column = None }
  in
  let with_position (message : string) (offset : Z.t) : parse_failure =
    let sp = Parser_Diagnostics.position_of_offset text offset in
    { pf_message = message;
      pf_offset = Some (Z.to_int offset);
      pf_line = Some (Z.to_int sp.Parser_Diagnostics.sp_line);
      pf_column = Some (Z.to_int sp.Parser_Diagnostics.sp_column) }
  in
  let routing_error (canonical_tag : string) : parse_failure =
    no_position
      (Printf.sprintf
         "format '%s' is not in the lite bundle; load factoidal-npm-entry.js"
         canonical_tag)
  in
  let via_hook (canonical_tag : string) : (parse_outcome, parse_failure) result =
    match !extra_parsers with
    | None -> Error (routing_error canonical_tag)
    | Some parser ->
      (match parser text canonical_tag base_iri with
       | Ok ds ->
         Ok { po_ds = scope_dataset_bnodes ds; po_prefixes = []; po_error = None }
       | Error msg -> Error (no_position msg))
  in
  match fmt with
  | None -> Error (no_position (Printf.sprintf "unknown format tag '%s'" format_tag))
  | Some RDF_Format.Turtle ->
    let out = Parser_Diagnostics.turtle_document mode text base_iri in
    let ds =
      scope_dataset_bnodes { ds_default = out.Parser_Diagnostics.do_value; ds_named = [] }
    in
    Ok { po_ds = ds;
         po_prefixes = declaration_order_prefixes out.Parser_Diagnostics.do_prefixes;
         po_error =
           (match out.Parser_Diagnostics.do_error with
            | FStar_Pervasives_Native.None -> None
            | FStar_Pervasives_Native.Some (msg, offset) -> Some (msg, Z.to_int offset)) }
  | Some RDF_Format.TriG ->
    let out = Parser_Diagnostics.trig_document mode text base_iri in
    let ds = scope_dataset_bnodes out.Parser_Diagnostics.do_value in
    Ok { po_ds = ds;
         po_prefixes = declaration_order_prefixes out.Parser_Diagnostics.do_prefixes;
         po_error =
           (match out.Parser_Diagnostics.do_error with
            | FStar_Pervasives_Native.None -> None
            | FStar_Pervasives_Native.Some (msg, offset) -> Some (msg, Z.to_int offset)) }
  | Some RDF_Format.NT ->
    (match Parser_Diagnostics.ntriples_diagnostic mode text with
     | Parser_Combinators.ParseOk (triples, _pos) ->
       Ok { po_ds = scope_dataset_bnodes { ds_default = triples; ds_named = [] };
            po_prefixes = []; po_error = None }
     | Parser_Combinators.ParseFail (msg, pos) -> Error (with_position msg pos))
  | Some RDF_Format.NQuads ->
    (match Parser_Diagnostics.nquads_diagnostic mode text with
     | Parser_Combinators.ParseOk (ds, _pos) ->
       Ok { po_ds = scope_dataset_bnodes ds; po_prefixes = []; po_error = None }
     | Parser_Combinators.ParseFail (msg, pos) -> Error (with_position msg pos))
  | Some RDF_Format.RDFXML -> via_hook "rdfxml"
  | Some RDF_Format.JSONLD -> via_hook "jsonld"

(* The display "format" field of a strict-parse error envelope: the
   caller's own format_tag string (lowercased), or "turtle" for the
   empty-string default -- the caller's own spelling, not a normalised
   one, so the envelope always names what was actually requested. *)
let format_of_display_tag (format_tag : string) : string =
  if format_tag = "" then "turtle" else String.lowercase_ascii format_tag

(* The shared strict-parse error envelope:
     {"ok":false,"error":"<msg>[ at line L, column C]",
      "offset"?:N,"line"?:N,"column"?:N,"format":tag}
   `position` is None for a routing error or an RDF/XML/JSON-LD failure
   (no offset available), Some (offset,line,column) otherwise. Shared by
   parseToDatasetJson, parseDocument (non-lenient) and datasetOpen. *)
let parse_error_envelope (format_tag : string) (message : string)
    (position : (int * int * int) option) : string =
  let display_tag = format_of_display_tag format_tag in
  match position with
  | None ->
    "{\"ok\":false,\"error\":" ^ jstr message
    ^ ",\"format\":" ^ jstr display_tag ^ "}"
  | Some (offset, line, column) ->
    "{\"ok\":false,\"error\":"
    ^ jstr (Printf.sprintf "%s at line %d, column %d" message line column)
    ^ ",\"offset\":" ^ string_of_int offset
    ^ ",\"line\":" ^ string_of_int line
    ^ ",\"column\":" ^ string_of_int column
    ^ ",\"format\":" ^ jstr display_tag ^ "}"

(* Runs `parse_document`, then either the caller's `on_ok` (no parse
   error at all -- do_error/ParseFail-free) or the shared error
   envelope (an outright parser_failure, OR a Turtle/TriG do_error --
   strict callers reject on ANY error even though the lenient walk
   recovered some statements past it). *)
let strict_parse_result (text : string) (format_tag : string)
    (r : (parse_outcome, parse_failure) result)
    (on_ok : parse_outcome -> string) : string =
  match r with
  | Error pf ->
    let position =
      match pf.pf_offset, pf.pf_line, pf.pf_column with
      | Some o, Some l, Some c -> Some (o, l, c)
      | _ -> None
    in
    parse_error_envelope format_tag pf.pf_message position
  | Ok outcome ->
    (match outcome.po_error with
     | None -> on_ok outcome
     | Some (msg, offset) ->
       let sp = Parser_Diagnostics.position_of_offset text (Z.of_int offset) in
       parse_error_envelope format_tag msg
         (Some (offset, Z.to_int sp.Parser_Diagnostics.sp_line,
                Z.to_int sp.Parser_Diagnostics.sp_column)))

let parse_to_dataset_json (text : string) (format_tag : string)
    (base_iri : string) : string =
  guarded (fun () ->
    strict_parse_result text format_tag (parse_document text format_tag base_iri)
      (fun outcome ->
         let nq = RDF_Canonical.canonical_nquads outcome.po_ds in
         let count = Z.to_string (SPARQL11_Algebra.dataset_triple_count outcome.po_ds) in
         "{\"ok\":true,\"count\":" ^ count ^ ",\"nquads\":" ^ jstr nq
         ^ ",\"prefixes\":" ^ prefixes_json outcome.po_prefixes ^ "}"))

(* parseDocument(text, formatTag, baseIri, optionsJson) -- optionsJson is
   "" or a JSON object; {"lenient":true} answers ok:true with whatever
   the parser recovered (Turtle/TriG: statements up to and past the
   first error; N-Triples/N-Quads: Parser.Diagnostics has no
   partial-recovery channel for them, so an empty dataset) plus a
   "diagnostics" array (0 or 1 entries -- Parser.Diagnostics reports
   only the first error, never a list). Anything else (including "")
   answers exactly as parseToDatasetJson. *)
let parse_lenient_of_json (options_json : string) : bool =
  if options_json = "" then false
  else
    match Parser_JSON.parse_json options_json with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some root ->
      (match Parser_JSON.json_get_field "lenient" root with
       | FStar_Pervasives_Native.Some (Parser_JSON.JBool b) -> b
       | _ -> false)

let diagnostic_json (text : string) (msg : string) (offset : int) : string =
  let sp = Parser_Diagnostics.position_of_offset text (Z.of_int offset) in
  "{\"message\":" ^ jstr msg
  ^ ",\"offset\":" ^ string_of_int offset
  ^ ",\"line\":" ^ string_of_int (Z.to_int sp.Parser_Diagnostics.sp_line)
  ^ ",\"column\":" ^ string_of_int (Z.to_int sp.Parser_Diagnostics.sp_column) ^ "}"

let parse_document_json (text : string) (format_tag : string) (base_iri : string)
    (options_json : string) : string =
  guarded (fun () ->
    if not (parse_lenient_of_json options_json) then
      parse_to_dataset_json text format_tag base_iri
    else
      match parse_document text format_tag base_iri with
      | Error pf ->
        let position =
          match pf.pf_offset, pf.pf_line, pf.pf_column with
          | Some o, Some l, Some c -> Some (o, l, c)
          | _ -> None
        in
        parse_error_envelope format_tag pf.pf_message position
      | Ok outcome ->
        let nq = RDF_Canonical.canonical_nquads outcome.po_ds in
        let count = Z.to_string (SPARQL11_Algebra.dataset_triple_count outcome.po_ds) in
        let diagnostics =
          match outcome.po_error with
          | None -> "[]"
          | Some (msg, offset) -> "[" ^ diagnostic_json text msg offset ^ "]"
        in
        "{\"ok\":true,\"count\":" ^ count ^ ",\"nquads\":" ^ jstr nq
        ^ ",\"prefixes\":" ^ prefixes_json outcome.po_prefixes
        ^ ",\"diagnostics\":" ^ diagnostics ^ "}")

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

(* Shared evaluator: dataset + a prebuilt indexed backend -> the
   queryDataset envelope family (kind ask/select/construct). Used both
   by the stateless query_dataset_mode (fresh backend per call) and by
   the dataset-handle datasetQuery (cached backend, built once at
   datasetOpen/datasetUpdate -- https://github.com/danbri/factoidal/issues/680).
   Not itself wrapped in `guarded`, so both callers' own `guarded`
   handles the error envelope exactly once. *)
let eval_query_over_backend (sparql12 : bool) (ds : rdf_dataset)
    (backend : SPARQL11_Store.dataset_backend) (sparql : string) : string =
  let parsed =
    if sparql12 then
      SPARQL11_Parser.parse_sparql_12_with_base
        FStar_Pervasives_Native.None sparql
    else SPARQL11_Parser.parse_sparql sparql
  in
  match parsed with
  | SPARQL11_Parser.ParseErr msg -> err_json ("SPARQL parse error: " ^ msg)
  | SPARQL11_Parser.ParseOk (q, _) ->
    let q = OWL_QueryRewrite.rewrite_query q in
    (match q.q_form with
     | QF_Ask ->
       let b =
         match SPARQL11_Store.run_ask_query_backend_dataset q backend with
         | FStar_Pervasives_Native.Some b -> b
         | FStar_Pervasives_Native.None ->
           SPARQL11_Algebra.eval_ask_query q ds.ds_default ds
       in
       "{\"ok\":true,\"kind\":\"ask\",\"boolean\":"
       ^ (if b then "true" else "false") ^ "}"
     | QF_Select _ ->
       let rows =
         match SPARQL11_Store.run_select_query_backend_dataset q backend with
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
       err_json "DESCRIBE is not supported by the npm entry yet")

(* SPARQL 1.2 opt-in (rule #11 DISPATCH only): sparql12=true selects the
   extracted parse_sparql_12_with_base (tokenize_12: TRIPLE/isTRIPLE/
   SUBJECT/PREDICATE/OBJECT/VERSION/lang-dir builtins + <<( )>> triple-term
   patterns), gated exactly as w3c_runner --sparql12. sparql12=false keeps
   the SPARQL 1.1 parser byte-identical so the protected 1.1 suite is
   unaffected. All algebra/eval is the shared extracted F* code above. *)
let query_dataset_mode (sparql12 : bool) (nq : string) (sparql : string)
    : string =
  guarded (fun () ->
    let ds = dataset_of_nquads_mode sparql12 nq in
    let backend = SPARQL11_Store.indexed_dataset_backend ds in
    eval_query_over_backend sparql12 ds backend sparql)

let query_dataset (nq : string) (sparql : string) : string =
  query_dataset_mode false nq sparql
let query_dataset_12 (nq : string) (sparql : string) : string =
  query_dataset_mode true nq sparql

let ask_dataset_mode (sparql12 : bool) (nq : string) (sparql : string)
    : string =
  guarded (fun () ->
    let ds = dataset_of_nquads_mode sparql12 nq in
    let parsed =
      if sparql12 then
        SPARQL11_Parser.parse_sparql_12_with_base
          FStar_Pervasives_Native.None sparql
      else SPARQL11_Parser.parse_sparql sparql
    in
    match parsed with
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

let ask_dataset (nq : string) (sparql : string) : string =
  ask_dataset_mode false nq sparql
let ask_dataset_12 (nq : string) (sparql : string) : string =
  ask_dataset_mode true nq sparql

let update_dataset_mode (sparql12 : bool) (nq : string) (update_text : string)
    : string =
  guarded (fun () ->
    let ds = dataset_of_nquads_mode sparql12 nq in
    let parsed =
      if sparql12 then
        SPARQL11_Parser.parse_sparql_update_12_with_base
          FStar_Pervasives_Native.None update_text
      else SPARQL11_Parser.parse_sparql_update update_text
    in
    match parsed with
    | SPARQL11_Parser.ParseErr msg ->
      err_json ("SPARQL update parse error: " ^ msg)
    | SPARQL11_Parser.ParseOk (u, _) ->
      let ds' = SPARQL11_Algebra.apply_update ds u in
      ok_nquads_json (RDF_Canonical.canonical_nquads ds'))

let update_dataset (nq : string) (update_text : string) : string =
  update_dataset_mode false nq update_text
let update_dataset_12 (nq : string) (update_text : string) : string =
  update_dataset_mode true nq update_text

let serialize_nquads (nq : string) : string =
  guarded (fun () ->
    ok_nquads_json (RDF_Canonical.canonical_nquads (dataset_of_nquads nq)))

let canonicalize_to_nquads (nq : string) : string =
  guarded (fun () ->
    ok_nquads_json (RDF_Canonical.canonicalize_to_nquads (dataset_of_nquads nq)))

(* ---------------------------------------------------------------------
   Turtle serialization, plain and prefix/shorthand-aware
   (https://github.com/danbri/factoidal/issues/681).
   RDF_Turtle_Serialize.turtle_of_graph_opts/_auto take a single
   rdf_graph, not a dataset — named graphs are flattened into the
   default graph for this pretty-print path (the fidelity-preserving
   path is serializeNQuads / canonicalizeToNQuads, which keep graph
   structure).
   --------------------------------------------------------------------- *)

let serialize_turtle (nq : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    let g = ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named in
    ok_turtle_json (RDF_Turtle_Serialize.turtle_of_graph_auto g))

(* optionsJson for serializeTurtleWith / datasetSerializeWith: "" or
   {"prefixes": {label: iri}, "literalShorthand": true|false}. A
   "prefixes" object maps EACH LABEL (the JSON key, without a colon) to
   its namespace IRI; turtle_render_options wants (namespace_iri,
   "label:") pairs, so this transposes and appends the colon.
   "prefixes" absent keeps `default_prefixes` (the handle's own
   prefixes for datasetSerializeWith, [] for the stateless
   serializeTurtleWith); "literalShorthand" absent means true. *)
let turtle_prefixes_of_json_object (root : Parser_JSON.json_val)
    : (string * string) list option =
  match Parser_JSON.json_get_field "prefixes" root with
  | FStar_Pervasives_Native.Some (Parser_JSON.JObject fields) ->
    Some (List.filter_map
            (fun (label, v) ->
               match v with
               | Parser_JSON.JString iri -> Some (iri, label ^ ":")
               | _ -> None)
            fields)
  | _ -> None

let turtle_literal_shorthand_of_json_object (root : Parser_JSON.json_val) : bool =
  match Parser_JSON.json_get_field "literalShorthand" root with
  | FStar_Pervasives_Native.Some (Parser_JSON.JBool b) -> b
  | _ -> true

let turtle_render_options_of_json
    (default_prefixes : (string * string) list) (options_json : string)
    : RDF_Turtle_Serialize.turtle_render_options =
  if options_json = "" then
    { RDF_Turtle_Serialize.tro_prefixes = default_prefixes;
      RDF_Turtle_Serialize.tro_literal_shorthand = true }
  else
    match Parser_JSON.parse_json options_json with
    | FStar_Pervasives_Native.None -> failwith "invalid optionsJson (not valid JSON)"
    | FStar_Pervasives_Native.Some root ->
      let prefixes =
        match turtle_prefixes_of_json_object root with
        | Some ps -> ps
        | None -> default_prefixes
      in
      { RDF_Turtle_Serialize.tro_prefixes = prefixes;
        RDF_Turtle_Serialize.tro_literal_shorthand =
          turtle_literal_shorthand_of_json_object root }

let serialize_turtle_with (nq : string) (options_json : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    let g = ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named in
    let opts = turtle_render_options_of_json [] options_json in
    ok_turtle_json (RDF_Turtle_Serialize.turtle_of_graph_opts opts g))

(* ---------------------------------------------------------------------
   Dataset handles: parse once, index once, reference by handle string
   (https://github.com/danbri/factoidal/issues/680, mirroring
   formal/lean4/Wasm/Ops/Handles.lean). Handles are process-local
   strings "h1", "h2", ... in open order, never reused.
   --------------------------------------------------------------------- *)

type handle_entry = {
  he_ds : rdf_dataset;
  he_backend : SPARQL11_Store.dataset_backend;
  he_prefixes : (string * string) list;
}

let handle_registry : (string, handle_entry) Hashtbl.t = Hashtbl.create 16
let handle_counter = ref 0

let unknown_handle_json (h : string) : string =
  err_json (Printf.sprintf "unknown dataset handle: %s" h)

let with_handle (h : string) (f : handle_entry -> string) : string =
  match Hashtbl.find_opt handle_registry h with
  | None -> unknown_handle_json h
  | Some he -> f he

(* datasetOpen(text, formatTag, baseIri) -> strict parse -> {"ok":true,
   "handle":"h1","count":N,"prefixes":{...}} | the parse error envelope
   above. The backend is built once here (SPARQL11_Store.
   indexed_dataset_backend), so every later datasetQuery on this handle
   runs without rebuilding indexes. *)
let dataset_open (text : string) (format_tag : string) (base_iri : string)
    : string =
  guarded (fun () ->
    strict_parse_result text format_tag (parse_document text format_tag base_iri)
      (fun outcome ->
         let backend = SPARQL11_Store.indexed_dataset_backend outcome.po_ds in
         incr handle_counter;
         let h = Printf.sprintf "h%d" !handle_counter in
         Hashtbl.replace handle_registry h
           { he_ds = outcome.po_ds; he_backend = backend;
             he_prefixes = outcome.po_prefixes };
         "{\"ok\":true,\"handle\":" ^ jstr h
         ^ ",\"count\":" ^ Z.to_string (SPARQL11_Algebra.dataset_triple_count outcome.po_ds)
         ^ ",\"prefixes\":" ^ prefixes_json outcome.po_prefixes ^ "}"))

(* datasetQuery(handle, sparql) / datasetQuery12 -- the queryDataset
   envelope family evaluated with the stored dataset and its cached
   backend: no re-parse, no backend rebuild. Shares eval_query_over_backend
   with the stateless query_dataset_mode above. *)
let dataset_query_mode (sparql12 : bool) (h : string) (sparql : string) : string =
  guarded (fun () ->
    with_handle h (fun he -> eval_query_over_backend sparql12 he.he_ds he.he_backend sparql))

let dataset_query (h : string) (sparql : string) : string =
  dataset_query_mode false h sparql
let dataset_query_12 (h : string) (sparql : string) : string =
  dataset_query_mode true h sparql

(* datasetUpdate(handle, sparqlUpdate) -> apply the update, REPLACE the
   stored dataset and rebuild its backend, answer {"ok":true,"count":N}.
   On a parse or evaluation error the stored dataset is unchanged. *)
let dataset_update (h : string) (update_text : string) : string =
  guarded (fun () ->
    with_handle h (fun he ->
      match SPARQL11_Parser.parse_sparql_update update_text with
      | SPARQL11_Parser.ParseErr msg -> err_json ("SPARQL update parse error: " ^ msg)
      | SPARQL11_Parser.ParseOk (u, _) ->
        let ds' = SPARQL11_Algebra.apply_update he.he_ds u in
        let backend' = SPARQL11_Store.indexed_dataset_backend ds' in
        Hashtbl.replace handle_registry h { he with he_ds = ds'; he_backend = backend' };
        "{\"ok\":true,\"count\":"
        ^ Z.to_string (SPARQL11_Algebra.dataset_triple_count ds') ^ "}"))

let turtle_graph_of_handle_dataset (ds : rdf_dataset) =
  ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named

(* datasetSerialize(handle, formatTag) -> nquads (RDF_Canonical.
   canonical_nquads) or turtle (named graphs flattened as today), where
   the Turtle path uses the handle's own prefixes (the ones datasetOpen
   recorded from the parse). *)
let dataset_serialize (h : string) (format_tag : string) : string =
  guarded (fun () ->
    with_handle h (fun he ->
      match String.lowercase_ascii format_tag with
      | "" | "nquads" | "nq" | "n-quads" ->
        ok_nquads_json (RDF_Canonical.canonical_nquads he.he_ds)
      | "turtle" | "ttl" ->
        let g = turtle_graph_of_handle_dataset he.he_ds in
        let opts =
          { RDF_Turtle_Serialize.tro_prefixes =
              List.map (fun (label, iri) -> (iri, label ^ ":")) he.he_prefixes;
            RDF_Turtle_Serialize.tro_literal_shorthand = true }
        in
        ok_turtle_json (RDF_Turtle_Serialize.turtle_of_graph_opts opts g)
      | _ ->
        err_json (Printf.sprintf
          "datasetSerialize: unknown format tag '%s' (nquads | turtle)" format_tag)))

let dataset_serialize_with (h : string) (format_tag : string) (options_json : string)
    : string =
  guarded (fun () ->
    with_handle h (fun he ->
      match String.lowercase_ascii format_tag with
      | "" | "nquads" | "nq" | "n-quads" ->
        ok_nquads_json (RDF_Canonical.canonical_nquads he.he_ds)
      | "turtle" | "ttl" ->
        let g = turtle_graph_of_handle_dataset he.he_ds in
        let default_prefixes =
          List.map (fun (label, iri) -> (iri, label ^ ":")) he.he_prefixes
        in
        let opts = turtle_render_options_of_json default_prefixes options_json in
        ok_turtle_json (RDF_Turtle_Serialize.turtle_of_graph_opts opts g)
      | _ ->
        err_json (Printf.sprintf
          "datasetSerializeWith: unknown format tag '%s' (nquads | turtle)" format_tag)))

(* datasetClose(handle) -> {"ok":true}; any op on an unknown handle ->
   {"ok":false,"error":"unknown dataset handle: h9"}. *)
let dataset_close (h : string) : string =
  guarded (fun () ->
    if Hashtbl.mem handle_registry h then begin
      Hashtbl.remove handle_registry h;
      "{\"ok\":true}"
    end else unknown_handle_json h)

(* ---------------------------------------------------------------------
   SPARQL 1.1 s17.6 extension functions -- issue #463.
   https://github.com/danbri/factoidal/issues/463

   Bridges caller-supplied JS functions (Comunica-style
   extensionFunctions, keyed by absolute IRI) into the F*-specified
   registry hook (SPARQL11.Algebra.extension_function_call, realised
   by experimental_ocaml_glue/extension_function_registry.sh).

   Marshaling only, no semantics: argument values go OUT through the
   F*-extracted converters (er_to_term + SPARQL_Protocol.json_term, the
   same SRJ term shape query results use), serialised as one JSON array
   string. The JS return value comes BACK as a raw JS value decoded
   field-by-field into an eval_result: an SRJ-style term object, or an
   ergonomic JS primitive (boolean / number / string). null, undefined,
   a thrown exception, or the JS bridge's pending marker all map to
   None -> ER_Error in F*.

   The async contract lives in lib/api.js: the engine is synchronous,
   so api.js memoises per (iri, serialised args) and re-runs the query
   until no pending async results remain. This file stays sync.
   --------------------------------------------------------------------- *)

let ext_pending_marker = "__FACTOIDAL_EXT_PENDING__"

let ext_args_to_json (args : SPARQL11_Algebra.eval_result list) : string =
  "["
  ^ String.concat ","
      (List.map
         (fun r ->
            match SPARQL11_Algebra.er_to_term r with
            | FStar_Pervasives_Native.Some t -> SPARQL_Protocol.json_term t
            | FStar_Pervasives_Native.None -> "{\"type\":\"error\"}")
         args)
  ^ "]"

let ext_string_literal (s : string) : RDF_Term.rdf_term =
  RDF_Term.T_Literal
    { RDF_Term.lexical_form = s;
      RDF_Term.datatype = "http://www.w3.org/2001/XMLSchema#string";
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None }

(* Read a string-valued field from a JS object; None when absent or
   not a string. *)
let ext_js_field (v : Js.Unsafe.any) (name : string) : string option =
  let f = Js.Unsafe.get v (Js.string name) in
  if Js.to_string (Js.typeof f) = "string"
  then Some (Js.to_string (Js.Unsafe.coerce f))
  else None

let ext_decode_result (v : Js.Unsafe.any) : SPARQL11_Algebra.eval_result option =
  match Js.to_string (Js.typeof (Js.Unsafe.coerce v)) with
  | "undefined" -> None
  | "boolean" -> Some (SPARQL11_Algebra.ER_Bool (Js.to_bool (Js.Unsafe.coerce v)))
  | "number" ->
    let f = Js.float_of_number (Js.Unsafe.coerce v) in
    if Float.is_integer f && Float.abs f <= 9007199254740991.0
    then Some (SPARQL11_Algebra.ER_Num (Z.of_float f))
    else Some (SPARQL11_Algebra.ER_Dbl (Printf.sprintf "%.17g" f))
  | "string" ->
    let s = Js.to_string (Js.Unsafe.coerce v) in
    if s = ext_pending_marker then None
    else Some (SPARQL11_Algebra.ER_Term (ext_string_literal s))
  | "object" ->
    if not (Js.Opt.test (Obj.magic v : 'a Js.opt)) then None (* null *)
    else
      (match ext_js_field v "type", ext_js_field v "value" with
       | Some "uri", Some value ->
         Some (SPARQL11_Algebra.ER_Term (RDF_Term.T_IRI value))
       | Some "bnode", Some value ->
         Some (SPARQL11_Algebra.ER_Term (RDF_Term.T_BNode value))
       | Some "literal", Some value ->
         let (datatype, lang_tag) =
           match ext_js_field v "xml:lang" with
           | Some l ->
             ("http://www.w3.org/1999/02/22-rdf-syntax-ns#langString",
              FStar_Pervasives_Native.Some l)
           | None ->
             ((match ext_js_field v "datatype" with
               | Some d -> d
               | None -> "http://www.w3.org/2001/XMLSchema#string"),
              FStar_Pervasives_Native.None)
         in
         Some (SPARQL11_Algebra.ER_Term (RDF_Term.T_Literal
           { RDF_Term.lexical_form = value;
             RDF_Term.datatype = datatype;
             RDF_Term.lang_tag = lang_tag;
             RDF_Term.direction = FStar_Pervasives_Native.None }))
       | _, _ -> None)
  | _ -> None

let ext_register (iri : Js.js_string Js.t) (cb : Js.Unsafe.any) : Js.js_string Js.t =
  let iri_s = Js.to_string iri in
  SPARQL11_Algebra.extension_function_register iri_s
    (fun args ->
       let args_json = ext_args_to_json args in
       match
         (try
            Some (Js.Unsafe.fun_call cb
                    [| Js.Unsafe.inject (Js.string iri_s);
                       Js.Unsafe.inject (Js.string args_json) |])
          with _ -> None)
       with
       | None -> None
       | Some v -> ext_decode_result v);
  Js.string "{\"ok\":true}"

let ext_unregister (iri : string) : string =
  guarded (fun () ->
    SPARQL11_Algebra.extension_function_unregister iri;
    "{\"ok\":true}")

let ext_clear () : string =
  guarded (fun () ->
    SPARQL11_Algebra.extension_function_clear ();
    "{\"ok\":true}")

(* SPARQL 1.1 SERVICE endpoint snapshots -- issue #57 family. The same
   registry hook the W3C runner fills from qt:serviceData manifests
   (SPARQL11_Algebra.service_endpoint_register, realised by
   57_service_client_bind.sh), exposed over the ABI so browser/Node
   callers can bind an endpoint IRI to a local graph snapshot and then
   run SERVICE / LATERAL{SERVICE} queries against it. Marshaling only:
   the payload is parsed by the F*-extracted N-Quads parser; the
   snapshot registered is the payload's default graph. *)
let register_service_endpoint (iri : string) (nq : string) : string =
  guarded (fun () ->
    let ds = dataset_of_nquads nq in
    SPARQL11_Algebra.service_endpoint_register iri ds.ds_default;
    "{\"ok\":true,\"count\":"
    ^ string_of_int (List.length ds.ds_default) ^ "}")

let clear_service_endpoints () : string =
  guarded (fun () ->
    SPARQL11_Algebra.service_endpoint_clear ();
    "{\"ok\":true}")

(* ---------------------------------------------------------------------
   Js.export helpers — the only js_of_ocaml-specific plumbing besides
   the extension-function bridge above. Strings cross the boundary via
   Js.to_string / Js.string (UTF-16 JS <-> UTF-8 OCaml). Shared by
   entry_jsoo.ml (full) and entry_lite_jsoo.ml (lite).
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
