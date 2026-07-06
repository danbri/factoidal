(* factoidal — a SPARQL query tool backed by formally verified F* code.

   Usage is modelled on Apache Jena's arq / Rasqal's roqet:

     factoidal --data data.ttl --query query.rq
     factoidal --data data.ttl -e 'SELECT * WHERE { ?s ?p ?o }'
     factoidal --data data.ttl --data more.nt --query query.rq
     factoidal --dump data.ttl
     factoidal --count data.ttl

   Pipe-friendly: reads stdin when data file is "-".

   This file is UNVERIFIED test/CLI infrastructure — not extracted from F*.
   All RDF parsing, SPARQL parsing, and query evaluation is done by the
   F*-extracted modules. *)

open RDF_Graph_Executable
open SPARQL11_Algebra

(* Issue #275 (rule #11 ASSUME-IO): explicitly realise the JSON-LD
   documentLoader seam as an honest "no remote loading" for this CLI —
   see JSONLD.Loader.fst's banner and jsonld_runner.ml (the ONE
   consumer with a real fixture-file loader). Explicit rather than
   relying on the ref cell's own default so the choice is auditable
   here, not implicit. *)
let () = JSONLD_Loader.jsonld_loader_register (fun _ -> FStar_Pervasives_Native.None)

(* ============================================================================
   Output formatting
   ============================================================================ *)

(* Pretty-printers — F* is the source of truth.
   Logic lives in formal/fstar/RDF.Pretty.fst (extracted as
   RDF_Pretty.ml). The aliases below preserve the legacy names so
   the rest of this file (output formatters, dump-nq, etc.) compiles
   unchanged. *)
let term_to_ntriples t = RDF_Pretty.term_to_ntriples t
let term_to_turtle   t = RDF_Pretty.term_to_turtle   t
let subject_to_string s = RDF_Pretty.subject_to_turtle s

(* Turtle pretty-printer (prefix-compacted, subject-grouped) — logic
   lives in formal/fstar/RDF.Turtle.Serialize.fst (extracted as
   RDF_Turtle_Serialize.ml). This is the "not gratuitously ugly"
   human-facing serializer; --dump-nq / --canonicalize stay on the
   byte-correct N-Quads path (RDF_Canonical). *)
let turtle_of_graph_pretty g = RDF_Turtle_Serialize.turtle_of_graph_auto g

(* ============================================================================
   File I/O helpers
   ============================================================================ *)

let read_file path =
  if path = "-" then begin
    let buf = Buffer.create 4096 in
    (try while true do Buffer.add_char buf (input_char stdin) done
     with End_of_file -> ());
    Buffer.contents buf
  end else begin
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  end

(* RDF format identification — F* is the source of truth.
   Logic lives in formal/fstar/RDF.Format.fst (extracted as
   RDF_Format.ml). The wrappers below re-export the constructors and
   adapt F*'s option to OCaml's native option so existing
   match-Some/None call sites compile unchanged. *)
type rdf_format = RDF_Format.rdf_format =
  | NT
  | Turtle
  | NQuads
  | TriG
  | RDFXML
  | JSONLD

let detect_format filename =
  RDF_Format.detect_format_or_default (Filename.extension filename)

let format_of_string s =
  match RDF_Format.format_of_string s with
  | FStar_Pervasives_Native.Some f -> Some f
  | FStar_Pervasives_Native.None -> None

let format_name = RDF_Format.format_name

let file_base_iri path =
  if path = "-" then None
  else
    let abs = if Filename.is_relative path
              then Filename.concat (Sys.getcwd ()) path
              else path in
    Some ("file://" ^ abs)

(* Stack-safe list helpers for large triple/quad lists.

   OCaml's stdlib (@) and List.concat_map are not tail-recursive on
   their primary argument, so `huge_list @ []` blows the native stack
   on the ~889k-triple scale we see in wikidata-lifesci-kgx/*.ttl.
   The helpers below preserve the same element order as (@) /
   List.concat_map but run in constant stack, using List.rev_append
   (which IS tail-recursive) as their primitive.

   Concrete pattern:
     concat_preserve_order [xs; ys; zs] = xs @ ys @ zs
     concat_map_preserve_order f xs     = List.concat_map f xs
   but both are tail-recursive on the outer spine AND on the inner lists.

   Design sketch: docs/2026-04-21-large-turtle-stack-overflow-fix-sketch.md
*)
let append_preserve_order xs ys =
  List.rev_append (List.rev xs) ys

let concat_preserve_order lists =
  List.rev
    (List.fold_left
       (fun acc xs -> List.rev_append xs acc)
       []
       lists)

let concat_map_preserve_order f xs =
  concat_preserve_order (List.rev_map f xs |> List.rev)

(* Load as dataset, preserving named graph structure for NQuads/TriG.

   Blank-node scoping (priority 2d, Jena graph-probe regression):
   RDF 1.1 scopes bnode labels to their document. Each load_dataset
   call is one document, so every loaded dataset gets its labels
   prefixed with a per-call scope id via the F* renaming
   (RDF.Dataset.Merge.rename_dataset_bnodes — the semantic decision
   lives in F*, this is just the per-document counter). Without this,
   _:x in two separately loaded files spuriously joined. *)
let bnode_scope_counter = ref 0

let scope_dataset_bnodes ds =
  let n = !bnode_scope_counter in
  incr bnode_scope_counter;
  RDF_Dataset_Merge.rename_dataset_bnodes (Printf.sprintf "d%d_" n) ds

let load_dataset ?(format=None) ?(base=None) path =
  let content = read_file path in
  let fmt = match format with Some f -> f | None -> detect_format path in
  let base_iri = match base with Some b -> Some b | None -> file_base_iri path in
  scope_dataset_bnodes @@ match fmt with
  | NQuads ->
    Parser_NQuads.parse_nquads content
  | TriG ->
    (match base_iri with
     | Some b -> Parser_TriG.parse_trig_with_base_lenient content b
     | None -> Parser_TriG.parse_trig_lenient content)
  | JSONLD ->
    (* Context processing (JSONLD.Context/JSONLD.Expand) + document
       base threading per issue #275 — see
       formal/fstar/Parser.JSONLD.fst module banner. Remote contexts /
       "@import" are an honest FAIL here (no loader registered — see
       this file's top-of-file jsonld_loader_register call): the CLI
       has no notion of "the URL this file was loaded from" beyond a
       local file:// base. *)
    let fs_base = match base_iri with
      | Some b -> FStar_Pervasives_Native.Some b
      | None -> FStar_Pervasives_Native.None in
    (match Parser_JSONLD.parse_jsonld content fs_base FStar_Pervasives_Native.None FStar_Pervasives_Native.None FStar_Pervasives_Native.None with
     | FStar_Pervasives_Native.Some ds -> ds
     | FStar_Pervasives_Native.None ->
       failwith "invalid JSON-LD (parse or unsupported feature — remote contexts need a loader this CLI does not have)")
  | _ ->
    let triples = match fmt with
      | NT -> Parser_NTriples.parse_ntriples content
      | Turtle ->
        (match base_iri with
         | Some b -> Parser_Turtle.parse_turtle_with_base content b
         | None -> Parser_Turtle.parse_turtle content)
      | RDFXML ->
        (match base_iri with
         | Some b -> Parser_RDFXML.parse_rdfxml_with_base b content
         | None -> Parser_RDFXML.parse_rdfxml content)
      | _ -> [] in
    RDF_Graph_Executable.({ ds_default = triples; ds_named = [] })

let load_triples ?(format=None) ?(base=None) path =
  let ds = load_dataset ~format ~base path in
  match ds.ds_named with
  | [] -> ds.ds_default
  | named ->
    concat_preserve_order
      (ds.ds_default :: List.map (fun ng -> ng.ng_graph) named)

(* Load a COTTAS/Parquet artifact as an rdf_dataset.

   COTTAS files are Parquet files with four string columns
   (subject, predicate, object, graph). The F*-verified Parquet.Footer
   module decodes the DeltaLengthByteArray column values; the Ballyhoo
   COTTAS runtime glue (experimental_ocaml_glue/cottas_runtime.sh) maps
   those string tokens to RDF terms and caches them in a module-local
   Hashtbl. We call cottas_open_dataset_store to populate the cache,
   then iterate the cache's quads to re-emit them as an rdf_dataset
   with a default graph + one named graph per distinct graph IRI.

   This is hand-written CLI glue, not F*-extracted. It's fine: the RDF
   semantic work (term parsing, Parquet decoding) all lives in F*; we
   only reshape the result. *)
let load_cottas_dataset path =
  match Parser_BallyhooCOTTAS.cottas_open_dataset_store path FStar_Pervasives_Native.None with
  | FStar_Pervasives_Native.None ->
    Printf.eprintf "Error: could not open COTTAS artifact: %s\n" path;
    exit 1
  | FStar_Pervasives_Native.Some ds ->
    let cache = Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.cache_for_store ds in
    let open Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime in
    (* OCaml-side resolution: hashtable lookups are O(1); F* lists
       are O(n). For parliament-scale corpora only the OCaml hashtable
       path is tractable. The pure FOLD that buckets resolved quads
       lives in F* at RDF.Store.Loader.bucket_quads.
       #200 Section A non-codename migration, 2026-05-09. *)
    let resolved = List.map (fun row ->
      let s = match Hashtbl.find_opt cache.id_to_subject row.qr_s with
        | Some s -> s
        | None -> failwith "cottas: missing subject id" in
      let p = match Hashtbl.find_opt cache.id_to_predicate row.qr_p with
        | Some p -> p
        | None -> failwith "cottas: missing predicate id" in
      let o = match Hashtbl.find_opt cache.id_to_object row.qr_o with
        | Some o -> o
        | None -> failwith "cottas: missing object id" in
      let triple = RDF_Graph_Executable.({ s; p; o }) in
      let g_opt = match row.qr_g with
        | None -> FStar_Pervasives_Native.None
        | Some gid ->
          (match Hashtbl.find_opt cache.id_to_graph gid with
           | Some g_iri -> FStar_Pervasives_Native.Some g_iri
           | None -> failwith "cottas: missing graph id") in
      RDF_Store_Loader.({ rq_triple = triple; rq_graph = g_opt })
    ) cache.quads in
    RDF_Store_Loader.bucket_quads resolved

let open_cottas_ondisk_store path =
  match RDF_CottasStore.cottas_ondisk_open path with
  | FStar_Pervasives_Native.Some store -> store
  | FStar_Pervasives_Native.None ->
    Printf.eprintf "Error: could not open on-disk COTTAS artifact: %s\n" path;
    exit 1

(* HDT program plan stage 4 (docs/designissues/2026-07-06-hdt-program-
   plan.md): open an HDT artifact through the verified stage 1-3
   reader chain (Parser_BallyhooHDT.hdt_open_graph_store, itself pure
   F* calling HDT_Container/HDT_Dictionary/HDT_Triples -- no HDT-
   specific OCaml glue left to call into). `None` means the container
   inventory or triples section failed to parse (wrong cookie, a
   CRC mismatch, or truncation) -- loud failure, same posture as
   open_cottas_ondisk_store above. *)
let open_hdt_store path =
  match Parser_BallyhooHDT.hdt_open_graph_store FStar_Pervasives_Native.None path
          FStar_Pervasives_Native.None with
  | FStar_Pervasives_Native.Some store -> store
  | FStar_Pervasives_Native.None ->
    Printf.eprintf "Error: could not open HDT artifact: %s\n" path;
    exit 1

(* In-memory bytes store, stage 3 (docs/designissues/2026-07-06-
   inmemory-bytes-store.md): `--data-cottas-mem FILE` reads FILE fully
   into an OCaml string and registers it under a synthetic handle via
   `Parquet_Footer.register_memory_buffer` (stage 1's glue addition,
   experimental_ocaml_glue/parquet_footer_zz_register_memory_buffer.sh)
   -- the SAME process-wide cache `--data-cottas`'s real-path reads
   already populate. The synthetic handle is then pushed onto
   `cfg.data_cottas_files` exactly like a real path would be: every
   existing consumer of that list (`open_cottas_ondisk_store`, the
   dataset-backend builder, the delta-log overlay wiring) works
   unmodified, because from their point of view it IS just a path
   string that happens to already be cached. This is the whole point
   of the design doc's §2.1 finding -- no new query logic, one new
   glue entry point, reused everywhere `--data-cottas` already flows. *)
let mem_handle_counter = ref 0

let register_cottas_mem_file (f : string) : string =
  if not (Sys.file_exists f) then begin
    Printf.eprintf "Error: --data-cottas-mem file not found: %s\n" f; exit 1
  end;
  let ic = open_in_bin f in
  let len = in_channel_length ic in
  let bytes =
    try really_input_string ic len
    with e -> close_in_noerr ic; raise e
  in
  close_in ic;
  incr mem_handle_counter;
  let handle = Printf.sprintf "mem:%d:%s" !mem_handle_counter f in
  Parquet_Footer.register_memory_buffer handle bytes;
  handle

(* Durable-UPDATE stage 4 (compaction) needs this reader in TWO places:
   here (so an ordinary query sees the epoch-filtered delta a compacted
   store requires) and in `run_compact` below (to decide what "already
   folded" means for the NEXT compaction) -- defined once, shared.
   `module DLog` is likewise shared with `run_compact`'s much larger
   compaction banner further down this file. *)
module DLog = RDF_Store_Columnar_DeltaLog

(* Best-effort: does `<version_dir>/data.compacted-epoch` exist, and if
   so what epoch does it record? `None` = never compacted -- nothing to
   skip (matches SPARQL11_Store.cottas_with_delta_dataset_backend's own
   `compacted_epoch : option nat` contract). *)
let read_compacted_epoch (version_dir : string) : Z.t option =
  let marker = Filename.concat version_dir "data.compacted-epoch" in
  if not (Sys.file_exists marker) then None
  else
    let bytes = DLog.delta_log_read_all marker in
    match DLog.parse_compacted_epoch bytes with
    | FStar_Pervasives_Native.Some n -> Some n
    | FStar_Pervasives_Native.None -> None

let read_compacted_epoch_opt (version_dir : string) : Z.t FStar_Pervasives_Native.option =
  match read_compacted_epoch version_dir with
  | Some n -> FStar_Pervasives_Native.Some n
  | None -> FStar_Pervasives_Native.None

(* Durable-UPDATE stage 3 (merge-on-read, docs/designissues/2026-07-06-
   durable-update-design.md) -- CLI-side plumbing only (rule #11: this
   file is a consumer, not the verified library). `--delta-log PATH`
   pairs with exactly one `--data-cottas` store: reads through that
   store now see the delta, via SPARQL11_Store.cottas_with_delta_
   dataset_backend (the F*-side D-overlay wiring -- RDF.Store.
   Capabilities.Delta.fst's `overlay`, reached through SPARQL11.Store's
   GB_CottasOnDiskDelta arm, no new dispatch logic on this side). *)
let build_dataset_backend
    (in_memory : RDF_Graph_Executable.rdf_dataset)
    (cottas_stores : RDF_CottasStore.cottas_ondisk_store list)
    (cottas_paths : string list)
    (delta_log_path : string option)
    (hdt_stores : Parser_BallyhooHDT.hdt_graph_store list)
    : SPARQL11_Store.dataset_backend =
  let module S = SPARQL11_Store in
  let in_memory_backend = S.indexed_dataset_backend in_memory in
  (* HDT program plan stage 4: read-only, triples-only (no HDTQ yet,
     docs/designissues/2026-07-06-hdt-program-plan.md "Out of scope"),
     so every HDT store is a default-graph-only backend with no named
     graphs -- same shape indexed_dataset_backend/cottas_ondisk_
     dataset_backend build for their own default graph. *)
  let hdt_backends =
    List.map
      (fun (hgs : Parser_BallyhooHDT.hdt_graph_store) ->
         S.({ dsb_default = GB_HDT hgs; dsb_named = [] }))
      hdt_stores
  in
  match delta_log_path, cottas_stores, cottas_paths with
  | Some log_path, [ cods ], [ cpath ] ->
    (* Durable-UPDATE stage 4: an ordinary query against a store that
       has been compacted must see the SAME epoch-filtered delta the
       `compact` command itself reads (this file's `read_compacted_
       epoch`, defined below with the rest of stage 4's compaction
       code) -- otherwise a ordinary `--data-cottas current/data.cottas
       --delta-log PATH` query would double-apply whatever the last
       compaction already folded in, exactly the crash-window bug
       filter_batches_since_epoch exists to prevent. *)
    let epoch = read_compacted_epoch_opt (Filename.dirname cpath) in
    let delta_backend = S.cottas_with_delta_dataset_backend cods log_path epoch in
    RDF_Store_Combine.combine_dataset_backends
      ([ in_memory_backend; delta_backend ] @ hdt_backends)
  | Some _, _, _ ->
    Printf.eprintf
      "Error: --delta-log requires exactly one --data-cottas store (got %d)\n"
      (List.length cottas_stores);
    exit 1
  | None, _, _ ->
    let cottas_backends =
      List.map S.cottas_ondisk_dataset_backend cottas_stores
    in
    RDF_Store_Combine.combine_dataset_backends
      (in_memory_backend :: (cottas_backends @ hdt_backends))

(* ============================================================================
   Result table formatting (like arq / isql)
   ============================================================================ *)

let print_results_table vars rows =
  if rows = [] then
    Printf.printf "(no results)\n"
  else begin
    (* Compute column widths *)
    let col_widths = List.map (fun v ->
      let header_w = String.length v + 1 in  (* +1 for ? prefix *)
      let data_w = List.fold_left (fun mx row ->
        match List.assoc_opt v row with
        | Some t -> max mx (String.length (term_to_turtle t))
        | None -> mx
      ) 0 rows in
      max header_w data_w
    ) vars in
    (* Separator line *)
    let sep = String.concat "+" ("" :: List.map (fun w ->
      String.make (w + 2) '-') col_widths @ [""]) in
    Printf.printf "%s\n" sep;
    (* Header *)
    Printf.printf "|";
    List.iter2 (fun v w ->
      Printf.printf " %-*s |" w ("?" ^ v)
    ) vars col_widths;
    Printf.printf "\n%s\n" sep;
    (* Data rows *)
    List.iter (fun row ->
      Printf.printf "|";
      List.iter2 (fun v w ->
        let cell = match List.assoc_opt v row with
          | Some t -> term_to_turtle t
          | None -> "" in
        Printf.printf " %-*s |" w cell
      ) vars col_widths;
      Printf.printf "\n"
    ) rows;
    Printf.printf "%s\n" sep;
    Printf.printf "%d result(s)\n" (List.length rows)
  end

let print_results_csv vars rows =
  Printf.printf "%s\n" (String.concat "," vars);
  List.iter (fun row ->
    let cells = List.map (fun v ->
      match List.assoc_opt v row with
      | Some (T_IRI i) -> i
      | Some (T_BNode b) -> "_:" ^ b
      | Some (T_Literal l) -> l.lexical_form
      | None -> ""
    ) vars in
    Printf.printf "%s\n" (String.concat "," cells)
  ) rows

(* json_escape and json_term delegate to F*: SPARQL.JSON.Escape and
   SPARQL.Protocol own the SPARQL Results JSON byte-level rendering.
   factoidal_http.ml already does the same delegation; this brings
   factoidal_cli.ml in line. Rule #1 / #11. *)
let json_escape s = SPARQL_JSON_Escape.json_escape s
let json_term t = SPARQL_Protocol.json_term t

let print_results_json vars rows =
  let vars_json = String.concat "," (List.map (fun v ->
    Printf.sprintf "\"%s\"" (json_escape v)) vars) in
  Printf.printf "{\n";
  Printf.printf "  \"head\": { \"vars\": [%s] },\n" vars_json;
  Printf.printf "  \"results\": {\n";
  Printf.printf "    \"bindings\": [";
  let first = ref true in
  List.iter (fun row ->
    if !first then first := false else Printf.printf ",";
    Printf.printf "\n      {";
    let bfirst = ref true in
    List.iter (fun v ->
      match List.assoc_opt v row with
      | None -> ()
      | Some t ->
        if !bfirst then bfirst := false else Printf.printf ",";
        Printf.printf " \"%s\": %s" (json_escape v) (json_term t)
    ) vars;
    Printf.printf " }"
  ) rows;
  Printf.printf "\n    ]\n";
  Printf.printf "  }\n";
  Printf.printf "}\n"

let print_results_ntriples triples =
  List.iter (fun t ->
    let s = match t.s with
      | S_IRI i -> Printf.sprintf "<%s>" i
      | S_BNode b -> Printf.sprintf "_:%s" b in
    let p = Printf.sprintf "<%s>" t.p in
    let o = term_to_ntriples t.o in
    Printf.printf "%s %s %s .\n" s p o
  ) triples

(* ============================================================================
   CLI parsing
   ============================================================================ *)

type output_format = Table | CSV | NTOut | JSON

type config = {
  mutable data_files : string list;
  mutable data_cottas_files : string list;  (* COTTAS/Parquet artifacts *)
  mutable data_hdt_files : string list;     (* HDT artifacts, read-only, default graph only *)
  mutable delta_log_path : string option;   (* durable-UPDATE stage 3: --delta-log PATH *)
  mutable named_graphs : (string * string) list;  (* (iri, file) *)
  mutable query_file : string option;
  mutable query_string : string option;
  mutable base_iri : string option;
  mutable input_format : rdf_format option;
  mutable output_format : output_format;
  mutable dump_mode : bool;
  mutable dump_nq_mode : bool;
  mutable dump_turtle_mode : bool;
  mutable canonicalize_mode : bool;  (* RDFC-1.0 canonical N-Quads *)
  mutable count_mode : bool;
  mutable explain_mode : bool;     (* --explain: parse + plan + estimate, no execution *)
  mutable explain_out : string option;  (* --explain-out=PATH for JSON sidecar *)
  mutable help_mode : bool;
  mutable version_mode : bool;
  mutable entail_regime : string;  (* "" (none), "RDFS", or "OWL-RL" *)
}

(* Shared SELECT/ASK output formatter — factored out of the query-
   evaluation tail (was inline, see git history) so the parse-stream
   query fast path (docs/designissues/2026-07-05-disk-backed-db-perf-
   review.md) and the materialise-then-evaluate path print through
   the EXACT same code, byte for byte, rather than two hand-maintained
   copies that could quietly drift apart. Takes exactly what either
   path already has in hand: the parsed query (for SELECT's projected
   var list), an ASK answer if this is an ASK query, and the SELECT
   result rows (empty for ASK). *)
let print_query_results (cfg : config) (query : SPARQL11_Algebra.query)
    (ask_answer : bool option)
    (results : (string * RDF_Graph_Executable.rdf_term) list list) : unit =
  let vars = match query.q_form with
    | QF_Select (Select_Vars items) ->
      List.filter_map (fun item -> match item with
        | SI_Var v -> Some v
        | SI_Expr (_, v) -> Some v
      ) items
    | _ ->
      (* Star projection or non-SELECT — collect all vars from results *)
      let seen = Hashtbl.create 16 in
      List.concat_map (fun row ->
        List.filter_map (fun (v, _) ->
          if Hashtbl.mem seen v then None
          else (Hashtbl.add seen v (); Some v)
        ) row
      ) results
  in
  match cfg.output_format with
  | Table ->
    (match ask_answer with
     | Some b ->
       let lexical =
         match SPARQL11_Algebra.er_to_string (SPARQL11_Algebra.ER_Bool b) with
         | FStar_Pervasives_Native.Some s -> s
         | FStar_Pervasives_Native.None -> if b then "true" else "false"
       in
       Printf.printf "%s\n" lexical
     | None -> print_results_table vars results)
  | CSV -> print_results_csv vars results
  | JSON ->
    (match ask_answer with
     | Some b ->
       Printf.printf "{\n  \"head\": {},\n  \"boolean\": %s\n}\n"
         (if b then "true" else "false")
     | None -> print_results_json vars results)
  | NTOut ->
    (* For CONSTRUCT-like output, print triples *)
    List.iter (fun row ->
      List.iter (fun (v, t) ->
        Printf.printf "?%s = %s  " v (term_to_turtle t)
      ) row;
      Printf.printf "\n"
    ) results

(* Normalise --entail argument: accept case-insensitive and with/without
   hyphen variants. Maps to the regime tags expected by F*'s
   entailment_closure: "RDFS", "OWL-RL", or "" for none. *)
let normalise_entail_regime s =
  let lc = String.lowercase_ascii s in
  match lc with
  | "" | "none" | "no" | "off" -> Some ""
  | "rdfs" -> Some "RDFS"
  | "owl-rl" | "owlrl" | "owl_rl" | "owl" -> Some "OWL-RL"
  | _ -> None

let usage () =
  Printf.printf "factoidal — formally verified SPARQL query tool\n\n";
  Printf.printf "SPARQL query:\n";
  Printf.printf "  factoidal --data FILE --query FILE.rq\n";
  Printf.printf "  factoidal --data FILE -e 'SELECT * WHERE { ?s ?p ?o }'\n";
  Printf.printf "  factoidal -d file1.ttl -d file2.nt --query q.rq\n";
  Printf.printf "  cat data.ttl | factoidal -d - -e 'SELECT ...'\n";
  Printf.printf "\n";
  Printf.printf "Named graphs (N-Quads / TriG):\n";
  Printf.printf "  factoidal -d data.nq -e 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }'\n";
  Printf.printf "  factoidal -d data.trig -e 'SELECT ?g ?s WHERE { GRAPH ?g { ?s ?p ?o } }'\n";
  Printf.printf "  factoidal -d data.nq -e 'SELECT * WHERE { ?s ?p ?o }'  (queries default graph)\n";
  Printf.printf "\n";
  Printf.printf "RDF parsing/dump:\n";
  Printf.printf "  factoidal --dump FILE.ttl           Parse and dump as N-Triples\n";
  Printf.printf "  factoidal --dump-nq FILE.trig       Parse and dump as sorted N-Quads\n";
  Printf.printf "  factoidal --dump-turtle FILE.nt     Parse and dump as pretty-printed Turtle\n";
  Printf.printf "  factoidal --canonicalize FILE.trig  RDFC-1.0 canonical N-Quads\n";
  Printf.printf "  factoidal --count FILE.ttl          Count triples\n";
  Printf.printf "  factoidal --dump --format rdfxml FILE.rdf\n";
  Printf.printf "\n";
  Printf.printf "Options:\n";
  Printf.printf "  -d, --data FILE        Load RDF data (repeatable, \"-\" for stdin)\n";
  Printf.printf "                         Format auto-detected from extension:\n";
  Printf.printf "                         .ttl .nt .nq .nquads .trig .rdf .xml .owl .jsonld\n";
  Printf.printf "      --data-cottas FILE Load a COTTAS/Parquet dataset (repeatable).\n";
  Printf.printf "                         Parsed via the F*-verified Parquet footer\n";
  Printf.printf "                         + DeltaLengthByteArray decoder; Zstd\n";
  Printf.printf "                         decompression via the C stub.\n";
  Printf.printf "      --data-cottas-mem FILE  Read FILE fully into memory and query it\n";
  Printf.printf "                         through the SAME on-disk COTTAS code path via a\n";
  Printf.printf "                         synthetic byte-cache handle (repeatable). No\n";
  Printf.printf "                         file is opened again after the initial read;\n";
  Printf.printf "                         composes with --delta-log like --data-cottas.\n";
  Printf.printf "      --delta-log PATH   Durable-UPDATE stage 3 (merge-on-read): read\n";
  Printf.printf "                         --data-cottas's store composed with the delta\n";
  Printf.printf "                         batches recorded at PATH. Requires exactly one\n";
  Printf.printf "                         --data-cottas FILE.\n";
  Printf.printf "      --data-hdt FILE    Load a read-only HDT (Header-Dictionary-Triples)\n";
  Printf.printf "                         artifact (repeatable). Default graph only (no\n";
  Printf.printf "                         named graphs -- HDTQ is a separate, deferred\n";
  Printf.printf "                         extension); SELECT/ASK only.\n";
  Printf.printf "  -n, --named IRI=FILE   Load named graph\n";
  Printf.printf "  -q, --query FILE       SPARQL query file\n";
  Printf.printf "  -e SPARQL              Inline SPARQL query string\n";
  Printf.printf "  -b, --base IRI         Base IRI for parsing\n";
  Printf.printf "  -f, --format FMT       Input format: turtle, ntriples, nquads, trig, rdfxml,\n";
  Printf.printf "                         jsonld (Phase 1: expanded form only)\n";
  Printf.printf "  -o, --output FMT       Output format: table (default), csv, ntriples, json\n";
  Printf.printf "  --entail REGIME        Apply entailment closure to loaded data before\n";
  Printf.printf "                         query evaluation. REGIME is one of:\n";
  Printf.printf "                           none    no closure (default)\n";
  Printf.printf "                           RDFS    RDFS closure + reflexivity axioms\n";
  Printf.printf "                           OWL-RL  OWL 2 RL Datalog subset (includes RDFS)\n";
  Printf.printf "                         Case-insensitive. All closures are F*-extracted.\n";
  Printf.printf "  --dump                 Parse RDF and dump as N-Triples\n";
  Printf.printf "  --dump-nq              Parse RDF and dump as canonical N-Quads\n";
  Printf.printf "  --dump-turtle          Parse RDF and dump as pretty-printed Turtle\n";
  Printf.printf "                         (prefix-compacted, subject-grouped)\n";
  Printf.printf "  --count                Parse RDF and count triples\n";
  Printf.printf "  --explain '<SPARQL>'   Plan dump without executing.\n";
  Printf.printf "                         Reports algebra tree, per-triple-pattern\n";
  Printf.printf "                         estimate, and join order. Requires\n";
  Printf.printf "                         --data-cottas FILE.\n";
  Printf.printf "  --explain-only         Enable explain on -e / --query input.\n";
  Printf.printf "  --explain-out PATH     Write JSON explain to PATH.\n";
  Printf.printf "  --version              Show version\n";
  Printf.printf "  --help                 This help\n";
  Printf.printf "\n";
  Printf.printf "Supported RDF formats:  Turtle (.ttl), N-Triples (.nt), N-Quads (.nq),\n";
  Printf.printf "                        TriG (.trig), RDF/XML (.rdf, .xml, .owl),\n";
  Printf.printf "                        JSON-LD expanded form (.jsonld)\n";
  Printf.printf "Supported query forms:  SELECT, ASK, CONSTRUCT\n";
  Printf.printf "\n";
  Printf.printf "N-Quads and TriG files preserve named graph structure. Use GRAPH\n";
  Printf.printf "patterns in SPARQL to query specific graphs. Without GRAPH, only\n";
  Printf.printf "the default graph is queried.\n";
  Printf.printf "\n";
  Printf.printf "All parsing and query evaluation is performed by formally verified\n";
  Printf.printf "F* code, extracted to OCaml. See https://github.com/danbri/factoidal\n"

let version () =
  Printf.printf "factoidal 0.1.0 (F*-extracted SPARQL/RDF)\n"

(* parse_args reads from an explicit args list (NOT Sys.argv directly) so
   the subcommand dispatcher can hand it the post-subcommand tail. The
   default ?args defaults to (Array.to_list Sys.argv |> List.tl) for the
   legacy callers. *)
let parse_args ?args () =
  let cfg = {
    data_files = []; data_cottas_files = []; data_hdt_files = []; delta_log_path = None; named_graphs = []; query_file = None;
    query_string = None; base_iri = None; input_format = None;
    output_format = Table; dump_mode = false; dump_nq_mode = false;
    dump_turtle_mode = false;
    canonicalize_mode = false; count_mode = false;
    explain_mode = false; explain_out = None;
    help_mode = false; version_mode = false;
    entail_regime = "";
  } in
  let args = match args with
    | Some a -> a
    | None -> Array.to_list Sys.argv |> List.tl in
  let rec loop = function
    | [] -> ()
    | ("--help" | "-h") :: _ -> cfg.help_mode <- true
    | "--version" :: _ -> cfg.version_mode <- true
    | ("--data" | "-d") :: f :: rest -> cfg.data_files <- cfg.data_files @ [f]; loop rest
    | "--data-cottas" :: f :: rest ->
      cfg.data_cottas_files <- cfg.data_cottas_files @ [f]; loop rest
    | "--data-cottas-mem" :: f :: rest ->
      (* Stage 3, in-memory bytes store: load FILE fully into RAM and
         query it through the SAME on-disk COTTAS code path via a
         synthetic cache handle -- see register_cottas_mem_file above. *)
      cfg.data_cottas_files <- cfg.data_cottas_files @ [register_cottas_mem_file f]; loop rest
    | "--data-hdt" :: f :: rest ->
      (* HDT program plan stage 4 (docs/designissues/2026-07-06-hdt-
         program-plan.md): a read-only, default-graph-only backend --
         see build_dataset_backend's hdt handling below. *)
      cfg.data_hdt_files <- cfg.data_hdt_files @ [f]; loop rest
    | "--delta-log" :: f :: rest ->
      cfg.delta_log_path <- Some f; loop rest
    | ("--named" | "-n") :: spec :: rest ->
      (* spec is IRI=FILE *)
      (match String.index_opt spec '=' with
       | Some i ->
         let iri = String.sub spec 0 i in
         let file = String.sub spec (i+1) (String.length spec - i - 1) in
         cfg.named_graphs <- cfg.named_graphs @ [(iri, file)]
       | None ->
         Printf.eprintf "Error: --named requires IRI=FILE format\n"; exit 1);
      loop rest
    | ("--query" | "-q") :: f :: rest -> cfg.query_file <- Some f; loop rest
    | "-e" :: q :: rest -> cfg.query_string <- Some q; loop rest
    | ("--base" | "-b") :: b :: rest -> cfg.base_iri <- Some b; loop rest
    | ("--format" | "-f") :: fmt :: rest ->
      (match format_of_string fmt with
       | Some f -> cfg.input_format <- Some f; loop rest
       | None -> Printf.eprintf "Error: unknown format '%s'\n" fmt; exit 1)
    | ("--output" | "-o") :: fmt :: rest ->
      (match String.lowercase_ascii fmt with
       | "table" -> cfg.output_format <- Table; loop rest
       | "csv" -> cfg.output_format <- CSV; loop rest
       | "ntriples" | "nt" -> cfg.output_format <- NTOut; loop rest
       | "json" | "srj" -> cfg.output_format <- JSON; loop rest
       | _ -> Printf.eprintf "Error: unknown output format '%s'\n" fmt; exit 1)
    | "--entail" :: regime :: rest ->
      (match normalise_entail_regime regime with
       | Some r -> cfg.entail_regime <- r; loop rest
       | None ->
         Printf.eprintf "Error: unknown entailment regime '%s' (expected none, RDFS, or OWL-RL)\n" regime;
         exit 1)
    | "--dump" :: rest -> cfg.dump_mode <- true; loop rest
    | "--dump-nq" :: rest -> cfg.dump_nq_mode <- true; loop rest
    | "--dump-turtle" :: rest -> cfg.dump_turtle_mode <- true; loop rest
    | "--canonicalize" :: rest -> cfg.canonicalize_mode <- true; loop rest
    | "--count" :: rest -> cfg.count_mode <- true; loop rest
    | "--explain" :: q :: rest ->
      (* `--explain SPARQL` is the new "plan dump without execution" mode.
         The argument is the SPARQL query text (or use --query-file with
         --explain-only).  See factoidal_explain.ml. *)
      cfg.explain_mode <- true;
      cfg.query_string <- Some q;
      loop rest
    | "--explain-only" :: rest ->
      (* Variant: enable explain mode but expect --query / -e to provide
         the query text.  Useful when the query is in a file. *)
      cfg.explain_mode <- true;
      loop rest
    | "--explain-out" :: f :: rest ->
      cfg.explain_out <- Some f; loop rest
    | arg :: rest ->
      if String.length arg > 0 && arg.[0] = '-' then begin
        Printf.eprintf "Error: unknown option '%s' (try --help)\n" arg; exit 1
      end else begin
        (* Bare filename — treat as data file *)
        cfg.data_files <- cfg.data_files @ [arg]; loop rest
      end
  in
  loop args;
  cfg

(* ============================================================================
   Subcommand dispatcher (Phase 0 navigation + Phase 1 exec shims)

   Design + scope: docs/designissues/2026-04-25-unified-factoidal-cli-plan.md

   `factoidal` historically takes long flags (--data, --query, --dump,
   --count). We're consolidating to a git/cargo-style subcommand surface
   without breaking the old form. Strategy:

     * If argv[1] is a recognised subcommand keyword, dispatch.
     * Otherwise fall through to the legacy flag parser below.

   The keyword detector is conservative — it only triggers on bare words
   in a fixed set, never on flag-shaped tokens. That means
   `factoidal --data X --query Q.rq` stays untouched. *)

let known_subcommands =
  ["help"; "version"; "query"; "serve"; "dump"; "dump-nq"; "dump-turtle"; "canonicalize";
   "count"; "test"; "cottas-import"; "cottas-info"; "graphs"; "validate"; "compact"; "import";
   "shacl"; "shex"; "rml"; "csvw"; "jsonld"; "rif"; "entail"; "update"]

(* Locate a sibling binary by the same convention busybox uses: look in
   the same directory as argv[0] first, fall back to PATH. *)
let sibling_binary name =
  let argv0_dir = Filename.dirname Sys.executable_name in
  let candidate = Filename.concat argv0_dir name in
  if Sys.file_exists candidate then Some candidate
  else None  (* PATH lookup happens implicitly via execvp *)

(* exec a sibling: replace current process so signals/ttys behave right.
   On Windows this would need Sys.command, but factoidal-http already
   refuses to build on Windows (Unix-only), so Unix.execv is fine. *)
let exec_sibling name args =
  let path = match sibling_binary name with
    | Some p -> p
    | None -> name  (* let execvp search PATH *)
  in
  let argv = Array.of_list (path :: args) in
  try Unix.execvp path argv
  with Unix.Unix_error (e, _, _) ->
    Printf.eprintf
      "factoidal: could not exec '%s' (%s).\n\
       This subcommand is a thin shim — it requires the standalone\n\
       binary to be available next to factoidal or on PATH.\n\
       Build it with: cd formal/fstar && ./build-ocaml.sh compile\n"
      name (Unix.error_message e);
    exit 127

(* Find the repo root by walking up from argv[0] looking for
   tools/corpus_pipeline.py. Honour FACTOIDAL_REPO_ROOT if set. *)
let find_repo_root () =
  match Sys.getenv_opt "FACTOIDAL_REPO_ROOT" with
  | Some p when Sys.file_exists p -> Some p
  | _ ->
    let argv0_dir = Filename.dirname (
      if Filename.is_relative Sys.executable_name
      then Filename.concat (Sys.getcwd ()) Sys.executable_name
      else Sys.executable_name
    ) in
    let rec walk dir =
      let candidate = Filename.concat dir "tools/corpus_pipeline.py" in
      if Sys.file_exists candidate then Some dir
      else
        let parent = Filename.dirname dir in
        if parent = dir then None else walk parent
    in
    walk argv0_dir

let exec_corpus_pipeline subcmd args =
  match find_repo_root () with
  | None ->
    Printf.eprintf
      "factoidal: cottas-import needs tools/corpus_pipeline.py.\n\
       Could not locate repo root above %s.\n\
       Set FACTOIDAL_REPO_ROOT=/path/to/factoidal and retry.\n"
      Sys.executable_name;
    exit 127
  | Some root ->
    let script = Filename.concat root "tools/corpus_pipeline.py" in
    let argv = Array.of_list ("python3" :: script :: subcmd :: args) in
    (try Unix.execvp "python3" argv
     with Unix.Unix_error (e, _, _) ->
       Printf.eprintf
         "factoidal: could not exec python3 %s: %s\n"
         script (Unix.error_message e);
       exit 127)

(* ============================================================================
   Durable-UPDATE stage 4: compaction ("factoidal compact")
   docs/designissues/2026-07-06-durable-update-design.md §3.3 step 5 / §5
   row 4. Consumer-side orchestration only (rule #11's last paragraph):
   every byte-format DECISION (what the compacted-epoch marker looks
   like, which delta batches survive an epoch filter, how base ⊕ delta
   materializes into one rdf_dataset) is F* -- RDF.Store.Columnar.
   DeltaLog.fst's serialize/parse_compacted_epoch + filter_batches_
   since_epoch, and SPARQL11.Store.fst's materialize_dataset_backend.
   This function only decides WHEN to call those, invokes the EXISTING
   corpus_pipeline.py import pipeline unmodified (rule #15: no new
   store-writing logic), and performs the atomic swap with the SAME
   five stage-2 I/O primitives (issue #282) already used by the delta
   log itself -- zero new `assume val`s.

   ---------------------------------------------------------------------
   Directory-layout / swap-protocol decision (the design doc under-
   specifies this: §3.3 step 5 says "atomic_rename the temp base over
   the live path" for what reads like a single file, but a compacted
   COTTAS base is actually a SET of files -- data.cottas plus its eager
   sidecars plus this stage's own data.compacted-epoch plus a few
   metadata files. One `atomic_rename` cannot swap a SET of files as
   one step, and renaming a whole directory ONTO an existing non-empty
   directory is not POSIX-atomic (rename(2) refuses unless the target
   is empty). Disclosed decision: symlink indirection, the standard
   "atomic release swap" pattern --

     <chunk_dir>/v1/          the FIRST import (corpus_pipeline.py's own
                               convention; unchanged, always directly
                               queryable by its own path)
     <chunk_dir>/v2/, v3/...  one full artifact SET per compaction,
                               written to a FRESH, never-yet-referenced
                               directory name -- an existing version is
                               never mutated in place
     <chunk_dir>/current      a SYMLINK to "v1"/"v2"/... -- the live
                               pointer. Renaming a symlink onto an
                               existing name (`atomic_rename`, the SAME
                               issue-#282 primitive the base-file swap
                               itself uses) is a single atomic syscall
                               with NO window where the name is absent
                               -- unlike a directory rename, which needs
                               the old target removed first. This one
                               property is what makes the WHOLE artifact
                               set become visible together, atomically.

   Callers wanting the crash-safe live view point `--data-cottas` at
   `<chunk_dir>/current/data.cottas` (this command prints that path on
   success). Any earlier version (`v1/data.cottas`, ...) remains
   directly queryable and untouched.

   The delta log is NOT inside a version directory -- it is a
   store-level, not a base-version-level, artifact (the same logical
   append stream survives across many compactions) -- and is truncated
   via its own temp-write + atomic_rename + fsync_dir, identical in
   shape to stage 2's own protocol, reusing the same functions.

   Crash-safety argument (a kill at ANY point during this function):
     - before the `current` rename (step 6 below): `current` still
       resolves to whatever it did before this run (or does not exist
       yet, on a store's very first compaction) -- the pre-compaction
       base and the pre-compaction, untouched delta log are both
       exactly as they were. A half-written v2/v3/... directory is
       orphaned garbage, never referenced by `current`, harmless.
     - after the `current` rename, before the delta-log truncate
       (step 7): a reader opening `current` gets the fully-compacted
       new base (durable -- every file in it was fsynced, then the
       directory itself fsynced, BEFORE the symlink flip). The delta
       log may still physically contain the just-folded batch(es), but
       `filter_batches_since_epoch` (keyed off the new base's own
       data.compacted-epoch) makes their contribution zero -- the
       composed read gives EXACTLY the post-compaction view regardless
       of whether truncation ever runs. Log truncation is thus a
       space-reclamation step, not a correctness dependency, given the
       epoch filter is wired into the read path
       (SPARQL11_Store.cottas_with_delta_dataset_backend).
     - after the delta-log truncate completes: same post-compaction
       view, smaller log file.
   In every case: the store opens readable, and its content is EXACTLY
   the pre- or the post-compaction view -- never a third state.

   Single-writer assumption (open decision 4, disclosed): this command
   assumes no OTHER process appends to the SAME delta log while it
   runs -- an "explicit `factoidal compact`, one at a time" operational
   model (open decision 1's recommended starting point, not an
   automatic background trigger). A concurrent appender writing to the
   live delta log during compaction could have its batch's effect
   lost when the log is truncated post-swap; that hazard is open
   decision 4's own scope, not re-solved here.
   ---------------------------------------------------------------------- *)

let read_whole_fd fd =
  let buf = Buffer.create 65536 in
  let chunk = Bytes.create 65536 in
  let rec loop () =
    let n = Unix.read fd chunk 0 65536 in
    if n > 0 then begin Buffer.add_subbytes buf chunk 0 n; loop () end
  in
  (try loop () with Unix.Unix_error _ -> ());
  Buffer.contents buf

(* Spawn argv.(0) (looked up on PATH), wait for it, return (exit_code,
   combined stdout+stderr) -- unlike exec_sibling/exec_corpus_pipeline
   above (which replace this process), compaction needs to keep running
   AFTER the subprocess exits (build the epoch marker, fsync, swap). *)
let run_and_wait (argv : string array) : int * string =
  let (r, w) = Unix.pipe () in
  Unix.set_close_on_exec r;
  let pid =
    try Unix.create_process argv.(0) argv Unix.stdin w w
    with Unix.Unix_error (e, _, _) ->
      Unix.close r; Unix.close w;
      failwith (Printf.sprintf "could not spawn %s: %s" argv.(0) (Unix.error_message e))
  in
  Unix.close w;
  let out = read_whole_fd r in
  Unix.close r;
  let (_, status) = Unix.waitpid [] pid in
  let code = match status with
    | Unix.WEXITED c -> c
    | Unix.WSIGNALED s -> 128 + s
    | Unix.WSTOPPED s -> 128 + s
  in
  (code, out)

(* fsync a single regular file. Reuses the F*-extracted, already-tested
   `delta_log_fsync` (issue #282) -- its OCaml realisation is a generic
   "open O_WRONLY, fsync, close," with no dependence on the path being
   a delta log specifically (rule #11(a): pure I/O, no branching on
   content). *)
let fsync_file path = DLog.delta_log_fsync path

(* Fast path for writing a POTENTIALLY LARGE `RDF.Bytes.bytes` (F*
   `list char`) payload to disk. `DLog.delta_log_append` (issue #282)
   is right for what it was built for -- single delta-log entries/
   batches/an 8-byte epoch marker, all a few dozen to a few hundred
   bytes -- because its OCaml realisation converts via
   `RDF_Bytes.bytes_to_string`, i.e. F*'s stdlib `String.string_of_list`,
   which extracts (ulib/ml/app/FStar_String.ml) to
   `BatUTF8.init (List.length l) (fun i -> BatUChar.chr (List.at l i))`
   -- an O(n) `List.at` INSIDE an O(n) `init` loop, i.e. quadratic in
   the byte count. Confirmed by measurement, not just reading the
   source: a 903,559-byte `data.cottas` (the 6,780-quad medication
   fixture) via `delta_log_append` did not finish in over 3 minutes of
   100% CPU before being killed; the same bytes converted the way
   `write_dict_file`/`write_presence_file`
   (experimental_ocaml_glue/cottas_ondisk_zzzzz_ondisk_index.sh) already
   do it -- walk the list ONCE with `List.iter` into a `Buffer` -- is
   linear and takes a fraction of a second. Reusing `delta_log_append`
   for a whole COTTAS base file was the wrong call; this is the
   dedicated O(n) path a base-file-sized payload needs. Still rule-#11(a)
   pure I/O: no branching on byte CONTENT, just format conversion +
   write. *)
let write_bytes_file (path : string) (bytes : RDF_Bytes.bytes) : unit =
  let buf = Buffer.create (List.length bytes) in
  List.iter (fun b -> Buffer.add_char buf (Char.chr (b land 0xff))) bytes;
  let oc = open_out_bin path in
  Buffer.output_buffer oc buf;
  flush oc;
  (try Unix.fsync (Unix.descr_of_out_channel oc) with _ -> ());
  close_out oc

let list_regular_files dir =
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun name -> not (Sys.is_directory (Filename.concat dir name)))

let version_dir_re = Str.regexp "^v\\([0-9]+\\)$"

let next_version_number chunk_dir =
  let entries = try Array.to_list (Sys.readdir chunk_dir) with Sys_error _ -> [] in
  let nums =
    List.filter_map
      (fun name ->
         if Str.string_match version_dir_re name 0
            && Sys.is_directory (Filename.concat chunk_dir name)
         then Some (int_of_string (Str.matched_group 1 name))
         else None)
      entries
  in
  1 + List.fold_left max 0 nums

let rm_rf path =
  ignore (Sys.command (Printf.sprintf "rm -rf %s" (Filename.quote path)))

(* ----------------------------------------------------------------------
   Shared native-writer core (2026-07-06), used by BOTH `factoidal
   import` and `factoidal compact --native-writer`: parse N-Quads text
   with the F*-extracted parser, sort (s,p,o,g) consumer-side, call the
   pure F* serializer RDF.CottasStore.BaseWriter.serialize_cottas_v2, write
   DIR/data.cottas, and (optionally) eagerly build the 10 companion
   sidecars by re-invoking this same binary's `query --explain` path
   (the exact trick corpus_pipeline.py's build_cottas_sidecars_eager
   uses -- prewarm_via_companions writes dict/presence/offsets/
   compound-po to disk as a side effect of opening the store).
   Returns the quad count. Rule #11: parse and byte layout are F*;
   this function is argv-free orchestration + plain I/O.
   ---------------------------------------------------------------------- *)

let subject_to_cottas_string (s : RDF_Graph_Executable.subject) : string =
  match s with
  | S_IRI i -> Printf.sprintf "<%s>" i
  | S_BNode b -> Printf.sprintf "_:%s" b

let cottas_quad_of_triple_graph
    (t : RDF_Graph_Executable.triple) (g : string option)
    : RDF_CottasStore_BaseWriter.cottas_quad =
  { RDF_CottasStore_BaseWriter.cq_s = subject_to_cottas_string t.s;
    RDF_CottasStore_BaseWriter.cq_p = Printf.sprintf "<%s>" t.p;
    RDF_CottasStore_BaseWriter.cq_o = term_to_ntriples t.o;
    RDF_CottasStore_BaseWriter.cq_g =
      (match g with Some iri -> Printf.sprintf "<%s>" iri | None -> "DEFAULT") }

let cottas_quad_key (q : RDF_CottasStore_BaseWriter.cottas_quad) =
  (q.RDF_CottasStore_BaseWriter.cq_s, q.RDF_CottasStore_BaseWriter.cq_p,
   q.RDF_CottasStore_BaseWriter.cq_o, q.RDF_CottasStore_BaseWriter.cq_g)

let native_write_base_and_sidecars
    ~(nq_content : string) ~(out_dir : string)
    ~(build_sidecars : bool) ~(verb : string) : int =
  (try Unix.mkdir out_dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  let t0 = Unix.gettimeofday () in
  let quads_rev =
    Parser_NQuads.fold_nquads
      (fun t g acc -> cottas_quad_of_triple_graph t g :: acc)
      (fun _ -> false)
      []
      nq_content
  in
  let quads = List.rev quads_rev in
  let quad_count = List.length quads in
  Printf.printf "%s: parsed %d quads (%.2fs)\n%!" verb quad_count (Unix.gettimeofday () -. t0);

  (* Consumer-side sort (rule #11's consumer carve-out). Array-based:
     stdlib List.sort/List.map are non-tail-recursive in OCaml 4.x and
     blew the native stack at 888,949 quads (gene corpus, measured
     2026-07-06). *)
  let t1 = Unix.gettimeofday () in
  let arr = Array.of_list quads in
  Array.sort (fun a b -> compare (cottas_quad_key a) (cottas_quad_key b)) arr;
  let sorted = Array.to_list arr in
  Printf.printf "%s: sorted (%.2fs)\n%!" verb (Unix.gettimeofday () -. t1);

  (* Native F* writer: pure Tot function, no I/O, no assume val.
     v2 (2026-07-06): RLE_DICTIONARY for p/g always, s/o via
     encode_column_choose_smaller (build both DLBA and RLE_DICTIONARY,
     keep whichever is fewer bytes). serialize_cottas (v1, DLBA-only)
     stays defined for its own pinned round-trip test but is no longer
     the writer this CLI path calls -- see RDF.CottasStore.BaseWriter.fst's
     "Writer v2" banner for the encoding-choice policy. *)
  let t2 = Unix.gettimeofday () in
  let bytes = RDF_CottasStore_BaseWriter.serialize_cottas_v2 sorted in
  let byte_count = List.length bytes in
  Printf.printf "%s: serialized %d bytes (%.2fs, %.2f bytes/quad)\n%!"
    verb byte_count (Unix.gettimeofday () -. t2)
    (if quad_count = 0 then 0.0 else float_of_int byte_count /. float_of_int quad_count);

  let cottas_path = Filename.concat out_dir "data.cottas" in
  let tmp_cottas = Printf.sprintf "%s.tmp.%d" cottas_path (Unix.getpid ()) in
  (try Sys.remove tmp_cottas with Sys_error _ -> ());
  write_bytes_file tmp_cottas bytes;
  DLog.atomic_rename tmp_cottas cottas_path;
  DLog.fsync_dir out_dir;
  Printf.printf "%s: wrote %s\n%!" verb cottas_path;

  if build_sidecars then begin
    Printf.printf "%s: building eager sidecars via self-query --explain ...\n%!" verb;
    let self_bin = Sys.executable_name in
    let argv =
      [| self_bin; "query"; "--data-cottas"; cottas_path;
         "--explain"; "SELECT * WHERE { ?s ?p ?o } LIMIT 1" |]
    in
    let (code, output) = run_and_wait argv in
    if code <> 0 then begin
      Printf.eprintf "%s: sidecar pre-warm failed (rc=%d):\n%s\n" verb code output;
      exit 1
    end
  end;
  quad_count

let usage_compact () =
  Printf.eprintf
    "Usage: factoidal compact --data-cottas FILE --delta-log PATH\n\
    \                          [--python PATH] [--parser NAME] [--index PERM]\n\n\
     Durable-UPDATE stage 4: fold the delta log into a fresh .cottas base\n\
     via the existing corpus_pipeline.py import pipeline, then atomically\n\
     swap it in (chunk_dir/current -> vN symlink flip) and truncate the\n\
     delta log. See docs/designissues/2026-07-06-durable-update-design.md\n\
     section 3.3 step 5 and this file's own compaction banner (above\n\
     `run_compact`) for the swap protocol and its crash-safety argument.\n";
  exit 2

let run_compact (args : string list) : unit =
  let data_cottas = ref None in
  let delta_log = ref None in
  let python = ref (match Sys.getenv_opt "PYCOTTAS_PYTHON" with Some p -> p | None -> "python3") in
  let parser_name = ref "factoidal" in
  let index_perm = ref "spog" in
  (* Native-writer path (2026-07-06): rebuild the compacted base with
     RDF.CottasStore.BaseWriter.serialize_cottas_v2 + the eager-sidecar
     self-invocation instead of shelling out to corpus_pipeline.py /
     pycottas / DuckDB -- the LAST Python dependency in the write path.
     Opt in per-invocation with --native-writer, or globally with
     FACTOIDAL_COMPACT_NATIVE=1 (lets existing scripts switch without
     changing their own argv). --python-writer forces the legacy path
     even when the env var is set. *)
  let native_writer =
    ref (match Sys.getenv_opt "FACTOIDAL_COMPACT_NATIVE" with
         | Some ("1" | "true" | "yes") -> true
         | _ -> false) in
  let rec loop = function
    | [] -> ()
    | "--data-cottas" :: v :: rest -> data_cottas := Some v; loop rest
    | "--delta-log" :: v :: rest -> delta_log := Some v; loop rest
    | "--python" :: v :: rest -> python := v; loop rest
    | "--parser" :: v :: rest -> parser_name := v; loop rest
    | "--index" :: v :: rest -> index_perm := v; loop rest
    | "--native-writer" :: rest -> native_writer := true; loop rest
    | "--python-writer" :: rest -> native_writer := false; loop rest
    | ("--help" | "-h") :: _ -> usage_compact ()
    | _ -> usage_compact ()
  in
  loop args;
  let data_cottas_path = match !data_cottas with Some p -> p | None -> usage_compact () in
  let delta_log_path = match !delta_log with Some p -> p | None -> usage_compact () in
  if not (Sys.file_exists data_cottas_path) then begin
    Printf.eprintf "Error: --data-cottas file not found: %s\n" data_cottas_path; exit 1
  end;
  let old_version_dir = Filename.dirname data_cottas_path in
  let chunk_dir = Filename.dirname old_version_dir in
  let chunk_name = Filename.basename chunk_dir in
  let corpus_root = Filename.dirname chunk_dir in

  Printf.printf "compact: chunk_dir=%s corpus_root=%s chunk_name=%s\n%!"
    chunk_dir corpus_root chunk_name;

  (* 1. Read the CURRENT base + delta log through the SAME F*-verified
     read path a query would use, and materialize base (+) delta into a
     plain in-memory rdf_dataset via SPARQL11_Store.materialize_dataset_
     backend (Tot) -- no new store-reading logic (rule #15/#7). *)
  let old_epoch = read_compacted_epoch old_version_dir in
  let old_epoch_fs = read_compacted_epoch_opt old_version_dir in
  let cods = open_cottas_ondisk_store data_cottas_path in
  let dsb = SPARQL11_Store.cottas_with_delta_dataset_backend cods delta_log_path old_epoch_fs in
  let merged_ds = SPARQL11_Store.materialize_dataset_backend dsb in
  let nq_text = RDF_Canonical.canonical_nquads merged_ds in

  (* 2. Compute the new "compacted through epoch": the max db_epoch
     among the batches actually folded (the SAME epoch filter
     cottas_with_delta_dataset_backend just used above), or the old
     epoch unchanged if the log contributed nothing new. *)
  let log_bytes = DLog.delta_log_read_all delta_log_path in
  let raw_batches = match DLog.parse_log log_bytes with
    | FStar_Pervasives_Native.Some (bs, _) -> bs
    | FStar_Pervasives_Native.None -> [] in
  let kept_batches = DLog.filter_batches_since_epoch old_epoch_fs raw_batches in
  let new_epoch =
    List.fold_left
      (fun acc (b : DLog.delta_batch) -> Z.max acc b.DLog.db_epoch)
      (match old_epoch with Some n -> n | None -> Z.zero)
      kept_batches
  in
  Printf.printf "compact: folded %d batch(es), compacted_through_epoch=%s\n%!"
    (List.length kept_batches) (Z.to_string new_epoch);

  (* 3. Build the new version directory DIRECTLY via corpus_pipeline.py
     (rule #15: reuse the existing import pipeline, no new store
     writer) -- --corpus-root/--dataset-name/--chunk-name/--version
     target it so the output lands EXACTLY at chunk_dir/vN, not a
     nested scratch copy that then needs moving. vN is a FRESH name,
     never before referenced by `current`, so building into it cannot
     disturb anything live. *)
  let next_num = next_version_number chunk_dir in
  let new_version_name = Printf.sprintf "v%d" next_num in
  let new_version_dir = Filename.concat chunk_dir new_version_name in
  if Sys.file_exists new_version_dir then rm_rf new_version_dir;

  if !native_writer then begin
    (* Native path: same materialized N-Quads text, written by the F*
       serializer + eager sidecars, no subprocess beyond the sidecar
       self-invocation. See `native_write_base_and_sidecars`'s banner. *)
    Printf.printf "compact: native writer (RDF.CottasStore.BaseWriter) -> %s\n%!"
      new_version_dir;
    let (_ : int) =
      native_write_base_and_sidecars ~nq_content:nq_text
        ~out_dir:new_version_dir ~build_sidecars:true ~verb:"compact"
    in ()
  end else begin
    let tmp_nq = Filename.temp_file "factoidal-compact-" ".nq" in
    let oc = open_out tmp_nq in
    output_string oc nq_text;
    close_out oc;

    let repo_root = match find_repo_root () with
      | Some r -> r
      | None ->
        failwith "factoidal compact: could not locate tools/corpus_pipeline.py \
                  (set FACTOIDAL_REPO_ROOT)"
    in
    let corpus_script = Filename.concat repo_root "tools/corpus_pipeline.py" in
    let argv =
      [| !python; corpus_script; "materialize-nq-cottas-corpus";
         "--input"; tmp_nq; "--input-format"; "nq";
         "--corpus-root"; corpus_root;
         "--dataset-name"; chunk_name;
         "--chunk-name"; chunk_name;
         "--version"; new_version_name;
         "--parser"; !parser_name;
         "--index"; !index_perm;
         "--build-sidecars" |]
    in
    Printf.printf "compact: %s\n%!" (String.concat " " (Array.to_list argv));
    let (code, output) = run_and_wait argv in
    (try Sys.remove tmp_nq with Sys_error _ -> ());
    if code <> 0 then begin
      Printf.eprintf "factoidal compact: corpus_pipeline.py failed (rc=%d):\n%s\n" code output;
      rm_rf new_version_dir;
      exit 1
    end;
    print_string output
  end;

  (* 4. Write the compacted-epoch companion file INSIDE the new (not
     yet live) version directory -- it becomes visible atomically
     together with the rest of the base when `current` flips, in
     step 6. *)
  let epoch_marker_path = Filename.concat new_version_dir "data.compacted-epoch" in
  DLog.delta_log_append epoch_marker_path (DLog.serialize_compacted_epoch new_epoch);
  DLog.delta_log_fsync epoch_marker_path;

  (* 5. fsync every regular file in the new version directory, then the
     directory itself -- durability of the whole base must be
     established BEFORE it becomes reachable via `current`. *)
  List.iter
    (fun name -> fsync_file (Filename.concat new_version_dir name))
    (list_regular_files new_version_dir);
  DLog.fsync_dir new_version_dir;

  (* 6. The atomic swap: symlink indirection (see this function's own
     banner above for why a plain directory rename cannot do this
     atomically). Create a temp symlink, then atomic_rename it onto
     `current` -- ONE syscall, no window where `current` is absent. *)
  let current_path = Filename.concat chunk_dir "current" in
  let tmp_symlink = Filename.concat chunk_dir
      (Printf.sprintf ".current.tmp.%d" (Unix.getpid ())) in
  (try Sys.remove tmp_symlink with Sys_error _ -> ());
  Unix.symlink new_version_name tmp_symlink;
  DLog.atomic_rename tmp_symlink current_path;
  DLog.fsync_dir chunk_dir;
  Printf.printf "compact: current -> %s\n%!" new_version_name;

  (* 7. Truncate the delta log: fresh empty log to a temp path, fsync,
     atomic_rename over the live log, fsync the containing directory --
     the SAME temp+fsync+rename+fsync_dir shape as the base swap,
     reusing the SAME five stage-2 assume vals (issue #282), zero new
     ones. Space reclamation, not a correctness dependency (see the
     crash-safety argument in this function's banner). *)
  let log_dir = Filename.dirname delta_log_path in
  let tmp_log = Printf.sprintf "%s.tmp.%d" delta_log_path (Unix.getpid ()) in
  (try Sys.remove tmp_log with Sys_error _ -> ());
  DLog.delta_log_append tmp_log (DLog.serialize_log []);
  DLog.delta_log_fsync tmp_log;
  DLog.atomic_rename tmp_log delta_log_path;
  DLog.fsync_dir log_dir;

  Printf.printf "compact: OK new_base=%s current=%s compacted_through_epoch=%s\n%!"
    (Filename.concat new_version_dir "data.cottas")
    (Filename.concat current_path "data.cottas")
    (Z.to_string new_epoch)

(* ============================================================================
   Native COTTAS import ("factoidal import") -- 2026-07-06, closing the
   owner's "why is Python still needed to write it" gap.

   Every prior store-creation path (cottas-import, compact) shells out to
   corpus_pipeline.py -> pycottas.rdf2cottas -> DuckDB to write data.cottas.
   This command instead calls the native F* writer
   (RDF.CottasStore.BaseWriter.serialize_cottas_v2, a pure `Tot` function --
   the byte layout, RLE_DICTIONARY/DELTA_LENGTH_BYTE_ARRAY encoding, and thrift-compact
   footer assembly are ALL in F*, per rule #11) so store CREATION has
   zero Python in its critical path.

   What stays in OCaml here, and why each piece is rule-#11 acceptable:
     - Parsing: Parser_NQuads.fold_nquads (an EXTRACTED F* parser --
       Iron Rule #4). No hand-written tokenizer.
     - Term -> COTTAS-column-string rendering (subject_to_cottas_string /
       RDF_Pretty.term_to_ntriples): reuses the SAME N-Triples token
       rendering `print_results_ntriples` already uses elsewhere in this
       file, not a new serializer. The default graph gets the literal
       sentinel "DEFAULT", matching cottas_ondisk_runtime.sh's
       collect_distinct_graph convention (never NULL, never "").
     - Sort order: (s,p,o,g) lexicographic via OCaml's polymorphic
       `compare` on tuples of strings. This is exactly the "Consumer
       tools ... are not part of the verified library" carve-out in rule
       #11 -- reordering already-parsed strings is not RDF/SPARQL
       semantic logic. Matches corpus_pipeline.py's `index=spog` default
       row order (pycottas.rdf2cottas's `ORDER BY s,p,o,g`).
       Characteristic-set clustering (`--row-order cs`) is NOT
       implemented here -- follow-up, not a correctness requirement.
     - File I/O: DLog.delta_log_append / delta_log_fsync / atomic_rename
       / fsync_dir -- the SAME five issue-#282 primitives `compact`
       already uses above. `delta_log_append` is a generic "write bytes
       to a path" primitive despite its name (see `fsync_file`'s comment
       a few hundred lines up); no new `assume val`.

   Eager sidecars (dict/presence/offsets/compound-po): built by
   re-invoking this SAME binary's `query --explain` path as a
   subprocess, exactly the trick corpus_pipeline.py's
   `build_cottas_sidecars_eager` already uses (prewarm_via_companions
   runs as a side effect of opening the store for --explain). Zero new
   sidecar-writing logic; reuses the existing eager-build path
   verbatim.

   Epoch marker + empty delta log: writing `data.compacted-epoch = 0`
   and an initialized (header-only) `data.deltalog` makes a freshly
   imported store immediately eligible for `--delta-log`-flagged
   queries/updates without a separate init step -- `read_compacted_epoch_
   opt` treats an absent marker as "never compacted" already, so this is
   not required for correctness, but matches what a compacted store
   carries and lets `factoidal serve --rw --delta-log <dir>/data.deltalog`
   work against a brand-new import with no extra step. *)

(* subject_to_cottas_string / cottas_quad_of_triple_graph /
   cottas_quad_key / the parse-sort-serialize-write-sidecars core all
   live above `run_compact` as `native_write_base_and_sidecars`,
   shared with `factoidal compact --native-writer`. *)

let usage_import () =
  Printf.eprintf
    "Usage: factoidal import --nq FILE.nq --out DIR [--build-sidecars] [--no-epoch-marker]\n\n\
     Native (zero-Python) COTTAS store creation: parses FILE.nq with the\n\
     F*-extracted N-Quads parser, sorts (s,p,o,g), writes DIR/data.cottas\n\
     via RDF.CottasStore.BaseWriter.serialize_cottas_v2, then (by default)\n\
     eagerly builds the 10 companion sidecars and initializes\n\
     data.compacted-epoch + data.deltalog so the store is immediately\n\
     queryable and --delta-log-ready.\n";
  exit 2

let run_import (args : string list) : unit =
  let nq_path = ref None in
  let out_dir = ref None in
  let build_sidecars = ref true in
  let write_epoch_marker = ref true in
  let rec loop = function
    | [] -> ()
    | "--nq" :: v :: rest -> nq_path := Some v; loop rest
    | "--out" :: v :: rest -> out_dir := Some v; loop rest
    | "--build-sidecars" :: rest -> build_sidecars := true; loop rest
    | "--no-sidecars" :: rest -> build_sidecars := false; loop rest
    | "--no-epoch-marker" :: rest -> write_epoch_marker := false; loop rest
    | ("-h" | "--help") :: _ -> usage_import ()
    | unknown :: _ ->
      Printf.eprintf "factoidal import: unrecognised argument '%s'\n" unknown;
      usage_import ()
  in
  loop args;
  let nq_path = match !nq_path with Some p -> p | None -> usage_import () in
  let out_dir = match !out_dir with Some d -> d | None -> usage_import () in
  if not (Sys.file_exists nq_path) then begin
    Printf.eprintf "factoidal import: --nq file not found: %s\n" nq_path;
    exit 1
  end;
  (try Unix.mkdir out_dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());

  Printf.printf "import: parsing %s ...\n%!" nq_path;
  let content = read_file nq_path in
  (* Shared core (also used by `compact --native-writer`): parse via the
     F*-extracted N-Quads parser, sort (s,p,o,g), serialize via the pure
     F* writer, write data.cottas, eager sidecars. *)
  let quad_count =
    native_write_base_and_sidecars ~nq_content:content ~out_dir
      ~build_sidecars:!build_sidecars ~verb:"import"
  in

  if !write_epoch_marker then begin
    let epoch_marker_path = Filename.concat out_dir "data.compacted-epoch" in
    let tmp_epoch = Printf.sprintf "%s.tmp.%d" epoch_marker_path (Unix.getpid ()) in
    (try Sys.remove tmp_epoch with Sys_error _ -> ());
    DLog.delta_log_append tmp_epoch (DLog.serialize_compacted_epoch Z.zero);
    DLog.delta_log_fsync tmp_epoch;
    DLog.atomic_rename tmp_epoch epoch_marker_path;

    let delta_log_path = Filename.concat out_dir "data.deltalog" in
    let tmp_log = Printf.sprintf "%s.tmp.%d" delta_log_path (Unix.getpid ()) in
    (try Sys.remove tmp_log with Sys_error _ -> ());
    DLog.delta_log_append tmp_log (DLog.serialize_log []);
    DLog.delta_log_fsync tmp_log;
    DLog.atomic_rename tmp_log delta_log_path;
    DLog.fsync_dir out_dir;
    Printf.printf "import: initialized %s and %s\n%!" epoch_marker_path delta_log_path
  end;

  Printf.printf "import: OK quads=%d out=%s\n%!" quad_count out_dir

(* ============================================================================
   npm FP API parity: shacl / shex / rml / csvw / jsonld / rif / entail /
   update -- thin CLI wrappers over the SAME F*-extracted functions the
   npm-entry ABI (bin/npm-entry/entry_jsoo.ml) already calls, one call
   each (parse_shape_from_graph+validate, decode_shex_schema+
   validate_focus, decode_mapping_document+eval_triples_map_*,
   csvw_decode_metadata_text+csvw_convert_document_*, parse_rif_program+
   RIF_Core_Eval.fixpoint, rdfs/owl_rl_closure_with_reflexivity,
   parse_sparql_update+apply_update) -- so the native CLI reaches the
   same npm/factoidal surface (owner directive: "ensure full npm fp api
   surface is usable via cli tools," 2026-07-06). Every module below
   ($COMMON_MODULES in build-ocaml.sh) is already linked into this
   binary via bin/shacl-runner, bin/shex-runner, bin/rml-runner,
   bin/csvw-runner, bin/rif-runner's own builds, so no new link-line
   entry is needed. Rule #11: this section is argv parsing, file I/O,
   and output formatting only -- zero RDF/RML/ShEx/CSVW/RIF semantics
   live here. *)

(* ---- shacl (SHACL Core validation; `validate` is the original verb
   name, kept unchanged below for backward compatibility -- `shacl` is
   the npm-name-parity alias, extended with --data/--json). ---- *)

let usage_shacl () =
  Printf.eprintf
    "Usage: factoidal shacl --data DATA.ttl --shapes SHAPES.ttl [--json]\n\
    \       factoidal validate --shapes SHAPES.ttl DATA.ttl   (legacy form)\n";
  exit 2

let run_shacl_validate (args : string list) : unit =
  let shapes_path = ref None in
  let data_path = ref None in
  let json_out = ref false in
  let rec loop = function
    | [] -> ()
    | "--shapes" :: p :: rest -> shapes_path := Some p; loop rest
    | "--data" :: p :: rest -> data_path := Some p; loop rest
    | "--json" :: rest -> json_out := true; loop rest
    | ("--help" | "-h") :: _ -> usage_shacl ()
    | p :: rest when !data_path = None && String.length p > 0 && p.[0] <> '-' ->
      data_path := Some p; loop rest
    | _ -> usage_shacl ()
  in
  loop args;
  match !shapes_path, !data_path with
  | Some sp, Some dp ->
    let shapes_triples =
      try load_triples sp
      with e ->
        Printf.eprintf "Error parsing shapes graph %s: %s\n" sp (Printexc.to_string e);
        exit 1
    in
    let data_triples =
      try load_triples dp
      with e ->
        Printf.eprintf "Error parsing data graph %s: %s\n" dp (Printexc.to_string e);
        exit 1
    in
    let sg = SHACL_Validation.parse_shape_from_graph shapes_triples in
    let report = SHACL_Validation.validate data_triples shapes_triples sg in
    let conforms = report.SHACL_Validation.conforms in
    if !json_out then begin
      let report_graph = SHACL_Validation.validation_report_to_graph report in
      let report_ds = RDF_Graph_Executable.({ ds_default = report_graph; ds_named = [] }) in
      let report_nq = RDF_Canonical.canonical_nquads report_ds in
      Printf.printf "{\"conforms\":%s,\"report\":\"%s\"}\n"
        (if conforms then "true" else "false") (json_escape report_nq)
    end else begin
      let results = report.SHACL_Validation.results in
      let string_of_term t = RDF_Pretty.term_to_turtle t in
      let string_of_path_opt = function
        | FStar_Pervasives_Native.None -> "(none)"
        | FStar_Pervasives_Native.Some (SHACL_Validation.P_Predicate p) -> p
        | FStar_Pervasives_Native.Some (SHACL_Validation.P_Inverse (SHACL_Validation.P_Predicate p)) ->
          "^" ^ p
        | FStar_Pervasives_Native.Some _ -> "(complex path)"
      in
      let string_of_severity = function
        | SHACL_Validation.Sev_Info -> "Info"
        | SHACL_Validation.Sev_Warning -> "Warning"
        | SHACL_Validation.Sev_Violation -> "Violation"
        | SHACL_Validation.Sev_Custom iri -> iri
      in
      Printf.printf "sh:conforms %b\n" conforms;
      List.iter
        (fun v ->
           Printf.printf "  [%s] focus=%s path=%s%s source=%s\n"
             (string_of_severity v.SHACL_Validation.v_severity)
             (string_of_term v.SHACL_Validation.v_focus_node)
             (string_of_path_opt v.SHACL_Validation.v_path)
             (match v.SHACL_Validation.v_value with
              | FStar_Pervasives_Native.Some value -> " value=" ^ string_of_term value
              | FStar_Pervasives_Native.None -> "")
             v.SHACL_Validation.v_source_shape)
        results
    end;
    exit (if conforms then 0 else 1)
  | _ -> usage_shacl ()

(* ---- shex (ShEx / Shape Expressions validation of one focus node) ---- *)

let usage_shex () =
  Printf.eprintf
    "Usage: factoidal shex --data DATA.ttl --schema SCHEMA.json --node NODE [--shape SHAPE]\n\
    \       NODE/SHAPE are an IRI, or \"_:label\" for a blank node.\n\
     Prints \"true\" / \"false\" / \"null\" (deferred -- outside this\n\
     engine's decidable ShEx fragment, never a guessed answer) and exits\n\
     0 / 1 / 2 respectively.\n";
  exit 2

(* Same IRI / "_:label" convention bin/shex-runner and entry_jsoo.ml's
   term_of_focus_string use, so a caller round-tripping a shex_runner-
   style ShapeMap entry gets the identical term. *)
let shex_term_of_focus_string (s : string) : RDF_Graph_Executable.rdf_term =
  if String.length s >= 2 && String.sub s 0 2 = "_:"
  then RDF_Graph_Executable.T_BNode (String.sub s 2 (String.length s - 2))
  else RDF_Graph_Executable.T_IRI s

let run_shex (args : string list) : unit =
  let data_path = ref None in
  let schema_path = ref None in
  let node = ref None in
  let shape = ref None in
  let rec loop = function
    | [] -> ()
    | "--data" :: p :: rest -> data_path := Some p; loop rest
    | "--schema" :: p :: rest -> schema_path := Some p; loop rest
    | "--node" :: n :: rest -> node := Some n; loop rest
    | "--shape" :: s :: rest -> shape := Some s; loop rest
    | ("--help" | "-h") :: _ -> usage_shex ()
    | _ -> usage_shex ()
  in
  loop args;
  match !data_path, !schema_path, !node with
  | Some dp, Some sp, Some n ->
    let data_graph =
      try load_triples dp
      with e -> Printf.eprintf "Error parsing %s: %s\n" dp (Printexc.to_string e); exit 1
    in
    let schema_json =
      try read_file sp
      with e -> Printf.eprintf "Error reading %s: %s\n" sp (Printexc.to_string e); exit 1
    in
    (match ShEx_Schema.decode_shex_schema schema_json "" with
     | FStar_Pervasives_Native.None ->
       Printf.eprintf "Error: could not decode ShExJ schema %s\n" sp; exit 1
     | FStar_Pervasives_Native.Some schema ->
       let focus_term = shex_term_of_focus_string n in
       let shape_id = match !shape with
         | None -> FStar_Pervasives_Native.None
         | Some s -> FStar_Pervasives_Native.Some s
       in
       (match ShEx_Validation.validate_focus schema shape_id focus_term data_graph with
        | FStar_Pervasives_Native.None -> Printf.printf "null\n"; exit 2
        | FStar_Pervasives_Native.Some true -> Printf.printf "true\n"; exit 0
        | FStar_Pervasives_Native.Some false -> Printf.printf "false\n"; exit 1))
  | _ -> usage_shex ()

(* ---- rml (RML mapping evaluation against one logical source) ---- *)

let usage_rml () =
  Printf.eprintf
    "Usage: factoidal rml --mapping MAPPING.ttl --source SOURCE [--kind json|csv]\n\
    \       --kind defaults from SOURCE's extension (.json -> json, .csv -> csv).\n\
     Every triples map in MAPPING reads the SAME source (no cross-source\n\
     joins through this entry point -- see bin/rml-runner/rml_runner.ml\n\
     for the full multi-source join driver). Prints the generated\n\
     triples as N-Quads.\n";
  exit 2

let run_rml (args : string list) : unit =
  let mapping_path = ref None in
  let source_path = ref None in
  let kind = ref None in
  let rec loop = function
    | [] -> ()
    | "--mapping" :: p :: rest -> mapping_path := Some p; loop rest
    | "--source" :: p :: rest -> source_path := Some p; loop rest
    | "--kind" :: k :: rest -> kind := Some (String.lowercase_ascii k); loop rest
    | ("--help" | "-h") :: _ -> usage_rml ()
    | _ -> usage_rml ()
  in
  loop args;
  match !mapping_path, !source_path with
  | Some mp, Some srcp ->
    let mapping_graph =
      try load_triples mp
      with e -> Printf.eprintf "Error parsing %s: %s\n" mp (Printexc.to_string e); exit 1
    in
    let source_data =
      try read_file srcp
      with e -> Printf.eprintf "Error reading %s: %s\n" srcp (Printexc.to_string e); exit 1
    in
    let source_kind = match !kind with
      | Some k -> k
      | None ->
        (match String.lowercase_ascii (Filename.extension srcp) with
         | ".json" -> "json"
         | ".csv" -> "csv"
         | _ ->
           Printf.eprintf "Error: --kind json|csv required (could not infer from %s)\n" srcp;
           exit 1)
    in
    if source_kind <> "json" && source_kind <> "csv" then begin
      Printf.eprintf "Error: --kind must be 'json' or 'csv' (got '%s')\n" source_kind; exit 1
    end;
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
    print_string (RDF_Canonical.canonical_nquads ds)
  | _ -> usage_rml ()

(* ---- csvw (CSVW csv2rdf conversion) ---- *)

let usage_csvw () =
  Printf.eprintf
    "Usage: factoidal csvw --csv DATA.csv [--metadata METADATA.json] [--minimal]\n\
    \                      [--base IRI] [--url URL]\n\
     mode defaults to \"standard\" (full csvw:TableGroup/Table/Row wrapper);\n\
     --minimal selects the flat mode. Metadata omitted infers the schema\n\
     from the CSV's own header row. Prints the generated triples as N-Quads.\n";
  exit 2

let run_csvw (args : string list) : unit =
  let csv_path = ref None in
  let metadata_path = ref None in
  let minimal = ref false in
  let base_iri = ref "file:///" in
  let url = ref None in
  let rec loop = function
    | [] -> ()
    | "--csv" :: p :: rest -> csv_path := Some p; loop rest
    | "--metadata" :: p :: rest -> metadata_path := Some p; loop rest
    | "--minimal" :: rest -> minimal := true; loop rest
    | "--base" :: b :: rest -> base_iri := b; loop rest
    | "--url" :: u :: rest -> url := Some u; loop rest
    | ("--help" | "-h") :: _ -> usage_csvw ()
    | _ -> usage_csvw ()
  in
  loop args;
  match !csv_path with
  | Some cp ->
    let csv_text =
      try read_file cp
      with e -> Printf.eprintf "Error reading %s: %s\n" cp (Printexc.to_string e); exit 1
    in
    let metadata_json = match !metadata_path with
      | None -> ""
      | Some mp ->
        (try read_file mp
         with e -> Printf.eprintf "Error reading %s: %s\n" mp (Printexc.to_string e); exit 1)
    in
    let fallback_url = match !url with Some u -> u | None -> Filename.basename cp in
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
       Printf.eprintf "Error: %s is not a decodable CSVW metadata document\n"
         (match !metadata_path with Some m -> m | None -> "(none)");
       exit 1
     | FStar_Pervasives_Native.Some tables ->
       let rows = RML_Sources.csv_parse_rows csv_text in
       let tables_with_rows = List.map (fun t -> (t, fallback_url, rows)) tables in
       let triples =
         if !minimal
         then CSVW_Conversion.csvw_convert_document_minimal !base_iri tables_with_rows
         else CSVW_Conversion.csvw_convert_document_standard !base_iri tables_with_rows
       in
       let ds = RDF_Graph_Executable.({ ds_default = triples; ds_named = [] }) in
       print_string (RDF_Canonical.canonical_nquads (scope_dataset_bnodes ds)))
  | None -> usage_csvw ()

(* ---- jsonld (JSON-LD -> RDF, dedicated verb + --base) ----
   `factoidal dump-nq FILE.jsonld` (extension auto-detect) or
   `factoidal dump-nq --format jsonld FILE` already work via
   load_dataset's existing JSONLD branch; this is a friendlier,
   npm-name-parity verb over the exact same load_dataset call. *)

let usage_jsonld () =
  Printf.eprintf
    "Usage: factoidal jsonld --in DOC.jsonld [--base IRI]\n\
     Remote @context URLs are an honest failure -- no documentLoader is\n\
     registered for this CLI. Prints canonical N-Quads.\n";
  exit 2

let run_jsonld (args : string list) : unit =
  let in_path = ref None in
  let base = ref None in
  let rec loop = function
    | [] -> ()
    | "--in" :: p :: rest -> in_path := Some p; loop rest
    | "--base" :: b :: rest -> base := Some b; loop rest
    | ("--help" | "-h") :: _ -> usage_jsonld ()
    | p :: rest when !in_path = None && String.length p > 0 && p.[0] <> '-' ->
      in_path := Some p; loop rest
    | _ -> usage_jsonld ()
  in
  loop args;
  match !in_path with
  | Some path ->
    let ds =
      try load_dataset ~format:(Some JSONLD) ~base:!base path
      with e -> Printf.eprintf "Error parsing %s: %s\n" path (Printexc.to_string e); exit 1
    in
    print_string (RDF_Canonical.canonical_nquads ds)
  | None -> usage_jsonld ()

(* ---- rif (RIF Core forward-chaining saturation) ---- *)

(* Ported verbatim from bin/npm-entry/entry_jsoo.ml's rif_xml_preprocess
   (itself ported from bin/w3c-runner/w3c_runner.ml) -- real vendored
   RIF-XML fixtures carry a <!DOCTYPE ... [ <!ENTITY rif "..."> ... ]>
   prolog that Parser_RIFXML (an XML *content* parser, not a DTD
   processor) cannot see through; this consumer-side text
   preprocessing strips the DOCTYPE and inlines the &rif;/&xs;/&rdf;
   entities it declares. Not RIF semantics -- rule #11/#15 stays
   satisfied. *)
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

let usage_rif () =
  Printf.eprintf
    "Usage: factoidal rif --rules RULES.rif --data DATA.ttl\n\
    \       RULES.rif is a RIF Core XML rule document (real vendored\n\
    \       <!DOCTYPE>/entity-form accepted unmodified). Prints the\n\
     saturated graph (input + derived triples) as N-Quads.\n";
  exit 2

let run_rif (args : string list) : unit =
  let rules_path = ref None in
  let data_path = ref None in
  let rec loop = function
    | [] -> ()
    | "--rules" :: p :: rest -> rules_path := Some p; loop rest
    | "--data" :: p :: rest -> data_path := Some p; loop rest
    | ("--help" | "-h") :: _ -> usage_rif ()
    | _ -> usage_rif ()
  in
  loop args;
  match !rules_path, !data_path with
  | Some rp, Some dp ->
    let rules_xml =
      try rif_xml_preprocess (read_file rp)
      with e -> Printf.eprintf "Error reading %s: %s\n" rp (Printexc.to_string e); exit 1
    in
    let premise =
      try load_triples dp
      with e -> Printf.eprintf "Error parsing %s: %s\n" dp (Printexc.to_string e); exit 1
    in
    (match Parser_RIFXML.parse_rif_program rules_xml with
     | FStar_Pervasives_Native.None ->
       Printf.eprintf "Error: could not parse RIF-XML program %s\n" rp; exit 1
     | FStar_Pervasives_Native.Some program ->
       let saturated = RIF_Core_Eval.fixpoint premise program (Z.of_int 100) in
       let ds = RDF_Graph_Executable.({ ds_default = saturated; ds_named = [] }) in
       print_string (RDF_Canonical.canonical_nquads ds))
  | _ -> usage_rif ()

(* ---- entail (materialize an RDFS/OWL-RL closure as a standalone dump;
   the npm owlClosure()-equivalent. `query --entail REGIME` applies the
   SAME closure internally before evaluating a query, but has no way to
   dump the closure itself -- this is that missing standalone verb.) ---- *)

let usage_entail () =
  Printf.eprintf
    "Usage: factoidal entail --data FILE [--data FILE...] --regime RDFS|OWL-RL\n\
    \       Materializes the entailment closure (input + derived triples)\n\
    \       and prints it as N-Quads. Default graph + each named graph\n\
    \       are closed independently.\n";
  exit 2

let run_entail (args : string list) : unit =
  let data_paths = ref [] in
  let regime = ref None in
  let rec loop = function
    | [] -> ()
    | "--data" :: p :: rest -> data_paths := !data_paths @ [p]; loop rest
    | "--regime" :: r :: rest ->
      let norm = match normalise_entail_regime r with
        | Some "RDFS" -> "RDFS"
        | Some "OWL-RL" -> "OWL-RL"
        | _ ->
          Printf.eprintf "Error: --regime must be RDFS or OWL-RL (got '%s')\n" r; exit 1
      in
      regime := Some norm; loop rest
    | ("--help" | "-h") :: _ -> usage_entail ()
    | p :: rest when String.length p > 0 && p.[0] <> '-' ->
      data_paths := !data_paths @ [p]; loop rest
    | _ -> usage_entail ()
  in
  loop args;
  match !data_paths, !regime with
  | [], _ | _, None -> usage_entail ()
  | paths, Some norm ->
    let datasets = List.map (fun f ->
      try load_dataset f
      with e -> Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e); exit 1
    ) paths in
    let closure tr =
      if norm = "OWL-RL"
      then RDF_Graph_Executable.owl_rl_closure_with_reflexivity tr (Z.of_int 100)
      else RDF_Graph_Executable.rdfs_closure_with_reflexivity tr (Z.of_int 100)
    in
    let graph = closure (concat_map_preserve_order (fun ds -> ds.ds_default) datasets) in
    let named = concat_map_preserve_order (fun ds -> ds.ds_named) datasets in
    let named = List.map (fun ng ->
      RDF_Graph_Executable.({ ng_name = ng.ng_name; ng_graph = closure ng.ng_graph })
    ) named in
    let ds = RDF_Graph_Executable.({ ds_default = graph; ds_named = named }) in
    print_string (RDF_Canonical.canonical_nquads ds)

(* ---- update (in-memory SPARQL 1.1 Update apply + dump; the npm
   update()-equivalent. Durable, on-disk UPDATE against a COTTAS store
   is a SEPARATE path: `factoidal serve --rw --delta-log ...` /
   `factoidal compact`, docs/designissues/2026-07-06-durable-update-
   design.md -- this is the in-memory-only counterpart.) ---- *)

let usage_update () =
  Printf.eprintf
    "Usage: factoidal update --data FILE [--data FILE...] -e 'SPARQL update'\n\
    \       factoidal update --data FILE [--data FILE...] --update FILE.ru\n\
    \       In-memory apply (no persistence) -- prints the resulting\n\
    \       dataset as N-Quads.\n";
  exit 2

let run_update (args : string list) : unit =
  let data_paths = ref [] in
  let update_string = ref None in
  let update_file = ref None in
  let rec loop = function
    | [] -> ()
    | "--data" :: p :: rest -> data_paths := !data_paths @ [p]; loop rest
    | "-e" :: u :: rest -> update_string := Some u; loop rest
    | "--update" :: f :: rest -> update_file := Some f; loop rest
    | ("--help" | "-h") :: _ -> usage_update ()
    | p :: rest when !data_paths = [] && String.length p > 0 && p.[0] <> '-' ->
      data_paths := [p]; loop rest
    | _ -> usage_update ()
  in
  loop args;
  if !data_paths = [] then usage_update ();
  let update_text = match !update_string, !update_file with
    | Some u, _ -> u
    | None, Some f -> read_file f
    | None, None -> usage_update ()
  in
  let datasets = List.map (fun f ->
    try load_dataset f
    with e -> Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e); exit 1
  ) !data_paths in
  let ds_default = concat_map_preserve_order (fun ds -> ds.ds_default) datasets in
  let ds_named = concat_map_preserve_order (fun ds -> ds.ds_named) datasets in
  let ds = RDF_Graph_Executable.({ ds_default; ds_named }) in
  match SPARQL11_Parser.parse_sparql_update update_text with
  | SPARQL11_Parser.ParseErr msg ->
    Printf.eprintf "SPARQL update parse error: %s\n" msg; exit 1
  | SPARQL11_Parser.ParseOk (u, _) ->
    let ds' = SPARQL11_Algebra.apply_update ds u in
    print_string (RDF_Canonical.canonical_nquads ds')

let print_navigation_help () =
  Printf.printf "factoidal — formally verified RDF/SPARQL toolkit\n\n";
  Printf.printf "Usage: factoidal <subcommand> [options...]\n\n";
  Printf.printf "Subcommands (current target surface):\n\n";
  Printf.printf "  query          Run a SPARQL query against RDF data\n";
  Printf.printf "                   factoidal query --data X.ttl --query Q.rq\n";
  Printf.printf "                   factoidal query --data X.ttl -e 'SELECT ...'\n";
  Printf.printf "                   (also: factoidal --data X --query Q.rq, legacy form)\n";
  Printf.printf "  serve          Start the SPARQL 1.1 Protocol HTTP server\n";
  Printf.printf "                   factoidal serve --port 3030 --dataset X.ttl\n";
  Printf.printf "                   (shares Factoidal_http parser/server in-process)\n";
  Printf.printf "  dump FILE      Parse RDF and dump as N-Triples\n";
  Printf.printf "  dump-nq FILE   Parse RDF and dump as sorted N-Quads\n";
  Printf.printf "  dump-turtle FILE  Parse RDF and dump as pretty-printed Turtle\n";
  Printf.printf "                   (prefix-compacted, subject-grouped, auto @prefix table)\n";
  Printf.printf "  canonicalize FILE  RDFC-1.0 canonical N-Quads (canonical bnode labels)\n";
  Printf.printf "  count FILE     Parse RDF and count triples\n";
  Printf.printf "  graphs list|get|hash|diff  Named-graph enumeration + RDFC-1.0 per-graph hash\n";
  Printf.printf "                   factoidal graphs list FILE            list named-graph IRIs\n";
  Printf.printf "                   factoidal graphs get FILE IRI         dump one graph (N-Triples)\n";
  Printf.printf "                   factoidal graphs hash FILE IRI        RDFC-1.0 canonical hash\n";
  Printf.printf "                   factoidal graphs diff FILE1 FILE2     added/removed/changed graphs\n";
  Printf.printf "  validate       SHACL Core validation (slice 1, issue #181)\n";
  Printf.printf "                   factoidal validate --shapes shapes.ttl data.ttl\n";
  Printf.printf "                   (see formal/fstar/SHACL.Validation.fst for constraint coverage)\n";
  Printf.printf "  shacl          SHACL Core validation (npm shaclValidate()-equivalent)\n";
  Printf.printf "                   factoidal shacl --data data.ttl --shapes shapes.ttl [--json]\n";
  Printf.printf "                   (alias of `validate`, plus --data/--json)\n";
  Printf.printf "  shex           ShEx (Shape Expressions) validation of one focus node\n";
  Printf.printf "                   factoidal shex --data data.ttl --schema schema.json --node N [--shape S]\n";
  Printf.printf "  rml            RML mapping evaluation against one JSON/CSV logical source\n";
  Printf.printf "                   factoidal rml --mapping map.ttl --source data.json --kind json\n";
  Printf.printf "  csvw           CSVW csv2rdf conversion\n";
  Printf.printf "                   factoidal csvw --csv data.csv [--metadata meta.json] [--minimal]\n";
  Printf.printf "  jsonld         JSON-LD -> RDF (dedicated verb; N-Quads out)\n";
  Printf.printf "                   factoidal jsonld --in doc.jsonld [--base IRI]\n";
  Printf.printf "  rif            RIF Core forward-chaining saturation\n";
  Printf.printf "                   factoidal rif --rules rules.rif --data data.ttl\n";
  Printf.printf "  entail         Materialize an RDFS/OWL-RL entailment closure (npm owlClosure())\n";
  Printf.printf "                   factoidal entail --data data.ttl --regime RDFS|OWL-RL\n";
  Printf.printf "  update         In-memory SPARQL 1.1 Update apply + dump (npm update())\n";
  Printf.printf "                   factoidal update --data data.ttl -e 'INSERT DATA {...}'\n";
  Printf.printf "                   (durable on-disk UPDATE: `serve --rw --delta-log` / `compact`)\n";
  Printf.printf "  cottas-import  Import RDF -> COTTAS/Parquet artifact\n";
  Printf.printf "                   factoidal cottas-import --input X.trig --corpus-root C ...\n";
  Printf.printf "                   (shim: execs python3 tools/corpus_pipeline.py)\n";
  Printf.printf "  cottas-info    Summary stats for a COTTAS/Parquet file\n";
  Printf.printf "                   factoidal cottas-info FILE.cottas\n";
  Printf.printf "  compact        Durable-UPDATE stage 4: fold --delta-log into a fresh base\n";
  Printf.printf "                   factoidal compact --data-cottas FILE --delta-log PATH\n";
  Printf.printf "                   (atomic chunk_dir/current -> vN swap; see factoidal_cli.ml)\n";
  Printf.printf "  test SUITE     Run W3C / OWL / RDFC test suites\n";
  Printf.printf "                   factoidal test w3c          (sibling: w3c_runner)\n";
  Printf.printf "                   factoidal test owl-rl       (sibling: owl_runner)\n";
  Printf.printf "                   factoidal test rdfc10       (sibling: rdfc10_runner)\n";
  Printf.printf "  help           Show this help\n";
  Printf.printf "  version        Show version\n";
  Printf.printf "\n";
  Printf.printf "Standalone binaries (still shipped, will be deprecated in 1.0):\n";
  Printf.printf "  factoidal-http   -> factoidal serve\n";
  Printf.printf "  w3c_runner       -> factoidal test w3c\n";
  Printf.printf "  owl_runner       -> factoidal test owl-rl\n";
  Printf.printf "  rdfc10_runner    -> factoidal test rdfc10\n";
  Printf.printf "  tools/corpus_pipeline.py materialize-nq-cottas-corpus\n";
  Printf.printf "                   -> factoidal cottas-import\n";
  Printf.printf "\n";
  Printf.printf "For the full legacy flag surface (--data, --query, --dump, --count,\n";
  Printf.printf "--data-cottas, --entail RDFS|OWL-RL, etc.) run: factoidal query --help\n";
  Printf.printf "\n";
  Printf.printf "Plan: docs/designissues/2026-04-25-unified-factoidal-cli-plan.md\n"

(* Returns the args (post-argv[0]) the legacy parser should consume.
   - For navigation/exec subcommands, exits or execs and never returns.
   - For `query`, returns the tail (subcommand stripped).
   - For `dump`/`dump-nq`/`count`, prepends the matching legacy flag + --data flags.
   - For everything else (legacy invocation), returns the original tail. *)
let dispatch_subcommand () =
  let argv_tail = Array.to_list Sys.argv |> List.tl in
  match argv_tail with
  | cmd :: rest when List.mem cmd known_subcommands ->
    (match cmd with
     | "help" -> print_navigation_help (); exit 0
     | "version" -> version (); exit 0
     | "serve" ->
       (* In-process call (no exec). The native build links
          factoidal_serve.ml (which forwards to Factoidal_http); the JS
          build links factoidal_serve_jsoo.ml (a stub that errors out).
          Either way the entry point is the same Factoidal_serve module.
          Phase 2: docs/designissues/2026-04-25-cli-http-unification-phase2.md *)
       Factoidal_serve.start_with_args rest;
       exit 0
     | "test" ->
       (match rest with
        | "w3c" :: tail -> exec_sibling "w3c_runner" tail
        | ("owl-rl" | "owl") :: tail -> exec_sibling "owl_runner" tail
        | ("rdfc10" | "rdfc-10") :: tail -> exec_sibling "rdfc10_runner" tail
        | suite :: _ ->
          Printf.eprintf
            "factoidal test: unknown suite '%s'. Try: w3c | owl-rl | rdfc10\n" suite;
          exit 2
        | [] ->
          Printf.eprintf
            "factoidal test: missing suite name. Try: w3c | owl-rl | rdfc10\n";
          exit 2)
     | "cottas-import" ->
       exec_corpus_pipeline "materialize-nq-cottas-corpus" rest
     | "cottas-info" ->
       (* Bet7 (issue #100, 2026-04-26): summary of a COTTAS/Parquet
          artifact via Parquet_Footer probes only. Previously this opened
          the corpus through Parser_BallyhooCOTTAS.cottas_open_dataset_store
          which eagerly decoded all 4 columns across every row group +
          interned every term — ~98 s + 2.2 GB RSS for the parliament
          corpus.

          The headline number cottas-info reports (quads) is derivable
          from the Parquet footer alone. Distinct subject / predicate /
          object / named-graph counts require walking the column data
          pages: for the parliament corpus the predicate column has
          ~232 distinct values but each row group's data page must still
          be decoded to enumerate them (no separate dictionary page is
          present in the COTTAS-style layout we ship). So this handler
          now:
            - quads, row groups: probe_parquet_*       (footer-only, ms).
            - distinct subj/pred/obj/graph: SKIPPED by default. Pass
              --full-scan to fall back to the old eager Ballyhoo load
              (~100 s + 2 GB RSS on parliament).

          F* / RDF semantics live in Parquet.Footer.probe_parquet_*; this
          is pure read + arithmetic glue (rule #15). *)
       (match rest with
        | [] | ["--help"] | ["-h"] ->
          Printf.printf
            "Usage: factoidal cottas-info [--full-scan] FILE\n\n\
             Print summary statistics for a COTTAS/Parquet artifact.\n\n\
             Reports total quads + row group count in seconds via Parquet\n\
             footer probes (no data scan). Pass --full-scan to also report\n\
             distinct subject / predicate / object / named-graph counts,\n\
             which requires decoding every row group's columns (~100 s\n\
             for the 3M-quad parliament corpus).\n";
          exit (if rest = [] then 2 else 0)
        | args ->
          let full_scan = List.mem "--full-scan" args in
          let path =
            match List.filter (fun s -> s <> "--full-scan") args with
            | p :: _ -> p
            | [] ->
              Printf.eprintf "Error: cottas-info requires a path\n";
              exit 2
          in
          (* Footer-only probes: cheap (single tail read + thrift parse). *)
          let n_quads = match Parquet_Footer.probe_parquet_num_rows path with
            | FStar_Pervasives_Native.Some n -> Z.to_int n
            | FStar_Pervasives_Native.None ->
              Printf.eprintf "Error: could not read Parquet footer: %s\n" path;
              exit 1 in
          let n_row_groups = match Parquet_Footer.probe_parquet_row_group_count path with
            | FStar_Pervasives_Native.Some n -> Z.to_int n
            | FStar_Pervasives_Native.None -> 0 in
          Printf.printf "file:               %s\n" path;
          Printf.printf "quads:              %d\n" n_quads;
          Printf.printf "row groups:         %d\n" n_row_groups;
          if full_scan then begin
            Printf.printf "(full-scan: walking all row groups for distinct counts ...)\n%!";
            (match Parser_BallyhooCOTTAS.cottas_open_dataset_store
                     path FStar_Pervasives_Native.None with
             | FStar_Pervasives_Native.None ->
               Printf.eprintf "Error: --full-scan open failed: %s\n" path;
               exit 1
             | FStar_Pervasives_Native.Some store ->
               let cache =
                 Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.cache_for_store
                   store in
               (* The cache already has subject_to_id / predicate_to_id /
                  object_to_id / graph_to_id hashtables populated by
                  interning during load_cache; use their lengths directly
                  rather than re-walking the quads list. *)
               Printf.printf "distinct subjects:  %d\n"
                 (Hashtbl.length cache.Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.subject_to_id);
               Printf.printf "distinct predicates:%d\n"
                 (Hashtbl.length cache.Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.predicate_to_id);
               Printf.printf "distinct objects:   %d\n"
                 (Hashtbl.length cache.Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.object_to_id);
               Printf.printf "named graphs:       %d\n"
                 (Hashtbl.length cache.Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.graph_to_id))
          end else begin
            Printf.printf "distinct subjects:  (skipped; pass --full-scan)\n";
            Printf.printf "distinct predicates:(skipped; pass --full-scan)\n";
            Printf.printf "distinct objects:   (skipped; pass --full-scan)\n";
            Printf.printf "named graphs:       (skipped; pass --full-scan)\n"
          end;
          exit 0)
     | "graphs" ->
       (* Graphs-first API surface, in-memory only (slice 1):
          docs/designissues/2026-07-05-graphs-api-design.md section 1.2.
          Each subcommand is a thin bin/ wrapper (rule #11) over
          RDF.Dataset.Graphs / RDF.Canonical, both F*-verified; this
          layer only loads the file(s) and formats output. *)
       let usage_graphs () =
         Printf.eprintf
           "Usage: factoidal graphs list FILE\n\
            \       factoidal graphs get FILE IRI\n\
            \       factoidal graphs hash FILE IRI\n\
            \       factoidal graphs diff FILE1 FILE2\n";
         exit 2
       in
       let load_one f =
         try load_dataset f
         with e ->
           Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
           exit 1
       in
       (* (iri, canonical-N-Quads-hash) pairs for every named graph in a
          dataset, dropping any name not resolved by component_of (should
          not happen: names come from the same dataset's ds_named). *)
       let graph_hashes ds =
         List.filter_map (fun (iri, _g) ->
           match RDF_Canonical.canonicalize_named_graph ds iri with
           | FStar_Pervasives_Native.Some h -> Some (iri, h)
           | FStar_Pervasives_Native.None -> None
         ) (RDF_Dataset_Graphs.graphs ds)
       in
       (match rest with
        | ["list"; file] ->
          let ds = load_one file in
          List.iter (fun (iri, _g) -> Printf.printf "%s\n" iri)
            (RDF_Dataset_Graphs.graphs ds);
          exit 0
        | ["get"; file; iri] ->
          let ds = load_one file in
          (match RDF_Dataset_Graphs.component_of ds iri with
           | FStar_Pervasives_Native.Some g -> print_results_ntriples g; exit 0
           | FStar_Pervasives_Native.None ->
             Printf.eprintf "Error: no such named graph: %s\n" iri; exit 1)
        | ["hash"; file; iri] ->
          let ds = load_one file in
          (match RDF_Canonical.canonicalize_named_graph ds iri with
           | FStar_Pervasives_Native.Some s -> print_string s; exit 0
           | FStar_Pervasives_Native.None ->
             Printf.eprintf "Error: no such named graph: %s\n" iri; exit 1)
        | ["diff"; file1; file2] ->
          (* Set comparison over two already-verified strings, not new
             RDF/SPARQL semantics -- stays in bin/ under rule #11. *)
          let hashes1 = graph_hashes (load_one file1) in
          let hashes2 = graph_hashes (load_one file2) in
          let names1 = List.map fst hashes1 in
          let names2 = List.map fst hashes2 in
          let added = List.filter (fun n -> not (List.mem n names1)) names2 in
          let removed = List.filter (fun n -> not (List.mem n names2)) names1 in
          let changed = List.filter_map (fun (n, h1) ->
            match List.assoc_opt n hashes2 with
            | Some h2 when h2 <> h1 -> Some n
            | _ -> None
          ) hashes1 in
          List.iter (fun n -> Printf.printf "+ %s\n" n) added;
          List.iter (fun n -> Printf.printf "- %s\n" n) removed;
          List.iter (fun n -> Printf.printf "~ %s\n" n) changed;
          exit 0
        | _ -> usage_graphs ())
     | "validate" ->
       (* SHACL Core validation (slice 1, issue #181). Consumer wiring
          only (rule #11) — all shape parsing, target computation,
          path evaluation, and constraint evaluation live in
          formal/fstar/SHACL.Validation.fst. This handler just loads
          two RDF files and prints the resulting report. *)
       let usage_validate () =
         Printf.eprintf
           "Usage: factoidal validate --shapes SHAPES.ttl DATA.ttl\n";
         exit 2
       in
       let rec parse_validate_args shapes_path data_path = function
         | [] -> (shapes_path, data_path)
         | "--shapes" :: p :: rest -> parse_validate_args (Some p) data_path rest
         | ("--help" | "-h") :: _ -> usage_validate ()
         | p :: rest when data_path = None -> parse_validate_args shapes_path (Some p) rest
         | _ -> usage_validate ()
       in
       let (shapes_path, data_path) = parse_validate_args None None rest in
       (match shapes_path, data_path with
        | Some sp, Some dp ->
          let shapes_triples =
            try load_triples sp
            with e ->
              Printf.eprintf "Error parsing shapes graph %s: %s\n" sp (Printexc.to_string e);
              exit 1
          in
          let data_triples =
            try load_triples dp
            with e ->
              Printf.eprintf "Error parsing data graph %s: %s\n" dp (Printexc.to_string e);
              exit 1
          in
          let sg = SHACL_Validation.parse_shape_from_graph shapes_triples in
          let report = SHACL_Validation.validate data_triples shapes_triples sg in
          let conforms = report.SHACL_Validation.conforms in
          let results = report.SHACL_Validation.results in
          let string_of_term t = RDF_Pretty.term_to_turtle t in
          let string_of_path_opt = function
            | FStar_Pervasives_Native.None -> "(none)"
            | FStar_Pervasives_Native.Some (SHACL_Validation.P_Predicate p) -> p
            | FStar_Pervasives_Native.Some (SHACL_Validation.P_Inverse (SHACL_Validation.P_Predicate p)) ->
              "^" ^ p
            | FStar_Pervasives_Native.Some _ -> "(complex path)"
          in
          let string_of_severity = function
            | SHACL_Validation.Sev_Info -> "Info"
            | SHACL_Validation.Sev_Warning -> "Warning"
            | SHACL_Validation.Sev_Violation -> "Violation"
            | SHACL_Validation.Sev_Custom iri -> iri
          in
          Printf.printf "sh:conforms %b\n" conforms;
          List.iter
            (fun v ->
               Printf.printf "  [%s] focus=%s path=%s%s source=%s\n"
                 (string_of_severity v.SHACL_Validation.v_severity)
                 (string_of_term v.SHACL_Validation.v_focus_node)
                 (string_of_path_opt v.SHACL_Validation.v_path)
                 (match v.SHACL_Validation.v_value with
                  | FStar_Pervasives_Native.Some value -> " value=" ^ string_of_term value
                  | FStar_Pervasives_Native.None -> "")
                 v.SHACL_Validation.v_source_shape)
            results;
          exit (if conforms then 0 else 1)
        | _ -> usage_validate ())
     | "compact" -> run_compact rest; exit 0
     | "import" -> run_import rest; exit 0
     | "shacl" -> run_shacl_validate rest; exit 0
     | "shex" -> run_shex rest; exit 0
     | "rml" -> run_rml rest; exit 0
     | "csvw" -> run_csvw rest; exit 0
     | "jsonld" -> run_jsonld rest; exit 0
     | "rif" -> run_rif rest; exit 0
     | "entail" -> run_entail rest; exit 0
     | "update" -> run_update rest; exit 0
     | "query" -> rest
     | "dump"  -> "--dump"  :: List.concat_map (fun f -> ["--data"; f]) rest
     | "dump-nq" -> "--dump-nq" :: List.concat_map (fun f -> ["--data"; f]) rest
     | "dump-turtle" -> "--dump-turtle" :: List.concat_map (fun f -> ["--data"; f]) rest
     | "canonicalize" -> "--canonicalize" :: List.concat_map (fun f -> ["--data"; f]) rest
     | "count" -> "--count" :: List.concat_map (fun f -> ["--data"; f]) rest
     | _ -> argv_tail)  (* unreachable *)
  | ("--help" | "-h") :: _ ->
    (* Top-level --help shows BOTH the subcommand nav + legacy flags. *)
    print_navigation_help ();
    Printf.printf "\n--- Legacy flag-form usage (factoidal query) ---\n\n";
    usage ();
    exit 0
  | _ -> argv_tail  (* fall through to legacy parser *)

(* ============================================================================
   Main
   ============================================================================ *)

let () =
  (* Pe4 instrumentation: enable backtraces + signal handlers so the
     `factoidal serve` daemon doesn't disappear silently when the
     cottas-ondisk runtime hits an abort/SIGPIPE/SIGTERM.  Mirrors the
     handlers in factoidal_http_main.ml (which only fire for the
     standalone factoidal-http binary).  See
     docs/designissues/2026-04-25-pe4-mim2-daemon-crash-investigation.md. *)
  Printexc.record_backtrace true;
  let log_signal sname signo =
    Printf.eprintf "[pe4-SIGNAL] caught %s (signo=%d) — printing backtrace and exiting\n%!"
      sname signo;
    Printexc.print_backtrace stderr;
    Printf.eprintf "[pe4-SIGNAL] (note: backtrace may be empty if not raised via OCaml exception)\n%!";
    exit 137
  in
  (try Sys.set_signal Sys.sigabrt (Sys.Signal_handle (log_signal "SIGABRT")) with _ -> ());
  (try Sys.set_signal Sys.sigpipe (Sys.Signal_handle (log_signal "SIGPIPE")) with _ -> ());
  (try Sys.set_signal Sys.sigterm (Sys.Signal_handle (log_signal "SIGTERM")) with _ -> ());
  let args = dispatch_subcommand () in
  let cfg = parse_args ~args () in

  if cfg.help_mode then (usage (); exit 0);
  if cfg.version_mode then (version (); exit 0);

  (* Helper: flatten a COTTAS dataset down to a triple list (default + named) *)
  let cottas_all_triples path =
    let ds = load_cottas_dataset path in
    match ds.ds_named with
    | [] -> ds.ds_default
    | named ->
      concat_preserve_order
        (ds.ds_default :: List.map (fun ng -> ng.ng_graph) named)
  in

  (* Explain mode: parse + algebra + per-triple-pattern cardinality estimates.
     Does NOT execute the BGP walk. See factoidal_explain.ml + scratch
     docs/designissues/2026-04-26-pe5-explain-mode.md.

     Requires at least one --data-cottas FILE (the explain logic queries
     the on-disk dictionaries to determine bound dictionary hits/misses
     + estimate). The query text comes from -e, --explain "...", or
     --query FILE with --explain-only. *)
  if cfg.explain_mode then begin
    let query_text = match cfg.query_string, cfg.query_file with
      | Some q, _ -> q
      | None, Some f -> read_file f
      | None, None ->
        Printf.eprintf "Error: --explain requires SPARQL via --explain '<query>', -e '<query>', or --query FILE.\n";
        exit 1
    in
    if cfg.data_cottas_files = [] then begin
      Printf.eprintf "Error: --explain requires at least one --data-cottas FILE.\n";
      Printf.eprintf "       (Plan dump only makes sense against an on-disk store today.)\n";
      exit 1
    end;
    let json_out = match cfg.explain_out with
      | None -> None
      | Some path -> Some (open_out path)
    in
    let rc = Factoidal_explain.explain_query
      ~query_text
      ~cottas_paths:cfg.data_cottas_files
      ~json_out
      ()
    in
    (match json_out with Some c -> close_out c | None -> ());
    exit rc
  end;

  (* Dump mode: parse and emit N-Triples *)
  if cfg.dump_mode then begin
    if cfg.data_files = [] && cfg.data_cottas_files = [] then begin
      Printf.eprintf "Error: no data files specified (use --data FILE or just FILE)\n";
      exit 1
    end;
    let file_triples = concat_map_preserve_order (fun f ->
      try load_triples ~format:cfg.input_format ~base:cfg.base_iri f
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files in
    let cottas_triples = concat_map_preserve_order (fun f ->
      try cottas_all_triples f
      with e ->
        Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_cottas_files in
    print_results_ntriples (append_preserve_order file_triples cottas_triples);
    exit 0
  end;

  (* Dump mode: parse and emit prefix-compacted, subject-grouped Turtle.
     Same load path as --dump; the rendering itself is
     RDF_Turtle_Serialize.turtle_of_graph_auto (formal/fstar/
     RDF.Turtle.Serialize.fst) — auto-derives an @prefix table from the
     graph's own most-frequent IRI namespaces. *)
  if cfg.dump_turtle_mode then begin
    if cfg.data_files = [] && cfg.data_cottas_files = [] then begin
      Printf.eprintf "Error: no data files specified (use --data FILE or just FILE)\n";
      exit 1
    end;
    let file_triples = concat_map_preserve_order (fun f ->
      try load_triples ~format:cfg.input_format ~base:cfg.base_iri f
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files in
    let cottas_triples = concat_map_preserve_order (fun f ->
      try cottas_all_triples f
      with e ->
        Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_cottas_files in
    print_string (turtle_of_graph_pretty (append_preserve_order file_triples cottas_triples));
    exit 0
  end;

  if cfg.dump_nq_mode then begin
    if cfg.data_files = [] && cfg.data_cottas_files = [] then begin
      Printf.eprintf "Error: no data files specified (use --data FILE or just FILE)\n";
      exit 1
    end;
    let file_datasets = List.map (fun f ->
      try load_dataset ~format:cfg.input_format ~base:cfg.base_iri f
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files in
    let cottas_datasets = List.map (fun f ->
      try load_cottas_dataset f
      with e ->
        Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_cottas_files in
    let datasets = file_datasets @ cottas_datasets in
    let ds_default = concat_map_preserve_order (fun ds -> ds.ds_default) datasets in
    let ds_named = concat_map_preserve_order (fun ds -> ds.ds_named) datasets in
    let dataset = RDF_Graph_Executable.({ ds_default; ds_named }) in
    print_string (RDF_Canonical.canonical_nquads dataset);
    exit 0
  end;

  (* Canonicalize mode: RDFC-1.0 (RDF Dataset Canonicalization).
     Unlike dump-nq (which only sorts), this runs the canonical
     blank-node labelling algorithm from RDF.Canonical.fst, then
     serializes canonical N-Quads. Same load path as dump-nq. *)
  if cfg.canonicalize_mode then begin
    if cfg.data_files = [] && cfg.data_cottas_files = [] then begin
      Printf.eprintf "Error: no data files specified (use --data FILE or just FILE)\n";
      exit 1
    end;
    let file_datasets = List.map (fun f ->
      try load_dataset ~format:cfg.input_format ~base:cfg.base_iri f
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files in
    let cottas_datasets = List.map (fun f ->
      try load_cottas_dataset f
      with e ->
        Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_cottas_files in
    let datasets = file_datasets @ cottas_datasets in
    let ds_default = concat_map_preserve_order (fun ds -> ds.ds_default) datasets in
    let ds_named = concat_map_preserve_order (fun ds -> ds.ds_named) datasets in
    let dataset = RDF_Graph_Executable.({ ds_default; ds_named }) in
    print_string (RDF_Canonical.canonicalize_to_nquads dataset);
    exit 0
  end;

  (* Count mode.
     Turtle fast path: Parser_Turtle.count_turtle_triples(_with_base)
     scans once without materialising a triple list — safe on
     million-triple files where the full list would overflow the
     native stack on downstream List ops. *)
  if cfg.count_mode then begin
    if cfg.data_files = [] && cfg.data_cottas_files = [] then begin
      Printf.eprintf "Error: no data files specified\n"; exit 1
    end;
    List.iter (fun f ->
      try
        let fmt = match cfg.input_format with
          | Some x -> x
          | None -> detect_format f in
        let label = if f = "-" then "<stdin>" else f in
        match fmt with
        | Turtle ->
          let content = read_file f in
          let base_iri = match cfg.base_iri with
            | Some b -> Some b
            | None -> file_base_iri f in
          let n = match base_iri with
            | Some b -> Parser_Turtle.count_turtle_triples_with_base content b
            | None -> Parser_Turtle.count_turtle_triples content in
          Printf.printf "%s: %s triples\n" label (Z.to_string n)
        | NT ->
          (* Issue #121: count-only avoids growing a 7M-element triple list. *)
          let content = read_file f in
          let n = Parser_NTriples.count_ntriples content in
          Printf.printf "%s: %s triples\n" label (Z.to_string n)
        | NQuads ->
          (* Issue #121: count-only avoids growing the rdf_dataset. *)
          let content = read_file f in
          let n = Parser_NQuads.count_nquads_quads content in
          Printf.printf "%s: %s triples\n" label (Z.to_string n)
        | _ ->
          let triples = load_triples ~format:cfg.input_format ~base:cfg.base_iri f in
          Printf.printf "%s: %d triples\n" label (List.length triples)
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files;
    List.iter (fun f ->
      try
        let triples = cottas_all_triples f in
        Printf.printf "%s: %d triples (COTTAS)\n" f (List.length triples)
      with e ->
        Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_cottas_files;
    exit 0
  end;

  (* Query mode *)
  let query_text = match cfg.query_string, cfg.query_file with
    | Some q, _ -> q
    | None, Some f -> read_file f
    | None, None ->
      Printf.eprintf "Error: no query specified. Use --query FILE or -e 'SPARQL'\n";
      Printf.eprintf "       For RDF parsing, use --dump or --count.\n";
      Printf.eprintf "       Try --help for usage.\n";
      exit 1
  in

  (* Parse SPARQL query *)
  let query = try
    match SPARQL11_Parser.parse_sparql query_text with
    | SPARQL11_Parser.ParseOk (q, _) -> q
    | SPARQL11_Parser.ParseErr msg ->
      Printf.eprintf "SPARQL parse error: %s\n" msg; exit 1
  with e ->
    Printf.eprintf "SPARQL parse error: %s\n" (Printexc.to_string e); exit 1
  in

  (* Parse-stream query fast path (docs/designissues/2026-07-05-disk-
     backed-db-perf-review.md, roadmap "bound in-memory query
     memory"): `factoidal --data gene.ttl` answering a one-row
     COUNT-star peaked at 731 MiB RSS -- the same cost as a full point-
     lookup materialisation -- because load_dataset below always
     parses every --data file into a complete in-memory term graph
     before the query is evaluated at all. For the four shapes
     SPARQL.Plan.Streamable recognizes (COUNT-star/ASK over a single
     triple pattern, default graph or a `GRAPH ?g` wildcard over named
     graphs), answer straight off the SAME incremental parse hook the
     `count` subcommand above uses (Parser_Turtle/NTriples/NQuads'
     fold_* entry points) and skip load_dataset/build_indexed
     entirely. Output goes through print_query_results -- the exact
     same formatter the materialise path below uses -- so JSON/CSV/
     table output is byte-identical by construction, not by a second
     hand-written formatter that could drift.
     Gated off entirely for COTTAS/--named/entailment-closure inputs
     (those need the full backend machinery regardless); anything
     SPARQL.Plan.Streamable.streamable_shape doesn't recognize, or any
     --data file that isn't Turtle/NT/NQuads, falls through unchanged
     to the existing path below. FACTOIDAL_DISABLE_STREAM_FASTPATH=1
     forces the fallthrough -- used by
     tests/local/streamable_fastpath_regressions.sh to diff fast-path
     output against the materialise path on the same fixtures/queries. *)
  let fastpath_disabled =
    match Sys.getenv_opt "FACTOIDAL_DISABLE_STREAM_FASTPATH" with
    | Some "1" -> true
    | _ -> false
  in
  if not fastpath_disabled
     && cfg.data_cottas_files = []
     && cfg.data_hdt_files = []
     && cfg.named_graphs = []
     && cfg.entail_regime = ""
     && cfg.data_files <> []
  then begin
    match SPARQL_Plan_Streamable.streamable_shape query with
    | None -> ()
    | Some plan ->
      let file_formats = List.map (fun f ->
        match cfg.input_format with
        | Some fmt -> fmt
        | None -> detect_format f
      ) cfg.data_files in
      let all_streamable_fmt = List.for_all (fun fmt -> match fmt with
        | Turtle | NT | NQuads -> true
        | _ -> false
      ) file_formats in
      if all_streamable_fmt then begin
        let open SPARQL_Plan_Streamable in
        let state = List.fold_left (fun st f ->
          let fmt = match cfg.input_format with
            | Some fmt -> fmt
            | None -> detect_format f in
          let content = read_file f in
          match fmt with
          | Turtle ->
            let base_iri = match cfg.base_iri with
              | Some b -> Some b
              | None -> file_base_iri f in
            (match base_iri with
             | Some b ->
               Parser_Turtle.fold_turtle_triples_with_base
                 (fun t acc -> stream_step plan t acc) (stream_stop plan) st content b
             | None ->
               Parser_Turtle.fold_turtle_triples
                 (fun t acc -> stream_step plan t acc) (stream_stop plan) st content)
          | NT ->
            Parser_NTriples.fold_ntriples
              (fun t acc -> stream_step plan t acc) (stream_stop plan) st content
          | NQuads ->
            Parser_NQuads.fold_nquads
              (fun t g acc -> if stream_in_domain plan g then stream_step plan t acc else acc)
              (stream_stop plan) st content
          | _ ->
            (* unreachable: all_streamable_fmt already filtered these out *)
            st
        ) stream_init cfg.data_files in
        let ask_answer, results = match plan.sp_goal with
          | SG_Ask -> (Some (stream_ask_result state), [])
          | SG_Count alias ->
            let n = stream_count_result state in
            let omega = SPARQL11_Store.count_star_solution alias n in
            (None, SPARQL11_Algebra.slice_solutions plan.sp_offset plan.sp_limit omega)
        in
        print_query_results cfg query ask_answer results;
        exit 0
      end
  end;

  (* Load data files as datasets, preserving named graph structure *)
  let datasets = List.map (fun f ->
    try load_dataset ~format:cfg.input_format ~base:cfg.base_iri f
    with e ->
      Printf.eprintf "Error loading %s: %s\n" f (Printexc.to_string e);
      exit 1
  ) cfg.data_files in

  (* Merge all default graphs and named graphs from file-based inputs.
     The on-disk COTTAS path is attached later as a dataset_backend so
     SELECT/ASK can share the same executor as the production server. *)
  let graph = concat_map_preserve_order (fun ds -> ds.ds_default) datasets in
  let file_named_graphs = concat_map_preserve_order (fun ds -> ds.ds_named) datasets in

  (* Load explicitly named graphs from --named flag *)
  let cli_named_graphs = List.map (fun (iri, path) ->
    let triples = try load_triples ~format:cfg.input_format ~base:cfg.base_iri path
    with e ->
      Printf.eprintf "Error loading named graph %s from %s: %s\n"
        iri path (Printexc.to_string e);
      exit 1
    in
    RDF_Graph_Executable.({ ng_name = iri; ng_graph = triples })
  ) cfg.named_graphs in

  (* Apply entailment regime closure if requested. The F*-extracted closure
     operates on rdf_graph (list of triples); apply it to the default graph
     and to each named graph in turn. "" is the no-op / "none" case. *)
  let apply_entail tr = match cfg.entail_regime with
    | "OWL-RL" ->
      (try RDF_Graph_Executable.owl_rl_closure_with_reflexivity tr (Z.of_int 100)
       with _ -> tr)
    | "RDFS" ->
      (try RDF_Graph_Executable.rdfs_closure_with_reflexivity tr (Z.of_int 100)
       with _ -> tr)
    | _ -> tr
  in
  let graph = apply_entail graph in
  let all_named = file_named_graphs @ cli_named_graphs in
  let all_named = List.map (fun ng ->
    RDF_Graph_Executable.({ ng_name = ng.ng_name;
                             ng_graph = apply_entail ng.ng_graph })
  ) all_named in

  let dataset = RDF_Graph_Executable.({
    ds_default = graph;
    ds_named = all_named
  }) in

  (* Issue #103: CONSTRUCT (and DESCRIBE) produce an RDF graph, not
     solution bindings, so they are handled here rather than falling
     into the SELECT/ASK dispatch below. Before this fix the code below
     unconditionally called `eval_select_query` for every non-backend
     form, and SPARQL11_Algebra.eval_select_query's catch-all is
     `| QF_Construct _ -> [] | QF_Describe _ -> []` (SPARQL11.Algebra.fst
     ~line 3829) — so CONSTRUCT silently produced zero triples.
     SPARQL11_Algebra.eval_construct_query (SPARQL11.Algebra.fst:3940)
     is the real evaluator (already consumed by w3c_runner.ml and
     entry_jsoo.ml); wire it in here.
     There is no backend-dataset CONSTRUCT executor yet — SPARQL11_Store
     only exposes run_select_query_backend_dataset /
     run_ask_query_backend_dataset — so --data-cottas CONSTRUCT still
     runs against an eagerly-materialized in-memory graph, same
     limitation tracked in issue #103's acceptance criteria for the
     backend-executor follow-up. To make --data-cottas usable at all
     for CONSTRUCT in the meantime, COTTAS triples are folded into the
     eager graph here (mirroring --dump / --dump-nq's cottas_all_triples
     use above) rather than silently ignored. *)
  (match query.q_form with
   | QF_Construct _ ->
     let cottas_triples = concat_map_preserve_order (fun f ->
       try cottas_all_triples f
       with e ->
         Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
         exit 1
     ) cfg.data_cottas_files in
     let construct_graph = append_preserve_order graph cottas_triples in
     let construct_dataset = RDF_Graph_Executable.({
       ds_default = construct_graph;
       ds_named = all_named
     }) in
     let rewritten_query = OWL_QueryRewrite.rewrite_query query in
     let triples =
       try
         SPARQL11_Algebra.eval_construct_query
           rewritten_query construct_graph construct_dataset
       with e ->
         Printf.eprintf "Query evaluation error: %s\n" (Printexc.to_string e);
         exit 1
     in
     (match cfg.output_format with
      | NTOut | Table -> print_results_ntriples triples
      | CSV | JSON ->
        (* CONSTRUCT yields a graph, not tabular rows; CSV/JSON result
           formats don't apply. Fall back to N-Triples rather than
           silently emitting nothing. *)
        print_results_ntriples triples);
     exit 0
   | QF_Describe _ ->
     Printf.eprintf
       "Error: DESCRIBE is not supported by the factoidal CLI yet \
        (no F*-extracted eval_describe_query; SPARQL11_Algebra.eval_select_query's \
        QF_Describe case is a stub returning []). See issue #103.\n";
     exit 1
   | QF_Select _ | QF_Ask -> ());

  (* Take the SPARQL11_Store backend executor for SELECT/ASK whenever
     entailment is the no-op identity — including the in-memory case.
     build_dataset_backend handles the empty-cottas list (returns the
     indexed_dataset_backend of the in-memory dataset). The previous
     `data_cottas_files <> []` gate forced in-memory loads onto the
     slower eval_select_query path, which also bypasses the
     detect_streaming_count_group_by_graph fast path needed for Q01-
     style demo queries. *)
  let use_backend_exec =
    cfg.entail_regime = "" &&
    match query.q_form with
    | QF_Select _ | QF_Ask -> true
    | _ -> false
  in

  (* Evaluate *)
  (try
    let is_ask = match query.q_form with QF_Ask -> true | _ -> false in
    let rewritten_query = OWL_QueryRewrite.rewrite_query query in
    let ask_answer, results =
      if use_backend_exec then begin
        let cottas_stores = List.map (fun f ->
          try open_cottas_ondisk_store f
          with e ->
            Printf.eprintf "Error opening on-disk COTTAS %s: %s\n" f (Printexc.to_string e);
            exit 1
        ) cfg.data_cottas_files in
        let hdt_stores = List.map (fun f ->
          try open_hdt_store f
          with e ->
            Printf.eprintf "Error opening HDT %s: %s\n" f (Printexc.to_string e);
            exit 1
        ) cfg.data_hdt_files in
        let dsb =
          build_dataset_backend dataset cottas_stores cfg.data_cottas_files cfg.delta_log_path hdt_stores
        in
        let ask_answer =
          if is_ask then
            match SPARQL11_Store.run_ask_query_backend_dataset rewritten_query dsb with
            | Some b -> Some b
            | None ->
              Printf.eprintf "Query evaluation error: backend ASK path unavailable\n";
              exit 1
          else None in
        let results =
          if is_ask then []
          else
            match SPARQL11_Store.run_select_query_backend_dataset rewritten_query dsb with
            | Some rows -> rows
            | None ->
              Printf.eprintf "Query evaluation error: backend SELECT path unavailable\n";
              exit 1 in
        (ask_answer, results)
      end else begin
        let ask_answer =
          if is_ask then Some (SPARQL11_Algebra.eval_ask_query rewritten_query graph dataset)
          else None in
        let results =
          if is_ask then []
          else SPARQL11_Algebra.eval_select_query rewritten_query graph dataset in
        (ask_answer, results)
      end in

    print_query_results cfg query ask_answer results
  with e ->
    Printf.eprintf "Query evaluation error: %s\n" (Printexc.to_string e);
    exit 1)
