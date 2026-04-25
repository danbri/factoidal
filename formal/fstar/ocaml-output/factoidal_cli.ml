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

(* ============================================================================
   Output formatting
   ============================================================================ *)

let term_to_ntriples t =
  match t with
  | T_IRI i -> Printf.sprintf "<%s>" i
  | T_BNode b -> Printf.sprintf "_:%s" b
  | T_Literal l ->
    let xsd_string = "http://www.w3.org/2001/XMLSchema#string" in
    match l.lang_tag with
    | Some tag -> Printf.sprintf "\"%s\"@%s" l.lexical_form tag
    | None ->
      if l.datatype = "" || l.datatype = xsd_string then
        Printf.sprintf "\"%s\"" l.lexical_form
      else
        Printf.sprintf "\"%s\"^^<%s>" l.lexical_form l.datatype

let term_to_turtle t =
  (* For display purposes, abbreviate common prefixes *)
  match t with
  | T_IRI i ->
    let prefixes = [
      ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
      ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
      ("http://www.w3.org/2001/XMLSchema#", "xsd:");
      ("http://www.w3.org/2002/07/owl#", "owl:");
      ("http://xmlns.com/foaf/0.1/", "foaf:");
      ("http://purl.org/dc/terms/", "dcterms:");
      ("http://purl.org/dc/elements/1.1/", "dc:");
      ("http://schema.org/", "schema:");
    ] in
    (match List.find_opt (fun (ns, _) ->
       String.length i > String.length ns &&
       String.sub i 0 (String.length ns) = ns) prefixes with
     | Some (ns, prefix) ->
       prefix ^ String.sub i (String.length ns) (String.length i - String.length ns)
     | None -> "<" ^ i ^ ">")
  | _ -> term_to_ntriples t

let subject_to_string s =
  match s with
  | S_IRI i -> term_to_turtle (T_IRI i)
  | S_BNode b -> "_:" ^ b

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

(* Detect RDF format from filename extension *)
type rdf_format = NT | Turtle | NQuads | TriG | RDFXML

let detect_format filename =
  let ext = String.lowercase_ascii (Filename.extension filename) in
  match ext with
  | ".nt" | ".ntriples" -> NT
  | ".ttl" | ".turtle" -> Turtle
  | ".nq" | ".nquads" -> NQuads
  | ".trig" -> TriG
  | ".rdf" | ".xml" | ".rdfxml" | ".owl" -> RDFXML
  | _ -> Turtle  (* default *)

let format_of_string s =
  match String.lowercase_ascii s with
  | "ntriples" | "nt" | "n-triples" -> Some NT
  | "turtle" | "ttl" -> Some Turtle
  | "nquads" | "nq" | "n-quads" -> Some NQuads
  | "trig" -> Some TriG
  | "rdfxml" | "rdf/xml" | "rdf" | "xml" -> Some RDFXML
  | _ -> None

let format_name = function
  | NT -> "N-Triples" | Turtle -> "Turtle" | NQuads -> "N-Quads"
  | TriG -> "TriG" | RDFXML -> "RDF/XML"

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

(* Load as dataset, preserving named graph structure for NQuads/TriG *)
let load_dataset ?(format=None) ?(base=None) path =
  let content = read_file path in
  let fmt = match format with Some f -> f | None -> detect_format path in
  let base_iri = match base with Some b -> Some b | None -> file_base_iri path in
  match fmt with
  | NQuads ->
    Parser_NQuads.parse_nquads content
  | TriG ->
    (match base_iri with
     | Some b -> Parser_TriG.parse_trig_with_base_lenient content b
     | None -> Parser_TriG.parse_trig_lenient content)
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
    (* Walk each quad_row in the cache; decode via id_to_* hashtables;
       bucket into default-graph and one triple-list per named graph IRI. *)
    let default_rev = ref [] in
    let named_tbl : (string, RDF_Graph_Executable.triple list ref) Hashtbl.t =
      Hashtbl.create 17 in
    let open Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime in
    List.iter (fun row ->
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
      match row.qr_g with
      | None ->
        default_rev := triple :: !default_rev
      | Some gid ->
        let g_iri = match Hashtbl.find_opt cache.id_to_graph gid with
          | Some g -> g
          | None -> failwith "cottas: missing graph id" in
        let bucket = match Hashtbl.find_opt named_tbl g_iri with
          | Some b -> b
          | None ->
            let b = ref [] in Hashtbl.add named_tbl g_iri b; b in
        bucket := triple :: !bucket
    ) cache.quads;
    let default_g = List.rev !default_rev in
    let named_gs = Hashtbl.fold (fun iri triples acc ->
      RDF_Graph_Executable.({ ng_name = iri; ng_graph = List.rev !triples }) :: acc
    ) named_tbl [] in
    RDF_Graph_Executable.({ ds_default = default_g; ds_named = named_gs })

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

let json_escape s =
  let buf = Buffer.create (String.length s + 8) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | '\b' -> Buffer.add_string buf "\\b"
    | '\012' -> Buffer.add_string buf "\\f"
    | c when Char.code c < 0x20 ->
      Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let json_term t =
  match t with
  | T_IRI i ->
    Printf.sprintf "{\"type\":\"uri\",\"value\":\"%s\"}" (json_escape i)
  | T_BNode b ->
    Printf.sprintf "{\"type\":\"bnode\",\"value\":\"%s\"}" (json_escape b)
  | T_Literal l ->
    let xsd_string = "http://www.w3.org/2001/XMLSchema#string" in
    (match l.lang_tag with
     | Some tag ->
       Printf.sprintf "{\"type\":\"literal\",\"value\":\"%s\",\"xml:lang\":\"%s\"}"
         (json_escape l.lexical_form) (json_escape tag)
     | None ->
       if l.datatype = "" || l.datatype = xsd_string then
         Printf.sprintf "{\"type\":\"literal\",\"value\":\"%s\"}"
           (json_escape l.lexical_form)
       else
         Printf.sprintf "{\"type\":\"literal\",\"value\":\"%s\",\"datatype\":\"%s\"}"
           (json_escape l.lexical_form) (json_escape l.datatype))

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
  mutable named_graphs : (string * string) list;  (* (iri, file) *)
  mutable query_file : string option;
  mutable query_string : string option;
  mutable base_iri : string option;
  mutable input_format : rdf_format option;
  mutable output_format : output_format;
  mutable dump_mode : bool;
  mutable count_mode : bool;
  mutable help_mode : bool;
  mutable version_mode : bool;
  mutable entail_regime : string;  (* "" (none), "RDFS", or "OWL-RL" *)
}

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
  Printf.printf "  factoidal --count FILE.ttl          Count triples\n";
  Printf.printf "  factoidal --dump --format rdfxml FILE.rdf\n";
  Printf.printf "\n";
  Printf.printf "Options:\n";
  Printf.printf "  -d, --data FILE        Load RDF data (repeatable, \"-\" for stdin)\n";
  Printf.printf "                         Format auto-detected from extension:\n";
  Printf.printf "                         .ttl .nt .nq .nquads .trig .rdf .xml .owl\n";
  Printf.printf "      --data-cottas FILE Load a COTTAS/Parquet dataset (repeatable).\n";
  Printf.printf "                         Parsed via the F*-verified Parquet footer\n";
  Printf.printf "                         + DeltaLengthByteArray decoder; Zstd\n";
  Printf.printf "                         decompression via the C stub.\n";
  Printf.printf "  -n, --named IRI=FILE   Load named graph\n";
  Printf.printf "  -q, --query FILE       SPARQL query file\n";
  Printf.printf "  -e SPARQL              Inline SPARQL query string\n";
  Printf.printf "  -b, --base IRI         Base IRI for parsing\n";
  Printf.printf "  -f, --format FMT       Input format: turtle, ntriples, nquads, trig, rdfxml\n";
  Printf.printf "  -o, --output FMT       Output format: table (default), csv, ntriples, json\n";
  Printf.printf "  --entail REGIME        Apply entailment closure to loaded data before\n";
  Printf.printf "                         query evaluation. REGIME is one of:\n";
  Printf.printf "                           none    no closure (default)\n";
  Printf.printf "                           RDFS    RDFS closure + reflexivity axioms\n";
  Printf.printf "                           OWL-RL  OWL 2 RL Datalog subset (includes RDFS)\n";
  Printf.printf "                         Case-insensitive. All closures are F*-extracted.\n";
  Printf.printf "  --dump                 Parse RDF and dump as N-Triples\n";
  Printf.printf "  --count                Parse RDF and count triples\n";
  Printf.printf "  --version              Show version\n";
  Printf.printf "  --help                 This help\n";
  Printf.printf "\n";
  Printf.printf "Supported RDF formats:  Turtle (.ttl), N-Triples (.nt), N-Quads (.nq),\n";
  Printf.printf "                        TriG (.trig), RDF/XML (.rdf, .xml, .owl)\n";
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
    data_files = []; data_cottas_files = []; named_graphs = []; query_file = None;
    query_string = None; base_iri = None; input_format = None;
    output_format = Table; dump_mode = false; count_mode = false;
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
    | "--count" :: rest -> cfg.count_mode <- true; loop rest
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
  ["help"; "version"; "query"; "serve"; "dump"; "count";
   "test"; "cottas-import"; "cottas-info"]

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
  Printf.printf "  count FILE     Parse RDF and count triples\n";
  Printf.printf "  cottas-import  Import RDF -> COTTAS/Parquet artifact\n";
  Printf.printf "                   factoidal cottas-import --input X.trig --corpus-root C ...\n";
  Printf.printf "                   (shim: execs python3 tools/corpus_pipeline.py)\n";
  Printf.printf "  cottas-info    Summary stats for a COTTAS/Parquet file\n";
  Printf.printf "                   factoidal cottas-info FILE.cottas\n";
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
   - For `dump`/`count`, prepends the legacy --dump / --count + --data flags.
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
       (* Minimal summary of a COTTAS/Parquet artifact: open via the
          F*-extracted Parser_BallyhooCOTTAS, walk the cached quad rows,
          and report distinct subject/predicate/object/graph counts plus
          total quad count. All decoding (Parquet footer, DLBA strings)
          happens in F*; this is pure read + count glue (rule #15). *)
       (match rest with
        | [] | ["--help"] | ["-h"] ->
          Printf.printf
            "Usage: factoidal cottas-info FILE\n\n\
             Print summary statistics for a COTTAS/Parquet artifact:\n\
               total quads, distinct subjects, predicates, objects, and\n\
               named graphs.\n";
          exit (if rest = [] then 2 else 0)
        | path :: _ ->
          (match Parser_BallyhooCOTTAS.cottas_open_dataset_store
                   path FStar_Pervasives_Native.None with
           | FStar_Pervasives_Native.None ->
             Printf.eprintf "Error: could not open COTTAS artifact: %s\n" path;
             exit 1
           | FStar_Pervasives_Native.Some store ->
             let cache =
               Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime.cache_for_store
                 store in
             let n_quads = List.length cache.quads in
             let s_set = Hashtbl.create 1024 in
             let p_set = Hashtbl.create 64 in
             let o_set = Hashtbl.create 1024 in
             let g_set = Hashtbl.create 8 in
             let open Parser_BallyhooCOTTAS.Ballyhoo_cottas_runtime in
             List.iter (fun row ->
               Hashtbl.replace s_set row.qr_s ();
               Hashtbl.replace p_set row.qr_p ();
               Hashtbl.replace o_set row.qr_o ();
               (match row.qr_g with
                | None -> ()
                | Some g -> Hashtbl.replace g_set g ())
             ) cache.quads;
             Printf.printf "file:               %s\n" path;
             Printf.printf "quads:              %d\n" n_quads;
             Printf.printf "distinct subjects:  %d\n" (Hashtbl.length s_set);
             Printf.printf "distinct predicates:%d\n" (Hashtbl.length p_set);
             Printf.printf "distinct objects:   %d\n" (Hashtbl.length o_set);
             Printf.printf "named graphs:       %d\n" (Hashtbl.length g_set);
             exit 0))
     | "query" -> rest
     | "dump"  -> "--dump"  :: List.concat_map (fun f -> ["--data"; f]) rest
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

  (* Load data files as datasets, preserving named graph structure *)
  let datasets = List.map (fun f ->
    try load_dataset ~format:cfg.input_format ~base:cfg.base_iri f
    with e ->
      Printf.eprintf "Error loading %s: %s\n" f (Printexc.to_string e);
      exit 1
  ) cfg.data_files in

  (* Load COTTAS/Parquet data files as datasets *)
  let cottas_datasets = List.map (fun f ->
    try load_cottas_dataset f
    with e ->
      Printf.eprintf "Error loading COTTAS %s: %s\n" f (Printexc.to_string e);
      exit 1
  ) cfg.data_cottas_files in
  let datasets = datasets @ cottas_datasets in

  (* Merge all default graphs and named graphs *)
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

  (* Evaluate *)
  (try
    let is_ask = match query.q_form with QF_Ask -> true | _ -> false in
    (* ASK has its own evaluator that returns bool; eval_select_query
       hardcodes QF_Ask -> [] and loses the result. *)
    (* Route both ASK and SELECT through OWL_QueryEval wrappers so the
       OWL.QueryRewrite rewriter runs at every entry point, not just the
       W3C runner's. Keeps the CLI and runner paths identical at the
       F*-visible API level. The wrappers are structurally a no-op on
       queries without OWL-CE markers. *)
    let ask_answer =
      if is_ask then Some (OWL_QueryEval.eval_ask_query_owl query graph dataset)
      else None in
    let results =
      if is_ask then []  (* suppress the select path for ASK *)
      else OWL_QueryEval.eval_select_query_owl query graph dataset in

    (* Extract variable names from query or results *)
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
  with e ->
    Printf.eprintf "Query evaluation error: %s\n" (Printexc.to_string e);
    exit 1)
