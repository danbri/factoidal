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
  ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named

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
}

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
  Printf.printf "  -n, --named IRI=FILE   Load named graph\n";
  Printf.printf "  -q, --query FILE       SPARQL query file\n";
  Printf.printf "  -e SPARQL              Inline SPARQL query string\n";
  Printf.printf "  -b, --base IRI         Base IRI for parsing\n";
  Printf.printf "  -f, --format FMT       Input format: turtle, ntriples, nquads, trig, rdfxml\n";
  Printf.printf "  -o, --output FMT       Output format: table (default), csv, ntriples, json\n";
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

let parse_args () =
  let cfg = {
    data_files = []; named_graphs = []; query_file = None;
    query_string = None; base_iri = None; input_format = None;
    output_format = Table; dump_mode = false; count_mode = false;
    help_mode = false; version_mode = false;
  } in
  let args = Array.to_list Sys.argv |> List.tl in
  let rec loop = function
    | [] -> ()
    | ("--help" | "-h") :: _ -> cfg.help_mode <- true
    | "--version" :: _ -> cfg.version_mode <- true
    | ("--data" | "-d") :: f :: rest -> cfg.data_files <- cfg.data_files @ [f]; loop rest
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
   Main
   ============================================================================ *)

let () =
  let cfg = parse_args () in

  if cfg.help_mode then (usage (); exit 0);
  if cfg.version_mode then (version (); exit 0);

  (* Dump mode: parse and emit N-Triples *)
  if cfg.dump_mode then begin
    if cfg.data_files = [] then begin
      Printf.eprintf "Error: no data files specified (use --data FILE or just FILE)\n";
      exit 1
    end;
    let all_triples = List.concat_map (fun f ->
      try load_triples ~format:cfg.input_format ~base:cfg.base_iri f
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files in
    print_results_ntriples all_triples;
    exit 0
  end;

  (* Count mode *)
  if cfg.count_mode then begin
    if cfg.data_files = [] then begin
      Printf.eprintf "Error: no data files specified\n"; exit 1
    end;
    List.iter (fun f ->
      try
        let triples = load_triples ~format:cfg.input_format ~base:cfg.base_iri f in
        let label = if f = "-" then "<stdin>" else f in
        Printf.printf "%s: %d triples\n" label (List.length triples)
      with e ->
        Printf.eprintf "Error parsing %s: %s\n" f (Printexc.to_string e);
        exit 1
    ) cfg.data_files;
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

  (* Merge all default graphs and named graphs *)
  let graph = List.concat_map (fun ds -> ds.ds_default) datasets in
  let file_named_graphs = List.concat_map (fun ds -> ds.ds_named) datasets in

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

  let dataset = RDF_Graph_Executable.({
    ds_default = graph;
    ds_named = file_named_graphs @ cli_named_graphs
  }) in

  (* Evaluate *)
  (try
    let results = eval_select_query query graph dataset in

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

    let is_ask = match query.q_form with QF_Ask -> true | _ -> false in
    match cfg.output_format with
    | Table ->
      if is_ask then
        Printf.printf "%s\n" (if results <> [] then "Yes" else "No")
      else print_results_table vars results
    | CSV -> print_results_csv vars results
    | JSON ->
      if is_ask then
        Printf.printf "{\n  \"head\": {},\n  \"boolean\": %s\n}\n"
          (if results <> [] then "true" else "false")
      else print_results_json vars results
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
