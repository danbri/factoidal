(* Minimal standalone RDF dataset -> canonical N-Quads serializer.

   This intentionally avoids the HTTP and COTTAS stacks so it can stay
   buildable even when the wider native toolchain is in flux. It uses
   the same extracted RDF parsers + RDF_Canonical serializer that power
   the main CLI. *)

open RDF_Graph_Executable

type rdf_format = NT | Turtle | NQuads | TriG | RDFXML

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

let detect_format filename =
  let ext = String.lowercase_ascii (Filename.extension filename) in
  match ext with
  | ".nt" | ".ntriples" -> NT
  | ".ttl" | ".turtle" -> Turtle
  | ".nq" | ".nquads" -> NQuads
  | ".trig" -> TriG
  | ".rdf" | ".xml" | ".rdfxml" | ".owl" -> RDFXML
  | _ -> Turtle

let format_of_string s =
  match String.lowercase_ascii s with
  | "ntriples" | "nt" | "n-triples" -> Some NT
  | "turtle" | "ttl" -> Some Turtle
  | "nquads" | "nq" | "n-quads" -> Some NQuads
  | "trig" -> Some TriG
  | "rdfxml" | "rdf/xml" | "rdf" | "xml" -> Some RDFXML
  | _ -> None

let file_base_iri path =
  if path = "-" then None
  else
    let abs =
      if Filename.is_relative path
      then Filename.concat (Sys.getcwd ()) path
      else path
    in
    Some ("file://" ^ abs)

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

let usage () =
  Printf.eprintf
    "Usage: factoidal-dump-nq [--format nt|turtle|nq|trig|rdfxml] FILE\n\n\
     Parse RDF with Factoidal's extracted parser stack and emit canonical N-Quads.\n";
  exit 2

let () =
  let format = ref None in
  let input = ref None in
  let rec loop = function
    | [] -> ()
    | ["--help"] | ["-h"] -> usage ()
    | "--format" :: fmt :: rest ->
      (match format_of_string fmt with
       | Some f -> format := Some f; loop rest
       | None ->
         Printf.eprintf "Error: unknown format '%s'\n" fmt;
         exit 2)
    | [path] -> input := Some path
    | arg :: _ when String.length arg > 0 && arg.[0] = '-' ->
      Printf.eprintf "Error: unknown option '%s'\n" arg;
      exit 2
    | _ -> usage ()
  in
  loop (Array.to_list Sys.argv |> List.tl);
  let path = match !input with
    | Some p -> p
    | None -> usage ()
  in
  let dataset =
    try load_dataset ~format:!format path
    with e ->
      Printf.eprintf "Error parsing %s: %s\n" path (Printexc.to_string e);
      exit 1
  in
  print_string (RDF_Canonical.canonical_nquads dataset)
