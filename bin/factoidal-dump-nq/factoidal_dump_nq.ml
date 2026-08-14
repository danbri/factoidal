(* Minimal standalone RDF dataset -> canonical N-Quads serializer.

   This intentionally avoids the HTTP and COTTAS stacks so it can stay
   buildable even when the wider native toolchain is in flux. It uses
   the same extracted RDF parsers + RDF_Canonical serializer that power
   the main CLI. *)

open RDF_Graph_Executable

(* Issue #275 (rule #11 ASSUME-IO): explicitly realise the JSON-LD
   documentLoader seam as an honest "no remote loading" for this
   standalone tool — see JSONLD.Loader.fst's banner and
   jsonld_runner.ml (the ONE consumer with a real fixture-file
   loader). *)
let () = JSONLD_Loader.jsonld_loader_register (fun _ -> FStar_Pervasives_Native.None)

(* rdf_format / detect_format / format_of_string delegate to the
   F*-extracted RDF.Format module so this small standalone tool stays
   in sync with factoidal_cli.ml's version automatically. Rule #1. *)
type rdf_format = RDF_Format.rdf_format =
  | NT
  | Turtle
  | NQuads
  | TriG
  | RDFXML
  | JSONLD

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
  RDF_Format.detect_format_or_default (Filename.extension filename)

let format_of_string s =
  match RDF_Format.format_of_string s with
  | FStar_Pervasives_Native.Some f -> Some f
  | FStar_Pervasives_Native.None -> None

let file_base_iri path =
  if path = "-" then None
  else
    let abs =
      if Filename.is_relative path
      then Filename.concat (Sys.getcwd ()) path
      else path
    in
    Some ("file://" ^ abs)

(* --strict (issue #317 differential-testing harness, 2026-08-14):
   the plain parse_ntriples / parse_turtle[_with_base] entry points
   below are LENIENT — they silently drop malformed input rather than
   failing, so a negative-syntax test (input the spec says MUST be
   rejected) comes back as "parsed successfully, zero triples" instead
   of an error. That is the right behaviour for a best-effort dump
   tool, but it is the WRONG parser to compare against another
   engine's accept/reject verdict: it makes every "-bad-" fixture look
   like a false disagreement. w3c_runner.ml grades negative-syntax
   tests against parse_turtle_strict / parse_ntriples_strict (see its
   comments around parse_turtle_strict / parse_ntriples_strict), which
   return `option` and actually signal failure. --strict routes
   through those same *_strict entry points so this tool's
   accept/reject verdict matches what the W3C conformance suite
   actually grades.

   TriG/N-Quads/RDF-XML (2026-08-14, issue #317 harness extension):
   Parser.TriG.fst's plain `parse_trig` / `parse_trig_with_base` were
   ALREADY option-returning (fail on any parse error) — unlike
   N-Triples/Turtle, TriG never grew a separate "_strict" name because
   its lenient variant is the one with the "_lenient" suffix
   (`parse_trig_lenient` / `parse_trig_with_base_lenient`). So --strict
   for TriG below calls the un-suffixed entry point, not a "_strict"
   one — same option-returning contract, different naming history.
   N-Quads and RDF/XML DO have "_strict"-suffixed entry points
   (`parse_nquads_strict`, `parse_rdfxml_strict` /
   `parse_rdfxml_with_base_strict`), extracted and used exactly like
   the NT/Turtle ones. All of these were already extracted from F* —
   this file only adds the OCaml dispatch to call them (rule #11:
   bin/ is a consumer tool, not inside the verified-library boundary,
   so wiring already-extracted entry points here is not a spec gap). *)
let load_dataset ?(format=None) ?(base=None) ?(strict=false) path =
  let content = read_file path in
  let fmt = match format with Some f -> f | None -> detect_format path in
  let base_iri = match base with Some b -> Some b | None -> file_base_iri path in
  match fmt with
  | NQuads ->
    if strict then
      (match Parser_NQuads.parse_nquads_strict content with
       | FStar_Pervasives_Native.Some ds -> ds
       | FStar_Pervasives_Native.None -> failwith "strict N-Quads parse rejected this input")
    else Parser_NQuads.parse_nquads content
  | TriG ->
    if strict then
      (match
         (match base_iri with
          | Some b -> Parser_TriG.parse_trig_with_base content b
          | None -> Parser_TriG.parse_trig content)
       with
       | FStar_Pervasives_Native.Some ds -> ds
       | FStar_Pervasives_Native.None -> failwith "strict TriG parse rejected this input")
    else
      (match base_iri with
       | Some b -> Parser_TriG.parse_trig_with_base_lenient content b
       | None -> Parser_TriG.parse_trig_lenient content)
  | JSONLD ->
    (* Context processing + document base threading per issue #275 —
       see formal/fstar/Parser.JSONLD.fst module banner. Remote
       contexts / "@import" are an honest FAIL here (no loader
       registered above). *)
    let fs_base = match base_iri with
      | Some b -> FStar_Pervasives_Native.Some b
      | None -> FStar_Pervasives_Native.None in
    (match Parser_JSONLD.parse_jsonld content fs_base FStar_Pervasives_Native.None FStar_Pervasives_Native.None FStar_Pervasives_Native.None with
     | FStar_Pervasives_Native.Some ds -> ds
     | FStar_Pervasives_Native.None ->
       failwith "invalid JSON-LD (parse or unsupported feature — remote contexts need a loader this tool does not have)")
  | _ ->
    let triples = match fmt with
      | NT ->
        if strict then
          (match Parser_NTriples.parse_ntriples_strict content with
           | FStar_Pervasives_Native.Some ts -> ts
           | FStar_Pervasives_Native.None -> failwith "strict N-Triples parse rejected this input")
        else Parser_NTriples.parse_ntriples content
      | Turtle ->
        if strict then
          (match base_iri with
           | Some b ->
             (match Parser_Turtle.parse_turtle_with_base_strict content b with
              | FStar_Pervasives_Native.Some ts -> ts
              | FStar_Pervasives_Native.None -> failwith "strict Turtle parse rejected this input")
           | None ->
             (match Parser_Turtle.parse_turtle_strict content with
              | FStar_Pervasives_Native.Some ts -> ts
              | FStar_Pervasives_Native.None -> failwith "strict Turtle parse rejected this input"))
        else
          (match base_iri with
           | Some b -> Parser_Turtle.parse_turtle_with_base content b
           | None -> Parser_Turtle.parse_turtle content)
      | RDFXML ->
        if strict then
          (match
             (match base_iri with
              | Some b -> Parser_RDFXML.parse_rdfxml_with_base_strict b content
              | None -> Parser_RDFXML.parse_rdfxml_strict content)
           with
           | FStar_Pervasives_Native.Some ts -> ts
           | FStar_Pervasives_Native.None -> failwith "strict RDF/XML parse rejected this input")
        else
        (match base_iri with
         | Some b -> Parser_RDFXML.parse_rdfxml_with_base b content
         | None -> Parser_RDFXML.parse_rdfxml content)
      | _ -> [] in
    RDF_Graph_Executable.({ ds_default = triples; ds_named = [] })

let usage () =
  Printf.eprintf
    "Usage: factoidal-dump-nq [--format nt|turtle|nq|trig|rdfxml|jsonld] [--strict] FILE\n\n\
     Parse RDF with Factoidal's extracted parser stack and emit canonical N-Quads.\n\
     --strict uses the option-returning parser entry points (nt, turtle, nq,\n\
     trig, rdfxml) so a spec-invalid input FAILS instead of silently parsing\n\
     to zero triples — use this when comparing accept/reject verdicts against\n\
     another engine. jsonld has no strict/lenient split (parse_jsonld already\n\
     fails on invalid input), so --strict is a no-op there.\n";
  exit 2

let () =
  let format = ref None in
  let input = ref None in
  let strict = ref false in
  let rec loop = function
    | [] -> ()
    | ["--help"] | ["-h"] -> usage ()
    | "--format" :: fmt :: rest ->
      (match format_of_string fmt with
       | Some f -> format := Some f; loop rest
       | None ->
         Printf.eprintf "Error: unknown format '%s'\n" fmt;
         exit 2)
    | "--strict" :: rest -> strict := true; loop rest
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
    try load_dataset ~format:!format ~strict:!strict path
    with e ->
      Printf.eprintf "Error parsing %s: %s\n" path (Printexc.to_string e);
      exit 1
  in
  print_string (RDF_Canonical.canonical_nquads dataset)
