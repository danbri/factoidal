(* tests/local/rml_virtual_pushdown_probe.ml -- throwaway test glue
   (not registered in build-ocaml.sh; same ad-hoc-harness-compiled-by-
   its-own-shell-script convention as tests/local/delta_log_crash_
   harness.sh's probe.ml) proving RML.VirtualSource.fst's row-level
   pushdown actually inspects fewer rows for a bound query than for
   an unbound scan, on RMLTC0012b-JSON specifically (two TriplesMaps,
   each over its OWN JSON source file, distinct constant predicates
   foaf:name / ex:city, template-shaped BlankNode subjects -- see
   tests/local/virtual_rml_stage5.sh's own banner for why this
   fixture exercises every pushdown dimension in one small mapping).

   Every function this calls (RML_Mapping.decode_mapping_document,
   RML_VirtualSource.rml_solve_trace) is Tot -- the row counts below
   are deterministic values computed once, not runtime side-effect
   instrumentation.

   Usage: rml_virtual_pushdown_probe <fixture-dir> *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "usage: rml_virtual_pushdown_probe <fixture-dir>\n"; exit 2
  end;
  let fixture_dir = Sys.argv.(1) in
  let mapping_ttl = read_file (Filename.concat fixture_dir "mapping.ttl") in
  let g = Parser_Turtle.parse_turtle mapping_ttl in
  let doc = RML_Mapping.decode_mapping_document g in
  let json_source name =
    let content = read_file (Filename.concat fixture_dir name) in
    match Parser_JSON.parse_json content with
    | FStar_Pervasives_Native.Some root -> root
    | FStar_Pervasives_Native.None -> failwith (Printf.sprintf "could not parse %s" name)
  in
  let persons_root = json_source "persons.json" in
  let lives_root = json_source "lives.json" in
  (* tm_id -> source data, matched by which JSON file each TriplesMap's
     own rml:source names (read off the decoded logical source, not
     hardcoded by TriplesMap position -- robust to fixture edits). *)
  let source_for (tmap : RML_Mapping.triples_map) =
    match tmap.RML_Mapping.tm_logical_source with
    | FStar_Pervasives_Native.None -> None
    | FStar_Pervasives_Native.Some ls ->
      (match ls.RML_Mapping.ls_source_path with
       | FStar_Pervasives_Native.Some "persons.json" ->
         Some (tmap.RML_Mapping.tm_id, RML_VirtualSource.RSD_Json persons_root)
       | FStar_Pervasives_Native.Some "lives.json" ->
         Some (tmap.RML_Mapping.tm_id, RML_VirtualSource.RSD_Json lives_root)
       | _ -> None)
  in
  let sources = List.filter_map source_for doc.RML_Mapping.md_triples_maps in
  let n_maps = List.length doc.RML_Mapping.md_triples_maps in
  (* rml_solve_trace returns row counts as Prims.nat, which extracts to
     Z.t -- convert to OCaml int for printing/summing. *)
  let print_trace label b =
    Printf.printf "%s:\n" label;
    let trace = RML_VirtualSource.rml_solve_trace doc sources FStar_Pervasives_Native.None b in
    List.iter (fun (tm_id, n) -> Printf.printf "  %s rows_considered=%d\n" tm_id (Z.to_int n)) trace;
    let total = List.fold_left (fun acc (_, n) -> acc + Z.to_int n) 0 trace in
    Printf.printf "  TOTAL rows_considered=%d candidate_maps=%d out_of=%d\n"
      total (List.length trace) n_maps
  in
  let unbound =
    SPARQL11_Algebra.({ bs = FStar_Pervasives_Native.None;
                         bp = FStar_Pervasives_Native.None;
                         bo = FStar_Pervasives_Native.None }) in
  let bp_city =
    SPARQL11_Algebra.({ bs = FStar_Pervasives_Native.None;
                         bp = FStar_Pervasives_Native.Some "http://example.com/city";
                         bo = FStar_Pervasives_Native.None }) in
  let bp_city_bs_bob =
    SPARQL11_Algebra.({ bs = FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_BNode "BobSmith");
                         bp = FStar_Pervasives_Native.Some "http://example.com/city";
                         bo = FStar_Pervasives_Native.None }) in
  print_trace "UNBOUND (?s ?p ?o)" unbound;
  print_trace "BOUND bp=<http://example.com/city>" bp_city;
  print_trace "BOUND bp=<http://example.com/city> AND bs=_:BobSmith" bp_city_bs_bob
