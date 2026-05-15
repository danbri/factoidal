(* rdfxml_profile_repro.ml — minimal direct repro of the owl_runner
   stall (#263). Calls Parser_XML.parse_xml_document on profile-RL.rdf
   under a SIGALRM cap. *)

let path = "third_party/testing/owl/profile-RL.rdf"
let cap_seconds = 10.0

let pass = ref 0
let xfail = ref 0

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.unsafe_to_string s

let with_cap seconds f =
  let triggered = ref false in
  let prev =
    Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> triggered := true; raise Exit))
  in
  let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = seconds } in
  let r =
    try
      let v = f () in
      let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = 0.0 } in
      Some v
    with
    | Exit -> None
    | e ->
      let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = 0.0 } in
      Sys.set_signal Sys.sigalrm prev;
      raise e
  in
  Sys.set_signal Sys.sigalrm prev;
  if !triggered then None else r

(* Strip the DOCTYPE between <!DOCTYPE and ]>. Plain OCaml. *)
let strip_doctype (s : string) : string =
  let open_re = Str.regexp_string "<!DOCTYPE" in
  let close_re = Str.regexp_string "]>" in
  try
    let i = Str.search_forward open_re s 0 in
    let j = Str.search_forward close_re s i in
    let before = String.sub s 0 i in
    let after = String.sub s (j + 2) (String.length s - (j + 2)) in
    before ^ after
  with Not_found -> s

let catalog_entities = [
  "&rdf;",  "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
  "&rdfs;", "http://www.w3.org/2000/01/rdf-schema#";
  "&owl;",  "http://www.w3.org/2002/07/owl#";
  "&xsd;",  "http://www.w3.org/2001/XMLSchema#";
  "&test;", "http://www.w3.org/2007/OWL/testOntology#";
]

let expand_catalog_entities (s : string) : string =
  List.fold_left
    (fun acc (ent, repl) ->
       Str.global_replace (Str.regexp_string ent) repl acc)
    s catalog_entities

let () =
  let s = read_file path in
  Printf.printf "Loaded %s (%d bytes)\n%!" path (String.length s);

  (* Step A: strip DOCTYPE. *)
  Printf.printf "\nStep A: strip DOCTYPE\n%!";
  let t0 = Unix.gettimeofday () in
  let stripped = strip_doctype s in
  Printf.printf "  stripped to %d bytes in %.3fs\n%!"
    (String.length stripped) (Unix.gettimeofday () -. t0);

  (* Step B: expand entities. *)
  Printf.printf "\nStep B: expand catalog entities (Str.global_replace x 5)\n%!";
  let t1 = Unix.gettimeofday () in
  let expanded = expand_catalog_entities stripped in
  Printf.printf "  expanded to %d bytes in %.3fs\n%!"
    (String.length expanded) (Unix.gettimeofday () -. t1);

  (* Step C: parse via Parser_XML (low-level XML). *)
  Printf.printf "\nStep C: Parser_XML.parse_xml_document on expanded\n%!";
  let t2 = Unix.gettimeofday () in
  (match with_cap cap_seconds (fun () -> Parser_XML.parse_xml_document expanded) with
   | Some (Some _) ->
     Printf.printf "  PASS  parsed (%.3fs)\n%!" (Unix.gettimeofday () -. t2);
     incr pass
   | Some None ->
     Printf.printf "  PASS  None returned (%.3fs)\n%!" (Unix.gettimeofday () -. t2);
     incr pass
   | None ->
     Printf.printf "  XFAIL did not return in %.0fs\n%!" cap_seconds;
     incr xfail);

  (* Step D: parse via Parser_RDFXML.parse_rdfxml_with_base (full path). *)
  Printf.printf "\nStep D: Parser_RDFXML.parse_rdfxml_with_base on expanded\n%!";
  let t3 = Unix.gettimeofday () in
  (match with_cap cap_seconds (fun () ->
    Parser_RDFXML.parse_rdfxml_with_base "file:///profile-RL.rdf" expanded)
  with
   | Some triples ->
     Printf.printf "  PASS  %d triples (%.3fs)\n%!"
       (List.length triples) (Unix.gettimeofday () -. t3);
     incr pass
   | None ->
     Printf.printf "  XFAIL did not return in %.0fs\n%!" cap_seconds;
     incr xfail);

  Printf.printf "\nsummary: %d pass, %d expected-fail\n" !pass !xfail;
  exit 0
