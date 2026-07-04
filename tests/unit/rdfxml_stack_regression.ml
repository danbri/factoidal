(* rdfxml_stack_regression.ml — issue #273 regression.

   Parser.XML.parse_children and Parser.RDFXML.process_node_elements /
   process_property_children used to build their result lists via
   `x :: (recurse ...)` AFTER the recursive call returned — non-tail,
   one native stack frame per sibling element. A flat RDF/XML document
   (many <rdf:Description> elements as direct siblings of <rdf:RDF>,
   exactly the shape tools/bench-parse-serialize.sh's fixture and the
   W3C stress case both use) hit this directly: `factoidal count
   FILE.rdf` crashed with "Stack overflow" above roughly 10k triples
   while N-Triples/Turtle on the same triple count parsed fine (those
   parsers are already accumulator-based).

   2026-07-04 fix: both walks now thread an accumulator and reverse
   once at the end (List.Tot.rev / List.Tot.rev_acc), same shape as
   RDF.Canonical's dedup_qquads_acc. This test pins two things beyond
   what tools/bench-parse-serialize.sh's size-scaling already covers:
     1. A document past the crash threshold (50,000 triples, ~5x the
        ~10k that used to overflow) parses without crashing or hanging.
     2. The triple count and document ORDER survive the accumulator
        rewrite — reversing an accumulator is exactly the kind of
        change that silently reverses output order if got wrong. *)

let n = 50000

(* Cap at 60s: a correct tail-recursive parse of 50k trivial triples
   should take well under a second; this only guards against a
   reintroduced hang or a Stack_overflow that isn't caught cleanly.
   Per CLAUDE.md anti-pattern #17, no ad-hoc parse run is allowed to
   hang unbounded. *)
let with_cap seconds f =
  let triggered = ref false in
  let prev =
    Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> triggered := true; raise Exit))
  in
  let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = seconds } in
  let restore () =
    let _ = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.0; it_value = 0.0 } in
    Sys.set_signal Sys.sigalrm prev
  in
  let r =
    try
      let v = f () in
      restore ();
      Some v
    with
    | Exit -> restore (); None
    | Stack_overflow -> restore (); None
    | e -> restore (); raise e
  in
  if !triggered then None else r

(* Mirrors tools/bench-parse-serialize.sh's RDF/XML fixture generator
   exactly: one <rdf:Description> per triple, one <ex:p rdf:resource>
   child each, all as direct siblings of <rdf:RDF>. *)
let build_fixture n =
  let buf = Buffer.create (n * 90) in
  Buffer.add_string buf "<?xml version=\"1.0\"?>\n";
  Buffer.add_string buf
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:ex=\"http://example.org/\">\n";
  for i = 0 to n - 1 do
    Buffer.add_string buf
      (Printf.sprintf "  <rdf:Description rdf:about=\"http://example.org/s%d\">\n" i);
    Buffer.add_string buf
      (Printf.sprintf "    <ex:p rdf:resource=\"http://example.org/o%d\"/>\n" i);
    Buffer.add_string buf "  </rdf:Description>\n"
  done;
  Buffer.add_string buf "</rdf:RDF>\n";
  Buffer.contents buf

let passed = ref 0
let failed = ref 0

let check ~name cond msg =
  if cond then begin
    incr passed;
    Printf.printf "  PASS  %s\n%!" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: %s\n%!" name msg
  end

let subject_is_iri (expect : string) (s : RDF_Graph_Executable.subject) : bool =
  let open RDF_Graph_Executable in
  match s with
  | S_IRI i -> i = expect
  | S_BNode _ -> false

let () =
  let doc = build_fixture n in
  Printf.printf "rdfxml_stack_regression: generated %d-triple fixture (%d bytes)\n%!"
    n (String.length doc);
  let t0 = Unix.gettimeofday () in
  match with_cap 60.0 (fun () ->
    Parser_RDFXML.parse_rdfxml_with_base "file:///bench.rdf" doc)
  with
  | None ->
    incr failed;
    Printf.printf
      "  FAIL  parse did not complete within 60s (stack overflow or hang)\n%!"
  | Some triples ->
    let dt = Unix.gettimeofday () -. t0 in
    Printf.printf "  parsed %d triples in %.3fs\n%!" (List.length triples) dt;
    check ~name:"triple count"
      (List.length triples = n)
      (Printf.sprintf "expected %d triples, got %d" n (List.length triples));
    (match triples with
     | first :: _ ->
       check ~name:"first triple subject is s0"
         (subject_is_iri "http://example.org/s0" first.RDF_Graph_Executable.s)
         "expected the first triple's subject to be http://example.org/s0"
     | [] ->
       check ~name:"first triple subject is s0" false "no triples parsed");
    (match List.rev triples with
     | last :: _ ->
       let expect_s = Printf.sprintf "http://example.org/s%d" (n - 1) in
       check ~name:"last triple subject is s(n-1)"
         (subject_is_iri expect_s last.RDF_Graph_Executable.s)
         (Printf.sprintf "expected the last triple's subject to be %s" expect_s)
     | [] ->
       check ~name:"last triple subject is s(n-1)" false "no triples parsed")
  ;
  Printf.printf "rdfxml_stack_regression: %d pass, %d fail (out of %d)\n%!"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
