(* Smoke test for F*-extracted SPARQL parser *)
let () =
  let test_queries = [
    "SELECT * WHERE { ?s ?p ?o }";
    "PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?name WHERE { ?x foaf:name ?name }";
    "SELECT ?s WHERE { ?s ?p ?o } LIMIT 10";
    "ASK { <http://example.org/a> <http://example.org/b> <http://example.org/c> }";
    "SELECT ?x WHERE { ?x <http://example.org/p> ?y OPTIONAL { ?y <http://example.org/q> ?z } }";
  ] in
  List.iter (fun q ->
    Printf.printf "Query: %s\n" q;
    (match SPARQL11_Parser.parse_sparql q with
     | SPARQL11_Parser.ParseOk (query, remaining) ->
       Printf.printf "  OK! SSE: %s\n" (SPARQL11_Parser.sse_query query);
       Printf.printf "  Remaining tokens: %d\n" (List.length remaining)
     | SPARQL11_Parser.ParseErr msg ->
       Printf.printf "  FAIL: %s\n" msg);
    print_newline ()
  ) test_queries
