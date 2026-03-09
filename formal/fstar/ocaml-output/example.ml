(* Example: Using extracted F* RDF/SPARQL modules to build and query a graph *)

open RDF_Graph_Executable
open SPARQL11_Algebra

(* Helper to create a simple IRI term *)
let iri s = T_IRI s

(* Helper to create a simple string literal *)
let str_lit s =
  T_Literal {
    lexical_form = s;
    datatype = "http://www.w3.org/2001/XMLSchema#string";
    lang_tag = None;
  }

(* Helper to create an integer literal *)
let int_lit n =
  T_Literal {
    lexical_form = string_of_int n;
    datatype = "http://www.w3.org/2001/XMLSchema#integer";
    lang_tag = None;
  }

(* Helper to make a triple *)
let make_triple s p o : triple =
  { s = S_IRI s; p = p; o = o }

(* Print an rdf_term *)
let term_to_string (t : rdf_term) : string =
  match t with
  | T_IRI i -> Printf.sprintf "<%s>" i
  | T_BNode b -> Printf.sprintf "_:%s" b
  | T_Literal l ->
    (match l.lang_tag with
     | Some lang -> Printf.sprintf "\"%s\"@%s" l.lexical_form lang
     | None ->
       if l.datatype = xsd_string then
         Printf.sprintf "\"%s\"" l.lexical_form
       else
         Printf.sprintf "\"%s\"^^<%s>" l.lexical_form l.datatype)

let subject_to_string (s : subject) : string =
  match s with
  | S_IRI i -> Printf.sprintf "<%s>" i
  | S_BNode b -> Printf.sprintf "_:%s" b

(* Print a triple *)
let print_triple (t : triple) =
  Printf.printf "  %s %s %s .\n"
    (subject_to_string t.s)
    (Printf.sprintf "<%s>" t.p)
    (term_to_string t.o)

(* Print solution mappings *)
let print_solutions (vars : string list) (solutions : solution_sequence) =
  (* Print header *)
  List.iter (fun v -> Printf.printf "%-30s" ("?" ^ v)) vars;
  print_newline ();
  List.iter (fun _ -> Printf.printf "%-30s" "---") vars;
  print_newline ();
  (* Print each solution *)
  List.iter (fun (mu : solution_mapping) ->
    List.iter (fun v ->
      let value = List.assoc_opt v mu in
      let s = match value with
        | Some t -> term_to_string t
        | None -> "(unbound)"
      in
      Printf.printf "%-30s" s
    ) vars;
    print_newline ()
  ) solutions

let () =
  Printf.printf "=== Factoidal: F*-extracted RDF/SPARQL Example ===\n\n";

  (* Define some IRIs *)
  let ex = "http://example.org/" in
  let foaf = "http://xmlns.com/foaf/0.1/" in
  let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in

  (* Build an RDF graph about people *)
  let g = empty_graph in
  let g = graph_add (make_triple (ex ^ "alice") rdf_type (iri (foaf ^ "Person"))) g in
  let g = graph_add (make_triple (ex ^ "bob") rdf_type (iri (foaf ^ "Person"))) g in
  let g = graph_add (make_triple (ex ^ "charlie") rdf_type (iri (foaf ^ "Person"))) g in
  let g = graph_add (make_triple (ex ^ "alice") (foaf ^ "name") (str_lit "Alice")) g in
  let g = graph_add (make_triple (ex ^ "bob") (foaf ^ "name") (str_lit "Bob")) g in
  let g = graph_add (make_triple (ex ^ "charlie") (foaf ^ "name") (str_lit "Charlie")) g in
  let g = graph_add (make_triple (ex ^ "alice") (foaf ^ "knows") (iri (ex ^ "bob"))) g in
  let g = graph_add (make_triple (ex ^ "alice") (foaf ^ "knows") (iri (ex ^ "charlie"))) g in
  let g = graph_add (make_triple (ex ^ "bob") (foaf ^ "knows") (iri (ex ^ "alice"))) g in
  let g = graph_add (make_triple (ex ^ "alice") (foaf ^ "age") (int_lit 30)) g in
  let g = graph_add (make_triple (ex ^ "bob") (foaf ^ "age") (int_lit 25)) g in
  let g = graph_add (make_triple (ex ^ "charlie") (foaf ^ "age") (int_lit 35)) g in

  Printf.printf "Graph (%d triples):\n" (Z.to_int (graph_len g));
  List.iter print_triple g;

  (* Query 1: Find all people (BGP query) *)
  Printf.printf "\n--- Query 1: SELECT ?person WHERE { ?person rdf:type foaf:Person } ---\n\n";
  let bgp1 = [
    { tp_s = PS_Var "person";
      tp_p = PT_IRI rdf_type;
      tp_o = PT_IRI (foaf ^ "Person") }
  ] in
  let pattern1 = GP_BGP bgp1 in
  let ds = empty_dataset in
  let results1 = eval_pattern pattern1 g ds in
  print_solutions ["person"] results1;

  (* Query 2: Find names of people Alice knows *)
  Printf.printf "\n--- Query 2: SELECT ?name WHERE { ex:alice foaf:knows ?friend . ?friend foaf:name ?name } ---\n\n";
  let bgp2a = [
    { tp_s = PS_IRI (ex ^ "alice");
      tp_p = PT_IRI (foaf ^ "knows");
      tp_o = PT_Var "friend" }
  ] in
  let bgp2b = [
    { tp_s = PS_Var "friend";
      tp_p = PT_IRI (foaf ^ "name");
      tp_o = PT_Var "name" }
  ] in
  let pattern2 = GP_Join (GP_BGP bgp2a, GP_BGP bgp2b) in
  let results2 = eval_pattern pattern2 g ds in
  print_solutions ["friend"; "name"] results2;

  (* Query 3: Full SELECT query with DISTINCT *)
  Printf.printf "\n--- Query 3: SELECT DISTINCT ?person ?name WHERE { ?person foaf:name ?name } ---\n\n";
  let bgp3 = [
    { tp_s = PS_Var "person";
      tp_p = PT_IRI (foaf ^ "name");
      tp_o = PT_Var "name" }
  ] in
  let q3 : query = {
    q_base = None;
    q_prefixes = [];
    q_form = QF_Select (Select_Vars [SI_Var "person"; SI_Var "name"]);
    q_dataset = [];
    q_pattern = GP_BGP bgp3;
    q_group_by = None;
    q_having = None;
    q_values = None;
    q_modifier = {
      sm_order_by = None;
      sm_distinct = true;
      sm_reduced = false;
      sm_offset = None;
      sm_limit = None;
    };
  } in
  let results3 = eval_select_query q3 g ds in
  print_solutions ["person"; "name"] results3;

  (* Query 4: Find people by subject lookup *)
  Printf.printf "\n--- RDF API: find_by_subject ex:alice ---\n\n";
  let alice_triples = find_by_subject (ex ^ "alice") g in
  List.iter print_triple alice_triples;

  (* Query 5: Graph union *)
  Printf.printf "\n--- RDF API: graph_union with new data ---\n\n";
  let g2 = empty_graph in
  let g2 = graph_add (make_triple (ex ^ "dave") rdf_type (iri (foaf ^ "Person"))) g2 in
  let g2 = graph_add (make_triple (ex ^ "dave") (foaf ^ "name") (str_lit "Dave")) g2 in
  let merged = graph_union g g2 in
  Printf.printf "Original: %d triples, Extra: %d triples, Merged: %d triples\n"
    (Z.to_int (graph_len g)) (Z.to_int (graph_len g2)) (Z.to_int (graph_len merged));

  Printf.printf "\n=== Done! ===\n"
