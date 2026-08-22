(* extension_function_unit.ml -- pins SPARQL 1.1 s17.6 extension
   functions (issue #463,
   https://github.com/danbri/factoidal/issues/463) one layer below the
   npm bridge: plain OCaml closures registered straight into the
   glue-realised registry (experimental_ocaml_glue/
   extension_function_registry.sh), evaluated through the F*-extracted
   engine (SPARQL11_Parser.parse_sparql + eval_select_query).

   What is pinned:

   1. Dispatch order (the F* E_FunctionCall arm): the registry is
      consulted LAST -- a natively-implemented IRI (an xsd: cast)
      never reaches a registered function of the same name.
   2. Unknown IRI = the s17.6 error: FILTER drops the row, BIND
      leaves the variable unbound (ER_Error is value-level in the Tot
      engine).
   3. Custom functions work in FILTER, BIND, and SELECT expressions.
   4. Argument marshaling: the closure sees already-evaluated
      eval_result values (a numeric literal arrives as a promoted
      ER_* or ER_Term -- the test accepts both, mirroring
      anti-pattern #6's promoted-type rule).
   5. A closure returning None is the same s17.6 error as an
      unregistered IRI. *)

let passed = ref 0
let failed = ref 0

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

open RDF_Graph_Executable
open SPARQL11_Algebra

let ex n = "http://example.org/" ^ n
let t s p o : triple = { s; p; o }
let iri_subj i : subject = S_IRI i
let iri_obj i : rdf_term = T_IRI i
let int_lit (n : int) : rdf_term =
  T_Literal { RDF_Term.lexical_form = string_of_int n;
              RDF_Term.datatype = "http://www.w3.org/2001/XMLSchema#integer";
              RDF_Term.lang_tag = FStar_Pervasives_Native.None;
              RDF_Term.direction = FStar_Pervasives_Native.None }
let str_lit (s : string) : rdf_term =
  T_Literal { RDF_Term.lexical_form = s;
              RDF_Term.datatype = "http://www.w3.org/2001/XMLSchema#string";
              RDF_Term.lang_tag = FStar_Pervasives_Native.None;
              RDF_Term.direction = FStar_Pervasives_Native.None }

let graph : rdf_graph = [
  t (iri_subj (ex "alice")) (ex "age") (int_lit 30);
  t (iri_subj (ex "bob"))   (ex "age") (int_lit 7);
]

(* Evaluate a SELECT query text against the fixture graph; None on a
   parse error. *)
let run_query (src : string) : solution_sequence option =
  match SPARQL11_Parser.parse_sparql src with
  | SPARQL11_Parser.ParseOk (q, _) ->
    Some (eval_select_query q graph empty_dataset)
  | SPARQL11_Parser.ParseErr _ -> None

(* Read an eval_result argument as an integer, accepting both the
   promoted ER_Num form and a typed-literal ER_Term (anti-pattern #6:
   handle promoted types alongside ER_Term everywhere). *)
let arg_to_int (r : eval_result) : int option =
  match r with
  | ER_Num z -> Some (Z.to_int z)
  | ER_Term (T_Literal l) -> int_of_string_opt l.RDF_Term.lexical_form
  | _ -> None

let () =
  Printf.printf "-- direct registry dispatch --\n";
  extension_function_clear ();

  check ~name:"unregistered IRI: extension_function_call returns None"
    (extension_function_call (ex "fn/nope") [] = FStar_Pervasives_Native.None);

  extension_function_register (ex "fn/answer")
    (fun _args -> Some (ER_Num (Z.of_int 42)));
  check ~name:"registered IRI: closure result comes back as Some"
    (extension_function_call (ex "fn/answer") [] =
       FStar_Pervasives_Native.Some (ER_Num (Z.of_int 42)));

  extension_function_register (ex "fn/refuse") (fun _args -> None);
  check ~name:"closure returning None surfaces as None (s17.6 error at the arm)"
    (extension_function_call (ex "fn/refuse") [] = FStar_Pervasives_Native.None);

  extension_function_unregister (ex "fn/answer");
  check ~name:"unregister restores None"
    (extension_function_call (ex "fn/answer") [] = FStar_Pervasives_Native.None)

let () =
  Printf.printf "-- end-to-end through parse + eval --\n";
  extension_function_clear ();

  (* fn:isAdult(?a) -- boolean-valued, used in FILTER. *)
  extension_function_register (ex "fn/isAdult")
    (fun args ->
       match args with
       | [a] -> (match arg_to_int a with
                 | Some n -> Some (ER_Bool (n >= 18))
                 | None -> None)
       | _ -> None);

  (* fn:double(?a) -- numeric-valued, used in BIND and SELECT exprs. *)
  extension_function_register (ex "fn/double")
    (fun args ->
       match args with
       | [a] -> (match arg_to_int a with
                 | Some n -> Some (ER_Num (Z.of_int (2 * n)))
                 | None -> None)
       | _ -> None);

  (* (1) FILTER: only alice (30 >= 18) survives. *)
  (match run_query
     ("SELECT ?s WHERE { ?s <http://example.org/age> ?a . " ^
      "FILTER(<http://example.org/fn/isAdult>(?a)) }") with
   | Some omega ->
     check ~name:"(1) FILTER with custom function keeps exactly the adult row"
       (List.length omega = 1
        && List.exists (fun mu -> sm_lookup "s" mu =
             FStar_Pervasives_Native.Some (iri_obj (ex "alice"))) omega)
   | None -> check ~name:"(1) FILTER with custom function keeps exactly the adult row" false);

  (* (2) BIND: both rows get ?d = 2 * age. *)
  (match run_query
     ("SELECT ?s ?d WHERE { ?s <http://example.org/age> ?a . " ^
      "BIND(<http://example.org/fn/double>(?a) AS ?d) }") with
   | Some omega ->
     let d_of subj =
       List.fold_left (fun acc mu ->
         if sm_lookup "s" mu = FStar_Pervasives_Native.Some (iri_obj (ex subj))
         then sm_lookup "d" mu else acc) FStar_Pervasives_Native.None omega in
     let is_sixty = (match d_of "alice" with
       | FStar_Pervasives_Native.Some t2 -> rdf_term_eq t2 (int_lit 60)
       | FStar_Pervasives_Native.None -> false) in
     let is_fourteen = (match d_of "bob" with
       | FStar_Pervasives_Native.Some t2 -> rdf_term_eq t2 (int_lit 14)
       | FStar_Pervasives_Native.None -> false) in
     check ~name:"(2) BIND with custom function computes 2*age per row"
       (List.length omega = 2 && is_sixty && is_fourteen)
   | None -> check ~name:"(2) BIND with custom function computes 2*age per row" false);

  (* (3) SELECT expression: same function in the projection. *)
  (match run_query
     ("SELECT (<http://example.org/fn/double>(?a) AS ?d) " ^
      "WHERE { <http://example.org/alice> <http://example.org/age> ?a }") with
   | Some omega ->
     check ~name:"(3) SELECT expression with custom function projects the value"
       (List.length omega = 1
        && (match sm_lookup "d" (List.hd omega) with
            | FStar_Pervasives_Native.Some t2 -> rdf_term_eq t2 (int_lit 60)
            | FStar_Pervasives_Native.None -> false))
   | None -> check ~name:"(3) SELECT expression with custom function projects the value" false);

  (* (4) Unknown IRI in FILTER: every row dropped. *)
  (match run_query
     ("SELECT ?s WHERE { ?s <http://example.org/age> ?a . " ^
      "FILTER(<http://example.org/fn/noSuchFunction>(?a)) }") with
   | Some omega ->
     check ~name:"(4) unknown IRI in FILTER drops every row" (omega = [])
   | None -> check ~name:"(4) unknown IRI in FILTER drops every row" false);

  (* (5) Unknown IRI in BIND: rows survive, variable unbound. *)
  (match run_query
     ("SELECT ?s ?x WHERE { ?s <http://example.org/age> ?a . " ^
      "BIND(<http://example.org/fn/noSuchFunction>(?a) AS ?x) }") with
   | Some omega ->
     check ~name:"(5) unknown IRI in BIND leaves ?x unbound in both rows"
       (List.length omega = 2
        && List.for_all (fun mu -> sm_lookup "x" mu = FStar_Pervasives_Native.None) omega)
   | None -> check ~name:"(5) unknown IRI in BIND leaves ?x unbound in both rows" false);

  (* (6) Precedence: a registered function under an xsd: cast IRI is
     never consulted -- the native cast wins. *)
  let hijack_called = ref false in
  extension_function_register "http://www.w3.org/2001/XMLSchema#integer"
    (fun _args -> hijack_called := true; Some (ER_Num (Z.of_int 999)));
  (match run_query
     "SELECT (<http://www.w3.org/2001/XMLSchema#integer>(\"41\") AS ?v) WHERE {}" with
   | Some omega ->
     check ~name:"(6) xsd:integer cast keeps precedence over a registered hijack"
       (List.length omega = 1
        && (match sm_lookup "v" (List.hd omega) with
            | FStar_Pervasives_Native.Some t2 -> rdf_term_eq t2 (int_lit 41)
            | FStar_Pervasives_Native.None -> false)
        && not !hijack_called)
   | None -> check ~name:"(6) xsd:integer cast keeps precedence over a registered hijack" false);

  extension_function_clear ()

let () =
  Printf.printf "extension_function_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  exit (if !failed = 0 then 0 else 1)
