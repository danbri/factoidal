(* lateral_service_unit.ml -- pins the LATERAL x SERVICE interaction
   (SPARQL 1.2 track LATERAL, Jena extension,
   https://jena.apache.org/documentation/query/lateral-join.html;
   SPARQL 1.1 federated query, issue #57).

   Why this suite exists: LATERAL's stated design point in this repo is
   that the correlated join works at the group-graph-pattern level of
   abstraction, so the RHS can be ANY pattern -- including SERVICE.
   tests/unit/lateral_unit.ml pins LATERAL itself; nothing pinned the
   SERVICE interplay. This suite does, one layer below the CLI, by
   calling the extracted F* functions directly and registering remote
   endpoint snapshots through the same `service_endpoint_register`
   hook the W3C runner uses for qt:serviceData.

   What is pinned:

   1. `lateral_substitute` reaches INTO SERVICE nodes
      (SPARQL11.Algebra.fst, GP_Service / GP_ServiceVar arms): the
      outer row's bindings rewrite the remote pattern, and a
      GP_ServiceVar whose endpoint variable is bound to an IRI by the
      outer row RESOLVES to GP_Service (correlated endpoint
      selection). Bound-to-literal and unbound endpoints stay
      GP_ServiceVar.

   2. End-to-end evaluation (eval_pattern + the registered-endpoint
      resolver):
      (a) LATERAL { SERVICE <e> { ... } } is correlated per outer row;
      (b) the observable LATERAL-vs-JOIN row-count difference (LIMIT
          inside a SELECT * sub-query) survives crossing a SERVICE
          boundary;
      (c) SILENT semantics inside LATERAL (unregistered endpoint:
          SILENT keeps the outer row unextended, non-SILENT drops it);
      (d) LATERAL *inside* a SERVICE body evaluates against the remote
          snapshot;
      (e) SERVICE ?endpoint under LATERAL dispatches each outer row to
          ITS OWN endpoint (proved with deliberately conflicting data
          on two endpoints).

   3. The same shapes end-to-end through SPARQL11_Parser.parse_sparql
      (query text -> AST -> eval), including the illegal-reassignment
      parse gate firing THROUGH a SERVICE wrapper. *)

let passed = ref 0
let failed = ref 0

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

open RDF_Graph_Executable
open SPARQL11_Algebra

(* ---------------------------------------------------------------- *)
(* Shared builders (mirrors lateral_unit.ml's shape)                  *)
(* ---------------------------------------------------------------- *)

let default_modifier : solution_modifier = {
  sm_order_by = FStar_Pervasives_Native.None;
  sm_distinct = false;
  sm_reduced  = false;
  sm_offset   = FStar_Pervasives_Native.None;
  sm_limit    = FStar_Pervasives_Native.None;
}

let mk_query
    ?(modifier = default_modifier)
    (form : query_form) (pattern : group_graph_pattern) : query =
  { q_base = FStar_Pervasives_Native.None; q_prefixes = []; q_form = form;
    q_dataset = []; q_pattern = pattern;
    q_group_by = FStar_Pervasives_Native.None;
    q_having = FStar_Pervasives_Native.None;
    q_modifier = modifier; q_values = FStar_Pervasives_Native.None }

let ex n = "http://example.org/" ^ n
let t s p o : triple = { s; p; o }
let iri_subj i : subject = S_IRI i
let iri_obj i : rdf_term = T_IRI i
let lit_obj lex : rdf_term =
  T_Literal { RDF_Term.lexical_form = lex;
              RDF_Term.datatype = "http://www.w3.org/2001/XMLSchema#string";
              RDF_Term.lang_tag = FStar_Pervasives_Native.None;
              RDF_Term.direction = FStar_Pervasives_Native.None }

(* Local (query-side) graph: two Persons, NO labels locally. Every
   label in this suite can only come from a SERVICE endpoint, so a
   correlated result is proof the remote hop actually happened. *)
let local_graph : rdf_graph = [
  t (iri_subj (ex "alice")) (ex "type") (iri_obj (ex "Person"));
  t (iri_subj (ex "bob"))   (ex "type") (iri_obj (ex "Person"));
]

let lhs_persons =
  GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "type"); tp_o = PT_IRI (ex "Person") } ]
let label_bgp =
  GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "label"); tp_o = PT_Var "label" } ]

let eval p = eval_pattern FStar_Pervasives_Native.None p local_graph empty_dataset

let row_pairs omega =
  List.sort compare
    (List.map (fun mu -> (sm_lookup "s" mu, sm_lookup "label" mu)) omega)

(* ---------------------------------------------------------------- *)
(* 1. lateral_substitute reaches into SERVICE nodes (AST level)       *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- lateral_substitute through SERVICE nodes --\n";

  let mu1 : solution_mapping = [("s", iri_obj (ex "alice"))] in
  let subst_label_bgp =
    GP_BGP [ { tp_s = PS_IRI (ex "alice"); tp_p = PT_IRI (ex "label"); tp_o = PT_Var "label" } ]
  in

  check ~name:"(a) GP_Service: outer binding rewrites the REMOTE pattern (endpoint + silent preserved)"
    (lateral_substitute mu1 (GP_Service (ex "svc", label_bgp, false))
     = GP_Service (ex "svc", subst_label_bgp, false));

  check ~name:"(b) GP_ServiceVar bound to an IRI resolves to GP_Service with the substituted body"
    (lateral_substitute [("e", iri_obj (ex "svc")); ("s", iri_obj (ex "alice"))]
       (GP_ServiceVar ("e", label_bgp, true))
     = GP_Service (ex "svc", subst_label_bgp, true));

  check ~name:"(c) GP_ServiceVar with an UNBOUND endpoint var stays GP_ServiceVar (body still substituted)"
    (lateral_substitute mu1 (GP_ServiceVar ("e", label_bgp, false))
     = GP_ServiceVar ("e", subst_label_bgp, false));

  check ~name:"(d) GP_ServiceVar bound to a LITERAL stays GP_ServiceVar (not a dispatchable endpoint)"
    (lateral_substitute [("e", lit_obj "not-an-iri"); ("s", iri_obj (ex "alice"))]
       (GP_ServiceVar ("e", label_bgp, false))
     = GP_ServiceVar ("e", subst_label_bgp, false))

(* ---------------------------------------------------------------- *)
(* 2. End-to-end evaluation with registered endpoints                 *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- LATERAL over SERVICE, end-to-end evaluation --\n";
  service_endpoint_clear ();

  (* Remote endpoint: labels live ONLY here. *)
  let remote_labels : rdf_graph = [
    t (iri_subj (ex "alice")) (ex "label") (lit_obj "alice-label");
    t (iri_subj (ex "bob"))   (ex "label") (lit_obj "bob-label");
  ] in
  service_endpoint_register (ex "svc") remote_labels;

  (* (a) LATERAL { SERVICE <svc> { ?s :label ?label } }: each local
     Person row is pushed into the remote pattern -- 2 correlated rows,
     each subject paired with its OWN remote label. *)
  let omega_a = eval (GP_Lateral (lhs_persons, GP_Service (ex "svc", label_bgp, false))) in
  check ~name:"(a) LATERAL { SERVICE }: 2 rows, each subject with its own remote label"
    (row_pairs omega_a =
       [ (FStar_Pervasives_Native.Some (iri_obj (ex "alice")),
          FStar_Pervasives_Native.Some (lit_obj "alice-label"));
         (FStar_Pervasives_Native.Some (iri_obj (ex "bob")),
          FStar_Pervasives_Native.Some (lit_obj "bob-label")) ]);

  (* (b) The observable LATERAL-vs-JOIN difference THROUGH a SERVICE
     boundary: SELECT * + LIMIT 1 inside the remote pattern. Under
     LATERAL the limit applies per outer row (2 rows, both subjects
     present); under a plain join it applies once globally (1 row). *)
  let limit1 = { default_modifier with sm_limit = FStar_Pervasives_Native.Some (Z.of_int 1) } in
  let remote_limited =
    GP_Service (ex "svc",
                GP_SubSelect (mk_query ~modifier:limit1 (QF_Select Select_All) label_bgp),
                false) in
  let omega_lat  = eval (GP_Lateral (lhs_persons, remote_limited)) in
  let omega_join = eval (GP_Join    (lhs_persons, remote_limited)) in
  let subjects omega =
    List.sort_uniq compare (List.map (fun mu -> sm_lookup "s" mu) omega) in
  check ~name:"(b) SELECT * LIMIT 1 remotely: LATERAL gives one row PER subject (2 rows, 2 subjects)"
    (List.length omega_lat = 2 && List.length (subjects omega_lat) = 2);
  check ~name:"(b') same pattern under plain JOIN: LIMIT applies globally (1 row)"
    (List.length omega_join = 1);

  (* (c) SILENT semantics inside LATERAL, unregistered endpoint. *)
  let omega_silent =
    eval (GP_Lateral (lhs_persons, GP_Service (ex "unregistered", label_bgp, true))) in
  check ~name:"(c) SERVICE SILENT to an unregistered endpoint: outer rows survive unextended"
    (List.length omega_silent = 2
     && List.for_all (fun mu -> sm_lookup "label" mu = FStar_Pervasives_Native.None) omega_silent);
  let omega_loud =
    eval (GP_Lateral (lhs_persons, GP_Service (ex "unregistered", label_bgp, false))) in
  check ~name:"(c') non-SILENT to an unregistered endpoint: 0 rows (error sentinel)"
    (omega_loud = []);

  (* (d) LATERAL *inside* a SERVICE body: the whole correlated join
     evaluates against the remote snapshot (which carries both the
     Person typing and the labels; the local graph has no labels, so
     any label row proves remote evaluation). *)
  let remote_full : rdf_graph = [
    t (iri_subj (ex "carol")) (ex "type")  (iri_obj (ex "Person"));
    t (iri_subj (ex "carol")) (ex "label") (lit_obj "carol-label");
  ] in
  service_endpoint_register (ex "svc-full") remote_full;
  let omega_d = eval (GP_Service (ex "svc-full", GP_Lateral (lhs_persons, label_bgp), false)) in
  check ~name:"(d) LATERAL inside SERVICE: evaluated against the remote snapshot (carol found)"
    (row_pairs omega_d =
       [ (FStar_Pervasives_Native.Some (iri_obj (ex "carol")),
          FStar_Pervasives_Native.Some (lit_obj "carol-label")) ]);

  (* (e) Correlated endpoint selection: SERVICE ?endpoint under
     LATERAL. Two endpoints carry deliberately conflicting data; each
     outer row must reach ITS OWN endpoint only. A failure of the
     per-row GP_ServiceVar -> GP_Service resolution would surface the
     cross-endpoint labels. *)
  let svc_a = ex "svcA" and svc_b = ex "svcB" in
  service_endpoint_register svc_a [
    t (iri_subj (ex "alice")) (ex "label") (lit_obj "alice-from-A");
    t (iri_subj (ex "bob"))   (ex "label") (lit_obj "bob-from-A-WRONG");
  ];
  service_endpoint_register svc_b [
    t (iri_subj (ex "bob"))   (ex "label") (lit_obj "bob-from-B");
    t (iri_subj (ex "alice")) (ex "label") (lit_obj "alice-from-B-WRONG");
  ];
  let some x = FStar_Pervasives_Native.Some x in
  let lhs_values =
    GP_Values (["s"; "e"],
               [ [some (iri_obj (ex "alice")); some (iri_obj svc_a)];
                 [some (iri_obj (ex "bob"));   some (iri_obj svc_b)] ]) in
  let omega_e = eval (GP_Lateral (lhs_values, GP_ServiceVar ("e", label_bgp, false))) in
  check ~name:"(e) SERVICE ?endpoint under LATERAL: each row dispatched to its OWN endpoint"
    (row_pairs omega_e =
       [ (FStar_Pervasives_Native.Some (iri_obj (ex "alice")),
          FStar_Pervasives_Native.Some (lit_obj "alice-from-A"));
         (FStar_Pervasives_Native.Some (iri_obj (ex "bob")),
          FStar_Pervasives_Native.Some (lit_obj "bob-from-B")) ]);

  (* (e') Control: an UNBOUND endpoint var under LATERAL cannot
     dispatch -- non-SILENT drops every row, SILENT keeps them
     unextended (mirrors the GP_ServiceVar standalone-arm semantics). *)
  let omega_unbound = eval (GP_Lateral (lhs_persons, GP_ServiceVar ("e", label_bgp, false))) in
  check ~name:"(e') unbound SERVICE ?endpoint under LATERAL, non-SILENT: 0 rows"
    (omega_unbound = []);
  let omega_unbound_s = eval (GP_Lateral (lhs_persons, GP_ServiceVar ("e", label_bgp, true))) in
  check ~name:"(e'') unbound SERVICE ?endpoint under LATERAL, SILENT: outer rows survive unextended"
    (List.length omega_unbound_s = 2
     && List.for_all (fun mu -> sm_lookup "label" mu = FStar_Pervasives_Native.None) omega_unbound_s)

(* ---------------------------------------------------------------- *)
(* 3. Same shapes end-to-end through the parser                       *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- parser end-to-end (query text -> AST -> eval) --\n";

  let contains haystack needle =
    let lh = String.length haystack and ln = String.length needle in
    let rec scan i = i + ln <= lh && (String.sub haystack i ln = needle || scan (i + 1)) in
    scan 0
  in
  let parse_eval src =
    match SPARQL11_Parser.parse_sparql src with
    | SPARQL11_Parser.ParseOk (q, _) ->
      Some (eval_select_query q local_graph empty_dataset)
    | SPARQL11_Parser.ParseErr _ -> None
  in

  (* (a) LATERAL { SERVICE <svc> { ... } } from concrete syntax.
     Endpoints registered in section 2 are still live. *)
  let src_lat_svc =
    "SELECT ?s ?label WHERE {\n\
     \  ?s <http://example.org/type> <http://example.org/Person> .\n\
     \  LATERAL { SERVICE <http://example.org/svc> { ?s <http://example.org/label> ?label } }\n\
     }" in
  (match parse_eval src_lat_svc with
   | Some omega ->
     check ~name:"(a) parsed LATERAL { SERVICE }: 2 correlated rows"
       (row_pairs omega =
          [ (FStar_Pervasives_Native.Some (iri_obj (ex "alice")),
             FStar_Pervasives_Native.Some (lit_obj "alice-label"));
            (FStar_Pervasives_Native.Some (iri_obj (ex "bob")),
             FStar_Pervasives_Native.Some (lit_obj "bob-label")) ])
   | None -> check ~name:"(a) parsed LATERAL { SERVICE }: 2 correlated rows" false);

  (* (b) SERVICE <svc-full> { ... LATERAL { ... } } from concrete
     syntax: LATERAL accepted inside a SERVICE body and evaluated
     against the remote snapshot. *)
  let src_svc_lat =
    "SELECT ?s ?label WHERE {\n\
     \  SERVICE <http://example.org/svc-full> {\n\
     \    ?s <http://example.org/type> <http://example.org/Person> .\n\
     \    LATERAL { ?s <http://example.org/label> ?label }\n\
     \  }\n\
     }" in
  (match parse_eval src_svc_lat with
   | Some omega ->
     check ~name:"(b) parsed SERVICE { ... LATERAL }: evaluated remotely (carol found)"
       (row_pairs omega =
          [ (FStar_Pervasives_Native.Some (iri_obj (ex "carol")),
             FStar_Pervasives_Native.Some (lit_obj "carol-label")) ])
   | None -> check ~name:"(b) parsed SERVICE { ... LATERAL }: evaluated remotely (carol found)" false);

  (* (c) The illegal-reassignment gate fires THROUGH a SERVICE wrapper:
     lateral_assignable_vars passes through GP_Service, so a BIND on an
     LHS-bound var inside the remote body is still rejected at parse
     time. *)
  let src_illegal =
    "SELECT * WHERE {\n\
     \  ?s <http://example.org/type> <http://example.org/Person> .\n\
     \  LATERAL { SERVICE <http://example.org/svc> { BIND(1 AS ?s) } }\n\
     }" in
  check ~name:"(c) BIND reassignment inside SERVICE inside LATERAL is rejected at parse time"
    (match SPARQL11_Parser.parse_sparql src_illegal with
     | SPARQL11_Parser.ParseErr m ->
       contains m "reassigns a variable already bound by the left-hand pattern"
     | SPARQL11_Parser.ParseOk _ -> false);

  service_endpoint_clear ()

let () =
  Printf.printf "lateral_service_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  exit (if !failed = 0 then 0 else 1)
