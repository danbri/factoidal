(* lateral_unit.ml -- pins LATERAL (SPARQL 1.2 track / Jena extension,
   https://jena.apache.org/documentation/query/lateral-join.html), added
   this session in formal/fstar/SPARQL11.Algebra.fst (GP_Lateral eval
   arm + lateral_substitute/lateral_assignable_vars/
   lateral_subselect_visible_vars, "LATERAL join" section) and gated at
   parse time in formal/fstar/SPARQL11.Parser.fst (the
   ggp_has_var/lateral_assignable_vars reassignment check, Tok_LATERAL
   arm). tests/local/lateral_joins.sh + tests/local/sparql/lateral_*.rq
   already exercise the full CLI end-to-end; this suite pins the same
   scenarios one layer down, calling the extracted F* functions
   directly with hand-built ASTs/graphs (no process spawn, no I/O).

   Four things are pinned:

   1. `lateral_substitute` -- LHS-row substitution into a BGP's triple
      patterns (subject/predicate/object positions), left untouched
      through FILTER/BIND expression trees (only the nested pattern is
      recursed into), and the GP_SubSelect masking/shadowing rule.

   2. `lateral_assignable_vars` -- which names a pattern could
      REASSIGN at its own top level: BIND's target var, VALUES' vars,
      and a sub-SELECT's "AS"-aliased (SI_Expr) projection items --
      but NOT a plain SI_Var pass-through projection, matching the
      Jena-confirmed asymmetry documented in the .fst banner.

   3. `lateral_subselect_visible_vars` -- Select_Vars projects exactly
      its listed names, Select_All exposes everything (None = no
      restriction), non-SELECT forms expose nothing.

   4. The illegal-reassignment DETECTION itself
      (`ggp_has_var v acc && List.mem v (lateral_assignable_vars rhs)`,
      SPARQL11.Parser.fst's Tok_LATERAL arm) at both the raw-primitive
      level and end-to-end via SPARQL11_Parser.parse_sparql on the same
      query text as tests/local/sparql/lateral_illegal_*.rq /
      lateral_plain_bgp.rq / lateral_subselect_masking.rq.

   Plus a small end-to-end correlated evaluation over a hand-built
   in-memory graph (`SPARQL11_Algebra.eval_pattern`) reproducing the
   module's own "SELECT ?label" (masked, uncorrelated) vs "SELECT *"
   (visible, correlated) contrast from the .fst banner and from
   lateral_subselect_masking.rq / lateral_plain_bgp.rq. *)

let passed = ref 0
let failed = ref 0

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

open RDF_Graph_Executable
open SPARQL11_Algebra

(* ---------------------------------------------------------------- *)
(* Shared builders (mirrors streamable_fastpath_unit.ml's shape)      *)
(* ---------------------------------------------------------------- *)

let default_modifier : solution_modifier = {
  sm_order_by = FStar_Pervasives_Native.None;
  sm_distinct = false;
  sm_reduced  = false;
  sm_offset   = FStar_Pervasives_Native.None;
  sm_limit    = FStar_Pervasives_Native.None;
}

let mk_query
    ?(group_by = FStar_Pervasives_Native.None)
    ?(having   = FStar_Pervasives_Native.None)
    ?(modifier = default_modifier)
    ?(values   = FStar_Pervasives_Native.None)
    (form : query_form) (pattern : group_graph_pattern) : query =
  { q_base = FStar_Pervasives_Native.None; q_prefixes = []; q_form = form;
    q_dataset = []; q_pattern = pattern; q_group_by = group_by;
    q_having = having; q_modifier = modifier; q_values = values }

let ex n = "http://example.org/" ^ n
let t s p o : triple = { s; p; o }
let iri_subj i : subject = S_IRI i
let iri_obj i : rdf_term = T_IRI i
let lit_obj lex : rdf_term =
  T_Literal { RDF_Term.lexical_form = lex;
              RDF_Term.datatype = "http://www.w3.org/2001/XMLSchema#string";
              RDF_Term.lang_tag = FStar_Pervasives_Native.None }

(* ---------------------------------------------------------------- *)
(* 1. lateral_substitute                                              *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- lateral_substitute --\n";

  let mu1 : solution_mapping = [("s", iri_obj (ex "alice"))] in

  (* (a) BGP substitution: ?s in subject position becomes the constant,
     unrelated variables (?label) are left alone. *)
  let rhs_bgp = GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "label"); tp_o = PT_Var "label" } ] in
  let expect_bgp =
    GP_BGP [ { tp_s = PS_IRI (ex "alice"); tp_p = PT_IRI (ex "label"); tp_o = PT_Var "label" } ]
  in
  check ~name:"(a) BGP: bound ?s -> constant subject, ?label untouched"
    (lateral_substitute mu1 rhs_bgp = expect_bgp);

  (* (b) A variable NOT in mu is left as a pattern variable everywhere. *)
  let mu_empty : solution_mapping = [] in
  check ~name:"(b) empty mu: BGP substitution is a no-op"
    (lateral_substitute mu_empty rhs_bgp = rhs_bgp);

  (* (c) FILTER/BIND: the nested pattern is substituted, but the
     expr tree carried by FILTER/BIND itself is NOT rewritten (per the
     .fst banner -- expression-level variable resolution happens later,
     during eval_pattern_store's own evaluation of the substituted
     pattern, not via textual substitution here). *)
  let filter_expr = E_Compare (CmpEq, E_Var "s", E_IRI (ex "alice")) in
  let rhs_filter = GP_Filter (filter_expr, rhs_bgp) in
  check ~name:"(c) FILTER: expr untouched, nested pattern substituted"
    (lateral_substitute mu1 rhs_filter = GP_Filter (filter_expr, expect_bgp));

  let bind_expr = E_NumericLit (Z.of_int 1) in
  let rhs_bind = GP_Bind (bind_expr, "y", rhs_bgp) in
  check ~name:"(d) BIND: expr untouched, target var untouched, nested pattern substituted"
    (lateral_substitute mu1 rhs_bind = GP_Bind (bind_expr, "y", expect_bgp));

  (* (e) GP_Lateral nests recursively on BOTH sides. *)
  let rhs_nested_lateral = GP_Lateral (rhs_bgp, rhs_bgp) in
  check ~name:"(e) nested GP_Lateral: substitution recurses into both sides"
    (lateral_substitute mu1 rhs_nested_lateral = GP_Lateral (expect_bgp, expect_bgp));

  (* (f) GP_SubSelect masking: Select_Vars ["label"] does NOT expose
     ?s, so mu1's ("s", ...) binding is filtered out (mu_visible = [])
     before recursing -- the inner BGP is left UNSUBSTITUTED even
     though mu1 has a binding for "s". *)
  let inner_q_select_label =
    mk_query (QF_Select (Select_Vars [SI_Var "label"])) rhs_bgp
  in
  check ~name:"(f) sub-SELECT projecting only ?label: outer ?s is masked, inner BGP unsubstituted"
    (lateral_substitute mu1 (GP_SubSelect inner_q_select_label)
     = GP_SubSelect { inner_q_select_label with q_pattern = rhs_bgp });

  (* (g) GP_SubSelect Select_All: exposes everything (no restriction),
     so mu1's ?s DOES reach the inner pattern. *)
  let inner_q_select_all = mk_query (QF_Select Select_All) rhs_bgp in
  check ~name:"(g) sub-SELECT * : outer ?s is visible, inner BGP IS substituted"
    (lateral_substitute mu1 (GP_SubSelect inner_q_select_all)
     = GP_SubSelect { inner_q_select_all with q_pattern = expect_bgp });

  (* (h) GP_SubSelect shadowing: if the inner query itself reassigns
     "s" (e.g. `SELECT * { BIND(1 AS ?s) ?s :label ?label }`), that
     name is a fresh, deeper-scoped variable -- dropped from mu before
     recursing, so the reassigning BIND's own nested pattern does NOT
     get the outer substitution for "s" either. *)
  let reassigning_inner_pattern = GP_Join (GP_Bind (E_NumericLit (Z.of_int 99), "s", GP_Empty), rhs_bgp) in
  let inner_q_reassigns = mk_query (QF_Select Select_All) reassigning_inner_pattern in
  let expect_shadowed_result =
    GP_SubSelect
      { inner_q_reassigns with
        q_pattern =
          GP_Join (GP_Bind (E_NumericLit (Z.of_int 99), "s", GP_Empty), rhs_bgp) (* "s" NOT substituted: shadowed *) }
  in
  check ~name:"(h) sub-SELECT that reassigns ?s: outer ?s is shadowed from that subtree"
    (lateral_substitute mu1 (GP_SubSelect inner_q_reassigns) = expect_shadowed_result)

(* ---------------------------------------------------------------- *)
(* 2. lateral_assignable_vars                                         *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- lateral_assignable_vars --\n";

  check ~name:"GP_Bind contributes its target var"
    (lateral_assignable_vars (GP_Bind (E_NumericLit (Z.of_int 1), "x", GP_Empty)) = ["x"]);

  check ~name:"GP_Values contributes every var it lists"
    (lateral_assignable_vars (GP_Values (["x"; "y"], [])) = ["x"; "y"]);

  check ~name:"GP_BGP assigns nothing (matching, not assigning)"
    (lateral_assignable_vars
       (GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_Var "p"; tp_o = PT_Var "o" } ]) = []);

  check ~name:"GP_PropertyPath assigns nothing"
    (lateral_assignable_vars (GP_PropertyPath (PS_Var "s", PP_IRI (ex "p"), PT_Var "o")) = []);

  check ~name:"GP_Empty assigns nothing"
    (lateral_assignable_vars GP_Empty = []);

  (* sub-SELECT: SI_Expr (the "AS" form) counts; SI_Var (plain
     pass-through) does not -- this asymmetry IS the Jena-confirmed
     rule quoted in the .fst banner. *)
  check ~name:"sub-SELECT: SI_Var (\"SELECT ?s\") is NOT assignable"
    (lateral_assignable_vars (GP_SubSelect (mk_query (QF_Select (Select_Vars [SI_Var "s"])) GP_Empty)) = []);

  check ~name:"sub-SELECT: SI_Expr (\"SELECT (1 AS ?s)\") IS assignable"
    (lateral_assignable_vars
       (GP_SubSelect (mk_query (QF_Select (Select_Vars [SI_Expr (E_NumericLit (Z.of_int 1), "s")])) GP_Empty))
     = ["s"]);

  check ~name:"sub-SELECT: mixed SELECT list only reports the AS-aliased names"
    (lateral_assignable_vars
       (GP_SubSelect
          (mk_query
             (QF_Select (Select_Vars [SI_Var "keep"; SI_Expr (E_NumericLit (Z.of_int 1), "assigned")]))
             GP_Empty))
     = ["assigned"]);

  check ~name:"sub-SELECT Select_All recurses into its own pattern's assignable vars"
    (lateral_assignable_vars
       (GP_SubSelect (mk_query (QF_Select Select_All) (GP_Bind (E_NumericLit (Z.of_int 1), "x", GP_Empty))))
     = ["x"]);

  check ~name:"sub-SELECT non-SELECT form (e.g. ASK) assigns nothing"
    (lateral_assignable_vars (GP_SubSelect (mk_query QF_Ask (GP_Bind (E_NumericLit (Z.of_int 1), "x", GP_Empty)))) = []);

  (* Combinators union both branches / pass through to the one operand
     that can surface bindings. *)
  let bind_x = GP_Bind (E_NumericLit (Z.of_int 1), "x", GP_Empty) in
  let bind_y = GP_Bind (E_NumericLit (Z.of_int 2), "y", GP_Empty) in
  check ~name:"GP_Join unions both sides' assignable vars"
    (lateral_assignable_vars (GP_Join (bind_x, bind_y)) = ["x"; "y"]);
  check ~name:"GP_Union unions both sides' assignable vars"
    (lateral_assignable_vars (GP_Union (bind_x, bind_y)) = ["x"; "y"]);
  check ~name:"GP_LeftJoin unions both sides' assignable vars"
    (lateral_assignable_vars (GP_LeftJoin (bind_x, bind_y, E_BoolLit true)) = ["x"; "y"]);
  check ~name:"GP_Lateral unions both sides' assignable vars"
    (lateral_assignable_vars (GP_Lateral (bind_x, bind_y)) = ["x"; "y"]);
  check ~name:"GP_Filter passes through its nested pattern's assignable vars"
    (lateral_assignable_vars (GP_Filter (E_BoolLit true, bind_x)) = ["x"]);
  check ~name:"GP_Graph passes through its nested pattern's assignable vars"
    (lateral_assignable_vars (GP_Graph (PT_IRI (ex "g"), bind_x)) = ["x"]);
  check ~name:"GP_Minus only reports its LEFT operand (RHS never surfaces bindings)"
    (lateral_assignable_vars (GP_Minus (bind_x, bind_y)) = ["x"]);
  check ~name:"GP_Service passes through its nested pattern's assignable vars"
    (lateral_assignable_vars (GP_Service (ex "svc", bind_x, false)) = ["x"]);
  check ~name:"GP_ServiceVar passes through its nested pattern's assignable vars"
    (lateral_assignable_vars (GP_ServiceVar ("svcvar", bind_x, false)) = ["x"])

(* ---------------------------------------------------------------- *)
(* 3. lateral_subselect_visible_vars                                  *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- lateral_subselect_visible_vars --\n";

  check ~name:"Select_Vars: exactly the listed names, both SI_Var and SI_Expr"
    (lateral_subselect_visible_vars
       (mk_query (QF_Select (Select_Vars [SI_Var "a"; SI_Expr (E_NumericLit (Z.of_int 1), "b")])) GP_Empty)
     = FStar_Pervasives_Native.Some ["a"; "b"]);

  check ~name:"Select_Vars empty list: nothing visible"
    (lateral_subselect_visible_vars (mk_query (QF_Select (Select_Vars [])) GP_Empty)
     = FStar_Pervasives_Native.Some []);

  check ~name:"Select_All: no restriction (None)"
    (lateral_subselect_visible_vars (mk_query (QF_Select Select_All) GP_Empty)
     = FStar_Pervasives_Native.None);

  check ~name:"non-SELECT form (ASK): nothing visible"
    (lateral_subselect_visible_vars (mk_query QF_Ask GP_Empty) = FStar_Pervasives_Native.Some [])

(* ---------------------------------------------------------------- *)
(* 4. Illegal-reassignment detection                                  *)
(*    (mirrors SPARQL11.Parser.fst's Tok_LATERAL arm exactly:          *)
(*     `List.existsb (fun v -> ggp_has_var v acc) (lateral_assignable_vars g)`) *)
(* ---------------------------------------------------------------- *)

let lateral_reassigns_bound_var (acc : group_graph_pattern) (rhs : group_graph_pattern) : bool =
  List.exists (fun v -> ggp_has_var v acc) (lateral_assignable_vars rhs)

let () =
  Printf.printf "-- illegal-reassignment detection (parser-primitive level) --\n";

  let acc_binds_s = GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "type"); tp_o = PT_IRI (ex "Person") } ] in

  check ~name:"BIND reassigning an already-bound LHS var IS flagged"
    (lateral_reassigns_bound_var acc_binds_s (GP_Bind (E_NumericLit (Z.of_int 1), "s", GP_Empty)) = true);

  check ~name:"BIND assigning a FRESH var is NOT flagged"
    (lateral_reassigns_bound_var acc_binds_s (GP_Bind (E_NumericLit (Z.of_int 1), "fresh", GP_Empty)) = false);

  check ~name:"VALUES reassigning an already-bound LHS var IS flagged"
    (lateral_reassigns_bound_var acc_binds_s (GP_Values (["s"], [])) = true);

  check ~name:"VALUES on a fresh var is NOT flagged"
    (lateral_reassigns_bound_var acc_binds_s (GP_Values (["fresh"], [])) = false);

  check ~name:"sub-SELECT AS-aliasing an already-bound LHS var IS flagged"
    (lateral_reassigns_bound_var acc_binds_s
       (GP_SubSelect (mk_query (QF_Select (Select_Vars [SI_Expr (E_NumericLit (Z.of_int 1), "s")])) GP_Empty))
     = true);

  check ~name:"sub-SELECT plain SI_Var pass-through projection of the SAME name is NOT flagged \
               (Jena-confirmed: `LATERAL { SELECT ?s WHERE {...} }` runs without error)"
    (lateral_reassigns_bound_var acc_binds_s
       (GP_SubSelect (mk_query (QF_Select (Select_Vars [SI_Var "s"])) GP_Empty))
     = false);

  check ~name:"plain correlated BGP (no BIND/VALUES/sub-SELECT) never flags anything"
    (lateral_reassigns_bound_var acc_binds_s
       (GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "label"); tp_o = PT_Var "label" } ])
     = false)

(* ---------------------------------------------------------------- *)
(* 4b. Same checks, end-to-end through SPARQL11_Parser.parse_sparql   *)
(*     on the exact query text of tests/local/sparql/lateral_*.rq     *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- illegal-reassignment detection (end-to-end parser) --\n";

  let contains haystack needle =
    let lh = String.length haystack and ln = String.length needle in
    let rec scan i = i + ln <= lh && (String.sub haystack i ln = needle || scan (i + 1)) in
    scan 0
  in
  let is_parse_err msg_substr src =
    match SPARQL11_Parser.parse_sparql src with
    | SPARQL11_Parser.ParseErr m -> contains m msg_substr
    | SPARQL11_Parser.ParseOk _ -> false
  in
  let is_parse_ok src =
    match SPARQL11_Parser.parse_sparql src with
    | SPARQL11_Parser.ParseOk _ -> true
    | SPARQL11_Parser.ParseErr _ -> false
  in
  let reassign_err = "reassigns a variable already bound by the left-hand pattern" in

  (* mirrors tests/local/sparql/lateral_illegal_bind.rq *)
  check ~name:"end-to-end: LATERAL { BIND(1 AS ?s) } after ?s rdf:type :Person is rejected"
    (is_parse_err reassign_err
       "PREFIX : <https://example.org/>\n\
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
        SELECT * WHERE {\n\
        \  ?s rdf:type :Person .\n\
        \  LATERAL { BIND(1 AS ?s) }\n\
        }");

  (* mirrors tests/local/sparql/lateral_illegal_values.rq *)
  check ~name:"end-to-end: LATERAL { VALUES ?s {...} } after ?s rdf:type :Person is rejected"
    (is_parse_err reassign_err
       "PREFIX : <https://example.org/>\n\
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
        SELECT * WHERE {\n\
        \  ?s rdf:type :Person .\n\
        \  LATERAL { VALUES ?s { <https://example.org/nope> } }\n\
        }");

  (* mirrors tests/local/sparql/lateral_illegal_subselect_projection.rq.
     This query text trips TWO independent well-formedness checks at
     once: `(1 AS ?s)` aliases a name that is ALSO used by the SAME
     sub-query's own WHERE clause (a general SPARQL 1.1 SELECT-list
     restriction, unrelated to LATERAL) AND ?s is already bound by the
     LATERAL LHS (the check this suite is pinning). Whichever the
     parser reaches first is a legitimate rejection of this query --
     tests/local/lateral_joins.sh's own `expect_parse_error` helper
     already tolerates either message for this exact fixture, so this
     test mirrors that same tolerance rather than over-committing to
     one specific error string. *)
  check ~name:"end-to-end: LATERAL { SELECT (1 AS ?s) ... } after ?s rdf:type :Person is rejected"
    (is_parse_err reassign_err
       "PREFIX : <https://example.org/>\n\
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
        SELECT * WHERE {\n\
        \  ?s rdf:type :Person .\n\
        \  LATERAL { SELECT (1 AS ?s) WHERE { ?s :label ?label } }\n\
        }"
     || is_parse_err "SELECT expression aliases variable already in scope"
       "PREFIX : <https://example.org/>\n\
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
        SELECT * WHERE {\n\
        \  ?s rdf:type :Person .\n\
        \  LATERAL { SELECT (1 AS ?s) WHERE { ?s :label ?label } }\n\
        }");

  (* mirrors tests/local/sparql/lateral_plain_bgp.rq -- legal, no reassignment *)
  check ~name:"end-to-end: plain correlated BGP inside LATERAL parses fine"
    (is_parse_ok
       "PREFIX : <https://example.org/>\n\
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
        SELECT ?s ?label WHERE {\n\
        \  ?s rdf:type :Person .\n\
        \  LATERAL { ?s :label ?label }\n\
        }\n\
        ORDER BY ?s ?label");

  (* mirrors tests/local/sparql/lateral_subselect_masking.rq -- legal:
     SELECT ?label only (a plain pass-through, no AS on ?s) *)
  check ~name:"end-to-end: LATERAL { SELECT ?label {...} } (no AS on ?s) parses fine"
    (is_parse_ok
       "PREFIX : <https://example.org/>\n\
        PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n\
        SELECT ?s ?label WHERE {\n\
        \  ?s rdf:type :Person .\n\
        \  LATERAL {\n\
        \    SELECT ?label WHERE { ?s :label ?label } ORDER BY ?label LIMIT 1\n\
        \  }\n\
        }\n\
        ORDER BY ?s")

(* ---------------------------------------------------------------- *)
(* 5. End-to-end correlated evaluation over a hand-built graph        *)
(*    (SPARQL11_Algebra.eval_pattern, no store/backend indirection)   *)
(* ---------------------------------------------------------------- *)

let () =
  Printf.printf "-- end-to-end correlated evaluation (eval_pattern) --\n";

  let graph : rdf_graph = [
    t (iri_subj (ex "alice")) (ex "type") (iri_obj (ex "Person"));
    t (iri_subj (ex "bob"))   (ex "type") (iri_obj (ex "Person"));
    t (iri_subj (ex "alice")) (ex "label") (lit_obj "aaa");
    t (iri_subj (ex "bob"))   (ex "label") (lit_obj "bbb");
  ] in

  let lhs = GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "type"); tp_o = PT_IRI (ex "Person") } ] in
  let label_pattern = GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "label"); tp_o = PT_Var "label" } ] in

  (* (a) Plain correlated BGP (no sub-SELECT at all): LATERAL degenerates
     to an ordinary join -- each of the 2 outer subjects pairs with
     exactly its OWN label (2 rows total), matching
     tests/local/sparql/lateral_plain_bgp.rq's documented behavior. *)
  let pattern_plain_bgp = GP_Lateral (lhs, label_pattern) in
  let omega_plain = eval_pattern FStar_Pervasives_Native.None pattern_plain_bgp graph empty_dataset in
  let pairs_plain =
    List.sort compare
      (List.map
         (fun mu -> (sm_lookup "s" mu, sm_lookup "label" mu))
         omega_plain)
  in
  check ~name:"(a) plain BGP LATERAL: 2 rows, each subject paired with its own label"
    (pairs_plain =
       [ (FStar_Pervasives_Native.Some (iri_obj (ex "alice")), FStar_Pervasives_Native.Some (lit_obj "aaa"));
         (FStar_Pervasives_Native.Some (iri_obj (ex "bob")),   FStar_Pervasives_Native.Some (lit_obj "bbb")) ]);

  (* (b) Sub-SELECT projecting only ?label (masked): outer ?s is NOT
     substituted in, so the inner query runs unconstrained against the
     WHOLE graph for every single outer row -- both labels reach every
     outer row (2 outer x 2 inner = 4 rows), matching the
     "masking"/lateral_subselect_masking.rq contrast documented in the
     .fst banner (illustrated here without ORDER BY/LIMIT, via a row
     count instead of "same globally-smallest label", to keep the
     comparison assumption-free). *)
  let rhs_masked = GP_SubSelect (mk_query (QF_Select (Select_Vars [SI_Var "label"])) label_pattern) in
  let pattern_masked = GP_Lateral (lhs, rhs_masked) in
  let omega_masked = eval_pattern FStar_Pervasives_Native.None pattern_masked graph empty_dataset in
  check ~name:"(b) sub-SELECT ?label only: masked/uncorrelated -- 4 rows (2 outer x 2 inner)"
    (List.length omega_masked = 4);

  (* (c) Sub-SELECT * (visible): outer ?s IS substituted in, so each
     outer row's inner evaluation is constrained to its OWN subject --
     back to 2 correlated rows, matching lateral_plain_bgp.rq's
     "LATERAL degenerates to JOIN" contrast when a sub-SELECT * is used
     instead of no sub-SELECT at all. *)
  let rhs_correlated = GP_SubSelect (mk_query (QF_Select Select_All) label_pattern) in
  let pattern_correlated = GP_Lateral (lhs, rhs_correlated) in
  let omega_correlated = eval_pattern FStar_Pervasives_Native.None pattern_correlated graph empty_dataset in
  let pairs_correlated =
    List.sort compare
      (List.map
         (fun mu -> (sm_lookup "s" mu, sm_lookup "label" mu))
         omega_correlated)
  in
  check ~name:"(c) sub-SELECT *: visible/correlated -- back to 2 rows, each subject's own label"
    (pairs_correlated = pairs_plain);

  (* (d) Empty LHS: RHS is never even reached -- 0 rows (no rdf:type
     :NoSuchClass triples exist), matching lateral_empty_lhs.rq. *)
  let lhs_empty =
    GP_BGP [ { tp_s = PS_Var "s"; tp_p = PT_IRI (ex "type"); tp_o = PT_IRI (ex "NoSuchClass") } ]
  in
  let pattern_empty_lhs = GP_Lateral (lhs_empty, label_pattern) in
  let omega_empty_lhs = eval_pattern FStar_Pervasives_Native.None pattern_empty_lhs graph empty_dataset in
  check ~name:"(d) empty LHS: 0 rows, RHS never evaluated for a nonexistent outer row"
    (omega_empty_lhs = []);

  (* (e) A subject with no matching RHS row disappears entirely
     (LATERAL is a flatmap/inner-join, not a left-join): add carol
     (a Person with no :label triple) and confirm she drops out. *)
  let graph_with_carol = t (iri_subj (ex "carol")) (ex "type") (iri_obj (ex "Person")) :: graph in
  let omega_with_carol =
    eval_pattern FStar_Pervasives_Native.None pattern_plain_bgp graph_with_carol empty_dataset
  in
  check ~name:"(e) LATERAL is inner-join-shaped: a labelless Person contributes 0 rows, not a null row"
    (List.length omega_with_carol = 2
     && not (List.exists (fun mu -> sm_lookup "s" mu = FStar_Pervasives_Native.Some (iri_obj (ex "carol"))) omega_with_carol));

  Printf.printf "lateral_unit: %d pass, %d fail (out of %d)\n" !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
