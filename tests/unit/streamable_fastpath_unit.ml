(* streamable_fastpath_unit.ml — pins SPARQL.Plan.Streamable.fst, the
   F* shape-recognizer + per-triple fold behind the CLI's parse-stream
   query fast path (docs/designissues/2026-07-05-disk-backed-db-perf-
   review.md, roadmap "bound in-memory query memory").

   Three things are pinned here:

   1. `streamable_shape` recognizes exactly the four target shapes
      (COUNT-star/ASK over a single triple pattern, default graph or a
      GRAPH ?g wildcard over named graphs; any triple-pattern position
      may be a constant) and returns None for shapes that need row
      materialisation (multi-pattern BGP, FILTER, GROUP BY, DISTINCT,
      VALUES-on-ASK) -- the CLI falls through to the existing
      materialise-then-evaluate path whenever this returns None, so an
      over-eager `Some` here would silently produce a wrong answer,
      not just a slow one.

   2. `stream_step` / `stream_in_domain` / `stream_stop` fold triples
      into a `stream_state` correctly: COUNT tallies matches against a
      bound pattern, ASK latches on first match and reports "stop",
      and the N-Quads default-graph/named-graph domain split (see the
      module's banner) doesn't cross-count.

   3. The new generic parser fold entry points (Parser_Turtle.
      fold_turtle_triples, Parser_NTriples.fold_ntriples,
      Parser_NQuads.fold_nquads) produce the exact same triples, in
      the exact same order, as the pre-existing known-correct
      parse_turtle/parse_ntriples/parse_nquads on the same input --
      i.e. the new fold machinery is a faithful generalisation of the
      existing parsers, not a second, drifting implementation. *)

open RDF_Graph_Executable
open SPARQL11_Algebra

let passed = ref 0
let failed = ref 0

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

(* ------------------------------------------------------------------ *)
(* 1. streamable_shape                                                 *)
(* ------------------------------------------------------------------ *)

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
  {
    q_base     = FStar_Pervasives_Native.None;
    q_prefixes = [];
    q_form     = form;
    q_dataset  = [];
    q_pattern  = pattern;
    q_group_by = group_by;
    q_having   = having;
    q_modifier = modifier;
    q_values   = values;
  }

let count_star_select (alias : string) : select_clause =
  Select_Vars [SI_Expr (E_Aggregate (Agg_Count, false, E_Var "*"), alias)]

let tp_all_var : triple_pattern =
  { tp_s = PS_Var "s"; tp_p = PT_Var "p"; tp_o = PT_Var "o" }

let tp_bound_pred : triple_pattern =
  { tp_s = PS_Var "s"; tp_p = PT_IRI "http://ex/p1"; tp_o = PT_Var "o" }

let empty_bound : triple_pattern_bound =
  { bs = FStar_Pervasives_Native.None;
    bp = FStar_Pervasives_Native.None;
    bo = FStar_Pervasives_Native.None }

let bound_with_pred : triple_pattern_bound =
  { empty_bound with bp = FStar_Pervasives_Native.Some "http://ex/p1" }

let () =
  Printf.printf "-- streamable_shape: positive shapes --\n";
  let open SPARQL_Plan_Streamable in

  (* (a) SELECT (COUNT-star AS ?n) WHERE { ?s ?p ?o } *)
  let shape_a = mk_query (QF_Select (count_star_select "n")) (GP_BGP [tp_all_var]) in
  let expect_a : stream_plan option = FStar_Pervasives_Native.Some {
    sp_domain = SD_DefaultGraph; sp_bound = empty_bound; sp_goal = SG_Count "n";
    sp_offset = FStar_Pervasives_Native.None; sp_limit = FStar_Pervasives_Native.None;
  } in
  check ~name:"(a) COUNT(*) over ?s ?p ?o" (streamable_shape shape_a = expect_a);

  (* (b) SELECT (COUNT-star AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } *)
  let shape_b = mk_query (QF_Select (count_star_select "n"))
      (GP_Graph (PT_Var "g", GP_BGP [tp_all_var])) in
  let expect_b : stream_plan option = FStar_Pervasives_Native.Some {
    sp_domain = SD_AnyNamedGraph; sp_bound = empty_bound; sp_goal = SG_Count "n";
    sp_offset = FStar_Pervasives_Native.None; sp_limit = FStar_Pervasives_Native.None;
  } in
  check ~name:"(b) COUNT(*) over GRAPH ?g wildcard" (streamable_shape shape_b = expect_b);

  (* (c) ASK { ?s ?p ?o } *)
  let shape_c = mk_query QF_Ask (GP_BGP [tp_all_var]) in
  let expect_c : stream_plan option = FStar_Pervasives_Native.Some {
    sp_domain = SD_DefaultGraph; sp_bound = empty_bound; sp_goal = SG_Ask;
    sp_offset = FStar_Pervasives_Native.None; sp_limit = FStar_Pervasives_Native.None;
  } in
  check ~name:"(c) ASK { ?s ?p ?o }" (streamable_shape shape_c = expect_c);

  (* (d) COUNT-star with a bound predicate *)
  let shape_d = mk_query (QF_Select (count_star_select "n")) (GP_BGP [tp_bound_pred]) in
  let expect_d : stream_plan option = FStar_Pervasives_Native.Some {
    sp_domain = SD_DefaultGraph; sp_bound = bound_with_pred; sp_goal = SG_Count "n";
    sp_offset = FStar_Pervasives_Native.None; sp_limit = FStar_Pervasives_Native.None;
  } in
  check ~name:"(d) COUNT(*) with bound predicate" (streamable_shape shape_d = expect_d);

  (* (d) ASK with a bound predicate — same idea, ASK form *)
  let shape_d_ask = mk_query QF_Ask (GP_BGP [tp_bound_pred]) in
  let expect_d_ask : stream_plan option = FStar_Pervasives_Native.Some {
    sp_domain = SD_DefaultGraph; sp_bound = bound_with_pred; sp_goal = SG_Ask;
    sp_offset = FStar_Pervasives_Native.None; sp_limit = FStar_Pervasives_Native.None;
  } in
  check ~name:"(d) ASK with bound predicate" (streamable_shape shape_d_ask = expect_d_ask);

  Printf.printf "-- streamable_shape: non-streamable shapes (must fall through) --\n";

  (* Two-pattern BGP — needs a join, not a single bound scan. *)
  let shape_neg1 = mk_query (QF_Select (count_star_select "n"))
      (GP_BGP [tp_all_var; tp_bound_pred]) in
  check ~name:"multi-pattern BGP falls through"
    (streamable_shape shape_neg1 = FStar_Pervasives_Native.None);

  (* FILTER above the BGP — needs row materialisation to evaluate. *)
  let shape_neg2 = mk_query (QF_Select (count_star_select "n"))
      (GP_Filter (E_BoolLit true, GP_BGP [tp_all_var])) in
  check ~name:"FILTER-wrapped pattern falls through"
    (streamable_shape shape_neg2 = FStar_Pervasives_Native.None);

  (* GROUP BY — needs per-group materialisation. *)
  let shape_neg3 = mk_query
      ~group_by:(FStar_Pervasives_Native.Some [GC_Var "p"])
      (QF_Select (Select_Vars [SI_Var "p"; SI_Expr (E_Aggregate (Agg_Count, false, E_Var "*"), "n")]))
      (GP_BGP [tp_all_var]) in
  check ~name:"GROUP BY falls through"
    (streamable_shape shape_neg3 = FStar_Pervasives_Native.None);

  (* DISTINCT — needs a dedup pass over materialised rows. *)
  let distinct_modifier = { default_modifier with sm_distinct = true } in
  let shape_neg4 = mk_query ~modifier:distinct_modifier
      (QF_Select (count_star_select "n")) (GP_BGP [tp_all_var]) in
  check ~name:"DISTINCT falls through"
    (streamable_shape shape_neg4 = FStar_Pervasives_Native.None);

  (* VALUES on an ASK — the fast path can't honour the join. *)
  let shape_neg5 = mk_query
      ~values:(FStar_Pervasives_Native.Some [[("s", T_IRI "http://example.org/x")]])
      QF_Ask (GP_BGP [tp_all_var]) in
  check ~name:"VALUES-on-ASK falls through"
    (streamable_shape shape_neg5 = FStar_Pervasives_Native.None);

  (* GRAPH ?g wildcard where the graph var is reused inside the BGP —
     an implicit equality constraint the bound-only match can't
     honour (module banner explains why this must be rejected). *)
  let shape_neg6 = mk_query (QF_Select (count_star_select "n"))
      (GP_Graph (PT_Var "g", GP_BGP [{ tp_s = PS_Var "g"; tp_p = PT_Var "p"; tp_o = PT_Var "o" }])) in
  check ~name:"GRAPH ?g reused inside BGP falls through"
    (streamable_shape shape_neg6 = FStar_Pervasives_Native.None)

(* ------------------------------------------------------------------ *)
(* 2. stream_step / stream_in_domain / stream_stop                     *)
(* ------------------------------------------------------------------ *)

let mk_t s p o = ({ s = S_IRI s; p; o = T_IRI o } : triple)

let t_ab = mk_t "http://ex/a" "http://ex/p1" "http://ex/b"
let t_ac = mk_t "http://ex/a" "http://ex/p2" "http://ex/c"
let t_de = mk_t "http://ex/d" "http://ex/p1" "http://ex/e"

let () =
  Printf.printf "-- stream_step / stream_stop --\n";
  let open SPARQL_Plan_Streamable in

  let count_all_plan : stream_plan = {
    sp_domain = SD_DefaultGraph; sp_bound = empty_bound; sp_goal = SG_Count "n";
    sp_offset = FStar_Pervasives_Native.None; sp_limit = FStar_Pervasives_Native.None;
  } in
  let st = List.fold_left (fun acc t -> stream_step count_all_plan t acc)
      stream_init [t_ab; t_ac; t_de] in
  check ~name:"COUNT(*) over 3 triples = 3" (Z.equal (stream_count_result st) (Z.of_int 3));

  let count_pred_plan : stream_plan = { count_all_plan with sp_bound = bound_with_pred } in
  let st2 = List.fold_left (fun acc t -> stream_step count_pred_plan t acc)
      stream_init [t_ab; t_ac; t_de] in
  check ~name:"COUNT(*) bound predicate p1 = 2" (Z.equal (stream_count_result st2) (Z.of_int 2));

  let ask_plan : stream_plan = { count_all_plan with sp_goal = SG_Ask } in
  let st3a = stream_step ask_plan t_ac stream_init in
  check ~name:"ASK finds a match" (stream_ask_result st3a = true);
  check ~name:"ASK stops after a match" (stream_stop ask_plan st3a = true);
  check ~name:"ASK does not stop before any match" (stream_stop ask_plan stream_init = false);

  let count_plan_never_stops : stream_plan = count_all_plan in
  check ~name:"COUNT never signals stop"
    (stream_stop count_plan_never_stops st = false);

  (* Domain split: a default-graph plan only accepts quads with no
     graph label; an any-named-graph plan only accepts quads WITH
     one. Conflating the two would over/under-count on N-Quads input
     with a mix of labelled and unlabelled lines. *)
  let named_plan : stream_plan = { count_all_plan with sp_domain = SD_AnyNamedGraph } in
  check ~name:"default-graph plan accepts unlabelled quad"
    (stream_in_domain count_all_plan FStar_Pervasives_Native.None = true);
  check ~name:"default-graph plan rejects labelled quad"
    (stream_in_domain count_all_plan (FStar_Pervasives_Native.Some "http://ex/g1") = false);
  check ~name:"any-named-graph plan rejects unlabelled quad"
    (stream_in_domain named_plan FStar_Pervasives_Native.None = false);
  check ~name:"any-named-graph plan accepts labelled quad"
    (stream_in_domain named_plan (FStar_Pervasives_Native.Some "http://ex/g1") = true)

(* ------------------------------------------------------------------ *)
(* 3. Generic parser folds must match the pre-existing parsers         *)
(* ------------------------------------------------------------------ *)

let () =
  Printf.printf "-- generic parser folds vs. known-correct parsers --\n";

  let turtle_src =
    "<http://ex/a> <http://ex/p1> <http://ex/b> .\n\
     <http://ex/c> <http://ex/p2> <http://ex/d> .\n\
     <http://ex/e> <http://ex/p1> <http://ex/f> .\n" in
  let via_parse = Parser_Turtle.parse_turtle turtle_src in
  let via_fold =
    List.rev (Parser_Turtle.fold_turtle_triples
                (fun t acc -> t :: acc) (fun _ -> false) [] turtle_src) in
  check ~name:"Turtle fold matches parse_turtle" (via_parse = via_fold);

  let nt_src =
    "<http://ex/a> <http://ex/p1> <http://ex/b> .\n\
     <http://ex/c> <http://ex/p2> <http://ex/d> .\n" in
  let via_parse_nt = Parser_NTriples.parse_ntriples nt_src in
  let via_fold_nt =
    List.rev (Parser_NTriples.fold_ntriples
                (fun t acc -> t :: acc) (fun _ -> false) [] nt_src) in
  check ~name:"NTriples fold matches parse_ntriples" (via_parse_nt = via_fold_nt);

  let nq_src =
    "<http://ex/a> <http://ex/p1> <http://ex/b> .\n\
     <http://ex/c> <http://ex/p1> <http://ex/d> <http://ex/g1> .\n" in
  let ds = Parser_NQuads.parse_nquads nq_src in
  let via_fold_nq =
    List.rev (Parser_NQuads.fold_nquads
                (fun t g acc -> (t, g) :: acc) (fun _ -> false) [] nq_src) in
  let expected_nq = [
    (mk_t "http://ex/a" "http://ex/p1" "http://ex/b", FStar_Pervasives_Native.None);
    (mk_t "http://ex/c" "http://ex/p1" "http://ex/d", FStar_Pervasives_Native.Some "http://ex/g1");
  ] in
  check ~name:"NQuads fold produces (triple, graph label) pairs in order"
    (via_fold_nq = expected_nq);
  check ~name:"NQuads fold's unlabelled quad matches parse_nquads default graph"
    (ds.ds_default = [mk_t "http://ex/a" "http://ex/p1" "http://ex/b"]);
  check ~name:"NQuads fold's labelled quad matches parse_nquads named graph"
    (match ds.ds_named with
     | [ng] -> ng.ng_name = "http://ex/g1" && ng.ng_graph = [mk_t "http://ex/c" "http://ex/p1" "http://ex/d"]
     | _ -> false)

let () =
  Printf.printf "streamable_fastpath_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
