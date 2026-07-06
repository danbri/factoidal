(* store_capabilities_unit.ml -- stage U1 safety net for
   docs/designissues/2026-07-06-unified-store-architecture.md.

   RDF.Store.Capabilities.fst / RDF.Store.Capabilities.Cottas.fst
   introduce ONE typed capability record (`store_caps`) whose fields
   are supposed to be nothing more than the SAME entry points
   SPARQL11.Store.fst's six tag-dispatchers already call
   (ig_search/ig_estimate for the in-memory backend;
   cottas_ondisk_search/_limited/_estimate/_count_exact/
   _predicate_present/_has_decode_failure for the on-disk COTTAS
   backend). Stage U1 deliberately does NOT rewire any dispatcher (that
   is U2) -- this test is the "proof by test, not by wiring" floor the
   design doc's migration table asks for: it loads a small dataset
   through BOTH builders (`caps_of_indexed` over an in-memory
   `indexed_graph`; `caps_of_cottas` over a real on-disk COTTAS
   artifact) and asserts, across a matrix of bound/unbound pattern
   shapes (including a named-graph case for each backend), that
   invoking the field through the `store_caps` record returns EXACTLY
   what invoking the underlying function directly returns.

   Order convention: every comparison below preserves LIST ORDER (no
   sorting) -- `sc_solve`/`sc_solve_limited` are documented as literal
   wrappers around `ig_search`/`cottas_ondisk_search[_limited]`, which
   return already-ordered lists, and the wrapper closures do not
   reorder them. If a future change makes either side reorder its
   result this test will legitimately fail rather than silently
   passing via a sort-normalized comparison.

   Fixtures:
     - In-memory: five triples built directly in this file, matching
       tests/local/data/cottas_sample.nq (reused so both backends load
       "the same dataset" in spirit): two named graphs
       (.../graph/people, .../graph/docs) + one default-graph triple.
     - On-disk: tests/unit/fixtures/store_capabilities_sample.cottas,
       the pycottas-materialised COTTAS artifact built from that exact
       .nq file (tools/corpus_pipeline.py materialize-nq-cottas-corpus,
       verified via `pycottas.verify` at build time) -- a REAL
       N-Quads-token-encoded artifact, unlike the bare-string
       Parquet-decode fixtures elsewhere in tests/unit/fixtures/, so
       cottas_ondisk_build_bound_qp_opt's term-to-dictionary encoding
       actually round-trips and bound queries produce non-empty
       results to compare. *)

let passed = ref 0
let failed = ref 0

let check ~name ok =
  if ok then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

(* ---------------------------------------------------------------- *)
(* Term/triple helpers                                               *)
(* ---------------------------------------------------------------- *)

let s_iri (i : string) : RDF_Term.subject = RDF_Term.S_IRI i
let t_iri (i : string) : RDF_Term.rdf_term = RDF_Term.T_IRI i
let t_lit (v : string) : RDF_Term.rdf_term =
  RDF_Term.T_Literal
    { RDF_Term.lexical_form = v;
      RDF_Term.datatype = RDF_Term.xsd_string;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None }
let mk_triple s p o : RDF_Triple.triple =
  { RDF_Triple.s = s; RDF_Triple.p = p; RDF_Triple.o = o }

let some x = FStar_Pervasives_Native.Some x
let none = FStar_Pervasives_Native.None

let bound ?s ?p ?o () : SPARQL11_Algebra.triple_pattern_bound =
  { SPARQL11_Algebra.bs = (match s with None -> none | Some v -> some v);
    SPARQL11_Algebra.bp = (match p with None -> none | Some v -> some v);
    SPARQL11_Algebra.bo = (match o with None -> none | Some v -> some v) }

(* The eight bound/unbound shapes for one anchor triple: every subset
   of {s, p, o} bound, the rest unbound. *)
let shapes_of (t : RDF_Triple.triple) :
  (string * SPARQL11_Algebra.triple_pattern_bound) list =
  [ "unbound",   bound ();
    "bound-s",   bound ~s:t.RDF_Triple.s ();
    "bound-p",   bound ~p:t.RDF_Triple.p ();
    "bound-o",   bound ~o:t.RDF_Triple.o ();
    "bound-sp",  bound ~s:t.RDF_Triple.s ~p:t.RDF_Triple.p ();
    "bound-po",  bound ~p:t.RDF_Triple.p ~o:t.RDF_Triple.o ();
    "bound-so",  bound ~s:t.RDF_Triple.s ~o:t.RDF_Triple.o ();
    "bound-spo", bound ~s:t.RDF_Triple.s ~p:t.RDF_Triple.p ~o:t.RDF_Triple.o ();
  ]

let contains ~needle hay =
  let nl = String.length needle and hl = String.length hay in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  go 0

(* ---------------------------------------------------------------- *)
(* In-memory backend: caps_of_indexed vs ig_search/ig_estimate direct *)
(* ---------------------------------------------------------------- *)

let alice = "https://example.org/alice"
let bob = "https://example.org/bob"
let doc = "https://example.org/doc"
let default_subject = "https://example.org/default-subject"
let p_name = "https://example.org/name"
let p_knows = "https://example.org/knows"
let p_title = "https://example.org/title"
let p_status = "https://example.org/status"
let p_absent = "https://example.org/does-not-exist"

let people_triples =
  [ mk_triple (s_iri alice) p_name (t_lit "Alice");
    mk_triple (s_iri alice) p_knows (t_iri bob);
    mk_triple (s_iri bob) p_name (t_lit "Bob");
  ]
let docs_triples = [ mk_triple (s_iri doc) p_title (t_lit "Specimen") ]
let default_triples = [ mk_triple (s_iri default_subject) p_status (t_lit "default") ]

let check_indexed_graph ~label ~(ig : RDF_Indexed.indexed_graph)
    ~(caps : RDF_Store_Capabilities.store_caps) ~(anchor : RDF_Triple.triple)
    ~(known_pred : string) =
  List.iter
    (fun (shape_name, b) ->
      let name field = Printf.sprintf "indexed/%s/%s/%s" label shape_name field in
      check ~name:(name "solve")
        ((caps.RDF_Store_Capabilities.sc_solve b) = (SPARQL11_Algebra.ig_search ig b));
      check ~name:(name "solve_limited(1)")
        ((caps.RDF_Store_Capabilities.sc_solve_limited b Z.one)
         = (RDF_Store_Capabilities.caps_take_n Z.one (SPARQL11_Algebra.ig_search ig b)));
      check ~name:(name "estimate")
        ((caps.RDF_Store_Capabilities.sc_estimate b) = (SPARQL11_Algebra.ig_estimate ig b));
      check ~name:(name "count_exact")
        ((caps.RDF_Store_Capabilities.sc_count_exact b) = (SPARQL11_Algebra.ig_estimate ig b)))
    (shapes_of anchor);
  check ~name:(Printf.sprintf "indexed/%s/predicate_present/known" label)
    ((caps.RDF_Store_Capabilities.sc_predicate_present known_pred)
     = (Z.gt (SPARQL11_Algebra.ig_estimate ig (bound ~p:known_pred ())) Z.zero));
  check ~name:(Printf.sprintf "indexed/%s/predicate_present/absent" label)
    ((caps.RDF_Store_Capabilities.sc_predicate_present p_absent)
     = (Z.gt (SPARQL11_Algebra.ig_estimate ig (bound ~p:p_absent ())) Z.zero));
  check ~name:(Printf.sprintf "indexed/%s/decode_failure" label)
    ((caps.RDF_Store_Capabilities.sc_decode_failure ()) = false)

(* ---------------------------------------------------------------- *)
(* COTTAS-on-disk backend: caps_of_cottas vs the raw entry points     *)
(* ---------------------------------------------------------------- *)

let raw_bound_opt cods scope (b : SPARQL11_Algebra.triple_pattern_bound) =
  RDF_CottasStore.cottas_ondisk_build_bound_qp_opt cods
    b.SPARQL11_Algebra.bs b.SPARQL11_Algebra.bp b.SPARQL11_Algebra.bo scope

let raw_solve cods scope b =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some bnd ->
    RDF_CottasStore.cottas_ondisk_rows_to_triples cods
      (RDF_CottasStore.cottas_ondisk_search cods bnd)

let raw_solve_limited cods scope b n =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some bnd ->
    RDF_CottasStore.cottas_ondisk_rows_to_triples cods
      (RDF_CottasStore.cottas_ondisk_search_limited cods bnd n)

let raw_estimate cods scope b =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> Z.zero
  | FStar_Pervasives_Native.Some bnd -> RDF_CottasStore.cottas_ondisk_estimate cods bnd

let raw_count_exact cods scope b =
  match raw_bound_opt cods scope b with
  | FStar_Pervasives_Native.None -> Z.zero
  | FStar_Pervasives_Native.Some bnd -> RDF_CottasStore.cottas_ondisk_count_exact cods bnd

let check_cottas_scope ~label ~cods ~scope
    ~(caps : RDF_Store_Capabilities.store_caps) ~(anchor : RDF_Triple.triple)
    ~(known_pred : string) =
  List.iter
    (fun (shape_name, b) ->
      let name field = Printf.sprintf "cottas/%s/%s/%s" label shape_name field in
      check ~name:(name "solve")
        ((caps.RDF_Store_Capabilities.sc_solve b) = (raw_solve cods scope b));
      check ~name:(name "solve_limited(1)")
        ((caps.RDF_Store_Capabilities.sc_solve_limited b Z.one) = (raw_solve_limited cods scope b Z.one));
      check ~name:(name "estimate")
        ((caps.RDF_Store_Capabilities.sc_estimate b) = (raw_estimate cods scope b));
      check ~name:(name "count_exact")
        ((caps.RDF_Store_Capabilities.sc_count_exact b) = (raw_count_exact cods scope b)))
    (shapes_of anchor);
  check ~name:(Printf.sprintf "cottas/%s/predicate_present/known" label)
    ((caps.RDF_Store_Capabilities.sc_predicate_present known_pred)
     = (RDF_CottasStore.cottas_ondisk_predicate_present cods known_pred));
  check ~name:(Printf.sprintf "cottas/%s/predicate_present/absent" label)
    ((caps.RDF_Store_Capabilities.sc_predicate_present p_absent)
     = (RDF_CottasStore.cottas_ondisk_predicate_present cods p_absent));
  check ~name:(Printf.sprintf "cottas/%s/decode_failure" label)
    ((caps.RDF_Store_Capabilities.sc_decode_failure ())
     = (RDF_CottasStore.cottas_ondisk_has_decode_failure cods.RDF_CottasStore.cods_handle))

(* ---------------------------------------------------------------- *)
(* GB_Union equivalence: RDF_Store_Capabilities.union_caps vs the     *)
(* pre-U2 GB_Union recursion (SPARQL11_Store.backend_search/_limited/ *)
(* estimate/count_exact/predicate_present/decode_failure applied to a *)
(* REAL `GB_Union [...]` value built from the SAME underlying graphs) *)
(*                                                                     *)
(* Stage U2 risk item (docs/designissues/2026-07-06-unified-store-    *)
(* architecture.md): union_caps was UNTESTED in U1. This is the "test *)
(* before rewiring" floor -- SPARQL11_Store's dispatchers are STILL   *)
(* the old per-constructor match at the point this test runs, so a    *)
(* mismatch here is caught before SPARQL11.Store.fst's own dispatchers*)
(* are rewired to go through caps_of_backend/union_caps.               *)
(*                                                                     *)
(* solve_limited is exercised across n = 0,1,2,3,4,5,100 on the fully  *)
(* unbound shape specifically to walk the boundary BETWEEN union      *)
(* members' own contributions (the real per-member LIMIT-pushdown     *)
(* budget accounting in union_solve_limited_acc), not just the total. *)
(* ---------------------------------------------------------------- *)

let check_union_case ~label ~(gb_union : SPARQL11_Store.graph_backend)
    ~(caps_union : RDF_Store_Capabilities.store_caps) ~(anchors : RDF_Triple.triple list)
    ~(known_preds : string list) =
  List.iter
    (fun (anchor : RDF_Triple.triple) ->
      List.iter
        (fun (shape_name, b) ->
          let name field = Printf.sprintf "union/%s/%s/%s" label shape_name field in
          check ~name:(name "solve")
            ((caps_union.RDF_Store_Capabilities.sc_solve b)
             = (SPARQL11_Store.backend_search gb_union b));
          check ~name:(name "estimate")
            ((caps_union.RDF_Store_Capabilities.sc_estimate b)
             = (SPARQL11_Store.backend_estimate gb_union b));
          check ~name:(name "count_exact")
            ((caps_union.RDF_Store_Capabilities.sc_count_exact b)
             = (SPARQL11_Store.backend_count_exact gb_union b)))
        (shapes_of anchor))
    anchors;
  List.iter
    (fun n ->
      let name = Printf.sprintf "union/%s/solve_limited(%s)" label (Z.to_string n) in
      check ~name
        ((caps_union.RDF_Store_Capabilities.sc_solve_limited (bound ()) n)
         = (SPARQL11_Store.backend_search_limited gb_union (bound ()) n)))
    [ Z.zero; Z.one; Z.of_int 2; Z.of_int 3; Z.of_int 4; Z.of_int 5; Z.of_int 100 ];
  List.iter
    (fun pred ->
      check ~name:(Printf.sprintf "union/%s/predicate_present/%s" label pred)
        ((caps_union.RDF_Store_Capabilities.sc_predicate_present pred)
         = (SPARQL11_Store.backend_predicate_present gb_union pred)))
    (p_absent :: known_preds);
  check ~name:(Printf.sprintf "union/%s/decode_failure" label)
    ((caps_union.RDF_Store_Capabilities.sc_decode_failure ())
     = (SPARQL11_Store.backend_decode_failure gb_union))

let () =
  Printf.printf "== store_capabilities_unit ==\n";

  (* ---- In-memory backend ------------------------------------------- *)
  let ig_default = RDF_Indexed.build_indexed default_triples in
  let ig_people = RDF_Indexed.build_indexed people_triples in
  let ig_docs = RDF_Indexed.build_indexed docs_triples in
  let caps_default = RDF_Store_Capabilities.caps_of_indexed ig_default in
  let caps_people = RDF_Store_Capabilities.caps_of_indexed ig_people in
  let caps_docs = RDF_Store_Capabilities.caps_of_indexed ig_docs in

  check_indexed_graph ~label:"default" ~ig:ig_default ~caps:caps_default
    ~anchor:(List.hd default_triples) ~known_pred:p_status;
  check_indexed_graph ~label:"people(named-graph-analog)" ~ig:ig_people ~caps:caps_people
    ~anchor:(List.hd people_triples) ~known_pred:p_name;
  check_indexed_graph ~label:"docs(named-graph-analog)" ~ig:ig_docs ~caps:caps_docs
    ~anchor:(List.hd docs_triples) ~known_pred:p_title;

  (* Flags sanity (cheap, not part of the equivalence matrix but pins
     the builder's documented truth-table, design doc §3.1). *)
  check ~name:"indexed/flags/estimate_is_exact"
    caps_default.RDF_Store_Capabilities.sc_flags.RDF_Store_Capabilities.scf_estimate_is_exact;
  check ~name:"indexed/flags/can_report_decode_fail(false)"
    (not caps_default.RDF_Store_Capabilities.sc_flags.RDF_Store_Capabilities.scf_can_report_decode_fail);
  check ~name:"indexed/flags/supports_update"
    caps_default.RDF_Store_Capabilities.sc_flags.RDF_Store_Capabilities.scf_supports_update;

  (* ---- GB_Union: pure in-memory (people + docs), order preserved ---- *)
  let gb_people = SPARQL11_Store.GB_Indexed ig_people in
  let gb_docs = SPARQL11_Store.GB_Indexed ig_docs in
  let gb_union_mem = SPARQL11_Store.GB_Union [ gb_people; gb_docs ] in
  let caps_union_mem = RDF_Store_Capabilities.union_caps [ caps_people; caps_docs ] in
  check_union_case ~label:"in-memory(people+docs)" ~gb_union:gb_union_mem
    ~caps_union:caps_union_mem
    ~anchors:[ List.hd people_triples; List.hd docs_triples ]
    ~known_preds:[ p_name; p_title ];

  (* ---- COTTAS-on-disk backend --------------------------------------- *)
  let fixture_path = Filename.concat "tests/unit/fixtures" "store_capabilities_sample.cottas" in
  if not (Sys.file_exists fixture_path) then begin
    Printf.printf "  FAIL  fixture missing at %s\n" fixture_path;
    Printf.printf "== summary: %d pass, %d fail (out of %d) ==\n" !passed (!failed + 1) (!passed + !failed + 1);
    exit 1
  end;
  (match RDF_CottasStore.cottas_ondisk_open fixture_path with
   | FStar_Pervasives_Native.None ->
     Printf.printf "  FAIL  cottas_ondisk_open returned None for %s\n" fixture_path;
     incr failed
   | FStar_Pervasives_Native.Some cods ->
     let named_graphs = RDF_CottasStore.cottas_ondisk_named_graphs cods in
     let people_graph_iri =
       match List.find_opt (fun (iri, _) -> contains ~needle:"graph/people" iri) named_graphs with
       | Some (iri, _) -> iri
       | None -> failwith "store_capabilities_unit: no .../graph/people entry in fixture's named-graph inventory"
     in
     let caps_cottas_default = RDF_Store_Capabilities_Cottas.caps_of_cottas cods RDF_CottasStore.COS_DefaultOnly in
     let caps_cottas_people =
       RDF_Store_Capabilities_Cottas.caps_of_cottas cods (RDF_CottasStore.COS_NamedGraph people_graph_iri) in

     (* Anchor triples: whatever the on-disk decoder actually returns for
        an unbound scan of each scope -- avoids hand-guessing the exact
        decoded literal/IRI shapes the dictionary round-trip produces. *)
     let default_anchor =
       match raw_solve cods RDF_CottasStore.COS_DefaultOnly (bound ()) with
       | t :: _ -> t
       | [] -> failwith "store_capabilities_unit: default-graph scope returned zero rows"
     in
     let people_anchor =
       match raw_solve cods (RDF_CottasStore.COS_NamedGraph people_graph_iri) (bound ()) with
       | t :: _ -> t
       | [] -> failwith "store_capabilities_unit: people-graph scope returned zero rows"
     in

     check_cottas_scope ~label:"default" ~cods ~scope:RDF_CottasStore.COS_DefaultOnly
       ~caps:caps_cottas_default ~anchor:default_anchor ~known_pred:p_status;
     check_cottas_scope ~label:"named-graph(people)" ~cods
       ~scope:(RDF_CottasStore.COS_NamedGraph people_graph_iri)
       ~caps:caps_cottas_people ~anchor:people_anchor ~known_pred:p_name;

     check ~name:"cottas/flags/estimate_is_exact(false)"
       (not caps_cottas_default.RDF_Store_Capabilities.sc_flags.RDF_Store_Capabilities.scf_estimate_is_exact);
     check ~name:"cottas/flags/can_report_decode_fail"
       caps_cottas_default.RDF_Store_Capabilities.sc_flags.RDF_Store_Capabilities.scf_can_report_decode_fail;
     check ~name:"cottas/flags/supports_update(false)"
       (not caps_cottas_default.RDF_Store_Capabilities.sc_flags.RDF_Store_Capabilities.scf_supports_update);

     (* ---- GB_Union: mixed indexed + cottas-on-disk, matching the real
        production shape (RDF.Store.Combine.combine_dataset_backends
        unions [in-memory default; cottas-on-disk default, ...] in that
        order for a `--data foo.ttl --data-cottas bar.cottas` CLI
        invocation). Exercises the boundary between a member with NO
        real LIMIT pushdown (indexed) and one WITH it (cottas-on-disk)
        -- exactly the case union_solve_limited_acc's per-member budget
        accounting has to get right. *)
     let gb_mixed = SPARQL11_Store.GB_Union
       [ SPARQL11_Store.GB_Indexed ig_default;
         SPARQL11_Store.GB_CottasOnDisk (cods, RDF_CottasStore.COS_DefaultOnly) ] in
     let caps_mixed = RDF_Store_Capabilities.union_caps [ caps_default; caps_cottas_default ] in
     check_union_case ~label:"mixed(indexed+cottas-ondisk)" ~gb_union:gb_mixed
       ~caps_union:caps_mixed
       ~anchors:[ List.hd default_triples; default_anchor ]
       ~known_preds:[ p_status ]);

  (* ---------------------------------------------------------------- *)
  (* dataset_caps: the U1.5 amendment (owner requirement, 2026-07-06 -- *)
  (* "the db must support full named graphs too, not just triples";    *)
  (* named-graph ROUTING must flow through capability records, not     *)
  (* around the seam). Builds a dataset_backend (default + two named   *)
  (* graphs, reusing this file's existing people/docs/default in-memory*)
  (* fixtures), converts it via SPARQL11_Store.dataset_caps_of_backend,*)
  (* and checks three things:                                          *)
  (*   1. dataset_caps_lookup_named / dataset_caps_list_graphs agree    *)
  (*      with dsb_named's own name list (the graph-backend-level      *)
  (*      resolution the pre-existing evaluator already uses) -- a hit *)
  (*      for every real name in the same order, a miss for an absent  *)
  (*      one.                                                          *)
  (*   2. Per-named-graph solve/estimate/count_exact through the       *)
  (*      dataset_caps composition equal the SAME fields reached via   *)
  (*      lookup_named_backend + backend_search/estimate/count_exact   *)
  (*      (the pre-U2 graph-backend route, itself now a caps_of_backend*)
  (*      forwarder) -- the composition is a faithful additional view, *)
  (*      not a second, drifting implementation.                       *)
  (*   3. A FULL evaluator run (SPARQL11_Store.eval_pattern_backend,   *)
  (*      UNCHANGED by U2) over `GRAPH <iri> { ?s ?p ?o }` and          *)
  (*      `GRAPH ?g { ?s ?p ?o }` produces exactly as many solutions as *)
  (*      the graph has triples (tp_all_var's three pairwise-distinct  *)
  (*      variables mean one solution per triple, no dedup/join to      *)
  (*      confound the count) -- pinning that the REAL GP_Graph        *)
  (*      dispatch path agrees with the dataset_caps view's own counts,*)
  (*      not just that both call the same function in isolation.      *)
  (*                                                                     *)
  (* Deliberately scoped to counts/fields rather than decoding solution *)
  (* mappings term-by-term (this file has no existing helper for that);*)
  (* full binding-level GRAPH coverage already exists via the W3C      *)
  (* SPARQL suite's GRAPH tests and tests/local/                        *)
  (* cottas_row_order_regressions.sh's GRAPH-wrapped checks.            *)
  (* ---------------------------------------------------------------- *)
  let graph_people_iri = "https://example.org/graph/people" in
  let graph_docs_iri = "https://example.org/graph/docs" in
  let graph_absent_iri = "https://example.org/graph/does-not-exist" in
  let tp_all_var : SPARQL11_Algebra.triple_pattern =
    { SPARQL11_Algebra.tp_s = SPARQL11_Algebra.PS_Var "s";
      SPARQL11_Algebra.tp_p = SPARQL11_Algebra.PT_Var "p";
      SPARQL11_Algebra.tp_o = SPARQL11_Algebra.PT_Var "o" } in
  let dsb : SPARQL11_Store.dataset_backend =
    { SPARQL11_Store.dsb_default = SPARQL11_Store.GB_Indexed ig_default;
      SPARQL11_Store.dsb_named =
        [ { SPARQL11_Store.ngb_name = graph_people_iri;
            SPARQL11_Store.ngb_graph = SPARQL11_Store.GB_Indexed ig_people };
          { SPARQL11_Store.ngb_name = graph_docs_iri;
            SPARQL11_Store.ngb_graph = SPARQL11_Store.GB_Indexed ig_docs } ] } in
  let dsc = SPARQL11_Store.dataset_caps_of_backend dsb in

  (* 1. lookup / enumeration round-trip *)
  check ~name:"dataset_caps/list_graphs matches dsb_named order"
    (RDF_Store_Capabilities.dataset_caps_list_graphs dsc.RDF_Store_Capabilities.dsc_named
     = List.map (fun (ngb : SPARQL11_Store.named_graph_backend) -> ngb.SPARQL11_Store.ngb_name)
         dsb.SPARQL11_Store.dsb_named);
  check ~name:"dataset_caps/lookup_named(absent) = None"
    (RDF_Store_Capabilities.dataset_caps_lookup_named graph_absent_iri
       dsc.RDF_Store_Capabilities.dsc_named
     = FStar_Pervasives_Native.None);

  (* 2. per-named-graph field equivalence vs the pre-existing
     graph-backend route (lookup_named_backend plus the backend_search/
     backend_estimate/backend_count_exact forwarders). *)
  List.iter
    (fun (name, ig) ->
      match
        RDF_Store_Capabilities.dataset_caps_lookup_named name dsc.RDF_Store_Capabilities.dsc_named,
        SPARQL11_Store.lookup_named_backend name dsb.SPARQL11_Store.dsb_named
      with
      | FStar_Pervasives_Native.Some caps, FStar_Pervasives_Native.Some gb ->
        List.iter
          (fun (shape_name, b) ->
            let label field = Printf.sprintf "dataset_caps/%s/%s/%s" name shape_name field in
            check ~name:(label "solve")
              ((caps.RDF_Store_Capabilities.sc_solve b) = (SPARQL11_Store.backend_search gb b));
            check ~name:(label "estimate")
              ((caps.RDF_Store_Capabilities.sc_estimate b) = (SPARQL11_Store.backend_estimate gb b));
            check ~name:(label "count_exact")
              ((caps.RDF_Store_Capabilities.sc_count_exact b)
               = (SPARQL11_Store.backend_count_exact gb b)))
          (shapes_of (List.hd (SPARQL11_Algebra.ig_search ig (bound ()))))
      | _ -> check ~name:(Printf.sprintf "dataset_caps/%s/lookup agrees" name) false)
    [ (graph_people_iri, ig_people); (graph_docs_iri, ig_docs) ];

  (* 3. full evaluator: GRAPH <iri> { ?s ?p ?o } and GRAPH ?g { ?s ?p ?o }
     produce as many solutions as the graph has triples. *)
  let gp_graph_const name =
    SPARQL11_Algebra.GP_Graph (SPARQL11_Algebra.PT_IRI name, SPARQL11_Algebra.GP_BGP [ tp_all_var ]) in
  let gp_graph_var =
    SPARQL11_Algebra.GP_Graph (SPARQL11_Algebra.PT_Var "g", SPARQL11_Algebra.GP_BGP [ tp_all_var ]) in
  let placeholder_gb = SPARQL11_Store.GB_Indexed ig_default in
  List.iter
    (fun (name, ig) ->
      let n_solutions =
        List.length
          (SPARQL11_Store.eval_pattern_backend FStar_Pervasives_Native.None (gp_graph_const name)
             placeholder_gb dsb) in
      let n_triples = List.length (SPARQL11_Algebra.ig_search ig (bound ())) in
      check ~name:(Printf.sprintf "dataset_caps/eval/GRAPH<%s>/solution-count" name)
        (n_solutions = n_triples))
    [ (graph_people_iri, ig_people); (graph_docs_iri, ig_docs) ];
  let n_solutions_var =
    List.length
      (SPARQL11_Store.eval_pattern_backend FStar_Pervasives_Native.None gp_graph_var placeholder_gb
         dsb) in
  let n_triples_total =
    List.length (SPARQL11_Algebra.ig_search ig_people (bound ()))
    + List.length (SPARQL11_Algebra.ig_search ig_docs (bound ())) in
  check ~name:"dataset_caps/eval/GRAPH?g/solution-count" (n_solutions_var = n_triples_total);

  Printf.printf "== summary: %d pass, %d fail (out of %d) ==\n" !passed !failed (!passed + !failed);
  if !failed = 0 then exit 0 else exit 1
