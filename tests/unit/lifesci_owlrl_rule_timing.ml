(* lifesci_owlrl_rule_timing.ml — per-rule timing bisect for OWL-RL on
   real lifesci data (task #36, docs/designissues/2026-07-04-lifesci-
   demo-entailment-perf.md §3.1 cap-trip). Same technique as
   tests/unit/owl_rl_bisect.ml (SIGALRM cap per rule), but driven off
   the real 6455/9227/27421-triple lifesci fixtures instead of the tiny
   simple.ttl entailment-suite fixture, to find which of the ~28
   extracted OWL-RL rules dominates cost on schema-free data-scale
   graphs (zero owl:sameAs / subClassOf / subPropertyOf / domain /
   range / Restriction triples).

   Uses only the already-extracted formal/fstar/ocaml-output (no
   build-ocaml.sh invocation). *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.unsafe_to_string s

let per_rule_cap = 20.0

let pass = ref 0
let xfail = ref 0

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

let probe name f =
  Printf.printf "  testing %-44s ... %!" name;
  let t0 = Unix.gettimeofday () in
  match with_cap per_rule_cap f with
  | Some r ->
    let dt = Unix.gettimeofday () -. t0 in
    Printf.printf "PASS  %6d triples  (%7.3fs)\n%!" (List.length r) dt;
    incr pass
  | None ->
    Printf.printf "XFAIL did not return within %.0fs\n%!" per_rule_cap;
    incr xfail

let () =
  let name = if Array.length Sys.argv > 1 then Sys.argv.(1) else "sequence_variant" in
  let path = Printf.sprintf "docs/fstar-extracted/lifesci/%s.ttl" name in
  let ttl = read_file path in
  let triples = Parser_Turtle.parse_turtle_with_base ttl (Printf.sprintf "file:///%s.ttl" name) in
  Printf.printf "Input g0 (%s): %d triples\n%!" name (List.length triples);

  let t0 = Unix.gettimeofday () in
  let g1a = RDF_Graph_Executable.rdfs_closure_with_reflexivity triples (Z.of_int 100) in
  Printf.printf "g1a = rdfs_closure_with_reflexivity(g0, fuel=100): %d triples (%.3fs)\n%!"
    (List.length g1a) (Unix.gettimeofday () -. t0);

  (* Optional --grow N: apply N rounds of (owl_rl_closure_step;
     rdfs_closure_step) before the per-rule bisect, so we're profiling
     rules on the POST-growth graph (after the owl:Thing/universal-axiom
     one-time doubling seen in lifesci_owlrl_loop_timing), not the small
     pre-growth graph where every rule looks cheap because it hasn't
     seen the larger effective N yet. *)
  let grow_rounds =
    if Array.length Sys.argv > 2 && Sys.argv.(2) = "--grow"
    then (if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 1)
    else 0
  in
  let g1 = ref g1a in
  for r = 1 to grow_rounds do
    let t0 = Unix.gettimeofday () in
    let g_owl = RDF_Graph_Executable.owl_rl_closure_step !g1 in
    let g_rdfs = RDF_Graph_Executable.rdfs_closure_step g_owl in
    Printf.printf "grow round %d: %d -> %d triples (%.3fs)\n%!"
      r (List.length !g1) (List.length g_rdfs) (Unix.gettimeofday () -. t0);
    g1 := g_rdfs
  done;
  let g1 = !g1 in
  Printf.printf "\n";

  Printf.printf "Per-rule timing on g1 (%d triples, cap=%.0fs each):\n%!" (List.length g1) per_rule_cap;

  let (ig, dt) =
    let t0 = Unix.gettimeofday () in
    let r = RDF_Graph_Executable.build_indexed g1 in
    (r, Unix.gettimeofday () -. t0)
  in
  Printf.printf "  build_indexed: %.3fs\n\n%!" dt;

  probe "equivalent_class"               (fun () -> RDF_Graph_Executable.owl_rule_equivalent_class g1 ig);
  probe "equivalent_property"            (fun () -> RDF_Graph_Executable.owl_rule_equivalent_property g1 ig);
  probe "scm_eqc2"                       (fun () -> RDF_Graph_Executable.owl_rule_scm_eqc2 g1 ig);
  probe "scm_eqp2"                       (fun () -> RDF_Graph_Executable.owl_rule_scm_eqp2 g1 ig);
  probe "inverse_of"                     (fun () -> RDF_Graph_Executable.owl_rule_inverse_of g1 ig);
  probe "disjoint_with_propagation"      (fun () -> RDF_Graph_Executable.owl_rule_disjoint_with_propagation g1 ig);
  probe "inverseOf_domain_range_flip"    (fun () -> RDF_Graph_Executable.owl_rule_inverseOf_domain_range_flip g1 ig);
  probe "symmetric_property"             (fun () -> RDF_Graph_Executable.owl_rule_symmetric_property g1 ig);
  probe "transitive_property"            (fun () -> RDF_Graph_Executable.owl_rule_transitive_property g1 ig);
  probe "named_equivClass_to_sameAs"     (fun () -> RDF_Graph_Executable.owl_rule_named_equivClass_to_sameAs g1 ig);
  probe "sameAs_reflexivity"             (fun () -> RDF_Graph_Executable.owl_rule_sameAs_reflexivity g1 ig);
  probe "sameAs_symmetry"                (fun () -> RDF_Graph_Executable.owl_rule_sameAs_symmetry g1 ig);
  probe "differentFrom_symmetry"         (fun () -> RDF_Graph_Executable.owl_rule_differentFrom_symmetry g1 ig);
  probe "sameAs_transitivity"            (fun () -> RDF_Graph_Executable.owl_rule_sameAs_transitivity g1 ig);
  probe "sameAs_replace_subject"         (fun () -> RDF_Graph_Executable.owl_rule_sameAs_replace_subject g1 ig);
  probe "sameAs_replace_object"          (fun () -> RDF_Graph_Executable.owl_rule_sameAs_replace_object g1 ig);
  probe "sameAs_replace_predicate"       (fun () -> RDF_Graph_Executable.owl_rule_sameAs_replace_predicate g1 ig);
  probe "functional"                     (fun () -> RDF_Graph_Executable.owl_rule_functional g1 ig);
  probe "inverse_functional"             (fun () -> RDF_Graph_Executable.owl_rule_inverse_functional g1 ig);
  probe "pdw_to_differentFrom"           (fun () -> RDF_Graph_Executable.owl_rule_pdw_to_differentFrom g1 ig);
  probe "fp_diff_to_diff"                (fun () -> RDF_Graph_Executable.owl_rule_fp_diff_to_diff g1 ig);
  probe "ifp_diff_to_diff"               (fun () -> RDF_Graph_Executable.owl_rule_ifp_diff_to_diff g1 ig);
  probe "minc1_bridge"                   (fun () -> RDF_Graph_Executable.owl_rule_minc1_bridge g1 ig);
  probe "svf2_existential_witness"       (fun () -> RDF_Graph_Executable.owl_rule_svf2_existential_witness g1 ig);
  probe "cls_svf2_qualified"             (fun () -> RDF_Graph_Executable.owl_rule_cls_svf2_qualified g1 ig);
  probe "cls_minc_qual1"                 (fun () -> RDF_Graph_Executable.owl_rule_cls_minc_qual1 g1 ig);
  probe "cls_maxqc1"                     (fun () -> RDF_Graph_Executable.owl_rule_cls_maxqc1 g1 ig);
  probe "cls_exactqc1"                   (fun () -> RDF_Graph_Executable.owl_rule_cls_exactqc1 g1 ig);
  probe "cls_maxc2"                      (fun () -> RDF_Graph_Executable.owl_rule_cls_maxc2 g1 ig);
  probe "cls_avf1"                       (fun () -> RDF_Graph_Executable.owl_rule_cls_avf1 g1 ig);
  probe "reflexive_property"             (fun () -> RDF_Graph_Executable.owl_rule_reflexive_property g1 ig);
  probe "scm_cls_restriction"            (fun () -> RDF_Graph_Executable.owl_rule_scm_cls_restriction g1 ig);
  probe "property_chain_2"               (fun () -> RDF_Graph_Executable.owl_rule_property_chain_2 g1 ig);
  probe "property_chain_n"               (fun () -> RDF_Graph_Executable.owl_rule_property_chain_n g1 ig);
  probe "chain_to_transitive"            (fun () -> RDF_Graph_Executable.owl_rule_chain_to_transitive g1 ig);
  probe "named_sameAs_to_equivClass"     (fun () -> RDF_Graph_Executable.owl_rule_named_sameAs_to_equivClass g1 ig);
  probe "prp_key"                        (fun () -> RDF_Graph_Executable.owl_rule_prp_key g1 ig);
  probe "xsd_datatype_axioms"            (fun () -> RDF_Graph_Executable.owl_rule_xsd_datatype_axioms g1 ig);
  probe "scm_dom2"                       (fun () -> RDF_Graph_Executable.owl_rule_scm_dom2 g1 ig);
  probe "scm_rng2"                       (fun () -> RDF_Graph_Executable.owl_rule_scm_rng2 g1 ig);

  Printf.printf "\nsummary: %d pass, %d expected-fail (suspect rule(s)) (out of %d)\n"
    !pass !xfail (!pass + !xfail);
  exit 0
