(* owl_rl_bisect.ml — bisect which OWL-RL rule blows up on the
   207-triple step-1 output of `entailment/simple1`.

   Calls each of the 28 rules independently on g1 (= owl_rl_closure_step
   on the simple.ttl input) with a SIGALRM cap. Each rule that returns
   reports its emit count + delta. The rule(s) that hit the cap are the
   suspects. *)

let simple_ttl_path =
  "third_party/testing/w3c/sparql/sparql11/entailment/simple.ttl"

let per_rule_cap = 10.0

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

let probe name f =
  Printf.printf "  testing %-44s ... %!" name;
  let t0 = Unix.gettimeofday () in
  match with_cap per_rule_cap f with
  | Some r ->
    let dt = Unix.gettimeofday () -. t0 in
    Printf.printf "PASS  %5d triples  (%.3fs)\n%!" (List.length r) dt;
    incr pass
  | None ->
    Printf.printf "XFAIL did not return within %.0fs\n%!" per_rule_cap;
    incr xfail

let () =
  let ttl = read_file simple_ttl_path in
  let triples = Parser_Turtle.parse_turtle_with_base ttl "file:///simple.ttl" in
  Printf.printf "Input g0: %d triples\n%!" (List.length triples);

  let g1 = RDF_Graph_Executable.owl_rl_closure_with_reflexivity triples (Z.of_int 1) in
  Printf.printf "g1 = closure(g0, fuel=1): %d triples\n\n" (List.length g1);
  Printf.printf "Per-rule timing on g1 (cap=%.0fs each):\n" per_rule_cap;

  let ig = RDF_Graph_Executable.build_indexed g1 in

  (* All 28 rules called on (g1, ig). Order matches owl_rl_closure_step. *)
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

  Printf.printf "\nsummary: %d pass, %d expected-fail (suspect rule(s))\n" !pass !xfail;
  exit 0
