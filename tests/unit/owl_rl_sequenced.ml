(* owl_rl_sequenced.ml — sequenced-rule timing for #262.

   owl_rl_bisect.ml showed every rule terminates in 0-1ms on g1
   independently. The blow-up must be in the sequential interaction
   inside owl_rl_closure_step.

   This test mirrors owl_rl_closure_step's exact rule sequence but
   times each step on its actual cumulative input (rule N runs on
   rule N-1's output, not on g1). Each step is capped at 10s.

   The first cap that fires (or the first step whose output grows
   non-trivially) localises the rule pair responsible. *)

let simple_ttl_path =
  "third_party/testing/w3c/sparql/sparql11/entailment/simple.ttl"

let per_step_cap = 10.0
let fuel : Prims.nat = Z.of_int 100

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

(* Build an indexed_graph from g, then run rule(g, ig). The index is
   rebuilt at each step to match owl_rl_closure_step's behaviour
   (the index is built once per closure-step, but we want each rule
   timing to be self-contained for clarity). *)
let step name g rule =
  let n_in = List.length g in
  Printf.printf "  step %-32s (in=%d) %!" name n_in;
  let t0 = Unix.gettimeofday () in
  let result = with_cap per_step_cap (fun () ->
    let ig = RDF_Graph_Executable.build_indexed g in
    rule g ig)
  in
  let dt = Unix.gettimeofday () -. t0 in
  match result with
  | Some g' ->
    let n_out = List.length g' in
    let delta = n_out - n_in in
    let tag = if delta = 0 then "[unchanged]"
              else if delta > 100 then Printf.sprintf "[+%d !]" delta
              else Printf.sprintf "[+%d]" delta
    in
    Printf.printf "%.3fs -> %d %s\n%!" dt n_out tag;
    incr pass;
    g'
  | None ->
    Printf.printf "XFAIL did not return within %.0fs (this is the suspect rule pair)\n%!" per_step_cap;
    incr xfail;
    g

let () =
  let ttl = read_file simple_ttl_path in
  let triples = Parser_Turtle.parse_turtle_with_base ttl "file:///simple.ttl" in
  Printf.printf "Input g0: %d triples\n%!" (List.length triples);

  let g1 = RDF_Graph_Executable.owl_rl_closure_with_reflexivity triples (Z.of_int 1) in
  Printf.printf "g1 = closure(g0, fuel=1): %d triples\n\n" (List.length g1);
  Printf.printf "Sequenced timing through owl_rl_closure_step's 28 rules (cap=%.0fs each):\n" per_step_cap;

  (* Mirrors RDF.Graph.Executable.fst owl_rl_closure_step. Each step
     consumes the previous step's output. *)
  let g = g1 in
  let g = step "equivalent_class"               g RDF_Graph_Executable.owl_rule_equivalent_class in
  let g = step "equivalent_property"            g RDF_Graph_Executable.owl_rule_equivalent_property in
  let g = step "scm_eqc2"                       g RDF_Graph_Executable.owl_rule_scm_eqc2 in
  let g = step "scm_eqp2"                       g RDF_Graph_Executable.owl_rule_scm_eqp2 in
  let g = step "inverse_of"                     g RDF_Graph_Executable.owl_rule_inverse_of in
  let g = step "disjoint_with_propagation"      g RDF_Graph_Executable.owl_rule_disjoint_with_propagation in
  let g = step "inverseOf_domain_range_flip"    g RDF_Graph_Executable.owl_rule_inverseOf_domain_range_flip in
  let g = step "symmetric_property"             g RDF_Graph_Executable.owl_rule_symmetric_property in
  let g = step "transitive_property"            g RDF_Graph_Executable.owl_rule_transitive_property in
  let g = step "named_equivClass_to_sameAs"     g RDF_Graph_Executable.owl_rule_named_equivClass_to_sameAs in
  let g = step "sameAs_reflexivity"             g RDF_Graph_Executable.owl_rule_sameAs_reflexivity in
  let g = step "sameAs_symmetry"                g RDF_Graph_Executable.owl_rule_sameAs_symmetry in
  let g = step "differentFrom_symmetry"         g RDF_Graph_Executable.owl_rule_differentFrom_symmetry in
  let g = step "sameAs_transitivity"            g RDF_Graph_Executable.owl_rule_sameAs_transitivity in
  let g = step "sameAs_replace_subject"         g RDF_Graph_Executable.owl_rule_sameAs_replace_subject in
  let g = step "sameAs_replace_object"          g RDF_Graph_Executable.owl_rule_sameAs_replace_object in
  let g = step "sameAs_replace_predicate"       g RDF_Graph_Executable.owl_rule_sameAs_replace_predicate in
  let g = step "functional"                     g RDF_Graph_Executable.owl_rule_functional in
  let g = step "inverse_functional"             g RDF_Graph_Executable.owl_rule_inverse_functional in
  let g = step "pdw_to_differentFrom"           g RDF_Graph_Executable.owl_rule_pdw_to_differentFrom in
  let g = step "fp_diff_to_diff"                g RDF_Graph_Executable.owl_rule_fp_diff_to_diff in
  let g = step "ifp_diff_to_diff"               g RDF_Graph_Executable.owl_rule_ifp_diff_to_diff in
  let g = step "minc1_bridge"                   g RDF_Graph_Executable.owl_rule_minc1_bridge in
  let g = step "svf2_existential_witness"       g RDF_Graph_Executable.owl_rule_svf2_existential_witness in
  let g = step "cls_svf2_qualified"             g RDF_Graph_Executable.owl_rule_cls_svf2_qualified in
  let g = step "cls_minc_qual1"                 g RDF_Graph_Executable.owl_rule_cls_minc_qual1 in
  let g = step "cls_maxqc1"                     g RDF_Graph_Executable.owl_rule_cls_maxqc1 in
  let g = step "cls_exactqc1"                   g RDF_Graph_Executable.owl_rule_cls_exactqc1 in
  let g = step "cls_maxc2"                      g RDF_Graph_Executable.owl_rule_cls_maxc2 in
  let g = step "cls_avf1"                       g RDF_Graph_Executable.owl_rule_cls_avf1 in
  let g = step "reflexive_property"             g RDF_Graph_Executable.owl_rule_reflexive_property in
  let g = step "scm_cls_restriction"            g RDF_Graph_Executable.owl_rule_scm_cls_restriction in
  let g = step "property_chain_2"               g RDF_Graph_Executable.owl_rule_property_chain_2 in
  let g = step "property_chain_n"               g RDF_Graph_Executable.owl_rule_property_chain_n in
  let g = step "chain_to_transitive"            g RDF_Graph_Executable.owl_rule_chain_to_transitive in
  let g = step "named_sameAs_to_equivClass"     g RDF_Graph_Executable.owl_rule_named_sameAs_to_equivClass in
  let g = step "prp_key"                        g RDF_Graph_Executable.owl_rule_prp_key in
  let g = step "xsd_datatype_axioms"            g RDF_Graph_Executable.owl_rule_xsd_datatype_axioms in
  let g = step "scm_dom2"                       g RDF_Graph_Executable.owl_rule_scm_dom2 in
  let _g = step "scm_rng2"                       g RDF_Graph_Executable.owl_rule_scm_rng2 in

  Printf.printf "\nsummary: %d pass, %d capped\n" !pass !xfail;
  exit 0
