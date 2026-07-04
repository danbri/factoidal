(* lifesci_owlrl_rule_reorder_check.ml — before/after check for the
   task #36 vocab-guard fix to owl_rule_reflexive_property and
   owl_rule_property_chain_n in formal/fstar/RDF.Graph.Executable.fst
   (docs/designissues/2026-07-04-lifesci-demo-entailment-perf.md).

   Same method as lifesci_rdfs_rule_reorder_check.ml: "before" calls the
   currently-extracted (unfixed) rule bodies; "after" hand-transcribes
   the new guarded bodies using the same already-extracted primitives,
   run on the POST-GROWTH graph (after one owl_rl_closure_step +
   rdfs_closure_step round) where these rules showed their largest
   measured cost (1.879s / 0.393s on the 18480-triple grown chromosome
   fixture). *)

open RDF_Graph_Executable

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.unsafe_to_string s

let time_it label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf "  [%-46s] %8.3fs\n%!" label dt;
  (r, dt)

let owl_ReflexiveProperty = "http://www.w3.org/2002/07/owl#ReflexiveProperty"

let cons_if_new_iri (p : wf_iri) (acc : wf_iri list) : wf_iri list =
  if List.mem p acc then acc else p :: acc

let owl_rule_reflexive_property_after (g : rdf_graph) (_ig : indexed_graph) : rdf_graph =
  let refl_props =
    List.fold_left
      (fun acc (t : triple) ->
        if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_ReflexiveProperty) then
          match t.s with S_IRI p_iri -> cons_if_new_iri p_iri acc | _ -> acc
        else acc)
      [] g
  in
  match refl_props with
  | [] -> g
  | _ ->
    let indivs = prp_rfl_individuals g in
    List.fold_left
      (fun acc p_iri ->
        List.fold_left
          (fun acc2 x -> add_triple_unchecked acc2 { s = S_IRI x; p = p_iri; o = T_IRI x })
          acc indivs)
      g refl_props

let owl_propertyChainAxiom = "http://www.w3.org/2002/07/owl#propertyChainAxiom"

let owl_rule_property_chain_n_after (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let chain_decls = bucket_lookup ig.ig_pred owl_propertyChainAxiom in
  match chain_decls with
  | [] -> g
  | _ ->
    let starting_subjects =
      List.fold_left
        (fun acc (t : triple) ->
          if List.exists (fun s -> subject_eq s t.s) acc then acc else t.s :: acc)
        [] g
    in
    List.fold_left
      (fun acc (chain_t : triple) ->
        if chain_t.p = owl_propertyChainAxiom then
          match chain_t.s, term_to_subject chain_t.o with
          | S_IRI p_iri, Some list_subj ->
            (match decode_chain_list g ig list_subj with
             | Some chain ->
               if List.length chain >= 2 then
                 List.fold_left
                   (fun acc1 x ->
                     let zs = find_chain_endpoints g ig chain x in
                     List.fold_left
                       (fun acc2 z_term -> add_triple_unchecked acc2 { s = x; p = p_iri; o = z_term })
                       acc1 zs)
                   acc starting_subjects
               else acc
             | None -> acc)
          | _, _ -> acc
        else acc)
      g g

let load name =
  let path = Printf.sprintf "docs/fstar-extracted/lifesci/%s.ttl" name in
  let ttl = read_file path in
  Parser_Turtle.parse_turtle_with_base ttl (Printf.sprintf "file:///%s.ttl" name)

let normalize gr = List.sort_uniq compare (List.map (fun (t : triple) -> (t.s, t.p, t.o)) gr)
let check_eq label b a =
  if normalize b = normalize a
  then Printf.printf "    %-28s EQUIVALENT (%d triples both sides)\n%!" label (List.length (normalize b))
  else Printf.printf "    %-28s MISMATCH — before %d after %d triples\n%!"
         label (List.length (normalize b)) (List.length (normalize a))

let () =
  Printf.printf "=== lifesci_owlrl_rule_reorder_check: task #36 before/after + equivalence ===\n\n%!";
  let chromosome = load "chromosome" in
  Printf.printf "chromosome: %d triples\n%!" (List.length chromosome);
  let (rdfs_closed, _) = time_it "rdfs_closure_with_reflexivity" (fun () ->
    rdfs_closure_with_reflexivity chromosome (Z.of_int 100)) in
  let (grown, _) = time_it "one owl_step+rdfs_step round (grow)" (fun () ->
    let g_owl = owl_rl_closure_step rdfs_closed in
    rdfs_closure_step g_owl) in
  Printf.printf "grown graph: %d triples\n\n%!" (List.length grown);

  let ig = build_indexed grown in

  let (before_refl, _) = time_it "BEFORE owl_rule_reflexive_property" (fun () -> owl_rule_reflexive_property grown ig) in
  let (after_refl, _)  = time_it "AFTER  owl_rule_reflexive_property" (fun () -> owl_rule_reflexive_property_after grown ig) in
  check_eq "reflexive_property" before_refl after_refl;

  let (before_chain, _) = time_it "BEFORE owl_rule_property_chain_n" (fun () -> owl_rule_property_chain_n grown ig) in
  let (after_chain, _)  = time_it "AFTER  owl_rule_property_chain_n" (fun () -> owl_rule_property_chain_n_after grown ig) in
  check_eq "property_chain_n" before_chain after_chain;

  Printf.printf "\nsummary: probe complete\n%!";
  exit 0
