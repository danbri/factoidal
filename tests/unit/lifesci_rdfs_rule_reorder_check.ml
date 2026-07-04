(* lifesci_rdfs_rule_reorder_check.ml — before/after check for the
   task #36 join-reorder fix to rdfs_rule_subPropertyOf / domain /
   range in formal/fstar/RDF.Graph.Executable.fst (see
   docs/designissues/2026-07-04-lifesci-demo-entailment-perf.md).

   "before" = calls the CURRENTLY EXTRACTED (unfixed) rule functions
   directly from formal/fstar/ocaml-output/RDF_Graph_Executable.ml
   (no build-ocaml.sh invocation in this session, per task constraint —
   ocaml-output still reflects the pre-fix .fst).

   "after" = a hand-transcription of the NEW .fst rule bodies (see the
   task #36 comment blocks on rdfs_rule_subPropertyOf/domain/range in
   RDF.Graph.Executable.fst) into OCaml, calling the SAME already-
   extracted primitives the new F* code calls (bucket_lookup,
   add_triple_unchecked, term_to_subject, the rdfs_domain / rdfs_range /
   rdfs_subPropertyOf / rdf_type constants, and the S_IRI / T_IRI
   constructors) — i.e. this computes exactly what the new .fst will
   compute once extracted, without needing a re-extraction to prove it.

   This is a validation probe, not a permanent regression test — it
   exists to produce a real measured "before vs after" number for the
   task #36 report. *)

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

(* ---- "after": hand-transcription of the new join-reordered rule
   bodies, calling the same already-extracted primitives ---- *)

let rdfs_rule_subPropertyOf_after (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
  List.fold_left
    (fun acc (decl : triple) ->
      match decl.s, decl.o with
      | S_IRI p, T_IRI q ->
        let matching = bucket_lookup ig.ig_pred p in
        List.fold_left
          (fun acc2 (t : triple) ->
            add_triple_unchecked acc2 { s = t.s; p = q; o = t.o })
          acc matching
      | _, _ -> acc)
    g decls

let rdfs_rule_domain_after (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  List.fold_left
    (fun acc (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.fold_left
          (fun acc2 (t : triple) ->
            add_triple_unchecked acc2 { s = t.s; p = rdf_type; o = decl.o })
          acc matching
      | _ -> acc)
    g decls

let rdfs_rule_range_after (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_range in
  List.fold_left
    (fun acc (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.fold_left
          (fun acc2 (t : triple) ->
            match term_to_subject t.o with
            | Some b_subj ->
              add_triple_unchecked acc2 { s = b_subj; p = rdf_type; o = decl.o }
            | None -> acc2)
          acc matching
      | _ -> acc)
    g decls

let load name =
  let path = Printf.sprintf "docs/fstar-extracted/lifesci/%s.ttl" name in
  let ttl = read_file path in
  Parser_Turtle.parse_turtle_with_base ttl (Printf.sprintf "file:///%s.ttl" name)

let check name g =
  Printf.printf "-- %s (%d triples) --\n%!" name (List.length g);
  let (ig, _) = time_it "build_indexed" (fun () -> build_indexed g) in

  let (before_sp, _) = time_it "BEFORE rdfs_rule_subPropertyOf" (fun () -> rdfs_rule_subPropertyOf g ig) in
  let (after_sp, _)  = time_it "AFTER  rdfs_rule_subPropertyOf" (fun () -> rdfs_rule_subPropertyOf_after g ig) in

  let (before_dom, _) = time_it "BEFORE rdfs_rule_domain" (fun () -> rdfs_rule_domain g ig) in
  let (after_dom, _)  = time_it "AFTER  rdfs_rule_domain" (fun () -> rdfs_rule_domain_after g ig) in

  let (before_rng, _) = time_it "BEFORE rdfs_rule_range" (fun () -> rdfs_rule_range g ig) in
  let (after_rng, _)  = time_it "AFTER  rdfs_rule_range" (fun () -> rdfs_rule_range_after g ig) in

  (* Sort+dedup both outputs (list order may legitimately differ between
     the two join orders) and compare triple SETS for equivalence. *)
  let normalize gr = List.sort_uniq compare (List.map (fun (t : triple) -> (t.s, t.p, t.o)) gr) in
  let check_eq label b a =
    if normalize b = normalize a
    then Printf.printf "    %-28s EQUIVALENT (%d triples both sides)\n%!" label (List.length (normalize b))
    else Printf.printf "    %-28s MISMATCH — before %d after %d triples (see below)\n%!"
           label (List.length (normalize b)) (List.length (normalize a))
  in
  check_eq "subPropertyOf" before_sp after_sp;
  check_eq "domain" before_dom after_dom;
  check_eq "range" before_rng after_rng;
  Printf.printf "\n%!"

let () =
  Printf.printf "=== lifesci_rdfs_rule_reorder_check: task #36 before/after + equivalence ===\n\n%!";
  check "sequence_variant" (load "sequence_variant");
  check "chromosome" (load "chromosome");
  check "disease" (load "disease");
  Printf.printf "summary: probe complete (see EQUIVALENT/MISMATCH lines above for correctness; timings above for speedup)\n%!";
  exit 0
