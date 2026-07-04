(* lifesci_closure_timing.ml — instrumentation probe for
   docs/designissues/2026-07-04-lifesci-demo-entailment-perf.md task #36.

   Times the individual phases of one rdfs_closure_step
   (build_indexed / rule-chain / graph_dedup_sort) and the iteration
   count + per-iteration wall time of rdfs_closure_with_reflexivity, on
   the real lifesci fixture data (docs/fstar-extracted/lifesci/*.ttl).

   Goal: confirm or refute the hypothesis that build_indexed's six
   List.Tot.sortWith passes (each keyed by a comparator that
   RECOMPUTES the key string from scratch on every comparison, instead
   of a decorate-sort-undecorate pass) dominate the ~41-56s per-query
   RDFS cost documented in the diagnosis doc, on data with zero
   subClassOf/subPropertyOf/domain/range triples (so the rule chain
   itself should be near-free).

   This uses only the ALREADY-EXTRACTED formal/fstar/ocaml-output
   (no build-ocaml.sh invocation — CLAUDE.md task constraint). It will
   not reflect the uncommitted g18a/g25a rules; that's fine, this probe
   only measures build_indexed / graph_dedup_sort / rule-chain phases
   that are common to before and after this session's edit. *)

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
  Printf.printf "  [%-40s] %8.3fs\n%!" label dt;
  (r, dt)

let fixture_dir = "docs/fstar-extracted/lifesci"

let load name =
  let path = Filename.concat fixture_dir (name ^ ".ttl") in
  let ttl = read_file path in
  let (triples, dt) =
    time_it (Printf.sprintf "parse %s" name)
      (fun () -> Parser_Turtle.parse_turtle_with_base ttl (Printf.sprintf "file:///%s.ttl" name))
  in
  ignore dt;
  Printf.printf "  %s: %d triples\n%!" name (List.length triples);
  triples

(* Manual step-by-step fixpoint loop so we can print (iteration, len,
   wall time) instead of only the final converged result — the doc's
   open question is whether cost is one expensive step repeated few
   times, or many iterations. *)
let manual_rdfs_closure_loop label g0 max_iters =
  Printf.printf "-- %s: manual rdfs_closure_step loop (cap %d iters) --\n%!" label max_iters;
  let g = ref g0 in
  let prev_len = ref (List.length g0) in
  let converged = ref false in
  let i = ref 0 in
  while not !converged && !i < max_iters do
    incr i;
    let (g', dt) = time_it (Printf.sprintf "iter %2d rdfs_closure_step" !i)
      (fun () -> RDF_Graph_Executable.rdfs_closure_step !g) in
    let len' = List.length g' in
    Printf.printf "      iter %2d: len %d -> %d (delta %+d) in %.3fs\n%!"
      !i !prev_len len' (len' - !prev_len) dt;
    if len' = !prev_len then converged := true
    else begin g := g'; prev_len := len' end
  done;
  if !converged then Printf.printf "  converged after %d iteration(s)\n\n%!" !i
  else Printf.printf "  DID NOT CONVERGE within %d iterations\n\n%!" max_iters

let phase_breakdown label g =
  Printf.printf "-- %s: single rdfs_closure_step phase breakdown --\n%!" label;
  let (ig, _) = time_it "build_indexed (6 sortWith passes)" (fun () -> RDF_Graph_Executable.build_indexed g) in
  let (g1, _) = time_it "rdfs_rule_subPropertyOf" (fun () -> RDF_Graph_Executable.rdfs_rule_subPropertyOf g ig) in
  let (g2, _) = time_it "rdfs_rule_domain" (fun () -> RDF_Graph_Executable.rdfs_rule_domain g1 ig) in
  let (g3, _) = time_it "rdfs_rule_range" (fun () -> RDF_Graph_Executable.rdfs_rule_range g2 ig) in
  let (g4, _) = time_it "rdfs_rule_subClassOf" (fun () -> RDF_Graph_Executable.rdfs_rule_subClassOf g3 ig) in
  let (g5, _) = time_it "rdfs_rule_container_membership" (fun () -> RDF_Graph_Executable.rdfs_rule_container_membership g4 ig) in
  let (g6, _) = time_it "rdfs_rule_subClassOf_trans" (fun () -> RDF_Graph_Executable.rdfs_rule_subClassOf_trans g5 ig) in
  let (g7, _) = time_it "rdfs_rule_subPropertyOf_trans" (fun () -> RDF_Graph_Executable.rdfs_rule_subPropertyOf_trans g6 ig) in
  let (gd, _) = time_it "graph_dedup_sort" (fun () -> RDF_Graph_Executable.graph_dedup_sort g7) in
  Printf.printf "  final: %d -> %d triples\n\n%!" (List.length g) (List.length gd)

let () =
  Printf.printf "=== lifesci_closure_timing: RDFS closure fixed-overhead probe ===\n\n%!";
  let chromosome = load "chromosome" in
  let sequence_variant = load "sequence_variant" in
  let disease = load "disease" in
  Printf.printf "\n";

  phase_breakdown "sequence_variant (6455 triples)" sequence_variant;
  phase_breakdown "chromosome (9227 triples)" chromosome;
  phase_breakdown "disease (27421 triples)" disease;

  manual_rdfs_closure_loop "sequence_variant" sequence_variant 6;
  manual_rdfs_closure_loop "disease" disease 6;

  let (full, dt) = time_it "rdfs_closure_with_reflexivity(disease, fuel=100)"
    (fun () -> RDF_Graph_Executable.rdfs_closure_with_reflexivity disease (Z.of_int 100)) in
  Printf.printf "  disease: %d -> %d triples in %.3fs\n%!"
    (List.length disease) (List.length full) dt;

  Printf.printf "\nsummary: probe complete (no pass/fail assertions — instrumentation only)\n%!";
  exit 0
