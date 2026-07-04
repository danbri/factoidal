(* lifesci_owlrl_loop_timing.ml — manual owl_rl_closure fixpoint loop
   with per-iteration (len, wall time) printed, to distinguish "many
   iterations needed" from "one iteration is just very expensive" as
   the mechanism behind the >590s OWL-RL cap-trip in
   docs/designissues/2026-07-04-lifesci-demo-entailment-perf.md §3.1.

   Mirrors owl_rl_closure's own loop body (owl_rl_closure_step then
   rdfs_closure_step, compare length to the START of the iteration) but
   prints after every iteration and stops on a wall-clock budget instead
   of only a fuel count, so a slow-but-converging run is distinguishable
   from a truly runaway one within this probe's time budget.

   Usage: lifesci_owlrl_loop_timing <fixture-name> <max-iters> <budget-seconds> *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.unsafe_to_string s

let () =
  let name = if Array.length Sys.argv > 1 then Sys.argv.(1) else "sequence_variant" in
  let max_iters = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 10 in
  let budget = if Array.length Sys.argv > 3 then float_of_string Sys.argv.(3) else 120.0 in
  let path = Printf.sprintf "docs/fstar-extracted/lifesci/%s.ttl" name in
  let ttl = read_file path in
  let triples = Parser_Turtle.parse_turtle_with_base ttl (Printf.sprintf "file:///%s.ttl" name) in
  Printf.printf "Input g0 (%s): %d triples\n%!" name (List.length triples);

  (* Match owl_rl_closure_with_reflexivity's own prep: rdfs_closure first,
     then owl Thing axioms, before the interleaved owl+rdfs loop. We
     replicate just enough to get a realistic starting graph, then hand-
     roll the iteration loop ourselves so we can print per-iteration
     stats that owl_rl_closure (Tot, no side effects) can't emit. *)
  let t0 = Unix.gettimeofday () in
  let rdfs_closed = RDF_Graph_Executable.rdfs_closure_with_reflexivity triples (Z.of_int 100) in
  Printf.printf "rdfs_closed: %d triples (%.3fs)\n%!"
    (List.length rdfs_closed) (Unix.gettimeofday () -. t0);

  let g = ref rdfs_closed in
  let prev_len = ref (List.length rdfs_closed) in
  let start = Unix.gettimeofday () in
  let i = ref 0 in
  let converged = ref false in
  let out_of_budget = ref false in
  while not !converged && not !out_of_budget && !i < max_iters do
    incr i;
    let t0 = Unix.gettimeofday () in
    let g_owl = RDF_Graph_Executable.owl_rl_closure_step !g in
    let t_owl = Unix.gettimeofday () -. t0 in
    let t1 = Unix.gettimeofday () in
    let g_rdfs = RDF_Graph_Executable.rdfs_closure_step g_owl in
    let t_rdfs = Unix.gettimeofday () -. t1 in
    let len' = List.length g_rdfs in
    let total_dt = Unix.gettimeofday () -. t0 in
    Printf.printf "  iter %2d: len %d -> %d (delta %+d)  owl_step=%.3fs  rdfs_step=%.3fs  total=%.3fs  elapsed=%.1fs\n%!"
      !i !prev_len len' (len' - !prev_len) t_owl t_rdfs total_dt (Unix.gettimeofday () -. start);
    if len' = !prev_len then converged := true
    else begin g := g_rdfs; prev_len := len' end;
    if Unix.gettimeofday () -. start > budget then out_of_budget := true
  done;
  if !converged then
    Printf.printf "\nconverged after %d iteration(s), final len=%d, wall=%.1fs\n%!"
      !i !prev_len (Unix.gettimeofday () -. start)
  else if !out_of_budget then
    Printf.printf "\nBUDGET EXCEEDED after %d iteration(s) (%.0fs budget), len still %d and %s\n%!"
      !i budget !prev_len (if !i > 0 then "growing/oscillating" else "n/a")
  else
    Printf.printf "\nHIT max_iters=%d without converging, len=%d\n%!" max_iters !prev_len;
  exit 0
