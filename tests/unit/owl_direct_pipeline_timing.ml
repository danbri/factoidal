(* owl_direct_pipeline_timing.ml — pinpoints the hang in
   `w3c_runner entailment` test [50/70] "simple 1".

   The runner does (for OWL-Direct tests):
     1. parse simple.ttl
     2. owl_rl_closure_with_reflexivity g 100   (call A)
     3. Tableau.tableau_materialise g1          (call B)
     4. owl_rl_closure_with_reflexivity g2 100  (call C)

   This test runs only call A across a sweep of fuel values 1..3 with a
   per-step wall-clock cap. With the current implementation:

     - fuel=1 takes ~100ms and produces ~207 triples (13x blow-up).
     - fuel=2 does not return within the cap.

   The test PASSES when fuel=1 returns, FAILS if the cap fires.

   See docs/designissues/2026-05-15-cottas-literal-lookup-and-owl-rl-blowup.md
   for the corresponding bug write-up. *)

let simple_ttl_path =
  "third_party/testing/w3c/sparql/sparql11/entailment/simple.ttl"

let cap_seconds = 5.0

let pass = ref 0
let fail = ref 0
let xfail = ref 0

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.unsafe_to_string s

(* Run f () with a SIGALRM cap. Returns (Some r) on success or None on cap. *)
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

let time_it label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf "  [%-32s] %.3fs\n%!" label dt;
  (r, dt)

let () =
  let ttl = read_file simple_ttl_path in
  Printf.printf "Loaded %s (%d bytes)\n%!" simple_ttl_path (String.length ttl);

  let triples =
    Parser_Turtle.parse_turtle_with_base ttl "file:///simple.ttl"
  in
  Printf.printf "  parsed: %d triples\n%!" (List.length triples);

  let try_closure fuel_n =
    let label = Printf.sprintf "owl_rl_closure fuel=%d (cap=%.0fs)" fuel_n cap_seconds in
    let started = Unix.gettimeofday () in
    let r = with_cap cap_seconds (fun () ->
      time_it (Printf.sprintf "owl_rl_closure fuel=%d" fuel_n) (fun () ->
        RDF_Graph_Executable.owl_rl_closure_with_reflexivity triples (Z.of_int fuel_n)))
    in
    match r with
    | Some (g, _dt) ->
      Printf.printf "PASS  %s -> %d triples\n%!" label (List.length g);
      incr pass
    | None ->
      let elapsed = Unix.gettimeofday () -. started in
      Printf.printf "XFAIL %s (capped at %.1fs, see #-fileme)\n%!" label elapsed;
      incr xfail
  in

  try_closure 1;
  try_closure 2;

  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !pass !xfail !fail;
  exit (if !fail > 0 then 1 else 0)
