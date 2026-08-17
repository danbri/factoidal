(* dep_reachability_unit.ml -- pins Dep_Reachability (#448 Part 2), the
   extracted OCaml surface of formal/fstar/Dep.Reachability.fst: the
   verified reachability core tools/module-liveness.py v3 calls into
   (via bin/depcheck) instead of trusting an unverified Python BFS
   over ocamlobjinfo output.

   Three things are pinned:

   1. `reachable` finds exactly the right set on a diamond graph, a
      cycle, and a disconnected node -- the three shapes the module's
      own header names as the fuel-adequacy argument's edge cases
      (fixpoint reached before fuel runs out; a cycle that must not
      loop forever; a root with no outgoing edges that must still
      appear in its own reachable set).

   2. `is_closed` ACCEPTS the output `reachable` computes for each of
      those graphs -- the runtime premise depcheck's refusal path
      re-checks on every real run.

   3. `is_closed` REJECTS a hand-built non-closed set (anti-vacuity:
      the checker can say no, not just say yes on everything). *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let check_bool ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %b got %b\n" name expected actual
  end

let sorted l = List.sort_uniq compare l

let () =
  (* 1a. Diamond: A -> B, A -> C, B -> D, C -> D. Root A reaches
     everything; root D reaches only itself. *)
  let diamond = [ ("A", "B"); ("A", "C"); ("B", "D"); ("C", "D") ] in
  check ~name:"diamond: reachable from A"
    [ "A"; "B"; "C"; "D" ]
    (sorted (Dep_Reachability.reachable diamond [ "A" ]));
  check ~name:"diamond: reachable from D (sink)"
    [ "D" ]
    (sorted (Dep_Reachability.reachable diamond [ "D" ]));
  check_bool ~name:"diamond: is_closed accepts reachable(A)'s output" true
    (Dep_Reachability.is_closed diamond
       (Dep_Reachability.reachable diamond [ "A" ]));

  (* 1b. Cycle: X -> Y -> Z -> X. Must terminate (not loop on fuel)
     and every node reaches every other node. *)
  let cycle = [ ("X", "Y"); ("Y", "Z"); ("Z", "X") ] in
  check ~name:"cycle: reachable from X"
    [ "X"; "Y"; "Z" ]
    (sorted (Dep_Reachability.reachable cycle [ "X" ]));
  check_bool ~name:"cycle: is_closed accepts reachable(X)'s output" true
    (Dep_Reachability.is_closed cycle
       (Dep_Reachability.reachable cycle [ "X" ]));

  (* 1c. Disconnected node: edges only among A/B; root set includes an
     isolated node "LONE" with no incident edges. reachable must still
     contain LONE (roots are always in their own reachable set) and
     must not pull in A/B, which LONE cannot reach. *)
  let with_isolate = [ ("A", "B") ] in
  check ~name:"disconnected: reachable from {LONE} stays just {LONE}"
    [ "LONE" ]
    (sorted (Dep_Reachability.reachable with_isolate [ "LONE" ]));
  check ~name:"disconnected: reachable from {A; LONE}"
    [ "A"; "B"; "LONE" ]
    (sorted (Dep_Reachability.reachable with_isolate [ "A"; "LONE" ]));
  check_bool ~name:"disconnected: all_mem roots holds on the output" true
    (Dep_Reachability.all_mem [ "A"; "LONE" ]
       (Dep_Reachability.reachable with_isolate [ "A"; "LONE" ]));

  (* 2. Anti-vacuity: is_closed REJECTS a hand-built non-closed set.
     Diamond graph again, but the candidate set {A; B; C} omits D even
     though B->D and C->D are both edges out of members of the set. *)
  check_bool ~name:"anti-vacuity: is_closed rejects a non-closed set" false
    (Dep_Reachability.is_closed diamond [ "A"; "B"; "C" ]);
  (* And the positive control on the same graph: {A;B;C;D} IS closed. *)
  check_bool ~name:"anti-vacuity: is_closed accepts the true closure" true
    (Dep_Reachability.is_closed diamond [ "A"; "B"; "C"; "D" ]);

  Printf.printf "dep_reachability_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
