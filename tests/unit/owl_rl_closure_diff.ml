(* owl_rl_closure_diff.ml — characterise the OWL-RL closure blow-up
   on third_party/testing/w3c/sparql/sparql11/entailment/simple.ttl.

   The closure on a 16-triple input produces 207 triples after one
   step (13x blow-up); fuel=2 does not return in 5+ minutes.

   This test prints, per closure step:
     - total triple count
     - new triples bucketed by predicate (top N)
     - first few example new triples

   so we can see which OWL-RL rules are firing and which terms they
   are generating. Diagnostic for issue #262. *)

let simple_ttl_path =
  "third_party/testing/w3c/sparql/sparql11/entailment/simple.ttl"

let cap_seconds = 60.0

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

(* Run f () with a SIGALRM cap. Returns (Some r) on success, None on cap. *)
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

(* Convert an extracted RDF triple back to a short string for display.
   Truncate long IRIs for readability. *)
let show_term (t : RDF_Graph_Executable.rdf_term) : string =
  let open RDF_Graph_Executable in
  match t with
  | T_IRI i ->
    let s = i in
    if String.length s > 50
    then "<..." ^ String.sub s (String.length s - 40) 40 ^ ">"
    else "<" ^ s ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l ->
    let q = "\"" ^ l.lexical_form ^ "\"" in
    (match l.lang_tag with
     | Some t -> q ^ "@" ^ t
     | None ->
       if l.datatype = "" then q
       else q ^ "^^<" ^ l.datatype ^ ">")

let show_subject (s : RDF_Graph_Executable.subject) : string =
  match s with
  | RDF_Graph_Executable.S_IRI i -> "<" ^ i ^ ">"
  | RDF_Graph_Executable.S_BNode b -> "_:" ^ b

let show_predicate (p : RDF_Graph_Executable.wf_iri) : string =
  "<" ^ p ^ ">"

let show_triple (t : RDF_Graph_Executable.triple) : string =
  Printf.sprintf "%s %s %s ."
    (show_subject t.RDF_Graph_Executable.s)
    (show_predicate t.RDF_Graph_Executable.p)
    (show_term t.RDF_Graph_Executable.o)

(* Equality on (subject, predicate, object) so we can compute set diffs. *)
let triple_eq (a : RDF_Graph_Executable.triple) (b : RDF_Graph_Executable.triple) : bool =
  let open RDF_Graph_Executable in
  let s_eq sa sb = match sa, sb with
    | S_IRI i1, S_IRI i2 -> i1 = i2
    | S_BNode b1, S_BNode b2 -> b1 = b2
    | _ -> false
  in
  let p_eq = a.p = b.p in
  let o_eq oa ob = match oa, ob with
    | T_IRI i1, T_IRI i2 -> i1 = i2
    | T_BNode b1, T_BNode b2 -> b1 = b2
    | T_Literal l1, T_Literal l2 -> l1 = l2
    | _ -> false
  in
  s_eq a.s b.s && p_eq && o_eq a.o b.o

(* Triples in `b` not in `a`. *)
let triple_diff a b =
  List.filter (fun t -> not (List.exists (triple_eq t) a)) b

(* Bucket new triples by predicate IRI; sort by count desc. *)
let bucket_by_predicate (ts : RDF_Graph_Executable.triple list) =
  let h = Hashtbl.create 64 in
  List.iter (fun t ->
    let key = t.RDF_Graph_Executable.p in
    let cur = try Hashtbl.find h key with Not_found -> 0 in
    Hashtbl.replace h key (cur + 1)
  ) ts;
  let pairs = Hashtbl.fold (fun k v acc -> (k, v) :: acc) h [] in
  List.sort (fun (_, a) (_, b) -> compare b a) pairs

let () =
  let ttl = read_file simple_ttl_path in
  Printf.printf "Loaded %s (%d bytes)\n%!" simple_ttl_path (String.length ttl);

  let triples =
    Parser_Turtle.parse_turtle_with_base ttl "file:///simple.ttl"
  in
  let n0 = List.length triples in
  Printf.printf "Step 0 (input): %d triples\n%!" n0;
  Printf.printf "  sample input:\n";
  List.iter (fun t -> Printf.printf "    %s\n" (show_triple t)) triples;

  let run_closure fuel_n =
    let t0 = Unix.gettimeofday () in
    let g = RDF_Graph_Executable.owl_rl_closure_with_reflexivity triples (Z.of_int fuel_n) in
    let dt = Unix.gettimeofday () -. t0 in
    (g, dt)
  in

  let report ~prev ~cur ~label ~elapsed =
    let n_cur = List.length cur in
    let new_triples = triple_diff prev cur in
    let n_new = List.length new_triples in
    Printf.printf "\n%s: %d triples (+%d new) in %.3fs\n" label n_cur n_new elapsed;
    let buckets = bucket_by_predicate new_triples in
    Printf.printf "  new-triple predicates (top 10):\n";
    let rec take n = function
      | [] -> []
      | _ when n = 0 -> []
      | x :: xs -> x :: take (n-1) xs
    in
    List.iter (fun (p, c) ->
      Printf.printf "    %5d  <%s>\n" c p
    ) (take 10 buckets);
    let rec take_t n = function
      | [] -> []
      | _ when n = 0 -> []
      | x :: xs -> x :: take_t (n-1) xs
    in
    Printf.printf "  first 5 new triples:\n";
    List.iter (fun t -> Printf.printf "    %s\n" (show_triple t)) (take_t 5 new_triples)
  in

  (* fuel=1: known to terminate in ~100ms. Always inside the cap. *)
  let (g1, dt1) = run_closure 1 in
  report ~prev:triples ~cur:g1 ~label:"Step 1 (fuel=1)" ~elapsed:dt1;
  incr pass;

  (* fuel=2: capped — the diagnostic question is "what would step 2 add?"
     Try it under a long cap and report whether it returns. *)
  Printf.printf "\nAttempting fuel=2 with %.0fs cap...\n%!" cap_seconds;
  (match with_cap cap_seconds (fun () -> run_closure 2) with
  | Some (g2, dt2) ->
    Printf.printf "fuel=2 returned in %.3fs\n" dt2;
    report ~prev:g1 ~cur:g2 ~label:"Step 2 (fuel=2)" ~elapsed:dt2;
    incr pass
  | None ->
    Printf.printf "XFAIL fuel=2 did not return within %.0fs (issue #262)\n" cap_seconds;
    incr xfail);

  Printf.printf "\nsummary: %d pass, %d expected-fail, %d unexpected fail\n"
    !pass !xfail !fail;
  exit (if !fail > 0 then 1 else 0)
