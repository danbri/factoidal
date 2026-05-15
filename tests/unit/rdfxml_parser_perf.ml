(* rdfxml_parser_perf.ml — characterise the RDF/XML parser perf curve
   on truncated prefixes of profile-EL.rdf. Diagnostic for #263.

   We chop the OWL test catalog (~190 KB) at various lengths and parse
   each prefix with a per-attempt SIGALRM cap. The shape of the
   wall-clock vs input-size curve identifies whether the bug is
   O(n²) (small files fast, doubles → 4×), O(n³), or worse. *)

let owl_catalog =
  "third_party/testing/owl/profile-EL.rdf"

let cap_seconds = 5.0

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

(* Look at the input and find an element-boundary close to `target_pos`,
   so we don't chop in the middle of a tag (which would produce a
   non-well-formed XML that fails fast rather than testing perf). *)
let find_safe_chunk_end (s : string) (target : int) : int =
  let len = String.length s in
  let safe = min target len in
  (* Walk forward to the next '>' character; max 200 chars. *)
  let rec walk i bound =
    if bound = 0 || i >= len then i
    else if s.[i] = '>' then i + 1
    else walk (i + 1) (bound - 1)
  in
  walk safe 200

(* Wrap the prefix in a minimal <rdf:RDF> wrapper to keep XML well-formed. *)
let wrap_prefix (header : string) (body : string) : string =
  String.concat "" [header; body; "\n</rdf:RDF>\n"]

let () =
  let full = read_file owl_catalog in
  Printf.printf "Loaded %s (%d bytes)\n%!" owl_catalog (String.length full);

  (* Find header — everything through and including <rdf:RDF ...> *)
  let header_end =
    try
      let rec find i =
        if i + 12 >= String.length full then String.length full
        else if String.sub full i 4 = "<rdf"
             && String.sub full (i+4) 4 = ":RDF"
        then begin
          (* Walk forward to the '>' that closes <rdf:RDF ...> *)
          let rec close j =
            if j >= String.length full then j
            else if full.[j] = '>' then j + 1
            else close (j + 1)
          in
          close (i + 8)
        end
        else find (i + 1)
      in
      find 0
    with _ -> 256
  in
  let header = String.sub full 0 header_end in
  Printf.printf "header: %d bytes\n\n" header_end;

  let body_full = String.sub full header_end (String.length full - header_end) in

  let try_size target =
    let end_pos = find_safe_chunk_end body_full target in
    let body = String.sub body_full 0 end_pos in
    let input = wrap_prefix header body in
    let size = String.length input in
    Printf.printf "  size=%6d bytes  ... %!" size;
    let t0 = Unix.gettimeofday () in
    match with_cap cap_seconds (fun () ->
      Parser_RDFXML.parse_rdfxml_with_base "file:///catalog.rdf" input)
    with
    | Some r ->
      let dt = Unix.gettimeofday () -. t0 in
      let n_triples = List.length r in
      Printf.printf "PASS  %d triples (%.3fs, %.1f bytes/ms)\n%!"
        n_triples dt
        (if dt > 0.0 then float_of_int size /. (dt *. 1000.0) else 0.0);
      incr pass
    | None ->
      Printf.printf "XFAIL did not return within %.0fs\n%!" cap_seconds;
      incr xfail
  in

  Printf.printf "Per-size timing on profile-EL prefixes:\n";
  List.iter try_size [
    500; 1000; 2000; 4000; 8000;
    12000; 16000; 24000;
    32000; 48000; 64000; 96000;
    128000;
  ];

  Printf.printf "\nsummary: %d pass, %d expected-fail (perf cap exceeded)\n"
    !pass !xfail;
  exit 0
