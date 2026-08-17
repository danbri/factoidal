(* depcheck — #448 Part 2 consumer for Dep.Reachability, the verified
   graph-reachability core (formal/fstar/Dep.Reachability.fst).

   Not part of the verified library (iron rule #11): this is a thin
   I/O shell that reads an edge file and a roots file, calls the
   EXTRACTED Dep_Reachability.reachable, and then RE-CHECKS
   Dep_Reachability.is_closed and Dep_Reachability.all_mem on the
   ACTUAL OUTPUT before trusting it. That runtime recheck is what
   makes the verified theorem's premises real for this run: neither
   closure_fuel's fuel bound nor its implementation is trusted for
   soundness, only the recheck plus Dep.Reachability.closed_set_
   catches_all/no_root_reaches are (see that module's header).

   Usage: depcheck EDGE_FILE ROOTS_FILE [RESULT_FILE]
     EDGE_FILE:  one "src dst" pair per line (whitespace-separated).
     ROOTS_FILE: one node per line.
     RESULT_FILE (optional): one node per line — a candidate result to
       AUDIT instead of computing one via reachable(). Lets a stored or
       hand-edited set be re-checked against the same is_closed/all_mem
       gate a fresh run uses (also how the refusal path is exercised
       against a deliberately doctored, non-closed set).
   Prints the (computed or audited) node set, one per line, to stdout
   on success. Exits 2 with a loud stderr message if it fails either
   recheck — that refusal is the anti-vacuity guarantee: this tool can
   say no. *)

let read_lines path =
  let ic = open_in path in
  let rec loop acc =
    match input_line ic with
    | line -> loop (String.trim line :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  List.filter (fun l -> l <> "") (loop [])

let () =
  if Array.length Sys.argv < 3 || Array.length Sys.argv > 4 then begin
    Printf.eprintf "usage: depcheck EDGE_FILE ROOTS_FILE [RESULT_FILE]\n";
    exit 1
  end;
  let edges =
    read_lines Sys.argv.(1)
    |> List.map (fun l -> match String.split_on_char ' ' l with
                 | s :: d :: _ -> (s, d)
                 | _ -> Printf.eprintf "depcheck: malformed edge line %S\n" l; exit 1)
  in
  let roots = read_lines Sys.argv.(2) in
  let result =
    if Array.length Sys.argv = 4 then read_lines Sys.argv.(3)
    else Dep_Reachability.reachable edges roots
  in
  if not (Dep_Reachability.is_closed edges result) then begin
    Printf.eprintf
      "depcheck: REFUSED — reachable() output is not closed under edges \
       (fuel ran out or the closure algorithm is buggy). Not trusting this \
       result. See formal/fstar/Dep.Reachability.fst.\n";
    exit 2
  end;
  if not (Dep_Reachability.all_mem roots result) then begin
    Printf.eprintf
      "depcheck: REFUSED — reachable() output does not contain all roots. \
       Not trusting this result. See formal/fstar/Dep.Reachability.fst.\n";
    exit 2
  end;
  List.iter (fun n -> print_string n; print_newline ()) result
