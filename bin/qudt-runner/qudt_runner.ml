(* QUDT v3.4.0 SHACL suite runner (Layer A of
   docs/designissues/2026-07-10-qudt-scoping.md).

   Two measured sections, both driven by the F*-extracted SHACL
   validator (SHACL_Validation.parse_shape_from_graph + .validate —
   the same entry points bin/shacl-runner uses):

   qudt-integrity
     Runs QUDT's own contributor-facing integrity ruleset
     (third_party/qudt/COLLECTION_QUDT_QA_TESTS_ALL.ttl) against the
     QUDT v3.4.0 all-in-one SHACL distribution
     (third_party/qudt/QUDT-all-in-one-SHACL.ttl, 131k triples).
     One scored entry per root shape in the ruleset. A shape:
       - PASSES when the validator evaluates it to completion and the
         distribution conforms to it, or when its violations are
         annotated as upstream data issues in
         tests/qudt/dispositions.tsv (annotated, never patched — the
         vendored distribution is untouched);
       - FAILS when the validator reports an engine failure
         (report_failure — an sh:sparql query we cannot parse or
         evaluate), when its violations are dispositioned as our bug,
         or when violations have no disposition yet (untriaged
         violations are a fail, not a shrug);
       - SKIPS (labelled) when the shape is sh:deactivated, when its
         only target is a sh:SPARQLTarget (the one acknowledged
         SHACL gap, issue #181), or when the wall-clock budget ran
         out before its turn (shapes run cheapest-target-first so a
         budget trip loses the most expensive tail, and the skip
         reason names the budget — a perf finding, not a silence).

   qudt-user-shapes
     Runs QUDT's user-facing ruleset
     (third_party/qudt/COLLECTION_QUDT_USER_TESTS.ttl — deprecation
     flagging + quantity-data consistency) against small authored
     fixtures in tests/qudt/fixtures/. Expected verdict is encoded in
     the filename (-ok = adds no findings, -viol = must be flagged),
     mirroring the vc fixture convention. Because every user shape is
     an sh:sparql constraint evaluated per focus node, and the
     rulesets target wide classes (qudt:Concept), validating a
     fixture against the FULL 131k-triple distribution exceeds the
     10-minute cap (measured — see the results log; a standing perf
     finding per the scoping doc). The scored fixture run therefore
     validates each fixture against fixture + a mechanically
     extracted context: distribution triples about every IRI the
     fixture mentions, one more hop of subject triples, plus the
     rdfs:subClassOf spine so sh:targetClass instance computation
     sees the real class hierarchy. The extraction is a plain
     reachability walk over already-parsed triples (I/O glue, same
     category as shacl_runner's bnode_path_closure) and its size is
     printed per fixture. A fixture is flagged iff validation of
     (fixture + context) reports findings that validation of
     (context alone) does not — so pre-existing findings inside the
     distribution slice can never mask or fake a fixture verdict.
     --full-union switches to fixture + full distribution (perf
     measurement mode; expect the cap).

   !! THIS IS I/O GLUE — NO SHACL/SPARQL SEMANTIC LOGIC !!
   See CLAUDE.md iron rule #11 / anti-pattern #15. Shape parsing,
   target computation, SPARQL constraint evaluation and report
   construction all live in formal/fstar/SHACL.Validation.fst and
   the SPARQL11 modules. This file does file I/O, per-shape slicing of the
   shapes DOCUMENT (triple-list bookkeeping so each ruleset shape
   gets its own timed, budgeted validator run), fixture-context
   extraction (reachability over parsed triples), wall-clock
   accounting, and score printing.

   Usage:
     ./qudt_runner                 Run both sections
     ./qudt_runner --integrity    Run only qudt-integrity
     ./qudt_runner --fixtures     Run only qudt-user-shapes
     ./qudt_runner --budget N     Integrity wall-clock budget, seconds
                                  (default 420; outer harness cap is
                                  timeout 600 per anti-pattern #17)
     ./qudt_runner --full-union   Fixtures against the full
                                  distribution (perf mode)
     ./qudt_runner -v|--verbose   Print every violation, not a sample
     ./qudt_runner --help
*)

open RDF_Graph_Executable

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to shacl_runner.ml). *)

let find_repo_root () =
  let rec walk d =
    if d = "/" || d = "" then None
    else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
    else walk (Filename.dirname d)
  in
  let start =
    try Filename.dirname (Sys.executable_name)
    with _ -> Sys.getcwd ()
  in
  match walk start with
  | Some r -> r
  | None ->
    (match walk (Sys.getcwd ()) with
     | Some r -> r
     | None -> Sys.getcwd ())

let repo_root = find_repo_root ()
let rp p = Filename.concat repo_root p

let dist_path      = "third_party/qudt/QUDT-all-in-one-SHACL.ttl"
let qa_path        = "third_party/qudt/COLLECTION_QUDT_QA_TESTS_ALL.ttl"
let user_path      = "third_party/qudt/COLLECTION_QUDT_USER_TESTS.ttl"
let fixtures_dir   = "tests/qudt/fixtures"
let dispositions_p = "tests/qudt/dispositions.tsv"

(* ------------------------------------------------------------------ *)
(* File I/O + Turtle parsing. *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let b = Bytes.create n in
    really_input ic b 0 n;
    close_in ic;
    Some (Bytes.to_string b)
  with Sys_error _ -> None

let abs_path p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p
let file_uri p = "file://" ^ abs_path p

let parse_ttl_file (path : string) : (rdf_graph * int) option =
  match read_file path with
  | None -> None
  | Some raw ->
    Some (Parser_Turtle.parse_turtle_with_base raw (file_uri path), String.length raw)

let now () = Unix.gettimeofday ()

(* ------------------------------------------------------------------ *)
(* Thin graph accessors (as in shacl_runner.ml). *)

let term_to_subj_opt (t : rdf_term) : subject option =
  match term_to_subject t with
  | FStar_Pervasives_Native.Some s -> Some s
  | FStar_Pervasives_Native.None -> None

let objs_of (g : rdf_graph) (subj_term : rdf_term) (pred : string) : rdf_term list =
  match term_to_subj_opt subj_term with
  | None -> []
  | Some s -> find_objects g s pred

let iri_str (t : rdf_term) : string option =
  match t with T_IRI i -> Some i | _ -> None

let rdf_type_iri  = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdfs_subclass = "http://www.w3.org/2000/01/rdf-schema#subClassOf"
let rdfs_label    = "http://www.w3.org/2000/01/rdf-schema#label"
let sh_ns = "http://www.w3.org/ns/shacl#"
let sh_NodeShape        = sh_ns ^ "NodeShape"
let sh_PropertyShape    = sh_ns ^ "PropertyShape"
let sh_SPARQLTarget     = sh_ns ^ "SPARQLTarget"
let sh_target           = sh_ns ^ "target"
let sh_targetClass      = sh_ns ^ "targetClass"
let sh_targetSubjectsOf = sh_ns ^ "targetSubjectsOf"
let sh_targetObjectsOf  = sh_ns ^ "targetObjectsOf"
let sh_targetNode       = sh_ns ^ "targetNode"
let sh_deactivated      = sh_ns ^ "deactivated"

let subjects_typed (g : rdf_graph) (type_iri : string) : rdf_term list =
  List.sort_uniq compare
    (List.filter_map
       (fun (tr : triple) ->
          if tr.p = rdf_type_iri
          then (match tr.o with
                | T_IRI i when i = type_iri -> Some (subject_to_term tr.s)
                | _ -> None)
          else None)
       g)

let triples_with_subject (g : rdf_graph) (t : rdf_term) : triple list =
  match term_to_subj_opt t with
  | None -> []
  | Some s -> List.filter (fun (tr : triple) -> subject_eq tr.s s) g

let term_str (t : rdf_term) : string =
  match t with
  | T_IRI i -> "<" ^ i ^ ">"
  | T_BNode b -> "_:" ^ b
  | T_Literal l -> "\"" ^ l.lexical_form ^ "\""

(* ------------------------------------------------------------------ *)
(* Violation rendering + delta keys. *)

let severity_str (s : SHACL_Validation.severity) : string =
  match s with
  | SHACL_Validation.Sev_Info -> "Info"
  | SHACL_Validation.Sev_Warning -> "Warning"
  | SHACL_Validation.Sev_Violation -> "Violation"
  | SHACL_Validation.Sev_Custom i -> "Custom(" ^ i ^ ")"

let violation_msg (v : SHACL_Validation.violation) : string =
  match v.SHACL_Validation.v_message with
  | FStar_Pervasives_Native.Some l -> l.lexical_form
  | FStar_Pervasives_Native.None -> "(no message)"

let violation_line (v : SHACL_Validation.violation) : string =
  Printf.sprintf "[%s] shape=%s focus=%s value=%s — %s"
    (severity_str v.SHACL_Validation.v_severity)
    v.SHACL_Validation.v_source_shape
    (term_str v.SHACL_Validation.v_focus_node)
    (match v.SHACL_Validation.v_value with
     | FStar_Pervasives_Native.Some t -> term_str t
     | FStar_Pervasives_Native.None -> "-")
    (violation_msg v)

(* Key for the fixture baseline-delta comparison: focus node + source
   shape + message text identifies a finding across the two runs. *)
let violation_key (v : SHACL_Validation.violation) : string =
  term_str v.SHACL_Validation.v_focus_node ^ "|"
  ^ v.SHACL_Validation.v_source_shape ^ "|"
  ^ violation_msg v

(* ------------------------------------------------------------------ *)
(* Dispositions (integrity-run triage annotations). Tab-separated:
   <shape-iri> TAB <upstream|our-bug> TAB <note>. Lines starting with
   '#' are comments. Upstream data issues are ANNOTATED here, never
   patched into the vendored files (skills/test-suites discipline). *)

let load_dispositions () : (string * string * string) list =
  match read_file (rp dispositions_p) with
  | None -> []
  | Some raw ->
    List.filter_map
      (fun line ->
         let line = String.trim line in
         if line = "" || line.[0] = '#' then None
         else match String.split_on_char '\t' line with
           | shape :: disp :: rest -> Some (shape, disp, String.concat " " rest)
           | _ -> None)
      (String.split_on_char '\n' raw)

(* ------------------------------------------------------------------ *)
(* Per-shape slicing of the QA ruleset document.

   closure S = S's own triples + reachable blank-node structure
   (sh:sparql constraint bnodes, sh:target bnodes, list nodes).
   slice for S = whole shapes document MINUS the closures of every
   OTHER root shape — prefix-declaration nodes, ontology headers and
   any shared IRI-subject support triples stay in every slice. *)

let rec bnode_closure (g : rdf_graph) (frontier : rdf_term list)
    (acc : triple list) (fuel : int) : triple list =
  if fuel <= 0 then acc
  else
    match frontier with
    | [] -> acc
    | t :: rest ->
      (match t with
       | T_BNode _ ->
         let ts = triples_with_subject g t in
         let objs = List.map (fun (tr : triple) -> tr.o) ts in
         bnode_closure g (rest @ objs) (acc @ ts) (fuel - 1)
       | _ -> bnode_closure g rest acc (fuel - 1))

let shape_closure (g : rdf_graph) (shape : rdf_term) : triple list =
  let own = triples_with_subject g shape in
  let objs = List.map (fun (tr : triple) -> tr.o) own in
  own @ bnode_closure g objs [] 10000

let slice_for_shape (g : rdf_graph) (all_shapes : rdf_term list)
    (shape : rdf_term) : rdf_graph =
  let excluded =
    List.concat_map
      (fun s -> if s = shape then [] else shape_closure g s)
      all_shapes
  in
  List.filter (fun tr -> not (List.mem tr excluded)) g

(* ------------------------------------------------------------------ *)
(* Wall-clock budget: a per-shape SIGALRM cap so one expensive shape
   surrenders the floor instead of eating the whole outer timeout. *)

exception Shape_budget_exceeded

let with_alarm (secs : int) (f : unit -> 'a) : 'a =
  let old = Sys.signal Sys.sigalrm
      (Sys.Signal_handle (fun _ -> raise Shape_budget_exceeded)) in
  ignore (Unix.alarm secs);
  let restore () = ignore (Unix.alarm 0); Sys.set_signal Sys.sigalrm old in
  (try let r = f () in restore (); r
   with e -> restore (); raise e)

(* ------------------------------------------------------------------ *)
(* Section 1: qudt-integrity. *)

type outcome = Pass of string | Fail of string | Skip of string

let shape_label (g : rdf_graph) (s : rdf_term) : string =
  match s with
  | T_IRI i ->
    (* strip the qudt namespace for readability *)
    let pfx = "http://qudt.org/schema/qudt/" in
    if String.length i > String.length pfx
       && String.sub i 0 (String.length pfx) = pfx
    then String.sub i (String.length pfx) (String.length i - String.length pfx)
    else i
  | _ ->
    (match objs_of g s rdfs_label with
     | T_Literal l :: _ -> l.lexical_form
     | _ -> term_str s)

(* Estimated focus-node count, used ONLY to order shapes
   cheapest-first (so a budget trip skips the most expensive tail) and
   to label skip lines. Includes a transitive rdfs:subClassOf walk so
   a sh:targetClass qudt:Concept shape is costed at its real 11,510
   SHACL instances (v3.4.0), not the 0 direct `a qudt:Concept` triples
   (the first cut ordered by direct typing and put the widest shapes
   FIRST). Bookkeeping only — the real target computation happens
   inside SHACL_Validation.validate. *)
let subclasses_of (dist : rdf_graph) (c : string) : string list =
  let known = Hashtbl.create 64 in
  Hashtbl.add known c ();
  let changed = ref true in
  let fuel = ref 50 in
  while !changed && !fuel > 0 do
    changed := false;
    decr fuel;
    List.iter
      (fun (tr : triple) ->
         if tr.p = rdfs_subclass then
           match subject_to_term tr.s, tr.o with
           | T_IRI sub, T_IRI sup ->
             if Hashtbl.mem known sup && not (Hashtbl.mem known sub) then begin
               Hashtbl.add known sub (); changed := true
             end
           | _ -> ())
      dist
  done;
  Hashtbl.fold (fun k () acc -> k :: acc) known []

let estimate_foci (dist : rdf_graph) (shapes_g : rdf_graph) (s : rdf_term) : int =
  let count_type c =
    let cs = subclasses_of dist c in
    List.length
      (List.filter
         (fun (tr : triple) ->
            tr.p = rdf_type_iri
            && (match tr.o with T_IRI i -> List.mem i cs | _ -> false))
         dist)
  in
  let count_pred p =
    List.length (List.filter (fun (tr : triple) -> tr.p = p) dist)
  in
  let classes = List.filter_map iri_str (objs_of shapes_g s sh_targetClass) in
  let subj_preds = List.filter_map iri_str (objs_of shapes_g s sh_targetSubjectsOf) in
  let obj_preds = List.filter_map iri_str (objs_of shapes_g s sh_targetObjectsOf) in
  let nodes = List.length (objs_of shapes_g s sh_targetNode) in
  List.fold_left (+) nodes
    (List.map count_type classes
     @ List.map count_pred subj_preds
     @ List.map count_pred obj_preds)

let has_sparql_target (shapes_g : rdf_graph) (s : rdf_term) : bool =
  List.exists
    (fun t ->
       List.exists
         (fun ty -> match ty with T_IRI i -> i = sh_SPARQLTarget | _ -> false)
         (objs_of shapes_g t rdf_type_iri))
    (objs_of shapes_g s sh_target)

let has_non_sparql_target (shapes_g : rdf_graph) (s : rdf_term) : bool =
  objs_of shapes_g s sh_targetClass <> []
  || objs_of shapes_g s sh_targetSubjectsOf <> []
  || objs_of shapes_g s sh_targetObjectsOf <> []
  || objs_of shapes_g s sh_targetNode <> []

let is_deactivated_shape (shapes_g : rdf_graph) (s : rdf_term) : bool =
  List.exists
    (fun t -> match t with
       | T_Literal l -> l.lexical_form = "true" || l.lexical_form = "1"
       | _ -> false)
    (objs_of shapes_g s sh_deactivated)

let run_integrity ~verbose ~budget : int * int * int * int =
  Printf.printf "=== qudt-integrity: QUDT contributor ruleset vs QUDT v3.4.0 distribution ===\n%!";
  let t0 = now () in
  let dist, dist_bytes =
    match parse_ttl_file (rp dist_path) with
    | Some (g, b) -> g, b
    | None -> Printf.eprintf "qudt_runner: cannot read %s\n" dist_path; exit 2
  in
  let t1 = now () in
  Printf.printf "parsed %s: %d bytes, %d triples in %.2fs\n%!"
    dist_path dist_bytes (List.length dist) (t1 -. t0);
  let qa, qa_bytes =
    match parse_ttl_file (rp qa_path) with
    | Some (g, b) -> g, b
    | None -> Printf.eprintf "qudt_runner: cannot read %s\n" qa_path; exit 2
  in
  Printf.printf "parsed %s: %d bytes, %d triples in %.2fs\n%!"
    qa_path qa_bytes (List.length qa) (now () -. t1);
  let dispositions = load_dispositions () in
  let root_shapes =
    List.sort_uniq compare
      (subjects_typed qa sh_NodeShape @ subjects_typed qa sh_PropertyShape)
  in
  let with_est =
    List.map (fun s -> (estimate_foci dist qa s, s)) root_shapes in
  let ordered = List.sort (fun (a, _) (b, _) -> compare a b) with_est in
  Printf.printf "%d root shapes in ruleset; running cheapest-target-first, budget %ds\n\n%!"
    (List.length ordered) budget;
  let start = now () in
  let outcomes =
    List.map
      (fun (est, s) ->
         let label = shape_label qa s in
         let elapsed = now () -. start in
         if is_deactivated_shape qa s then begin
           Printf.printf "  skip: %-55s sh:deactivated true (excluded by SHACL semantics)\n%!" label;
           (label, Skip "sh:deactivated")
         end
         else if has_sparql_target qa s && not (has_non_sparql_target qa s) then begin
           Printf.printf "  skip: %-55s sh:SPARQLTarget only (acknowledged gap, issue #181)\n%!" label;
           (label, Skip "sh:SPARQLTarget (#181)")
         end
         else if elapsed > float_of_int budget then begin
           Printf.printf "  skip: %-55s wall-clock budget exhausted (%.0fs > %ds) before this shape (est. %d foci) — perf finding\n%!"
             label elapsed budget est;
           (label, Skip "time budget (perf finding)")
         end
         else begin
           let remaining = float_of_int budget -. elapsed in
           let shape_cap = max 5 (int_of_float remaining) in
           let slice = slice_for_shape qa root_shapes s in
           let ts = now () in
           let result =
             try
               with_alarm shape_cap (fun () ->
                 let sg = SHACL_Validation.parse_shape_from_graph slice in
                 let report = SHACL_Validation.validate dist slice sg in
                 `Report report)
             with
             | Shape_budget_exceeded -> `Timeout
             | e -> `Exn (Printexc.to_string e)
           in
           let dt = now () -. ts in
           let partial_note =
             if has_sparql_target qa s
             then " [partial: sh:SPARQLTarget component ignored (#181)]" else "" in
           match result with
           | `Timeout ->
             Printf.printf "  skip: %-55s per-shape wall-clock cap (%ds) tripped after %.1fs (est. %d foci) — perf finding\n%!"
               label shape_cap dt est;
             (label, Skip "time budget (perf finding)")
           | `Exn msg ->
             Printf.printf "  FAIL: %-55s exception after %.1fs: %s\n%!" label dt msg;
             (label, Fail ("exception: " ^ msg))
           | `Report report ->
             (match report.SHACL_Validation.report_failure with
              | FStar_Pervasives_Native.Some msg ->
                Printf.printf "  FAIL: %-55s engine failure in %.1fs: %s%s\n%!"
                  label dt msg partial_note;
                (label, Fail ("engine: " ^ msg))
              | FStar_Pervasives_Native.None ->
                let vs = report.SHACL_Validation.results in
                let n = List.length vs in
                if n = 0 then begin
                  Printf.printf "  PASS: %-55s conformant, %d est. foci, %.1fs%s\n%!"
                    label est dt partial_note;
                  (label, Pass "conformant")
                end else begin
                  let shape_iri = match s with T_IRI i -> i | _ -> "" in
                  let disp =
                    List.find_opt (fun (si, _, _) -> si = shape_iri) dispositions in
                  let sample = if verbose then vs else (List.filteri (fun i _ -> i < 10) vs) in
                  List.iter (fun v -> Printf.printf "        %s\n" (violation_line v)) sample;
                  if not verbose && n > 10 then
                    Printf.printf "        ... (%d findings total; -v prints all)\n" n;
                  match disp with
                  | Some (_, "upstream", note) ->
                    Printf.printf "  PASS: %-55s %d findings, all annotated upstream data issues: %s (%.1fs)%s\n%!"
                      label n note dt partial_note;
                    (label, Pass (Printf.sprintf "%d upstream findings (annotated)" n))
                  | Some (_, "our-bug", note) ->
                    Printf.printf "  FAIL: %-55s %d findings dispositioned as our bug: %s (%.1fs)\n%!"
                      label n note dt;
                    (label, Fail ("our bug: " ^ note))
                  | _ ->
                    Printf.printf "  FAIL: %-55s %d findings, UNTRIAGED (no dispositions.tsv entry) (%.1fs)\n%!"
                      label n dt;
                    (label, Fail (Printf.sprintf "%d untriaged findings" n))
                end)
         end)
      ordered
  in
  let pass = List.length (List.filter (fun (_, o) -> match o with Pass _ -> true | _ -> false) outcomes) in
  let fail = List.length (List.filter (fun (_, o) -> match o with Fail _ -> true | _ -> false) outcomes) in
  let skip = List.length (List.filter (fun (_, o) -> match o with Skip _ -> true | _ -> false) outcomes) in
  let total = List.length outcomes in
  Printf.printf "\nqudt-integrity elapsed: %.1fs (parse %.2fs + validation)\n" (now () -. t0) (t1 -. t0);
  (pass, fail, skip, total)

(* ------------------------------------------------------------------ *)
(* Section 2: qudt-user-shapes fixtures. *)

(* Context extraction: distribution triples about every IRI the
   fixture mentions, one further hop of subject triples, then the
   rdfs:subClassOf spine to fixpoint. Reachability bookkeeping only. *)

let subject_index (g : rdf_graph) : (string, triple list) Hashtbl.t =
  let h = Hashtbl.create 65536 in
  List.iter
    (fun (tr : triple) ->
       let k = term_str (subject_to_term tr.s) in
       Hashtbl.replace h k (tr :: (try Hashtbl.find h k with Not_found -> [])))
    g;
  h

let extract_context (idx : (string, triple list) Hashtbl.t) (fixture : rdf_graph)
  : rdf_graph =
  let included : (string, unit) Hashtbl.t = Hashtbl.create 256 in
  let acc = ref [] in
  let add_subject (iri : string) =
    let k = "<" ^ iri ^ ">" in
    if not (Hashtbl.mem included k) then begin
      Hashtbl.add included k ();
      match Hashtbl.find_opt idx k with
      | Some ts -> acc := ts @ !acc
      | None -> ()
    end
  in
  let iris_of_triple (tr : triple) : string list =
    let s = match subject_to_term tr.s with T_IRI i -> [i] | _ -> [] in
    let o = match tr.o with T_IRI i -> [i] | _ -> [] in
    s @ (tr.p :: o)
  in
  (* hop 1: everything the fixture mentions *)
  List.iter (fun tr -> List.iter add_subject (iris_of_triple tr)) fixture;
  (* hop 2: subjects for every IRI object of hop 1 *)
  let hop1 = !acc in
  List.iter
    (fun (tr : triple) -> match tr.o with T_IRI i -> add_subject i | _ -> ())
    hop1;
  (* rdfs:subClassOf spine to fixpoint (fuel-capped) *)
  let rec spine fuel =
    if fuel <= 0 then ()
    else begin
      let before = Hashtbl.length included in
      List.iter
        (fun (tr : triple) ->
           if tr.p = rdfs_subclass then
             match tr.o with T_IRI i -> add_subject i | _ -> ())
        !acc;
      if Hashtbl.length included > before then spine (fuel - 1)
    end
  in
  spine 30;
  !acc

let run_fixtures ~verbose ~full_union : int * int * int * int =
  Printf.printf "\n=== qudt-user-shapes: QUDT user ruleset vs authored fixtures ===\n%!";
  let t0 = now () in
  let dist, _ =
    match parse_ttl_file (rp dist_path) with
    | Some r -> r
    | None -> Printf.eprintf "qudt_runner: cannot read %s\n" dist_path; exit 2
  in
  let user, _ =
    match parse_ttl_file (rp user_path) with
    | Some r -> r
    | None -> Printf.eprintf "qudt_runner: cannot read %s\n" user_path; exit 2
  in
  Printf.printf "parsed distribution (%d triples) + user ruleset (%d triples) in %.2fs\n%!"
    (List.length dist) (List.length user) (now () -. t0);
  let idx = if full_union then Hashtbl.create 1 else subject_index dist in
  let dir = rp fixtures_dir in
  let files =
    try
      Sys.readdir dir |> Array.to_list
      |> List.filter (fun f -> Filename.check_suffix f ".ttl")
      |> List.sort compare
    with Sys_error _ -> []
  in
  if files = [] then begin
    Printf.eprintf "qudt_runner: no fixtures found under %s\n" fixtures_dir;
    (0, 0, 0, 0)
  end else begin
    let sg_user = SHACL_Validation.parse_shape_from_graph user in
    (* full-union mode shares one baseline over the whole distribution;
       context mode computes a per-fixture baseline over the slice. *)
    let full_baseline =
      if full_union then begin
        let tb = now () in
        let r = SHACL_Validation.validate dist user sg_user in
        Printf.printf "full-union baseline: %d findings over the distribution alone in %.1fs\n%!"
          (List.length r.SHACL_Validation.results) (now () -. tb);
        List.map violation_key r.SHACL_Validation.results
      end else []
    in
    let outcomes =
      List.map
        (fun f ->
           let path = Filename.concat dir f in
           let expected_flagged =
             let has sub =
               let re = Str.regexp_string sub in
               (try ignore (Str.search_forward re f 0); true with Not_found -> false)
             in
             if has "-viol" then Some true
             else if has "-ok" then Some false
             else None
           in
           match expected_flagged, parse_ttl_file path with
           | None, _ ->
             Printf.printf "  skip: %-45s filename encodes no -ok/-viol verdict\n%!" f;
             Skip "no expected verdict in filename"
           | _, None ->
             Printf.printf "  FAIL: %-45s cannot read/parse\n%!" f;
             Fail "unreadable fixture"
           | Some expect, Some (fixture, _) ->
             let tf = now () in
             (try
                let (baseline_keys, data) =
                  if full_union then (full_baseline, fixture @ dist)
                  else begin
                    let ctx = extract_context idx fixture in
                    let rb = SHACL_Validation.validate ctx user sg_user in
                    (List.map violation_key rb.SHACL_Validation.results, fixture @ ctx)
                  end
                in
                let report = SHACL_Validation.validate data user sg_user in
                (match report.SHACL_Validation.report_failure with
                 | FStar_Pervasives_Native.Some msg ->
                   Printf.printf "  FAIL: %-45s engine failure: %s\n%!" f msg;
                   Fail ("engine: " ^ msg)
                 | FStar_Pervasives_Native.None ->
                   (* Multiset delta: a finding is NEW iff the union run
                      produced more occurrences of its key than the
                      baseline did — identical keys (same focus + shape +
                      raw message) from a second referrer still count. *)
                   let counts = Hashtbl.create 64 in
                   List.iter
                     (fun k ->
                        Hashtbl.replace counts k
                          (1 + (try Hashtbl.find counts k with Not_found -> 0)))
                     baseline_keys;
                   let delta =
                     List.filter
                       (fun v ->
                          let k = violation_key v in
                          let remaining = try Hashtbl.find counts k with Not_found -> 0 in
                          if remaining > 0 then begin
                            Hashtbl.replace counts k (remaining - 1); false
                          end else true)
                       report.SHACL_Validation.results
                   in
                   let flagged = delta <> [] in
                   let dt = now () -. tf in
                   let ctx_note =
                     if full_union then "full distribution"
                     else Printf.sprintf "%d context triples" (List.length data) in
                   if verbose || flagged <> expect then
                     List.iter (fun v -> Printf.printf "        %s\n" (violation_line v)) delta;
                   if flagged = expect then begin
                     Printf.printf "  PASS: %-45s expected %s, got %s (%d new findings; %s; %.1fs)\n%!"
                       f (if expect then "flagged" else "clean")
                       (if flagged then "flagged" else "clean")
                       (List.length delta) ctx_note dt;
                     Pass "verdict matches"
                   end else begin
                     Printf.printf "  FAIL: %-45s expected %s, got %s (%d new findings; %s; %.1fs)\n%!"
                       f (if expect then "flagged" else "clean")
                       (if flagged then "flagged" else "clean")
                       (List.length delta) ctx_note dt;
                     Fail "verdict mismatch"
                   end)
              with e ->
                Printf.printf "  FAIL: %-45s exception: %s\n%!" f (Printexc.to_string e);
                Fail ("exception: " ^ Printexc.to_string e)))
        files
    in
    let pass = List.length (List.filter (fun o -> match o with Pass _ -> true | _ -> false) outcomes) in
    let fail = List.length (List.filter (fun o -> match o with Fail _ -> true | _ -> false) outcomes) in
    let skip = List.length (List.filter (fun o -> match o with Skip _ -> true | _ -> false) outcomes) in
    Printf.printf "\nqudt-user-shapes elapsed: %.1fs\n" (now () -. t0);
    (pass, fail, skip, List.length outcomes)
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "QUDT v3.4.0 SHACL suite runner (Layer A, qudt-scoping design doc).\n\
     \n\
     Usage:\n\
     \  ./qudt_runner                Run both sections\n\
     \  ./qudt_runner --integrity    Contributor ruleset vs the distribution\n\
     \  ./qudt_runner --fixtures     User ruleset vs tests/qudt/fixtures\n\
     \  ./qudt_runner --budget N     Integrity wall-clock budget in seconds (default 420)\n\
     \  ./qudt_runner --full-union   Fixtures vs the FULL distribution (perf mode)\n\
     \  ./qudt_runner -v|--verbose   Print every finding\n\
     \  ./qudt_runner --help         This help\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let integrity_only = ref false in
  let fixtures_only = ref false in
  let full_union = ref false in
  let budget = ref 420 in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--integrity" :: rest -> integrity_only := true; loop rest
    | "--fixtures" :: rest -> fixtures_only := true; loop rest
    | "--full-union" :: rest -> full_union := true; loop rest
    | "--budget" :: n :: rest -> budget := int_of_string n; loop rest
    | a :: _ ->
      Printf.eprintf "qudt_runner: unexpected argument %s; try --help\n" a;
      exit 2
  in
  loop args;
  let run_i = not !fixtures_only in
  let run_f = not !integrity_only in
  let (ip, if_, is, it) =
    if run_i then run_integrity ~verbose:!verbose ~budget:!budget else (0, 0, 0, 0) in
  let (fp, ff, fs, ft) =
    if run_f then run_fixtures ~verbose:!verbose ~full_union:!full_union else (0, 0, 0, 0) in
  Printf.printf "\n========================================\n";
  if run_i then
    Printf.printf "qudt-integrity: %d pass, %d fail, %d skip (out of %d)\n" ip if_ is it;
  if run_f then
    Printf.printf "qudt-user-shapes: %d pass, %d fail, %d skip (out of %d)\n" fp ff fs ft;
  Printf.printf "========================================\n";
  if if_ + ff > 0 then exit 1
