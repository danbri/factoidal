(* selective_decode_differential_gate.ml -- the stage-2 differential
   gate for the OPTIONAL/FILTER row-index-selective decode design
   (docs/designissues/2026-07-13-optional-filter-selective-decode.md).

   Nothing calls `cottas_ondisk_search_tok_selective` from query
   evaluation yet (stage 4, a narrow single-BGP detector, is a follow-up
   landing) -- this is the ONLY thing exercising it before that lands,
   so it has to prove the mechanism itself is sound:

     (a) `cottas_ondisk_search_tok_selective cods bound col_need_all`
         returns EXACTLY the same rows, in the same order, as the
         unaccelerated `cottas_ondisk_search_tok cods bound`, for:
         a bound-predicate shape (wdt:P1057), a bound-subject shape,
         and an all-unbound (LIMIT-shaped) bound.

     (b) with a `col_need` that marks some position(s) NOT needed,
         every KEPT position (the ones `need` DID mark) still matches
         the reference exactly -- the unkept positions are read-once
         and ignored (see `cottas_qp_row_tok_selective`'s own contract:
         an unneeded position may be `None`; this test never reads it).

   Runs against the real gene COTTAS artifact (888,949 quads,
   examples/wikidata/subsets/lifesci-kgx/data/gene.ttl materialised via
   tools/bench_competitive.py) at whichever of the two known locations
   is present; skips (not fails) if neither is found, so this suite
   degrades gracefully on a checkout that hasn't built the corpus. *)

open RDF_Graph_Executable
open RDF_CottasStore

let passed = ref 0
let failed = ref 0
let skipped = ref false

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

let none = FStar_Pervasives_Native.None
let some x = FStar_Pervasives_Native.Some x

let candidate_paths =
  [ "/tmp/bench-competitive-v274mush/cottas-gene/gene-bench/v1/data.cottas";
    "../local/data/gene-bench/v1/data.cottas";
  ]

let find_artifact () : string option =
  List.find_opt Sys.file_exists candidate_paths

(* ------------------------------------------------------------------ *)
(* Row-shape comparison helpers                                       *)
(* ------------------------------------------------------------------ *)

(* Reference row -> selective row with every position "kept" (Some),
   for the col_need_all / gate-(a) comparison. *)
let selective_of_reference (r : cottas_qp_row_tok) : cottas_qp_row_tok_selective =
  { rst_s = some r.cqprt_s;
    rst_p = some r.cqprt_p;
    rst_o = some r.cqprt_o;
    rst_g = r.cqprt_g;
  }

let row_eq (a : cottas_qp_row_tok_selective) (b : cottas_qp_row_tok_selective) : bool =
  a.rst_s = b.rst_s && a.rst_p = b.rst_p && a.rst_o = b.rst_o && a.rst_g = b.rst_g

let rec rows_eq (a : cottas_qp_row_tok_selective list) (b : cottas_qp_row_tok_selective list) : bool =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> row_eq x y && rows_eq xs ys
  | _, _ -> false

(* gate (b): compare only the KEPT positions (per `need`) against the
   reference row's corresponding field; an unkept position is skipped
   entirely (never inspected on either side). *)
let kept_positions_eq (need : col_need) (ref_rows : cottas_qp_row_tok list)
    (sel_rows : cottas_qp_row_tok_selective list) : bool =
  List.length ref_rows = List.length sel_rows
  && List.for_all2
       (fun (r : cottas_qp_row_tok) (s : cottas_qp_row_tok_selective) ->
         (not need.cn_s || s.rst_s = some r.cqprt_s)
         && (not need.cn_p || s.rst_p = some r.cqprt_p)
         && (not need.cn_o || s.rst_o = some r.cqprt_o)
         && s.rst_g = r.cqprt_g)
       ref_rows sel_rows

(* ------------------------------------------------------------------ *)
(* Main                                                                *)
(* ------------------------------------------------------------------ *)

let () =
  Printf.printf "== selective_decode_differential_gate ==\n";
  match find_artifact () with
  | None ->
    skipped := true;
    Printf.printf "  SKIP  gene COTTAS artifact not found at any of:\n";
    List.iter (fun p -> Printf.printf "          %s\n" p) candidate_paths;
    Printf.printf "  (build via tools/bench_competitive.py; see the design doc's gate)\n"
  | Some path ->
    Printf.printf "  using artifact: %s\n" path;
    (match cottas_ondisk_open path with
     | FStar_Pervasives_Native.None ->
       incr failed;
       Printf.printf "  FAIL  cottas_ondisk_open returned None for %s\n" path
     | FStar_Pervasives_Native.Some cods ->
       let p1057 = "http://www.wikidata.org/prop/direct/P1057" in

       let bound_all_unbound : cottas_bound_qp_tok =
         { cbqpt_s = none; cbqpt_p = none; cbqpt_o = none; cbqpt_g = some "DEFAULT" } in
       let bound_pred : cottas_bound_qp_tok =
         { cbqpt_s = none; cbqpt_p = some ("<" ^ p1057 ^ ">"); cbqpt_o = none; cbqpt_g = some "DEFAULT" } in

       (* Reference rows for the bound-predicate shape, used both to
          derive a real on-disk subject for the bound-subject shape and
          as the (a)/(b) comparison baseline. *)
       let pred_ref_rows = cottas_ondisk_search_tok cods bound_pred in
       check ~name:"fixture sanity: wdt:P1057 has at least one row on this artifact"
         (List.length pred_ref_rows > 0);

       let bound_subj_opt =
         match pred_ref_rows with
         | r :: _ -> Some r.cqprt_s
         | [] -> None
       in

       let run_gate_a ~label (bound : cottas_bound_qp_tok) =
         let ref_rows = cottas_ondisk_search_tok cods bound in
         let sel_rows = cottas_ondisk_search_tok_selective cods bound col_need_all in
         check ~name:(Printf.sprintf "gate-a/%s: row count matches" label)
           (List.length ref_rows = List.length sel_rows);
         check ~name:(Printf.sprintf "gate-a/%s: rows byte-equal, in order, col_need_all" label)
           (rows_eq (List.rev (List.rev_map selective_of_reference ref_rows)) sel_rows);  (* rev_map: stdlib List.map is not stack-safe at 889k elems on OCaml 4.14 *)
         ref_rows
       in

       let pred_ref_rows2 = run_gate_a ~label:"bound-predicate(P1057)" bound_pred in
       ignore pred_ref_rows2;

       (match bound_subj_opt with
        | None ->
          incr failed;
          Printf.printf "  FAIL  could not derive a bound-subject anchor from the P1057 scan\n"
        | Some subj_tok ->
          let bound_subj : cottas_bound_qp_tok =
            { cbqpt_s = some subj_tok; cbqpt_p = none; cbqpt_o = none; cbqpt_g = some "DEFAULT" } in
          let subj_ref_rows = run_gate_a ~label:"bound-subject" bound_subj in

          (* gate (b): with need = {cn_s=false; cn_p=true; cn_o=true} on
             the bound-subject shape (?s is CONSTANT here anyway, so
             gating it off is the interesting case -- s is always filled
             from the bound token regardless of `need`, per the
             mechanism's own contract: bound positions never need
             decode). Every kept position (p, o, g) must still match. *)
          let need_no_s : col_need = { cn_s = false; cn_p = true; cn_o = true } in
          let sel_no_s = cottas_ondisk_search_tok_selective cods bound_subj need_no_s in
          check ~name:"gate-b/bound-subject: kept positions (p,o,g) match with cn_s=false"
            (kept_positions_eq need_no_s subj_ref_rows sel_no_s);
          check ~name:"gate-b/bound-subject: s is still Some (filled from the bound, not gated by need)"
            (List.for_all (fun (r : cottas_qp_row_tok_selective) -> r.rst_s <> none) sel_no_s));

       let need_p_only : col_need = { cn_s = false; cn_p = true; cn_o = false } in
       let sel_p_only = cottas_ondisk_search_tok_selective cods bound_pred need_p_only in
       check ~name:"gate-b/bound-predicate: kept position (p) matches with cn_s=cn_o=false"
         (kept_positions_eq need_p_only pred_ref_rows sel_p_only);
       check ~name:"gate-b/bound-predicate: p is still Some (bound position, always filled)"
         (List.for_all (fun (r : cottas_qp_row_tok_selective) -> r.rst_p <> none) sel_p_only);
       check ~name:"gate-b/bound-predicate: s is None (unbound, not needed)"
         (List.for_all (fun (r : cottas_qp_row_tok_selective) -> r.rst_s = none) sel_p_only);
       check ~name:"gate-b/bound-predicate: o is None (unbound, not needed)"
         (List.for_all (fun (r : cottas_qp_row_tok_selective) -> r.rst_o = none) sel_p_only);

       let need_o_only : col_need = { cn_s = false; cn_p = false; cn_o = true } in
       let sel_o_only = cottas_ondisk_search_tok_selective cods bound_pred need_o_only in
       check ~name:"gate-b/bound-predicate: kept position (o) matches with cn_s=cn_p=false"
         (kept_positions_eq need_o_only pred_ref_rows sel_o_only);

       (* All-unbound (LIMIT-shaped) bound: every position unbound. This
          is the shape a `LIMIT`-bearing SELECT * WHERE { ?s ?p ?o }
          would present to the store seam. col_need_all here forces
          both sides to decode every column of every row group -- the
          differential gate's most expensive case, so it runs LAST. *)
       ignore (run_gate_a ~label:"all-unbound(LIMIT-shaped)" bound_all_unbound));

  Printf.printf "\nselective_decode_differential_gate: %d pass, %d fail (out of %d)%s\n"
    !passed !failed (!passed + !failed)
    (if !skipped then " [SKIPPED: artifact not found]" else "");
  if !failed > 0 then exit 1
