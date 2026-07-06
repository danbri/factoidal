(* factoidal --explain — plan-only dump of a SPARQL query against a COTTAS
   on-disk store. Parses + builds algebra + per-pattern cardinality estimates;
   does NOT execute the BGP walk.

   Used to diagnose query-planner regressions. The Q03 use case
   (`?s ?p ?o . ?o a geo:wktLiteral LIMIT 3`) regressed from "graceful
   empty in 7s" to a 30s timeout because the optimiser walks both BGP
   triples instead of short-circuiting on T2's empty bound-object
   estimate. Without `--explain` we have to run the query for 30s and
   grep ~1500 trace lines to see why. With it: ms-scale plan dump.

   This file is hand-written CLI glue, not F*-extracted. The actual
   estimate / index lookups all go through F*-verified entrypoints in
   RDF.CottasStore + SPARQL11.Store. We only walk the algebra tree from
   OCaml and report what F* told us. (Per CLAUDE.md rule #15 — glue
   does not contain RDF/SPARQL semantic logic.)

   See docs/designissues/2026-04-26-pe5-explain-mode.md. *)

module A = SPARQL11_Algebra
module S = SPARQL11_Store
module C = RDF_CottasStore
module G = RDF_Graph_Executable
module P = Parser_BallyhooCOTTAS  (* cottas_bound_qp etc. *)

(* =========================================================================
   Pretty-printing the algebra tree.

   Indented multi-line dump showing every GP_* constructor + the
   triple_pattern leaves. Keep it scannable; the format is for humans.
   ========================================================================= *)

(* Pretty-printers — F* is the source of truth.
   Logic lives in formal/fstar/RDF.Pretty.fst (extracted as
   RDF_Pretty.ml). The aliases below preserve the legacy names so
   the rest of this file (print_ggp, explain_query, JSON renderers)
   compiles unchanged. *)
let term_short (t : G.rdf_term) : string =
  RDF_Pretty.term_short_explain t

let pattern_term_short (pt : A.pattern_term) : string =
  RDF_Pretty.pattern_term_short_explain pt

let pattern_subject_short (ps : A.pattern_subject) : string =
  RDF_Pretty.pattern_subject_short_explain ps

let triple_pattern_short (tp : A.triple_pattern) : string =
  RDF_Pretty.triple_pattern_short_explain tp

(* Indent + print a group_graph_pattern recursively. *)
let rec print_ggp (out : out_channel) (depth : int) (p : A.group_graph_pattern) : unit =
  let ind = String.make (depth * 2) ' ' in
  match p with
  | A.GP_BGP tps ->
    Printf.fprintf out "%sBGP\n" ind;
    List.iter (fun tp ->
      Printf.fprintf out "%s  %s\n" ind (triple_pattern_short tp)
    ) tps
  | A.GP_Join (p1, p2) ->
    Printf.fprintf out "%sJoin\n" ind;
    print_ggp out (depth+1) p1;
    print_ggp out (depth+1) p2
  | A.GP_LeftJoin (p1, p2, _e) ->
    Printf.fprintf out "%sLeftJoin (OPTIONAL)\n" ind;
    print_ggp out (depth+1) p1;
    print_ggp out (depth+1) p2
  | A.GP_Filter (_e, p1) ->
    Printf.fprintf out "%sFilter\n" ind;
    print_ggp out (depth+1) p1
  | A.GP_Union (p1, p2) ->
    Printf.fprintf out "%sUnion\n" ind;
    print_ggp out (depth+1) p1;
    print_ggp out (depth+1) p2
  | A.GP_Graph (gt, p1) ->
    Printf.fprintf out "%sGraph %s\n" ind (pattern_term_short gt);
    print_ggp out (depth+1) p1
  | A.GP_Minus (p1, p2) ->
    Printf.fprintf out "%sMinus\n" ind;
    print_ggp out (depth+1) p1;
    print_ggp out (depth+1) p2
  | A.GP_Lateral (p1, p2) ->
    Printf.fprintf out "%sLateral\n" ind;
    print_ggp out (depth+1) p1;
    print_ggp out (depth+1) p2
  | A.GP_Bind (_e, v, p1) ->
    Printf.fprintf out "%sBind ?%s\n" ind v;
    print_ggp out (depth+1) p1
  | A.GP_Values (vars, _rows) ->
    Printf.fprintf out "%sValues [%s]\n" ind
      (String.concat ", " (List.map (fun v -> "?" ^ v) vars))
  | A.GP_Service (iri, p1, _silent) ->
    Printf.fprintf out "%sService <%s>\n" ind iri;
    print_ggp out (depth+1) p1
  | A.GP_ServiceVar (v, p1, _silent) ->
    Printf.fprintf out "%sServiceVar ?%s\n" ind v;
    print_ggp out (depth+1) p1
  | A.GP_SubSelect _ ->
    Printf.fprintf out "%sSubSelect (...)\n" ind
  | A.GP_PropertyPath (s, _pp, o) ->
    Printf.fprintf out "%sPropertyPath %s ... %s\n" ind
      (pattern_subject_short s) (pattern_term_short o)
  | A.GP_Empty ->
    Printf.fprintf out "%sEmpty\n" ind

(* Wrap the algebra dump with the solution-modifier shell (Project / Slice
   / Distinct / OrderBy) so it looks like SPARQL-algebra output. *)
let print_query_algebra (out : out_channel) (q : A.query) : unit =
  let m = q.A.q_modifier in
  let limit_str =
    match m.A.sm_limit, m.A.sm_offset with
    | None, None -> None
    | Some l, None -> Some (Printf.sprintf "Slice limit=%s" (Z.to_string l))
    | None, Some o -> Some (Printf.sprintf "Slice offset=%s" (Z.to_string o))
    | Some l, Some o ->
      Some (Printf.sprintf "Slice offset=%s limit=%s" (Z.to_string o) (Z.to_string l))
  in
  let header =
    match q.A.q_form with
    | A.QF_Select (A.Select_Vars items) ->
      let vars = List.map (fun it -> match it with
        | A.SI_Var v -> "?" ^ v
        | A.SI_Expr (_, v) -> "?" ^ v
      ) items in
      Some (Printf.sprintf "Project [%s]" (String.concat ", " vars))
    | A.QF_Select A.Select_All -> Some "Project [*]"
    | A.QF_Construct _ -> Some "Construct"
    | A.QF_Ask -> Some "Ask"
    | A.QF_Describe _ -> Some "Describe"
  in
  let depth = ref 0 in
  (match header with
   | Some h -> Printf.fprintf out "%s\n" h; incr depth
   | None -> ());
  if m.A.sm_distinct then begin
    Printf.fprintf out "%sDistinct\n" (String.make (!depth * 2) ' ');
    incr depth
  end;
  (match limit_str with
   | Some s -> Printf.fprintf out "%s%s\n" (String.make (!depth * 2) ' ') s; incr depth
   | None -> ());
  (match m.A.sm_order_by with
   | Some _ ->
     Printf.fprintf out "%sOrderBy [...]\n" (String.make (!depth * 2) ' ');
     incr depth
   | None -> ());
  print_ggp out !depth q.A.q_pattern

(* =========================================================================
   Walk the algebra to extract every triple_pattern (with a positional
   path label) so we can run per-pattern estimates and report join order.

   The label is a "T1.0", "T2.0" etc. - flat counter for now; per-bgp
   labels could be added later if needed.
   ========================================================================= *)

let collect_triple_patterns (q : A.query) : (string * A.triple_pattern) list =
  let counter = ref 0 in
  let acc : (string * A.triple_pattern) list ref = ref [] in
  let label_of () = incr counter; Printf.sprintf "T%d" !counter in
  let rec go (p : A.group_graph_pattern) : unit =
    match p with
    | A.GP_BGP tps -> List.iter (fun tp ->
        acc := (label_of (), tp) :: !acc) tps
    | A.GP_Join (p1, p2) -> go p1; go p2
    | A.GP_LeftJoin (p1, p2, _) -> go p1; go p2
    | A.GP_Filter (_, p1) -> go p1
    | A.GP_Union (p1, p2) -> go p1; go p2
    | A.GP_Graph (_, p1) -> go p1
    | A.GP_Minus (p1, p2) -> go p1; go p2
    | A.GP_Lateral (p1, p2) -> go p1; go p2
    | A.GP_Bind (_, _, p1) -> go p1
    | A.GP_Service (_, p1, _) -> go p1
    | A.GP_ServiceVar (_, p1, _) -> go p1
    | A.GP_SubSelect _ -> ()  (* deliberately don't recurse — sub-selects have own scope *)
    | A.GP_Values (_, _) -> ()
    | A.GP_PropertyPath (_, _, _) -> ()
    | A.GP_Empty -> ()
  in
  go q.A.q_pattern;
  List.rev !acc

(* Pull the BGP back out of a GP_BGP wrapper for choose_best_tp_backend. *)
(* bgps_in_query lives in F* per rule #1; see
   formal/fstar/SPARQL.Query.Analysis.fst. *)
let bgps_in_query : A.query -> A.bgp list =
  SPARQL_Query_Analysis.bgps_in_query

(* =========================================================================
   Per-triple-pattern explain row.

   For each triple_pattern in the query, we report:
     - bound channels: which of (s, p, o) is concrete (vs variable)
     - dictionary hits: for each concrete bound, did the on-disk store's
       reverse-map find the term? (None → definitively-empty result.)
     - estimate: backend_estimate of the pattern with empty mu
     - predicate-presence: cottas_ondisk_predicate_present (for bound pred)

   The estimate is the value the optimiser will use for join-ordering
   via choose_best_tp_backend / estimate_tp_backend_mu. Reporting it
   directly tells us why the optimiser picked the order it did.
   ========================================================================= *)

(* Issue #110 retirement (2026-04-29): the OCaml-side
   `estimate_fast_inner` Mem5 bypass was retired with the rest of the
   dead-on-public-path COTTAS shims. Use the F*-extracted public
   `cottas_ondisk_estimate` for all bound shapes. If a future
   estimate path turns out to be too slow on 3M-row corpora,
   speed it up in F*, not by re-introducing an OCaml bypass
   (rule #11). *)
let cottas_estimate_quick
    (cods : C.cottas_ondisk_store)
    (bound : P.cottas_bound_qp)
  : int =
  Z.to_int (C.cottas_ondisk_estimate cods bound)

(* bound_status type and bs_string renderer live in F* per rule #1
   (formal/fstar/SPARQL.Explain.fst). The re-export below preserves
   the constructor names for the rest of the file. *)
type bound_status = SPARQL_Explain.bound_status =
  | BS_Var of string
  | BS_Hit of string
  | BS_Miss of string
  | BS_Other of string

let bs_string : bound_status -> string = SPARQL_Explain.bs_string

(* For each leaf triple-pattern + a single-store cottas-ondisk handle, return
   - subject status (var or hit/miss)
   - predicate status
   - object status
   - whether the encoded bound succeeded (None → result definitely empty)
   - the F*-computed estimate via cottas_ondisk_estimate
   - whether predicate-presence said the predicate exists

   The record type and JSON renderers (`bs_json`, `tpx_json`) live in F* per
   rule #1 (formal/fstar/SPARQL.Explain.fst). The alias below keeps the
   legacy field names visible to the rest of this file unchanged.
   F* extracts `int` as `Prims.int = Z.t`, so `tpx_estimate` is `Z.t` here;
   call sites convert with `Z.of_int` / `Z.to_int` at the boundary. *)
type tp_explain = SPARQL_Explain.tp_explain = {
  tpx_label : string;
  tpx_tp : A.triple_pattern;
  tpx_s_status : bound_status;
  tpx_p_status : bound_status;
  tpx_o_status : bound_status;
  tpx_bound_built : bool;
  tpx_pred_present : bool option;
  tpx_estimate : Prims.int;
}

let explain_triple_pattern_against_store
    (cods : C.cottas_ondisk_store)
    (label : string)
    (tp : A.triple_pattern)
  : tp_explain =
  (* Subject status *)
  let s_status, s_bound = match tp.A.tp_s with
    | A.PS_Var v -> BS_Var v, None
    | A.PS_IRI i ->
      let r = C.cottas_ondisk_encode_subject_ml cods (G.S_IRI i) in
      (match r with
       | FStar_Pervasives_Native.Some _ ->
         BS_Hit (term_short (G.T_IRI i)), Some (G.S_IRI i)
       | FStar_Pervasives_Native.None ->
         BS_Miss (term_short (G.T_IRI i)), Some (G.S_IRI i))
    | A.PS_BNode b ->
      let r = C.cottas_ondisk_encode_subject_ml cods (G.S_BNode b) in
      (match r with
       | FStar_Pervasives_Native.Some _ ->
         BS_Hit ("_:" ^ b), Some (G.S_BNode b)
       | FStar_Pervasives_Native.None ->
         BS_Miss ("_:" ^ b), Some (G.S_BNode b))
  in
  (* Predicate status *)
  let p_status, p_bound = match tp.A.tp_p with
    | A.PT_Var v -> BS_Var v, None
    | A.PT_IRI i ->
      let r = C.cottas_ondisk_encode_predicate_ml cods i in
      (match r with
       | FStar_Pervasives_Native.Some _ ->
         BS_Hit (term_short (G.T_IRI i)), Some i
       | FStar_Pervasives_Native.None ->
         BS_Miss (term_short (G.T_IRI i)), Some i)
    | A.PT_BNode _ -> BS_Other "bnode-as-predicate", None
    | A.PT_Literal l -> BS_Other ("literal-as-predicate: " ^ l.G.lexical_form), None
  in
  (* Object status *)
  let o_status, o_bound = match tp.A.tp_o with
    | A.PT_Var v -> BS_Var v, None
    | A.PT_IRI i ->
      let r = C.cottas_ondisk_encode_object_ml cods (G.T_IRI i) in
      (match r with
       | FStar_Pervasives_Native.Some _ ->
         BS_Hit (term_short (G.T_IRI i)), Some (G.T_IRI i)
       | FStar_Pervasives_Native.None ->
         BS_Miss (term_short (G.T_IRI i)), Some (G.T_IRI i))
    | A.PT_BNode b ->
      let r = C.cottas_ondisk_encode_object_ml cods (G.T_BNode b) in
      (match r with
       | FStar_Pervasives_Native.Some _ ->
         BS_Hit ("_:" ^ b), Some (G.T_BNode b)
       | FStar_Pervasives_Native.None ->
         BS_Miss ("_:" ^ b), Some (G.T_BNode b))
    | A.PT_Literal l ->
      let r = C.cottas_ondisk_encode_object_ml cods (G.T_Literal l) in
      (match r with
       | FStar_Pervasives_Native.Some _ ->
         BS_Hit (term_short (G.T_Literal l)), Some (G.T_Literal l)
       | FStar_Pervasives_Native.None ->
         BS_Miss (term_short (G.T_Literal l)), Some (G.T_Literal l))
  in
  (* Build the bound (None means definitely empty). *)
  let bound_opt = C.cottas_ondisk_build_bound_qp_opt
    cods
    (match s_bound with Some s -> FStar_Pervasives_Native.Some s | None -> FStar_Pervasives_Native.None)
    (match p_bound with Some p -> FStar_Pervasives_Native.Some p | None -> FStar_Pervasives_Native.None)
    (match o_bound with Some o -> FStar_Pervasives_Native.Some o | None -> FStar_Pervasives_Native.None)
    (* issue #267: a bare triple pattern estimates against the default
       graph only, matching BGP dataset semantics. *)
    C.COS_DefaultOnly
  in
  let bound_built, estimate = match bound_opt with
    | FStar_Pervasives_Native.None -> false, 0
    | FStar_Pervasives_Native.Some bound ->
      (* Bypass the slow data-page walk for bound_p + bound_o queries
         (see cottas_estimate_quick above). *)
      true, cottas_estimate_quick cods bound
  in
  let pred_present = match p_bound with
    | None -> None
    | Some p -> Some (C.cottas_ondisk_predicate_present cods p)
  in
  {
    tpx_label = label;
    tpx_tp = tp;
    tpx_s_status = s_status;
    tpx_p_status = p_status;
    tpx_o_status = o_status;
    tpx_bound_built = bound_built;
    tpx_pred_present = pred_present;
    tpx_estimate = Z.of_int estimate;
  }

(* =========================================================================
   Reproduce the F* optimiser's choose_best order without executing.

   choose_best_tp_backend takes a bgp + graph_backend + mu and picks the
   pattern with the lowest estimate; we walk it iteratively to extract the
   full ordering. Pure repro of the F* logic, calling F* primitives. We
   build the SAME GB_CottasOnDisk wrapper the engine uses.
   ========================================================================= *)

(* Direct call to F*'s real choose_best_tp_backend. Iteratively pick
   the smallest-estimate pattern under empty mu, exactly as the
   runtime planner does at eval time. This is the GROUND-TRUTH
   planner output — what the engine actually decides.

   Performance note: this calls F*'s estimate path which on a
   COTTAS store routes through Mem5's bitmap fast path -> usually
   microseconds per call. So calling F*'s planner from --explain
   is fine.

   #200 Section C 4/4 (2026-05-10): the parallel OCaml reimpl
   (`optimiser_order_for_bgp_from_explains`, formerly defined here)
   was an explicitly known-divergent shadow used to surface drift
   during Pe5 unwinding. F* is the sole ground truth now. *)
let optimiser_order_via_fstar
    (gb : S.graph_backend)
    (patterns : A.bgp)
  : A.triple_pattern list =
  let rec loop remaining acc =
    match S.choose_best_tp_backend remaining gb A.sm_empty with
    | FStar_Pervasives_Native.None -> List.rev acc
    | FStar_Pervasives_Native.Some (chosen, rest) ->
      loop rest (chosen :: acc)
  in
  loop patterns []

(* =========================================================================
   Top-level entry: explain a query against one or more cottas-ondisk
   stores. Pretty-prints to `out` (default stdout); JSON to `json_out` if
   provided.
   ========================================================================= *)

(* Find the index of a triple_pattern in a list — for labelling join order. *)
let rec index_of_tp (tp : A.triple_pattern) (tps : (string * A.triple_pattern) list) : string option =
  match tps with
  | [] -> None
  | (lbl, t) :: rest ->
    if t == tp then Some lbl  (* physical equality on AST node *)
    else if A.pattern_subject_eq t.A.tp_s tp.A.tp_s
         && A.pattern_term_eq t.A.tp_p tp.A.tp_p
         && A.pattern_term_eq t.A.tp_o tp.A.tp_o then Some lbl
    else index_of_tp tp rest

(* json_escape lives in F* per rule #1 (PR #126 migrated it to
   SPARQL.JSON.Escape). The local copy here was a duplicate; this
   alias keeps the local symbol for downstream callers. *)
let json_escape : string -> string = SPARQL_JSON_Escape.json_escape

(* bs_json and tpx_json live in F* per rule #1
   (formal/fstar/SPARQL.Explain.fst). The OCaml glue may not carry
   rendering logic (rule #11). *)
let bs_json : bound_status -> string = SPARQL_Explain.bs_json

let tpx_json : tp_explain -> string = SPARQL_Explain.tpx_json

(* =========================================================================
   Index-use summary.

   For each per-pattern explain row, surface which on-disk index files
   the planner would consult. Today the F* code consults:
     - .p.offsets   (Lamed3 — predicate row offsets)
     - .p.presence  (Yod6  — predicate-rg presence bitmap)
     - .s.presence  (Tet3  — subject-rg presence bitmap)
     - .o.presence  (Tet3  — object-rg presence bitmap)
     - .s.dict / .p.dict / .o.dict / .g.dict (Vav3 — mmap'd dictionaries)

   Decision rules (from RDF.CottasStore.fst):
     - Any concrete bound on a column → its `.dict` will be consulted at
       open() time (revmap_lookup encodes the term).
     - Bound predicate → cottas_ondisk_predicate_present + plan_candidate_rgs
       walks the predicate column → `.p.presence` consulted.
     - Bound subject → plan_candidate_rgs walks subject column → `.s.presence`.
     - Bound object → plan_candidate_rgs walks object column → `.o.presence`.

   Lamed3 `.p.offsets` is consulted by the BGP walker's per-rg
   per-predicate row offsets path (estimate_fast_via_offsets in
   walk_candidate_rgs_search_fast); we report it as "available" iff
   any pattern has a bound predicate.
   ========================================================================= *)

let print_index_use_summary (out : out_channel) (rows : tp_explain list) : unit =
  let bound_s_labels = List.filter_map (fun r ->
    match r.tpx_s_status with BS_Hit _ | BS_Miss _ -> Some r.tpx_label | _ -> None) rows in
  let bound_p_labels = List.filter_map (fun r ->
    match r.tpx_p_status with BS_Hit _ | BS_Miss _ -> Some r.tpx_label | _ -> None) rows in
  let bound_o_labels = List.filter_map (fun r ->
    match r.tpx_o_status with BS_Hit _ | BS_Miss _ -> Some r.tpx_label | _ -> None) rows in
  let labels_str = function
    | [] -> "(none)"
    | xs -> String.concat " " xs
  in
  Printf.fprintf out "=== INDEX-USE SUMMARY ===\n";
  Printf.fprintf out "Vav3 dict.s.dict     : encode subjects for: %s\n" (labels_str bound_s_labels);
  Printf.fprintf out "Vav3 dict.p.dict     : encode predicates for: %s\n" (labels_str bound_p_labels);
  Printf.fprintf out "Vav3 dict.o.dict     : encode objects for: %s\n" (labels_str bound_o_labels);
  Printf.fprintf out "Tet3 .s.presence     : %s\n"
    (if bound_s_labels = [] then "not consulted (no bound subject)"
     else "consulted by plan_candidate_rgs for: " ^ labels_str bound_s_labels);
  Printf.fprintf out "Yod6 .p.presence     : %s\n"
    (if bound_p_labels = [] then "not consulted (no bound predicate)"
     else "consulted by plan_candidate_rgs for: " ^ labels_str bound_p_labels);
  Printf.fprintf out "Tet3 .o.presence     : %s\n"
    (if bound_o_labels = [] then "not consulted (no bound object)"
     else "consulted by plan_candidate_rgs for: " ^ labels_str bound_o_labels);
  Printf.fprintf out "Lamed3 .p.offsets    : %s\n"
    (if bound_p_labels = [] then "not consulted (no bound predicate)"
     else "available for fast walk in: " ^ labels_str bound_p_labels)

(* =========================================================================
   Main entry: explain a query against one cottas-ondisk path.

   We open the store, parse the query, walk the algebra, run estimates,
   and emit human + optional JSON output. No execution.
   ========================================================================= *)

let explain_query
    ~(query_text : string)
    ~(cottas_paths : string list)
    ?(json_out : out_channel option = None)
    () : int =
  let out = stdout in
  (* Set line-buffering on stdout so traces from F* (eprintf) and our
     headers interleave readably in piped/redirected output. *)
  set_binary_mode_out out false;
  let t0 = Unix.gettimeofday () in
  Printf.fprintf out "=== PARSE ===\n"; flush out;
  (* Show the query stripped of comment-only lines, single newline. *)
  let trimmed_q = String.trim query_text in
  Printf.fprintf out "%s\n\n" trimmed_q;

  (* Parse SPARQL *)
  let q = match SPARQL11_Parser.parse_sparql query_text with
    | SPARQL11_Parser.ParseOk (q, _) -> q
    | SPARQL11_Parser.ParseErr msg ->
      Printf.eprintf "SPARQL parse error: %s\n" msg; exit 1
  in
  let t_parse = Unix.gettimeofday () in

  (* Open all cottas stores (must have at least one). *)
  if cottas_paths = [] then begin
    Printf.eprintf "Error: --explain requires at least one --data-cottas FILE\n";
    exit 1
  end;
  let stores = List.map (fun p ->
    match C.cottas_ondisk_open p with
    | FStar_Pervasives_Native.Some s ->
      (* Pre-warm via mmap'd companion files (Vav3). On parliament this
         is <2s if .s.dict / .p.dict / .o.dict / .g.dict / .p.offsets
         / .*.presence companions already exist next to data.cottas
         (which they do, because the running daemon built them). Without
         this, the first call to cottas_ondisk_estimate would walk all
         row groups to populate the dict — minutes of warm-up. *)
      (try C.Cottas_companion_boot.prewarm_via_companions p s.C.cods_handle
       with e ->
         Printf.eprintf "[explain] pre-warm failed: %s (continuing with lazy populator)\n%!"
           (Printexc.to_string e));
      (p, s)
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "Error: cottas_ondisk_open returned None for %s\n" p;
      exit 1
  ) cottas_paths in
  let t_open = Unix.gettimeofday () in

  (* Print algebra. *)
  Printf.fprintf out "=== ALGEBRA ===\n"; flush out;
  print_query_algebra out q;
  Printf.fprintf out "\n"; flush out;
  let t_algebra = Unix.gettimeofday () in

  (* Per-triple-pattern explain rows.

     For now: explain each pattern against the FIRST cottas store. Multi-store
     UNION explains would be useful but add complexity; if you have a mix of
     in-memory + cottas, the explain_query call is single-store. *)
  let (_first_path, first_store) = List.hd stores in
  let labelled_tps = collect_triple_patterns q in

  Printf.fprintf out "=== BGP PLAN (%d triple%s) ===\n"
    (List.length labelled_tps)
    (if List.length labelled_tps = 1 then "" else "s");
  flush out;
  let rows = List.map (fun (lbl, tp) ->
    explain_triple_pattern_against_store first_store lbl tp
  ) labelled_tps in
  List.iter (fun r ->
    Printf.fprintf out "[%s] %s\n" r.tpx_label (triple_pattern_short r.tpx_tp);
    Printf.fprintf out "    s: %s\n" (bs_string r.tpx_s_status);
    Printf.fprintf out "    p: %s\n" (bs_string r.tpx_p_status);
    Printf.fprintf out "    o: %s\n" (bs_string r.tpx_o_status);
    Printf.fprintf out "    bound built: %b%s\n" r.tpx_bound_built
      (if not r.tpx_bound_built then "  <-- definitely empty (a bound term missing from dict)" else "");
    (match r.tpx_pred_present with
     | None -> ()
     | Some b ->
       Printf.fprintf out "    predicate-presence: %s\n"
         (if b then "true (present in dictionary)"
          else "false (predicate ABSENT from corpus)"));
    Printf.fprintf out "    estimate: %s row(s)\n" (Z.to_string r.tpx_estimate);
    Printf.fprintf out "\n";
    flush out
  ) rows;
  let t_estimate = Unix.gettimeofday () in

  (* Optimiser join order: per-BGP, mirror choose_best_tp_backend using
     our pre-computed (fast) estimates so we don't re-trigger the slow
     data-page walk. *)
  Printf.fprintf out "=== JOIN ORDER (per BGP) ===\n"; flush out;
  let bgps = bgps_in_query q in
  (* Build the GB_CottasOnDisk wrapper the engine uses, so we can call
     F*'s real choose_best_tp_backend on it (issue #267: the scope arg
     is now explicit — COS_DefaultOnly = default graph). *)
  let gb = S.GB_CottasOnDisk (first_store, C.COS_DefaultOnly) in
  let render_order out_label order =
    Printf.fprintf out "  %s:" out_label;
    List.iter (fun tp ->
      let lbl = match index_of_tp tp labelled_tps with
        | Some l -> l
        | None -> "?" in
      let est = match List.find_opt (fun r ->
        A.pattern_subject_eq r.tpx_tp.A.tp_s tp.A.tp_s
        && A.pattern_term_eq r.tpx_tp.A.tp_p tp.A.tp_p
        && A.pattern_term_eq r.tpx_tp.A.tp_o tp.A.tp_o) rows with
        | Some r -> Z.to_string r.tpx_estimate
        | None -> "-1" in
      Printf.fprintf out " %s(est=%s)" lbl est
    ) order;
    Printf.fprintf out "\n"
  in
  List.iteri (fun i tps ->
    Printf.fprintf out "  BGP #%d: %d triple%s\n" (i+1) (List.length tps)
      (if List.length tps = 1 then "" else "s");
    (* GROUND TRUTH: F*'s real planner. *)
    let order_fstar = optimiser_order_via_fstar gb tps in
    render_order "F* planner (runtime ground truth)" order_fstar
  ) bgps;
  Printf.fprintf out "\n";

  (* Index-use summary. *)
  print_index_use_summary out rows;
  Printf.fprintf out "\n";

  let t_done = Unix.gettimeofday () in
  Printf.fprintf out "=== ELAPSED ===\n";
  Printf.fprintf out "parse=%.1fms  open=%.1fms  algebra=%.1fms  estimate=%.1fms  total=%.1fms  (no execution)\n"
    ((t_parse -. t0) *. 1000.0)
    ((t_open -. t_parse) *. 1000.0)
    ((t_algebra -. t_open) *. 1000.0)
    ((t_estimate -. t_algebra) *. 1000.0)
    ((t_done -. t0) *. 1000.0);

  (* Optional JSON output. *)
  (match json_out with
   | None -> ()
   | Some jc ->
     Printf.fprintf jc "{\n";
     Printf.fprintf jc "  \"query\": \"%s\",\n" (json_escape trimmed_q);
     Printf.fprintf jc "  \"cottas_paths\": [%s],\n"
       (String.concat ", " (List.map (fun p -> "\"" ^ json_escape p ^ "\"") cottas_paths));
     Printf.fprintf jc "  \"triple_patterns\": [\n    ";
     Printf.fprintf jc "%s" (String.concat ",\n    " (List.map tpx_json rows));
     Printf.fprintf jc "\n  ],\n";
     Printf.fprintf jc "  \"timing_ms\": {\n";
     Printf.fprintf jc "    \"parse\": %.3f,\n" ((t_parse -. t0) *. 1000.0);
     Printf.fprintf jc "    \"open\":  %.3f,\n" ((t_open -. t_parse) *. 1000.0);
     Printf.fprintf jc "    \"algebra\": %.3f,\n" ((t_algebra -. t_open) *. 1000.0);
     Printf.fprintf jc "    \"estimate\": %.3f,\n" ((t_estimate -. t_algebra) *. 1000.0);
     Printf.fprintf jc "    \"total\": %.3f\n" ((t_done -. t0) *. 1000.0);
     Printf.fprintf jc "  }\n";
     Printf.fprintf jc "}\n");
  0
