(* selective_decode_vars_unit.ml -- stage 1 unit tests for the
   OPTIONAL/FILTER row-index-selective decode design
   (docs/designissues/2026-07-13-optional-filter-selective-decode.md).

   Pins `expr_vars` (SPARQL11.Algebra.fst), `query_live_vars`, and
   `col_need_for_tp` -- pure, unwired free-variable / needed-column
   analysis. Nothing calls these from the evaluator yet (stage 4, a
   narrow single-BGP detector, is a follow-up landing); this suite is
   the only thing exercising them until then.

   Checklist covered (design doc's stage 1 bullet):
     - every var-carrying `expr` constructor contributes its var(s)
     - SELECT * means everything live
     - FILTER/HAVING/ORDER BY/BIND free vars are included
     - bound (constant) triple-pattern positions never need decode
     - cross-pattern join vars and within-BGP repeats count as live *)

open RDF_Graph_Executable
open SPARQL11_Algebra

let passed = ref 0
let failed = ref 0

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

let none = FStar_Pervasives_Native.None
let some x = FStar_Pervasives_Native.Some x
let n (i : int) : expr = E_NumericLit (Z.of_int i)

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

let set_eq (a : string list) (b : string list) : bool =
  let sa = List.sort_uniq compare a and sb = List.sort_uniq compare b in
  sa = sb

let subset (a : string list) (b : string list) : bool =
  List.for_all (fun x -> List.mem x b) a

let default_modifier : solution_modifier = {
  sm_order_by = none;
  sm_distinct = false;
  sm_reduced  = false;
  sm_offset   = none;
  sm_limit    = none;
}

let mk_query
    ?(group_by = none)
    ?(having   = none)
    ?(modifier = default_modifier)
    ?(values   = none)
    (form : query_form) (pattern : group_graph_pattern) : query =
  {
    q_base     = none;
    q_prefixes = [];
    q_form     = form;
    q_dataset  = [];
    q_pattern  = pattern;
    q_group_by = group_by;
    q_having   = having;
    q_modifier = modifier;
    q_values   = values;
  }

let tp (s : pattern_subject) (p : pattern_term) (o : pattern_term) : triple_pattern =
  { tp_s = s; tp_p = p; tp_o = o }

let iri_p (i : string) : pattern_term = PT_IRI i

let bgp1 (t : triple_pattern) : group_graph_pattern = GP_BGP [t]

(* ------------------------------------------------------------------ *)
(* 1. expr_vars: every var-carrying constructor contributes            *)
(* ------------------------------------------------------------------ *)

let () =
  check ~name:"expr_vars: E_Var"
    (set_eq (expr_vars (E_Var "x")) ["x"]);
  check ~name:"expr_vars: literals/constants contribute nothing"
    (expr_vars (E_BoolLit true) = [] &&
     expr_vars (n 1) = [] &&
     expr_vars E_Now = []);
  check ~name:"expr_vars: E_Arith both sides"
    (set_eq (expr_vars (E_Arith (Add, E_Var "a", E_Var "b"))) ["a"; "b"]);
  check ~name:"expr_vars: E_Compare both sides"
    (set_eq (expr_vars (E_Compare (CmpEq, E_Var "a", E_Var "b"))) ["a"; "b"]);
  check ~name:"expr_vars: E_And / E_Or / E_Not"
    (set_eq (expr_vars (E_And (E_Var "a", E_Or (E_Var "b", E_Not (E_Var "c")))))
       ["a"; "b"; "c"]);
  check ~name:"expr_vars: E_IsIRI/E_IsBlank/E_IsLiteral/E_IsNumeric"
    (set_eq (expr_vars (E_IsIRI (E_Var "a"))) ["a"] &&
     set_eq (expr_vars (E_IsBlank (E_Var "b"))) ["b"] &&
     set_eq (expr_vars (E_IsLiteral (E_Var "c"))) ["c"] &&
     set_eq (expr_vars (E_IsNumeric (E_Var "d"))) ["d"]);
  check ~name:"expr_vars: E_Str/E_Lang/E_Datatype/E_IRI_fn"
    (set_eq (expr_vars (E_Str (E_Var "a"))) ["a"] &&
     set_eq (expr_vars (E_Lang (E_Var "b"))) ["b"] &&
     set_eq (expr_vars (E_Datatype (E_Var "c"))) ["c"] &&
     set_eq (expr_vars (E_IRI_fn (E_Var "d"))) ["d"]);
  check ~name:"expr_vars: E_StrDt / E_StrLang"
    (set_eq (expr_vars (E_StrDt (E_Var "a", E_Var "b"))) ["a"; "b"] &&
     set_eq (expr_vars (E_StrLang (E_Var "c", E_Var "d"))) ["c"; "d"]);
  check ~name:"expr_vars: E_Bound"
    (set_eq (expr_vars (E_Bound "x")) ["x"]);
  check ~name:"expr_vars: E_If all three branches"
    (set_eq (expr_vars (E_If (E_Var "c", E_Var "t", E_Var "f"))) ["c"; "t"; "f"]);
  check ~name:"expr_vars: E_Coalesce list"
    (set_eq (expr_vars (E_Coalesce [E_Var "a"; E_Var "b"])) ["a"; "b"]);
  check ~name:"expr_vars: E_In / E_NotIn"
    (set_eq (expr_vars (E_In (E_Var "x", [E_Var "a"; E_Var "b"]))) ["x"; "a"; "b"] &&
     set_eq (expr_vars (E_NotIn (E_Var "x", [E_Var "a"]))) ["x"; "a"]);
  check ~name:"expr_vars: E_StrLen"
    (set_eq (expr_vars (E_StrLen (E_Var "a"))) ["a"]);
  check ~name:"expr_vars: E_Substr with and without the optional length"
    (set_eq (expr_vars (E_Substr (E_Var "a", E_Var "b", some (E_Var "c"))))
       ["a"; "b"; "c"] &&
     set_eq (expr_vars (E_Substr (E_Var "a", E_Var "b", none))) ["a"; "b"]);
  check ~name:"expr_vars: E_UCase / E_LCase"
    (set_eq (expr_vars (E_UCase (E_Var "a"))) ["a"] &&
     set_eq (expr_vars (E_LCase (E_Var "b"))) ["b"]);
  check ~name:"expr_vars: E_StrStarts/E_StrEnds/E_Contains/E_StrBefore/E_StrAfter"
    (set_eq (expr_vars (E_StrStarts (E_Var "a", E_Var "b"))) ["a"; "b"] &&
     set_eq (expr_vars (E_StrEnds (E_Var "a", E_Var "b"))) ["a"; "b"] &&
     set_eq (expr_vars (E_Contains (E_Var "a", E_Var "b"))) ["a"; "b"] &&
     set_eq (expr_vars (E_StrBefore (E_Var "a", E_Var "b"))) ["a"; "b"] &&
     set_eq (expr_vars (E_StrAfter (E_Var "a", E_Var "b"))) ["a"; "b"]);
  check ~name:"expr_vars: E_Concat list"
    (set_eq (expr_vars (E_Concat [E_Var "a"; E_Var "b"; E_Var "c"])) ["a"; "b"; "c"]);
  check ~name:"expr_vars: E_EncodeForUri"
    (set_eq (expr_vars (E_EncodeForUri (E_Var "a"))) ["a"]);
  check ~name:"expr_vars: E_Replace with and without flags"
    (set_eq (expr_vars (E_Replace (E_Var "a", E_Var "b", E_Var "c", some (E_Var "d"))))
       ["a"; "b"; "c"; "d"] &&
     set_eq (expr_vars (E_Replace (E_Var "a", E_Var "b", E_Var "c", none)))
       ["a"; "b"; "c"]);
  check ~name:"expr_vars: E_Regex with and without flags"
    (set_eq (expr_vars (E_Regex (E_Var "a", E_Var "b", some (E_Var "c"))))
       ["a"; "b"; "c"] &&
     set_eq (expr_vars (E_Regex (E_Var "a", E_Var "b", none))) ["a"; "b"]);
  check ~name:"expr_vars: numeric functions (Abs/Round/Ceil/Floor)"
    (set_eq (expr_vars (E_Abs (E_Var "a"))) ["a"] &&
     set_eq (expr_vars (E_Round (E_Var "b"))) ["b"] &&
     set_eq (expr_vars (E_Ceil (E_Var "c"))) ["c"] &&
     set_eq (expr_vars (E_Floor (E_Var "d"))) ["d"]);
  check ~name:"expr_vars: hash functions (MD5/SHA1/SHA256/SHA384/SHA512)"
    (set_eq (expr_vars (E_MD5 (E_Var "a"))) ["a"] &&
     set_eq (expr_vars (E_SHA1 (E_Var "b"))) ["b"] &&
     set_eq (expr_vars (E_SHA256 (E_Var "c"))) ["c"] &&
     set_eq (expr_vars (E_SHA384 (E_Var "d"))) ["d"] &&
     set_eq (expr_vars (E_SHA512 (E_Var "e"))) ["e"]);
  check ~name:"expr_vars: date/time accessors"
    (set_eq (expr_vars (E_Year (E_Var "a"))) ["a"] &&
     set_eq (expr_vars (E_Month (E_Var "b"))) ["b"] &&
     set_eq (expr_vars (E_Day (E_Var "c"))) ["c"] &&
     set_eq (expr_vars (E_Hours (E_Var "d"))) ["d"] &&
     set_eq (expr_vars (E_Minutes (E_Var "e"))) ["e"] &&
     set_eq (expr_vars (E_Seconds (E_Var "f"))) ["f"] &&
     set_eq (expr_vars (E_Timezone (E_Var "g"))) ["g"] &&
     set_eq (expr_vars (E_Tz (E_Var "h"))) ["h"]);
  check ~name:"expr_vars: E_SameTerm"
    (set_eq (expr_vars (E_SameTerm (E_Var "a", E_Var "b"))) ["a"; "b"]);
  check ~name:"expr_vars: E_Exists descends into its sub-pattern"
    (set_eq
       (expr_vars (E_Exists (bgp1 (tp (PS_Var "x") (iri_p "http://ex/p") (PT_Var "y")))))
       ["x"; "y"]);
  check ~name:"expr_vars: E_NotExists descends into its sub-pattern"
    (set_eq
       (expr_vars (E_NotExists (bgp1 (tp (PS_Var "x") (iri_p "http://ex/p") (PT_Var "z")))))
       ["x"; "z"]);
  check ~name:"expr_vars: E_Aggregate"
    (set_eq (expr_vars (E_Aggregate (Agg_Sum, false, E_Var "a"))) ["a"]);
  check ~name:"expr_vars: E_FunctionCall args"
    (set_eq (expr_vars (E_FunctionCall ("http://ex/fn", [E_Var "a"; E_Var "b"])))
       ["a"; "b"])

(* ------------------------------------------------------------------ *)
(* 2. query_live_vars                                                  *)
(* ------------------------------------------------------------------ *)

(* SELECT ?s WHERE { ?s ?p ?o } -- only ?s is projected/live; ?p/?o are
   dead unless shared elsewhere (they are not, in this single-BGP
   pattern with no repeats). *)
let () =
  let q =
    mk_query (QF_Select (Select_Vars [SI_Var "s"]))
      (bgp1 (tp (PS_Var "s") (PT_Var "p") (PT_Var "o")))
  in
  check ~name:"query_live_vars: plain SELECT ?s projects only ?s"
    (set_eq (query_live_vars q) ["s"])

(* SELECT * WHERE { ?s ?p ?o } -- everything live. *)
let () =
  let q =
    mk_query (QF_Select Select_All)
      (bgp1 (tp (PS_Var "s") (PT_Var "p") (PT_Var "o")))
  in
  check ~name:"query_live_vars: SELECT * means everything live"
    (set_eq (query_live_vars q) ["s"; "p"; "o"])

(* SELECT ?s WHERE { ?s ?p ?o FILTER(?o > 5) } -- ?o becomes live via
   the FILTER even though it is not projected. *)
let () =
  let q =
    mk_query (QF_Select (Select_Vars [SI_Var "s"]))
      (GP_Filter (E_Compare (CmpGt, E_Var "o", n 5),
                  bgp1 (tp (PS_Var "s") (PT_Var "p") (PT_Var "o"))))
  in
  check ~name:"query_live_vars: FILTER free vars are live"
    (subset ["s"; "o"] (query_live_vars q))

(* SELECT ?s WHERE { ?s ?p ?o } ORDER BY ?p -- ?p live via ORDER BY. *)
let () =
  let q =
    mk_query (QF_Select (Select_Vars [SI_Var "s"]))
      (bgp1 (tp (PS_Var "s") (PT_Var "p") (PT_Var "o")))
      ~modifier:{ default_modifier with sm_order_by = some [OC_Asc (E_Var "p")] }
  in
  check ~name:"query_live_vars: ORDER BY free vars are live"
    (subset ["s"; "p"] (query_live_vars q))

(* SELECT ?s WHERE { ?s ?p ?o } GROUP BY ?g HAVING(?g > 1) -- ?g live
   via HAVING. *)
let () =
  let q =
    mk_query (QF_Select (Select_Vars [SI_Var "s"]))
      (bgp1 (tp (PS_Var "s") (PT_Var "p") (PT_Var "o")))
      ~having:(some [E_Compare (CmpGt, E_Var "g", n 1)])
  in
  check ~name:"query_live_vars: HAVING free vars are live"
    (subset ["s"; "g"] (query_live_vars q))

(* SELECT ?s WHERE { ?s ?p ?o BIND(?o + 1 AS ?o2) } -- ?o live via the
   BIND expression even though ?o2 (the bound alias) is not projected. *)
let () =
  let q =
    mk_query (QF_Select (Select_Vars [SI_Var "s"]))
      (GP_Bind (E_Arith (Add, E_Var "o", n 1), "o2",
                bgp1 (tp (PS_Var "s") (PT_Var "p") (PT_Var "o"))))
  in
  check ~name:"query_live_vars: BIND free vars are live"
    (subset ["s"; "o"] (query_live_vars q))

(* ------------------------------------------------------------------ *)
(* 3. col_need_for_tp                                                  *)
(* ------------------------------------------------------------------ *)

(* Single BGP `?s :p ?o`, projecting only ?s. ?p is a constant (never
   needs decode regardless of liveness); ?o is unbound and dead (not
   projected, no filter, occurs once) -- should NOT need decode. *)
let () =
  let t = tp (PS_Var "s") (iri_p "http://ex/p") (PT_Var "o") in
  let q = mk_query (QF_Select (Select_Vars [SI_Var "s"])) (bgp1 t) in
  let occ = pattern_var_occurrences (bgp1 t) in
  let live = query_live_vars q in
  let need = col_need_for_tp occ live t in
  check ~name:"col_need_for_tp: bound predicate position never needs decode"
    (need.cn_p = false);
  check ~name:"col_need_for_tp: live projected subject needs decode"
    (need.cn_s = true);
  check ~name:"col_need_for_tp: dead unbound object does not need decode"
    (need.cn_o = false)

(* Cross-pattern join var: `?s :p1 ?o . ?o :p2 ?z`, projecting only ?z.
   ?o is not projected/filtered but occurs in BOTH triple patterns, so
   it must still be decoded to perform the join. *)
let () =
  let t1 = tp (PS_Var "s") (iri_p "http://ex/p1") (PT_Var "o") in
  let t2 = tp (PS_Var "o") (iri_p "http://ex/p2") (PT_Var "z") in
  let pat = GP_BGP [t1; t2] in
  let q = mk_query (QF_Select (Select_Vars [SI_Var "z"])) pat in
  let occ = pattern_var_occurrences pat in
  let live = query_live_vars q in
  let need1 = col_need_for_tp occ live t1 in
  check ~name:"col_need_for_tp: cross-pattern join var needs decode"
    (need1.cn_o = true);
  check ~name:"col_need_for_tp: non-shared non-live subject does not need decode"
    (need1.cn_s = false)

(* Within-BGP repeat: `?x :knows ?y . ?y :knows ?x`, projecting an
   UNRELATED variable so neither ?x nor ?y is live via projection --
   isolates the occurrence-sharing mechanism specifically (both
   variables repeat within the same BGP, so both must still be decoded
   to perform the self-join). *)
let () =
  let t1 = tp (PS_Var "x") (iri_p "http://ex/knows") (PT_Var "y") in
  let t2 = tp (PS_Var "y") (iri_p "http://ex/knows") (PT_Var "x") in
  let pat = GP_BGP [t1; t2] in
  let q = mk_query (QF_Select (Select_Vars [SI_Var "unrelated"])) pat in
  let occ = pattern_var_occurrences pat in
  let live = query_live_vars q in
  let need1 = col_need_for_tp occ live t1 in
  let need2 = col_need_for_tp occ live t2 in
  check ~name:"col_need_for_tp: within-BGP repeat (subject side of t1) needs decode"
    (need1.cn_s = true);
  check ~name:"col_need_for_tp: within-BGP repeat (object side of t1) needs decode"
    (need1.cn_o = true);
  check ~name:"col_need_for_tp: within-BGP repeat (subject side of t2) needs decode"
    (need2.cn_s = true);
  check ~name:"col_need_for_tp: within-BGP repeat (object side of t2) needs decode"
    (need2.cn_o = true)

(* ------------------------------------------------------------------ *)
(* Summary                                                             *)
(* ------------------------------------------------------------------ *)

let () =
  Printf.printf "\nselective_decode_vars_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
