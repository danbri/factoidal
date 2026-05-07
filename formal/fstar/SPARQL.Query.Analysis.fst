module SPARQL.Query.Analysis

// Cheap structural-analysis predicates over SPARQL 1.1 query ASTs.
// One question per function, all pure, all total. Companion to
// SPARQL.Update.Analysis.fst (which serves the analogous purpose for
// SPARQL UPDATE).
//
// Migrated from factoidal_explain.ml. The Pe5 explain dump uses
// `bgps_in_query` to walk a parsed query and report per-BGP rows;
// the semantic decision "what counts as a BGP under nested patterns"
// belongs in F\* per Iron Rule #1 even though the dump itself is
// observability glue.

open FStar.List.Tot
open SPARQL11.Algebra

// ---------------------------------------------------------------
// bgps_in_query
//
// Walk a query's group_graph_pattern, collecting every non-empty BGP
// in source order. Recurses through Join / LeftJoin / Filter / Union
// / Graph / Minus / Bind / Service / ServiceVar; bottoms out at
// SubSelect / Values / PropertyPath / Empty (which are not BGPs by
// the SPARQL 1.1 algebra's flattening rules — explain-time
// reporting just lists them as their own constructors).
//
// Returns the BGPs in *first-seen* order so the explain dump's
// per-BGP row order matches what a user reading the query
// top-to-bottom would expect.
// ---------------------------------------------------------------

let rec collect_bgps_aux
    (acc : list bgp) (p : group_graph_pattern)
  : Tot (list bgp) (decreases p) =
  match p with
  | GP_BGP tps -> if Cons? tps then tps :: acc else acc
  | GP_Join p1 p2 -> collect_bgps_aux (collect_bgps_aux acc p1) p2
  | GP_LeftJoin p1 p2 _ -> collect_bgps_aux (collect_bgps_aux acc p1) p2
  | GP_Union p1 p2 -> collect_bgps_aux (collect_bgps_aux acc p1) p2
  | GP_Minus p1 p2 -> collect_bgps_aux (collect_bgps_aux acc p1) p2
  | GP_Filter _ p1 -> collect_bgps_aux acc p1
  | GP_Graph _ p1 -> collect_bgps_aux acc p1
  | GP_Bind _ _ p1 -> collect_bgps_aux acc p1
  | GP_Service _ p1 _ -> collect_bgps_aux acc p1
  | GP_ServiceVar _ p1 _ -> collect_bgps_aux acc p1
  | GP_SubSelect _ -> acc
  | GP_Values _ _ -> acc
  | GP_PropertyPath _ _ _ -> acc
  | GP_Empty -> acc

let bgps_in_query (q : query) : Tot (list bgp) =
  rev (collect_bgps_aux [] q.q_pattern)
