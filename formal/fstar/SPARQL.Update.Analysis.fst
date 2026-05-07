module SPARQL.Update.Analysis

// Cheap structural-analysis predicates over SPARQL 1.1 UPDATE ASTs.
// One question per predicate, all pure, all total.
//
// Migrated from factoidal_http.ml. The HTTP layer uses these to make
// dispatch decisions (whether to reject the request, whether to set
// up a sandbox, etc.). The semantic decision "what does this update
// contain?" lives here in F\* per Iron Rule #1; the HTTP wiring
// (status codes, error messages) stays in the OCaml caller.

open FStar.List.Tot
open SPARQL11.Algebra

// ---------------------------------------------------------------
// update_has_load: does this update include any U_Load operation?
//
// LOAD requires fetching an external IRI over HTTP — outside the F\*
// runtime's purview. The HTTP layer therefore rejects updates that
// contain LOAD with 501 Not Implemented (rather than running them
// silently and producing wrong results). This predicate is the
// "is there a LOAD anywhere in this update?" check it consults.
// ---------------------------------------------------------------

let is_load_op (op : update_op) : Tot bool =
  match op with
  | U_Load _ _ _ -> true
  | _            -> false

let update_has_load (u : sparql_update) : Tot bool =
  existsb is_load_op u.u_ops
