module SPARQL.Explain

// Types and rendering for the Pe5 `factoidal --explain` dump.
//
// First slice of the audit's #2 unwind item (the rest of the
// `factoidal_explain.ml` migration — the per-pattern estimator
// loop, `tp_explain`, `tpx_json` — depends on additional F\*
// algebra plumbing not yet built; see the 2026-05-06 status doc).
//
// What this module owns now:
//   - `bound_status` type: classifies a triple-pattern position
//     as a free variable, a dictionary hit, a dictionary miss,
//     or "concrete but not encodable" (e.g. a literal in
//     predicate position).
//   - `bs_string`: human-readable rendering used in the textual
//     `--explain` dump (lines like `wd:Q5 [hit]`).
//
// Migrated from factoidal_explain.ml. Keeping bound_status
// constructors verbatim so OCaml callers can re-export them
// without touching the existing builder code in
// `explain_triple_pattern_against_store`.

type bound_status =
  | BS_Var   : string -> bound_status
    // ?varname — unbound
  | BS_Hit   : string -> bound_status
    // concrete, present in dictionary
  | BS_Miss  : string -> bound_status
    // concrete, ABSENT from dictionary (key for diagnosis: the
    // result set is definitely empty for any join through this
    // pattern)
  | BS_Other : string -> bound_status
    // concrete but no dictionary for this column (e.g. literal
    // as predicate, blank node where a column expects an IRI)

let bs_string (b : bound_status) : Tot string =
  match b with
  | BS_Var v   -> "?" ^ v ^ " (free)"
  | BS_Hit s   -> s ^ " [hit]"
  | BS_Miss s  -> s ^ " [MISS — term not in dictionary; result definitely empty]"
  | BS_Other s -> s ^ " [non-encodable]"
