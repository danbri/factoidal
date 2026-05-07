module SPARQL.Explain

// Types and rendering for the Pe5 `factoidal --explain` dump.
//
// What this module owns now:
//   - `bound_status` type: classifies a triple-pattern position
//     as a free variable, a dictionary hit, a dictionary miss,
//     or "concrete but not encodable" (e.g. a literal in
//     predicate position).
//   - `bs_string`: human-readable rendering used in the textual
//     `--explain` dump (lines like `wd:Q5 [hit]`).
//   - `bs_json`: JSON renderer for `bound_status`.
//   - `tp_explain`: per-triple-pattern explain row record.
//   - `tpx_json`: JSON renderer for one explain row.
//
// Migrated from factoidal_explain.ml. The estimator loop that
// builds `tp_explain` rows from a store (i.e.
// `explain_triple_pattern_against_store`) remains in OCaml for
// the moment, blocked on time-budget infra in F\*. Lifting the
// record + JSON renderer first lets the OCaml side delegate
// without conflating two migrations.
//
// Per CLAUDE.md rule #11: OCaml glue may not carry rendering
// logic.

module JE = SPARQL.JSON.Escape
module RP = RDF.Pretty
module A = SPARQL11.Algebra

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

// ---------------------------------------------------------------
// bs_json — JSON renderer for bound_status. Migrated from
// factoidal_explain.ml. Per CLAUDE.md rule #11 the OCaml glue
// holds no rendering logic.
// ---------------------------------------------------------------

let bs_json (bs : bound_status) : Tot string =
  match bs with
  | BS_Var v   -> "{\"kind\":\"var\",\"name\":\""   ^ JE.json_escape v ^ "\"}"
  | BS_Hit s   -> "{\"kind\":\"hit\",\"term\":\""   ^ JE.json_escape s ^ "\"}"
  | BS_Miss s  -> "{\"kind\":\"miss\",\"term\":\""  ^ JE.json_escape s ^ "\"}"
  | BS_Other s -> "{\"kind\":\"other\",\"term\":\"" ^ JE.json_escape s ^ "\"}"

// ---------------------------------------------------------------
// tp_explain — per-triple-pattern explain row. Data-only; the
// estimator loop that builds these from a store is still in OCaml
// (factoidal_explain.ml :: explain_triple_pattern_against_store),
// blocked on time_budget infra. Lifting the record + JSON
// renderer first lets the OCaml side delegate without conflating
// two migrations.
// ---------------------------------------------------------------

noeq type tp_explain = {
  tpx_label        : string;
  tpx_tp           : A.triple_pattern;
  tpx_s_status     : bound_status;
  tpx_p_status     : bound_status;
  tpx_o_status     : bound_status;
  tpx_bound_built  : bool;
  tpx_pred_present : option bool;
  tpx_estimate     : int;
}

// Helper: render `option bool` as the JSON literals null / true / false.
let opt_bool_json (ob : option bool) : Tot string =
  match ob with
  | None -> "null"
  | Some true -> "true"
  | Some false -> "false"

// ---------------------------------------------------------------
// tpx_json — JSON renderer for one explain row.
// ---------------------------------------------------------------

let tpx_json (tpx : tp_explain) : Tot string =
  "{\"label\":\"" ^ JE.json_escape tpx.tpx_label
  ^ "\",\"pattern\":\""
  ^ JE.json_escape (RP.triple_pattern_short_explain tpx.tpx_tp)
  ^ "\",\"s\":" ^ bs_json tpx.tpx_s_status
  ^ ",\"p\":" ^ bs_json tpx.tpx_p_status
  ^ ",\"o\":" ^ bs_json tpx.tpx_o_status
  ^ ",\"bound_built\":" ^ (if tpx.tpx_bound_built then "true" else "false")
  ^ ",\"predicate_present\":" ^ opt_bool_json tpx.tpx_pred_present
  ^ ",\"estimate\":" ^ string_of_int tpx.tpx_estimate
  ^ "}"
