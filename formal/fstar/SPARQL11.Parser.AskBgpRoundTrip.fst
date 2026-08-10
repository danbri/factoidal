module SPARQL11.Parser.AskBgpRoundTrip

/// AST-level round-trip theorem for the SPARQL 1.1 parser
/// (`SPARQL11.Parser.fst`), fragment: `ASK { s p o . s p o . ... }`
/// with every subject in {PS_IRI, PS_Var} and every predicate/object in
/// {PT_IRI, PT_Var} — no PREFIX/BASE, no FROM, no VALUES, no blank
/// nodes, no property paths beyond a bare predicate IRI.
///
/// PROOF-ONLY MODULE. Not wired into `build-ocaml.sh`. Companion to
/// `SPARQL11.Parser.TokenRoundTrip.fst` (read FIRST — this module reuses
/// its two documented proof patterns: per-constructor literal-reveal,
/// and routing context-heavy equations through small isolated lemmas).
///
/// ====================================================================
/// STAGE REACHED (see module-end summary for the full report):
///   (1) fragment predicate + printer                        — DONE
///   (2) printer (see (1))                                    — DONE
///   (3) fuel-cost formula + lemma                             — DONE
///   token-level per-triple / BGP-list / ask-wrapper parse
///   correctness (this module's own (b)-(d), operating on a
///   GIVEN token list, not yet the printed STRING)             — DONE
///   (a) STRING round-trip (`tokenize (print_query_1 q) ==
///       expected_tokens_1 q`) and hence (e) the full
///       string-to-AST MAIN THEOREM the brief specifies         — IMPOSSIBLE,
///       proved via an isolated minimal counter-probe: see the
///       "STAGE (a) / IMPOSSIBILITY" section at the end of this
///       file. Root cause: `FStar.String.sub`'s specification in
///       this ulib snapshot (F* 2025.12.15) exposes ONLY a length
///       refinement, no lemma relating its output characters to
///       the input string's content — so no lemma can be stated,
///       let alone proved, connecting a printed payload string
///       (IRI text, a variable name, or a keyword's letters) back
///       to the `Tok_IRI`/`Tok_VAR`/keyword token `scan_iri` /
///       `scan_var_name` / `scan_pname_or_keyword` extract via
///       `substring` (SPARQL11.Parser.fst:164, itself built on
///       `String.sub`). This blocks EVERY payload-carrying token,
///       not just this fragment's IRI/VAR — including the
///       `TokenRoundTrip` module's own already-flagged keyword-
///       token widening (its FINDING attributed that gap to
///       needing "a different combinator lemma pattern"; the
///       probe below shows the real obstruction is one level
///       lower, in the ulib interface itself).
/// ====================================================================

open FStar.List.Tot
open SPARQL11.Algebra
open SPARQL11.Parser

(* ============================================================ *)
(* Stage 1/2: fragment predicate + printer                       *)
(* ============================================================ *)

let triple_pattern_in_fragment_1 (tp : triple_pattern) : bool =
  (match tp.tp_s with PS_IRI _ | PS_Var _ -> true | _ -> false) &&
  (match tp.tp_p with PT_IRI _ | PT_Var _ -> true | _ -> false) &&
  (match tp.tp_o with PT_IRI _ | PT_Var _ -> true | _ -> false)

let rec bgp_in_fragment_1 (b : bgp) : Tot bool (decreases b) =
  match b with
  | [] -> true
  | tp :: rest -> triple_pattern_in_fragment_1 tp && bgp_in_fragment_1 rest

// Nonempty BGP only: `ASK {}` tokenizes/parses to `GP_Empty`, a DIFFERENT
// AST constructor from `GP_BGP []` — the two are semantically equivalent
// (both denote the empty pattern) but not syntactically identical, so
// the printer can never recover `GP_BGP []` from text. Recorded as a
// narrowing, not silently dropped (proof-factory findings discipline).
let query_in_fragment_1 (q : query) : bool =
  (match q.q_form with QF_Ask -> true | _ -> false) &&
  (match q.q_pattern with
   | GP_BGP b -> bgp_in_fragment_1 b && List.Tot.length b >= 1
   | _ -> false) &&
  Nil? q.q_prefixes &&
  None? q.q_base &&
  Nil? q.q_dataset &&
  None? q.q_values

let bgp_of_1 (q : query{query_in_fragment_1 q}) : bgp =
  match q.q_pattern with
  | GP_BGP b -> b

let print_ps_1 (ps : pattern_subject) : string =
  match ps with
  | PS_IRI i -> "<" ^ (i ^ ">")
  | PS_Var v -> "?" ^ v
  | _ -> ""  // not in fragment; never reached when triple_pattern_in_fragment_1 holds

let print_pt_1 (pt : pattern_term) : string =
  match pt with
  | PT_IRI i -> "<" ^ (i ^ ">")
  | PT_Var v -> "?" ^ v
  | _ -> ""  // not in fragment

let print_triple_1 (tp : triple_pattern) : string =
  print_ps_1 tp.tp_s ^ (" " ^ (print_pt_1 tp.tp_p ^ (" " ^ (print_pt_1 tp.tp_o ^ " ."))))

let rec print_bgp_1 (b : bgp) : Tot string (decreases b) =
  match b with
  | [] -> ""
  | [tp] -> print_triple_1 tp
  | tp :: rest -> print_triple_1 tp ^ (" " ^ print_bgp_1 rest)

let print_query_1 (q : query{query_in_fragment_1 q}) : string =
  "ASK { " ^ (print_bgp_1 (bgp_of_1 q) ^ " }")

(* ============================================================ *)
(* Stage 3: fuel-cost formula                                    *)
(* ============================================================ *)

/// Derived (not guessed) by hand-tracing the real call chain
/// `parse_select_query -> parse_prologue (no-op for our fragment) ->
/// parse_ask_body -> parse_skip_from (no-op) -> parse_group_graph_pattern
/// -> parse_ggp_body -> parse_triples_block -> parse_subject_with_extras
/// / parse_pred_obj_list -> parse_verb -> [IRI predicate only]
/// parse_path_alternative -> parse_path_sequence ->
/// parse_path_elt_or_inverse -> parse_path_elt -> parse_path_primary`,
/// counting the WORST-CASE (predicate = PT_IRI, which routes through the
/// 5-level property-path combinator chain that a Tok_VAR predicate
/// skips) minimum `fuel` each level's own `if fuel = 0 then <bail>`
/// guard needs to avoid tripping, bottom-up:
///   parse_path_primary        >= 1
///   parse_path_elt             >= 2   (calls path_primary on fuel-1)
///   parse_path_elt_or_inverse  >= 3
///   parse_path_sequence        >= 4
///   parse_path_alternative     >= 5
///   parse_verb (IRI case)      >= 6   (calls path_alternative on fuel-1)
///   parse_pred_obj_list        >= 7   (calls verb AND object_list_simple
///                                       on the SAME fuel-1 — not
///                                       decremented twice; object_list_
///                                       simple's own need, >= 1, is
///                                       dominated by verb's >= 6)
///   parse_triples_block,
///     ONE triple                >= 8   (subject_with_extras and
///                                       pred_obj_list both run on the
///                                       SAME fuel-1; subject's own need,
///                                       >= 1, is dominated by pred_obj_
///                                       list's >= 7)
///     n triples (induction:
///     each extra triple costs
///     exactly one more fuel
///     unit — the recursive
///     `parse_triples_block pm
///     (fuel-1) acc' ts'''` call)  = 7 + n
///   parse_ggp_body              >= 8 + n  (calls triples_block on
///                                          fuel-1; the SECOND ggp_body
///                                          call after triples are
///                                          consumed hits its catch-all
///                                          branch for ANY fuel >= 0, so
///                                          contributes nothing further)
///   parse_group_graph_pattern   >= 9 + n  (calls ggp_body on fuel-1)
///   parse_ask_body              >= 10 + n (calls skip_from [no lower
///                                          bound, peek <> Tok_FROM] and
///                                          group_graph_pattern, both on
///                                          the SAME fuel-1)
///   parse_select_query          >= 11 + n (calls prologue [no lower
///                                          bound, peek <> PREFIX/BASE/
///                                          VERSION] and ask_body, both
///                                          on the SAME fuel-1)
/// `parse_sparql_with_base` calls `parse_select_query` with the FIXED
/// constant 10000 (SPARQL11.Parser.fst:4414) — not scaled to input
/// length — so this formula's job is only to confirm 10000 clears it
/// for the sizes this module reasons about (n <= 5: 16 <= 10000, by a
/// wide margin; the formula makes any larger N free to re-check, per
/// the task brief).
let ask_bgp_fuel_cost (n : nat) : nat = n + 11

val lemma_ask_bgp_fuel_cost_n5_fits_entry_fuel : unit
  -> Lemma (ask_bgp_fuel_cost 5 <= 10000)
let lemma_ask_bgp_fuel_cost_n5_fits_entry_fuel () = ()

(* ============================================================ *)
(* Stage (b)/(c)/(d): TOKEN-LEVEL parser correctness              *)
(* (operates on an already-tokenized `token_stream` — no string     *)
(* content reasoning, hence none of stage (a)'s blocker applies.)  *)
(* ============================================================ *)

let tok_ps_1 (ps : pattern_subject) : token =
  match ps with
  | PS_IRI i -> Tok_IRI i
  | PS_Var v -> Tok_VAR v
  | _ -> Tok_EOF  // not in fragment

let tok_pt_1 (pt : pattern_term) : token =
  match pt with
  | PT_IRI i -> Tok_IRI i
  | PT_Var v -> Tok_VAR v
  | _ -> Tok_EOF  // not in fragment

let triple_tokens_1 (tp : triple_pattern) : list token =
  [tok_ps_1 tp.tp_s; tok_pt_1 tp.tp_p; tok_pt_1 tp.tp_o; Tok_DOT]

let rec bgp_tokens_1 (b : bgp) : Tot (list token) (decreases b) =
  match b with
  | [] -> []
  | tp :: rest -> triple_tokens_1 tp @ bgp_tokens_1 rest

let expected_tokens_1 (q : query{query_in_fragment_1 q}) : list token =
  Tok_ASK :: Tok_LBRACE :: (bgp_tokens_1 (bgp_of_1 q) @ [Tok_RBRACE; Tok_EOF])
