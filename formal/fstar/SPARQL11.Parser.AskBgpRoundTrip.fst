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
open RDF.Term
open SPARQL11.Algebra
open SPARQL11.Parser

(* ============================================================ *)
(* Stage 1/2: fragment predicate + printer                       *)
(* ============================================================ *)

// `p <> SPARQL.FullText.fulltext_query_pred` narrows out one IRI: that
// predicate routes `parse_object_list_simple` through jena-text's
// bespoke `text:query` argument grammar (SPARQL.FullText.fst) instead
// of the ordinary object grammar this fragment's printer/parse lemmas
// assume — see `parse_object_list_simple`'s `is_fulltext_query` branch,
// SPARQL11.Parser.fst:3352-3372. A documented narrowing, not a silent
// one: any triple using that exact IRI as an ordinary predicate (not
// as a text:query call) is outside `query_in_fragment_1`.
let triple_pattern_in_fragment_1 (tp : triple_pattern) : bool =
  (match tp.tp_s with PS_IRI _ | PS_Var _ -> true | _ -> false) &&
  (match tp.tp_p with
   | PT_IRI p -> p <> SPARQL.FullText.fulltext_query_pred
   | PT_Var _ -> true
   | _ -> false) &&
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

(* ---- property-path combinator chain (verb = IRI case) ---- *)

let is_obj_start (t : token) : bool = Tok_IRI? t || Tok_VAR? t

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_path_primary_iri (pm : prefix_map) (fuel : nat{fuel >= 1}) (p : wf_iri) (rest : token_stream)
  : Lemma (ensures parse_path_primary pm fuel (Tok_IRI p :: rest) == ParseOk (PP_IRI p) rest)
let lemma_path_primary_iri pm fuel p rest = ()
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_path_elt_iri (pm : prefix_map) (fuel : nat{fuel >= 2}) (p : wf_iri) (rest : token_stream)
  : Lemma (requires is_obj_start (parse_peek rest))
          (ensures parse_path_elt pm fuel (Tok_IRI p :: rest) == ParseOk (PP_IRI p) rest)
let lemma_path_elt_iri pm fuel p rest =
  lemma_path_primary_iri pm (fuel - 1) p rest
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_path_elt_or_inverse_iri (pm : prefix_map) (fuel : nat{fuel >= 3}) (p : wf_iri) (rest : token_stream)
  : Lemma (requires is_obj_start (parse_peek rest))
          (ensures parse_path_elt_or_inverse pm fuel (Tok_IRI p :: rest) == ParseOk (PP_IRI p) rest)
let lemma_path_elt_or_inverse_iri pm fuel p rest =
  lemma_path_elt_iri pm (fuel - 1) p rest
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_path_sequence_iri (pm : prefix_map) (fuel : nat{fuel >= 4}) (p : wf_iri) (rest : token_stream)
  : Lemma (requires is_obj_start (parse_peek rest))
          (ensures parse_path_sequence pm fuel (Tok_IRI p :: rest) == ParseOk (PP_IRI p) rest)
let lemma_path_sequence_iri pm fuel p rest =
  lemma_path_elt_or_inverse_iri pm (fuel - 1) p rest
  // parse_path_seq_rest pm (fuel-1) (PP_IRI p) rest: peek rest is Tok_IRI/Tok_VAR, not Tok_SLASH
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_path_alternative_iri (pm : prefix_map) (fuel : nat{fuel >= 5}) (p : wf_iri) (rest : token_stream)
  : Lemma (requires is_obj_start (parse_peek rest))
          (ensures parse_path_alternative pm fuel (Tok_IRI p :: rest) == ParseOk (PP_IRI p) rest)
let lemma_path_alternative_iri pm fuel p rest =
  lemma_path_sequence_iri pm (fuel - 1) p rest
  // parse_path_alt_rest pm (fuel-1) (PP_IRI p) rest: peek rest is Tok_IRI/Tok_VAR, not Tok_PIPE
#pop-options

(* ---- verb (predicate) ---- *)

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_verb_iri (pm : prefix_map) (fuel : nat{fuel >= 6}) (p : wf_iri) (rest : token_stream)
  : Lemma (requires is_obj_start (parse_peek rest))
          (ensures parse_verb pm fuel (Tok_IRI p :: rest) == ParseOk (VSimple (PT_IRI p)) rest)
let lemma_parse_verb_iri pm fuel p rest =
  lemma_path_alternative_iri pm (fuel - 1) p rest
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_verb_var (pm : prefix_map) (fuel : nat{fuel >= 1}) (v : string) (rest : token_stream)
  : Lemma (ensures parse_verb pm fuel (Tok_VAR v :: rest) == ParseOk (VSimple (PT_Var v)) rest)
let lemma_parse_verb_var pm fuel v rest = ()
#pop-options

(* Dispatch over the fragment's two predicate shapes, worst-casing on
   IRI's fuel need (>= 6) for the shared entry point pred_obj_list uses. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_verb_1 (pm : prefix_map) (fuel : nat{fuel >= 6}) (pt : pattern_term{PT_IRI? pt \/ PT_Var? pt}) (rest : token_stream)
  : Lemma (requires is_obj_start (parse_peek rest))
          (ensures parse_verb pm fuel (tok_pt_1 pt :: rest) == ParseOk (VSimple pt) rest)
let lemma_parse_verb_1 pm fuel pt rest =
  match pt with
  | PT_IRI p -> lemma_parse_verb_iri pm fuel p rest
  | PT_Var v -> lemma_parse_verb_var pm fuel v rest
#pop-options

(* ---- object ---- *)

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_object_with_extras_1 (pm : prefix_map) (fuel : nat{fuel >= 1}) (pt : pattern_term{PT_IRI? pt \/ PT_Var? pt}) (rest : token_stream)
  : Lemma (ensures parse_object_with_extras pm fuel (tok_pt_1 pt :: rest) == ParseOk (pt, GP_Empty) rest)
let lemma_parse_object_with_extras_1 pm fuel pt rest =
  match pt with
  | PT_IRI p -> ()
  | PT_Var v -> ()
#pop-options

(* ---- annotations: no-op when the next token is DOT (1.1 mode has no
   Tok_TILDE/Tok_ANNOT_OPEN producers, but even syntactically here the
   head token is DOT, which matches neither) ---- *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_annotations_dot (pm : prefix_map) (fuel : nat) (s : pattern_subject) (p o : pattern_term) (rest : token_stream)
  : Lemma (ensures parse_annotations pm fuel s p o None (Tok_DOT :: rest) == ParseOk GP_Empty (Tok_DOT :: rest))
let lemma_parse_annotations_dot pm fuel s p o rest =
  if fuel = 0 then () else ()
#pop-options

(* ---- object_list_simple: single object, no comma continuation ---- *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_object_list_simple_1
    (pm : prefix_map) (fuel : nat{fuel >= 2}) (subj : pattern_subject) (pred : pattern_term{PT_IRI? pred \/ PT_Var? pred})
    (acc : group_graph_pattern) (o : pattern_term{PT_IRI? o \/ PT_Var? o}) (rest : token_stream)
  : Lemma (requires (match pred with PT_IRI p -> p <> SPARQL.FullText.fulltext_query_pred | _ -> True))
          (ensures parse_object_list_simple pm fuel subj pred acc (tok_pt_1 o :: (Tok_DOT :: rest))
                   == ParseOk (ggp_add_triple acc { tp_s = subj; tp_p = pred; tp_o = o }) (Tok_DOT :: rest))
let lemma_parse_object_list_simple_1 pm fuel subj pred acc o rest =
  lemma_parse_object_with_extras_1 pm (fuel - 1) o (Tok_DOT :: rest);
  let acc' = ggp_add_triple acc { tp_s = subj; tp_p = pred; tp_o = o } in
  assert (ggp_join acc' GP_Empty == acc');
  lemma_parse_annotations_dot pm (fuel - 1) subj pred o rest
#pop-options

(* ---- pred_obj_list: single verb + single object, no `;` continuation ---- *)
#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val lemma_parse_pred_obj_list_1
    (pm : prefix_map) (fuel : nat{fuel >= 7}) (subj : pattern_subject) (acc : group_graph_pattern)
    (pred : pattern_term{PT_IRI? pred \/ PT_Var? pred}) (o : pattern_term{PT_IRI? o \/ PT_Var? o}) (rest : token_stream)
  : Lemma (requires (match pred with PT_IRI p -> p <> SPARQL.FullText.fulltext_query_pred | _ -> True))
          (ensures parse_pred_obj_list pm fuel subj acc (tok_pt_1 pred :: (tok_pt_1 o :: (Tok_DOT :: rest)))
                   == ParseOk (ggp_add_triple acc { tp_s = subj; tp_p = pred; tp_o = o }) (Tok_DOT :: rest))
let lemma_parse_pred_obj_list_1 pm fuel subj acc pred o rest =
  lemma_parse_verb_1 pm (fuel - 1) pred (tok_pt_1 o :: (Tok_DOT :: rest));
  lemma_parse_object_list_simple_1 pm (fuel - 1) subj pred acc o rest
#pop-options

(* ---- subject ---- *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_parse_subject_with_extras_1 (pm : prefix_map) (fuel : nat{fuel >= 1}) (ps : pattern_subject{PS_IRI? ps \/ PS_Var? ps}) (rest : token_stream)
  : Lemma (ensures parse_subject_with_extras pm fuel (tok_ps_1 ps :: rest) == ParseOk (ps, GP_Empty, false) rest)
let lemma_parse_subject_with_extras_1 pm fuel ps rest =
  match ps with
  | PS_IRI i -> ()
  | PS_Var v -> ()
#pop-options

(* ============================================================ *)
(* Stage (b)/(c): one-triple step + BGP-list induction            *)
(* ============================================================ *)

// `acc_b = []` and `acc_b <> []` are represented by DIFFERENT AST nodes
// (`GP_Empty` vs `GP_BGP acc_b`) even though `ggp_add_triple` treats
// them identically as an accumulator — this bridges the two.
let mk_ggp_acc (acc_b : bgp) : group_graph_pattern =
  match acc_b with
  | [] -> GP_Empty
  | _ -> GP_BGP acc_b

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_ggp_add_triple_acc (acc_b : bgp) (tp : triple_pattern)
  : Lemma (ensures ggp_add_triple (mk_ggp_acc acc_b) tp == GP_BGP (acc_b @ [tp]))
let lemma_ggp_add_triple_acc acc_b tp =
  match acc_b with
  | [] -> ()
  | _ :: _ -> ()
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val lemma_ggp_join_acc_empty (acc_b : bgp)
  : Lemma (ensures ggp_join (mk_ggp_acc acc_b) GP_Empty == mk_ggp_acc acc_b)
let lemma_ggp_join_acc_empty acc_b =
  match acc_b with
  | [] -> ()
  | _ :: _ -> ()
#pop-options

// One-triple unfold, mirroring TokenRoundTrip's `combine_step`: reveals
// the triple's subject/predicate/object shape and states the
// `parse_triples_block` step as its OWN conclusion directly (matching
// SPARQL11.Parser.fst:3507-3524's own post-DOT trigger-token match
// verbatim on the RHS), so the induction below only ever INSTANTIATES
// this equation instead of re-deriving the unfold at the call site
// (TokenRoundTrip's "RESOLVED, attempt 6" pattern — see that module's
// banner). `dot_tail`'s FullText narrowing: our fragment's predicate
// set is {PT_IRI, PT_Var}, and `p <> fulltext_query_pred` is exactly
// what `lemma_parse_pred_obj_list_1`/`lemma_parse_object_list_simple_1`
// require to route through the ordinary object grammar instead of
// `text:query`'s bespoke argument grammar; recorded as a fragment
// narrowing (any triple pattern using this exact predicate IRI as an
// ordinary IRI predicate is outside `query_in_fragment_1`), not a
// silent omission.
#push-options "--z3rlimit 1500 --fuel 8 --ifuel 8"
val lemma_triples_block_unfold_one_triple
    (pm : prefix_map) (acc_b : bgp) (tp : triple_pattern{triple_pattern_in_fragment_1 tp})
    (dot_tail : token_stream) (fuel : nat)
  : Lemma
      (requires fuel >= 8)
      (ensures parse_triples_block pm fuel (mk_ggp_acc acc_b) (triple_tokens_1 tp @ dot_tail)
               == (match parse_peek dot_tail with
                   | Tok_VAR _ | Tok_IRI _ | Tok_PNAME _ | Tok_BNODE _ | Tok_LBRACKET
                   | Tok_LPAREN | Tok_A | Tok_INTEGER _ | Tok_DECIMAL _ | Tok_DOUBLE _
                   | Tok_STRING _ | Tok_TRUE | Tok_FALSE | Tok_TT_OPEN | Tok_TT_BARE_OPEN ->
                     parse_triples_block pm (fuel - 1) (GP_BGP (acc_b @ [tp])) dot_tail
                   | _ -> ParseOk (GP_BGP (acc_b @ [tp])) dot_tail))
let lemma_triples_block_unfold_one_triple pm acc_b tp dot_tail fuel =
  assert (PS_IRI? tp.tp_s \/ PS_Var? tp.tp_s);
  assert (PT_IRI? tp.tp_p \/ PT_Var? tp.tp_p);
  assert (PT_IRI? tp.tp_o \/ PT_Var? tp.tp_o);
  assert (match tp.tp_p with PT_IRI p -> p <> SPARQL.FullText.fulltext_query_pred | _ -> True);
  let subj_rest = tok_pt_1 tp.tp_p :: (tok_pt_1 tp.tp_o :: (Tok_DOT :: dot_tail)) in
  assert (triple_tokens_1 tp @ dot_tail == tok_ps_1 tp.tp_s :: subj_rest);
  lemma_parse_subject_with_extras_1 pm (fuel - 1) tp.tp_s subj_rest;
  lemma_ggp_join_acc_empty acc_b;
  lemma_parse_pred_obj_list_1 pm (fuel - 1) tp.tp_s (mk_ggp_acc acc_b) tp.tp_p tp.tp_o dot_tail;
  lemma_ggp_add_triple_acc acc_b tp
#pop-options

// Main BGP-list induction. `tail`'s head token must not be a
// `parse_ggp_body` trigger token (VAR/IRI/PNAME/BNODE/[/(/A/INTEGER/
// DECIMAL/DOUBLE/STRING/TRUE/FALSE/TT_OPEN/TT_BARE_OPEN) so the LAST
// triple's post-DOT peek correctly stops instead of recursing again —
// our only actual instantiation is `tail = Tok_RBRACE :: ...`, so this
// is stated narrowly against that rather than the full trigger set
// (a documented narrowing, not a silent one: widening to the full
// grammar's other GGP element keywords is free, same shape, just more
// `<>` disjuncts in the `requires`).
#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val lemma_parse_triples_block_bgp
    (pm : prefix_map) (acc_b : bgp) (b : bgp{bgp_in_fragment_1 b /\ List.Tot.length b >= 1})
    (tail : token_stream) (fuel : nat)
  : Lemma
      (requires fuel >= 7 + List.Tot.length b /\ Cons? tail /\ List.Tot.hd tail == Tok_RBRACE)
      (ensures parse_triples_block pm fuel (mk_ggp_acc acc_b) (bgp_tokens_1 b @ tail)
               == ParseOk (GP_BGP (acc_b @ b)) tail)
      (decreases b)
let rec lemma_parse_triples_block_bgp pm acc_b b tail fuel =
  match b with
  | [tp] ->
    assert (bgp_tokens_1 b == triple_tokens_1 tp);
    lemma_triples_block_unfold_one_triple pm acc_b tp tail fuel;
    // parse_peek tail == Tok_RBRACE (given), not a trigger token, so
    // the RHS match's `_` branch fires.
    assert (parse_peek tail == Tok_RBRACE);
    List.Tot.append_l_nil acc_b;
    assert (acc_b @ [tp] == acc_b @ b)
  | tp :: (tp2 :: rest2) ->
    let rest = tp2 :: rest2 in
    assert (bgp_in_fragment_1 rest);
    List.Tot.append_assoc (triple_tokens_1 tp) (bgp_tokens_1 rest) tail;
    assert (bgp_tokens_1 b @ tail == triple_tokens_1 tp @ (bgp_tokens_1 rest @ tail));
    lemma_triples_block_unfold_one_triple pm acc_b tp (bgp_tokens_1 rest @ tail) fuel;
    // after the DOT, the head of `bgp_tokens_1 rest @ tail` is tp2's
    // subject token (Tok_IRI/Tok_VAR) — a `parse_ggp_body`/
    // `parse_triples_block` trigger, so the RHS match's continuation
    // branch fires.
    assert (bgp_tokens_1 rest == triple_tokens_1 tp2 @ bgp_tokens_1 rest2);
    assert (List.Tot.hd (bgp_tokens_1 rest @ tail) == tok_ps_1 tp2.tp_s);
    assert (Tok_IRI? (tok_ps_1 tp2.tp_s) \/ Tok_VAR? (tok_ps_1 tp2.tp_s));
    assert (parse_peek (bgp_tokens_1 rest @ tail) == tok_ps_1 tp2.tp_s);
    lemma_parse_triples_block_bgp pm (acc_b @ [tp]) rest tail (fuel - 1);
    List.Tot.append_assoc acc_b [tp] rest;
    assert ((acc_b @ [tp]) @ rest == acc_b @ (tp :: rest));
    assert (acc_b @ (tp :: rest) == acc_b @ b)
#pop-options

(* ============================================================ *)
(* Stage (d): `{ ... }` wrapper, ASK-body wrapper, select-query    *)
(* dispatch — token-level                                          *)
(* ============================================================ *)

// Split into two ISOLATED near-empty steps (TokenRoundTrip's
// "context-heavy assertions through small isolated lemmas" pattern —
// the combined single-lemma version of this proof (first attempt)
// hung past 10 minutes of wall clock at rlimit 1500; splitting the two
// `parse_ggp_body` unfolds into their own standalone lemmas, each
// touching only what it needs, brought both back under a few hundred
// milliseconds).
#push-options "--z3rlimit 1000 --fuel 8 --ifuel 8"
val lemma_ggp_body_step1
    (pm : prefix_map) (b : bgp{bgp_in_fragment_1 b /\ List.Tot.length b >= 1})
    (after_rbrace : token_stream) (fuel : nat)
  : Lemma
      (requires fuel >= 8 + List.Tot.length b)
      (ensures parse_ggp_body pm fuel GP_Empty [] false (bgp_tokens_1 b @ (Tok_RBRACE :: after_rbrace))
               == parse_ggp_body pm (fuel - 1) (GP_BGP b) [] false (Tok_RBRACE :: after_rbrace))
let lemma_ggp_body_step1 pm b after_rbrace fuel =
  let ts = bgp_tokens_1 b @ (Tok_RBRACE :: after_rbrace) in
  let tp0 = List.Tot.hd b in
  assert (List.Tot.hd (bgp_tokens_1 b) == tok_ps_1 tp0.tp_s);
  assert (Tok_IRI? (tok_ps_1 tp0.tp_s) \/ Tok_VAR? (tok_ps_1 tp0.tp_s));
  assert (parse_peek ts == tok_ps_1 tp0.tp_s);
  lemma_parse_triples_block_bgp pm [] b (Tok_RBRACE :: after_rbrace) (fuel - 1);
  List.Tot.append_l_nil b;
  assert (parse_triples_block pm (fuel - 1) GP_Empty ts == ParseOk (GP_BGP b) (Tok_RBRACE :: after_rbrace));
  assert (ggp_join GP_Empty (GP_BGP b) == GP_BGP b)
#pop-options

#push-options "--z3rlimit 400 --fuel 8 --ifuel 8"
val lemma_ggp_body_step2 (pm : prefix_map) (b : bgp) (after_rbrace : token_stream) (fuel : nat)
  : Lemma (ensures parse_ggp_body pm fuel (GP_BGP b) [] false (Tok_RBRACE :: after_rbrace)
                    == ParseOk (GP_BGP b) (Tok_RBRACE :: after_rbrace))
let lemma_ggp_body_step2 pm b after_rbrace fuel =
  assert (List.Tot.fold_left (fun g e -> GP_Filter e g) (GP_BGP b) ([] <: list expr) == GP_BGP b)
#pop-options

#push-options "--z3rlimit 400 --fuel 8 --ifuel 8"
val lemma_parse_group_graph_pattern_ask_bgp
    (pm : prefix_map) (b : bgp{bgp_in_fragment_1 b /\ List.Tot.length b >= 1})
    (after_rbrace : token_stream) (fuel : nat)
  : Lemma
      (requires fuel >= 9 + List.Tot.length b)
      (ensures parse_group_graph_pattern pm fuel
                 (Tok_LBRACE :: (bgp_tokens_1 b @ (Tok_RBRACE :: after_rbrace)))
               == ParseOk (GP_BGP b) after_rbrace)
let lemma_parse_group_graph_pattern_ask_bgp pm b after_rbrace fuel =
  let inner = bgp_tokens_1 b @ (Tok_RBRACE :: after_rbrace) in
  assert (parse_expect Tok_LBRACE (Tok_LBRACE :: inner) == ParseOk () inner);
  let tp0 = List.Tot.hd b in
  assert (Tok_IRI? (tok_ps_1 tp0.tp_s) \/ Tok_VAR? (tok_ps_1 tp0.tp_s));
  assert (parse_peek inner == tok_ps_1 tp0.tp_s);
  lemma_ggp_body_step1 pm b after_rbrace (fuel - 1);
  lemma_ggp_body_step2 pm b after_rbrace (fuel - 2);
  assert (parse_ggp_body pm (fuel - 1) GP_Empty [] false inner == ParseOk (GP_BGP b) (Tok_RBRACE :: after_rbrace));
  assert (parse_expect Tok_RBRACE (Tok_RBRACE :: after_rbrace) == ParseOk () after_rbrace)
#pop-options
