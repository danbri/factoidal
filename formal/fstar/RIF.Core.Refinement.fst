module RIF.Core.Refinement

// ===================================================================
// G4 wave -- pulling RIF Core into the theorems zone.
//
// PROOF-ONLY module (no build-list wiring -- see the landing report).
// States and proves, for RIF.Core.Eval's forward-chaining fixpoint,
// the same two properties RDF.Entailment.RDFS.RhoDFClosure.fst
// establishes for the six-rule rho-df closure step:
//
//   1. EXTENSIVITY -- the step (and the fuel loop) never drops an
//      input fact.
//   2. LICENSING   -- every fact the step ADDS is either already
//      present, or is the head-instantiation of SOME rule in the
//      program applied to a binding that matches SOME snapshot
//      extending the step's input (the "two-graph" src/seed idiom
//      `RhoDFClosure.rdfs_rule_domain_reaches2` and
//      `OWL.RL.Refinement.prp_trp_licensed` already use, needed here
//      because `one_round`'s rules fire in sequence against the
//      SAME graph, each seeing the prior rules' new triples in the
//      SAME round -- RIF.Core.Eval's own "Note" comment ahead of
//      `one_round_aux`, section 4, flags this order-dependence
//      directly).
//
// `RIF.Core.Eval.fixpoint` is the object under study, mirroring
// `RDF.Entailment.RDFS.RhoDFClosure.rho_df_closure`; `one_round` is
// the per-round step, mirroring `rho_df_closure_step`; `fire_rule` is
// one PHASE of that step (one rule firing), mirroring each of the six
// `rdfs_rule_*` calls `rho_df_closure_step_pre_dedup` composes.
//
// STEP-FUNCTION ANATOMY (read from RIF.Core.Eval.fst; transcribed,
// not reimplemented):
//
//   fixpoint g p fuel                                  -- fuel loop
//     = if fuel = 0 then g
//       else let (g', changed) = one_round g p in
//            if not changed then g' else fixpoint g' p (fuel - 1)
//
//   one_round g p = one_round_aux p.rules g false        -- THE STEP
//     one_round_aux rules g changed                      -- per-rule fold
//       = match rules with
//         | [] -> (g, changed)
//         | r :: rest ->
//           let (g', c') = fire_rule g r in               -- ONE PHASE
//           one_round_aux rest g' (changed || c')
//
//   fire_rule g r                                        -- ONE PHASE
//     = let (atoms, extras) = Tx.split_body r.body in
//       match Tx.translate_atoms_bgp atoms with
//       | None -> (g, false)
//       | Some body_bgp ->
//         let bindings0 = eval_bgp body_bgp g in
//         let bindings1 = filter_bindings_by_extras extras bindings0 in
//         fire_head_per_bindings r.head bindings1 g false  -- inner fold
//
//   fire_head_per_bindings head bindings g changed        -- inner fold
//     = match bindings with
//       | [] -> (g, changed)
//       | mu :: rest ->
//         let (g', c') = add_triples_tracking g (instantiate_atom_all mu head) changed in
//         fire_head_per_bindings head rest g' c'
//
// So `one_round` is a TWO-LEVEL fold (outer over `p.rules`, inner --
// inside `fire_head_per_bindings` -- over the bindings SPARQL's
// `eval_bgp` returns for one rule), exactly the "outer decls-fold,
// inner matching-fold" shape RhoDFClosure's per-row REACHES lemmas
// already carry (section 5 there) -- except here the outer fold is
// the ONE that threads the growing accumulator (RhoDFClosure's rows
// each read a FIXED index built once per row; RIF's rules read the
// literal live graph via a fresh `eval_bgp` call per rule, so the
// order-dependence is real, not just a proof-side artifact).
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10, rule #3).
//   - No "(*" or "*)" inside block comments (rule #12); use //.
// ===================================================================

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra
open RIF.Core.Eval
module Syn = RIF.Core.Syntax
module Tx  = RIF.Core.Translation

// ===================================================================
// 1. EXTENSIVITY.
//
// `RIF.Core.Eval.lemma_fixpoint_extends` ALREADY proves
// `graph_subset g (fixpoint g p fuel)`, UNCONDITIONALLY -- no
// `no_dup_keys`/chain-canonical hypothesis, unlike
// `rho_df_closure_extensive`. FINDING E-1 (below) records why: RIF's
// per-triple insertion (`add_one_triple_tracking`) tests membership
// BEFORE appending, so there is no separate dedup-sort pass whose own
// extensivity needs a no-duplicate-keys side condition the way
// `rho_df_closure_step`'s trailing `graph_dedup_sort` does. This
// section restates that fact as `rif_fixpoint_extensive` (the name
// this module's other theorems reference) and adds the one missing
// rung of the ladder Eval.fst does not itself state: `graph_subset`
// for a SINGLE round (`rif_one_round_extensive`), needed as a step
// obligation by the licensing induction in section 3.
// ===================================================================

// -------------------------------------------------------------------
// THEOREM 1 (restated). Thin corollary -- no new proof content beyond
// what RIF.Core.Eval.lemma_fixpoint_extends already discharges.
// -------------------------------------------------------------------
val rif_fixpoint_extensive (g : rdf_graph) (p : Syn.rif_program) (fuel : nat)
  : Lemma (ensures graph_subset g (fixpoint g p fuel))

let rif_fixpoint_extensive g p fuel = lemma_fixpoint_extends g p fuel

// One-round extensivity, universally quantified -- Eval.fst only
// carries the per-triple form (`lemma_one_round_preserves`); this is
// that lemma's `graph_subset` wrapper, same shape as
// `lemma_fixpoint_extends` itself (section 6 there).
val rif_one_round_extensive (g : rdf_graph) (p : Syn.rif_program)
  : Lemma (ensures graph_subset g (fst (one_round g p)))

let rif_one_round_extensive g p =
  let aux (t : triple) : Lemma (mem_triple t g ==> mem_triple t (fst (one_round g p))) =
    let pf () : Lemma (requires mem_triple t g)
                      (ensures  mem_triple t (fst (one_round g p))) =
      lemma_one_round_preserves g p t
    in
    Classical.move_requires pf ()
  in
  Classical.forall_intro aux

// `fire_rule`'s own `graph_subset` wrapper -- the per-PHASE extensivity
// step obligation the licensing induction (section 3) needs to grow
// the "snapshot" it hands to later rules in the same round.
val rif_fire_rule_extensive (g : rdf_graph) (r : Syn.rif_rule)
  : Lemma (ensures graph_subset g (fst (fire_rule g r)))

let rif_fire_rule_extensive g r =
  let aux (t : triple) : Lemma (mem_triple t g ==> mem_triple t (fst (fire_rule g r))) =
    let pf () : Lemma (requires mem_triple t g)
                      (ensures  mem_triple t (fst (fire_rule g r))) =
      lemma_fire_rule_preserves g r t
    in
    Classical.move_requires pf ()
  in
  Classical.forall_intro aux

// Transitivity of `graph_subset` -- the glue the round-level licensing
// induction (section 3) uses to carry "the snapshot extends the
// round's ORIGINAL input" across each rule firing in the round.
let lemma_graph_subset_trans (g1 g2 g3 : rdf_graph)
  : Lemma (requires graph_subset g1 g2 /\ graph_subset g2 g3)
          (ensures  graph_subset g1 g3) = ()

// ===================================================================
// 2. LICENSING -- the per-fold collect/emit building blocks.
//
// `add_one_triple_tracking`/`add_triples_tracking` are the innermost
// fold (append-if-new); their licensing form is the direct analogue
// of `OWL.RL.Refinement.lemma_dedup_pairs_memP`'s collect-fold shape:
// everything in the result is either already in the accumulator, or
// is one of the freshly-offered candidates.
// ===================================================================

// `g @ [u]` reached: whatever's newly visible was either already in
// `g` or is `u` itself (read via `mem_triple t [u]`, sidestepping any
// `triple_eq` symmetry lemma -- `mem_triple t [u]` unfolds to
// `triple_eq u t` directly, the same order `mem_triple`'s own cons
// case uses).
let rec lemma_mem_triple_append_or (t u : triple) (g : rdf_graph)
  : Lemma (ensures mem_triple t (g @ [u]) ==> (mem_triple t g \/ mem_triple t [u]))
          (decreases g) =
  match g with
  | [] -> ()
  | hd :: tl -> lemma_mem_triple_append_or t u tl

let add_one_triple_tracking_licensed (g : rdf_graph) (u : triple) (changed : bool) (t : triple)
  : Lemma (ensures mem_triple t (fst (add_one_triple_tracking g u changed)) ==>
                    (mem_triple t g \/ mem_triple t [u])) =
  if mem_triple u g then () else lemma_mem_triple_append_or t u g

// Per-list-of-candidates form: everything visible after threading the
// whole `ts` list through was already in `g`, or is one of `ts`.
let rec add_triples_tracking_licensed (g : rdf_graph) (ts : list triple) (changed : bool) (t : triple)
  : Lemma (ensures mem_triple t (fst (add_triples_tracking g ts changed)) ==>
                    (mem_triple t g \/ mem_triple t ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | u :: rest ->
    let (g', c') = add_one_triple_tracking g u changed in
    add_one_triple_tracking_licensed g u changed t;
    add_triples_tracking_licensed g' rest c' t

// ===================================================================
// 3. LICENSING -- the declarative spec + per-phase/per-step theorems.
//
// `rif_bindings_derive` names "some binding in this list instantiates
// the head to t" -- the inner-fold declarative spec, mirroring
// `OWL.RL.Refinement.eq_sym_derives`'s shape (an existential over a
// witness structure, not over the fold's own accumulator).
//
// `rif_rule_derives` is the per-RULE declarative spec the brief asks
// for: transcribed from `fire_rule`'s SHAPE (translate the body,
// evaluate the BGP, filter by extras, instantiate the head) but
// naming those as SEMANTIC building blocks -- `eval_bgp`,
// `filter_bindings_by_extras`, `instantiate_atom_all` -- rather than
// re-deriving `fire_head_per_bindings`'s accumulator-threading fold.
// This is the same discipline `eq_sym_derives` uses `term_to_subject`/
// `subject_to_term` (semantic conversions) but never `sameas_pairs`'s
// own dedup fold.
//
// `rif_derives` is the TOP-level spec the wave brief names
// (`rif_derives (rules) (facts) (t)`): a rule `r` from the program
// applied to SOME snapshot `h` extending the input facts `g`. The
// `graph_subset g h` existential is the two-graph idiom -- required
// because, per the step-function anatomy comment above, `one_round`'s
// rules fire against the SAME live graph in sequence, so a rule late
// in the list may read triples an earlier rule in the SAME round just
// added.
// ===================================================================

let rif_bindings_derive (head : Syn.rif_atom) (bindings : solution_sequence) (t : triple) : prop =
  exists (mu : solution_mapping). memP mu bindings /\ mem_triple t (instantiate_atom_all mu head)

let rif_rule_derives (r : Syn.rif_rule) (h : rdf_graph) (t : triple) : prop =
  (let (atoms, extras) = Tx.split_body r.body in
   match Tx.translate_atoms_bgp atoms with
   | None -> False
   | Some body_bgp ->
     rif_bindings_derive r.head (filter_bindings_by_extras extras (eval_bgp body_bgp h)) t)

let rif_derives (rules : list Syn.rif_rule) (g : rdf_graph) (t : triple) : prop =
  exists (r : Syn.rif_rule) (h : rdf_graph).
    memP r rules /\ graph_subset g h /\ rif_rule_derives r h t

// -------------------------------------------------------------------
// 3a. Inner-fold licensing: `fire_head_per_bindings`.
// -------------------------------------------------------------------
let rec fire_head_per_bindings_licensed
  (head : Syn.rif_atom) (bindings : solution_sequence) (g : rdf_graph) (changed : bool) (t : triple)
  : Lemma (ensures mem_triple t (fst (fire_head_per_bindings head bindings g changed)) ==>
                    (mem_triple t g \/ rif_bindings_derive head bindings t))
          (decreases bindings) =
  match bindings with
  | [] -> ()
  | mu :: rest ->
    let us = instantiate_atom_all mu head in
    let (g', c') = add_triples_tracking g us changed in
    add_triples_tracking_licensed g us changed t;
    fire_head_per_bindings_licensed head rest g' c' t;
    introduce mem_triple t us ==> rif_bindings_derive head bindings t
    with _ . FStar.Classical.exists_intro
               (fun (m : solution_mapping) -> memP m bindings /\ mem_triple t (instantiate_atom_all m head))
               mu

// -------------------------------------------------------------------
// 3b. Per-PHASE (single rule) licensing -- direct substitution into
// `fire_head_per_bindings_licensed`, since `fire_rule` itself is not
// a fold (it calls translate/eval_bgp/filter once, then hands off).
// -------------------------------------------------------------------
val fire_rule_licensed (g : rdf_graph) (r : Syn.rif_rule) (t : triple)
  : Lemma (ensures mem_triple t (fst (fire_rule g r)) ==>
                    (mem_triple t g \/ rif_rule_derives r g t))

let fire_rule_licensed g r t =
  let (atoms, extras) = Tx.split_body r.body in
  match Tx.translate_atoms_bgp atoms with
  | None -> ()
  | Some body_bgp ->
    let bindings0 = eval_bgp body_bgp g in
    let bindings1 = filter_bindings_by_extras extras bindings0 in
    fire_head_per_bindings_licensed r.head bindings1 g false t

// -------------------------------------------------------------------
// 3c. STEP-level (one_round) licensing -- outer fold over `p.rules`,
// each phase read against the CURRENT accumulator `g_acc` (which the
// round has already grown past the round's own starting graph `g0`).
// `graph_subset g0 g_acc` is the invariant carried through the
// induction (extended at each phase via `rif_fire_rule_extensive` +
// `lemma_graph_subset_trans`), matching the "snapshot extends input"
// half of `rif_derives`'s existential.
// -------------------------------------------------------------------
let rec lemma_one_round_aux_licensed
  (rules : list Syn.rif_rule) (g0 : rdf_graph) (g_acc : rdf_graph) (changed : bool) (t : triple)
  : Lemma (requires graph_subset g0 g_acc)
          (ensures  mem_triple t (fst (one_round_aux rules g_acc changed)) ==>
                    (mem_triple t g_acc \/ rif_derives rules g0 t))
          (decreases rules) =
  match rules with
  | [] -> ()
  | r :: rest ->
    let (g', c') = fire_rule g_acc r in
    fire_rule_licensed g_acc r t;
    rif_fire_rule_extensive g_acc r;
    lemma_graph_subset_trans g0 g_acc g';
    // NOTE the `changed || c'` here MUST match `one_round_aux`'s own
    // threading exactly (`one_round_aux rest g' (changed || c')`) --
    // passing `c'` alone leaves `fst (one_round_aux rest g' c')` a
    // syntactically different term from what the goal unfolds to
    // (same graph, different changed-flag argument), which SMT will
    // not identify without an extra independence lemma. Matching the
    // real call site avoids needing one.
    lemma_one_round_aux_licensed rest g0 g' (changed || c') t;
    introduce rif_rule_derives r g_acc t ==> rif_derives rules g0 t
    with _ . FStar.Classical.exists_intro
               (fun (rr : Syn.rif_rule) -> exists (h : rdf_graph).
                  memP rr rules /\ graph_subset g0 h /\ rif_rule_derives rr h t)
               r

// -------------------------------------------------------------------
// THEOREM 2 (per-round). `one_round`'s new facts are each either
// already in the round's input, or licensed by SOME rule in the
// program applied to a snapshot extending that input.
// -------------------------------------------------------------------
val one_round_licensed (g : rdf_graph) (p : Syn.rif_program) (t : triple)
  : Lemma (ensures mem_triple t (fst (one_round g p)) ==>
                    (mem_triple t g \/ rif_derives p.rules g t))

let one_round_licensed g p t =
  let lemma_refl (h : rdf_graph) : Lemma (graph_subset h h) = () in
  lemma_refl g;
  lemma_one_round_aux_licensed p.rules g g false t

// ===================================================================
// 4. FUEL-LOOP LICENSED-CLOSURE COROLLARY.
//
// `fixpoint g p fuel`'s new facts are each either already in `g`, or
// licensed by SOME rule applied to SOME snapshot extending `g` --
// the snapshot now ranges over every graph the fuel recursion visits
// (`rho_df_closure_sound`'s own fuel-induction shape, section 3
// there), reusing `rif_fixpoint_extensive` at the recursive graph
// `g'` to keep the "snapshot extends the ORIGINAL g" invariant.
// ===================================================================
val fixpoint_licensed (g : rdf_graph) (p : Syn.rif_program) (fuel : nat) (t : triple)
  : Lemma (ensures mem_triple t (fixpoint g p fuel) ==>
                    (mem_triple t g \/ rif_derives p.rules g t))
          (decreases fuel)

let rec fixpoint_licensed g p fuel t =
  if fuel = 0 then ()
  else begin
    let (g', changed) = one_round g p in
    one_round_licensed g p t;
    if not changed then ()
    else begin
      fixpoint_licensed g' p (fuel - 1) t;
      // Bridge the recursive call's `rif_derives p.rules g' t` back to
      // `g`: every rule/snapshot witness at g' extends g' which
      // extends g (rif_fixpoint_extensive is not needed here -- the
      // ONE step from g to g' via `rif_one_round_extensive` is the
      // only hop the fuel-1 recursive corollary needs composed with).
      rif_one_round_extensive g p;
      introduce rif_derives p.rules g' t ==> rif_derives p.rules g t
      with _ . eliminate exists (r : Syn.rif_rule) (h : rdf_graph).
                 memP r p.rules /\ graph_subset g' h /\ rif_rule_derives r h t
               returns rif_derives p.rules g t
               with _ . begin
                 lemma_graph_subset_trans g g' h;
                 FStar.Classical.exists_intro
                   (fun (rr : Syn.rif_rule) -> exists (hh : rdf_graph).
                      memP rr p.rules /\ graph_subset g hh /\ rif_rule_derives rr hh t)
                   r
               end
    end
  end
