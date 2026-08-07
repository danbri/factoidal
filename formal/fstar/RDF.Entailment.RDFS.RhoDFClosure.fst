module RDF.Entailment.RDFS.RhoDFClosure

// ===================================================================
// G3 milestone M1b — the SIX-RULE rho-df closure operator.
//
// RDF.Entailment.RDFS.Completeness.fst proves the fragment iff
// (`rho_df_saturation_iff`) against an ABSTRACT saturation `c`: any
// graph that is extensive over `g`, rho-df-SOUND for `g`, and rho-df-
// CLOSED decides rho-df entailment of fragment graphs from `g` by
// simple entailment. Finding C-2 there is that the SHIPPING twelve-
// rule `rdfs_closure` cannot instantiate `c` in the SOUNDNESS
// direction, because six of its twelve rows (rdfs1, rdfs4a, rdfs4b,
// rdfs8, rdfs13, container membership) rest on interpretation
// conditions `rho_df_conditions` does not carry.
//
// This module supplies the missing operator: `rho_df_closure` runs
// EXACTLY the six rho-df rows --
//
//   rdfs7  rdfs_rule_subPropertyOf
//   rdfs2  rdfs_rule_domain
//   rdfs3  rdfs_rule_range
//   rdfs9  rdfs_rule_subClassOf
//   rdfs11 rdfs_rule_subClassOf_trans
//   rdfs5  rdfs_rule_subPropertyOf_trans
//
// -- reusing the SAME `rdfs_rule_*` functions RDFS.Closure.fsti's
// twelve-rule `rdfs_closure_step` composes, in the SAME relative
// order (the five rows finding C-2 flags -- container membership,
// rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13 -- are simply omitted from the
// chain; no rule body is reimplemented), plus the same fuel/length-
// test fixed-point loop `rdfs_closure` uses.
//
// FIVE THEOREMS, matching `rho_df_saturation_iff`'s four hypotheses
// plus the payoff instantiation:
//   1. rho_df_closure_extensive        -- is_subgraph g (rho_df_closure g fuel)
//   2. rho_df_closure_sound            -- rho_df_entails g (rho_df_closure g fuel)
//   3. rho_df_closure_closed           -- at a fuel witness where the
//                                         length test passes, the result
//                                         is rho_df_closed
//   4. rho_df_closure_frag_preserving  -- FALSE AS A FLAT IMPLICATION;
//                                         see FINDING F-1 below. A
//                                         repaired, still-useful form
//                                         is delivered instead.
//   5. rho_df_closure_decides          -- the payoff: apply
//                                         `rho_df_saturation_iff`
//
// HYPOTHESES CARRIED, not discharged (M2's job, same discipline as
// the Completeness module's own banner):
//   * `rho_df_chain_canonical` / `rho_df_chain_wf` -- `no_dup_keys`
//     (of the pre-dedup accumulator) and `ig_wf_sp` respectively, at
//     EVERY graph the fuel recursion visits. Exactly the shape
//     `RDF.Entailment.RDFS.ModelTheory`'s `closure_chain_wf` and
//     `RDF.Entailment.RDFS.FixedPoint`'s `closure_chain_canonical`
//     already carry for the twelve-rule chain; restated here for the
//     six-rule one because the visited graphs differ.
//   * `no_repeats_p g` / `no_repeats_p (rho_df_closure_step g)` at the
//     fuel witness `rho_df_closure_closed` names -- the same two
//     explicit hypotheses `RDF.Entailment.RDFS.FixedPoint.
//     lemma_len_eq_saturated` takes, taken here rather than proved,
//     per the brief.
//
// `rho_df_closure` (section 1) and the decidable fragment checker
// (section 10, added for the npm/js entry points) are the two
// EXTRACTABLE definitions this module ships; everything else here is
// verify-only (theorems 1-5 and their supporting lemmas).
// ===================================================================

open FStar.List.Tot
open FStar.List.Tot.Properties
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas
open RDF.Vocabulary.Axioms
open RDF.Entailment.Simple.Spec
open RDF.Entailment.Simple.ModelTheory
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec
open RDF.Entailment.RDFS.Refinement
open RDF.Entailment.RDFS.ModelTheory
open RDF.Entailment.RDFS.FixedPoint
open RDF.Entailment.RDFS.Completeness
open RDF.Indexed.Completeness

// ===================================================================
// 1. THE SIX-RULE STEP AND THE FUEL/LENGTH-TEST LOOP.
//
// Byte-identical row order to `RDFS.Closure.fsti`'s `rdfs_closure_step`
// (subPropertyOf, domain, range, subClassOf, subClassOf_trans,
// subPropertyOf_trans) with the container-membership row and the five
// RS-2 rows dropped. Every `rdfs_rule_*` call below is the SAME
// function `rdfs_closure_step` calls -- no reimplementation.
// ===================================================================

let rho_df_closure_step_pre_dedup (g : rdf_graph) : rdf_graph =
  let ig = build_indexed g in
  let g1 = rdfs_rule_subPropertyOf g ig in
  let g2 = rdfs_rule_domain g1 ig in
  let g3 = rdfs_rule_range g2 ig in
  let g4 = rdfs_rule_subClassOf g3 ig in
  let g5 = rdfs_rule_subClassOf_trans g4 ig in
  rdfs_rule_subPropertyOf_trans g5 ig

let rho_df_closure_step (g : rdf_graph) : rdf_graph =
  graph_dedup_sort (rho_df_closure_step_pre_dedup g)

let lemma_rho_df_step_is_dedup_of_pre_dedup (g : rdf_graph)
  : Lemma (rho_df_closure_step g == graph_dedup_sort (rho_df_closure_step_pre_dedup g)) = ()

#push-options "--z3rlimit 30"
let rec rho_df_closure (g : rdf_graph) (fuel : nat) : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> g
  | n ->
    let g' = rho_df_closure_step g in
    if graph_len g' = graph_len g
    then g  // fixed point reached -- no new triples added
    else rho_df_closure g' (n - 1)
#pop-options

let rec rho_df_closure_iter (g : rdf_graph) (n : nat) : Tot rdf_graph (decreases n) =
  if n = 0 then g else rho_df_closure_iter (rho_df_closure_step g) (n - 1)

// ===================================================================
// 2. THEOREM 1 -- EXTENSIVITY.
//
// `rho_df_chain_canonical` names the `no_dup_keys` hypothesis at
// EVERY graph the fuel recursion visits -- the same shape
// `RDF.Entailment.RDFS.FixedPoint.closure_chain_canonical` carries for
// the twelve-rule chain, restated over `rho_df_closure_iter`. Carried,
// not discharged (M2's job; see the module banner).
// ===================================================================

let rho_df_chain_canonical (g : rdf_graph) : prop =
  forall (n : nat). no_dup_keys (rho_df_closure_step_pre_dedup (rho_df_closure_iter g n))

let lemma_rho_df_closure_iter_shift (g : rdf_graph) (n : nat)
  : Lemma (rho_df_closure_iter (rho_df_closure_step g) n == rho_df_closure_iter g (n + 1)) = ()

let lemma_rho_df_chain_canonical_shift (g : rdf_graph)
  : Lemma (requires rho_df_chain_canonical g)
          (ensures  rho_df_chain_canonical (rho_df_closure_step g)) =
  FStar.Classical.forall_intro (lemma_rho_df_closure_iter_shift g)

// Six-row pre-dedup extensivity, unconditional -- direct reuse of the
// six per-row extensivity lemmas RDF.Entailment.RDFS.FixedPoint
// already proves (section 3 there), in the same relative order as
// `rho_df_closure_step_pre_dedup`.
#push-options "--z3rlimit 60"
let lemma_rho_df_pre_dedup_extensive (g : rdf_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rho_df_closure_step_pre_dedup g)) =
  let ig = build_indexed g in
  introduce memP x g ==> memP x (rho_df_closure_step_pre_dedup g)
  with _ . begin
    lemma_rdfs_rule_subPropertyOf_extensive g ig x;
    let g1 = rdfs_rule_subPropertyOf g ig in
    lemma_rdfs_rule_domain_extensive g1 ig x;
    let g2 = rdfs_rule_domain g1 ig in
    lemma_rdfs_rule_range_extensive g2 ig x;
    let g3 = rdfs_rule_range g2 ig in
    lemma_rdfs_rule_subClassOf_extensive g3 ig x;
    let g4 = rdfs_rule_subClassOf g3 ig in
    lemma_rdfs_rule_subClassOf_trans_extensive g4 ig x;
    let g5 = rdfs_rule_subClassOf_trans g4 ig in
    lemma_rdfs_rule_subPropertyOf_trans_extensive g5 ig x
  end
#pop-options

val lemma_rho_df_step_extensive (g : rdf_graph)
  : Lemma (requires no_dup_keys (rho_df_closure_step_pre_dedup g))
          (ensures forall (t : triple). memP t g ==> memP t (rho_df_closure_step g))

let lemma_rho_df_step_extensive g =
  introduce forall (t : triple). memP t g ==> memP t (rho_df_closure_step g)
  with introduce memP t g ==> memP t (rho_df_closure_step g)
  with _ . begin
    lemma_rho_df_pre_dedup_extensive g t;
    lemma_graph_dedup_sort_extensive (rho_df_closure_step_pre_dedup g) t;
    lemma_rho_df_step_is_dedup_of_pre_dedup g
  end

#push-options "--z3rlimit 120"
let rec lemma_rho_df_closure_extensive_aux (g : rdf_graph) (fuel : nat)
  : Lemma (requires rho_df_chain_canonical g)
          (ensures  is_subgraph g (rho_df_closure g fuel))
          (decreases fuel) =
  if fuel = 0 then ()
  else begin
    assert (rho_df_closure_iter g 0 == g);
    lemma_rho_df_step_extensive g;
    lemma_rho_df_chain_canonical_shift g;
    let g' = rho_df_closure_step g in
    if graph_len g' = graph_len g then ()
    else lemma_rho_df_closure_extensive_aux g' (fuel - 1)
  end
#pop-options

// -------------------------------------------------------------------
// THEOREM 1.
// -------------------------------------------------------------------
val rho_df_closure_extensive (g : rdf_graph) (fuel : nat)
  : Lemma (requires rho_df_chain_canonical g)
          (ensures  is_subgraph g (rho_df_closure g fuel))

let rho_df_closure_extensive g fuel = lemma_rho_df_closure_extensive_aux g fuel

// ===================================================================
// 3. THEOREM 2 -- SOUNDNESS.
//
// `rho_df_chain_wf` names the `ig_wf_sp` hypothesis at every graph the
// fuel recursion visits -- the same shape
// `RDF.Entailment.RDFS.ModelTheory.closure_chain_wf` carries for the
// twelve-rule chain (needed because rdfs9/rdfs11/rdfs5 are ig_sp-
// driven), restated over `rho_df_closure_iter`. `ig_wf_pred` needs no
// such hypothesis -- `lemma_build_indexed_wf_pred` gives it
// unconditionally for every graph, exactly as
// `rdfs_closure_step_sound` already relies on.
//
// AUDIT (the task's step 2 ask): each of the six `_true` lemmas this
// proof composes (`rdfs2_true` .. `rdfs11_true`, ModelTheory.fst
// section 3) requires EXACTLY ONE `cond_*` conjunct of
// `rho_df_conditions` -- `cond_domain`, `cond_range`,
// `cond_subPropertyOf`, `cond_subPropertyOf_trans`, `cond_subClassOf`,
// `cond_subClassOf_trans` respectively -- and no other condition. This
// is visible directly in each lemma's `requires` clause; no row's
// proof secretly reaches for a dropped condition (`cond_resource`,
// `cond_subClassOf_refl`, etc.). No finding here: the six rows'
// soundness proofs restate under `rho_df_conditions` by hypothesis-
// weakening replay exactly as the brief predicted, not new proof work.
// ===================================================================

let rho_df_chain_wf (g : rdf_graph) : prop =
  forall (n : nat). ig_wf_sp (build_indexed (rho_df_closure_iter g n))

let lemma_rho_df_chain_wf_shift (g : rdf_graph)
  : Lemma (requires rho_df_chain_wf g)
          (ensures  rho_df_chain_wf (rho_df_closure_step g)) =
  FStar.Classical.forall_intro (lemma_rho_df_closure_iter_shift g)

#push-options "--z3rlimit 120"
val lemma_rho_df_step_sound (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph)
  : Lemma (requires rho_df_conditions i /\ holds_all i a g /\
                    ig_wf_sp (build_indexed g))
          (ensures  holds_all i a (rho_df_closure_step g))

let lemma_rho_df_step_sound i a g =
  let ig = build_indexed g in
  lemma_build_indexed_wf_pred g;
  assert (ig.ig_triples == g);
  assert (ig_wf_pred ig);
  let g1 = rdfs_rule_subPropertyOf g ig in
  rdfs_rule_subPropertyOf_preserves i a g ig;
  let g2 = rdfs_rule_domain g1 ig in
  rdfs_rule_domain_preserves i a g1 ig;
  let g3 = rdfs_rule_range g2 ig in
  rdfs_rule_range_preserves i a g2 ig;
  let g4 = rdfs_rule_subClassOf g3 ig in
  rdfs_rule_subClassOf_preserves i a g3 ig;
  let g5 = rdfs_rule_subClassOf_trans g4 ig in
  rdfs_rule_subClassOf_trans_preserves i a g4 ig;
  let g6 = rdfs_rule_subPropertyOf_trans g5 ig in
  rdfs_rule_subPropertyOf_trans_preserves i a g5 ig;
  FStar.Classical.forall_intro (lemma_graph_dedup_sort_memP g6);
  assert (rho_df_closure_step g == graph_dedup_sort g6)
#pop-options

#push-options "--z3rlimit 240"
let rec lemma_rho_df_closure_sound_aux (i : interp) (a : bnode_assignment i.idom)
                                       (g : rdf_graph) (fuel : nat)
  : Lemma (requires rho_df_conditions i /\ holds_all i a g /\ rho_df_chain_wf g)
          (ensures  holds_all i a (rho_df_closure g fuel))
          (decreases fuel) =
  if fuel = 0 then ()
  else begin
    assert (fuel > 0);
    let g' = rho_df_closure_step g in
    assert (rho_df_closure_iter g 0 == g);
    lemma_rho_df_step_sound i a g;
    lemma_rho_df_chain_wf_shift g;
    if graph_len g' = graph_len g then ()
    else lemma_rho_df_closure_sound_aux i a g' (fuel - 1)
  end
#pop-options

// -------------------------------------------------------------------
// THEOREM 2. `rho_df_closure g fuel` is rho-df-entailed by `g`.
// -------------------------------------------------------------------
val rho_df_closure_sound (g : rdf_graph) (fuel : nat)
  : Lemma (requires rho_df_chain_wf g)
          (ensures  rho_df_entails g (rho_df_closure g fuel))

let rho_df_closure_sound g fuel =
  introduce forall (i : interp).
      rho_df_conditions i ==> satisfies i g ==> satisfies i (rho_df_closure g fuel)
  with introduce rho_df_conditions i ==>
                 (satisfies i g ==> satisfies i (rho_df_closure g fuel))
  with _ . introduce satisfies i g ==> satisfies i (rho_df_closure g fuel)
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (rho_df_closure g fuel)
    with _ . lemma_rho_df_closure_sound_aux i a g fuel
  end

// ===================================================================
// 4. GENERIC REACHES MACHINERY (for theorem 3).
//
// `rdf_term_eq` soundness is NOT general -- `literal_eq`'s XMLLiteral
// branch compares via `xml_canon_eq` (value equality, not structural
// equality: RDF.Term.fsti's own banner at `literal_eq`), so two
// DIFFERENT XMLLiteral lexical forms can compare equal. Scoped to
// `rho_df_object_ok`, which excludes literals entirely, the soundness
// direction is exactly the case split `OWL.Semantics.Soundness.
// lemma_rdf_term_eq_iri` already uses for the single-constructor case,
// generalised to both sides.
// ===================================================================

let lemma_rdf_term_eq_sound (x y : rdf_term)
  : Lemma (requires rho_df_object_ok x /\ rho_df_object_ok y /\ rdf_term_eq x y == true)
          (ensures  x == y) =
  match x with
  | T_IRI _   -> (match y with | T_IRI _ -> () | _ -> ())
  | T_BNode _ -> (match y with | T_BNode _ -> () | _ -> ())
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// `fold_left f acc l` reached through the element `x` of `l`: split
// `l` at `x` (`FStar.List.Tot.Properties.split_using`, ghost), then
// `fold_left_append` (stdlib) plus `fold_left`'s own cons-unfolding
// on the tail (`x :: rest`) reduce the whole fold to "apply `f` at
// `x`, then let the REST of the list only grow the result" --
// `fold_left_grows` (RDF.Entailment.RDFS.Refinement) supplies that
// half. Generic over `f`; reused by every one of the six per-row
// completeness lemmas below (both the outer decls-fold and, applied a
// second time, the inner matching-fold).
#push-options "--z3rlimit 60"
let lemma_fold_left_reaches_at (#b : Type) (f : rdf_graph -> b -> rdf_graph)
    (l : list b) (x : b) (acc : rdf_graph) (goal : triple)
  : Lemma
    (requires
      memP x l /\
      (forall (y : rdf_graph) (z : b) (t : triple). memP t y ==> memP t (f y z)) /\
      memP goal (f (fold_left f acc (fst (split_using l x))) x))
    (ensures memP goal (fold_left f acc l)) =
  let (l1, l2) = split_using l x in
  lemma_split_using l x;
  fold_left_append f l1 l2;
  match l2 with
  | hd2 :: tl2 ->
    assert (hd2 == x);
    assert (fold_left f (fold_left f acc l1) l2 ==
            fold_left f (f (fold_left f acc l1) hd2) tl2);
    fold_left_grows f tl2 (f (fold_left f acc l1) x)
  | [] -> ()
#pop-options

// `RDF.Entailment.RDFS.Refinement.fold_left_reaches`'s fourth
// hypothesis is universally quantified over EVERY `y : b`, not just
// members of `l` -- fine for a `concl` whose conclusion object is a
// constant captured from an outer scope (domain/range: always
// `decl.o`), but too strong for rdfs7, whose conclusion object is
// `y.o` itself and is fragment-ok only because `y` is drawn from a
// rho-df-fragment graph. This is the same lemma with the fourth
// hypothesis restricted to `safe y`, and `safe` required to hold
// across `l` instead of unconditionally -- provable by the identical
// induction, since `safe`'s scope only shrinks along the recursion
// (`memP y tl ==> memP y l`).
let rec fold_left_reaches_scoped (#b : Type) (f : rdf_graph -> b -> rdf_graph)
                          (concl : b -> option triple)
                          (keep : rdf_graph -> prop)
                          (safe : b -> prop)
                          (l : list b) (acc : rdf_graph)
  : Lemma (requires keep acc /\
                    (forall (x : rdf_graph) (y : b). keep x ==> keep (f x y)) /\
                    (forall (x : rdf_graph) (y : b) (t : triple).
                       memP t x ==> memP t (f x y)) /\
                    (forall (x : rdf_graph) (y : b) (t : triple).
                       (safe y /\ keep x /\ concl y == Some t) ==> memP t (f x y)) /\
                    (forall (y : b). memP y l ==> safe y))
          (ensures  forall (y : b) (t : triple).
                      (memP y l /\ concl y == Some t) ==> memP t (fold_left f acc l))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    fold_left_grows f tl (f acc hd);
    fold_left_reaches_scoped f concl keep safe tl (f acc hd)

// `emit_once_term` never drops anything (unconditional, both
// branches), and yields its own conclusion when the accumulator
// already covers the snapshot, PROVIDED the object stays inside the
// rho-df fragment (needed for `lemma_rdf_term_eq_sound` above) and the
// snapshot itself is a fragment graph (so a matched object read back
// off the index is fragment-ok too). Same case structure as
// `RDF.Entailment.RDFS.Refinement.lemma_emit_once`/`lemma_emit_once_all`,
// generalised from a fixed `T_IRI cls` conclusion to an arbitrary
// fragment-ok `obj : rdf_term`.
#push-options "--z3rlimit 60"
let lemma_emit_once_term_grows (ig : indexed_graph) (acc : rdf_graph)
    (sub : subject) (prd : wf_iri) (obj : rdf_term) (x : triple)
  : Lemma (memP x acc ==> memP x (emit_once_term ig acc sub prd obj)) =
  lemma_emit_once_term_extensive ig acc sub prd obj x

let lemma_emit_once_term_reaches (ig : indexed_graph) (acc : rdf_graph)
    (sub : subject) (prd : wf_iri) (obj : rdf_term)
  : Lemma (requires ig_wf_sp ig /\ snapshot_subset ig acc /\
                    rho_df_frag_graph ig.ig_triples /\ rho_df_object_ok obj)
          (ensures  memP ({ s = sub; p = prd; o = obj } <: triple)
                         (emit_once_term ig acc sub prd obj)) =
  if ig.ig_built.bn_sp &&
     List.Tot.existsb (fun (o : rdf_term) -> rdf_term_eq o obj)
                      (find_objects_indexed ig sub prd)
  then begin
    lemma_existsb_elim (fun (o : rdf_term) -> rdf_term_eq o obj)
                       (find_objects_indexed ig sub prd);
    eliminate exists (x : rdf_term).
        memP x (find_objects_indexed ig sub prd) /\ rdf_term_eq x obj
    returns memP ({ s = sub; p = prd; o = obj } <: triple)
                 (emit_once_term ig acc sub prd obj)
    with _ . begin
      lemma_find_objects_elim ig sub prd x;
      eliminate exists (u : triple).
          memP u ig.ig_triples /\ u.s == sub /\ u.p == prd /\ u.o == x
      returns memP ({ s = sub; p = prd; o = obj } <: triple)
                   (emit_once_term ig acc sub prd obj)
      with _ . begin
        assert (rho_df_frag_triple u);
        lemma_rdf_term_eq_sound x obj;
        assert (u == ({ s = sub; p = prd; o = obj } <: triple))
      end
    end
  end else ()
#pop-options

// Index completeness for `ig_sp`, the composite-key bucket
// `find_objects_indexed` reads. `RDF.Indexed.Completeness.
// lemma_build_indexed_complete_pred` is the same fact for `ig_pred`;
// this is the same argument re-instantiated at `bucket_key_sp`
// (`RDF.Indexed.fsti`), reusing the SAME generic
// `lemma_build_bucket_complete` that proof composes from -- an
// instantiation, not new index logic.
let lemma_find_objects_complete (g : rdf_graph) (u : triple)
  : Lemma (requires memP u g)
          (ensures (let ig = build_indexed g in
                    memP u.o (find_objects_indexed ig u.s u.p))) =
  let ig = build_indexed g in
  assert (ig.ig_sp == build_bucket bucket_key_sp g);
  lemma_build_bucket_complete bucket_key_sp g (sp_key u.s u.p) u;
  memP_map_intro (fun (tt : triple) -> tt.o) u (bucket_lookup ig.ig_sp (sp_key u.s u.p))

// ===================================================================
// 5. PER-ROW COMPLETENESS ("REACHES"): if the declarative premises are
// members of `g`, the conclusion IS a member of the shipping rule
// function's output on `g`. Mirror image of
// RDF.Entailment.RDFS.Refinement's `_licensed` lemmas (which go
// output -> premises); these go premises -> output. Same local
// `outer_step`/`inner_step` mirroring + `assert_norm` bridge each
// `_licensed` proof uses, per the closure-identity trap those proofs'
// own comments document (rdfs7's especially, section 4 there).
// ===================================================================

// -- rdfs2 (domain) --
//
// TWO-GRAPH form, matching `licensed_by2`/`_derives2`'s own reason for
// splitting source from seed (RDF.Entailment.RDFS.ModelTheory's
// banner): inside the six-rule pipeline, domain's premises are read
// from `src` (the graph theorem 3 states `rdfs2_derives` against) but
// domain FOLDS over `seed` -- the ACCUMULATOR the prior row (rdfs7)
// already extended. `is_subgraph src seed` is what a real pipeline
// step guarantees (extensivity of everything before it); the diagonal
// `src == seed` recovers the single-graph statement.
#push-options "--z3rlimit 150"
let rdfs_rule_domain_reaches2 (src seed : rdf_graph) (t : triple)
  : Lemma (requires rho_df_frag_graph src /\ ig_wf_sp (build_indexed src) /\
                    is_subgraph src seed /\ rdfs2_derives src t)
          (ensures  memP t (rdfs_rule_domain seed (build_indexed src))) =
  lemma_vocab_agree ();
  let ig = build_indexed src in
  eliminate exists (decl u : triple) (aa : wf_iri).
      memP decl src /\ decl.p == i_rdfs_domain /\ decl.s == S_IRI aa /\
      memP u src /\ u.p == aa /\
      t == ({ s = u.s; p = i_rdf_type; o = decl.o } <: triple)
  returns memP t (rdfs_rule_domain seed ig)
  with _ . begin
    assert (ig.ig_triples == src);
    assert (rho_df_frag_triple decl);
    assert (rho_df_object_ok decl.o);
    let decls = bucket_lookup ig.ig_pred rdfs_domain in
    let outer_step : rdf_graph -> triple -> rdf_graph =
      fun (accx : rdf_graph) (declx : triple) ->
        match declx.s with
        | S_IRI p ->
          let matching = bucket_lookup ig.ig_pred p in
          fold_left
            (fun (acc2 : rdf_graph) (tt : triple) ->
              emit_once_term ig acc2 tt.s rdf_type declx.o)
            accx matching
        | _ -> accx in
    assert_norm (rdfs_rule_domain seed ig == fold_left outer_step seed decls);
    lemma_build_indexed_complete_pred src;
    assert (memP decl decls);
    assert (memP u (bucket_lookup ig.ig_pred aa));
    let outer_grows (accx : rdf_graph) (declx : triple) (tx : triple)
      : Lemma (memP tx accx ==> memP tx (outer_step accx declx)) =
      match declx.s with
      | S_IRI p ->
        fold_left_grows
          (fun (acc2 : rdf_graph) (tt : triple) -> emit_once_term ig acc2 tt.s rdf_type declx.o)
          (bucket_lookup ig.ig_pred p) accx
      | _ -> () in
    FStar.Classical.forall_intro_3 outer_grows;
    let (l1, _) = split_using decls decl in
    let acc_before = fold_left outer_step seed l1 in
    fold_left_grows outer_step l1 seed;
    assert (forall (tt : triple). memP tt seed ==> memP tt acc_before);
    assert (forall (tt : triple). memP tt src ==> memP tt seed);
    assert (snapshot_subset ig acc_before);
    let matching = bucket_lookup ig.ig_pred aa in
    let inner_step : rdf_graph -> triple -> rdf_graph =
      fun (acc2 : rdf_graph) (tt : triple) -> emit_once_term ig acc2 tt.s rdf_type decl.o in
    let inner_grows (accx : rdf_graph) (tt : triple) (tx : triple)
      : Lemma (memP tx accx ==> memP tx (inner_step accx tt)) =
      lemma_emit_once_term_grows ig accx tt.s rdf_type decl.o tx in
    FStar.Classical.forall_intro_3 inner_grows;
    let concl_inner : triple -> option triple =
      fun (tt : triple) -> Some ({ s = tt.s; p = i_rdf_type; o = decl.o } <: triple) in
    let keep : rdf_graph -> prop = fun (x : rdf_graph) -> snapshot_subset ig x in
    let inner_reaches (accx : rdf_graph) (tt : triple)
      : Lemma (requires keep accx)
              (ensures  keep (inner_step accx tt)) =
      let r = inner_step accx tt in
      introduce forall (uu : triple). memP uu ig.ig_triples ==> memP uu r
      with introduce memP uu ig.ig_triples ==> memP uu r
      with _ . lemma_emit_once_term_grows ig accx tt.s rdf_type decl.o uu in
    FStar.Classical.forall_intro_2 (fun (accx : rdf_graph) (tt : triple) ->
      FStar.Classical.move_requires (inner_reaches accx) tt);
    let inner_produces (accx : rdf_graph) (tt : triple) (tx : triple)
      : Lemma (requires keep accx /\ concl_inner tt == Some tx)
              (ensures  memP tx (inner_step accx tt)) =
      lemma_emit_once_term_reaches ig accx tt.s rdf_type decl.o in
    FStar.Classical.forall_intro_3 (fun (accx : rdf_graph) (tt : triple) (tx : triple) ->
      FStar.Classical.move_requires (inner_produces accx tt) tx);
    fold_left_reaches inner_step concl_inner keep matching acc_before;
    assert (memP u matching /\ concl_inner u == Some t);
    assert (memP t (fold_left inner_step acc_before matching));
    // Work with `decl` DIRECTLY -- not a reconstructed `decl'`. The
    // orchestrator's diagnosis: a reconstructed record, even
    // propositionally equal to `decl`, gives `outer_step`'s internal
    // closure (which captures `declx.o`, instantiated at `decl'.o`) a
    // DIFFERENT SMT function token from the separately-declared
    // `inner_step` (which captures `decl.o`) -- the closure-identity
    // law biting one level down, on a closed-over term rather than an
    // anonymous lambda. `decl.s == S_IRI aa` (already in context) lets
    // SMT case-split `outer_step acc_before decl`'s own `match
    // declx.s` directly, and since `inner_step` is spelled VERBATIM as
    // the engine copy's inner lambda after substituting `decl` for
    // `declx` (both close over the SAME variable `decl`, not two
    // equal-valued ones), the two folds become the identical term.
    assert (outer_step acc_before decl ==
                 fold_left inner_step acc_before (bucket_lookup ig.ig_pred aa));
    assert (memP t (outer_step acc_before decl));
    lemma_fold_left_reaches_at outer_step decls decl seed t
  end
#pop-options

// Diagonal corollary (`src == seed`) -- used directly by finding F-1's
// witness (section 6), which is a one-rule application, not part of
// the composed pipeline.
let rdfs_rule_domain_reaches (g : rdf_graph) (t : triple)
  : Lemma (requires rho_df_frag_graph g /\ ig_wf_sp (build_indexed g) /\ rdfs2_derives g t)
          (ensures  memP t (rdfs_rule_domain g (build_indexed g))) =
  let lemma_refl (h : rdf_graph) : Lemma (is_subgraph h h) = () in
  lemma_refl g;
  rdfs_rule_domain_reaches2 g g t

// -- rdfs3 (range) --
// `subj_term` / `term_to_subject` are mutually inverse on the
// S_IRI/S_BNode domain (`RDF.Graph.fsti`'s definitions); this is the
// direction `RDF.Entailment.RDFS.Refinement.lemma_term_to_subject_
// subj_term` does not give (that one goes term_to_subject -> subj_term).
let lemma_subj_term_to_subject (zs : subject) (o : rdf_term)
  : Lemma (requires subj_term zs == o) (ensures term_to_subject o == Some zs) =
  match zs with
  | S_IRI _   -> ()
  | S_BNode _ -> ()

// TWO-GRAPH form -- same reason as domain above.
#push-options "--z3rlimit 150"
let rdfs_rule_range_reaches2 (src seed : rdf_graph) (t : triple)
  : Lemma (requires rho_df_frag_graph src /\ ig_wf_sp (build_indexed src) /\
                    is_subgraph src seed /\ rdfs3_derives src t)
          (ensures  memP t (rdfs_rule_range seed (build_indexed src))) =
  lemma_vocab_agree ();
  let ig = build_indexed src in
  eliminate exists (decl u : triple) (aa : wf_iri) (zs : subject).
      memP decl src /\ decl.p == i_rdfs_range /\ decl.s == S_IRI aa /\
      memP u src /\ u.p == aa /\ subj_term zs == u.o /\
      t == ({ s = zs; p = i_rdf_type; o = decl.o } <: triple)
  returns memP t (rdfs_rule_range seed ig)
  with _ . begin
    assert (ig.ig_triples == src);
    assert (rho_df_frag_triple decl);
    assert (rho_df_object_ok decl.o);
    lemma_subj_term_to_subject zs u.o;
    let decls = bucket_lookup ig.ig_pred rdfs_range in
    let outer_step : rdf_graph -> triple -> rdf_graph =
      fun (accx : rdf_graph) (declx : triple) ->
        match declx.s with
        | S_IRI p ->
          let matching = bucket_lookup ig.ig_pred p in
          fold_left
            (fun (acc2 : rdf_graph) (tt : triple) ->
              match term_to_subject tt.o with
              | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type declx.o
              | None -> acc2)
            accx matching
        | _ -> accx in
    assert_norm (rdfs_rule_range seed ig == fold_left outer_step seed decls);
    lemma_build_indexed_complete_pred src;
    assert (memP decl decls);
    assert (memP u (bucket_lookup ig.ig_pred aa));
    let outer_grows (accx : rdf_graph) (declx : triple) (tx : triple)
      : Lemma (memP tx accx ==> memP tx (outer_step accx declx)) =
      match declx.s with
      | S_IRI p ->
        fold_left_grows
          (fun (acc2 : rdf_graph) (tt : triple) ->
            match term_to_subject tt.o with
            | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type declx.o
            | None -> acc2)
          (bucket_lookup ig.ig_pred p) accx
      | _ -> () in
    FStar.Classical.forall_intro_3 outer_grows;
    let (l1, _) = split_using decls decl in
    let acc_before = fold_left outer_step seed l1 in
    fold_left_grows outer_step l1 seed;
    assert (forall (tt : triple). memP tt src ==> memP tt seed);
    assert (snapshot_subset ig acc_before);
    let matching = bucket_lookup ig.ig_pred aa in
    let inner_step : rdf_graph -> triple -> rdf_graph =
      fun (acc2 : rdf_graph) (tt : triple) ->
        match term_to_subject tt.o with
        | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type decl.o
        | None -> acc2 in
    let inner_grows (accx : rdf_graph) (tt : triple) (tx : triple)
      : Lemma (memP tx accx ==> memP tx (inner_step accx tt)) =
      match term_to_subject tt.o with
      | Some b_subj -> lemma_emit_once_term_grows ig accx b_subj rdf_type decl.o tx
      | None -> () in
    FStar.Classical.forall_intro_3 inner_grows;
    let concl_inner : triple -> option triple =
      fun (tt : triple) ->
        match term_to_subject tt.o with
        | Some b_subj -> Some ({ s = b_subj; p = i_rdf_type; o = decl.o } <: triple)
        | None -> None in
    let keep : rdf_graph -> prop = fun (x : rdf_graph) -> snapshot_subset ig x in
    let inner_reaches (accx : rdf_graph) (tt : triple)
      : Lemma (requires keep accx)
              (ensures  keep (inner_step accx tt)) =
      let r = inner_step accx tt in
      introduce forall (uu : triple). memP uu ig.ig_triples ==> memP uu r
      with introduce memP uu ig.ig_triples ==> memP uu r
      with _ . begin
        match term_to_subject tt.o with
        | Some b_subj -> lemma_emit_once_term_grows ig accx b_subj rdf_type decl.o uu
        | None -> ()
      end in
    FStar.Classical.forall_intro_2 (fun (accx : rdf_graph) (tt : triple) ->
      FStar.Classical.move_requires (inner_reaches accx) tt);
    let inner_produces (accx : rdf_graph) (tt : triple) (tx : triple)
      : Lemma (requires keep accx /\ concl_inner tt == Some tx)
              (ensures  memP tx (inner_step accx tt)) =
      match term_to_subject tt.o with
      | Some b_subj -> lemma_emit_once_term_reaches ig accx b_subj rdf_type decl.o
      | None -> () in
    FStar.Classical.forall_intro_3 (fun (accx : rdf_graph) (tt : triple) (tx : triple) ->
      FStar.Classical.move_requires (inner_produces accx tt) tx);
    fold_left_reaches inner_step concl_inner keep matching acc_before;
    assert (memP u matching /\ concl_inner u == Some t);
    assert (memP t (fold_left inner_step acc_before matching));
    // Work with `decl` DIRECTLY -- same closed-over-term
    // closure-identity repair as the domain rule's site above (see the
    // long comment there): `decl.s == S_IRI aa` is in context, so the
    // engine copy's own `match declx.s` case-splits on `decl` itself,
    // and `inner_step` closes over the SAME `decl` variable.
    assert (outer_step acc_before decl ==
                 fold_left inner_step acc_before (bucket_lookup ig.ig_pred aa));
    assert (memP t (outer_step acc_before decl));
    lemma_fold_left_reaches_at outer_step decls decl seed t
  end
#pop-options

let rdfs_rule_range_reaches (g : rdf_graph) (t : triple)
  : Lemma (requires rho_df_frag_graph g /\ ig_wf_sp (build_indexed g) /\ rdfs3_derives g t)
          (ensures  memP t (rdfs_rule_range g (build_indexed g))) =
  let lemma_refl (h : rdf_graph) : Lemma (is_subgraph h h) = () in
  lemma_refl g;
  rdfs_rule_range_reaches2 g g t

// -- rdfs7 (subPropertyOf) -- RESOLVED 2026-08-06 (was PARKED; five
// prior attempts recorded below for the record).
//
// ROOT CAUSE (confirmed by the fix): every earlier attempt re-spelled
// the inner emitter as an anonymous proof-local lambda closing over
// `q`, the OUTER match's pattern-bound variable (`match declx.s,
// declx.o with S_IRI p, T_IRI q -> ...`). The closure-identity law
// (`skills/proof-factory/SKILL.md`) says two syntactically identical
// anonymous lambdas are DISTINCT SMT function tokens -- no
// record-literal reconstruction, nested-match respelling, or explicit
// bridging assert closes that gap, at any budget (attempts 0-2 below,
// all against the PROOF side). The treatment that already worked for
// every OWL analogue (`OWL.Closure.fsti`'s `*_emit` family) but had
// never been tried here: lift the lambda in the ENGINE instead.
// `RDFS.Closure.fsti` now names `rdfs7_emit (ig : indexed_graph) (q :
// wf_iri) (acc2 : rdf_graph) (tt : triple) : rdf_graph = emit_once_term
// ig acc2 tt.s q tt.o`, and `rdfs_rule_subPropertyOf`'s inner fold
// calls `fold_left (rdfs7_emit ig q) acc matching` -- behavior-
// identical, byte-for-byte same emitted triple set. With the engine's
// step and this proof's `outer_step`/`inner_step` both referencing the
// literal top-level symbol `rdfs7_emit ig q`/`rdfs7_emit ig bb`
// (rather than two independently-elaborated closures), first-order
// congruence carries facts across and the reaches lemma below
// discharges in ONE attempt -- no reconstruction trick needed at all
// (contrast the licensing/extensivity proofs of this same row in
// `RDF.Entailment.RDFS.Refinement.fst` / `...FixedPoint.fst`, which
// kept their pre-existing record-literal bridge since it already
// worked and touching it was not required).
//
// Ripple: `RDFS.Closure.fsti`'s `rdfs_rule_subPropertyOf` itself,
// `RDF.Entailment.RDFS.Refinement.fst`'s `rdfs_rule_subPropertyOf_
// licensed`, and `RDF.Entailment.RDFS.FixedPoint.fst`'s `lemma_rdfs_
// rule_subPropertyOf_extensive` all had their local `outer_step`/
// `inner_step` re-spelled to call the same named `rdfs7_emit`
// (mechanical, both still verify). `rdfs7_reaches_fact` (the PARKED
// hypothesis this section used to define) is no longer needed by
// `lemma_rho_df_closed_row_subPropertyOf`, `rho_df_closure_closed`,
// `rho_df_closure_decides`, or the finding F-1 witness call site
// (section 6) -- each now calls `rdfs_rule_subPropertyOf_reaches`/
// `rdfs_rule_subPropertyOf_reaches2` directly and has the hypothesis
// dropped from its `requires` (statement strengthening).
//
// PRIOR ATTEMPT HISTORY (kept for the record; none of these touched
// the engine, which is why none of them worked):
//
//   ATTEMPT 0 (first pass). `outer_step`/`outer_grows` built with a
//   reconstructed `decl' : triple = { s = S_IRI aa; p = decl.p; o =
//   T_IRI b }` and `assert_norm`, mirroring the domain/range sites'
//   working pattern. Failed: Error 19 at the eliminate head
//   (719,2-798,5 in that revision), "Assertion failed", same anchor
//   across reruns ("no location shift").
//
//   ATTEMPT 1. Diagnosis (orchestrator): a reconstructed record, even
//   propositionally equal to `decl`, gives `outer_step`'s internal
//   closure (capturing `declx.o`, instantiated at `decl'.o`) a
//   DIFFERENT SMT function token from a separately-declared
//   `inner_step` (capturing `decl.o`) -- the closure-identity law
//   biting on a CLOSED-OVER TERM, one level below the anonymous-
//   lambda form `RDF.Entailment.RDFS.Refinement.rdfs_rule_
//   subPropertyOf_licensed`'s own comment already documents (section
//   4 there). Fix: one named `inner_of (q : wf_iri) : rdf_graph ->
//   triple -> rdf_graph` shared by `outer_step`, `outer_grows`, and
//   `inner_step` (`inner_step := inner_of b`), direct `decl` (no
//   reconstruction) at the final bridge. RESULT: the final bridge and
//   `fold_left_reaches_scoped` call now succeed, but `outer_grows`
//   itself still fails -- `query_stats` isolates it precisely:
//   "failed {reason-unknown=unknown because (incomplete quantifiers)}
//   ... rlimit 150 (used rlimit 131.949)" (NOT resource-starved -- z3
//   had budget left and still could not find the proof), "See also"
//   at `outer_grows`'s own `: Lemma (... memP tx (outer_step accx
//   declx))` signature line. Root cause per `query_stats`: `outer_
//   step`'s TUPLE match `match declx.s, declx.o with S_IRI p, T_IRI q
//   -> ...` does not refine through SMT's encoding as reliably as the
//   single-field matches domain/range/subClassOf-trans/subPropertyOf-
//   trans all use -- exactly the asymmetry `rdfs_rule_subPropertyOf_
//   licensed`'s own comment flags as this row's distinguishing trap.
//   (Still a proof-side lambda, `inner_of q` -- named LOCALLY, not in
//   the engine, which is why the closure-identity gap persisted.)
//
//   ATTEMPT 2 (this module's own repair pass, two sub-tries. Sub-try
//   A: respelled `outer_step`/`outer_grows` with NESTED matches
//   (`match declx.s with S_IRI p -> (match declx.o with T_IRI q ->
//   ...) | _ -> accx`), matching the single-field technique that
//   already works elsewhere. `query_stats` confirmed the "See also"
//   location MOVED (750 -> 761) -- real progress on `outer_grows` --
//   but broke the `assert_norm (rdfs_rule_subPropertyOf g ig ==
//   fold_left outer_step g decls)` bridge instead: `assert_norm` is
//   PURE normalisation and does not identify a nested match with the
//   shipping function's tuple-match spelling as the same core term,
//   even though semantically identical. Sub-try B (kept): reverted
//   `outer_step`/`outer_grows` to the tuple match (restoring the
//   `assert_norm` bridge), added an EXPLICIT `assert (outer_step accx
//   declx == fold_left (inner_of q) accx (bucket_lookup ig.ig_pred
//   p))` inside `outer_grows`'s own tuple-match branch before handing
//   the goal to `fold_left_grows`, so SMT gets a named, separately-
//   dischargeable equality instead of relying on the implicit
//   `Lemma`-postcondition search to find the same reduction. RESULT:
//   still fails. Three consecutive `query_stats` runs against this
//   exact lemma: "unknown because (incomplete quantifiers)" (rlimit
//   used 131.949/150), then "canceled" twice more at rlimit 150.000 (z3
//   RAN OUT of budget this time, at fuel 2/ifuel 1 then fuel 2/ifuel 2
//   on F*'s own automatic retry) -- the explicit assert changed the
//   query's shape enough to consume the FULL budget without a bump,
//   the opposite direction from resolving it. No budget increase
//   closes this from here; the remaining candidate (a local `fold_
//   left` extensionality lemma over pointwise-equal functions, never
//   attempted) is real further work, not a small nudge.
//
// Every attempt above respelled the lambda somewhere on the PROOF
// side. None tried the engine-side lambda-lift, which is what
// actually worked (see the resolution paragraph above).
let rdfs7_reaches_fact (g : rdf_graph) : prop =
  forall (t : triple). rdfs7_derives g t ==> memP t (rdfs_rule_subPropertyOf g (build_indexed g))
// ^ Superseded 2026-08-06 by the unconditional `rdfs_rule_
// subPropertyOf_reaches`/`_reaches2` lemmas below -- kept, unused, as
// the historical record of what was carried as a hypothesis and for
// exactly how long (park: this section's original landing; resolution:
// the RESOLVED banner above).

// `fold_left_reaches_scoped`'s `safe`-restricted fourth hypothesis
// (declared above, section "5" preamble) is what rdfs7 actually needs:
// its conclusion object is `tt.o` itself, the matching data triple's
// OWN object, not a constant captured from the declaration the way
// domain/range's `decl.o` is -- so `rho_df_object_ok tt.o` must be
// shown for every `tt` the inner fold visits, not proved once at a
// fixed term.
#push-options "--z3rlimit 200"
let rdfs_rule_subPropertyOf_reaches2 (src seed : rdf_graph) (t : triple)
  : Lemma (requires rho_df_frag_graph src /\ ig_wf_sp (build_indexed src) /\
                    is_subgraph src seed /\ rdfs7_derives src t)
          (ensures  memP t (rdfs_rule_subPropertyOf seed (build_indexed src))) =
  lemma_vocab_agree ();
  let ig = build_indexed src in
  eliminate exists (decl u : triple) (aa bb : wf_iri).
      memP decl src /\ decl.p == i_rdfs_subPropertyOf /\
      decl.s == S_IRI aa /\ decl.o == T_IRI bb /\
      memP u src /\ u.p == aa /\
      t == ({ s = u.s; p = bb; o = u.o } <: triple)
  returns memP t (rdfs_rule_subPropertyOf seed ig)
  with _ . begin
    assert (ig.ig_triples == src);
    assert (rho_df_frag_triple decl);
    let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
    let outer_step : rdf_graph -> triple -> rdf_graph =
      fun (accx : rdf_graph) (declx : triple) ->
        match declx.s, declx.o with
        | S_IRI p, T_IRI q ->
          let matching = bucket_lookup ig.ig_pred p in
          fold_left (rdfs7_emit ig q) accx matching
        | _, _ -> accx in
    assert_norm (rdfs_rule_subPropertyOf seed ig == fold_left outer_step seed decls);
    lemma_build_indexed_complete_pred src;
    assert (memP decl decls);
    assert (memP u (bucket_lookup ig.ig_pred aa));
    let outer_grows (accx : rdf_graph) (declx : triple) (tx : triple)
      : Lemma (memP tx accx ==> memP tx (outer_step accx declx)) =
      match declx.s, declx.o with
      | S_IRI p, T_IRI q ->
        fold_left_grows (rdfs7_emit ig q) (bucket_lookup ig.ig_pred p) accx
      | _, _ -> () in
    FStar.Classical.forall_intro_3 outer_grows;
    let (l1, _) = split_using decls decl in
    let acc_before = fold_left outer_step seed l1 in
    fold_left_grows outer_step l1 seed;
    assert (forall (tt : triple). memP tt seed ==> memP tt acc_before);
    assert (forall (tt : triple). memP tt src ==> memP tt seed);
    assert (snapshot_subset ig acc_before);
    let matching = bucket_lookup ig.ig_pred aa in
    let inner_step : rdf_graph -> triple -> rdf_graph = rdfs7_emit ig bb in
    let concl_inner : triple -> option triple =
      fun (tt : triple) -> Some ({ s = tt.s; p = bb; o = tt.o } <: triple) in
    let keep : rdf_graph -> prop = fun (x : rdf_graph) -> snapshot_subset ig x in
    let safe : triple -> prop = fun (tt : triple) -> rho_df_object_ok tt.o in
    lemma_build_indexed_wf_pred src;
    introduce forall (tt : triple). memP tt matching ==> safe tt
    with introduce memP tt matching ==> safe tt
    with _ . assert (rho_df_frag_triple tt);
    let inner_grows (accx : rdf_graph) (tt : triple) (tx : triple)
      : Lemma (memP tx accx ==> memP tx (inner_step accx tt)) =
      lemma_emit_once_term_grows ig accx tt.s bb tt.o tx in
    FStar.Classical.forall_intro_3 inner_grows;
    let inner_reaches (accx : rdf_graph) (tt : triple)
      : Lemma (requires keep accx)
              (ensures  keep (inner_step accx tt)) =
      let r = inner_step accx tt in
      introduce forall (uu : triple). memP uu ig.ig_triples ==> memP uu r
      with introduce memP uu ig.ig_triples ==> memP uu r
      with _ . lemma_emit_once_term_grows ig accx tt.s bb tt.o uu in
    FStar.Classical.forall_intro_2 (fun (accx : rdf_graph) (tt : triple) ->
      FStar.Classical.move_requires (inner_reaches accx) tt);
    let inner_produces (accx : rdf_graph) (tt : triple) (tx : triple)
      : Lemma (requires safe tt /\ keep accx /\ concl_inner tt == Some tx)
              (ensures  memP tx (inner_step accx tt)) =
      lemma_emit_once_term_reaches ig accx tt.s bb tt.o in
    FStar.Classical.forall_intro_3 (fun (accx : rdf_graph) (tt : triple) (tx : triple) ->
      FStar.Classical.move_requires (inner_produces accx tt) tx);
    fold_left_reaches_scoped inner_step concl_inner keep safe matching acc_before;
    assert (memP u matching /\ concl_inner u == Some t);
    assert (memP t (fold_left inner_step acc_before matching));
    // Direct `decl` -- same closed-over-term identity as domain/range
    // above, now for free: `outer_step`'s inner call and `inner_step`
    // are the SAME symbol (`rdfs7_emit ig bb`), so no record-literal
    // reconstruction is needed to bridge them.
    assert (outer_step acc_before decl ==
                 fold_left inner_step acc_before (bucket_lookup ig.ig_pred aa));
    assert (memP t (outer_step acc_before decl));
    lemma_fold_left_reaches_at outer_step decls decl seed t
  end
#pop-options

// Diagonal corollary (`src == seed`) -- used directly by the F-1
// witness call site (section 6) and by `lemma_rho_df_closed_row_
// subPropertyOf` (theorem 3), both of which previously carried
// `rdfs7_reaches_fact` as an explicit hypothesis instead.
let rdfs_rule_subPropertyOf_reaches (g : rdf_graph) (t : triple)
  : Lemma (requires rho_df_frag_graph g /\ ig_wf_sp (build_indexed g) /\ rdfs7_derives g t)
          (ensures  memP t (rdfs_rule_subPropertyOf g (build_indexed g))) =
  let lemma_refl (h : rdf_graph) : Lemma (is_subgraph h h) = () in
  lemma_refl g;
  rdfs_rule_subPropertyOf_reaches2 g g t

// -- rdfs11 (subClassOf-trans) and rdfs5 (subPropertyOf-trans) --
//
// Both rules fold over `g` ITSELF (the outer "decls" list IS `g`), and
// their inner premise is read via `find_objects_indexed`
// (`ig_sp`-driven), not a guarded `emit_once_term` -- `add_triple_
// unchecked` is UNCONDITIONAL, so the "already produced" case
// `lemma_emit_once_term_reaches` exists for never arises here; plain
// `fold_left_reaches` (unscoped) applies with `keep := fun _ -> True`.
//
// The `assert_norm` bridge needs the reconstructed triple's `o` field
// to be a LITERAL constructor application (`T_IRI _` / `T_BNode _`),
// not merely propositionally equal to one -- `assert_norm` is pure
// normalisation and cannot consult a hypothesis. Matching on `ys`
// itself (its OWN two constructors) gives that literal form in each
// branch via `subj_term`'s definitional unfolding, mirroring the
// record-literal trick `RDF.Entailment.RDFS.Refinement.
// rdfs_rule_subPropertyOf_licensed`'s own comment documents for rdfs7
// (section 4 there), generalised from matching a captured IRI pair to
// matching a captured `subject`.
// TWO-GRAPH form -- same reason as domain/range above, but here `g`
// served DOUBLE duty in the one-graph version: it was both the
// premise source AND the list the outer fold iterates over (`rdfs_
// rule_subClassOf_trans` folds over ITS OWN INPUT, not a derived
// bucket). `t1` (the outer loop variable) therefore needs `memP t1
// seed` -- via `is_subgraph src seed` -- not merely `memP t1 src`;
// `t2` (read through the `ig_sp` index, which stays built from `src`)
// keeps `memP t2 src`.
#push-options "--z3rlimit 200"
let rdfs_rule_subClassOf_trans_reaches2 (src seed : rdf_graph) (t : triple)
  : Lemma (requires ig_wf_sp (build_indexed src) /\ is_subgraph src seed /\
                    rdfs11_derives src t)
          (ensures  memP t (rdfs_rule_subClassOf_trans seed (build_indexed src))) =
  lemma_vocab_agree ();
  let ig = build_indexed src in
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 src /\ t1.p == i_rdfs_subClassOf /\
      memP t2 src /\ t2.p == i_rdfs_subClassOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subClassOf; o = t2.o } <: triple)
  returns memP t (rdfs_rule_subClassOf_trans seed ig)
  with _ . begin
    lemma_subj_term_to_subject ys t1.o;
    lemma_find_objects_complete src t2;
    assert (memP t1 seed);
    let outer_step : rdf_graph -> triple -> rdf_graph =
      fun (accx : rdf_graph) (tx : triple) ->
        if tx.p = rdfs_subClassOf then
          match term_to_subject tx.o with
          | Some b_subj ->
            let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
            fold_left
              (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
                add_triple_unchecked acc2
                  ({ s = tx.s; p = rdfs_subClassOf; o = c_term } <: triple))
              accx supers
          | None -> accx
        else accx in
    assert_norm (rdfs_rule_subClassOf_trans seed ig == fold_left outer_step seed seed);
    let outer_grows (accx : rdf_graph) (tx : triple) (vx : triple)
      : Lemma (memP vx accx ==> memP vx (outer_step accx tx)) =
      if tx.p = rdfs_subClassOf then
        match term_to_subject tx.o with
        | Some b_subj ->
          fold_left_grows
            (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
              add_triple_unchecked acc2
                ({ s = tx.s; p = rdfs_subClassOf; o = c_term } <: triple))
            (find_objects_indexed ig b_subj rdfs_subClassOf) accx
        | None -> ()
      else () in
    FStar.Classical.forall_intro_3 outer_grows;
    let (l1, _) = split_using seed t1 in
    let acc_before = fold_left outer_step seed l1 in
    let supers = find_objects_indexed ig ys rdfs_subClassOf in
    let inner_step : rdf_graph -> rdf_term -> rdf_graph =
      fun (acc2 : rdf_graph) (c_term : rdf_term) ->
        add_triple_unchecked acc2 ({ s = t1.s; p = rdfs_subClassOf; o = c_term } <: triple) in
    let concl_inner : rdf_term -> option triple =
      fun (c_term : rdf_term) -> Some ({ s = t1.s; p = rdfs_subClassOf; o = c_term } <: triple) in
    let keep : rdf_graph -> prop = fun (_ : rdf_graph) -> True in
    fold_left_reaches inner_step concl_inner keep supers acc_before;
    assert (memP t2.o supers /\ concl_inner t2.o == Some t);
    assert (memP t (fold_left inner_step acc_before supers));
    // Direct `t1` -- NOT a reconstructed `t1'`. Same fix as the
    // domain/range sites: a reconstructed record, even propositionally
    // (or even SYNTACTICALLY, field-for-field) equal to `t1`, gives
    // `outer_step`'s internal closure (which captures `tx.o`,
    // instantiated at the reconstructed copy) a DIFFERENT SMT function
    // token from the separately-declared `inner_step` (which captures
    // `t1.s` directly) -- the closure-identity law on a closed-over
    // term. `term_to_subject t1.o == Some ys` is already established
    // (`lemma_subj_term_to_subject` above), so SMT can case-split
    // `outer_step acc_before t1`'s own `match term_to_subject tx.o`
    // directly, no reconstruction needed.
    assert (outer_step acc_before t1 ==
                 fold_left inner_step acc_before (find_objects_indexed ig ys rdfs_subClassOf));
    assert (memP t (outer_step acc_before t1));
    lemma_fold_left_reaches_at outer_step seed t1 seed t
  end
#pop-options

let rdfs_rule_subClassOf_trans_reaches (g : rdf_graph) (t : triple)
  : Lemma (requires ig_wf_sp (build_indexed g) /\ rdfs11_derives g t)
          (ensures  memP t (rdfs_rule_subClassOf_trans g (build_indexed g))) =
  let lemma_refl (h : rdf_graph) : Lemma (is_subgraph h h) = () in
  lemma_refl g;
  rdfs_rule_subClassOf_trans_reaches2 g g t

#push-options "--z3rlimit 200"
let rdfs_rule_subPropertyOf_trans_reaches2 (src seed : rdf_graph) (t : triple)
  : Lemma (requires ig_wf_sp (build_indexed src) /\ is_subgraph src seed /\
                    rdfs5_derives src t)
          (ensures  memP t (rdfs_rule_subPropertyOf_trans seed (build_indexed src))) =
  lemma_vocab_agree ();
  let ig = build_indexed src in
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 src /\ t1.p == i_rdfs_subPropertyOf /\
      memP t2 src /\ t2.p == i_rdfs_subPropertyOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subPropertyOf; o = t2.o } <: triple)
  returns memP t (rdfs_rule_subPropertyOf_trans seed ig)
  with _ . begin
    lemma_subj_term_to_subject ys t1.o;
    lemma_find_objects_complete src t2;
    assert (memP t1 seed);
    let outer_step : rdf_graph -> triple -> rdf_graph =
      fun (accx : rdf_graph) (tx : triple) ->
        if tx.p = rdfs_subPropertyOf then
          match term_to_subject tx.o with
          | Some b_subj ->
            let supers = find_objects_indexed ig b_subj rdfs_subPropertyOf in
            fold_left
              (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
                add_triple_unchecked acc2
                  ({ s = tx.s; p = rdfs_subPropertyOf; o = r_term } <: triple))
              accx supers
          | None -> accx
        else accx in
    assert_norm (rdfs_rule_subPropertyOf_trans seed ig == fold_left outer_step seed seed);
    let outer_grows (accx : rdf_graph) (tx : triple) (vx : triple)
      : Lemma (memP vx accx ==> memP vx (outer_step accx tx)) =
      if tx.p = rdfs_subPropertyOf then
        match term_to_subject tx.o with
        | Some b_subj ->
          fold_left_grows
            (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
              add_triple_unchecked acc2
                ({ s = tx.s; p = rdfs_subPropertyOf; o = r_term } <: triple))
            (find_objects_indexed ig b_subj rdfs_subPropertyOf) accx
        | None -> ()
      else () in
    FStar.Classical.forall_intro_3 outer_grows;
    let (l1, _) = split_using seed t1 in
    let acc_before = fold_left outer_step seed l1 in
    let supers = find_objects_indexed ig ys rdfs_subPropertyOf in
    let inner_step : rdf_graph -> rdf_term -> rdf_graph =
      fun (acc2 : rdf_graph) (r_term : rdf_term) ->
        add_triple_unchecked acc2 ({ s = t1.s; p = rdfs_subPropertyOf; o = r_term } <: triple) in
    let concl_inner : rdf_term -> option triple =
      fun (r_term : rdf_term) -> Some ({ s = t1.s; p = rdfs_subPropertyOf; o = r_term } <: triple) in
    let keep : rdf_graph -> prop = fun (_ : rdf_graph) -> True in
    fold_left_reaches inner_step concl_inner keep supers acc_before;
    assert (memP t2.o supers /\ concl_inner t2.o == Some t);
    assert (memP t (fold_left inner_step acc_before supers));
    // Direct `t1` -- see subClassOf-trans's identical note above.
    assert (outer_step acc_before t1 ==
                 fold_left inner_step acc_before (find_objects_indexed ig ys rdfs_subPropertyOf));
    assert (memP t (outer_step acc_before t1));
    lemma_fold_left_reaches_at outer_step seed t1 seed t
  end
#pop-options

let rdfs_rule_subPropertyOf_trans_reaches (g : rdf_graph) (t : triple)
  : Lemma (requires ig_wf_sp (build_indexed g) /\ rdfs5_derives g t)
          (ensures  memP t (rdfs_rule_subPropertyOf_trans g (build_indexed g))) =
  let lemma_refl (h : rdf_graph) : Lemma (is_subgraph h h) = () in
  lemma_refl g;
  rdfs_rule_subPropertyOf_trans_reaches2 g g t

// -- rdfs9 (subClassOf) --
//
// FINDING F-2 (falls directly out of stating this honestly, not a
// separate machine-checked witness). `rdfs9_derives`'s declarative
// `xs : subject` is UNRESTRICTED (`S_IRI` or `S_BNode`); the shipping
// `rdfs_rule_subClassOf` only chases `t.o = T_IRI class_iri` before
// consulting the index --
//
//   match t.o with T_IRI class_iri -> ... | _ -> acc
//
// -- so an `rdf:type` triple whose OBJECT is a blank node (a legal,
// if unusual, "typed as a blank-node class" assertion -- OWL-style
// class punning without OWL) is never picked up: `xs = S_BNode _`
// witnesses `rdfs9_derives g t` but the engine's `| _ -> acc` branch
// discards the premise before any index lookup, so `t` is provably
// NOT in `rdfs_rule_subClassOf g ig` for such a witness. Unlike RS-3
// (rdfs3), where the declarative rule ALREADY carries the engine's
// own restriction (`RDF.Entailment.RDFS.Refinement`'s banner), rdfs9
// and its engine implementation are NOT in refinement here, and no
// restatement of the completeness lemma closes the gap -- only a
// change to `rdfs_rule_subClassOf` (to also chase `T_BNode`-typed
// classes via `term_to_subject`, the way rdfs11/rdfs5 already do)
// would. STOPPED at the boundary the shipping function actually
// draws: this lemma is honest about covering only the `S_IRI` case.
// TWO-GRAPH form -- same double-duty note as subClassOf-trans above:
// `typ` (the outer loop variable) needs `memP typ seed`; `sub` (read
// through the index, built from `src`) keeps `memP sub src`.
#push-options "--z3rlimit 200"
let rdfs_rule_subClassOf_reaches_iri2 (src seed : rdf_graph) (t : triple) (class_iri : wf_iri)
  : Lemma (requires rho_df_frag_graph src /\ ig_wf_sp (build_indexed src) /\
                    is_subgraph src seed /\
                    (exists (sub typ : triple).
                       memP sub src /\ sub.p == i_rdfs_subClassOf /\ sub.s == S_IRI class_iri /\
                       memP typ src /\ typ.p == i_rdf_type /\ typ.o == T_IRI class_iri /\
                       t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)))
          (ensures  memP t (rdfs_rule_subClassOf seed (build_indexed src))) =
  lemma_vocab_agree ();
  let ig = build_indexed src in
  eliminate exists (sub typ : triple).
      memP sub src /\ sub.p == i_rdfs_subClassOf /\ sub.s == S_IRI class_iri /\
      memP typ src /\ typ.p == i_rdf_type /\ typ.o == T_IRI class_iri /\
      t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)
  returns memP t (rdfs_rule_subClassOf seed ig)
  with _ . begin
    assert (ig.ig_triples == src);
    lemma_find_objects_complete src sub;
    assert (memP typ seed);
    let outer_step : rdf_graph -> triple -> rdf_graph =
      fun (accx : rdf_graph) (tx : triple) ->
        if tx.p = rdf_type then
          match tx.o with
          | T_IRI ci ->
            let super_classes = find_objects_indexed ig (S_IRI ci) rdfs_subClassOf in
            fold_left
              (fun (acc2 : rdf_graph) (b_term : rdf_term) ->
                emit_once_term ig acc2 tx.s rdf_type b_term)
              accx super_classes
          | _ -> accx
        else accx in
    assert_norm (rdfs_rule_subClassOf seed ig == fold_left outer_step seed seed);
    let outer_grows (accx : rdf_graph) (tx : triple) (vx : triple)
      : Lemma (memP vx accx ==> memP vx (outer_step accx tx)) =
      if tx.p = rdf_type then
        match tx.o with
        | T_IRI ci ->
          fold_left_grows
            (fun (acc2 : rdf_graph) (b_term : rdf_term) ->
              emit_once_term ig acc2 tx.s rdf_type b_term)
            (find_objects_indexed ig (S_IRI ci) rdfs_subClassOf) accx
        | _ -> ()
      else () in
    FStar.Classical.forall_intro_3 outer_grows;
    let (l1, _) = split_using seed typ in
    let acc_before = fold_left outer_step seed l1 in
    fold_left_grows outer_step l1 seed;
    assert (forall (tt : triple). memP tt src ==> memP tt seed);
    assert (snapshot_subset ig acc_before);
    let super_classes = find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf in
    let inner_step : rdf_graph -> rdf_term -> rdf_graph =
      fun (acc2 : rdf_graph) (b_term : rdf_term) -> emit_once_term ig acc2 typ.s rdf_type b_term in
    let concl_inner : rdf_term -> option triple =
      fun (b_term : rdf_term) -> Some ({ s = typ.s; p = i_rdf_type; o = b_term } <: triple) in
    let keep : rdf_graph -> prop = fun (x : rdf_graph) -> snapshot_subset ig x in
    let safe : rdf_term -> prop = fun (b_term : rdf_term) -> rho_df_object_ok b_term in
    introduce forall (b_term : rdf_term). memP b_term super_classes ==> safe b_term
    with introduce memP b_term super_classes ==> safe b_term
    with _ . begin
      lemma_find_objects_elim ig (S_IRI class_iri) rdfs_subClassOf b_term;
      eliminate exists (w : triple).
          memP w ig.ig_triples /\ w.s == S_IRI class_iri /\
          w.p == rdfs_subClassOf /\ w.o == b_term
      returns safe b_term
      with _ . assert (rho_df_frag_triple w)
    end;
    let inner_grows (accx : rdf_graph) (b_term : rdf_term) (vx : triple)
      : Lemma (memP vx accx ==> memP vx (inner_step accx b_term)) =
      lemma_emit_once_term_grows ig accx typ.s rdf_type b_term vx in
    FStar.Classical.forall_intro_3 inner_grows;
    let inner_reaches (accx : rdf_graph) (b_term : rdf_term)
      : Lemma (requires keep accx) (ensures keep (inner_step accx b_term)) =
      let r = inner_step accx b_term in
      introduce forall (uu : triple). memP uu ig.ig_triples ==> memP uu r
      with introduce memP uu ig.ig_triples ==> memP uu r
      with _ . lemma_emit_once_term_grows ig accx typ.s rdf_type b_term uu in
    FStar.Classical.forall_intro_2 (fun (accx : rdf_graph) (b_term : rdf_term) ->
      FStar.Classical.move_requires (inner_reaches accx) b_term);
    let inner_produces (accx : rdf_graph) (b_term : rdf_term) (vx : triple)
      : Lemma (requires safe b_term /\ keep accx /\ concl_inner b_term == Some vx)
              (ensures  memP vx (inner_step accx b_term)) =
      lemma_emit_once_term_reaches ig accx typ.s rdf_type b_term in
    FStar.Classical.forall_intro_3 (fun (accx : rdf_graph) (b_term : rdf_term) (vx : triple) ->
      FStar.Classical.move_requires (inner_produces accx b_term) vx);
    fold_left_reaches_scoped inner_step concl_inner keep safe super_classes acc_before;
    assert (memP sub.o super_classes /\ concl_inner sub.o == Some t);
    assert (memP t (fold_left inner_step acc_before super_classes));
    // Direct `typ` -- see subClassOf-trans's identical note. `typ.o ==
    // T_IRI class_iri` is already in context (from the destructured
    // existential), so SMT can case-split `outer_step`'s own `match
    // tx.o with T_IRI ci -> ...` directly on `typ`.
    assert (outer_step acc_before typ ==
                 fold_left inner_step acc_before (find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf));
    assert (memP t (outer_step acc_before typ));
    lemma_fold_left_reaches_at outer_step seed typ seed t
  end
#pop-options

let rdfs_rule_subClassOf_reaches_iri (g : rdf_graph) (t : triple) (class_iri : wf_iri)
  : Lemma (requires rho_df_frag_graph g /\ ig_wf_sp (build_indexed g) /\
                    (exists (sub typ : triple).
                       memP sub g /\ sub.p == i_rdfs_subClassOf /\ sub.s == S_IRI class_iri /\
                       memP typ g /\ typ.p == i_rdf_type /\ typ.o == T_IRI class_iri /\
                       t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)))
          (ensures  memP t (rdfs_rule_subClassOf g (build_indexed g))) =
  let lemma_refl (h : rdf_graph) : Lemma (is_subgraph h h) = () in
  lemma_refl g;
  rdfs_rule_subClassOf_reaches_iri2 g g t class_iri

// ===================================================================
// 6. FINDING F-1, MACHINE-CHECKED.
//
// The task's flat statement "rho_df_frag_graph g ==> rho_df_frag_graph
// (rho_df_closure g fuel)" is FALSE. Witness: `g = [ P
// rdfs:subPropertyOf rdfs:subPropertyOf ; a P _:b1 ]` satisfies
// `rho_df_frag_graph` (F1: every object is an IRI or blank node; F2:
// the one subPropertyOf triple's object IS an IRI -- rdfs:
// subPropertyOf itself). One application of `rdfs_rule_subPropertyOf`
// (rdfs7: "aaa subPropertyOf bbb, xxx aaa yyy |- xxx bbb yyy",
// instantiated aaa=P, bbb=rdfs:subPropertyOf, xxx=a, yyy=_:b1) derives
// `a rdfs:subPropertyOf _:b1`, whose OBJECT is a blank node -- F2
// requires an IRI there. So this row's output (hence
// `rho_df_closure_step g`, hence `rho_df_closure g fuel` for any fuel
// that actually applies the row) does NOT satisfy `rho_df_frag_graph`,
// even though `g` does.
//
// Real engine behaviour, not a proof artefact: `rdfs_rule_
// subPropertyOf` never special-cases `bbb = rdfs:subPropertyOf`, and
// nothing in `rho_df_frag_graph` rules out declaring an ordinary
// property P a sub-property of `rdfs:subPropertyOf` itself. F2 keeps
// the STARTING graph inside the tree's generalized-RDF term algebra;
// it is not, and cannot be by construction, an invariant of the six-
// rule step.
//
// CONSEQUENCE for theorem 5: `rho_df_closure_decides` cannot derive
// `rho_df_frag_graph (rho_df_closure g fuel)` from `rho_df_frag_graph
// g` alone. It carries that fact as an explicit hypothesis instead --
// the same "hypotheses carried, not discharged" discipline
// RDF.Entailment.RDFS.Completeness.fst's own banner already applies to
// `rho_df_closed` and `is_subgraph`.
// ===================================================================

let f1_decl_triple (p : wf_iri) : triple =
  { s = S_IRI p; p = i_rdfs_subPropertyOf; o = T_IRI i_rdfs_subPropertyOf }

let f1_data_triple (p a : wf_iri) : triple =
  { s = S_IRI a; p = p; o = T_BNode "b1" }

let f1_witness (p a : wf_iri) : rdf_graph = [ f1_decl_triple p; f1_data_triple p a ]

let f1_bad_triple (a : wf_iri) : triple =
  { s = S_IRI a; p = i_rdfs_subPropertyOf; o = T_BNode "b1" }

let lemma_f1_witness_frag (p a : wf_iri)
  : Lemma (requires ~(p == i_rdfs_subPropertyOf))
          (ensures  rho_df_frag_graph (f1_witness p a)) = ()

let lemma_f1_bad_triple_not_frag (a : wf_iri)
  : Lemma (~(rho_df_frag_triple (f1_bad_triple a))) = ()

// `rdfs7_reaches_fact` no longer carried as a hypothesis here (RESOLVED
// 2026-08-06, section 5's rdfs7 banner) -- this witness graph's reach
// is now derived directly from the unconditional `rdfs_rule_
// subPropertyOf_reaches`, in the same shape `assert (rdfs7_derives g
// (f1_bad_triple a))` below already established.
#push-options "--z3rlimit 100"
let lemma_f1_bad_triple_derived (p a : wf_iri)
  : Lemma (requires ~(p == i_rdfs_subPropertyOf) /\
                    ig_wf_sp (build_indexed (f1_witness p a)))
          (ensures  memP (f1_bad_triple a)
                         (rdfs_rule_subPropertyOf (f1_witness p a) (build_indexed (f1_witness p a)))) =
  lemma_vocab_agree ();
  let g = f1_witness p a in
  lemma_f1_witness_frag p a;
  let decl = f1_decl_triple p in
  let u = f1_data_triple p a in
  introduce exists (declx ux : triple) (aa b : wf_iri).
      memP declx g /\ declx.p == i_rdfs_subPropertyOf /\
      declx.s == S_IRI aa /\ declx.o == T_IRI b /\
      memP ux g /\ ux.p == aa /\
      f1_bad_triple a == ({ s = ux.s; p = b; o = ux.o } <: triple)
  with decl u p i_rdfs_subPropertyOf
  and ();
  assert (rdfs7_derives g (f1_bad_triple a));
  rdfs_rule_subPropertyOf_reaches g (f1_bad_triple a)
#pop-options

// -------------------------------------------------------------------
// THEOREM (finding F-1, separation). Every conjunct is unconditionally
// machine-checked (the `rdfs7_reaches_fact` hypothesis this used to
// carry is DISCHARGED, not just dropped -- see section 5's rdfs7
// RESOLVED banner and `rdfs_rule_subPropertyOf_reaches` above).
// -------------------------------------------------------------------
val rho_df_frag_preservation_fails (p a : wf_iri)
  : Lemma (requires ~(p == i_rdfs_subPropertyOf) /\
                    ig_wf_sp (build_indexed (f1_witness p a)))
          (ensures  rho_df_frag_graph (f1_witness p a) /\
                    memP (f1_bad_triple a)
                         (rdfs_rule_subPropertyOf (f1_witness p a) (build_indexed (f1_witness p a))) /\
                    ~(rho_df_frag_triple (f1_bad_triple a)))

let rho_df_frag_preservation_fails p a =
  lemma_f1_witness_frag p a;
  lemma_f1_bad_triple_derived p a;
  lemma_f1_bad_triple_not_frag a

// ===================================================================
// 7. THEOREM 3 -- CLOSEDNESS.
//
// Route: (a) a triple present at any of the six intermediate stages
// survives to `rho_df_closure_step_pre_dedup c` (each later row only
// ADDS -- the six per-row extensivity lemmas already reused for
// theorem 1); (b) `graph_dedup_sort` doesn't drop it either, under
// `no_dup_keys`; (c) at a fuel witness where the length test passes,
// `rho_df_step_saturated c` (the `lemma_len_eq_saturated` argument,
// restated for the six-rule step, taking the SAME two explicit
// hypotheses -- `no_dup_keys`/`no_repeats_p` -- as hypotheses, per the
// brief); (d) combine with the six PER-ROW REACHES lemmas (section 5).
//
// Five of the six rows (domain, range, subPropertyOf, subClassOf-
// trans, subPropertyOf-trans) close FULLY. The sixth (subClassOf,
// rdfs9) closes only under the extra `rho_df_subclass_subjects_iri c`
// hypothesis finding F-2 makes necessary -- carried explicitly, not
// smuggled into `rho_df_closed`'s definition (which this module does
// not touch).
// ===================================================================

let rho_df_step_saturated (c : rdf_graph) : prop =
  forall (t : triple). memP t (rho_df_closure_step c) ==> memP t c

val rho_df_len_eq_saturated (c : rdf_graph)
  : Lemma
    (requires no_dup_keys (rho_df_closure_step_pre_dedup c) /\
              no_repeats_p c /\ no_repeats_p (rho_df_closure_step c) /\
              graph_len (rho_df_closure_step c) = graph_len c)
    (ensures  rho_df_step_saturated c)

#push-options "--z3rlimit 60"
let rho_df_len_eq_saturated c =
  introduce forall (t : triple). memP t c ==> memP t (rho_df_closure_step c)
  with introduce memP t c ==> memP t (rho_df_closure_step c)
  with _ . lemma_rho_df_step_extensive c;
  lemma_no_repeats_subset_same_length_eq c (rho_df_closure_step c)
#pop-options

// Row-by-row: "present right after row K" survives to the pre-dedup
// accumulator. Six variants (the six starting points), each chaining
// the SAME per-row extensivity lemmas theorem 1 already reuses.
#push-options "--z3rlimit 100"
let lemma_after_row1_pre_dedup (c : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma (requires ig == build_indexed c /\ memP t (rdfs_rule_subPropertyOf c ig))
          (ensures  memP t (rho_df_closure_step_pre_dedup c)) =
  let g1 = rdfs_rule_subPropertyOf c ig in
  lemma_rdfs_rule_domain_extensive g1 ig t;
  let g2 = rdfs_rule_domain g1 ig in
  lemma_rdfs_rule_range_extensive g2 ig t;
  let g3 = rdfs_rule_range g2 ig in
  lemma_rdfs_rule_subClassOf_extensive g3 ig t;
  let g4 = rdfs_rule_subClassOf g3 ig in
  lemma_rdfs_rule_subClassOf_trans_extensive g4 ig t;
  let g5 = rdfs_rule_subClassOf_trans g4 ig in
  lemma_rdfs_rule_subPropertyOf_trans_extensive g5 ig t

let lemma_after_row2_pre_dedup (c : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma (requires ig == build_indexed c /\
                    memP t (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig))
          (ensures  memP t (rho_df_closure_step_pre_dedup c)) =
  let g2 = rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig in
  lemma_rdfs_rule_range_extensive g2 ig t;
  let g3 = rdfs_rule_range g2 ig in
  lemma_rdfs_rule_subClassOf_extensive g3 ig t;
  let g4 = rdfs_rule_subClassOf g3 ig in
  lemma_rdfs_rule_subClassOf_trans_extensive g4 ig t;
  let g5 = rdfs_rule_subClassOf_trans g4 ig in
  lemma_rdfs_rule_subPropertyOf_trans_extensive g5 ig t

let lemma_after_row3_pre_dedup (c : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma (requires ig == build_indexed c /\
                    memP t (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig))
          (ensures  memP t (rho_df_closure_step_pre_dedup c)) =
  let g3 = rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig in
  lemma_rdfs_rule_subClassOf_extensive g3 ig t;
  let g4 = rdfs_rule_subClassOf g3 ig in
  lemma_rdfs_rule_subClassOf_trans_extensive g4 ig t;
  let g5 = rdfs_rule_subClassOf_trans g4 ig in
  lemma_rdfs_rule_subPropertyOf_trans_extensive g5 ig t

let lemma_after_row4_pre_dedup (c : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma (requires ig == build_indexed c /\
                    memP t (rdfs_rule_subClassOf
                              (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig))
          (ensures  memP t (rho_df_closure_step_pre_dedup c)) =
  let g4 = rdfs_rule_subClassOf
             (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig in
  lemma_rdfs_rule_subClassOf_trans_extensive g4 ig t;
  let g5 = rdfs_rule_subClassOf_trans g4 ig in
  lemma_rdfs_rule_subPropertyOf_trans_extensive g5 ig t

let lemma_after_row5_pre_dedup (c : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma (requires ig == build_indexed c /\
                    memP t (rdfs_rule_subClassOf_trans
                              (rdfs_rule_subClassOf
                                (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig) ig))
          (ensures  memP t (rho_df_closure_step_pre_dedup c)) =
  let g5 = rdfs_rule_subClassOf_trans
             (rdfs_rule_subClassOf
               (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig) ig in
  lemma_rdfs_rule_subPropertyOf_trans_extensive g5 ig t
#pop-options

// row 6 (subPropertyOf-trans) needs no bridge: `rho_df_closure_step_pre_dedup`
// literally ends there.

// `rho_df_step_saturated c` plus the dedup step gets any pre-dedup
// member into `c` itself (mirrors `lemma_len_eq_saturated`'s own use
// of `lemma_step_extensive`, restated for the six-rule step).
let lemma_pre_dedup_in_c (c : rdf_graph) (t : triple)
  : Lemma (requires no_dup_keys (rho_df_closure_step_pre_dedup c) /\
                    rho_df_step_saturated c /\
                    memP t (rho_df_closure_step_pre_dedup c))
          (ensures  memP t c) =
  lemma_graph_dedup_sort_extensive (rho_df_closure_step_pre_dedup c) t;
  lemma_rho_df_step_is_dedup_of_pre_dedup c

// The extra hypothesis finding F-2 makes necessary: every
// `rdfs:subClassOf` triple's SUBJECT in `c` is an IRI (not a blank
// node). Satisfiable (any graph with no blank-node-subject subClassOf
// triple), NOT derivable from `rho_df_frag_graph c` alone (F1/F2 both
// constrain OBJECTS, never subjects).
let rho_df_subclass_subjects_iri (c : rdf_graph) : prop =
  forall (sub : triple). memP sub c /\ sub.p == i_rdfs_subClassOf ==> S_IRI? sub.s

// `is_subgraph c gK`: `c` survives to each of the six intermediate
// pipeline stages -- direct reuse of the SAME per-row extensivity
// lemmas theorem 1 already composes (section 2), chained FORWARD (c
// into stage K) instead of backward (stage K into the pre-dedup end,
// section 7's `lemma_after_rowN_pre_dedup`). Feeds the `is_subgraph
// src seed` hypothesis every two-graph reaches lemma needs.
#push-options "--z3rlimit 100"
let lemma_c_in_g1 (c : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig == build_indexed c)
          (ensures  is_subgraph c (rdfs_rule_subPropertyOf c ig)) =
  introduce forall (t : triple). memP t c ==> memP t (rdfs_rule_subPropertyOf c ig)
  with introduce memP t c ==> memP t (rdfs_rule_subPropertyOf c ig)
  with _ . lemma_rdfs_rule_subPropertyOf_extensive c ig t

let lemma_c_in_g2 (c : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig == build_indexed c)
          (ensures  is_subgraph c (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig)) =
  let g1 = rdfs_rule_subPropertyOf c ig in
  lemma_c_in_g1 c ig;
  introduce forall (t : triple). memP t c ==> memP t (rdfs_rule_domain g1 ig)
  with introduce memP t c ==> memP t (rdfs_rule_domain g1 ig)
  with _ . lemma_rdfs_rule_domain_extensive g1 ig t

let lemma_c_in_g3 (c : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig == build_indexed c)
          (ensures  is_subgraph c
                      (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig)) =
  let g2 = rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig in
  lemma_c_in_g2 c ig;
  introduce forall (t : triple). memP t c ==> memP t (rdfs_rule_range g2 ig)
  with introduce memP t c ==> memP t (rdfs_rule_range g2 ig)
  with _ . lemma_rdfs_rule_range_extensive g2 ig t

let lemma_c_in_g4 (c : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig == build_indexed c)
          (ensures  is_subgraph c
                      (rdfs_rule_subClassOf
                        (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig)) =
  let g3 = rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig in
  lemma_c_in_g3 c ig;
  introduce forall (t : triple). memP t c ==> memP t (rdfs_rule_subClassOf g3 ig)
  with introduce memP t c ==> memP t (rdfs_rule_subClassOf g3 ig)
  with _ . lemma_rdfs_rule_subClassOf_extensive g3 ig t

let lemma_c_in_g5 (c : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig == build_indexed c)
          (ensures  is_subgraph c
                      (rdfs_rule_subClassOf_trans
                        (rdfs_rule_subClassOf
                          (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig) ig)) =
  let g4 = rdfs_rule_subClassOf
             (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig in
  lemma_c_in_g4 c ig;
  introduce forall (t : triple). memP t c ==> memP t (rdfs_rule_subClassOf_trans g4 ig)
  with introduce memP t c ==> memP t (rdfs_rule_subClassOf_trans g4 ig)
  with _ . lemma_rdfs_rule_subClassOf_trans_extensive g4 ig t
#pop-options

#push-options "--z3rlimit 150"
// Each row's completeness at the graph theorem 3 actually needs
// (`c`) has to instantiate the corresponding TWO-GRAPH reaches lemma
// at (src := c, seed := the pipeline's ACCUMULATOR right before this
// row runs) -- the diagonal one-graph corollaries only cover a rule
// applied to its OWN premise source, which is what row 1 does but
// none of rows 2-6 do (each folds over, or reads through, the
// accumulator the PRIOR rows already extended).
let lemma_rho_df_closed_row_domain (c : rdf_graph)
  : Lemma (requires rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
                    no_dup_keys (rho_df_closure_step_pre_dedup c) /\ rho_df_step_saturated c)
          (ensures  forall (t : triple). rdfs2_derives c t ==> memP t c) =
  let ig = build_indexed c in
  introduce forall (t : triple). rdfs2_derives c t ==> memP t c
  with introduce rdfs2_derives c t ==> memP t c
  with _ . begin
    let g1 = rdfs_rule_subPropertyOf c ig in
    lemma_c_in_g1 c ig;
    rdfs_rule_domain_reaches2 c g1 t;
    lemma_after_row2_pre_dedup c ig t;
    lemma_pre_dedup_in_c c t
  end

let lemma_rho_df_closed_row_range (c : rdf_graph)
  : Lemma (requires rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
                    no_dup_keys (rho_df_closure_step_pre_dedup c) /\ rho_df_step_saturated c)
          (ensures  forall (t : triple). rdfs3_derives c t ==> memP t c) =
  let ig = build_indexed c in
  introduce forall (t : triple). rdfs3_derives c t ==> memP t c
  with introduce rdfs3_derives c t ==> memP t c
  with _ . begin
    let g2 = rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig in
    lemma_c_in_g2 c ig;
    rdfs_rule_range_reaches2 c g2 t;
    lemma_after_row3_pre_dedup c ig t;
    lemma_pre_dedup_in_c c t
  end

// `rdfs7_reaches_fact c` no longer carried as a hypothesis (RESOLVED
// 2026-08-06, section 5's rdfs7 banner) -- discharged directly by
// `rdfs_rule_subPropertyOf_reaches`. Every row's contribution to
// `rho_df_closed` below is now unconditional (row 9/subClassOf still
// needs `rho_df_subclass_subjects_iri`, finding F-2, carried
// separately at the theorem-3 val).
let lemma_rho_df_closed_row_subPropertyOf (c : rdf_graph)
  : Lemma (requires rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
                    no_dup_keys (rho_df_closure_step_pre_dedup c) /\ rho_df_step_saturated c)
          (ensures  forall (t : triple). rdfs7_derives c t ==> memP t c) =
  introduce forall (t : triple). rdfs7_derives c t ==> memP t c
  with introduce rdfs7_derives c t ==> memP t c
  with _ . begin
    rdfs_rule_subPropertyOf_reaches c t;
    assert (memP t (rdfs_rule_subPropertyOf c (build_indexed c)));
    lemma_after_row1_pre_dedup c (build_indexed c) t;
    lemma_pre_dedup_in_c c t
  end

let lemma_rho_df_closed_row_subClassOf_trans (c : rdf_graph)
  : Lemma (requires rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
                    no_dup_keys (rho_df_closure_step_pre_dedup c) /\ rho_df_step_saturated c)
          (ensures  forall (t : triple). rdfs11_derives c t ==> memP t c) =
  let ig = build_indexed c in
  introduce forall (t : triple). rdfs11_derives c t ==> memP t c
  with introduce rdfs11_derives c t ==> memP t c
  with _ . begin
    let g4 = rdfs_rule_subClassOf
               (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig in
    lemma_c_in_g4 c ig;
    rdfs_rule_subClassOf_trans_reaches2 c g4 t;
    lemma_after_row5_pre_dedup c ig t;
    lemma_pre_dedup_in_c c t
  end

let lemma_rho_df_closed_row_subPropertyOf_trans (c : rdf_graph)
  : Lemma (requires rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
                    no_dup_keys (rho_df_closure_step_pre_dedup c) /\ rho_df_step_saturated c)
          (ensures  forall (t : triple). rdfs5_derives c t ==> memP t c) =
  let ig = build_indexed c in
  introduce forall (t : triple). rdfs5_derives c t ==> memP t c
  with introduce rdfs5_derives c t ==> memP t c
  with _ . begin
    let g5 = rdfs_rule_subClassOf_trans
               (rdfs_rule_subClassOf
                 (rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig) ig) ig in
    lemma_c_in_g5 c ig;
    rdfs_rule_subPropertyOf_trans_reaches2 c g5 t;
    (* row 6 needs no bridge -- pre_dedup ends there *)
    lemma_pre_dedup_in_c c t
  end

// Row 9 (subClassOf) -- FULL under the extra `rho_df_subclass_
// subjects_iri` hypothesis finding F-2 forces.
let lemma_rho_df_closed_row_subClassOf (c : rdf_graph)
  : Lemma (requires rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
                    rho_df_subclass_subjects_iri c /\
                    no_dup_keys (rho_df_closure_step_pre_dedup c) /\ rho_df_step_saturated c)
          (ensures  forall (t : triple). rdfs9_derives c t ==> memP t c) =
  let ig = build_indexed c in
  introduce forall (t : triple). rdfs9_derives c t ==> memP t c
  with introduce rdfs9_derives c t ==> memP t c
  with _ . begin
    eliminate exists (sub typ : triple) (xs : subject).
        memP sub c /\ sub.p == i_rdfs_subClassOf /\ sub.s == xs /\
        memP typ c /\ typ.p == i_rdf_type /\ typ.o == subj_term xs /\
        t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)
    returns memP t c
    with _ . begin
      assert (S_IRI? sub.s);
      // `sub.s == xs`, and `rho_df_subclass_subjects_iri c` pins
      // `sub.s` to `S_IRI _` -- match `xs` directly (not `eliminate
      // exists`, which needs an actual existential term in context,
      // not merely a refinement fact) to name the IRI.
      match xs with
      | S_IRI class_iri ->
        assert (typ.o == T_IRI class_iri);
        assert (exists (sub2 typ2 : triple).
                  memP sub2 c /\ sub2.p == i_rdfs_subClassOf /\ sub2.s == S_IRI class_iri /\
                  memP typ2 c /\ typ2.p == i_rdf_type /\ typ2.o == T_IRI class_iri /\
                  t == ({ s = typ2.s; p = i_rdf_type; o = sub2.o } <: triple));
        let g3 = rdfs_rule_range (rdfs_rule_domain (rdfs_rule_subPropertyOf c ig) ig) ig in
        lemma_c_in_g3 c ig;
        rdfs_rule_subClassOf_reaches_iri2 c g3 t class_iri;
        lemma_after_row4_pre_dedup c ig t;
        lemma_pre_dedup_in_c c t
      | S_BNode _ -> ()
    end
  end
#pop-options

// -------------------------------------------------------------------
// THEOREM 3. `rdfs7_reaches_fact c` DROPPED from the hypothesis list
// 2026-08-06 (statement strengthening) -- discharged by `rdfs_rule_
// subPropertyOf_reaches` inside `lemma_rho_df_closed_row_
// subPropertyOf` now, not carried. `rho_df_subclass_subjects_iri c`
// (finding F-2, row 9/subClassOf) remains carried -- a different row,
// not touched by this landing.
// -------------------------------------------------------------------
val rho_df_closure_closed (g : rdf_graph) (fuel : nat)
  : Lemma
    (requires (let c = rho_df_closure g fuel in
               rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
               rho_df_subclass_subjects_iri c /\
               no_dup_keys (rho_df_closure_step_pre_dedup c) /\
               no_repeats_p c /\ no_repeats_p (rho_df_closure_step c) /\
               graph_len (rho_df_closure_step c) = graph_len c))
    (ensures  rho_df_closed (rho_df_closure g fuel))

#push-options "--z3rlimit 60"
let rho_df_closure_closed g fuel =
  let c = rho_df_closure g fuel in
  rho_df_len_eq_saturated c;
  lemma_rho_df_closed_row_domain c;
  lemma_rho_df_closed_row_range c;
  lemma_rho_df_closed_row_subPropertyOf c;
  lemma_rho_df_closed_row_subClassOf_trans c;
  lemma_rho_df_closed_row_subPropertyOf_trans c;
  lemma_rho_df_closed_row_subClassOf c
#pop-options

// ===================================================================
// 8. THEOREM 4 -- FRAGMENT PRESERVATION.
//
// FALSE as a flat implication (finding F-1, section 6). What IS true,
// and what theorem 5 actually needs: `rho_df_frag_graph (rho_df_closure
// g fuel)` is a SATISFIABLE, checkable-per-graph hypothesis (finding
// F-1's witness is a two-triple graph specifically engineered to
// trigger the gap; it is not generic). Carried explicitly into
// theorem 5 below, per the "hypotheses carried, not discharged"
// discipline this module inherits from
// RDF.Entailment.RDFS.Completeness.fst's own banner. No lemma named
// `rho_df_closure_frag_preserving` is stated here as an unconditional
// theorem, because none holds; `rho_df_frag_preservation_fails`
// (section 6) is the machine-checked record of why.
// ===================================================================

// ===================================================================
// 9. THEOREM 5 -- THE PAYOFF: instantiate `rho_df_saturation_iff` with
// theorems 1-3 (extensive, sound, closed) plus the carried
// `rho_df_frag_graph c` hypothesis theorem 4's finding requires.
// ===================================================================

// `rdfs7_reaches_fact c` DROPPED from the hypothesis list 2026-08-06,
// same reason as theorem 3's val above (it feeds `rho_df_closure_
// closed`, which no longer needs it).
val rho_df_closure_decides (g e : rdf_graph) (fuel : nat)
  : Lemma
    (requires (let c = rho_df_closure g fuel in
               rho_df_chain_canonical g /\ rho_df_chain_wf g /\
               rho_df_frag_graph c /\ ig_wf_sp (build_indexed c) /\
               rho_df_subclass_subjects_iri c /\
               no_dup_keys (rho_df_closure_step_pre_dedup c) /\
               no_repeats_p c /\ no_repeats_p (rho_df_closure_step c) /\
               graph_len (rho_df_closure_step c) = graph_len c /\
               graph_tt_free e))
    (ensures  (let c = rho_df_closure g fuel in
               rho_df_entails g e <==> simple_entailment_spec c e))

#push-options "--z3rlimit 60"
let rho_df_closure_decides g e fuel =
  let c = rho_df_closure g fuel in
  rho_df_closure_extensive g fuel;
  rho_df_closure_sound g fuel;
  rho_df_closure_closed g fuel;
  rho_df_saturation_iff g c e
#pop-options

// ===================================================================
// 10. DECIDABLE FRAGMENT CHECKER -- `rho_df_frag_graph`
// (RDF.Entailment.RDFS.Completeness, opened above) is a `prop`, so it
// cannot be called from extracted code. `is_rho_df_frag` is its
// `List.Tot.for_all`-shaped `bool` twin, EXTRACTABLE and the function
// the npm/js `rhoDfFragmentCheck` entry point calls;
// `lemma_is_rho_df_frag_correct` is the recipe-shaped correspondence
// lemma pinning it to the prop (same shape as
// `RDF.Semantics.HypothesisWitness.lemma_memP_obj_is_iri`'s
// for_all/memP recursion).
// ===================================================================

// F1's per-object test, decidable: bool twin of `rho_df_object_ok`.
let is_rho_df_object_ok (t : rdf_term) : bool =
  match t with
  | T_IRI _   -> true
  | T_BNode _ -> true
  | _         -> false

let lemma_is_rho_df_object_ok_correct (t : rdf_term)
  : Lemma (ensures (is_rho_df_object_ok t == true) <==> rho_df_object_ok t) =
  match t with
  | T_IRI _            -> ()
  | T_BNode _          -> ()
  | T_Literal _        -> ()
  | T_TripleTerm _ _ _ -> ()

// F1 /\ F2 per-triple, decidable: bool twin of `rho_df_frag_triple`.
// `t.p = i_rdfs_subPropertyOf` is ordinary string equality on `wf_iri`
// (`RDF.Term.wf_iri = s:iri{is_iri s}`, `iri = string`, an eqtype), so
// it decides the same fact `t.p == i_rdfs_subPropertyOf` tests in the
// prop version.
let is_rho_df_frag_triple (t : triple) : bool =
  is_rho_df_object_ok t.o &&
  (if t.p = i_rdfs_subPropertyOf then T_IRI? t.o else true)

let lemma_is_rho_df_frag_triple_correct (t : triple)
  : Lemma (ensures (is_rho_df_frag_triple t == true) <==> rho_df_frag_triple t) =
  lemma_is_rho_df_object_ok_correct t.o

// The graph-level check, decidable: bool twin of `rho_df_frag_graph`.
// Definitionally `List.Tot.for_all is_rho_df_frag_triple g` -- spelled
// out as a recursion here so the correspondence proof below is a
// direct structural induction, one step per cons, matching
// `rho_df_frag_graph`'s own `memP`-over-cons unfolding.
let rec is_rho_df_frag (g : rdf_graph) : Tot bool (decreases g) =
  match g with
  | []      -> true
  | t :: tl -> is_rho_df_frag_triple t && is_rho_df_frag tl

let lemma_is_rho_df_frag_is_for_all (g : rdf_graph)
  : Lemma (ensures is_rho_df_frag g == List.Tot.for_all is_rho_df_frag_triple g)
          (decreases g) =
  let rec aux (g : rdf_graph)
    : Lemma (ensures is_rho_df_frag g == List.Tot.for_all is_rho_df_frag_triple g)
            (decreases g) =
    match g with
    | []      -> ()
    | t :: tl -> aux tl
  in
  aux g

let rec lemma_is_rho_df_frag_correct (g : rdf_graph)
  : Lemma (ensures (is_rho_df_frag g == true) <==> rho_df_frag_graph g)
          (decreases g) =
  match g with
  | []      -> ()
  | t :: tl ->
    lemma_is_rho_df_frag_triple_correct t;
    lemma_is_rho_df_frag_correct tl
