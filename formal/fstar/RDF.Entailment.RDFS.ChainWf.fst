module RDF.Entailment.RDFS.ChainWf

// ===================================================================
// #338 follow-up, PHASE 2: `closure_chain_wf g` -- the hypothesis
// `RDF.Entailment.RDFS.ModelTheory.rdfs_closure_sound` needs and that
// nobody could previously instantiate for a real graph -- follows from
// `RDF.Entailment.RDFS.SepFree.graph_sep_free g` alone.
//
// THE SHAPE OF THE ARGUMENT.
//   `closure_chain_wf g = forall n. ig_wf_sp (build_indexed (closure_iter g n))`
//   (ModelTheory.fst). `ig_wf_sp (build_indexed h)` is exactly what
//   `RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_sp` discharges
//   from the side condition `graph_sp_sep_free h`, which
//   `RDF.Entailment.RDFS.SepFree.lemma_graph_sep_free_sp` gets from the
//   stronger `graph_sep_free h`. So the whole chain closes as soon as
//   "sep-freeness is a CLOSURE INVARIANT": every `closure_iter g n` is
//   `graph_sep_free`, given `graph_sep_free g`. That per-step
//   preservation is what SepFree (phase 1) proved ROW BY ROW; this
//   module folds the twelve rows into one step-lemma (mirroring
//   ModelTheory's `rdfs_closure_step_sound`, truth swapped for
//   sep-freeness) and inducts it over `closure_iter`.
//
// TWO DEVIATIONS FROM A NAIVE READING OF THE SepFree ROW LEMMAS.
//   1. `rdfs_rule_subClassOf` / `_subClassOf_trans` / `_subPropertyOf_trans`
//      are licensed by the TWO-SOURCE `rdfs9_derives2 g ig.ig_triples` /
//      `rdfs11_derives2 g ig.ig_triples` / `rdfs5_derives2 g ig.ig_triples`
//      (RDF.Entailment.RDFS.Refinement's `_licensed` theorems), not the
//      single-graph diagonal SepFree proves lemmas for. Section 1 below
//      adds the two-source variants -- copies of SepFree's rdfs5/9/11
//      row proofs with `gd`/`gs` kept apart, since the linking variable
//      never reaches the conclusion in any of the three rows (SepFree's
//      own comment on rdfs5/rdfs9/rdfs11) so the proof text is
//      unchanged, only the two premises' SOURCE graphs are.
//   2. `rdfs_rule_container_membership` cannot go through its licensing
//      predicate at all (`rdfs_axiomatic` / `rdfs_member_subproperty`
//      both route through `is_rdf_member_iri`, which SepFree's own
//      banner flags as admitting U+001F). Section on that rule proves
//      preservation DIRECTLY from the engine's fold, copying the exact
//      step lambda `RDF.Entailment.RDFS.Refinement.
//      rdfs_rule_container_membership_licensed` already uses, with
//      `RDF.Entailment.RDFS.SepFree.lemma_axiomatic_tables_sep_free`
//      supplying cleanliness of the finite `rdf:_1..rdf:_5` list instead
//      of the (false-in-general) licensing route.
//
// Verify-only module; nothing here extracts, and nothing here is wired
// into build-ocaml.sh (orchestrator's job on landing).
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDF.Vocabulary.Axioms
open RDFS.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas
open RDF.Indexed.KeyInjectivity
open RDF.Entailment.Simple.Spec
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec
open RDF.Entailment.RDFS.Refinement
open RDF.Entailment.RDFS.SepFree
open RDF.Entailment.RDFS.ModelTheory

// ===================================================================
// 0. The generic bridge -- mirrors ModelTheory's `bridge`, truth
// swapped for sep-freeness. `licensed_by2` is
// RDF.Entailment.RDFS.Refinement's (already in scope via the open
// above).
// ===================================================================

let sep_bridge (r : list triple -> triple -> prop) (src seed out : list triple)
  : Lemma (requires graph_sep_free seed /\ licensed_by2 r src seed out /\
                    (forall (t : triple). r src t ==> triple_sep_free t))
          (ensures graph_sep_free out) = ()

// ===================================================================
// 1. Two-source row lemmas for rdfs5 / rdfs9 / rdfs11 -- the three
// rows whose shipping licence (RDF.Entailment.RDFS.Refinement) is
// stated against `<row>_derives2 gd gs`, not the single-graph diagonal
// SepFree proves lemmas for. In all three the linking variable (`ys`
// for rdfs5/rdfs11, `xs` for rdfs9) never reaches the conclusion, so
// the proof body is unchanged from SepFree's diagonal version -- only
// the two premises now come from separate graphs `gd`/`gs`.
// ===================================================================

let lemma_rdfs5_sep_free2 (gd gs : list triple) (t : triple)
  : Lemma (requires graph_sep_free gd /\ graph_sep_free gs /\ rdfs5_derives2 gd gs t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 gd /\ t1.p == i_rdfs_subPropertyOf /\
      memP t2 gs /\ t2.p == i_rdfs_subPropertyOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subPropertyOf; o = t2.o } <: triple)
  returns triple_sep_free t
  with _ . ()

let lemma_rdfs9_sep_free2 (gd gs : list triple) (t : triple)
  : Lemma (requires graph_sep_free gd /\ graph_sep_free gs /\ rdfs9_derives2 gd gs t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (sub typ : triple) (xs : subject).
      memP sub gs /\ sub.p == i_rdfs_subClassOf /\ sub.s == xs /\
      memP typ gd /\ typ.p == i_rdf_type /\ typ.o == subj_term xs /\
      t == ({ s = typ.s; p = i_rdf_type; o = sub.o } <: triple)
  returns triple_sep_free t
  with _ . ()

let lemma_rdfs11_sep_free2 (gd gs : list triple) (t : triple)
  : Lemma (requires graph_sep_free gd /\ graph_sep_free gs /\ rdfs11_derives2 gd gs t)
          (ensures triple_sep_free t) =
  lemma_vocab_sep_free ();
  eliminate exists (t1 t2 : triple) (ys : subject).
      memP t1 gd /\ t1.p == i_rdfs_subClassOf /\
      memP t2 gs /\ t2.p == i_rdfs_subClassOf /\
      subj_term ys == t1.o /\ t2.s == ys /\
      t == ({ s = t1.s; p = i_rdfs_subClassOf; o = t2.o } <: triple)
  returns triple_sep_free t
  with _ . ()

// `d_minimal` (RDF.Entailment.RDF.Spec) is the fixed two-element set
// {rdf:langString, xsd:string} -- both concrete ASCII strings, so
// `datatype_set_sep_free` closes by normalization exactly like
// SepFree's own `lemma_vocab_sep_free`.
let lemma_d_minimal_sep_free ()
  : Lemma (ensures datatype_set_sep_free d_minimal) =
  assert_norm (str_sep_free rdf_lang_string);
  assert_norm (str_sep_free xsd_string);
  introduce forall (a : wf_iri). d_minimal a ==> str_sep_free a
  with introduce d_minimal a ==> str_sep_free a
  with _ . ()

// ===================================================================
// 2. Per-rule preservation corollaries, in the exact order
// `rdfs_closure_step` chains them (RDFS.Closure.fsti lines 511-533).
// Each requires sep-freeness of its own `g` argument, plus sep-freeness
// of `ig.ig_triples` and the index well-formedness the corresponding
// `_licensed` theorem needs (`ig_wf_pred` for the ig_pred-driven rows,
// `ig_wf_sp` for the ig_sp-driven rows, neither for the rows that fold
// straight over `g`) -- read off each `_licensed` theorem's own
// `requires`, not assumed.
// ===================================================================

let rdfs_rule_subPropertyOf_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g /\ graph_sep_free ig.ig_triples /\ ig_wf_pred ig)
          (ensures graph_sep_free (rdfs_rule_subPropertyOf g ig)) =
  rdfs_rule_subPropertyOf_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs7_sep_free ig.ig_triples));
  sep_bridge rdfs7_derives ig.ig_triples g (rdfs_rule_subPropertyOf g ig)

let rdfs_rule_domain_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g /\ graph_sep_free ig.ig_triples /\ ig_wf_pred ig)
          (ensures graph_sep_free (rdfs_rule_domain g ig)) =
  rdfs_rule_domain_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs2_sep_free ig.ig_triples));
  sep_bridge rdfs2_derives ig.ig_triples g (rdfs_rule_domain g ig)

let rdfs_rule_range_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g /\ graph_sep_free ig.ig_triples /\ ig_wf_pred ig)
          (ensures graph_sep_free (rdfs_rule_range g ig)) =
  rdfs_rule_range_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs3_sep_free ig.ig_triples));
  sep_bridge rdfs3_derives ig.ig_triples g (rdfs_rule_range g ig)

let rdfs_rule_subClassOf_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g /\ graph_sep_free ig.ig_triples /\ ig_wf_sp ig)
          (ensures graph_sep_free (rdfs_rule_subClassOf g ig)) =
  rdfs_rule_subClassOf_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (lemma_rdfs9_sep_free2 g ig.ig_triples));
  sep_bridge (rdfs9_derives2 g) ig.ig_triples g (rdfs_rule_subClassOf g ig)

// `rdfs_rule_container_membership` -- DIRECT ROUTE (see module banner
// point 2). No hypothesis on `ig` at all: the rule folds over the
// fixed `container_membership_properties` list, never touching `ig`.
// The step lambda below is copied VERBATIM from
// `RDFS.Closure.rdfs_rule_container_membership` (and from
// `RDF.Entailment.RDFS.Refinement.rdfs_rule_container_membership_licensed`,
// which proves a different invariant over the identical fold) so the
// closing `assert_norm` iota-reduces.
#push-options "--fuel 8 --z3rlimit 60"
let rdfs_rule_container_membership_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g)
          (ensures graph_sep_free (rdfs_rule_container_membership g ig)) =
  lemma_vocab_sep_free ();
  lemma_vocab_agree ();
  lemma_axiomatic_tables_sep_free ();
  let inv : rdf_graph -> prop = graph_sep_free in
  let step : rdf_graph -> wf_iri -> rdf_graph =
    fun (acc : rdf_graph) (cmp : wf_iri) ->
      let t1 : triple = { s = S_IRI cmp; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } in
      let t2 : triple = { s = S_IRI cmp; p = rdf_type;
                          o = T_IRI rdfs_ContainerMembershipProperty } in
      add_triple_unchecked (add_triple_unchecked acc t1) t2 in
  introduce forall (acc : rdf_graph) (cmp : wf_iri).
      (memP cmp container_membership_properties /\ inv acc) ==> inv (step acc cmp)
  with introduce (memP cmp container_membership_properties /\ inv acc) ==> inv (step acc cmp)
  with _ . begin
    assert (str_sep_free cmp);
    let t1 : triple = { s = S_IRI cmp; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } in
    let t2 : triple = { s = S_IRI cmp; p = rdf_type;
                        o = T_IRI rdfs_ContainerMembershipProperty } in
    assert (triple_sep_free t1);
    assert (triple_sep_free t2);
    assert (step acc cmp == t2 :: t1 :: acc);
    assert (forall (x : triple). memP x (t2 :: t1 :: acc) ==>
              (x == t2 \/ x == t1 \/ memP x acc));
    assert (inv (t2 :: t1 :: acc))
  end;
  fold_left_inv inv step container_membership_properties g;
  assert_norm (rdfs_rule_container_membership g ig ==
               fold_left step g container_membership_properties)
#pop-options

let rdfs_rule_subClassOf_trans_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g /\ graph_sep_free ig.ig_triples /\ ig_wf_sp ig)
          (ensures graph_sep_free (rdfs_rule_subClassOf_trans g ig)) =
  rdfs_rule_subClassOf_trans_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (lemma_rdfs11_sep_free2 g ig.ig_triples));
  sep_bridge (rdfs11_derives2 g) ig.ig_triples g (rdfs_rule_subClassOf_trans g ig)

let rdfs_rule_subPropertyOf_trans_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g /\ graph_sep_free ig.ig_triples /\ ig_wf_sp ig)
          (ensures graph_sep_free (rdfs_rule_subPropertyOf_trans g ig)) =
  rdfs_rule_subPropertyOf_trans_licensed g ig;
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (lemma_rdfs5_sep_free2 g ig.ig_triples));
  sep_bridge (rdfs5_derives2 g) ig.ig_triples g (rdfs_rule_subPropertyOf_trans g ig)

// The five RS-2 rows: each folds straight over `g` (no `ig` premise),
// so no index hypothesis is needed.

let rdfs_rule_recognized_datatypes_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g)
          (ensures graph_sep_free (rdfs_rule_recognized_datatypes g ig)) =
  rdfs_rule_recognized_datatypes_licensed g ig;
  lemma_d_minimal_sep_free ();
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs1_sep_free d_minimal));
  introduce forall (t : triple). memP t (rdfs_rule_recognized_datatypes g ig) ==> triple_sep_free t
  with introduce memP t (rdfs_rule_recognized_datatypes g ig) ==> triple_sep_free t
  with _ . ()

let rdfs_rule_class_subclass_resource_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g)
          (ensures graph_sep_free (rdfs_rule_class_subclass_resource g ig)) =
  rdfs_rule_class_subclass_resource_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs8_sep_free g));
  sep_bridge rdfs8_derives g g (rdfs_rule_class_subclass_resource g ig)

let rdfs_rule_datatype_subclass_literal_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g)
          (ensures graph_sep_free (rdfs_rule_datatype_subclass_literal g ig)) =
  rdfs_rule_datatype_subclass_literal_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs13_sep_free g));
  sep_bridge rdfs13_derives g g (rdfs_rule_datatype_subclass_literal g ig)

let rdfs_rule_resource_subject_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g)
          (ensures graph_sep_free (rdfs_rule_resource_subject g ig)) =
  rdfs_rule_resource_subject_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs4a_sep_free g));
  sep_bridge rdfs4a_derives g g (rdfs_rule_resource_subject g ig)

let rdfs_rule_resource_object_preserves_sep (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires graph_sep_free g)
          (ensures graph_sep_free (rdfs_rule_resource_object g ig)) =
  rdfs_rule_resource_object_licensed g ig;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_rdfs4b_sep_free g));
  sep_bridge rdfs4b_derives g g (rdfs_rule_resource_object g ig)

// ===================================================================
// 3. Step preservation -- chains g1..g12 exactly as
// `rdfs_closure_step` / ModelTheory's `rdfs_closure_step_sound` do,
// then carries sep-freeness through the closing `graph_dedup_sort` via
// Refinement's `lemma_graph_dedup_sort_memP` (memP through the dedup
// sort: every output triple came from the input).
// ===================================================================

#push-options "--z3rlimit 120"
val step_preserves_sep_free (g : rdf_graph)
  : Lemma (requires graph_sep_free g) (ensures graph_sep_free (rdfs_closure_step g))

let step_preserves_sep_free g =
  let ig = build_indexed g in
  lemma_build_indexed_wf_pred g;
  lemma_graph_sep_free_sp g;
  lemma_build_indexed_wf_sp g;
  assert (ig.ig_triples == g);
  assert (ig_wf_pred ig);
  assert (ig_wf_sp ig);
  let g1 = rdfs_rule_subPropertyOf g ig in
  rdfs_rule_subPropertyOf_preserves_sep g ig;
  let g2 = rdfs_rule_domain g1 ig in
  rdfs_rule_domain_preserves_sep g1 ig;
  let g3 = rdfs_rule_range g2 ig in
  rdfs_rule_range_preserves_sep g2 ig;
  let g4 = rdfs_rule_subClassOf g3 ig in
  rdfs_rule_subClassOf_preserves_sep g3 ig;
  let g5 = rdfs_rule_container_membership g4 ig in
  rdfs_rule_container_membership_preserves_sep g4 ig;
  let g6 = rdfs_rule_subClassOf_trans g5 ig in
  rdfs_rule_subClassOf_trans_preserves_sep g5 ig;
  let g7 = rdfs_rule_subPropertyOf_trans g6 ig in
  rdfs_rule_subPropertyOf_trans_preserves_sep g6 ig;
  let g8 = rdfs_rule_recognized_datatypes g7 ig in
  rdfs_rule_recognized_datatypes_preserves_sep g7 ig;
  let g9 = rdfs_rule_class_subclass_resource g8 ig in
  rdfs_rule_class_subclass_resource_preserves_sep g8 ig;
  let g10 = rdfs_rule_datatype_subclass_literal g9 ig in
  rdfs_rule_datatype_subclass_literal_preserves_sep g9 ig;
  let g11 = rdfs_rule_resource_subject g10 ig in
  rdfs_rule_resource_subject_preserves_sep g10 ig;
  let g12 = rdfs_rule_resource_object g11 ig in
  rdfs_rule_resource_object_preserves_sep g11 ig;
  FStar.Classical.forall_intro (lemma_graph_dedup_sort_memP g12);
  assert (rdfs_closure_step g == graph_dedup_sort g12)
#pop-options

// ===================================================================
// 4. The chain induction and the discharge.
// ===================================================================

let rec closure_iter_preserves_sep_free (g : rdf_graph) (n : nat)
  : Lemma (requires graph_sep_free g) (ensures graph_sep_free (closure_iter g n))
          (decreases n) =
  if n = 0 then ()
  else begin
    step_preserves_sep_free g;
    closure_iter_preserves_sep_free (rdfs_closure_step g) (n - 1)
  end

// Named helper so the closing `forall n` goal can be reached by
// `FStar.Classical.forall_intro (move_requires ...)` (the standard
// idiom in this tree, e.g. ModelTheory's own `lemma_chain_shift`)
// rather than an `introduce forall` block over a bare conjunction.
let lemma_closure_chain_wf_step (g : rdf_graph) (n : nat)
  : Lemma (requires graph_sep_free g)
          (ensures ig_wf_sp (build_indexed (closure_iter g n))) =
  closure_iter_preserves_sep_free g n;
  lemma_graph_sep_free_sp (closure_iter g n);
  lemma_build_indexed_wf_sp (closure_iter g n)

val theorem_closure_chain_wf_of_sep_free (g : rdf_graph)
  : Lemma (requires graph_sep_free g) (ensures closure_chain_wf g)

let theorem_closure_chain_wf_of_sep_free g =
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_closure_chain_wf_step g))

// ===================================================================
// 5. The payoff instances -- #338's ask: a theorem nobody could
// instantiate carries no assurance until someone can.
// ===================================================================

val theorem_closure_chain_wf_empty () : Lemma (closure_chain_wf [])

let theorem_closure_chain_wf_empty () =
  assert (graph_sep_free (([] <: rdf_graph)));
  theorem_closure_chain_wf_of_sep_free []

val theorem_closure_chain_wf_nonempty_instance () : Lemma (closure_chain_wf ki_sample)

let theorem_closure_chain_wf_nonempty_instance () =
  assert_norm (graph_sep_free_b ki_sample == true);
  lemma_graph_sep_free_b_sound ki_sample;
  theorem_closure_chain_wf_of_sep_free ki_sample
