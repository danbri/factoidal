module RDF.Entailment.RDFSPlus

// ===================================================================
// RDFS-Plus closure operator.
//
// TIER: this is RDFS-Plus / RDFS++ -- RDFS plus a small practical OWL
// subset: owl:sameAs (symmetry, transitivity, substitution into
// subject/object/predicate position), owl:inverseOf,
// owl:SymmetricProperty, owl:TransitiveProperty,
// owl:FunctionalProperty, owl:InverseFunctionalProperty,
// owl:equivalentClass, owl:equivalentProperty. Name sources:
// "RDFS-Plus" (Allemang & Hendler, Semantic Web for the Working
// Ontologist, 2008) and "RDFS++" (Franz Inc., AllegroGraph
// reasoner). Public API name: `rdfsPlusClosure`. This tier sits
// between core-rdfs (rho-df, six rules, full bidirectional chain
// proofs -- see RDF.Entailment.RDFS.RhoDFClosure.fst) and full
// OWL 2 RL.
//
// CLAIM LEVEL, stated plainly: every OWL rule this operator runs
// carries a PROVED licensing lemma (and truth-preservation lemma) in
// OWL.RL.Refinement.fst / OWL.Semantics.Soundness.fst -- per-rule
// certificates, e.g. eq_sym_licensed / owl_rule_sameAs_symmetry_licensed
// (OWL.RL.Refinement.fst ~166-208), eq_trans_licensed (~825),
// prp_symp_licensed (~358). The rows covered: eq-sym, eq-trans,
// eq-rep-s, eq-rep-o, eq-rep-p, prp-symp, prp-trp, prp-inv (two rows,
// prp-inv1 + prp-inv2), prp-fp, prp-ifp, cax-eqc, prp-eqp.
//
// NO chain-level completeness is claimed for this tier: unlike
// rho_df_closure (which RDF.Entailment.RDFS.Completeness.fst proves
// decides rho-df entailment via `rho_df_saturation_iff`),
// owl:sameAs introduces equality reasoning, and the Herbrand
// construction behind the corerdfs completeness theorem does not
// survive quotienting by sameAs classes. This module makes no
// completeness claim, chain-level or otherwise -- each step's rows
// are individually licensed and truth-preserving; nothing here
// asserts that the fixed point captures every RDFS-Plus consequence.
//
// EXCLUSION, documented: `owl_rule_sameAs_reflexivity` (eq-ref: `x
// sameAs x` for every node in the graph) is deliberately NOT in the
// step below -- a reflexivity noise row, excluded for the same
// reason rho_df_closure_step excludes rdfs6/rdfs10 (see
// RDF.Entailment.RDFS.RhoDFClosure.fst): it manufactures one triple
// per node without contributing new entailments any downstream rule
// consumes, and including it would only inflate every intermediate
// graph.
//
// SHAPE: byte-identical fuel/dedup/length-test loop to
// `rho_df_closure` (RDF.Entailment.RDFS.RhoDFClosure.fst lines
// 98-122) and to `rdfs_closure` (RDFS.Closure.fsti). Zero new rule
// bodies, zero new lemmas: every function called below is the SAME
// `rdfs_closure_step` / `owl_rule_*` function the shipping RDFS and
// OWL closures already call -- no reimplementation.
// ===================================================================

open FStar.List.Tot
open FStar.List.Tot.Properties
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Closure

let rdfs_plus_step_pre_dedup (g : rdf_graph) : rdf_graph =
  let g0 = rdfs_closure_step g in
  let ig = build_indexed g0 in
  let g1  = owl_rule_equivalent_class g0 ig in
  let g2  = owl_rule_equivalent_property g1 ig in
  let g3  = owl_rule_symmetric_property g2 ig in
  let g4  = owl_rule_transitive_property g3 ig in
  let g5  = owl_rule_inverse_of g4 ig in
  let g6  = owl_rule_inverseOf_domain_range_flip g5 ig in
  let g7  = owl_rule_functional g6 ig in
  let g8  = owl_rule_inverse_functional g7 ig in
  let g9  = owl_rule_sameAs_symmetry g8 ig in
  let g10 = owl_rule_sameAs_transitivity g9 ig in
  let g11 = owl_rule_sameAs_replace_subject g10 ig in
  let g12 = owl_rule_sameAs_replace_object g11 ig in
  owl_rule_sameAs_replace_predicate g12 ig

let rdfs_plus_step (g : rdf_graph) : rdf_graph =
  graph_dedup_sort (rdfs_plus_step_pre_dedup g)

#push-options "--z3rlimit 30"
let rec rdfs_plus_closure (g : rdf_graph) (fuel : nat) : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> g
  | n ->
    let g' = rdfs_plus_step g in
    if graph_len g' = graph_len g
    then g
    else rdfs_plus_closure g' (n - 1)
#pop-options
