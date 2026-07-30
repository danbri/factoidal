module RDF.Semantics.HypothesisWitness

// ===================================================================
// SATISFIABILITY WITNESSES for the hypotheses the W3C-refinement
// theorems restrict on.
//
// WHY THIS MODULE EXISTS
// -------------------------------------------------------------------
// A theorem whose `requires` is UNSATISFIABLE verifies cleanly and
// proves nothing. That is not hypothetical here: the first draft of
// RDF.Entailment.RDFS.ModelTheory.rdfs_closure_sound assumed
// `forall (h : rdf_graph). ig_wf_sp (build_indexed h)`, which is
// FALSE, and F* reported "All verification conditions discharged
// successfully". The story is written up in section 3 of
// docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md.
// Until now the guard against a repeat was a paragraph of prose. This
// module makes it machine-checked: for each hypothesis predicate that
// a shipping-function refinement theorem restricts on, a WITNESS.
//
// This module is VERIFY-ONLY. It computes nothing at runtime, it is
// not in any .ml link list, and it edits no shipping module.
//
// WHAT A WITNESS HAS TO BE
// -------------------------------------------------------------------
// Non-degenerate. "The theorem holds of nothing" is exactly the
// failure mode being guarded against, so a witness that is the empty
// graph / empty binding / empty index buys nothing. Every witness
// below is either non-degenerate, or is LABELLED as degenerate with
// the obstruction named. Two hypotheses (`ig_wf_sp`,
// `closure_chain_wf`) reach only the degenerate form; see part 4 and
// the design note's follow-up list. Nothing here was weakened to make
// a proof go through -- that is section 7.7 of
// docs/designissues/2026-07-29-simple-entailment-refinement.md.
//
// LAYOUT
// -------------------------------------------------------------------
//   1. Consistency of the interpretation-condition bundles. The
//      one-element interpretation satisfies all of them.
//   2. NON-TRIVIALITY of the same bundles. Part 1 alone would be
//      satisfied by the all-true IEXT, which satisfies EVERY graph and
//      so leaves open that `rdfs_entails` is the everything-relation.
//      Part 2 closes that: a model of all fifteen RDFS conditions that
//      does NOT satisfy some graph, hence
//      `~(rdfs_entails dd [] unsat_graph)`.
//   3. The data-side restriction predicates of the simple-entailment
//      and SPARQL-algebra verticals.
//   4. The index hypotheses, where the honest answer is a gap.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Semantics
open RDF.Vocabulary.Axioms
open RDF.Entailment.RDF.Spec
open RDF.Entailment.RDFS.Spec
open RDF.Entailment.RDFS.ModelTheory
open RDF.Entailment.Simple.Spec

module OwlC     = OWL.Closure
module SimpleRef = RDF.Entailment.Simple.Refinement
module AlgSpec  = SPARQL11.Algebra.Spec
module Alg      = SPARQL11.Algebra
module AlgRef   = SPARQL11.Algebra.Refinement

// ===================================================================
// 0. Shared vocabulary for the witnesses.
// ===================================================================

let ex_iri : wf_iri =
  assert_norm (is_iri "http://example.org/s");
  "http://example.org/s"

let ex_lit : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "v"; datatype = xsd_string;
                             lang_tag = None; direction = None }));
  { lexical_form = "v"; datatype = xsd_string; lang_tag = None; direction = None }

// ===================================================================
// 1. THE INTERPRETATION-CONDITION BUNDLES ARE CONSISTENT.
//
// `rdfs_entails dd g1 g2` is `forall i. rdfs_conditions dd i ==>
// satisfies i g1 ==> satisfies i g2`. If the fifteen conjuncts of
// `rdfs_conditions` were jointly unsatisfiable, that would be the
// everything-relation and every soundness theorem of
// RDF.Entailment.RDFS.ModelTheory would be vacuous.
//
// Every `cond_*` is an implication whose CONCLUSION is an `iext` atom,
// so an interpretation whose IEXT is all-true satisfies all of them --
// PROVIDED the domain is a single element, because
// `cond_sameas_identity` is an iff and its forward half forces
// `x == y` for every pair the all-true IEXT relates. `unit` supplies
// exactly that. This was checked conjunct by conjunct, not assumed;
// `cond_datatypes` is the one worth naming, and it constrains only
// `i_iri`, never `i_lit`.
// ===================================================================

let trivial_interp : interp = {
  idom     = unit;
  idom_wit = ();
  i_iri    = (fun _ -> ());
  i_lit    = (fun _ -> ());
  i_tt     = (fun _ _ _ -> ());
  iext     = (fun _ _ _ -> True);
}

let lemma_trivial_rdf_conditions ()
  : Lemma (rdf_conditions trivial_interp) = ()

let lemma_trivial_rdfs_conditions (dd : datatype_set)
  : Lemma (rdfs_conditions dd trivial_interp) = ()

let lemma_trivial_owl_rl_pilot_conditions ()
  : Lemma (owl_rl_pilot_conditions trivial_interp) = ()

val theorem_rdf_conditions_satisfiable (_ : unit)
  : Lemma (exists (i : interp). rdf_conditions i)
let theorem_rdf_conditions_satisfiable () = lemma_trivial_rdf_conditions ()

val theorem_rdfs_conditions_satisfiable (dd : datatype_set)
  : Lemma (exists (i : interp). rdfs_conditions dd i)
let theorem_rdfs_conditions_satisfiable dd = lemma_trivial_rdfs_conditions dd

val theorem_owl_rl_pilot_conditions_satisfiable (_ : unit)
  : Lemma (exists (i : interp). owl_rl_pilot_conditions i)
let theorem_owl_rl_pilot_conditions_satisfiable () =
  lemma_trivial_owl_rl_pilot_conditions ()

// ===================================================================
// 2. THE BUNDLES ARE NON-TRIVIALLY SATISFIABLE.
//
// Part 1 proves consistency and nothing more. `trivial_interp`
// satisfies EVERY graph, so it cannot separate two graphs and cannot
// witness that `rdfs_entails` is a proper relation. The sharper
// property is
//
//   exists (i : interp) (g : rdf_graph). rdfs_conditions dd i /\
//                                        ~(satisfies i g)
//
// and it does hold. The construction below is the one that survives
// the obstruction the RDFS conditions put in the way of the obvious
// attempts, which is worth recording because three of them fail:
//
//   (a) "give one predicate an empty extension." Contradicted by
//       `cond_subPropertyOf`, whose conclusion is on an ARBITRARY
//       property q: as soon as `iext subPropertyOf r q` holds, IEXT(r)
//       must be contained in IEXT(q), and `cond_subPropertyOf_refl`
//       plus `cond_cmp_member` put enough pairs into
//       IEXT(I(rdfs:subPropertyOf)) to make that bite.
//   (b) "full extension for a set S of properties, empty otherwise."
//       Same failure, one level up: if I(rdfs:subPropertyOf) is in S
//       its extension is everything, so IEXT(x) must be contained in
//       IEXT(y) for EVERY x and y, forcing S to be everything.
//   (c) "exclude a triple by its PREDICATE." Any element with an empty
//       extension is again killed by (b).
//
// What works is excluding by the OBJECT slot, in a shape closed under
// all fifteen conditions:
//
//   domain      bool. `true` is the resource every IRI denotes;
//               `false` is the resource every LITERAL denotes.
//   IEXT(true)  every pair EXCEPT (true, false).
//   IEXT(false) empty.
//
// Read as a relation: `sep_iext p x y` holds when p is the IRI-side
// resource and either the object is the IRI-side resource or the
// subject is the literal-side one. The exclusion is invisible to
// `cond_subPropertyOf` because the pairs that condition ranges over
// are exactly (true, true), (false, true) and (false, false), and for
// each of them the required containment already holds.
//
// Consequence: a triple with an IRI subject and a LITERAL object is
// false in this model, and it is ground, so no blank-node assignment
// rescues it.
// ===================================================================

let sep_iext (p x y : bool) : prop = b2t (p && (y || not x))

let separating_interp : interp = {
  idom     = bool;
  idom_wit = true;
  i_iri    = (fun _ -> true);
  i_lit    = (fun _ -> false);
  i_tt     = (fun _ _ _ -> true);
  iext     = sep_iext;
}

// -------------------------------------------------------------------
// The axiomatic-triple conditions. Every RDF and RDFS axiomatic triple
// has an IRI object -- checked by `assert_norm` over the two
// transcribed lists rather than asserted -- so its object denotes the
// IRI-side resource and the excluded pair is never reached.
// -------------------------------------------------------------------

let obj_is_iri (t : triple) : bool = T_IRI? t.o

let rec lemma_memP_obj_is_iri (l : list triple) (t : triple)
  : Lemma (requires List.Tot.for_all obj_is_iri l /\ memP t l)
          (ensures  T_IRI? t.o)
          (decreases l) =
  match l with
  | [] -> ()
  | h :: tl ->
    eliminate (t == h) \/ memP t tl
    returns T_IRI? t.o
    with _ . ()
    and  _ . lemma_memP_obj_is_iri tl t

let lemma_sep_denot_iri (a : bnode_assignment separating_interp.idom) (o : rdf_term)
  : Lemma (requires T_IRI? o)
          (ensures  denot_term separating_interp a o == true) =
  match o with
  | T_IRI _ -> ()
  | _ -> ()

let lemma_sep_holds_of_iri_object (a : bnode_assignment separating_interp.idom)
                                  (t : triple)
  : Lemma (requires T_IRI? t.o) (ensures triple_holds separating_interp a t) =
  lemma_sep_denot_iri a t.o

let lemma_sep_rdf_axioms (a : bnode_assignment separating_interp.idom) (t : triple)
  : Lemma (requires rdf_axiomatic t)
          (ensures  triple_holds separating_interp a t) =
  assert_norm (List.Tot.for_all obj_is_iri rdf_axiomatic_triples);
  eliminate (memP t rdf_axiomatic_triples) \/
            (exists (i : wf_iri). is_rdf_member_iri i /\
               t == ({ s = S_IRI i; p = i_rdf_type; o = T_IRI i_rdf_Property } <: triple))
  returns triple_holds separating_interp a t
  with _ . (lemma_memP_obj_is_iri rdf_axiomatic_triples t;
            lemma_sep_holds_of_iri_object a t)
  and  _ . lemma_sep_holds_of_iri_object a t

let lemma_sep_rdfs_axioms (a : bnode_assignment separating_interp.idom) (t : triple)
  : Lemma (requires rdfs_axiomatic t)
          (ensures  triple_holds separating_interp a t) =
  assert_norm (List.Tot.for_all obj_is_iri rdfs_axiomatic_triples);
  eliminate (memP t rdfs_axiomatic_triples) \/
            (exists (i : wf_iri). is_rdf_member_iri i /\
               (t == ({ s = S_IRI i; p = i_rdf_type;
                        o = T_IRI i_rdfs_ContainerMembershipProperty } <: triple) \/
                t == ({ s = S_IRI i; p = i_rdfs_domain;
                        o = T_IRI i_rdfs_Resource } <: triple) \/
                t == ({ s = S_IRI i; p = i_rdfs_range;
                        o = T_IRI i_rdfs_Resource } <: triple)))
  returns triple_holds separating_interp a t
  with _ . (lemma_memP_obj_is_iri rdfs_axiomatic_triples t;
            lemma_sep_holds_of_iri_object a t)
  and  _ . lemma_sep_holds_of_iri_object a t

#push-options "--z3rlimit 60"
let lemma_separating_rdf_conditions ()
  : Lemma (rdf_conditions separating_interp) =
  introduce forall (a : bnode_assignment separating_interp.idom) (t : triple).
      rdf_axiomatic t ==> triple_holds separating_interp a t
  with introduce rdf_axiomatic t ==> triple_holds separating_interp a t
  with _ . lemma_sep_rdf_axioms a t

let lemma_separating_rdfs_conditions (dd : datatype_set)
  : Lemma (rdfs_conditions dd separating_interp) =
  lemma_separating_rdf_conditions ();
  introduce forall (a : bnode_assignment separating_interp.idom) (t : triple).
      rdfs_axiomatic t ==> triple_holds separating_interp a t
  with introduce rdfs_axiomatic t ==> triple_holds separating_interp a t
  with _ . lemma_sep_rdfs_axioms a t
#pop-options

// The graph the separating model rejects: one ground triple whose
// object is a literal.
let unsat_triple : triple = { s = S_IRI ex_iri; p = ex_iri; o = T_Literal ex_lit }
let unsat_graph : rdf_graph = [ unsat_triple ]

let lemma_separating_rejects () : Lemma (~(satisfies separating_interp unsat_graph)) =
  introduce forall (a : bnode_assignment separating_interp.idom).
      ~(holds_all separating_interp a unsat_graph)
  with begin
    assert (memP unsat_triple unsat_graph);
    assert (~(triple_holds separating_interp a unsat_triple))
  end

let lemma_everything_satisfies_empty (i : interp) : Lemma (satisfies i []) =
  assert (holds_all i (fun _ -> i.idom_wit) [])

// -------------------------------------------------------------------
// THEOREM. There is an interpretation meeting all fifteen RDFS
// conditions and a graph it does not satisfy. So the bundle is not
// merely consistent: it does not collapse to the all-true IEXT.
// -------------------------------------------------------------------
val theorem_rdfs_conditions_nontrivially_satisfiable (dd : datatype_set)
  : Lemma (exists (i : interp) (g : rdf_graph).
             rdfs_conditions dd i /\ ~(satisfies i g))
let theorem_rdfs_conditions_nontrivially_satisfiable dd =
  lemma_separating_rdfs_conditions dd;
  lemma_separating_rejects ()

val theorem_rdf_conditions_nontrivially_satisfiable (_ : unit)
  : Lemma (exists (i : interp) (g : rdf_graph).
             rdf_conditions i /\ ~(satisfies i g))
let theorem_rdf_conditions_nontrivially_satisfiable () =
  lemma_separating_rdf_conditions ();
  lemma_separating_rejects ()

// -------------------------------------------------------------------
// COROLLARY. `rdfs_entails` and `rdf_entails` are PROPER relations --
// they do not hold of every pair of graphs. This is the statement the
// soundness theorems of RDF.Entailment.RDFS.ModelTheory need in order
// to carry content.
// -------------------------------------------------------------------
val theorem_rdfs_entails_not_everything (dd : datatype_set)
  : Lemma (~(rdfs_entails dd [] unsat_graph))
let theorem_rdfs_entails_not_everything dd =
  lemma_separating_rdfs_conditions dd;
  lemma_separating_rejects ();
  lemma_everything_satisfies_empty separating_interp

val theorem_rdf_entails_not_everything (_ : unit)
  : Lemma (~(rdf_entails [] unsat_graph))
let theorem_rdf_entails_not_everything () =
  lemma_separating_rdf_conditions ();
  lemma_separating_rejects ();
  lemma_everything_satisfies_empty separating_interp

// -------------------------------------------------------------------
// The same for the OWL 2 RL pilot bundle of OWL.Semantics.
//
// `separating_interp` does NOT work here: `cond_sameas_identity` is an
// iff, and `sep_iext true false true` holds while `false == true` does
// not. The pilot needs its own shape -- IEXT of the resource
// `owl:sameAs` denotes is exactly the diagonal, every other resource
// relates everything -- which in turn needs `owl:sameAs` to denote
// something no other vocabulary IRI denotes. That is the only place in
// this module where two IRIs have to be told apart.
// -------------------------------------------------------------------
let owl_sep_iext (p x y : bool) : prop = if p then True else x == y

let owl_separating_interp : interp = {
  idom     = bool;
  idom_wit = true;
  i_iri    = (fun (a : wf_iri) -> a <> OwlC.owl_sameAs);
  i_lit    = (fun _ -> true);
  i_tt     = (fun _ _ _ -> true);
  iext     = owl_sep_iext;
}

let owl_unsat_triple : triple =
  { s = S_IRI ex_iri; p = OwlC.owl_sameAs; o = T_IRI OwlC.owl_sameAs }
let owl_unsat_graph : rdf_graph = [ owl_unsat_triple ]

#push-options "--z3rlimit 40"
let lemma_owl_separating_conditions ()
  : Lemma (owl_rl_pilot_conditions owl_separating_interp) = ()

let lemma_owl_separating_rejects ()
  : Lemma (~(satisfies owl_separating_interp owl_unsat_graph)) =
  introduce forall (a : bnode_assignment owl_separating_interp.idom).
      ~(holds_all owl_separating_interp a owl_unsat_graph)
  with begin
    assert (memP owl_unsat_triple owl_unsat_graph);
    assert (~(triple_holds owl_separating_interp a owl_unsat_triple))
  end
#pop-options

val theorem_owl_rl_pilot_conditions_nontrivially_satisfiable (_ : unit)
  : Lemma (exists (i : interp) (g : rdf_graph).
             owl_rl_pilot_conditions i /\ ~(satisfies i g))
let theorem_owl_rl_pilot_conditions_nontrivially_satisfiable () =
  lemma_owl_separating_conditions ();
  lemma_owl_separating_rejects ()

val theorem_pilot_entails_not_everything (_ : unit)
  : Lemma (~(pilot_entails [] owl_unsat_graph))
let theorem_pilot_entails_not_everything () =
  lemma_owl_separating_conditions ();
  lemma_owl_separating_rejects ();
  lemma_everything_satisfies_empty owl_separating_interp

// ===================================================================
// 3. THE DATA-SIDE RESTRICTION PREDICATES.
//
// Each of these is a `requires` on a shipping-function refinement
// theorem. Each witness below is non-degenerate: a non-empty graph, a
// non-empty binding, a non-empty solution mapping, and -- for
// `ptrm_exact` -- the PT_Literal constructor, i.e. the only one of the
// five for which the predicate says anything at all.
// ===================================================================

// -------------------------------------------------------------------
// 3a. lit_exact / term_exact / triple_exact / graph_exact
// (RDF.Entailment.Simple.Spec). The fragment on which the shipping
// `literal_eq` coincides with RDF literal TERM equality.
// -------------------------------------------------------------------

let exact_triple : triple = { s = S_IRI ex_iri; p = ex_iri; o = T_Literal ex_lit }
let exact_graph : rdf_graph = [ exact_triple ]

val theorem_graph_exact_witness (_ : unit)
  : Lemma (lit_exact ex_lit /\ term_exact (T_Literal ex_lit) /\
           triple_exact exact_triple /\ graph_exact exact_graph /\
           Cons? exact_graph)
let theorem_graph_exact_witness () = ()

// The fragment is a real restriction, not a tautology: an
// rdf:XMLLiteral-typed literal is outside it. `graph_exact` therefore
// discriminates, which is what makes it worth carrying as a
// hypothesis (and is the syntactic side of finding SE-1).
let xml_lit : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "<a></a>"; datatype = rdf_XMLLiteral;
                             lang_tag = None; direction = None }));
  { lexical_form = "<a></a>"; datatype = rdf_XMLLiteral;
    lang_tag = None; direction = None }

let inexact_graph : rdf_graph =
  [ { s = S_IRI ex_iri; p = ex_iri; o = T_Literal xml_lit } ]

val theorem_graph_exact_not_universal (_ : unit)
  : Lemma (~(graph_exact inexact_graph))
let theorem_graph_exact_not_universal () =
  assert (memP (List.Tot.hd inexact_graph) inexact_graph)

// -------------------------------------------------------------------
// 3b. binding_exact / leq_reflexive / leq_exact_identity / bnd_total
// (RDF.Entailment.Simple.Refinement).
//
// The two predicate-parameter hypotheses are witnessed by the SHIPPING
// instantiation, not by an invented function: `simple_leq` is the
// literal test `simple_entails` actually passes to `entails_with`, and
// RDF.Entailment.Simple.Refinement already proves both properties of
// it. Recording the existential here puts the witness where a vacuity
// audit will find it.
// -------------------------------------------------------------------

let exact_binding : RDF.Entailment.Simple.binding = [ ("b0", T_IRI ex_iri) ]

val theorem_binding_exact_witness (_ : unit)
  : Lemma (SimpleRef.binding_exact exact_binding /\ Cons? exact_binding)
let theorem_binding_exact_witness () = ()

val theorem_leq_hypotheses_satisfiable (_ : unit)
  : Lemma (exists (leq : bool -> literal -> literal -> bool).
             SimpleRef.leq_reflexive leq /\ SimpleRef.leq_exact_identity leq)
let theorem_leq_hypotheses_satisfiable () =
  introduce exists (leq : bool -> literal -> literal -> bool).
      SimpleRef.leq_reflexive leq /\ SimpleRef.leq_exact_identity leq
  with SimpleRef.simple_leq
  and  (SimpleRef.lemma_simple_leq_reflexive ();
        SimpleRef.lemma_simple_leq_exact_identity ())

val theorem_bnd_total_satisfiable (_ : unit)
  : Lemma (exists (bnd : rdf_term -> bool). SimpleRef.bnd_total bnd)
let theorem_bnd_total_satisfiable () =
  introduce exists (bnd : rdf_term -> bool). SimpleRef.bnd_total bnd
  with SimpleRef.simple_bnd
  and  SimpleRef.lemma_simple_bnd_total ()

// -------------------------------------------------------------------
// 3c. smap_exact / seq_exact / ptrm_exact
// (SPARQL11.Algebra.Refinement). Same fragment, reached from the
// SPARQL side.
// -------------------------------------------------------------------

let exact_smap : AlgSpec.smap = [ ("x", T_IRI ex_iri); ("y", T_Literal ex_lit) ]
let exact_seq : list AlgSpec.smap = [ exact_smap ]
let exact_ptrm : Alg.pattern_term = Alg.PT_Literal ex_lit

val theorem_smap_exact_witness (_ : unit)
  : Lemma (AlgRef.smap_exact exact_smap /\ Cons? exact_smap /\
           AlgRef.seq_exact exact_seq /\ Cons? exact_seq /\
           AlgRef.ptrm_exact exact_ptrm /\ Alg.PT_Literal? exact_ptrm)
let theorem_smap_exact_witness () = ()

// ===================================================================
// 4. THE INDEX HYPOTHESES -- one witness, one GAP.
//
// `ig_wf_pred` and `ig_wf_sp` (OWL.Semantics) are the two index
// well-formedness props the RDFS rule refinement theorems restrict on.
// They are not symmetric, and the asymmetry is the whole content of
// this part.
// ===================================================================

// -------------------------------------------------------------------
// 4a. ig_wf_pred: non-degenerate witness.
//
// The predicate bucket's key IS the predicate, so no key decomposition
// is involved. The index below serves a real triple under a real key
// -- the second conjunct is what makes the witness non-degenerate,
// since `ig_wf_pred` of an index with no buckets holds for the wrong
// reason.
// -------------------------------------------------------------------
let index_triple : triple = { s = S_IRI ex_iri; p = ex_iri; o = T_IRI ex_iri }

let wf_pred_index : indexed_graph = {
  ig_triples = [ index_triple ];
  ig_pred    = BNode ex_iri [ index_triple ] BLeaf BLeaf;
  ig_subj    = BLeaf;
  ig_obj     = BLeaf;
  ig_sp      = BLeaf;
  ig_po      = BLeaf;
  ig_so      = BLeaf;
  ig_built   = all_bucket_needs;
}

val theorem_ig_wf_pred_witness (_ : unit)
  : Lemma (ig_wf_pred wf_pred_index /\
           memP index_triple (bucket_lookup wf_pred_index.ig_pred ex_iri))
let theorem_ig_wf_pred_witness () = ()

// -------------------------------------------------------------------
// 4b. ig_wf_sp: the hypothesis is a REAL restriction.
//
// An index whose sp-bucket files a triple under the composite key of a
// DIFFERENT subject falsifies it. So the hypothesis is not a tautology
// dressed up as a side condition -- the theorems that carry it are
// genuinely narrowed by it.
// -------------------------------------------------------------------
let mismatched_subject : subject = S_BNode "b0"

let bad_sp_index : indexed_graph = {
  ig_triples = [ index_triple ];
  ig_pred    = BLeaf;
  ig_subj    = BLeaf;
  ig_obj     = BLeaf;
  ig_sp      = BNode (sp_key mismatched_subject ex_iri) [ index_triple ] BLeaf BLeaf;
  ig_po      = BLeaf;
  ig_so      = BLeaf;
  ig_built   = all_bucket_needs;
}

val theorem_ig_wf_sp_not_universal (_ : unit)
  : Lemma (~(ig_wf_sp bad_sp_index))
let theorem_ig_wf_sp_not_universal () =
  assert (memP index_triple
                (bucket_lookup bad_sp_index.ig_sp (sp_key mismatched_subject ex_iri)));
  assert (index_triple.s =!= mismatched_subject)

// -------------------------------------------------------------------
// 4c. ig_wf_sp: satisfiable, but only DEGENERATELY. An open obligation.
//
// The witness below has a non-empty graph and an EMPTY sp-bucket, so
// `ig_wf_sp` holds because the bucket serves nothing. That is exactly
// the shape this module exists to reject, and it is labelled as such.
//
// A non-degenerate witness -- an sp-bucket that serves a triple, under
// a key that determines its subject and predicate -- needs `sp_key`
// INJECTIVITY, and `sp_key` is not injective. The tree's finding F1
// blames blank-node labels containing U+001F; the theorem below
// sharpens that. `is_iri` (RDF.Term.fsti) asks only for "non-empty and
// contains a colon", so an IRI may itself contain U+001F, and two
// DIFFERENT subject/predicate pairs -- both with IRI subjects, no
// blank node anywhere -- produce the SAME composite key.
//
// Consequence, stated plainly: this module does not establish that
// `ig_wf_sp (build_indexed g)` holds for any non-empty g, and so does
// not establish that `rdfs_closure_step_sound` / `rdfs_closure_sound` /
// `rdfs_closure_entails` have any non-empty instance. The follow-up is
// in docs/designissues/2026-07-30-hypothesis-satisfiability.md.
// -------------------------------------------------------------------
let degenerate_sp_index : indexed_graph = {
  ig_triples = [ index_triple ];
  ig_pred    = BLeaf;
  ig_subj    = BLeaf;
  ig_obj     = BLeaf;
  ig_sp      = BLeaf;
  ig_po      = BLeaf;
  ig_so      = BLeaf;
  ig_built   = all_bucket_needs;
}

val theorem_ig_wf_sp_satisfiable_degenerately (_ : unit)
  : Lemma (ig_wf_sp degenerate_sp_index /\ Cons? degenerate_sp_index.ig_triples /\
           bucket_lookup degenerate_sp_index.ig_sp (sp_key (S_IRI ex_iri) ex_iri) == [])
let theorem_ig_wf_sp_satisfiable_degenerately () = ()

// The composite key is not injective, on IRI subjects alone.
//   subject_to_key (S_IRI "a:")      = "I_a:"
//   sp_key (S_IRI "a:") "b:<US>c:"   = "I_a:" <US> "b:" <US> "c:"
//   subject_to_key (S_IRI "a:<US>b:") = "I_a:" <US> "b:"
//   sp_key (S_IRI "a:<US>b:") "c:"   = "I_a:" <US> "b:" <US> "c:"
// where <US> is U+001F. Both IRIs clear `is_iri`.
let clash_iri_a : wf_iri = assert_norm (is_iri "a:"); "a:"
let clash_iri_ab : wf_iri = assert_norm (is_iri "a:\x1fb:"); "a:\x1fb:"
let clash_iri_bc : wf_iri = assert_norm (is_iri "b:\x1fc:"); "b:\x1fc:"
let clash_iri_c : wf_iri = assert_norm (is_iri "c:"); "c:"

val theorem_sp_key_not_injective (_ : unit)
  : Lemma (sp_key (S_IRI clash_iri_a) clash_iri_bc ==
           sp_key (S_IRI clash_iri_ab) clash_iri_c /\
           S_IRI clash_iri_a =!= S_IRI clash_iri_ab /\
           clash_iri_bc =!= clash_iri_c)
let theorem_sp_key_not_injective () =
  assert_norm (sp_key (S_IRI clash_iri_a) clash_iri_bc ==
               sp_key (S_IRI clash_iri_ab) clash_iri_c);
  assert_norm (clash_iri_a =!= clash_iri_ab);
  assert_norm (clash_iri_bc =!= clash_iri_c)

// -------------------------------------------------------------------
// 4d. closure_chain_wf: NO witness, not even the degenerate one.
//
// `closure_chain_wf g = forall (n : nat). ig_wf_sp (build_indexed
// (closure_iter g n))` is the hypothesis of
// RDF.Entailment.RDFS.ModelTheory's `rdfs_closure_sound` and of its
// headline corollary `rdfs_closure_entails`.
//
// The n = 0 conjunct is discharged for the empty graph
// (`lemma_ig_wf_sp_of_empty` below: `build_indexed []` files nothing,
// so `bucket_lookup` serves nothing). The chain does NOT stay there.
// `rdfs_rule_container_membership` emits its ten rdf:_1 .. rdf:_5 rows
// unconditionally, with no premise read from the data, so
// `rdfs_closure_step []` is NON-EMPTY -- machine-checked below. At
// n = 1 the sp-bucket is populated and the argument of 4c applies.
//
// `build_indexed` files EVERY triple into `ig_sp` (`bucket_key_sp t`
// is `Some (sp_key t.s t.p)` for every t, never `None`), so an empty
// sp-bucket means an empty graph, and the empty graph leaves the
// chain after one step. There is therefore no graph at all for which
// this module can discharge `closure_chain_wf`.
//
// STATED PLAINLY, because it is the finding of this commit:
// `rdfs_closure_sound` and `rdfs_closure_entails` are SATISFIABLE in
// the mathematical sense -- any graph whose blank-node labels and IRIs
// avoid U+001F has a clean chain -- but this tree contains no
// machine-checked instance of either, so neither is known to apply to
// any graph whatsoever. Closing it means proving `sp_key` injective on
// U+001F-free keys, which needs a char-list argument over
// `FStar.String.list_of_concat`. Follow-up list in
// docs/designissues/2026-07-30-hypothesis-satisfiability.md.
// -------------------------------------------------------------------
let lemma_ig_wf_sp_of_empty ()
  : Lemma (ig_wf_sp (build_indexed [])) =
  OWL.Semantics.MemLemmas.lemma_build_indexed_wf_sp_weak []

val theorem_closure_chain_wf_n0_of_empty (_ : unit)
  : Lemma (ig_wf_sp (build_indexed (closure_iter [] 0)))
let theorem_closure_chain_wf_n0_of_empty () = lemma_ig_wf_sp_of_empty ()

// ... and the chain leaves the empty graph immediately, so the n = 0
// conjunct is all of `closure_chain_wf []` that is in reach.
val theorem_closure_step_of_empty_is_nonempty (_ : unit)
  : Lemma (Cons? (rdfs_closure_step []) /\ Cons? (closure_iter [] 1))
let theorem_closure_step_of_empty_is_nonempty () =
  assert_norm (Cons? (rdfs_closure_step []))

// ===================================================================
// 5. WHAT THIS MODULE DOES NOT ESTABLISH
//
// * A non-degenerate witness for `ig_wf_sp` or `closure_chain_wf`.
//   See 4c. This is the one open obligation.
// * COMPLETENESS of any bundle. Part 2 shows `rdfs_entails` is a
//   proper relation; it does not show it is the RIGHT relation. That
//   is the phase-2 embedding obligation the simple and RDFS rungs both
//   record: `OWL.Semantics.interp` is a SUPERSET of the genuine W3C
//   interpretation class, which is the sound direction and the wrong
//   direction for completeness.
// * That the separating models are RDFS interpretations in the W3C
//   sense. They meet the conditions this tree transcribes, which is
//   the entire content of `rdfs_conditions`, and nothing more is
//   claimed.
// ===================================================================
