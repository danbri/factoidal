module RDF.Entailment.Simple.ModelTheory

// ===================================================================
// THE INTERPOLATION LEMMA, machine-checked.
//
// RDF.Entailment.Simple.Spec.fst states the SYNTACTIC characterisation
// of simple entailment ("a subgraph of A is an instance of B"). That
// is the right-hand side of the interpolation lemma, not the
// definition. The DEFINITION is model-theoretic (RDF 1.1 Semantics,
// W3C Rec 25 February 2014, section 5.2, verbatim):
//
//   "A graph G simply entails a graph E when every interpretation
//    which satisfies G also satisfies E."
//
// and the lemma that connects them (section 5.3, verbatim):
//
//   "G simply entails a graph E if and only if a subgraph of G is an
//    instance of E."
//
// This module proves that "if and only if" rather than assuming it, so
// nothing in the vertical rests on the syntactic characterisation
// being taken on faith. Composed with
// RDF.Entailment.Simple.Refinement.fst, the result is:
//
//   simple_entails a b = true   <==>   every interpretation that
//                                      satisfies a satisfies b
//
// (`simple_entails_iff_model_theory`, bottom of this file) -- the
// shipping boolean against the model-theoretic definition, with the
// side conditions named.
//
// -------------------------------------------------------------------
// REUSE, not re-derivation
// -------------------------------------------------------------------
// The interpretation machinery is `OWL.Semantics.interp` /
// `denot_subject` / `denot_term` / `holds_all` / `satisfies` from the
// 2026-07-29 RDF-Based-semantics pilot
// (docs/designissues/2026-07-29-rdf-based-semantics-formalization.md).
// Nothing is redefined here. That module's banner records the shape
// decisions; the two that matter for this file are repeated:
//
//   * `interp` is a SUPERSET of the genuine simple interpretations
//     (IEXT totalized over the domain instead of typed on IP, IL
//     totalized, only the if-halves of iff conditions). For the EASY
//     direction (`interpolation_sound`) that makes the theorem
//     STRONGER: entailment over a larger class implies entailment over
//     the smaller one. For the HARD direction (`interpolation_
//     complete`) the direction of the inclusion is the wrong way
//     round, so that theorem does not follow for free -- see
//     "Scope of the hard direction" below.
//   * blank nodes are existential over a TOTAL assignment, which is
//     Hayes' "mapping A from the set of blank nodes in E to IR"
//     extended by the domain's inhabitant.
//
// -------------------------------------------------------------------
// Scope of the hard direction
// -------------------------------------------------------------------
// `interpolation_complete` is proved by exhibiting a countermodel: the
// HERBRAND interpretation of A, whose domain is the set of RDF terms
// and whose IEXT is read straight off A's triples. The theorem as
// stated quantifies over `OWL.Semantics.interp`, the superset class.
// To transfer it to the genuine W3C class one needs `herbrand a` to be
// a genuine simple interpretation, which it is -- take IR = the RDF
// terms, IP = IR, IEXT(p) = { <x,y> | some triple of A reads
// <p-as-IRI, x, y> }, IS(iri) = the IRI term, IL(lit) = the literal
// term; every clause of RDF 1.1 Semantics section 5's definition is
// satisfied, IR is nonempty, and IL may be total because a partial
// mapping is allowed to be total. That last step is an argument about
// the W3C text, not a machine-checked fact: formalizing the genuine
// class and proving the embedding is the pilot's phase-2 obligation
// (design doc section "External review 2026-07-29", item 1). The
// countermodel is given here explicitly and in ten lines precisely so
// that the remaining step is checkable by inspection.
//
// -------------------------------------------------------------------
// RDF 1.2 QUARANTINE
// -------------------------------------------------------------------
// `T_TripleTerm` has no denotation in either baseline's model theory
// (Hayes 2004; RDF 1.1 Semantics 2014). `OWL.Semantics.interp` gives
// it an uninterpreted compositional constructor `i_tt` so that
// `denot_term` stays total. Consequences, honestly:
//   * `interpolation_sound` (easy direction) holds for ALL graphs,
//     triple terms included: it only needs `i_tt` to be a function of
//     the component denotations, which it is by construction.
//   * `interpolation_complete` (hard direction) carries a
//     `graph_tt_free` hypothesis on BOTH graphs. The Herbrand
//     construction cannot reconstruct a triple term from an arbitrary
//     assignment's images (a blank node may be assigned a literal,
//     which is not a legal triple-term subject), so the countermodel
//     argument does not go through for triple terms. This is the
//     mandated quarantine, and it is a real restriction, not a
//     formality.
// The SYNTACTIC results (soundness and completeness of the shipping
// search against `simple_entailment_spec`, in
// RDF.Entailment.Simple.Refinement.fst) have no such restriction.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open OWL.Semantics
open RDF.Entailment.Simple
open RDF.Entailment.Simple.Spec
open RDF.Entailment.Simple.Refinement

// ===================================================================
// 0. The model-theoretic DEFINITION of simple entailment.
// ===================================================================

let simple_entails_mt (a b : list triple) : prop =
  forall (i : interp). satisfies i a ==> satisfies i b

// `subj_term` (Spec) and `subject_to_term` (RDF.Graph, which
// OWL.Semantics' lemmas are stated over) are the same function.
let lemma_subj_term_is_subject_to_term (s : subject)
  : Lemma (subj_term s == subject_to_term s) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

let lemma_subj_term_injective (s1 s2 : subject)
  : Lemma (requires subj_term s1 == subj_term s2) (ensures s1 == s2) =
  match s1, s2 with
  | S_IRI _, S_IRI _ -> ()
  | S_BNode _, S_BNode _ -> ()
  | _, _ -> ()

// ===================================================================
// 1. EASY DIRECTION: an instance-subgraph witness yields, for every
// interpretation satisfying A, an assignment satisfying B.
//
// The construction is the composite assignment
//   a_b (l) = [I + a_a] (M l)
// -- interpret B's blank node l by interpreting the term M sent it to.
// The two lemmas below are the substitution lemma for that composite,
// one per syntactic position.
// ===================================================================

let composed_assignment (i : interp) (aa : bnode_assignment i.idom) (m : bnode_subst)
  : bnode_assignment i.idom =
  fun l -> denot_term i aa (m l)

let lemma_subst_denot_subj (i : interp) (aa : bnode_assignment i.idom)
                           (m : bnode_subst) (ps : subject) (gs : subject)
  : Lemma (requires subj_inst m ps gs)
          (ensures denot_subject i (composed_assignment i aa m) ps ==
                   denot_subject i aa gs) =
  match ps with
  | S_IRI _ -> ()
  | S_BNode b ->
    lemma_subj_term_is_subject_to_term gs;
    lemma_denot_subject_to_term i aa gs

let rec lemma_subst_denot_term (i : interp) (aa : bnode_assignment i.idom)
                               (m : bnode_subst) (pat : rdf_term) (g : rdf_term)
  : Lemma (requires term_inst m pat g)
          (ensures denot_term i (composed_assignment i aa m) pat == denot_term i aa g)
          (decreases pat) =
  match pat with
  | T_BNode _   -> ()
  | T_IRI _     -> ()
  | T_Literal _ -> ()
  | T_TripleTerm ps pp po ->
    eliminate exists (gs : subject) (go : rdf_term).
        g == T_TripleTerm gs pp go /\ subj_inst m ps gs /\ term_inst m po go
    returns (denot_term i (composed_assignment i aa m) pat == denot_term i aa g)
    with _pf.
      (lemma_subst_denot_subj i aa m ps gs;
       lemma_subst_denot_term i aa m po go)

let lemma_subst_triple_holds (i : interp) (aa : bnode_assignment i.idom)
                             (m : bnode_subst) (tb : triple) (ta : triple)
  : Lemma (requires triple_inst m tb ta /\ triple_holds i aa ta)
          (ensures triple_holds i (composed_assignment i aa m) tb) =
  lemma_subst_denot_subj i aa m tb.s ta.s;
  lemma_subst_denot_term i aa m tb.o ta.o

// -------------------------------------------------------------------
// THEOREM (interpolation, easy direction / soundness of the syntactic
// characterisation). Holds for ALL graphs -- triple terms included.
// -------------------------------------------------------------------
let interpolation_sound (a b : list triple)
  : Lemma (requires simple_entailment_spec a b)
          (ensures  simple_entails_mt a b) =
  let step (i : interp)
    : Lemma (requires satisfies i a) (ensures satisfies i b) =
    eliminate exists (m : bnode_subst).
        (forall (tb : triple). memP tb b ==>
           (exists (ta : triple). memP ta a /\ triple_inst m tb ta))
    returns (satisfies i b)
    with _pm.
      (eliminate exists (aa : bnode_assignment i.idom). holds_all i aa a
       returns (satisfies i b)
       with _pa.
         (let ab = composed_assignment i aa m in
          let per_triple (tb : triple)
            : Lemma (requires memP tb b) (ensures triple_holds i ab tb) =
            eliminate exists (ta : triple). memP ta a /\ triple_inst m tb ta
            returns (triple_holds i ab tb)
            with _pt. lemma_subst_triple_holds i aa m tb ta
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple);
          assert (holds_all i ab b)))
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires step)

// ===================================================================
// 2. HARD DIRECTION: the Herbrand interpretation of A.
//
// Domain = the RDF terms. Each IRI and literal denotes itself; a
// triple <s,p,o> of A puts <s-as-term, o> into IEXT(p-as-term). Under
// this interpretation "true" means "literally a triple of A", so an
// assignment satisfying B IS a witnessing substitution -- the
// existential blank-node semantics and the instance condition become
// the same statement.
//
// `i_tt` is the quarantine point: it is given an arbitrary constant
// value, which is why both graphs must be `graph_tt_free`.
// ===================================================================

let herb_iext (a : list triple) (p x y : rdf_term) : prop =
  exists (t : triple). memP t a /\ p == T_IRI t.p /\ x == subj_term t.s /\ y == t.o

let herbrand (a : list triple) : interp = {
  idom     = rdf_term;
  idom_wit = T_BNode "";
  i_iri    = (fun (x : wf_iri) -> T_IRI x);
  i_lit    = (fun (l : wf_literal) -> T_Literal l);
  i_tt     = (fun _ _ _ -> T_BNode "");
  iext     = herb_iext a;
}

// The identity assignment: every blank node denotes itself.
let herb_id_assignment (a : list triple) : bnode_assignment (herbrand a).idom =
  fun (l : bnode_id) -> T_BNode l

let lemma_herb_denot_subj_id (a : list triple) (s : subject)
  : Lemma (denot_subject (herbrand a) (herb_id_assignment a) s == subj_term s) =
  match s with
  | S_IRI _ -> ()
  | S_BNode _ -> ()

let lemma_herb_denot_term_id (a : list triple) (t : rdf_term)
  : Lemma (requires term_tt_free t)
          (ensures denot_term (herbrand a) (herb_id_assignment a) t == t)
 =
  match t with
  | T_IRI _     -> ()
  | T_BNode _   -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// A simply satisfies itself under its own Herbrand interpretation.
let lemma_herbrand_satisfies (a : list triple)
  : Lemma (requires graph_tt_free a) (ensures satisfies (herbrand a) a) =
  let ai = herb_id_assignment a in
  let per_triple (t : triple)
    : Lemma (requires memP t a) (ensures triple_holds (herbrand a) ai t) =
    lemma_herb_denot_subj_id a t.s;
    lemma_herb_denot_term_id a t.o;
    assert (herb_iext a (T_IRI t.p) (subj_term t.s) t.o)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple);
  assert (holds_all (herbrand a) ai a)

// Under the Herbrand interpretation, denotation IS substitution: an
// assignment read as a `bnode_subst` relates a pattern term to its own
// denotation exactly as `term_inst` demands.
let lemma_herb_denot_is_subj_inst (a : list triple)
                                  (ab : bnode_assignment (herbrand a).idom)
                                  (ps : subject) (gs : subject)
  : Lemma (requires denot_subject (herbrand a) ab ps == subj_term gs)
          (ensures  subj_inst ab ps gs) =
  match ps with
  | S_IRI i -> lemma_subj_term_injective (S_IRI i) gs
  | S_BNode _ -> ()

let lemma_herb_denot_is_term_inst (a : list triple)
                                      (ab : bnode_assignment (herbrand a).idom)
                                      (pat : rdf_term) (g : rdf_term)
  : Lemma (requires term_tt_free pat /\ denot_term (herbrand a) ab pat == g)
          (ensures  term_inst ab pat g) =
  match pat with
  | T_BNode _   -> ()
  | T_IRI _     -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// If the Herbrand interpretation of A satisfies B, the witnessing
// assignment IS an instance-subgraph witness.
let lemma_herbrand_reflects (a b : list triple)
  : Lemma (requires satisfies (herbrand a) b /\ graph_tt_free b)
          (ensures  simple_entailment_spec a b) =
  eliminate exists (ab : bnode_assignment (herbrand a).idom). holds_all (herbrand a) ab b
  returns (simple_entailment_spec a b)
  with _pb.
    (let m : bnode_subst = ab in
     let per_triple (tb : triple)
       : Lemma (requires memP tb b)
               (ensures (exists (ta : triple). memP ta a /\ triple_inst m tb ta)) =
       assert (triple_holds (herbrand a) ab tb);
       assert (herb_iext a (T_IRI tb.p)
                         (denot_subject (herbrand a) ab tb.s)
                         (denot_term (herbrand a) ab tb.o));
       eliminate exists (t : triple).
           memP t a /\ T_IRI tb.p == T_IRI t.p /\
           denot_subject (herbrand a) ab tb.s == subj_term t.s /\
           denot_term (herbrand a) ab tb.o == t.o
       returns (exists (ta : triple). memP ta a /\ triple_inst m tb ta)
       with _pt.
         (lemma_herb_denot_is_subj_inst a ab tb.s t.s;
          lemma_herb_denot_is_term_inst a ab tb.o t.o;
          assert (memP t a /\ triple_inst m tb t))
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple);
     assert (forall (tb : triple). memP tb b ==>
               (exists (ta : triple). memP ta a /\ triple_inst m tb ta));
     introduce exists (mm : bnode_subst).
         (forall (tb : triple). memP tb b ==>
            (exists (ta : triple). memP ta a /\ triple_inst mm tb ta))
     with m
     and ())

// -------------------------------------------------------------------
// THEOREM (interpolation, hard direction). Triple-term-free graphs.
// -------------------------------------------------------------------
let interpolation_complete (a b : list triple)
  : Lemma (requires simple_entails_mt a b /\ graph_tt_free a /\ graph_tt_free b)
          (ensures  simple_entailment_spec a b) =
  lemma_herbrand_satisfies a;
  assert (satisfies (herbrand a) b);
  lemma_herbrand_reflects a b

// ===================================================================
// THEOREM (the interpolation lemma of RDF 1.1 Semantics section 5.3).
// ===================================================================
let interpolation_lemma (a b : list triple)
  : Lemma (requires graph_tt_free a /\ graph_tt_free b)
          (ensures  simple_entailment_spec a b <==> simple_entails_mt a b) =
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> interpolation_sound x y) a b;
  FStar.Classical.move_requires_2
    (fun (x : list triple) (y : list triple) -> interpolation_complete x y) a b

// ===================================================================
// THE VERTICAL, END TO END.
//
// The shipping boolean decides the model-theoretic definition of
// simple entailment. Both side conditions are named in the `requires`
// and neither is decoration:
//   * graph_exact  -- outside it the shipping literal test is coarser
//     than RDF literal term equality; `simple_entails_not_sound_
//     unconditionally` (Refinement) is the witness.
//   * graph_tt_free -- RDF 1.2 triple terms have no model theory in
//     either baseline; this is the mandated quarantine.
// ===================================================================
let simple_entails_iff_model_theory (a b : list triple)
  : Lemma (requires graph_exact a /\ graph_exact b /\
                    graph_tt_free a /\ graph_tt_free b)
          (ensures  (simple_entails a b == true) <==> simple_entails_mt a b) =
  simple_entails_iff_spec a b;
  interpolation_lemma a b

// ===================================================================
// ADOPTION ITEM A5 (docs/designissues/2026-08-05-semantics-proposal-
// adoption.md): two more small semantic-layer lemmas, built directly
// on the `interp` / `bnode_assignment` / `satisfies` machinery reused
// above.
//   5a. `graph_bnodes_complete` -- satisfaction of a graph under a
//       fixed assignment depends on that assignment only through its
//       restriction to the graph's own blank-node labels.
//   5b. the RDF 1.1 Semantics section 5.2 MERGING lemma -- the
//       bnode-disjoint union form, plus the two-graph entailment
//       corollary the REC states.
// ===================================================================

// -------------------------------------------------------------------
// 5.0 Blank-node labels occurring in a term / triple / graph.
//
// A fresh, LOCAL enumeration -- not `RDF.Graph.Executable.graph_bnodes`,
// which lives in the pragmatics/executable layer this file
// deliberately does not open (that module `include`s `RDFS.Closure`
// and `OWL.Closure`, dragging in the whole engine for one list
// function). This one also differs in a way worth flagging: it
// recurses into RDF 1.2 triple-term subjects, matching `denot_term`'s
// own recursion (`OWL.Semantics.denot_term`), so the completeness
// theorem below is not restricted to `graph_tt_free` graphs.
// `RDF.Graph.Executable.graph_bnodes` inspects only a triple's
// top-level `s` and `o` fields and therefore MISSES a blank node
// nested inside a `T_TripleTerm` object -- a pre-existing gap in that
// function, flagged here rather than fixed there (out of scope for
// this lemma; every caller of that function today runs RDF 1.0/1.1
// pipelines that never construct triple terms).
// -------------------------------------------------------------------
let subject_bnode (s : subject) : list bnode_id =
  match s with
  | S_IRI _   -> []
  | S_BNode b -> [b]

let rec term_bnodes (t : rdf_term) : Tot (list bnode_id) (decreases t) =
  match t with
  | T_IRI _            -> []
  | T_BNode b          -> [b]
  | T_Literal _        -> []
  | T_TripleTerm s _ o -> subject_bnode s @ term_bnodes o

let triple_bnodes (t : triple) : list bnode_id =
  subject_bnode t.s @ term_bnodes t.o

let rec graph_bnode_ids (g : list triple) : Tot (list bnode_id) (decreases g) =
  match g with
  | []       -> []
  | hd :: tl -> triple_bnodes hd @ graph_bnode_ids tl

// The occurrence predicate the enumeration above is checked against --
// structurally independent of the list-building recursion above, so
// the membership-correctness lemmas below are a genuine correspondence
// proof and not a restatement of the same computation.
let subject_has_bnode (s : subject) (b : bnode_id) : prop =
  match s with
  | S_IRI _    -> False
  | S_BNode b' -> b' == b

let rec term_has_bnode (t : rdf_term) (b : bnode_id) : Tot prop (decreases t) =
  match t with
  | T_IRI _            -> False
  | T_BNode b'         -> b' == b
  | T_Literal _        -> False
  | T_TripleTerm s _ o -> subject_has_bnode s b \/ term_has_bnode o b

let triple_has_bnode (t : triple) (b : bnode_id) : prop =
  subject_has_bnode t.s b \/ term_has_bnode t.o b

let rec graph_has_bnode (g : list triple) (b : bnode_id) : Tot prop (decreases g) =
  match g with
  | []       -> False
  | hd :: tl -> triple_has_bnode hd b \/ graph_has_bnode tl b

// Membership correctness: "b is in the enumeration" iff "b occurs in
// the graph".
let lemma_subject_bnode_mem (s : subject) (b : bnode_id)
  : Lemma (memP b (subject_bnode s) <==> subject_has_bnode s b) =
  match s with
  | S_IRI _   -> ()
  | S_BNode _ -> ()

let rec lemma_term_bnodes_mem (t : rdf_term) (b : bnode_id)
  : Lemma (ensures memP b (term_bnodes t) <==> term_has_bnode t b)
          (decreases t) =
  match t with
  | T_IRI _     -> ()
  | T_BNode _   -> ()
  | T_Literal _ -> ()
  | T_TripleTerm s _ o ->
    lemma_subject_bnode_mem s b;
    lemma_term_bnodes_mem o b;
    append_memP (subject_bnode s) (term_bnodes o) b

let lemma_triple_bnodes_mem (t : triple) (b : bnode_id)
  : Lemma (memP b (triple_bnodes t) <==> triple_has_bnode t b) =
  lemma_subject_bnode_mem t.s b;
  lemma_term_bnodes_mem t.o b;
  append_memP (subject_bnode t.s) (term_bnodes t.o) b

let rec lemma_graph_bnode_ids_mem (g : list triple) (b : bnode_id)
  : Lemma (ensures memP b (graph_bnode_ids g) <==> graph_has_bnode g b)
          (decreases g) =
  match g with
  | []       -> ()
  | hd :: tl ->
    lemma_triple_bnodes_mem hd b;
    lemma_graph_bnode_ids_mem tl b;
    append_memP (triple_bnodes hd) (graph_bnode_ids tl) b

// Monotonicity: every bnode of a member triple is a bnode of the
// whole graph. The graph-level completeness theorem needs this to
// transfer the graph-wide "assignments agree" hypothesis down to a
// single triple.
let rec lemma_mem_triple_bnodes_subset (g : list triple) (t : triple) (b : bnode_id)
  : Lemma (requires memP t g /\ triple_has_bnode t b)
          (ensures  graph_has_bnode g b)
          (decreases g) =
  match g with
  | [] -> ()
  | hd :: tl ->
    eliminate (t == hd) \/ memP t tl
    returns graph_has_bnode g b
    with _ . ()
    and  _ . lemma_mem_triple_bnodes_subset tl t b

// -------------------------------------------------------------------
// 5a. graph_bnodes_complete: two assignments agreeing on every bnode
// label of a graph make that graph hold identically (same
// interpretation, fixed assignments -- no existential over
// assignments here; that is `satisfies`, one layer up).
//
// Proof shape: reduce to a per-triple denotation lemma
// (`lemma_denot_agree`) via structural induction matching
// `denot_subject`/`denot_term`, then lift from one triple to
// `holds_all` via the monotonicity lemma above.
// -------------------------------------------------------------------
let assignments_agree_on (i : interp) (bs : list bnode_id)
                         (a1 a2 : bnode_assignment i.idom) : prop =
  forall (b : bnode_id). memP b bs ==> a1 b == a2 b

let lemma_denot_subject_agree (i : interp) (a1 a2 : bnode_assignment i.idom) (s : subject)
  : Lemma (requires forall (b : bnode_id). subject_has_bnode s b ==> a1 b == a2 b)
          (ensures  denot_subject i a1 s == denot_subject i a2 s) =
  match s with
  | S_IRI _   -> ()
  | S_BNode _ -> ()

let rec lemma_denot_term_agree (i : interp) (a1 a2 : bnode_assignment i.idom) (t : rdf_term)
  : Lemma (requires forall (b : bnode_id). term_has_bnode t b ==> a1 b == a2 b)
          (ensures  denot_term i a1 t == denot_term i a2 t)
          (decreases t) =
  match t with
  | T_IRI _     -> ()
  | T_BNode _   -> ()
  | T_Literal _ -> ()
  | T_TripleTerm s _ o ->
    lemma_denot_subject_agree i a1 a2 s;
    lemma_denot_term_agree i a1 a2 o

let lemma_triple_holds_agree (i : interp) (a1 a2 : bnode_assignment i.idom) (t : triple)
  : Lemma (requires forall (b : bnode_id). triple_has_bnode t b ==> a1 b == a2 b)
          (ensures  triple_holds i a1 t <==> triple_holds i a2 t) =
  lemma_denot_subject_agree i a1 a2 t.s;
  lemma_denot_term_agree i a1 a2 t.o

let graph_bnodes_complete (i : interp) (a1 a2 : bnode_assignment i.idom) (g : list triple)
  : Lemma (requires assignments_agree_on i (graph_bnode_ids g) a1 a2)
          (ensures  holds_all i a1 g <==> holds_all i a2 g) =
  let per_triple (t : triple)
    : Lemma (requires memP t g) (ensures triple_holds i a1 t <==> triple_holds i a2 t) =
    let agree_on_t (b : bnode_id)
      : Lemma (requires triple_has_bnode t b) (ensures a1 b == a2 b) =
      lemma_mem_triple_bnodes_subset g t b;
      lemma_graph_bnode_ids_mem g b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires agree_on_t);
    lemma_triple_holds_agree i a1 a2 t
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires per_triple)

// -------------------------------------------------------------------
// 5b. The MERGING lemma, RDF 1.1 Semantics section 5.2 ("Merging
// graphs"): the union of two bnode-disjoint graphs behaves, under a
// fixed interpretation and assignment, exactly as the two graphs
// separately -- and, given disjointness, at the level of `satisfies`
// (existential over the assignment) too.
//
// The FIXED-ASSIGNMENT half needs no disjointness at all: `memP` over
// `@` splits into the two `memP`s regardless of what the bnode labels
// are, since both sides read the same assignment. Disjointness only
// starts to matter once the assignment is allowed to vary independently
// on each side, i.e. at the `satisfies` (existential) level -- which is
// exactly where the REC's own entailment corollary lives.
// -------------------------------------------------------------------
let lemma_holds_all_append (i : interp) (a : bnode_assignment i.idom) (g1 g2 : list triple)
  : Lemma (holds_all i a (g1 @ g2) <==> holds_all i a g1 /\ holds_all i a g2) =
  let step (t : triple)
    : Lemma (memP t (g1 @ g2) <==> memP t g1 \/ memP t g2) =
    append_memP g1 g2 t
  in
  FStar.Classical.forall_intro step

// Bnode-disjointness of two graphs, in the occurrence-predicate
// vocabulary 5.0 introduced. Stated as a single symmetric conjunction
// so neither direction needs a separate symmetry lemma.
let bnode_disjoint (g1 g2 : list triple) : prop =
  forall (b : bnode_id). ~(graph_has_bnode g1 b /\ graph_has_bnode g2 b)

// The merged assignment: read off `a1` for a label that is one of
// `g1`'s bnodes, `a2` otherwise. Well-defined regardless of
// disjointness; disjointness is what makes it agree with `a2` on
// `g2`'s own labels too (proved just below).
let merge_assignment (i : interp) (g1 : list triple) (a1 a2 : bnode_assignment i.idom)
  : bnode_assignment i.idom =
  fun (b : bnode_id) -> if List.Tot.mem b (graph_bnode_ids g1) then a1 b else a2 b

let lemma_merge_assignment_g1 (i : interp) (g1 : list triple) (a1 a2 : bnode_assignment i.idom)
                              (b : bnode_id)
  : Lemma (requires graph_has_bnode g1 b)
          (ensures  merge_assignment i g1 a1 a2 b == a1 b) =
  lemma_graph_bnode_ids_mem g1 b;
  mem_memP b (graph_bnode_ids g1)

let lemma_merge_assignment_g2 (i : interp) (g1 g2 : list triple) (a1 a2 : bnode_assignment i.idom)
                              (b : bnode_id)
  : Lemma (requires bnode_disjoint g1 g2 /\ graph_has_bnode g2 b)
          (ensures  merge_assignment i g1 a1 a2 b == a2 b) =
  lemma_graph_bnode_ids_mem g1 b;
  mem_memP b (graph_bnode_ids g1)

// The fixed-interpretation, fixed-assignment satisfaction of the
// merge, from bnode-disjoint separate satisfaction of the components
// under (possibly different) witness assignments a1, a2.
let lemma_merge_satisfies (i : interp) (g1 g2 : list triple)
                          (a1 a2 : bnode_assignment i.idom)
  : Lemma (requires bnode_disjoint g1 g2 /\ holds_all i a1 g1 /\ holds_all i a2 g2)
          (ensures  holds_all i (merge_assignment i g1 a1 a2) (g1 @ g2)) =
  let am = merge_assignment i g1 a1 a2 in
  let agrees_g1 (b : bnode_id)
    : Lemma (requires memP b (graph_bnode_ids g1)) (ensures am b == a1 b) =
    lemma_graph_bnode_ids_mem g1 b;
    lemma_merge_assignment_g1 i g1 a1 a2 b
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires agrees_g1);
  let agrees_g2 (b : bnode_id)
    : Lemma (requires memP b (graph_bnode_ids g2)) (ensures am b == a2 b) =
    lemma_graph_bnode_ids_mem g2 b;
    lemma_merge_assignment_g2 i g1 g2 a1 a2 b
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires agrees_g2);
  graph_bnodes_complete i a1 am g1;
  graph_bnodes_complete i a2 am g2;
  assert (holds_all i am g1);
  assert (holds_all i am g2);
  lemma_holds_all_append i am g1 g2

// THEOREM (merging, satisfies level). The union of two bnode-disjoint
// graphs is satisfied by an interpretation iff each graph is.
let merge_satisfies_iff (i : interp) (g1 g2 : list triple)
  : Lemma (requires bnode_disjoint g1 g2)
          (ensures  satisfies i (g1 @ g2) <==> (satisfies i g1 /\ satisfies i g2)) =
  let forward ()
    : Lemma (requires satisfies i (g1 @ g2)) (ensures satisfies i g1 /\ satisfies i g2) =
    eliminate exists (a : bnode_assignment i.idom). holds_all i a (g1 @ g2)
    returns (satisfies i g1 /\ satisfies i g2)
    with _pf.
      (lemma_holds_all_append i a g1 g2;
       assert (satisfies i g1);
       assert (satisfies i g2))
  in
  let backward ()
    : Lemma (requires satisfies i g1 /\ satisfies i g2) (ensures satisfies i (g1 @ g2)) =
    eliminate exists (a1 : bnode_assignment i.idom). holds_all i a1 g1
    returns (satisfies i (g1 @ g2))
    with _p1.
      (eliminate exists (a2 : bnode_assignment i.idom). holds_all i a2 g2
       returns (satisfies i (g1 @ g2))
       with _p2.
         (lemma_merge_satisfies i g1 g2 a1 a2;
          assert (satisfies i (g1 @ g2))))
  in
  FStar.Classical.move_requires forward ();
  FStar.Classical.move_requires backward ()

// THEOREM (the entailment corollary the REC states, two-graph form):
// "the merge of a set of graphs entails each of the graphs in the
// set, and a set of graphs entails a graph E if and only if the merge
// of the set entails E" (RDF 1.1 Semantics section 5.2). Stated here
// for two graphs (the set form is a straightforward induction on the
// set were it needed; two graphs is what this vertical's callers use).
//
// Direction 1: the merge entails each component.
let merge_entails_component (i : interp) (g1 g2 : list triple)
  : Lemma (requires bnode_disjoint g1 g2 /\ satisfies i (g1 @ g2))
          (ensures  satisfies i g1 /\ satisfies i g2) =
  merge_satisfies_iff i g1 g2

// Direction 2: {g1, g2} entails E iff the merge entails E -- the
// "only if" needs no disjointness (an interpretation satisfying the
// merge always satisfies both components, by `lemma_holds_all_append`
// alone); the "if" needs it, to build one assignment for the merge out
// of separate witnesses for g1 and g2.
let merge_entails_iff (i : interp) (g1 g2 e : list triple)
  : Lemma (requires bnode_disjoint g1 g2)
          (ensures  (satisfies i g1 /\ satisfies i g2 ==> satisfies i e) <==>
                    (satisfies i (g1 @ g2) ==> satisfies i e)) =
  merge_satisfies_iff i g1 g2
