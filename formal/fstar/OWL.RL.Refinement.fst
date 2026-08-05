module OWL.RL.Refinement

// ===================================================================
// REFINEMENT: the SHIPPING OWL 2 RL closure rules against the
// declarative rule tables of OWL.RL.Spec.fst.
//
// Every theorem below names a function the engine actually runs
// (OWL.Closure.fsti's `owl_rule_*`) -- not a model or transcription
// of it. Verify-only proof layer; no shipping module is edited and
// nothing here extracts.
//
// -------------------------------------------------------------------
// WHAT "LICENSED" MEANS HERE, precisely
// -------------------------------------------------------------------
// A closure rule is a graph transformer, so its licensing statement
// is the TRANSCRIPTION-FIDELITY property:
//
//     every triple in the rule's output is either already in the
//     rule's input graph, or is derived from the step-input snapshot
//     by ONE application of the table row the rule's ledger entry
//     claims it implements (the row's `*_derives` predicate in
//     OWL.RL.Spec).
//
// This is the syntactic sibling of OWL.Semantics.Soundness's
// truth-preservation lemmas. Soundness says each emission is TRUE in
// every interpretation satisfying the row's semantic condition; this
// module says each emission is exactly what the W3C table row
// LICENSES -- no more. The two lemma kinds together, rule by rule,
// are the program recorded in the engine ledger at the foot of
// OWL.RL.Spec.fst (task #10).
//
// This first landing proves ONE rule -- `owl_rule_sameAs_symmetry`
// against row eq-sym -- end to end, establishing the reusable
// pieces:
//   * the vocabulary bridge (engine wf_iri casts == Spec casts);
//   * the converter bridge (`subj_term` == `subject_to_term`, and
//     the `term_to_subject` half-inverse);
//   * memP through the #262 pair pipeline (collect / sortWith /
//     dedup) -- the syntactic twin of the truth-carrying walk in
//     OWL.Semantics.Soundness.lemma_sameas_pairs_hold;
//   * the fold_left_inv skeleton for a cons-emitting rule fold,
//     with the licensing property as the invariant.
//
// Proof-shape note: the step lambdas are LOCAL lets spelled verbatim
// from the engine text, closed by `assert_norm (rule g ig ==
// fold_left step ...)` -- the same skeleton as OWL.Semantics.
// Soundness. A first draft used top-level step functions and memP
// recursions instead; the closing assert_norm does NOT reduce
// through a top-level name the way it reduces through a zeta-
// unfoldable local, and the assertion fails. Keep the locals.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas
open RDF.Entailment.Simple.Spec
open OWL.RL.Spec

// ===================================================================
// 0. Bridges: the two sides spell the same objects differently.
//
// OWL.Closure and OWL.RL.Spec each cast the canonical vocabulary
// strings to `wf_iri` independently (two `assert_norm` sites, by
// design -- the Spec module opens no engine module). The Spec
// phrases subject-position terms with Simple.Spec's `subj_term`; the
// engine converts with RDF.Graph's `subject_to_term` and
// `term_to_subject`. These lemmas make the identifications available
// to the SMT encoding by name.
// ===================================================================

let lemma_vocab_sameas_agree ()
  : Lemma (OWL.Closure.owl_sameAs == OWL.RL.Spec.o_owl_sameAs) = ()

let lemma_subj_term_agree (s : subject)
  : Lemma (subj_term s == subject_to_term s) = ()

// Half-inverse: recovering a subject from a term pins the term.
// (Same statement as RDF.Entailment.RDFS.Refinement's
// `lemma_term_to_subject_subj_term`; restated so this module does
// not depend on the RDFS refinement layer.)
let lemma_term_to_subject_subj_term (t : rdf_term) (s : subject)
  : Lemma (requires term_to_subject t == Some s) (ensures subj_term s == t) =
  match t with
  | T_IRI _ -> ()
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// ===================================================================
// 1. memP through the #262 sameAs pair pipeline.
//
// `sameas_pairs` is collect / sortWith / dedup over the step-input
// snapshot. Provenance: every pair it yields names a sameAs edge of
// the snapshot. The dedup walk is restated here rather than imported
// from OWL.Semantics.Soundness so the syntactic layer carries no
// dependency on the interpretation machinery.
// ===================================================================

// A pair names a sameAs edge of g.
let pair_from_edge (g : list triple) (xy : subject * subject) : prop =
  exists (u : triple).
    memP u g /\ u.p == owl_sameAs /\
    u.s == fst xy /\ term_to_subject u.o == Some (snd xy)

// Every pair of ps names an edge of g.
let pairs_licensed (g : list triple) (ps : list (subject * subject)) : prop =
  forall (xy : subject * subject). memP xy ps ==> pair_from_edge g xy

// Membership preservation through the pair dedup walk.
let rec lemma_dedup_pairs_memP (prev : option string)
    (ps acc : list (subject * subject)) (x : subject * subject)
  : Lemma
    (ensures memP x (dedup_pairs_sorted_aux prev ps acc) ==>
             (memP x ps \/ memP x acc))
    (decreases ps) =
  match ps with
  | [] -> rev_memP acc x
  | p :: rest ->
    lemma_dedup_pairs_memP prev rest acc x;
    lemma_dedup_pairs_memP (Some (sameas_pair_key p)) rest (p :: acc) x

let lemma_sameas_pairs_provenance (ig : indexed_graph)
  : Lemma (ensures pairs_licensed ig.ig_triples (sameas_pairs ig)) =
  let collect_step : list (subject * subject) -> triple -> list (subject * subject) =
    fun (acc : list (subject * subject)) (t : triple) ->
      if t.p = owl_sameAs then
        match term_to_subject t.o with
        | Some y -> if subject_eq t.s y then acc else (t.s, y) :: acc
        | None -> acc
      else acc in
  let raw = List.Tot.fold_left collect_step [] ig.ig_triples in
  // Step preservation: the consed pair (t.s, y) has t itself as its
  // edge witness; everything else was licensed already.
  introduce forall (acc : list (subject * subject)) (t : triple).
      (memP t ig.ig_triples /\ pairs_licensed ig.ig_triples acc) ==>
      pairs_licensed ig.ig_triples (collect_step acc t)
  with introduce (memP t ig.ig_triples /\ pairs_licensed ig.ig_triples acc) ==>
                 pairs_licensed ig.ig_triples (collect_step acc t)
  with _ . ();
  fold_left_inv (pairs_licensed ig.ig_triples) collect_step ig.ig_triples [];
  let sorted = List.Tot.sortWith sameas_pair_cmp raw in
  lemma_sortWith_memP_forall sameas_pair_cmp raw;
  FStar.Classical.forall_intro (lemma_dedup_pairs_memP None sorted []);
  assert_norm (sameas_pairs ig == dedup_pairs_sorted_aux None sorted [])

// ===================================================================
// 2. eq-sym: every `owl_rule_sameAs_symmetry` emission is licensed.
//
// OWL 2 RL/RDF rules table row eq-sym:
//   T(?x, owl:sameAs, ?y)  =>  T(?y, owl:sameAs, ?x)
// transcribed as OWL.RL.Spec.eq_sym_derives. The statement is
// against the step-input snapshot `ig.ig_triples` -- the same
// snapshot semantics the rule's #262 banner declares.
// ===================================================================

// The licensing invariant, specialised to this rule: everything in
// `out` is an input triple of `g` or an eq-sym conclusion from the
// snapshot.
let eq_sym_licensed (g : rdf_graph) (snapshot : list triple) (out : rdf_graph)
  : prop =
  forall (t : triple). memP t out ==>
    (memP t g \/ eq_sym_derives snapshot t)

val owl_rule_sameAs_symmetry_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (ensures eq_sym_licensed g ig.ig_triples (owl_rule_sameAs_symmetry g ig))

let owl_rule_sameAs_symmetry_licensed g ig =
  lemma_sameas_pairs_provenance ig;
  lemma_vocab_sameas_agree ();
  let emit_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let new_t : triple = { s = y; p = owl_sameAs; o = subject_to_term x } in
      add_triple_unchecked acc new_t in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (memP xy (sameas_pairs ig) /\ eq_sym_licensed g ig.ig_triples acc) ==>
      eq_sym_licensed g ig.ig_triples (emit_step acc xy)
  with introduce (memP xy (sameas_pairs ig) /\ eq_sym_licensed g ig.ig_triples acc) ==>
                 eq_sym_licensed g ig.ig_triples (emit_step acc xy)
  with _ . begin
    let (x, y) = xy in
    let new_t : triple = { s = y; p = owl_sameAs; o = subject_to_term x } in
    // pairs_licensed names the edge u behind xy; u and ys := y are
    // exactly eq_sym_derives' witnesses, after bridging:
    //   u.p == o_owl_sameAs        -- vocabulary agreement;
    //   subj_term y == u.o         -- the half-inverse;
    //   new_t.o == subj_term u.s   -- x == u.s and the converter
    //                                 bridge folds subject_to_term.
    eliminate exists (u : triple).
        memP u ig.ig_triples /\ u.p == owl_sameAs /\
        u.s == fst xy /\ term_to_subject u.o == Some (snd xy)
    returns eq_sym_derives ig.ig_triples new_t
    with _ . begin
      lemma_term_to_subject_subj_term u.o (snd xy);
      lemma_subj_term_agree u.s;
      assert (new_t == ({ s = snd xy; p = o_owl_sameAs;
                          o = subj_term u.s } <: triple))
    end
  end;
  fold_left_inv (eq_sym_licensed g ig.ig_triples) emit_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_symmetry g ig ==
               List.Tot.fold_left emit_step g (sameas_pairs ig))

// Per-triple corollary, the form downstream compositions consume.
val theorem_sameAs_symmetry_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires memP t (owl_rule_sameAs_symmetry g ig))
    (ensures  memP t g \/ eq_sym_derives ig.ig_triples t)

let theorem_sameAs_symmetry_licensed g ig t =
  owl_rule_sameAs_symmetry_licensed g ig

// ===================================================================
// 3. eq-ref: every `owl_rule_sameAs_reflexivity` emission is licensed.
//
// OWL 2 RL/RDF rules table row eq-ref:
//   T(?s, ?p, ?o)  =>  T(?s, owl:sameAs, ?s)  T(?p, owl:sameAs, ?p)
//                      T(?o, owl:sameAs, ?o)
// transcribed as OWL.RL.Spec.eq_ref_derives. The engine collects the
// IRI/bnode nodes of g from subject and object positions only (its
// "named individual" approximation never collects predicates), so
// the licensing uses the first and third disjuncts of the row. The
// rule reads g, not the snapshot: the statement is over g.
// ===================================================================

// A node occurs in g in subject or (subject-eligible) object position.
let node_from_graph (g : list triple) (n : subject) : prop =
  exists (u : triple).
    memP u g /\ (u.s == n \/ subj_term n == u.o)

let nodes_licensed (g : list triple) (ns : list subject) : prop =
  forall (n : subject). memP n ns ==> node_from_graph g n

let lemma_collect_nodes_provenance (g : rdf_graph)
  : Lemma (ensures nodes_licensed g (collect_iri_or_bnode_terms g)) =
  let collect_step : list subject -> triple -> list subject =
    fun (acc : list subject) (t : triple) ->
      let acc1 =
        if List.Tot.existsb (fun x -> subject_eq x t.s) acc
        then acc else t.s :: acc
      in
      match t.o with
      | T_IRI i ->
        let ox = S_IRI i in
        if List.Tot.existsb (fun x -> subject_eq x ox) acc1 then acc1 else ox :: acc1
      | T_BNode b ->
        let ox = S_BNode b in
        if List.Tot.existsb (fun x -> subject_eq x ox) acc1 then acc1 else ox :: acc1
      | T_Literal _ -> acc1
      | T_TripleTerm _ _ _ -> acc1 in
  introduce forall (acc : list subject) (t : triple).
      (memP t g /\ nodes_licensed g acc) ==>
      nodes_licensed g (collect_step acc t)
  with introduce (memP t g /\ nodes_licensed g acc) ==>
                 nodes_licensed g (collect_step acc t)
  with _ . ();
  fold_left_inv (nodes_licensed g) collect_step g [];
  assert_norm (collect_iri_or_bnode_terms g ==
               List.Tot.fold_left collect_step [] g)

// The licensing invariant for this rule.
let eq_ref_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ eq_ref_derives g t)

val owl_rule_sameAs_reflexivity_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures eq_ref_licensed g (owl_rule_sameAs_reflexivity g ig))

let owl_rule_sameAs_reflexivity_licensed g ig =
  lemma_collect_nodes_provenance g;
  lemma_vocab_sameas_agree ();
  let nodes = collect_iri_or_bnode_terms g in
  let emit_step : rdf_graph -> subject -> rdf_graph =
    fun (acc : rdf_graph) (n : subject) ->
      let new_t : triple = { s = n; p = owl_sameAs; o = subject_to_term n } in
      add_triple_unchecked acc new_t in
  introduce forall (acc : rdf_graph) (n : subject).
      (memP n nodes /\ eq_ref_licensed g acc) ==>
      eq_ref_licensed g (emit_step acc n)
  with introduce (memP n nodes /\ eq_ref_licensed g acc) ==>
                 eq_ref_licensed g (emit_step acc n)
  with _ . begin
    let new_t : triple = { s = n; p = owl_sameAs; o = subject_to_term n } in
    lemma_subj_term_agree n;
    eliminate exists (u : triple). memP u g /\ (u.s == n \/ subj_term n == u.o)
    returns eq_ref_derives g new_t
    with _ . begin
      eliminate u.s == n \/ subj_term n == u.o
      returns eq_ref_derives g new_t
      with _ . begin
        lemma_subj_term_agree u.s;
        assert (new_t == ({ s = u.s; p = o_owl_sameAs;
                            o = subj_term u.s } <: triple))
      end
      and  _ . begin
        assert (new_t == ({ s = n; p = o_owl_sameAs; o = u.o } <: triple))
      end
    end
  end;
  fold_left_inv (eq_ref_licensed g) emit_step nodes g;
  assert_norm (owl_rule_sameAs_reflexivity g ig ==
               List.Tot.fold_left emit_step g (collect_iri_or_bnode_terms g))

// Per-triple corollary.
val theorem_sameAs_reflexivity_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires memP t (owl_rule_sameAs_reflexivity g ig))
    (ensures  memP t g \/ eq_ref_derives g t)

let theorem_sameAs_reflexivity_licensed g ig t =
  owl_rule_sameAs_reflexivity_licensed g ig

// ===================================================================
// 4. prp-symp: every `owl_rule_symmetric_property` emission licensed.
//
// OWL 2 RL/RDF rules table row prp-symp:
//   T(?p, rdf:type, owl:SymmetricProperty), T(?x, ?p, ?y)
//     =>  T(?y, ?p, ?x)
// transcribed as OWL.RL.Spec.prp_symp_derives. Both of the rule's
// folds read g; ig is unused. The statement is over g.
// ===================================================================

let lemma_vocab_symp_agree ()
  : Lemma (RDFS.Closure.rdf_type == OWL.RL.Spec.o_rdf_type /\
           OWL.Closure.owl_SymmetricProperty ==
             OWL.RL.Spec.o_owl_SymmetricProperty) = ()

// rdf_term_eq on two IRIs is IRI equality (one unfolding of the
// recursion).
let lemma_rdf_term_eq_iri (i1 i2 : wf_iri)
  : Lemma (requires rdf_term_eq (T_IRI i1) (T_IRI i2) == true)
          (ensures i1 == i2) = ()

// Membership through cons_if_new_iri. (Restated from
// RDF.Entailment.RDFS.Refinement, which verifies AFTER this module
// in the build list.)
let lemma_cons_if_new_iri_memP (i : wf_iri) (acc : list wf_iri) (x : wf_iri)
  : Lemma (memP x (cons_if_new_iri i acc) ==> x == i \/ memP x acc) = ()

// A property IRI declared symmetric in g.
let symp_from_decl (g : list triple) (p : wf_iri) : prop =
  exists (decl : triple).
    memP decl g /\ decl.p == rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI owl_SymmetricProperty

let symps_licensed (g : list triple) (ps : list wf_iri) : prop =
  forall (p : wf_iri). memP p ps ==> symp_from_decl g p

let prp_symp_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ prp_symp_derives g t)

val owl_rule_symmetric_property_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures prp_symp_licensed g (owl_rule_symmetric_property g ig))

let owl_rule_symmetric_property_licensed g ig =
  lemma_vocab_symp_agree ();
  let collect_step : list wf_iri -> triple -> list wf_iri =
    fun (acc : list wf_iri) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then
        match t.s with
        | S_IRI p_iri -> cons_if_new_iri p_iri acc
        | _ -> acc
      else acc in
  let sym_props = List.Tot.fold_left collect_step [] g in
  // Collect-step preservation: the consed IRI has t itself as decl.
  introduce forall (acc : list wf_iri) (t : triple).
      (memP t g /\ symps_licensed g acc) ==>
      symps_licensed g (collect_step acc t)
  with introduce (memP t g /\ symps_licensed g acc) ==>
                 symps_licensed g (collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then
      match t.s, t.o with
      | S_IRI p_iri, T_IRI j ->
        lemma_rdf_term_eq_iri j owl_SymmetricProperty;
        FStar.Classical.forall_intro (lemma_cons_if_new_iri_memP p_iri acc)
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (symps_licensed g) collect_step g [];
  // Emission-step preservation: mem gives memP for the declared
  // predicate; t itself is the (x P y) premise.
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if List.Tot.mem t.p sym_props then
        match term_to_subject t.o with
        | Some new_subj ->
          let new_t : triple = { s = new_subj; p = t.p; o = subject_to_term t.s } in
          add_triple_unchecked acc new_t
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ prp_symp_licensed g acc) ==>
      prp_symp_licensed g (emit_step acc t)
  with introduce (memP t g /\ prp_symp_licensed g acc) ==>
                 prp_symp_licensed g (emit_step acc t)
  with _ . begin
    if List.Tot.mem t.p sym_props then
      match term_to_subject t.o with
      | Some new_subj ->
        List.Tot.Properties.mem_memP t.p sym_props;
        lemma_term_to_subject_subj_term t.o new_subj;
        lemma_subj_term_agree t.s;
        assert (({ s = new_subj; p = t.p; o = subject_to_term t.s } <: triple) ==
                ({ s = new_subj; p = t.p; o = subj_term t.s } <: triple))
      | None -> ()
    else ()
  end;
  fold_left_inv (prp_symp_licensed g) emit_step g g;
  assert_norm (owl_rule_symmetric_property g ig ==
               List.Tot.fold_left emit_step g g)

// Per-triple corollary.
val theorem_symmetric_property_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires memP t (owl_rule_symmetric_property g ig))
    (ensures  memP t g \/ prp_symp_derives g t)

let theorem_symmetric_property_licensed g ig t =
  owl_rule_symmetric_property_licensed g ig

// ===================================================================
// 5. scm-eqc1: every `owl_rule_equivalent_class` emission is licensed.
//
// The engine ledger in OWL.RL.Spec.fst labels `equivalent_class` as
// implementing cax-eqc1 + cax-eqc2, but that is a downstream-effect
// label, not a transcription target: cax-eqc1/cax-eqc2 conclude class
// MEMBERSHIP ("if C1 eqc C2 and x:C1 then x:C2"), which this rule
// never touches -- it only ever writes rdfs:subClassOf triples. The
// cax-eqc effect is reached two rules downstream, via cax-sco
// consuming the subClassOf edges this rule emits. What this rule's
// emissions actually ARE is the literal conclusion of Table 8 row
// scm-eqc1:
//   T(?c1, owl:equivalentClass, ?c2)
//     => T(?c1, rdfs:subClassOf, ?c2), T(?c2, rdfs:subClassOf, ?c1)
// transcribed as OWL.RL.Spec.scm_eqc1_derives. This is the row this
// module licenses against; scm-eqc2 (the converse direction, sco+sco
// => eqc) is a different rule, not implemented by this fold, and out
// of scope here.
//
// The engine's BNODE-POLLUTION GUARD (parent9, 2026-04-23) makes the
// rule emit FEWER conclusions than the row licenses whenever either
// side is an anonymous class-expression bnode: S_IRI/S_BNode emits
// only the first disjunct's triple, S_BNode/S_IRI only the second's,
// and S_BNode/S_BNode emits neither. Emitting fewer conclusions than
// a row licenses is still licensed -- the case split below carries no
// extra proof burden, it just narrows which disjunct (or neither) is
// asserted per case.
// ===================================================================

let lemma_vocab_eqc_agree ()
  : Lemma (OWL.Closure.owl_equivalentClass == OWL.RL.Spec.o_owl_equivalentClass /\
           RDFS.Closure.rdfs_subClassOf == OWL.RL.Spec.o_rdfs_subClassOf) = ()

// The licensing invariant for this rule, against scm-eqc1's row.
let scm_eqc1_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ scm_eqc1_derives g t)

val owl_rule_equivalent_class_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures scm_eqc1_licensed g (owl_rule_equivalent_class g ig))

let owl_rule_equivalent_class_licensed g ig =
  lemma_vocab_eqc_agree ();
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_equivalentClass then
        match term_to_subject t.o with
        | Some d_subj ->
          let t1 : triple = { s = t.s;    p = rdfs_subClassOf; o = subject_to_term d_subj } in
          let t2 : triple = { s = d_subj; p = rdfs_subClassOf; o = subject_to_term t.s } in
          (match t.s, d_subj with
           | S_IRI _, S_IRI _ ->
             add_triple_unchecked (add_triple_unchecked acc t1) t2
           | S_IRI _, S_BNode _ ->
             add_triple_unchecked acc t1
           | S_BNode _, S_IRI _ ->
             add_triple_unchecked acc t2
           | S_BNode _, S_BNode _ ->
             acc)
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ scm_eqc1_licensed g acc) ==>
      scm_eqc1_licensed g (emit_step acc t)
  with introduce (memP t g /\ scm_eqc1_licensed g acc) ==>
                 scm_eqc1_licensed g (emit_step acc t)
  with _ . begin
    if t.p = owl_equivalentClass then
      match term_to_subject t.o with
      | Some d_subj ->
        let t1 : triple = { s = t.s;    p = rdfs_subClassOf; o = subject_to_term d_subj } in
        let t2 : triple = { s = d_subj; p = rdfs_subClassOf; o = subject_to_term t.s } in
        // Both t1 and t2 are witnessed by u := t. subject_to_term
        // d_subj == t.o via the half-inverse plus the converter
        // bridge; that equality carries both directions at once.
        lemma_term_to_subject_subj_term t.o d_subj;
        lemma_subj_term_agree d_subj;
        lemma_subj_term_agree t.s;
        // t1 is scm_eqc1_derives' first disjunct, witness u := t
        // (so u.s == t.s and u.o == t.o literally).
        assert (t1 == ({ s = t.s; p = o_rdfs_subClassOf; o = t.o } <: triple));
        // t2 is the second disjunct, witness u := t, c2s := d_subj.
        assert (subj_term d_subj == t.o);
        assert (t2 == ({ s = d_subj; p = o_rdfs_subClassOf;
                         o = subj_term t.s } <: triple));
        (match t.s, d_subj with
         | S_IRI _, S_IRI _ -> ()
         | S_IRI _, S_BNode _ -> ()
         | S_BNode _, S_IRI _ -> ()
         | S_BNode _, S_BNode _ -> ())
      | None -> ()
    else ()
  end;
  fold_left_inv (scm_eqc1_licensed g) emit_step g g;
  assert_norm (owl_rule_equivalent_class g ig ==
               List.Tot.fold_left emit_step g g)

// Per-triple corollary.
val theorem_equivalent_class_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires memP t (owl_rule_equivalent_class g ig))
    (ensures  memP t g \/ scm_eqc1_derives g t)

let theorem_equivalent_class_licensed g ig t =
  owl_rule_equivalent_class_licensed g ig

// ===================================================================
// 6. scm-eqp1: every `owl_rule_equivalent_property` emission is licensed.
//
// The engine ledger labels `equivalent_property` as implementing
// prp-eqp1 + prp-eqp2, but those rows conclude DATA triples ("if
// P eqp Q and x P y then x Q y"), which this rule never emits -- its
// emissions are the two rdfs:subPropertyOf conclusions of Table 8 row
// scm-eqp1:
//   T(?p1, owl:equivalentProperty, ?p2)
//     => T(?p1, rdfs:subPropertyOf, ?p2), T(?p2, rdfs:subPropertyOf, ?p1)
// transcribed as OWL.RL.Spec.scm_eqp1_derives. The prp-eqp data-triple
// effect arrives downstream via prp-spo1 consuming the subPropertyOf
// edges this rule emits, exactly as cax-eqc arrives downstream of
// scm-eqc1 via cax-sco (see the section 5 banner above). This is the
// row this module licenses against.
//
// Unlike owl_rule_equivalent_class, this rule's single match arm only
// fires on S_IRI/T_IRI (property IRIs are never anonymous), so there
// is no bnode-pollution case split here -- both conclusions are always
// emitted together.
// ===================================================================

let lemma_vocab_eqp_agree ()
  : Lemma (OWL.Closure.owl_equivalentProperty == OWL.RL.Spec.o_owl_equivalentProperty /\
           RDFS.Closure.rdfs_subPropertyOf == OWL.RL.Spec.o_rdfs_subPropertyOf) = ()

// The licensing invariant for this rule, against scm-eqp1's row.
let scm_eqp1_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ scm_eqp1_derives g t)

val owl_rule_equivalent_property_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures scm_eqp1_licensed g (owl_rule_equivalent_property g ig))

let owl_rule_equivalent_property_licensed g ig =
  lemma_vocab_eqp_agree ();
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_equivalentProperty then
        match t.s, t.o with
        | S_IRI p_iri, T_IRI q_iri ->
          let t1 : triple = { s = S_IRI p_iri; p = rdfs_subPropertyOf; o = T_IRI q_iri } in
          let t2 : triple = { s = S_IRI q_iri; p = rdfs_subPropertyOf; o = T_IRI p_iri } in
          add_triple_unchecked (add_triple_unchecked acc t1) t2
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ scm_eqp1_licensed g acc) ==>
      scm_eqp1_licensed g (emit_step acc t)
  with introduce (memP t g /\ scm_eqp1_licensed g acc) ==>
                 scm_eqp1_licensed g (emit_step acc t)
  with _ . begin
    if t.p = owl_equivalentProperty then
      match t.s, t.o with
      | S_IRI p_iri, T_IRI q_iri ->
        let t1 : triple = { s = S_IRI p_iri; p = rdfs_subPropertyOf; o = T_IRI q_iri } in
        let t2 : triple = { s = S_IRI q_iri; p = rdfs_subPropertyOf; o = T_IRI p_iri } in
        // t1 is scm_eqp1_derives' first disjunct, witness u := t
        // (so u.s == S_IRI p_iri and u.o == T_IRI q_iri literally).
        assert (t1 == ({ s = t.s; p = o_rdfs_subPropertyOf; o = t.o } <: triple));
        // t2 is the second disjunct, witness u := t, p2s := S_IRI q_iri:
        // subj_term (S_IRI q_iri) == T_IRI q_iri == u.o by definition of
        // subj_term, and subj_term u.s == subj_term (S_IRI p_iri) ==
        // T_IRI p_iri likewise.
        lemma_subj_term_agree (S_IRI q_iri);
        lemma_subj_term_agree t.s;
        assert (subj_term (S_IRI q_iri) == t.o);
        assert (t2 == ({ s = S_IRI q_iri; p = o_rdfs_subPropertyOf;
                         o = subj_term t.s } <: triple))
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (scm_eqp1_licensed g) emit_step g g;
  assert_norm (owl_rule_equivalent_property g ig ==
               List.Tot.fold_left emit_step g g)

// Per-triple corollary.
val theorem_equivalent_property_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires memP t (owl_rule_equivalent_property g ig))
    (ensures  memP t g \/ scm_eqp1_derives g t)

let theorem_equivalent_property_licensed g ig t =
  owl_rule_equivalent_property_licensed g ig

// ===================================================================
// 7. prp-inv1 + prp-inv2: every `owl_rule_inverse_of` emission is
// licensed.
//
// OWL 2 RL/RDF rules table rows prp-inv1 / prp-inv2:
//   T(?p1, owl:inverseOf, ?p2)  T(?x, ?p1, ?y)  =>  T(?y, ?p2, ?x)
//   T(?p1, owl:inverseOf, ?p2)  T(?x, ?p2, ?y)  =>  T(?y, ?p1, ?x)
// transcribed as OWL.RL.Spec.prp_inv1_derives / prp_inv2_derives. Both
// of the rule's folds read g; ig is unused. The statement is over g
// -- like prp-symp, this is a non-snapshot rule.
//
// This is the module's first NESTED-fold rule: the outer fold walks
// the owl:inverseOf declarations of g, seeded at g; for each
// declaration the INNER fold walks all of g again, seeded at the
// outer accumulator, emitting the flipped triple for whichever side
// of the pair the current triple's predicate matches. The proof
// follows OWL.Semantics.Soundness.rdfs_rule_domain_sound's shape:
// prove the inner step's invariant preservation FIRST (inside the
// outer introduce body), close it with its own fold_left_inv, and
// only then does the outer introduce's postcondition follow.
//
// PROOF-SHAPE NOTE, specific to nested folds (recorded for prp-trp /
// prp-spo2, which reuse this skeleton): the inner step CANNOT be
// spelled as a bare `fun acc2 t -> ...` re-typed inside the outer
// introduce's body. outer_step's OWN pattern match binds its own
// p1_iri/p2_iri (a DIFFERENT variable from the introduce body's
// p1_iri/p2_iri, even though provably equal via `inv_t.s ==
// S_IRI p1_iri`). Two closures that differ only in which
// (propositionally-equal) variable they capture are NOT identified by
// SMT congruence -- congruence needs the SAME function symbol, and
// proving `fold_left F1 acc g == fold_left F2 acc g` for merely
// pointwise-equal F1/F2 is functional EXTENSIONALITY, which F*'s SMT
// encoding does not supply automatically (confirmed by direct probe:
// even `--z3rlimit 2000` leaves it "incomplete quantifiers", not a
// resource shortfall).
//
// RESOLVED (2026-08-05, commit fb8d98f / task #36): the fix is the
// PROOF-FRIENDLY GUARD RULE, not a proof-side workaround. The inner
// fold is now the top-level named `OWL.Closure.inverse_of_emit p1_iri
// p2_iri` -- ONE function symbol, defined once in the engine and
// referenced identically by outer_step's own branch and by this
// proof's `inner_step`. Reconciling the two closures is now a single
// application-congruence step (`f a b == f a' b'` given `a==a',
// b==b'`) instead of extensionality -- and congruence IS automatic.
// assert_norm's closing zeta-unfolds `inner_step` (a local alias for
// the named application) the same as any other local, so the
// top-level normal-form comparison against the engine's fold is
// unaffected.
// ===================================================================

let lemma_vocab_inv_agree ()
  : Lemma (OWL.Closure.owl_inverseOf == OWL.RL.Spec.o_owl_inverseOf) = ()

let inv_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==>
    (memP t g \/ prp_inv1_derives g t \/ prp_inv2_derives g t)

#push-options "--z3rlimit 100 --split_queries always"

val owl_rule_inverse_of_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (ensures inv_licensed g (owl_rule_inverse_of g ig))

let owl_rule_inverse_of_licensed g ig =
  lemma_vocab_inv_agree ();
  // Engine text verbatim -- the inner fold is the shared named
  // application `inverse_of_emit p1_iri p2_iri`, exactly as
  // owl_rule_inverse_of writes it after the closure-identity fix.
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (inv_t : triple) ->
      if inv_t.p = owl_inverseOf then
        match inv_t.s, inv_t.o with
        | S_IRI p1_iri, T_IRI p2_iri ->
          List.Tot.fold_left (inverse_of_emit p1_iri p2_iri) acc g
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (inv_t : triple).
      (memP inv_t g /\ inv_licensed g acc) ==>
      inv_licensed g (outer_step acc inv_t)
  with introduce (memP inv_t g /\ inv_licensed g acc) ==>
                 inv_licensed g (outer_step acc inv_t)
  with _ . begin
    if inv_t.p = owl_inverseOf then
      match inv_t.s, inv_t.o with
      | S_IRI p1_iri, T_IRI p2_iri ->
        let inner_step : rdf_graph -> triple -> rdf_graph =
          inverse_of_emit p1_iri p2_iri in
        introduce forall (acc2 : rdf_graph) (t : triple).
            (memP t g /\ inv_licensed g acc2) ==>
            inv_licensed g (inner_step acc2 t)
        with introduce (memP t g /\ inv_licensed g acc2) ==>
                       inv_licensed g (inner_step acc2 t)
        with _ . begin
          // decl := inv_t, u := t, p1 := p1_iri, p2 := p2_iri --
          // shared witnesses for both branches below.
          if t.p = p1_iri then begin
            match term_to_subject t.o with
            | Some new_subj ->
              let new_t : triple =
                { s = new_subj; p = p2_iri; o = subject_to_term t.s } in
              // prp-inv1: u.p == p1, ys := new_subj, conclusion
              // predicate p2.
              lemma_term_to_subject_subj_term t.o new_subj;
              lemma_subj_term_agree t.s;
              assert (new_t == ({ s = new_subj; p = p2_iri;
                                  o = subj_term t.s } <: triple));
              assert (prp_inv1_derives g new_t)
            | None -> ()
          end else if t.p = p2_iri then begin
            match term_to_subject t.o with
            | Some new_subj ->
              let new_t : triple =
                { s = new_subj; p = p1_iri; o = subject_to_term t.s } in
              // prp-inv2: u.p == p2, ys := new_subj, conclusion
              // predicate p1.
              lemma_term_to_subject_subj_term t.o new_subj;
              lemma_subj_term_agree t.s;
              assert (new_t == ({ s = new_subj; p = p1_iri;
                                  o = subj_term t.s } <: triple));
              assert (prp_inv2_derives g new_t)
            | None -> ()
          end else ()
        end;
        fold_left_inv (inv_licensed g) inner_step g acc
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (inv_licensed g) outer_step g g;
  assert_norm (owl_rule_inverse_of g ig ==
               List.Tot.fold_left outer_step g g)

#pop-options

// Per-triple corollary.
val theorem_inverse_of_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires memP t (owl_rule_inverse_of g ig))
    (ensures  memP t g \/ prp_inv1_derives g t \/ prp_inv2_derives g t)

let theorem_inverse_of_licensed g ig t =
  owl_rule_inverse_of_licensed g ig

// ===================================================================
// 8. eq-trans: every `owl_rule_sameAs_transitivity` emission licensed.
//
// OWL 2 RL/RDF rules table row eq-trans:
//   T(?x, owl:sameAs, ?y), T(?y, owl:sameAs, ?z)  =>  T(?x, owl:sameAs, ?z)
// transcribed as OWL.RL.Spec.eq_trans_derives. #262's outer fold walks
// the deduped snapshot pair list (section 1's `sameas_pairs`, seeded
// from g); for each pair (x, y) the INNER fold walks
// `find_objects_indexed ig y owl_sameAs` -- the ig_sp bucket lookup
// for y's sameAs-successors z, keeping the rule off an O(k^3)
// live-graph rescan. This is the module's FIRST index-reading rule:
// tracing a served z_term back to a real (y owl:sameAs z) triple
// needs `ig_wf_sp` (RDF.Indexed.fsti's serving contract for the ig_sp
// bucket, provable for real indexes via RDF.Indexed.KeyInjectivity),
// so the theorem below takes it as a hypothesis -- the same shape
// OWL.Semantics.Soundness's `rdfs_rule_domain_sound` takes
// `ig_wf_pred`, and the direct syntactic-licensing sibling of
// RDF.Entailment.RDFS.Refinement's `rdfs_rule_subClassOf_licensed` /
// `..._trans_licensed`, which prove the same outer-fold / inner-
// index-fold shape over `ig_wf_sp` for the RDFS layer. This module's
// `open OWL.Semantics` (for `ig_wf_sp`) is new as of this section --
// checked against every name already used here, no clashes.
//
// PROOF-FRIENDLY GUARD RULE (task #36): the engine's inner fold uses
// the NAMED partial application `sameas_trans_emit x`
// (OWL.Closure.fsti), not an anonymous closure -- this proof mirrors
// that same named application on both sides (the local `outer_step`
// below and the introduce-block's `inner_step`), so first-order
// congruence carries guard/witness facts across the mirror the way
// the scm-eqc2 pilot (`term_is_iri`) demonstrated. Before that fix
// this rule's inner-fold obligation was undischargeable at any
// solver budget (skills/fstar-module-style/SKILL.md trap 3).
//
// Proof follows the RDFS.Refinement precedent's shape exactly: outer
// introduce over (acc, xy), inner introduce + fold_left_inv over the
// looked-up `zs` as the LAST expression of the outer branch -- no
// trailing assert about the outer step itself. (A sibling proof,
// prp-inv's nested fold over g x g, could NOT be discharged this way
// and is parked -- but that inner fold walks the live graph, not an
// index-served list; this rule's inner fold, like RDFS.Refinement's,
// is over a bucket lookup, and closes the same way theirs does.)
// ===================================================================

// Everything the ig_sp bucket serves at key (s, owl:sameAs) names a
// real snapshot triple with exactly that subject and predicate.
// Restated locally (rather than reusing RDF.Entailment.RDFS.
// Refinement's `lemma_find_objects_elim`, which verifies AFTER this
// module in the build list) so this module carries no forward
// dependency.
let lemma_find_objects_indexed_sp_elim
    (ig : indexed_graph) (s : subject) (p : wf_iri) (x : rdf_term)
  : Lemma (requires ig_wf_sp ig /\ memP x (find_objects_indexed ig s p))
          (ensures exists (u : triple).
                     memP u ig.ig_triples /\ u.s == s /\ u.p == p /\ u.o == x) =
  let bucket = bucket_lookup ig.ig_sp (sp_key s p) in
  List.Tot.Properties.memP_map_elim (fun (t : triple) -> t.o) x bucket

// The licensing invariant for this rule, against eq-trans's row.
// Snapshot-relative like eq-sym (section 2): the row's premises are
// read off ig.ig_triples, not the step-input g.
let eq_trans_licensed (g : rdf_graph) (snapshot : list triple) (out : rdf_graph)
  : prop =
  forall (t : triple). memP t out ==>
    (memP t g \/ eq_trans_derives snapshot t)

val owl_rule_sameAs_transitivity_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires ig_wf_sp ig)
    (ensures  eq_trans_licensed g ig.ig_triples (owl_rule_sameAs_transitivity g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_sameAs_transitivity_licensed g ig =
  lemma_sameas_pairs_provenance ig;
  lemma_vocab_sameas_agree ();
  let inv = eq_trans_licensed g ig.ig_triples in
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let zs = find_objects_indexed ig y owl_sameAs in
      List.Tot.fold_left (sameas_trans_emit x) acc zs in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (memP xy (sameas_pairs ig) /\ inv acc) ==> inv (outer_step acc xy)
  with introduce (memP xy (sameas_pairs ig) /\ inv acc) ==>
                 inv (outer_step acc xy)
  with _ . begin
    let (x, y) = xy in
    let zs = find_objects_indexed ig y owl_sameAs in
    let inner_step : rdf_graph -> rdf_term -> rdf_graph = sameas_trans_emit x in
    introduce forall (acc2 : rdf_graph) (z_term : rdf_term).
        (memP z_term zs /\ inv acc2) ==> inv (inner_step acc2 z_term)
    with introduce (memP z_term zs /\ inv acc2) ==>
                   inv (inner_step acc2 z_term)
    with _ . begin
      let new_t : triple = { s = x; p = owl_sameAs; o = z_term } in
      // pairs_licensed names the edge u1 behind xy: the (x sameAs y)
      // premise.
      eliminate exists (u1 : triple).
          memP u1 ig.ig_triples /\ u1.p == owl_sameAs /\
          u1.s == fst xy /\ term_to_subject u1.o == Some (snd xy)
      returns inv (inner_step acc2 z_term)
      with _ . begin
        lemma_term_to_subject_subj_term u1.o (snd xy);
        // z_term is served from the sp-bucket at (y, owl_sameAs);
        // ig_wf_sp names the bucket triple u2: the (y sameAs z)
        // premise.
        lemma_find_objects_indexed_sp_elim ig y owl_sameAs z_term;
        eliminate exists (u2 : triple).
            memP u2 ig.ig_triples /\ u2.s == y /\ u2.p == owl_sameAs /\
            u2.o == z_term
        returns inv (inner_step acc2 z_term)
        with _ . begin
          // subj_term u2.s == subj_term y == u1.o (the half-inverse
          // above), which is eq_trans_derives' join condition; new_t
          // is its conclusion after the vocabulary bridge.
          assert (subj_term u2.s == u1.o);
          assert (new_t == ({ s = u1.s; p = o_owl_sameAs;
                              o = u2.o } <: triple))
        end
      end
    end;
    fold_left_inv inv inner_step zs acc
  end;
  fold_left_inv inv outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_transitivity g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))
#pop-options

// Per-triple corollary, the form downstream compositions consume.
val theorem_sameAs_transitivity_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ memP t (owl_rule_sameAs_transitivity g ig))
    (ensures  memP t g \/ eq_trans_derives ig.ig_triples t)

let theorem_sameAs_transitivity_licensed g ig t =
  owl_rule_sameAs_transitivity_licensed g ig
// ===================================================================
// 9. prp-trp: every `owl_rule_transitive_property` emission is licensed.
//
// OWL 2 RL/RDF rules table row prp-trp:
//   T(?p, rdf:type, owl:TransitiveProperty), T(?x, ?p, ?y), T(?y, ?p, ?z)
//     => T(?x, ?p, ?z)
// transcribed as OWL.RL.Spec.prp_trp_derives. The collect fold (trans
// props) is prp-symp's collect-fold provenance verbatim with the
// TransitiveProperty class IRI (section 4). The emission fold is a
// TWO-LEVEL nested fold: the outer binder is a single triple `t`
// (this rule's collect list is g itself, exactly as prp-symp's own
// emission fold reads g -- no separately-collected outer list, unlike
// rdfs_rule_domain_sound's `decls`); the inner fold walks
// `find_objects_indexed ig y_subj t.p`, the sp-index's serving of the
// (y_subj, t.p) bucket. Naming the inner premise u2 needs `ig_wf_sp
// ig` (OWL.Semantics) to place a served triple in the snapshot with
// the right subject/predicate, and `ig.ig_triples == g` to place that
// snapshot triple in g itself, matching how the closure step actually
// builds ig from the same g it folds over.
// ===================================================================

let lemma_vocab_trp_agree ()
  : Lemma (RDFS.Closure.rdf_type == OWL.RL.Spec.o_rdf_type /\
           OWL.Closure.owl_TransitiveProperty ==
             OWL.RL.Spec.o_owl_TransitiveProperty) = ()

// A property IRI declared transitive in g.
let trp_from_decl (g : list triple) (p : wf_iri) : prop =
  exists (decl : triple).
    memP decl g /\ decl.p == rdf_type /\
    decl.s == S_IRI p /\ decl.o == T_IRI owl_TransitiveProperty

let trps_licensed (g : list triple) (ps : list wf_iri) : prop =
  forall (p : wf_iri). memP p ps ==> trp_from_decl g p

// The licensing invariant for this rule, against prp-trp's row. The
// `snapshot` slot mirrors eq_sym_licensed's shape (this module's
// established 3-arg pattern for a rule that reads an index bucket)
// even though prp_trp_derives is stated against g directly, exactly
// as the theorem below instantiates it (snapshot := g).
let prp_trp_licensed (g : rdf_graph) (snapshot : list triple) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ prp_trp_derives g t)

val owl_rule_transitive_property_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ ig.ig_triples == g)
          (ensures prp_trp_licensed g g (owl_rule_transitive_property g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_transitive_property_licensed g ig =
  lemma_vocab_trp_agree ();
  let collect_step : list wf_iri -> triple -> list wf_iri =
    fun (acc : list wf_iri) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_TransitiveProperty) then
        match t.s with
        | S_IRI p_iri -> cons_if_new_iri p_iri acc
        | _ -> acc
      else acc in
  let trans_props = List.Tot.fold_left collect_step [] g in
  // Collect-step preservation: the consed IRI has t itself as decl.
  introduce forall (acc : list wf_iri) (t : triple).
      (memP t g /\ trps_licensed g acc) ==>
      trps_licensed g (collect_step acc t)
  with introduce (memP t g /\ trps_licensed g acc) ==>
                 trps_licensed g (collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_TransitiveProperty) then
      match t.s, t.o with
      | S_IRI p_iri, T_IRI j ->
        lemma_rdf_term_eq_iri j owl_TransitiveProperty;
        FStar.Classical.forall_intro (lemma_cons_if_new_iri_memP p_iri acc)
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (trps_licensed g) collect_step g [];
  // Emission fold: outer over g (single-triple binder t); when t.p is
  // transitive and t.o converts to a subject y_subj, an inner fold
  // over the sp-indexed objects zs emits (t.s, t.p, z) per z.
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if List.Tot.mem t.p trans_props then
        match term_to_subject t.o with
        | Some y_subj ->
          let zs = find_objects_indexed ig y_subj t.p in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (z_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = t.p; o = z_term } in
              add_triple_unchecked acc2 new_t)
            acc
            zs
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ prp_trp_licensed g g acc) ==>
      prp_trp_licensed g g (outer_step acc t)
  with introduce (memP t g /\ prp_trp_licensed g g acc) ==>
                 prp_trp_licensed g g (outer_step acc t)
  with _ . begin
    if List.Tot.mem t.p trans_props then begin
      match term_to_subject t.o with
      | Some y_subj ->
        let zs = find_objects_indexed ig y_subj t.p in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (z_term : rdf_term) ->
            let new_t : triple = { s = t.s; p = t.p; o = z_term } in
            add_triple_unchecked acc2 new_t in
        introduce forall (acc2 : rdf_graph) (z_term : rdf_term).
            (memP z_term zs /\ prp_trp_licensed g g acc2) ==>
            prp_trp_licensed g g (inner_step acc2 z_term)
        with introduce (memP z_term zs /\ prp_trp_licensed g g acc2) ==>
                       prp_trp_licensed g g (inner_step acc2 z_term)
        with _ . begin
          let new_t : triple = { s = t.s; p = t.p; o = z_term } in
          // trans_props provenance: t.p is declared transitive in g
          // (decl stays unnamed -- symps_licensed's own emission-fold
          // proof, section 4, discharges the same shape of fact this
          // way, no explicit `eliminate exists decl` needed).
          List.Tot.Properties.mem_memP t.p trans_props;
          // u2 comes from the sp-index bucket at (y_subj, t.p): the
          // served object z_term names a real bucket triple.
          FStar.List.Tot.Properties.memP_map_elim
            (fun (tt : triple) -> tt.o) z_term
            (bucket_lookup ig.ig_sp (sp_key y_subj t.p));
          eliminate exists (u2 : triple).
              memP u2 (bucket_lookup ig.ig_sp (sp_key y_subj t.p)) /\ u2.o == z_term
          returns prp_trp_derives g new_t
          with _ . begin
            // ig_wf_sp places u2 in the snapshot with u2.s == y_subj,
            // u2.p == t.p; ig.ig_triples == g places it in g itself.
            lemma_term_to_subject_subj_term t.o y_subj;
            assert (subj_term u2.s == t.o);
            assert (new_t == ({ s = t.s; p = t.p; o = u2.o } <: triple))
          end
        end;
        fold_left_inv (prp_trp_licensed g g) inner_step zs acc
      | None -> ()
    end else ()
  end;
  fold_left_inv (prp_trp_licensed g g) outer_step g g;
  assert_norm (owl_rule_transitive_property g ig ==
               List.Tot.fold_left outer_step g g)
#pop-options

// Per-triple corollary.
val theorem_transitive_property_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_transitive_property g ig))
    (ensures  memP t g \/ prp_trp_derives g t)

let theorem_transitive_property_licensed g ig t =
  owl_rule_transitive_property_licensed g ig

// ===================================================================
// 10. scm-eqc2: every `owl_rule_scm_eqc2` emission is licensed.
//
// OWL 2 RL/RDF rules table row scm-eqc2:
//   T(?c1, rdfs:subClassOf, ?c2), T(?c2, rdfs:subClassOf, ?c1)
//     => T(?c1, owl:equivalentClass, ?c2)
// transcribed as OWL.RL.Spec.scm_eqc2_derives -- the converse
// direction of scm-eqc1 (section 5), reached here by a SINGLE fold
// over g whose step carries an index-reading GUARD
// (`find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf`, then
// `existsb` for C among the results) rather than a second inner
// fold, so the parked nested-fold hazard does not apply.
//
// Both premise triples of the row land in g: u1 is the fold-input
// triple t itself (memP t g from the fold hypothesis); u2 is the
// snapshot triple the guard's bucket lookup names, recovered via
// `FStar.List.Tot.Properties.memP_map_elim` over
// `find_objects_indexed`'s own `map (fun t -> t.o)` definition and
// licensed into g by `ig_wf_sp` together with the `ig.ig_triples ==
// g` hypothesis that ties the index back to the fold's own input
// graph -- the index-precedent shape `owl_rule_cls_oneof_sound` in
// OWL.Semantics.Soundness.fst uses for the sibling `rdf:first`/
// `rdf:rest` buckets.
//
// The rule restricts to S_IRI/T_IRI pairs and skips the degenerate
// c_iri = d_iri case (see OWL.Closure.fsti's comment above the
// definition) -- both restrictions only narrow which conclusions are
// asserted, never emit anything the row doesn't license, so the case
// split below carries no extra proof burden.
//
// PROOF-FRIENDLY GUARD RULE (task #36): the engine's guard tests
// bucket membership with the NAMED partial application `term_is_iri
// c_iri` (OWL.Closure.fsti), not an inline closure, and the guard is
// flattened to ONE boolean (`c_iri <> d_iri && existsb ...`). This
// proof mirrors both: the emit_step lambda below is the engine text
// verbatim, and the emission lemma's existsb hypothesis is stated
// over `term_is_iri c_iri` so the `memP_existsb`/`eliminate` chain
// shares the same first-order symbol the engine's fold actually
// calls. `term_is_iri c_iri x = true` unfolds definitionally to
// `rdf_term_eq x (T_IRI c_iri) = true` (a plain, non-recursive `let`,
// so the SMT encoding carries its body as an equation); from there
// `lemma_rdf_term_eq_pins_iri` pins x, exactly as in the WIP draft
// against the older two-`if` engine text.
// ===================================================================

// rdf_term_eq against a fixed T_IRI pins the LHS to that same IRI:
// the T_IRI branch reuses section 4's `lemma_rdf_term_eq_iri`; every
// other constructor makes rdf_term_eq's catch-all arm `false`,
// contradicting the requires.
let lemma_rdf_term_eq_pins_iri (x : rdf_term) (i : wf_iri)
  : Lemma (requires rdf_term_eq x (T_IRI i) == true)
          (ensures x == T_IRI i) =
  match x with
  | T_IRI j -> lemma_rdf_term_eq_iri j i
  | T_BNode _ -> ()
  | T_Literal _ -> ()
  | T_TripleTerm _ _ _ -> ()

// The licensing invariant for this rule, against scm-eqc2's row.
let scm_eqc2_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ scm_eqc2_derives g t)

// The single emission this rule's step can make, isolated into its own
// lemma so the fold's invariant-preservation obligation (below) only
// has to consume its conclusion, not re-derive it inline: u1 is t
// itself (the hypotheses pin t.p/t.s/t.o exactly as the emit_step
// match already narrowed them), u2 is the snapshot triple the guard's
// bucket lookup names, recovered via `memP_map_elim` over
// `find_objects_indexed`'s own `map (fun t -> t.o)` definition and
// licensed into g by `ig_wf_sp` + `ig.ig_triples == g`.
val lemma_scm_eqc2_emission_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple) (c_iri d_iri : wf_iri)
  : Lemma
    (requires
       ig_wf_sp ig /\ ig.ig_triples == g /\ memP t g /\
       t.p == rdfs_subClassOf /\ t.s == S_IRI c_iri /\ t.o == T_IRI d_iri /\
       List.Tot.existsb (term_is_iri c_iri)
         (find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf) == true)
    (ensures
       scm_eqc2_derives g
         ({ s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } <: triple))

#push-options "--z3rlimit 150 --split_queries always"
let lemma_scm_eqc2_emission_licensed g ig t c_iri d_iri =
  lemma_vocab_eqc_agree ();
  let new_t : triple = { s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } in
  let supers_of_d = find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf in
  assert_norm (supers_of_d ==
               List.Tot.map (fun (u : triple) -> u.o)
                 (bucket_lookup ig.ig_sp (sp_key (S_IRI d_iri) rdfs_subClassOf)));
  FStar.List.Tot.Properties.memP_existsb (term_is_iri c_iri) supers_of_d;
  // u1 is t itself: memP t g, t.p == o_rdfs_subClassOf via the vocab
  // bridge, and t.s/t.o are exactly S_IRI c_iri / T_IRI d_iri (hypotheses).
  eliminate exists (x : rdf_term).
      term_is_iri c_iri x = true /\ memP x supers_of_d
  returns scm_eqc2_derives g new_t
  with _ . begin
    // term_is_iri unfolds definitionally: term_is_iri c_iri x ==
    // rdf_term_eq x (T_IRI c_iri).
    assert (rdf_term_eq x (T_IRI c_iri) = true);
    FStar.List.Tot.Properties.memP_map_elim
      (fun (u : triple) -> u.o) x
      (bucket_lookup ig.ig_sp (sp_key (S_IRI d_iri) rdfs_subClassOf));
    // u2 is the bucket triple memP_map_elim names: ig_wf_sp pins its
    // subject/predicate/snapshot-membership off the syntactic memP
    // fact against ig.ig_sp's own sp_key bucket (auto-instantiated by
    // Z3 e-matching, same as owl_rule_cls_oneof_sound's use of
    // ig_wf_sp in OWL.Semantics.Soundness.fst).
    eliminate exists (u2 : triple).
        memP u2 (bucket_lookup ig.ig_sp (sp_key (S_IRI d_iri) rdfs_subClassOf)) /\
        u2.o == x
    returns scm_eqc2_derives g new_t
    with _ . begin
      lemma_rdf_term_eq_pins_iri x c_iri;
      assert (memP u2 ig.ig_triples /\
              u2.s == S_IRI d_iri /\ u2.p == rdfs_subClassOf);
      lemma_subj_term_agree u2.s;
      lemma_subj_term_agree t.s;
      // Row equations: subj_term u2.s == u1.o (both T_IRI d_iri) and
      // u2.o == subj_term u1.s (both T_IRI c_iri, via the existsb hit
      // pinned to x == T_IRI c_iri above).
      assert (subj_term u2.s == t.o);
      assert (u2.o == subj_term t.s);
      assert (new_t == ({ s = t.s; p = o_owl_equivalentClass;
                          o = t.o } <: triple))
    end
  end
#pop-options

val owl_rule_scm_eqc2_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ ig.ig_triples == g)
          (ensures scm_eqc2_licensed g (owl_rule_scm_eqc2 g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_scm_eqc2_licensed g ig =
  lemma_vocab_eqc_agree ();
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        match t.s, t.o with
        | S_IRI c_iri, T_IRI d_iri ->
          if c_iri <> d_iri &&
             List.Tot.existsb (term_is_iri c_iri)
               (find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf)
          then
            let new_t : triple =
              { s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } in
            add_triple_unchecked acc new_t
          else acc
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ scm_eqc2_licensed g acc) ==>
      scm_eqc2_licensed g (emit_step acc t)
  with introduce (memP t g /\ scm_eqc2_licensed g acc) ==>
                 scm_eqc2_licensed g (emit_step acc t)
  with _ . begin
    if t.p = rdfs_subClassOf then
      match t.s, t.o with
      | S_IRI c_iri, T_IRI d_iri ->
        if c_iri <> d_iri &&
           List.Tot.existsb (term_is_iri c_iri)
             (find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf)
        then lemma_scm_eqc2_emission_licensed g ig t c_iri d_iri
        else ()
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (scm_eqc2_licensed g) emit_step g g;
  assert_norm (owl_rule_scm_eqc2 g ig ==
               List.Tot.fold_left emit_step g g)
#pop-options

// Per-triple corollary.
val theorem_scm_eqc2_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_scm_eqc2 g ig))
    (ensures  memP t g \/ scm_eqc2_derives g t)

let theorem_scm_eqc2_licensed g ig t =
  owl_rule_scm_eqc2_licensed g ig
// ===================================================================
// 11. eq-rep-s: every `owl_rule_sameAs_replace_subject` emission is
// licensed. PATTERN-SETTER for the eq-rep family (replace_object and
// replace_predicate follow the same recipe next).
//
// OWL 2 RL/RDF rules table row eq-rep-s:
//   T(?s, owl:sameAs, ?s'), T(?s, ?p, ?o)  =>  T(?s', ?p, ?o)
// transcribed as OWL.RL.Spec.eq_rep_s_derives. #262's outer fold walks
// the deduped snapshot pair list (section 1's `sameas_pairs`); for
// each pair (x, s_prime) the INNER fold walks
// `bucket_lookup ig.ig_subj (subject_to_key x)` -- the ig_subj
// bucket's serving of triples with subject x, keeping the rule off an
// O(k^6) live-graph rescan (the #262 banner on both rules). Tracing a
// served bucket triple back to a real (x P o) triple needs
// `ig_wf_subj` (OWL.Semantics), which unlike `ig_wf_sp` (section 8/9)
// is UNCONDITIONAL for build_indexed -- no separator side condition
// (RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_subj) -- so the
// theorem below takes `ig_wf_subj ig /\ ig.ig_triples == g` as its
// hypothesis, mirroring section 9's (prp-trp) shape exactly, not
// section 8's (eq-trans keeps the row snapshot-relative because it has
// no `ig.ig_triples == g` premise available at its call sites; this
// rule states the row against `g` directly, the same choice prp-trp
// made once `ig.ig_triples == g` was in hand).
//
// PROOF-FRIENDLY GUARD RULE (task #36): the inner fold's emitter is
// the NAMED partial application `sameas_rep_subj_emit s_prime`
// (OWL.Closure.fsti), not an anonymous closure -- this proof mirrors
// that named application on both sides (the local `outer_step` below
// and the introduce-block's `inner_step`), exactly as section 8's
// `sameas_trans_emit x` and section 7's `inverse_of_emit p1_iri
// p2_iri`. This rule's inner fold ALSO carries a boolean guard inside
// the named emitter (`t.p <> owl_sameAs`) -- per the guard-rule's own
// closing note, a plain disequality guard does not itself need naming,
// only the closure wrapping it; the proof mirrors the guard with an
// ordinary `if`/`else` inside the introduce block, case-splitting the
// SAME way `sameas_rep_subj_emit` does.
//
// SPEC-ROW MISMATCH (GR-delta-sensitive, as flagged in the dispatch
// brief): eq_rep_s_derives does NOT exclude u.p == owl:sameAs -- the
// row licenses replacing the subject of a sameAs edge itself, same as
// any other data triple. The engine's guard `t.p <> owl_sameAs` makes
// owl_rule_sameAs_replace_subject emit a STRICT SUBSET of what the row
// licenses (it never re-derives a replaced sameAs edge under this
// rule). That narrowing is sound -- a subset of a licensed set is
// still licensed, which is all this theorem claims -- but it is
// INCOMPLETE relative to the row taken alone; the missing conclusions
// are still reached via eq-sym/eq-trans consuming the original sameAs
// edges, so the closure's overall sameAs completeness is unaffected.
// Flagging per the brief's request, not fixing: the guard's own
// purpose (avoiding a redundant same-shape sameAs re-derivation this
// rule doesn't need to make) is outside this licensing lemma's scope.
// ===================================================================

// The licensing invariant for this rule, against eq-rep-s's row. Same
// 3-arg shape as prp_trp_licensed (section 9): snapshot is
// instantiated at g via the `ig.ig_triples == g` hypothesis, even
// though eq_rep_s_derives is stated against g directly.
let eq_rep_s_licensed (g : rdf_graph) (snapshot : list triple) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ eq_rep_s_derives snapshot t)

val owl_rule_sameAs_replace_subject_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_subj ig /\ ig.ig_triples == g)
          (ensures  eq_rep_s_licensed g g (owl_rule_sameAs_replace_subject g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_sameAs_replace_subject_licensed g ig =
  lemma_sameas_pairs_provenance ig;
  lemma_vocab_sameas_agree ();
  let inv = eq_rep_s_licensed g g in
  // Engine text verbatim -- the inner fold is the shared named
  // application `sameas_rep_subj_emit s_prime`, exactly as
  // owl_rule_sameAs_replace_subject writes it after the closure-
  // identity fix.
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, s_prime) = xy in
      let srcs = bucket_lookup ig.ig_subj (subject_to_key x) in
      List.Tot.fold_left (sameas_rep_subj_emit s_prime) acc srcs in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (memP xy (sameas_pairs ig) /\ inv acc) ==> inv (outer_step acc xy)
  with introduce (memP xy (sameas_pairs ig) /\ inv acc) ==>
                 inv (outer_step acc xy)
  with _ . begin
    let (x, s_prime) = xy in
    let srcs = bucket_lookup ig.ig_subj (subject_to_key x) in
    let inner_step : rdf_graph -> triple -> rdf_graph =
      sameas_rep_subj_emit s_prime in
    introduce forall (acc2 : rdf_graph) (src : triple).
        (memP src srcs /\ inv acc2) ==> inv (inner_step acc2 src)
    with introduce (memP src srcs /\ inv acc2) ==>
                   inv (inner_step acc2 src)
    with _ . begin
      // pairs_licensed names the edge eq_edge behind xy: the
      // (x owl:sameAs s_prime) premise.
      eliminate exists (eq_edge : triple).
          memP eq_edge ig.ig_triples /\ eq_edge.p == owl_sameAs /\
          eq_edge.s == fst xy /\ term_to_subject eq_edge.o == Some (snd xy)
      returns inv (inner_step acc2 src)
      with _ . begin
        lemma_term_to_subject_subj_term eq_edge.o (snd xy);
        // ig_wf_subj places src in the snapshot with src.s == x -- the
        // (x P o) data-triple premise, u := src; ig.ig_triples == g
        // places it in g itself.
        if src.p <> owl_sameAs then begin
          let new_t : triple = { s = s_prime; p = src.p; o = src.o } in
          assert (new_t == ({ s = s_prime; p = src.p; o = src.o } <: triple));
          assert (eq_rep_s_derives g new_t)
        end else ()
      end
    end;
    fold_left_inv inv inner_step srcs acc
  end;
  fold_left_inv inv outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_replace_subject g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))
#pop-options

// Per-triple corollary, the form downstream compositions consume.
val theorem_sameAs_replace_subject_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_subj ig /\ ig.ig_triples == g /\
              memP t (owl_rule_sameAs_replace_subject g ig))
    (ensures  memP t g \/ eq_rep_s_derives g t)

let theorem_sameAs_replace_subject_licensed g ig t =
  owl_rule_sameAs_replace_subject_licensed g ig

// ===================================================================
// 12. eq-rep-o: every `owl_rule_sameAs_replace_object` emission is
// licensed. Second of the eq-rep family, following section 11's
// PATTERN-SETTER recipe.
//
// OWL 2 RL/RDF rules table row eq-rep-o:
//   T(?o, owl:sameAs, ?o'), T(?s, ?p, ?o)  =>  T(?s, ?p, ?o')
// transcribed as OWL.RL.Spec.eq_rep_o_derives. #262's outer fold walks
// the same deduped snapshot pair list as section 11; for each pair
// (x, y) the INNER fold walks `bucket_lookup ig.ig_obj (subject_to_key
// x)` -- the ig_obj bucket's serving of triples whose OBJECT is the
// term x denotes.
//
// ig_obj is keyed by `term_to_key_opt` (RDF.Indexed.fsti), a
// DIFFERENT key function from `subject_to_key` (section 11's ig_subj),
// so this rule needed its own well-formedness predicate: `ig_wf_obj`
// did not exist before this landing. Added, following section 11's
// own precedent exactly:
//   * `term_to_key_opt` rebuilt with `^` instead of the opaque
//     `String.concat "" [...]`, mirroring `subject_to_key`'s own
//     rewrite -- purely a proof-friendliness change, same string
//     values (RDF.Indexed.fsti);
//   * `ig_wf_obj` stated in OWL.Semantics.fst next to `ig_wf_subj`, in
//     the SUBJECT-SHAPED form the engine actually queries with
//     (`bucket_lookup ig.ig_obj (subject_to_key s)`), not the fully
//     generic term-keyed form -- narrower, but exactly what this rule
//     needs, per the dispatch brief's "acceptable for this rule" call;
//   * the weak membership lemma `lemma_build_indexed_wf_obj_weak`
//     added to OWL.Semantics.MemLemmas.fst, mirroring
//     `lemma_build_indexed_wf_subj_weak` verbatim (both key functions
//     return `option string`, so `tree_ok`/`lemma_tree_ok_lookup`
//     apply unchanged);
//   * the strong discharge `lemma_build_indexed_wf_obj` added to
//     RDF.Indexed.KeyInjectivity.fst, needing `term_to_key_opt`'s OWN
//     injectivity lemma (`lemma_term_to_key_opt_injective` -- the same
//     two-char-tag argument as `lemma_subject_to_key_injective`, now
//     available because of the `^` rewrite) plus a one-line bridge
//     lemma (`lemma_subject_to_key_eq_term_to_key_opt`) connecting the
//     two key functions' shared I_/B_ shape. UNCONDITIONAL, like
//     `ig_wf_subj` -- no separator side condition, for the same reason
//     (the two-char tag alone separates the constructors).
//
// Both premise triples of the row land in g: eq is the sameAs edge
// the pair names (`lemma_sameas_pairs_provenance`, section 1); u is
// the bucket triple the inner fold consumes, licensed into g by
// `ig_wf_obj` together with `ig.ig_triples == g` -- the SAME
// e-matching-triggered shape section 11 uses for `ig_wf_subj`
// (`memP src srcs` where `srcs` is syntactically the bucket-lookup
// term `ig_wf_obj`'s forall quantifies over, so Z3 auto-instantiates
// it without an explicit `assert`).
//
// PROOF-FRIENDLY GUARD RULE (task #36): the inner fold's emitter is
// the NAMED partial application `sameas_rep_obj_emit y_term`
// (OWL.Closure.fsti), not an anonymous closure -- mirrors section 11's
// `sameas_rep_subj_emit s_prime` naming exactly. This rule's inner
// fold also carries the same `t.p <> owl_sameAs` guard, named inside
// `sameas_rep_obj_emit` the same way `sameas_rep_subj_emit` carries
// it; the proof mirrors it with an ordinary `if`/`else`.
//
// SPEC-ROW MISMATCH (GR-delta-sensitive, same shape as section 11's
// finding): eq_rep_o_derives does NOT exclude u.p == owl:sameAs -- the
// row licenses replacing the object of a sameAs edge itself. The
// engine's guard `src.p <> owl_sameAs` (inside `sameas_rep_obj_emit`)
// makes owl_rule_sameAs_replace_object emit a STRICT SUBSET of what
// the row licenses, for the same reason section 11 flags: sound (a
// subset of a licensed set is still licensed) but INCOMPLETE relative
// to the row alone, with the missing conclusions reached downstream
// via eq-sym/eq-trans. Flagging per the brief's request, not fixing.
// ===================================================================

// The licensing invariant for this rule, against eq-rep-o's row. Same
// 3-arg shape as eq_rep_s_licensed (section 11).
let eq_rep_o_licensed (g : rdf_graph) (snapshot : list triple) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ eq_rep_o_derives snapshot t)

val owl_rule_sameAs_replace_object_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_obj ig /\ ig.ig_triples == g)
          (ensures  eq_rep_o_licensed g g (owl_rule_sameAs_replace_object g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_sameAs_replace_object_licensed g ig =
  lemma_sameas_pairs_provenance ig;
  lemma_vocab_sameas_agree ();
  let inv = eq_rep_o_licensed g g in
  // Engine text verbatim -- the inner fold is the shared named
  // application `sameas_rep_obj_emit y_term`, exactly as
  // owl_rule_sameAs_replace_object writes it after the closure-hoist.
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let y_term = subject_to_term y in
      let srcs = bucket_lookup ig.ig_obj (subject_to_key x) in
      List.Tot.fold_left (sameas_rep_obj_emit y_term) acc srcs in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (memP xy (sameas_pairs ig) /\ inv acc) ==> inv (outer_step acc xy)
  with introduce (memP xy (sameas_pairs ig) /\ inv acc) ==>
                 inv (outer_step acc xy)
  with _ . begin
    let (x, y) = xy in
    let y_term = subject_to_term y in
    let srcs = bucket_lookup ig.ig_obj (subject_to_key x) in
    let inner_step : rdf_graph -> triple -> rdf_graph =
      sameas_rep_obj_emit y_term in
    introduce forall (acc2 : rdf_graph) (src : triple).
        (memP src srcs /\ inv acc2) ==> inv (inner_step acc2 src)
    with introduce (memP src srcs /\ inv acc2) ==>
                   inv (inner_step acc2 src)
    with _ . begin
      // pairs_licensed names the edge eq_edge behind xy: the
      // (x owl:sameAs y) premise, x == eq_edge.s (the sameAs edge's
      // subject -- the term being replaced, in OBJECT position for
      // this rule), y the sameAs partner.
      eliminate exists (eq_edge : triple).
          memP eq_edge ig.ig_triples /\ eq_edge.p == owl_sameAs /\
          eq_edge.s == fst xy /\ term_to_subject eq_edge.o == Some (snd xy)
      returns inv (inner_step acc2 src)
      with _ . begin
        lemma_term_to_subject_subj_term eq_edge.o (snd xy);
        // ig_wf_obj places src in the snapshot with src.o ==
        // subject_to_term x -- the (s P o) data-triple premise with
        // o == x, u := src; ig.ig_triples == g places it in g itself.
        lemma_subj_term_agree eq_edge.s;
        lemma_subj_term_agree y;
        if src.p <> owl_sameAs then begin
          let new_t : triple = { s = src.s; p = src.p; o = y_term } in
          assert (new_t == ({ s = src.s; p = src.p; o = y_term } <: triple));
          assert (eq_rep_o_derives g new_t)
        end else ()
      end
    end;
    fold_left_inv inv inner_step srcs acc
  end;
  fold_left_inv inv outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_replace_object g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))
#pop-options

// Per-triple corollary, the form downstream compositions consume.
val theorem_sameAs_replace_object_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_obj ig /\ ig.ig_triples == g /\
              memP t (owl_rule_sameAs_replace_object g ig))
    (ensures  memP t g \/ eq_rep_o_derives g t)

let theorem_sameAs_replace_object_licensed g ig t =
  owl_rule_sameAs_replace_object_licensed g ig

// ===================================================================
// 13. eq-rep-p: every `owl_rule_sameAs_replace_predicate` emission is
// licensed. Third of the eq-rep family, following section 11/12's
// PATTERN-SETTER recipe.
//
// OWL 2 RL/RDF rules table row eq-rep-p:
//   T(?p, owl:sameAs, ?p'), T(?s, ?p, ?o)  =>  T(?s, ?p', ?o)
// transcribed as OWL.RL.Spec.eq_rep_p_derives. #262's outer fold walks
// the same deduped snapshot pair list, restricted here to S_IRI/S_IRI
// pairs (predicates are never blank-node or literal, so any other
// pair shape is a no-op, same restriction the engine's
// `is_owl_metapredicate` guard sits alongside); the inner fold walks
// `bucket_lookup ig.ig_pred p_iri` -- the ig_pred bucket's serving of
// triples with predicate p_iri. `ig_wf_pred` is ALREADY fully
// discharged (OWL.Semantics.MemLemmas.lemma_build_indexed_wf_pred, no
// side condition -- bucket_key_pred t = Some t.p, no composite-key
// decomposition), so this rule needed no new well-formedness
// machinery, unlike section 12's `ig_wf_obj`. The theorem below takes
// `ig_wf_pred ig /\ ig.ig_triples == g` as its hypothesis -- the
// simplest of the eq-rep family's three.
//
// Both premise triples of the row land in g: eq is the sameAs edge
// the pair names; u is the bucket triple the inner fold consumes,
// licensed into g by `ig_wf_pred` together with `ig.ig_triples == g`,
// via the same e-matching-triggered shape sections 11/12 use.
//
// PROOF-FRIENDLY GUARD RULE (task #36): the inner fold's emitter is
// the NAMED partial application `sameas_rep_pred_emit p_prime_iri`
// (OWL.Closure.fsti), not an anonymous closure -- mirrors sections
// 11/12's inner-fold naming exactly. Unlike those two, this emitter
// carries NO boolean guard of its own (every bucket triple is
// rewritten unconditionally) -- the only guard in this rule is the
// OUTER `is_owl_metapredicate p_iri` check, which the proof mirrors
// with the same `if`/`else` the engine's outer step uses.
//
// SPEC-ROW MISMATCH (GR-delta-sensitive, same shape as sections 11/
// 12's findings): eq_rep_p_derives places NO restriction on p beyond
// it being an IRI paired sameAs-with another IRI p' -- the row
// licenses replacing ANY predicate this way, including
// owl:sameAs/owl:inverseOf/owl:equivalentClass/owl:equivalentProperty
// themselves. The engine's `is_owl_metapredicate p_iri` guard (used
// to block re-emitting a no-op-shaped triple already present) makes
// owl_rule_sameAs_replace_predicate emit a STRICT SUBSET of what the
// row licenses for those four reserved predicates. Sound (a subset of
// a licensed set is still licensed) but INCOMPLETE relative to the
// row taken alone; flagging per the brief's request, not fixing --
// the guard's own purpose (avoiding redundant re-derivation of an
// already-present schema triple) is outside this licensing lemma's
// scope, same as sections 11/12's guard notes.
// ===================================================================

// The licensing invariant for this rule, against eq-rep-p's row. Same
// 3-arg shape as eq_rep_s_licensed / eq_rep_o_licensed.
let eq_rep_p_licensed (g : rdf_graph) (snapshot : list triple) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ eq_rep_p_derives snapshot t)

val owl_rule_sameAs_replace_predicate_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_pred ig /\ ig.ig_triples == g)
          (ensures  eq_rep_p_licensed g g (owl_rule_sameAs_replace_predicate g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_sameAs_replace_predicate_licensed g ig =
  lemma_sameas_pairs_provenance ig;
  lemma_vocab_sameas_agree ();
  let inv = eq_rep_p_licensed g g in
  // Engine text verbatim -- the inner fold is the shared named
  // application `sameas_rep_pred_emit p_prime_iri`, exactly as
  // owl_rule_sameAs_replace_predicate writes it after the
  // closure-hoist.
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      match xy with
      | (S_IRI p_iri, S_IRI p_prime_iri) ->
        if is_owl_metapredicate p_iri then acc
        else
          let srcs = bucket_lookup ig.ig_pred p_iri in
          List.Tot.fold_left (sameas_rep_pred_emit p_prime_iri) acc srcs
      | _ -> acc in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (memP xy (sameas_pairs ig) /\ inv acc) ==> inv (outer_step acc xy)
  with introduce (memP xy (sameas_pairs ig) /\ inv acc) ==>
                 inv (outer_step acc xy)
  with _ . begin
    match xy with
    | (S_IRI p_iri, S_IRI p_prime_iri) ->
      if is_owl_metapredicate p_iri then ()
      else begin
        let srcs = bucket_lookup ig.ig_pred p_iri in
        let inner_step : rdf_graph -> triple -> rdf_graph =
          sameas_rep_pred_emit p_prime_iri in
        introduce forall (acc2 : rdf_graph) (src : triple).
            (memP src srcs /\ inv acc2) ==> inv (inner_step acc2 src)
        with introduce (memP src srcs /\ inv acc2) ==>
                       inv (inner_step acc2 src)
        with _ . begin
          // pairs_licensed names the edge eq_edge behind xy: the
          // (S_IRI p_iri owl:sameAs S_IRI p_prime_iri) premise.
          eliminate exists (eq_edge : triple).
              memP eq_edge ig.ig_triples /\ eq_edge.p == owl_sameAs /\
              eq_edge.s == fst xy /\ term_to_subject eq_edge.o == Some (snd xy)
          returns inv (inner_step acc2 src)
          with _ . begin
            lemma_term_to_subject_subj_term eq_edge.o (snd xy);
            lemma_subj_term_agree (S_IRI p_prime_iri);
            // ig_wf_pred places src in the snapshot with src.p ==
            // p_iri -- the (s P o) data-triple premise, u := src;
            // ig.ig_triples == g places it in g itself.
            let new_t : triple = { s = src.s; p = p_prime_iri; o = src.o } in
            assert (new_t == ({ s = src.s; p = p_prime_iri; o = src.o } <: triple));
            assert (eq_rep_p_derives g new_t)
          end
        end;
        fold_left_inv inv inner_step srcs acc
      end
    | _ -> ()
  end;
  fold_left_inv inv outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_replace_predicate g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))
#pop-options

// Per-triple corollary, the form downstream compositions consume.
val theorem_sameAs_replace_predicate_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_pred ig /\ ig.ig_triples == g /\
              memP t (owl_rule_sameAs_replace_predicate g ig))
    (ensures  memP t g \/ eq_rep_p_derives g t)

let theorem_sameAs_replace_predicate_licensed g ig t =
  owl_rule_sameAs_replace_predicate_licensed g ig

// ===================================================================
// 14. scm-eqp2: every `owl_rule_scm_eqp2` emission is licensed.
//
// OWL 2 RL/RDF rules table row scm-eqp2:
//   T(?p1, rdfs:subPropertyOf, ?p2), T(?p2, rdfs:subPropertyOf, ?p1)
//     => T(?p1, owl:equivalentProperty, ?p2)
// transcribed as OWL.RL.Spec.scm_eqp2_derives -- the property mirror
// of scm-eqc2 (section 10), reached here by the SAME single-fold-
// plus-index-guard shape: `find_objects_indexed ig (S_IRI q_iri)
// rdfs_subPropertyOf`, then `existsb` for P among the results.
//
// Both premise triples of the row land in g: u1 is the fold-input
// triple t itself (memP t g from the fold hypothesis); u2 is the
// snapshot triple the guard's bucket lookup names, recovered via
// `FStar.List.Tot.Properties.memP_map_elim` over
// `find_objects_indexed`'s own `map (fun t -> t.o)` definition and
// licensed into g by `ig_wf_sp` together with the `ig.ig_triples ==
// g` hypothesis -- exactly section 10's chain, with
// rdfs_subPropertyOf/owl_equivalentProperty in place of
// rdfs_subClassOf/owl_equivalentClass.
//
// The rule restricts to S_IRI/T_IRI pairs and skips the degenerate
// p_iri = q_iri case (property IRIs are never anonymous, unlike
// classes) -- both restrictions only narrow which conclusions are
// asserted, never emit anything the row doesn't license, so the case
// split below carries no extra proof burden, same as section 10.
//
// PROOF-FRIENDLY GUARD RULE (task #36): the engine's guard, before
// this landing, tested bucket membership with an INLINE closure
// inside TWO nested conditionals (`if p_iri = q_iri then acc else let
// supers = ... in if existsb (fun x -> rdf_term_eq x (T_IRI p_iri))
// supers then ... else acc`) -- the exact shape scm-eqc2 carried
// before its own 2026-08-05 flatten (section 10's banner). Applying
// the SAME treatment here: the guard is now the NAMED partial
// application `term_is_iri p_iri` (OWL.Closure.fsti), flattened to
// ONE boolean (`p_iri <> q_iri && existsb ...`). Semantics unchanged
// on both counts. This proof mirrors both: the emit_step lambda below
// is the engine text verbatim, and the emission lemma's existsb
// hypothesis is stated over `term_is_iri p_iri` so the
// `memP_existsb`/`eliminate` chain shares the same first-order symbol
// the engine's fold actually calls -- `lemma_rdf_term_eq_pins_iri`
// (section 10, reused verbatim: it is stated generically over any
// `wf_iri`, not scm-eqc2-specific) pins the existsb witness the same
// way.
// ===================================================================

// The licensing invariant for this rule, against scm-eqp2's row.
let scm_eqp2_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ scm_eqp2_derives g t)

// The single emission this rule's step can make -- section 10's
// lemma_scm_eqc2_emission_licensed, with rdfs_subPropertyOf /
// owl_equivalentProperty in place of rdfs_subClassOf /
// owl_equivalentClass.
val lemma_scm_eqp2_emission_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple) (p_iri q_iri : wf_iri)
  : Lemma
    (requires
       ig_wf_sp ig /\ ig.ig_triples == g /\ memP t g /\
       t.p == rdfs_subPropertyOf /\ t.s == S_IRI p_iri /\ t.o == T_IRI q_iri /\
       List.Tot.existsb (term_is_iri p_iri)
         (find_objects_indexed ig (S_IRI q_iri) rdfs_subPropertyOf) == true)
    (ensures
       scm_eqp2_derives g
         ({ s = S_IRI p_iri; p = owl_equivalentProperty; o = T_IRI q_iri } <: triple))

#push-options "--z3rlimit 150 --split_queries always"
let lemma_scm_eqp2_emission_licensed g ig t p_iri q_iri =
  lemma_vocab_eqp_agree ();
  let new_t : triple = { s = S_IRI p_iri; p = owl_equivalentProperty; o = T_IRI q_iri } in
  let supers_of_q = find_objects_indexed ig (S_IRI q_iri) rdfs_subPropertyOf in
  assert_norm (supers_of_q ==
               List.Tot.map (fun (u : triple) -> u.o)
                 (bucket_lookup ig.ig_sp (sp_key (S_IRI q_iri) rdfs_subPropertyOf)));
  FStar.List.Tot.Properties.memP_existsb (term_is_iri p_iri) supers_of_q;
  // u1 is t itself: memP t g, t.p == o_rdfs_subPropertyOf via the
  // vocab bridge, and t.s/t.o are exactly S_IRI p_iri / T_IRI q_iri
  // (hypotheses).
  eliminate exists (x : rdf_term).
      term_is_iri p_iri x = true /\ memP x supers_of_q
  returns scm_eqp2_derives g new_t
  with _ . begin
    // term_is_iri unfolds definitionally: term_is_iri p_iri x ==
    // rdf_term_eq x (T_IRI p_iri).
    assert (rdf_term_eq x (T_IRI p_iri) = true);
    FStar.List.Tot.Properties.memP_map_elim
      (fun (u : triple) -> u.o) x
      (bucket_lookup ig.ig_sp (sp_key (S_IRI q_iri) rdfs_subPropertyOf));
    // u2 is the bucket triple memP_map_elim names: ig_wf_sp pins its
    // subject/predicate/snapshot-membership off the syntactic memP
    // fact against ig.ig_sp's own sp_key bucket (auto-instantiated by
    // Z3 e-matching, same as section 10's use of ig_wf_sp).
    eliminate exists (u2 : triple).
        memP u2 (bucket_lookup ig.ig_sp (sp_key (S_IRI q_iri) rdfs_subPropertyOf)) /\
        u2.o == x
    returns scm_eqp2_derives g new_t
    with _ . begin
      lemma_rdf_term_eq_pins_iri x p_iri;
      assert (memP u2 ig.ig_triples /\
              u2.s == S_IRI q_iri /\ u2.p == rdfs_subPropertyOf);
      lemma_subj_term_agree u2.s;
      lemma_subj_term_agree t.s;
      // Row equations: subj_term u2.s == u1.o (both T_IRI q_iri) and
      // u2.o == subj_term u1.s (both T_IRI p_iri, via the existsb hit
      // pinned to x == T_IRI p_iri above).
      assert (subj_term u2.s == t.o);
      assert (u2.o == subj_term t.s);
      assert (new_t == ({ s = t.s; p = o_owl_equivalentProperty;
                          o = t.o } <: triple))
    end
  end
#pop-options

val owl_rule_scm_eqp2_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ ig.ig_triples == g)
          (ensures scm_eqp2_licensed g (owl_rule_scm_eqp2 g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_scm_eqp2_licensed g ig =
  lemma_vocab_eqp_agree ();
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match t.s, t.o with
        | S_IRI p_iri, T_IRI q_iri ->
          if p_iri <> q_iri &&
             List.Tot.existsb (term_is_iri p_iri)
               (find_objects_indexed ig (S_IRI q_iri) rdfs_subPropertyOf)
          then
            let new_t : triple =
              { s = S_IRI p_iri; p = owl_equivalentProperty; o = T_IRI q_iri } in
            add_triple_unchecked acc new_t
          else acc
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ scm_eqp2_licensed g acc) ==>
      scm_eqp2_licensed g (emit_step acc t)
  with introduce (memP t g /\ scm_eqp2_licensed g acc) ==>
                 scm_eqp2_licensed g (emit_step acc t)
  with _ . begin
    if t.p = rdfs_subPropertyOf then
      match t.s, t.o with
      | S_IRI p_iri, T_IRI q_iri ->
        if p_iri <> q_iri &&
           List.Tot.existsb (term_is_iri p_iri)
             (find_objects_indexed ig (S_IRI q_iri) rdfs_subPropertyOf)
        then lemma_scm_eqp2_emission_licensed g ig t p_iri q_iri
        else ()
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (scm_eqp2_licensed g) emit_step g g;
  assert_norm (owl_rule_scm_eqp2 g ig ==
               List.Tot.fold_left emit_step g g)
#pop-options

// Per-triple corollary.
val theorem_scm_eqp2_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_scm_eqp2 g ig))
    (ensures  memP t g \/ scm_eqp2_derives g t)

let theorem_scm_eqp2_licensed g ig t =
  owl_rule_scm_eqp2_licensed g ig

// ===================================================================
// 15. scm-dom2 (dispatched row) / scm-dom1 (row the engine function
// ACTUALLY realizes): every `owl_rule_scm_dom2` emission is licensed.
//
// ENGINE NAME VS ROW FINDING (recorded per the dispatch brief): the
// W3C OWL 2 RL/RDF Table 8 rows are
//   scm-dom1 | T(?p, rdfs:domain, ?c1)  T(?c1, rdfs:subClassOf, ?c2)
//             | T(?p, rdfs:domain, ?c2)
//   scm-dom2 | T(?p2, rdfs:domain, ?c)  T(?p1, rdfs:subPropertyOf, ?p2)
//             | T(?p1, rdfs:domain, ?c)
// -- transcribed VERBATIM as `scm_dom1_derives` / `scm_dom2_derives`,
// OWL.RL.Spec.fst lines 1369-1381. The engine function this module was
// asked to license, `OWL.Closure.fsti`'s `owl_rule_scm_dom2` (lines
// 3612-3640), computes: for every domain triple (?p, rdfs:domain, ?c1)
// in g, walk `find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf`
// (?c1's NAMED superclasses) and emit (?p, rdfs:domain, ?c2) per
// superclass. That is scm-dom1's premise pair (domain + subClassOf on
// the DOMAIN CLASS), not scm-dom2's (domain + subPropertyOf on the
// PROPERTY) -- the engine's own banner comment above the definition
// ("Mirrors rdfs9 but for property-domain instead of subject-class")
// independently confirms it is the subClassOf-lifting rule. Attempting
// `scm_dom2_licensed` against this function is FALSE in general: take
// g = [(p, rdfs:domain, c1); (c1, rdfs:subClassOf, c2)] with NO
// rdfs:subPropertyOf triple anywhere -- the engine still emits
// (p, rdfs:domain, c2), but `scm_dom2_derives g (p, rdfs:domain, c2)`
// has no witness (no `sub` triple exists), so the emission is neither
// already in g nor licensed by the scm-dom2 row. No lemma is stated
// against `scm_dom2_derives` for this function; per Iron Rule #10
// (no `--lax`/`--admit_smt_queries`) a false theorem cannot be forced
// through, and per the eq-rep-o/eq-rep-p precedent (sections 12-13)
// the honest move is to prove what the function ACTUALLY computes and
// flag the naming mismatch in-file, not to silently rename the engine
// function (out of scope for a licensing-lemma landing; a rename
// ripples through the fixpoint pipeline call site at
// OWL.Closure.fsti:5463 and every build-list consumer).
//
// The row `owl_rule_scm_dom2` DOES realize, scm-dom1, is licensed
// below as `scm_dom1_licensed`, using section 9's (prp-trp) TWO-LEVEL
// nested-fold recipe: the engine text is a genuine outer/inner fold
// pair (outer over g on `t.p = rdfs_domain`, inner over
// `find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf`), not a
// single-fold-plus-existsb-guard shape like scm-eqc2/scm-eqp2
// (sections 10/14) -- there is no reciprocal check here, every named
// superclass found is emitted. `ig_wf_sp ig /\ ig.ig_triples == g`
// places the inner fold's bucket witness (the `sub` premise triple)
// back into g, exactly as section 9's `u2`.
//
// The engine's own BNODE-POLLUTION GUARD (banner above the
// definition, OWL.Closure.fsti:3615-3620) restricts `c2_term` to
// T_IRI -- only named superclasses propagate. This only NARROWS what
// is emitted relative to the row (a superclass could in principle be
// a bnode restriction the row does not exclude), so the case split
// below carries no extra proof burden, same as sections 10/14's own
// S_IRI/T_IRI restriction note.
//
// The true scm-dom2 row (subPropertyOf-based domain lifting) is
// ALREADY realized in the engine, just under a different name:
// `owl_rule_subprop_domain_range` (OWL.Closure.fsti:3684-3705, "Group
// B: rdfsext domain/range through subPropertyOf"), which folds over
// g on `t.p = rdfs_subPropertyOf` and, for the linked property p2,
// emits both a domain and a range conclusion from p2's declared
// domain/range set -- exactly scm-dom2's and scm-rng2's premise shape
// in one combined function. It is not licensed by this landing (out
// of scope: a different engine function from the two named in the
// dispatch brief); flagging its existence here so a future session
// does not re-derive this finding from scratch.
// ===================================================================

let lemma_vocab_dom_agree ()
  : Lemma (RDFS.Closure.rdfs_domain == OWL.RL.Spec.o_rdfs_domain /\
           RDFS.Closure.rdfs_subClassOf == OWL.RL.Spec.o_rdfs_subClassOf) = ()

// The licensing invariant against scm-dom1's row -- the row
// `owl_rule_scm_dom2` actually realizes; see the ENGINE NAME VS ROW
// finding above.
let scm_dom1_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ scm_dom1_derives g t)

val owl_rule_scm_dom2_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ ig.ig_triples == g)
          (ensures  scm_dom1_licensed g (owl_rule_scm_dom2 g ig))

#push-options "--z3rlimit 150 --split_queries always"
let owl_rule_scm_dom2_licensed g ig =
  lemma_vocab_dom_agree ();
  // Engine text verbatim (OWL.Closure.fsti:3621-3640).
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_domain then
        match t.o with
        | T_IRI c1_iri ->
          let supers = find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
              match c2_term with
              | T_IRI _ ->
                let new_t : triple = { s = t.s; p = rdfs_domain; o = c2_term } in
                add_triple_unchecked acc2 new_t
              | _ -> acc2)
            acc
            supers
        | _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ scm_dom1_licensed g acc) ==>
      scm_dom1_licensed g (outer_step acc t)
  with introduce (memP t g /\ scm_dom1_licensed g acc) ==>
                 scm_dom1_licensed g (outer_step acc t)
  with _ . begin
    if t.p = rdfs_domain then
      match t.o with
      | T_IRI c1_iri ->
        let supers = find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
            match c2_term with
            | T_IRI _ ->
              let new_t : triple = { s = t.s; p = rdfs_domain; o = c2_term } in
              add_triple_unchecked acc2 new_t
            | _ -> acc2 in
        introduce forall (acc2 : rdf_graph) (c2_term : rdf_term).
            (memP c2_term supers /\ scm_dom1_licensed g acc2) ==>
            scm_dom1_licensed g (inner_step acc2 c2_term)
        with introduce (memP c2_term supers /\ scm_dom1_licensed g acc2) ==>
                       scm_dom1_licensed g (inner_step acc2 c2_term)
        with _ . begin
          match c2_term with
          | T_IRI d_iri ->
            let new_t : triple = { s = t.s; p = rdfs_domain; o = c2_term } in
            // u2 comes from the sp-index bucket at (S_IRI c1_iri,
            // rdfs_subClassOf): the served object c2_term names a real
            // bucket triple (section 9/10's memP_map_elim recipe).
            assert_norm (supers ==
                         List.Tot.map (fun (u : triple) -> u.o)
                           (bucket_lookup ig.ig_sp
                              (sp_key (S_IRI c1_iri) rdfs_subClassOf)));
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c2_term
              (bucket_lookup ig.ig_sp (sp_key (S_IRI c1_iri) rdfs_subClassOf));
            eliminate exists (u2 : triple).
                memP u2 (bucket_lookup ig.ig_sp
                           (sp_key (S_IRI c1_iri) rdfs_subClassOf)) /\
                u2.o == c2_term
            returns scm_dom1_derives g new_t
            with _ . begin
              // ig_wf_sp places u2 in the snapshot with u2.s ==
              // S_IRI c1_iri, u2.p == rdfs_subClassOf; ig.ig_triples ==
              // g places it in g itself (auto-instantiated by Z3
              // e-matching, same as sections 9/10/14).
              assert (memP u2 ig.ig_triples /\
                      u2.s == S_IRI c1_iri /\ u2.p == rdfs_subClassOf);
              lemma_subj_term_agree u2.s;
              // Row equations: subj_term u2.s == dom.o (both
              // T_IRI c1_iri, via the T_IRI match on t.o) and the
              // conclusion's object is u2.o (== c2_term == d_iri).
              assert (subj_term u2.s == t.o);
              assert (new_t == ({ s = t.s; p = o_rdfs_domain;
                                  o = u2.o } <: triple))
            end
          | _ -> ()
        end;
        fold_left_inv (scm_dom1_licensed g) inner_step supers acc
      | _ -> ()
    else ()
  end;
  fold_left_inv (scm_dom1_licensed g) outer_step g g;
  assert_norm (owl_rule_scm_dom2 g ig ==
               List.Tot.fold_left outer_step g g)
#pop-options

// Per-triple corollary.
val theorem_scm_dom2_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_scm_dom2 g ig))
    (ensures  memP t g \/ scm_dom1_derives g t)

let theorem_scm_dom2_licensed g ig t =
  owl_rule_scm_dom2_licensed g ig

// ===================================================================
// 16. scm-rng2 (dispatched row) / scm-rng1 (row the engine function
// ACTUALLY realizes): every `owl_rule_scm_rng2` emission is licensed.
// Range mirror of section 15 -- same ENGINE NAME VS ROW finding, same
// two-level-fold recipe, rdfs:range/rdfs_range in place of
// rdfs:domain/rdfs_domain throughout.
//
// W3C Table 8:
//   scm-rng1 | T(?p, rdfs:range, ?c1)  T(?c1, rdfs:subClassOf, ?c2)
//             | T(?p, rdfs:range, ?c2)
//   scm-rng2 | T(?p2, rdfs:range, ?c)  T(?p1, rdfs:subPropertyOf, ?p2)
//             | T(?p1, rdfs:range, ?c)
// -- transcribed as `scm_rng1_derives` / `scm_rng2_derives`,
// OWL.RL.Spec.fst lines 1391-1403. `owl_rule_scm_rng2` (OWL.Closure.
// fsti:3645-3664) computes the SAME subClassOf-lifting shape as
// section 15's function, on rdfs:range instead of rdfs:domain -- it
// is scm-rng1, not scm-rng2, for exactly the reason section 15 gives
// (same counterexample construction with rdfs:range substituted for
// rdfs:domain). No lemma is stated against `scm_rng2_derives` for the
// same false-in-general reason. The true scm-rng2 row is the range
// half of `owl_rule_subprop_domain_range` (section 15's closing note).
// ===================================================================

let lemma_vocab_rng_agree ()
  : Lemma (RDFS.Closure.rdfs_range == OWL.RL.Spec.o_rdfs_range /\
           RDFS.Closure.rdfs_subClassOf == OWL.RL.Spec.o_rdfs_subClassOf) = ()

// The licensing invariant against scm-rng1's row -- the row
// `owl_rule_scm_rng2` actually realizes; see section 15's finding.
let scm_rng1_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ scm_rng1_derives g t)

val owl_rule_scm_rng2_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ ig.ig_triples == g)
          (ensures  scm_rng1_licensed g (owl_rule_scm_rng2 g ig))

#push-options "--z3rlimit 150 --split_queries always"
let owl_rule_scm_rng2_licensed g ig =
  lemma_vocab_rng_agree ();
  // Engine text verbatim (OWL.Closure.fsti:3645-3664).
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_range then
        match t.o with
        | T_IRI c1_iri ->
          let supers = find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
              match c2_term with
              | T_IRI _ ->
                let new_t : triple = { s = t.s; p = rdfs_range; o = c2_term } in
                add_triple_unchecked acc2 new_t
              | _ -> acc2)
            acc
            supers
        | _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ scm_rng1_licensed g acc) ==>
      scm_rng1_licensed g (outer_step acc t)
  with introduce (memP t g /\ scm_rng1_licensed g acc) ==>
                 scm_rng1_licensed g (outer_step acc t)
  with _ . begin
    if t.p = rdfs_range then
      match t.o with
      | T_IRI c1_iri ->
        let supers = find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
            match c2_term with
            | T_IRI _ ->
              let new_t : triple = { s = t.s; p = rdfs_range; o = c2_term } in
              add_triple_unchecked acc2 new_t
            | _ -> acc2 in
        introduce forall (acc2 : rdf_graph) (c2_term : rdf_term).
            (memP c2_term supers /\ scm_rng1_licensed g acc2) ==>
            scm_rng1_licensed g (inner_step acc2 c2_term)
        with introduce (memP c2_term supers /\ scm_rng1_licensed g acc2) ==>
                       scm_rng1_licensed g (inner_step acc2 c2_term)
        with _ . begin
          match c2_term with
          | T_IRI d_iri ->
            let new_t : triple = { s = t.s; p = rdfs_range; o = c2_term } in
            assert_norm (supers ==
                         List.Tot.map (fun (u : triple) -> u.o)
                           (bucket_lookup ig.ig_sp
                              (sp_key (S_IRI c1_iri) rdfs_subClassOf)));
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c2_term
              (bucket_lookup ig.ig_sp (sp_key (S_IRI c1_iri) rdfs_subClassOf));
            eliminate exists (u2 : triple).
                memP u2 (bucket_lookup ig.ig_sp
                           (sp_key (S_IRI c1_iri) rdfs_subClassOf)) /\
                u2.o == c2_term
            returns scm_rng1_derives g new_t
            with _ . begin
              assert (memP u2 ig.ig_triples /\
                      u2.s == S_IRI c1_iri /\ u2.p == rdfs_subClassOf);
              lemma_subj_term_agree u2.s;
              assert (subj_term u2.s == t.o);
              assert (new_t == ({ s = t.s; p = o_rdfs_range;
                                  o = u2.o } <: triple))
            end
          | _ -> ()
        end;
        fold_left_inv (scm_rng1_licensed g) inner_step supers acc
      | _ -> ()
    else ()
  end;
  fold_left_inv (scm_rng1_licensed g) outer_step g g;
  assert_norm (owl_rule_scm_rng2 g ig ==
               List.Tot.fold_left outer_step g g)
#pop-options

// Per-triple corollary.
val theorem_scm_rng2_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_scm_rng2 g ig))
    (ensures  memP t g \/ scm_rng1_derives g t)

let theorem_scm_rng2_licensed g ig t =
  owl_rule_scm_rng2_licensed g ig
// ===================================================================
// 17. scm-dom2 / scm-rng2 (the rows this function ACTUALLY realizes):
// every `owl_rule_subprop_domain_range` emission is licensed.
//
// Sections 15/16 found that the engine functions NAMED `owl_rule_
// scm_dom2` / `owl_rule_scm_rng2` in fact realize scm-dom1/scm-rng1
// (subClassOf-lifting), and flagged that the TRUE scm-dom2/scm-rng2
// row (subPropertyOf-lifting) is realized elsewhere, under a THIRD
// name: `owl_rule_subprop_domain_range` (OWL.Closure.fsti:3684-3715,
// "Group B: rdfsext domain/range through subPropertyOf"). This
// section licenses that function against the two rows it actually
// computes.
//
// W3C Table 8, verbatim:
//   scm-dom2 | T(?p2, rdfs:domain, ?c)  T(?p1, rdfs:subPropertyOf, ?p2)
//             | T(?p1, rdfs:domain, ?c)
//   scm-rng2 | T(?p2, rdfs:range, ?c)  T(?p1, rdfs:subPropertyOf, ?p2)
//             | T(?p1, rdfs:range, ?c)
// -- transcribed as `scm_dom2_derives` / `scm_rng2_derives`,
// OWL.RL.Spec.fst lines 1376-1381 / 1398-1403.
//
// The engine text (verbatim, OWL.Closure.fsti:3684-3715) is a SINGLE
// outer fold over g on `t.p = rdfs_subPropertyOf`, converting t.o to
// a subject p2 via `term_to_subject`; for that p2 it runs TWO
// SEQUENTIAL inner folds against the sp-index -- `find_objects_
// indexed ig p2 rdfs_domain` first (building `acc_d` from `acc`),
// then `find_objects_indexed ig p2 rdfs_range` (building the step's
// result from `acc_d`) -- emitting a domain conclusion and a range
// conclusion from the SAME subPropertyOf triple in one pass. This is
// a new fold SHAPE for this module: sections 8/9/15/16's rules all
// have outer-fold-plus-ONE-inner-fold; here one outer item drives TWO
// inner folds back to back, so the invariant has to be threaded
// through twice -- `fold_left_inv` applied to the domain fold to
// reach `acc_d`, then applied again to the range fold starting from
// `acc_d`. `fold_left_inv`'s step hypothesis is a `forall` over ANY
// accumulator satisfying the invariant (not just the one reached from
// `acc`), so the two applications compose without extra proof burden
// -- the domain-fold's per-element argument and the range-fold's
// per-element argument are each independent of which invariant-
// satisfying accumulator they start from.
//
// Both inner folds read the SAME `ig_sp` bucket that sections 8/9/
// 15/16 already use (`ig_wf_sp ig /\ ig.ig_triples == g` is again the
// only hypothesis the lookups need): the domain fold's bucket key is
// `sp_key p2 rdfs_domain`, the range fold's is `sp_key p2 rdfs_range`.
// In each case the sub-property premise is `t` itself (the outer
// fold's own item, named `sub` in the row) and the domain/range
// declaration premise is the bucket-served triple (named `dom`/`rng`
// in the row); `p2`'s round trip through `term_to_subject`/`subj_term`
// (the half-inverse `lemma_term_to_subject_subj_term`, section 0) is
// what ties the bucket's subject key back to `sub.o`, exactly as
// sections 8/9's `y`/`y_subj` joins do.
//
// BNODE-POLLUTION GUARD (banner above the engine definition,
// OWL.Closure.fsti:3678-3680): both inner folds restrict the emitted
// object to `T_IRI` -- only NAMED domain/range classes propagate.
// Same narrowing note as sections 15/16: this only NARROWS what is
// emitted relative to the row (the row does not exclude a bnode-typed
// domain/range declaration), so it costs the case-split below nothing
// extra to discharge, never an unsound over-approximation.
//
// PROOF-FRIENDLY GUARD RULE check (task brief flagged this as a
// possible OWL.Closure.fsti touch): the two inner-fold lambdas here
// are anonymous, exactly like sections 15/16's single inner-fold
// lambdas (which also close over `t.s` from the enclosing scope and
// verify with no named-emitter hoist). The hoist sections 8's banner
// describes was needed only where an inner closure is built as a
// NAMED PARTIAL APPLICATION the engine itself already factors out
// (`sameas_trans_emit x`) and the proof mirrors that factoring; this
// rule's engine text factors nothing out, so the anonymous-local-copy
// recipe applies unchanged and no OWL.Closure.fsti edit was needed --
// recorded here so a future session does not re-check this for
// nothing.
// ===================================================================

// The licensing invariant for this rule, against BOTH rows it
// realizes: a two-disjunct row set, unlike every earlier section's
// single row, because one engine pass emits under two different
// table rows.
let subprop_domain_range_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==>
    (memP t g \/ scm_dom2_derives g t \/ scm_rng2_derives g t)

val owl_rule_subprop_domain_range_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (requires ig_wf_sp ig /\ ig.ig_triples == g)
          (ensures  subprop_domain_range_licensed g
                      (owl_rule_subprop_domain_range g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_subprop_domain_range_licensed g ig =
  lemma_vocab_dom_agree ();
  lemma_vocab_rng_agree ();
  lemma_vocab_eqp_agree ();
  let inv = subprop_domain_range_licensed g in
  // Engine text verbatim (OWL.Closure.fsti:3684-3715).
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match term_to_subject t.o with
        | None -> acc
        | Some p2 ->
          let doms = find_objects_indexed ig p2 rdfs_domain in
          let rngs = find_objects_indexed ig p2 rdfs_range in
          let acc_d =
            List.Tot.fold_left
              (fun (acc1 : rdf_graph) (c : rdf_term) ->
                 match c with
                 | T_IRI _ ->
                   add_triple_unchecked acc1
                     ({ s = t.s; p = rdfs_domain; o = c })
                 | _ -> acc1)
              acc
              doms
          in
          List.Tot.fold_left
            (fun (acc1 : rdf_graph) (c : rdf_term) ->
               match c with
               | T_IRI _ ->
                 add_triple_unchecked acc1
                   ({ s = t.s; p = rdfs_range; o = c })
               | _ -> acc1)
            acc_d
            rngs
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (outer_step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (outer_step acc t)
  with _ . begin
    if t.p = rdfs_subPropertyOf then
      match term_to_subject t.o with
      | Some p2 ->
        let doms = find_objects_indexed ig p2 rdfs_domain in
        let rngs = find_objects_indexed ig p2 rdfs_range in
        let dom_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc1 : rdf_graph) (c : rdf_term) ->
            match c with
            | T_IRI _ ->
              add_triple_unchecked acc1
                ({ s = t.s; p = rdfs_domain; o = c })
            | _ -> acc1 in
        let rng_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc1 : rdf_graph) (c : rdf_term) ->
            match c with
            | T_IRI _ ->
              add_triple_unchecked acc1
                ({ s = t.s; p = rdfs_range; o = c })
            | _ -> acc1 in
        // Domain-inner fold: every c served from the sp-index bucket
        // at (p2, rdfs_domain) is a real domain declaration of p2 in
        // g (ig_wf_sp + ig.ig_triples == g); t itself is the
        // subPropertyOf premise (sub), and p2's round trip through
        // term_to_subject/subj_term ties t.o to the bucket's subject
        // key -- scm-dom2's exact premise pair.
        introduce forall (acc1 : rdf_graph) (c : rdf_term).
            (memP c doms /\ inv acc1) ==> inv (dom_step acc1 c)
        with introduce (memP c doms /\ inv acc1) ==> inv (dom_step acc1 c)
        with _ . begin
          match c with
          | T_IRI _ ->
            let new_t : triple = { s = t.s; p = rdfs_domain; o = c } in
            assert_norm (doms ==
                         List.Tot.map (fun (u : triple) -> u.o)
                           (bucket_lookup ig.ig_sp (sp_key p2 rdfs_domain)));
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c
              (bucket_lookup ig.ig_sp (sp_key p2 rdfs_domain));
            eliminate exists (dom : triple).
                memP dom (bucket_lookup ig.ig_sp (sp_key p2 rdfs_domain)) /\
                dom.o == c
            returns scm_dom2_derives g new_t
            with _ . begin
              // ig_wf_sp places dom in the snapshot with dom.s == p2,
              // dom.p == rdfs_domain; ig.ig_triples == g places it in
              // g itself. t.o's term_to_subject is p2 (this branch's
              // match), so the half-inverse pins subj_term p2 == t.o,
              // i.e. subj_term dom.s == t.o -- scm-dom2's join
              // condition (`sub.o == subj_term dom.s`, sub := t).
              assert (memP dom ig.ig_triples /\
                      dom.s == p2 /\ dom.p == rdfs_domain);
              lemma_term_to_subject_subj_term t.o p2;
              assert (t.o == subj_term dom.s);
              assert (new_t == ({ s = t.s; p = o_rdfs_domain;
                                  o = dom.o } <: triple))
            end
          | _ -> ()
        end;
        fold_left_inv inv dom_step doms acc;
        let acc_d = List.Tot.fold_left dom_step acc doms in
        // Range-inner fold, applied starting from acc_d: the SAME
        // argument, scm-rng2 / rdfs_range in place of scm-dom2 /
        // rdfs_domain. fold_left_inv's per-element hypothesis is
        // generic over any invariant-satisfying accumulator, so this
        // second application composes with the first regardless of
        // acc_d's specific identity.
        introduce forall (acc1 : rdf_graph) (c : rdf_term).
            (memP c rngs /\ inv acc1) ==> inv (rng_step acc1 c)
        with introduce (memP c rngs /\ inv acc1) ==> inv (rng_step acc1 c)
        with _ . begin
          match c with
          | T_IRI _ ->
            let new_t : triple = { s = t.s; p = rdfs_range; o = c } in
            assert_norm (rngs ==
                         List.Tot.map (fun (u : triple) -> u.o)
                           (bucket_lookup ig.ig_sp (sp_key p2 rdfs_range)));
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c
              (bucket_lookup ig.ig_sp (sp_key p2 rdfs_range));
            eliminate exists (rng : triple).
                memP rng (bucket_lookup ig.ig_sp (sp_key p2 rdfs_range)) /\
                rng.o == c
            returns scm_rng2_derives g new_t
            with _ . begin
              assert (memP rng ig.ig_triples /\
                      rng.s == p2 /\ rng.p == rdfs_range);
              lemma_term_to_subject_subj_term t.o p2;
              assert (t.o == subj_term rng.s);
              assert (new_t == ({ s = t.s; p = o_rdfs_range;
                                  o = rng.o } <: triple))
            end
          | _ -> ()
        end;
        fold_left_inv inv rng_step rngs acc_d
      | None -> ()
    else ()
  end;
  fold_left_inv inv outer_step g g;
  assert_norm (owl_rule_subprop_domain_range g ig ==
               List.Tot.fold_left outer_step g g)
#pop-options

// Per-triple corollary.
val theorem_subprop_domain_range_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_subprop_domain_range g ig))
    (ensures  memP t g \/ scm_dom2_derives g t \/ scm_rng2_derives g t)

let theorem_subprop_domain_range_licensed g ig t =
  owl_rule_subprop_domain_range_licensed g ig
// ===================================================================
// 18. LIST-WALK licensing bridge (`decode_iri_list` vs
// `owl_list_denotes`), and its first consumer: cls-oo.
//
// OWL.Closure.fsti's `decode_iri_list` is a FUELED recursion over
// `ig_sp` bucket lookups (rdf:first / rdf:rest per node); OWL.RL.
// Spec.fst's `owl_list_denotes` is the table's declarative LIST[...]
// shape -- an exists-chain over `memP` in the plain graph. This is
// the syntactic sibling of OWL.Semantics.Soundness's
// `decode_iri_list_sound` (~line 385 there): same fuel induction,
// same nil/fuel-zero base cases, same two-bucket-then-recurse cons
// step: only the payload changes, TRUTH (`triple_holds` under an
// interpretation) becomes PROVENANCE (`memP` in the syntactic
// snapshot). `ig_wf_sp` (section 8/9's index-serving contract) pins
// each served rdf:first/rdf:rest hop into `ig.ig_triples`, and
// `ig.ig_triples == g` places it in the rule's own input graph --
// same two hypotheses section 9's `prp-trp` licensing carries for
// its own single-hop bucket read.
//
// Type alignment: `decode_iri_list` returns `option (list wf_iri)`
// (IRI-only list elements, `hasKey`'s narrower contract); the Spec's
// `owl_list_denotes` reads a `head : rdf_term` against `elems : list
// rdf_term` (arbitrary terms, no IRI restriction). The bridge lifts
// with the same `T_IRI` cast decode_iri_list_sound uses for `i.i_iri`,
// and reads the list head off `subj_term s` (`s : subject`) rather
// than a bare IRI, since `owl_list_denotes`'s head slot is a term,
// not a subject.
// ===================================================================

let lemma_vocab_list_agree ()
  : Lemma (OWL.Closure.rdf_first   == OWL.RL.Spec.o_rdf_first /\
           OWL.Closure.rdf_rest    == OWL.RL.Spec.o_rdf_rest /\
           OWL.Closure.rdf_nil_iri == OWL.RL.Spec.o_rdf_nil) = ()

// The bridge. Mirrors `decode_iri_list_sound`'s induction on `fuel`
// exactly: nil-head and fuel-exhaustion both hold vacuously (`None`
// or the `[]` case of `owl_list_denotes`); the cons step reads the
// same two ig_sp buckets (`rdf:first`, `rdf:rest`) at the same head
// subject, pins both hop-triples into `g` via `ig_wf_sp` +
// `ig.ig_triples == g` (the syntactic replacement for
// `holds_all i a ig.ig_triples`), recurses on the tail subject, and
// reassembles the `owl_list_denotes` cons case with witnesses
// `node := s`, `tail := tail_term` -- the two existentials
// `owl_list_denotes` carries that `seq_is` does not need (`seq_is`
// threads its current node through the domain element `l` directly;
// `owl_list_denotes` threads it through a `head : rdf_term`, so a
// witness subject has to be supplied at every hop).
#push-options "--z3rlimit 150 --split_queries always"
let rec lemma_decode_iri_list_licensed
    (g : rdf_graph) (ig : indexed_graph) (s : subject) (fuel : nat)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g)
    (ensures (match decode_iri_list g ig s fuel with
              | None -> True
              | Some members ->
                owl_list_denotes g (subj_term s)
                  (List.Tot.map (fun (x : wf_iri) -> T_IRI x) members)))
    (decreases fuel) =
  lemma_vocab_list_agree ();
  let is_nil_head =
    match s with
    | S_IRI x -> x = rdf_nil_iri
    | _ -> false in
  if is_nil_head then ()
  else if fuel = 0 then ()
  else begin
    let fb = bucket_lookup ig.ig_sp (sp_key s rdf_first) in
    let rb = bucket_lookup ig.ig_sp (sp_key s rdf_rest) in
    let firsts = find_objects_indexed ig s rdf_first in
    let rests  = find_objects_indexed ig s rdf_rest in
    assert (firsts == List.Tot.map (fun (t : triple) -> t.o) fb);
    assert (rests  == List.Tot.map (fun (t : triple) -> t.o) rb);
    match firsts, rests with
    | (T_IRI p_iri) :: _, tail_term :: _ ->
      (match fb, rb with
       | ft :: _, rt :: _ ->
         assert (ft.o == T_IRI p_iri);
         assert (rt.o == tail_term);
         assert (List.Tot.memP ft (bucket_lookup ig.ig_sp (sp_key s rdf_first)));
         assert (List.Tot.memP rt (bucket_lookup ig.ig_sp (sp_key s rdf_rest)));
         // ig_wf_sp pins ft, rt into the snapshot at subject s
         // (auto-instantiated by Z3 e-matching, same as sections 9/10's
         // use of ig_wf_sp); ig.ig_triples == g places them in g.
         assert (List.Tot.memP ft ig.ig_triples /\ ft.s == s /\ ft.p == rdf_first);
         assert (List.Tot.memP rt ig.ig_triples /\ rt.s == s /\ rt.p == rdf_rest);
         assert (List.Tot.memP ft g);
         assert (List.Tot.memP rt g);
         (match term_to_subject tail_term with
          | None -> ()
          | Some tail_subj ->
            lemma_decode_iri_list_licensed g ig tail_subj (fuel - 1);
            lemma_term_to_subject_subj_term tail_term tail_subj;
            (match decode_iri_list g ig tail_subj (fuel - 1) with
             | None -> ()
             | Some rest_props ->
               // The two list-hop triples, spelled as owl_list_denotes'
               // cons-case rdf:first / rdf:rest literals at witness
               // node := s.
               assert (ft == ({ s = s; p = o_rdf_first; o = T_IRI p_iri } <: triple));
               assert (rt == ({ s = s; p = o_rdf_rest;  o = tail_term } <: triple));
               assert (List.Tot.memP
                         ({ s = s; p = o_rdf_first; o = T_IRI p_iri } <: triple) g);
               assert (List.Tot.memP
                         ({ s = s; p = o_rdf_rest; o = tail_term } <: triple) g);
               // IH result, rewritten from subj_term tail_subj to
               // tail_term via the half-inverse -- the tail witness.
               assert (owl_list_denotes g tail_term
                         (List.Tot.map (fun (x : wf_iri) -> T_IRI x) rest_props))))
       | _, _ -> ())
    | _, _ -> ()
  end
#pop-options

// -------------------------------------------------------------------
// Consumer: cls-oo, Table 5 --
//   T(?c, owl:oneOf, ?x)  LIST[?x, ?y1, ..., ?yn]
//     => T(?y1, rdf:type, ?c), ..., T(?yn, rdf:type, ?c)
// transcribed as OWL.RL.Spec.cls_oo_derives. `owl_cls_oneof_step` /
// `owl_cls_oneof_emit` (OWL.Closure.fsti ~line 3099) are ALREADY
// lambda-lifted named top-level functions (the 2026-07-29 RDF-Based-
// semantics soundness pilot did this hoist for `owl_rule_cls_oneof_
// sound`'s benefit) -- no anonymous-closure hoist is needed here, so
// this section touches only this file.
//
// decl in cls_oo_derives is the fold-input triple `t` itself
// (`memP t g` from the outer fold hypothesis, `t.p == o_owl_oneOf`
// via the vocab bridge); `ys` is the bridge's decoded member list
// cast to terms; `yi := T_IRI m`, `yis := S_IRI m` for the member `m`
// the inner fold is emitting over -- `subj_term yis == yi` is the
// same one-line fact section 4's symmetric-property emission proof
// leans on for its own S_IRI/T_IRI round trip.
// -------------------------------------------------------------------

let lemma_vocab_cls_oo_agree ()
  : Lemma (RDFS.Closure.rdf_type    == OWL.RL.Spec.o_rdf_type /\
           OWL.Closure.owl_oneOf_iri == OWL.RL.Spec.o_owl_oneOf) = ()

let cls_oo_licensed (g : rdf_graph) (out : rdf_graph) : prop =
  forall (t : triple). memP t out ==> (memP t g \/ cls_oo_derives g t)

val owl_rule_cls_oneof_licensed (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g)
    (ensures  cls_oo_licensed g (owl_rule_cls_oneof g ig))

#push-options "--z3rlimit 200 --ifuel 4 --split_queries always"
let owl_rule_cls_oneof_licensed g ig =
  lemma_vocab_cls_oo_agree ();
  let fuel : nat = List.Tot.length g in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ cls_oo_licensed g acc) ==>
      cls_oo_licensed g (owl_cls_oneof_step g ig fuel acc t)
  with introduce (List.Tot.memP t g /\ cls_oo_licensed g acc) ==>
                 cls_oo_licensed g (owl_cls_oneof_step g ig fuel acc t)
  with _ . begin
    if t.p = owl_oneOf_iri then
      match t.s, term_to_subject t.o with
      | S_IRI c_iri, Some list_subj ->
        (match decode_iri_list g ig list_subj fuel with
         | None -> ()
         | Some members ->
           lemma_decode_iri_list_licensed g ig list_subj fuel;
           lemma_term_to_subject_subj_term t.o list_subj;
           // owl_list_denotes now reads off `subj_term list_subj`,
           // which the half-inverse pins to `t.o` -- the oneOf
           // declaration's own list-head object.
           let elems_d = List.Tot.map (fun (x : wf_iri) -> T_IRI x) members in
           assert (owl_list_denotes g t.o elems_d);
           introduce forall (acc1 : rdf_graph) (m : wf_iri).
               (List.Tot.memP m members /\ cls_oo_licensed g acc1) ==>
               cls_oo_licensed g (owl_cls_oneof_emit c_iri acc1 m)
           with introduce (List.Tot.memP m members /\ cls_oo_licensed g acc1) ==>
                          cls_oo_licensed g (owl_cls_oneof_emit c_iri acc1 m)
           with _ . begin
             List.Tot.Properties.memP_map_intro (fun (x : wf_iri) -> T_IRI x) m members;
             let new_t : triple = { s = S_IRI m; p = rdf_type; o = T_IRI c_iri } in
             lemma_subj_term_agree (S_IRI m);
             lemma_subj_term_agree t.s;
             // cls_oo_derives' witnesses: decl := t, ys := elems_d,
             // yi := T_IRI m, yis := S_IRI m.
             assert (subj_term (S_IRI m) == T_IRI m);
             assert (List.Tot.memP (T_IRI m) elems_d);
             assert (new_t == ({ s = S_IRI m; p = o_rdf_type;
                                 o = subj_term t.s } <: triple))
           end;
           fold_left_inv (cls_oo_licensed g) (owl_cls_oneof_emit c_iri) members acc)
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (cls_oo_licensed g) (owl_cls_oneof_step g ig fuel) g g
#pop-options

// Per-triple corollary.
val theorem_cls_oneof_licensed
    (g : rdf_graph) (ig : indexed_graph) (t : triple)
  : Lemma
    (requires ig_wf_sp ig /\ ig.ig_triples == g /\
              memP t (owl_rule_cls_oneof g ig))
    (ensures  memP t g \/ cls_oo_derives g t)

let theorem_cls_oneof_licensed g ig t =
  owl_rule_cls_oneof_licensed g ig
// ===================================================================
