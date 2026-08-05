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
