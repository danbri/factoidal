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
open OWL.Closure
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
