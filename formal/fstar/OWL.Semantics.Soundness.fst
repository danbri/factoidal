module OWL.Semantics.Soundness

// Machine-checked soundness proofs for SHIPPING closure rules from
// RDFS.Closure.fsti / OWL.Closure.fsti, against the OWL 2 RDF-Based
// semantic conditions formalized in OWL.Semantics.fst. Every theorem
// below is about the exact executable rule function the engine runs —
// not a model or transcription of it. No admits, no --lax.
//
// Pilot rules proven (design doc: docs/designissues/2026-07-29-
// rdf-based-semantics-formalization.md):
//   * rdfs_rule_domain              (rdfs2 — RDFS family, index-driven)
//   * owl_rule_symmetric_property   (prp-symp — property characteristic)
//   * owl_rule_sameAs_symmetry      (eq-sym — equality family, snapshot
//                                    pair-list machinery included)
//   * owl_rule_cls_oneof            (cls-oo — the list-walking case,
//                                    via decode_iri_list_sound)
//
// Proof shape shared by all four: fix an interpretation and ONE bnode
// assignment; show every triple the rule appends is true under that
// same assignment (the pilot rules mint no fresh bnodes); conclude at
// the satisfaction level. The fold_left inductions all go through
// OWL.Semantics.MemLemmas.fold_left_inv with the step obligation
// established by an `introduce forall` block.

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Closure
open OWL.Semantics
open OWL.Semantics.MemLemmas
open OWL.RL.Refinement

// ===================================================================
// Small bridging lemmas: boolean structural equality to propositional
// equality, in the shapes the rule bodies use.
// ===================================================================

let lemma_rdf_term_eq_iri (o : rdf_term) (x : wf_iri)
  : Lemma (requires rdf_term_eq o (T_IRI x) = true)
          (ensures o == T_IRI x) =
  match o with
  | T_IRI _ -> ()
  | _ -> ()

// ===================================================================
// Rule 1: owl_rule_symmetric_property (prp-symp).
// OWL 2 RL/RDF rules table: T(?p, rdf:type, owl:SymmetricProperty),
// T(?x, ?p, ?y) => T(?y, ?p, ?x). Uses no index bucket.
// ===================================================================

// Everything the collection fold gathers really is declared
// symmetric in g — stated semantically (its denotation is in
// ICEXT(I(owl:SymmetricProperty))) so the emission fold can consume
// it directly.
let sym_props_sound (i : interp) (a : bnode_assignment i.idom) (ps : list wf_iri) : prop =
  forall (p : wf_iri). List.Tot.mem p ps ==>
    icext i (i.i_iri p) (i.i_iri owl_SymmetricProperty)

val owl_rule_symmetric_property_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_symmetric i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_symmetric_property g ig))

let owl_rule_symmetric_property_sound i a g ig =
  let collect_step : list wf_iri -> triple -> list wf_iri =
    fun (acc : list wf_iri) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then
        match t.s with
        | S_IRI p_iri -> cons_if_new_iri p_iri acc
        | _ -> acc
      else acc in
  let sym_props = List.Tot.fold_left collect_step [] g in
  // Step 1: the collection fold is sound.
  introduce forall (acc : list wf_iri) (t : triple).
      (List.Tot.memP t g /\ sym_props_sound i a acc) ==>
      sym_props_sound i a (collect_step acc t)
  with introduce (List.Tot.memP t g /\ sym_props_sound i a acc) ==>
                 sym_props_sound i a (collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_SymmetricProperty) then begin
      lemma_rdf_term_eq_iri t.o owl_SymmetricProperty;
      assert (triple_holds i a t)
    end else ()
  end;
  fold_left_inv (sym_props_sound i a) collect_step g [];
  assert (sym_props_sound i a sym_props);
  // Step 2: the emission fold preserves truth.
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if List.Tot.mem t.p sym_props then
      match term_to_subject t.o with
      | Some new_subj ->
        lemma_denot_term_to_subject i a t.o new_subj;
        lemma_denot_subject_to_term i a t.s;
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri t.p) (denot_subject i a t.s) (denot_term i a t.o))
      | None -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_symmetric_property g ig ==
               List.Tot.fold_left emit_step g g)

// ===================================================================
// Rule 2: rdfs_rule_domain (rdfs2).
// RDF 1.1 Semantics, RDFS entailment rule rdfs2: (P rdfs:domain C),
// (a P b) |- (a rdf:type C). Reads the ig_pred bucket twice (once
// for the domain declarations, once for the data triples of each
// declared property), so its hypotheses are ig_wf_pred plus truth of
// the snapshot.
// ===================================================================

val rdfs_rule_domain_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_domain i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_pred ig)
    (ensures  holds_all i a (rdfs_rule_domain g ig))

let rdfs_rule_domain_sound i a g ig =
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            emit_once_term ig acc2 t.s rdf_type decl.o)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (List.Tot.memP decl decls /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc decl)
  with introduce (List.Tot.memP decl decls /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc decl)
  with _ . begin
    // ig_wf_pred at key rdfs_domain: decl is a real snapshot triple
    // asserting (decl.s rdfs:domain decl.o).
    assert (List.Tot.memP decl ig.ig_triples /\ decl.p == rdfs_domain);
    assert (triple_holds i a decl);
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) ->
          // Guarded since 2026-08-02 (emit_once_term): either the
          // snapshot already carries the conclusion and acc2 is
          // returned unchanged -- truth-preservation is the hypothesis
          // itself -- or the rule emits exactly the triple the
          // pre-guard body emitted, and the cond_domain argument below
          // covers it. Both branches are visible to SMT because
          // emit_once_term stays transparent in this module.
          emit_once_term ig acc2 t.s rdf_type decl.o in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (List.Tot.memP t matching /\ holds_all i a acc2) ==>
          holds_all i a (inner_step acc2 t)
      with introduce (List.Tot.memP t matching /\ holds_all i a acc2) ==>
                     holds_all i a (inner_step acc2 t)
      with _ . begin
        // ig_wf_pred at key p: t really is an (x P y) data triple.
        assert (List.Tot.memP t ig.ig_triples /\ t.p == p);
        assert (triple_holds i a t);
        // cond_domain: <I(P), I(C)> in IEXT(I(rdfs:domain)) and
        // <x,y> in IEXT(I(P)) give x in ICEXT(I(C)).
        assert (i.iext (i.i_iri rdfs_domain) (i.i_iri p) (denot_term i a decl.o));
        assert (icext i (denot_subject i a t.s) (denot_term i a decl.o))
      end;
      fold_left_inv (holds_all i a) inner_step matching acc
    | _ -> ()
  end;
  fold_left_inv (holds_all i a) outer_step decls g;
  assert_norm (rdfs_rule_domain g ig == List.Tot.fold_left outer_step g decls)

// ===================================================================
// ===================================================================
// Rule 2b: rdfs_rule_range (rdfs3; OWL-RL prp-rng via the interleaved
// fixpoint).
//
// First lemma of the rule-by-rule soundness program approved
// 2026-08-04, and the semantic mirror of rdfs_rule_domain_sound. This
// is the rule at the centre of the #345 unsoundness accusation
// ("range types the SUBJECT") -- refuted then by an evening of
// empirical forensics, refuted now by statement: under cond_range,
// every triple this rule emits is TRUE in every model of its
// premises, so no wrong reading of the rule can be among its
// emissions. The syntactic half (every emission is rdfs3_derives-
// licensed) lives in RDF.Entailment.RDFS.Refinement; this is the
// truth-preservation half.
// ===================================================================

val rdfs_rule_range_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_range i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_pred ig)
    (ensures  holds_all i a (rdfs_rule_range g ig))

let rdfs_rule_range_sound i a g ig =
  let decls = bucket_lookup ig.ig_pred rdfs_range in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            match term_to_subject t.o with
            | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type decl.o
            | None -> acc2)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (List.Tot.memP decl decls /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc decl)
  with introduce (List.Tot.memP decl decls /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc decl)
  with _ . begin
    // ig_wf_pred at key rdfs_range: decl is a real snapshot triple
    // asserting (decl.s rdfs:range decl.o).
    assert (List.Tot.memP decl ig.ig_triples /\ decl.p == rdfs_range);
    assert (triple_holds i a decl);
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) ->
          // Guarded emission (emit_once_term): either the snapshot
          // already carries the conclusion and acc2 comes back
          // unchanged -- truth-preservation is the hypothesis -- or
          // the rule emits exactly the rdfs3 conclusion, covered by
          // the cond_range argument below.
          match term_to_subject t.o with
          | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type decl.o
          | None -> acc2 in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (List.Tot.memP t matching /\ holds_all i a acc2) ==>
          holds_all i a (inner_step acc2 t)
      with introduce (List.Tot.memP t matching /\ holds_all i a acc2) ==>
                     holds_all i a (inner_step acc2 t)
      with _ . begin
        // ig_wf_pred at key p: t really is an (x P y) data triple.
        assert (List.Tot.memP t ig.ig_triples /\ t.p == p);
        assert (triple_holds i a t);
        match term_to_subject t.o with
        | Some b_subj ->
          // The conclusion subject is the PREMISE'S OBJECT -- this
          // alignment is the whole content of "range types the
          // object", and the denotation lemma is what carries it.
          lemma_denot_term_to_subject i a t.o b_subj;
          // cond_range: <I(P), I(C)> in IEXT(I(rdfs:range)) and
          // <x, y> in IEXT(I(P)) give y in ICEXT(I(C)).
          assert (i.iext (i.i_iri rdfs_range) (i.i_iri p) (denot_term i a decl.o));
          assert (icext i (denot_term i a t.o) (denot_term i a decl.o));
          assert (icext i (denot_subject i a b_subj) (denot_term i a decl.o))
        | None -> ()
      end;
      fold_left_inv (holds_all i a) inner_step matching acc
    | _ -> ()
  end;
  fold_left_inv (holds_all i a) outer_step decls g;
  assert_norm (rdfs_rule_range g ig == List.Tot.fold_left outer_step g decls)

// Rule 3: owl_rule_sameAs_symmetry (eq-sym).
// OWL 2 RL/RDF rules table: T(?x, owl:sameAs, ?y) => T(?y,
// owl:sameAs, ?x). The rule folds over the deduped snapshot pair
// list (#262 perf shape), so the proof first carries truth through
// the collect / sortWith / dedup pipeline.
// ===================================================================

// Membership preservation through OWL.Closure's pair dedup walk.
let rec lemma_dedup_pairs_memP (prev : option string)
    (ps acc : list (subject * subject)) (x : subject * subject)
  : Lemma
    (ensures List.Tot.memP x (dedup_pairs_sorted_aux prev ps acc) ==>
             (List.Tot.memP x ps \/ List.Tot.memP x acc))
    (decreases ps) =
  match ps with
  | [] -> List.Tot.rev_memP acc x
  | p :: rest ->
    lemma_dedup_pairs_memP prev rest acc x;
    lemma_dedup_pairs_memP (Some (sameas_pair_key p)) rest (p :: acc) x

// Every pair the snapshot machinery yields is a true sameAs edge.
let sameas_pairs_hold (i : interp) (a : bnode_assignment i.idom)
    (ps : list (subject * subject)) : prop =
  forall (xy : subject * subject). List.Tot.memP xy ps ==>
    i.iext (i.i_iri owl_sameAs)
           (denot_subject i a (fst xy)) (denot_subject i a (snd xy))

let lemma_sameas_pairs_hold
    (i : interp) (a : bnode_assignment i.idom) (ig : indexed_graph)
  : Lemma
    (requires holds_all i a ig.ig_triples)
    (ensures  sameas_pairs_hold i a (sameas_pairs ig)) =
  let collect_step : list (subject * subject) -> triple -> list (subject * subject) =
    fun (acc : list (subject * subject)) (t : triple) ->
      if t.p = owl_sameAs then
        match term_to_subject t.o with
        | Some y -> if subject_eq t.s y then acc else (t.s, y) :: acc
        | None -> acc
      else acc in
  let raw = List.Tot.fold_left collect_step [] ig.ig_triples in
  introduce forall (acc : list (subject * subject)) (t : triple).
      (List.Tot.memP t ig.ig_triples /\ sameas_pairs_hold i a acc) ==>
      sameas_pairs_hold i a (collect_step acc t)
  with introduce (List.Tot.memP t ig.ig_triples /\ sameas_pairs_hold i a acc) ==>
                 sameas_pairs_hold i a (collect_step acc t)
  with _ . begin
    if t.p = owl_sameAs then
      match term_to_subject t.o with
      | Some y ->
        lemma_denot_term_to_subject i a t.o y;
        assert (triple_holds i a t)
      | None -> ()
    else ()
  end;
  fold_left_inv (sameas_pairs_hold i a) collect_step ig.ig_triples [];
  let sorted = List.Tot.sortWith sameas_pair_cmp raw in
  lemma_sortWith_memP_forall sameas_pair_cmp raw;
  FStar.Classical.forall_intro (lemma_dedup_pairs_memP None sorted []);
  assert_norm (sameas_pairs ig == dedup_pairs_sorted_aux None sorted [])

val owl_rule_sameAs_symmetry_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_identity i /\ holds_all i a g /\ holds_all i a ig.ig_triples)
    (ensures  holds_all i a (owl_rule_sameAs_symmetry g ig))

let owl_rule_sameAs_symmetry_sound i a g ig =
  lemma_sameas_pairs_hold i a ig;
  let emit_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let new_t : triple = { s = y; p = owl_sameAs; o = subject_to_term x } in
      add_triple_unchecked acc new_t in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
      holds_all i a (emit_step acc xy)
  with introduce (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc xy)
  with _ . begin
    let (x, y) = xy in
    lemma_denot_subject_to_term i a x;
    // sameas_pairs_hold gives IEXT(sameAs)(dx, dy); the identity
    // condition collapses dx == dy, and then gives the flipped edge.
    assert (i.iext (i.i_iri owl_sameAs)
                   (denot_subject i a x) (denot_subject i a y))
  end;
  fold_left_inv (holds_all i a) emit_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_symmetry g ig ==
               List.Tot.fold_left emit_step g (sameas_pairs ig))

// ===================================================================
// Rule 4: owl_rule_cls_oneof (cls-oo) — the list-walking case.
// OWL 2 RL/RDF rules table: T(?c, owl:oneOf, ?x), LIST[?x, ?y1..?yn]
// => T(?yk, rdf:type, ?c). The structural risk the pilot exists to
// de-risk: the rule reads a SYNTACTIC rdf:List via decode_iri_list's
// fueled recursion over ig_sp lookups; the proof turns that decode
// into a SEMANTIC sequence reading (seq_is) so the oneOf condition
// can fire. decode_iri_list_sound is the reusable bridge — every
// other list-walking rule (cls-int1, cls-uni, prp-key, prp-spo2,
// cax-adc/adp) can reuse it as-is.
// ===================================================================

// Borderline VC (Warning 349 without the bump): same --z3rlimit idiom
// as RDFS.Closure.fsti's rdfs_closure — a resource-budget margin, not
// a logic change.
#push-options "--z3rlimit 60 --split_queries always"
let rec decode_iri_list_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph) (head_subj : subject) (fuel : nat)
  : Lemma
    (requires ig_wf_sp ig /\ holds_all i a ig.ig_triples)
    (ensures (match decode_iri_list g ig head_subj fuel with
              | None -> True
              | Some elems ->
                seq_is i (denot_subject i a head_subj)
                       (List.Tot.map (fun (x : wf_iri) -> i.i_iri x) elems)))
    (decreases fuel) =
  let is_nil_head = match head_subj with
    | S_IRI x -> x = rdf_nil_iri
    | _ -> false in
  if is_nil_head then ()
  else if fuel = 0 then ()
  else begin
    let fb = bucket_lookup ig.ig_sp (sp_key head_subj rdf_first) in
    let rb = bucket_lookup ig.ig_sp (sp_key head_subj rdf_rest) in
    let firsts = find_objects_indexed ig head_subj rdf_first in
    let rests  = find_objects_indexed ig head_subj rdf_rest in
    assert (firsts == List.Tot.map (fun (t : triple) -> t.o) fb);
    assert (rests  == List.Tot.map (fun (t : triple) -> t.o) rb);
    match firsts, rests with
    | (T_IRI p_iri) :: _, tail_term :: _ ->
      (match fb, rb with
       | ft :: _, rt :: _ ->
         // The heads of the object lists are the heads of the buckets.
         assert (ft.o == T_IRI p_iri);
         assert (rt.o == tail_term);
         // ig_wf_sp: both are real snapshot triples rooted at
         // head_subj with predicates rdf:first / rdf:rest.
         assert (List.Tot.memP ft (bucket_lookup ig.ig_sp (sp_key head_subj rdf_first)));
         assert (List.Tot.memP rt (bucket_lookup ig.ig_sp (sp_key head_subj rdf_rest)));
         assert (triple_holds i a ft);
         assert (triple_holds i a rt);
         (match term_to_subject tail_term with
          | None -> ()
          | Some tail_subj ->
            decode_iri_list_sound i a g ig tail_subj (fuel - 1);
            lemma_denot_term_to_subject i a tail_term tail_subj;
            (match decode_iri_list g ig tail_subj (fuel - 1) with
             | None -> ()
             | Some rest_props ->
               // The three conjuncts of the seq_is cons case, with
               // denot_term tail_term as the ground witness.
               assert (i.iext (i.i_iri rdf_first)
                              (denot_subject i a head_subj) (i.i_iri p_iri));
               assert (i.iext (i.i_iri rdf_rest)
                              (denot_subject i a head_subj) (denot_term i a tail_term));
               assert (seq_is i (denot_term i a tail_term)
                              (List.Tot.map (fun (x : wf_iri) -> i.i_iri x) rest_props))))
       | _, _ -> ())
    | _, _ -> ()
  end
#pop-options

// Proof-engineering note (found the hard way, kept for the next ~15
// list-walking rules): alpha-identical closures over different-but-
// equal captured variables share one SMT encoding symbol, so
// "my inner fold equals the rule's inner fold" closes by congruence —
// but ONLY if the proof-side lambda is written INLINE and UNASCRIBED.
// A `let step : ty = fun ...` ascription wraps the term and breaks
// the encoding-cache sharing, making the equality unprovable. So:
// state the step obligation on the BETA-REDUCED application, pass the
// verbatim inline lambda to fold_left_inv, and let the closure's
// defining axiom connect the two.

#push-options "--z3rlimit 90 --ifuel 4 --split_queries always"
val owl_rule_cls_oneof_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_oneof i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_cls_oneof g ig))

let owl_rule_cls_oneof_sound i a g ig =
  let fuel : nat = List.Tot.length g in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==>
      holds_all i a (owl_cls_oneof_step g ig fuel acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (owl_cls_oneof_step g ig fuel acc t)
  with _ . begin
    if t.p = owl_oneOf_iri then
      match t.s, term_to_subject t.o with
      | S_IRI c_iri, Some list_subj ->
        (match decode_iri_list g ig list_subj fuel with
         | None -> ()
         | Some members ->
           decode_iri_list_sound i a g ig list_subj fuel;
           lemma_denot_term_to_subject i a t.o list_subj;
           assert (triple_holds i a t);
           let elems_d = List.Tot.map (fun (x : wf_iri) -> i.i_iri x) members in
           assert (seq_is i (denot_subject i a list_subj) elems_d);
           assert (i.iext (i.i_iri owl_oneOf_iri)
                          (i.i_iri c_iri) (denot_subject i a list_subj));
           // cond_oneof fires on the sequence reading just built.
           assert (forall (x : i.idom). List.Tot.memP x elems_d ==>
                     icext i x (i.i_iri c_iri));
           introduce forall (acc1 : rdf_graph) (m : wf_iri).
               (List.Tot.memP m members /\ holds_all i a acc1) ==>
               holds_all i a (owl_cls_oneof_emit c_iri acc1 m)
           with introduce (List.Tot.memP m members /\ holds_all i a acc1) ==>
                          holds_all i a (owl_cls_oneof_emit c_iri acc1 m)
           with _ . begin
             List.Tot.memP_map_intro (fun (x : wf_iri) -> i.i_iri x) m members;
             assert (icext i (i.i_iri m) (i.i_iri c_iri))
           end;
           fold_left_inv (holds_all i a) (owl_cls_oneof_emit c_iri) members acc)
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) (owl_cls_oneof_step g ig fuel) g g
#pop-options

// ===================================================================
// Rule 5: owl_rule_equivalent_class (scm-eqc1 -- the row label the
// 2026-08-04 ledger correction fixed; the licensing sibling in
// OWL.RL.Refinement.fst section 5 carries the full story).
// OWL 2 RL/RDF rules table row scm-eqc1: T(?c, owl:equivalentClass, ?d) =>
// T(?c, rdfs:subClassOf, ?d), T(?d, rdfs:subClassOf, ?c). The engine
// rule's bnode-pollution guard (OWL.Closure.fsti ~line 201) narrows
// WHICH of the two conclusions is emitted per (t.s, d_subj)
// constructor pair -- it never emits a conclusion beyond the two
// cond_equivalent_class licenses, so every case is a subset of an
// already-sound pair; the 4-way match needs no extra argument.
// ===================================================================

val owl_rule_equivalent_class_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_equivalent_class i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_equivalent_class g ig))

let owl_rule_equivalent_class_sound i a g ig =
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_equivalentClass then
        match term_to_subject t.o with
        | Some d_subj ->
          let t1 : triple = { s = t.s;    p = rdfs_subClassOf; o = subject_to_term d_subj } in
          let t2 : triple = { s = d_subj; p = rdfs_subClassOf; o = subject_to_term t.s } in
          (match t.s, d_subj with
           | S_IRI _, S_IRI _ ->
             // both named: emit both directions (symmetric equivalence)
             add_triple_unchecked (add_triple_unchecked acc t1) t2
           | S_IRI _, S_BNode _ ->
             // named -> anon CE: only emit the forward (named sco bnode).
             add_triple_unchecked acc t1
           | S_BNode _, S_IRI _ ->
             // anon CE -> named: only emit the forward (named sco bnode).
             add_triple_unchecked acc t2
           | S_BNode _, S_BNode _ ->
             // bnode-to-bnode equivalence: skip (no test needs it,
             // and transitivity through such a pair would pollute).
             acc)
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = owl_equivalentClass then
      match term_to_subject t.o with
      | Some d_subj ->
        lemma_denot_term_to_subject i a t.o d_subj;
        lemma_denot_subject_to_term i a d_subj;
        lemma_denot_subject_to_term i a t.s;
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri owl_equivalentClass)
                       (denot_subject i a t.s) (denot_subject i a d_subj));
        // cond_equivalent_class: both subClassOf directions follow from
        // the single equivalentClass edge just established.
        assert (i.iext (i.i_iri rdfs_subClassOf)
                       (denot_subject i a t.s) (denot_subject i a d_subj));
        assert (i.iext (i.i_iri rdfs_subClassOf)
                       (denot_subject i a d_subj) (denot_subject i a t.s))
      | None -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_equivalent_class g ig == List.Tot.fold_left emit_step g g)

// ===================================================================
// Rule 6: owl_rule_equivalent_property (scm-eqp1 -- Table 8).
// OWL 2 RL/RDF rules table row scm-eqp1: T(?p, owl:equivalentProperty,
// ?q) => T(?p, rdfs:subPropertyOf, ?q), T(?q, rdfs:subPropertyOf, ?p).
// The prp-eqp1/prp-eqp2 data-triple effect (propagating ?p ?q edges
// through the equivalence) arrives via prp-spo1 downstream once the
// two subPropertyOf triples are in the graph -- same claim-drift
// story as Rule 5's banner. The engine rule fires only on the
// S_IRI/T_IRI shape (OWL.Closure.fsti's owl_rule_equivalent_property
// has no bnode case split and no term_to_subject round trip), so this
// proof needs neither the term_to_subject bridge lemmas nor a 4-way
// match: the S_IRI/T_IRI denotations unfold directly.
// ===================================================================

val owl_rule_equivalent_property_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_equivalent_property i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_equivalent_property g ig))

let owl_rule_equivalent_property_sound i a g ig =
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = owl_equivalentProperty then
      match t.s, t.o with
      | S_IRI p_iri, T_IRI q_iri ->
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri owl_equivalentProperty)
                       (i.i_iri p_iri) (i.i_iri q_iri));
        // cond_equivalent_property: both subPropertyOf directions
        // follow from the single equivalentProperty edge just
        // established.
        assert (i.iext (i.i_iri rdfs_subPropertyOf)
                       (i.i_iri p_iri) (i.i_iri q_iri));
        assert (i.iext (i.i_iri rdfs_subPropertyOf)
                       (i.i_iri q_iri) (i.i_iri p_iri))
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_equivalent_property g ig == List.Tot.fold_left emit_step g g)

// ===================================================================
// Rule 7: owl_rule_sameAs_reflexivity (eq-ref -- Table 4). OWL 2
// RL/RDF rules table row eq-ref: T(?s, ?p, ?o) => T(?s, owl:sameAs,
// ?s), T(?p, owl:sameAs, ?p), T(?o, owl:sameAs, ?o), restated by the
// engine (OWL.Closure.fsti ~line 471) as: fold over
// collect_iri_or_bnode_terms g and emit a reflexive owl:sameAs
// triple per node. cond_sameas_identity above gives the COLLAPSE
// direction (sameAs x y ==> x = y), which the eq-rep-* congruence
// rules need; this rule needs the other half of the Table 5.11
// identity relation -- every element is reflexively related -- which
// is exactly cond_sameas_reflexive. The licensing sibling in
// OWL.RL.Refinement.fst section 3 (owl_rule_sameAs_reflexivity_
// licensed) shows the same fold shape over the same collect_iri_
// or_bnode_terms list and additionally tracks node PROVENANCE (via
// lemma_collect_nodes_provenance) to prove each emitted triple is
// licensed by something already in g. This semantic proof needs none
// of that: cond_sameas_reflexive holds for every domain element, so
// the emission step's truth needs no fact about where n came from --
// only the fold structure (over nodes, not g) is shared.
// ===================================================================

val owl_rule_sameAs_reflexivity_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_reflexive i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_sameAs_reflexivity g ig))

let owl_rule_sameAs_reflexivity_sound i a g ig =
  let nodes = collect_iri_or_bnode_terms g in
  let emit_step : rdf_graph -> subject -> rdf_graph =
    fun (acc : rdf_graph) (n : subject) ->
      let new_t : triple = { s = n; p = owl_sameAs; o = subject_to_term n } in
      add_triple_unchecked acc new_t in
  introduce forall (acc : rdf_graph) (n : subject).
      (List.Tot.memP n nodes /\ holds_all i a acc) ==> holds_all i a (emit_step acc n)
  with introduce (List.Tot.memP n nodes /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc n)
  with _ . begin
    lemma_denot_subject_to_term i a n;
    assert (i.iext (i.i_iri owl_sameAs) (denot_subject i a n) (denot_subject i a n))
  end;
  fold_left_inv (holds_all i a) emit_step nodes g;
  assert_norm (owl_rule_sameAs_reflexivity g ig ==
               List.Tot.fold_left emit_step g (collect_iri_or_bnode_terms g))

// ===================================================================
// Rule 8: owl_rule_differentFrom_symmetry (eq-diff-sym; OWL.Closure.fsti
// ~line 546). OWL.RL.Spec.fst's engine ledger lists this rule
// differentFrom_symmetry [ext] "Table 5.13's differentFrom condition is
// symmetric in its arguments" -- the FIRST [ext] entry in the ledger to
// get its promised proof: the rule implements no W3C RL table row, and
// cond_differentfrom_symmetric plus this lemma IS that justification
// made machine-checked. The engine rule is the emission-fold half of
// Rule 1 (owl_rule_symmetric_property) with owl_sameAs's collection
// pipeline dropped entirely: it reads g directly and flips
// owl:differentFrom edges via term_to_subject / subject_to_term, so
// this proof mirrors Rule 1's emission-fold half exactly, with
// cond_differentfrom_symmetric standing in for cond_symmetric + the
// sym_props side condition.
// ===================================================================

val owl_rule_differentFrom_symmetry_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_differentfrom_symmetric i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_differentFrom_symmetry g ig))

let owl_rule_differentFrom_symmetry_sound i a g ig =
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_differentFrom then
        match term_to_subject t.o with
        | Some new_subj ->
          let new_t : triple =
            { s = new_subj; p = owl_differentFrom; o = subject_to_term t.s } in
          add_triple_unchecked acc new_t
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = owl_differentFrom then
      match term_to_subject t.o with
      | Some new_subj ->
        lemma_denot_term_to_subject i a t.o new_subj;
        lemma_denot_subject_to_term i a t.s;
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri owl_differentFrom)
                       (denot_subject i a t.s) (denot_term i a t.o))
      | None -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_differentFrom_symmetry g ig ==
               List.Tot.fold_left emit_step g g)

// ===================================================================
// Rule 9: owl_rule_disjoint_with_propagation (OWL.Closure.fsti
// ~line 1237). OWL.RL.Spec.fst's engine ledger justifies this rule by
// disjointness symmetry plus complementOf-implies-disjointness -- the
// SECOND [ext] entry in the ledger to get its promised proof (Rule 8's
// differentFrom_symmetry was the first, landed within the hour): the
// rule implements no W3C RL table row, and cond_disjointwith_symmetric
// plus cond_complementof_disjoint plus this lemma IS that
// justification made machine-checked. The engine rule fires on two
// branches over the SAME fold, both restricted to the S_IRI/T_IRI
// shape (no bnode case split, per the BNODE-POLLUTION GUARD comment on
// the engine rule): (1) t.p = owl:disjointWith emits the flipped
// triple (symmetry, mirrors Rule 6's single-conclusion S_IRI/T_IRI
// shape -- the denotations unfold directly, no term_to_subject bridge
// needed); (2) t.p = owl:complementOf emits BOTH disjointWith
// directions via nested add_triple_unchecked (mirrors Rule 5's
// two-conclusion S_IRI,S_IRI case -- no extra lemma needed for the
// two-cons step; SMT unfolds memP over the two prepends directly).
// ===================================================================

val owl_rule_disjoint_with_propagation_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_disjointwith_symmetric i /\ cond_complementof_disjoint i /\
              holds_all i a g)
    (ensures  holds_all i a (owl_rule_disjoint_with_propagation g ig))

let owl_rule_disjoint_with_propagation_sound i a g ig =
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_disjointWith_iri then
        // Symmetry: (C disjointWith D) -> (D disjointWith C).
        match t.s, t.o with
        | S_IRI c_iri, T_IRI d_iri ->
          let new_t : triple =
            { s = S_IRI d_iri; p = owl_disjointWith_iri; o = T_IRI c_iri } in
          add_triple_unchecked acc new_t
        | _, _ -> acc
      else if t.p = owl_complementOf_iri then
        // complementOf -> disjointWith (both directions).
        match t.s, t.o with
        | S_IRI c_iri, T_IRI d_iri ->
          let t1 : triple =
            { s = S_IRI c_iri; p = owl_disjointWith_iri; o = T_IRI d_iri } in
          let t2 : triple =
            { s = S_IRI d_iri; p = owl_disjointWith_iri; o = T_IRI c_iri } in
          add_triple_unchecked (add_triple_unchecked acc t1) t2
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = owl_disjointWith_iri then
      match t.s, t.o with
      | S_IRI c_iri, T_IRI d_iri ->
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri owl_disjointWith_iri)
                       (i.i_iri c_iri) (i.i_iri d_iri));
        // cond_disjointwith_symmetric: the flipped direction follows
        // from the single disjointWith edge just established.
        assert (i.iext (i.i_iri owl_disjointWith_iri)
                       (i.i_iri d_iri) (i.i_iri c_iri))
      | _, _ -> ()
    else if t.p = owl_complementOf_iri then
      match t.s, t.o with
      | S_IRI c_iri, T_IRI d_iri ->
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri owl_complementOf_iri)
                       (i.i_iri c_iri) (i.i_iri d_iri));
        // cond_complementof_disjoint: both disjointWith directions
        // follow from the single complementOf edge just established.
        assert (i.iext (i.i_iri owl_disjointWith_iri)
                       (i.i_iri c_iri) (i.i_iri d_iri));
        assert (i.iext (i.i_iri owl_disjointWith_iri)
                       (i.i_iri d_iri) (i.i_iri c_iri))
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_disjoint_with_propagation g ig ==
               List.Tot.fold_left emit_step g g)

// ===================================================================
// Rule 10: owl_rule_symmetric_metapredicates (OWL.Closure.fsti
// ~line 3749, "Group E(a): symmetric OWL metapredicates"). OWL.RL.
// Spec.fst's engine ledger justifies this rule by argument-symmetry
// of six OWL vocabulary predicates' RDF-Based semantic conditions --
// the THIRD [ext] entry in the ledger to get its promised proof
// (Rule 8's differentFrom_symmetry and Rule 9's
// disjoint_with_propagation came first, both landed earlier the same
// day): the rule implements no W3C RL table row, and the six
// per-predicate symmetry conditions below plus this lemma IS that
// justification made machine-checked. The engine rule fires a SINGLE
// fold testing is_owl_symmetric_metapredicate t.p (List.Tot.mem
// against the fixed 6-entry owl_symmetric_metapredicates table:
// owl:complementOf, owl:disjointWith, owl:propertyDisjointWith,
// owl:inverseOf, owl:equivalentClass, owl:equivalentProperty),
// restricted to the S_IRI/T_IRI shape (no bnode case split, per the
// BNODE-POLLUTION GUARD comment shared with every sibling rule in the
// file) with a self-loop guard (a = b emits nothing, since a
// predicate cannot be its own witness of an irreflexive-looking flip
// -- the guard just avoids a no-op self-insert). cond_disjointwith_
// symmetric already exists (Rule 9 above uses it for its symmetry
// branch) and is REUSED here rather than duplicated; the other five
// predicates each get a new direct predicate-level flip condition,
// since cond_equivalent_class / cond_equivalent_property (existing)
// state the WEAKER rdfs:subClassOf/subPropertyOf-both-directions
// consequence cls-eqc1/2 / prp-eqp1/2 need, not the direct flip this
// rule emits, and cond_complementof_disjoint (existing) states the
// disjointWith consequence Rule 9 needs, not the complementOf flip
// itself.
//
// Proof shape: the emit_step lambda below is copied VERBATIM from the
// engine rule (assert_norm's final equation needs the syntactic
// match). Inside the introduce-forall step-preservation block, the
// six-way membership test unfolds by explicit case analysis on t.p
// against each of the six table entries in the SAME order as
// owl_symmetric_metapredicates; the trailing catch-all case is
// unreachable (is_owl_symmetric_metapredicate t.p holds in that
// branch, per the outer if, yet t.p matches none of the six literal
// entries that predicate tests membership against) and is closed by
// unfolding the list literal for Z3 to contradict.
// ===================================================================

val owl_rule_symmetric_metapredicates_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_complementof_symmetric i /\ cond_disjointwith_symmetric i /\
              cond_propertydisjointwith_symmetric i /\ cond_inverseof_symmetric i /\
              cond_equivalentclass_symmetric i /\ cond_equivalentproperty_symmetric i /\
              holds_all i a g)
    (ensures  holds_all i a (owl_rule_symmetric_metapredicates g ig))

#push-options "--fuel 8 --ifuel 8 --z3rlimit 60"
let owl_rule_symmetric_metapredicates_sound i a g ig =
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if is_owl_symmetric_metapredicate t.p then
        match t.s, t.o with
        | S_IRI a, T_IRI b ->
          if a = b then acc
          else
            add_triple_unchecked acc
              ({ s = S_IRI b; p = t.p; o = T_IRI a } <: triple)
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if is_owl_symmetric_metapredicate t.p then
      match t.s, t.o with
      | S_IRI c_iri, T_IRI d_iri ->
        if c_iri = d_iri then ()
        else begin
          assert (triple_holds i a t);
          assert (i.iext (i.i_iri t.p) (i.i_iri c_iri) (i.i_iri d_iri));
          if t.p = owl_complementOf_iri then
            // cond_complementof_symmetric.
            assert (i.iext (i.i_iri owl_complementOf_iri)
                           (i.i_iri d_iri) (i.i_iri c_iri))
          else if t.p = owl_disjointWith_iri then
            // cond_disjointwith_symmetric (Rule 9's condition, reused).
            assert (i.iext (i.i_iri owl_disjointWith_iri)
                           (i.i_iri d_iri) (i.i_iri c_iri))
          else if t.p = owl_propertyDisjointWith then
            // cond_propertydisjointwith_symmetric.
            assert (i.iext (i.i_iri owl_propertyDisjointWith)
                           (i.i_iri d_iri) (i.i_iri c_iri))
          else if t.p = owl_inverseOf then
            // cond_inverseof_symmetric.
            assert (i.iext (i.i_iri owl_inverseOf)
                           (i.i_iri d_iri) (i.i_iri c_iri))
          else if t.p = owl_equivalentClass then
            // cond_equivalentclass_symmetric.
            assert (i.iext (i.i_iri owl_equivalentClass)
                           (i.i_iri d_iri) (i.i_iri c_iri))
          else if t.p = owl_equivalentProperty then
            // cond_equivalentproperty_symmetric.
            assert (i.iext (i.i_iri owl_equivalentProperty)
                           (i.i_iri d_iri) (i.i_iri c_iri))
          else
            // Unreachable: is_owl_symmetric_metapredicate t.p holds
            // (outer if) yet t.p matches none of the six literal
            // entries owl_symmetric_metapredicates tests membership
            // against -- contradiction. Unfold the concrete 6-entry
            // list so Z3 can derive False from the six accumulated
            // mismatches above plus the membership hypothesis.
            assert_norm (owl_symmetric_metapredicates ==
              [owl_complementOf_iri; owl_disjointWith_iri;
               owl_propertyDisjointWith; owl_inverseOf;
               owl_equivalentClass; owl_equivalentProperty])
        end
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_symmetric_metapredicates g ig ==
               List.Tot.fold_left emit_step g g)
#pop-options

// ===================================================================
// Rule 11: owl_rule_chain_to_transitive (scm-trans-from-chain;
// OWL.Closure.fsti ~line 2704, "sound but not in OWL 2 RL/RDF Table 9").
// The engine rule's own banner: "if (P owl:propertyChainAxiom (P P))
// -- i.e. a chain of length 2 of P composed with itself -- then P is
// transitive." cond_chain2_transitive (OWL.Semantics.fst) plus this
// lemma IS that justification made machine-checked: OWL 2 RDF-Based
// Semantics Table 5 (axiom mapping, SubObjectPropertyOf(ObjectProperty
// Chain(P1..Pn), Q) row, specialized to n=2, Q=P1=P2=P) licenses the
// composition-closure fact; Table 5.14's TransitiveProperty condition
// (the converse half of the direction cond_symmetric uses for
// SymmetricProperty) turns that closure fact into class membership.
//
// SHAPE: a single fold over g (owl-rule-shape-matrix.md classifies it
// SINGLE-FOLD; verified against the actual OWL.Closure.fsti text while
// writing this proof -- classification confirmed, not misclassified).
// decode_chain_pair is NOT a fold/list-walk needing its own induction:
// it is a fixed two-hop, non-recursive read (first cell, its
// rest-pointer, second cell, nil check), the same shape as the
// index-reading guards the other SINGLE-FOLD rules already use.
// decode_chain_pair_sound below is the bridge lemma for that fixed
// two-hop read, mirroring decode_iri_list_sound's per-hop assertions
// (Rule 4 above) but WITHOUT the recursion -- decode_chain_pair never
// recurses past depth 2, so no fuel / `decreases` clause is needed.
//
// No fresh bnodes: list_subj comes from chain_t.o (an object already
// present in g via chain_t, itself drawn from g), and the two
// list-cell triples decode_chain_pair reads are real members of g
// found through the sp-bucket index (ig_wf_sp) -- the SAME assignment
// a that makes g true already makes them true, so this rule fits the
// module banner's "mints no fresh bnodes" proof shape (contrast Rule
// 12's finding below, where the converse rule mints exactly such
// bnodes and that shape breaks).
// ===================================================================

// Bridge lemma for decode_chain_pair (OWL.Closure.fsti ~line 2508):
// when the two-hop read succeeds, the list head denotes a genuine
// 2-element sequence over the two decoded IRIs' denotations. Fixed
// depth 2, no recursion -- mirrors decode_iri_list_sound's per-hop
// assertions (Rule 4) without needing its `fuel` machinery.
#push-options "--z3rlimit 60 --split_queries always"
let decode_chain_pair_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph) (head_subj : subject)
  : Lemma
    (requires ig_wf_sp ig /\ holds_all i a ig.ig_triples)
    (ensures (match decode_chain_pair g ig head_subj with
              | None -> True
              | Some (q1, q2) ->
                seq_is i (denot_subject i a head_subj)
                       [i.i_iri q1; i.i_iri q2])) =
  let fb1 = bucket_lookup ig.ig_sp (sp_key head_subj rdf_first) in
  let rb1 = bucket_lookup ig.ig_sp (sp_key head_subj rdf_rest) in
  let firsts1 = find_objects_indexed ig head_subj rdf_first in
  let rests1  = find_objects_indexed ig head_subj rdf_rest in
  assert (firsts1 == List.Tot.map (fun (t : triple) -> t.o) fb1);
  assert (rests1  == List.Tot.map (fun (t : triple) -> t.o) rb1);
  match firsts1, rests1 with
  | (T_IRI p1) :: _, tail_term :: _ ->
    (match fb1, rb1 with
     | ft1 :: _, rt1 :: _ ->
       assert (ft1.o == T_IRI p1);
       assert (rt1.o == tail_term);
       assert (List.Tot.memP ft1 (bucket_lookup ig.ig_sp (sp_key head_subj rdf_first)));
       assert (List.Tot.memP rt1 (bucket_lookup ig.ig_sp (sp_key head_subj rdf_rest)));
       assert (triple_holds i a ft1);
       assert (triple_holds i a rt1);
       (match term_to_subject tail_term with
        | None -> ()
        | Some tail_subj ->
          lemma_denot_term_to_subject i a tail_term tail_subj;
          let fb2 = bucket_lookup ig.ig_sp (sp_key tail_subj rdf_first) in
          let rb2 = bucket_lookup ig.ig_sp (sp_key tail_subj rdf_rest) in
          let firsts2 = find_objects_indexed ig tail_subj rdf_first in
          let rests2  = find_objects_indexed ig tail_subj rdf_rest in
          assert (firsts2 == List.Tot.map (fun (t : triple) -> t.o) fb2);
          assert (rests2  == List.Tot.map (fun (t : triple) -> t.o) rb2);
          (match firsts2, rests2 with
           | (T_IRI p2) :: _, (T_IRI nil_iri) :: _ ->
             if nil_iri = rdf_nil_iri then
               (match fb2, rb2 with
                | ft2 :: _, rt2 :: _ ->
                  assert (ft2.o == T_IRI p2);
                  assert (rt2.o == T_IRI nil_iri);
                  assert (List.Tot.memP ft2 (bucket_lookup ig.ig_sp (sp_key tail_subj rdf_first)));
                  assert (List.Tot.memP rt2 (bucket_lookup ig.ig_sp (sp_key tail_subj rdf_rest)));
                  assert (triple_holds i a ft2);
                  assert (triple_holds i a rt2);
                  assert (i.iext (i.i_iri rdf_first) (denot_subject i a head_subj) (i.i_iri p1));
                  assert (i.iext (i.i_iri rdf_rest) (denot_subject i a head_subj) (denot_subject i a tail_subj));
                  assert (i.iext (i.i_iri rdf_first) (denot_subject i a tail_subj) (i.i_iri p2));
                  assert (i.iext (i.i_iri rdf_rest) (denot_subject i a tail_subj) (i.i_iri rdf_nil_iri));
                  assert (seq_is i (i.i_iri rdf_nil_iri) []);
                  assert (seq_is i (denot_subject i a tail_subj) [i.i_iri p2]);
                  assert (seq_is i (denot_subject i a head_subj) [i.i_iri p1; i.i_iri p2])
                | _, _ -> ())
             else ()
           | _, _ -> ()))
     | _, _ -> ())
  | _, _ -> ()
#pop-options

val owl_rule_chain_to_transitive_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_chain2_transitive i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_chain_to_transitive g ig))

#push-options "--z3rlimit 90 --split_queries always"
let owl_rule_chain_to_transitive_sound i a g ig =
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (chain_t : triple) ->
      if chain_t.p = owl_propertyChainAxiom then
        match chain_t.s, term_to_subject chain_t.o with
        | S_IRI p_iri, Some list_subj ->
          (match decode_chain_pair g ig list_subj with
           | Some (q1, q2) ->
             if q1 = p_iri && q2 = p_iri then
               let new_t : triple =
                 { s = S_IRI p_iri; p = rdf_type;
                   o = T_IRI owl_TransitiveProperty } in
               add_triple_unchecked acc new_t
             else acc
           | None -> acc)
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (chain_t : triple).
      (List.Tot.memP chain_t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc chain_t)
  with introduce (List.Tot.memP chain_t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc chain_t)
  with _ . begin
    if chain_t.p = owl_propertyChainAxiom then
      match chain_t.s, term_to_subject chain_t.o with
      | S_IRI p_iri, Some list_subj ->
        (match decode_chain_pair g ig list_subj with
         | Some (q1, q2) ->
           if q1 = p_iri && q2 = p_iri then begin
             decode_chain_pair_sound i a g ig list_subj;
             lemma_denot_term_to_subject i a chain_t.o list_subj;
             assert (triple_holds i a chain_t);
             assert (i.iext (i.i_iri owl_propertyChainAxiom)
                            (i.i_iri p_iri) (denot_subject i a list_subj));
             assert (seq_is i (denot_subject i a list_subj)
                            [i.i_iri p_iri; i.i_iri p_iri]);
             // cond_chain2_transitive fires on the chain edge plus the
             // sequence reading just built.
             assert (icext i (i.i_iri p_iri) (i.i_iri owl_TransitiveProperty))
           end else ()
         | None -> ())
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_chain_to_transitive g ig == List.Tot.fold_left emit_step g g)
#pop-options

// ===================================================================
// Rule 12: owl_rule_transitive_to_chain (prp-trp-to-chain;
// OWL.Closure.fsti ~line 2750) -- FINDING, not proven. STOP per the
// two-attempt rule: the honest condition this rule needs is not
// justifiable from the W3C tables, so no lemma is added here.
//
// owl-rule-shape-matrix.md's SINGLE-FOLD classification is correct (one
// fold_left over g, no list-walk) -- the blocker is semantic, not
// shape. Unlike every rule proven above (1 through 11), this rule
// MINTS FRESH BLANK NODES: canonical_chainl1_bnode / _chainl2_bnode
// are deterministic labels derived from p_iri that do NOT occur in g.
// The module banner's shared proof shape ("fix ONE bnode assignment;
// the pilot rules mint no fresh bnodes, so the assignment chosen for g
// serves the conclusion graph too") does not extend to this rule: the
// assignment `a` used to establish holds_all i a g is a TOTAL function
// or bnode_id, but its value at these fresh labels is UNCONSTRAINED by
// g, and satisfies-level reasoning (choosing a DIFFERENT/extended
// assignment a') does not rescue it either -- it still requires the
// interpretation's domain to already CONTAIN elements v1, v2 with
// iext(propertyChainAxiom) (denot P) v1 /\ iext(first) v1 (denot P) /\
// iext(rest) v1 v2 /\ iext(first) v2 (denot P) /\ iext(rest) v2
// (i.i_iri rdf_nil_iri). That is an EXISTENCE condition on the
// interpretation, not an implication -- and it is not implied by any
// W3C RDF-Based Semantics table: a genuine OWL 2 RDF-Based
// interpretation is free to leave IEXT(rdf:first) / IEXT(rdf:rest)
// with no elements related to P at all while still satisfying "P is
// transitive" (Table 5.14 says nothing about rdf:first/rdf:rest
// witnesses). Adding such an existence condition as a lemma hypothesis
// would make the F* theorem type-check, but it would NOT be sound
// relative to genuine OWL 2 RDF-Based interpretations -- it would
// violate the module banner's "class of interpretations here is a
// SUPERSET of the genuine OWL 2 RDF-Based interpretations" invariant
// the whole soundness architecture depends on (see OWL.Semantics.fst
// header). That is a table-groundedness failure, not a proof-
// engineering one, so per the brief ("if the honest condition would be
// unjustifiable from the tables, STOP for that rule and report the gap
// as a finding") this is reported here rather than forced.
//
// What WOULD close this: the rule's actual soundness argument (per its
// own banner, "every model of P transitive is a model of chain(P,P)
// subPropertyOf P and vice versa") is an axiom-equivalence claim under
// OWL 2's ontology-level deduction, not a same-model truth-preservation
// claim in this file's per-assignment RDF-Based semantics. Closing it
// properly needs either (a) a Henkin/Skolem-style model-EXTENSION
// lemma (construct a strictly larger interpretation i' >= i realizing
// the needed witnesses, then argue entailment through the extension --
// a different lemma shape than any rule 1-11 uses), or (b) reframing
// the claim at the "licensed by g" (syntactic-provenance) level the way
// OWL.RL.Refinement.fst's licensing proofs do for other existential-
// witness rules (svf2_existential_witness, cls_svf_thing_witness,
// singleton_nominal_functionality in the shape matrix), which is a
// different soundness notion than this file's model-theoretic one.
// Neither is a same-shape extension of the Rule 1-11 skeleton.
// ===================================================================

// ===================================================================
// Rule 13: owl_rule_scm_cls_restriction (OWL.Closure.fsti ~line 2466).
// Engine banner: "scm-cls [OWL 2 RL/RDF, partial]: every
// owl:Restriction is also an owl:Class." OWL.RL.Spec.fst ledger:
// "[ext] scm-cls extended to restriction nodes".
// cond_restriction_subclass_of_class (OWL.Semantics.fst) is that
// justification made machine-checked: OWL 2 RL/RDF Table 5 (Axiomatic
// Triples) fixes `owl:Restriction rdfs:subClassOf owl:Class`
// unconditionally, read through the RDFS class-extension semantic
// condition into the ICEXT-subset implication the rule needs.
//
// SHAPE: single fold over g, no list-walk, no fresh bnodes — new_t's
// subject is t.s, an existing node already present in g via t. Same
// "mints no fresh bnodes" shape as Rules 1-11; fits the module
// banner's shared proof skeleton directly (fix one assignment; every
// emitted triple is true under it).
// ===================================================================

val owl_rule_scm_cls_restriction_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_restriction_subclass_of_class i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_scm_cls_restriction g ig))

#push-options "--z3rlimit 60 --split_queries always"
let owl_rule_scm_cls_restriction_sound i a g ig =
  let emit_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_Restriction_iri) then
        let new_t : triple =
          { s = t.s; p = rdf_type; o = T_IRI owl_Class } in
        add_triple_unchecked acc new_t
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_Restriction_iri) then begin
      lemma_rdf_term_eq_iri t.o owl_Restriction_iri;
      assert (triple_holds i a t);
      assert (icext i (denot_subject i a t.s) (i.i_iri owl_Restriction_iri));
      assert (icext i (denot_subject i a t.s) (i.i_iri owl_Class))
    end else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_scm_cls_restriction g ig ==
               List.Tot.fold_left emit_step g g)
#pop-options

// ===================================================================
// Rule 14: owl_rule_cls_svf_thing_materialize (OWL.Closure.fsti
// ~line 1873) -- FINDING, not proven. STOP per the two-attempt rule,
// same reasoning as Rule 12's finding above (cited and extended here,
// not repeated from scratch).
//
// OWL.RL.Spec.fst ledger: "[ext] cls-svf2-adjacent comprehension
// entry". owl-rule-shape-matrix.md's SINGLE-FOLD classification is
// correct (one fold_left over g) -- the blocker is semantic, exactly
// as Rule 12's was, not shape.
//
// MINTED TERM: for every non-schema, non-rdf:type edge `(x P y)` that
// passes edge_subject_is_safe, the rule constructs
//   rb = canonical_svf_thing_restriction_bnode p
//      = String.concat "" ["__rl_svfthing_"; p]        (OWL.Closure.fsti
//                                                         line 1870-1871)
// and unconditionally emits, via add_triple_unchecked, four triples
// keyed on rb: `rb rdf:type owl:Restriction`, `rb owl:onProperty P`,
// `rb owl:someValuesFrom owl:Thing`, and the membership triple
// `x rdf:type rb` (OWL.Closure.fsti lines 1885-1898). No table or
// premise in g asserts that a resource denoted `rb` — with exactly
// those three shape-triples true of it — already exists; `rb` is a
// canonical LABEL the engine invents, not a node read out of g. (This
// is the SAME kind of freshness Rule 12 found fatal for
// canonical_chainl1_bnode / canonical_chainl2_bnode, though the
// mechanism differs: Rule 12 needed rdf:first/rdf:rest LIST-CELL
// witnesses; this rule needs a COMPREHENSION witness for the
// anonymous class expression SomeValuesFrom(P, owl:Thing).)
//
// WHY NO HONEST CONDITION CLOSES IT: at the satisfies level (Hayes
// section 5.2 / this file's `satisfies`), proving
// `satisfies i (owl_rule_cls_svf_thing_materialize g ig)` from
// `satisfies i g` lets us pick a FRESH assignment a' for the output
// graph — a'(rb) can be any element of i.idom — but it cannot pick
// which pairs lie in the FIXED interpretation i's IEXT relation. The
// four emitted triples require ONE domain element d = a'(rb)
// simultaneously satisfying: icext i d (i.i_iri owl_Restriction_iri),
// i.iext (i.i_iri owl_onProperty_iri) d (i.i_iri p),
// i.iext (i.i_iri owl_someValuesFrom_iri) d (i.i_iri owl_Thing), AND
// icext i (denot_subject i a' x) d. That is a four-way EXISTENCE claim
// about i's domain, not an implication from anything holds_all i a g
// supplies (g need not mention owl:onProperty, owl:Restriction, or
// owl:someValuesFrom at all — e.g. bnode2somevaluesfrom's premise is
// bare instance data). A degenerate interpretation with
// IEXT(owl:onProperty) = the empty relation trivially satisfies every
// cond_* in this file (none of them constrain owl:onProperty without a
// premise firing) while satisfying g, and it has NO witnessing d — so
// satisfies i g' genuinely fails for that i. Adding the needed
// existence fact as a hypothesis would type-check the lemma but
// violate the module banner's "class of interpretations here is a
// SUPERSET of the genuine OWL 2 RDF-Based interpretations" invariant,
// exactly as Rule 12's finding describes.
//
// This is precisely the gap OWL.Closure.fsti's own "20b.
// Comprehension-witness closure" section documents (~line 5832-5874):
// the five owl_rule_comp_* / witness rules realise OWL 2 RDF-Based
// Semantics section 8's comprehension conditions, which "were
// NORMATIVE in OWL 1 Full and are informative-only in OWL 2 precisely
// because, taken as iff-conditions, they force infinite structures
// into every interpretation." The engine's own comment on this rule
// family (OWL.Closure.fsti ~line 5800) claims soundness "under Direct
// Semantics" — a DIFFERENT model-theoretic framework in which
// SomeValuesFrom(P, owl:Thing) denotes a SET {x | exists y. (x,y) in
// P}, not an extra domain element requiring a witness proof. That
// Direct-Semantics argument is real but is not a same-model
// truth-preservation claim in this file's per-assignment RDF-Based
// semantics, so it cannot supply the lemma this file's skeleton needs.
// Closing it properly needs the same two routes Rule 12's finding
// names: (a) a Henkin/Skolem model-EXTENSION lemma, or (b) reframing
// at the "licensed by g" (syntactic-provenance) level the way
// OWL.RL.Refinement.fst's licensing proofs do for
// svf2_existential_witness / cls_svf_thing_witness — a different
// soundness notion than this file's model-theoretic one. Neither is a
// same-shape extension of the Rule 1-11/13 skeleton, so per the brief
// this is reported here rather than forced.
// ===================================================================

// ===================================================================
// Rule 15: owl_rule_cls_hasself2_synth (OWL.Closure.fsti ~line 1806)
// -- FINDING, not proven. Same STOP, same reasoning as Rule 14 above
// (and Rule 12): a distinct rule, an identical comprehension-witness
// gap.
//
// OWL.RL.Spec.fst ledger: "[ext] cls_hasself2_synth ... sibling of the
// above" (of cls_hasself1). owl-rule-shape-matrix.md's SINGLE-FOLD
// classification is correct; the blocker is semantic.
//
// MINTED TERM: for every self-loop edge `(x P x)` (edge.s and edge.o
// denote the same resource) that is non-schema and
// edge_subject_is_safe, the rule constructs
//   rb = canonical_hasself_restriction_bnode p
//      = String.concat "" ["__rl_hasself_"; p]          (OWL.Closure.fsti
//                                                          line 1803-1804)
// and unconditionally emits, via add_triple_unchecked, four triples
// keyed on rb: `rb rdf:type owl:Restriction`, `rb owl:onProperty P`,
// `rb owl:hasSelf "true"^^xsd:boolean`, and `x rdf:type rb`
// (OWL.Closure.fsti lines 1818-1828). As with Rule 14's rb, no premise
// in g asserts that such a resource already exists — `rb` is an
// invented canonical label, not a node read out of g.
//
// WHY NO HONEST CONDITION CLOSES IT: identical argument to Rule 14's,
// substituting the ObjectHasSelf(P) comprehension witness for
// SomeValuesFrom(P, owl:Thing)'s. At the satisfies level, the four
// emitted triples require ONE domain element d = a'(rb) with
// icext i d (i.i_iri owl_Restriction_iri),
// i.iext (i.i_iri owl_onProperty_iri) d (i.i_iri p),
// i.iext (i.i_iri owl_hasSelf_iri) d (i.i_lit true_xsd_boolean_literal),
// AND icext i (denot_subject i a' x) d, simultaneously, in a FIXED
// interpretation i whose IEXT this proof does not get to choose. g's
// only premise is the bare self-loop `(x P x)`
// (New-Feature-SelfRestriction-002's premise: `Peter :likes Peter`,
// no owl:Restriction anywhere) — nothing in it, nor in any cond_* this
// file defines, forces IEXT(owl:hasSelf) or ICEXT(owl:Restriction) to
// be nonempty, let alone to contain a witness related as required. A
// degenerate interpretation with IEXT(owl:onProperty) empty satisfies
// every cond_* here while satisfying g and has no such d, so
// satisfies i g' fails for it — the same counterexample shape as Rule
// 14 and Rule 12. Adding the existence fact as a hypothesis would
// again violate the interpretations-superset invariant. This is the
// same OWL.Closure.fsti "20b. Comprehension-witness closure" gap
// (~line 5832-5874) and the same "sound under Direct Semantics, not
// under this file's per-assignment RDF-Based semantics" distinction
// Rule 14's finding details — closing it needs the same
// model-extension or syntactic-licensing route, not a same-shape
// extension of the Rule 1-11/13 skeleton.
// ===================================================================

// Rule 16: owl_rule_scm_eqc2 (scm-eqc2; OWL.Closure.fsti ~line 267) --
// FINDING, not proven. CONTROLLED EXPERIMENT result, per the brief:
// try inline, then factored; if both hit the SAME undischargeable
// step obligation, stop and report rather than force it.
//
// OWL 2 RDF-Based Semantics Table 5.8, the OTHER direction from Rule
// 5's owl_rule_equivalent_class: T(?c, rdfs:subClassOf, ?d), T(?d,
// rdfs:subClassOf, ?c) => T(?c, owl:equivalentClass, ?d) -- "Reverse
// of cls-eqc1/cls-eqc2" per the engine rule's own banner comment. The
// condition (cond_mutual_subclass_equivalent, OWL.Semantics.fst) is
// added and verifies standalone; it is exactly the table-grounded
// hypothesis the rule needs. What does NOT close is the step-
// preservation obligation for the engine rule's NON-firing branch.
//
// BOTH attempts below reached IDENTICAL witness-chain success and
// IDENTICAL final failure:
//   * ATTEMPT 1 (INLINE): the C-sco-D / D-sco-C / cond_mutual_
//     subclass_equivalent witness chain (t itself for C-sco-D;
//     memP_existsb + find_objects_indexed's definitional map equation
//     + memP_map_elim + ig_wf_sp + lemma_rdf_term_eq_iri for D-sco-C)
//     written INLINE in the introduce-forall step-preservation block
//     DISCHARGED CLEANLY -- every assert in the firing (existsb-true)
//     branch passed, including the closing
//     `i.iext (i.i_iri owl_equivalentClass) (i.i_iri c_iri) (i.i_iri d_iri)`.
//     The failure is NOT in the witness chain. It is in the NON-firing
//     (existsb-false, "no emission") branch: proving
//     `holds_all i a (emit_step acc t)` there reduces to proving
//     `emit_step acc t == acc`, and neither the direct squash-typed
//     `()` nor an explicit `assert (emit_step acc t == acc)` (with
//     every governing fact -- t.p, t.s/t.o, c_iri<>d_iri, existsb=false
//     -- ALSO asserted explicitly right beforehand) discharges, even
//     under `--z3rlimit 300 --fuel 8 --ifuel 8` (30x the rlimit and 2x
//     the fuel of Rule 10's comparably-shaped proof). Exact error
//     (reproduced verbatim across every rlimit/fuel variant tried):
//       Error 19: Subtyping check failed
//       - Expected type Prims.squash (OWL.Semantics.holds_all i a (emit_step acc t))
//         got type Prims.unit
//       - The SMT solver could not prove the query.
//   * ATTEMPT 2 (FACTORED): the SAME witness chain moved into a
//     separate `owl_scm_eqc2_emission_sound` val+let lemma (taking
//     c_iri/d_iri/the firing facts as explicit parameters, called from
//     the introduce body on the existsb-true branch) -- the shape the
//     failed OWL.RL.Refinement.fst licensing attempt used. This ALSO
//     discharged the witness chain cleanly and ALSO failed at the
//     SAME non-firing branch, with the SAME error text (only the
//     source line/column of the `()` moved, per the refactor).
//
// READING: the discriminator is neither "module context" (it fails
// here in OWL.Semantics.Soundness.fst exactly as in OWL.RL.Refinement.
// fst) nor "inline vs factored" (both forms fail identically) nor the
// witness chain itself (it discharges in both forms). It is the
// engine rule's STEP FUNCTION SHAPE: emit_step nests FOUR decision
// points on the firing triple (if t.p = rdfs_subClassOf; match t.s,
// t.o; if c_iri = d_iri; if existsb ...), one level DEEPER than every
// other rule in this file (Rules 1-11 bottom out their "no-op" case at
// THREE nested decisions at most -- e.g. Rule 10's `if c_iri = d_iri
// then ()` inside `if is_owl_symmetric_metapredicate t.p then match
// t.s, t.o with ...`, which DOES discharge). Proving the ascribed
// `emit_step`'s no-op branch reduces to `acc` needs Z3 to chain
// THROUGH all four levels to the SAME conclusion the surrounding
// proof-side if/match already established at each level; that chain
// discharges through three levels elsewhere in this file but not
// through four here, and bumping --z3rlimit/--fuel does not move it
// (ruling out a resource-starvation explanation; this reads as a
// missing unfolding trigger, not a slow one).
//
// What would close it: restate the goal so the non-firing branch
// never needs `emit_step acc t == acc` as a DERIVED equality -- e.g.
// an unfold/rewrite lemma proven separately for exactly this
// four-level shape (mirroring Rule 4's decode_iri_list_sound /
// Rule 11's decode_chain_pair_sound bridge-lemma pattern, but bridging
// the STEP FUNCTION's own reduction rather than a list/chain decode),
// or restructuring emit_step's guard as a single computed `option`
// value (matched once) rather than two sequential booleans, IF that
// restructuring can still be shown equal to the engine's literal
// definition for the closing assert_norm. Neither was attempted here
// per the two-structural-attempt stop rule; that is the next step for
// whoever picks this up.
// ===================================================================

// ===================================================================
// Rule 17: owl_rule_scm_eqc2 -- PROVED, after the guard-depth
// flattening (2026-08-05). Rule 16 above is the record of the depth-4
// failure on this exact rule; OWL.Closure.fsti's step now combines
// the self-loop test and the supers lookup into ONE boolean guard
// (depth 3, see the GUARD-DEPTH RULE comment there), and the same
// witness chain Rule 16 reported as "proves fine" now discharges the
// whole obligation. This proof is the on-real-code CONFIRMATION of
// the guard-depth diagnosis, and the template for unblocking the
// rest of the failing band (task #36).
// ===================================================================

val owl_rule_scm_eqc2_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_mutual_subclass_equivalent i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_scm_eqc2 g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_scm_eqc2_sound i a g ig =
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = rdfs_subClassOf then
      match t.s, t.o with
      | S_IRI c_iri, T_IRI d_iri ->
        let bucket = bucket_lookup ig.ig_sp (sp_key (S_IRI d_iri) rdfs_subClassOf) in
        let supers = find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf in
        if c_iri <> d_iri &&
           List.Tot.existsb (term_is_iri c_iri) supers
        then begin
          // (C sco D) semantically, from t itself.
          assert (triple_holds i a t);
          // The existsb hit names a served object x == T_IRI c_iri...
          FStar.List.Tot.Properties.memP_existsb (term_is_iri c_iri) supers;
          eliminate exists (x : rdf_term).
              term_is_iri c_iri x = true /\ List.Tot.memP x supers
          returns triple_holds i a
            ({ s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } <: triple)
          with _ . begin
            lemma_rdf_term_eq_iri x c_iri;
            // ...whose bucket triple u2 the sp index serves:
            // find_objects_indexed IS map (.o) over the sp bucket.
            assert_norm (find_objects_indexed ig (S_IRI d_iri) rdfs_subClassOf ==
                         List.Tot.map (fun (u : triple) -> u.o) bucket);
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) x bucket;
            eliminate exists (u2 : triple).
                List.Tot.memP u2 bucket /\ u2.o == x
            returns triple_holds i a
              ({ s = S_IRI c_iri; p = owl_equivalentClass; o = T_IRI d_iri } <: triple)
            with _ . begin
              // ig_wf_sp pins u2 as a real snapshot triple
              // (D sco C-term); the snapshot's truth makes it a
              // semantic edge; the condition closes both directions.
              assert (List.Tot.memP u2 ig.ig_triples /\
                      u2.s == S_IRI d_iri /\ u2.p == rdfs_subClassOf);
              assert (triple_holds i a u2);
              assert (i.iext (i.i_iri rdfs_subClassOf)
                             (i.i_iri d_iri) (i.i_iri c_iri));
              assert (i.iext (i.i_iri rdfs_subClassOf)
                             (i.i_iri c_iri) (i.i_iri d_iri))
            end
          end
        end
        else ()
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_scm_eqc2 g ig == List.Tot.fold_left emit_step g g)
#pop-options

// ===================================================================
// Rule 18: owl_rule_sameAs_replace_subject (eq-rep-s; OWL.Closure.fsti
// ~line 620). OWL 2 RL/RDF rules table row eq-rep-s: T(?s, owl:sameAs,
// ?s'), T(?s, ?p, ?o) => T(?s', ?p, ?o). #262's perf shape: an outer
// fold over the deduped snapshot pair list sameas_pairs ig, and for
// each pair (x, s'), an INNER fold over the ig_subj bucket keyed by
// subject_to_key x (the named emitter sameas_rep_subj_emit s'), so the
// proof shape mirrors Rule 2 (rdfs_rule_domain_sound): outer witness
// chain via lemma_sameas_pairs_hold / cond_sameas_identity, inner
// bucket-lookup truth via ig_wf_subj.
//
// Argument: for pair (x, s') the pair machinery gives IEXT(sameAs)(dx,
// ds') (lemma_sameas_pairs_hold); cond_sameas_identity's iff collapses
// dx == ds'. Each bucket triple t (ig_wf_subj pins t.s == x, t a real
// snapshot triple) holds semantically: IEXT(t.p)(dx, denot(t.o)). The
// emitted triple { s = s'; p = t.p; o = t.o } then holds because its
// subject denotes the SAME domain element as t's (dx == ds').
//
// GUARD: sameas_rep_subj_emit's `if t.p <> owl_sameAs` only NARROWS
// which bucket triples get replaced (skipping sameAs edges themselves
// to avoid re-deriving eq-sym's own conclusions here) — the argument
// above holds regardless of t.p, so the non-firing branch needs no
// extra semantic step, only holds_all i a acc2 unchanged (the
// hypothesis itself).
// ===================================================================

val owl_rule_sameAs_replace_subject_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_identity i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_subj ig)
    (ensures  holds_all i a (owl_rule_sameAs_replace_subject g ig))

let owl_rule_sameAs_replace_subject_sound i a g ig =
  lemma_sameas_pairs_hold i a ig;
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, s_prime) = xy in
      let srcs = bucket_lookup ig.ig_subj (subject_to_key x) in
      List.Tot.fold_left (sameas_rep_subj_emit s_prime) acc srcs in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc xy)
  with introduce (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc xy)
  with _ . begin
    let (x, s_prime) = xy in
    // sameas_pairs_hold gives IEXT(sameAs)(dx, ds'); cond_sameas_identity
    // collapses dx == ds'.
    assert (i.iext (i.i_iri owl_sameAs)
                   (denot_subject i a x) (denot_subject i a s_prime));
    assert (denot_subject i a x == denot_subject i a s_prime);
    let srcs = bucket_lookup ig.ig_subj (subject_to_key x) in
    let inner_step : rdf_graph -> triple -> rdf_graph = sameas_rep_subj_emit s_prime in
    introduce forall (acc2 : rdf_graph) (t : triple).
        (List.Tot.memP t srcs /\ holds_all i a acc2) ==>
        holds_all i a (inner_step acc2 t)
    with introduce (List.Tot.memP t srcs /\ holds_all i a acc2) ==>
                   holds_all i a (inner_step acc2 t)
    with _ . begin
      // ig_wf_subj at key x: t really is a snapshot triple with
      // subject x.
      assert (List.Tot.memP t ig.ig_triples /\ t.s == x);
      assert (triple_holds i a t);
      if t.p <> owl_sameAs then
        assert (i.iext (i.i_iri t.p)
                       (denot_subject i a s_prime) (denot_term i a t.o))
      else ()
    end;
    fold_left_inv (holds_all i a) inner_step srcs acc
  end;
  fold_left_inv (holds_all i a) outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_replace_subject g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))

// ===================================================================
// Rule 19: owl_rule_sameAs_replace_object (eq-rep-o; OWL.Closure.fsti
// ~line 644). OWL 2 RL/RDF rules table row eq-rep-o: T(?o, owl:sameAs,
// ?o'), T(?s, ?p, ?o) => T(?s, ?p, ?o'). Same #262 outer/inner fold
// shape as Rule 18, over the ig_obj bucket keyed by subject_to_key x
// this time (the named emitter sameas_rep_obj_emit, taking the
// partner's TERM y_term = subject_to_term y — the object position is
// rdf_term, not subject, so the proof needs the term/subject bridge
// lemmas lemma_denot_subject_to_term / lemma_denot_term_to_subject on
// both t.o (via ig_wf_obj's t.o == subject_to_term x) and y_term.
// ig_wf_obj is exactly the bucket shape this rule's engine code reads
// (subject-shaped key, per OWL.Semantics.fst's comment on ig_wf_obj).
//
// Argument: for pair (x, y) the pair machinery gives IEXT(sameAs)(dx,
// dy); cond_sameas_identity collapses dx == dy. Each bucket triple t
// (ig_wf_obj pins t.o == subject_to_term x, t a real snapshot triple)
// holds semantically: IEXT(t.p)(denot(t.s), dx) (denot_term i a t.o ==
// dx via lemma_denot_subject_to_term). The emitted triple { s = t.s;
// p = t.p; o = y_term } then holds because y_term denotes the SAME
// domain element as x's partner y, which IS x's own denotation.
//
// GUARD: sameas_rep_obj_emit's `if t.p <> owl_sameAs` narrows the same
// way Rule 18's does — no extra semantic argument for the non-firing
// branch.
// ===================================================================

val owl_rule_sameAs_replace_object_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_identity i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_obj ig)
    (ensures  holds_all i a (owl_rule_sameAs_replace_object g ig))

let owl_rule_sameAs_replace_object_sound i a g ig =
  lemma_sameas_pairs_hold i a ig;
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let y_term = subject_to_term y in
      let srcs = bucket_lookup ig.ig_obj (subject_to_key x) in
      List.Tot.fold_left (sameas_rep_obj_emit y_term) acc srcs in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc xy)
  with introduce (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc xy)
  with _ . begin
    let (x, y) = xy in
    let y_term = subject_to_term y in
    // sameas_pairs_hold gives IEXT(sameAs)(dx, dy); cond_sameas_identity
    // collapses dx == dy.
    assert (i.iext (i.i_iri owl_sameAs)
                   (denot_subject i a x) (denot_subject i a y));
    assert (denot_subject i a x == denot_subject i a y);
    lemma_denot_subject_to_term i a y;
    assert (denot_term i a y_term == denot_subject i a y);
    let srcs = bucket_lookup ig.ig_obj (subject_to_key x) in
    let inner_step : rdf_graph -> triple -> rdf_graph = sameas_rep_obj_emit y_term in
    introduce forall (acc2 : rdf_graph) (t : triple).
        (List.Tot.memP t srcs /\ holds_all i a acc2) ==>
        holds_all i a (inner_step acc2 t)
    with introduce (List.Tot.memP t srcs /\ holds_all i a acc2) ==>
                   holds_all i a (inner_step acc2 t)
    with _ . begin
      // ig_wf_obj at key x: t really is a snapshot triple whose object
      // denotes x.
      assert (List.Tot.memP t ig.ig_triples /\ t.o == subject_to_term x);
      assert (triple_holds i a t);
      lemma_denot_subject_to_term i a x;
      assert (denot_term i a t.o == denot_subject i a x);
      if t.p <> owl_sameAs then
        assert (i.iext (i.i_iri t.p)
                       (denot_subject i a t.s) (denot_term i a y_term))
      else ()
    end;
    fold_left_inv (holds_all i a) inner_step srcs acc
  end;
  fold_left_inv (holds_all i a) outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_replace_object g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))

// ===================================================================
// Rule 20: owl_rule_sameAs_replace_predicate (eq-rep-p; OWL.Closure.
// fsti ~line 665). OWL 2 RL/RDF rules table row eq-rep-p: T(?p,
// owl:sameAs, ?p'), T(?s, ?p, ?o) => T(?s, ?p', ?o). Same #262
// outer/inner fold shape again, this time over the ig_pred bucket
// keyed by the RAW predicate IRI p_iri (the named emitter
// sameas_rep_pred_emit p_prime_iri) — mirroring Rule 2's ig_pred
// bucket-lookup idiom directly, since predicates are IRIs and need no
// term/subject bridge. The engine rule reads the pair ONLY when both
// sides are S_IRI (predicates cannot be blank nodes or literals); the
// sameas_pairs machinery already guarantees the pair denotes via
// denot_subject on S_IRI, which unfolds to i.i_iri directly.
//
// Argument: for pair (S_IRI p_iri, S_IRI p_prime_iri) the pair
// machinery gives IEXT(sameAs)(I(p_iri), I(p_prime_iri));
// cond_sameas_identity collapses I(p_iri) == I(p_prime_iri). Each
// bucket triple t (ig_wf_pred pins t.p == p_iri, t a real snapshot
// triple) holds semantically: IEXT(I(p_iri))(denot(t.s), denot(t.o)).
// The emitted triple { s = t.s; p = p_prime_iri; o = t.o } then holds
// because I(p_prime_iri) IS I(p_iri) at the domain-element level.
//
// GUARD: the engine's `if is_owl_metapredicate p_iri then acc` only
// NARROWS which pairs are processed (skipping the six OWL vocabulary
// predicates Group E(a) already handles via owl_rule_symmetric_
// metapredicates, so eq-rep-p does not re-derive their sameAs-driven
// replacements) — the argument above is unaffected by which p_iri
// fires, so the non-firing branch needs no extra semantic step.
// ===================================================================

val owl_rule_sameAs_replace_predicate_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_identity i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_pred ig)
    (ensures  holds_all i a (owl_rule_sameAs_replace_predicate g ig))

let owl_rule_sameAs_replace_predicate_sound i a g ig =
  lemma_sameas_pairs_hold i a ig;
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
      (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc xy)
  with introduce (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc xy)
  with _ . begin
    match xy with
    | (S_IRI p_iri, S_IRI p_prime_iri) ->
      if is_owl_metapredicate p_iri then ()
      else begin
        // sameas_pairs_hold gives IEXT(sameAs)(I(p_iri), I(p_prime_iri))
        // (denot_subject on S_IRI unfolds to i_iri); cond_sameas_identity
        // collapses the two denotations.
        assert (i.iext (i.i_iri owl_sameAs)
                       (i.i_iri p_iri) (i.i_iri p_prime_iri));
        assert (i.i_iri p_iri == i.i_iri p_prime_iri);
        let srcs = bucket_lookup ig.ig_pred p_iri in
        let inner_step : rdf_graph -> triple -> rdf_graph =
          sameas_rep_pred_emit p_prime_iri in
        introduce forall (acc2 : rdf_graph) (t : triple).
            (List.Tot.memP t srcs /\ holds_all i a acc2) ==>
            holds_all i a (inner_step acc2 t)
        with introduce (List.Tot.memP t srcs /\ holds_all i a acc2) ==>
                       holds_all i a (inner_step acc2 t)
        with _ . begin
          // ig_wf_pred at key p_iri: t really is an (x p_iri y) data
          // triple.
          assert (List.Tot.memP t ig.ig_triples /\ t.p == p_iri);
          assert (triple_holds i a t);
          assert (i.iext (i.i_iri p_prime_iri)
                         (denot_subject i a t.s) (denot_term i a t.o))
        end;
        fold_left_inv (holds_all i a) inner_step srcs acc
      end
    | _ -> ()
  end;
  fold_left_inv (holds_all i a) outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_replace_predicate g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))

// ===================================================================
// Rule 21: owl_rule_scm_eqp2 (scm-eqp2; OWL.Closure.fsti ~line 307) --
// PROVED, mirroring Rule 17's guard-depth-flattened scm-eqc2 proof
// exactly (Table 5.9's equivalentProperty condition instead of Table
// 5.8's equivalentClass; rdfs:subPropertyOf instead of
// rdfs:subClassOf). The engine rule already carries the PROOF-FRIENDLY
// GUARD RULE flatten (one boolean guard, named partial application
// `term_is_iri p_iri`), so this is a same-shape instance of the Rule
// 17 skeleton, not a fresh diagnosis.
// ===================================================================

val owl_rule_scm_eqp2_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_mutual_subproperty_equivalent i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_scm_eqp2 g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_scm_eqp2_sound i a g ig =
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (emit_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (emit_step acc t)
  with _ . begin
    if t.p = rdfs_subPropertyOf then
      match t.s, t.o with
      | S_IRI p_iri, T_IRI q_iri ->
        let bucket = bucket_lookup ig.ig_sp (sp_key (S_IRI q_iri) rdfs_subPropertyOf) in
        let supers = find_objects_indexed ig (S_IRI q_iri) rdfs_subPropertyOf in
        if p_iri <> q_iri &&
           List.Tot.existsb (term_is_iri p_iri) supers
        then begin
          // (P spo Q) semantically, from t itself.
          assert (triple_holds i a t);
          // The existsb hit names a served object x == T_IRI p_iri...
          FStar.List.Tot.Properties.memP_existsb (term_is_iri p_iri) supers;
          eliminate exists (x : rdf_term).
              term_is_iri p_iri x = true /\ List.Tot.memP x supers
          returns triple_holds i a
            ({ s = S_IRI p_iri; p = owl_equivalentProperty; o = T_IRI q_iri } <: triple)
          with _ . begin
            lemma_rdf_term_eq_iri x p_iri;
            // ...whose bucket triple u2 the sp index serves:
            // find_objects_indexed IS map (.o) over the sp bucket.
            assert_norm (find_objects_indexed ig (S_IRI q_iri) rdfs_subPropertyOf ==
                         List.Tot.map (fun (u : triple) -> u.o) bucket);
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) x bucket;
            eliminate exists (u2 : triple).
                List.Tot.memP u2 bucket /\ u2.o == x
            returns triple_holds i a
              ({ s = S_IRI p_iri; p = owl_equivalentProperty; o = T_IRI q_iri } <: triple)
            with _ . begin
              // ig_wf_sp pins u2 as a real snapshot triple
              // (Q spo P-term); the snapshot's truth makes it a
              // semantic edge; the condition closes both directions.
              assert (List.Tot.memP u2 ig.ig_triples /\
                      u2.s == S_IRI q_iri /\ u2.p == rdfs_subPropertyOf);
              assert (triple_holds i a u2);
              assert (i.iext (i.i_iri rdfs_subPropertyOf)
                             (i.i_iri q_iri) (i.i_iri p_iri));
              assert (i.iext (i.i_iri rdfs_subPropertyOf)
                             (i.i_iri p_iri) (i.i_iri q_iri))
            end
          end
        end
        else ()
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) emit_step g g;
  assert_norm (owl_rule_scm_eqp2 g ig == List.Tot.fold_left emit_step g g)
#pop-options

// ===================================================================
// Rule 22: owl_rule_sameAs_transitivity (eq-trans; OWL.Closure.fsti
// ~line 598). OWL 2 RL/RDF rules table row eq-trans: T(?x, owl:sameAs,
// ?y), T(?y, owl:sameAs, ?z) => T(?x, owl:sameAs, ?z). #262's outer
// fold over the deduped snapshot pair list (sameas_pairs ig); for each
// pair (x, y), an INNER fold over the ig_sp bucket at key (y,
// owl:sameAs) via find_objects_indexed (the named emitter
// sameas_trans_emit x), mirroring Rule 2's ig_pred bucket-lookup idiom
// but through ig_sp / find_objects_indexed instead (same bridge shape
// as decode_iri_list_sound's per-hop bucket reads).
//
// Argument: for pair (x, y) the pair machinery gives IEXT(sameAs)(dx,
// dy) (lemma_sameas_pairs_hold); cond_sameas_identity's iff (both
// directions used here, unlike Rules 18-20 which only need the
// forward COLLAPSE half) turns that into dx == dy. Each bucket triple
// t serving zs (ig_wf_sp pins t.s == y, t.p == owl_sameAs, a real
// snapshot triple) holds semantically: IEXT(sameAs)(dy, denot(t.o));
// cond_sameas_identity's forward half collapses dy == denot(t.o).
// Chaining dx == dy == denot(t.o) and cond_sameas_identity's backward
// half re-introduces the emitted edge IEXT(sameAs)(dx, denot(t.o)) --
// exactly the transitivity chain the row states, carried entirely by
// the identity condition rather than a dedicated cond_sameas_transitive
// (the iff is strong enough on its own, unlike cond_transitive below
// which needs its own dedicated condition since IEXT is not assumed to
// be an equivalence relation in general).
// ===================================================================

val owl_rule_sameAs_transitivity_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_sameas_identity i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_sameAs_transitivity g ig))

let owl_rule_sameAs_transitivity_sound i a g ig =
  lemma_sameas_pairs_hold i a ig;
  let outer_step : rdf_graph -> (subject * subject) -> rdf_graph =
    fun (acc : rdf_graph) (xy : subject * subject) ->
      let (x, y) = xy in
      let zs = find_objects_indexed ig y owl_sameAs in
      List.Tot.fold_left (sameas_trans_emit x) acc zs in
  introduce forall (acc : rdf_graph) (xy : subject * subject).
      (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc xy)
  with introduce (List.Tot.memP xy (sameas_pairs ig) /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc xy)
  with _ . begin
    let (x, y) = xy in
    // sameas_pairs_hold gives IEXT(sameAs)(dx, dy); cond_sameas_identity
    // collapses dx == dy.
    assert (i.iext (i.i_iri owl_sameAs)
                   (denot_subject i a x) (denot_subject i a y));
    assert (denot_subject i a x == denot_subject i a y);
    let bucket = bucket_lookup ig.ig_sp (sp_key y owl_sameAs) in
    let zs = find_objects_indexed ig y owl_sameAs in
    assert (zs == List.Tot.map (fun (u : triple) -> u.o) bucket);
    let inner_step : rdf_graph -> rdf_term -> rdf_graph = sameas_trans_emit x in
    introduce forall (acc2 : rdf_graph) (z_term : rdf_term).
        (List.Tot.memP z_term zs /\ holds_all i a acc2) ==>
        holds_all i a (inner_step acc2 z_term)
    with introduce (List.Tot.memP z_term zs /\ holds_all i a acc2) ==>
                   holds_all i a (inner_step acc2 z_term)
    with _ . begin
      FStar.List.Tot.Properties.memP_map_elim (fun (u : triple) -> u.o) z_term bucket;
      eliminate exists (u : triple). List.Tot.memP u bucket /\ u.o == z_term
      returns holds_all i a (inner_step acc2 z_term)
      with _ . begin
        // ig_wf_sp at key (y, owl_sameAs): u really is a real snapshot
        // triple.
        assert (List.Tot.memP u ig.ig_triples /\ u.s == y /\ u.p == owl_sameAs);
        assert (triple_holds i a u);
        assert (i.iext (i.i_iri owl_sameAs)
                       (denot_subject i a y) (denot_term i a z_term));
        // cond_sameas_identity forward, then chain, then backward:
        // dy == denot(z_term); dx == dy; so dx == denot(z_term); the
        // iff's backward half re-derives the emitted edge.
        assert (denot_subject i a y == denot_term i a z_term);
        assert (denot_subject i a x == denot_term i a z_term);
        assert (i.iext (i.i_iri owl_sameAs)
                       (denot_subject i a x) (denot_term i a z_term))
      end
    end;
    fold_left_inv (holds_all i a) inner_step zs acc
  end;
  fold_left_inv (holds_all i a) outer_step (sameas_pairs ig) g;
  assert_norm (owl_rule_sameAs_transitivity g ig ==
               List.Tot.fold_left outer_step g (sameas_pairs ig))

// ===================================================================
// Rule 23: owl_rule_transitive_property (prp-trp; OWL.Closure.fsti
// ~line 366). OWL 2 RL/RDF rules table row prp-trp: T(?p, rdf:type,
// owl:TransitiveProperty), T(?x, ?p, ?y), T(?y, ?p, ?z) => T(?x, ?p,
// ?z). Same collect-then-emit two-fold shape as Rule 1
// (owl_rule_symmetric_property): a collection fold over g gathers
// trans_props (trans_props_sound mirrors sym_props_sound exactly),
// then a NESTED-SINGLE emission fold over g -- for every triple t
// whose predicate is transitive, an inner fold over find_objects_indexed
// ig y_subj t.p (the same ig_sp / bucket-map bridge Rule 22 and
// decode_iri_list_sound use) emits (t.s, t.p, z) per successor z of
// y_subj := term_to_subject t.o. Licensing sibling
// (OWL.RL.Refinement.fst, prp-trp) is the FIRST NESTED-SINGLE
// licensing proof and the proof-friendly-guard-rule precedent; this
// truth proof is its semantic mirror, one indexed-lookup deeper than
// Rule 1's flat collect-then-emit.
// ===================================================================

let trans_props_sound (i : interp) (a : bnode_assignment i.idom) (ps : list wf_iri) : prop =
  forall (p : wf_iri). List.Tot.mem p ps ==>
    icext i (i.i_iri p) (i.i_iri owl_TransitiveProperty)

val owl_rule_transitive_property_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_transitive i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_transitive_property g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_transitive_property_sound i a g ig =
  let collect_step : list wf_iri -> triple -> list wf_iri =
    fun (acc : list wf_iri) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_TransitiveProperty) then
        match t.s with
        | S_IRI p_iri -> cons_if_new_iri p_iri acc
        | _ -> acc
      else acc in
  let trans_props = List.Tot.fold_left collect_step [] g in
  introduce forall (acc : list wf_iri) (t : triple).
      (List.Tot.memP t g /\ trans_props_sound i a acc) ==>
      trans_props_sound i a (collect_step acc t)
  with introduce (List.Tot.memP t g /\ trans_props_sound i a acc) ==>
                 trans_props_sound i a (collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_TransitiveProperty) then begin
      lemma_rdf_term_eq_iri t.o owl_TransitiveProperty;
      assert (triple_holds i a t)
    end else ()
  end;
  fold_left_inv (trans_props_sound i a) collect_step g [];
  assert (trans_props_sound i a trans_props);
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (outer_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc t)
  with _ . begin
    if List.Tot.mem t.p trans_props then begin
      assert (icext i (i.i_iri t.p) (i.i_iri owl_TransitiveProperty));
      match term_to_subject t.o with
      | Some y_subj ->
        lemma_denot_term_to_subject i a t.o y_subj;
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri t.p)
                       (denot_subject i a t.s) (denot_subject i a y_subj));
        let bucket = bucket_lookup ig.ig_sp (sp_key y_subj t.p) in
        let zs = find_objects_indexed ig y_subj t.p in
        assert (zs == List.Tot.map (fun (u : triple) -> u.o) bucket);
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (z_term : rdf_term) ->
            let new_t : triple = { s = t.s; p = t.p; o = z_term } in
            add_triple_unchecked acc2 new_t in
        introduce forall (acc2 : rdf_graph) (z_term : rdf_term).
            (List.Tot.memP z_term zs /\ holds_all i a acc2) ==>
            holds_all i a (inner_step acc2 z_term)
        with introduce (List.Tot.memP z_term zs /\ holds_all i a acc2) ==>
                       holds_all i a (inner_step acc2 z_term)
        with _ . begin
          FStar.List.Tot.Properties.memP_map_elim (fun (u : triple) -> u.o) z_term bucket;
          eliminate exists (u : triple). List.Tot.memP u bucket /\ u.o == z_term
          returns holds_all i a (inner_step acc2 z_term)
          with _ . begin
            // ig_wf_sp at key (y_subj, t.p): u really is a real
            // snapshot triple.
            assert (List.Tot.memP u ig.ig_triples /\ u.s == y_subj /\ u.p == t.p);
            assert (triple_holds i a u);
            assert (i.iext (i.i_iri t.p)
                           (denot_subject i a y_subj) (denot_term i a z_term));
            // cond_transitive closes the chain: t.s -P-> y_subj -P-> z.
            assert (i.iext (i.i_iri t.p)
                           (denot_subject i a t.s) (denot_term i a z_term))
          end
        end;
        fold_left_inv (holds_all i a) inner_step zs acc
      | None -> ()
    end else ()
  end;
  fold_left_inv (holds_all i a) outer_step g g;
  assert_norm (owl_rule_transitive_property g ig == List.Tot.fold_left outer_step g g)
#pop-options

// ===================================================================
// Rule 24: owl_rule_functional (prp-fp; OWL.Closure.fsti ~line 740).
// OWL 2 RL/RDF rules table row prp-fp: T(?p, rdf:type,
// owl:FunctionalProperty), T(?x, ?p, ?y1), T(?x, ?p, ?y2) => T(?y1,
// owl:sameAs, ?y2). Every fold level of the engine rule is already a
// NAMED top-level function (task #36 lambda-lift, OWL.Closure.fsti's
// own banner on this rule): owl_prp_fp_collect_step / owl_prp_fp_step
// / owl_prp_fp_emit. This proof references those SAME symbols
// directly (no local re-elaboration of the collect/step/emit
// closures), so there is no closure-identity gap to bridge at any
// level -- the cleanest of the seven target rules for exactly that
// reason.
//
// Argument: fp_props_sound mirrors sym_props_sound / trans_props_sound
// (the collect fold gathers only IRIs really typed
// owl:FunctionalProperty in g). For the emission fold, fixing t1 with
// t1.p in fp_props and y_subj := term_to_subject t1.o (t1's own
// object, reused as the "first witness" throughout): cond_functional
// (icext i (i.i_iri t1.p) FunctionalProperty; iext p (denot t1.s)
// (denot y_subj); iext p (denot t1.s) (denot z), for z ranging over
// find_objects_indexed ig t1.s t1.p) gives denot y_subj == denot z at
// the DOMAIN-ELEMENT level (the row's actual semantic content); the
// engine's guard `if rdf_term_eq z t1.o then acc2` only skips emitting
// the self pair (already true trivially, no argument needed for the
// no-op branch); the surviving branch's emission owl_prp_fp_emit's
// { s = y_subj; p = owl_sameAs; o = z } then holds via
// cond_sameas_identity's backward half applied to the domain-element
// identity cond_functional just gave.
// ===================================================================

let fp_props_sound (i : interp) (a : bnode_assignment i.idom) (ps : list wf_iri) : prop =
  forall (p : wf_iri). List.Tot.mem p ps ==>
    icext i (i.i_iri p) (i.i_iri owl_FunctionalProperty)

val owl_rule_functional_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_functional i /\ cond_sameas_identity i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_functional g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_functional_sound i a g ig =
  let fp_props = List.Tot.fold_left owl_prp_fp_collect_step [] g in
  introduce forall (acc : list wf_iri) (t : triple).
      (List.Tot.memP t g /\ fp_props_sound i a acc) ==>
      fp_props_sound i a (owl_prp_fp_collect_step acc t)
  with introduce (List.Tot.memP t g /\ fp_props_sound i a acc) ==>
                 fp_props_sound i a (owl_prp_fp_collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_FunctionalProperty) then begin
      lemma_rdf_term_eq_iri t.o owl_FunctionalProperty;
      assert (triple_holds i a t)
    end else ()
  end;
  fold_left_inv (fp_props_sound i a) owl_prp_fp_collect_step g [];
  assert (fp_props_sound i a fp_props);
  introduce forall (acc : rdf_graph) (t1 : triple).
      (List.Tot.memP t1 g /\ holds_all i a acc) ==>
      holds_all i a (owl_prp_fp_step ig fp_props acc t1)
  with introduce (List.Tot.memP t1 g /\ holds_all i a acc) ==>
                 holds_all i a (owl_prp_fp_step ig fp_props acc t1)
  with _ . begin
    if List.Tot.mem t1.p fp_props then begin
      assert (icext i (i.i_iri t1.p) (i.i_iri owl_FunctionalProperty));
      match term_to_subject t1.o with
      | None -> ()
      | Some y_subj ->
        lemma_denot_term_to_subject i a t1.o y_subj;
        assert (triple_holds i a t1);
        assert (i.iext (i.i_iri t1.p)
                       (denot_subject i a t1.s) (denot_subject i a y_subj));
        let bucket = bucket_lookup ig.ig_sp (sp_key t1.s t1.p) in
        let zs = find_objects_indexed ig t1.s t1.p in
        assert (zs == List.Tot.map (fun (u : triple) -> u.o) bucket);
        introduce forall (acc2 : rdf_graph) (z : rdf_term).
            (List.Tot.memP z zs /\ holds_all i a acc2) ==>
            holds_all i a (owl_prp_fp_emit y_subj t1.o acc2 z)
        with introduce (List.Tot.memP z zs /\ holds_all i a acc2) ==>
                       holds_all i a (owl_prp_fp_emit y_subj t1.o acc2 z)
        with _ . begin
          if rdf_term_eq z t1.o then ()
          else begin
            FStar.List.Tot.Properties.memP_map_elim (fun (u : triple) -> u.o) z bucket;
            eliminate exists (u : triple). List.Tot.memP u bucket /\ u.o == z
            returns holds_all i a (owl_prp_fp_emit y_subj t1.o acc2 z)
            with _ . begin
              assert (List.Tot.memP u ig.ig_triples /\ u.s == t1.s /\ u.p == t1.p);
              assert (triple_holds i a u);
              assert (i.iext (i.i_iri t1.p)
                             (denot_subject i a t1.s) (denot_term i a z));
              // cond_functional: two objects of the same functional-
              // property edge from x denote the same domain element.
              assert (denot_subject i a y_subj == denot_term i a z);
              // cond_sameas_identity backward: equal denotations give
              // the emitted sameAs edge.
              assert (i.iext (i.i_iri owl_sameAs)
                             (denot_subject i a y_subj) (denot_term i a z))
            end
          end
        end;
        fold_left_inv (holds_all i a) (owl_prp_fp_emit y_subj t1.o) zs acc
    end else ()
  end;
  fold_left_inv (holds_all i a) (owl_prp_fp_step ig fp_props) g g;
  assert_norm (owl_rule_functional g ig ==
               List.Tot.fold_left (owl_prp_fp_step ig fp_props) g g)
#pop-options

// ===================================================================
// Rule 25: owl_rule_inverse_functional (prp-ifp; OWL.Closure.fsti
// ~line 771). OWL 2 RL/RDF rules table row prp-ifp: T(?p, rdf:type,
// owl:InverseFunctionalProperty), T(?x1, ?p, ?y), T(?x2, ?p, ?y) =>
// T(?x1, owl:sameAs, ?x2). Same named-top-level-function shape as
// Rule 24 (owl_prp_ifp_collect_step / owl_prp_ifp_step /
// owl_prp_ifp_emit, task #36 lambda-lift), but the inner lookup is
// `find_subjects_indexed ig t1.p t1.o` -- the po/pred two-branch
// index read OWL.RL.Refinement.fst's licensing proof (section 25)
// already carries a full provenance lemma for
// (`lemma_find_subjects_indexed_wf`, requiring `ig_wf_po`, `ig_wf_pred`,
// and the literal-fallback side condition `graph_literal_match_exact`
// the registry's hypothesis column names). REUSED HERE VERBATIM via
// `open OWL.RL.Refinement` rather than re-derived: it already produces
// exactly the witness triple u2 (memP u2 g /\ u2.p == t1.p /\ u2.o ==
// t1.o /\ u2.s == z) this truth proof needs, so no separate po/literal
// case split is written in this file.
//
// Argument: for firing t1 (t1.p in ifp_props) and z in
// find_subjects_indexed ig t1.p t1.o with z <> t1.s,
// lemma_find_subjects_indexed_wf gives a real snapshot triple u2 with
// u2.p == t1.p, u2.o == t1.o, u2.s == z -- so u2 and t1 are TWO
// DIFFERENT subjects (z, t1.s) related to the SAME object under the
// SAME inverse-functional property. cond_inverse_functional (mirroring
// cond_functional's shape, symmetric in the two edges instead of the
// two objects) collapses denot z == denot t1.s at the domain-element
// level; cond_sameas_identity's backward half turns that into the
// emitted { s = t1.s; p = owl_sameAs; o = subject_to_term z } edge.
// ===================================================================

// owl:InverseFunctionalProperty -- OWL 2 RDF-Based Semantics Table
// 5.14 (property characteristics), if-direction: membership in
// ICEXT(I(owl:InverseFunctionalProperty)) makes the extension
// injective -- two subjects related to the same object under an
// inverse-functional property are the SAME domain element. Mirrors
// cond_functional, symmetric in which side of the pair is held fixed
// (object instead of subject).
let cond_inverse_functional (i : interp) : prop =
  forall (p x1 x2 y : i.idom).
    icext i p (i.i_iri owl_InverseFunctionalProperty) ==>
    i.iext p x1 y ==> i.iext p x2 y ==> x1 == x2

let ifp_props_sound (i : interp) (a : bnode_assignment i.idom) (ps : list wf_iri) : prop =
  forall (p : wf_iri). List.Tot.mem p ps ==>
    icext i (i.i_iri p) (i.i_iri owl_InverseFunctionalProperty)

val owl_rule_inverse_functional_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_inverse_functional i /\ cond_sameas_identity i /\ holds_all i a g /\
              ig.ig_triples == g /\ ig_wf_po ig /\ ig_wf_pred ig /\
              graph_literal_match_exact g)
    (ensures  holds_all i a (owl_rule_inverse_functional g ig))

#push-options "--z3rlimit 200 --split_queries always"
let owl_rule_inverse_functional_sound i a g ig =
  let ifp_props = List.Tot.fold_left owl_prp_ifp_collect_step [] g in
  introduce forall (acc : list wf_iri) (t : triple).
      (List.Tot.memP t g /\ ifp_props_sound i a acc) ==>
      ifp_props_sound i a (owl_prp_ifp_collect_step acc t)
  with introduce (List.Tot.memP t g /\ ifp_props_sound i a acc) ==>
                 ifp_props_sound i a (owl_prp_ifp_collect_step acc t)
  with _ . begin
    if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_InverseFunctionalProperty) then begin
      lemma_rdf_term_eq_iri t.o owl_InverseFunctionalProperty;
      assert (triple_holds i a t)
    end else ()
  end;
  fold_left_inv (ifp_props_sound i a) owl_prp_ifp_collect_step g [];
  assert (ifp_props_sound i a ifp_props);
  introduce forall (acc : rdf_graph) (t1 : triple).
      (List.Tot.memP t1 g /\ holds_all i a acc) ==>
      holds_all i a (owl_prp_ifp_step ig ifp_props acc t1)
  with introduce (List.Tot.memP t1 g /\ holds_all i a acc) ==>
                 holds_all i a (owl_prp_ifp_step ig ifp_props acc t1)
  with _ . begin
    if List.Tot.mem t1.p ifp_props then begin
      assert (icext i (i.i_iri t1.p) (i.i_iri owl_InverseFunctionalProperty));
      assert (triple_holds i a t1);
      let zs = find_subjects_indexed ig t1.p t1.o in
      introduce forall (acc2 : rdf_graph) (z : subject).
          (List.Tot.memP z zs /\ holds_all i a acc2) ==>
          holds_all i a (owl_prp_ifp_emit t1.s acc2 z)
      with introduce (List.Tot.memP z zs /\ holds_all i a acc2) ==>
                     holds_all i a (owl_prp_ifp_emit t1.s acc2 z)
      with _ . begin
        if subject_eq z t1.s then ()
        else begin
          lemma_find_subjects_indexed_wf ig g t1 z;
          eliminate exists (u2 : triple).
              List.Tot.memP u2 g /\ u2.p == t1.p /\ u2.o == t1.o /\ u2.s == z
          returns holds_all i a (owl_prp_ifp_emit t1.s acc2 z)
          with _ . begin
            assert (triple_holds i a u2);
            assert (i.iext (i.i_iri t1.p)
                           (denot_subject i a z) (denot_term i a t1.o));
            assert (i.iext (i.i_iri t1.p)
                           (denot_subject i a t1.s) (denot_term i a t1.o));
            // cond_inverse_functional: two subjects of the same
            // inverse-functional edge to y denote the same domain
            // element.
            assert (denot_subject i a z == denot_subject i a t1.s);
            // cond_sameas_identity backward: equal denotations give
            // the emitted sameAs edge.
            assert (i.iext (i.i_iri owl_sameAs)
                           (denot_subject i a t1.s) (denot_subject i a z))
          end
        end
      end;
      fold_left_inv (holds_all i a) (owl_prp_ifp_emit t1.s) zs acc
    end else ()
  end;
  fold_left_inv (holds_all i a) (owl_prp_ifp_step ig ifp_props) g g;
  assert_norm (owl_rule_inverse_functional g ig ==
               List.Tot.fold_left (owl_prp_ifp_step ig ifp_props) g g)
#pop-options

// ===================================================================
// Rule 26: owl_rule_inverse_of (prp-inv1 + prp-inv2; OWL.Closure.fsti
// ~line 458). OWL 2 RL/RDF rules table rows prp-inv1: T(?P1,
// owl:inverseOf, ?P2), T(?x, ?P1, ?y) => T(?y, ?P2, ?x); prp-inv2:
// same premise, T(?x, ?P2, ?y) => T(?y, ?P1, ?x). NESTED-PAIR shape,
// the licensing sibling's own precedent for the closure-identity fix
// (task #36, `OWL.Closure.inverse_of_emit`, the FIRST rule proved
// after the nested-pair obstruction was diagnosed): an outer fold over
// g finds owl:inverseOf declarations (P1, P2); for each, an INNER fold
// over ALL of g applies the NAMED top-level emitter `inverse_of_emit
// p1_iri p2_iri`, which itself tests t.p against p1_iri then p2_iri
// and flips the matching edge -- both prp-inv1 and prp-inv2 come out
// of the SAME inner fold, one per branch of inverse_of_emit's guard.
// This truth proof references `inverse_of_emit` directly (the engine's
// own named symbol), so the inner step obligation is exactly Rule 20's
// nested-pair shape with the closure-identity risk already retired by
// the engine's own lambda-lift.
//
// Argument: cond_inverse_of's iff (iext p x y <==> iext q y x) is
// symmetric in which of P1/P2 fires -- instantiating it with (p, q) :=
// (denot P1, denot P2) covers the forward branch (t.p = p1_iri) via
// the iff's -> direction, and instantiating the SAME iff at (x, y) :=
// (denot new_subj, denot t.s) covers the backward branch (t.p =
// p2_iri) via the iff's <- direction read the other way -- no second
// condition needed, unlike cond_functional/cond_inverse_functional
// above which are genuinely one-directional per table row.
// ===================================================================

val owl_rule_inverse_of_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_inverse_of i /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_inverse_of g ig))

#push-options "--z3rlimit 100 --split_queries always"
let owl_rule_inverse_of_sound i a g ig =
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (inv_t : triple) ->
      if inv_t.p = owl_inverseOf then
        match inv_t.s, inv_t.o with
        | S_IRI p1_iri, T_IRI p2_iri ->
          List.Tot.fold_left (inverse_of_emit p1_iri p2_iri) acc g
        | _, _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (inv_t : triple).
      (List.Tot.memP inv_t g /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc inv_t)
  with introduce (List.Tot.memP inv_t g /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc inv_t)
  with _ . begin
    if inv_t.p = owl_inverseOf then
      match inv_t.s, inv_t.o with
      | S_IRI p1_iri, T_IRI p2_iri ->
        assert (triple_holds i a inv_t);
        assert (i.iext (i.i_iri owl_inverseOf) (i.i_iri p1_iri) (i.i_iri p2_iri));
        let inner_step : rdf_graph -> triple -> rdf_graph =
          inverse_of_emit p1_iri p2_iri in
        introduce forall (acc2 : rdf_graph) (t : triple).
            (List.Tot.memP t g /\ holds_all i a acc2) ==>
            holds_all i a (inner_step acc2 t)
        with introduce (List.Tot.memP t g /\ holds_all i a acc2) ==>
                       holds_all i a (inner_step acc2 t)
        with _ . begin
          assert (triple_holds i a t);
          if t.p = p1_iri then
            match term_to_subject t.o with
            | Some new_subj ->
              lemma_denot_term_to_subject i a t.o new_subj;
              lemma_denot_subject_to_term i a t.s;
              assert (i.iext (i.i_iri p1_iri)
                             (denot_subject i a t.s) (denot_subject i a new_subj));
              // cond_inverse_of forward direction.
              assert (i.iext (i.i_iri p2_iri)
                             (denot_subject i a new_subj) (denot_subject i a t.s))
            | None -> ()
          else if t.p = p2_iri then
            match term_to_subject t.o with
            | Some new_subj ->
              lemma_denot_term_to_subject i a t.o new_subj;
              lemma_denot_subject_to_term i a t.s;
              assert (i.iext (i.i_iri p2_iri)
                             (denot_subject i a t.s) (denot_subject i a new_subj));
              // cond_inverse_of backward direction (same iff, read the
              // other way).
              assert (i.iext (i.i_iri p1_iri)
                             (denot_subject i a new_subj) (denot_subject i a t.s))
            | None -> ()
          else ()
        end;
        fold_left_inv (holds_all i a) inner_step g acc
      | _, _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) outer_step g g;
  assert_norm (owl_rule_inverse_of g ig == List.Tot.fold_left outer_step g g)
#pop-options

// ===================================================================
// Rule 27: owl_rule_prp_key (prp-key; OWL.Closure.fsti ~line 3422).
// OWL 2 RL/RDF rules table row prp-key: T(?c, owl:hasKey,
// LIST(?p1..?pn)), T(?x, rdf:type, ?c), T(?y, rdf:type, ?c), and for
// each ?pi, exists ?vi. T(?x, ?pi, ?vi), T(?y, ?pi, ?vi) => T(?x,
// owl:sameAs, ?y). WEAKENED-ROW: as the licensing sibling
// (OWL.RL.Refinement.fst section 23, `owl_rule_prp_key_licensed`)
// found and the registry records (docs/theorem-registry.md, prp-key
// row), the engine's `agree_on_property` tests key-value agreement via
// `rdf_term_eq` (RDF 1.1 term equality: case-insensitive language
// tags, XMLLiteral c14n) where the literal table row's `?vi` premise
// reads as plain structural identity -- a machine-checked
// counterexample (`lemma_agree_on_property_overapproximates_shares_
// key_values`) shows two DISTINCT wf_literal values the engine accepts
// as "the same value ?vi" the row's literal premise would not. This
// truth proof closes that gap on the SEMANTIC side rather than
// weakening the statement further: `cond_literal_term_eq_respecting`
// (OWL.Semantics.fst) plus `lemma_rdf_term_eq_denot` establish that
// rdf_term_eq-equal literals denote the SAME domain element under any
// genuine interpretation (RDF 1.1 Concepts SS3.3 already treats
// case-different-but-equal language tags as naming the SAME abstract
// literal term, not two co-denoting ones) -- so the "extra" pairs the
// engine's rdf_term_eq accepts are not spurious relative to the TRUE
// semantic premise `exists v. T(x,pi,v), T(y,pi,v)`, they are ONE
// value read through two syntactic spellings. Unlike prp-key's
// LICENSING statement (which stays weakened against
// `prp_key_derives_approx`, a syntactic notion `==` genuinely cannot
// bridge without changing what "licensed by g" means), the TRUTH
// statement below is proved against the UNWEAKENED cond_haskey
// condition -- the bridging fact the registry asked for exists, so no
// parking is needed here.
//
// SHAPE: outer fold over collect_haskey_axioms (haskey_axiom_from_
// triple, OWL.RL.Refinement.fst section 22, gives the real hasKey
// declaration triple + decode_iri_list witness -- REUSED via `open
// OWL.RL.Refinement` rather than re-derived); per nonempty-key-list
// axiom, an x/y double fold over members_of_class (class_member_from_
// triple, section 22's sibling, gives the real rdf:type witnesses).
// The double fold's y-step guard `x <> y && all_keys_match g ig x y
// props` is tested via `lemma_all_keys_match_shares_approx` (section
// 23, REUSED verbatim) into `shares_key_values_approx` -- the same
// per-property rdf_term_eq-witness-pair existential the licensing
// proof consumes -- then lifted to the DOMAIN-ELEMENT level by the two
// new helper lemmas below (`lemma_shares_key_values_semantic`,
// `lemma_pterms_agree`) so `cond_haskey`'s premise (a per-pterm
// SHARED VALUE existential, seq_is-indexed like cond_oneof) can fire.
// ===================================================================

// Per-property semantic lifting of shares_key_values_approx: turn the
// syntactic rdf_term_eq-witness-pair existential (two triples whose
// objects rdf_term_eq-match) into a semantic shared-value existential
// (one domain element both x and y relate to under the property) --
// the exact premise shape cond_haskey needs. The literal case goes
// through cond_literal_term_eq_respecting via lemma_rdf_term_eq_denot;
// IRI/BNode witnesses need no condition (rdf_term_eq on those reduces
// to structural `=`, closed inside lemma_rdf_term_eq_denot's own
// T_IRI/T_BNode cases).
#push-options "--z3rlimit 150 --split_queries always"
let rec lemma_shares_key_values_semantic
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (x y : subject) (props : list wf_iri)
  : Lemma
    (requires cond_literal_term_eq_respecting i /\ holds_all i a g /\
              shares_key_values_approx g x y props)
    (ensures forall (p : wf_iri). List.Tot.memP p props ==>
               (exists (v : i.idom).
                  i.iext (i.i_iri p) (denot_subject i a x) v /\
                  i.iext (i.i_iri p) (denot_subject i a y) v))
    (decreases props) =
  match props with
  | [] -> ()
  | p0 :: rest ->
    lemma_shares_key_values_semantic i a g x y rest;
    introduce forall (p : wf_iri). List.Tot.memP p props ==>
        (exists (v : i.idom).
           i.iext (i.i_iri p) (denot_subject i a x) v /\
           i.iext (i.i_iri p) (denot_subject i a y) v)
    with introduce List.Tot.memP p props ==>
                   (exists (v : i.idom).
                      i.iext (i.i_iri p) (denot_subject i a x) v /\
                      i.iext (i.i_iri p) (denot_subject i a y) v)
    with _ . begin
      if p = p0 then begin
        eliminate exists (ux uy : triple).
            List.Tot.memP ux g /\ ux.s == x /\ ux.p == p0 /\
            List.Tot.memP uy g /\ uy.s == y /\ uy.p == p0 /\
            rdf_term_eq ux.o uy.o == true
        returns (exists (v : i.idom).
                   i.iext (i.i_iri p) (denot_subject i a x) v /\
                   i.iext (i.i_iri p) (denot_subject i a y) v)
        with _ . begin
          assert (triple_holds i a ux);
          assert (triple_holds i a uy);
          lemma_rdf_term_eq_denot i a ux.o uy.o;
          assert (i.iext (i.i_iri p0) (denot_subject i a x) (denot_term i a ux.o));
          assert (i.iext (i.i_iri p0) (denot_subject i a y) (denot_term i a uy.o))
        end
      end else ()
    end
#pop-options

// Bridges the per-wf_iri semantic agreement lemma_shares_key_values_
// semantic establishes into the per-domain-element form cond_haskey's
// pterms quantifier needs (pterms == List.Tot.map i.i_iri props).
let lemma_pterms_agree
    (i : interp) (dx dy : i.idom) (props : list wf_iri)
  : Lemma
    (requires forall (q : wf_iri). List.Tot.memP q props ==>
                (exists (v : i.idom). i.iext (i.i_iri q) dx v /\ i.iext (i.i_iri q) dy v))
    (ensures forall (p : i.idom).
               List.Tot.memP p (List.Tot.map (fun (q : wf_iri) -> i.i_iri q) props) ==>
               (exists (v : i.idom). i.iext p dx v /\ i.iext p dy v)) =
  introduce forall (p : i.idom).
      List.Tot.memP p (List.Tot.map (fun (q : wf_iri) -> i.i_iri q) props) ==>
      (exists (v : i.idom). i.iext p dx v /\ i.iext p dy v)
  with introduce List.Tot.memP p (List.Tot.map (fun (q : wf_iri) -> i.i_iri q) props) ==>
                 (exists (v : i.idom). i.iext p dx v /\ i.iext p dy v)
  with _ . begin
    FStar.List.Tot.Properties.memP_map_elim (fun (q : wf_iri) -> i.i_iri q) p props;
    eliminate exists (q : wf_iri). List.Tot.memP q props /\ i.i_iri q == p
    returns (exists (v : i.idom). i.iext p dx v /\ i.iext p dy v)
    with _ . ()
  end

val owl_rule_prp_key_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_haskey i /\ cond_sameas_identity i /\ cond_literal_term_eq_respecting i /\
              holds_all i a g /\ ig.ig_triples == g /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_prp_key g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_prp_key_sound i a g ig =
  let fuel : nat = List.Tot.length g in
  let axioms = collect_haskey_axioms g ig in
  lemma_collect_haskey_axioms_licensed g ig;
  introduce forall (acc : rdf_graph) (axiom : (wf_iri & list wf_iri)).
      (List.Tot.memP axiom axioms /\ holds_all i a acc) ==>
      holds_all i a (owl_prp_key_axiom_step g ig acc axiom)
  with introduce (List.Tot.memP axiom axioms /\ holds_all i a acc) ==>
                 holds_all i a (owl_prp_key_axiom_step g ig acc axiom)
  with _ . begin
    let (c_iri, props) = axiom in
    match props with
    | [] -> ()
    | _ ->
      assert (haskey_axiom_from_triple g ig fuel axiom);
      eliminate exists (decl : triple) (list_subj : subject).
          List.Tot.memP decl g /\ decl.p == owl_hasKey /\ decl.s == S_IRI c_iri /\
          term_to_subject decl.o == Some list_subj /\
          decode_iri_list g ig list_subj fuel == Some props
      returns holds_all i a (owl_prp_key_axiom_step g ig acc axiom)
      with _ . begin
        decode_iri_list_sound i a g ig list_subj fuel;
        lemma_denot_term_to_subject i a decl.o list_subj;
        assert (triple_holds i a decl);
        let pterms = List.Tot.map (fun (q : wf_iri) -> i.i_iri q) props in
        assert (seq_is i (denot_subject i a list_subj) pterms);
        assert (i.iext (i.i_iri owl_hasKey)
                       (i.i_iri c_iri) (denot_subject i a list_subj));
        let members = members_of_class g c_iri in
        lemma_members_of_class_licensed g c_iri;
        introduce forall (acc1 : rdf_graph) (x : wf_iri).
            (List.Tot.memP x members /\ holds_all i a acc1) ==>
            holds_all i a (owl_prp_key_x_step g ig props members acc1 x)
        with introduce (List.Tot.memP x members /\ holds_all i a acc1) ==>
                       holds_all i a (owl_prp_key_x_step g ig props members acc1 x)
        with _ . begin
          introduce forall (acc2 : rdf_graph) (y : wf_iri).
              (List.Tot.memP y members /\ holds_all i a acc2) ==>
              holds_all i a (owl_prp_key_y_step g ig props x acc2 y)
          with introduce (List.Tot.memP y members /\ holds_all i a acc2) ==>
                         holds_all i a (owl_prp_key_y_step g ig props x acc2 y)
          with _ . begin
            if x <> y && all_keys_match g ig x y props then begin
              assert (class_member_from_triple g c_iri x);
              assert (class_member_from_triple g c_iri y);
              eliminate exists (tx : triple).
                  List.Tot.memP tx g /\ tx.p == rdf_type /\ tx.s == S_IRI x /\
                  rdf_term_eq tx.o (T_IRI c_iri) = true
              returns holds_all i a (owl_prp_key_y_step g ig props x acc2 y)
              with _ . begin
                lemma_rdf_term_eq_iri tx.o c_iri;
                assert (triple_holds i a tx);
                assert (icext i (i.i_iri x) (i.i_iri c_iri));
                eliminate exists (ty : triple).
                    List.Tot.memP ty g /\ ty.p == rdf_type /\ ty.s == S_IRI y /\
                    rdf_term_eq ty.o (T_IRI c_iri) = true
                returns holds_all i a (owl_prp_key_y_step g ig props x acc2 y)
                with _ . begin
                  lemma_rdf_term_eq_iri ty.o c_iri;
                  assert (triple_holds i a ty);
                  assert (icext i (i.i_iri y) (i.i_iri c_iri));
                  lemma_all_keys_match_shares_approx g ig x y props;
                  lemma_shares_key_values_semantic i a g (S_IRI x) (S_IRI y) props;
                  lemma_pterms_agree i (i.i_iri x) (i.i_iri y) props;
                  // cond_haskey fires on: hasKey(c,l); seq_is l pterms;
                  // icext x c; icext y c; every pterm agreed on a
                  // shared value -- giving x == y at the domain level.
                  assert (i.i_iri x == i.i_iri y);
                  // cond_sameas_identity backward: equal denotations
                  // give the emitted sameAs edge.
                  assert (i.iext (i.i_iri owl_sameAs) (i.i_iri x) (i.i_iri y))
                end
              end
            end else ()
          end;
          fold_left_inv (holds_all i a) (owl_prp_key_y_step g ig props x) members acc1
        end;
        fold_left_inv (holds_all i a) (owl_prp_key_x_step g ig props members) members acc
      end
  end;
  fold_left_inv (holds_all i a) (owl_prp_key_axiom_step g ig) axioms g;
  assert_norm (owl_rule_prp_key g ig ==
               List.Tot.fold_left (owl_prp_key_axiom_step g ig) g axioms)
#pop-options

// ===================================================================
// G3 M4 wave 2 (2026-08-06): Rules 28-32, the Table 8 schema-vocabulary
// closure quartet (scm-dom1/scm-rng1/scm-dom2/scm-rng2, dispatched
// across two engine functions per OWL.RL.Refinement.fst sections
// 15-17's ENGINE NAME VS ROW findings) plus the two list-walking
// comprehension rules cls-int1/cls-uni (sections 19-20's findings).
// Every new cond_* these five rules need lives in OWL.Semantics.fst,
// right after cond_haskey. `ig_wf_po_spec` (cls-int1) and
// `no_disjoint_union` / `lemma_no_disjoint_union_elim` (cls-uni) are
// REUSED verbatim from OWL.RL.Refinement.fst (already `open`ed above)
// rather than re-derived, per the dispatch brief.
// ===================================================================

// ===================================================================
// Rule 28: owl_rule_scm_dom2 (dispatched row scm-dom2; the row the
// engine function ACTUALLY realizes is scm-dom1 -- OWL.RL.Refinement.
// fst section 15's ENGINE NAME VS ROW finding, `scm_dom1_licensed`,
// not `scm_dom2_licensed`). OWL 2 RL/RDF Table 8 row scm-dom1: T(?p,
// rdfs:domain, ?c1), T(?c1, rdfs:subClassOf, ?c2) => T(?p, rdfs:domain,
// ?c2). Two-level nested fold (outer over g on the domain tag, inner
// over find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf) -- same
// NESTED-SINGLE shape as Rule 23's prp-trp, one bucket-lookup deep,
// mirroring the licensing proof's own structure (section 15) exactly;
// cond_domain_subclass carries the semantic closure the licensing side
// gets for free from scm_dom1_derives's syntactic witness. The engine's
// un-lambda-lifted `owl_rule_scm_dom2` (OWL.Closure.fsti:3652-3671) is
// spelled verbatim below via named-but-ascribed local lets, the same
// technique Rules 21/23 use for un-lifted engine rules (this module's
// own "Proof-engineering note" at decode_iri_list_sound applies only to
// the LIST-WALK recursion's alpha-identical-closure sharing, not to
// this shape -- Rules 21/23 already confirm ascribed lets discharge
// here).
// ===================================================================

val owl_rule_scm_dom2_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_domain_subclass i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_scm_dom2 g ig))

#push-options "--z3rlimit 150 --split_queries always"
let owl_rule_scm_dom2_sound i a g ig =
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (outer_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc t)
  with _ . begin
    if t.p = rdfs_domain then
      match t.o with
      | T_IRI c1_iri ->
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri rdfs_domain) (denot_subject i a t.s) (i.i_iri c1_iri));
        let bucket = bucket_lookup ig.ig_sp (sp_key (S_IRI c1_iri) rdfs_subClassOf) in
        let supers = find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf in
        assert (supers == List.Tot.map (fun (u : triple) -> u.o) bucket);
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
            match c2_term with
            | T_IRI _ ->
              let new_t : triple = { s = t.s; p = rdfs_domain; o = c2_term } in
              add_triple_unchecked acc2 new_t
            | _ -> acc2 in
        introduce forall (acc2 : rdf_graph) (c2_term : rdf_term).
            (List.Tot.memP c2_term supers /\ holds_all i a acc2) ==>
            holds_all i a (inner_step acc2 c2_term)
        with introduce (List.Tot.memP c2_term supers /\ holds_all i a acc2) ==>
                       holds_all i a (inner_step acc2 c2_term)
        with _ . begin
          match c2_term with
          | T_IRI d_iri ->
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c2_term bucket;
            eliminate exists (u2 : triple).
                List.Tot.memP u2 bucket /\ u2.o == c2_term
            returns holds_all i a (inner_step acc2 c2_term)
            with _ . begin
              assert (List.Tot.memP u2 ig.ig_triples /\
                      u2.s == S_IRI c1_iri /\ u2.p == rdfs_subClassOf);
              assert (triple_holds i a u2);
              assert (i.iext (i.i_iri rdfs_subClassOf)
                             (i.i_iri c1_iri) (denot_term i a c2_term));
              // cond_domain_subclass closes: domain(p,c1) + subClassOf
              // (c1,c2) => domain(p,c2).
              assert (i.iext (i.i_iri rdfs_domain)
                             (denot_subject i a t.s) (denot_term i a c2_term));
              let new_t : triple = { s = t.s; p = rdfs_domain; o = c2_term } in
              assert (triple_holds i a new_t)
            end
          | _ -> ()
        end;
        fold_left_inv (holds_all i a) inner_step supers acc
      | _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) outer_step g g;
  assert_norm (owl_rule_scm_dom2 g ig == List.Tot.fold_left outer_step g g)
#pop-options

// ===================================================================
// Rule 29: owl_rule_scm_rng2 (dispatched row scm-rng2; the row the
// engine function ACTUALLY realizes is scm-rng1, section 16's finding)
// -- range mirror of Rule 28. cond_range_subclass in place of
// cond_domain_subclass, rdfs:range in place of rdfs:domain throughout.
// ===================================================================

val owl_rule_scm_rng2_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_range_subclass i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_scm_rng2 g ig))

#push-options "--z3rlimit 150 --split_queries always"
let owl_rule_scm_rng2_sound i a g ig =
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (outer_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc t)
  with _ . begin
    if t.p = rdfs_range then
      match t.o with
      | T_IRI c1_iri ->
        assert (triple_holds i a t);
        assert (i.iext (i.i_iri rdfs_range) (denot_subject i a t.s) (i.i_iri c1_iri));
        let bucket = bucket_lookup ig.ig_sp (sp_key (S_IRI c1_iri) rdfs_subClassOf) in
        let supers = find_objects_indexed ig (S_IRI c1_iri) rdfs_subClassOf in
        assert (supers == List.Tot.map (fun (u : triple) -> u.o) bucket);
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (c2_term : rdf_term) ->
            match c2_term with
            | T_IRI _ ->
              let new_t : triple = { s = t.s; p = rdfs_range; o = c2_term } in
              add_triple_unchecked acc2 new_t
            | _ -> acc2 in
        introduce forall (acc2 : rdf_graph) (c2_term : rdf_term).
            (List.Tot.memP c2_term supers /\ holds_all i a acc2) ==>
            holds_all i a (inner_step acc2 c2_term)
        with introduce (List.Tot.memP c2_term supers /\ holds_all i a acc2) ==>
                       holds_all i a (inner_step acc2 c2_term)
        with _ . begin
          match c2_term with
          | T_IRI d_iri ->
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c2_term bucket;
            eliminate exists (u2 : triple).
                List.Tot.memP u2 bucket /\ u2.o == c2_term
            returns holds_all i a (inner_step acc2 c2_term)
            with _ . begin
              assert (List.Tot.memP u2 ig.ig_triples /\
                      u2.s == S_IRI c1_iri /\ u2.p == rdfs_subClassOf);
              assert (triple_holds i a u2);
              assert (i.iext (i.i_iri rdfs_subClassOf)
                             (i.i_iri c1_iri) (denot_term i a c2_term));
              // cond_range_subclass closes: range(p,c1) + subClassOf
              // (c1,c2) => range(p,c2).
              assert (i.iext (i.i_iri rdfs_range)
                             (denot_subject i a t.s) (denot_term i a c2_term));
              let new_t : triple = { s = t.s; p = rdfs_range; o = c2_term } in
              assert (triple_holds i a new_t)
            end
          | _ -> ()
        end;
        fold_left_inv (holds_all i a) inner_step supers acc
      | _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) outer_step g g;
  assert_norm (owl_rule_scm_rng2 g ig == List.Tot.fold_left outer_step g g)
#pop-options

// ===================================================================
// Rule 30: owl_rule_subprop_domain_range (dispatched rows scm-dom2 +
// scm-rng2; this engine function is the one that ACTUALLY realizes
// BOTH literal rows, per section 17's ENGINE NAME VS ROW finding --
// `owl_rule_scm_dom2`/`owl_rule_scm_rng2` above realize scm-dom1/
// scm-rng1 instead). OWL 2 RL/RDF Table 8: scm-dom2 T(?p2, rdfs:domain,
// ?c), T(?p1, rdfs:subPropertyOf, ?p2) => T(?p1, rdfs:domain, ?c);
// scm-rng2 same premise shape for rdfs:range. TWO SEQUENTIAL INNER
// FOLDS per outer item (domain-fold then range-fold, chained through
// the intermediate acc_d), mirroring the licensing proof's own
// structure (section 17) exactly: cond_domain_subprop / cond_range_
// subprop replace scm_dom2_derives / scm_rng2_derives's syntactic
// witnesses with the semantic closure.
// ===================================================================

val owl_rule_subprop_domain_range_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_domain_subprop i /\ cond_range_subprop i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_subprop_domain_range g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_subprop_domain_range_sound i a g ig =
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
      (List.Tot.memP t g /\ holds_all i a acc) ==> holds_all i a (outer_step acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc t)
  with _ . begin
    if t.p = rdfs_subPropertyOf then
      match term_to_subject t.o with
      | Some p2 ->
        assert (triple_holds i a t);
        lemma_denot_term_to_subject i a t.o p2;
        assert (i.iext (i.i_iri rdfs_subPropertyOf)
                       (denot_subject i a t.s) (denot_subject i a p2));
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
        introduce forall (acc1 : rdf_graph) (c : rdf_term).
            (List.Tot.memP c doms /\ holds_all i a acc1) ==> holds_all i a (dom_step acc1 c)
        with introduce (List.Tot.memP c doms /\ holds_all i a acc1) ==>
                       holds_all i a (dom_step acc1 c)
        with _ . begin
          match c with
          | T_IRI _ ->
            let dom_bucket = bucket_lookup ig.ig_sp (sp_key p2 rdfs_domain) in
            assert (doms == List.Tot.map (fun (u : triple) -> u.o) dom_bucket);
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c dom_bucket;
            eliminate exists (dom : triple).
                List.Tot.memP dom dom_bucket /\ dom.o == c
            returns holds_all i a (dom_step acc1 c)
            with _ . begin
              assert (List.Tot.memP dom ig.ig_triples /\
                      dom.s == p2 /\ dom.p == rdfs_domain);
              assert (triple_holds i a dom);
              assert (i.iext (i.i_iri rdfs_domain)
                             (denot_subject i a p2) (denot_term i a c));
              // cond_domain_subprop: subPropertyOf(p1,p2) + domain(p2,c)
              // => domain(p1,c).
              assert (i.iext (i.i_iri rdfs_domain)
                             (denot_subject i a t.s) (denot_term i a c));
              let new_t : triple = { s = t.s; p = rdfs_domain; o = c } in
              assert (triple_holds i a new_t)
            end
          | _ -> ()
        end;
        fold_left_inv (holds_all i a) dom_step doms acc;
        let acc_d = List.Tot.fold_left dom_step acc doms in
        introduce forall (acc1 : rdf_graph) (c : rdf_term).
            (List.Tot.memP c rngs /\ holds_all i a acc1) ==> holds_all i a (rng_step acc1 c)
        with introduce (List.Tot.memP c rngs /\ holds_all i a acc1) ==>
                       holds_all i a (rng_step acc1 c)
        with _ . begin
          match c with
          | T_IRI _ ->
            let rng_bucket = bucket_lookup ig.ig_sp (sp_key p2 rdfs_range) in
            assert (rngs == List.Tot.map (fun (u : triple) -> u.o) rng_bucket);
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) c rng_bucket;
            eliminate exists (rng : triple).
                List.Tot.memP rng rng_bucket /\ rng.o == c
            returns holds_all i a (rng_step acc1 c)
            with _ . begin
              assert (List.Tot.memP rng ig.ig_triples /\
                      rng.s == p2 /\ rng.p == rdfs_range);
              assert (triple_holds i a rng);
              assert (i.iext (i.i_iri rdfs_range)
                             (denot_subject i a p2) (denot_term i a c));
              // cond_range_subprop: subPropertyOf(p1,p2) + range(p2,c)
              // => range(p1,c).
              assert (i.iext (i.i_iri rdfs_range)
                             (denot_subject i a t.s) (denot_term i a c));
              let new_t : triple = { s = t.s; p = rdfs_range; o = c } in
              assert (triple_holds i a new_t)
            end
          | _ -> ()
        end;
        fold_left_inv (holds_all i a) rng_step rngs acc_d
      | None -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) outer_step g g;
  assert_norm (owl_rule_subprop_domain_range g ig == List.Tot.fold_left outer_step g g)
#pop-options

// ===================================================================
// Rule 31: owl_rule_cls_int1 (dispatched row cls-int1; the row the
// engine function ACTUALLY realizes is cls-int2 -- OWL.RL.Refinement.
// fst section 19's ENGINE NAME VS ROW finding, `cls_int2_licensed`).
// OWL 2 RL/RDF Table 5 row cls-int2: T(?c, owl:intersectionOf, ?x),
// LIST[?x, ?c1..?cn], T(?y, rdf:type, ?c) => T(?y, rdf:type, ?c1) ...
// T(?y, rdf:type, ?cn). THREE-level nested fold (outer over g on the
// intersectionOf tag, middle over xs -- subjects typed into C via
// find_subjects_indexed, inner over the decoded member list) -- every
// level is already a NAMED top-level function in OWL.Closure.fsti
// (owl_cls_int1_step / owl_cls_int1_x_step / owl_cls_int1_emit, task
// #36 lambda-lift), so this proof's fold_left_inv arguments are the
// SAME symbols the engine calls, exactly the section-19 licensing
// recipe. decode_iri_list_sound (Rule 4's bridge) turns the syntactic
// list decode into the semantic seq_is reading cond_intersection_of
// needs; ig_wf_po_spec (OWL.RL.Refinement.fst section 19, REUSED
// verbatim) gives the real rdf:type witness `find_subjects_indexed`
// serves for the middle fold's subject-shaped po-bucket query.
// ===================================================================

val owl_rule_cls_int1_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_intersection_of i /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig /\ ig_wf_po_spec ig)
    (ensures  holds_all i a (owl_rule_cls_int1 g ig))

#push-options "--z3rlimit 300 --ifuel 4 --split_queries always"
let owl_rule_cls_int1_sound i a g ig =
  let fuel : nat = List.Tot.length g in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==>
      holds_all i a (owl_cls_int1_step g ig fuel acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (owl_cls_int1_step g ig fuel acc t)
  with _ . begin
    if t.p = owl_intersectionOf_iri then begin
      match term_to_subject t.o with
      | None -> ()
      | Some list_subj ->
        (match decode_iri_list g ig list_subj fuel with
         | None -> ()
         | Some members ->
           decode_iri_list_sound i a g ig list_subj fuel;
           lemma_denot_term_to_subject i a t.o list_subj;
           assert (triple_holds i a t);
           let elems_d = List.Tot.map (fun (x : wf_iri) -> i.i_iri x) members in
           assert (seq_is i (denot_subject i a list_subj) elems_d);
           assert (i.iext (i.i_iri owl_intersectionOf_iri)
                          (denot_subject i a t.s) (denot_subject i a list_subj));
           let xs = find_subjects_indexed ig rdf_type (subject_to_term t.s) in
           introduce forall (acc1 : rdf_graph) (x : subject).
               (List.Tot.memP x xs /\ holds_all i a acc1) ==>
               holds_all i a (owl_cls_int1_x_step members acc1 x)
           with introduce (List.Tot.memP x xs /\ holds_all i a acc1) ==>
                          holds_all i a (owl_cls_int1_x_step members acc1 x)
           with _ . begin
             assert (exists (u : triple).
                       List.Tot.memP u ig.ig_triples /\ u.s == x /\ u.p == rdf_type /\
                       u.o == subject_to_term t.s);
             eliminate exists (u : triple).
                 List.Tot.memP u ig.ig_triples /\ u.s == x /\ u.p == rdf_type /\
                 u.o == subject_to_term t.s
             returns holds_all i a (owl_cls_int1_x_step members acc1 x)
             with _ . begin
               assert (triple_holds i a u);
               lemma_denot_subject_to_term i a t.s;
               assert (icext i (denot_subject i a x) (denot_subject i a t.s));
               // cond_intersection_of fires on the sequence reading above:
               // icext x C and C == intersectionOf elems_d gives icext x
               // ci for every listed member ci.
               assert (forall (ci : i.idom). List.Tot.memP ci elems_d ==>
                         icext i (denot_subject i a x) ci);
               introduce forall (acc2 : rdf_graph) (ci : wf_iri).
                   (List.Tot.memP ci members /\ holds_all i a acc2) ==>
                   holds_all i a (owl_cls_int1_emit x acc2 ci)
               with introduce (List.Tot.memP ci members /\ holds_all i a acc2) ==>
                              holds_all i a (owl_cls_int1_emit x acc2 ci)
               with _ . begin
                 List.Tot.Properties.memP_map_intro
                   (fun (y : wf_iri) -> i.i_iri y) ci members;
                 assert (icext i (denot_subject i a x) (i.i_iri ci));
                 let new_t : triple = { s = x; p = rdf_type; o = T_IRI ci } in
                 assert (triple_holds i a new_t)
               end;
               fold_left_inv (holds_all i a) (owl_cls_int1_emit x) members acc1
             end
           end;
           fold_left_inv (holds_all i a) (owl_cls_int1_x_step members) xs acc)
    end else ()
  end;
  fold_left_inv (holds_all i a) (owl_cls_int1_step g ig fuel) g g
#pop-options

// ===================================================================
// Rule 32: owl_rule_cls_uni (dispatched row cls-uni; the row the
// engine function ACTUALLY realizes, for its owl:unionOf branch, is
// scm-uni -- OWL.RL.Refinement.fst section 20's ENGINE NAME VS ROW
// finding). OWL 2 RL/RDF Table 8 row scm-uni: T(?c, owl:unionOf, ?x),
// LIST[?x, ?c1..?cn] => T(?c1, rdfs:subClassOf, ?c) ... T(?cn,
// rdfs:subClassOf, ?c). Every fold level is a NAMED top-level function
// in OWL.Closure.fsti (owl_cls_uni_decode_axiom / owl_cls_uni_sub_emit
// / owl_cls_uni_step, task #36 lambda-lift), mirroring the licensing
// proof's structure (section 20) exactly for Stage 1 (the subClassOf
// fold). SCOPED to `no_disjoint_union g` (REUSED verbatim from
// OWL.RL.Refinement.fst, same narrowing the pre-lambda-lift licensing
// scaffolding used): the owl:disjointUnionOf branch's own defining
// semantic condition (plain-unionOf restatement + pairwise
// disjointWith) has no cond_* yet and is out of this landing's scope
// -- the disjointUnionOf EXTENSION triples stay UNATTEMPTED for truth,
// same as their licensing predicate `cls_disjoint_union_ext_derives`
// needed no narrowing lift here, only the scm-uni row itself does.
// Under `no_disjoint_union g`, every t in g has t.p <> owl:
// disjointUnionOf, so `lemma_no_disjoint_union_elim` rules out the
// engine's disjointUnionOf-only Stage 2/3 branch for every t the outer
// fold actually reaches; the guard disjunction collapses to
// t.p == owl:unionOf.
// ===================================================================

val owl_rule_cls_uni_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_union_of i /\ no_disjoint_union g /\ holds_all i a g /\
              holds_all i a ig.ig_triples /\ ig_wf_sp ig)
    (ensures  holds_all i a (owl_rule_cls_uni g ig))

#push-options "--z3rlimit 300 --split_queries always"
let owl_rule_cls_uni_sound i a g ig =
  let fuel : nat = List.Tot.length g in
  introduce forall (acc : rdf_graph) (t : triple).
      (List.Tot.memP t g /\ holds_all i a acc) ==>
      holds_all i a (owl_cls_uni_step g ig fuel acc t)
  with introduce (List.Tot.memP t g /\ holds_all i a acc) ==>
                 holds_all i a (owl_cls_uni_step g ig fuel acc t)
  with _ . begin
    lemma_no_disjoint_union_elim g t;
    if t.p = owl_unionOf_iri || t.p = owl_disjointUnionOf_iri then begin
      match t.s, term_to_subject t.o with
      | S_IRI c_iri, Some list_subj ->
        (match decode_iri_list g ig list_subj fuel with
         | None -> ()
         | Some members ->
           assert (owl_cls_uni_decode_axiom g ig fuel t == Some (c_iri, members));
           decode_iri_list_sound i a g ig list_subj fuel;
           lemma_denot_term_to_subject i a t.o list_subj;
           assert (t.p = owl_unionOf_iri);
           assert (triple_holds i a t);
           let elems_d = List.Tot.map (fun (x : wf_iri) -> i.i_iri x) members in
           assert (seq_is i (denot_subject i a list_subj) elems_d);
           assert (i.iext (i.i_iri owl_unionOf_iri)
                          (i.i_iri c_iri) (denot_subject i a list_subj));
           introduce forall (acc1 : rdf_graph) (ci : wf_iri).
               (List.Tot.memP ci members /\ holds_all i a acc1) ==>
               holds_all i a (owl_cls_uni_sub_emit c_iri acc1 ci)
           with introduce (List.Tot.memP ci members /\ holds_all i a acc1) ==>
                          holds_all i a (owl_cls_uni_sub_emit c_iri acc1 ci)
           with _ . begin
             List.Tot.Properties.memP_map_intro (fun (x : wf_iri) -> i.i_iri x) ci members;
             assert (i.iext (i.i_iri rdfs_subClassOf) (i.i_iri ci) (i.i_iri c_iri));
             let new_t : triple = { s = S_IRI ci; p = rdfs_subClassOf; o = T_IRI c_iri } in
             assert (triple_holds i a new_t)
           end;
           let acc_sub = List.Tot.fold_left (owl_cls_uni_sub_emit c_iri) acc members in
           fold_left_inv (holds_all i a) (owl_cls_uni_sub_emit c_iri) members acc;
           assert (holds_all i a acc_sub);
           if t.p = owl_disjointUnionOf_iri then ()
           else ())
      | _, _ -> ()
    end else ()
  end;
  fold_left_inv (holds_all i a) (owl_cls_uni_step g ig fuel) g g
#pop-options

// ===================================================================
// Rule 33: owl_rule_cls_hv1 (cls-hv1; OWL.Closure.fsti ~line 1548).
// OWL 2 RL/RDF Table 6 row cls-hv1: T(?x, owl:hasValue, ?y), T(?x,
// owl:onProperty, ?p), T(?u, rdf:type, ?x) => T(?u, ?p, ?y). THREE-
// level fold over the wave 3 relift's named top-level helpers
// (owl_cls_hv1_outer / _mid / _emit, OWL.Closure.fsti, closure-
// identity law) -- the licensing sibling (OWL.RL.Refinement.fst
// section 26) is the shape precedent. Per the DEPTH COROLLARY
// (proof-factory skill), each proof level below is its OWN
// standalone lemma taking the level above's witnesses as ARGUMENTS
// (lemma_cls_hv1_witness_holds assembles the row's semantic content
// flat), the same treatment that unparked the licensing proof.
//
// cond_hasvalue (OWL.Semantics.fst) supplies the semantic HasValue
// condition; cls-hv1 reads its forward direction (icext u x ==>
// iext p u v). lemma_find_subjects_indexed_wf_subj (OWL.RL.Refinement,
// section 26) supplies the members-lookup provenance witness --
// reused verbatim (a purely syntactic index fact, no interpretation
// involved, so the same lemma serves both the licensing and the
// truth proof).
// ===================================================================

// The row's semantic content, assembled flat: every witness a fold
// level binds is an ARGUMENT here -- the obligation the depth
// corollary says to keep OUT of nested introduce scopes.
val lemma_cls_hv1_witness_holds
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (hv_t : triple) (onp : triple) (p : wf_iri) (x : subject)
  : Lemma
    (requires cond_hasvalue i /\ ig_wf_po ig /\ ig.ig_triples == g /\
              holds_all i a g /\
              memP hv_t g /\ hv_t.p == owl_hasValue_iri /\
              memP onp g /\ onp.s == hv_t.s /\ onp.p == owl_onProperty_iri /\
              onp.o == T_IRI p /\
              memP x (find_subjects_indexed ig rdf_type
                        (subject_to_term hv_t.s)))
    (ensures triple_holds i a ({ s = x; p = p; o = hv_t.o } <: triple))

#push-options "--z3rlimit 200 --split_queries always"
let lemma_cls_hv1_witness_holds i a g ig hv_t onp p x =
  lemma_find_subjects_indexed_wf_subj ig g rdf_type hv_t.s x;
  eliminate exists (tu : triple).
      memP tu g /\ tu.p == rdf_type /\
      tu.o == subject_to_term hv_t.s /\ tu.s == x
  returns triple_holds i a ({ s = x; p = p; o = hv_t.o } <: triple)
  with _ . begin
    assert (triple_holds i a tu);
    assert (triple_holds i a hv_t);
    assert (triple_holds i a onp);
    lemma_denot_subject_to_term i a hv_t.s;
    assert (icext i (denot_subject i a x) (denot_subject i a hv_t.s));
    // cond_hasvalue, forward direction.
    assert (i.iext (i.i_iri p) (denot_subject i a x) (denot_term i a hv_t.o))
  end
#pop-options

// Level 3 (innermost fold, over the restriction's members): the
// engine's own `owl_cls_hv1_emit p hv_t.o` is the folded function --
// same symbol, no re-spelling.
val lemma_cls_hv1_members_fold_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (hv_t : triple) (onp : triple) (p : wf_iri) (acc2 : rdf_graph)
  : Lemma
    (requires cond_hasvalue i /\ ig_wf_po ig /\ ig.ig_triples == g /\
              holds_all i a g /\
              memP hv_t g /\ hv_t.p == owl_hasValue_iri /\
              memP onp g /\ onp.s == hv_t.s /\ onp.p == owl_onProperty_iri /\
              onp.o == T_IRI p /\
              holds_all i a acc2)
    (ensures holds_all i a
               (List.Tot.fold_left (owl_cls_hv1_emit p hv_t.o) acc2
                  (find_subjects_indexed ig rdf_type
                     (subject_to_term hv_t.s))))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_cls_hv1_members_fold_sound i a g ig hv_t onp p acc2 =
  let members = find_subjects_indexed ig rdf_type (subject_to_term hv_t.s) in
  introduce forall (acc3 : rdf_graph) (x : subject).
      (memP x members /\ holds_all i a acc3) ==>
      holds_all i a (owl_cls_hv1_emit p hv_t.o acc3 x)
  with introduce (memP x members /\ holds_all i a acc3) ==>
                 holds_all i a (owl_cls_hv1_emit p hv_t.o acc3 x)
  with _ . begin
    lemma_cls_hv1_witness_holds i a g ig hv_t onp p x
  end;
  fold_left_inv (holds_all i a) (owl_cls_hv1_emit p hv_t.o) members acc2
#pop-options

// Level 2 (middle fold, over the restriction's onProperty objects):
// extracts the `onp` witness from the sp bucket, then hands it to
// level 3 as an ARGUMENT.
val lemma_cls_hv1_mid_step_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (hv_t : triple) (acc2 : rdf_graph) (op_term : rdf_term)
  : Lemma
    (requires cond_hasvalue i /\ ig_wf_sp ig /\ ig_wf_po ig /\
              ig.ig_triples == g /\ holds_all i a g /\
              memP hv_t g /\ hv_t.p == owl_hasValue_iri /\
              memP op_term (find_objects_indexed ig hv_t.s owl_onProperty_iri) /\
              holds_all i a acc2)
    (ensures holds_all i a
               (owl_cls_hv1_mid ig hv_t.s hv_t.o acc2 op_term))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_cls_hv1_mid_step_sound i a g ig hv_t acc2 op_term =
  let r_subj = hv_t.s in
  match op_term with
  | T_IRI p ->
    let ob = bucket_lookup ig.ig_sp (sp_key r_subj owl_onProperty_iri) in
    assert (find_objects_indexed ig r_subj owl_onProperty_iri ==
            List.Tot.map (fun (u : triple) -> u.o) ob);
    FStar.List.Tot.Properties.memP_map_elim
      (fun (u : triple) -> u.o) op_term ob;
    eliminate exists (onp : triple).
        memP onp ob /\ onp.o == op_term
    returns holds_all i a (owl_cls_hv1_mid ig r_subj hv_t.o acc2 op_term)
    with _ . begin
      assert (memP onp g /\ onp.s == r_subj /\ onp.p == owl_onProperty_iri);
      lemma_cls_hv1_members_fold_sound i a g ig hv_t onp p acc2
    end
  | _ -> ()
#pop-options

val owl_rule_cls_hv1_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_hasvalue i /\ ig_wf_sp ig /\ ig_wf_po ig /\
              ig.ig_triples == g /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_cls_hv1 g ig))

#push-options "--z3rlimit 400 --split_queries always"
let owl_rule_cls_hv1_sound i a g ig =
  introduce forall (acc : rdf_graph) (hv_t : triple).
      (memP hv_t g /\ holds_all i a acc) ==>
      holds_all i a (owl_cls_hv1_outer ig acc hv_t)
  with introduce (memP hv_t g /\ holds_all i a acc) ==>
                 holds_all i a (owl_cls_hv1_outer ig acc hv_t)
  with _ . begin
    if hv_t.p = owl_hasValue_iri then begin
      let r_subj = hv_t.s in
      let onprops = find_objects_indexed ig r_subj owl_onProperty_iri in
      introduce forall (acc2 : rdf_graph) (op_term : rdf_term).
          (memP op_term onprops /\ holds_all i a acc2) ==>
          holds_all i a (owl_cls_hv1_mid ig r_subj hv_t.o acc2 op_term)
      with introduce (memP op_term onprops /\ holds_all i a acc2) ==>
                     holds_all i a (owl_cls_hv1_mid ig r_subj hv_t.o acc2 op_term)
      with _ . begin
        lemma_cls_hv1_mid_step_sound i a g ig hv_t acc2 op_term
      end;
      fold_left_inv (holds_all i a)
        (owl_cls_hv1_mid ig r_subj hv_t.o) onprops acc
    end else ()
  end;
  fold_left_inv (holds_all i a) (owl_cls_hv1_outer ig) g g
#pop-options

// ===================================================================
// Rule 34: owl_rule_cls_hv2 (cls-hv2; OWL.Closure.fsti ~line 1581).
// OWL 2 RL/RDF Table 6 row cls-hv2: T(?x, owl:hasValue, ?y), T(?x,
// owl:onProperty, ?p), T(?u, ?p, ?y) => T(?u, rdf:type, ?x). Converse
// of Rule 33 -- same cond_hasvalue iff, backward direction. UNLIKE
// cls-hv1/cls-avf/prp-spo2, cls-hv2's engine function was NOT
// lambda-lifted in the wave 3 relift (its licensing proof discharges
// with anonymous local lambdas, OWL.RL.Refinement.fst section 27), so
// this truth proof follows the SAME local-verbatim-lambda skeleton
// (proof-factory skill: "assert_norm reduces only through
// zeta-unfoldable LOCAL step lambdas spelled VERBATIM from the engine
// text") rather than the named-top-level-helper treatment Rules
// 33/35/36 use. Per the DEPTH COROLLARY the deepest semantic-assembly
// step is still pulled into its own standalone lemma
// (lemma_cls_hv2_witness_holds) so the innermost introduce scope's
// SMT context stays flat, even though the fold-threading itself must
// stay inline (the closure-identity law: a proof-side re-spelling of
// an ENGINE anonymous lambda is a distinct token, so the local lets
// below are copied verbatim from OWL.Closure.fsti's owl_rule_cls_hv2
// text, matching what its own licensing proof already does).
//
// WEAKENED-ROW note (licensing sibling, section 27): the engine's
// `find_subjects_indexed ig p v` falls back to an `rdf_term_eq`
// filter for literal `v`, coarser than structural `==`. On the TRUTH
// side this gap closes for free, the SAME way Rule 27 (prp-key)
// closed it: `cond_literal_term_eq_respecting` + `lemma_rdf_term_eq_
// denot` show rdf_term_eq-equal terms denote the SAME domain element
// under any genuine interpretation, so the "extra" witnesses the
// engine's rdf_term_eq match accepts are not spurious relative to the
// TRUE semantic premise -- this proof goes through UNWEAKENED (no
// `_approx` predicate needed for truth, unlike the licensing
// statement, which stays weakened because it is a genuinely SYNTACTIC
// notion `==` cannot bridge without changing what "licensed by g"
// means).
// ===================================================================

val lemma_cls_hv2_witness_holds
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (hv_t : triple) (onp : triple) (p : wf_iri) (z : subject)
  : Lemma
    (requires cond_hasvalue i /\ cond_literal_term_eq_respecting i /\
              ig_wf_po ig /\ ig_wf_pred ig /\ ig.ig_triples == g /\
              holds_all i a g /\
              memP hv_t g /\ hv_t.p == owl_hasValue_iri /\
              memP onp g /\ onp.s == hv_t.s /\ onp.p == owl_onProperty_iri /\
              onp.o == T_IRI p /\
              memP z (find_subjects_indexed ig p hv_t.o))
    (ensures triple_holds i a
               ({ s = z; p = rdf_type; o = subject_to_term hv_t.s } <: triple))

#push-options "--z3rlimit 200 --split_queries always"
let lemma_cls_hv2_witness_holds i a g ig hv_t onp p z =
  lemma_find_subjects_indexed_wf_approx ig g p hv_t.o z;
  eliminate exists (u2 : triple).
      memP u2 g /\ u2.p == p /\ rdf_term_eq u2.o hv_t.o == true /\ u2.s == z
  returns triple_holds i a ({ s = z; p = rdf_type; o = subject_to_term hv_t.s } <: triple)
  with _ . begin
    lemma_rdf_term_eq_denot i a u2.o hv_t.o;
    assert (triple_holds i a u2);
    assert (triple_holds i a onp);
    assert (triple_holds i a hv_t);
    assert (i.iext (i.i_iri p) (denot_subject i a z) (denot_term i a hv_t.o));
    // cond_hasvalue, backward direction.
    assert (icext i (denot_subject i a z) (denot_subject i a hv_t.s));
    lemma_denot_subject_to_term i a hv_t.s
  end
#pop-options

val owl_rule_cls_hv2_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_hasvalue i /\ cond_literal_term_eq_respecting i /\
              ig_wf_sp ig /\ ig_wf_po ig /\ ig_wf_pred ig /\
              ig.ig_triples == g /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_cls_hv2 g ig))

#push-options "--z3rlimit 600 --fuel 2 --ifuel 2 --split_queries always"
let owl_rule_cls_hv2_sound i a g ig =
  // Engine text verbatim (OWL.Closure.fsti's owl_rule_cls_hv2).
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (hv_t : triple) ->
      if hv_t.p = owl_hasValue_iri then
        let r_subj = hv_t.s in
        let v = hv_t.o in
        let onprops = find_objects_indexed ig r_subj owl_onProperty_iri in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (op_term : rdf_term) ->
            match op_term with
            | T_IRI p ->
              let holders = find_subjects_indexed ig p v in
              List.Tot.fold_left
                (fun (acc3 : rdf_graph) (x : subject) ->
                  add_triple_unchecked acc3
                    ({ s = x; p = rdf_type; o = subject_to_term r_subj }))
                acc2
                holders
            | _ -> acc2)
          acc
          onprops
      else acc in
  introduce forall (acc : rdf_graph) (hv_t : triple).
      (memP hv_t g /\ holds_all i a acc) ==>
      holds_all i a (outer_step acc hv_t)
  with introduce (memP hv_t g /\ holds_all i a acc) ==>
                 holds_all i a (outer_step acc hv_t)
  with _ . begin
    if hv_t.p = owl_hasValue_iri then begin
      let r_subj = hv_t.s in
      let v = hv_t.o in
      let onprops = find_objects_indexed ig r_subj owl_onProperty_iri in
      let mid_step : rdf_graph -> rdf_term -> rdf_graph =
        fun (acc2 : rdf_graph) (op_term : rdf_term) ->
          match op_term with
          | T_IRI p ->
            let holders = find_subjects_indexed ig p v in
            List.Tot.fold_left
              (fun (acc3 : rdf_graph) (x : subject) ->
                add_triple_unchecked acc3
                  ({ s = x; p = rdf_type; o = subject_to_term r_subj }))
              acc2
              holders
          | _ -> acc2 in
      introduce forall (acc2 : rdf_graph) (op_term : rdf_term).
          (memP op_term onprops /\ holds_all i a acc2) ==>
          holds_all i a (mid_step acc2 op_term)
      with introduce (memP op_term onprops /\ holds_all i a acc2) ==>
                     holds_all i a (mid_step acc2 op_term)
      with _ . begin
        match op_term with
        | T_IRI p ->
          let holders = find_subjects_indexed ig p v in
          let inner_step : rdf_graph -> subject -> rdf_graph =
            fun (acc3 : rdf_graph) (x : subject) ->
              add_triple_unchecked acc3
                ({ s = x; p = rdf_type; o = subject_to_term r_subj }) in
          introduce forall (acc3 : rdf_graph) (x : subject).
              (memP x holders /\ holds_all i a acc3) ==>
              holds_all i a (inner_step acc3 x)
          with introduce (memP x holders /\ holds_all i a acc3) ==>
                         holds_all i a (inner_step acc3 x)
          with _ . begin
            // onp witness: op_term memP onprops ==
            //   find_objects_indexed ig r_subj owl_onProperty_iri.
            assert_norm (onprops ==
                         List.Tot.map (fun (u : triple) -> u.o)
                           (bucket_lookup ig.ig_sp (sp_key r_subj owl_onProperty_iri)));
            FStar.List.Tot.Properties.memP_map_elim
              (fun (u : triple) -> u.o) op_term
              (bucket_lookup ig.ig_sp (sp_key r_subj owl_onProperty_iri));
            eliminate exists (onp : triple).
                memP onp (bucket_lookup ig.ig_sp (sp_key r_subj owl_onProperty_iri)) /\
                onp.o == op_term
            returns holds_all i a (inner_step acc3 x)
            with _ . begin
              assert (memP onp g /\ onp.s == r_subj /\ onp.p == owl_onProperty_iri);
              lemma_cls_hv2_witness_holds i a g ig hv_t onp p x
            end
          end;
          fold_left_inv (holds_all i a) inner_step holders acc2
        | _ -> ()
      end;
      fold_left_inv (holds_all i a) mid_step onprops acc
    end else ()
  end;
  fold_left_inv (holds_all i a) outer_step g g;
  assert_norm (owl_rule_cls_hv2 g ig == List.Tot.fold_left outer_step g g)
#pop-options

// ===================================================================
// Rule 35: owl_rule_cls_avf1 (cls-avf; OWL.Closure.fsti ~line 2379).
// OWL 2 RL/RDF Table 5 row cls-avf: T(?x, owl:allValuesFrom, ?y),
// T(?x, owl:onProperty, ?p), T(?u, rdf:type, ?x), T(?u, ?p, ?v) =>
// T(?v, rdf:type, ?y). The program's deepest rule -- a FOUR-level
// fold, all four levels NAMED top-level helpers in the wave 3 relift
// (owl_cls_avf1_outer / _prop / _member / _emit). Same two-part
// DEPTH COROLLARY treatment as Rule 33: the row's six-way existential
// is assembled flat in `lemma_cls_avf_witness_holds`, taking every
// level's witness as an argument, instead of nesting four introduce
// scopes.
//
// cond_allvaluesfrom (OWL.Semantics.fst) supplies the semantic
// condition; unlike cond_hasvalue this one is already one-directional
// in the table (no converse row exists for allValuesFrom the way
// cls-hv2 converses cls-hv1). Reuses `lemma_find_subjects_indexed_wf_
// subj` a second time in the same proof (section 29's own comment on
// its licensing sibling: "every bridge this rule needs already exists
// from sections 15-17 and 26").
// ===================================================================

// The row's semantic content, assembled flat.
val lemma_cls_avf_witness_holds
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (t_avf : triple) (onp : triple) (d : wf_iri) (p : wf_iri)
    (x : subject) (y : rdf_term) (y_subj : subject)
  : Lemma
    (requires cond_allvaluesfrom i /\ ig_wf_sp ig /\ ig_wf_po ig /\
              ig.ig_triples == g /\ holds_all i a g /\
              memP t_avf g /\ t_avf.p == owl_allValuesFrom_iri /\
              t_avf.o == T_IRI d /\
              memP onp g /\ onp.s == t_avf.s /\ onp.p == owl_onProperty_iri /\
              onp.o == T_IRI p /\
              memP x (find_subjects_indexed ig rdf_type
                        (subject_to_term t_avf.s)) /\
              memP y (find_objects_indexed ig x p) /\
              term_to_subject y == Some y_subj)
    (ensures triple_holds i a
               ({ s = y_subj; p = rdf_type; o = T_IRI d } <: triple))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_cls_avf_witness_holds i a g ig t_avf onp d p x y y_subj =
  lemma_find_subjects_indexed_wf_subj ig g rdf_type t_avf.s x;
  let yb = bucket_lookup ig.ig_sp (sp_key x p) in
  assert (find_objects_indexed ig x p == List.Tot.map (fun (u : triple) -> u.o) yb);
  FStar.List.Tot.Properties.memP_map_elim (fun (u : triple) -> u.o) y yb;
  eliminate exists (tu : triple).
      memP tu g /\ tu.p == rdf_type /\
      tu.o == subject_to_term t_avf.s /\ tu.s == x
  returns triple_holds i a ({ s = y_subj; p = rdf_type; o = T_IRI d } <: triple)
  with _ . begin
    eliminate exists (u2 : triple).
        memP u2 yb /\ u2.o == y
    returns triple_holds i a ({ s = y_subj; p = rdf_type; o = T_IRI d } <: triple)
    with _ . begin
      assert (memP u2 g /\ u2.s == x /\ u2.p == p);
      assert (triple_holds i a tu);
      assert (triple_holds i a u2);
      assert (triple_holds i a onp);
      assert (triple_holds i a t_avf);
      lemma_denot_subject_to_term i a t_avf.s;
      assert (icext i (denot_subject i a x) (denot_subject i a t_avf.s));
      assert (i.iext (i.i_iri p) (denot_subject i a x) (denot_term i a y));
      lemma_denot_term_to_subject i a y y_subj;
      // cond_allvaluesfrom.
      assert (icext i (denot_subject i a y_subj) (i.i_iri d))
    end
  end
#pop-options

// Level 4 -> 3: the per-member fold over that member's P-edges. The
// folded function is the engine's own `owl_cls_avf1_emit d`.
val lemma_cls_avf_member_fold_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (t_avf : triple) (onp : triple) (d : wf_iri) (p : wf_iri)
    (x : subject) (acc3 : rdf_graph)
  : Lemma
    (requires cond_allvaluesfrom i /\ ig_wf_sp ig /\ ig_wf_po ig /\
              ig.ig_triples == g /\ holds_all i a g /\
              memP t_avf g /\ t_avf.p == owl_allValuesFrom_iri /\
              t_avf.o == T_IRI d /\
              memP onp g /\ onp.s == t_avf.s /\ onp.p == owl_onProperty_iri /\
              onp.o == T_IRI p /\
              memP x (find_subjects_indexed ig rdf_type
                        (subject_to_term t_avf.s)) /\
              holds_all i a acc3)
    (ensures holds_all i a
               (List.Tot.fold_left (owl_cls_avf1_emit d) acc3
                  (find_objects_indexed ig x p)))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_cls_avf_member_fold_sound i a g ig t_avf onp d p x acc3 =
  let ys = find_objects_indexed ig x p in
  introduce forall (acc4 : rdf_graph) (y : rdf_term).
      (memP y ys /\ holds_all i a acc4) ==>
      holds_all i a (owl_cls_avf1_emit d acc4 y)
  with introduce (memP y ys /\ holds_all i a acc4) ==>
                 holds_all i a (owl_cls_avf1_emit d acc4 y)
  with _ . begin
    match term_to_subject y with
    | Some y_subj ->
      lemma_cls_avf_witness_holds i a g ig t_avf onp d p x y y_subj
    | None -> ()
  end;
  fold_left_inv (holds_all i a) (owl_cls_avf1_emit d) ys acc3
#pop-options

// Level 2: per onProperty object -- extracts the `onp` witness from
// the sp bucket, then folds level 3/4 over the restriction's members.
val lemma_cls_avf_prop_step_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (t_avf : triple) (d : wf_iri) (acc2 : rdf_graph) (p_term : rdf_term)
  : Lemma
    (requires cond_allvaluesfrom i /\ ig_wf_sp ig /\ ig_wf_po ig /\
              ig.ig_triples == g /\ holds_all i a g /\
              memP t_avf g /\ t_avf.p == owl_allValuesFrom_iri /\
              t_avf.o == T_IRI d /\
              memP p_term (find_objects_indexed ig t_avf.s owl_onProperty_iri) /\
              holds_all i a acc2)
    (ensures holds_all i a (owl_cls_avf1_prop ig d t_avf.s acc2 p_term))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_cls_avf_prop_step_sound i a g ig t_avf d acc2 p_term =
  let r_subj = t_avf.s in
  match p_term with
  | T_IRI p ->
    let ob = bucket_lookup ig.ig_sp (sp_key r_subj owl_onProperty_iri) in
    assert (find_objects_indexed ig r_subj owl_onProperty_iri ==
            List.Tot.map (fun (u : triple) -> u.o) ob);
    FStar.List.Tot.Properties.memP_map_elim
      (fun (u : triple) -> u.o) p_term ob;
    eliminate exists (onp : triple).
        memP onp ob /\ onp.o == p_term
    returns holds_all i a (owl_cls_avf1_prop ig d r_subj acc2 p_term)
    with _ . begin
      assert (memP onp g /\ onp.s == r_subj /\ onp.p == owl_onProperty_iri);
      let members = find_subjects_indexed ig rdf_type (subject_to_term r_subj) in
      introduce forall (acc3 : rdf_graph) (x : subject).
          (memP x members /\ holds_all i a acc3) ==>
          holds_all i a (owl_cls_avf1_member ig d p acc3 x)
      with introduce (memP x members /\ holds_all i a acc3) ==>
                     holds_all i a (owl_cls_avf1_member ig d p acc3 x)
      with _ . begin
        lemma_cls_avf_member_fold_sound i a g ig t_avf onp d p x acc3
      end;
      fold_left_inv (holds_all i a) (owl_cls_avf1_member ig d p) members acc2
    end
  | _ -> ()
#pop-options

val owl_rule_cls_avf1_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_allvaluesfrom i /\ ig_wf_sp ig /\ ig_wf_po ig /\
              ig.ig_triples == g /\ holds_all i a g)
    (ensures  holds_all i a (owl_rule_cls_avf1 g ig))

#push-options "--z3rlimit 400 --split_queries always"
let owl_rule_cls_avf1_sound i a g ig =
  introduce forall (acc : rdf_graph) (t_avf : triple).
      (memP t_avf g /\ holds_all i a acc) ==>
      holds_all i a (owl_cls_avf1_outer ig acc t_avf)
  with introduce (memP t_avf g /\ holds_all i a acc) ==>
                 holds_all i a (owl_cls_avf1_outer ig acc t_avf)
  with _ . begin
    if t_avf.p = owl_allValuesFrom_iri then
      match t_avf.o with
      | T_IRI d ->
        let r_subj = t_avf.s in
        let props = find_objects_indexed ig r_subj owl_onProperty_iri in
        introduce forall (acc2 : rdf_graph) (p_term : rdf_term).
            (memP p_term props /\ holds_all i a acc2) ==>
            holds_all i a (owl_cls_avf1_prop ig d r_subj acc2 p_term)
        with introduce (memP p_term props /\ holds_all i a acc2) ==>
                       holds_all i a (owl_cls_avf1_prop ig d r_subj acc2 p_term)
        with _ . begin
          lemma_cls_avf_prop_step_sound i a g ig t_avf d acc2 p_term
        end;
        fold_left_inv (holds_all i a) (owl_cls_avf1_prop ig d r_subj) props acc
      | _ -> ()
    else ()
  end;
  fold_left_inv (holds_all i a) (owl_cls_avf1_outer ig) g g
#pop-options

// ===================================================================
// Rule 36: owl_rule_property_chain_2 (prp-spo2, n=2 specialisation;
// OWL.Closure.fsti ~line 2580). OWL 2 RL/RDF Table 4 row prp-spo2,
// general-n form specialised to n=2: T(p, owl:propertyChainAxiom,
// LIST[p1;p2]) /\ T(x,p1,y) /\ T(y,p2,z) => T(x,p,z). THREE-level
// fold over the wave 3 relift's named top-level helpers
// (owl_chain2_outer / _mid / _emit). Same DEPTH COROLLARY treatment
// as Rules 33/35: `lemma_prp_spo2_witness_holds` assembles the row's
// semantic content flat.
//
// Per the BRIDGE-LEMMA COROLLARY, the list-decode half of this proof
// reuses `decode_chain_pair_sound` (Rule 11 above) VERBATIM rather
// than re-deriving it -- that lemma already carries the four-step
// per-hop spelling (served-object equation -> bucket memP ->
// ig_wf_sp-pinned triple -> record-literal memP in g) the corollary
// requires, so no new list-walk bridge is written here. cond_chain2_
// compose (OWL.Semantics.fst) is the GENERAL 2-hop composition
// condition, distinct from Rule 11's cond_chain2_transitive (which
// specialises the SAME Table 5 row to the self-composition case
// Q=P1=P2=P and reads its TransitiveProperty consequence instead).
// ===================================================================

// The row's semantic content, assembled flat.
val lemma_prp_spo2_witness_holds
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (chain_t : triple) (p_iri : wf_iri) (list_subj : subject)
    (p1 : wf_iri) (p2 : wf_iri)
    (t1 : triple) (y_subj : subject) (z_term : rdf_term)
  : Lemma
    (requires cond_chain2_compose i /\ ig_wf_sp ig /\ ig.ig_triples == g /\
              holds_all i a g /\
              memP chain_t g /\ chain_t.p == owl_propertyChainAxiom /\
              chain_t.s == S_IRI p_iri /\
              term_to_subject chain_t.o == Some list_subj /\
              seq_is i (denot_subject i a list_subj) [i.i_iri p1; i.i_iri p2] /\
              memP t1 g /\ t1.p == p1 /\ term_to_subject t1.o == Some y_subj /\
              memP z_term (find_objects_indexed ig y_subj p2))
    (ensures triple_holds i a ({ s = t1.s; p = p_iri; o = z_term } <: triple))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_prp_spo2_witness_holds i a g ig chain_t p_iri list_subj p1 p2 t1 y_subj z_term =
  let zb = bucket_lookup ig.ig_sp (sp_key y_subj p2) in
  assert (find_objects_indexed ig y_subj p2 == List.Tot.map (fun (u : triple) -> u.o) zb);
  FStar.List.Tot.Properties.memP_map_elim (fun (u : triple) -> u.o) z_term zb;
  eliminate exists (u2 : triple).
      memP u2 zb /\ u2.o == z_term
  returns triple_holds i a ({ s = t1.s; p = p_iri; o = z_term } <: triple)
  with _ . begin
    assert (memP u2 g /\ u2.s == y_subj /\ u2.p == p2);
    assert (triple_holds i a chain_t);
    assert (triple_holds i a t1);
    assert (triple_holds i a u2);
    lemma_denot_term_to_subject i a chain_t.o list_subj;
    lemma_denot_term_to_subject i a t1.o y_subj;
    assert (i.iext (i.i_iri owl_propertyChainAxiom)
                   (denot_subject i a chain_t.s) (denot_term i a chain_t.o));
    assert (i.iext (i.i_iri p1) (denot_subject i a t1.s) (denot_subject i a y_subj));
    assert (i.iext (i.i_iri p2) (denot_subject i a y_subj) (denot_term i a z_term));
    // cond_chain2_compose.
    assert (i.iext (i.i_iri p_iri) (denot_subject i a t1.s) (denot_term i a z_term))
  end
#pop-options

// Level 2 (middle fold, over g): the engine's own
// `owl_chain2_mid ig p_iri p1 p2` is the folded function.
val lemma_prp_spo2_mid_step_sound
    (i : interp) (a : bnode_assignment i.idom)
    (g : rdf_graph) (ig : indexed_graph)
    (chain_t : triple) (p_iri : wf_iri) (list_subj : subject)
    (p1 : wf_iri) (p2 : wf_iri) (acc2 : rdf_graph) (t1 : triple)
  : Lemma
    (requires cond_chain2_compose i /\ ig_wf_sp ig /\ ig.ig_triples == g /\
              holds_all i a g /\
              memP chain_t g /\ chain_t.p == owl_propertyChainAxiom /\
              chain_t.s == S_IRI p_iri /\
              term_to_subject chain_t.o == Some list_subj /\
              seq_is i (denot_subject i a list_subj) [i.i_iri p1; i.i_iri p2] /\
              memP t1 g /\ holds_all i a acc2)
    (ensures holds_all i a (owl_chain2_mid ig p_iri p1 p2 acc2 t1))

#push-options "--z3rlimit 300 --split_queries always"
let lemma_prp_spo2_mid_step_sound i a g ig chain_t p_iri list_subj p1 p2 acc2 t1 =
  if t1.p = p1 then
    match term_to_subject t1.o with
    | Some y_subj ->
      let zs = find_objects_indexed ig y_subj p2 in
      introduce forall (acc3 : rdf_graph) (z_term : rdf_term).
          (memP z_term zs /\ holds_all i a acc3) ==>
          holds_all i a (owl_chain2_emit p_iri t1.s acc3 z_term)
      with introduce (memP z_term zs /\ holds_all i a acc3) ==>
                     holds_all i a (owl_chain2_emit p_iri t1.s acc3 z_term)
      with _ . begin
        lemma_prp_spo2_witness_holds i a g ig chain_t p_iri list_subj p1 p2 t1 y_subj z_term
      end;
      fold_left_inv (holds_all i a) (owl_chain2_emit p_iri t1.s) zs acc2
    | None -> ()
  else ()
#pop-options

val owl_rule_property_chain_2_sound
    (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) (ig : indexed_graph)
  : Lemma
    (requires cond_chain2_compose i /\ ig_wf_sp ig /\ ig.ig_triples == g /\
              holds_all i a g)
    (ensures  holds_all i a (owl_rule_property_chain_2 g ig))

#push-options "--z3rlimit 400 --split_queries always"
let owl_rule_property_chain_2_sound i a g ig =
  introduce forall (acc : rdf_graph) (chain_t : triple).
      (memP chain_t g /\ holds_all i a acc) ==>
      holds_all i a (owl_chain2_outer g ig acc chain_t)
  with introduce (memP chain_t g /\ holds_all i a acc) ==>
                 holds_all i a (owl_chain2_outer g ig acc chain_t)
  with _ . begin
    if chain_t.p = owl_propertyChainAxiom then begin
      match chain_t.s, term_to_subject chain_t.o with
      | S_IRI p_iri, Some list_subj ->
        (match decode_chain_pair g ig list_subj with
         | Some (p1, p2) ->
           decode_chain_pair_sound i a g ig list_subj;
           assert (seq_is i (denot_subject i a list_subj) [i.i_iri p1; i.i_iri p2]);
           introduce forall (acc2 : rdf_graph) (t1 : triple).
               (memP t1 g /\ holds_all i a acc2) ==>
               holds_all i a (owl_chain2_mid ig p_iri p1 p2 acc2 t1)
           with introduce (memP t1 g /\ holds_all i a acc2) ==>
                          holds_all i a (owl_chain2_mid ig p_iri p1 p2 acc2 t1)
           with _ . begin
             lemma_prp_spo2_mid_step_sound i a g ig chain_t p_iri list_subj p1 p2 acc2 t1
           end;
           fold_left_inv (holds_all i a)
             (owl_chain2_mid ig p_iri p1 p2) g acc
         | None -> ())
      | _, _ -> ()
    end else ()
  end;
  fold_left_inv (holds_all i a) (owl_chain2_outer g ig) g g
#pop-options

// ===================================================================
// Entailment corollaries — from per-assignment truth preservation to
// satisfaction and pilot_entails, with the index hypotheses
// discharged against build_indexed where the pilot can discharge
// them. Note (build_indexed g).ig_triples is definitionally g, and
// the pilot rules mint no fresh blank nodes, so the assignment
// chosen for g serves the conclusion graph too.
// ===================================================================

// prp-symp ignores its index argument, so the corollary holds for
// ANY indexed_graph.
val owl_rule_symmetric_property_entailed (g : rdf_graph) (ig : indexed_graph)
  : Lemma (pilot_entails g (owl_rule_symmetric_property g ig))

let owl_rule_symmetric_property_entailed g ig =
  introduce forall (i : interp).
      owl_rl_pilot_conditions i ==> satisfies i g ==>
      satisfies i (owl_rule_symmetric_property g ig)
  with introduce owl_rl_pilot_conditions i ==>
                 (satisfies i g ==> satisfies i (owl_rule_symmetric_property g ig))
  with _ . introduce satisfies i g ==> satisfies i (owl_rule_symmetric_property g ig)
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (owl_rule_symmetric_property g ig)
    with _ . begin
      owl_rule_symmetric_property_sound i a g ig;
      assert (holds_all i a (owl_rule_symmetric_property g ig))
    end
  end

val rdfs_rule_domain_entailed (g : rdf_graph)
  : Lemma (pilot_entails g (rdfs_rule_domain g (build_indexed g)))

let rdfs_rule_domain_entailed g =
  introduce forall (i : interp).
      owl_rl_pilot_conditions i ==> satisfies i g ==>
      satisfies i (rdfs_rule_domain g (build_indexed g))
  with introduce owl_rl_pilot_conditions i ==>
                 (satisfies i g ==> satisfies i (rdfs_rule_domain g (build_indexed g)))
  with _ . introduce satisfies i g ==> satisfies i (rdfs_rule_domain g (build_indexed g))
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (rdfs_rule_domain g (build_indexed g))
    with _ . begin
      lemma_build_indexed_wf_pred g;
      assert ((build_indexed g).ig_triples == g);
      rdfs_rule_domain_sound i a g (build_indexed g);
      assert (holds_all i a (rdfs_rule_domain g (build_indexed g)))
    end
  end

val rdfs_rule_range_entailed (g : rdf_graph)
  : Lemma (pilot_entails g (rdfs_rule_range g (build_indexed g)))

let rdfs_rule_range_entailed g =
  introduce forall (i : interp).
      owl_rl_pilot_conditions i ==> satisfies i g ==>
      satisfies i (rdfs_rule_range g (build_indexed g))
  with introduce owl_rl_pilot_conditions i ==>
                 (satisfies i g ==> satisfies i (rdfs_rule_range g (build_indexed g)))
  with _ . introduce satisfies i g ==> satisfies i (rdfs_rule_range g (build_indexed g))
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (rdfs_rule_range g (build_indexed g))
    with _ . begin
      lemma_build_indexed_wf_pred g;
      assert ((build_indexed g).ig_triples == g);
      rdfs_rule_range_sound i a g (build_indexed g);
      assert (holds_all i a (rdfs_rule_range g (build_indexed g)))
    end
  end

val owl_rule_sameAs_symmetry_entailed (g : rdf_graph)
  : Lemma (pilot_entails g (owl_rule_sameAs_symmetry g (build_indexed g)))

let owl_rule_sameAs_symmetry_entailed g =
  introduce forall (i : interp).
      owl_rl_pilot_conditions i ==> satisfies i g ==>
      satisfies i (owl_rule_sameAs_symmetry g (build_indexed g))
  with introduce owl_rl_pilot_conditions i ==>
                 (satisfies i g ==> satisfies i (owl_rule_sameAs_symmetry g (build_indexed g)))
  with _ . introduce satisfies i g ==> satisfies i (owl_rule_sameAs_symmetry g (build_indexed g))
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (owl_rule_sameAs_symmetry g (build_indexed g))
    with _ . begin
      assert ((build_indexed g).ig_triples == g);
      owl_rule_sameAs_symmetry_sound i a g (build_indexed g);
      assert (holds_all i a (owl_rule_sameAs_symmetry g (build_indexed g)))
    end
  end

// cls-oo's corollary is CONDITIONAL on the ig_sp component-recovery
// clause: the pilot proves the weak half against build_indexed
// (lemma_build_indexed_wf_sp_weak — membership plus the composite-key
// equation); recovering t.s == s /\ t.p == p from the key equation
// needs sp_key injectivity, which fails if a blank-node label may
// contain U+001F. Finding F1 in the design doc; the framework keeps
// the hypothesis explicit rather than assuming it silently.
val owl_rule_cls_oneof_entailed (g : rdf_graph)
  : Lemma
    (requires ig_wf_sp (build_indexed g))
    (ensures pilot_entails g (owl_rule_cls_oneof g (build_indexed g)))

let owl_rule_cls_oneof_entailed g =
  introduce forall (i : interp).
      owl_rl_pilot_conditions i ==> satisfies i g ==>
      satisfies i (owl_rule_cls_oneof g (build_indexed g))
  with introduce owl_rl_pilot_conditions i ==>
                 (satisfies i g ==> satisfies i (owl_rule_cls_oneof g (build_indexed g)))
  with _ . introduce satisfies i g ==> satisfies i (owl_rule_cls_oneof g (build_indexed g))
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies i (owl_rule_cls_oneof g (build_indexed g))
    with _ . begin
      assert ((build_indexed g).ig_triples == g);
      owl_rule_cls_oneof_sound i a g (build_indexed g);
      assert (holds_all i a (owl_rule_cls_oneof g (build_indexed g)))
    end
  end
