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
