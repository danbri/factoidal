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
