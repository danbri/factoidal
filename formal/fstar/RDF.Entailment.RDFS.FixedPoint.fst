module RDF.Entailment.RDFS.FixedPoint

// ===================================================================
// The FAITHFUL FIXED-POINT story for `rdfs_closure` (gap #3 of
// docs/claude-rules/rdf-rdfs-semantics-coverage.md).
//
// `rdfs_closure` (RDFS.Closure.fsti) is fuel-bounded and stops early
// on `graph_len (rdfs_closure_step g) = graph_len g`. The design note
// (docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md
// section 6, obligation 2) flags this as a possibly UNFAITHFUL
// fixed-point test: `rdfs_closure_step` ends in `graph_dedup_sort`, so
// a step that both ADDS a new triple and DROPS a duplicate could
// leave the length unchanged while the graph's actual content
// changed -- length equality would then not imply "no rule derives
// anything new".
//
// THIS MODULE:
//   1. Defines the SEMANTIC fixed point directly, membership-wise
//      (`step_saturated`), independent of any length bookkeeping.
//   2. Proves the step is EXTENSIVE (every input triple survives the
//      step) -- unconditionally for the twelve-rule chain that
//      precedes the final `graph_dedup_sort`, and, for the dedup
//      itself, conditional on a `no_dup_keys` canonicity hypothesis
//      (section 5 explains exactly why that hypothesis cannot be
//      dropped: `triple_to_key` is NOT unconditionally injective in
//      this tree).
//   3. Delivers the saturation-stability theorem (b) in the honest
//      form the extensivity + saturation machinery actually supports,
//      and STOPS the length-test-faithfulness theorem (a) with a
//      precise account of the combinatorial fact that blocks it
//      (section 8).
//
// FINDING, stated up front (full argument in section 8): the length
// test in `rdfs_closure` is faithful ONLY modulo the same key-
// injectivity gap the project already tracks for `sp_key`/`po_key`
// (RDF.Indexed.KeyInjectivity, issue #338) -- and that gap is WIDER
// here, because `graph_dedup_sort`'s key (`RDF.Graph.triple_to_key`)
// also folds literal content through an ad hoc "^^" join
// (RDF.Graph.fsti's `term_to_key_total`, T_Literal case) that is not
// even a control-character separator like `unit_sep`.
//
// Verify-only module; nothing here extracts, and nothing here is
// wired into build-ocaml.sh (orchestrator's job on landing).
// ===================================================================

open FStar.List.Tot
open FStar.List.Tot.Properties
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDF.Indexed.StringOrder
open RDFS.Closure
open OWL.Semantics.MemLemmas
open RDF.Entailment.RDFS.Refinement
open RDF.Entailment.RDFS.ModelTheory
open RDF.Indexed.KeyInjectivity
open RDF.Entailment.RDFS.SepFree

// ===================================================================
// 1. THE SEMANTIC FIXED POINT.
//
// A graph is step-saturated when the step derives nothing new: every
// triple the step's output carries was already in the input. This is
// the MEMBERSHIP-LEVEL fixed-point condition the design note says the
// LENGTH test is supposed to be a proxy for.
// ===================================================================

let step_saturated (g : rdf_graph) : prop =
  forall (t : triple). memP t (rdfs_closure_step g) ==> memP t g

// ===================================================================
// 2. ATOMIC MONOTONICITY.
//
// `add_triple_unchecked g t = t :: g` (RDF.Graph.fsti) -- a bare
// prepend, so anything in `g` is still in the result. `emit_once` /
// `emit_once_term` (RDFS.Closure.fsti) each either return the
// accumulator UNCHANGED (the snapshot already carries the
// conclusion) or call `add_triple_unchecked` on it -- never anything
// that removes an element.
// ===================================================================

let lemma_add_triple_unchecked_extensive (acc : rdf_graph) (t x : triple)
  : Lemma (memP x acc ==> memP x (add_triple_unchecked acc t)) = ()

let lemma_emit_once_term_extensive (ig : indexed_graph) (acc : rdf_graph)
    (sub : subject) (prd : wf_iri) (obj : rdf_term) (x : triple)
  : Lemma (memP x acc ==> memP x (emit_once_term ig acc sub prd obj)) =
  lemma_add_triple_unchecked_extensive acc ({ s = sub; p = prd; o = obj } <: triple) x

let lemma_emit_once_extensive (ig : indexed_graph) (acc : rdf_graph)
    (sub : subject) (prd : wf_iri) (cls : wf_iri) (x : triple)
  : Lemma (memP x acc ==> memP x (emit_once ig acc sub prd cls)) =
  lemma_add_triple_unchecked_extensive acc ({ s = sub; p = prd; o = T_IRI cls } <: triple) x

// ===================================================================
// 3. PER-RULE EXTENSIVITY: each of the twelve rows `rdfs_closure_step`
// chains only ever ADDS triples on top of its seed accumulator.
//
// Proved via `OWL.Semantics.MemLemmas.fold_left_inv`, instantiated
// with the invariant "the fixed target triple `x` is a member" --
// following the EXACT proof shape RDF.Entailment.RDFS.Refinement.fst
// already uses for the `_licensed` theorems of these same rules
// (local `step`/`inner_step` re-spelling the engine's fold, an
// `introduce forall` establishing per-element preservation, then
// `fold_left_inv` and an `assert_norm` bridge back to the shipping
// function). `rdfs_rule_subPropertyOf` needs the SAME special
// handling that file's own comment documents at its rdfs7 proof
// (section 4 there): its inner lambda closes over `q`, a variable
// bound by the OUTER match pattern (`S_IRI p, T_IRI q`) rather than a
// plain field projection, so the standard bridge does not iota-reduce
// without first rebuilding `decl` as a record literal.
// ===================================================================

#push-options "--z3rlimit 60"

let lemma_rdfs_rule_subPropertyOf_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_subPropertyOf g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s, decl.o with
      | S_IRI p, T_IRI q ->
        let matching = bucket_lookup ig.ig_pred p in
        fold_left
          (fun (acc2 : rdf_graph) (t : triple) -> emit_once_term ig acc2 t.s q t.o)
          acc matching
      | _, _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with introduce (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with _ . begin
    // Constructor-complete case split on the PAIR, not a catch-all:
    // `outer_step` only reduces the fall-through arms when each
    // component has its own constructor equation (same trap
    // RDF.Entailment.RDFS.Refinement.rdfs_rule_subPropertyOf_licensed
    // documents).
    match decl.s, decl.o with
    | S_BNode _, _ -> ()
    | S_IRI _, T_BNode _ -> ()
    | S_IRI _, T_Literal _ -> ()
    | S_IRI _, T_TripleTerm _ _ _ -> ()
    | S_IRI p, T_IRI q ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) -> emit_once_term ig acc2 t.s q t.o in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with introduce (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with _ . lemma_emit_once_term_extensive ig acc2 t.s q t.o x;
      fold_left_inv inv inner_step matching acc;
      // The rdfs7 special case (Refinement.fst section 4's own
      // comment): `q` is pattern-bound, not a field projection, so
      // bridge via a rebuilt record literal.
      let decl' : triple = { s = S_IRI p; p = decl.p; o = T_IRI q } in
      assert (decl == decl');
      assert_norm (outer_step acc decl' == fold_left inner_step acc
                     (bucket_lookup ig.ig_pred p))
  end;
  introduce memP x g ==> memP x (rdfs_rule_subPropertyOf g ig)
  with _ . begin
    fold_left_inv inv outer_step decls g;
    assert_norm (rdfs_rule_subPropertyOf g ig == fold_left outer_step g decls)
  end

let lemma_rdfs_rule_domain_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_domain g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        fold_left
          (fun (acc2 : rdf_graph) (t : triple) -> emit_once_term ig acc2 t.s rdf_type decl.o)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with introduce (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with _ . begin
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) -> emit_once_term ig acc2 t.s rdf_type decl.o in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with introduce (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with _ . lemma_emit_once_term_extensive ig acc2 t.s rdf_type decl.o x;
      fold_left_inv inv inner_step matching acc
    | _ -> ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_domain g ig)
  with _ . begin
    fold_left_inv inv outer_step decls g;
    assert_norm (rdfs_rule_domain g ig == fold_left outer_step g decls)
  end

let lemma_rdfs_rule_range_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_range g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let decls = bucket_lookup ig.ig_pred rdfs_range in
  let outer_step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            match term_to_subject t.o with
            | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type decl.o
            | None -> acc2)
          acc matching
      | _ -> acc in
  introduce forall (acc : rdf_graph) (decl : triple).
      (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with introduce (memP decl decls /\ inv acc) ==> inv (outer_step acc decl)
  with _ . begin
    match decl.s with
    | S_IRI p ->
      let matching = bucket_lookup ig.ig_pred p in
      let inner_step : rdf_graph -> triple -> rdf_graph =
        fun (acc2 : rdf_graph) (t : triple) ->
          match term_to_subject t.o with
          | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type decl.o
          | None -> acc2 in
      introduce forall (acc2 : rdf_graph) (t : triple).
          (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with introduce (memP t matching /\ inv acc2) ==> inv (inner_step acc2 t)
      with _ . begin
        match term_to_subject t.o with
        | Some b_subj -> lemma_emit_once_term_extensive ig acc2 b_subj rdf_type decl.o x
        | None -> ()
      end;
      fold_left_inv inv inner_step matching acc
    | _ -> ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_range g ig)
  with _ . begin
    fold_left_inv inv outer_step decls g;
    assert_norm (rdfs_rule_range g ig == fold_left outer_step g decls)
  end

let lemma_rdfs_rule_subClassOf_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_subClassOf g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type then
        match t.o with
        | T_IRI class_iri ->
          let super_classes = find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf in
          fold_left
            (fun (acc2 : rdf_graph) (b_term : rdf_term) -> emit_once_term ig acc2 t.s rdf_type b_term)
            acc super_classes
        | _ -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if t.p = rdf_type then
      match t.o with
      | T_IRI class_iri ->
        let super_classes = find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (b_term : rdf_term) -> emit_once_term ig acc2 t.s rdf_type b_term in
        introduce forall (acc2 : rdf_graph) (b_term : rdf_term).
            (memP b_term super_classes /\ inv acc2) ==> inv (inner_step acc2 b_term)
        with introduce (memP b_term super_classes /\ inv acc2) ==> inv (inner_step acc2 b_term)
        with _ . lemma_emit_once_term_extensive ig acc2 t.s rdf_type b_term x;
        fold_left_inv inv inner_step super_classes acc
      | _ -> ()
    else ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_subClassOf g ig)
  with _ . begin
    fold_left_inv inv step g g;
    assert_norm (rdfs_rule_subClassOf g ig == fold_left step g g)
  end

let lemma_rdfs_rule_subClassOf_trans_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_subClassOf_trans g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        match term_to_subject t.o with
        | Some b_subj ->
          let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
          fold_left
            (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
              add_triple_unchecked acc2 ({ s = t.s; p = rdfs_subClassOf; o = c_term } <: triple))
            acc supers
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if t.p = rdfs_subClassOf then
      match term_to_subject t.o with
      | Some b_subj ->
        let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (c_term : rdf_term) ->
            add_triple_unchecked acc2 ({ s = t.s; p = rdfs_subClassOf; o = c_term } <: triple) in
        introduce forall (acc2 : rdf_graph) (c_term : rdf_term).
            (memP c_term supers /\ inv acc2) ==> inv (inner_step acc2 c_term)
        with introduce (memP c_term supers /\ inv acc2) ==> inv (inner_step acc2 c_term)
        with _ . lemma_add_triple_unchecked_extensive acc2
                   ({ s = t.s; p = rdfs_subClassOf; o = c_term } <: triple) x;
        fold_left_inv inv inner_step supers acc
      | None -> ()
    else ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_subClassOf_trans g ig)
  with _ . begin
    fold_left_inv inv step g g;
    assert_norm (rdfs_rule_subClassOf_trans g ig == fold_left step g g)
  end

let lemma_rdfs_rule_subPropertyOf_trans_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_subPropertyOf_trans g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let step : rdf_graph -> triple -> rdf_graph =
    fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match term_to_subject t.o with
        | Some q_subj ->
          let supers = find_objects_indexed ig q_subj rdfs_subPropertyOf in
          fold_left
            (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
              add_triple_unchecked acc2 ({ s = t.s; p = rdfs_subPropertyOf; o = r_term } <: triple))
            acc supers
        | None -> acc
      else acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (step acc t)
  with introduce (memP t g /\ inv acc) ==> inv (step acc t)
  with _ . begin
    if t.p = rdfs_subPropertyOf then
      match term_to_subject t.o with
      | Some q_subj ->
        let supers = find_objects_indexed ig q_subj rdfs_subPropertyOf in
        let inner_step : rdf_graph -> rdf_term -> rdf_graph =
          fun (acc2 : rdf_graph) (r_term : rdf_term) ->
            add_triple_unchecked acc2 ({ s = t.s; p = rdfs_subPropertyOf; o = r_term } <: triple) in
        introduce forall (acc2 : rdf_graph) (r_term : rdf_term).
            (memP r_term supers /\ inv acc2) ==> inv (inner_step acc2 r_term)
        with introduce (memP r_term supers /\ inv acc2) ==> inv (inner_step acc2 r_term)
        with _ . lemma_add_triple_unchecked_extensive acc2
                   ({ s = t.s; p = rdfs_subPropertyOf; o = r_term } <: triple) x;
        fold_left_inv inv inner_step supers acc
      | None -> ()
    else ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_subPropertyOf_trans g ig)
  with _ . begin
    fold_left_inv inv step g g;
    assert_norm (rdfs_rule_subPropertyOf_trans g ig == fold_left step g g)
  end

let lemma_rdfs_rule_container_membership_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_container_membership g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  let step : rdf_graph -> wf_iri -> rdf_graph =
    fun (acc : rdf_graph) (cmp : wf_iri) ->
      let t1 : triple = { s = S_IRI cmp; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } in
      let t2 : triple = { s = S_IRI cmp; p = rdf_type; o = T_IRI rdfs_ContainerMembershipProperty } in
      add_triple_unchecked (add_triple_unchecked acc t1) t2 in
  introduce forall (acc : rdf_graph) (cmp : wf_iri).
      (memP cmp container_membership_properties /\ inv acc) ==> inv (step acc cmp)
  with introduce (memP cmp container_membership_properties /\ inv acc) ==> inv (step acc cmp)
  with _ . begin
    let t1 : triple = { s = S_IRI cmp; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } in
    lemma_add_triple_unchecked_extensive acc t1 x;
    let t2 : triple = { s = S_IRI cmp; p = rdf_type; o = T_IRI rdfs_ContainerMembershipProperty } in
    lemma_add_triple_unchecked_extensive (add_triple_unchecked acc t1) t2 x
  end;
  introduce memP x g ==> memP x (rdfs_rule_container_membership g ig)
  with _ . begin
    fold_left_inv inv step container_membership_properties g;
    assert_norm (rdfs_rule_container_membership g ig ==
                 fold_left step g container_membership_properties)
  end

// The five RS-2 rows: each is `List.Tot.fold_left (rdfsN_step ig) g g`
// where `rdfsN_step` is ALREADY a named, top-level RDFS.Closure.fsti
// function (no re-spelling needed, so no closure-identity concern).

let lemma_rdfs_rule_recognized_datatypes_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_recognized_datatypes g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  introduce forall (acc : rdf_graph) (d : wf_iri).
      (memP d recognized_datatypes /\ inv acc) ==> inv (rdfs1_step ig acc d)
  with introduce (memP d recognized_datatypes /\ inv acc) ==> inv (rdfs1_step ig acc d)
  with _ . lemma_emit_once_extensive ig acc (S_IRI d) rdf_type rdfs_Datatype x;
  introduce memP x g ==> memP x (rdfs_rule_recognized_datatypes g ig)
  with _ . fold_left_inv inv (rdfs1_step ig) recognized_datatypes g

let lemma_rdfs_rule_resource_subject_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_resource_subject g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (rdfs4a_step ig acc t)
  with introduce (memP t g /\ inv acc) ==> inv (rdfs4a_step ig acc t)
  with _ . lemma_emit_once_extensive ig acc t.s rdf_type rdfs_Resource x;
  introduce memP x g ==> memP x (rdfs_rule_resource_subject g ig)
  with _ . fold_left_inv inv (rdfs4a_step ig) g g

let lemma_rdfs_rule_resource_object_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_resource_object g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (rdfs4b_step ig acc t)
  with introduce (memP t g /\ inv acc) ==> inv (rdfs4b_step ig acc t)
  with _ . begin
    match term_to_subject t.o with
    | Some y_subj -> lemma_emit_once_extensive ig acc y_subj rdf_type rdfs_Resource x
    | None -> ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_resource_object g ig)
  with _ . fold_left_inv inv (rdfs4b_step ig) g g

let lemma_rdfs_rule_class_subclass_resource_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_class_subclass_resource g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (rdfs8_step ig acc t)
  with introduce (memP t g /\ inv acc) ==> inv (rdfs8_step ig acc t)
  with _ . begin
    if is_typed_as t rdfs_Class
    then lemma_emit_once_extensive ig acc t.s rdfs_subClassOf rdfs_Resource x
    else ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_class_subclass_resource g ig)
  with _ . fold_left_inv inv (rdfs8_step ig) g g

let lemma_rdfs_rule_datatype_subclass_literal_extensive (g : rdf_graph) (ig : indexed_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_rule_datatype_subclass_literal g ig)) =
  let inv (acc : rdf_graph) : prop = memP x acc in
  introduce forall (acc : rdf_graph) (t : triple).
      (memP t g /\ inv acc) ==> inv (rdfs13_step ig acc t)
  with introduce (memP t g /\ inv acc) ==> inv (rdfs13_step ig acc t)
  with _ . begin
    if is_typed_as t rdfs_Datatype
    then lemma_emit_once_extensive ig acc t.s rdfs_subClassOf rdfs_Literal x
    else ()
  end;
  introduce memP x g ==> memP x (rdfs_rule_datatype_subclass_literal g ig)
  with _ . fold_left_inv inv (rdfs13_step ig) g g

#pop-options

// ===================================================================
// 4. THE PRE-DEDUP ACCUMULATOR AND ITS EXTENSIVITY (unconditional).
//
// `rdfs_closure_step_pre_dedup` mirrors `RDFS.Closure.rdfs_closure_step`
// VERBATIM, minus the closing `graph_dedup_sort`, so section 3's
// per-rule lemmas chain into one fact about the exact accumulator
// `rdfs_closure_step` itself builds before deduplicating.
// ===================================================================

let rdfs_closure_step_pre_dedup (g : rdf_graph) : rdf_graph =
  let ig = build_indexed g in
  let g1 = rdfs_rule_subPropertyOf g ig in
  let g2 = rdfs_rule_domain g1 ig in
  let g3 = rdfs_rule_range g2 ig in
  let g4 = rdfs_rule_subClassOf g3 ig in
  let g5 = rdfs_rule_container_membership g4 ig in
  let g6 = rdfs_rule_subClassOf_trans g5 ig in
  let g7 = rdfs_rule_subPropertyOf_trans g6 ig in
  let g8  = rdfs_rule_recognized_datatypes g7 ig in
  let g9  = rdfs_rule_class_subclass_resource g8 ig in
  let g10 = rdfs_rule_datatype_subclass_literal g9 ig in
  let g11 = rdfs_rule_resource_subject g10 ig in
  rdfs_rule_resource_object g11 ig

let lemma_step_is_dedup_of_pre_dedup (g : rdf_graph)
  : Lemma (rdfs_closure_step g == graph_dedup_sort (rdfs_closure_step_pre_dedup g)) = ()

#push-options "--z3rlimit 60"
let lemma_pre_dedup_extensive (g : rdf_graph) (x : triple)
  : Lemma (memP x g ==> memP x (rdfs_closure_step_pre_dedup g)) =
  let ig = build_indexed g in
  introduce memP x g ==> memP x (rdfs_closure_step_pre_dedup g)
  with _ . begin
    lemma_rdfs_rule_subPropertyOf_extensive g ig x;
    let g1 = rdfs_rule_subPropertyOf g ig in
    lemma_rdfs_rule_domain_extensive g1 ig x;
    let g2 = rdfs_rule_domain g1 ig in
    lemma_rdfs_rule_range_extensive g2 ig x;
    let g3 = rdfs_rule_range g2 ig in
    lemma_rdfs_rule_subClassOf_extensive g3 ig x;
    let g4 = rdfs_rule_subClassOf g3 ig in
    lemma_rdfs_rule_container_membership_extensive g4 ig x;
    let g5 = rdfs_rule_container_membership g4 ig in
    lemma_rdfs_rule_subClassOf_trans_extensive g5 ig x;
    let g6 = rdfs_rule_subClassOf_trans g5 ig in
    lemma_rdfs_rule_subPropertyOf_trans_extensive g6 ig x;
    let g7 = rdfs_rule_subPropertyOf_trans g6 ig in
    lemma_rdfs_rule_recognized_datatypes_extensive g7 ig x;
    let g8 = rdfs_rule_recognized_datatypes g7 ig in
    lemma_rdfs_rule_class_subclass_resource_extensive g8 ig x;
    let g9 = rdfs_rule_class_subclass_resource g8 ig in
    lemma_rdfs_rule_datatype_subclass_literal_extensive g9 ig x;
    let g10 = rdfs_rule_datatype_subclass_literal g9 ig in
    lemma_rdfs_rule_resource_subject_extensive g10 ig x;
    let g11 = rdfs_rule_resource_subject g10 ig in
    lemma_rdfs_rule_resource_object_extensive g11 ig x
  end
#pop-options

// ===================================================================
// 5. THE DEDUP-SORT COMPLETENESS DIRECTION.
//
// `RDF.Entailment.RDFS.Refinement.lemma_graph_dedup_sort_memP` is the
// OUT direction: `memP x (graph_dedup_sort g) ==> memP x g`. The IN
// direction -- every element of `g` SURVIVES the dedup -- is what
// `lemma_step_extensive` (section 6) additionally needs, and it does
// NOT hold unconditionally: `graph_dedup_sort` keeps exactly one
// representative per `triple_to_key` VALUE, so if two DISTINCT
// triples in `g` collide on that key, one of them is dropped.
//
// `no_dup_keys` names the canonicity hypothesis that rules this out.
// The induction below carries a "the previous kept key already has a
// representative in `acc`" invariant through
// `dedup_sorted_decorated_aux`: whenever the walk is about to drop a
// pair `(k, t)` as a duplicate of `prev`, `no_dup_keys` (restricted to
// the combined multiset still in play) identifies that representative
// with `t`, so dropping `t` loses nothing.
// ===================================================================

let no_dup_keys (h : list triple) : prop =
  forall (t1 t2 : triple). memP t1 h /\ memP t2 h /\ triple_to_key t1 == triple_to_key t2 ==> t1 == t2

let no_dup_keys_combined (ts : list (string * triple)) (acc : list triple) : prop =
  forall (t1 t2 : triple).
    (memP t1 (map snd ts) \/ memP t1 acc) /\
    (memP t2 (map snd ts) \/ memP t2 acc) /\
    triple_to_key t1 == triple_to_key t2 ==> t1 == t2

let decoration_consistent (ts : list (string * triple)) : prop =
  forall (p : (string * triple)). memP p ts ==> fst p == triple_to_key (snd p)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec lemma_dedup_sorted_decorated_extensive
    (prev : option string) (ts : list (string * triple)) (acc : list triple) (x : triple)
  : Lemma
    (requires
      decoration_consistent ts /\
      no_dup_keys_combined ts acc /\
      (match prev with
       | Some k -> exists (u : triple). memP u acc /\ triple_to_key u == k
       | None -> True))
    (ensures (memP x (map snd ts) \/ memP x acc) ==>
             memP x (dedup_sorted_decorated_aux prev ts acc))
    (decreases ts) =
  match ts with
  | [] -> introduce memP x acc ==> memP x (dedup_sorted_decorated_aux prev [] acc)
          with _ . rev_memP acc x
  | (k, t) :: rest ->
    let dup = match prev with | Some p -> p = k | None -> false in
    if dup then begin
      (match prev with
       | Some p ->
         eliminate exists (u : triple). memP u acc /\ triple_to_key u == p
         returns (memP x (map snd ts) \/ memP x acc) ==>
                 memP x (dedup_sorted_decorated_aux prev rest acc)
         with _ . begin
           introduce (memP x (map snd ts) \/ memP x acc) ==>
                     memP x (dedup_sorted_decorated_aux prev rest acc)
           with _ . begin
             if FStar.StrongExcludedMiddle.strong_excluded_middle (x == t) then begin
               assert (memP t (map snd ((k, t) :: rest)));
               assert (memP u acc);
               assert (triple_to_key u == triple_to_key t);
               lemma_dedup_sorted_decorated_extensive prev rest acc x
             end else
               lemma_dedup_sorted_decorated_extensive prev rest acc x
           end
         end
       | None -> ())
    end else begin
      lemma_dedup_sorted_decorated_extensive (Some k) rest (t :: acc) x
    end
#pop-options

let rec lemma_map_snd_decorate (g : list triple)
  : Lemma (ensures List.Tot.map snd (List.Tot.map (fun (t : triple) -> (triple_to_key t, t)) g) == g)
          (decreases g) =
  match g with
  | [] -> ()
  | _ :: tl -> lemma_map_snd_decorate tl

// `graph_dedup_sort` runs `dedup_sorted_decorated_aux` over the
// SORTED decorated list, not the raw one -- `sortWith` reorders, so
// section 5's induction (which needs no particular order, only
// membership facts) has to be handed the sorted list. That needs
// `sortWith` membership preservation BOTH ways; the tree's own
// `OWL.Semantics.MemLemmas.lemma_sortWith_memP` proves only the OUT
// direction. Same recursive proof, IFF instead of ==>: `partition_memP`
// and `append_memP` are already IFFs (Type, not eqtype), so the
// upgrade is free.
let rec lemma_sortWith_memP_iff (#a : Type) (cmp : a -> a -> Tot int) (l : list a) (y : a)
  : Lemma (ensures memP y (List.Tot.sortWith cmp l) <==> memP y l)
          (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare cmp pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare cmp pivot) tl;
    lemma_sortWith_memP_iff cmp lo y;
    lemma_sortWith_memP_iff cmp hi y;
    lemma_partition_memP (List.Tot.bool_of_compare cmp pivot) tl y;
    List.Tot.append_memP (List.Tot.sortWith cmp lo) (pivot :: List.Tot.sortWith cmp hi) y

#push-options "--z3rlimit 150"
val lemma_graph_dedup_sort_extensive (g : list triple) (x : triple)
  : Lemma (requires no_dup_keys g /\ memP x g)
          (ensures memP x (graph_dedup_sort g))

let lemma_graph_dedup_sort_extensive g x =
  let f = fun (t : triple) -> (triple_to_key t, t) in
  let dec : list (string * triple) = List.Tot.map f g in
  let sorted : list (string * triple) = List.Tot.sortWith cmp_decorated_triple dec in
  lemma_map_snd_decorate g;
  assert (List.Tot.map snd dec == g);
  // decoration_consistent transports from `dec` to `sorted` since both
  // are pure membership (memP) facts and sortWith preserves membership
  // (`lemma_sortWith_memP_iff`).
  introduce forall (p : (string * triple)). memP p dec ==> fst p == triple_to_key (snd p)
  with introduce memP p dec ==> fst p == triple_to_key (snd p)
  with _ . begin
    memP_map_elim f p g;
    eliminate exists (t : triple). memP t g /\ f t == p
    returns fst p == triple_to_key (snd p)
    with _ . ()
  end;
  introduce forall (p : (string * triple)). memP p sorted ==> fst p == triple_to_key (snd p)
  with introduce memP p sorted ==> fst p == triple_to_key (snd p)
  with _ . lemma_sortWith_memP_iff cmp_decorated_triple dec p;
  assert (decoration_consistent sorted);
  // no_dup_keys_combined for `sorted`: every element of `map snd
  // sorted` traces back (via sortWith's membership-iff, then the
  // decoration map) to a member of `g`, so `no_dup_keys g` (the
  // hypothesis) supplies the conclusion directly.
  introduce forall (t1 t2 : triple).
      (memP t1 (List.Tot.map snd sorted) \/ memP t1 ([] <: list triple)) /\
      (memP t2 (List.Tot.map snd sorted) \/ memP t2 ([] <: list triple)) /\
      triple_to_key t1 == triple_to_key t2 ==> t1 == t2
  with introduce
      (memP t1 (List.Tot.map snd sorted) \/ memP t1 ([] <: list triple)) /\
      (memP t2 (List.Tot.map snd sorted) \/ memP t2 ([] <: list triple)) /\
      triple_to_key t1 == triple_to_key t2 ==> t1 == t2
  with _ . begin
    memP_map_elim snd t1 sorted;
    eliminate exists (p1 : (string * triple)). memP p1 sorted /\ snd p1 == t1
    returns t1 == t2
    with _ . begin
      memP_map_elim snd t2 sorted;
      eliminate exists (p2 : (string * triple)). memP p2 sorted /\ snd p2 == t2
      returns t1 == t2
      with _ . begin
        lemma_sortWith_memP_iff cmp_decorated_triple dec p1;
        lemma_sortWith_memP_iff cmp_decorated_triple dec p2;
        memP_map_elim f p1 g;
        eliminate exists (u1 : triple). memP u1 g /\ f u1 == p1
        returns t1 == t2
        with _ . begin
          memP_map_elim f p2 g;
          eliminate exists (u2 : triple). memP u2 g /\ f u2 == p2
          returns t1 == t2
          with _ . ()
        end
      end
    end
  end;
  assert (no_dup_keys_combined sorted ([] <: list triple));
  lemma_dedup_sorted_decorated_extensive None sorted ([] <: list triple) x;
  // Discharge the implication's antecedent: memP x g gives
  // memP (triple_to_key x, x) dec (decoration), hence memP (triple_to_key
  // x, x) sorted (sortWith iff), hence memP x (map snd sorted).
  memP_map_intro f x g;
  lemma_sortWith_memP_iff cmp_decorated_triple dec (triple_to_key x, x);
  memP_map_intro snd (triple_to_key x, x) sorted
#pop-options

// ===================================================================
// 6. FULL STEP EXTENSIVITY.
//
// Combines the unconditional pre-dedup chain (section 4) with the
// conditional dedup-sort completeness direction (section 5). The
// `no_dup_keys` hypothesis is stated over the PRE-DEDUP accumulator,
// not over `g` -- that is the graph the final `graph_dedup_sort`
// actually reads.
// ===================================================================

val lemma_step_extensive (g : rdf_graph)
  : Lemma (requires no_dup_keys (rdfs_closure_step_pre_dedup g))
          (ensures forall (t : triple). memP t g ==> memP t (rdfs_closure_step g))

let lemma_step_extensive g =
  introduce forall (t : triple). memP t g ==> memP t (rdfs_closure_step g)
  with introduce memP t g ==> memP t (rdfs_closure_step g)
  with _ . begin
    lemma_pre_dedup_extensive g t;
    lemma_graph_dedup_sort_extensive (rdfs_closure_step_pre_dedup g) t;
    lemma_step_is_dedup_of_pre_dedup g
  end

// ===================================================================
// 7. SATURATION IS STABLE UNDER ITERATION.
//
// The task's literal ask is `Lemma (requires step_saturated g)
// (ensures forall n t. memP t (closure_iter g n) <==> memP t g)` --
// saturation of `g` ALONE. That needs a MEMBERSHIP-CONGRUENCE
// property of `rdfs_closure_step` this tree does not have -- "if `h1`
// and `h2` have the same membership set, so do `rdfs_closure_step h1`
// and `rdfs_closure_step h2`" -- because `step_saturated g` is a fact
// about `g` specifically, but the induction's (n-1)-th iterate is a
// DIFFERENT graph (`closure_iter g (n-1)`) only known to share `g`'s
// membership SET, not its list identity. See section 8's STOP note.
//
// What IS delivered here is the version that composes with a
// SATURATION WITNESS CHECKED AT EVERY ITERATE -- exactly the pairing
// item 4 of the brief recommends: once fuel is sufficient to reach a
// fixed point AND that fixed point (and everything after it) is
// independently confirmed saturated and canonical, membership is
// provably stable for all further n.
// ===================================================================

let closure_chain_saturated (g : rdf_graph) : prop =
  forall (n : nat). step_saturated (closure_iter g n)

let closure_chain_canonical (g : rdf_graph) : prop =
  forall (n : nat). no_dup_keys (rdfs_closure_step_pre_dedup (closure_iter g n))

// RIGHT-recursion commutation for `closure_iter`: the definition
// itself is LEFT-recursive; this is the other association ("step the
// (n-1)-th iterate LAST"), proved by induction on `n` re-applied at
// `rdfs_closure_step g` in place of `g`.
let rec lemma_closure_iter_step_shift (g : rdf_graph) (n : nat)
  : Lemma (ensures closure_iter g (n + 1) == rdfs_closure_step (closure_iter g n))
          (decreases n) =
  if n = 0 then ()
  else lemma_closure_iter_step_shift (rdfs_closure_step g) (n - 1)

#push-options "--z3rlimit 100"
let rec lemma_saturated_stable_at (g : rdf_graph) (n : nat) (t : triple)
  : Lemma
    (requires closure_chain_saturated g /\ closure_chain_canonical g)
    (ensures memP t (closure_iter g n) <==> memP t g)
    (decreases n) =
  if n = 0 then ()
  else begin
    lemma_saturated_stable_at g (n - 1) t;
    lemma_closure_iter_step_shift g (n - 1);
    let h = closure_iter g (n - 1) in
    assert (closure_iter g n == rdfs_closure_step h);
    assert (step_saturated h);
    assert (no_dup_keys (rdfs_closure_step_pre_dedup h));
    lemma_step_extensive h
  end
#pop-options

val lemma_saturated_stable (g : rdf_graph)
  : Lemma (requires closure_chain_saturated g /\ closure_chain_canonical g)
          (ensures forall (n : nat) (t : triple). memP t (closure_iter g n) <==> memP t g)

let lemma_saturated_stable g =
  introduce forall (n : nat) (t : triple). memP t (closure_iter g n) <==> memP t g
  with lemma_saturated_stable_at g n t

// ===================================================================
// 8. THE LENGTH TEST'S FAITHFULNESS (item 3a) -- attempted, and
// exactly where it stops.
//
// ATTEMPT 1: hypothesis = `no_dup_keys g` alone (the task's literal
// "no-duplicate-precondition on g"). FAILS at the first step:
// `lemma_step_extensive` needs `no_dup_keys` of the PRE-DEDUP
// accumulator `rdfs_closure_step_pre_dedup g` (section 6), a
// materially different, much larger graph -- `no_dup_keys g` says
// nothing about it. Canonicity of the INPUT does not propagate to
// canonicity of the rule pipeline's own intermediate accumulator.
//
// ATTEMPT 2: strengthen the hypothesis to `no_dup_keys
// (rdfs_closure_step_pre_dedup g)`, which DOES give `g` extensive
// into `rdfs_closure_step g`. The remaining step -- "same LENGTH plus
// subset (memP) forces the superset back into the subset" -- needs:
//
//     no_repeats_p A /\ no_repeats_p B /\ length A = length B /\
//     (forall x. memP x A ==> memP x B)
//     ==> (forall x. memP x B ==> memP x A)
//
// `no_repeats_p` (not `no_dup_keys`) is what LENGTH needs, since
// length counts list POSITIONS and `no_dup_keys` (an existential
// membership condition) does not rule out the same triple occupying
// two different positions. `no_repeats_p g` is a reasonable
// hypothesis to add, but `no_repeats_p (rdfs_closure_step g)` is NOT
// free: `rdfs_closure_step g` is `graph_dedup_sort (...)`, and
// `graph_dedup_sort`'s output has no repeats only because its
// `sortWith` pass places every equal-key pair ADJACENT first -- i.e.
// it needs `FStar.List.Tot.Properties.sortWith_sorted`, which is
// stated for `#a:eqtype`. The decorated type `graph_dedup_sort` sorts
// over is `(string * triple)`; `triple` is declared `noeq`
// (OWL.Semantics.MemLemmas's own banner: "the stdlib's own lemmas ...
// require eqtype; triple is noeq, so we need memP versions"), so the
// pair type is not `eqtype` either and `sortWith_sorted` does not
// apply. Recovering sortedness needs a bespoke "sortWith commutes
// with the key projection" argument -- a nontrivial, separate piece
// of proof engineering, not a corollary of anything above.
//
// STOPPED HERE after two attempts, per the brief's own escape hatch
// (item 4). Delivered instead: the combinatorial lemma with
// `no_repeats_p` of BOTH sides taken as an explicit hypothesis
// (rather than derived), so the length-equality argument is available
// to any caller that can independently supply that one missing fact.
// ===================================================================

#push-options "--z3rlimit 60"
let rec lemma_no_repeats_subset_same_length_eq (a b : list triple)
  : Lemma
    (requires no_repeats_p a /\ no_repeats_p b /\ length a = length b /\
              (forall (x : triple). memP x a ==> memP x b))
    (ensures forall (x : triple). memP x b ==> memP x a)
    (decreases a) =
  match a with
  | [] -> ()
  | hd :: tl ->
    assert (memP hd a);
    assert (memP hd b);
    let (b1, b2) = split_using b hd in
    lemma_split_using b hd;
    let tl2 = List.Tot.tl b2 in
    assert (b2 == hd :: tl2);
    assert (b == append b1 b2);
    no_repeats_p_append_elim b1 b2;
    assert (no_repeats_p b2);
    assert (~(memP hd tl2) /\ no_repeats_p tl2);
    let bprime = append b1 tl2 in
    no_repeats_p_append_intro b1 tl2;
    assert (forall (x : triple). memP x b1 ==> ~(memP x b2));
    assert (no_repeats_p bprime);
    append_length b1 b2;
    append_length b1 tl2;
    assert (length bprime == length tl);
    assert (~(memP hd tl) /\ no_repeats_p tl);
    introduce forall (x : triple). memP x tl ==> memP x bprime
    with introduce memP x tl ==> memP x bprime
    with _ . begin
      assert (memP x a);
      assert (memP x b);
      append_memP b1 b2 x;
      if FStar.StrongExcludedMiddle.strong_excluded_middle (x == hd) then ()
      else append_memP b1 tl2 x
    end;
    lemma_no_repeats_subset_same_length_eq tl bprime;
    introduce forall (x : triple). memP x b ==> memP x a
    with introduce memP x b ==> memP x a
    with _ . begin
      append_memP b1 b2 x;
      if FStar.StrongExcludedMiddle.strong_excluded_middle (x == hd) then ()
      else append_memP b1 tl2 x
    end
#pop-options

val lemma_len_eq_saturated (g : rdf_graph)
  : Lemma
    (requires no_dup_keys (rdfs_closure_step_pre_dedup g) /\
              no_repeats_p g /\ no_repeats_p (rdfs_closure_step g) /\
              graph_len (rdfs_closure_step g) = graph_len g)
    (ensures step_saturated g)

#push-options "--z3rlimit 60"
let lemma_len_eq_saturated g =
  introduce forall (t : triple). memP t g ==> memP t (rdfs_closure_step g)
  with introduce memP t g ==> memP t (rdfs_closure_step g)
  with _ . lemma_step_extensive g;
  lemma_no_repeats_subset_same_length_eq g (rdfs_closure_step g)
#pop-options

// ===================================================================
// 9. #348 STAGE 3 -- discharging section 8's two gaps.
//
// GAP B: `no_repeats_p (rdfs_closure_step g)`, UNCONDITIONALLY -- no
// separator-freeness or any other side condition. `rdfs_closure_step g
// = graph_dedup_sort g12` sorts its decorated `(string * triple)`
// pairs by KEY (`RDF.Graph.cmp_decorated_triple`, `String.compare` on
// `triple_to_key`) via `List.Tot.sortWith`. `RDF.Indexed.Completeness.
// lemma_sortWith_sorted_pairs` already proves an ALL-PAIRS sortedness
// fact for `sortWith` GENERICALLY (no `eqtype` -- exactly the
// `sortWith_sorted` stdlib blocker section 8 names), but for
// `(option string * a)` decorated pairs, the shape RDF.Indexed's index
// buckets use. `graph_dedup_sort` decorates with a BARE `string`, so
// this section replays the SAME two-stage proof (order facts from
// `RDF.Indexed.StringOrder`'s three axioms, then all-pairs sortedness
// for `sortWith`) specialised to bare-string keys -- simpler than the
// `option`-wrapped original since there is no `None` case to carry.
// ===================================================================

let all_ge_dt (pivot : string * triple) (l : list (string * triple)) : prop =
  forall (y : string * triple). memP y l ==> FStar.String.compare (fst pivot) (fst y) <= 0

let rec sorted_pairs_dt (l : list (string * triple)) : prop =
  match l with
  | [] -> True
  | x :: tl -> all_ge_dt x tl /\ sorted_pairs_dt tl

// Non-strict transitivity from the two StringOrder axioms -- the same
// zero-or-strict case split RDF.Indexed.Completeness's own
// `lemma_key_order_cmp_trans_le` uses, replayed on bare strings.
let lemma_str_compare_trans_le (k1 k2 k3 : string)
  : Lemma (requires FStar.String.compare k1 k2 <= 0 /\ FStar.String.compare k2 k3 <= 0)
          (ensures FStar.String.compare k1 k3 <= 0) =
  string_compare_zero_iff_eq k1 k2;
  string_compare_zero_iff_eq k2 k3;
  if FStar.String.compare k1 k2 = 0 then ()
  else if FStar.String.compare k2 k3 = 0 then ()
  else string_compare_trans k1 k2 k3

// Mixed non-strict/strict composition: a<=b, b<c ==> a<c. What Gap B's
// dedup-ascending induction (below) needs at each KEEP step.
let lemma_str_compare_le_lt_trans (a b c : string)
  : Lemma (requires FStar.String.compare a b <= 0 /\ FStar.String.compare b c < 0)
          (ensures FStar.String.compare a c < 0) =
  string_compare_zero_iff_eq a b;
  if FStar.String.compare a b = 0 then ()
  else string_compare_trans a b c

#push-options "--z3rlimit 60"
let rec lemma_sorted_pairs_dt_append (pivot : string * triple) (lo hi : list (string * triple))
  : Lemma
    (requires
       sorted_pairs_dt lo /\ sorted_pairs_dt hi /\
       (forall y. memP y lo ==> FStar.String.compare (fst y) (fst pivot) <= 0) /\
       (forall y. memP y hi ==> FStar.String.compare (fst pivot) (fst y) <= 0))
    (ensures sorted_pairs_dt (List.Tot.append lo (pivot :: hi)))
    (decreases lo) =
  match lo with
  | [] -> ()
  | hd :: tl ->
    lemma_sorted_pairs_dt_append pivot tl hi;
    List.Tot.append_memP_forall tl (pivot :: hi);
    let aux (y : string * triple) : Lemma
      (requires memP y hi)
      (ensures FStar.String.compare (fst hd) (fst y) <= 0) =
      lemma_str_compare_trans_le (fst hd) (fst pivot) (fst y)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 100"
let rec lemma_sortWith_sorted_pairs_dt (l : list (string * triple))
  : Lemma
    (ensures sorted_pairs_dt (List.Tot.sortWith cmp_decorated_triple l))
    (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare cmp_decorated_triple pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare cmp_decorated_triple pivot) tl;
    lemma_sortWith_sorted_pairs_dt lo;
    lemma_sortWith_sorted_pairs_dt hi;
    RDF.Indexed.Completeness.lemma_partition_pred_memP_forall
      (List.Tot.bool_of_compare cmp_decorated_triple pivot) tl;
    lemma_sortWith_memP_forall cmp_decorated_triple lo;
    lemma_sortWith_memP_forall cmp_decorated_triple hi;
    let aux_lo (y : string * triple) : Lemma
      (requires memP y (List.Tot.sortWith cmp_decorated_triple lo))
      (ensures FStar.String.compare (fst y) (fst pivot) <= 0) =
      string_compare_antisym (fst pivot) (fst y)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_lo);
    let aux_hi (y : string * triple) : Lemma
      (requires memP y (List.Tot.sortWith cmp_decorated_triple hi))
      (ensures FStar.String.compare (fst pivot) (fst y) <= 0) = ()
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_hi);
    lemma_sorted_pairs_dt_append pivot (List.Tot.sortWith cmp_decorated_triple lo)
                                       (List.Tot.sortWith cmp_decorated_triple hi)
#pop-options

// ===================================================================
// 9a. `no_repeats_p` is `rev`-invariant -- the small bridge
// `dedup_sorted_decorated_aux`'s trailing `List.Tot.rev acc` needs
// (the aux's own accumulator is built by CONS, reversed only once at
// the very end).
// ===================================================================

#push-options "--z3rlimit 60"
let rec lemma_no_repeats_p_rev (#a:Type) (l : list a)
  : Lemma (ensures no_repeats_p (List.Tot.rev l) <==> no_repeats_p l)
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    lemma_no_repeats_p_rev tl;
    List.Tot.rev_append [hd] tl;
    assert (List.Tot.rev (hd :: tl) == List.Tot.append (List.Tot.rev tl) (List.Tot.rev [hd]));
    assert (List.Tot.rev [hd] == [hd]);
    List.Tot.rev_memP tl hd;
    no_repeats_p_append (List.Tot.rev tl) [hd]
#pop-options

// ===================================================================
// 9b. The dedup-ascending induction: given the incoming decorated list
// is ALL-PAIRS sorted by key and the accumulator invariant holds (its
// elements' keys are all <= the tracked `prev` key, with a witness for
// `prev` itself, mirroring section 5's OWN `lemma_dedup_sorted_
// decorated_extensive` invariant shape), the output has no repeats.
//
// At each KEEP step (fresh key `k`), the entering pair's own
// all-pairs-sortedness fact (`sorted_pairs_dt`'s head clause) gives
// "every later key is >= k", carrying the `ts`-side invariant forward;
// the OLD `prev`'s "<=" bound composed with `prev < k` (mixed le/lt
// transitivity, since `prev <> k` in the KEEP branch by definition of
// `dup`) gives every OLD acc element STRICTLY less than `k`, hence
// (same triple ==> same key, contrapositive) distinct from the new
// element `t` -- `no_repeats_p_cons` closes the extended accumulator.
// ===================================================================

let dedup_acc_inv (prev : option string) (acc : list triple) : prop =
  no_repeats_p acc /\
  (match prev with
   | Some k -> (exists (u : triple). memP u acc /\ triple_to_key u == k) /\
               (forall (t : triple). memP t acc ==> FStar.String.compare (triple_to_key t) k <= 0)
   | None -> acc == [])

#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let rec lemma_dedup_sorted_decorated_no_repeats
    (prev : option string) (ts : list (string * triple)) (acc : list triple)
  : Lemma
    (requires
      decoration_consistent ts /\
      sorted_pairs_dt ts /\
      dedup_acc_inv prev acc /\
      (match prev with
       | Some k -> forall (p : (string * triple)). memP p ts ==> FStar.String.compare k (fst p) <= 0
       | None -> True))
    (ensures no_repeats_p (dedup_sorted_decorated_aux prev ts acc))
    (decreases ts) =
  match ts with
  | [] -> lemma_no_repeats_p_rev acc
  | (k, t) :: rest ->
    let dup = match prev with | Some p -> p = k | None -> false in
    if dup then begin
      // Same key as `prev` -- drop `t`, recurse unchanged on `rest`.
      // `rest`'s own all-pairs bound against `prev` (= k here) comes
      // straight from `sorted_pairs_dt ts`'s head clause.
      (match prev with
       | Some p ->
         introduce forall (p' : (string * triple)). memP p' rest ==> FStar.String.compare p (fst p') <= 0
         with introduce memP p' rest ==> FStar.String.compare p (fst p') <= 0
         with _ . ()
       | None -> ());
      lemma_dedup_sorted_decorated_no_repeats prev rest acc
    end else begin
      // Fresh key -- keep `t`, recurse with `Some k` and `t :: acc`.
      introduce forall (p' : (string * triple)). memP p' rest ==> FStar.String.compare k (fst p') <= 0
      with introduce memP p' rest ==> FStar.String.compare k (fst p') <= 0
      with _ . ();
      assert (triple_to_key t == k);
      // Every OLD acc element's key is STRICTLY below k -- vacuously
      // (acc == []) when prev is None, or via "<= p, p < k" mixed
      // transitivity (p <> k since dup is false) when prev is Some p.
      let old_below_k : squash (forall (u : triple). memP u acc ==>
                                   FStar.String.compare (triple_to_key u) k < 0) =
        match prev with
        | Some p ->
          string_compare_zero_iff_eq p k;
          assert (FStar.String.compare p k < 0);
          introduce forall (u : triple). memP u acc ==>
              FStar.String.compare (triple_to_key u) k < 0
          with introduce memP u acc ==> FStar.String.compare (triple_to_key u) k < 0
          with _ . lemma_str_compare_le_lt_trans (triple_to_key u) p k
        | None -> assert (acc == []) in
      introduce memP t acc ==> False
      with _ . begin
        assert (FStar.String.compare (triple_to_key t) k < 0);
        string_compare_zero_iff_eq k k
      end;
      no_repeats_p_cons t acc;
      introduce forall (t' : triple). memP t' (t :: acc) ==>
          FStar.String.compare (triple_to_key t') k <= 0
      with introduce memP t' (t :: acc) ==> FStar.String.compare (triple_to_key t') k <= 0
      with _ . begin
        eliminate t' == t \/ memP t' acc
        returns FStar.String.compare (triple_to_key t') k <= 0
        with _ . string_compare_zero_iff_eq k k
        and  _ . assert (FStar.String.compare (triple_to_key t') k < 0)
      end;
      assert (exists (u : triple). memP u (t :: acc) /\ triple_to_key u == k);
      lemma_dedup_sorted_decorated_no_repeats (Some k) rest (t :: acc)
    end
#pop-options

// ===================================================================
// 9c. Gap B, closed: `no_repeats_p (graph_dedup_sort h)` for ANY `h`
// -- no side condition. Same decorate/sort setup section 5's
// `lemma_graph_dedup_sort_extensive` already uses, composed with 9a/9b.
// ===================================================================

#push-options "--z3rlimit 100"
val lemma_graph_dedup_sort_no_repeats (h : list triple)
  : Lemma (no_repeats_p (graph_dedup_sort h))

let lemma_graph_dedup_sort_no_repeats h =
  let f = fun (t : triple) -> (triple_to_key t, t) in
  let dec : list (string * triple) = List.Tot.map f h in
  let sorted : list (string * triple) = List.Tot.sortWith cmp_decorated_triple dec in
  lemma_sortWith_sorted_pairs_dt dec;
  introduce forall (p : (string * triple)). memP p dec ==> fst p == triple_to_key (snd p)
  with introduce memP p dec ==> fst p == triple_to_key (snd p)
  with _ . begin
    memP_map_elim f p h;
    eliminate exists (t : triple). memP t h /\ f t == p
    returns fst p == triple_to_key (snd p)
    with _ . ()
  end;
  introduce forall (p : (string * triple)). memP p sorted ==> fst p == triple_to_key (snd p)
  with introduce memP p sorted ==> fst p == triple_to_key (snd p)
  with _ . lemma_sortWith_memP_iff cmp_decorated_triple dec p;
  assert (decoration_consistent sorted);
  assert (dedup_acc_inv None ([] <: list triple));
  lemma_dedup_sorted_decorated_no_repeats None sorted [];
  assert (graph_dedup_sort h == dedup_sorted_decorated_aux None sorted [])
#pop-options

val lemma_rdfs_closure_step_no_repeats (g : rdf_graph)
  : Lemma (no_repeats_p (rdfs_closure_step g))

let lemma_rdfs_closure_step_no_repeats g =
  lemma_graph_dedup_sort_no_repeats (rdfs_closure_step_pre_dedup g);
  lemma_step_is_dedup_of_pre_dedup g

// ===================================================================
// 9d. Gap B folded into the length-test theorem: `lemma_len_eq_
// saturated`'s `no_repeats_p (rdfs_closure_step g)` hypothesis is now
// DISCHARGED (9c), not merely assumed, so this corollary drops it --
// down to THREE hypotheses where section 8 needed four. `no_dup_keys
// (rdfs_closure_step_pre_dedup g)` (Gap A) and `no_repeats_p g` (the
// INPUT graph's own list has no literal duplicate triples -- a
// reasonable ask of a freshly-parsed graph, unlike the OUTPUT-side
// hypothesis this corollary just eliminated) remain.
// ===================================================================

val lemma_len_eq_saturated_gapB (g : rdf_graph)
  : Lemma
    (requires no_dup_keys (rdfs_closure_step_pre_dedup g) /\
              no_repeats_p g /\
              graph_len (rdfs_closure_step g) = graph_len g)
    (ensures step_saturated g)

let lemma_len_eq_saturated_gapB g =
  lemma_rdfs_closure_step_no_repeats g;
  lemma_len_eq_saturated g
