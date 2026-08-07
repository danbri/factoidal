module RDFS.Closure.SemiNaive

// ===================================================================
// SEMI-NAIVE (DELTA) EVALUATION for the RDFS closure — Phase 1 of
// docs/designissues/2026-07-31-rdfs-performance-scalability.md.
//
// WHAT IS WRONG WITH THE NAIVE LOOP. `RDFS.Closure.rdfs_closure`
// re-applies all twelve rows to the WHOLE graph on every round. A
// triple derived in round 1 is re-derived, re-emitted and re-sorted in
// rounds 2, 3, ... r. The answer is produced r times and thrown away
// r-1 times.
//
// Semi-naive evaluation (Bancilhon and Ramakrishnan 1986) applies the
// rules only where at least one premise is NEW. For a two-premise rule
// with body B1 and B2, the round-k+1 work is
//
//     delta_out  =  (delta_B1 join B2_full)  union  (B1_full join delta_B2)
//
// Both terms are needed. Dropping either loses derivations. The cross
// term delta_B1 join delta_B2 is covered twice over, harmlessly, since
// the full graph contains the delta.
//
// -------------------------------------------------------------------
// WHY THIS IS SAFE EVEN IF THE DELTA REASONING BELOW IS WRONG
// -------------------------------------------------------------------
// Every row here applies the SAME rule bodies as RDFS.Closure, to a
// SUBSET of the inputs. So this module can only ever derive triples the
// naive loop also derives: it is sound by construction, and the only
// way it can be wrong is by deriving too FEW.
//
// That is exactly what `rdfs_closure_semi_naive_checked` tests. It runs
// the delta loop, then applies ONE full naive `rdfs_closure_step` to
// the result:
//
//   * if that step adds nothing, the result is a fixed point of the
//     naive step containing the input graph. The naive closure is the
//     LEAST such fixed point, so it is contained in ours; and ours is
//     contained in it by soundness. The two are therefore EQUAL, and
//     the fast answer is returned.
//   * if that step adds something, the delta loop missed a derivation.
//     The result is discarded and the untouched `rdfs_closure` runs.
//
// A hole in the reasoning below costs SPEED, never correctness. This is
// the same discipline as RDFS.SchemaSplit's post-hoc check, and for the
// same reason: confident reasoning about this rule set has been wrong
// repeatedly (issue #340 item 4 proposed hoisting five rows out of the
// loop; all five turned out to be recursive).
//
// ZERO DIFF to RDFS.Closure.fsti. The naive loop stays the reference
// implementation and the fallback.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDF.Vocabulary
open RDFS.Closure

(** ======================================================================== *)
(** Sorted set difference                                                    *)
(** ======================================================================== *)

// `graph_dedup_sort` leaves a graph sorted by `triple_cmp` with no
// duplicate keys, so the delta between two rounds is one linear merge
// rather than a membership scan per triple. Both arguments MUST come
// from `graph_dedup_sort`; on unsorted input this returns a subset of
// the true difference, which the post-hoc check would then catch.
// `sorted_diff` now lives in RDF.Graph.fsti next to `graph_dedup_sort`,
// whose output shape it requires, so `add_triples_if_new_bulk` can use
// it too. It arrived here first, and it arrived non-tail-recursive:
// written as `n :: sorted_diff ns older` it verified cleanly, passed
// every W3C suite and every synthetic benchmark shape, and then died
// with `Fatal error: exception Stack overflow` on QUDT's 508,139-triple
// closure. F* proves termination, not stack depth. See trap 5 in
// skills/fstar-module-style.

(** ======================================================================== *)
(** Form A — rows whose index argument is NOT a premise                      *)
(** ======================================================================== *)

// rdfs4a, rdfs4b, rdfs8 and rdfs13 read `ig` only through `emit_once`,
// which consults it to skip a conclusion the snapshot already carries.
// The index is a duplicate filter, not a premise. So restricting the
// DRIVER to the delta is exactly complete for these rows: a conclusion
// can only be licensed by a premise triple, and every premise triple is
// either old (its conclusion was drawn in an earlier round) or in the
// delta.
//
// The index passed here is the FULL one on purpose. A delta-only index
// would fail to suppress duplicates the accumulator already holds --
// costing emissions, not correctness.

let sn_rdfs4a (acc : rdf_graph) (ig : indexed_graph) (delta : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left (rdfs4a_step ig) acc delta

let sn_rdfs4b (acc : rdf_graph) (ig : indexed_graph) (delta : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left (rdfs4b_step ig) acc delta

let sn_rdfs8 (acc : rdf_graph) (ig : indexed_graph) (delta : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left (rdfs8_step ig) acc delta

let sn_rdfs13 (acc : rdf_graph) (ig : indexed_graph) (delta : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left (rdfs13_step ig) acc delta

(** ======================================================================== *)
(** Form B — rows with no data premise at all                                *)
(** ======================================================================== *)

// rdfs1 folds over `recognized_datatypes` and the container-membership
// row folds over `container_membership_properties`. Both are FIXED
// lists: the conclusions do not depend on the graph, so after the first
// round they can never produce anything new. They run in round 1 only.
//
// This is a hoist, and hoists in this rule set have been unsound before
// (#340 item 4). It is safe HERE only because the premise list is a
// constant -- neither row reads the graph, so no later round can change
// what they emit. The five rows that hoist proposal targeted all read
// the graph; these two do not.

let sn_axiom_rows (acc : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let a1 = rdfs_rule_recognized_datatypes acc ig in
  rdfs_rule_container_membership a1 ig

(** ======================================================================== *)
(** Form C — graph-driven rows with the index as second premise              *)
(** ======================================================================== *)

// rdfs9, rdfs11 and rdfs5 walk the graph for premise 1 and probe the
// index for premise 2. Both premises are live, so both delta terms are
// needed. Each row below takes the driver and the probe index
// SEPARATELY, so the caller can instantiate it twice:
//
//     row acc ig_full  delta      -- new premise 1, all premise 2
//     row acc ig_delta full       -- all premise 1, new premise 2
//
// The bodies are the bodies of `rdfs_rule_subClassOf`,
// `rdfs_rule_subClassOf_trans` and `rdfs_rule_subPropertyOf_trans` in
// RDFS.Closure.fsti with the accumulator and the driver split apart.
// They must stay in step with those; the post-hoc check is what
// notices if they drift.

// rdfs9: a rdf:type A, A rdfs:subClassOf B |- a rdf:type B
let sn_rdfs9 (acc : rdf_graph) (ig_probe : indexed_graph) (driver : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left
    (fun (acc1 : rdf_graph) (t : triple) ->
      if t.p = rdf_type then
        match t.o with
        | T_IRI class_iri ->
          let super_classes =
            find_objects_indexed ig_probe (S_IRI class_iri) rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (b_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdf_type; o = b_term } in
              add_triple_unchecked acc2 new_t)
            acc1
            super_classes
        | _ -> acc1
      else acc1)
    acc
    driver

// rdfs11: A rdfs:subClassOf B, B rdfs:subClassOf C |- A rdfs:subClassOf C
let sn_rdfs11 (acc : rdf_graph) (ig_probe : indexed_graph) (driver : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left
    (fun (acc1 : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        match term_to_subject t.o with
        | Some b_subj ->
          let supers = find_objects_indexed ig_probe b_subj rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
              let new_t : triple =
                { s = t.s; p = rdfs_subClassOf; o = c_term } in
              add_triple_unchecked acc2 new_t)
            acc1
            supers
        | None -> acc1
      else acc1)
    acc
    driver

// rdfs5: P rdfs:subPropertyOf Q, Q rdfs:subPropertyOf R
//        |- P rdfs:subPropertyOf R
let sn_rdfs5 (acc : rdf_graph) (ig_probe : indexed_graph) (driver : rdf_graph)
  : rdf_graph =
  List.Tot.fold_left
    (fun (acc1 : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match term_to_subject t.o with
        | Some q_subj ->
          let supers =
            find_objects_indexed ig_probe q_subj rdfs_subPropertyOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
              let new_t : triple =
                { s = t.s; p = rdfs_subPropertyOf; o = r_term } in
              add_triple_unchecked acc2 new_t)
            acc1
            supers
        | None -> acc1
      else acc1)
    acc
    driver

(** ======================================================================== *)
(** Form D — rows driven from the index on BOTH sides                        *)
(** ======================================================================== *)

// rdfs7, rdfs2 and rdfs3 look up the DECLARATIONS in one bucket and the
// matching data triples in another. Both lookups are premises, so each
// row takes two index arguments and the caller instantiates it twice:
//
//     row acc ig_delta ig_full    -- new declaration, all data
//     row acc ig_full  ig_delta   -- all declarations, new data
//
// Bodies mirror `rdfs_rule_subPropertyOf`, `rdfs_rule_domain` and
// `rdfs_rule_range` with the single `ig` split into `ig_decls` and
// `ig_data`.

// rdfs7: a P b, P rdfs:subPropertyOf Q |- a Q b
let sn_rdfs7 (acc : rdf_graph)
             (ig_decls : indexed_graph) (ig_data : indexed_graph)
  : rdf_graph =
  let decls = bucket_lookup ig_decls.ig_pred rdfs_subPropertyOf in
  List.Tot.fold_left
    (fun (acc1 : rdf_graph) (decl : triple) ->
      match decl.s, decl.o with
      | S_IRI p, T_IRI q ->
        let matching = bucket_lookup ig_data.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            let new_t : triple = { s = t.s; p = q; o = t.o } in
            add_triple_unchecked acc2 new_t)
          acc1
          matching
      | _, _ -> acc1)
    acc
    decls

// rdfs2: a P b, P rdfs:domain C |- a rdf:type C
let sn_rdfs2 (acc : rdf_graph)
             (ig_decls : indexed_graph) (ig_data : indexed_graph)
  : rdf_graph =
  let decls = bucket_lookup ig_decls.ig_pred rdfs_domain in
  List.Tot.fold_left
    (fun (acc1 : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig_data.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            let new_t : triple = { s = t.s; p = rdf_type; o = decl.o } in
            add_triple_unchecked acc2 new_t)
          acc1
          matching
      | _ -> acc1)
    acc
    decls

// rdfs3: a P b, P rdfs:range C |- b rdf:type C
let sn_rdfs3 (acc : rdf_graph)
             (ig_decls : indexed_graph) (ig_data : indexed_graph)
  : rdf_graph =
  let decls = bucket_lookup ig_decls.ig_pred rdfs_range in
  List.Tot.fold_left
    (fun (acc1 : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig_data.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            match term_to_subject t.o with
            | Some b_subj ->
              let new_t : triple =
                { s = b_subj; p = rdf_type; o = decl.o } in
              add_triple_unchecked acc2 new_t
            | None -> acc2)
          acc1
          matching
      | _ -> acc1)
    acc
    decls

(** ======================================================================== *)
(** One delta round                                                          *)
(** ======================================================================== *)

// `full` is the whole graph so far, `delta` the triples the previous
// round added. Returns the accumulated graph, deduped and sorted so the
// next round's `sorted_diff` is linear.
//
// Rule ORDER matches RDFS.Closure.rdfs_closure_step. It does not have to
// -- a fixed point is order-independent -- but keeping it identical
// makes the two loops comparable when a difference has to be chased.
let semi_naive_round (full : rdf_graph) (delta : rdf_graph)
                     (ig_full : indexed_graph) (ig_delta : indexed_graph)
  : rdf_graph =
  // Form D rows, both join terms each.
  let a1  = sn_rdfs7 full  ig_delta ig_full in
  let a2  = sn_rdfs7 a1    ig_full  ig_delta in
  let a3  = sn_rdfs2 a2    ig_delta ig_full in
  let a4  = sn_rdfs2 a3    ig_full  ig_delta in
  let a5  = sn_rdfs3 a4    ig_delta ig_full in
  let a6  = sn_rdfs3 a5    ig_full  ig_delta in
  // Form C rows, both join terms each.
  let a7  = sn_rdfs9  a6   ig_full  delta in
  let a8  = sn_rdfs9  a7   ig_delta full in
  let a9  = sn_rdfs11 a8   ig_full  delta in
  let a10 = sn_rdfs11 a9   ig_delta full in
  let a11 = sn_rdfs5  a10  ig_full  delta in
  let a12 = sn_rdfs5  a11  ig_delta full in
  // Form A rows: driver restricted to the delta, full index for
  // duplicate suppression.
  let a13 = sn_rdfs8  a12 ig_full delta in
  let a14 = sn_rdfs13 a13 ig_full delta in
  let a15 = sn_rdfs4a a14 ig_full delta in
  let a16 = sn_rdfs4b a15 ig_full delta in
  graph_dedup_sort a16

(** ======================================================================== *)
(** The delta loop                                                           *)
(** ======================================================================== *)

// Round 1 is a full naive step: everything is new, so there is no delta
// to exploit and the axiom rows (form B) fire here. Later rounds are
// delta-driven.
//
// Like `rdfs_closure`, this returns its input unchanged when fuel runs
// out. That silent cap is the naive loop's behaviour too (see
// skills/measuring-inference rule 8) and this module deliberately does
// not change it: the checked wrapper below is what a caller should use,
// and a fuel-exhausted result fails its check and falls back.
// `--z3rlimit 30` for the same reason `RDFS.Closure.rdfs_closure`
// carries it: the loop body drags sixteen large rule terms into the
// SMT context and the termination obligation goes borderline. A
// resource-budget bump, not a logic change. No --admit_smt_queries, no
// --lax (iron rule #10).
#push-options "--z3rlimit 30"
let rec semi_naive_loop (full : rdf_graph) (delta : rdf_graph) (fuel : nat)
  : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> full
  | n ->
    if Nil? delta then full
    else begin
      let ig_full  = build_indexed full in
      let ig_delta = build_indexed delta in
      let next = semi_naive_round full delta ig_full ig_delta in
      if graph_len next = graph_len full
      then full
      else semi_naive_loop next (sorted_diff next full) (n - 1)
    end
#pop-options

let rdfs_closure_semi_naive (g : rdf_graph) (fuel : nat) : rdf_graph =
  match fuel with
  | 0 -> g
  | n ->
    // Round 1 has been spent, so the loop gets n-1. Written with the
    // guard rather than as `n - 1` so the nat-ness is syntactic: F*
    // does not carry `n <> 0` out of this match far enough to type the
    // subtraction on its own here.
    let remaining : nat = if n > 0 then n - 1 else 0 in
    // Round 1: the full naive step, plus the two constant-premise rows.
    let ig0 = build_indexed g in
    let seeded = graph_dedup_sort (sn_axiom_rows g ig0) in
    let first = rdfs_closure_step seeded in
    if graph_len first = graph_len seeded
    then first
    else semi_naive_loop first (sorted_diff first seeded) remaining

(** ======================================================================== *)
(** The checked entry point                                                  *)
(** ======================================================================== *)

// Run the delta loop, then apply ONE full naive step to the answer.
//
// If that step adds nothing, the answer is a fixed point of the naive
// step that contains `g`. The naive closure is the least such fixed
// point, so naive is contained in ours; and every triple this module
// emits comes from a rule body copied from RDFS.Closure applied to a
// subset of the inputs, so ours is contained in naive. Equal.
//
// If the step DOES add something, the delta loop was incomplete on this
// graph. Throw the answer away and run the untouched naive closure. The
// cost of a hole in the reasoning is one wasted fast pass.
//
// The check is one extra round out of the r the loop already ran, and
// it is the reason this module needs no refinement proof to be trusted.
let rdfs_closure_checked (g : rdf_graph) (fuel : nat) : rdf_graph =
  let fast = rdfs_closure_semi_naive g fuel in
  let probe = rdfs_closure_step fast in
  if graph_len probe = graph_len fast
  then fast
  else rdfs_closure g fuel

// Mirror of `RDFS.Closure.rdfs_closure_with_reflexivity` with the two
// `rdfs_closure` calls replaced by the checked delta loop. The
// reflexivity-axiom harvesting between them is unchanged and still
// comes from RDFS.Closure -- this module adds no semantics, only an
// evaluation strategy.
//
// The second closure call is what makes the reflexivity axioms
// productive, and it starts from an already-closed graph, so its delta
// is exactly `refl_axioms`. That is the case semi-naive evaluation is
// best at: the naive loop re-derives the whole closure to absorb a
// handful of new edges.
let rdfs_closure_with_reflexivity_checked (g : rdf_graph) (fuel : nat)
  : Tot rdf_graph =
  let closed = rdfs_closure_checked g fuel in
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = add_triples_if_new_bulk closed refl_axioms in
  rdfs_closure_checked with_refl fuel
