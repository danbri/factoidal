module RDF.Store.Columnar.DeltaMerge

(* Durable-UPDATE stage 3 (merge-on-read) of
   docs/designissues/2026-07-06-durable-update-design.md §3.2, and the
   D-overlay of docs/designissues/2026-07-06-unified-store-architecture.md
   §3.3. Stages 1-2 (RDF.Store.Columnar.DeltaLog.fst) gave the durable
   BYTE format + the fsync/rename I/O boundary; this module is the pure
   F* layer in between: fold a replayed log into a resolved per-graph
   diff, and compose that diff with a base read result at query time.

   Everything below is `Tot` — no I/O, no `assume val`. The five ML
   assume vals stay in RDF.Store.Columnar.DeltaLog.fst; this module only
   consumes their PARSED output (`list DL.delta_batch`).

   -----------------------------------------------------------------
   Deviation from the design doc's §3.2 sketch, disclosed:

   The sketch's `fold_delta_batches : list delta_batch -> Tot
   delta_resolved` and `overlay : store_caps -> delta_resolved -> Tot
   store_caps` (unified-store-architecture.md §3.3) only typecheck
   together if `delta_resolved` is ALREADY a single graph's resolved
   diff — `overlay` takes exactly one `store_caps` (one graph's read
   seam, per RDF.Store.Capabilities.Cottas's own per-graph-scoped
   builder) and exactly one `delta_resolved`, with no graph-key
   argument of its own. This module therefore makes `delta_resolved`
   per-graph (`dr_cleared`/`dr_added`/`dr_removed` for ONE graph key)
   and moves the "which graph" question into `fold_delta_batches`,
   which now takes an explicit `graph_key : option T.iri` (`None` =
   default graph, matching DL.delta_entry's own convention) alongside
   the batch list. The wiring layer (SPARQL11.Store.fst's
   `cottas_with_delta_dataset_backend`) calls `fold_delta_batches`
   once per graph the delta log or the base store carries, exactly
   mirroring how `RDF.Store.Capabilities.dataset_caps` and
   `SPARQL11.Store.dataset_caps_of_backend` already resolve one
   `store_caps` per graph rather than a single quad-shaped one
   (RDF.Store.Capabilities.fst's own U1.5 banner names this same
   "still triple-shaped, not quad-native" residual).

   Second disclosed extension: DE_Clear/DE_Drop are graph-WIPE
   operations, not simple add/remove — a CLEAR after some ADDs must
   make the base's own rows invisible too, not just cancel the
   ADDs recorded since the last clear. `delta_resolved` therefore
   carries `dr_cleared : bool` (design doc's sketch had no such field;
   its `merge_on_read` only ever subtracts a tombstone set from base
   results). `dr_cleared = true` means "ignore the base entirely for
   this graph, from this delta's replay onward" — the WAL's own
   "on replay, a batch below the compacted epoch is a no-op" argument
   (design doc §3.3 step 5) applies unchanged: once compaction folds a
   CLEAR into a fresh base file, this module sees a shorter delta log
   again. DE_Create is a no-op for THIS module's triple-level merge —
   it's existence bookkeeping (a named graph existing-but-empty), not
   a triple-set operation; the wiring layer uses
   `delta_batches_named_graphs` below to discover CREATE-only graphs
   that have no base rows and no ADD/REMOVE of their own, so a
   `CREATE GRAPH <g>` still makes `<g>` resolvable (queryable, answers
   empty) at the store-construction layer even though this module's
   own fold treats it as inert. *)

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

module DL = RDF.Store.Columnar.DeltaLog
module T = RDF.Term

(* ======================================================================
   1. delta_resolved — one graph's resolved diff over the base.
   ====================================================================== *)

noeq type delta_resolved = {
  dr_cleared : bool;          // a CLEAR/DROP fired for this graph in this log
  dr_added   : list triple;   // net additions since the last clear (a set: graph_add-built)
  dr_removed : list triple;   // net tombstones since the last clear (a set: graph_add-built)
}

let delta_resolved_empty : delta_resolved =
  { dr_cleared = false; dr_added = []; dr_removed = [] }

let delta_resolved_cleared : delta_resolved =
  { dr_cleared = true; dr_added = []; dr_removed = [] }

// A delta this graph has none of — the case `overlay` must reproduce the
// wrapped store's behaviour byte-for-byte (design doc §4.1's "empty delta
// is provably a no-op").
let delta_resolved_is_empty (dr : delta_resolved) : bool =
  (not dr.dr_cleared) &&
  (match dr.dr_added with   | [] -> true | _ -> false) &&
  (match dr.dr_removed with | [] -> true | _ -> false)

(* ======================================================================
   2. Folding delta_entry / delta_batch lists into a delta_resolved,
   for ONE graph key, in commit order (DL.delta_batch's own `db_seq`
   IS list order — a delta log is read/replayed front-to-back).
   ====================================================================== *)

// Does this entry target `graph_key`? Mirrors DL.delta_entry's own
// "None = default graph" convention (DeltaLog.fst §1's banner).
let apply_entry_to_delta (graph_key : option T.iri) (dr : delta_resolved) (e : DL.delta_entry)
  : Tot delta_resolved =
  match e with
  | DL.DE_Add q g ->
    if g = graph_key
    then { dr with dr_removed = graph_remove q dr.dr_removed;
                   dr_added   = graph_add q dr.dr_added }
    else dr
  | DL.DE_Remove q g ->
    if g = graph_key
    then { dr with dr_added   = graph_remove q dr.dr_added;
                   dr_removed = graph_add q dr.dr_removed }
    else dr
  | DL.DE_Clear g ->
    if g = graph_key then delta_resolved_cleared else dr
  | DL.DE_Drop g ->
    if Some g = graph_key then delta_resolved_cleared else dr
  | DL.DE_Create _ ->
    // Existence bookkeeping only (see module banner) — no triple-set effect.
    dr

let rec fold_entries_for_graph (graph_key : option T.iri) (entries : list DL.delta_entry)
  (acc : delta_resolved) : Tot delta_resolved (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest -> fold_entries_for_graph graph_key rest (apply_entry_to_delta graph_key acc e)

// The whole-log fold for one graph. Batches are already in commit order
// (the log is append-only; DL.parse_log returns them front-to-back) —
// concatenating their ops preserves that order exactly.
let fold_delta_batches (batches : list DL.delta_batch) (graph_key : option T.iri)
  : Tot delta_resolved =
  fold_entries_for_graph graph_key
    (List.Tot.concatMap (fun (b : DL.delta_batch) -> b.DL.db_ops) batches)
    delta_resolved_empty

(* ======================================================================
   3. Named-graph discovery — which graph IRIs does this delta log
   mention that a caller building a dataset_caps/dataset_backend needs
   a slot for, beyond whatever the base store already lists? (Wiring
   layer's "graph create+add" case: a CREATE/ADD against a brand-new
   named graph must be resolvable even though the base store has no
   rows for it.)
   ====================================================================== *)

let entry_graph_mentions (e : DL.delta_entry) : list T.iri =
  match e with
  | DL.DE_Add _ g | DL.DE_Remove _ g | DL.DE_Clear g ->
    (match g with None -> [] | Some gi -> [gi])
  | DL.DE_Drop g | DL.DE_Create g -> [g]

let rec dedup_iri_acc (seen : list T.iri) (xs : list T.iri) : Tot (list T.iri) (decreases xs) =
  match xs with
  | [] -> seen
  | x :: rest -> if List.Tot.mem x seen then dedup_iri_acc seen rest else dedup_iri_acc (seen @ [x]) rest

// Every distinct named-graph IRI (default graph excluded — it has no IRI)
// mentioned anywhere in the log, in first-seen order.
let delta_batches_named_graphs (batches : list DL.delta_batch) : Tot (list T.iri) =
  let all_mentions =
    List.Tot.concatMap
      (fun (b : DL.delta_batch) -> List.Tot.concatMap entry_graph_mentions b.DL.db_ops)
      batches
  in
  dedup_iri_acc [] all_mentions

(* ======================================================================
   4. merge_on_read — the read-time composition (design doc §3.2).
   Pure over already-decoded values; does not decide how the base is
   read. `base_results` is whatever the base backend's `sc_solve b`
   already returned (matching the SAME bound `b` this call receives).
   ====================================================================== *)

let filter_tombstoned (base_results : list triple) (dr : delta_resolved) : Tot (list triple) =
  if dr.dr_cleared then []
  else List.Tot.filter (fun t -> not (mem_triple t dr.dr_removed)) base_results

let merge_on_read (base_results : list triple) (dr : delta_resolved) (b : triple_pattern_bound)
  : Tot (list triple) =
  let survivors = filter_tombstoned base_results dr in
  let additions = triple_matches_bound b dr.dr_added in
  survivors @ additions

// Cheap (O(delta), never touches base_results) — the additive term
// `overlay`'s sc_estimate uses so an empty-bound-matching delta costs
// nothing beyond a length-of-dr_added scan.
let delta_matching_count (dr : delta_resolved) (b : triple_pattern_bound) : Tot nat =
  List.Tot.length (triple_matches_bound b dr.dr_added)

// O(base_results-matching-bound) — only ever called by `overlay` when
// the delta is non-empty (see RDF.Store.Capabilities.Delta.fst); an
// empty delta short-circuits before this runs, which is what keeps the
// "empty delta costs nothing" floor exact rather than approximate.
let tombstoned_count (dr : delta_resolved) (base_results : list triple) : Tot nat =
  if dr.dr_cleared then List.Tot.length base_results
  else List.Tot.length (List.Tot.filter (fun t -> mem_triple t dr.dr_removed) base_results)

// Conservative (never a false negative) predicate-presence check: OR
// base's own answer with "does the delta's own addition set carry this
// predicate." A tombstoned-to-zero predicate can still report present
// (a false positive, safe for a planner short-circuit / presence probe,
// same "sound direction only" trade RDF.Store.Capabilities.fst's own
// sc_predicate_present fields already accept for their backends).
let rec delta_added_has_predicate (added : list triple) (pred : wf_iri)
  : Tot bool (decreases added) =
  match added with
  | [] -> false
  | t :: rest -> t.p = pred || delta_added_has_predicate rest pred

(* ======================================================================
   5. Reference model for the correctness bridge (§6 below): applying
   delta entries DIRECTLY to a plain rdf_graph, for one graph key. This
   is what a durable-UPDATE-naive in-memory engine would do if it
   re-applied the SAME entries as literal graph_add/graph_remove/clear
   operations rather than going through a base+delta split at all —
   the ground truth `merge_on_read (fold_delta_batches ...)` must agree
   with.
   ====================================================================== *)

// One entry applied directly to a plain graph — named (rather than
// inlined) so the correctness proof below can state facts about it
// once and have `apply_entries_ref`'s recursion and the step lemma's
// signature refer to the exact same term.
let apply_entry_ref_step (graph_key : option T.iri) (g : rdf_graph) (e : DL.delta_entry) : Tot rdf_graph =
  match e with
  | DL.DE_Add q gr    -> if gr = graph_key then graph_add q g else g
  | DL.DE_Remove q gr -> if gr = graph_key then graph_remove q g else g
  | DL.DE_Clear gr    -> if gr = graph_key then [] else g
  | DL.DE_Drop gr     -> if Some gr = graph_key then [] else g
  | DL.DE_Create _    -> g

let rec apply_entries_ref (graph_key : option T.iri) (g : rdf_graph) (entries : list DL.delta_entry)
  : Tot rdf_graph (decreases entries) =
  match entries with
  | [] -> g
  | e :: rest -> apply_entries_ref graph_key (apply_entry_ref_step graph_key g e) rest

(* ======================================================================
   6. The core merge lemma (design doc §3.2's
   `lemma_merge_on_read_matches_apply_update`, PROVED here for the
   subset of update_ops a delta_entry can express directly — ground
   INSERT DATA / DELETE DATA / CLEAR / DROP on one graph, in sequence.
   Full generality over `update_op`/`apply_update_ops` (which also
   covers DELETE/INSERT WHERE, COPY/MOVE/ADD between graphs, and CLEAR
   ALL/NAMED's multi-graph fan-out) needs an `update_ops_to_delta_
   entries` translator that does not exist yet (it needs ground-quad
   extraction out of a `group_graph_pattern`, graph-target resolution,
   and WHERE-clause evaluation against the composed store — none of
   which is delta-log or merge-on-read logic; it is the "compile a
   committed Update request into a delta_batch" bridge the design doc
   names but defers, and stage 3's own brief scopes to merge-on-read).
   That residual is written up at the end of this section as a
   documented, NOT compiled, lemma statement — the task's own
   escape hatch ("prove if commit-sized, else pin exhaustively in
   tests and state the residual") for the part genuinely outside
   this stage.

   What IS proved below is real and does the boundary-crossing work
   the design doc's own comment on `lemma_merge_on_read_matches_
   apply_update` cares about: `merge_on_read` composed with
   `fold_entries_for_graph` reproduces EXACTLY what re-applying the
   same entries directly to the base graph (`apply_entries_ref`,
   i.e. what an in-memory `apply_update_ops` would do for
   INSERT DATA/DELETE DATA/CLEAR/DROP restricted to one graph) would
   have produced — the semantic bridge between the durable delta path
   and direct in-memory application, for the entry vocabulary
   delta_entry actually has.
   ====================================================================== *)

// -- equivalence-relation lemmas for RDF.Term's custom equality tests.
// Needed because `bound_matches` (below) tests a QUERY triple's
// components against a BOUND value, while `mem_triple`/`triple_eq`
// test two GRAPH triples against each other — bridging the two needs
// subject_eq/rdf_term_eq to behave like genuine equivalence relations
// (symmetric, transitive), not just reflexive. None of this exists
// elsewhere in the tree (grepped) — RDF.Term.fsti only proves
// reflexivity — so it is proved here, as lemmas ABOUT those existing
// functions (no redefinition).

let lemma_subject_eq_symm (a b : subject) : Lemma (subject_eq a b == subject_eq b a) =
  match a, b with
  | S_IRI _, S_IRI _ -> ()
  | S_BNode _, S_BNode _ -> ()
  | _, _ -> ()

let lemma_subject_eq_trans (a b c : subject)
  : Lemma (requires subject_eq a b /\ subject_eq b c) (ensures subject_eq a c) =
  match a, b, c with
  | S_IRI _, S_IRI _, S_IRI _ -> ()
  | S_BNode _, S_BNode _, S_BNode _ -> ()
  | _, _, _ -> ()

let lemma_subject_eq_congruent (s a b : subject)
  : Lemma (requires subject_eq a b) (ensures subject_eq s a == subject_eq s b) =
  lemma_subject_eq_symm a b;
  if subject_eq s a then lemma_subject_eq_trans s a b
  else if subject_eq s b then lemma_subject_eq_trans s b a
  else ()

let lemma_lang_tag_eq_symm (a b : string) : Lemma (lang_tag_eq a b == lang_tag_eq b a) = ()

let lemma_lang_tag_eq_trans (a b c : string)
  : Lemma (requires lang_tag_eq a b /\ lang_tag_eq b c) (ensures lang_tag_eq a c) = ()

let lemma_lang_tag_option_eq_symm (a b : option string)
  : Lemma (lang_tag_option_eq a b == lang_tag_option_eq b a) =
  match a, b with
  | None, None -> ()
  | Some x, Some y -> lemma_lang_tag_eq_symm x y
  | _, _ -> ()

let lemma_lang_tag_option_eq_trans (a b c : option string)
  : Lemma (requires lang_tag_option_eq a b /\ lang_tag_option_eq b c) (ensures lang_tag_option_eq a c) =
  match a, b, c with
  | None, None, None -> ()
  | Some x, Some y, Some z -> lemma_lang_tag_eq_trans x y z
  | _, _, _ -> ()

let lemma_literal_eq_symm (l1 l2 : literal) : Lemma (literal_eq l1 l2 == literal_eq l2 l1) =
  lemma_lang_tag_option_eq_symm l1.lang_tag l2.lang_tag

let lemma_literal_eq_trans (l1 l2 l3 : literal)
  : Lemma (requires literal_eq l1 l2 /\ literal_eq l2 l3) (ensures literal_eq l1 l3) =
  lemma_lang_tag_option_eq_trans l1.lang_tag l2.lang_tag l3.lang_tag

let lemma_rdf_term_eq_symm (a b : rdf_term) : Lemma (rdf_term_eq a b == rdf_term_eq b a) =
  match a, b with
  | T_IRI _, T_IRI _ -> ()
  | T_BNode _, T_BNode _ -> ()
  | T_Literal l1, T_Literal l2 -> lemma_literal_eq_symm l1 l2
  | _, _ -> ()

let lemma_rdf_term_eq_trans (a b c : rdf_term)
  : Lemma (requires rdf_term_eq a b /\ rdf_term_eq b c) (ensures rdf_term_eq a c) =
  match a, b, c with
  | T_IRI _, T_IRI _, T_IRI _ -> ()
  | T_BNode _, T_BNode _, T_BNode _ -> ()
  | T_Literal l1, T_Literal l2, T_Literal l3 -> lemma_literal_eq_trans l1 l2 l3
  | _, _, _ -> ()

let lemma_rdf_term_eq_congruent (o a b : rdf_term)
  : Lemma (requires rdf_term_eq a b) (ensures rdf_term_eq o a == rdf_term_eq o b) =
  lemma_rdf_term_eq_symm a b;
  if rdf_term_eq o a then lemma_rdf_term_eq_trans o a b
  else if rdf_term_eq o b then lemma_rdf_term_eq_trans o b a
  else ()

// The per-element test `triple_matches_bound_acc` (SPARQL11.Algebra.fst)
// applies, spelled out standalone so it can be reasoned about directly.
let bound_matches (b : triple_pattern_bound) (t : triple) : bool =
  (match b.bs with | None -> true | Some s -> subject_eq s t.s) &&
  (match b.bp with | None -> true | Some p -> p = t.p) &&
  (match b.bo with | None -> true | Some o -> rdf_term_eq o t.o)

// `triple_eq hd t` ==> `bound_matches` agrees on `hd` and `t` — the
// bridge fact `lemma_mem_matches_bound_acc` below needs.
let lemma_bound_matches_congruent (b : triple_pattern_bound) (hd t : triple)
  : Lemma (requires triple_eq hd t) (ensures bound_matches b hd == bound_matches b t)
  = (match b.bs with
     | None -> ()
     | Some s -> lemma_subject_eq_congruent s hd.s t.s);
    (match b.bo with
     | None -> ()
     | Some o -> lemma_rdf_term_eq_congruent o hd.o t.o)

// mem_triple through triple_matches_bound_acc's own accumulator shape,
// generalised over an arbitrary starting accumulator (what the induction
// in `triple_matches_bound`'s definition needs).
let rec lemma_mem_matches_bound_acc (b : triple_pattern_bound) (ts : list triple) (acc : list triple) (t : triple)
  : Lemma
      (ensures mem_triple t (triple_matches_bound_acc b ts acc) ==
               ((mem_triple t ts && bound_matches b t) || mem_triple t acc))
      (decreases ts)
  = match ts with
    | [] -> ()
    | hd :: tl ->
      let subj_ok = match b.bs with | None -> true | Some s -> subject_eq s hd.s in
      let pred_ok = match b.bp with | None -> true | Some p -> p = hd.p in
      let obj_ok = match b.bo with | None -> true | Some o -> rdf_term_eq o hd.o in
      if subj_ok && pred_ok && obj_ok
      then begin
        lemma_mem_matches_bound_acc b tl (hd :: acc) t;
        if triple_eq hd t then lemma_bound_matches_congruent b hd t
      end
      else lemma_mem_matches_bound_acc b tl acc t

// `triple_matches_bound` finishes with `List.Tot.rev` (SPARQL11.Algebra.fst
// :193-195) — mem_triple doesn't care about order, so this bridges
// `lemma_mem_matches_bound_acc`'s fact about the pre-reverse accumulator
// to the actual `triple_matches_bound` result.
let rec lemma_mem_triple_rev_acc (t : triple) (l acc : list triple)
  : Lemma (ensures mem_triple t (List.Tot.rev_acc l acc) == (mem_triple t l || mem_triple t acc))
          (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl -> lemma_mem_triple_rev_acc t tl (hd :: acc)

let lemma_mem_triple_rev (t : triple) (l : list triple)
  : Lemma (mem_triple t (List.Tot.rev l) == mem_triple t l)
  = lemma_mem_triple_rev_acc t l []

// The clean, acc-free membership characterisation `merge_on_read`'s
// correctness proof consumes.
let lemma_mem_triple_matches_bound (b : triple_pattern_bound) (l : list triple) (t : triple)
  : Lemma (mem_triple t (triple_matches_bound b l) == (mem_triple t l && bound_matches b t))
  = lemma_mem_matches_bound_acc b l [] t;
    lemma_mem_triple_rev t (triple_matches_bound_acc b l [])

let rec lemma_mem_triple_append (t : triple) (l1 l2 : list triple)
  : Lemma (ensures mem_triple t (l1 @ l2) == (mem_triple t l1 || mem_triple t l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | hd :: tl -> lemma_mem_triple_append t tl l2

// `triple_eq a b` ==> `triple_eq s a == triple_eq s b` for any third
// triple `s` — the same congruence property one level up from
// subject_eq/rdf_term_eq, needed by `mem_triple`'s own congruence below.
let lemma_triple_eq_congruent (s a b : triple)
  : Lemma (requires triple_eq a b) (ensures triple_eq s a == triple_eq s b)
  = lemma_subject_eq_congruent s.s a.s b.s;
    lemma_rdf_term_eq_congruent s.o a.o b.o

// `triple_eq hd t` ==> membership in any list agrees for `hd` and `t` —
// mem_triple only ever compares via triple_eq, so this is exactly
// `lemma_triple_eq_congruent` threaded down the list.
let rec lemma_mem_triple_congruent (hd t : triple) (l : list triple)
  : Lemma (requires triple_eq hd t) (ensures mem_triple hd l == mem_triple t l) (decreases l)
  = match l with
    | [] -> ()
    | e :: rest ->
      lemma_mem_triple_congruent hd t rest;
      lemma_triple_eq_congruent e hd t

// The tombstone filter's membership characterisation: `filter_tombstoned`
// (when not cleared) is `List.Tot.filter (fun x -> not (mem_triple x
// removed))`; this is that filter's mem-preservation fact, needing the
// congruence lemma above wherever the filtered-out/kept element happens
// to equal the query triple `t`.
let rec lemma_mem_triple_filter_tombstone (removed : list triple) (l : list triple) (t : triple)
  : Lemma
      (ensures mem_triple t (List.Tot.filter (fun x -> not (mem_triple x removed)) l) ==
               (mem_triple t l && not (mem_triple t removed)))
      (decreases l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      lemma_mem_triple_filter_tombstone removed tl t;
      if triple_eq hd t then lemma_mem_triple_congruent hd t removed

// `filter_tombstoned`'s own membership characterisation, stated directly
// (rather than leaning on Z3 to unfold `filter_tombstoned`'s if/else
// inline inside a larger proof) — a top-level Lemma whose stated type
// already has `filter_tombstoned base_results dr` on one side, so
// F*'s own elaboration (not just Z3 E-matching) lines the two up.
let lemma_mem_filter_tombstoned (base_results : list triple) (dr : delta_resolved) (t : triple)
  : Lemma (
      mem_triple t (filter_tombstoned base_results dr) ==
      (if dr.dr_cleared then false
       else mem_triple t base_results && not (mem_triple t dr.dr_removed)))
  = if dr.dr_cleared then ()
    else lemma_mem_triple_filter_tombstone dr.dr_removed base_results t

let lemma_triple_eq_symm (a b : triple) : Lemma (triple_eq a b == triple_eq b a)
  = lemma_subject_eq_symm a.s b.s;
    lemma_rdf_term_eq_symm a.o b.o

// `mem_triple t (graph_add q g) == (triple_eq t q || mem_triple t g)` —
// graph_add's own membership characterisation (RDF.Graph.fsti:77).
let lemma_mem_graph_add (q : triple) (g : rdf_graph) (t : triple)
  : Lemma (mem_triple t (graph_add q g) == (triple_eq t q || mem_triple t g))
  = if mem_triple q g then begin
      if triple_eq t q then begin
        lemma_triple_eq_symm t q;
        lemma_mem_triple_congruent q t g
      end
    end else begin
      lemma_mem_triple_append t g [q];
      lemma_triple_eq_symm q t
    end

// `mem_triple t (graph_remove q g) == (mem_triple t g && not (triple_eq t q))`
// — graph_remove's own membership characterisation (RDF.Graph.Executable.fst:162).
let rec lemma_mem_graph_remove (q : triple) (g : rdf_graph) (t : triple)
  : Lemma (ensures mem_triple t (graph_remove q g) == (mem_triple t g && not (triple_eq t q)))
          (decreases g)
  = match g with
    | [] -> ()
    | hd :: tl ->
      lemma_mem_graph_remove q tl t;
      if triple_eq hd t then begin
        lemma_triple_eq_congruent q hd t;
        lemma_triple_eq_symm q hd;
        lemma_triple_eq_symm q t
      end

// The unbounded (no `triple_pattern_bound` yet) state invariant: after
// applying the SAME entries to a reference graph and to a
// (base, delta_resolved) pair starting from the same base, the
// reference graph's membership predicate equals base-composed-with-
// delta's membership predicate, for every triple. Proved by induction
// over `entries`, generalised over the starting `(g_ref, g_base, dr)`
// triple so the induction goes through one entry at a time.
let state_agrees (g_ref g_base : rdf_graph) (dr : delta_resolved) : Type0 =
  forall (t : triple).
    mem_triple t g_ref ==
    (if dr.dr_cleared
     then mem_triple t dr.dr_added
     else (mem_triple t g_base && not (mem_triple t dr.dr_removed)) || mem_triple t dr.dr_added)

let lemma_state_agrees_init (g_base : rdf_graph)
  : Lemma (state_agrees g_base g_base delta_resolved_empty)
  = ()

// Explicit forall-elimination at a chosen `t` — used instead of relying
// on Z3 to auto-instantiate the ambient `state_agrees` hypothesis deep
// inside a larger proof; anchoring the instantiation in its own lemma
// call gives Z3 an unambiguous trigger.
let lemma_state_agrees_elim (g_ref g_base : rdf_graph) (dr : delta_resolved) (t : triple)
  : Lemma (requires state_agrees g_ref g_base dr)
          (ensures
            mem_triple t g_ref ==
            (if dr.dr_cleared
             then mem_triple t dr.dr_added
             else (mem_triple t g_base && not (mem_triple t dr.dr_removed)) || mem_triple t dr.dr_added))
  = ()

// One step: applying the SAME entry `e` to `g_ref` (`apply_entry_ref_step`)
// and to `dr` (`apply_entry_to_delta`) preserves `state_agrees`, given it
// held before the step. Each of the five constructors either leaves both
// sides untouched (entry doesn't target `graph_key`, or DE_Create) or
// updates both sides through the SAME graph_add/graph_remove/clear shape
// — the per-`t` boolean algebra is spelled out in this module's own
// design notes; here it is discharged by asserting the graph_add/
// graph_remove membership facts at the right places and letting Z3
// close the resulting boolean identity.
let lemma_state_agrees_step
  (graph_key : option T.iri) (g_ref g_base : rdf_graph) (dr : delta_resolved) (e : DL.delta_entry)
  : Lemma
      (requires state_agrees g_ref g_base dr)
      (ensures
        state_agrees
          (apply_entry_ref_step graph_key g_ref e)
          g_base
          (apply_entry_to_delta graph_key dr e))
  = let dr' = apply_entry_to_delta graph_key dr e in
    let g_ref' = apply_entry_ref_step graph_key g_ref e in
    let aux (t : triple) : Lemma (
        mem_triple t g_ref' ==
        (if dr'.dr_cleared
         then mem_triple t dr'.dr_added
         else (mem_triple t g_base && not (mem_triple t dr'.dr_removed)) || mem_triple t dr'.dr_added))
      =
        match e with
        | DL.DE_Add q gr ->
          if gr = graph_key then begin
            lemma_mem_graph_add q g_ref t;
            lemma_mem_graph_add q dr.dr_added t;
            if not dr.dr_cleared then lemma_mem_graph_remove q dr.dr_removed t
          end
        | DL.DE_Remove q gr ->
          if gr = graph_key then begin
            lemma_mem_graph_remove q g_ref t;
            lemma_mem_graph_remove q dr.dr_added t;
            if not dr.dr_cleared then lemma_mem_graph_add q dr.dr_removed t
          end
        | DL.DE_Clear gr -> ()
        | DL.DE_Drop gr -> ()
        | DL.DE_Create _ -> ()
      in
      FStar.Classical.forall_intro aux

let rec lemma_apply_entries_state_agrees
  (graph_key : option T.iri) (g_base : rdf_graph) (dr0 : delta_resolved) (entries : list DL.delta_entry)
  (g_ref0 : rdf_graph)
  : Lemma
      (requires state_agrees g_ref0 g_base dr0)
      (ensures
        state_agrees
          (apply_entries_ref graph_key g_ref0 entries)
          g_base
          (fold_entries_for_graph graph_key entries dr0))
      (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      lemma_state_agrees_step graph_key g_ref0 g_base dr0 e;
      lemma_apply_entries_state_agrees graph_key g_base
        (apply_entry_to_delta graph_key dr0 e) rest
        (apply_entry_ref_step graph_key g_ref0 e)

// The main theorem: querying the reference graph (entries applied
// directly) through `triple_matches_bound` agrees, triple for triple,
// with `merge_on_read` composed with `fold_entries_for_graph` applied
// to the SAME base + entries — for any bound `b`. This is the design
// doc's correctness bridge (§3.2's `lemma_merge_on_read_matches_
// apply_update`), proved for the delta_entry vocabulary directly
// (INSERT DATA/DELETE DATA/CLEAR/DROP on one graph, in sequence) —
// see this section's banner for the residual (full `update_op`/
// `apply_update_ops` generality).
#push-options "--z3rlimit 200"
let lemma_merge_on_read_matches_apply_entries
  (graph_key : option T.iri) (g_base : rdf_graph) (entries : list DL.delta_entry) (b : triple_pattern_bound)
  : Lemma (
      forall (t : triple).
        mem_triple t (triple_matches_bound b (apply_entries_ref graph_key g_base entries)) ==
        mem_triple t (merge_on_read (triple_matches_bound b g_base)
                                     (fold_entries_for_graph graph_key entries delta_resolved_empty) b))
  =
  let dr = fold_entries_for_graph graph_key entries delta_resolved_empty in
  let g_ref = apply_entries_ref graph_key g_base entries in
  lemma_state_agrees_init g_base;
  lemma_apply_entries_state_agrees graph_key g_base delta_resolved_empty entries g_base;
  let aux (t : triple) : Lemma (
      mem_triple t (triple_matches_bound b g_ref) ==
      mem_triple t (merge_on_read (triple_matches_bound b g_base) dr b))
    =
      lemma_state_agrees_elim g_ref g_base dr t;
      assert (
        mem_triple t g_ref ==
        (if dr.dr_cleared then mem_triple t dr.dr_added
         else (mem_triple t g_base && not (mem_triple t dr.dr_removed)) || mem_triple t dr.dr_added));
      lemma_mem_triple_matches_bound b g_ref t;
      assert (mem_triple t (triple_matches_bound b g_ref) == (mem_triple t g_ref && bound_matches b t));
      lemma_mem_triple_matches_bound b g_base t;
      assert (mem_triple t (triple_matches_bound b g_base) == (mem_triple t g_base && bound_matches b t));
      lemma_mem_triple_matches_bound b dr.dr_added t;
      assert (mem_triple t (triple_matches_bound b dr.dr_added) == (mem_triple t dr.dr_added && bound_matches b t));
      lemma_mem_triple_append t
        (filter_tombstoned (triple_matches_bound b g_base) dr)
        (triple_matches_bound b dr.dr_added);
      assert (
        mem_triple t (merge_on_read (triple_matches_bound b g_base) dr b) ==
        (mem_triple t (filter_tombstoned (triple_matches_bound b g_base) dr) ||
         mem_triple t (triple_matches_bound b dr.dr_added)));
      lemma_mem_filter_tombstoned (triple_matches_bound b g_base) dr t
    in
    FStar.Classical.forall_intro aux
#pop-options

(* ---------------------------------------------------------------------
   Residual (stage 3.5, per this task's own escape hatch): the FULL
   design-doc lemma, over real `update_op`/`apply_update_ops`
   (SPARQL11.Algebra.fst:5716/5728) rather than `delta_entry`/
   `apply_entries_ref` directly. Written as a statement, NOT compiled —
   it needs `update_ops_to_delta_entries`, an unbuilt translator:

     val update_ops_to_delta_entries : list update_op -> Tot (option (list DL.delta_entry))
     // Some entries  <=> every op is U_InsertData/U_DeleteData (ground
     //                    triples only, no WHERE) targeting `graph_key`,
     //                    or U_Clear/U_Drop/U_Create targeting `graph_key`
     //                    or GR_Default/GR_Graph (not GR_Named/GR_All --
     //                    those fan out over every named graph, which a
     //                    single delta_entry's per-entry graph field
     //                    cannot express without the CALLER already
     //                    knowing every graph name, i.e. dataset-level
     //                    translation, out of scope here)
     // None           <=> some op is U_DeleteWhere/U_Modify/U_Copy/
     //                    U_Move/U_Add/U_Load, or a Clear/Drop/Create
     //                    against GR_Named/GR_All

     val lemma_merge_on_read_matches_apply_update
       (ds : rdf_dataset) (ops : list update_op) (graph_key : option T.iri) (b : triple_pattern_bound)
       : Lemma
           (requires Some? (update_ops_to_delta_entries ops))
           (ensures (
             let ds' = apply_update_ops ds ops in
             let g_base = (match graph_key with
                           | None -> ds.ds_default
                           | Some gi -> match lookup_named_graph gi ds.ds_named with
                                        | Some g -> g | None -> []) in
             let g_after = (match graph_key with
                            | None -> ds'.ds_default
                            | Some gi -> match lookup_named_graph gi ds'.ds_named with
                                         | Some g -> g | None -> []) in
             let Some entries = update_ops_to_delta_entries ops in
             forall (t : triple).
               mem_triple t (triple_matches_bound b g_after) ==
               mem_triple t (merge_on_read (triple_matches_bound b g_base)
                                           (fold_entries_for_graph graph_key entries delta_resolved_empty) b)))

   This would follow from `lemma_merge_on_read_matches_apply_entries`
   above plus a SEPARATE lemma that `apply_update_ops` restricted to
   this op vocabulary agrees with `apply_entries_ref` on the same
   graph (i.e. `apply_insert_data`/`apply_delete_data` on ground data
   reduce to `graph_add`/`graph_remove` per triple, and `apply_clear`/
   `apply_drop` on `GR_Default`/`GR_Graph` reduce to emptying that one
   graph) — each of those four reductions is plausible from
   SPARQL11.Algebra.fst's own definitions (§ apply_insert_data/
   apply_delete_data/apply_clear/apply_drop, lines ~5600-5715) but
   proving them, plus writing `update_ops_to_delta_entries` itself and
   its own well-formedness/translatability lemmas, is real, separate
   F* work — not merge-on-read logic, and not this stage's brief.
   Empirically PINNED instead, exhaustively, by
   tests/local/durable_update_stage3.sh (§3(c)): every scenario it
   drives (adds, a remove, a graph create+add, a clear) is checked
   three ways — CLI-over-delta-log, in-memory apply_update, and (for
   the crash case) recovered-prefix consistency — so the bridge this
   residual states is exercised at the OCaml/CLI boundary even where
   it is not yet an F* theorem.
   --------------------------------------------------------------------- *)

(* ======================================================================
   7. update_ops_to_delta_entries — stage 8 (docs/designissues/2026-07-
   06-durable-update-design.md §5 row 8, HTTP/Protocol wiring). This is
   the translator the section 6 banner named and left unbuilt: turn a
   SANDBOXED, PARSED `list update_op` (the same value factoidal_http.ml
   already produces at the POST /update boundary, after
   SPARQL.Update.Sandbox's rewrite pass) into the `list DL.delta_entry`
   a durably-committed batch carries — or `None` if the request uses an
   op this translator does not (yet) express as delta entries.

   Ground-quad extraction reuses `collect_quads`/`rename_quad_bnodes`/
   `filter_no_bnode_quads`, ALREADY-VERIFIED SPARQL11.Algebra.fst
   functions that `apply_insert_data`/`apply_delete_data` themselves
   call (lines 4919-5044) — this translator does not reimplement ground-
   triple extraction or bnode freshening, it feeds the exact same
   helpers and wraps their output as DE_Add/DE_Remove instead of an
   in-place graph mutation. `request_salt` is threaded exactly as
   `apply_update_ops` threads it (SPARQL11.Algebra.fst:5729-5762) so a
   durably-committed INSERT DATA gets the SAME bnode identity the
   in-memory evaluator would have given it, had this op run there
   instead — required for the two paths (durable delta log vs. legacy
   in-memory dataset_ref) to ever agree on `:insert-data-same-bnode.

   Translatable vocabulary (`Some entries`):
     - U_InsertData / U_DeleteData: any ground quads the template
       carries, across ANY number of graphs (collect_quads already
       walks nested GP_Graph wrappers and tags each quad with its own
       graph — no single-graph restriction is needed here, unlike the
       design doc §3.2 sketch's `graph_key`-scoped phrasing suggested;
       DL.delta_entry's `graph:option T.iri` is already per-entry, and
       fold_entries_for_graph already filters per graph_key at fold
       time, so a multi-graph INSERT DATA template translates directly
       into a mixed-graph delta_entry list with no fan-out logic here).
     - U_Clear/U_Drop targeting GR_Default or GR_Graph <iri>. DE_Drop
       only carries a named-graph iri (no DEFAULT variant — see
       DeltaLog.fst's delta_entry banner); DROP DEFAULT has the exact
       same triple-level effect as CLEAR DEFAULT (apply_drop's own
       GR_Default arm just empties the default graph, identically to
       apply_clear's), so it translates to `DE_Clear None` too — this
       is NOT a semantic shortcut, it is what SPARQL11.Algebra.fst's
       own apply_drop/apply_clear already do for GR_Default.
     - U_Create <iri>: `DE_Create iri`, existence bookkeeping only
       (module banner §2) — always translatable, never fails.

   NOT translatable (`None` — the whole request is rejected, honestly,
   rather than partially committed):
     - U_Clear/U_Drop against GR_Named/GR_All: a fan-out over every
       named graph the store currently has, which this op-local
       translator cannot resolve (it never sees a `dataset`/backend,
       by design — see the module banner's "no I/O, no assume val").
     - U_DeleteWhere/U_Modify: require WHERE-clause evaluation against
       the composed (base ⊕ delta) view before there are any ground
       quads to turn into entries.
     - U_Copy/U_Move/U_Add: read one graph_ref and write another,
       which needs dataset-level graph lookup this translator does not
       have.
     - U_Load: already rejected upstream (LOAD needs HTTP I/O, gated at
       `SPARQL.Update.Analysis.update_has_load` before this translator
       ever runs).

   This IS the stage-3.5 residual named in section 6, built now for the
   part that is genuinely ground-quad-shaped — not a superset of it.
   The full-generality bridge lemma (`lemma_merge_on_read_matches_
   apply_update`, section 6's uncompiled statement) is NOT proved for
   this translator either: proving it requires, per graph_key, that
   `apply_update_ops` restricted to this exact vocabulary agrees with
   `apply_entries_ref` — four separate reductions (insert_data/
   delete_data/clear/drop each restricted to GR_Default/GR_Graph) that
   are plausible from SPARQL11.Algebra.fst's own definitions but are
   real, separate F* proof work, not merge-on-read logic. Per this
   task's own escape hatch ("prove if commit-sized, else pin
   exhaustively and keep the residual honest"): PINNED, not proved.
   Exercised by tests/local/durable_update_stage8_http.sh, which drives
   INSERT DATA / DELETE DATA / CLEAR / DROP / CREATE through the live
   --rw HTTP endpoint and checks the delta-log-backed read view agrees
   with an independent in-memory apply_update_ops run on the same op
   sequence — the same "three ways" empirical bridge stage 3 already
   established, now at the HTTP boundary. Every op OUTSIDE this
   vocabulary (Modify/DeleteWhere/Copy/Move/Add) is rejected with an
   explicit error at the OCaml boundary (factoidal_http.ml) rather than
   silently falling back to an in-memory-only apply that would desync
   the durable store from what a client was told succeeded — the
   translator's `None` is load-bearing, not a placeholder.
   ====================================================================== *)

// One collected (graph, triple) pair, promoted to a DE_Add. Typed over
// `option T.wf_iri` (collect_quads/rename_quad_bnodes's actual output
// type), not `option T.iri` — DE_Add's field is `option T.iri`, but the
// wf_iri -> iri refinement coercion only goes through cleanly at a
// concrete constructor application, not through a `list`-of-tuples
// codomain (F* cannot derive `list (option wf_iri * triple) <: list
// (option iri * triple)` from the function's arrow type alone; see
// RDF.Term.fsti's own `is_iri`/`wf_iri` banner and the CSVW.Conversion
// module's `pred_valid` comment for the same trap).
let quad_to_add (q : option T.wf_iri * triple) : DL.delta_entry =
  let (g, t) = q in
  // `option wf_iri` does not coerce to `option T.iri` as a whole value
  // (F*'s subtyping does not propagate through an already-applied
  // parametric type here) — rebuilding via Some/None forces the
  // coercion at the single `wf_iri`-typed argument position instead,
  // where it DOES hold (wf_iri is a plain refinement of iri).
  let g' : option T.iri = (match g with None -> None | Some gi -> Some gi) in
  DL.DE_Add t g'

// One collected (graph, triple) pair, promoted to a DE_Remove.
let quad_to_remove (q : option T.wf_iri * triple) : DL.delta_entry =
  let (g, t) = q in
  let g' : option T.iri = (match g with None -> None | Some gi -> Some gi) in
  DL.DE_Remove t g'

// Translate ONE update_op into its delta_entry sequence, or None if it
// falls outside the ground-data vocabulary above.
let op_to_delta_entries (request_salt : string) (op : update_op)
  : Tot (option (list DL.delta_entry)) =
  match op with
  | U_InsertData g ->
    let quads = collect_quads None g in
    let prefix = String.concat "" ["_insdata_"; request_salt] in
    let renamed = List.Tot.map (rename_quad_bnodes prefix) quads in
    Some (List.Tot.map quad_to_add renamed)
  | U_DeleteData g ->
    let quads = filter_no_bnode_quads (collect_quads None g) in
    Some (List.Tot.map quad_to_remove quads)
  | U_Clear _silent GR_Default     -> Some [ DL.DE_Clear None ]
  | U_Clear _silent (GR_Graph iri) -> Some [ DL.DE_Clear (Some iri) ]
  | U_Clear _silent GR_Named       -> None
  | U_Clear _silent GR_All         -> None
  | U_Drop  _silent GR_Default     -> Some [ DL.DE_Clear None ]  // see banner
  | U_Drop  _silent (GR_Graph iri) -> Some [ DL.DE_Drop iri ]
  | U_Drop  _silent GR_Named       -> None
  | U_Drop  _silent GR_All         -> None
  | U_Create _silent iri           -> Some [ DL.DE_Create iri ]
  | U_DeleteWhere _                -> None
  | U_Modify _ _ _ _ _             -> None
  | U_Copy _ _ _                   -> None
  | U_Move _ _ _                   -> None
  | U_Add _ _ _                    -> None
  | U_Load _ _ _                   -> None

// Translate a whole request's op list, in order (order matters:
// fold_entries_for_graph replays entries sequentially, so an op list
// containing e.g. an INSERT then a later DELETE of the same triple must
// keep that order in the emitted entries). `None` if ANY op in the list
// falls outside the translatable vocabulary — the whole request is
// rejected rather than partially durable (see banner).
let rec update_ops_to_delta_entries (request_salt : string) (ops : list update_op)
  : Tot (option (list DL.delta_entry)) (decreases ops) =
  match ops with
  | [] -> Some []
  | op :: rest ->
    (match op_to_delta_entries request_salt op with
     | None -> None
     | Some es ->
       (match update_ops_to_delta_entries request_salt rest with
        | None -> None
        | Some es' -> Some (es @ es')))

(* ======================================================================
   8. GSP write ops -> delta entries (stage 8's second wiring surface:
   the SPARQL 1.1 Graph Store HTTP Protocol, SPARQL.GraphStore.fst).

   Unlike `update_ops_to_delta_entries` above, all three GSP write verbs
   translate COMPLETELY — no `None` case, no residual. PUT/POST/DELETE
   are whole-graph replace/merge/remove operations against a single,
   already-resolved target graph (the GSP request target, `gs_target`
   in SPARQL.GraphStore.fst, is resolved to a `graph_key` by the HTTP
   layer BEFORE this runs — no WHERE clause, no multi-graph fan-out,
   no bnode-freshening request-salt threading the way INSERT DATA
   needs). This is exactly the shape a `delta_entry` sequence expresses
   natively, so no `option` return type is needed here.

   `graph_key : option T.iri` mirrors `DL.delta_entry`'s own convention
   (`None` = default graph); the OCaml boundary computes it from
   `SPARQL.GraphStore.gs_target` (`GT_Default -> None`, `GT_Named k ->
   Some k`) before calling in. `SPARQL.GraphStore.graph_key = string`
   is intentionally NOT `T.wf_iri` (that module's own banner: GSP graph
   IRIs may be relative, colon-optional) — no coercion trap here since
   `T.iri = string` is a plain alias, not a refinement, so a bare
   `graph_key` value already IS a `T.iri`. *)

// PUT: replace the target graph's entire content with `g`. Semantically
// CLEAR the graph then ADD every triple in `g` — `fold_entries_for_graph`
// processes entries in order, and `DE_Clear` resets `dr_added` to `[]`
// (module banner §2's `delta_resolved_cleared`), so the DE_Add entries
// that follow land in a genuinely-emptied accumulator, matching PUT's
// "replace" semantics (`SPARQL.GraphStore.gsp_put`) exactly.
let gsp_put_to_delta_entries (graph_key : option T.iri) (g : rdf_graph)
  : Tot (list DL.delta_entry) =
  DL.DE_Clear graph_key :: List.Tot.map (fun (t : triple) -> DL.DE_Add t graph_key) g

// POST: merge `g` into the target graph (`SPARQL.GraphStore.gsp_post`'s
// `graph_union`) — no CLEAR, just additions; `merge_on_read`'s own
// additive union with the base already gives set semantics (a
// re-added existing triple is a no-op via `graph_add`'s dedup, same as
// `gsp_post`'s `graph_union`).
let gsp_post_to_delta_entries (graph_key : option T.iri) (g : rdf_graph)
  : Tot (list DL.delta_entry) =
  List.Tot.map (fun (t : triple) -> DL.DE_Add t graph_key) g

// DELETE: remove the target graph entirely (`SPARQL.GraphStore.gsp_delete`
// empties it to `empty_graph`) — a single CLEAR.
let gsp_delete_to_delta_entries (graph_key : option T.iri)
  : Tot (list DL.delta_entry) =
  [ DL.DE_Clear graph_key ]
