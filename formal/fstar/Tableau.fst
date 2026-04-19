module Tableau

(* OWL-DL tableau reasoner — STAGE (a): SKELETON ONLY.

   This module is the foundation of a multi-session workstream to land a
   real tableau-based OWL-DL reasoner in factoidal, as described in
   `docs/designissues/2026-04-19-tableau-owl-plan.md` §5.

   ============================================================
   WHAT STAGE (a) DOES:
   ============================================================
   - Declares data types for a tableau node, branch, and state.
   - Exposes a single entry point, `owl_tableau_entails`, whose contract
     is:
         Some true  -> the goal triple is provably entailed by
                       `data` + `schema` under the named regime.
         Some false -> the goal is provably NOT entailed (in a complete
                       fragment, "not entailed" = "counter-model exists").
         None       -> the reasoner is incomplete for this input; the
                       caller should fall back to a Datalog closure or
                       report unknown.
   - Returns `None` for every non-trivial input. This is a FEATURE, not
     a bug: stage (a) is pure wiring, so the skeleton lands without
     making any claim we cannot back. Later stages (b) through (f) fill
     in actual reasoning, one OWL construct at a time.

   ============================================================
   WHAT STAGE (a) EXPLICITLY DOES NOT DO:
   ============================================================
   - No class-expression satisfiability checking (that is stage b).
   - No cardinality reasoning (stage c).
   - No complementOf / classical negation (stage d).
   - No fresh-individual skolemisation (stage e).
   - No optimisations (blocking, absorption, pruning) — stage f.
   - Does NOT materialise any new triples into the graph. Stage (a)'s
     runtime effect on the test suite is: zero. The entailment counts
     before and after this commit are expected to be identical. Any
     change in counts means wiring is wrong.

   ============================================================
   DESIGN NOTES:
   ============================================================
   A tableau node represents what is known (and derived) about a single
   individual within one branch of the search. The standard OWL-DL
   tableau carries:
     - a label: the set of class expressions asserted of the individual
       (here reduced to a list of named class IRIs for stage a; future
       stages will extend this to a rich `class_expr` ADT).
     - edges: outgoing property assertions to other nodes in the same
       branch.
     - equalities: `sameAs` assertions. Under UNA (Unique Name
       Assumption) all named individuals are distinct unless
       `owl:sameAs` is explicitly stated; stage (a) keeps UNA OFF by
       default (safer wrt OWL semantics) but carries the flag so future
       stages can toggle.

   A branch is a list of nodes + a status marker. A tableau in progress
   has multiple branches (disjunctive reasoning) — stage (a) stubs that
   by carrying a singleton branch list.

   The outstanding work in a tableau is a set of expansion obligations
   (a.k.a. completion rules waiting to fire) + pending clash checks.
   Stage (a) stores them but never processes them beyond a trivial
   "already in closure" check.

   Termination: the real tableau terminates via blocking (if a new
   node's label is a subset of an ancestor's, stop expanding). Stage
   (a) uses a simple fuel parameter — the caller passes a step budget,
   `tableau_step` decrements it. If fuel runs out, return `Unknown`.
   That's safe because `Unknown` yields `None` to the caller, who
   falls back to the Datalog closure.
*)

open FStar.List.Tot
open RDF.Graph.Executable

(* -------------------------------------------------------------------
   1. Tableau node — what's asserted / known about one individual.
   ------------------------------------------------------------------- *)

(* A property link out of a node.
   In the full tableau this points to another tableau node; in the
   stage-(a) skeleton we key by subject (the individual), predicate
   (an IRI), and object term. Self-loops allowed. *)
noeq type tab_link = {
  tl_pred : wf_iri;
  tl_obj  : rdf_term;
}

(* Representation of the individual this node is about. Can be an
   IRI-named individual (most named constants in a test) or a blank
   node / skolem constant introduced during expansion (stage e will
   use this). *)
noeq type tab_individual =
  | TI_IRI    : wf_iri    -> tab_individual
  | TI_BNode  : bnode_id  -> tab_individual
  | TI_Skolem : nat       -> tab_individual  (* fresh skolem id, unused in stage a *)

(* A tableau node = what we know about one individual in this branch.
   `tn_classes` is the set of (named) classes the individual is
   asserted or derived to be a member of.
   `tn_links` is the set of outgoing property assertions.
   `tn_same_as` is the set of `owl:sameAs` assertions for this node. *)
noeq type tab_node = {
  tn_indiv    : tab_individual;
  tn_classes  : list wf_iri;       (* stage (b) will upgrade to class_expr *)
  tn_links    : list tab_link;
  tn_same_as  : list tab_individual;
}

(* Smart constructor: an empty node at a named individual. *)
let make_iri_node (i : wf_iri) : tab_node =
  { tn_indiv = TI_IRI i; tn_classes = []; tn_links = []; tn_same_as = [] }

(* -------------------------------------------------------------------
   2. Tableau branch.
   ------------------------------------------------------------------- *)

(* A branch's status:
   - Open    : still being expanded, no clash found yet.
   - Closed  : a contradiction was derived — this branch refutes the goal.
   - Unknown : fuel exhausted / construct not yet implemented.           *)
type tab_status =
  | Open
  | Closed
  | Unknown

(* A branch is a collection of nodes + a status. The node list is
   effectively a map from individual-id to the node's label/links. *)
noeq type tab_branch = {
  tb_nodes  : list tab_node;
  tb_status : tab_status;
}

let empty_branch : tab_branch =
  { tb_nodes = []; tb_status = Open }

(* -------------------------------------------------------------------
   3. Tableau state — the whole search.
   ------------------------------------------------------------------- *)

(* Expansion obligations / pending class-expression satisfiability
   checks. Stage (a) tracks them as opaque strings for debugging; stage
   (b) introduces a real `class_expr` ADT and keyed obligations. *)
noeq type tab_obligation = {
  tob_owner : tab_individual;
  tob_desc  : string;                (* human-readable, for traces *)
}

noeq type tableau_state = {
  ts_branches     : list tab_branch;
  ts_obligations  : list tab_obligation;
  ts_una          : bool;            (* Unique Name Assumption toggle; OFF by default *)
  ts_fuel_used    : nat;             (* diagnostic *)
}

let init_tableau_state (_ : unit) : tableau_state =
  { ts_branches    = [empty_branch];
    ts_obligations = [];
    ts_una         = false;
    ts_fuel_used   = 0; }

(* -------------------------------------------------------------------
   4. Very small helpers.
   ------------------------------------------------------------------- *)

(* Does `goal` appear verbatim in `g` (already-closed graph)? Used by
   the trivial "already in closure" check in stage (a). *)
let rec triple_in_graph (goal : triple) (g : rdf_graph) : Tot bool (decreases g) =
  match g with
  | [] -> false
  | t :: rest -> if triple_eq t goal then true else triple_in_graph goal rest

(* -------------------------------------------------------------------
   5. tableau_step — one expansion / clash-check.
   ------------------------------------------------------------------- *)

(* Decrement fuel and do one tiny unit of work. In stage (a) this is
   deliberately minimal: if we see any obligations, we just bail out
   with Unknown (we can't handle anything yet). Fuel is a nat so
   termination is trivial. *)
let tableau_step (st : tableau_state) (fuel : nat)
  : Tot (tableau_state & tab_status) (decreases fuel) =
  if fuel = 0 then
    (st, Unknown)
  else
    match st.ts_obligations with
    | [] ->
      (* Nothing to do — the tableau is saturated wrt our (empty) rule
         set. An open branch with no pending obligations is a
         "completion" in DL parlance. Stage (a) always returns Unknown
         here because we haven't even checked class-expression
         satisfiability yet. Later stages will return Open (model
         found) for the satisfiability branch. *)
      (st, Unknown)
    | _ :: _ ->
      (* We have work to do but we can't do it yet. *)
      (st, Unknown)

(* -------------------------------------------------------------------
   6. owl_tableau_entails — top-level entry point.
   ------------------------------------------------------------------- *)

(* Contract reminder (see module header):
     Some true  : goal is provably entailed.
     Some false : goal is provably NOT entailed.
     None       : unknown — caller should fall back.

   Stage (a) logic:
     - Only recognise the trivial case "goal already appears
       syntactically in `data`" (which really just means our Datalog
       closure already derived it; the caller passes us the closed
       graph via `data`). That triggers `Some true`.
     - Everything else: `None`. No claims made.

   Arguments:
     regime : entailment regime string. Stage (a) accepts any string;
              stage (b) may branch on "OWL-Direct" vs other regimes.
     data   : dataset containing the ABox (already closed if the caller
              ran an outer Datalog pass, which is the expected mode
              under the `OWL-Direct` dispatch in
              RDF.Graph.Executable.entailment_closure).
     schema : dataset containing the TBox + schema axioms. Stage (a)
              ignores this entirely.
     goal   : the triple the caller wants entailment-checked.

   Stage (a) DELIBERATELY does not consult `schema` beyond trivia and
   does not attempt any reasoning — the whole point of this commit is
   to add the wiring point without claiming anything.

   Termination: argument-size decreasing via the `nat` fuel parameter
   in `tableau_step` only, which this function doesn't call in stage
   (a); here we just do a membership scan. No admits. *)
let owl_tableau_entails
  (regime : string)
  (data   : rdf_dataset)
  (schema : rdf_dataset)
  (goal   : triple)
  : Tot (option bool)
  =
  let _ = regime in  // silence "unused" in OCaml extraction (stage a)
  let _ = schema in
  // Trivial case: goal is already in the closed default graph.
  if triple_in_graph goal data.ds_default then
    Some true
  else
    // Everything else: we don't know. Caller falls back.
    None

(* -------------------------------------------------------------------
   7. Convenience: run on a pre-computed closure graph.
   ------------------------------------------------------------------- *)

(* Variant that takes a single graph rather than a dataset. Useful when
   the caller has already computed the entailment closure and just
   wants to consult the tableau for a single goal. *)
let owl_tableau_entails_graph
  (regime : string)
  (g      : rdf_graph)
  (goal   : triple)
  : Tot (option bool)
  =
  let ds = { ds_default = g; ds_named = [] } in
  owl_tableau_entails regime ds empty_dataset goal

(* -------------------------------------------------------------------
   8. In-file test matrix (guarded, non-executing).
   ------------------------------------------------------------------- *)

(* These assertions are compiled only when the literal `false` flips to
   `true` — they're here as a worked example for future sessions and
   as a compile-time sanity check that the types line up. F* does not
   prune this block at extraction, but `if false then ...` is dead
   code so the OCaml output is a no-op. *)
let _tableau_sanity_matrix : unit =
  if false then
    begin
      // Build a tiny IRI and a one-triple graph.
      let i_alice : wf_iri =
        assert_norm (is_iri "http://ex/alice");
        "http://ex/alice" in
      let i_person : wf_iri =
        assert_norm (is_iri "http://ex/Person");
        "http://ex/Person" in
      let type_triple : triple = {
        s = S_IRI i_alice;
        p = rdf_type;
        o = T_IRI i_person;
      } in

      // Goal present in data -> Some true.
      let data1 : rdf_dataset = {
        ds_default = [type_triple]; ds_named = [];
      } in
      let res1 = owl_tableau_entails "OWL-Direct" data1 empty_dataset type_triple in
      assert (res1 = Some true);

      // Goal absent from data -> None (stage-a skeleton).
      let i_student : wf_iri =
        assert_norm (is_iri "http://ex/Student");
        "http://ex/Student" in
      let different_goal : triple = {
        s = S_IRI i_alice;
        p = rdf_type;
        o = T_IRI i_student;
      } in
      let data2 : rdf_dataset = {
        ds_default = []; ds_named = [];
      } in
      let res2 = owl_tableau_entails "OWL-Direct" data2 empty_dataset different_goal in
      assert (res2 = None);

      // init_tableau_state + one step with zero fuel -> Unknown.
      let st = init_tableau_state () in
      let (_, status) = tableau_step st 0 in
      assert (status = Unknown);

      ()
    end
  else ()
