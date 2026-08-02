module RDFS.Closure

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.4/§3.3 step 6. Moves the RDFS entailment layer out of
// RDF.Graph.Executable.fst: the seven `rdfs_rule_*` functions, the
// fixed-point `rdfs_closure`/`rdfs_closure_step` driver, and the
// reflexivity-axiom harvesting (`rdfs_reflexivity_axioms`/
// `rdfs_closure_with_reflexivity`) that approximates RDFS's "every
// class is a subclass of itself" / "every property is a subproperty of
// itself" entailments. A copy-move, no logic change — every function
// body below is byte-identical to its pre-move counterpart in
// RDF.Graph.Executable.fst.
//
// RDFS rule-table IDs realised here (RDF Semantics / RDFS entailment
// rules, https://www.w3.org/TR/rdf11-mt/ §"RDFS entailment rules" —
// rule numbers per the table there):
//   - rdfs7  `rdfs_rule_subPropertyOf`         (a P b, P subPropertyOf Q |- a Q b)
//   - rdfs2  `rdfs_rule_domain`                (a P b, P domain C |- a type C)
//   - rdfs3  `rdfs_rule_range`                 (a P b, P range C |- b type C)
//   - rdfs9  `rdfs_rule_subClassOf`            (a type A, A subClassOf B |- a type B)
//   - rdfs11 `rdfs_rule_subClassOf_trans`      (A subClassOf B, B subClassOf C |- A subClassOf C)
//   - rdfs5  `rdfs_rule_subPropertyOf_trans`   (P subPropertyOf Q, Q subPropertyOf R |- P subPropertyOf R)
//   - (container membership axioms, not separately numbered in the
//     table — the finite `rdf:_1`..`rdf:_5` slice of the infinite
//     `rdf:_n` family; see RDF.Vocabulary.Axioms.fst's banner for why
//     the truly infinite family stays rule-generated, not tabulated)
//     `rdfs_rule_container_membership`
//   - rdfs1  `rdfs_rule_recognized_datatypes`   (aaa in D |- aaa type rdfs:Datatype)
//   - rdfs4a `rdfs_rule_resource_subject`       (x a y |- x type rdfs:Resource)
//   - rdfs4b `rdfs_rule_resource_object`        (x a y |- y type rdfs:Resource)
//   - rdfs8  `rdfs_rule_class_subclass_resource`  (x type rdfs:Class
//                                                  |- x subClassOf rdfs:Resource)
//   - rdfs13 `rdfs_rule_datatype_subclass_literal` (x type rdfs:Datatype
//                                                  |- x subClassOf rdfs:Literal)
// The last five landed 2026-07-31, closing finding RS-2 of
// docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md for
// every row that this tree's term algebra can build. Still not
// implemented: rdfD1 and the 2004 reading of rdfs1, both of which mint
// fresh blank nodes — see the design note for why that is a scoped gap
// rather than an oversight.
// Plus the reflexivity approximation of rdfs6 / rdfs10 (every class /
// property collected from the graph is related to itself —
// `rdfs_reflexivity_axioms`), which mirrors the pre-F* OCaml patch #60
// this block replaced (see the block's own comment below). Since
// 2026-07-31 that harvest is SPLIT BY REGIME (finding RS-1 / #335) and
// the RDFS-regime half carries a licence theorem.
//
// This module is the base layer OWL.Closure builds on: OWL 2 RL/RDF's
// Datalog closure interleaves its own rules with `rdfs_closure_step`
// every iteration (see OWL.Closure.fsti's `owl_rl_closure_mode`), and
// `entailment_closure`'s "RDFS"/"RDF" regimes dispatch straight to
// `rdfs_closure_with_reflexivity`/`rdfs_closure` here. OWL.Closure
// depends on this module; this module depends on nothing OWL-specific.
//
// Dependency direction (why this avoids the cycle RDF.Indexed.fsti's
// banner describes for step 3): this module opens RDF.Term/RDF.Triple/
// RDF.Graph/RDF.Indexed/RDF.Vocabulary only — never RDF.Graph.Executable.
// RDF.Graph.Executable.fst instead `include`s this module (F* `include`,
// same mechanism step 5 used for RDF.Term/RDF.Triple/RDF.Graph) so its
// existing dependents (SHACL.Validation.fst, RDF.Vocabulary.Axioms.fst,
// and any other `open RDF.Graph.Executable` caller of `rdfs_closure`/
// `rdfs_rule_*`) keep resolving these names unqualified with zero
// source changes.
//
// The RDFS vocabulary constants below are this module's OWN copy,
// re-derived from RDF.Vocabulary (never from RDF.Graph.Executable.fst's
// section-16 shim, which would cycle) — same `assert_norm`-cast pattern
// RDF.Graph.Executable.fst's shim and RDF.Vocabulary.Axioms.fst both
// already use. Byte-identical values; two call sites for the same
// vocabulary table is intentional (see RDF.Vocabulary.fsti for the
// underlying string constants) rather than a fork risk, since both
// forward straight from RDF.Vocabulary.

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDF.Vocabulary
// RDF.Vocabulary.Axioms.fst (2026-07-05, design doc "foundational-core-
// refactor" owner-addition header + §3.3 step 6's "Axioms seed-graph
// gate") holds the finite RDF+RDFS axiomatic triple tables. Re-targeted
// at step 6 to open RDF.Term/RDF.Triple directly (not
// RDF.Graph.Executable, which would cycle back through this file's
// `include`) so it can be opened here. Seeding it into
// `rdfs_closure_with_reflexivity` was attempted and DISABLED pending
// review — see that function's comment (bottom of this file) for the
// measured OWL-consistency regression and the #236 interaction.
open RDF.Vocabulary.Axioms

(** ------------------------------------------------------------------ *)
(** RDFS vocabulary constants (own copy — see banner)                  *)
(** ------------------------------------------------------------------ *)

let rdfs_subClassOf : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_subClassOf);
  RDF.Vocabulary.rdfs_subClassOf

let rdfs_subPropertyOf : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_subPropertyOf);
  RDF.Vocabulary.rdfs_subPropertyOf

let rdfs_domain : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_domain);
  RDF.Vocabulary.rdfs_domain

let rdfs_range : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_range);
  RDF.Vocabulary.rdfs_range

let rdf_type : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_type);
  RDF.Vocabulary.rdf_type

let rdfs_Class : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_Class);
  RDF.Vocabulary.rdfs_Class

let rdf_Property : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_Property);
  RDF.Vocabulary.rdf_Property

let rdfs_Resource : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_Resource);
  RDF.Vocabulary.rdfs_Resource

let rdfs_Literal : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_Literal);
  RDF.Vocabulary.rdfs_Literal

let rdfs_ContainerMembershipProperty : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_ContainerMembershipProperty);
  RDF.Vocabulary.rdfs_ContainerMembershipProperty

let rdfs_member : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_member);
  RDF.Vocabulary.rdfs_member

let rdfs_Datatype : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdfs_Datatype);
  RDF.Vocabulary.rdfs_Datatype

let rdf_1 : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_1);
  RDF.Vocabulary.rdf_1

let rdf_2 : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_2);
  RDF.Vocabulary.rdf_2

let rdf_3 : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_3);
  RDF.Vocabulary.rdf_3

let rdf_4 : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_4);
  RDF.Vocabulary.rdf_4

let rdf_5 : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_5);
  RDF.Vocabulary.rdf_5

(* Container membership property list for closure rules *)
let container_membership_properties : list wf_iri =
  [rdf_1; rdf_2; rdf_3; rdf_4; rdf_5]

(** ======================================================================== *)
(** RDFS Closure Rules (rdfs2/rdfs3/rdfs5/rdfs7/rdfs9/rdfs11 + container     *)
(** membership — see module banner for the rule-table cross-reference)      *)
(** ======================================================================== *)

(* rdfs7: If (a P b) and (P rdfs:subPropertyOf Q), infer (a Q b).
   task #36 join-reorder (2026-07-04, see docs/designissues/2026-07-04-
   lifesci-demo-entailment-perf.md): the previous shape iterated every
   DATA triple (a P b) and, for each, called find_objects_indexed on
   ig_sp keyed by (subject = P, pred = rdfs:subPropertyOf) — a compound
   key that essentially never exists on schema-free data, but
   bucket_lookup is a linear scan of ig_sp's ~N-distinct-key association
   list, so a non-match costs O(N) anyway. Measured: O(N) data triples x
   O(N) failed lookup = O(N^2), confirmed empirically (27421-triple
   lifesci disease.ttl: ~4.28s for this shape vs. sequence_variant's
   6455 triples at ~0.24s — a 4.25x size increase costing ~18x time,
   matching N^2 exactly).
   Fix: drive the join from the (schema, usually zero-to-few) subPropertyOf
   DECLARATIONS via one ig_pred lookup (that bucket's key is the bare
   predicate IRI, so it stays small regardless of graph size), then for
   each declared (P subPropertyOf Q) look up P's data triples via another
   ig_pred lookup. Semantically identical to the original (same emitted
   triple set for any graph); just the opposite join order. When there
   are zero subPropertyOf declarations (the common case for data-only
   graphs), this whole rule now costs O(1) instead of O(N^2). *)
// Same guard, for rows whose conclusion OBJECT is an arbitrary
// `rdf_term` rather than an IRI (rdfs2 and rdfs3 carry the declared
// class straight through, and it was never IRI-restricted).
//
// WHY THIS EXISTS (2026-08-02, measured). rdfs7, rdfs2, rdfs3 and rdfs9
// emitted through `add_triple_unchecked` unconditionally, so they
// re-emitted their ENTIRE conclusion set on every round and left
// `graph_dedup_sort` to collapse the duplicates. Feeding QUDT's own
// 508,139-triple closure back in -- a graph where every conclusion is
// already present and nothing can be derived -- still cost 78.8 s,
// which is 55% of the whole 143.87 s QUDT run. That is the cost of
// emitting and re-sorting a set that was already there.
//
// The emitted SET is unchanged: `ig` is built from the step's input and
// every row seeds its fold with an accumulator containing that input,
// so skipping an emission the snapshot already carries removes a
// duplicate and nothing else. Exactly the argument the five RS-2 rows
// above already rely on.
let emit_once_term (ig : indexed_graph) (acc : rdf_graph)
                   (sub : subject) (prd : wf_iri) (obj : rdf_term)
  : Tot rdf_graph =
  if ig.ig_built.bn_sp &&
     List.Tot.existsb (fun (o : rdf_term) -> rdf_term_eq o obj)
                      (find_objects_indexed ig sub prd)
  then acc
  else add_triple_unchecked acc ({ s = sub; p = prd; o = obj } <: triple)

let rdfs_rule_subPropertyOf (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (decl : triple) ->
      match decl.s, decl.o with
      | S_IRI p, T_IRI q ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            emit_once_term ig acc2 t.s q t.o)
          acc
          matching
      | _, _ -> acc)
    g
    decls

(* rdfs2: If (a P b) and (P rdfs:domain C), infer (a rdf:type C).
   Same join-reorder as rdfs_rule_subPropertyOf above (task #36):
   drive from the domain DECLARATIONS (ig_pred lookup, small/empty on
   schema-free data) rather than from every data triple. c_term is kept
   as the raw rdf_term (not restricted to T_IRI) to match the original
   rule's behaviour — domain classes were never IRI-restricted here. *)
let rdfs_rule_domain (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_domain in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            emit_once_term ig acc2 t.s rdf_type decl.o)
          acc
          matching
      | _ -> acc)
    g
    decls

(* rdfs3: If (a P b) and (P rdfs:range C), infer (b rdf:type C).
   Same join-reorder as above (task #36): drive from the range
   DECLARATIONS, not from every data triple. *)
let rdfs_rule_range (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_range in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (decl : triple) ->
      match decl.s with
      | S_IRI p ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            match term_to_subject t.o with
            | Some b_subj -> emit_once_term ig acc2 b_subj rdf_type decl.o
            | None -> acc2)
          acc
          matching
      | _ -> acc)
    g
    decls

(* rdfs9: If (a rdf:type A) and (A rdfs:subClassOf B), infer (a rdf:type B).
   For each triple (a type A) in g, find all B such that (A subClassOf B),
   then add (a type B). *)
let rdfs_rule_subClassOf (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type then
        match t.o with
        | T_IRI class_iri ->
          let super_classes = find_objects_indexed ig (S_IRI class_iri) rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (b_term : rdf_term) ->
              emit_once_term ig acc2 t.s rdf_type b_term)
            acc
            super_classes
        | _ -> acc
      else acc)
    g
    g

(* rdfs11: If (A rdfs:subClassOf B) and (B rdfs:subClassOf C) then
   (A rdfs:subClassOf C).
   Works uniformly for IRIs and bnodes in either position. *)
let rdfs_rule_subClassOf_trans (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subClassOf then
        (* t is (A subClassOf B). Find all C such that (B subClassOf C).
           B must be convertible to a subject (IRI or bnode). *)
        match term_to_subject t.o with
        | Some b_subj ->
          let supers = find_objects_indexed ig b_subj rdfs_subClassOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (c_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdfs_subClassOf; o = c_term } in
              add_triple_unchecked acc2 new_t)
            acc
            supers
        | None -> acc
      else acc)
    g
    g

(* rdfs5: If (P rdfs:subPropertyOf Q) and (Q rdfs:subPropertyOf R) then
   (P rdfs:subPropertyOf R).  Dual of rdfs11. *)
let rdfs_rule_subPropertyOf_trans (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_subPropertyOf then
        match term_to_subject t.o with
        | Some q_subj ->
          let supers = find_objects_indexed ig q_subj rdfs_subPropertyOf in
          List.Tot.fold_left
            (fun (acc2 : rdf_graph) (r_term : rdf_term) ->
              let new_t : triple = { s = t.s; p = rdfs_subPropertyOf; o = r_term } in
              add_triple_unchecked acc2 new_t)
            acc
            supers
        | None -> acc
      else acc)
    g
    g

(* Container membership property axioms:
   rdf:_1 rdfs:subPropertyOf rdfs:member
   rdf:_2 rdfs:subPropertyOf rdfs:member
   ... etc.
   Also: each rdf:_n rdf:type rdfs:ContainerMembershipProperty *)
let rdfs_rule_container_membership (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (cmp : wf_iri) ->
      let t1 : triple = {
        s = S_IRI cmp;
        p = rdfs_subPropertyOf;
        o = T_IRI rdfs_member
      } in
      let t2 : triple = {
        s = S_IRI cmp;
        p = rdf_type;
        o = T_IRI rdfs_ContainerMembershipProperty
      } in
      add_triple_unchecked (add_triple_unchecked acc t1) t2)
    g
    container_membership_properties

(** ======================================================================== *)
(** RDFS rule rows added 2026-07-31 (finding RS-2 of                         *)
(** docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md):         *)
(** rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13.                                    *)
(**                                                                          *)
(** Each is transcribed from RDF 1.1 Semantics section 9's rule table (the   *)
(** row text is quoted at the function) and proven against the declarative   *)
(** row in RDF.Entailment.RDFS.Spec.fst by a `_licensed` theorem in          *)
(** RDF.Entailment.RDFS.Refinement.fst, with a truth-preservation lemma in   *)
(** RDF.Entailment.RDFS.ModelTheory.fst.                                     *)
(** ======================================================================== *)

// Helper: is `t` of the shape `xxx rdf:type <c>` ? Written as a match on
// the object rather than a structural `=` so no decidable-equality
// instance for the recursive `rdf_term` is needed.
let is_typed_as (t : triple) (c : wf_iri) : bool =
  t.p = rdf_type && (match t.o with | T_IRI i -> i = c | _ -> false)

// The recognized datatype IRIs D. RDF 1.1 Semantics section 8: "RDF
// interpretations ... recognize the datatype IRIs rdf:langString and
// xsd:string". That MINIMUM D is what this engine recognizes for the
// purpose of rdfs1; it is the same set as
// RDF.Entailment.RDF.Spec.d_minimal, which the refinement theorem for
// this rule names.
let recognized_datatypes : list wf_iri = [rdf_lang_string; xsd_string]

// EMIT-ONCE GUARD (issue #340 item 4, 2026-07-31).
//
// All five RS-2 rows below are UNCONDITIONAL emitters: rdfs4a emits one
// triple per triple of the accumulator, rdfs4b one per subject-eligible
// object, rdfs8 / rdfs13 one per class / datatype declaration, rdfs1 two
// axioms. `rdfs_closure_step` re-runs every row on every round, so from
// round 2 onwards each row re-derived a graph-sized block of triples it
// had already derived. The accumulator handed to `graph_dedup_sort` grew
// to roughly 4x the graph on EVERY round; measured cost was OWL
// profile-RL ConsistencyTests 1.51s -> 6.07s.
//
// `snapshot_carries ig s p c` is true only when the step's index
// SNAPSHOT already carries the exact triple (s, p, <c>). A row that sees
// it true skips the emission.
//
// WHY THE RESULT IS UNCHANGED. The snapshot is the step's INPUT graph
// (`rdfs_closure_step` builds `ig` from `g` and never rebuilds it), and
// every row seeds its fold with an accumulator that already contains
// that input. So a suppressed triple is still an element of the row's
// result: the emitted SET is identical, only the duplicate COUNT drops.
// The three theorems that pin this per row live in
// RDF.Entailment.RDFS.Refinement.fst section 6c:
//   `_licensed`  -- nothing new appears  (unchanged statement, section 6b)
//   `_monotone`  -- the fold's seed survives
//   `_complete`  -- every conclusion the row licenses is still present
// `_licensed` and `_complete` together bracket the result set from both
// sides, so the guard cannot lose a derivation.
//
// NOT A HOIST. Issue #340's item 4 proposed lifting these rows out of
// the loop and running them once after the fixed point. That is UNSOUND
// -- every one of the five feeds rdfs9 or rdfs11, so a post-pass loses
// derivations. The counterexamples are in section 10.5 of
// docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md. All
// twelve rows stay in the loop; what changes is that each conclusion is
// emitted once instead of once per round.
//
// `ig_built.bn_sp` is checked first: a caller that passed a SELECTIVELY
// built index has `ig_sp = BLeaf` by construction, not because the
// triple is absent (see the `bucket_needs` banner in RDF.Indexed.fsti),
// and an unbuilt bucket must never be read as "not present".
let snapshot_carries (ig : indexed_graph) (s : subject) (p : wf_iri) (c : wf_iri)
  : Tot bool =
  ig.ig_built.bn_sp &&
  List.Tot.existsb
    (fun (o : rdf_term) -> match o with | T_IRI i -> i = c | _ -> false)
    (find_objects_indexed ig s p)

// The guarded emission all five rows perform. Named (rather than
// inlined at each call site) so section 6c's fold lemmas can be stated
// about it once instead of five times.
let emit_once (ig : indexed_graph) (acc : rdf_graph)
              (sub : subject) (prd : wf_iri) (cls : wf_iri) : Tot rdf_graph =
  if snapshot_carries ig sub prd cls then acc
  else add_triple_unchecked acc ({ s = sub; p = prd; o = T_IRI cls } <: triple)

// rdfs1, RDF 1.1 Semantics section 9 rule table, verbatim:
//   "rdfs1 | any IRI aaa in D | aaa rdf:type rdfs:Datatype ."
// The rule has NO premise from the data, so it is an axiom emitter over
// D, like rdfs_rule_container_membership above.
let rdfs1_step (ig : indexed_graph) (acc : rdf_graph) (d : wf_iri) : Tot rdf_graph =
  emit_once ig acc (S_IRI d) rdf_type rdfs_Datatype

let rdfs_rule_recognized_datatypes (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left (rdfs1_step ig) g recognized_datatypes

// rdfs4a, RDF 1.1 Semantics section 9 rule table, verbatim:
//   "rdfs4a | xxx aaa yyy . | xxx rdf:type rdfs:Resource ."
// The subject of the premise stays in subject position, so this row
// needs no generalized-RDF escape.
let rdfs4a_step (ig : indexed_graph) (acc : rdf_graph) (t : triple) : Tot rdf_graph =
  emit_once ig acc t.s rdf_type rdfs_Resource

let rdfs_rule_resource_subject (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left (rdfs4a_step ig) g g

// rdfs4b, RDF 1.1 Semantics section 9 rule table, verbatim:
//   "rdfs4b | xxx aaa yyy . | yyy rdf:type rdfs:Resource ."
// GENERALIZED-RDF PREMISE (delta D5, finding RS-3): the object moves
// into subject position, so the rule cannot fire when the object is a
// literal or an RDF 1.2 triple term -- `RDF.Term.subject` is
// IRI-or-bnode only and the conclusion is unbuildable. `term_to_subject`
// is that side condition. The declarative `rdfs4b_derives` carries the
// same premise, so the refinement is EXACT: the incompleteness is in
// the tree's term algebra, not in the proof.
let rdfs4b_step (ig : indexed_graph) (acc : rdf_graph) (t : triple) : Tot rdf_graph =
  match term_to_subject t.o with
  | Some y_subj -> emit_once ig acc y_subj rdf_type rdfs_Resource
  | None -> acc

let rdfs_rule_resource_object (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left (rdfs4b_step ig) g g

// rdfs8, RDF 1.1 Semantics section 9 rule table, verbatim:
//   "rdfs8 | xxx rdf:type rdfs:Class . | xxx rdfs:subClassOf rdfs:Resource ."
let rdfs8_step (ig : indexed_graph) (acc : rdf_graph) (t : triple) : Tot rdf_graph =
  if is_typed_as t rdfs_Class
  then emit_once ig acc t.s rdfs_subClassOf rdfs_Resource
  else acc

let rdfs_rule_class_subclass_resource (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left (rdfs8_step ig) g g

// rdfs13, RDF 1.1 Semantics section 9 rule table, verbatim:
//   "rdfs13 | xxx rdf:type rdfs:Datatype . | xxx rdfs:subClassOf rdfs:Literal ."
let rdfs13_step (ig : indexed_graph) (acc : rdf_graph) (t : triple) : Tot rdf_graph =
  if is_typed_as t rdfs_Datatype
  then emit_once ig acc t.s rdfs_subClassOf rdfs_Literal
  else acc

let rdfs_rule_datatype_subclass_literal (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left (rdfs13_step ig) g g

(** ======================================================================== *)
(** Fixed-Point RDFS Closure                                                 *)
(** ======================================================================== *)

(* Apply all RDFS rules once *)
let rdfs_closure_step (g : rdf_graph) : rdf_graph =
  (* OWL-RL Commit A: build the index once per step; share across all
     7 rules. Snapshot semantics — see #4 of the design doc. *)
  let ig = build_indexed g in
  let g1 = rdfs_rule_subPropertyOf g ig in
  let g2 = rdfs_rule_domain g1 ig in
  let g3 = rdfs_rule_range g2 ig in
  let g4 = rdfs_rule_subClassOf g3 ig in
  let g5 = rdfs_rule_container_membership g4 ig in
  let g6 = rdfs_rule_subClassOf_trans g5 ig in     (* rdfs11: C<C transitivity *)
  let g7 = rdfs_rule_subPropertyOf_trans g6 ig in  (* rdfs5:  P<P transitivity *)
  (* Rows added 2026-07-31 (RS-2). Order: the two axiom-emitting /
     class-shaped rows first, so the rdfs:Resource rows below see the
     subjects they introduce within this same step. rdfs4a/rdfs4b run
     last because they read the WHOLE accumulator.
     All five consult `snapshot_carries ig` and skip an emission the
     SNAPSHOT already carries (issue #340 item 4). `ig` is built from
     this step's INPUT and every row seeds its fold with an accumulator
     that contains that input, so the emitted SET is unchanged and only
     the duplicate count drops; see the guard's banner above and the
     `_monotone` / `_complete` theorems in
     RDF.Entailment.RDFS.Refinement.fst section 6b. *)
  let g8  = rdfs_rule_recognized_datatypes g7 ig in      (* rdfs1  *)
  let g9  = rdfs_rule_class_subclass_resource g8 ig in   (* rdfs8  *)
  let g10 = rdfs_rule_datatype_subclass_literal g9 ig in (* rdfs13 *)
  let g11 = rdfs_rule_resource_subject g10 ig in         (* rdfs4a *)
  let g12 = rdfs_rule_resource_object g11 ig in          (* rdfs4b *)
  (* #259 followup: each rule now emits duplicates via add_triple_unchecked
     (O(1) prepend). One sort-and-collapse pass here restores set semantics
     for the fixed-point check below and any downstream consumer. O(N log N)
     beats the per-insert O(N) membership scan that previously dominated
     RDFS closure on the lifesci-scale 27K-triple disease graph. *)
  graph_dedup_sort g12

(* Iterate closure until fixed point or max iterations.
   Uses nat fuel parameter for termination.
   2026-07-05 (design doc "foundational-core-refactor" §3.3 step 3): this
   proof is borderline in the unmodified tree too (verifies only via F*'s
   automatic split-on-failure retry, "Warning 349" in a plain run) — moving
   unrelated code earlier in this file (the RDF.Indexed extraction above)
   shifts the SMT context enough to tip it into a hard failure under the
   default budget. `--z3rlimit 30` is the same fix idiom already used
   throughout this tree (e.g. RDF.List.Helpers.fst, Parser.Turtle.fst) for
   borderline recursive proofs — a resource-budget bump, not a logic
   change; no --admit_smt_queries, no --lax. Kept here unconditionally at
   step 6 too — the module boundary changed again, and there is no upside
   to re-litigating whether the margin is still needed. *)
#push-options "--z3rlimit 30"
let rec rdfs_closure (g : rdf_graph) (fuel : nat) : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> g
  | n ->
    let g' = rdfs_closure_step g in
    if graph_len g' = graph_len g
    then g  (* fixed point reached — no new triples added *)
    else rdfs_closure g' (n - 1)
#pop-options

(** ======================================================================== *)
(** RDFS/OWL Reflexivity Axioms                                              *)
(** ======================================================================== *)

// RDFS entails that every class C is a subclass of itself, and every
// property P is a subproperty of itself (reflexivity of rdfs:subClassOf
// and rdfs:subPropertyOf). The set of "classes" in a graph is
// approximated by: any IRI that appears as subject or object of
// rdfs:subClassOf, or as subject of (rdf:type rdfs:Class) / (rdf:type
// owl:Class). Properties are collected analogously for rdfs:subPropertyOf,
// rdf:Property, owl:ObjectProperty, owl:DatatypeProperty.
//
// This block was formerly implemented in OCaml as post-extraction patch
// #60. Elevated to F* per iron rule #10. The owl:Class/owl:ObjectProperty/
// owl:DatatypeProperty/owl:Thing/owl:Nothing/owl:NamedIndividual
// constants below live here (not in OWL.Closure) because the RDFS-level
// reflexivity approximation itself already peeks at OWL class/property
// declarations — matching the single-file code's pre-existing behavior;
// OWL.Closure.fsti reuses these via `open RDFS.Closure`.

let owl_Class : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Class");
  "http://www.w3.org/2002/07/owl#Class"

let owl_ObjectProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#ObjectProperty");
  "http://www.w3.org/2002/07/owl#ObjectProperty"

let owl_DatatypeProperty : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#DatatypeProperty");
  "http://www.w3.org/2002/07/owl#DatatypeProperty"

let owl_Thing : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Thing");
  "http://www.w3.org/2002/07/owl#Thing"

let owl_Nothing : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Nothing");
  "http://www.w3.org/2002/07/owl#Nothing"

let owl_NamedIndividual : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#NamedIndividual");
  "http://www.w3.org/2002/07/owl#NamedIndividual"

// Prepend i to acc if not already present.
let cons_if_new_iri (i : wf_iri) (acc : list wf_iri) : list wf_iri =
  if List.Tot.mem i acc then acc else i :: acc

// If subject is an IRI, cons it into the accumulator; otherwise leave
// the accumulator unchanged (bnodes cannot participate in the OCaml
// version either — they are never classes or properties by IRI identity).
let cons_subject_iri_if_new (s : subject) (acc : list wf_iri) : list wf_iri =
  match s with
  | S_IRI i -> cons_if_new_iri i acc
  | S_BNode _ -> acc

let cons_term_iri_if_new (t : rdf_term) (acc : list wf_iri) : list wf_iri =
  match t with
  | T_IRI i -> cons_if_new_iri i acc
  | _ -> acc

// ---------------------------------------------------------------------
// REGIME SPLIT OF THE CLASS / PROPERTY HARVEST (finding RS-1 of
// docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md,
// section 7; fixed 2026-07-31, issue #335).
//
// Before this split there was ONE harvest, used by both the RDFS regime
// and the OWL-RL regime, and it accepted the OWL typing IRIs
// (owl:Class / owl:ObjectProperty / owl:DatatypeProperty). That is
// SOUND under the OWL 2 RDF-Based Semantics, whose Table 5.3 identifies
// ICEXT(I(owl:Class)) with IC, and UNSOUND at the RDFS rung, where
// owl:Class is an ordinary IRI that no RDFS condition relates to
// rdfs:Class. `entailment_closure` dispatched both regimes into the
// same function, so one regime's licence was being spent in the other.
// The machine-checked witness is
// RDF.Entailment.RDFS.Refinement.owl_reflexivity_axioms_not_rdfs_sound
// (it now names the OWL-regime function; before the split it named the
// RDFS-regime one, which is what made it a shipping-code unsoundness).
//
// The `_rdfs` harvest below reads ONLY what RDF 1.1 Semantics section 9
// licenses:
//   * subject and IRI-object of an `rdfs:subClassOf` triple -- the
//     section 9 condition "if <x,y> is in IEXT(I(rdfs:subClassOf)) then
//     x and y are in IC", combined with "IEXT(I(rdfs:subClassOf)) is
//     ... reflexive on IC";
//   * subject of `rdf:type rdfs:Class` -- rule rdfs10, whose conclusion
//     is exactly this triple.
// Duals for properties: `rdfs:subPropertyOf` positions (the IP
// condition plus reflexivity on IP) and `rdf:type rdf:Property`
// (rule rdfs6).
// ---------------------------------------------------------------------

// RDFS-regime class typing: rdfs:Class only.
let is_class_type_object_rdfs (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdfs_Class
  | _ -> false

// RDFS-regime property typing: rdf:Property only.
let is_property_type_object_rdfs (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdf_Property
  | _ -> false

// OWL-regime class typing: rdfs:Class or owl:Class. Licensed by OWL 2
// RDF-Based Semantics Table 5.3, NOT by RDF 1.1 Semantics section 9.
let is_class_type_object (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdfs_Class || c = owl_Class
  | _ -> false

// OWL-regime property typing: rdf:Property, owl:ObjectProperty or
// owl:DatatypeProperty. Same regime caveat.
let is_property_type_object (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdf_Property || c = owl_ObjectProperty || c = owl_DatatypeProperty
  | _ -> false

// Generic harvest, parameterised by the typing test, so the two regimes
// share one walk and differ only in the predicate they are handed.
let collect_related_iris (typing_ok : rdf_term -> bool) (rel : wf_iri)
                         (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 =
        if t.p = rel
        then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
        else acc
      in
      if t.p = rdf_type && typing_ok t.o
      then cons_subject_iri_if_new t.s acc1
      else acc1)
    []
    g

// RDFS-regime harvests (RS-1 fix).
let collect_classes_rdfs (g : rdf_graph) : list wf_iri =
  collect_related_iris is_class_type_object_rdfs rdfs_subClassOf g

let collect_properties_rdfs (g : rdf_graph) : list wf_iri =
  collect_related_iris is_property_type_object_rdfs rdfs_subPropertyOf g

// OWL-regime harvests. Byte-identical in behaviour to the pre-split
// `collect_classes` / `collect_properties`; OWL.Closure.fsti keeps
// using exactly these, so the OWL-RL regime is unchanged.
let collect_classes (g : rdf_graph) : list wf_iri =
  collect_related_iris is_class_type_object rdfs_subClassOf g

let collect_properties (g : rdf_graph) : list wf_iri =
  collect_related_iris is_property_type_object rdfs_subPropertyOf g

// Build the reflexivity triples (C rdfs:subClassOf C) and
// (P rdfs:subPropertyOf P) from a class list and a property list.
let reflexivity_axioms_of (classes properties : list wf_iri) : rdf_graph =
  let class_triples : rdf_graph =
    List.Tot.map
      (fun (c : wf_iri) -> ({ s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c } <: triple))
      classes
  in
  let property_triples : rdf_graph =
    List.Tot.map
      (fun (p : wf_iri) -> ({ s = S_IRI p; p = rdfs_subPropertyOf; o = T_IRI p } <: triple))
      properties
  in
  class_triples @ property_triples

// RDFS-regime reflexivity axioms. Every emitted triple is licensed by
// RDF 1.1 Semantics section 9 -- proven in
// RDF.Entailment.RDFS.Refinement.rdfs_reflexivity_axioms_licensed.
let rdfs_reflexivity_axioms (g : rdf_graph) : rdf_graph =
  reflexivity_axioms_of (collect_classes_rdfs g) (collect_properties_rdfs g)

// OWL-regime reflexivity axioms. Behaviourally identical to the
// pre-split `rdfs_reflexivity_axioms`; NOT RDFS-sound (that is the
// point of the split), sound under the OWL 2 RDF-Based Semantics.
let owl_reflexivity_axioms (g : rdf_graph) : rdf_graph =
  reflexivity_axioms_of (collect_classes g) (collect_properties g)

// Full RDFS closure with reflexivity axioms: run rdfs_closure, harvest
// classes/properties, add reflexivity triples, then run rdfs_closure
// again. This matches the two-pass behaviour of patch #60.
// The fuel parameter bounds the nested closure iterations; both passes
// share the same fuel budget (the same constant was used in the patch).
//
// AXIOMS SEEDING — ATTEMPTED AND DISABLED PENDING REVIEW (2026-07-05,
// design doc §3.3 step 6, "the Axioms seed-graph gate"). The step-6
// plan wired `RDF.Vocabulary.Axioms.finite_axiomatic_triples` in here
// (`let seeded = add_triples_if_new g finite_axiomatic_triples` before
// the first `rdfs_closure` pass; RDF-regime `rdfs_closure` above
// deliberately left unseeded). Measured result: every suite stayed
// byte-exact EXCEPT OWL 2 profile-RL ConsistencyTests, which dropped
// from 76 pass 0 fail to 75 pass 1 fail — `New-Feature-ObjectQCR-002`
// (a max-qualified-cardinality ontology that IS consistent) became
// "FAIL/unexpected-inconsistency". Mechanism: the seeded rdfs:domain/
// range axioms on core vocabulary (e.g. `rdf:type rdfs:range
// rdfs:Class`) inflate the closure's rdf:type triple set via rdfs2/
// rdfs3, which feeds the N=1 qualified-cardinality complementOf
// scaffolding (`owl_rule_cls_maxqc_comp`, OWL.Closure.fsti) enough
// extra typed members to trip the cls-com clash in `is_inconsistent` —
// i.e. the seed interacts unsoundly with the already-documented
// sound-but-narrow qualified-cardinality rewrites (CLAUDE.md "Known
// sound-but-narrow rewrites", issue #236). Reporting a consistent
// ontology as inconsistent is an unsoundness, not a spec-correct
// improvement, so per the gate the seeding is DISABLED (this function
// is byte-equivalent to its pre-step-6 behaviour) until the #236
// anchor-to-UNION generalisation — or a seeding path that excludes the
// cardinality-rule interaction — lands. RDF.Vocabulary.Axioms stays
// verified, wired into the build, and importable; nothing consumes it
// at runtime yet.
//
// STILL DISABLED after the 2026-07-31 RS-2 work. That work did NOT
// re-attempt the seeding; it implemented five RULE rows instead. The
// distinction matters: the reverted seed injected `rdf:type rdfs:range
// rdfs:Class` and the other ~38 core-vocabulary domain/range rows,
// which is exactly the shape that inflates the rdf:type set through
// rdfs2 / rdfs3 and trips the qualified-cardinality scaffolding. The
// rows added instead emit no domain/range triple at all: rdfs1 emits
// two `<datatype> rdf:type rdfs:Datatype` triples, rdfs8 / rdfs13 emit
// subClassOf edges to rdfs:Resource / rdfs:Literal, and rdfs4a / rdfs4b
// emit `rdf:type rdfs:Resource`. Re-attempting the full seed still
// needs the #236 work.
//
// REGIME SPLIT, 2026-07-31 (RS-1 / #335). This function is the RDFS
// regime's entry point (`entailment_closure`'s "RDFS" branch,
// RIF.Core.Tests' RDF/RDFS regime), so it harvests with the NARROW,
// RDFS-licensed `rdfs_reflexivity_axioms`. The OWL-RL path uses
// `owl_rdfs_closure_with_reflexivity` just below, which keeps the wide
// harvest; OWL-RL behaviour is therefore unchanged by the split.
let rdfs_closure_with_reflexivity (g : rdf_graph) (fuel : nat) : Tot rdf_graph =
  let closed = rdfs_closure g fuel in
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = add_triples_if_new closed refl_axioms in
  rdfs_closure with_refl fuel

// The OWL-regime RDFS pre-pass. Byte-identical to what
// `rdfs_closure_with_reflexivity` did before the RS-1 split: it
// harvests classes/properties through the OWL typing IRIs as well.
// OWL.Closure.fsti's `owl_rl_closure_with_reflexivity_mode` calls this.
let owl_rdfs_closure_with_reflexivity (g : rdf_graph) (fuel : nat) : Tot rdf_graph =
  let closed = rdfs_closure g fuel in
  let refl_axioms = owl_reflexivity_axioms closed in
  let with_refl = add_triples_if_new closed refl_axioms in
  rdfs_closure with_refl fuel

(* RDF entailment rule rdfD2 (https://www.w3.org/TR/rdf11-mt/ §"RDF
   entailment rules"): from any triple `sss ppp ooo`, infer
   `ppp rdf:type rdf:Property`. Applied ONLY under the pure `ent:RDF`
   regime (the runner's "RDF" branch) — kept OUT of rdfs_closure_step so
   it does not perturb the shared RDFS / OWL-RL closure driver. Needed by
   the SPARQL 1.1 entailment test rdf01 ("RDF inference test"). *)
let rdf_property_axiom_of_triple (t : triple) : triple =
  { s = S_IRI t.p; p = rdf_type; o = T_IRI rdf_Property }

let rdf_property_axiom_closure (g : rdf_graph) : Tot rdf_graph =
  let axioms : rdf_graph = List.Tot.map rdf_property_axiom_of_triple g in
  graph_dedup_sort (add_triples_if_new g axioms)
