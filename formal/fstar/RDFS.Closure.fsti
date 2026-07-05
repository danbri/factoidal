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
// Plus the reflexivity axioms of rdfs4a/4b-adjacent subClassOf/
// subPropertyOf (every class/property collected from the graph is
// related to itself — `rdfs_reflexivity_axioms`), which mirrors the
// pre-F* OCaml patch #60 this block replaced (see the block's own
// comment below).
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
let rdfs_rule_subPropertyOf (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let decls = bucket_lookup ig.ig_pred rdfs_subPropertyOf in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (decl : triple) ->
      match decl.s, decl.o with
      | S_IRI p, T_IRI q ->
        let matching = bucket_lookup ig.ig_pred p in
        List.Tot.fold_left
          (fun (acc2 : rdf_graph) (t : triple) ->
            let new_t : triple = { s = t.s; p = q; o = t.o } in
            add_triple_unchecked acc2 new_t)
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
            let new_t : triple = { s = t.s; p = rdf_type; o = decl.o } in
            add_triple_unchecked acc2 new_t)
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
            | Some b_subj ->
              let new_t : triple = { s = b_subj; p = rdf_type; o = decl.o } in
              add_triple_unchecked acc2 new_t
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
              let new_t : triple = { s = t.s; p = rdf_type; o = b_term } in
              add_triple_unchecked acc2 new_t)
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
  (* #259 followup: each rule now emits duplicates via add_triple_unchecked
     (O(1) prepend). One sort-and-collapse pass here restores set semantics
     for the fixed-point check below and any downstream consumer. O(N log N)
     beats the per-insert O(N) membership scan that previously dominated
     RDFS closure on the lifesci-scale 27K-triple disease graph. *)
  graph_dedup_sort g7

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

// Is the triple's object one of the class-typing IRIs (rdfs:Class or
// owl:Class)?
let is_class_type_object (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdfs_Class || c = owl_Class
  | _ -> false

// Is the triple's object one of the property-typing IRIs (rdf:Property,
// owl:ObjectProperty, owl:DatatypeProperty)?
let is_property_type_object (o : rdf_term) : bool =
  match o with
  | T_IRI c -> c = rdf_Property || c = owl_ObjectProperty || c = owl_DatatypeProperty
  | _ -> false

// Walk a graph and gather every IRI that should be treated as a class
// for the reflexivity of rdfs:subClassOf. Matches patch #60 behaviour
// exactly: collect subjects and IRI-objects of rdfs:subClassOf triples,
// plus subjects of (rdf:type rdfs:Class) and (rdf:type owl:Class).
let collect_classes (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 =
        if t.p = rdfs_subClassOf
        then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
        else acc
      in
      if t.p = rdf_type && is_class_type_object t.o
      then cons_subject_iri_if_new t.s acc1
      else acc1)
    []
    g

// Same for properties.
let collect_properties (g : rdf_graph) : list wf_iri =
  List.Tot.fold_left
    (fun (acc : list wf_iri) (t : triple) ->
      let acc1 =
        if t.p = rdfs_subPropertyOf
        then cons_term_iri_if_new t.o (cons_subject_iri_if_new t.s acc)
        else acc
      in
      if t.p = rdf_type && is_property_type_object t.o
      then cons_subject_iri_if_new t.s acc1
      else acc1)
    []
    g

// Build the reflexivity triples (C rdfs:subClassOf C) and
// (P rdfs:subPropertyOf P) for every class C and property P in g.
let rdfs_reflexivity_axioms (g : rdf_graph) : rdf_graph =
  let classes = collect_classes g in
  let properties = collect_properties g in
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
let rdfs_closure_with_reflexivity (g : rdf_graph) (fuel : nat) : Tot rdf_graph =
  let closed = rdfs_closure g fuel in
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = add_triples_if_new closed refl_axioms in
  rdfs_closure with_refl fuel
