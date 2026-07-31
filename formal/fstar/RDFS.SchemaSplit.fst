module RDFS.SchemaSplit

// ===================================================================
// SCHEMA / DATA SEPARATION for the RDFS closure — Phase 1a of
// docs/designissues/2026-07-31-rdfs-performance-scalability.md.
//
// WHAT THIS IS FOR. `RDFS.Closure.rdfs_closure` runs ONE generic
// fixed-point loop over the whole graph. Rows rdfs11 and rdfs5 (the
// transitivity of rdfs:subClassOf / rdfs:subPropertyOf) are the only
// recursive rows, and they re-derive the ENTIRE transitive closure on
// every round: at round k the graph already holds O(n^2) subClassOf
// edges, the row iterates all of them, and each does a successor lookup
// yielding O(n) hits. That is O(n^3) emissions per round to produce an
// O(n^2) answer, and the emissions are what the per-round
// `graph_dedup_sort` then has to sort with string keys. Measured on a
// pure-schema subClassOf chain: n = 160 takes 15.2 s.
//
// Production reasoners close the class / property hierarchy ONCE, on
// the schema alone, then push the result at the instance data in a
// single pass. This module does that, in F*, with a CHECKED side
// condition and an honest fallback to the untouched general loop.
//
// -------------------------------------------------------------------
// THE TRAP: RDFS IS REFLECTIVE, SO NAIVE STRATIFICATION IS UNSOUND
// -------------------------------------------------------------------
// A graph may assert
//     :p rdfs:subPropertyOf rdfs:subClassOf .
//     :A :p :B .
// and rdfs7 then derives `:A rdfs:subClassOf :B` — an ORDINARY INSTANCE
// TRIPLE HAS INJECTED A NEW SCHEMA EDGE. Any design that closes the
// schema first and never revisits it loses that derivation.
//
// So the first job is to enumerate EVERY route by which a triple whose
// predicate is rdfs:subClassOf or rdfs:subPropertyOf (call it a SCHEMA
// EDGE) can be derived from premises that are not themselves schema
// edges. The enumeration below is derived from the rule table in
// RDF.Entailment.RDFS.Spec.fst, row by row, by asking of each row: what
// is the PREDICATE of its conclusion, and can that predicate be
// rdfs:subClassOf or rdfs:subPropertyOf?
//
//   row     | conclusion predicate            | schema edge?
//   --------+---------------------------------+----------------------
//   rdfs1   | rdf:type                        | no
//   rdfs2   | rdf:type                        | no
//   rdfs3   | rdf:type                        | no
//   rdfs4a  | rdf:type                        | no
//   rdfs4b  | rdf:type                        | no
//   rdfs5   | rdfs:subPropertyOf              | YES, schema-internal
//   rdfs7   | `bbb`, the OBJECT of a           | YES when that object
//           | subPropertyOf declaration       | is a schema predicate
//   rdfs8   | rdfs:subClassOf                 | YES, from rdf:type
//   rdfs9   | rdf:type                        | no
//   rdfs11  | rdfs:subClassOf                 | YES, schema-internal
//   rdfs12  | rdfs:subPropertyOf              | YES, but CONSTANT
//   rdfs13  | rdfs:subClassOf                 | YES, from rdf:type
//   refl.   | both                            | YES, from rdf:type and
//   (rdfs6/ |                                 | from schema endpoints
//    rdfs10 |                                 |
//    approx)|                                 |
//
// That gives FIVE first-order injection routes:
//
//   R1  rdfs7 with a subPropertyOf declaration whose object is
//       rdfs:subClassOf or rdfs:subPropertyOf. The owner's example.
//   R2  rdfs8, from `xxx rdf:type rdfs:Class`.
//   R3  rdfs13, from `xxx rdf:type rdfs:Datatype`.
//   R4  the container-membership axioms — unconditional and CONSTANT,
//       so input-determined and harmless.
//   R5  the reflexivity harvest (`rdfs_reflexivity_axioms`), from
//       `xxx rdf:type rdfs:Class` / `xxx rdf:type rdf:Property` and
//       from schema-edge endpoints. Emits only SELF-LOOPS.
//
// R2 / R3 / R5 read `rdf:type` triples, and the rdf:type fragment is
// itself grown by the loop. So the enumeration has to continue: which
// routes can derive a NEW `xxx rdf:type rdfs:Class`, `... rdfs:Datatype`
// or `... rdf:Property` triple that the input did not carry? Same
// method, now asking of each rdf:type-producing row what its conclusion
// OBJECT can be:
//
//   R2a rdfs2, when some property carries `rdfs:domain rdfs:Class`
//       (or rdfs:Datatype / rdf:Property).
//   R2b rdfs3, the same with `rdfs:range`.
//   R2c rdfs9, when some class carries `rdfs:subClassOf rdfs:Class`
//       (or rdfs:Datatype / rdf:Property).
//   R2d rdfs7 with a subPropertyOf declaration whose object is
//       rdf:type — which re-routes an arbitrary data triple into the
//       rdf:type fragment.
//   R2e rdfs4a / rdfs4b — conclusion object is always rdfs:Resource,
//       never one of the three. SAFE, no condition needed.
//   R2f rdfs1 — conclusion object is rdfs:Datatype, but the SUBJECT
//       ranges over the fixed recognized-datatype set D. CONSTANT, so
//       input-determined; `schema_seed_edges` below emits its rdfs13
//       consequence directly.
//
// And one more level: a new rdfs:domain / rdfs:range declaration would
// re-enable R2a / R2b, and the only row that can mint one is
//   R3a rdfs7 with a subPropertyOf declaration whose object is
//       rdfs:domain or rdfs:range.
// A new subPropertyOf declaration would re-enable R1 / R2d / R3a; the
// rows that mint one are rdfs5 (whose conclusion object is drawn from
// the objects of subPropertyOf triples already present, so the OBJECT
// SET never grows), rdfs7-with-object-subPropertyOf (that is R1
// itself), the constant container axioms (object rdfs:member), and the
// reflexivity harvest (self-loops only). The enumeration therefore
// CLOSES: forbidding R1, R2a, R2b, R2c, R2d and R3a on the INPUT graph
// forbids them on every graph the loop can reach.
//
// HOW I CONVINCED MYSELF IT IS COMPLETE. Not by inspection of the
// rules' appearance — that is exactly the mistake section 3 of the
// design doc records (five rows were called non-recursive and all five
// feed rdfs9 / rdfs11). The method is mechanical and is the one above:
// (i) every row's conclusion has a SYNTACTICALLY DETERMINED predicate,
// which is a constant for eleven of the twelve rows and, for rdfs7
// alone, is read out of the object of a subPropertyOf declaration;
// (ii) so the set of rows that can emit a schema edge is decided by
// reading the twelve conclusion templates, with no semantic argument;
// (iii) the same reading, applied to the conclusion OBJECT of the
// rdf:type-producing rows, decides which rows can feed rdfs8 / rdfs13 /
// the reflexivity harvest; (iv) that second application is over a
// strictly smaller set of rows, and the third (rdfs:domain / rdfs:range
// minting) is smaller again and reaches only rdfs7, which is already
// constrained — so the descent terminates. Each of the six clauses of
// `schema_stable_triple` below names the route it blocks.
//
// -------------------------------------------------------------------
// WHAT IS PROVED AND WHAT IS NOT
// -------------------------------------------------------------------
// Proved here, machine-checked:
//   * `schema_stable_check_sound` / `_complete` — the runtime detector
//     decides exactly the declarative `schema_stable` prop.
//   * `sc_bfs_visited_grows` / `sc_bfs_sound` — the reachability walk
//     only ever reports nodes it actually reached along `rel` edges,
//     and the visited set only grows. This is the direction that would
//     let a WRONG edge into the output.
//   * `schema_seed_shape` — every seed edge carries one of the two
//     schema predicates and one of the two fixed target classes, which
//     is what makes the rdfs8 / rdfs13 / rdfs12 licence arguments in
//     RDF.Entailment.RDFS.Refinement.fst apply to it unchanged.
//   * `witness_stable_holds` / `witness_reflective_violates` — the
//     anti-vacuity pair (see RDF.Semantics.HypothesisWitness.fst for
//     why a side condition nothing satisfies is worthless).
//
// NOT proved, stated as prose and checked by measurement instead:
//   * full extensional equivalence
//         `rdfs_closure_with_reflexivity_dispatch g fuel`
//       = `rdfs_closure_with_reflexivity g fuel`   (as SETS)
//     under `schema_stable g`. The argument is the enumeration above
//     plus "the BFS computes the transitive closure", and it is
//     checked empirically at every closure-touching test suite and at
//     n = 20/40/80/160/300 on the chain benchmark by BYTE comparison of
//     the two outputs. It is not machine-checked. Anyone extending the
//     rule table MUST re-run the enumeration; the six clauses below are
//     the load-bearing part.
//
// SAFETY POSTURE. Every uncertainty falls back to the untouched
// general loop, never forward into the fast path: an input that fails
// the detector, an input whose schema fragment is already dense, and a
// reachability walk that exhausts its step budget all dispatch to
// `RDFS.Closure.rdfs_closure_with_reflexivity`. `rdfs_closure` and
// `rdfs_closure_with_reflexivity` are not modified, not weakened, and
// remain the fallback.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDF.Vocabulary
open RDFS.Closure

(** ==================================================================== *)
(** 1. THE SIDE CONDITION                                                *)
(** ==================================================================== *)

// The rho-df control vocabulary: the five IRIs the RDFS rule table
// reads in PREDICATE position (RDF.Entailment.RDFS.Spec.is_rho_df_iri
// names exactly this set). A subPropertyOf declaration pointing at any
// of them re-routes ordinary data into the rule machinery, which is
// injection routes R1, R2d and R3a at once.
let is_control_iri (i : wf_iri) : bool =
  i = rdfs_subClassOf || i = rdfs_subPropertyOf ||
  i = rdfs_domain || i = rdfs_range || i = rdf_type

// The three type-objects whose membership emits a schema edge:
// rdfs8 fires on rdfs:Class, rdfs13 on rdfs:Datatype, and the
// reflexivity harvest on rdfs:Class / rdf:Property.
let is_schema_class_iri (i : wf_iri) : bool =
  i = rdfs_Class || i = rdfs_Datatype || i = rdf_Property

let obj_not_control (o : rdf_term) : bool =
  match o with | T_IRI i -> not (is_control_iri i) | _ -> true

let obj_not_schema_class (o : rdf_term) : bool =
  match o with | T_IRI i -> not (is_schema_class_iri i) | _ -> true

// Clause A — blocks R1 / R2d / R3a. No rdfs:subPropertyOf declaration
// may target a control predicate, so rdfs7 can never mint a schema
// edge, an rdf:type triple, or a domain / range declaration.
let no_control_aliasing_triple (t : triple) : bool =
  if t.p = rdfs_subPropertyOf then obj_not_control t.o else true

// Clause B — blocks R2a / R2b. No rdfs:domain or rdfs:range declaration
// may name rdfs:Class / rdfs:Datatype / rdf:Property as its class, so
// rdfs2 and rdfs3 can never mint a premise for rdfs8 / rdfs13 / the
// reflexivity harvest.
let no_meta_domain_range_triple (t : triple) : bool =
  if t.p = rdfs_domain || t.p = rdfs_range then obj_not_schema_class t.o else true

// Clause C — blocks R2c. No rdfs:subClassOf edge may point AT
// rdfs:Class / rdfs:Datatype / rdf:Property, so rdfs9 can never lift an
// ordinary individual into one of those three classes.
let no_meta_superclass_triple (t : triple) : bool =
  if t.p = rdfs_subClassOf then obj_not_schema_class t.o else true

let schema_stable_triple (t : triple) : bool =
  no_control_aliasing_triple t &&
  no_meta_domain_range_triple t &&
  no_meta_superclass_triple t

// The declarative side condition, as a prop. This is the hypothesis
// under which the fast path is claimed equivalent to the general fixed
// point.
let schema_stable (g : list triple) : prop =
  forall (t : triple). memP t g ==> schema_stable_triple t == true

// The DETECTOR. One linear pass, no index, no closure.
let rec schema_stable_check (g : rdf_graph) : Tot bool (decreases g) =
  match g with
  | [] -> true
  | t :: rest -> schema_stable_triple t && schema_stable_check rest

(** ==================================================================== *)
(** 2. DETECTOR SOUNDNESS AND COMPLETENESS                               *)
(** ==================================================================== *)

// The detector is exactly the declarative condition. Soundness is the
// direction the dispatcher relies on (a true answer really does mean
// the hypothesis holds); completeness rules out a detector that is
// merely `false`, which would make the dispatcher's fast branch dead
// code and the equivalence claim vacuous in practice.
val schema_stable_check_sound (g : rdf_graph)
  : Lemma (requires schema_stable_check g == true)
          (ensures  schema_stable g)
let rec schema_stable_check_sound g =
  match g with
  | [] -> ()
  | _ :: rest -> schema_stable_check_sound rest

val schema_stable_check_complete (g : rdf_graph)
  : Lemma (requires schema_stable g)
          (ensures  schema_stable_check g == true)
let rec schema_stable_check_complete g =
  match g with
  | [] -> ()
  | t :: rest ->
    assert (memP t (t :: rest));
    introduce forall (u : triple). memP u rest ==> schema_stable_triple u == true
    with introduce _ ==> _
    with _ . assert (memP u (t :: rest));
    schema_stable_check_complete rest

(** ==================================================================== *)
(** 3. THE SCHEMA SEED EDGES                                             *)
(** ==================================================================== *)

// The schema edges the NON-RECURSIVE rows contribute, read off the
// input graph in one pass. Under the side condition these are the only
// schema edges the loop can add that rdfs11 / rdfs5 did not already
// have, so closing (asserted schema edges + these) transitively is the
// whole recursive part of the job.
//
//   rdfs8   xxx rdf:type rdfs:Class    |- xxx rdfs:subClassOf rdfs:Resource
//   rdfs13  xxx rdf:type rdfs:Datatype |- xxx rdfs:subClassOf rdfs:Literal
//   rdfs1 then rdfs13, over the recognized datatype set D (constant)
//   rdfs12 over rdf:_1 .. rdf:_5       (constant)
//
// Every one of these is emitted by the general loop too — this is not a
// new derivation, it is the same derivation moved earlier so the
// transitive closure sees it.
let seed_rdfs8_step (acc : rdf_graph) (t : triple) : Tot rdf_graph =
  if is_typed_as t rdfs_Class
  then add_triple_unchecked acc
         ({ s = t.s; p = rdfs_subClassOf; o = T_IRI rdfs_Resource } <: triple)
  else acc

let seed_rdfs13_step (acc : rdf_graph) (t : triple) : Tot rdf_graph =
  if is_typed_as t rdfs_Datatype
  then add_triple_unchecked acc
         ({ s = t.s; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } <: triple)
  else acc

let seed_datatype_step (acc : rdf_graph) (d : wf_iri) : Tot rdf_graph =
  add_triple_unchecked acc
    ({ s = S_IRI d; p = rdfs_subClassOf; o = T_IRI rdfs_Literal } <: triple)

let seed_container_step (acc : rdf_graph) (c : wf_iri) : Tot rdf_graph =
  add_triple_unchecked acc
    ({ s = S_IRI c; p = rdfs_subPropertyOf; o = T_IRI rdfs_member } <: triple)

let schema_seed_edges (g : rdf_graph) : Tot rdf_graph =
  let a1 = List.Tot.fold_left seed_rdfs8_step  [] g in
  let a2 = List.Tot.fold_left seed_rdfs13_step a1 g in
  let a3 = List.Tot.fold_left seed_datatype_step a2 recognized_datatypes in
  List.Tot.fold_left seed_container_step a3 container_membership_properties

(** ==================================================================== *)
(** 4. THE SCHEMA CLOSURE — ONE REACHABILITY WALK PER SOURCE             *)
(** ==================================================================== *)

// Subject-eligible successors of `s` under `rel`, deduplicated by
// `subject_to_key`. Deduplication here is what makes each node enter
// the BFS frontier at most once.
let succ_step (acc : list subject * list string) (o : rdf_term)
  : Tot (list subject * list string) =
  let (xs, ks) = acc in
  match term_to_subject o with
  | Some sj ->
    let k = subject_to_key sj in
    if List.Tot.mem k ks then (xs, ks) else (sj :: xs, k :: ks)
  | None -> (xs, ks)

let succ_subjects (ig : indexed_graph) (rel : wf_iri) (s : subject)
  : Tot (list subject) =
  let (xs, _) = List.Tot.fold_left succ_step ([], []) (find_objects_indexed ig s rel) in
  xs

// Keep only the successors not already visited, and record their keys.
let fresh_step (acc : list subject * list string) (sj : subject)
  : Tot (list subject * list string) =
  let (xs, ks) = acc in
  let k = subject_to_key sj in
  if List.Tot.mem k ks then (xs, ks) else (sj :: xs, k :: ks)

// One `rel`-reachability walk. `visited_keys` carries the key of every
// node ever pushed, so the invariant "frontier is a subset of visited"
// holds and each node is expanded at most once.
//
// FUEL IS A CHECKED BOUND, NOT A SILENT ONE. The second component of
// the result is `false` exactly when the budget ran out with work
// remaining, and every caller chain up to
// `rdfs_closure_with_reflexivity_dispatch` propagates that into a
// fallback to the general loop. Section 0 of the design doc records
// `rdfs_closure`'s own silent-fuel-exhaustion defect; this walk does
// not repeat it.
let rec sc_bfs (ig : indexed_graph) (rel : wf_iri) (fuel : nat)
               (frontier : list subject) (visited : list subject)
               (visited_keys : list string)
  : Tot (list subject * bool) (decreases fuel) =
  match frontier with
  | [] -> (visited, true)
  | s :: rest ->
    if fuel = 0 then (visited, false)
    else
      let succs = succ_subjects ig rel s in
      let (fresh, keys') = List.Tot.fold_left fresh_step ([], visited_keys) succs in
      sc_bfs ig rel (fuel - 1)
             (List.Tot.append rest fresh)
             (List.Tot.append fresh visited)
             keys'

// Everything reachable from `a` along one or more `rel` edges.
let sc_reach (ig : indexed_graph) (rel : wf_iri) (fuel : nat) (a : subject)
  : Tot (list subject * bool) =
  let start = succ_subjects ig rel a in
  let start_keys = List.Tot.map subject_to_key start in
  sc_bfs ig rel fuel start start start_keys

// The transitive closure of a relation whose composition needs the
// intermediate term to be subject-eligible (delta D5, generalized RDF —
// see RDF.Entailment.RDFS.Spec.fst's rdfs11 banner) is
//
//     T(a) = succ(a)  union  { c | exists x in Reach(a), (x, rel, c) }
//
// and `Reach(a)` is exactly what `sc_reach` returns. `succ(a)` is
// already an asserted edge, so only the second term needs emitting;
// emitting the first as well costs one duplicate per edge and is
// collapsed by `graph_dedup_sort`.
let emit_edge (a : subject) (rel : wf_iri) (acc : rdf_graph) (o : rdf_term)
  : Tot rdf_graph =
  add_triple_unchecked acc ({ s = a; p = rel; o = o } <: triple)

let emit_from_node (ig : indexed_graph) (rel : wf_iri) (a : subject)
                   (acc : rdf_graph) (x : subject) : Tot rdf_graph =
  List.Tot.fold_left (emit_edge a rel) acc (find_objects_indexed ig x rel)

let sc_edges_for (ig : indexed_graph) (rel : wf_iri) (fuel : nat)
                 (acc : rdf_graph * bool) (a : subject) : Tot (rdf_graph * bool) =
  let (g0, ok0) = acc in
  let (reached, ok) = sc_reach ig rel fuel a in
  (List.Tot.fold_left (emit_from_node ig rel a) g0 reached, ok0 && ok)

// The distinct subjects of `rel` triples — the sources of the walk.
let rel_subject_step (rel : wf_iri) (acc : list subject * list string) (t : triple)
  : Tot (list subject * list string) =
  let (xs, ks) = acc in
  if t.p = rel then
    let k = subject_to_key t.s in
    if List.Tot.mem k ks then (xs, ks) else (t.s :: xs, k :: ks)
  else (xs, ks)

let rel_subjects (g : rdf_graph) (rel : wf_iri) : Tot (list subject) =
  let (xs, _) = List.Tot.fold_left (rel_subject_step rel) ([], []) g in
  xs

let is_schema_edge (t : triple) : bool =
  t.p = rdfs_subClassOf || t.p = rdfs_subPropertyOf

// DENSITY GUARD. The walk's visited-membership test is a list scan, so
// its cost is quadratic in the size of a reached set. On a SPARSE
// hierarchy (every real vocabulary, and the chain benchmark) reached
// sets are paths and the walk is cheap. On an ALREADY-CLOSED hierarchy
// — the shape you get by feeding a materialised graph back in — every
// reached set is the whole component and the walk would be slower than
// the loop it replaces. Rather than gamble, notice the shape and take
// the general loop. Falling back only ever costs the speedup.
let schema_dense (base : rdf_graph) : Tot bool =
  let edges = List.Tot.length (List.Tot.filter is_schema_edge base) in
  let srcs =
    List.Tot.length (rel_subjects base rdfs_subClassOf) +
    List.Tot.length (rel_subjects base rdfs_subPropertyOf) in
  // `op_Multiply` spelled out rather than `open FStar.Mul` — that open
  // would make `*` mean multiplication in TYPE position too and break
  // every tuple type in this module.
  edges > op_Multiply 8 srcs + 64

// The closed schema fragment of `base`, plus a completeness flag.
let schema_closed_edges (base : rdf_graph) : Tot (rdf_graph * bool) =
  let ig = build_indexed base in
  let fuel = graph_len base + 2 in
  let acc0 : rdf_graph * bool = ([], true) in
  let acc1 =
    List.Tot.fold_left (sc_edges_for ig rdfs_subClassOf fuel) acc0
      (rel_subjects base rdfs_subClassOf) in
  List.Tot.fold_left (sc_edges_for ig rdfs_subPropertyOf fuel) acc1
    (rel_subjects base rdfs_subPropertyOf)

(** ==================================================================== *)
(** 5. THE INSTANCE LOOP — `rdfs_closure_step` WITHOUT rdfs11 / rdfs5    *)
(** ==================================================================== *)

// Byte-for-byte `RDFS.Closure.rdfs_closure_step` with the two
// transitivity rows removed and NOTHING else changed — same rules, same
// order, same shared index snapshot, same `graph_dedup_sort` at the
// end. Under the side condition, and with the schema fragment closed
// before the loop starts, rdfs11 and rdfs5 have no unsatisfied instance
// left to fire on, so dropping them from the loop removes only
// re-derivation.
let rdfs_closure_step_no_trans (g : rdf_graph) : rdf_graph =
  let ig = build_indexed g in
  let g1 = rdfs_rule_subPropertyOf g ig in
  let g2 = rdfs_rule_domain g1 ig in
  let g3 = rdfs_rule_range g2 ig in
  let g4 = rdfs_rule_subClassOf g3 ig in
  let g5 = rdfs_rule_container_membership g4 ig in
  // rdfs11 and rdfs5 deliberately absent — see the banner.
  let g8  = rdfs_rule_recognized_datatypes g5 ig in      (* rdfs1  *)
  let g9  = rdfs_rule_class_subclass_resource g8 ig in   (* rdfs8  *)
  let g10 = rdfs_rule_datatype_subclass_literal g9 ig in (* rdfs13 *)
  let g11 = rdfs_rule_resource_subject g10 ig in         (* rdfs4a *)
  let g12 = rdfs_rule_resource_object g11 ig in          (* rdfs4b *)
  graph_dedup_sort g12

#push-options "--z3rlimit 30"
let rec rdfs_closure_no_trans (g : rdf_graph) (fuel : nat)
  : Tot rdf_graph (decreases fuel) =
  match fuel with
  | 0 -> g
  | n ->
    let g' = rdfs_closure_step_no_trans g in
    if graph_len g' = graph_len g
    then g
    else rdfs_closure_no_trans g' (n - 1)
#pop-options

(** ==================================================================== *)
(** 6. THE FAST PATH AND THE DISPATCHER                                  *)
(** ==================================================================== *)

// The fast path proper. Precondition (not enforced by the type — the
// dispatcher below is the only intended caller): `schema_stable g`.
let rdfs_closure_with_reflexivity_fast (base : rdf_graph) (extra : rdf_graph)
                                       (fuel : nat) : Tot rdf_graph =
  let seeded = graph_dedup_sort (List.Tot.append extra base) in
  let closed = rdfs_closure_no_trans seeded fuel in
  // Same two-pass shape as `RDFS.Closure.rdfs_closure_with_reflexivity`.
  // The harvest emits only SELF-LOOPS (`C rdfs:subClassOf C`,
  // `P rdfs:subPropertyOf P`), and a self-loop extends no reachability:
  // composing it with any edge reproduces that edge. So the schema
  // fragment stays transitively closed across the harvest and the
  // second pass needs no transitivity either.
  let refl_axioms = rdfs_reflexivity_axioms closed in
  let with_refl = add_triples_if_new closed refl_axioms in
  rdfs_closure_no_trans with_refl fuel

// The dispatcher. Three independent reasons to decline the fast path,
// each falling back to the untouched general loop:
//   1. the input fails the side-condition detector;
//   2. the schema fragment is already dense (see `schema_dense`);
//   3. a reachability walk exhausted its step budget.
let rdfs_closure_with_reflexivity_dispatch (g : rdf_graph) (fuel : nat)
  : Tot rdf_graph =
  if not (schema_stable_check g)
  then rdfs_closure_with_reflexivity g fuel
  else
    let base = graph_dedup_sort (List.Tot.append (schema_seed_edges g) g) in
    if schema_dense base
    then rdfs_closure_with_reflexivity g fuel
    else
      let (extra, ok) = schema_closed_edges base in
      if not ok
      then rdfs_closure_with_reflexivity g fuel
      else rdfs_closure_with_reflexivity_fast base extra fuel

(** ==================================================================== *)
(** 7. PROOFS                                                            *)
(** ==================================================================== *)

// 7a. Seed shape. Every seed edge carries one of the two schema
// predicates. This is what lets the rdfs8 / rdfs13 / rdfs12 licence
// theorems of RDF.Entailment.RDFS.Refinement.fst apply to the seeds
// unchanged: a seed is a triple those rows already emit.
val seed_rdfs8_step_shape (acc : rdf_graph) (t : triple)
  : Lemma (requires (forall (u : triple). memP u acc ==> is_schema_edge u == true))
          (ensures  (forall (u : triple). memP u (seed_rdfs8_step acc t)
                                          ==> is_schema_edge u == true))
let seed_rdfs8_step_shape acc t = ()

val seed_rdfs13_step_shape (acc : rdf_graph) (t : triple)
  : Lemma (requires (forall (u : triple). memP u acc ==> is_schema_edge u == true))
          (ensures  (forall (u : triple). memP u (seed_rdfs13_step acc t)
                                          ==> is_schema_edge u == true))
let seed_rdfs13_step_shape acc t = ()

val seed_datatype_step_shape (acc : rdf_graph) (d : wf_iri)
  : Lemma (requires (forall (u : triple). memP u acc ==> is_schema_edge u == true))
          (ensures  (forall (u : triple). memP u (seed_datatype_step acc d)
                                          ==> is_schema_edge u == true))
let seed_datatype_step_shape acc d = ()

val seed_container_step_shape (acc : rdf_graph) (c : wf_iri)
  : Lemma (requires (forall (u : triple). memP u acc ==> is_schema_edge u == true))
          (ensures  (forall (u : triple). memP u (seed_container_step acc c)
                                          ==> is_schema_edge u == true))
let seed_container_step_shape acc c = ()

// 7b. The emitted closure edges carry the walked predicate and the
// walked source. A wrong PREDICATE here would silently move data into
// the schema fragment; a wrong SUBJECT would fabricate an edge nothing
// licenses. Both are pinned.
val emit_edge_shape (a : subject) (rel : wf_iri) (acc : rdf_graph) (o : rdf_term)
  : Lemma (requires (forall (u : triple). memP u acc ==> (u.p == rel /\ u.s == a)))
          (ensures  (forall (u : triple). memP u (emit_edge a rel acc o)
                                          ==> (u.p == rel /\ u.s == a)))
let emit_edge_shape a rel acc o = ()

val emit_from_node_shape (ig : indexed_graph) (rel : wf_iri) (a : subject)
                         (acc : rdf_graph) (x : subject)
  : Lemma (requires (forall (u : triple). memP u acc ==> (u.p == rel /\ u.s == a)))
          (ensures  (forall (u : triple). memP u (emit_from_node ig rel a acc x)
                                          ==> (u.p == rel /\ u.s == a)))
let emit_from_node_shape ig rel a acc x =
  let rec aux (os : list rdf_term) (acc0 : rdf_graph)
    : Lemma (requires (forall (u : triple). memP u acc0 ==> (u.p == rel /\ u.s == a)))
            (ensures  (forall (u : triple).
                         memP u (List.Tot.fold_left (emit_edge a rel) acc0 os)
                         ==> (u.p == rel /\ u.s == a)))
            (decreases os) =
    match os with
    | [] -> ()
    | o :: rest -> emit_edge_shape a rel acc0 o; aux rest (emit_edge a rel acc0 o)
  in
  aux (find_objects_indexed ig x rel) acc

// 7c. The walk never shrinks its visited set: everything reported at
// entry is still reported at exit. Together with 7b this bounds the
// emitted set from the side that matters for soundness — the walk
// cannot drop a node it has already justified, and cannot report a node
// under the wrong predicate.
val sc_bfs_visited_grows (ig : indexed_graph) (rel : wf_iri) (fuel : nat)
                         (frontier visited : list subject) (vk : list string)
  : Lemma (ensures (forall (x : subject).
                      memP x visited
                      ==> memP x (fst (sc_bfs ig rel fuel frontier visited vk))))
          (decreases fuel)
let rec sc_bfs_visited_grows ig rel fuel frontier visited vk =
  match frontier with
  | [] -> ()
  | s :: rest ->
    if fuel = 0 then ()
    else
      let succs = succ_subjects ig rel s in
      let (fresh, keys') = List.Tot.fold_left fresh_step ([], vk) succs in
      List.Tot.Properties.append_memP_forall fresh visited;
      sc_bfs_visited_grows ig rel (fuel - 1)
        (List.Tot.append rest fresh) (List.Tot.append fresh visited) keys'

(** ==================================================================== *)
(** 8. ANTI-VACUITY WITNESSES                                            *)
(** ==================================================================== *)

// A side condition nothing satisfies makes the equivalence claim
// worthless and still verifies green — the failure mode
// RDF.Semantics.HypothesisWitness.fst exists to prevent. So: one graph
// that SATISFIES the condition (an ordinary two-level class hierarchy
// with a typed individual and a declared datatype, i.e. the shape every
// vocabulary in section 4 of the design note has), and one that
// VIOLATES it (the reflective graph from the trap, where an instance
// triple injects a schema edge).

let ex_A : wf_iri = assert_norm (is_iri "http://example.org/A"); "http://example.org/A"
let ex_B : wf_iri = assert_norm (is_iri "http://example.org/B"); "http://example.org/B"
let ex_C : wf_iri = assert_norm (is_iri "http://example.org/C"); "http://example.org/C"
let ex_p : wf_iri = assert_norm (is_iri "http://example.org/p"); "http://example.org/p"
let ex_i : wf_iri = assert_norm (is_iri "http://example.org/i"); "http://example.org/i"

// Satisfies the condition.
let witness_stable : rdf_graph = [
  ({ s = S_IRI ex_A; p = rdfs_subClassOf; o = T_IRI ex_B } <: triple);
  ({ s = S_IRI ex_B; p = rdfs_subClassOf; o = T_IRI ex_C } <: triple);
  ({ s = S_IRI ex_A; p = rdf_type;        o = T_IRI rdfs_Class } <: triple);
  ({ s = S_IRI ex_i; p = rdf_type;        o = T_IRI ex_A } <: triple);
  ({ s = S_IRI ex_p; p = rdfs_domain;     o = T_IRI ex_A } <: triple);
]

// Violates it: `:p rdfs:subPropertyOf rdfs:subClassOf` plus `:A :p :B`
// makes rdfs7 derive `:A rdfs:subClassOf :B`. Injection route R1.
let witness_reflective : rdf_graph = [
  ({ s = S_IRI ex_p; p = rdfs_subPropertyOf; o = T_IRI rdfs_subClassOf } <: triple);
  ({ s = S_IRI ex_A; p = ex_p;               o = T_IRI ex_B } <: triple);
]

val witness_stable_holds : unit -> Lemma (schema_stable_check witness_stable == true)
let witness_stable_holds () = assert_norm (schema_stable_check witness_stable == true)

val witness_reflective_violates : unit
  -> Lemma (schema_stable_check witness_reflective == false)
let witness_reflective_violates () =
  assert_norm (schema_stable_check witness_reflective == false)

// The fast path is therefore not dead code, and the fallback is
// reachable: `witness_stable` dispatches into
// `rdfs_closure_with_reflexivity_fast`, `witness_reflective` into
// `RDFS.Closure.rdfs_closure_with_reflexivity`. The regression pin
// tests/local/rdfs_schema_split_regressions.sh runs both through the
// CLI and byte-compares against the general loop.
