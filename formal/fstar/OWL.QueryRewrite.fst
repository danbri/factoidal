module OWL.QueryRewrite

// Phase 3+4 of the entailment plan (docs/designissues/2026-04-23-entailment-plan.md):
// query-class-expression rewrite for owl:intersectionOf and
// owl:unionOf anonymous class expressions that appear as the object of
// rdf:type in a SPARQL WHERE clause.
//
// Target tests (entailment suite):
//   Phase 3 (flat):   simple1, simple4, paper-sparqldl-Q2.
//   Phase 4 (nested): simple7 — intersection whose operand is itself
//                     a union-of-named-classes bnode. The tests simple2,
//                     simple3, simple5, simple6, simple8 also involve
//                     nested CE, but every one of them has a restriction
//                     (owl:Restriction / someValuesFrom / allValuesFrom)
//                     somewhere in the tree. Rewriting those requires
//                     cooperating with canonical-bnode materialisation
//                     from RDF.Graph.Executable.owl_rl_closure_step,
//                     which doesn't yet cover the nested-CE cases
//                     (intersection-of / union-of inside someValuesFrom).
//                     Those cases are explicitly deferred to Phase 5.
//
// Shape handled in this module (flat only — Phase 4 handles nesting):
//     ?x rdf:type _:c .
//     _:c owl:intersectionOf ( :A :B ... :Cn ) .
// is rewritten to
//     ?x rdf:type :A . ?x rdf:type :B . ... ?x rdf:type :Cn .
//
// and
//     ?x rdf:type _:c .
//     _:c owl:unionOf ( :B :C ... :Cn ) .
// is rewritten to
//     { ?x rdf:type :B } UNION { ?x rdf:type :C } UNION ...
//
// The rewriter is a pure AST pass over SPARQL11.Algebra's
// group_graph_pattern. It runs BEFORE evaluator dispatch so that the
// Datalog/OWL-RL closure already has the named-class rdf:type triples
// to match against.
//
// Soundness: this rewrite is sound under OWL-Direct-Semantics for flat
// class expressions built exclusively from named classes and the two
// boolean combinators. It is NOT sound under RDF-Based entailment
// (unionOf in RDF-Based is just a set description, not a class
// equivalence), so the caller must guard with the regime tag.
//
// Soundness claim for intersection:
//   x is an instance of (C1 intersect ... intersect Cn)  iff
//   x is an instance of C1 AND ... AND x is an instance of Cn.
// This is the OWL-Direct model-theoretic definition, so the replacement
// BGP has the same solutions as the original in any DL model.
//
// Soundness claim for union:
//   x is an instance of (C1 union ... union Cn)  iff
//   x is an instance of Ci for some i.
// SPARQL UNION is bag-semantic; a single ?x can match multiple
// branches. The outer query SELECT DISTINCT (or the default bag) will
// handle deduplication, same as the pre-rewrite semantics.
//
// Complexity: single O(|BGP|) pass to index the marker bnodes, then
// O(|BGP|) to split triples, so overall linear in BGP size. No fuel
// parameter needed because the list walk over the RDF collection is
// bounded by the number of triples in the BGP.
//
// IRON RULES:
//   - Logic in F* (rule #10); patches are glue only.
//   - Stack-safe: fold_left / tail-recursive list walks only.
//   - No (* / *) inside block comments (rule #12). All multi-line
//     prose is // comments.

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra

// ------------------------------------------------------------------
// Section 1. OWL / RDF vocabulary we need to match on.
//
// These mirror the constants in Tableau.fst, but we re-declare them
// locally so this module has no cross-dependency on Tableau (which
// would create a cycle: Tableau depends on RDF.Graph.Executable; the
// rewriter depends on SPARQL11.Algebra which already depends on
// Tableau). Duplication is cheap — string literals unify.
// ------------------------------------------------------------------

let owl_intersectionOf_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#intersectionOf");
  "http://www.w3.org/2002/07/owl#intersectionOf"

let owl_unionOf_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#unionOf");
  "http://www.w3.org/2002/07/owl#unionOf"

let owl_Class_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Class");
  "http://www.w3.org/2002/07/owl#Class"

let rdf_first_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

let rdf_type_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

// Phase-5 additions: restriction class expressions.
//   _:r a owl:Restriction ;
//       owl:onProperty :p ;
//       owl:someValuesFrom <filler> .
// is rewritten, when _:r appears as the object of rdf:type, to
//   ?x :p ?fresh . (expand <filler> as CE rooted at ?fresh)
// See simple5.rq (someValuesFrom with unionOf filler).
let owl_Restriction_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#Restriction");
  "http://www.w3.org/2002/07/owl#Restriction"

let owl_onProperty_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onProperty");
  "http://www.w3.org/2002/07/owl#onProperty"

let owl_someValuesFrom_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#someValuesFrom");
  "http://www.w3.org/2002/07/owl#someValuesFrom"

let owl_allValuesFrom_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#allValuesFrom");
  "http://www.w3.org/2002/07/owl#allValuesFrom"

// Cardinality restriction predicates. Both unqualified
// (owl:minCardinality / owl:maxCardinality / owl:cardinality) and
// qualified (owl:minQualifiedCardinality / owl:maxQualifiedCardinality /
// owl:qualifiedCardinality with owl:onClass) variants are recognised.
// Parent4 uses unqualified minCardinality; parent6/7/8 use qualified
// variants with owl:onClass.
let owl_minCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minCardinality");
  "http://www.w3.org/2002/07/owl#minCardinality"

let owl_maxCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxCardinality");
  "http://www.w3.org/2002/07/owl#maxCardinality"

let owl_cardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#cardinality");
  "http://www.w3.org/2002/07/owl#cardinality"

let owl_minQualifiedCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#minQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#minQualifiedCardinality"

let owl_maxQualifiedCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#maxQualifiedCardinality");
  "http://www.w3.org/2002/07/owl#maxQualifiedCardinality"

let owl_qualifiedCardinality_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#qualifiedCardinality");
  "http://www.w3.org/2002/07/owl#qualifiedCardinality"

let owl_onClass_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#onClass");
  "http://www.w3.org/2002/07/owl#onClass"

// Class-complement marker. The bnode shape
//   _:c a owl:Class ; owl:complementOf <C> .
// is recognised as a CE bnode under OWL-Direct semantics (paper-Q3).
// Rewrite shape: `?x rdf:type _:c` becomes
//   { ?x rdf:type ?d . ?d owl:disjointWith <C> }
//   UNION
//   { ?x rdf:type ?d . <C> owl:disjointWith ?d }
// — the rewriter mirror of Tableau.fst's `has_disjoint_witness` bridge.
// Sound, monotonic, one direction (never produces solutions that aren't
// entailed). Incomplete: complementOf-membership can also be derived
// from explicit "not in C" assertions or open-world disjoint-classes
// axioms — those paths are out of scope here.
let owl_complementOf_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#complementOf");
  "http://www.w3.org/2002/07/owl#complementOf"

// owl:disjointWith is needed to emit the rewritten BGP. We include the
// IRI literal here to avoid a cross-module dependency on Tableau.fst's
// constant of the same name. String-equality unification means the
// duplicate is free at runtime.
let owl_disjointWith_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2002/07/owl#disjointWith");
  "http://www.w3.org/2002/07/owl#disjointWith"

// Prefix the w3c_runner uses when rewriting pattern bnodes to synthetic
// variables under RDFS / OWL regimes (see w3c_runner.ml ~line 687).
// The rewriter recognises subjects/objects of either shape:
//   PS_BNode "b0"  or  PS_Var "_bnode_b0"
// so it works whether it runs before or after that rewrite.
let bnode_var_prefix : string = "_bnode_"

// ------------------------------------------------------------------
// Section 2. Node "keys": a canonical string identity for pattern
// subjects/terms that represent the same anonymous node. We key on the
// underlying bnode id; if the runner has already converted the bnode
// to PS_Var "_bnode_<id>", we strip the prefix. Named IRIs and plain
// variables are NOT candidates (they can't be class-expression
// markers), so they get None.
// ------------------------------------------------------------------

let strip_bnode_prefix (v : string) : option string =
  if string_starts_with v bnode_var_prefix
  then Some (string_substring v (string_length bnode_var_prefix) None)
  else None

let ps_marker_key (ps : pattern_subject) : option string =
  match ps with
  | PS_BNode b -> Some b
  | PS_Var v   -> strip_bnode_prefix v
  | _ -> None

let pt_marker_key (pt : pattern_term) : option string =
  match pt with
  | PT_BNode b -> Some b
  | PT_Var v   -> strip_bnode_prefix v
  | _ -> None

// Are two nodes (one as subject, one as object) the same anonymous node?
let ps_pt_same_anon (ps : pattern_subject) (pt : pattern_term) : bool =
  match ps_marker_key ps, pt_marker_key pt with
  | Some k1, Some k2 -> k1 = k2
  | _, _ -> false

// ------------------------------------------------------------------
// Section 3. Walk an RDF collection through a BGP, given the pattern
// term that points at the list head. The walk is tail-recursive with
// an explicit accumulator and a fuel bound equal to the BGP length —
// each step strips at least one triple from consideration, so the
// BGP length is an adequate bound.
// ------------------------------------------------------------------

// Find the first object pattern_term of (subj_key, pred_iri, ?) in a BGP,
// where subj_key is the marker-key of the subject we're looking for.
let rec bgp_find_first_obj (b : bgp) (subj_key : string) (pred : wf_iri)
  : Tot (option pattern_term) (decreases b) =
  match b with
  | [] -> None
  | tp :: rest ->
    (match ps_marker_key tp.tp_s, tp.tp_p with
     | Some k, PT_IRI p ->
       if k = subj_key && p = pred
       then Some tp.tp_o
       else bgp_find_first_obj rest subj_key pred
     | _, _ -> bgp_find_first_obj rest subj_key pred)

// Tail-recursive walk of an rdf:first/rdf:rest chain. Returns the list
// of operand pattern_terms in source order. Terminates either when it
// sees rdf:nil, or when a step can't find first/rest (malformed
// collection — we return what we've got so far, which keeps the
// rewriter total even on weird inputs).
let rec walk_rdf_collection_acc (b : bgp) (head : pattern_term)
                                 (acc : list pattern_term)
                                 (fuel : nat)
  : Tot (list pattern_term) (decreases fuel) =
  match fuel with
  | 0 -> List.Tot.rev acc
  | n ->
    match head with
    | PT_IRI _ ->
      // Either rdf:nil (end of list, normal) or some other IRI
      // (malformed collection — abort and return what we have).
      List.Tot.rev acc
    | _ ->
      (match pt_marker_key head with
       | None -> List.Tot.rev acc
       | Some k ->
         let first = bgp_find_first_obj b k rdf_first_iri in
         let rest  = bgp_find_first_obj b k rdf_rest_iri in
         match first, rest with
         | Some hd, Some tl -> walk_rdf_collection_acc b tl (hd :: acc) (n - 1)
         | _, _ -> List.Tot.rev acc)

let walk_rdf_collection (b : bgp) (head : pattern_term) : list pattern_term =
  walk_rdf_collection_acc b head [] (List.Tot.length b + 1)

// ------------------------------------------------------------------
// Section 4. Public entry point requested by the scoping doc:
//
//   extract_flat_intersection bgp marker_key
//
// Given a BGP and the key of a candidate marker bnode, return the list
// of operand pattern_terms iff the BGP contains a single triple
//     marker owl:intersectionOf list_head
// and the list walks successfully. Otherwise None.
//
// Also exposed: extract_flat_union (same shape for owl:unionOf).
// ------------------------------------------------------------------

let extract_flat_intersection (b : bgp) (marker_key : string)
  : option (list pattern_term) =
  match bgp_find_first_obj b marker_key owl_intersectionOf_iri with
  | None -> None
  | Some list_head ->
    match walk_rdf_collection b list_head with
    | []       -> None
    | operands -> Some operands

let extract_flat_union (b : bgp) (marker_key : string)
  : option (list pattern_term) =
  match bgp_find_first_obj b marker_key owl_unionOf_iri with
  | None -> None
  | Some list_head ->
    match walk_rdf_collection b list_head with
    | []       -> None
    | operands -> Some operands

// ------------------------------------------------------------------
// Section 5. Which triples does the rewriter consume and discard when
// it rewrites a flat class-expression marker?
//
// For a marker m, the triples we delete from the original BGP are:
//   (1) m owl:intersectionOf list_head
//   (2) m owl:unionOf       list_head
//   (3) m rdf:type owl:Class                  // bookkeeping in simple4
//   (4) every triple whose subject is a bnode/var on the collection
//       chain rooted at list_head, with predicate rdf:first or
//       rdf:rest. We compute the set of collection-chain keys by
//       walking the chain through the BGP.
//
// We keep everything else (including any `?x rdf:type m` triples, so
// they can be rewritten in section 6).
// ------------------------------------------------------------------

// Compute the set (as a list of keys) of all collection-chain bnode
// keys reachable from a list-head pattern_term, via rdf:first / rdf:rest.
// Tail-recursive with explicit accumulator.
let rec collection_chain_keys_acc (b : bgp) (head : pattern_term)
                                   (acc : list string)
                                   (fuel : nat)
  : Tot (list string) (decreases fuel) =
  match fuel with
  | 0 -> acc
  | n ->
    match pt_marker_key head with
    | None -> acc
    | Some k ->
      let acc' = if List.Tot.mem k acc then acc else k :: acc in
      (match bgp_find_first_obj b k rdf_rest_iri with
       | Some tl -> collection_chain_keys_acc b tl acc' (n - 1)
       | None    -> acc')

let collection_chain_keys (b : bgp) (head : pattern_term) : list string =
  collection_chain_keys_acc b head [] (List.Tot.length b + 1)

// Does this triple belong to the marker's bookkeeping (to be deleted)?
// Marker-owned triples:
//   (m owl:intersectionOf _) / (m owl:unionOf _)
//   (m rdf:type owl:Class)
//   (chain_key rdf:first _) / (chain_key rdf:rest _)
let is_marker_bookkeeping (marker_key : string)
                          (chain_keys : list string)
                          (tp : triple_pattern) : bool =
  match ps_marker_key tp.tp_s, tp.tp_p with
  | Some sk, PT_IRI p ->
    if sk = marker_key then
      (p = owl_intersectionOf_iri ||
       p = owl_unionOf_iri ||
       (p = rdf_type_iri &&
        (match tp.tp_o with
         | PT_IRI oi -> oi = owl_Class_iri
         | _ -> false)))
    else if List.Tot.mem sk chain_keys then
      (p = rdf_first_iri || p = rdf_rest_iri)
    else false
  | _, _ -> false

// ------------------------------------------------------------------
// Section 6. Rewrite a BGP once, for ONE marker, returning either a
// BGP (intersection branch) or a union-of-BGPs (union branch). The
// caller lifts the result into a group_graph_pattern.
// ------------------------------------------------------------------

// "Consumer" triples are (?x rdf:type marker). For each operand O the
// rewriter produces a replacement triple (?x rdf:type O). Non-consumer,
// non-bookkeeping triples are kept unchanged.

let is_consumer_triple (marker_key : string) (tp : triple_pattern) : bool =
  match tp.tp_p, tp.tp_o with
  | PT_IRI p, o ->
    p = rdf_type_iri &&
    (match pt_marker_key o with
     | Some k -> k = marker_key
     | None -> false)
  | _, _ -> false

// Expand one consumer triple into n replacements, one per operand.
// Uses fold_left over operands for stack safety.
let expand_consumer_for_intersection
      (tp : triple_pattern) (operands : list pattern_term)
  : list triple_pattern =
  let mk (o : pattern_term) : triple_pattern =
    { tp_s = tp.tp_s; tp_p = PT_IRI rdf_type_iri; tp_o = o } in
  let step (acc : list triple_pattern) (o : pattern_term) : list triple_pattern =
    mk o :: acc in
  List.Tot.rev (List.Tot.fold_left step [] operands)

// Process a single triple under an intersection rewrite:
//   - bookkeeping       -> []
//   - consumer          -> n replacement triples
//   - otherwise         -> [tp]
let rewrite_triple_intersection
      (marker_key : string) (chain_keys : list string)
      (operands : list pattern_term) (tp : triple_pattern)
  : list triple_pattern =
  if is_marker_bookkeeping marker_key chain_keys tp then []
  else if is_consumer_triple marker_key tp
  then expand_consumer_for_intersection tp operands
  else [tp]

// Stack-safe rewrite over the whole BGP.
let rewrite_bgp_intersection
      (marker_key : string) (chain_keys : list string)
      (operands : list pattern_term) (b : bgp)
  : bgp =
  let step (acc : list triple_pattern) (tp : triple_pattern)
           : list triple_pattern =
    List.Tot.append acc (rewrite_triple_intersection marker_key chain_keys operands tp) in
  List.Tot.fold_left step [] b

// For union we need to build multiple "branch BGPs": one per operand,
// each sharing the non-marker triples and contributing one
// (?x rdf:type operand_i) triple per consumer triple. For the simple
// cases targeted here there is exactly one consumer triple, but we
// support N consumer triples by placing each replacement in its
// respective union branch.

// Strip bookkeeping + consumer triples from the BGP (the residue is
// shared across all union branches).
let rewrite_bgp_strip_marker
      (marker_key : string) (chain_keys : list string) (b : bgp)
  : bgp =
  let step (acc : list triple_pattern) (tp : triple_pattern)
           : list triple_pattern =
    if is_marker_bookkeeping marker_key chain_keys tp then acc
    else if is_consumer_triple marker_key tp then acc
    else List.Tot.append acc [tp] in
  List.Tot.fold_left step [] b

// Collect consumer triples (we need their subjects to build union branches).
let rewrite_bgp_collect_consumers
      (marker_key : string) (b : bgp)
  : list triple_pattern =
  let step (acc : list triple_pattern) (tp : triple_pattern)
           : list triple_pattern =
    if is_consumer_triple marker_key tp
    then List.Tot.append acc [tp]
    else acc in
  List.Tot.fold_left step [] b

// Build one union branch: residue BGP + (subj_i rdf:type operand) for
// every consumer. If there are no consumers this returns the residue
// unchanged (odd case: _:c owl:unionOf (:A :B) without a type-binder;
// the query has no use for the union, so keeping the residue is sound).
let build_union_branch
      (residue : bgp) (consumers : list triple_pattern) (op : pattern_term)
  : bgp =
  let step (acc : list triple_pattern) (tp : triple_pattern)
           : list triple_pattern =
    let new_tp : triple_pattern =
      { tp_s = tp.tp_s; tp_p = PT_IRI rdf_type_iri; tp_o = op } in
    List.Tot.append acc [new_tp] in
  List.Tot.append residue (List.Tot.fold_left step [] consumers)

// Stitch a list of branch BGPs into a left-deep GP_Union tree.
// Tail-recursive with accumulator.
let rec union_ladder (acc : group_graph_pattern)
                     (branches : list group_graph_pattern)
  : Tot group_graph_pattern (decreases branches) =
  match branches with
  | [] -> acc
  | br :: rest -> union_ladder (GP_Union acc br) rest

// Wrap a GGP in a SELECT * DISTINCT { g } sub-select. Used to dedupe
// at CE-emission sites (`build_union_ggp`, `expand_ce_subject` union
// arm) so that a single ?x matching multiple operands of an OWL
// unionOf class expression contributes only ONE solution row, even
// though SPARQL UNION is bag-semantic.
//
// Why localised here and not at rewrite_query level: the top-level
// SELECT modifier governs the user's projection. Forcing DISTINCT
// there breaks bag-semantic queries (subquery / property-path /
// bind / bindings tests) that go through OWL_QueryEval. A
// sub-select wrapper changes ONLY the CE-expanded portion's
// multiset, leaving the outer query's bag semantics intact. The
// outer pattern joins against the projected vars (every var free
// in g, via Select_All) just as if the union had been emitted
// directly.
//
// Caller responsibility: only wrap when there are 2+ union branches.
// A 0-branch union collapses to GP_Empty / leaf and a 1-branch union
// to GP_BGP — neither emits a duplicate, so wrapping would just add
// dead AST.
let wrap_distinct_over_ggp (g : group_graph_pattern) : group_graph_pattern =
  GP_SubSelect ({
    q_base     = None;
    q_prefixes = [];
    q_form     = QF_Select Select_All;
    q_dataset  = [];
    q_pattern  = g;
    q_group_by = None;
    q_having   = None;
    q_modifier = {
      sm_order_by = None;
      sm_distinct = true;
      sm_reduced  = false;
      sm_offset   = None;
      sm_limit    = None
    };
    q_values   = None
  })

let build_union_ggp (branch_bgps : list bgp) : group_graph_pattern =
  match branch_bgps with
  | [] -> GP_Empty
  | [b] -> GP_BGP b
  | b1 :: rest ->
    let head = GP_BGP b1 in
    let rec_branches : list group_graph_pattern =
      List.Tot.fold_left (fun acc b -> List.Tot.append acc [GP_BGP b]) [] rest in
    // 2+ branches => emit GP_Union ladder, then wrap in DISTINCT
    // sub-select so set-theoretic OWL union semantics are recovered
    // without forcing DISTINCT on the user's outer projection.
    wrap_distinct_over_ggp (union_ladder head rec_branches)

// ------------------------------------------------------------------
// Section 7. Identify marker candidates inside a BGP. A key is a
// "flat class-expression marker" iff there is a triple
//   (m, owl:intersectionOf, _) or (m, owl:unionOf, _)
// in the BGP. Returns a list of (key, combinator) pairs, in the
// order encountered.
// ------------------------------------------------------------------

// CE_SomeValuesFrom marks a bnode that is the subject of an
// owl:someValuesFrom triple — the standard shape of an existential
// restriction (`_:r a owl:Restriction ; owl:onProperty :p ;
// owl:someValuesFrom <filler>`). The combinator carries no payload
// here; onProperty / someValuesFrom triples are looked up on demand
// from the BGP at expansion time, which keeps this type first-order
// (and avoids a recursive type over pattern_term).
// Cardinality combinators carry no payload here; the actual N value
// and the (optional) onClass filler are looked up from the BGP at
// expansion time. Three variants:
//   CE_MinCardinality  — `owl:minCardinality` (unqualified)
//                        and `owl:minQualifiedCardinality` + `owl:onClass`
//   CE_MaxCardinality  — analogous max
//   CE_ExactCardinality — `owl:cardinality` and `owl:qualifiedCardinality`
type ce_combinator =
  | CE_Intersect | CE_Union | CE_SomeValuesFrom | CE_AllValuesFrom
  | CE_MinCardinality | CE_MaxCardinality | CE_ExactCardinality
  | CE_ComplementOf

// Predicates that classify a bnode as an intersection/union marker.
// owl:someValuesFrom is deliberately NOT in this set: restriction
// markers need an extra filler-check (see
// find_markers_with_restrictions below) to avoid taking over simple2
// / simple5 / simple6, where the closure's canonical-bnode
// materialisation is the correct path.
let combinator_of_pred_flat (p : wf_iri) : option ce_combinator =
  if p = owl_intersectionOf_iri then Some CE_Intersect
  else if p = owl_unionOf_iri then Some CE_Union
  else None

// Cardinality-predicate classifier: returns the combinator if `p` is
// any of the six cardinality predicates (qualified or not).
let combinator_of_card_pred (p : wf_iri) : option ce_combinator =
  if p = owl_minCardinality_iri || p = owl_minQualifiedCardinality_iri
  then Some CE_MinCardinality
  else if p = owl_maxCardinality_iri || p = owl_maxQualifiedCardinality_iri
  then Some CE_MaxCardinality
  else if p = owl_cardinality_iri || p = owl_qualifiedCardinality_iri
  then Some CE_ExactCardinality
  else None

// Kept for backward compatibility / external readers. Includes the
// someValuesFrom predicate, but users should prefer
// `combinator_of_pred_flat` + the restriction-filler guard below.
let combinator_of_pred (p : wf_iri) : option ce_combinator =
  if p = owl_intersectionOf_iri then Some CE_Intersect
  else if p = owl_unionOf_iri then Some CE_Union
  else if p = owl_someValuesFrom_iri then Some CE_SomeValuesFrom
  else if p = owl_allValuesFrom_iri then Some CE_AllValuesFrom
  else combinator_of_card_pred p

// Pass 1: gather flat markers (intersectionOf / unionOf) only.
let rec find_flat_markers_acc (b : bgp) (acc : list (string & ce_combinator))
  : Tot (list (string & ce_combinator)) (decreases b) =
  match b with
  | [] -> List.Tot.rev acc
  | tp :: rest ->
    (match ps_marker_key tp.tp_s, tp.tp_p with
     | Some k, PT_IRI p ->
       (match combinator_of_pred_flat p with
        | Some c ->
          let dup = List.Tot.existsb (fun (k', _) -> k' = k) acc in
          if dup then find_flat_markers_acc rest acc
          else find_flat_markers_acc rest ((k, c) :: acc)
        | None -> find_flat_markers_acc rest acc)
     | _, _ -> find_flat_markers_acc rest acc)

// Pass 2: augment with restriction markers whose someValuesFrom
// filler is itself a CE bnode (i.e., NESTED). Rationale:
//
//   * Flat restrictions (filler = named class, e.g. simple2:
//     `?x a [a owl:Restriction ; owl:onProperty :p ; owl:someValuesFrom :B]`)
//     are handled by the CLOSURE's canonical-bnode materialisation
//     (RDF.Graph.Executable.owl_rule_cls_svf2_qualified), which
//     emits `:a rdf:type _:rSVF(:p,:B)` only for those :a that
//     actually have a :p-successor typed :B — giving the expected
//     simple2 answer {:a} and NOT the over-approximation {:a,:c}
//     that a naive rewrite `?x :p ?g . ?g a :B` would produce.
//     We must therefore leave flat restrictions alone so the closure
//     path keeps working.
//
//   * Nested restrictions (filler = a CE bnode, e.g. simple8:
//     outer someValuesFrom points at another Restriction bnode) have
//     NO canonical data-side match: the closure only materialises
//     canonicals keyed on named classes. So we MUST rewrite these,
//     and the rewriter's `?x :p ?g . <expand filler at ?g>` gives
//     the right answer for simple8.
//
// Guard: a restriction is marked as CE_SomeValuesFrom iff its
// someValuesFrom filler is itself a CE bnode — either a flat
// intersection/union marker OR another restriction bnode (subject
// of a someValuesFrom triple). A named-IRI filler keeps the
// restriction OUT of the marker list and therefore routes via the
// closure's canonical materialisation, which preserves simple2 /
// simple5 / simple6 behaviour.

// Is `k` the subject of ANY owl:someValuesFrom triple in `b`?
let is_svf_subject (b : bgp) (k : string) : bool =
  Some? (bgp_find_first_obj b k owl_someValuesFrom_iri)

// Is `k` the subject of ANY owl:allValuesFrom triple in `b`?
let is_avf_subject (b : bgp) (k : string) : bool =
  Some? (bgp_find_first_obj b k owl_allValuesFrom_iri)

// Is `k` the subject of an owl:complementOf triple in `b`? Such a
// bnode marks a CE shape `[a owl:Class ; owl:complementOf <C>]` —
// see paper-sparqldl-Q3.
let is_complementOf_subject (b : bgp) (k : string) : bool =
  Some? (bgp_find_first_obj b k owl_complementOf_iri)

// Look up the complement target (the negated class term) for the
// complementOf bnode rooted at `k`.
let complementOf_target (b : bgp) (k : string) : option pattern_term =
  bgp_find_first_obj b k owl_complementOf_iri

// Is `k` the subject of any cardinality predicate? Returns the
// classifying combinator if so. Tries unqualified and qualified
// variants in order: min*, max*, exact (cardinality / qualifiedCardinality).
let card_subject_combinator (b : bgp) (k : string) : option ce_combinator =
  if Some? (bgp_find_first_obj b k owl_minCardinality_iri) ||
     Some? (bgp_find_first_obj b k owl_minQualifiedCardinality_iri)
  then Some CE_MinCardinality
  else if Some? (bgp_find_first_obj b k owl_maxCardinality_iri) ||
          Some? (bgp_find_first_obj b k owl_maxQualifiedCardinality_iri)
  then Some CE_MaxCardinality
  else if Some? (bgp_find_first_obj b k owl_cardinality_iri) ||
          Some? (bgp_find_first_obj b k owl_qualifiedCardinality_iri)
  then Some CE_ExactCardinality
  else None

let is_card_subject (b : bgp) (k : string) : bool =
  Some? (card_subject_combinator b k)

// Is `k` a restriction CE marker of any supported kind (svf, avf, or
// cardinality)?
let is_restriction_subject (b : bgp) (k : string) : bool =
  is_svf_subject b k || is_avf_subject b k || is_card_subject b k

// Look up the filler of the restriction rooted at `k`, trying both
// someValuesFrom and allValuesFrom in that order. Returns the filler
// pattern_term paired with the combinator telling the caller which
// predicate matched.
let restriction_filler (b : bgp) (k : string)
  : option (pattern_term & ce_combinator) =
  match bgp_find_first_obj b k owl_someValuesFrom_iri with
  | Some f -> Some (f, CE_SomeValuesFrom)
  | None ->
    match bgp_find_first_obj b k owl_allValuesFrom_iri with
    | Some f -> Some (f, CE_AllValuesFrom)
    | None -> None

// Does the restriction rooted at `k` have a filler that is itself
// a CE bnode? (Nested case.)
let restriction_has_nested_filler (b : bgp) (k : string) : bool =
  match restriction_filler b k with
  | None -> false
  | Some (filler, _) ->
    match pt_marker_key filler with
    | None -> false  // named IRI / literal / non-bnode-var filler
    | Some kf ->
      // filler is a bnode. CE-qualified iff flat marker OR itself a
      // restriction (svf / avf) subject OR a complementOf bnode (the
      // bnode shape `[a owl:Class ; owl:complementOf :C]`,
      // paper-sparqldl-Q3).
      let flat = find_flat_markers_acc b [] in
      List.Tot.existsb (fun (k', _) -> k' = kf) flat ||
      is_restriction_subject b kf ||
      is_complementOf_subject b kf

// Scan the BGP for restriction bnodes (subjects of someValuesFrom or
// allValuesFrom) and, for each, include as a marker according to the
// following discipline:
//   * someValuesFrom with flat (named-class) filler -> NOT a marker
//     (the closure's canonical-bnode materialisation is the correct
//     path, see simple2).
//   * someValuesFrom with nested (CE-bnode) filler -> CE_SomeValuesFrom
//     marker (simple5 / simple8 case).
//   * allValuesFrom (any filler, named class or nested) ->
//     CE_AllValuesFrom marker. The closure's `owl_rule_cls_avf1` only
//     propagates types onto y's; it never marks x as a member of the
//     restriction class. So the rewriter must always handle ?x queries
//     against AVF restrictions.
let rec add_restriction_markers_acc
          (b : bgp) (rem : bgp) (acc : list (string & ce_combinator))
  : Tot (list (string & ce_combinator)) (decreases rem) =
  match rem with
  | [] -> acc
  | tp :: rest ->
    (match ps_marker_key tp.tp_s, tp.tp_p with
     | Some k, PT_IRI p ->
       if p = owl_someValuesFrom_iri then
         (let dup = List.Tot.existsb (fun (k', _) -> k' = k) acc in
          if dup then add_restriction_markers_acc b rest acc
          else if restriction_has_nested_filler b k
          then add_restriction_markers_acc b rest
                 (List.Tot.append acc [(k, CE_SomeValuesFrom)])
          else add_restriction_markers_acc b rest acc)
       else if p = owl_allValuesFrom_iri then
         (let dup = List.Tot.existsb (fun (k', _) -> k' = k) acc in
          if dup then add_restriction_markers_acc b rest acc
          else add_restriction_markers_acc b rest
                 (List.Tot.append acc [(k, CE_AllValuesFrom)]))
       else if p = owl_complementOf_iri then
         // ComplementOf bnode (paper-sparqldl-Q3 inner CE).
         // We always mark it (no nested-filler guard like svf/avf):
         // the closure has no canonical materialisation that handles
         // class-complement, so the rewriter is the only path.
         (let dup = List.Tot.existsb (fun (k', _) -> k' = k) acc in
          if dup then add_restriction_markers_acc b rest acc
          else add_restriction_markers_acc b rest
                 (List.Tot.append acc [(k, CE_ComplementOf)]))
       else
         (match combinator_of_card_pred p with
          | Some c ->
            let dup = List.Tot.existsb (fun (k', _) -> k' = k) acc in
            if dup then add_restriction_markers_acc b rest acc
            else add_restriction_markers_acc b rest
                   (List.Tot.append acc [(k, c)])
          | None -> add_restriction_markers_acc b rest acc)
     | _, _ -> add_restriction_markers_acc b rest acc)

// Once we've decided to rewrite a top-level nested restriction, we
// also need to strip bookkeeping triples for every inner restriction
// that expansion will consume. Transitive closure: include any
// someValuesFrom-subject bnode reachable from the current marker set
// via the filler chain. Named-class fillers terminate the chain.
let rec add_inner_restrictions_acc
          (b : bgp) (work : list string) (acc : list (string & ce_combinator))
          (fuel : nat)
  : Tot (list (string & ce_combinator)) (decreases fuel) =
  match fuel, work with
  | 0, _ -> acc
  | _, [] -> acc
  | n, k :: rest ->
    // Look at this marker's restriction filler (svf or avf).
    (match restriction_filler b k with
     | None -> add_inner_restrictions_acc b rest acc (n - 1)
     | Some (filler, _) ->
       match pt_marker_key filler with
       | None -> add_inner_restrictions_acc b rest acc (n - 1)
       | Some kf ->
         let already =
           List.Tot.existsb (fun (k', _) -> k' = kf) acc in
         if already then add_inner_restrictions_acc b rest acc (n - 1)
         else if is_svf_subject b kf then
           // kf is an inner svf restriction — mark it and keep walking.
           add_inner_restrictions_acc b
             (List.Tot.append rest [kf])
             (List.Tot.append acc [(kf, CE_SomeValuesFrom)])
             (n - 1)
         else if is_avf_subject b kf then
           // kf is an inner avf restriction — mark it and keep walking.
           add_inner_restrictions_acc b
             (List.Tot.append rest [kf])
             (List.Tot.append acc [(kf, CE_AllValuesFrom)])
             (n - 1)
         else if is_complementOf_subject b kf then
           // kf is an inner complementOf bnode — mark it for
           // bookkeeping stripping. No further walk needed: the
           // complement target is a class term, not a chain head.
           add_inner_restrictions_acc b rest
             (List.Tot.append acc [(kf, CE_ComplementOf)])
             (n - 1)
         else add_inner_restrictions_acc b rest acc (n - 1))

let find_markers (b : bgp) : list (string & ce_combinator) =
  let flat   = find_flat_markers_acc b [] in
  let withr  = add_restriction_markers_acc b b flat in
  // Gather the initial work list: keys of all restriction markers
  // added in this pass (we don't need to chase inner fillers for
  // intersectionOf / unionOf markers, because their operands are
  // handled by walk_rdf_collection + expand_ce_subject's existing
  // recursion).
  let restr_keys =
    List.Tot.fold_left
      (fun acc (k, c) -> match c with
                        | CE_SomeValuesFrom -> List.Tot.append acc [k]
                        | CE_AllValuesFrom  -> List.Tot.append acc [k]
                        | _ -> acc)
      []
      withr in
  // Fuel = BGP length + 1 is a safe upper bound on restriction depth.
  add_inner_restrictions_acc b restr_keys withr (List.Tot.length b + 1)

// ------------------------------------------------------------------
// Section 8. Rewrite a single BGP: apply one marker at a time,
// left-to-right. Intersection markers stay inside the BGP; the first
// union marker escalates the whole BGP into a GP_Union tree. For
// the Phase 3 targets (simple1, simple4, paper-Q2) at most one marker
// is present per BGP so the order doesn't matter.
//
// Phase 3 only handles at most ONE combinator marker per BGP. If a
// BGP has a mix, we apply intersections first and then the first
// union; any remaining markers are left in place (will be picked up
// by the Phase 4 recursive pass when that lands).
// ------------------------------------------------------------------

let rewrite_bgp_one_intersection
      (marker_key : string) (b : bgp)
  : bgp =
  match extract_flat_intersection b marker_key with
  | None -> b
  | Some operands ->
    let head_opt = bgp_find_first_obj b marker_key owl_intersectionOf_iri in
    let chain_keys = match head_opt with
                     | Some hd -> collection_chain_keys b hd
                     | None    -> [] in
    rewrite_bgp_intersection marker_key chain_keys operands b

let rewrite_bgp_one_union
      (marker_key : string) (b : bgp)
  : group_graph_pattern =
  match extract_flat_union b marker_key with
  | None -> GP_BGP b
  | Some operands ->
    let head_opt = bgp_find_first_obj b marker_key owl_unionOf_iri in
    let chain_keys = match head_opt with
                     | Some hd -> collection_chain_keys b hd
                     | None    -> [] in
    let residue   = rewrite_bgp_strip_marker marker_key chain_keys b in
    let consumers = rewrite_bgp_collect_consumers marker_key b in
    let branch_bgps : list bgp =
      List.Tot.fold_left
        (fun acc op -> List.Tot.append acc [build_union_branch residue consumers op])
        []
        operands in
    build_union_ggp branch_bgps

// Apply all intersection markers first (in order), then the first
// union marker (if any). Returns a group_graph_pattern because a
// union escalates out of GP_BGP.
let rewrite_bgp_flat (b : bgp) : group_graph_pattern =
  let markers = find_markers b in
  // Split into intersection and union lists, preserving order.
  let inter_keys =
    List.Tot.fold_left
      (fun acc (k, c) -> match c with
                        | CE_Intersect -> List.Tot.append acc [k]
                        | _ -> acc)
      []
      markers in
  let union_keys =
    List.Tot.fold_left
      (fun acc (k, c) -> match c with
                        | CE_Union -> List.Tot.append acc [k]
                        | _ -> acc)
      []
      markers in
  // Apply intersections first.
  let b_after_inter =
    List.Tot.fold_left
      (fun cur k -> rewrite_bgp_one_intersection k cur)
      b
      inter_keys in
  // Then apply the first union marker, if any. Remaining union
  // markers in the same BGP are a Phase 4 concern.
  match union_keys with
  | [] -> GP_BGP b_after_inter
  | k :: _ -> rewrite_bgp_one_union k b_after_inter

// ------------------------------------------------------------------
// Section 8b. Phase 4: nested CE rewrite.
//
// The flat rewriter (Section 6-8) handles the shape
//   ?x rdf:type _:m .  _:m owl:intersectionOf ( :C1 ... :Cn ) .
// where every operand is already a named class IRI. Nested CE is
// the case where one or more operands is itself another CE bnode,
// e.g. (Phase 4 target test simple7):
//   ?x rdf:type _:m .
//   _:m owl:intersectionOf ( :A _:u ) .
//   _:u a owl:Class ; owl:unionOf ( :B :C ) .
//
// Strategy: **expand each CE marker, from the top, into a
// group_graph_pattern rooted at the consumer triple's subject**.
// An intersection over operands [o1; ...; on] expands to the BGP
// formed by concatenating (subj rdf:type o_i) — BUT any o_i that is
// itself a CE bnode recurses. A union expands to GP_Union branches,
// each built from (subj rdf:type o_i); again, o_i may be another CE.
//
// Fuel = the number of CE markers in the BGP + 1. Each recursion
// step resolves one CE bnode, and we never re-enter a marker (F*
// insists on a structurally decreasing measure, so we just pass the
// fuel down). For simple7 the depth is 2; fuel 32 is far more than
// needed but harmless.
//
// Operands that are NOT CE markers (named IRIs, vars, literals,
// non-CE bnodes) are leaves and become a single triple pattern
// `subj rdf:type leaf`. Notably, restriction bnodes ([a owl:Restriction;
// owl:onProperty :p; owl:someValuesFrom :B]) fall into this "leaf"
// branch — the flat rewriter emits the bnode unchanged as the
// object of rdf:type. That's why simple2 / simple3 / simple5 /
// simple6 / simple8 (all restriction-involved) remain deferred:
// the emitted bnode won't bind to any data triple unless the
// closure step materialises a matching canonical restriction.
// ------------------------------------------------------------------

// Is this pattern_term a CE marker in BGP b (subject of intersectionOf,
// unionOf, or someValuesFrom)? Returns its key and combinator if so.
//
// IMPORTANT: this is an EXPANSION-TIME classifier, not a
// top-level-marker classifier. It's called when `expand_ce_subject`
// recurses into a CE operand / filler. At that point we want to fully
// expand every CE bnode we encounter, including restrictions whose
// filler is a named class (e.g. the INNER restriction in simple8,
// whose filler is :B). Those are not top-level markers (so
// `find_markers` skips them, keeping simple2 on the closure path),
// but once we're already inside a nested expansion we must keep going.
let ce_combinator_for_term (b : bgp) (pt : pattern_term)
  : option (string & ce_combinator) =
  match pt_marker_key pt with
  | None -> None
  | Some k ->
    // 1. Flat intersection / union markers.
    let flat = find_flat_markers_acc b [] in
    let rec lookup (ms : list (string & ce_combinator))
      : Tot (option ce_combinator) (decreases ms) =
      match ms with
      | [] -> None
      | (k', c) :: rest -> if k' = k then Some c else lookup rest in
    (match lookup flat with
     | Some c -> Some (k, c)
     | None ->
       // 2. Restriction CE: any bnode with a someValuesFrom or
       //    allValuesFrom triple. Named-class fillers still reach here
       //    during nested expansion, and we expand them too (resulting
       //    in a simple `?_sv_k rdf:type C` leaf in the svf case, or
       //    the FILTER NOT EXISTS chain for avf).
       if is_svf_subject b k then Some (k, CE_SomeValuesFrom)
       else if is_avf_subject b k then Some (k, CE_AllValuesFrom)
       else if is_complementOf_subject b k then Some (k, CE_ComplementOf)
       else
         // 3. Cardinality CE: any bnode that is the subject of a
         //    minCardinality / maxCardinality / cardinality (or their
         //    qualified variants) predicate.
         (match card_subject_combinator b k with
          | Some c -> Some (k, c)
          | None -> None))

// Build a BGP containing a single `subj rdf:type leaf` triple.
let single_type_bgp (subj : pattern_subject) (leaf : pattern_term) : bgp =
  [ { tp_s = subj; tp_p = PT_IRI rdf_type_iri; tp_o = leaf } ]

// Join a list of BGPs into a single BGP by concatenation. Stack-safe
// fold_left. The result is *conjunction* — every triple must match.
let concat_bgps (bs : list bgp) : bgp =
  List.Tot.fold_left
    (fun acc b -> List.Tot.append acc b)
    []
    bs

// Nest a list of group_graph_pattern conjuncts into a left-deep
// GP_Join tree. Before taking the Join route, coalesce contiguous
// GP_BGP conjuncts at the start of the list into a single GP_BGP
// (conjunction of BGPs is just triple-pattern concatenation). This
// preserves the Phase 3 behaviour for simple1/simple4 — all-named
// operands still compile to a single BGP, not a Join tree.
let rec join_ggps_acc (acc : group_graph_pattern) (rest : list group_graph_pattern)
  : Tot group_graph_pattern (decreases rest) =
  match rest with
  | []       -> acc
  | g :: tl  ->
    (match acc, g with
     | GP_BGP ba, GP_BGP bg -> join_ggps_acc (GP_BGP (List.Tot.append ba bg)) tl
     | _, _ -> join_ggps_acc (GP_Join acc g) tl)

let join_ggps (gs : list group_graph_pattern) : group_graph_pattern =
  match gs with
  | []       -> GP_Empty
  | [g]      -> g
  | g :: tl  -> join_ggps_acc g tl

// Expand a CE operand `op` as a class expression applied to `subj`:
//   if op is a CE-intersect marker -> BGP with one conjunct per
//     recursively-expanded operand.
//   if op is a CE-union marker -> GP_Union tree with one branch per
//     recursively-expanded operand.
//   else (leaf) -> GP_BGP [ subj rdf:type op ].
// Fuel decreases on each CE-bnode dive.
let rec expand_ce_subject
  (b : bgp) (subj : pattern_subject) (op : pattern_term) (fuel : nat)
  : Tot group_graph_pattern (decreases fuel) =
  match fuel with
  | 0 ->
    // Out of fuel: emit the leaf form; at worst this is the
    // pre-rewrite behaviour (a bnode as the object of rdf:type that
    // won't bind in the data). Sound — never *adds* solutions.
    GP_BGP (single_type_bgp subj op)
  | n ->
    match ce_combinator_for_term b op with
    | None ->
      // Not a CE marker: emit leaf triple unchanged.
      GP_BGP (single_type_bgp subj op)
    | Some (k, CE_Intersect) ->
      (match extract_flat_intersection b k with
       | None ->
         // Marker is present but operand list is empty / broken.
         GP_BGP (single_type_bgp subj op)
       | Some operands ->
         // Recurse on each operand with one unit of fuel spent on
         // this expansion. Accumulate GGPs and join them.
         let step (acc : list group_graph_pattern) (o : pattern_term)
                  : list group_graph_pattern =
           List.Tot.append acc [expand_ce_subject b subj o (n - 1)] in
         let ggps = List.Tot.fold_left step [] operands in
         join_ggps ggps)
    | Some (k, CE_Union) ->
      (match extract_flat_union b k with
       | None ->
         GP_BGP (single_type_bgp subj op)
       | Some operands ->
         let step (acc : list group_graph_pattern) (o : pattern_term)
                  : list group_graph_pattern =
           List.Tot.append acc [expand_ce_subject b subj o (n - 1)] in
         let branches = List.Tot.fold_left step [] operands in
         // Reuse the flat union ladder: peel the first branch as
         // the left spine, fold the rest with GP_Union. For the
         // multi-branch case we wrap the resulting ladder in a
         // DISTINCT sub-select so OWL set-theoretic union semantics
         // are recovered without forcing DISTINCT on the outer query
         // (see `wrap_distinct_over_ggp`). simple4 / simple5 / simple7.
         match branches with
         | []  -> GP_BGP (single_type_bgp subj op)
         | [g] -> g
         | g :: tl ->
           let ladder = List.Tot.fold_left (fun acc br -> GP_Union acc br) g tl in
           wrap_distinct_over_ggp ladder)
    | Some (k, CE_SomeValuesFrom) ->
      // Existential restriction: _:r owl:onProperty :p ;
      //                            owl:someValuesFrom <filler> .
      // Rewrite (subj rdf:type _:r) to
      //   subj :p ?_sv_<k> . <filler expanded as CE rooted at ?_sv_<k>>
      // The fresh variable name is derived from the restriction
      // marker key, so two distinct restrictions in the same BGP get
      // two distinct fresh variables (bnode ids are unique within
      // a BGP). Leafs (named-class filler) expand via the default
      // branch of expand_ce_subject — giving ?_sv_<k> rdf:type C.
      let on_prop_opt  = bgp_find_first_obj b k owl_onProperty_iri in
      let filler_opt   = bgp_find_first_obj b k owl_someValuesFrom_iri in
      (match on_prop_opt, filler_opt with
       | Some (PT_IRI p_iri), Some filler ->
         let fresh_name : string = "_sv_" ^ k in
         let fresh_subj : pattern_subject = PS_Var fresh_name in
         let fresh_term : pattern_term    = PT_Var fresh_name in
         // (subj p_iri ?fresh)
         let prop_triple : triple_pattern =
           { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = fresh_term } in
         let prop_ggp : group_graph_pattern = GP_BGP [prop_triple] in
         // Expand the filler rooted at ?fresh.
         let filler_ggp = expand_ce_subject b fresh_subj filler (n - 1) in
         // Join the property triple with the filler expansion.
         // join_ggps coalesces BGP+BGP into a single BGP, otherwise
         // builds a GP_Join; either is semantically correct.
         join_ggps [prop_ggp; filler_ggp]
       | _, _ ->
         // Malformed restriction (no onProperty, or a variable
         // predicate we can't pin down): fall back to leaf. This is
         // sound but won't bind anything useful.
         GP_BGP (single_type_bgp subj op))
    | Some (k, CE_AllValuesFrom) ->
      // Universal restriction: _:r owl:onProperty :p ;
      //                          owl:allValuesFrom <filler> .
      // Rewrite (subj rdf:type _:r) to a FILTER NOT EXISTS chain:
      //   subj :p ?_av_anchor_<k> .
      //   FILTER NOT EXISTS {
      //     subj :p ?_av_bad_<k> .
      //     <per filler-branch> FILTER NOT EXISTS { ?bad rdf:type Ci }
      //   }
      //
      // Semantics: the anchor triple asserts "subj has at least one
      // :p-link" (tests' convention: excludes vacuous-true subjects).
      // The outer FNE asserts "no y exists that is :p-linked AND is
      // not a member of any branch of the filler."
      //
      // Supported fillers for the FNE-chain inversion:
      //   * named class C         -> one FNE branch {?bad a C}
      //   * owl:unionOf (C1..Cn)  -> n FNE branches, one per operand
      // For other shapes (intersectionOf, nested restrictions) we
      // fall back to the leaf form (unchanged bnode object of type),
      // which is sound but won't bind anything useful. Extending to
      // more shapes is Phase 6.
      let on_prop_opt  = bgp_find_first_obj b k owl_onProperty_iri in
      let filler_opt   = bgp_find_first_obj b k owl_allValuesFrom_iri in
      (match on_prop_opt, filler_opt with
       | Some (PT_IRI p_iri), Some filler ->
         let anchor_name : string = "_av_anchor_" ^ k in
         let bad_name    : string = "_av_bad_"    ^ k in
         let anchor_term : pattern_term    = PT_Var anchor_name in
         let bad_subj    : pattern_subject = PS_Var bad_name in
         let bad_term    : pattern_term    = PT_Var bad_name in
         // (subj p anchor)
         let anchor_triple : triple_pattern =
           { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = anchor_term } in
         let anchor_ggp : group_graph_pattern = GP_BGP [anchor_triple] in
         // Inner pattern: (subj p bad)
         let bad_triple : triple_pattern =
           { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = bad_term } in
         let bad_bgp_ggp : group_graph_pattern = GP_BGP [bad_triple] in
         // Branches list (pattern_terms): for named-class filler, a
         // one-element list containing the filler itself. For unionOf,
         // the operand list. Other CE shapes -> leaf fallback.
         let branches_opt : option (list pattern_term) =
           match ce_combinator_for_term b filler with
           | None ->
             // Leaf filler (named class / var / literal / non-CE bnode).
             Some [filler]
           | Some (kf, CE_Union) ->
             extract_flat_union b kf
           | _ ->
             // Intersection / restriction fillers: not yet supported.
             None in
         (match branches_opt with
          | None ->
            // Unsupported filler shape. Sound fallback: leaf.
            GP_BGP (single_type_bgp subj op)
          | Some branches ->
            // Wrap bad_bgp_ggp with successive FILTER NOT EXISTS
            // for each branch Ci: FILTER NOT EXISTS { bad a Ci }.
            let wrap_one (cur : group_graph_pattern) (branch : pattern_term)
                         : group_graph_pattern =
              // Use expand_ce_subject recursively so that a named
              // class gets `bad a Ci` and a bnode branch (if we ever
              // widen support) gets the right shape.
              let branch_ggp = expand_ce_subject b bad_subj branch (n - 1) in
              GP_Filter (E_NotExists branch_ggp) cur in
            let fne_body : group_graph_pattern =
              List.Tot.fold_left wrap_one bad_bgp_ggp branches in
            let outer_fne_ggp : group_graph_pattern =
              GP_Filter (E_NotExists fne_body) anchor_ggp in
            outer_fne_ggp)
       | _, _ ->
         // Malformed restriction (no onProperty, or a variable
         // predicate): fall back to leaf.
         GP_BGP (single_type_bgp subj op))
    | Some (k, CE_MinCardinality) ->
      // Minimum-cardinality restriction:
      //   _:r owl:onProperty :p ;
      //       owl:minCardinality N            (unqualified)
      //       (or owl:minQualifiedCardinality N ; owl:onClass :C)
      //
      // Encoding strategy (sound under OWL-Direct for N <= 1):
      //   N = 0  -> trivially satisfied. We emit GP_Empty so the
      //            consumer rewrite contributes no constraint.
      //   N >= 1 -> emit a single existential anchor triple
      //              `subj :p ?_mc_<k>`.
      //            For qualified cardinality we additionally constrain
      //            the anchor: `?_mc_<k> rdf:type :C`.
      //            This is exactly the `someValuesFrom` shape — sound
      //            but over-approximates for N >= 2 (those cases need
      //            a chain of distinct vars; out of scope here).
      let on_prop_opt = bgp_find_first_obj b k owl_onProperty_iri in
      let on_class_opt = bgp_find_first_obj b k owl_onClass_iri in
      let card_opt : option int =
        match bgp_find_first_obj b k owl_minCardinality_iri with
        | Some (PT_Literal l) -> parse_int_string (lit_lexical l)
        | _ ->
          match bgp_find_first_obj b k owl_minQualifiedCardinality_iri with
          | Some (PT_Literal l) -> parse_int_string (lit_lexical l)
          | _ -> None in
      (match on_prop_opt, card_opt with
       | Some (PT_IRI p_iri), Some card_n ->
         if card_n <= 0 then GP_Empty
         else
           let fresh_name : string = "_mc_" ^ k in
           let fresh_term : pattern_term    = PT_Var fresh_name in
           let fresh_subj : pattern_subject = PS_Var fresh_name in
           let prop_triple : triple_pattern =
             { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = fresh_term } in
           let prop_ggp : group_graph_pattern = GP_BGP [prop_triple] in
           (match on_class_opt with
            | Some filler ->
              let cls_ggp = expand_ce_subject b fresh_subj filler (n - 1) in
              join_ggps [prop_ggp; cls_ggp]
            | None -> prop_ggp)
       | _, _ -> GP_BGP (single_type_bgp subj op))
    | Some (k, CE_MaxCardinality) ->
      // Maximum-cardinality restriction:
      //   _:r owl:onProperty :p ;
      //       owl:maxCardinality N            (unqualified)
      //       (or owl:maxQualifiedCardinality N ; owl:onClass :C)
      //
      // Encoding strategy:
      //   N = 0  -> emit FILTER NOT EXISTS { subj :p ?_mxc_<k> }.
      //            Anchored on GP_Empty so the constraint is the
      //            whole group pattern.
      //            Qualified: FNE { subj :p ?fresh . ?fresh a :C }.
      //   N = 1, qualified (onClass :C present) ->
      //            Bind against the canonical maxqc1 restriction
      //            materialised by RDF.Graph.Executable's
      //            owl_rule_cls_maxqc1. That rule emits, for every
      //            (x P y) with (y rdf:type C) where the count of
      //            P-successors-typed-C of x is <= 1, a canonical
      //            bnode _:rMAXQC1(P,C) carrying the four shape
      //            triples (rdf:type owl:Restriction; owl:onProperty P;
      //            owl:maxQualifiedCardinality 1; owl:onClass C) plus
      //            the membership (x rdf:type _:rMAXQC1).
      //            The query CE has the SAME shape but a DIFFERENT
      //            (anonymous, query-side) bnode id. So leaf form
      //            (subj rdf:type op) cannot match — the two bnodes
      //            are not unified by SPARQL bnode-as-existential
      //            semantics. Instead we discover any restriction in
      //            the data with the same neighbourhood by emitting
      //            the four shape triples against a fresh variable
      //            ?_mxc_<k>, then assert (subj rdf:type ?_mxc_<k>).
      //            This binds the canonical when present and yields
      //            the correct subjects (parent7 / hasChild max 1
      //            Female -> exactly the individuals whose hasChild-
      //            successors typed Female number at most 1).
      //   N = 1, unqualified (no onClass) -> still leaf fallback.
      //            owl_rule_cls_maxqc1 only fires for the qualified
      //            shape (it requires a NAMED filler class), so the
      //            data does not carry a corresponding canonical to
      //            bind against. Sound but won't bind useful results
      //            without DL reasoning.
      //   N >= 2 -> NOT IMPLEMENTED. Fall back to the leaf form.
      //            Larger-N encoding needs n+1 distinct vars + pairwise
      //            FILTERs and is deferred.
      let on_prop_opt = bgp_find_first_obj b k owl_onProperty_iri in
      let on_class_opt = bgp_find_first_obj b k owl_onClass_iri in
      let card_opt : option int =
        match bgp_find_first_obj b k owl_maxCardinality_iri with
        | Some (PT_Literal l) -> parse_int_string (lit_lexical l)
        | _ ->
          match bgp_find_first_obj b k owl_maxQualifiedCardinality_iri with
          | Some (PT_Literal l) -> parse_int_string (lit_lexical l)
          | _ -> None in
      (match on_prop_opt, card_opt with
       | Some (PT_IRI p_iri), Some card_n ->
         if card_n = 0 then
           let fresh_name : string = "_mxc_" ^ k in
           let fresh_term : pattern_term    = PT_Var fresh_name in
           let fresh_subj : pattern_subject = PS_Var fresh_name in
           let prop_triple : triple_pattern =
             { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = fresh_term } in
           let prop_ggp : group_graph_pattern = GP_BGP [prop_triple] in
           let inner_ggp : group_graph_pattern =
             match on_class_opt with
             | Some filler ->
               let cls_ggp = expand_ce_subject b fresh_subj filler (n - 1) in
               join_ggps [prop_ggp; cls_ggp]
             | None -> prop_ggp in
           GP_Filter (E_NotExists inner_ggp) GP_Empty
         else if card_n = 1 then
           // N=1 qualified: bind to canonical owl_rule_cls_maxqc1
           // materialisation via shape discovery. Unqualified N=1
           // falls back to leaf (no canonical to bind against).
           match on_class_opt with
           | Some (PT_IRI c_iri) ->
             let restr_name : string = "_mxqc1_r_" ^ k in
             let restr_term : pattern_term    = PT_Var restr_name in
             let restr_subj : pattern_subject = PS_Var restr_name in
             let shape_type_triple : triple_pattern =
               { tp_s = restr_subj; tp_p = PT_IRI rdf_type_iri;
                 tp_o = PT_IRI owl_Restriction_iri } in
             let shape_onprop_triple : triple_pattern =
               { tp_s = restr_subj; tp_p = PT_IRI owl_onProperty_iri;
                 tp_o = PT_IRI p_iri } in
             let shape_maxqc_triple : triple_pattern =
               { tp_s = restr_subj;
                 tp_p = PT_IRI owl_maxQualifiedCardinality_iri;
                 tp_o = PT_Literal one_nonNegInteger_literal } in
             let shape_onclass_triple : triple_pattern =
               { tp_s = restr_subj; tp_p = PT_IRI owl_onClass_iri;
                 tp_o = PT_IRI c_iri } in
             let memb_triple : triple_pattern =
               { tp_s = subj; tp_p = PT_IRI rdf_type_iri;
                 tp_o = restr_term } in
             GP_BGP [ shape_type_triple;
                      shape_onprop_triple;
                      shape_maxqc_triple;
                      shape_onclass_triple;
                      memb_triple ]
           | _ ->
             // Unqualified maxCard 1, or non-IRI filler: leaf fallback.
             GP_BGP (single_type_bgp subj op)
         else
           // N < 0 or N >= 2: leaf fallback.
           GP_BGP (single_type_bgp subj op)
       | _, _ -> GP_BGP (single_type_bgp subj op))
    | Some (k, CE_ExactCardinality) ->
      // Exact-cardinality restriction:
      //   _:r owl:onProperty :p ;
      //       owl:cardinality N         (unqualified)
      //       (or owl:qualifiedCardinality N ; owl:onClass :C)
      //
      // Semantically equivalent to (min N AND max N). We compose by
      // hand-rolling the min and max encodings rather than recursing,
      // because the predicate keyword on the BGP differs.
      //   N = 0  -> just the max=0 FNE constraint.
      //   N = 1  -> existential anchor (min=1) AND FNE-of-2-distinct.
      //            We emit the min=1 anchor only; the max=1 side is
      //            deferred (same reason as CE_MaxCardinality with
      //            N >= 1). Sound but incomplete.
      //   other  -> leaf fallback.
      let on_prop_opt = bgp_find_first_obj b k owl_onProperty_iri in
      let on_class_opt = bgp_find_first_obj b k owl_onClass_iri in
      let card_opt : option int =
        match bgp_find_first_obj b k owl_cardinality_iri with
        | Some (PT_Literal l) -> parse_int_string (lit_lexical l)
        | _ ->
          match bgp_find_first_obj b k owl_qualifiedCardinality_iri with
          | Some (PT_Literal l) -> parse_int_string (lit_lexical l)
          | _ -> None in
      (match on_prop_opt, card_opt with
       | Some (PT_IRI p_iri), Some card_n ->
         if card_n < 0 then GP_BGP (single_type_bgp subj op)
         else if card_n = 0 then
           // Max-zero FNE.
           let fresh_name : string = "_exc_" ^ k in
           let fresh_term : pattern_term    = PT_Var fresh_name in
           let fresh_subj : pattern_subject = PS_Var fresh_name in
           let prop_triple : triple_pattern =
             { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = fresh_term } in
           let prop_ggp : group_graph_pattern = GP_BGP [prop_triple] in
           let inner_ggp : group_graph_pattern =
             match on_class_opt with
             | Some filler ->
               let cls_ggp = expand_ce_subject b fresh_subj filler (n - 1) in
               join_ggps [prop_ggp; cls_ggp]
             | None -> prop_ggp in
           GP_Filter (E_NotExists inner_ggp) GP_Empty
         else
           // card_n >= 1 — emit min-side anchor only.
           let fresh_name : string = "_exc_" ^ k in
           let fresh_term : pattern_term    = PT_Var fresh_name in
           let fresh_subj : pattern_subject = PS_Var fresh_name in
           let prop_triple : triple_pattern =
             { tp_s = subj; tp_p = PT_IRI p_iri; tp_o = fresh_term } in
           let prop_ggp : group_graph_pattern = GP_BGP [prop_triple] in
           (match on_class_opt with
            | Some filler ->
              let cls_ggp = expand_ce_subject b fresh_subj filler (n - 1) in
              join_ggps [prop_ggp; cls_ggp]
            | None -> prop_ggp)
       | _, _ -> GP_BGP (single_type_bgp subj op))
    | Some (k, CE_ComplementOf) ->
      // Class-complement: the bnode shape `[a owl:Class ;
      //                                      owl:complementOf <C>]`.
      // (paper-sparqldl-Q3 inner CE.)
      //
      // OWL-Direct semantics:
      //   subj rdf:type (complementOf C)  iff  subj is NOT a C.
      // Open-world rewriter cannot just emit `FILTER NOT EXISTS
      // { subj a C }` (that is closed-world / absence-of-evidence).
      // Instead, we emit the **disjointness-targeting** rewrite that
      // mirrors Tableau.fst's `has_disjoint_witness` bridge:
      //
      //   { subj rdf:type ?_co_<k> .
      //     ?_co_<k> owl:disjointWith C }
      //   UNION
      //   { subj rdf:type ?_co_<k> .
      //     C owl:disjointWith ?_co_<k> }
      //
      // Soundness (one direction, monotonic): if subj has a type ?d
      // and ?d is disjoint from C in either direction, then subj is
      // provably not in C — i.e. subj is a member of (complementOf C).
      // Never derives a binding that isn't entailed.
      //
      // Incompleteness: complementOf can also be derived from explicit
      // negative-type assertions or from the closure-side
      // disjointWith propagation rule (gap 3 in Shin's diagnosis);
      // those paths are deliberately not synthesised here.
      //
      // Edge case: if the complement target is not a named class
      // (e.g. a bnode CE), we fall through to the leaf form. Nested
      // complementOf-of-CE is out of scope for this agent.
      (match complementOf_target b k with
       | Some (PT_IRI _) ->
         let target_term : pattern_term =
           (match complementOf_target b k with
            | Some t -> t
            | None   -> PT_IRI rdf_nil_iri  // unreachable; satisfies F* exhaustiveness
           ) in
         let fresh_name : string = "_co_" ^ k in
         let fresh_subj : pattern_subject = PS_Var fresh_name in
         let fresh_term : pattern_term    = PT_Var fresh_name in
         // Triple A: subj rdf:type ?fresh
         let type_triple : triple_pattern =
           { tp_s = subj; tp_p = PT_IRI rdf_type_iri; tp_o = fresh_term } in
         // Forward branch: ?fresh owl:disjointWith <C>
         let forward_triple : triple_pattern =
           { tp_s = fresh_subj;
             tp_p = PT_IRI owl_disjointWith_iri;
             tp_o = target_term } in
         let forward_bgp : bgp = [type_triple; forward_triple] in
         // Reverse branch: <C> owl:disjointWith ?fresh — needs <C> as a
         // pattern_subject. PT_IRI converts to PS_IRI; non-IRI targets
         // can't be the subject of a triple pattern, so we filter.
         let reverse_branch_opt : option bgp =
           match target_term with
           | PT_IRI c_iri ->
             let target_subj : pattern_subject = PS_IRI c_iri in
             let reverse_triple : triple_pattern =
               { tp_s = target_subj;
                 tp_p = PT_IRI owl_disjointWith_iri;
                 tp_o = fresh_term } in
             Some [type_triple; reverse_triple]
           | _ -> None in
         (match reverse_branch_opt with
          | Some reverse_bgp ->
            // Two-branch UNION, wrapped in DISTINCT sub-select so a
            // single subj that has two disjoint witnesses contributes
            // one row (matches OWL set-theoretic semantics; same
            // discipline as the unionOf / Section 8b code).
            wrap_distinct_over_ggp
              (GP_Union (GP_BGP forward_bgp) (GP_BGP reverse_bgp))
          | None ->
            // Target wasn't a named-class IRI — emit just the forward
            // branch (still sound, just incomplete).
            GP_BGP forward_bgp)
       | _ ->
         // Non-IRI complement target (e.g. bnode CE): leaf fallback.
         // Sound — won't bind anything, but never adds wrong solutions.
         GP_BGP (single_type_bgp subj op))

// Top-level marker-set: the set of keys that are "top-level CE
// markers reachable from ?x rdf:type m" — i.e. the object of some
// rdf:type triple whose predicate is rdf:type. Every other marker
// in the BGP is a nested one and will be consumed by expansion.
let rec collect_top_markers_acc (b : bgp) (markers : list (string & ce_combinator))
                                 (acc : list string)
  : Tot (list string) (decreases b) =
  match b with
  | [] -> List.Tot.rev acc
  | tp :: rest ->
    (match tp.tp_p with
     | PT_IRI p ->
       if p = rdf_type_iri then
         (match pt_marker_key tp.tp_o with
          | Some k ->
            let is_marker = List.Tot.existsb (fun (k', _) -> k' = k) markers in
            if is_marker && not (List.Tot.mem k acc)
            then collect_top_markers_acc rest markers (k :: acc)
            else collect_top_markers_acc rest markers acc
          | None -> collect_top_markers_acc rest markers acc)
       else collect_top_markers_acc rest markers acc
     | _ -> collect_top_markers_acc rest markers acc)

let collect_top_markers (b : bgp) (markers : list (string & ce_combinator))
  : list string =
  collect_top_markers_acc b markers []

// Does this triple consume any top-level marker (i.e., is it a
// `?x rdf:type m` where m is one of the top markers)?
let is_any_top_consumer (top_markers : list string) (tp : triple_pattern) : bool =
  match tp.tp_p, pt_marker_key tp.tp_o with
  | PT_IRI p, Some k -> p = rdf_type_iri && List.Tot.mem k top_markers
  | _, _ -> false

// Is this triple part of the bookkeeping for ANY marker (including
// nested)? A triple (s,p,o) is bookkeeping when:
//   s is a marker key in `markers` AND p is one of the CE meta-preds
//   (owl:intersectionOf, owl:unionOf, rdf:type owl:Class), OR
//   s is on the rdf:first/rdf:rest chain of any marker's list.
let is_nested_bookkeeping
      (markers : list (string & ce_combinator))
      (all_chain_keys : list string)
      (tp : triple_pattern) : bool =
  match ps_marker_key tp.tp_s, tp.tp_p with
  | Some sk, PT_IRI p ->
    let is_marker = List.Tot.existsb (fun (k', _) -> k' = sk) markers in
    let is_on_chain = List.Tot.mem sk all_chain_keys in
    // Marker-meta triples get stripped if the subject is a marker.
    // owl:onProperty / owl:someValuesFrom / (rdf:type owl:Restriction)
    // are stripped alongside intersectionOf / unionOf / owl:Class so
    // that restriction CEs don't leak their bookkeeping into the
    // residue BGP.
    let marker_meta =
      is_marker &&
      (p = owl_intersectionOf_iri ||
       p = owl_unionOf_iri ||
       p = owl_complementOf_iri ||
       p = owl_onProperty_iri ||
       p = owl_someValuesFrom_iri ||
       p = owl_allValuesFrom_iri ||
       p = owl_minCardinality_iri ||
       p = owl_maxCardinality_iri ||
       p = owl_cardinality_iri ||
       p = owl_minQualifiedCardinality_iri ||
       p = owl_maxQualifiedCardinality_iri ||
       p = owl_qualifiedCardinality_iri ||
       p = owl_onClass_iri ||
       (p = rdf_type_iri &&
        (match tp.tp_o with
         | PT_IRI oi -> oi = owl_Class_iri || oi = owl_Restriction_iri
         | _ -> false))) in
    // Chain triples get stripped whenever the subject is on some
    // marker's rdf:first/rdf:rest chain. A subject can be BOTH a
    // marker and a chain cell (nested-CE case where the parser
    // reuses the bnode as an inner list operand); both conditions
    // must be checked with OR, not else-if.
    let chain_meta =
      is_on_chain && (p = rdf_first_iri || p = rdf_rest_iri) in
    marker_meta || chain_meta
  | _, _ -> false

// Compute the union of collection chain-keys for all markers in
// `markers`. This is the list of bnode keys that belong to some
// rdf:first/rdf:rest chain used by one of the markers.
let all_chain_keys_for_markers (b : bgp) (markers : list (string & ce_combinator))
  : list string =
  let step (acc : list string) (km : string & ce_combinator)
           : list string =
    let (k, _) = km in
    // Find the list-head for this marker under either predicate.
    let head_int = bgp_find_first_obj b k owl_intersectionOf_iri in
    let head_uni = bgp_find_first_obj b k owl_unionOf_iri in
    let head_opt = match head_int with
                   | Some h -> Some h
                   | None -> head_uni in
    (match head_opt with
     | None -> acc
     | Some hd ->
       let chain = collection_chain_keys b hd in
       List.Tot.fold_left
         (fun a c -> if List.Tot.mem c a then a else List.Tot.append a [c])
         acc
         chain) in
  List.Tot.fold_left step [] markers

// Rewrite a BGP with (possibly nested) CE markers. Top-level
// consumers each expand via `expand_ce_subject` to a GGP; the
// residue (non-bookkeeping, non-consumer triples) is the shared
// BGP that gets joined alongside.
let rewrite_bgp_nested (b : bgp) : group_graph_pattern =
  let markers     = find_markers b in
  match markers with
  | [] -> GP_BGP b
  | _ ->
    let top_markers = collect_top_markers b markers in
    (match top_markers with
     | [] ->
       // Markers exist in the BGP but none are "top-level" — there
       // is no ?x rdf:type m consumer we can safely rewrite. Fall
       // through to the flat rewriter (which also bails on this
       // shape, but keeps the BGP unchanged).
       rewrite_bgp_flat b
     | _ ->
       let chain_keys  = all_chain_keys_for_markers b markers in
       // Build the residue: keep every triple that is not a
       // bookkeeping triple of any marker AND not a consumer of a
       // top-level marker.
       let residue =
         List.Tot.fold_left
           (fun acc tp ->
             if is_nested_bookkeeping markers chain_keys tp then acc
             else if is_any_top_consumer top_markers tp then acc
             else List.Tot.append acc [tp])
           []
           b in
       // For each consumer, expand its marker using the current BGP
       // (so `ce_combinator_for_term` / `extract_flat_*` still see
       // the nested CE bookkeeping). Start fuel at a safe upper
       // bound on recursion depth: length of markers + 1.
       let fuel : nat = List.Tot.length markers + 1 in
       let consumer_ggps : list group_graph_pattern =
         List.Tot.fold_left
           (fun acc tp ->
             if is_any_top_consumer top_markers tp
             then List.Tot.append acc [expand_ce_subject b tp.tp_s tp.tp_o fuel]
             else acc)
           []
           b in
       // Stitch residue + consumer expansions.
       match consumer_ggps with
       | [] ->
         // No top consumer triples (shouldn't happen given the
         // top_markers check, but stay total).
         if List.Tot.length residue = 0 then GP_Empty else GP_BGP residue
       | _ ->
         let base : group_graph_pattern =
           if List.Tot.length residue = 0 then GP_Empty else GP_BGP residue in
         // Fold consumer GGPs into `base`. Coalesce BGP+BGP to a
         // single BGP when possible (preserves Phase 3 shape for
         // paper-sparqldl-Q2, which becomes a single BGP join of
         // [?x :name ?y; ?x a :Student; ?x a :Employee]).
         List.Tot.fold_left
           (fun acc g -> match acc, g with
                         | GP_Empty, _ -> g
                         | GP_BGP ba, GP_BGP bg -> GP_BGP (List.Tot.append ba bg)
                         | _, _ -> GP_Join acc g)
           base
           consumer_ggps)

// ------------------------------------------------------------------
// Section 9. Recurse over the group_graph_pattern tree. All non-BGP
// constructors are structurally preserved; only GP_BGP nodes are
// rewritten.
//
// IMPORTANT: the SPARQL parser splits BGPs apart on every period in
// the source. A single user-level BGP like
//   ?x a [ owl:intersectionOf (:A :B) ] .
// parses to a GP_Join tree of ~4 one-/two-triple GP_BGPs. The CE
// marker (owl:intersectionOf) and the rdf:first/rdf:rest chain live
// in different leaves, so rewrite_bgp_nested on any single leaf
// finds no markers. We therefore first FLATTEN contiguous
// GP_Join-of-GP_BGPs into a single GP_BGP before rewriting, which
// preserves SPARQL semantics (GP_Join of two BGPs = BGP-concat) and
// gives the rewriter the full picture.
// ------------------------------------------------------------------

// Two-operand coalesce: if both operands are GP_BGP, merge into a
// single GP_BGP by triple-list concatenation (preserves SPARQL
// semantics of GP_Join). Otherwise, preserve the GP_Join tree but
// also detect the left-deep shape where one side is a BGP and the
// other is a GP_Join whose left-spine starts with a GP_BGP; we pull
// the BGPs together in that case too. This coalesces arbitrary
// contiguous GP_Join-of-GP_BGPs into a single GP_BGP.
let coalesce_join (na : group_graph_pattern) (nb : group_graph_pattern)
  : group_graph_pattern =
  match na, nb with
  | GP_BGP ba, GP_BGP bb ->
    GP_BGP (List.Tot.append ba bb)
  | GP_BGP ba, GP_Join (GP_BGP bb) rest ->
    GP_Join (GP_BGP (List.Tot.append ba bb)) rest
  | GP_Join left_spine (GP_BGP ba), GP_BGP bb ->
    GP_Join left_spine (GP_BGP (List.Tot.append ba bb))
  | _, _ -> GP_Join na nb

// Normalise a GGP: recurse structurally, then coalesce adjacent
// GP_BGPs under GP_Join. Accepted by F* with `decreases g` — each
// recursive call is on a structurally smaller constructor argument
// of `g`.
let rec normalise_joins (g : group_graph_pattern)
  : Tot group_graph_pattern (decreases g) =
  match g with
  | GP_BGP b           -> GP_BGP b
  | GP_Join a b        ->
    coalesce_join (normalise_joins a) (normalise_joins b)
  | GP_LeftJoin a b e  -> GP_LeftJoin (normalise_joins a) (normalise_joins b) e
  | GP_Filter e a      -> GP_Filter e (normalise_joins a)
  | GP_Union a b       -> GP_Union (normalise_joins a) (normalise_joins b)
  | GP_Graph gt a      -> GP_Graph gt (normalise_joins a)
  | GP_Minus a b       -> GP_Minus (normalise_joins a) (normalise_joins b)
  | GP_Bind e v a      -> GP_Bind e v (normalise_joins a)
  | GP_Values vs rs    -> GP_Values vs rs
  | GP_Service i a s   -> GP_Service i (normalise_joins a) s
  | GP_ServiceVar v a s -> GP_ServiceVar v (normalise_joins a) s
  | GP_SubSelect q     -> GP_SubSelect q
  | GP_PropertyPath s pp o -> GP_PropertyPath s pp o
  | GP_Empty           -> GP_Empty

// Rewrite recursion on the group-graph-pattern tree. SubSelect bodies
// are deliberately NOT descended into in Phase 3 — if that matters for
// a future test we can extend here. F* accepts `decreases g` on
// structural recursion into the group_graph_pattern constructor
// arguments (see e.g. ggp_has_var / rewrite_query_bnodes_pattern).
let rec rewrite_ggp (g : group_graph_pattern)
  : Tot group_graph_pattern (decreases g) =
  match g with
  | GP_BGP b           -> rewrite_bgp_nested b
  | GP_Join a b        -> GP_Join (rewrite_ggp a) (rewrite_ggp b)
  | GP_LeftJoin a b e  -> GP_LeftJoin (rewrite_ggp a) (rewrite_ggp b) e
  | GP_Filter e a      -> GP_Filter e (rewrite_ggp a)
  | GP_Union a b       -> GP_Union (rewrite_ggp a) (rewrite_ggp b)
  | GP_Graph gt a      -> GP_Graph gt (rewrite_ggp a)
  | GP_Minus a b       -> GP_Minus (rewrite_ggp a) (rewrite_ggp b)
  | GP_Bind e v a      -> GP_Bind e v (rewrite_ggp a)
  | GP_Values vs rs    -> GP_Values vs rs
  | GP_Service i a s   -> GP_Service i (rewrite_ggp a) s
  | GP_ServiceVar v a s -> GP_ServiceVar v (rewrite_ggp a) s
  | GP_SubSelect q     -> GP_SubSelect q  // sub-select intentionally not rewritten here; Phase 4
  | GP_PropertyPath s pp o -> GP_PropertyPath s pp o
  | GP_Empty           -> GP_Empty

// ------------------------------------------------------------------
// Section 10. Top-level query rewrite. Only the WHERE pattern is
// rewritten; the query_form and all other fields are untouched.
// ------------------------------------------------------------------

// Section 10a. Detect whether a pattern contains any CE-marker predicate
// the rewriter would recognise. Used to decide whether rewrite_query's
// sm_distinct override is appropriate (only for OWL-entailment queries
// that actually exercise the rewriter — not every SELECT routed through
// OWL_QueryEval). Scans the ORIGINAL pattern before rewrite so we see
// the CE predicate rather than the post-rewrite GP_Union it became.

let tp_is_ce_marker_predicate (tp : triple_pattern) : bool =
  match tp.tp_p with
  | PT_IRI p ->
      p = owl_intersectionOf_iri ||
      p = owl_unionOf_iri ||
      p = owl_complementOf_iri ||
      p = owl_someValuesFrom_iri ||
      p = owl_allValuesFrom_iri ||
      p = owl_minCardinality_iri ||
      p = owl_maxCardinality_iri ||
      p = owl_cardinality_iri ||
      p = owl_minQualifiedCardinality_iri ||
      p = owl_maxQualifiedCardinality_iri ||
      p = owl_qualifiedCardinality_iri
  | _ -> false

let bgp_has_ce_marker (b : bgp) : bool =
  List.Tot.existsb tp_is_ce_marker_predicate b

let rec ggp_has_ce_marker (g : group_graph_pattern)
  : Tot bool (decreases g) =
  match g with
  | GP_BGP b           -> bgp_has_ce_marker b
  | GP_Join a b        -> ggp_has_ce_marker a || ggp_has_ce_marker b
  | GP_LeftJoin a b _  -> ggp_has_ce_marker a || ggp_has_ce_marker b
  | GP_Filter _ a      -> ggp_has_ce_marker a
  | GP_Union a b       -> ggp_has_ce_marker a || ggp_has_ce_marker b
  | GP_Graph _ a       -> ggp_has_ce_marker a
  | GP_Minus a b       -> ggp_has_ce_marker a || ggp_has_ce_marker b
  | GP_Bind _ _ a      -> ggp_has_ce_marker a
  | GP_Values _ _      -> false
  | GP_Service _ a _   -> ggp_has_ce_marker a
  | GP_ServiceVar _ a _ -> ggp_has_ce_marker a
  | GP_SubSelect _     -> false   // sub-select bodies not inspected
  | GP_PropertyPath _ _ _ -> false
  | GP_Empty           -> false

let rewrite_query (q : query) : query =
  // Normalise GP_Join / GP_BGP chains into single GP_BGPs first so
  // the CE-rewriter sees the full set of triples in one BGP. Without
  // this step, the SPARQL parser's habit of splitting BGPs on every
  // period leaves the CE marker (owl:intersectionOf _) and its
  // rdf:first/rdf:rest chain in different BGP leaves and the
  // rewriter finds nothing. See simple1 dump for the canonical
  // example.
  //
  // DISTINCT for OWL set-theoretic unionOf semantics is now applied
  // *locally* at each CE union-emission site via
  // `wrap_distinct_over_ggp` (see Section 6 / Section 8b). The
  // outer query modifier is therefore left untouched here, which
  // preserves bag semantics for non-CE queries that go through
  // OWL_QueryEval (bind / bindings / subquery / property-path
  // tests). `ggp_has_ce_marker` is kept for diagnostics but no
  // longer drives a top-level sm_distinct flip.
  { q with q_pattern = rewrite_ggp (normalise_joins q.q_pattern) }

// Convenience alias expected by the scoping doc ("rewrite_query" is
// the top-level entrypoint).
let rewrite_query_for_owl_direct (q : query) : query = rewrite_query q
