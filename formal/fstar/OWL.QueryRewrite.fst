module OWL.QueryRewrite

// Phase 3 of the entailment plan (docs/designissues/2026-04-23-entailment-plan.md):
// query-class-expression rewrite for FLAT owl:intersectionOf and
// owl:unionOf anonymous class expressions that appear as the object of
// rdf:type in a SPARQL WHERE clause.
//
// Target tests (entailment suite): simple1, simple4, paper-sparqldl-Q2.
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

let build_union_ggp (branch_bgps : list bgp) : group_graph_pattern =
  match branch_bgps with
  | [] -> GP_Empty
  | [b] -> GP_BGP b
  | b1 :: rest ->
    let head = GP_BGP b1 in
    let rec_branches : list group_graph_pattern =
      List.Tot.fold_left (fun acc b -> List.Tot.append acc [GP_BGP b]) [] rest in
    union_ladder head rec_branches

// ------------------------------------------------------------------
// Section 7. Identify marker candidates inside a BGP. A key is a
// "flat class-expression marker" iff there is a triple
//   (m, owl:intersectionOf, _) or (m, owl:unionOf, _)
// in the BGP. Returns a list of (key, combinator) pairs, in the
// order encountered.
// ------------------------------------------------------------------

type ce_combinator = | CE_Intersect | CE_Union

let combinator_of_pred (p : wf_iri) : option ce_combinator =
  if p = owl_intersectionOf_iri then Some CE_Intersect
  else if p = owl_unionOf_iri then Some CE_Union
  else None

let rec find_markers_acc (b : bgp) (acc : list (string & ce_combinator))
  : Tot (list (string & ce_combinator)) (decreases b) =
  match b with
  | [] -> List.Tot.rev acc
  | tp :: rest ->
    (match ps_marker_key tp.tp_s, tp.tp_p with
     | Some k, PT_IRI p ->
       (match combinator_of_pred p with
        | Some c ->
          // Avoid duplicates: if marker already in acc, skip
          let dup = List.Tot.existsb (fun (k', _) -> k' = k) acc in
          if dup then find_markers_acc rest acc
          else find_markers_acc rest ((k, c) :: acc)
        | None -> find_markers_acc rest acc)
     | _, _ -> find_markers_acc rest acc)

let find_markers (b : bgp) : list (string & ce_combinator) =
  find_markers_acc b []

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
// Section 9. Recurse over the group_graph_pattern tree. All non-BGP
// constructors are structurally preserved; only GP_BGP nodes are
// rewritten. Fuel bounds the recursion (the GGP tree is always
// finite, but F* needs a decreasing measure through the mutual
// recursion between GGP and query).
// ------------------------------------------------------------------

// Rewrite recursion on the group-graph-pattern tree. SubSelect bodies
// are deliberately NOT descended into in Phase 3 — if that matters for
// a future test we can extend here. F* accepts `decreases g` on
// structural recursion into the group_graph_pattern constructor
// arguments (see e.g. ggp_has_var / rewrite_query_bnodes_pattern).
let rec rewrite_ggp (g : group_graph_pattern)
  : Tot group_graph_pattern (decreases g) =
  match g with
  | GP_BGP b           -> rewrite_bgp_flat b
  | GP_Join a b        -> GP_Join (rewrite_ggp a) (rewrite_ggp b)
  | GP_LeftJoin a b e  -> GP_LeftJoin (rewrite_ggp a) (rewrite_ggp b) e
  | GP_Filter e a      -> GP_Filter e (rewrite_ggp a)
  | GP_Union a b       -> GP_Union (rewrite_ggp a) (rewrite_ggp b)
  | GP_Graph gt a      -> GP_Graph gt (rewrite_ggp a)
  | GP_Minus a b       -> GP_Minus (rewrite_ggp a) (rewrite_ggp b)
  | GP_Bind e v a      -> GP_Bind e v (rewrite_ggp a)
  | GP_Values vs rs    -> GP_Values vs rs
  | GP_Service i a s   -> GP_Service i (rewrite_ggp a) s
  | GP_SubSelect q     -> GP_SubSelect q  // sub-select intentionally not rewritten here; Phase 4
  | GP_PropertyPath s pp o -> GP_PropertyPath s pp o
  | GP_Empty           -> GP_Empty

// ------------------------------------------------------------------
// Section 10. Top-level query rewrite. Only the WHERE pattern is
// rewritten; the query_form and all other fields are untouched.
// ------------------------------------------------------------------

let rewrite_query (q : query) : query =
  { q with q_pattern = rewrite_ggp q.q_pattern }

// Convenience alias expected by the scoping doc ("rewrite_query" is
// the top-level entrypoint).
let rewrite_query_for_owl_direct (q : query) : query = rewrite_query q
