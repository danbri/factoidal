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

// CE_SomeValuesFrom marks a bnode that is the subject of an
// owl:someValuesFrom triple — the standard shape of an existential
// restriction (`_:r a owl:Restriction ; owl:onProperty :p ;
// owl:someValuesFrom <filler>`). The combinator carries no payload
// here; onProperty / someValuesFrom triples are looked up on demand
// from the BGP at expansion time, which keeps this type first-order
// (and avoids a recursive type over pattern_term).
type ce_combinator = | CE_Intersect | CE_Union | CE_SomeValuesFrom

let combinator_of_pred (p : wf_iri) : option ce_combinator =
  if p = owl_intersectionOf_iri then Some CE_Intersect
  else if p = owl_unionOf_iri then Some CE_Union
  else if p = owl_someValuesFrom_iri then Some CE_SomeValuesFrom
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

// Is this pattern_term a CE marker in BGP b (subject of intersectionOf
// or unionOf)? Returns its key and combinator if so.
let ce_combinator_for_term (b : bgp) (pt : pattern_term)
  : option (string & ce_combinator) =
  match pt_marker_key pt with
  | None -> None
  | Some k ->
    let markers = find_markers b in
    let rec lookup (ms : list (string & ce_combinator))
      : Tot (option ce_combinator) (decreases ms) =
      match ms with
      | [] -> None
      | (k', c) :: rest -> if k' = k then Some c else lookup rest in
    match lookup markers with
    | None -> None
    | Some c -> Some (k, c)

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
         // the left spine, fold the rest with GP_Union.
         match branches with
         | []  -> GP_BGP (single_type_bgp subj op)
         | [g] -> g
         | g :: tl ->
           List.Tot.fold_left (fun acc br -> GP_Union acc br) g tl)
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
       p = owl_onProperty_iri ||
       p = owl_someValuesFrom_iri ||
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
  | GP_SubSelect q     -> GP_SubSelect q  // sub-select intentionally not rewritten here; Phase 4
  | GP_PropertyPath s pp o -> GP_PropertyPath s pp o
  | GP_Empty           -> GP_Empty

// ------------------------------------------------------------------
// Section 10. Top-level query rewrite. Only the WHERE pattern is
// rewritten; the query_form and all other fields are untouched.
// ------------------------------------------------------------------

let rewrite_query (q : query) : query =
  // Normalise GP_Join / GP_BGP chains into single GP_BGPs first so
  // the CE-rewriter sees the full set of triples in one BGP. Without
  // this step, the SPARQL parser's habit of splitting BGPs on every
  // period leaves the CE marker (owl:intersectionOf _) and its
  // rdf:first/rdf:rest chain in different BGP leaves and the
  // rewriter finds nothing. See simple1 dump for the canonical
  // example.
  { q with q_pattern = rewrite_ggp (normalise_joins q.q_pattern) }

// Convenience alias expected by the scoping doc ("rewrite_query" is
// the top-level entrypoint).
let rewrite_query_for_owl_direct (q : query) : query = rewrite_query q
