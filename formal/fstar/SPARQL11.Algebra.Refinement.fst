module SPARQL11.Algebra.Refinement

// ===================================================================
// REFINEMENT of the shipping SPARQL evaluator against the independent
// declarative algebra semantics of SPARQL11.Algebra.Spec.
//
// Every theorem here names a SHIPPING function of SPARQL11.Algebra --
// the function the engine actually calls -- and no model of one. The
// spec side names only SPARQL11.Algebra.Spec, which in turn depends on
// RDF.Term alone. So a reader can check the two sides were written
// against different things.
//
// Issue #313 gate. Companion to RDF.Entailment.Simple.Refinement.fst
// (2026-07-29), and built with the same method: prove at the level the
// engine actually parameterizes, hunt for the fragment hypothesis, and
// when the unconditional statement is FALSE, prove that it is false
// with an explicit witness rather than weakening the specification.
//
// -------------------------------------------------------------------
// FINDINGS -- READ THESE BEFORE READING THE THEOREMS
// -------------------------------------------------------------------
//
// SR-1. `distinct_solutions` DOES NOT IMPLEMENT SPARQL DISTINCT.
//   `theorem_distinct_not_card_conformant` is a machine-checked
//   refutation: there is a solution sequence on which
//   `distinct_solutions` fails section 18.5's Card[Distinct] = 1
//   clause. The cause is that `sm_equal` compares two solution
//   mappings as ORDERED ASSOCIATION LISTS ("v1 = v2 && rdf_term_eq t1
//   t2 && sm_equal r1 r2"), while a solution mapping is a PARTIAL
//   FUNCTION (18.3) and two lists binding the same variables to the
//   same terms in a different order denote the same mapping. This is
//   not a corner case reachable only in F*: `tp_match` threads
//   bindings subject -> predicate -> object and `sm_bind` PREPENDS, so
//   the two arms of `{ ?x :p ?y } UNION { ?y :q ?x }` produce the
//   same mapping in opposite list order, and SELECT DISTINCT over
//   that union returns the row twice.
//
// SR-2. THE HASH-JOIN KEY IS FINER THAN THE COMPATIBILITY TEST IT
//   NARROWS, so `join` can DROP solutions that `join_nested_loop`
//   (and therefore the specification) requires.
//   `theorem_join_key_finer_than_compatibility` is the machine-checked
//   statement. `sm_join_key` keys on `RDF.NQuads.Serialize.nq_term_to_string`, which is
//   injective up to BYTE identity; `sm_compatible` accepts on
//   `rdf_term_eq`, which is COARSER -- it compares language tags
//   case-insensitively (`RDF.Term.lang_tag_eq`) and rdf:XMLLiteral
//   lexical forms up to exclusive canonical XML. Two mappings binding
//   the shared join variable to `"x"@en` and `"x"@EN` are compatible,
//   must be joined, and land in different hash buckets.
//   The same defect is inherited by `left_join`, where it is worse:
//   a dropped inner match does not remove a row, it makes the row come
//   back UNJOINED, as if the OPTIONAL had not matched.
//   This is the SPARQL-side sibling of finding SE-1 of the
//   simple-entailment vertical (2026-07-29): the same over-coarse
//   `rdf_term_eq`, reached from the other end of the tree.
//
// Neither finding is papered over below and neither specification was
// weakened to accommodate it.
//
// -------------------------------------------------------------------
// SCOPE
// -------------------------------------------------------------------
// The fragment is SPARQL11.Algebra.Spec's SPARQL-CORE-8; see that
// module's banner for the full in/out list. Additionally, WITHIN this
// module:
//
//   * Everything is relative to a SINGLE active graph. `join`,
//     `union`, `minus`, `left_join`, `filter_solutions`,
//     `project_solutions`, `distinct_solutions` and `fx_bind_rows` are
//     dataset-independent by construction, so this costs nothing for
//     them; it does bound the BGP results.
//   * Expression evaluation (section 17) is a PARAMETER, as in the
//     Spec module. Theorems about Filter and LeftJoin are stated for
//     the shipping `eval_expr_ebv base e` without any assumption about
//     what it computes. Where a bag-level (cardinality) statement is
//     made, it needs `fexpr_congr` -- that the evaluator gives the
//     same answer to two association lists denoting the same solution
//     mapping. Whether `eval_expr_ebv` satisfies `fexpr_congr` is
//     NOT proved here and is stated as an open obligation; it is a
//     480-line mutual recursion over the whole expression language and
//     is its own commit.
//   * `join`'s HASH path is not proved sound, only its no-shared-
//     variable path (which is definitionally `join_nested_loop`).
//     Soundness of the hash path additionally requires
//     "bucket_lookup's result is a sublist of the indexed sequence",
//     a lemma about RDF.Indexed's balanced-tree index that does not
//     exist yet. Completeness of the hash path is FALSE -- see SR-2.
//
// No admit, no --lax, no --admit_smt_queries, no assume. z3 4.13.3.
// Zero change to any shipping module: this file only reads them.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open SPARQL11.Algebra

module S = SPARQL11.Algebra.Spec
module T = FStar.Tactics
module Lh = RDF.List.Helpers

#push-options "--z3rlimit 120 --fuel 3 --ifuel 2"

(** ====================================================================== **)
(** Part 1: the fragment hypothesis -- where rdf_term_eq is term identity  **)
(** ====================================================================== **)

/// The engine decides term equality with `RDF.Term.rdf_term_eq`, which
/// is STRICTLY COARSER than RDF term identity: `lang_tag_eq` folds
/// case, and two rdf:XMLLiteral-typed literals compare by exclusive
/// canonical XML. Section 18.3's compatibility condition is identity.
///
/// `term_exact t` names the fragment where the two coincide AT t. It is
/// the SPARQL-side analogue of the simple-entailment vertical's
/// `lit_exact` (finding SE-1, 2026-07-29), stated semantically rather
/// than syntactically so it transfers to any future coarsening of
/// `rdf_term_eq` without restatement.
let term_exact (t : rdf_term) : prop =
  forall (t' : rdf_term). rdf_term_eq t t' == true ==> t == t'

/// A solution mapping all of whose bound terms are exact. Stated over
/// the LIST, not over `sval`, because `sm_compatible` walks the list.
let rec smap_exact (mu : S.smap) : Tot prop (decreases mu) =
  match mu with
  | [] -> True
  | (_, t) :: rest -> term_exact t /\ smap_exact rest

let rec seq_exact (omega : list S.smap) : Tot prop (decreases omega) =
  match omega with
  | [] -> True
  | mu :: rest -> smap_exact mu /\ seq_exact rest

/// A solution sequence whose every mapping is a well-formed
/// representation of a partial function (no repeated variable).
let rec seq_wf (omega : list S.smap) : Tot prop (decreases omega) =
  match omega with
  | [] -> True
  | mu :: rest -> S.smap_wf mu == true /\ seq_wf rest

(** ====================================================================== **)
(** Part 2: bridging -- engine primitives against section 18.3             **)
(** ====================================================================== **)

let rec lemma_assoc_some_mem (v : string) (mu : S.smap)
  : Lemma (requires Some? (List.Tot.assoc v mu))
          (ensures  List.Tot.memP v (List.Tot.map fst mu))
          (decreases mu) =
  match mu with
  | [] -> ()
  | (w, _) :: rest -> if w = v then () else lemma_assoc_some_mem v rest

(** 2.1 sm_compatible refines compatible_spec **)

/// SOUNDNESS. If the engine says two mappings are compatible then they
/// are compatible in the sense of section 18.3 -- PROVIDED the terms
/// of the left mapping are exact. The hypothesis is not slack: without
/// it the statement is false, because `rdf_term_eq` identifies `"x"@en`
/// with `"x"@EN` and section 18.3's "=" does not.
let rec lemma_sm_compatible_sound
      (mu1 mu2 : S.smap) (v : string) (t1 t2 : rdf_term)
  : Lemma (requires sm_compatible mu1 mu2 == true /\ smap_exact mu1 /\
                    S.sval v mu1 == Some t1 /\ S.sval v mu2 == Some t2)
          (ensures  t1 == t2)
          (decreases mu1) =
  match mu1 with
  | [] -> ()
  | (w, _) :: rest ->
    if w = v then () else lemma_sm_compatible_sound rest mu2 v t1 t2

let theorem_sm_compatible_sound (mu1 mu2 : S.smap)
  : Lemma (requires sm_compatible mu1 mu2 == true /\ smap_exact mu1)
          (ensures  S.compatible_spec mu1 mu2) =
  let aux (v : string) (t1 t2 : rdf_term)
    : Lemma (requires S.sval v mu1 == Some t1 /\ S.sval v mu2 == Some t2)
            (ensures  t1 == t2) =
    lemma_sm_compatible_sound mu1 mu2 v t1 t2
  in
  FStar.Classical.forall_intro_3
    (fun v t1 t2 -> FStar.Classical.move_requires (aux v t1) t2)

/// COMPLETENESS. Every section-18.3-compatible pair is accepted by the
/// engine -- provided the left mapping has no repeated variable.
/// That hypothesis is not slack either: the 2026-07-29 refutation
/// `SPARQL11.Algebra.lemma_sm_compatible_not_refl_with_dup_keys`
/// shows `sm_compatible` is not even reflexive without it.
/// No exactness is needed here: `rdf_term_eq` accepting MORE than
/// identity can only help this direction.
let rec theorem_sm_compatible_complete (mu1 mu2 : S.smap)
  : Lemma (requires S.smap_wf mu1 == true /\ S.compatible_spec mu1 mu2)
          (ensures  sm_compatible mu1 mu2 == true)
          (decreases mu1) =
  match mu1 with
  | [] -> ()
  | (v, t) :: rest ->
    assert (S.sval v mu1 == Some t);
    let aux (w : string) (a b : rdf_term)
      : Lemma (requires S.sval w rest == Some a /\ S.sval w mu2 == Some b)
              (ensures  a == b) =
      lemma_assoc_some_mem w rest;
      FStar.List.Tot.Properties.mem_memP w (List.Tot.map fst rest);
      FStar.List.Tot.Properties.mem_memP v (List.Tot.map fst rest);
      assert (w =!= v);
      assert (S.sval w mu1 == Some a)
    in
    FStar.Classical.forall_intro_3
      (fun w a b -> FStar.Classical.move_requires (aux w a) b);
    assert (S.compatible_spec rest mu2);
    assert (S.smap_wf rest == true);
    theorem_sm_compatible_complete rest mu2;
    assert (sm_compatible rest mu2 == true);
    (match List.Tot.assoc v mu2 with
     | None -> ()
     | Some t2 -> (assert (t == t2); lemma_rdf_term_eq_refl t))

(** 2.2 sm_merge computes THE merge of section 18.3 **)

/// The shipping `sm_merge` recurses on its SECOND argument and
/// prepends, so it does NOT return `mu1 @ mu2` and it is not the
/// identity on the left (see
/// `SPARQL11.Algebra.lemma_sm_merge_empty_l_not_structural_identity`,
/// 2026-07-29). As a SOLUTION MAPPING, however, it is exactly section
/// 18.3's merge -- which is what `is_merge` says, since `is_merge` is
/// stated pointwise and is therefore blind to list layout.
let theorem_sm_merge_is_merge (mu1 mu2 : S.smap)
  : Lemma (S.is_merge mu1 mu2 (sm_merge mu1 mu2)) =
  FStar.Classical.forall_intro (fun (v : string) ->
    lemma_sm_merge_aux_lookup mu1 mu2 v)

(** 2.3 domains_disjoint refines dom_disjoint_spec **)

let rec theorem_domains_disjoint_sound (mu1 mu2 : S.smap)
  : Lemma (requires domains_disjoint mu1 mu2 == true)
          (ensures  S.dom_disjoint_spec mu1 mu2)
          (decreases mu1) =
  match mu1 with
  | [] -> ()
  | (v, t0) :: rest ->
    theorem_domains_disjoint_sound rest mu2;
    assert (forall (w : string).
              ~(Some? (List.Tot.assoc w rest) /\ Some? (List.Tot.assoc w mu2)));
    assert (List.Tot.assoc v mu2 == None);
    assert (forall (w : string).
              ~(Some? (List.Tot.assoc w mu1) /\ Some? (List.Tot.assoc w mu2)))

let rec theorem_domains_disjoint_complete (mu1 mu2 : S.smap)
  : Lemma (requires S.dom_disjoint_spec mu1 mu2)
          (ensures  domains_disjoint mu1 mu2 == true)
          (decreases mu1) =
  match mu1 with
  | [] -> ()
  | (v, t0) :: rest ->
    assert (List.Tot.assoc v mu1 == Some t0);
    assert (List.Tot.assoc v mu2 == None);
    assert (forall (w : string).
              ~(Some? (List.Tot.assoc w rest) /\ Some? (List.Tot.assoc w mu2)));
    theorem_domains_disjoint_complete rest mu2

(** ====================================================================== **)
(** Part 3: multiset arithmetic on the evaluator's lists                   **)
(** ====================================================================== **)

let rec lemma_mult_append (mu : S.smap) (o1 o2 : list S.smap)
  : Lemma (ensures S.mult mu (List.Tot.append o1 o2) ==
                   S.mult mu o1 + S.mult mu o2)
          (decreases o1) =
  match o1 with
  | [] -> ()
  | _ :: rest -> lemma_mult_append mu rest o2

let rec lemma_memP_append (#a : Type) (x : a) (l1 l2 : list a)
  : Lemma (ensures List.Tot.memP x (List.Tot.append l1 l2) <==>
                   (List.Tot.memP x l1 \/ List.Tot.memP x l2))
          (decreases l1) =
  match l1 with
  | [] -> ()
  | _ :: rest -> lemma_memP_append x rest l2

(** ====================================================================== **)
(** Part 4: Union (section 18.5)                                           **)
(** ====================================================================== **)

/// The shipping `union` is `Lh.append_tr`, provably `List.Tot.append`.
let lemma_union_is_append (o1 o2 : list S.smap)
  : Lemma (union o1 o2 == List.Tot.append o1 o2) =
  Lh.lemma_append_tr_eq o1 o2

/// The NORMATIVE (bag) statement: section 18.5's
/// "Card[Union(Omega1,Omega2)][mu] = Card[Omega1][mu] + Card[Omega2][mu]".
/// Unconditional -- no fragment hypothesis of any kind.
let theorem_union_card (o1 o2 : list S.smap)
  : Lemma (S.union_card_spec o1 o2 (union o1 o2)) =
  lemma_union_is_append o1 o2;
  FStar.Classical.forall_intro (fun (mu : S.smap) ->
    lemma_mult_append mu o1 o2)

/// The set-level statement, for symmetry with the other operators.
let theorem_union_sound (o1 o2 : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (union o1 o2))
          (ensures  S.in_union_spec o1 o2 mu) =
  lemma_union_is_append o1 o2;
  lemma_memP_append mu o1 o2

let theorem_union_complete (o1 o2 : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu o1 \/ List.Tot.memP mu o2)
          (ensures  List.Tot.memP mu (union o1 o2)) =
  lemma_union_is_append o1 o2;
  lemma_memP_append mu o1 o2

(** ====================================================================== **)
(** Part 5: Filter (section 18.5)                                          **)
(** ====================================================================== **)

/// `filter_solutions` is `List.Tot.filter (eval_expr_ebv base e)`.
/// Both directions are unconditional in the expression evaluator: no
/// assumption is made about what `eval_expr_ebv` computes, exactly as
/// section 18.5 makes none ("expr(mu) ... has an effective boolean
/// value of true").
let rec theorem_filter_sound (base : option wf_iri) (e : expr)
      (omega : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (filter_solutions base e omega))
          (ensures  List.Tot.memP mu omega /\ eval_expr_ebv base e mu == true)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    if eval_expr_ebv base e m && FStar.StrongExcludedMiddle.strong_excluded_middle (mu == m)
    then ()
    else theorem_filter_sound base e rest mu

let rec theorem_filter_complete (base : option wf_iri) (e : expr)
      (omega : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu omega /\ eval_expr_ebv base e mu == true)
          (ensures  List.Tot.memP mu (filter_solutions base e omega))
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    eliminate (mu == m) \/ (List.Tot.memP mu rest)
    returns List.Tot.memP mu (filter_solutions base e omega)
    with _. ()
    and  _. theorem_filter_complete base e rest mu

/// The bag-level statement needs the expression evaluator to respect
/// solution-mapping equality -- a mapping is a partial function, so an
/// evaluator that could tell two representations of it apart would not
/// be evaluating a SPARQL expression at all. Stated as a hypothesis
/// rather than proved of `eval_expr_ebv`: see SCOPE.
let fexpr_congr (f : S.fexpr) : prop =
  forall (mu mu' : S.smap). S.smap_eq mu mu' ==> f mu == f mu'

let rec theorem_filter_card (f : S.fexpr) (omega : list S.smap)
  : Lemma (requires fexpr_congr f)
          (ensures  S.filter_card_spec f omega (List.Tot.filter f omega))
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    theorem_filter_card f rest;
    let aux (mu : S.smap)
      : Lemma (S.mult mu (List.Tot.filter f omega) ==
               (if f mu then S.mult mu omega else 0)) =
      if S.smap_eqb mu m then S.lemma_smap_eqb_sound mu m else ()
    in
    FStar.Classical.forall_intro aux

(** ====================================================================== **)
(** Part 6: Distinct (section 18.5) -- FINDING SR-1                        **)
(** ====================================================================== **)

/// What `distinct_solutions` DOES get right: it never invents a
/// solution.
let rec lemma_dedup_acc_sound (omega acc : list S.smap) (mu : S.smap)
  : Lemma (ensures List.Tot.memP mu (list_deduplicate_sm_acc omega acc) ==>
                   (List.Tot.memP mu omega \/ List.Tot.memP mu acc))
          (decreases omega) =
  match omega with
  | [] -> ()
  | x :: xs ->
    if sm_mem x xs then lemma_dedup_acc_sound xs acc mu
    else lemma_dedup_acc_sound xs (x :: acc) mu

let theorem_distinct_sound (omega : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (distinct_solutions omega))
          (ensures  List.Tot.memP mu omega) =
  FStar.List.Tot.Properties.rev_memP (list_deduplicate_sm_acc omega []) mu;
  lemma_dedup_acc_sound omega [] mu

(** 6.1 The refutation **)

/// Two association lists that denote the SAME solution mapping (18.3:
/// a partial function) but that `sm_equal` separates, because
/// `sm_equal` compares them position by position.
let sr1_term_a : rdf_term = T_BNode "b1"
let sr1_term_b : rdf_term = T_BNode "b2"
let sr1_mu1 : S.smap = [("a", sr1_term_a); ("b", sr1_term_b)]
let sr1_mu2 : S.smap = [("b", sr1_term_b); ("a", sr1_term_a)]

let lemma_sr1_same_mapping ()
  : Lemma (S.smap_eq sr1_mu1 sr1_mu2) = ()

let lemma_sr1_sm_equal_says_different ()
  : Lemma (sm_equal sr1_mu1 sr1_mu2 == false) = assert_norm (sm_equal sr1_mu1 sr1_mu2 == false)

let lemma_sr1_distinct_keeps_both ()
  : Lemma (distinct_solutions [sr1_mu1; sr1_mu2] == [sr1_mu1; sr1_mu2]) =
  assert_norm (distinct_solutions [sr1_mu1; sr1_mu2] == [sr1_mu1; sr1_mu2])

/// FINDING SR-1, as a theorem: the shipping DISTINCT does not satisfy
/// section 18.5's Card[Distinct(Omega)][mu] = 1.
///
/// The witness is stated with concrete blank nodes and concrete
/// variable names -- no hypothesis, nothing left to inspection. Both
/// mappings bind ?a to _:b1 and ?b to _:b2; they differ only in the
/// order the evaluator happened to build the association list, which
/// section 18.3 says carries no meaning.
let theorem_distinct_not_card_conformant ()
  : Lemma (exists (omega : list S.smap).
             ~(S.distinct_card_spec omega (distinct_solutions omega))) =
  lemma_sr1_same_mapping ();
  S.lemma_smap_eqb_complete sr1_mu1 sr1_mu2;
  lemma_sr1_distinct_keeps_both ();
  assert (S.mult sr1_mu1 [sr1_mu1; sr1_mu2] == 2);
  assert (S.mult sr1_mu1 (distinct_solutions [sr1_mu1; sr1_mu2]) == 2);
  assert (~(S.distinct_card_spec [sr1_mu1; sr1_mu2]
                                 (distinct_solutions [sr1_mu1; sr1_mu2])))

/// The same defect stated where a reader will meet it: `sm_equal`,
/// which `distinct_solutions` uses as its notion of "same solution",
/// is not the equality of solution mappings.
let theorem_sm_equal_is_not_smap_eq ()
  : Lemma (exists (mu1 mu2 : S.smap).
             S.smap_eq mu1 mu2 /\ sm_equal mu1 mu2 == false) =
  lemma_sr1_same_mapping ();
  lemma_sr1_sm_equal_says_different ()

(** ====================================================================== **)
(** Part 7: list-membership machinery for the evaluator's own combinators  **)
(** ====================================================================== **)

let rec lemma_memP_filter_map_acc (#a #b : Type)
      (f : a -> option b) (l : list a) (acc : list b) (y : b)
  : Lemma (ensures List.Tot.memP y (list_filter_map_acc f l acc) <==>
                   ((exists (x : a). List.Tot.memP x l /\ f x == Some y) \/
                    List.Tot.memP y acc))
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs ->
    (match f x with
     | Some z -> lemma_memP_filter_map_acc f xs (z :: acc) y
     | None   -> lemma_memP_filter_map_acc f xs acc y)

let lemma_memP_filter_map (#a #b : Type) (f : a -> option b) (l : list a) (y : b)
  : Lemma (List.Tot.memP y (list_filter_map f l) <==>
           (exists (x : a). List.Tot.memP x l /\ f x == Some y)) =
  lemma_memP_filter_map_acc f l [] y;
  FStar.List.Tot.Properties.rev_memP (list_filter_map_acc f l []) y

let rec lemma_memP_concatMap (#a #b : Type) (f : a -> list b) (l : list a) (y : b)
  : Lemma (ensures List.Tot.memP y (List.Tot.concatMap f l) <==>
                   (exists (x : a). List.Tot.memP x l /\ List.Tot.memP y (f x)))
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs ->
    lemma_memP_append y (f x) (List.Tot.concatMap f xs);
    lemma_memP_concatMap f xs y

let rec lemma_seq_exact_memP (omega : list S.smap) (mu : S.smap)
  : Lemma (requires seq_exact omega /\ List.Tot.memP mu omega)
          (ensures  smap_exact mu)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    eliminate (mu == m) \/ (List.Tot.memP mu rest)
    returns smap_exact mu
    with _. ()
    and  _. lemma_seq_exact_memP rest mu

let rec lemma_seq_wf_memP (omega : list S.smap) (mu : S.smap)
  : Lemma (requires seq_wf omega /\ List.Tot.memP mu omega)
          (ensures  S.smap_wf mu == true)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest ->
    eliminate (mu == m) \/ (List.Tot.memP mu rest)
    returns S.smap_wf mu == true
    with _. ()
    and  _. lemma_seq_wf_memP rest mu

(** ====================================================================== **)
(** Part 8: Join (section 18.5) at `join_nested_loop`                      **)
(** ====================================================================== **)

/// `join_nested_loop` is the shipping function `join` falls back to
/// when the two sides share no bound variable. It is also the only one
/// of the two that is a transcription of section 18.5's Join; `join`
/// adds a hash index on top, and that index is where finding SR-2
/// lives.
///
/// `unfold let` rather than a plain `let` for the inner step: the
/// shipping code passes an INLINE LAMBDA to `concatMap_tr`, and a
/// plain `let` copy gets an unrelated closure symbol in the SMT
/// encoding (the simple-entailment vertical's section 7.5, and the OWL
/// pilot's finding F3 before it). `unfold` makes the connection
/// definitional.
unfold let jnl_step (o2 : list S.smap) (mu1 : S.smap) : list S.smap =
  list_filter_map
    (fun mu2 -> if sm_compatible mu1 mu2 then Some (sm_merge mu1 mu2) else None)
    o2

let lemma_join_nested_loop_unfold (o1 o2 : list S.smap)
  : Lemma (join_nested_loop o1 o2 == List.Tot.concatMap (jnl_step o2) o1) =
  assert (join_nested_loop o1 o2 == Lh.concatMap_tr (jnl_step o2) o1)
    by (FStar.Tactics.trefl ());
  Lh.lemma_concatMap_tr_eq (jnl_step o2) o1

/// SOUNDNESS: every solution the nested-loop join emits is a merge of
/// two compatible mappings from the two inputs, in section 18.5's
/// sense. `seq_exact` is the fragment hypothesis inherited from
/// `theorem_sm_compatible_sound`; it is where the coarseness of
/// `rdf_term_eq` is quarantined.
let theorem_join_nested_loop_sound (o1 o2 : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (join_nested_loop o1 o2) /\ seq_exact o1)
          (ensures  S.in_join_spec o1 o2 mu) =
  lemma_join_nested_loop_unfold o1 o2;
  lemma_memP_concatMap (jnl_step o2) o1 mu;
  eliminate exists (mu1 : S.smap).
      (List.Tot.memP mu1 o1 /\ List.Tot.memP mu (jnl_step o2 mu1))
  returns S.in_join_spec o1 o2 mu
  with _.
    (lemma_seq_exact_memP o1 mu1;
     lemma_memP_filter_map
       (fun mu2 -> if sm_compatible mu1 mu2 then Some (sm_merge mu1 mu2) else None)
       o2 mu;
     eliminate exists (mu2 : S.smap).
         (List.Tot.memP mu2 o2 /\
          (if sm_compatible mu1 mu2 then Some (sm_merge mu1 mu2) else None) == Some mu)
     returns S.in_join_spec o1 o2 mu
     with _.
       (theorem_sm_compatible_sound mu1 mu2;
        theorem_sm_merge_is_merge mu1 mu2))

/// COMPLETENESS: every merge the specification demands is emitted.
/// `smap_wf mu1` is the hypothesis inherited from
/// `theorem_sm_compatible_complete` -- without it `sm_compatible` is
/// not even reflexive (2026-07-29).
let theorem_join_nested_loop_complete
      (o1 o2 : list S.smap) (mu1 mu2 : S.smap)
  : Lemma (requires List.Tot.memP mu1 o1 /\ List.Tot.memP mu2 o2 /\
                    S.compatible_spec mu1 mu2 /\ S.smap_wf mu1 == true)
          (ensures  (exists (mu : S.smap).
                       List.Tot.memP mu (join_nested_loop o1 o2) /\
                       S.is_merge mu1 mu2 mu)) =
  theorem_sm_compatible_complete mu1 mu2;
  theorem_sm_merge_is_merge mu1 mu2;
  lemma_memP_filter_map
    (fun m2 -> if sm_compatible mu1 m2 then Some (sm_merge mu1 m2) else None)
    o2 (sm_merge mu1 mu2);
  lemma_join_nested_loop_unfold o1 o2;
  lemma_memP_concatMap (jnl_step o2) o1 (sm_merge mu1 mu2)

(** 8.1 where `join` and `join_nested_loop` provably agree **)

let rec lemma_concatMap_nil_f (#a #b : Type) (f : a -> list b) (l : list a)
  : Lemma (requires forall (x : a). f x == [])
          (ensures  List.Tot.concatMap f l == [])
          (decreases l) =
  match l with
  | [] -> ()
  | _ :: rest -> lemma_concatMap_nil_f f rest

/// The hash path is skipped entirely when the representative rows of
/// the two sides share no variable; there `join` IS the specification's
/// Join, with no side condition beyond the two above.
let lemma_join_is_nested_loop_no_shared_vars (o1 o2 : list S.smap)
  : Lemma (requires Cons? o1 /\ Cons? o2 /\
                    vars_intersect (sm_domain (Cons?.hd o1))
                                   (sm_domain (Cons?.hd o2)) == [])
          (ensures  join o1 o2 == join_nested_loop o1 o2) = ()

let lemma_join_is_nested_loop_empty (o1 o2 : list S.smap)
  : Lemma (requires Nil? o1 \/ Nil? o2)
          (ensures  join o1 o2 == join_nested_loop o1 o2) =
  lemma_join_nested_loop_unfold o1 o2;
  if Nil? o1 then () else lemma_concatMap_nil_f (jnl_step o2) o1

(** ====================================================================== **)
(** Part 9: FINDING SR-2 -- the hash-join key is finer than compatibility  **)
(** ====================================================================== **)

/// The witness literal: `"x"` tagged with an arbitrary language tag.
/// `literal_wf` holds by construction (a language tag with no base
/// direction forces datatype = rdf:langString).
let sr2_lit (tag : string) : wf_literal =
  { lexical_form = "x";
    datatype     = rdf_lang_string;
    lang_tag     = Some tag;
    direction    = None }

/// String-concatenation disequality, from FStar.String.concat_injective.
/// The side condition concat_injective needs (equal lengths on one
/// side) is discharged trivially here because the shared factor is
/// literally the same string.
let lemma_strcat_left_neq (a b c : string)
  : Lemma (requires a =!= b) (ensures (a ^ c) =!= (b ^ c)) =
  FStar.String.concat_injective a b c c

let lemma_strcat_right_neq (a b c : string)
  : Lemma (requires a =!= b) (ensures (c ^ a) =!= (c ^ b)) =
  FStar.String.concat_injective c c a b

/// The byte-level fact underneath SR-2: the N-Quads serializer copies
/// the language tag VERBATIM (RDF.NQuads.Serialize line 123,
/// `"\"" ^ esc ^ "\"@" ^ tag ^ dir_suffix`), so two literals differing
/// only in tag CASE serialize to different bytes -- while `literal_eq`
/// calls them the same term.
let lemma_sr2_nq_differs (tag1 tag2 : string)
  : Lemma (requires tag1 =!= tag2)
          (ensures  RDF.NQuads.Serialize.nq_term_to_string (T_Literal (sr2_lit tag1)) =!=
                    RDF.NQuads.Serialize.nq_term_to_string (T_Literal (sr2_lit tag2))) =
  let esc = RDF.NQuads.Serialize.nq_escape_literal "x" in
  lemma_strcat_left_neq tag1 tag2 "";
  lemma_strcat_right_neq (tag1 ^ "") (tag2 ^ "") "\"@";
  lemma_strcat_right_neq ("\"@" ^ (tag1 ^ "")) ("\"@" ^ (tag2 ^ "")) esc;
  lemma_strcat_right_neq (esc ^ ("\"@" ^ (tag1 ^ ""))) (esc ^ ("\"@" ^ (tag2 ^ ""))) "\""

/// FINDING SR-2, machine-checked.
///
/// The tag pair is taken as a HYPOTHESIS rather than instantiated at
/// string constants, for the reason recorded in section 7.7 of the
/// simple-entailment design doc: `String.lowercase` is a primitive the
/// normaliser will not evaluate, so `assert_norm` cannot decide
/// `lowercase "en" = lowercase "EN"`. `"en"`/`"EN"` is the intended
/// instance and it is confirmed to fire end-to-end against the shipping
/// binary -- see the design doc for the exact query and output.
///
/// The conclusion is the contradiction itself: the two mappings ARE
/// compatible by the very test `join`/`left_join` apply after
/// narrowing (`sm_compatible`), and they are put in DIFFERENT hash
/// buckets by the narrowing step (`sm_join_key`). A candidate set
/// keyed this way is therefore NOT a superset of the compatible pairs,
/// which is the property the hash-join optimisation needs to be
/// semantics-preserving.
let theorem_join_key_finer_than_compatibility (v : string) (tag1 tag2 : string)
  : Lemma (requires String.lowercase tag1 == String.lowercase tag2 /\
                    tag1 =!= tag2)
          (ensures  (let t1 = T_Literal (sr2_lit tag1) in
                     let t2 = T_Literal (sr2_lit tag2) in
                     let mu1 : S.smap = [(v, t1)] in
                     let mu2 : S.smap = [(v, t2)] in
                     rdf_term_eq t1 t2 == true /\
                     sm_compatible mu1 mu2 == true /\
                     sm_join_key [v] mu1 =!= sm_join_key [v] mu2)) =
  lemma_sr2_nq_differs tag1 tag2;
  lemma_strcat_left_neq
    (RDF.NQuads.Serialize.nq_term_to_string (T_Literal (sr2_lit tag1)))
    (RDF.NQuads.Serialize.nq_term_to_string (T_Literal (sr2_lit tag2)))
    (RDF.Indexed.unit_sep ^ "")

(** ====================================================================== **)
(** Part 10: Project (section 18.5)                                        **)
(** ====================================================================== **)

let rec lemma_project_lookup (pv : list var_name) (mu : S.smap) (v : var_name)
  : Lemma (ensures S.sval v (project pv mu) ==
                   (if List.Tot.mem v pv then S.sval v mu else None))
          (decreases mu) =
  match mu with
  | [] -> ()
  | _ :: rest -> lemma_project_lookup pv rest v

/// `project` computes section 18.5's Proj(mu, PV) exactly --
/// unconditionally, no fragment hypothesis.
let theorem_project_is_proj (pv : list var_name) (mu : S.smap)
  : Lemma (S.is_proj pv mu (project pv mu)) =
  FStar.Classical.forall_intro (fun (v : var_name) -> lemma_project_lookup pv mu v)

let rec lemma_project_solutions_acc_memP
      (pv : list var_name) (omega acc : list S.smap) (mu' : S.smap)
  : Lemma (ensures List.Tot.memP mu' (project_solutions_acc pv omega acc) <==>
                   ((exists (mu : S.smap).
                       List.Tot.memP mu omega /\ mu' == project pv mu) \/
                    List.Tot.memP mu' acc))
          (decreases omega) =
  match omega with
  | [] -> ()
  | _ :: rest -> lemma_project_solutions_acc_memP pv rest (project pv (Cons?.hd omega) :: acc) mu'

let rec lemma_project_solutions_acc_length
      (pv : list var_name) (omega acc : list S.smap)
  : Lemma (ensures List.Tot.length (project_solutions_acc pv omega acc) ==
                   List.Tot.length omega + List.Tot.length acc)
          (decreases omega) =
  match omega with
  | [] -> ()
  | m :: rest -> lemma_project_solutions_acc_length pv rest (project pv m :: acc)

/// Project neither adds nor removes rows (section 18.5's Project
/// merges no duplicates -- that is DISTINCT's job) ...
let theorem_project_solutions_length (pv : list var_name) (omega : list S.smap)
  : Lemma (List.Tot.length (project_solutions pv omega) == List.Tot.length omega) =
  lemma_project_solutions_acc_length pv omega [];
  FStar.List.Tot.Properties.rev_length (project_solutions_acc pv omega [])

/// ... and every row it produces is a Proj of a row it consumed, and
/// conversely.
let theorem_project_solutions_spec
      (pv : list var_name) (omega : list S.smap) (mu' : S.smap)
  : Lemma (List.Tot.memP mu' (project_solutions pv omega) <==>
           (exists (mu : S.smap). List.Tot.memP mu omega /\ mu' == project pv mu)) =
  lemma_project_solutions_acc_memP pv omega [] mu';
  FStar.List.Tot.Properties.rev_memP (project_solutions_acc pv omega []) mu'

let theorem_project_solutions_sound
      (pv : list var_name) (omega : list S.smap) (mu' : S.smap)
  : Lemma (requires List.Tot.memP mu' (project_solutions pv omega))
          (ensures  S.in_project_spec pv omega mu') =
  theorem_project_solutions_spec pv omega mu';
  eliminate exists (mu : S.smap). (List.Tot.memP mu omega /\ mu' == project pv mu)
  returns S.in_project_spec pv omega mu'
  with _. theorem_project_is_proj pv mu

(** ====================================================================== **)
(** Part 11: Minus (section 18.5)                                          **)
(** ====================================================================== **)

unfold let minus_keep (o2 : list S.smap) (mu1 : S.smap) : bool =
  not (List.Tot.existsb
         (fun mu2 -> sm_compatible mu1 mu2 && not (domains_disjoint mu1 mu2))
         o2)

let lemma_minus_unfold (o1 o2 : list S.smap)
  : Lemma (minus o1 o2 == List.Tot.filter (minus_keep o2) o1) =
  assert (minus o1 o2 == List.Tot.filter (minus_keep o2) o1)
    by (FStar.Tactics.trefl ())

let rec lemma_existsb_memP (#a : Type) (f : a -> bool) (l : list a)
  : Lemma (ensures List.Tot.existsb f l <==>
                   (exists (x : a). List.Tot.memP x l /\ f x == true))
          (decreases l) =
  match l with
  | [] -> ()
  | _ :: rest -> lemma_existsb_memP f rest

let rec lemma_memP_filter (#a : Type) (f : a -> bool) (l : list a) (x : a)
  : Lemma (ensures List.Tot.memP x (List.Tot.filter f l) <==>
                   (List.Tot.memP x l /\ f x == true))
          (decreases l) =
  match l with
  | [] -> ()
  | _ :: rest -> lemma_memP_filter f rest x

/// The contrapositive of `theorem_sm_compatible_complete`: an engine
/// "not compatible" verdict IS a specification "not compatible"
/// verdict, on well-formed mappings.
let lemma_not_compatible_of_engine (mu1 mu2 : S.smap)
  : Lemma (requires S.smap_wf mu1 == true /\ sm_compatible mu1 mu2 == false)
          (ensures  ~(S.compatible_spec mu1 mu2)) =
  FStar.Classical.move_requires (theorem_sm_compatible_complete mu1) mu2

/// SOUNDNESS: everything Minus keeps satisfies section 18.5's
/// side condition. `smap_wf` is needed to turn the engine's
/// "not compatible" into the specification's, via the contrapositive of
/// `theorem_sm_compatible_complete`.
let theorem_minus_sound (o1 o2 : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (minus o1 o2) /\ S.smap_wf mu == true)
          (ensures  S.in_minus_spec o1 o2 mu) =
  lemma_memP_filter (minus_keep o2) o1 mu;
  lemma_existsb_memP
    (fun mu2 -> sm_compatible mu mu2 && not (domains_disjoint mu mu2)) o2;
  let aux (mu2 : S.smap)
    : Lemma (requires List.Tot.memP mu2 o2)
            (ensures  ~(S.compatible_spec mu mu2) \/ S.dom_disjoint_spec mu mu2) =
    if sm_compatible mu mu2 then theorem_domains_disjoint_sound mu mu2
    else lemma_not_compatible_of_engine mu mu2
  in
  FStar.Classical.forall_intro (fun mu2 -> FStar.Classical.move_requires aux mu2)

/// COMPLETENESS: everything the specification keeps is kept.
/// `smap_exact` is the fragment hypothesis, inherited from
/// `theorem_sm_compatible_sound`.
let theorem_minus_complete (o1 o2 : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu o1 /\ smap_exact mu /\
                    (forall (mu2 : S.smap). List.Tot.memP mu2 o2 ==>
                       (~(S.compatible_spec mu mu2) \/ S.dom_disjoint_spec mu mu2)))
          (ensures  List.Tot.memP mu (minus o1 o2)) =
  lemma_memP_filter (minus_keep o2) o1 mu;
  lemma_existsb_memP
    (fun mu2 -> sm_compatible mu mu2 && not (domains_disjoint mu mu2)) o2;
  let aux (mu2 : S.smap)
    : Lemma (requires List.Tot.memP mu2 o2)
            (ensures  (sm_compatible mu mu2 && not (domains_disjoint mu mu2)) == false) =
    if sm_compatible mu mu2 then begin
      theorem_sm_compatible_sound mu mu2;
      theorem_domains_disjoint_complete mu mu2
    end else ()
  in
  FStar.Classical.forall_intro (fun mu2 -> FStar.Classical.move_requires aux mu2)


(** ====================================================================== **)
(** Part 12: LeftJoin / OPTIONAL (section 18.5)                            **)
(** ====================================================================== **)

let lemma_filter_map_nil_all_none (#a #b : Type) (f : a -> option b) (l : list a) (x : a)
  : Lemma (requires list_filter_map f l == [] /\ List.Tot.memP x l)
          (ensures  f x == None) =
  match f x with
  | None -> ()
  | Some y -> lemma_memP_filter_map f l y

/// The per-left-row step of `left_join`'s no-shared-variable path,
/// named with `unfold` so the connection to the shipping inline lambda
/// stays definitional (the F3 trap again).
unfold let lj_step (base : option wf_iri) (fe : expr)
                   (o2 : list S.smap) (mu1 : S.smap) : list S.smap =
  let joins =
    list_filter_map
      (fun mu2 ->
        if sm_compatible mu1 mu2 then
          let merged = sm_merge mu1 mu2 in
          if eval_expr_ebv base fe merged then Some merged else None
        else None)
      o2 in
  if List.Tot.length joins > 0 then joins else [mu1]

/// PARTIAL RESULT ONLY, and the boundary is stated rather than hidden.
///
/// The two DEGENERATE arms of `left_join` are proved against section
/// 18.5's LeftJoin below. The general no-shared-variable arm is NOT
/// proved here, and the obstacle is worth recording so a second pass
/// does not rediscover it:
///
///   `left_join`'s body is `match omega1, omega2 with ... -> let vars =
///   vars_intersect ... in if vars = [] then concatMap_tr <lambda> ...`.
///   Relating it to `concatMap (lj_step ...)` needs BOTH a definitional
///   step (two syntactically distinct closures for the same lambda --
///   `FStar.Tactics.trefl` handles this, as it does for `jnl_step` in
///   part 8) AND a hypothesis-driven step (choosing the `vars = []`
///   branch -- SMT handles this, `trefl` cannot). Neither
///   `trefl` alone nor `norm [delta_only [left_join]] ; smt` alone
///   discharges the combination. The shape that should work is a
///   `trefl`-provable equation with the `if` LEFT IN the statement and
///   both branches spelled out, then an SMT step to pick the branch;
///   writing the hash branch out is the cost.
///
/// The mathematical content is not in doubt: the arm is the textbook
/// Filter(expr, Join) union Diff, and `theorem_join_nested_loop_sound`
/// already proves the Join half's shape. What is missing is the
/// definitional bridge, which is proof engineering, not semantics.

/// LeftJoin with an empty right side is Diff, which is Omega1 -- and
/// that is exactly what `left_join` returns.
let theorem_left_join_empty_right
      (base : option wf_iri) (fe : expr) (o1 : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu (left_join base o1 [] fe))
          (ensures  S.in_leftjoin_spec (eval_expr_ebv base fe) o1 [] mu) = ()

/// LeftJoin with an empty left side is empty.
let theorem_left_join_empty_left
      (base : option wf_iri) (fe : expr) (o2 : list S.smap) (mu : S.smap)
  : Lemma (~(List.Tot.memP mu (left_join base [] o2 fe))) = ()

(** ====================================================================== **)
(** Part 13: Extend / BIND (section 18.5)                                  **)
(** ====================================================================== **)

/// `fx_bind_rows` preserves the row count -- BIND is a per-row map,
/// never a filter and never a fan-out.
let rec theorem_fx_bind_rows_length
      (base : option wf_iri) (e : expr) (v : var_name)
      (omega : list S.smap) (i : nat)
  : Lemma (ensures List.Tot.length (fx_bind_rows base e v omega i) ==
                   List.Tot.length omega)
          (decreases omega) =
  match omega with
  | [] -> ()
  | _ :: rest -> theorem_fx_bind_rows_length base e v rest (i + 1)

/// The per-row characterisation, stated exactly as the code behaves so
/// that the DIVERGENCES from section 18.5 are visible rather than
/// smoothed over. Two of them:
///
///   (a) the expression is evaluated under `fx_ctx_put`'s CONTEXT
///       mapping (`mu` plus two non-variable keys carrying the row
///       index and the call-site tag, so BNODE()/UUID()/RAND() are
///       fresh per row), not under `mu`. Section 18.5 says expr(mu).
///       The extra keys start with U+0001 and are unreachable from
///       SPARQL syntax, so this is invisible to a conforming query --
///       but it is a departure from the letter of the text and the
///       reason `in_extend_spec` cannot simply be instantiated with
///       `eval_expr_fwd base e`.
///   (b) when `v` is ALREADY BOUND in `mu`, section 18.5 says
///       Extend is UNDEFINED. The engine silently returns `mu`
///       unchanged. The grammar forbids BIND to an in-scope variable,
///       so a conforming query cannot reach it; an
///       algebra-level caller can.
let rec theorem_fx_bind_rows_rowwise
      (base : option wf_iri) (e : expr) (v : var_name)
      (omega : list S.smap) (i : nat) (mu' : S.smap)
  : Lemma (ensures List.Tot.memP mu' (fx_bind_rows base e v omega i) ==>
                   (exists (mu : S.smap) (j : nat).
                      List.Tot.memP mu omega /\
                      (let ctx = fx_ctx_put (string_of_int j) v mu in
                       match er_to_term (eval_expr_fwd base e ctx) with
                       | Some t ->
                         (S.sval v mu == None /\ mu' == sm_bind v t mu) \/
                         (Some? (S.sval v mu) /\ mu' == mu)
                       | None -> mu' == mu)))
          (decreases omega) =
  match omega with
  | [] -> ()
  | mu :: rest ->
    Lh.lemma_assoc_tr_eq v mu;
    theorem_fx_bind_rows_rowwise base e v rest (i + 1) mu'

/// On the fragment section 18.5 actually covers -- `v` unbound and the
/// expression yielding a term -- the engine's row IS section 18.5's
/// Extend(mu, var, term).
let theorem_sm_bind_is_extend (mu : S.smap) (v : var_name) (t : rdf_term)
  : Lemma (requires S.sval v mu == None)
          (ensures  S.is_extend_at mu v t (sm_bind v t mu)) =
  Lh.lemma_assoc_tr_eq v mu

#pop-options
