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
// SR-1 (FIXED 2026-08-03, issue #336): `distinct_solutions` failed
//   section 18.5's Card[Distinct] = 1 clause because `sm_equal`
//   compared two solution mappings as ORDERED ASSOCIATION LISTS,
//   while a solution mapping is a PARTIAL FUNCTION (18.3). `sm_equal`
//   is now a mutual-submap check; the refutation theorems this file
//   carried are replaced by their positive forms on the same witness
//   (`theorem_sr1_witness_now_card_conformant`), and two lists
//   binding the same variables to the
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
//   (FIXED 2026-08-03, issue #337) `theorem_sr2_witness_keys_now_agree`
//   and `theorem_join_key_no_finer_than_compatibility` are the positive
//   forms of what was the machine-checked
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
// FC-1 (g4-fexpr-congr, 2026-08-10): `fexpr_congr` IS proved of the
//   real evaluator -- `lemma_eval_expr_congr`, structural induction
//   over `eval_expr_with_base`'s whole `expr` language (Part 5.0a,
//   below `theorem_filter_card`) -- but does NOT reach the literal
//   shipping `eval_expr_ebv` wrapper. `eval_expr_ebv`/`eval_expr_fwd`
//   are `irreducible` (SPARQL11.Algebra.fst ~4487/4491), and the
//   definitional equation needed to carry the induction's result back
//   out through the wrapper (`eval_expr_ebv base e mu == ebv
//   (eval_expr_with_base base e mu)`) is unreachable by every F*
//   technique tried against 2025.12.15/z3 4.13.3 (`assert_norm`,
//   `norm [delta_only [...]]`, blanket `delta`, `nbe`, `unfold_def`;
//   same-module and cross-module) -- not a semantic falsity (the
//   induction proves the function genuinely IS congruent) but a
//   proof-engineering wall the qualifier erects on purpose, to keep
//   the ~600-line evaluator body out of the SMT context of every OTHER
//   proof that calls `eval_expr_ebv` without needing its body.
//   `theorem_filter_card_eval_expr_with_base` restates the card-spec
//   UNCONDITIONALLY at `eval_expr_ebv_transparent` (the wrapper's own
//   body, re-declared without `irreducible`); `theorem_filter_card` on
//   the literal `eval_expr_ebv` / shipping `filter_solutions` stays
//   hypothesis-carrying pending a dedicated commit auditing removal of
//   `irreducible` across its call sites.
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
//     mapping. `fexpr_congr` IS now proved (g4-fexpr-congr,
//     `lemma_eval_expr_congr`, Part 5.0a) of the real evaluator
//     `eval_expr_with_base` -- a structural induction over the whole
//     expression language, per FC-1 above. It reaches the literal
//     `eval_expr_ebv` wrapper only up to the `irreducible`-qualifier
//     wall FC-1 documents: `theorem_filter_card_eval_expr_with_base`
//     is the unconditional card-spec at the transparent twin
//     `eval_expr_ebv_transparent`; `theorem_filter_card` on the
//     literal shipping `eval_expr_ebv` stays an open obligation,
//     narrowed from "whole proof missing" to "one qualifier-crossing
//     lemma missing, blocked pending a call-site audit."
//   * FILTER on the PRODUCTION path (`filter_solutions_with_graph`, the
//     function `eval_pattern_store`'s GP_Filter arm actually calls) is
//     now proved equal to the graph-free `filter_solutions` -- and
//     therefore inherits `theorem_filter_sound`/`_complete` above --
//     ON THE EXISTENTIAL-FREE FRAGMENT: `expr_has_existential e ==
//     false` (g4-filter-devacuation, Part 5 addendum below). The proof
//     is `substitute_existentials` being a syntactic no-op on such an
//     `e` (structural induction mirroring `expr_has_existential`'s own
//     match). EXISTS / NOT EXISTS, sub-SELECT, and property paths
//     remain future work, named rather than silently out of scope: an
//     `e` containing E_Exists/E_NotExists is exactly the case this
//     addendum's hypothesis excludes, and substituting them for their
//     boolean truth value under `mu`/`g`/`ds` before filtering is
//     `filter_solutions_with_graph`'s entire reason to exist over the
//     simpler `filter_solutions`.
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
module Mem = OWL.Semantics.MemLemmas
module SO = RDF.Indexed.StringOrder
// `open`, unlike `include`, does not re-export transitively: SPARQL11.Algebra
// itself `open`s RDF.Graph.Executable, but that does not make `rdf_graph` /
// `rdf_dataset` visible here just from `open SPARQL11.Algebra` above -- and
// an unqualified `open RDF.Graph.Executable` collides with
// SPARQL11.Algebra's OWN `pattern_term` (both modules define one; the later
// `open` would silently shadow the type Part 15's existing code matches
// against). Qualified alias instead, for the g4-filter-devacuation Part 5.1
// addendum (`filter_solutions_with_graph`'s `g`/`ds` parameters) only.
module GE = RDF.Graph.Executable

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

(** ------------------------------------------------------------------ **)
(** 5.0a `fexpr_congr` DISCHARGED for the real evaluator (g4-fexpr-congr). **)
(**                                                                       **)
(** `theorem_filter_card`'s hypothesis is discharged by structural        **)
(** induction over `eval_expr_with_base` (SPARQL11.Algebra.fst Part 8,    **)
(** the ~90-arm mutual-recursion clique): `mu` is consulted ONLY through  **)
(** `sm_lookup`/`fx_ctx_get`, and BOTH bottom out in `Lh.assoc_tr`, the    **)
(** same primitive `S.sval` uses (`Lh.lemma_assoc_tr_eq` identifies       **)
(** `assoc_tr` with `List.Tot.assoc`, and `S.sval v mu =                  **)
(** List.Tot.assoc v mu` by definition) -- so `S.smap_eq` (agreement of   **)
(** `sval` at every key) already forces agreement of every read the       **)
(** evaluator can make, ordinary variables (`E_Var`/`E_Bound`) and the    **)
(** two reserved `fx_key_row`/`fx_key_occ` freshness-context keys         **)
(** (RAND/UUID/STRUUID/BNODE, `SPARQL11.Algebra.fst` ~4342-4373) alike.   **)
(** Every other one of the ~74 `expr` constructors is congruence          **)
(** plumbing: recurse into sub-expressions, let first-order SMT           **)
(** congruence carry the equality through the surrounding pure function   **)
(** (`value_compare`, `fn_isIRI`, `ebv`, string/date/hash helpers, ...).   **)
(**                                                                       **)
(** FINDING FC-1. The induction below is unconditional and true of the    **)
(** SHIPPING `eval_expr_with_base`. It does NOT, however, transfer to     **)
(** the literal shipping wrapper `eval_expr_ebv` (nor `eval_expr_fwd`):   **)
(** both are `irreducible` (SPARQL11.Algebra.fst ~4487/4491), and the     **)
(** definitional equation `eval_expr_ebv base e mu == ebv                 **)
(** (eval_expr_with_base base e mu)` this proof needs to CROSS from       **)
(** `eval_expr_with_base` back out to the wrapper is unreachable by every **)
(** technique tried against F* 2025.12.15 / z3 4.13.3: `assert_norm`,     **)
(** `norm [delta_only [...]]` (both string and `` `%name `` quotation),   **)
(** blanket `norm [delta; zeta; iota; primops]`, `norm [nbe; delta_only]`,**)
(** and `FStar.Tactics.Derived.unfold_def` all fail identically ("cannot  **)
(** unify (eval_expr_ebv base e mu) and (ebv (eval_expr_with_base base e  **)
(** mu))") -- tried BOTH from this module and from a same-module          **)
(** minimal reproduction sitting next to `eval_expr_ebv`'s own            **)
(** definition. This is not a semantic falsity (the function plainly IS   **)
(** congruent -- that is exactly what the induction below proves of its   **)
(** body) but a proof-engineering wall the `irreducible` qualifier        **)
(** erects ON PURPOSE: it exists so that every OTHER proof calling        **)
(** `eval_expr_ebv` (this file has ~13 call sites; `SPARQL11.Expression.  **)
(** Refinement.fst`, `SPARQL11.Store.fst`, `SPARQL.Service.Wrap.fst` add   **)
(** more) is protected from an implicit unfold of the ~600-line evaluator **)
(** body blowing up its SMT context -- removing it to unblock this one    **)
(** theorem would widen the blast radius to every one of those call       **)
(** sites and needs its own dedicated re-verification commit, not a       **)
(** silent side effect of this one. So: `eval_expr_ebv_transparent`       **)
(** below is `eval_expr_ebv`'s own body (`ebv (eval_expr_with_base base e **)
(** mu)`), copied verbatim but WITHOUT `irreducible`, so this induction    **)
(** (and any future proof) can reach it; `theorem_filter_card`'s          **)
(** hypothesis remains open on the literal `eval_expr_ebv` / shipping     **)
(** `filter_solutions`.                                                   **)
(** ------------------------------------------------------------------ **)

#push-options "--z3rlimit 300 --fuel 4 --ifuel 4"

/// Every `mu`-read in `eval_expr_with_base` bottoms out in `Lh.assoc_tr`
/// (via `sm_lookup`/`fx_ctx_get`), the same primitive `S.sval` uses --
/// so `S.smap_eq` at a given key already gives assoc_tr-agreement at
/// that key, for ANY key (ordinary variable name or reserved fx_key_*).
let lemma_assoc_tr_congr (key : string) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  Lh.assoc_tr key mu == Lh.assoc_tr key mu') =
  Lh.lemma_assoc_tr_eq key mu;
  Lh.lemma_assoc_tr_eq key mu'

let lemma_sm_lookup_congr (v : string) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  sm_lookup v mu == sm_lookup v mu') =
  lemma_assoc_tr_congr v mu mu'

let lemma_fx_ctx_get_congr (key : string) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  fx_ctx_get key mu == fx_ctx_get key mu') =
  lemma_assoc_tr_congr key mu mu'

/// The induction. Structure mirrors `eval_expr_with_base`'s own match
/// (SPARQL11.Algebra.fst Part 8) constructor-family by constructor-
/// family, and the `and`-clique mirrors its four sibling functions
/// (`eval_coalesce_with_base` / `eval_geof_args_with_base` /
/// `eval_in_with_base` / `eval_concat_with_base`) plus one new helper
/// (`lemma_eval_expr_opt_congr`) for the `option expr` fields
/// (`E_Substr`/`E_Replace`/`E_Regex`'s optional 3rd/4th argument) that
/// the evaluator handles inline rather than through a named sibling.
/// The grouping below (which constructors share a proof) follows the
/// SAME arity classification `lemma_substitute_existentials_noop`
/// above already uses for the identical reason (uniform recursion into
/// every sub-expression) -- copied and re-purposed, not reinvented.
let rec lemma_eval_expr_congr (base : option wf_iri) (e : expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_expr_with_base base e mu == eval_expr_with_base base e mu')
          (decreases e) =
  match e with
  | E_Var v | E_Bound v ->
    lemma_sm_lookup_congr v mu mu'
  | E_Exists _ | E_NotExists _ | E_Aggregate _ _ _
  | E_IRI _ | E_Literal _ | E_BoolLit _ | E_NumericLit _
  | E_DecimalLit _ | E_DoubleLit _ | E_Now -> ()
  | E_Arith _ e1 e2 | E_Compare _ e1 e2 | E_And e1 e2 | E_Or e1 e2
  | E_StrDt e1 e2 | E_StrLang e1 e2
  | E_StrStarts e1 e2 | E_StrEnds e1 e2 | E_Contains e1 e2
  | E_StrBefore e1 e2 | E_StrAfter e1 e2
  | E_SameTerm e1 e2 ->
    lemma_eval_expr_congr base e1 mu mu';
    lemma_eval_expr_congr base e2 mu mu'
  | E_UnaryMinus e1 | E_UnaryPlus e1 | E_Not e1
  | E_IsIRI e1 | E_IsBlank e1 | E_IsLiteral e1 | E_IsNumeric e1
  | E_Str e1 | E_Lang e1 | E_Datatype e1 | E_IRI_fn e1
  | E_HasLang e1 | E_HasLangDir e1 | E_LangDir e1
  | E_StrLen e1 | E_UCase e1 | E_LCase e1 | E_EncodeForUri e1
  | E_Abs e1 | E_Round e1 | E_Ceil e1 | E_Floor e1
  | E_MD5 e1 | E_SHA1 e1 | E_SHA256 e1 | E_SHA384 e1 | E_SHA512 e1
  | E_Year e1 | E_Month e1 | E_Day e1 | E_Hours e1 | E_Minutes e1
  | E_Seconds e1 | E_Timezone e1 | E_Tz e1
  | E_TTSubject e1 | E_TTPredicate e1 | E_TTObject e1 | E_IsTriple e1 ->
    lemma_eval_expr_congr base e1 mu mu'
  | E_StrLangDir e1 e2 e3 | E_If e1 e2 e3 | E_TripleTerm e1 e2 e3 ->
    lemma_eval_expr_congr base e1 mu mu';
    lemma_eval_expr_congr base e2 mu mu';
    lemma_eval_expr_congr base e3 mu mu'
  | E_Coalesce es -> lemma_eval_coalesce_congr base es mu mu'
  | E_Concat es -> lemma_eval_concat_congr base es mu mu'
  | E_In ev es | E_NotIn ev es ->
    lemma_eval_expr_congr base ev mu mu';
    lemma_eval_in_congr base (eval_expr_with_base base ev mu) es mu mu'
  | E_Substr e1 e2 e3o | E_Regex e1 e2 e3o ->
    lemma_eval_expr_congr base e1 mu mu';
    lemma_eval_expr_congr base e2 mu mu';
    lemma_eval_expr_opt_congr base e3o mu mu'
  | E_Replace e1 e2 e3 e4o ->
    lemma_eval_expr_congr base e1 mu mu';
    lemma_eval_expr_congr base e2 mu mu';
    lemma_eval_expr_congr base e3 mu mu';
    lemma_eval_expr_opt_congr base e4o mu mu'
  | E_FunctionCall _ argsx ->
    // langMatches/xsd-cast/BNODE(str) read at most the first two
    // elements directly; geof reads the WHOLE list via
    // eval_geof_args_with_base; RAND/UUID/STRUUID/BNODE() read only
    // the fx_key_row/fx_key_occ context keys. All four covered.
    lemma_eval_geof_args_congr base argsx mu mu';
    (match argsx with
     | [] -> ()
     | [e1] -> lemma_eval_expr_congr base e1 mu mu'
     | e1 :: e2 :: _ ->
       lemma_eval_expr_congr base e1 mu mu';
       lemma_eval_expr_congr base e2 mu mu');
    lemma_fx_ctx_get_congr fx_key_row mu mu';
    lemma_fx_ctx_get_congr fx_key_occ mu mu'

and lemma_eval_coalesce_congr (base : option wf_iri) (es : list expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_coalesce_with_base base es mu == eval_coalesce_with_base base es mu')
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_eval_expr_congr base e mu mu';
    lemma_eval_coalesce_congr base rest mu mu'

and lemma_eval_geof_args_congr (base : option wf_iri) (es : list expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_geof_args_with_base base es mu == eval_geof_args_with_base base es mu')
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_eval_expr_congr base e mu mu';
    lemma_eval_geof_args_congr base rest mu mu'

and lemma_eval_in_congr (base : option wf_iri) (v : eval_result) (es : list expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_in_with_base base v es mu == eval_in_with_base base v es mu')
          (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    lemma_eval_expr_congr base e mu mu';
    lemma_eval_in_congr base v rest mu mu'

and lemma_eval_concat_congr (base : option wf_iri) (es : list expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_concat_with_base base es mu == eval_concat_with_base base es mu')
          (decreases es) =
  match es with
  | [] -> ()
  | [e] -> lemma_eval_expr_congr base e mu mu'
  | e :: rest ->
    lemma_eval_expr_congr base e mu mu';
    lemma_eval_concat_congr base rest mu mu'

and lemma_eval_expr_opt_congr (base : option wf_iri) (eo : option expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  (match eo with
                     | None -> True
                     | Some e1 -> eval_expr_with_base base e1 mu == eval_expr_with_base base e1 mu'))
          (decreases eo) =
  match eo with
  | None -> ()
  | Some e1 -> lemma_eval_expr_congr base e1 mu mu'

/// `eval_expr_ebv`'s own body (SPARQL11.Algebra.fst ~4487-4489),
/// restated WITHOUT `irreducible` so the induction above can reach it.
/// See FINDING FC-1: this is NOT the shipping `eval_expr_ebv` (that
/// symbol stays exactly as shipped, unmodified, per this file's SCOPE
/// promise) -- it is the same expression, transparently declared.
let eval_expr_ebv_transparent (base : option wf_iri) (e : expr) (mu : S.smap) : bool =
  ebv (eval_expr_with_base base e mu)

let lemma_eval_expr_ebv_transparent_congr (base : option wf_iri) (e : expr) (mu mu' : S.smap)
  : Lemma (requires S.smap_eq mu mu')
          (ensures  eval_expr_ebv_transparent base e mu == eval_expr_ebv_transparent base e mu') =
  lemma_eval_expr_congr base e mu mu'

/// `fexpr_congr`, discharged -- unconditionally, for every `base`/`e` --
/// of the transparent twin of the shipping evaluator's EBV wrapper.
let theorem_eval_expr_ebv_transparent_congr (base : option wf_iri) (e : expr)
  : Lemma (fexpr_congr (eval_expr_ebv_transparent base e)) =
  FStar.Classical.forall_intro_2
    (FStar.Classical.move_requires_2 (lemma_eval_expr_ebv_transparent_congr base e))

/// `theorem_filter_card`, restated UNCONDITIONALLY at the transparent
/// twin -- the "restate `theorem_filter_card` without the hypothesis"
/// deliverable, at the fragment FC-1 leaves reachable. `theorem_filter_card`
/// itself is UNCHANGED above: general infrastructure for an arbitrary
/// `f` a caller has independently shown `fexpr_congr` of.
let theorem_filter_card_eval_expr_with_base
      (base : option wf_iri) (e : expr) (omega : list S.smap)
  : Lemma (ensures S.filter_card_spec (eval_expr_ebv_transparent base e) omega
                     (List.Tot.filter (eval_expr_ebv_transparent base e) omega)) =
  theorem_eval_expr_ebv_transparent_congr base e;
  theorem_filter_card (eval_expr_ebv_transparent base e) omega

#pop-options

(** 5.1 The PRODUCTION filter path (`filter_solutions_with_graph`) agrees
    with the graph-free `filter_solutions` above, on the fragment where
    `e` has no EXISTS/NOT EXISTS. g4-filter-devacuation addendum. **)

/// `substitute_existentials` recurses into every sub-expression of `e`
/// unconditionally; on an `e` with `expr_has_existential e == false` none
/// of those sub-expressions is E_Exists/E_NotExists (each recursive
/// case's hypothesis follows from unfolding the `||` in
/// `expr_has_existential`'s matching case), so every case falls through
/// to its `E_ctor (substitute_existentials ... e1) ...` shape with the
/// IH giving `substitute_existentials ... e1 == e1`, reproducing `e`
/// unchanged. Structural induction mirroring `expr_has_existential`'s
/// match (Algebra.fst ~4587) against `substitute_existentials`'s match
/// (Algebra.fst ~4646).
let rec lemma_substitute_existentials_noop
      (base : option wf_iri) (e : expr) (mu : S.smap)
      (g : GE.rdf_graph) (ds : GE.rdf_dataset)
  : Lemma (requires expr_has_existential e == false)
          (ensures  substitute_existentials base e mu g ds == e)
          (decreases e) =
  match e with
  | E_Exists _ | E_NotExists _ -> ()
  | E_Var _ | E_IRI _ | E_Literal _ | E_BoolLit _ | E_NumericLit _
  | E_DecimalLit _ | E_DoubleLit _ | E_Bound _ | E_Now -> ()
  | E_Arith _ e1 e2 | E_Compare _ e1 e2 | E_And e1 e2 | E_Or e1 e2
  | E_StrDt e1 e2 | E_StrLang e1 e2
  | E_StrStarts e1 e2 | E_StrEnds e1 e2 | E_Contains e1 e2
  | E_StrBefore e1 e2 | E_StrAfter e1 e2
  | E_SameTerm e1 e2 ->
    lemma_substitute_existentials_noop base e1 mu g ds;
    lemma_substitute_existentials_noop base e2 mu g ds
  | E_UnaryMinus e1 | E_UnaryPlus e1 | E_Not e1
  | E_IsIRI e1 | E_IsBlank e1 | E_IsLiteral e1 | E_IsNumeric e1
  | E_Str e1 | E_Lang e1 | E_Datatype e1 | E_IRI_fn e1
  | E_HasLang e1 | E_HasLangDir e1 | E_LangDir e1
  | E_StrLen e1 | E_UCase e1 | E_LCase e1 | E_EncodeForUri e1
  | E_Abs e1 | E_Round e1 | E_Ceil e1 | E_Floor e1
  | E_MD5 e1 | E_SHA1 e1 | E_SHA256 e1 | E_SHA384 e1 | E_SHA512 e1
  | E_Year e1 | E_Month e1 | E_Day e1 | E_Hours e1 | E_Minutes e1
  | E_Seconds e1 | E_Timezone e1 | E_Tz e1
  | E_Aggregate _ _ e1
  | E_TTSubject e1 | E_TTPredicate e1 | E_TTObject e1 | E_IsTriple e1 ->
    lemma_substitute_existentials_noop base e1 mu g ds
  | E_StrLangDir e1 e2 e3 | E_If e1 e2 e3 | E_TripleTerm e1 e2 e3 ->
    lemma_substitute_existentials_noop base e1 mu g ds;
    lemma_substitute_existentials_noop base e2 mu g ds;
    lemma_substitute_existentials_noop base e3 mu g ds
  | E_Coalesce es | E_Concat es | E_FunctionCall _ es ->
    lemma_substitute_existentials_list_noop base es mu g ds
  | E_In e1 es | E_NotIn e1 es ->
    lemma_substitute_existentials_noop base e1 mu g ds;
    lemma_substitute_existentials_list_noop base es mu g ds
  | E_Substr e1 e2 e3o | E_Regex e1 e2 e3o ->
    lemma_substitute_existentials_noop base e1 mu g ds;
    lemma_substitute_existentials_noop base e2 mu g ds;
    lemma_substitute_existentials_opt_noop base e3o mu g ds
  | E_Replace e1 e2 e3 e4o ->
    lemma_substitute_existentials_noop base e1 mu g ds;
    lemma_substitute_existentials_noop base e2 mu g ds;
    lemma_substitute_existentials_noop base e3 mu g ds;
    lemma_substitute_existentials_opt_noop base e4o mu g ds

and lemma_substitute_existentials_list_noop
      (base : option wf_iri) (es : list expr) (mu : S.smap)
      (g : GE.rdf_graph) (ds : GE.rdf_dataset)
  : Lemma (requires expr_list_has_existential es == false)
          (ensures  substitute_existentials_list base es mu g ds == es)
          (decreases es) =
  match es with
  | [] -> ()
  | hd :: tl ->
    lemma_substitute_existentials_noop base hd mu g ds;
    lemma_substitute_existentials_list_noop base tl mu g ds

and lemma_substitute_existentials_opt_noop
      (base : option wf_iri) (eo : option expr) (mu : S.smap)
      (g : GE.rdf_graph) (ds : GE.rdf_dataset)
  : Lemma (requires expr_opt_has_existential eo == false)
          (ensures  substitute_existentials_opt base eo mu g ds == eo)
          (decreases eo) =
  match eo with
  | None -> ()
  | Some e1 -> lemma_substitute_existentials_noop base e1 mu g ds

/// `filter_solutions_with_graph` is `filter_solutions` once
/// `substitute_existentials` is a no-op: both reduce to
/// `List.Tot.filter (eval_expr_ebv base e)` on the same `omega`.
let rec theorem_filter_with_graph_is_filter_solutions
      (base : option wf_iri) (e : expr) (omega : solution_sequence)
      (g : GE.rdf_graph) (ds : GE.rdf_dataset)
  : Lemma (requires expr_has_existential e == false)
          (ensures  filter_solutions_with_graph base e omega g ds ==
                    filter_solutions base e omega)
          (decreases omega) =
  match omega with
  | [] -> ()
  | mu :: rest ->
    lemma_substitute_existentials_noop base e mu g ds;
    theorem_filter_with_graph_is_filter_solutions base e rest g ds

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

/// FIXED 2026-08-03. `sm_equal` is now a mutual-submap check --
/// order-insensitive, per section 18.3 -- and the three lemmas below
/// are the POSITIVE forms of the SR-1 refutation this file used to
/// carry (the refutation's own witness, re-judged by the repaired
/// function). History of the defect: issue #336 quotes the old
/// theorems in full.
let lemma_sr1_sm_equal_agrees ()
  : Lemma (sm_equal sr1_mu1 sr1_mu2 == true) =
  assert_norm (sm_equal sr1_mu1 sr1_mu2 == true)

let lemma_sr1_distinct_dedups ()
  : Lemma (distinct_solutions [sr1_mu1; sr1_mu2] == [sr1_mu2]) =
  assert_norm (distinct_solutions [sr1_mu1; sr1_mu2] == [sr1_mu2])

/// Card[Distinct(Omega)][mu] = 1 (section 18.5) now HOLDS on the exact
/// witness that refuted it: both input mappings denote one partial
/// function, and DISTINCT keeps exactly one representative.
///
/// (`distinct_solutions` keeps the LAST positional occurrence of an
/// equivalence class -- sm_mem checks the tail -- which is sr1_mu2
/// here; any representative satisfies the cardinality clause, since
/// mult counts through `smap_eqb`, which identifies the two.)
let theorem_sr1_witness_now_card_conformant ()
  : Lemma (S.distinct_card_spec [sr1_mu1; sr1_mu2]
                                (distinct_solutions [sr1_mu1; sr1_mu2])) =
  lemma_sr1_same_mapping ();
  lemma_sr1_distinct_dedups ();
  // The spec's forall ranges over ALL mappings, not just the members
  // of the witness sequence, so the proof is a genuine case split on
  // an arbitrary mu: whichever of the two witnesses mu matches by
  // smap_eqb, transitivity through smap_eq sr1_mu1 sr1_mu2 makes it
  // match the other, so the two multiplicities rise and fall together.
  introduce forall (mu : S.smap).
      S.mult mu [sr1_mu2] ==
      (if S.mult mu [sr1_mu1; sr1_mu2] > 0 then 1 else 0)
  with begin
    (if S.smap_eqb mu sr1_mu1 then begin
       S.lemma_smap_eqb_sound mu sr1_mu1;
       S.lemma_smap_eq_trans mu sr1_mu1 sr1_mu2;
       S.lemma_smap_eqb_complete mu sr1_mu2
     end);
    (if S.smap_eqb mu sr1_mu2 then begin
       S.lemma_smap_eqb_sound mu sr1_mu2;
       S.lemma_smap_eq_sym sr1_mu1 sr1_mu2;
       S.lemma_smap_eq_trans mu sr1_mu2 sr1_mu1;
       S.lemma_smap_eqb_complete mu sr1_mu1
     end)
  end;
  assert (S.distinct_card_spec [sr1_mu1; sr1_mu2] [sr1_mu2])

/// The repaired `sm_equal` agrees with the specification's `smap_eq`
/// on the witness pair. The GENERAL agreement (sm_equal decides
/// smap_eq wherever the two term equalities coincide) is deliberately
/// NOT stated here: `sm_equal` compares terms with `rdf_term_eq` and
/// `smap_eq` with term identity, and which of those is RDF 1.1 term
/// equality is the #324 dispute. DISTINCT does not get to settle #324
/// as a side effect; when #324 retires one equality, the general
/// theorem becomes stateable.
let theorem_sm_equal_matches_smap_eq_on_witness ()
  : Lemma (S.smap_eq sr1_mu1 sr1_mu2 /\ sm_equal sr1_mu1 sr1_mu2 == true) =
  lemma_sr1_same_mapping ();
  lemma_sr1_sm_equal_agrees ()

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

/// FIXED 2026-08-03 (issue #337). `sm_join_key` now serialises
/// `RDF.Term.join_canon_term` of each bound term -- the canonical form
/// that folds exactly what `rdf_term_eq` folds -- so the two theorems
/// below replace the finer-than refutation this file used to carry
/// (issue #337 quotes it in full). `lemma_sr2_nq_differs` above is KEPT:
/// it documents the raw serialiser's byte behaviour, which is unchanged
/// and still true -- the fix moved the KEY off the raw serialisation,
/// it did not change the serialiser.
///
/// The witness, re-judged: same hypotheses as the refutation (two tags
/// equal under lowercase, distinct as strings), and the keys are now
/// EQUAL while the mappings remain compatible -- the narrowing step can
/// no longer separate what the acceptance test identifies.
let theorem_sr2_witness_keys_now_agree (v : string) (tag1 tag2 : string)
  : Lemma (requires String.lowercase tag1 == String.lowercase tag2 /\
                    tag1 =!= tag2)
          (ensures  (let t1 = T_Literal (sr2_lit tag1) in
                     let t2 = T_Literal (sr2_lit tag2) in
                     let mu1 : S.smap = [(v, t1)] in
                     let mu2 : S.smap = [(v, t2)] in
                     rdf_term_eq t1 t2 == true /\
                     sm_compatible mu1 mu2 == true /\
                     sm_join_key [v] mu1 == sm_join_key [v] mu2)) =
  let t1 = T_Literal (sr2_lit tag1) in
  let t2 = T_Literal (sr2_lit tag2) in
  lemma_join_canon_term_eq t1 t2

/// The GENERAL superset property, no witness needed: any two terms the
/// acceptance test identifies produce the same single-variable key.
/// This is the property the hash join needs to be semantics-preserving,
/// now a theorem instead of a banner assertion.
let theorem_join_key_no_finer_than_compatibility (v : string) (t1 t2 : rdf_term)
  : Lemma (requires rdf_term_eq t1 t2 == true)
          (ensures  sm_join_key [v] [(v, t1)] == sm_join_key [v] [(v, t2)]) =
  lemma_join_canon_term_eq t1 t2

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


(** ====================================================================== **)
(** Part 14: BGP matching (sections 18.3.1 / 18.5)                         **)
(** ====================================================================== **)

/// mu' extends mu: every variable mu binds, mu' binds to the same term.
let binding_extends (a b : S.smap) : prop =
  forall (v : string) (x : rdf_term). S.sval v b == Some x ==> S.sval v a == Some x

let lemma_binding_extends_refl (a : S.smap) : Lemma (binding_extends a a) = ()

let lemma_binding_extends_trans (a b c : S.smap)
  : Lemma (requires binding_extends a b /\ binding_extends b c)
          (ensures  binding_extends a c) = ()

/// RDF 1.2 triple terms are QUARANTINED from this result, exactly as
/// the simple-entailment vertical quarantined them from its model
/// theory (`graph_tt_free`). They are not hard for a different reason
/// here -- the recursion is routine -- but they double the case
/// analysis and nothing in the fragment needs them. Stated as an
/// explicit hypothesis, never silently assumed.
let ptrm_tt_free (pt : pattern_term) : bool =
  match pt with
  | PT_TripleTerm _ _ _ -> false
  | _ -> true

let psub_tt_free (ps : pattern_subject) : bool =
  match ps with
  | PS_TripleTerm _ _ _ -> false
  | _ -> true

let term_tt_free (t : rdf_term) : bool =
  match t with
  | T_TripleTerm _ _ _ -> false
  | _ -> true

/// The pattern's own literal constants must be exact for the same
/// reason a mapping's bound terms must be: `try_bind_term` accepts a
/// graph literal on `literal_eq`, which is coarser than term identity,
/// and then `instantiate_tp` emits the PATTERN's literal, not the
/// graph's. Without this the two are different terms.
let ptrm_exact (pt : pattern_term) : prop =
  match pt with
  | PT_Literal l -> term_exact (T_Literal l)
  | _ -> True

/// A mapping's LOOKUP values are exact when its list entries are.
let rec lemma_smap_exact_sval (mu : S.smap) (v : string) (x : rdf_term)
  : Lemma (requires smap_exact mu /\ S.sval v mu == Some x)
          (ensures  term_exact x)
          (decreases mu) =
  match mu with
  | [] -> ()
  | (w, _) :: rest -> if w = v then () else lemma_smap_exact_sval rest v x

/// The core of BGP matching, in the shape section 7.3 of the
/// simple-entailment design doc identifies as the only one that makes
/// a search-with-accumulator induction go through: the
/// FORALL-OVER-LATER-EXTENSIONS conjunct. The substitution that finally
/// explains the whole pattern is read off the FINAL binding, built long
/// after this step, so a per-step statement of the form "this step
/// produces a binding that explains this position" is not usable.
let lemma_try_bind_term_instantiates
      (pt : pattern_term) (t : rdf_term) (mu mu' : S.smap)
  : Lemma (requires try_bind_term pt t mu == Some mu' /\
                    smap_exact mu /\ ptrm_exact pt /\ term_exact t /\
                    ptrm_tt_free pt /\ term_tt_free t)
          (ensures  binding_extends mu' mu /\ smap_exact mu' /\
                    (forall (mu2 : S.smap). binding_extends mu2 mu' ==>
                       bound_object_of_pattern pt mu2 == Some t)) =
  match pt with
  | PT_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    (match sm_lookup v mu with
     | Some existing ->
       lemma_smap_exact_sval mu v existing;
       assert (rdf_term_eq existing t == true);
       assert (existing == t);
       assert (mu' == mu);
       assert (S.sval v mu' == Some existing);
       let aux (mu2 : S.smap)
         : Lemma (requires binding_extends mu2 mu')
                 (ensures  bound_object_of_pattern pt mu2 == Some t) =
         Lh.lemma_assoc_tr_eq v mu2;
         assert (S.sval v mu2 == Some existing)
       in
       FStar.Classical.forall_intro (fun mu2 -> FStar.Classical.move_requires aux mu2)
     | None ->
       assert (mu' == sm_bind v t mu);
       assert (S.sval v mu' == Some t);
       let aux (mu2 : S.smap)
         : Lemma (requires binding_extends mu2 mu')
                 (ensures  bound_object_of_pattern pt mu2 == Some t) =
         Lh.lemma_assoc_tr_eq v mu2;
         assert (S.sval v mu2 == Some t)
       in
       FStar.Classical.forall_intro (fun mu2 -> FStar.Classical.move_requires aux mu2))
  | _ -> ()

let lemma_try_bind_subject_instantiates
      (ps : pattern_subject) (sj : subject) (mu mu' : S.smap)
  : Lemma (requires try_bind_subject ps sj mu == Some mu' /\
                    smap_exact mu /\ psub_tt_free ps)
          (ensures  binding_extends mu' mu /\ smap_exact mu' /\
                    (forall (mu2 : S.smap). binding_extends mu2 mu' ==>
                       bound_subject_of_pattern ps mu2 == Some sj)) =
  match ps with
  | PS_Var v ->
    Lh.lemma_assoc_tr_eq v mu;
    (match sm_lookup v mu with
     | Some existing ->
       (lemma_smap_exact_sval mu v existing;
        assert (mu' == mu);
        assert (S.sval v mu' == Some (subject_to_term sj)))
     | None -> assert (S.sval v mu' == Some (subject_to_term sj)));
    let aux (mu2 : S.smap)
      : Lemma (requires binding_extends mu2 mu')
              (ensures  bound_subject_of_pattern ps mu2 == Some sj) =
      Lh.lemma_assoc_tr_eq v mu2;
      assert (S.sval v mu2 == Some (subject_to_term sj))
    in
    FStar.Classical.forall_intro (fun mu2 -> FStar.Classical.move_requires aux mu2)
  | _ -> ()

/// BGP matching, one triple pattern: if `tp_match` accepts, the
/// resulting binding EXTENDS the incoming one and INSTANTIATES the
/// pattern to exactly the matched triple -- which is section 18.3.1's
/// "mu(P) is in G", the subgraph clause of `S.bgp_sol_spec`, for a
/// single pattern.
let theorem_tp_match_instantiates
      (tp : triple_pattern) (t : RDF.Triple.triple) (mu mu' : S.smap)
  : Lemma (requires tp_match tp t mu == Some mu' /\ smap_exact mu /\
                    psub_tt_free tp.tp_s /\
                    ptrm_tt_free tp.tp_p /\ ptrm_exact tp.tp_p /\
                    ptrm_tt_free tp.tp_o /\ ptrm_exact tp.tp_o /\
                    term_exact t.o /\ term_tt_free t.o)
          (ensures  binding_extends mu' mu /\ smap_exact mu' /\
                    instantiate_tp tp mu' == Some t) =
  let mu1 = Some?.v (try_bind_subject tp.tp_s t.s mu) in
  lemma_try_bind_subject_instantiates tp.tp_s t.s mu mu1;
  let mu2 = Some?.v (try_bind_term tp.tp_p (T_IRI t.p) mu1) in
  lemma_try_bind_term_instantiates tp.tp_p (T_IRI t.p) mu1 mu2;
  lemma_try_bind_term_instantiates tp.tp_o t.o mu2 mu';
  lemma_binding_extends_trans mu' mu2 mu1;
  lemma_binding_extends_trans mu' mu1 mu;
  lemma_binding_extends_refl mu'

#pop-options

#push-options "--z3rlimit 120 --fuel 3 --ifuel 2"


(** ====================================================================== **)
(** Part 15: ORDER BY / DISTINCT completeness / OFFSET-LIMIT (section 18.4) **)
(** ====================================================================== **)

// -------------------------------------------------------------------
// 15.1 ORDER BY -- `sort_solutions` is a permutation of its input
// (section 18.4: sorting reorders a solution sequence, it does not
// add or drop rows).
//
// `sort_solutions base conds` is `List.Tot.sortWith
// (compare_on_conditions base conds)`. The stdlib's own permutation
// lemma, `FStar.List.Tot.Properties.sortWith_permutation`, needs
// `#a:eqtype` -- it goes through `List.Tot.count`, which needs a
// decidable `=` on the element type. `S.smap = list (var_name *
// rdf_term)` and `rdf_term` is `noeq` (RDF.Term.fsti), so `S.smap`
// does NOT satisfy `eqtype`: instantiating `sortWith_permutation` at
// any noeq-carrying element type fails typechecking with "Expected
// type Prims.eqtype got type Type0" (checked directly against a
// minimal noeq reproducer before writing this section). So the
// stdlib lemma is not directly applicable here, contrary to the
// obvious reading of its signature.
//
// The permutation fact is re-derived at the MULT level instead --
// counting occurrences via `S.smap_eqb`, the exact decision procedure
// `S.mult` is built from (Spec.fst:708-709) -- by replaying
// `sortWith`'s own partition/append recursion (FStar.List.Tot.Base.fst,
// the `sortWith` definition) directly. This is the same technique
// `OWL.Semantics.MemLemmas.lemma_sortWith_memP`/`_rev` already use, one
// module over, for the strictly weaker memP-only fact (no cardinality)
// about `sortWith` on `triple`, another noeq-carrying type; `S.mult`
// asks for the stronger per-element COUNT, which the memP-only
// technique does not give, so the partition/append induction is
// redone here at the `List.Tot.filter`+`length` level.
// `SPARQL11.Algebra.lemma_filter_append` (section 19.3 of that module)
// supplies the append half.
//
// NOT attempted: a sortedness theorem. `compare_on_condition` returns
// 0 -- "equal" -- for two solution mappings that are not `sm_equal`
// (e.g. mappings binding disjoint variable sets, so every `OC_Asc`/
// `OC_Desc` condition evaluates its expression to the same "unbound"
// case on both sides; or two mappings `sparql_order`'s catch-all
// branches do not distinguish), so `compare_on_conditions` is not
// ANTISYMMETRIC: `f a b == 0 == f b a` for `a =!= b` is a
// counterexample to the antisymmetry conjunct of
// `FStar.List.Tot.Properties.total_order`
// (FStar.List.Tot.Properties.fsti, `total_order`), which
// `sortWith_sorted` requires unconditionally to conclude `sorted`. A
// comparator that fails antisymmetry cannot supply a `total_order`
// instance. ATTEMPTED in section 15.1b below, against a bespoke
// (non-stdlib) adjacent-pairs sortedness statement and a bespoke
// (non-antisymmetric) total-preorder hypothesis on the comparator.
// -------------------------------------------------------------------

let rec lemma_filter_partition_count (#a:Type) (eqb : a -> a -> bool) (p : a -> bool) (l : list a) (x : a)
  : Lemma (ensures
      List.Tot.length (List.Tot.filter (eqb x) l) ==
      List.Tot.length (List.Tot.filter (eqb x) (fst (List.Tot.partition p l))) +
      List.Tot.length (List.Tot.filter (eqb x) (snd (List.Tot.partition p l))))
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> lemma_filter_partition_count eqb p tl x

let rec lemma_sortWith_mult (#a:Type) (eqb : a -> a -> bool) (f : a -> a -> Tot int) (l : list a) (x : a)
  : Lemma (ensures
      List.Tot.length (List.Tot.filter (eqb x) (List.Tot.sortWith f l)) ==
      List.Tot.length (List.Tot.filter (eqb x) l))
          (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare f pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare f pivot) tl;
    lemma_sortWith_mult eqb f lo x;
    lemma_sortWith_mult eqb f hi x;
    lemma_filter_partition_count eqb (List.Tot.bool_of_compare f pivot) tl x;
    assert (List.Tot.length (List.Tot.filter (eqb x) tl) ==
            List.Tot.length (List.Tot.filter (eqb x) hi) +
            List.Tot.length (List.Tot.filter (eqb x) lo));
    assert (List.Tot.sortWith f l ==
            List.Tot.append (List.Tot.sortWith f lo) (pivot :: List.Tot.sortWith f hi));
    lemma_filter_append (eqb x) (List.Tot.sortWith f lo) (pivot :: List.Tot.sortWith f hi);
    assert (List.Tot.filter (eqb x) (List.Tot.sortWith f l) ==
            List.Tot.append (List.Tot.filter (eqb x) (List.Tot.sortWith f lo))
                             (List.Tot.filter (eqb x) (pivot :: List.Tot.sortWith f hi)));
    List.Tot.append_length (List.Tot.filter (eqb x) (List.Tot.sortWith f lo))
                            (List.Tot.filter (eqb x) (pivot :: List.Tot.sortWith f hi))

// The eqb PARAMETER form above is what makes `lemma_sortWith_mult`
// itself go through (every use of `eqb x` is the same bound variable,
// so no closure-identity issue between call sites). Connecting the
// result to `S.mult` -- which hardcodes its OWN lambda, `fun m ->
// smap_eqb mu m` (Spec.fst:708-709) -- needs a bridge: `S.smap_eqb mu`
// (a bare partial application) and that lambda are extensionally the
// same predicate but are NOT identified by a plain SMT `assert` here
// (confirmed: instantiating `eqb := S.smap_eqb` and asserting the
// `S.mult`-unfolded equality directly fails). `mult_pred` is `unfold`,
// so `mult_pred mu` beta-reduces (no eta needed) to exactly `S.mult`'s
// own lambda shape, and `trefl` -- definitional equality, not an SMT
// query -- closes the resulting goal directly (the same class of fix
// `lemma_join_nested_loop_unfold`/`lemma_minus_unfold` use for the
// analogous inline-lambda-vs-named-copy gap, Part 8/11 above).
unfold let mult_pred (mu m : S.smap) : bool = S.smap_eqb mu m

let lemma_mult_is_filter_length (mu : S.smap) (l : list S.smap)
  : Lemma (S.mult mu l == List.Tot.length (List.Tot.filter (mult_pred mu) l)) =
  assert (S.mult mu l == List.Tot.length (List.Tot.filter (mult_pred mu) l))
    by (FStar.Tactics.trefl ())

/// The NORMATIVE (bag) statement: ORDER BY reorders without adding or
/// dropping rows. Unconditional -- no fragment hypothesis of any kind.
/// `S.mult` (not `List.Tot.count`, unavailable at this noeq-carrying
/// type) is the same multiset-membership count `theorem_union_card`
/// and `theorem_filter_card` already use.
let lemma_sort_solutions_permutation_pointwise
      (base : option wf_iri) (conds : list order_condition) (omega : list S.smap) (mu : S.smap)
  : Lemma (S.mult mu (sort_solutions base conds omega) == S.mult mu omega) =
  lemma_sortWith_mult mult_pred (compare_on_conditions base conds) omega mu;
  lemma_mult_is_filter_length mu (sort_solutions base conds omega);
  lemma_mult_is_filter_length mu omega

let theorem_sort_solutions_permutation
      (base : option wf_iri) (conds : list order_condition) (omega : list S.smap)
  : Lemma (forall (mu : S.smap).
             S.mult mu (sort_solutions base conds omega) == S.mult mu omega) =
  FStar.Classical.forall_intro (lemma_sort_solutions_permutation_pointwise base conds omega)

(** ------------------------------------------------------------------ **)
(** 15.1b ORDER BY -- sortedness (adjacent-pairs form), not via the     **)
(** stdlib. This is the wave the "NOT attempted" note above 15.1       **)
(** points at.                                                          **)
(**                                                                     **)
(** `FStar.List.Tot.Properties.sortWith_sorted` needs TWO things this   **)
(** module cannot supply: `#a:eqtype` (`S.smap` is `noeq` -- the same   **)
(** obstruction 15.1 already works around for the permutation fact),    **)
(** and `total_order (bool_of_compare f)`, which expands to a           **)
(** REFLEXIVITY conjunct `forall a. bool_of_compare f a a`, i.e.        **)
(** `f a a < 0` for every `a` -- false for any comparator with `f a a   **)
(** = 0` (every comparator in this file, `compare_on_conditions`        **)
(** included, since `[]`-conditions and equal mappings both compare     **)
(** to 0). So `sortWith_sorted` is not reachable here at all, not even  **)
(** narrowly -- both its type-level and its prop-level preconditions    **)
(** fail independently of the antisymmetry point the 15.1 comment       **)
(** names. The lemmas below replay `sortWith`'s own partition/append    **)
(** recursion directly (the same technique 15.1 uses for the            **)
(** permutation fact), proving a WEAKER, ADJACENT-PAIRS-ONLY             **)
(** sortedness statement (`sorted_by`) against a WEAKER, non-            **)
(** antisymmetric hypothesis on `f` (`totality_on` / `transitivity_on`  **)
(** -- a total PREORDER, not a total order).                            **)
(**                                                                     **)
(** FINDING (`totality_on`'s exact shape). The obvious transcription    **)
(** of "total preorder" as the DISJUNCTIVE reading -- `forall x y.      **)
(** f x y <= 0 \/ f y x <= 0` -- is NOT strong enough to carry this     **)
(** proof; it is satisfiable by a comparator that still breaks          **)
(** sortedness. Concrete 2-element counterexample: elements `a`, `b`    **)
(** with `f a b = 0`, `f b a = 1`. The disjunctive check at (a,b) is    **)
(** satisfied by its FIRST disjunct (`f a b <= 0`) alone, so it says    **)
(** nothing about `f b a`; transitivity is vacuous with only 2          **)
(** elements, so it cannot rescue this either. Yet `sortWith f [a;b] =  **)
(** [b;a]` (pivot `a`; `bool_of_compare f a b = (f a b < 0) = false`,   **)
(** so `b` partitions into `lo`, giving `append (sortWith f [b]) [a] =  **)
(** [b;a]`), and `sorted_by` on that result needs `f b a <= 0`, which   **)
(** is false. `totality_on` below is stated in the IMPLICATIONAL form   **)
(** that actually closes this gap (`f x y >= 0 ==> f y x <= 0`); it     **)
(** still implies the disjunctive reading (case on `f x y < 0` vs      **)
(** `>= 0`), so nothing standard is lost, and it is still not           **)
(** antisymmetry -- no tie ever forces an element equality.             **)
(**                                                                     **)
(** FINDING (`transitivity_on` is carried, not used). `sorted_by` is a  **)
(** purely LOCAL (adjacent-pairs) property; the partition/append proof  **)
(** below only ever relates a pivot to its immediate lo/hi neighbours,  **)
(** never chains three list elements together, so `transitivity_on`    **)
(** never actually fires inside `lemma_sortWith_sorted_by`'s proof      **)
(** term. It is kept as a hypothesis on the public theorem              **)
(** (`theorem_sort_solutions_sorted`, below) because (a) it is the      **)
(** natural closing conjunct of "total preorder" and every concrete     **)
(** comparator this project instantiates it with satisfies it, and (b)  **)
(** a future ALL-PAIRS sortedness statement -- mirroring                **)
(** `RDF.Indexed.Completeness.sorted_pairs`, whose own                  **)
(** `lemma_sorted_pairs_append` DOES need transitivity, through the     **)
(** pivot -- will need it.                                              **)
(** ------------------------------------------------------------------ **)

/// Adjacent-pairs sortedness for an arbitrary int comparator `f`, with
/// NO decidable-equality requirement on the element type -- unlike
/// stdlib's `sorted`/`sortWith_sorted`, which need `#a:eqtype`
/// transitively (through `sortWith_sorted`'s own `#a:eqtype`, not just
/// through `total_order`). Same recursion shape as
/// `FStar.List.Tot.Properties.sorted`, just `prop`-valued (so it
/// type-checks against `noeq` element types like `S.smap`) and stated
/// directly on `f`'s own sign instead of `bool_of_compare f` -- no
/// artificial strict/non-strict split at the specification level.
let rec sorted_by (#a:Type) (f : a -> a -> Tot int) (l : list a) : prop =
  match l with
  | [] -> True
  | [_] -> True
  | x :: y :: tl -> f x y <= 0 /\ sorted_by f (y :: tl)

/// Total-preorder totality, restricted to `l`'s members, in the
/// IMPLICATIONAL form the proof below needs -- see the totality_on
/// FINDING above the section banner; the disjunctive textbook reading
/// is not strong enough. Still not antisymmetry: a tie (`f x y = 0`)
/// is required to reflect (`f y x <= 0`), never to force `x == y`.
let totality_on (#a:Type) (f : a -> a -> Tot int) (l : list a) : prop =
  forall (x y : a). List.Tot.memP x l /\ List.Tot.memP y l ==>
                     (f x y >= 0 ==> f y x <= 0)

/// Total-preorder transitivity, restricted to `l`'s members. Carried
/// per the brief; see the transitivity_on FINDING above the section
/// banner -- unused by `lemma_sortWith_sorted_by`'s adjacent-pairs
/// proof, needed by any future all-pairs sortedness statement.
let transitivity_on (#a:Type) (f : a -> a -> Tot int) (l : list a) : prop =
  forall (x y z : a). List.Tot.memP x l /\ List.Tot.memP y l /\ List.Tot.memP z l ==>
                       (f x y <= 0 /\ f y z <= 0 ==> f x z <= 0)

/// `totality_on` weakens along a member-subset -- lets the recursive
/// calls into `lo`/`hi` (below) discharge their OWN `totality_on`
/// obligation from the caller's, instead of needing a fresh hypothesis
/// threaded by hand.
let lemma_totality_on_weaken (#a:Type) (f : a -> a -> Tot int) (l l' : list a)
  : Lemma (requires totality_on f l /\ (forall x. List.Tot.memP x l' ==> List.Tot.memP x l))
          (ensures totality_on f l') = ()

/// `partition`'s own characterization, memP-based (noeq-safe -- same
/// technique `RDF.Indexed.Completeness.lemma_partition_pred_memP` uses
/// one module over, here folding in the plain subset-membership half
/// too): an element filed on a side of the partition is a member of
/// the original list AND satisfies (or refutes) the predicate
/// accordingly. Replays `partition`'s own recursion
/// (FStar.List.Tot.Base.fst).
let rec lemma_partition_bool_memP (#a:Type) (f : a -> Tot bool) (l : list a) (x : a)
  : Lemma
    (ensures
       (List.Tot.memP x (fst (List.Tot.partition f l)) ==> List.Tot.memP x l /\ f x == true) /\
       (List.Tot.memP x (snd (List.Tot.partition f l)) ==> List.Tot.memP x l /\ f x == false))
    (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> lemma_partition_bool_memP f tl x

let lemma_partition_bool_memP_forall (#a:Type) (f : a -> Tot bool) (l : list a)
  : Lemma
    (ensures
       (forall x. List.Tot.memP x (fst (List.Tot.partition f l)) ==> List.Tot.memP x l /\ f x == true) /\
       (forall x. List.Tot.memP x (snd (List.Tot.partition f l)) ==> List.Tot.memP x l /\ f x == false)) =
  FStar.Classical.forall_intro (lemma_partition_bool_memP f l)

/// One boundary step: `pivot :: hi` is sorted given `hi` is sorted and
/// `pivot` relates to every member of `hi`. Split out of
/// `lemma_sorted_by_append` below because both of ITS base cases
/// reduce to exactly this.
let lemma_sorted_by_cons_hi (#a:Type) (f : a -> a -> Tot int) (pivot : a) (hi : list a)
  : Lemma
    (requires sorted_by f hi /\ (forall y. List.Tot.memP y hi ==> f pivot y <= 0))
    (ensures sorted_by f (pivot :: hi)) =
  match hi with
  | [] -> ()
  | _ :: _ -> ()

/// The append-merge step: an already-sorted `lo` followed by `pivot`
/// followed by an already-sorted `hi` is `sorted_by`-sorted overall,
/// given every element of `lo` relates to `pivot` and `pivot` relates
/// to every element of `hi`. This is the only cross-list fact the
/// induction needs -- `sorted_by` only asks about ADJACENT pairs, so a
/// per-element (not merely per-adjacent-pair) hypothesis against the
/// pivot covers whatever position ends up next to it, however the
/// recursive sort inside `lo`/`hi` chose to order it; no transitivity
/// chain through 3 elements is ever needed here (contrast
/// `RDF.Indexed.Completeness.lemma_sorted_pairs_append`, whose ALL-
/// PAIRS statement genuinely does need one, through the pivot).
let rec lemma_sorted_by_append (#a:Type) (f : a -> a -> Tot int)
      (lo : list a) (pivot : a) (hi : list a)
  : Lemma
    (requires
       sorted_by f lo /\ sorted_by f hi /\
       (forall y. List.Tot.memP y lo ==> f y pivot <= 0) /\
       (forall y. List.Tot.memP y hi ==> f pivot y <= 0))
    (ensures sorted_by f (List.Tot.append lo (pivot :: hi)))
    (decreases lo) =
  match lo with
  | [] -> lemma_sorted_by_cons_hi f pivot hi
  | [_] -> lemma_sorted_by_cons_hi f pivot hi
  | x :: y :: tl -> lemma_sorted_by_append f (y :: tl) pivot hi

/// The bespoke sortedness theorem: `List.Tot.sortWith f l` is
/// `sorted_by f`, given only `totality_on f l` (see the
/// transitivity_on FINDING above the section banner for why
/// `transitivity_on` is not a hypothesis here). Replays `sortWith`'s
/// own partition/append recursion (FStar.List.Tot.Base.fst, the
/// `sortWith` definition), exactly as `lemma_sortWith_mult` (15.1,
/// above) does for the permutation fact, reusing
/// `OWL.Semantics.MemLemmas.lemma_sortWith_memP_forall` for the
/// membership-preservation half (already generic in `#a:Type`, no
/// eqtype needed -- proved one module over for the same `noeq`
/// reason, per "Foundations to reuse, never rebuild").
let rec lemma_sortWith_sorted_by (#a:Type) (f : a -> a -> Tot int) (l : list a)
  : Lemma
    (requires totality_on f l)
    (ensures sorted_by f (List.Tot.sortWith f l))
    (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | [_] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare f pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare f pivot) tl;
    lemma_partition_bool_memP_forall (List.Tot.bool_of_compare f pivot) tl;
    lemma_totality_on_weaken f l lo;
    lemma_totality_on_weaken f l hi;
    lemma_sortWith_sorted_by f lo;
    lemma_sortWith_sorted_by f hi;
    Mem.lemma_sortWith_memP_forall f lo;
    Mem.lemma_sortWith_memP_forall f hi;
    let aux_lo (y : a) : Lemma
      (requires List.Tot.memP y (List.Tot.sortWith f lo))
      (ensures f y pivot <= 0) =
      assert (List.Tot.memP y lo);
      assert (List.Tot.memP y tl /\ List.Tot.bool_of_compare f pivot y == false);
      assert (f pivot y >= 0);
      assert (List.Tot.memP y l);
      assert (List.Tot.memP pivot l)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_lo);
    let aux_hi (y : a) : Lemma
      (requires List.Tot.memP y (List.Tot.sortWith f hi))
      (ensures f pivot y <= 0) =
      assert (List.Tot.memP y hi);
      assert (List.Tot.bool_of_compare f pivot y == true);
      assert (f pivot y < 0)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_hi);
    lemma_sorted_by_append f (List.Tot.sortWith f lo) pivot (List.Tot.sortWith f hi)

/// `sort_solutions` is `sorted_by (compare_on_conditions base conds)`,
/// given the comparator is a total preorder over `omega`'s own
/// members -- the fragment hypothesis every ORDER BY clause needs
/// carried explicitly (see the two FINDINGs above the 15.1b banner):
/// the UNCONDITIONAL statement is FALSE, both abstractly
/// (`compare_on_conditions` ties unrelated mappings at 0 with no
/// promise the tie reflects) and concretely (the numeric-literal
/// FRAGMENT finding below names a live counterexample reachable from
/// `sparql_order` itself).
let theorem_sort_solutions_sorted
      (base : option wf_iri) (conds : list order_condition) (omega : list S.smap)
  : Lemma
    (requires totality_on (compare_on_conditions base conds) omega /\
              transitivity_on (compare_on_conditions base conds) omega)
    (ensures sorted_by (compare_on_conditions base conds) (sort_solutions base conds omega)) =
  lemma_sortWith_sorted_by (compare_on_conditions base conds) omega

// -------------------------------------------------------------------
// 15.1c FRAGMENT -- same-kind IRI comparisons discharge totality_on /
// transitivity_on cleanly (deliverable 3, first shape tried).
// `sparql_order`'s IRI branch (Algebra.fst:5237-5238) computes exactly
// `String.compare (iri_to_string _) (iri_to_string _)`, so
// `RDF.Indexed.StringOrder`'s three axioms for `FStar.String.compare`
// (issue #347) transcribe directly -- no new trust surface, same
// reuse `RDF.Indexed.Completeness.lemma_key_order_cmp_trans_le`
// already makes for the analogous `option string` key comparator one
// module over.
//
// FRAGMENT FINDING -- numeric-with-unparseable-literal breaks
// transitivity_on (deliverable 3, second shape tried, NOT discharged;
// stop here per the brief's two-attempt-then-record-a-finding rule).
// `sparql_order`'s numeric branch (Algebra.fst:5241-5244) falls to
// `numeric_compare a b`'s own `| _, _ -> None` arm (Algebra.fst:2324)
// whenever EITHER side's literal fails to parse
// (`er_to_numeric`/`parse_to_scaled`/`parse_double_to_scaled`
// returning `None`), and `sparql_order` reads that `None` as a tie
// (`| None -> 0`, Algebra.fst:5244) regardless of WHICH side failed.
// Concrete 3-element witness, all `ER_Num`/unparseable `ER_Dec`
// sharing er_rank 4: `A = ER_Num 5`, `B = ER_Dec "not-a-number"`
// (er_to_numeric B = None), `C = ER_Num 3`.
//   sparql_order A B = 0   (numeric_compare A B = None, unparseable)
//   sparql_order B C = 0   (numeric_compare B C = None, unparseable)
//   sparql_order A C = 1   (numeric_compare A C = Some (int_compare 5 3), positive)
// `transitivity_on`'s hypothesis instance at (A,B,C) -- `f A B <= 0 /\
// f B C <= 0 ==> f A C <= 0` -- has both antecedents true (0 <= 0) and
// the consequent FALSE (1 <= 0 is false): a genuine counterexample,
// not a proof gap. `B` is a spurious "tie" bridge between two
// genuinely-ordered numerics that are NOT tied with each other. No
// fragment hypothesis short of "every compared literal parses" (which
// would need to be threaded from `SELECT`/`ORDER BY` down through
// `eval_expr_with_base`, out of scope for this landing) rescues
// `transitivity_on` here; NOT attempted further under the two-attempt
// stop rule. `totality_on` (this section's OWN hypothesis, the
// implicational form) is unaffected by this witness -- both
// directions read `None` symmetrically (`er_to_numeric` does not
// depend on argument order), so this is purely a
// `transitivity_on`-shaped gap, tracked here for whichever future
// ALL-PAIRS sortedness wave (see the transitivity_on FINDING above)
// needs a parses-cleanly fragment hypothesis for the numeric case.
// -------------------------------------------------------------------

/// FRAGMENT: same-kind IRI comparator totality (the implicational
/// strength `totality_on` needs), reusing `RDF.Indexed.StringOrder`'s
/// `string_compare_antisym` axiom directly.
let lemma_sparql_order_iri_totality (i j : wf_iri)
  : Lemma (ensures sparql_order (ER_Term (T_IRI i)) (ER_Term (T_IRI j)) >= 0 ==>
                   sparql_order (ER_Term (T_IRI j)) (ER_Term (T_IRI i)) <= 0) =
  SO.string_compare_antisym (iri_to_string i) (iri_to_string j)

/// FRAGMENT: same-kind IRI comparator transitivity (non-strict), same
/// zero/strict case split `RDF.Indexed.Completeness.
/// lemma_key_order_cmp_trans_le` uses one module over for the
/// analogous `option string` key comparator.
let lemma_sparql_order_iri_trans (i j k : wf_iri)
  : Lemma (requires sparql_order (ER_Term (T_IRI i)) (ER_Term (T_IRI j)) <= 0 /\
                    sparql_order (ER_Term (T_IRI j)) (ER_Term (T_IRI k)) <= 0)
          (ensures  sparql_order (ER_Term (T_IRI i)) (ER_Term (T_IRI k)) <= 0) =
  let si = iri_to_string i in
  let sj = iri_to_string j in
  let sk = iri_to_string k in
  SO.string_compare_zero_iff_eq si sj;
  SO.string_compare_zero_iff_eq sj sk;
  if FStar.String.compare si sj = 0 then ()
  else if FStar.String.compare sj sk = 0 then ()
  else SO.string_compare_trans si sj sk

(** ------------------------------------------------------------------ **)
(** 15.2 OFFSET / LIMIT -- `slice_solutions` is a contiguous window     **)
(** ------------------------------------------------------------------ **)

/// `list_drop`/`list_take` length -- how many rows survive.
let rec lemma_list_drop_length (#a:Type) (n:nat) (l:list a)
  : Lemma (ensures List.Tot.length (list_drop n l) ==
                   (if n >= List.Tot.length l then 0 else List.Tot.length l - n))
          (decreases l) =
  if n = 0 then ()
  else match l with
  | [] -> ()
  | _ :: tl -> lemma_list_drop_length #a (n - 1) tl

let rec lemma_list_take_length (#a:Type) (n:nat) (l:list a)
  : Lemma (ensures List.Tot.length (list_take n l) ==
                   (if n <= List.Tot.length l then n else List.Tot.length l))
          (decreases l) =
  if n = 0 then ()
  else match l with
  | [] -> ()
  | _ :: tl -> lemma_list_take_length #a (n - 1) tl

/// `list_drop`/`list_take` index -- WHICH row survives at position `i`.
let rec lemma_list_drop_index (#a:Type) (n:nat) (l:list a) (i:nat)
  : Lemma (requires i < List.Tot.length (list_drop n l))
          (ensures i + n < List.Tot.length l /\
                   List.Tot.index (list_drop n l) i == List.Tot.index l (i + n))
          (decreases l) =
  if n = 0 then ()
  else match l with
  | [] -> ()
  | _ :: tl -> lemma_list_drop_index #a (n - 1) tl i

let rec lemma_list_take_index (#a:Type) (n:nat) (l:list a) (i:nat)
  : Lemma (requires i < List.Tot.length (list_take n l))
          (ensures i < n /\ i < List.Tot.length l /\
                   List.Tot.index (list_take n l) i == List.Tot.index l i)
          (decreases l) =
  if n = 0 then ()
  else match l with
  | [] -> ()
  | _ :: tl ->
    if i = 0 then ()
    else lemma_list_take_index #a (n - 1) tl (i - 1)

/// The WINDOW statement: row `i` of `slice_solutions` is row `i +
/// offset` of the input, unconditionally in both offset and limit
/// (all four combinations of `None`/`Some`). `off_val` is the
/// effective (zero-default) offset OFFSET/LIMIT §18.4 describes.
let theorem_slice_solutions_window
      (offset : option nat) (limit : option nat) (omega : list S.smap) (i : nat)
  : Lemma (requires i < List.Tot.length (slice_solutions offset limit omega))
          (ensures
            (let off_val = (match offset with None -> 0 | Some n -> n) in
             i + off_val < List.Tot.length omega /\
             List.Tot.index (slice_solutions offset limit omega) i ==
             List.Tot.index omega (i + off_val))) =
  match offset, limit with
  | None, None -> ()
  | None, Some n -> lemma_list_take_index n omega i
  | Some k, None -> lemma_list_drop_index k omega i
  | Some k, Some n ->
    let after_offset = list_drop k omega in
    lemma_list_take_index n after_offset i;
    lemma_list_drop_index k omega i

/// The LENGTH statement: the guarded arithmetic OFFSET/LIMIT §18.4
/// describes ("Result = a slice of the sequence, of length no greater
/// than LIMIT, starting after OFFSET elements"), spelled out over
/// `nat` (guarding the offset-past-end subtraction rather than
/// truncating it).
let theorem_slice_solutions_length
      (offset : option nat) (limit : option nat) (omega : list S.smap)
  : Lemma (ensures
      (let off_val = (match offset with None -> 0 | Some n -> n) in
       let after_len =
         (if off_val >= List.Tot.length omega then 0 else List.Tot.length omega - off_val) in
       List.Tot.length (slice_solutions offset limit omega) ==
       (match limit with
        | None -> after_len
        | Some n -> (if n <= after_len then n else after_len)))) =
  match offset, limit with
  | None, None -> ()
  | None, Some n -> lemma_list_take_length n omega
  | Some k, None -> lemma_list_drop_length k omega
  | Some k, Some n ->
    lemma_list_drop_length k omega;
    lemma_list_take_length n (list_drop k omega)

(** ------------------------------------------------------------------ **)
(** 15.3 DISTINCT completeness (section 18.5) -- REDUCED is identity    **)
(** ------------------------------------------------------------------ **)

// `reduced_solutions` is literally `let reduced_solutions omega = omega`
// (SPARQL11.Algebra.fst, section 11.2). Section 18.4's REDUCED clause
// ("the returned sequence... MAY eliminate some or all duplicates")
// makes duplicate elimination OPTIONAL, so keeping every row is
// trivially conformant by that clause's own wording -- no theorem is
// stated about it because the identity function needs none: it is
// conformant for every possible input by construction, not by proof.

// `sm_equal`'s underlying `rdf_term_eq` is an equivalence relation on
// `rdf_term` (reflexive: `RDF.Term.fsti`'s `lemma_rdf_term_eq_refl`;
// symmetric and transitive: NOT proved anywhere in the tree except
// `RDF.Store.Columnar.DeltaMerge.fst`'s local `lemma_rdf_term_eq_symm`/
// `_trans`, whose own header comment says so explicitly -- grepped
// before writing these). Re-derived here rather than imported, to keep
// this module's dependency footprint to `RDF.Term`/`SPARQL11.Algebra`
// (already open) plus `SPARQL11.Algebra.Spec` (already `module S`).
let lemma_lang_tag_eq_symm (a b : string)
  : Lemma (lang_tag_eq a b == lang_tag_eq b a) = ()

let lemma_lang_tag_eq_trans (a b c : string)
  : Lemma (requires lang_tag_eq a b /\ lang_tag_eq b c) (ensures lang_tag_eq a c) = ()

let lemma_lang_tag_option_eq_symm (a b : option string)
  : Lemma (lang_tag_option_eq a b == lang_tag_option_eq b a) =
  match a, b with
  | None, None -> ()
  | Some x, Some y -> lemma_lang_tag_eq_symm x y
  | _, _ -> ()

let lemma_lang_tag_option_eq_trans (a b c : option string)
  : Lemma (requires lang_tag_option_eq a b /\ lang_tag_option_eq b c)
          (ensures lang_tag_option_eq a c) =
  match a, b, c with
  | None, None, None -> ()
  | Some x, Some y, Some z -> lemma_lang_tag_eq_trans x y z
  | _, _, _ -> ()

let lemma_literal_eq_symm (l1 l2 : literal) : Lemma (literal_eq l1 l2 == literal_eq l2 l1) =
  lemma_lang_tag_option_eq_symm l1.lang_tag l2.lang_tag

let lemma_literal_eq_trans (l1 l2 l3 : literal)
  : Lemma (requires literal_eq l1 l2 /\ literal_eq l2 l3) (ensures literal_eq l1 l3) =
  lemma_lang_tag_option_eq_trans l1.lang_tag l2.lang_tag l3.lang_tag

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

let rec lemma_rdf_term_eq_symm (a b : rdf_term)
  : Lemma (ensures rdf_term_eq a b == rdf_term_eq b a) (decreases a) =
  match a, b with
  | T_Literal l1, T_Literal l2 -> lemma_literal_eq_symm l1 l2
  | T_TripleTerm s1 _ o1, T_TripleTerm s2 _ o2 ->
    lemma_subject_eq_symm s1 s2; lemma_rdf_term_eq_symm o1 o2
  | _, _ -> ()

let rec lemma_rdf_term_eq_trans (a b c : rdf_term)
  : Lemma (requires rdf_term_eq a b /\ rdf_term_eq b c) (ensures rdf_term_eq a c) (decreases a) =
  match a, b, c with
  | T_Literal l1, T_Literal l2, T_Literal l3 -> lemma_literal_eq_trans l1 l2 l3
  | T_TripleTerm s1 _ o1, T_TripleTerm s2 _ o2, T_TripleTerm s3 _ o3 ->
    lemma_subject_eq_trans s1 s2 s3; lemma_rdf_term_eq_trans o1 o2 o3
  | _, _, _ -> ()

// `sm_equal` reflexivity, symmetry, transitivity -- the equivalence-
// relation properties `list_deduplicate_sm_acc`'s correctness needs.
// Symmetry is free (`sm_equal m1 m2 = sm_submap m1 m2 && sm_submap m2
// m1`, so swapping is `&&` commutativity). Reflexivity needs
// no-repeated-keys (RT-5-adjacent: an association list can carry a
// repeated variable, `sm_lookup` resolves it to the FIRST binding, so
// a LATER occurrence of the same key with the same or a different term
// looks unequal to itself under `sm_submap`'s own list walk -- the
// same hazard `lemma_sm_compatible_refl`, one module over in
// SPARQL11.Algebra.fst section 19.9, already needed
// `List.Tot.noRepeats (sm_domain mu)` for).
let lemma_sm_equal_symm (m1 m2 : S.smap)
  : Lemma (sm_equal m1 m2 == sm_equal m2 m1) = ()

let rec lemma_sm_submap_extra_binding (m1 m2 : S.smap) (v : string) (t : rdf_term)
  : Lemma (requires not (List.Tot.mem v (sm_domain m1)))
          (ensures sm_submap m1 ((v, t) :: m2) == sm_submap m1 m2)
          (decreases m1) =
  match m1 with
  | [] -> ()
  | (v1, t1) :: rest -> lemma_sm_submap_extra_binding rest m2 v t

let rec lemma_sm_submap_refl (mu : S.smap)
  : Lemma (requires List.Tot.noRepeats (sm_domain mu))
          (ensures sm_submap mu mu == true)
          (decreases mu) =
  match mu with
  | [] -> ()
  | (v, t) :: rest ->
    lemma_rdf_term_eq_refl t;
    lemma_sm_submap_extra_binding rest rest v t;
    lemma_sm_submap_refl rest

let lemma_sm_equal_refl (mu : S.smap)
  : Lemma (requires List.Tot.noRepeats (sm_domain mu))
          (ensures sm_equal mu mu == true) =
  lemma_sm_submap_refl mu

let rec lemma_sm_submap_lookup (m1 m2 : S.smap) (v : string)
  : Lemma (requires sm_submap m1 m2 == true)
          (ensures (match sm_lookup v m1 with
                    | None -> True
                    | Some t -> (exists t'. sm_lookup v m2 == Some t' /\ rdf_term_eq t t' == true)))
          (decreases m1) =
  match m1 with
  | [] -> ()
  | (v1, t1) :: rest -> if v = v1 then () else lemma_sm_submap_lookup rest m2 v

let rec lemma_sm_submap_trans (m1 m2 m3 : S.smap)
  : Lemma (requires sm_submap m1 m2 == true /\ sm_submap m2 m3 == true)
          (ensures sm_submap m1 m3 == true)
          (decreases m1) =
  match m1 with
  | [] -> ()
  | (v, t) :: rest ->
    lemma_sm_submap_trans rest m2 m3;
    (match sm_lookup v m2 with
     | Some t2 ->
       lemma_sm_submap_lookup m2 m3 v;
       eliminate exists (t3 : rdf_term). sm_lookup v m3 == Some t3 /\ rdf_term_eq t2 t3 == true
       returns sm_submap m1 m3 == true
       with _ . lemma_rdf_term_eq_trans t t2 t3
     | None -> ())

let lemma_sm_equal_trans (m1 m2 m3 : S.smap)
  : Lemma (requires sm_equal m1 m2 == true /\ sm_equal m2 m3 == true)
          (ensures sm_equal m1 m3 == true) =
  lemma_sm_submap_trans m1 m2 m3;
  lemma_sm_submap_trans m3 m2 m1

/// `sm_mem mu l` gives a witness in `l` equal to `mu`.
let rec lemma_sm_mem_witness (mu : S.smap) (l : list S.smap)
  : Lemma (requires sm_mem mu l == true)
          (ensures exists (y : S.smap). List.Tot.memP y l /\ sm_equal mu y == true)
          (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> if sm_equal mu hd then () else lemma_sm_mem_witness mu tl

/// `list_deduplicate_sm_acc` is independent of its accumulator up to
/// append: growing/shrinking `acc` never changes what the walk over
/// `l` itself decides to keep, it only changes what that decision gets
/// appended onto. This decouples the completeness induction below from
/// having to track an evolving accumulator directly.
let rec lemma_dedup_acc_append (l acc : list S.smap)
  : Lemma (ensures list_deduplicate_sm_acc l acc ==
                   List.Tot.append (list_deduplicate_sm_acc l []) acc)
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs ->
    if sm_mem x xs then
      lemma_dedup_acc_append xs acc
    else begin
      lemma_dedup_acc_append xs (x :: acc);
      lemma_dedup_acc_append xs [x];
      List.Tot.append_assoc (list_deduplicate_sm_acc xs []) [x] acc
    end

/// COMPLETENESS: every solution mapping in the input has an `sm_equal`
/// representative in `distinct_solutions`' output -- nothing is lost,
/// only merged with its equivalence class (the SR-1-repaired
/// `sm_equal`, order-insensitive per section 18.3). The
/// no-repeated-keys hypothesis on every mapping in `omega` is the
/// well-formedness invariant `sm_equal` reflexivity needs (see the
/// comment above `lemma_sm_equal_symm`); it is the same invariant
/// `theorem_sm_compatible_sound`'s neighbourhood already carries for
/// this file's other engine-level equality reasoning.
let rec lemma_dedup_core_complete (l : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu l /\
                    (forall (m : S.smap).
                       List.Tot.memP m l ==> List.Tot.noRepeats (sm_domain m)))
          (ensures exists (mu' : S.smap).
                     List.Tot.memP mu' (list_deduplicate_sm_acc l []) /\ sm_equal mu mu' == true)
          (decreases l) =
  match l with
  | [] -> ()
  | x :: xs ->
    eliminate (mu == x) \/ (List.Tot.memP mu xs)
    returns exists (mu' : S.smap).
              List.Tot.memP mu' (list_deduplicate_sm_acc l []) /\ sm_equal mu mu' == true
    with _ . begin
      if sm_mem x xs then begin
        lemma_sm_mem_witness x xs;
        eliminate exists (y : S.smap). List.Tot.memP y xs /\ sm_equal x y == true
        returns exists (mu' : S.smap).
                  List.Tot.memP mu' (list_deduplicate_sm_acc l []) /\ sm_equal mu mu' == true
        with _ . begin
          lemma_dedup_core_complete xs y;
          eliminate exists (mu' : S.smap).
              List.Tot.memP mu' (list_deduplicate_sm_acc xs []) /\ sm_equal y mu' == true
          returns exists (mu'' : S.smap).
              List.Tot.memP mu'' (list_deduplicate_sm_acc l []) /\ sm_equal mu mu'' == true
          with _ . lemma_sm_equal_trans x y mu'
        end
      end else begin
        lemma_sm_equal_refl x;
        lemma_dedup_acc_append xs [x];
        List.Tot.append_memP (list_deduplicate_sm_acc xs []) [x] x
      end
    end
    and _ . begin
      lemma_dedup_core_complete xs mu;
      eliminate exists (mu' : S.smap).
          List.Tot.memP mu' (list_deduplicate_sm_acc xs []) /\ sm_equal mu mu' == true
      returns exists (mu'' : S.smap).
          List.Tot.memP mu'' (list_deduplicate_sm_acc l []) /\ sm_equal mu mu'' == true
      with _ . begin
        if sm_mem x xs then ()
        else begin
          lemma_dedup_acc_append xs [x];
          List.Tot.append_memP (list_deduplicate_sm_acc xs []) [x] mu'
        end
      end
    end

let theorem_distinct_complete (omega : list S.smap) (mu : S.smap)
  : Lemma (requires List.Tot.memP mu omega /\
                    (forall (m : S.smap).
                       List.Tot.memP m omega ==> List.Tot.noRepeats (sm_domain m)))
          (ensures exists (mu' : S.smap).
                     List.Tot.memP mu' (distinct_solutions omega) /\ sm_equal mu mu' == true) =
  lemma_dedup_core_complete omega mu;
  eliminate exists (mu' : S.smap).
      List.Tot.memP mu' (list_deduplicate_sm_acc omega []) /\ sm_equal mu mu' == true
  returns exists (mu'' : S.smap).
      List.Tot.memP mu'' (distinct_solutions omega) /\ sm_equal mu mu'' == true
  with _ . FStar.List.Tot.Properties.rev_memP (list_deduplicate_sm_acc omega []) mu'

(** ------------------------------------------------------------------ **)
(** 15.4 FINDING SR-3: distinct_card_spec does NOT hold of              **)
(** distinct_solutions -- the same rdf_term_eq/term_id_eqb gap as SR-1/ **)
(** SR-2, now on the CARDINALITY clause DISTINCT keeping its fix did    **)
(** not touch                                                          **)
(** ------------------------------------------------------------------ **)

// `distinct_card_spec omega res` (Spec.fst:773) is `forall mu. mult mu
// res == (if mult mu omega > 0 then 1 else 0)`, and `mult` is counted
// via `S.smap_eqb`, i.e. `term_id_eqb` -- EXACT structural term
// identity (Spec.fst's `lit_id_eqb`: lexical form, datatype, lang tag
// AND CASE, direction, all compared verbatim). `distinct_solutions`
// dedups via `sm_equal`, i.e. `rdf_term_eq` -- coarser: it folds
// language-tag CASE (`lang_tag_eq`, RDF.Term.fsti) and XMLLiteral
// canonical form. Two well-formed literals `rdf_term_eq` accepts as
// equal but `term_id_eqb` does not (`"Alice"@en` vs `"Alice"@EN`) are
// exactly `OWL.RL.Refinement.fst`'s `key_lit_en`/`key_lit_EN` crux,
// reused here for the same reason it was built there: a genuine
// `wf_literal` pair a real graph can carry, differing only in lang-tag
// case.
//
// Consequence: `distinct_solutions [dc_mu1; dc_mu2]` (dc_mu1, dc_mu2
// binding the same variable to those two literals) DEDUPS them into
// one representative (`sm_equal dc_mu1 dc_mu2 == true`, SR-1's fixed
// keep-the-last semantics keeps `dc_mu2`). But `S.mult dc_mu1 [dc_mu2]
// == 0` -- `term_id_eqb`, unlike `rdf_term_eq`, does NOT identify
// `"Alice"@en` with `"Alice"@EN`. `distinct_card_spec` requires
// `mult dc_mu1 res == 1` whenever `mult dc_mu1 omega > 0` (true here:
// `dc_mu1` matches itself), so the specification's forall instantiated
// at `dc_mu1` demands `1`, and the engine delivers `0`. FALSE --
// proved below with the explicit witness, not merely left unproved.
// This is SR-1/SR-2's root cause (rdf_term_eq vs term identity, the
// #324 dispute; see this file's Part 1) surfacing a THIRD time, on the
// one clause of DISTINCT the SR-1 mutual-submap fix did not reach: the
// fix corrected which rows survive relative to the SET semantics, not
// which count formula the BAG semantics is being checked against.

let dc_lit_en : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "Alice"; datatype = rdf_lang_string;
                             lang_tag = Some "en"; direction = None } <: literal));
  { lexical_form = "Alice"; datatype = rdf_lang_string;
    lang_tag = Some "en"; direction = None }

let dc_lit_EN : wf_literal =
  assert_norm (literal_wf ({ lexical_form = "Alice"; datatype = rdf_lang_string;
                             lang_tag = Some "EN"; direction = None } <: literal));
  { lexical_form = "Alice"; datatype = rdf_lang_string;
    lang_tag = Some "EN"; direction = None }

let dc_mu1 : S.smap = [("name", T_Literal dc_lit_en)]
let dc_mu2 : S.smap = [("name", T_Literal dc_lit_EN)]

let lemma_dc_witness_rdf_term_eq ()
  : Lemma (rdf_term_eq (T_Literal dc_lit_en) (T_Literal dc_lit_EN) == true) =
  assert_norm (rdf_term_eq (T_Literal dc_lit_en) (T_Literal dc_lit_EN) == true)

let lemma_dc_witness_term_id_eqb_false ()
  : Lemma (S.term_id_eqb (T_Literal dc_lit_en) (T_Literal dc_lit_EN) == false) =
  assert_norm (S.term_id_eqb (T_Literal dc_lit_en) (T_Literal dc_lit_EN) == false)

let lemma_dc_distinct_dedups ()
  : Lemma (distinct_solutions [dc_mu1; dc_mu2] == [dc_mu2]) =
  lemma_dc_witness_rdf_term_eq ();
  assert_norm (sm_equal dc_mu1 dc_mu2 == true);
  assert_norm (distinct_solutions [dc_mu1; dc_mu2] == [dc_mu2])

let lemma_dc_mult_witness_omega ()
  : Lemma (S.mult dc_mu1 [dc_mu1; dc_mu2] == 1) =
  lemma_dc_witness_term_id_eqb_false ();
  assert_norm (S.mult dc_mu1 [dc_mu1; dc_mu2] == 1)

let lemma_dc_mult_witness_res ()
  : Lemma (S.mult dc_mu1 [dc_mu2] == 0) =
  lemma_dc_witness_term_id_eqb_false ();
  assert_norm (S.mult dc_mu1 [dc_mu2] == 0)

/// FINDING SR-3, machine-checked: `distinct_card_spec` is FALSE of
/// `distinct_solutions` on this witness. `theorem_distinct_card` (the
/// unconditional statement the brief for this file's fourth theorem
/// names) is therefore not stated -- this is its refutation, in the
/// style Part 6/9 already use for SR-1/SR-2 (a positive theorem is not
/// weakened to paper over a false claim; the false claim is proved
/// false instead).
let theorem_sr3_distinct_card_spec_false ()
  : Lemma (~ (S.distinct_card_spec [dc_mu1; dc_mu2] (distinct_solutions [dc_mu1; dc_mu2]))) =
  lemma_dc_distinct_dedups ();
  lemma_dc_mult_witness_omega ();
  lemma_dc_mult_witness_res ()

#pop-options
