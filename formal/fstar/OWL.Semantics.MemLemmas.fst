module OWL.Semantics.MemLemmas

// Membership-preservation infrastructure for the OWL RL soundness
// proofs (OWL.Semantics.Soundness.fst). Everything here is a Lemma
// about SHIPPING functions — List.Tot.sortWith / partition (the F*
// stdlib functions the closure path calls), RDF.Graph's dedup
// helpers, RDF.Indexed's bucket_tree construction, and OWL.Closure's
// pair-dedup helpers. No new executable code, no admits, no --lax.
//
// The load-bearing results:
//   * fold_left_inv          — the one generic induction every rule
//                              soundness proof instantiates (twice,
//                              usually: once for a collection fold,
//                              once for the emission fold).
//   * lemma_bucket_lookup_ok — anything served from a build_bucket
//                              tree is a member of the source list
//                              AND carries the key it was filed
//                              under.
//   * lemma_build_indexed_wf_pred / _wf_sp_weak — instantiations for
//                              the two buckets the pilot rules read.
//
// Design doc: docs/designissues/2026-07-29-rdf-based-semantics-
// formalization.md (section "Discharging the index hypotheses").
//
// 2026-08-05 (index-completeness push, docs/claude-rules/rdf-rdfs-
// semantics-coverage.md gap #2): `lemma_sortWith_memP_rev` below lands
// (the converse of `lemma_sortWith_memP` -- sortWith drops nothing
// either). At the time this landed, the FULL index-completeness lemma
// (every triple with predicate p IS filed in `bucket_lookup ig.ig_pred
// p`) was BLOCKED, not merely hard: `bucket_tree`'s midpoint-bisection
// build (`sorted_list_to_tree` in RDF.Indexed.fsti) places pairs by
// LIST POSITION, while `bucket_lookup` navigates by KEY COMPARISON
// (`String.compare k k' < 0`), and `FStar.String.fsti`'s `compare`
// carried ZERO stated axioms (no reflexivity/antisymmetry/
// transitivity/totality) -- confirmed empirically: a bare transitivity
// lemma for `cmp = String.compare` failed with "Could not prove
// post-condition" given nothing but the type `string -> string -> Tot
// int`. The "ATTEMPT" comment block above `lemma_build_bucket_ok`
// records the two attempts made under that wall (direct proof;
// tree_ok-style reformulation).
//
// RESOLVED same day: RDF.Indexed.StringOrder.fsti added exactly three
// interface axioms about `FStar.String.compare` (compare-zero-iff-eq,
// antisymmetry, transitivity), tracked under issue #347. The full
// completeness lemma is proved in RDF.Indexed.Completeness.fst
// (`lemma_build_indexed_complete_pred`, generic underneath as
// `lemma_build_bucket_complete` so sp/subj/obj/po/so can reuse the
// same machinery) using those three axioms -- see that module's own
// banner for the proof shape (sortedness of sortWith's output, carried
// through grouping, then through the tree bisection).

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed

// ===================================================================
// The generic fold_left invariant lemma.
// ===================================================================

// If inv holds of the seed and every step on an element of l
// preserves inv, then inv holds of the fold. The step hypothesis is
// a prop-level forall so callers can establish it once with an
// `introduce forall` block and reuse it down the induction.
let rec fold_left_inv (#a #b : Type) (inv : a -> prop) (f : a -> b -> a) (l : list b) (acc : a)
  : Lemma
    (requires inv acc /\
              (forall (x : a) (y : b). (List.Tot.memP y l /\ inv x) ==> inv (f x y)))
    (ensures inv (List.Tot.fold_left f acc l))
    (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> fold_left_inv inv f tl (f acc hd)

// ===================================================================
// memP preservation through partition / sortWith / rev / dedup.
// The stdlib's own lemmas (partition_mem_forall, sortWith_permutation)
// require eqtype; triple is noeq, so we need memP versions.
// ===================================================================

let rec lemma_partition_memP (#a : Type) (f : a -> Tot bool) (l : list a) (x : a)
  : Lemma
    (ensures (List.Tot.memP x l <==>
              (List.Tot.memP x (fst (List.Tot.partition f l)) \/
               List.Tot.memP x (snd (List.Tot.partition f l)))))
    (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> lemma_partition_memP f tl x

let rec lemma_sortWith_memP (#a : Type) (f : a -> a -> Tot int) (l : list a) (x : a)
  : Lemma
    (ensures List.Tot.memP x (List.Tot.sortWith f l) ==> List.Tot.memP x l)
    (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare f pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare f pivot) tl;
    lemma_sortWith_memP f lo x;
    lemma_sortWith_memP f hi x;
    lemma_partition_memP (List.Tot.bool_of_compare f pivot) tl x;
    List.Tot.append_memP (List.Tot.sortWith f lo) (pivot :: List.Tot.sortWith f hi) x

let lemma_sortWith_memP_forall (#a : Type) (f : a -> a -> Tot int) (l : list a)
  : Lemma
    (ensures forall (x : a). List.Tot.memP x (List.Tot.sortWith f l) ==> List.Tot.memP x l) =
  FStar.Classical.forall_intro (lemma_sortWith_memP f l)

// Converse direction of lemma_sortWith_memP: sortWith is a PERMUTATION, so
// nothing is dropped either. The stdlib's own permutation lemma
// (`sortWith_permutation`) needs `#a:eqtype` (it goes through `count`);
// `triple` (and the `(option string * triple)` decorated pairs `build_bucket`
// sorts) are `noeq`, so we re-derive the converse memP fact by the same
// partition/append induction `lemma_sortWith_memP` already uses, just read
// the other way. Needed by `lemma_build_indexed_complete_pred`'s "membership
// preservation INTO build_bucket's group-by" step (2026-08-05 index-
// completeness push, docs/claude-rules/rdf-rdfs-semantics-coverage.md gap 2).
let rec lemma_sortWith_memP_rev (#a : Type) (f : a -> a -> Tot int) (l : list a) (x : a)
  : Lemma
    (ensures List.Tot.memP x l ==> List.Tot.memP x (List.Tot.sortWith f l))
    (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare f pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare f pivot) tl;
    lemma_sortWith_memP_rev f lo x;
    lemma_sortWith_memP_rev f hi x;
    lemma_partition_memP (List.Tot.bool_of_compare f pivot) tl x;
    List.Tot.append_memP (List.Tot.sortWith f lo) (pivot :: List.Tot.sortWith f hi) x

let lemma_sortWith_memP_rev_forall (#a : Type) (f : a -> a -> Tot int) (l : list a)
  : Lemma
    (ensures forall (x : a). List.Tot.memP x l ==> List.Tot.memP x (List.Tot.sortWith f l)) =
  FStar.Classical.forall_intro (lemma_sortWith_memP_rev f l)

let lemma_rev_memP_forall (#a : Type) (l : list a)
  : Lemma (ensures forall (x : a). List.Tot.memP x (List.Tot.rev l) <==> List.Tot.memP x l) =
  FStar.Classical.forall_intro (List.Tot.rev_memP l)

// ===================================================================
// bucket_tree well-formedness: everything filed in the tree came
// from the source list and is filed under its own key.
// ===================================================================

let rec tree_ok (#a : Type) (key_of : a -> option string) (src : list a) (m : bucket_tree a)
  : Tot prop (decreases m) =
  match m with
  | BLeaf -> True
  | BNode k v l r ->
    (forall (t : a). List.Tot.memP t v ==> (List.Tot.memP t src /\ key_of t == Some k)) /\
    tree_ok key_of src l /\ tree_ok key_of src r

let rec lemma_tree_ok_lookup (#a : Type) (key_of : a -> option string) (src : list a)
    (m : bucket_tree a) (k : string) (t : a)
  : Lemma
    (requires tree_ok key_of src m /\ List.Tot.memP t (bucket_lookup m k))
    (ensures List.Tot.memP t src /\ key_of t == Some k)
    (decreases m) =
  match m with
  | BLeaf -> ()
  | BNode k' _ l r ->
    if k = k' then ()
    else if FStar.String.compare k k' < 0 then lemma_tree_ok_lookup key_of src l k t
    else lemma_tree_ok_lookup key_of src r k t

// The (key, elements) pair-list analogue of tree_ok, for the
// intermediate stages of build_bucket.
let pairs_ok (#a : Type) (key_of : a -> option string) (src : list a)
    (xs : list (string * list a)) : prop =
  forall (kb : string * list a). List.Tot.memP kb xs ==>
    (forall (t : a). List.Tot.memP t (snd kb) ==>
       (List.Tot.memP t src /\ key_of t == Some (fst kb)))

// take_prefix splits a list; both halves stay inside the input.
let rec lemma_take_prefix_acc_memP (#a : Type) (n : nat) (acc xs : list a) (x : a)
  : Lemma
    (ensures (let (pre, suf) = take_prefix_acc n acc xs in
              (List.Tot.memP x pre \/ List.Tot.memP x suf) ==>
              (List.Tot.memP x xs \/ List.Tot.memP x acc)))
    (decreases xs) =
  if n = 0 then List.Tot.rev_memP acc x
  else match xs with
       | [] -> List.Tot.rev_memP acc x
       | hd :: tl -> lemma_take_prefix_acc_memP (n - 1) (hd :: acc) tl x

let lemma_take_prefix_memP_forall (#a : Type) (n : nat) (xs : list a)
  : Lemma
    (ensures (let (pre, suf) = take_prefix n xs in
              forall (x : a). (List.Tot.memP x pre \/ List.Tot.memP x suf) ==>
                         List.Tot.memP x xs)) =
  FStar.Classical.forall_intro (lemma_take_prefix_acc_memP n [] xs)

// The midpoint-bisection tree builder preserves pairs_ok into tree_ok.
let rec lemma_slt_tree_ok (#a : Type) (key_of : a -> option string) (src : list a)
    (xs : list (string * list a)) (fuel : nat)
  : Lemma
    (requires pairs_ok key_of src xs)
    (ensures tree_ok key_of src (sorted_list_to_tree_fuel xs fuel))
    (decreases fuel) =
  match xs with
  | [] -> ()
  | _ ->
    if fuel = 0 then ()
    else begin
      let n = List.Tot.length xs in
      let mid = n / 2 in
      let (left_xs, rest) = take_prefix mid xs in
      lemma_take_prefix_memP_forall mid xs;
      match rest with
      | _ :: right_xs ->
        lemma_slt_tree_ok key_of src left_xs (fuel - 1);
        lemma_slt_tree_ok key_of src right_xs (fuel - 1)
      | [] -> ()
    end

// Decorated pairs: each (k, t) with k == key_of t, t from the source.
let dec_ok (#a : Type) (key_of : a -> option string) (src : list a)
    (ts : list (option string * a)) : prop =
  forall (kt : option string * a). List.Tot.memP kt ts ==>
    (fst kt == key_of (snd kt) /\ List.Tot.memP (snd kt) src)

let rec lemma_decorated_ok (#a : Type) (key_of : a -> option string) (src ts : list a)
  : Lemma
    (requires forall (t : a). List.Tot.memP t ts ==> List.Tot.memP t src)
    (ensures dec_ok key_of src (List.Tot.map (fun (t : a) -> (key_of t, t)) ts))
    (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: tl -> lemma_decorated_ok key_of src tl

// The grouping pass turns dec_ok input into pairs_ok output.
let rec lemma_group_ok (#a : Type) (key_of : a -> option string) (src : list a)
    (ts : list (option string * a)) (cur_key : option string) (cur_bucket : list a)
    (acc : list (string * list a))
  : Lemma
    (requires dec_ok key_of src ts /\
              (forall (t : a). List.Tot.memP t cur_bucket ==>
                 (List.Tot.memP t src /\ Some? cur_key /\ key_of t == cur_key)) /\
              pairs_ok key_of src acc)
    (ensures pairs_ok key_of src (group_sorted_decorated_aux ts cur_key cur_bucket acc))
    (decreases ts) =
  match ts with
  | [] -> ()
  | (k, t) :: rest ->
    (match k with
     | None -> lemma_group_ok key_of src rest cur_key cur_bucket acc
     | Some kk ->
       // Fire the dec_ok quantifier at the head pair explicitly: the
       // recursive calls file t under kk, so we need its key fact.
       assert (List.Tot.memP (k, t) ts);
       assert (fst #(option string) #a (k, t) == key_of (snd #(option string) #a (k, t)));
       assert (key_of t == Some kk);
       assert (List.Tot.memP t src);
       (match cur_key with
        | Some k0 ->
          if kk = k0 then lemma_group_ok key_of src rest cur_key (t :: cur_bucket) acc
          else lemma_group_ok key_of src rest (Some kk) [t] ((k0, cur_bucket) :: acc)
        | None -> lemma_group_ok key_of src rest (Some kk) [t] acc))

// pairs_ok survives List.Tot.rev (element-wise property).
let lemma_pairs_ok_rev (#a : Type) (key_of : a -> option string) (src : list a)
    (xs : list (string * list a))
  : Lemma
    (requires pairs_ok key_of src xs)
    (ensures pairs_ok key_of src (List.Tot.rev xs)) =
  lemma_rev_memP_forall xs

// ATTEMPT (index-completeness push, gap #2): does the midpoint-bisection
// tree-builder serve every (key,elements) pair it is handed, with ZERO
// extra hypotheses? This is the "real work" step the task brief flagged.
// Expect this NOT to go through: `sorted_list_to_tree_fuel` places pairs by
// LIST POSITION (`take_prefix mid xs`, oblivious to key values), while
// `bucket_lookup` navigates by KEY COMPARISON (`String.compare k k' < 0`).
// The two only agree if `xs` is actually ordered by that same comparison
// -- and FStar.String.fsti's `compare` carries ZERO stated axioms (no
// reflexivity/antisymmetry/transitivity/totality; confirmed with a scratch
// probe, not kept in-tree: `Lemma (requires cmp a b<0 /\ cmp b c<0)
// (ensures cmp a c<0)` for `cmp = String.compare` FAILS with "Could not
// prove post-condition" given nothing but the type `string -> string ->
// Tot int`). Left in place (commented statement) as the recorded first
// attempt for the two-attempt stop rule.
//
// let rec lemma_slt_lookup_complete (#a : Type) (xs : list (string * list a))
//     (fuel : nat) (k : string) (v : list a) (t : a)
//   : Lemma
//     (requires List.Tot.memP (k, v) xs /\ List.Tot.memP t v /\
//               fuel >= List.Tot.length xs)
//     (ensures List.Tot.memP t (bucket_lookup (sorted_list_to_tree_fuel xs fuel) k))
//     (decreases fuel) =
//   match xs with
//   | [] -> ()
//   | _ ->
//     if fuel = 0 then ()
//     else
//       let n = List.Tot.length xs in
//       let mid = n / 2 in
//       let (left_xs, rest) = take_prefix mid xs in
//       lemma_take_prefix_memP_forall mid xs;   // gives memP (k,v) left_xs \/ memP (k,v) rest -- an OR, not knowing which
//       match rest with
//       | (k', v') :: right_xs ->
//         if k = k' then ()                      // k=k' doesn't give v==v' without a no-duplicate-keys fact
//         else if FStar.String.compare k k' < 0 then
//           lemma_slt_lookup_complete left_xs (fuel - 1) k v t   // requires memP (k,v) left_xs -- UNPROVABLE: nothing ties the
//                                                                 // comparison direction to which half take_prefix put (k,v) in
//         else
//           lemma_slt_lookup_complete right_xs (fuel - 1) k v t  // symmetric problem
//       | [] -> ()

// The headline build_bucket result: the tree is well-formed w.r.t.
// its own source list and key function.
let lemma_build_bucket_ok (#a : Type) (key_of : a -> option string) (ts : list a)
  : Lemma (ensures tree_ok key_of ts (build_bucket key_of ts)) =
  let decorated = List.Tot.map (fun (t : a) -> (key_of t, t)) ts in
  let sorted = List.Tot.sortWith cmp_by_decorated_key decorated in
  let grouped = group_sorted_decorated_aux sorted None [] [] in
  let ascending = List.Tot.rev grouped in
  lemma_decorated_ok key_of ts ts;
  lemma_sortWith_memP_forall cmp_by_decorated_key decorated;
  assert (dec_ok key_of ts sorted);
  lemma_group_ok key_of ts sorted None [] [];
  lemma_pairs_ok_rev key_of ts grouped;
  lemma_slt_tree_ok key_of ts ascending (List.Tot.length ascending)

// ===================================================================
// Instantiations for build_indexed's buckets.
// ===================================================================

// The predicate bucket: served triples are graph members with
// exactly the queried predicate. This is the FULL well-formedness
// the soundness proofs need for ig_pred, because that bucket's key
// IS the predicate (bucket_key_pred t = Some t.p — no composite-key
// decomposition involved).
let lemma_build_indexed_wf_pred (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_pred k) ==>
                (List.Tot.memP t ig.ig_triples /\ t.p == k))) =
  let ig = build_indexed g in
  lemma_build_bucket_ok bucket_key_pred g;
  assert (ig.ig_pred == build_bucket bucket_key_pred g);
  introduce forall (k : string) (t : triple).
      List.Tot.memP t (bucket_lookup ig.ig_pred k) ==>
      (List.Tot.memP t ig.ig_triples /\ t.p == k)
  with introduce List.Tot.memP t (bucket_lookup ig.ig_pred k) ==>
                 (List.Tot.memP t ig.ig_triples /\ t.p == k)
  with _ . lemma_tree_ok_lookup bucket_key_pred g ig.ig_pred k t

// The subject bucket: served triples are graph members whose own key
// equals the queried key. Weak form only, like ig_sp's below; the
// STRONG form (the subject recovered) lives in
// RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_subj, where
// subject_to_key injectivity needs no side condition at all.
let lemma_build_indexed_wf_subj_weak (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_subj k) ==>
                (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_subj t))) =
  let ig = build_indexed g in
  lemma_build_bucket_ok bucket_key_subj g;
  assert (ig.ig_subj == build_bucket bucket_key_subj g);
  introduce forall (k : string) (t : triple).
      List.Tot.memP t (bucket_lookup ig.ig_subj k) ==>
      (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_subj t)
  with introduce List.Tot.memP t (bucket_lookup ig.ig_subj k) ==>
                 (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_subj t)
  with _ . lemma_tree_ok_lookup bucket_key_subj g ig.ig_subj k t

// The object bucket: served triples are graph members whose own key
// equals the queried key. Weak form only; the STRONG form (the term
// recovered) lives in
// RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_obj, where
// term_to_key_opt injectivity (mirroring subject_to_key's, once
// term_to_key_opt is built with `^` -- RDF.Indexed.fsti) needs no
// separator side condition either.
let lemma_build_indexed_wf_obj_weak (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_obj k) ==>
                (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_obj t))) =
  let ig = build_indexed g in
  lemma_build_bucket_ok bucket_key_obj g;
  assert (ig.ig_obj == build_bucket bucket_key_obj g);
  introduce forall (k : string) (t : triple).
      List.Tot.memP t (bucket_lookup ig.ig_obj k) ==>
      (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_obj t)
  with introduce List.Tot.memP t (bucket_lookup ig.ig_obj k) ==>
                 (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_obj t)
  with _ . lemma_tree_ok_lookup bucket_key_obj g ig.ig_obj k t

// The subject-predicate bucket: served triples are graph members
// whose OWN composite key equals the queried key. NOTE this is the
// WEAK form: recovering the components (t.s == s /\ t.p == p from
// sp_key t.s t.p == sp_key s p) needs sp_key injectivity, which in
// turn needs "U+001F never occurs in a blank-node label" — a
// representation invariant nothing in the tree currently enforces.
// See the design doc, finding F1. [Since 2026-08-04 the injectivity
// IS proved for separator-free keys and the strong form discharged:
// RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_sp.]
let lemma_build_indexed_wf_sp_weak (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_sp k) ==>
                (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_sp t))) =
  let ig = build_indexed g in
  lemma_build_bucket_ok bucket_key_sp g;
  assert (ig.ig_sp == build_bucket bucket_key_sp g);
  introduce forall (k : string) (t : triple).
      List.Tot.memP t (bucket_lookup ig.ig_sp k) ==>
      (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_sp t)
  with introduce List.Tot.memP t (bucket_lookup ig.ig_sp k) ==>
                 (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_sp t)
  with _ . lemma_tree_ok_lookup bucket_key_sp g ig.ig_sp k t

// The predicate-object bucket: served triples are graph members whose
// own composite key equals the queried key. Weak form only, same
// shape as ig_sp's above; the STRONG form (predicate and object
// recovered) lives in
// RDF.Indexed.KeyInjectivity.lemma_build_indexed_wf_po, needing the
// same one-sided separator-freeness side condition sp_key's discharge
// does (po_key is a composite key too).
let lemma_build_indexed_wf_po_weak (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (k : string) (t : triple).
                List.Tot.memP t (bucket_lookup ig.ig_po k) ==>
                (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_po t))) =
  let ig = build_indexed g in
  lemma_build_bucket_ok bucket_key_po g;
  assert (ig.ig_po == build_bucket bucket_key_po g);
  introduce forall (k : string) (t : triple).
      List.Tot.memP t (bucket_lookup ig.ig_po k) ==>
      (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_po t)
  with introduce List.Tot.memP t (bucket_lookup ig.ig_po k) ==>
                 (List.Tot.memP t ig.ig_triples /\ Some k == bucket_key_po t)
  with _ . lemma_tree_ok_lookup bucket_key_po g ig.ig_po k t
