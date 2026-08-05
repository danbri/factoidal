module RDF.Indexed.Completeness

// Index COMPLETENESS (coverage gap 2, docs/claude-rules/rdf-rdfs-
// semantics-coverage.md): every triple of g whose predicate is p IS
// served by `bucket_lookup ig.ig_pred` under p's key, for
// `ig = build_indexed g`. Generic over `key_of` (RDF.Indexed's
// `build_bucket` parameter) so sp/subj/obj/po/so can reuse the same
// machinery by instantiating key_of, per the task brief.
//
// 2026-08-05. Unblocked by RDF.Indexed.StringOrder.fsti (three
// interface axioms about FStar.String.compare -- compare-zero-iff-eq,
// antisymmetry, transitivity -- tracked under issue #347).
// OWL.Semantics.MemLemmas's 2026-08-05 banner recorded the completeness
// direction as BLOCKED pending exactly those three facts; see that
// module's history for the two recorded first attempts (a direct
// proof and a tree_ok-style reformulation, both walled off by
// FStar.String.compare carrying zero stated axioms). This module
// discharges the completeness direction using the three axioms.
//
// PROOF SHAPE:
//   Stage 1 -- order facts (zero-iff-eq / antisym / transitivity) on
//     an option-string key comparator, lifted from the three axioms.
//   Stage 2 -- `sorted_pairs`: the ALL-PAIRS (not merely adjacent)
//     sortedness invariant over decorated (option string * a) pairs,
//     proved for List.Tot.sortWith's own quicksort recursion. This is
//     the one place transitivity is load-bearing: combining an
//     lo-element and an hi-element's relation to EACH OTHER goes
//     through the pivot (x <= pivot <= y ==> x <= y).
//   Stage 3 -- group_sorted_decorated_aux carries sorted_pairs into
//     (a) an EXISTENCE fact for its output (order-free: every element
//     ends up in SOME group for its key) and (b) a STRICT kv-level
//     sortedness fact for the closed groups (distinct keys only,
//     since grouping collapses same-key runs into one binding).
//   Stage 4 -- sorted_list_to_tree_fuel's midpoint bisection, given
//     kv-level strict sortedness, serves every element under its own
//     key: the direction the commented-out ATTEMPT block in
//     OWL.Semantics.MemLemmas.fst could not close.
//   Stage 5 -- compose 1-4 into `lemma_build_bucket_complete` (generic
//     key_of), then instantiate at bucket_key_pred for the pinned
//     statement `lemma_build_indexed_complete_pred`.

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDF.Indexed.StringOrder
open OWL.Semantics.MemLemmas

// ===================================================================
// Stage 1: order facts on an option-string key comparator, lifted
// from the three StringOrder axioms. Stated directly on
// `option string` (not on decorated pairs) because Stage 3's grouping
// invariant needs to compare `cur_key` -- an accumulator with no
// paired element -- against the keys of pending pairs.
// ===================================================================

let key_order_cmp (k1 k2 : option string) : int =
  match k1, k2 with
  | None, None       -> 0
  | None, Some _     -> -1
  | Some _, None     -> 1
  | Some a, Some b   -> FStar.String.compare a b

let lemma_key_order_cmp_zero_iff_eq (k1 k2 : option string)
  : Lemma (ensures key_order_cmp k1 k2 = 0 <==> k1 == k2) =
  match k1, k2 with
  | Some a, Some b -> string_compare_zero_iff_eq a b
  | _, _ -> ()

let lemma_key_order_cmp_antisym (k1 k2 : option string)
  : Lemma (ensures key_order_cmp k1 k2 < 0 <==> key_order_cmp k2 k1 > 0) =
  match k1, k2 with
  | Some a, Some b -> string_compare_antisym a b
  | _, _ -> ()

let lemma_key_order_cmp_trans (k1 k2 k3 : option string)
  : Lemma
    (requires key_order_cmp k1 k2 < 0 /\ key_order_cmp k2 k3 < 0)
    (ensures key_order_cmp k1 k3 < 0) =
  match k1, k2, k3 with
  | Some a, Some b, Some c -> string_compare_trans a b c
  | _, _, _ -> ()

// Non-strict transitivity: the one derived fact the sortWith merge
// step needs, case-split on whether either leg of the chain is an
// equality (via zero_iff_eq) or a strict step (via the raw axiom).
let lemma_key_order_cmp_trans_le (k1 k2 k3 : option string)
  : Lemma
    (requires key_order_cmp k1 k2 <= 0 /\ key_order_cmp k2 k3 <= 0)
    (ensures key_order_cmp k1 k3 <= 0) =
  lemma_key_order_cmp_zero_iff_eq k1 k2;
  lemma_key_order_cmp_zero_iff_eq k2 k3;
  if key_order_cmp k1 k2 = 0 then ()
  else if key_order_cmp k2 k3 = 0 then ()
  else lemma_key_order_cmp_trans k1 k2 k3

// Bridge: RDF.Indexed's own decorated-pair comparator agrees with
// key_order_cmp on the pairs' keys -- same match shape as
// cmp_by_decorated_key, just reading `fst p` instead of a bound
// variable.
let lemma_dkey_is_key_order_cmp (#a:Type) (p1 p2 : option string * a)
  : Lemma (ensures cmp_by_decorated_key p1 p2 = key_order_cmp (fst p1) (fst p2)) =
  match fst p1, fst p2 with
  | None, None -> ()
  | None, Some _ -> ()
  | Some _, None -> ()
  | Some _, Some _ -> ()

// ===================================================================
// Stage 2: ALL-PAIRS sortedness (not merely adjacent) of decorated
// (option string * a) pairs, over key_order_cmp on the pairs' `fst`.
// The recursive "head relates to the WHOLE tail" shape (via a
// memP-quantified `all_ge`, not structural recursion on the tail)
// composes for free with sortWith's own memP-preservation lemmas
// (lemma_sortWith_memP_forall / _rev_forall, OWL.Semantics.MemLemmas)
// while still encoding position (earlier elements relate to every
// later one) -- exactly what the tree-navigation stage 4 needs.
// ===================================================================

let all_ge (#a:Type) (pivot : option string * a) (l : list (option string * a)) : prop =
  forall (y : option string * a). List.Tot.memP y l ==> key_order_cmp (fst pivot) (fst y) <= 0

let rec sorted_pairs (#a:Type) (l : list (option string * a)) : prop =
  match l with
  | [] -> True
  | x :: tl -> all_ge x tl /\ sorted_pairs tl

// Partition's own characterization, memP-based (noeq-safe): elements
// filed on the `fst (partition f l)` side satisfy `f`, elements filed
// on `snd` side don't. Standard fact, not in the stdlib for noeq `a`
// (the stdlib's own partition lemmas go through `count`, needing
// eqtype) -- mirrors lemma_partition_memP's existing derivation style.
let rec lemma_partition_pred_memP (#a:Type) (f : a -> Tot bool) (l : list a) (x : a)
  : Lemma
    (ensures (List.Tot.memP x (fst (List.Tot.partition f l)) ==> f x == true) /\
             (List.Tot.memP x (snd (List.Tot.partition f l)) ==> f x == false))
    (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl -> lemma_partition_pred_memP f tl x

let lemma_partition_pred_memP_forall (#a:Type) (f : a -> Tot bool) (l : list a)
  : Lemma
    (ensures (forall x. List.Tot.memP x (fst (List.Tot.partition f l)) ==> f x == true) /\
             (forall x. List.Tot.memP x (snd (List.Tot.partition f l)) ==> f x == false)) =
  FStar.Classical.forall_intro (lemma_partition_pred_memP f l)

// Merge two sorted decorated lists around a pivot into one sorted
// list -- the step where transitivity is load-bearing: an element of
// `lo` and an element of `hi` are only related to EACH OTHER via the
// pivot (x <= pivot <= y ==> x <= y), never directly by partition.
let rec lemma_sorted_pairs_append (#a:Type) (pivot : option string * a) (lo hi : list (option string * a))
  : Lemma
    (requires
       sorted_pairs lo /\ sorted_pairs hi /\
       (forall y. List.Tot.memP y lo ==> key_order_cmp (fst y) (fst pivot) <= 0) /\
       (forall y. List.Tot.memP y hi ==> key_order_cmp (fst pivot) (fst y) <= 0))
    (ensures sorted_pairs (List.Tot.append lo (pivot :: hi)))
    (decreases lo) =
  match lo with
  | [] -> ()
  | hd :: tl ->
    lemma_sorted_pairs_append pivot tl hi;
    List.Tot.append_memP_forall tl (pivot :: hi);
    // Need: all_ge hd (append tl (pivot::hi)), i.e. hd relates to all
    // of tl (from sorted_pairs lo's own head fact), to pivot (from
    // the hypothesis at y=hd), and to all of hi -- the latter via
    // transitivity through the pivot: hd <= pivot (hyp) and
    // pivot <= y (hyp, for y in hi) gives hd <= y.
    let aux (y : option string * a) : Lemma
      (requires List.Tot.memP y hi)
      (ensures key_order_cmp (fst hd) (fst y) <= 0) =
      lemma_key_order_cmp_trans_le (fst hd) (fst pivot) (fst y)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec lemma_sortWith_sorted_pairs (#a:Type) (l : list (option string * a))
  : Lemma
    (ensures sorted_pairs (List.Tot.sortWith cmp_by_decorated_key l))
    (decreases (List.Tot.length l)) =
  match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = List.Tot.partition (List.Tot.bool_of_compare cmp_by_decorated_key pivot) tl in
    List.Tot.partition_length (List.Tot.bool_of_compare cmp_by_decorated_key pivot) tl;
    lemma_sortWith_sorted_pairs lo;
    lemma_sortWith_sorted_pairs hi;
    lemma_partition_pred_memP_forall (List.Tot.bool_of_compare cmp_by_decorated_key pivot) tl;
    // hi = elements y of tl with cmp_by_decorated_key pivot y < 0
    // (strictly greater than pivot); lo = elements with
    // cmp_by_decorated_key pivot y >= 0 (i.e. y <= pivot).
    lemma_sortWith_memP_forall cmp_by_decorated_key lo;
    lemma_sortWith_memP_forall cmp_by_decorated_key hi;
    let aux_lo (y : option string * a) : Lemma
      (requires List.Tot.memP y (List.Tot.sortWith cmp_by_decorated_key lo))
      (ensures key_order_cmp (fst y) (fst pivot) <= 0) =
      lemma_dkey_is_key_order_cmp pivot y;
      lemma_key_order_cmp_antisym (fst pivot) (fst y)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_lo);
    let aux_hi (y : option string * a) : Lemma
      (requires List.Tot.memP y (List.Tot.sortWith cmp_by_decorated_key hi))
      (ensures key_order_cmp (fst pivot) (fst y) <= 0) =
      lemma_dkey_is_key_order_cmp pivot y
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux_hi);
    lemma_sorted_pairs_append pivot (List.Tot.sortWith cmp_by_decorated_key lo)
                                     (List.Tot.sortWith cmp_by_decorated_key hi)

// ===================================================================
// Stage 3: group_sorted_decorated_aux carries sorted_pairs of its
// remaining input into (a) an EXISTENCE fact for its output -- every
// element for key `k` ends up in SOME group binding for `k`, whether
// still pending in `ts`, mid-accumulation in `cur_bucket`, or already
// closed into `acc` -- and (b) a STRICT descending kv-sortedness fact
// for the closed groups (distinct keys only, since grouping collapses
// same-key runs). (a) is order-free (pure bookkeeping); (b) is where
// the "once a key closes it never reopens" argument lives, and needs
// the same transitivity the sortWith stage did.
// ===================================================================

// (a) Existence, order-free: mirrors OWL.Semantics.MemLemmas's
// lemma_group_ok in recursion SHAPE (same match structure), but
// proves membership INTO the grouped output rather than membership
// OUT of it. The acc-disjunct is the induction's own bookkeeping: it
// is what lets an element already flushed into a closed group survive
// through further recursive calls (group_sorted_decorated_aux only
// ever CONSES new closed groups onto acc, never removes from it).
let rec lemma_group_exists (#a:Type)
    (ts : list (option string * a)) (cur_key : option string) (cur_bucket : list a)
    (acc : list (string * list a)) (k : string)
  : Lemma
    (ensures
       (forall (t : a).
          (List.Tot.memP (Some k, t) ts \/
           (cur_key == Some k /\ List.Tot.memP t cur_bucket) \/
           (exists (v0 : list a). List.Tot.memP (k, v0) acc /\ List.Tot.memP t v0))
          ==>
          (exists (v : list a).
             List.Tot.memP (k, v) (group_sorted_decorated_aux ts cur_key cur_bucket acc) /\
             List.Tot.memP t v)))
    (decreases ts) =
  match ts with
  | [] -> ()
  | (k', t') :: rest ->
    (match k' with
     | None -> lemma_group_exists rest cur_key cur_bucket acc k
     | Some kk ->
       (match cur_key with
        | Some k0 ->
          if kk = k0 then lemma_group_exists rest cur_key (t' :: cur_bucket) acc k
          else lemma_group_exists rest (Some kk) [t'] ((k0, cur_bucket) :: acc) k
        | None -> lemma_group_exists rest (Some kk) [t'] acc k))

// (b) STRICT descending kv-sortedness of the closed-group accumulator.
// `String.compare` directly (not key_order_cmp): grouped bindings
// carry bare `string` keys (the `option` layer is gone once a group
// closes), so no None case to handle here.
let rec sorted_kv_desc (#a:Type) (l : list (string * list a)) : prop =
  match l with
  | [] -> True
  | x :: tl -> (forall (y : string * list a). List.Tot.memP y tl ==> FStar.String.compare (fst x) (fst y) > 0) /\
              sorted_kv_desc tl

// Small helper: transitively re-bound every key in a list against a
// new, farther pivot -- the one place this file needs
// `string_compare_trans` a second time (the first was the sortWith
// merge in Stage 2).
let lemma_forall_lt_trans (#a:Type) (l : list (string * list a)) (a1 a2 : string)
  : Lemma
    (requires
       (forall (kv : string * list a). List.Tot.memP kv l ==> FStar.String.compare (fst kv) a1 < 0) /\
       FStar.String.compare a1 a2 < 0)
    (ensures (forall (kv : string * list a). List.Tot.memP kv l ==> FStar.String.compare (fst kv) a2 < 0)) =
  let aux (kv : string * list a) : Lemma
    (requires List.Tot.memP kv l)
    (ensures FStar.String.compare (fst kv) a2 < 0) =
    string_compare_trans (fst kv) a1 a2
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// The loop invariant carried through group_sorted_decorated_aux's own
// recursion: the remaining input is still sorted (trivial descent,
// `ts` only ever shrinks structurally); the closed accumulator is
// itself descending-sorted; every closed key is strictly below
// `cur_key` (the in-progress group is always the largest key seen so
// far); and `cur_key = None` forces `acc = []` (nothing can have
// closed before the first group starts).
let group_sorted_inv (#a:Type)
    (ts : list (option string * a)) (cur_key : option string) (acc : list (string * list a)) : prop =
  sorted_pairs ts /\
  sorted_kv_desc acc /\
  (Some? cur_key ==> (forall (kv : string * list a). List.Tot.memP kv acc ==>
                        key_order_cmp (Some (fst kv)) cur_key < 0)) /\
  (Some? cur_key ==> (forall (y : option string * a). List.Tot.memP y ts ==>
                        key_order_cmp cur_key (fst y) <= 0)) /\
  (None? cur_key ==> acc == [])

let rec lemma_group_sorted (#a:Type)
    (ts : list (option string * a)) (cur_key : option string) (cur_bucket : list a)
    (acc : list (string * list a))
  : Lemma
    (requires group_sorted_inv ts cur_key acc)
    (ensures sorted_kv_desc (group_sorted_decorated_aux ts cur_key cur_bucket acc))
    (decreases ts) =
  match ts with
  | [] ->
    (match cur_key with
     | Some k0 ->
       let aux (y : string * list a) : Lemma
         (requires List.Tot.memP y acc)
         (ensures FStar.String.compare k0 (fst y) > 0) =
         string_compare_antisym (fst y) k0
       in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
     | None -> ())
  | (k', t') :: rest ->
    (match k' with
     | None -> lemma_group_sorted rest cur_key cur_bucket acc
     | Some kk ->
       (match cur_key with
        | Some k0 ->
          if kk = k0 then lemma_group_sorted rest cur_key (t' :: cur_bucket) acc
          else begin
            // Closing k0's group: need compare k0 kk < 0 (k0 <= kk from
            // the invariant's cur_key<=ts bound, strict because kk<>k0).
            lemma_key_order_cmp_zero_iff_eq (Some k0) (Some kk);
            // sorted_kv_desc ((k0,cur_bucket)::acc): every OLD acc entry
            // is still < k0 (re-derive the same fact the base case
            // needs, from the OLD invariant's acc-vs-cur_key bound).
            let aux1 (y : string * list a) : Lemma
              (requires List.Tot.memP y acc)
              (ensures FStar.String.compare k0 (fst y) > 0) =
              string_compare_antisym (fst y) k0
            in FStar.Classical.forall_intro (FStar.Classical.move_requires aux1);
            // Every OLD acc entry (< k0) is transitively < the new
            // pivot kk too -- the second (and last) use of transitivity
            // in this file.
            lemma_forall_lt_trans acc k0 kk;
            lemma_group_sorted rest (Some kk) [t'] ((k0, cur_bucket) :: acc)
          end
        | None -> lemma_group_sorted rest (Some kk) [t'] acc))

// ===================================================================
// Stage 4a: `sorted_kv` -- STRICT ASCENDING kv-sortedness, the mirror
// of `sorted_kv_desc` obtained by reversal. Plain bare-string keys
// (matching `sorted_kv_desc`, no `option` layer).
// ===================================================================

let rec sorted_kv (#a:Type) (l : list (string * list a)) : prop =
  match l with
  | [] -> True
  | x :: tl -> (forall (y : string * list a). List.Tot.memP y tl ==> FStar.String.compare (fst x) (fst y) < 0) /\
              sorted_kv tl

// rev(hd::tl) == append (rev tl) [hd] -- via FStar.List.Tot.Properties'
// rev/rev' correspondence (rev_rev') and rev''s own defining equation.
let lemma_rev_cons (#a:Type) (hd:a) (tl:list a)
  : Lemma (ensures List.Tot.rev (hd::tl) == List.Tot.append (List.Tot.rev tl) [hd]) =
  List.Tot.rev_rev' (hd::tl);
  List.Tot.rev_rev' tl

// Appending one strictly-larger element at the END of a sorted_kv list
// keeps it sorted_kv.
let rec lemma_sorted_kv_snoc (#a:Type) (l : list (string*list a)) (x : string*list a)
  : Lemma
    (requires sorted_kv l /\ (forall y. List.Tot.memP y l ==> FStar.String.compare (fst y) (fst x) < 0))
    (ensures sorted_kv (List.Tot.append l [x]))
    (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    lemma_sorted_kv_snoc tl x;
    List.Tot.append_memP_forall tl [x]

// Reversing a descending-sorted kv list gives an ascending-sorted one.
let rec lemma_rev_desc_to_asc (#a:Type) (l : list (string*list a))
  : Lemma
    (requires sorted_kv_desc l)
    (ensures sorted_kv (List.Tot.rev l))
    (decreases l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    lemma_rev_desc_to_asc tl;
    lemma_rev_cons hd tl;
    let aux (y : string*list a) : Lemma
      (requires List.Tot.memP y (List.Tot.rev tl))
      (ensures FStar.String.compare (fst y) (fst hd) < 0) =
      List.Tot.rev_memP tl y;
      string_compare_antisym (fst y) (fst hd)
    in FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    lemma_sorted_kv_snoc (List.Tot.rev tl) hd

// Split direction (the one Stage 4b's tree recursion needs): a
// sorted_kv list's prefix and suffix are each sorted_kv, and every
// prefix element is strictly below every suffix element. Pure
// structural bookkeeping -- no order axioms, since sorted_kv is
// already the all-pairs (not merely adjacent) form.
let rec lemma_sorted_kv_append (#a:Type) (pre post : list (string*list a))
  : Lemma
    (requires sorted_kv (List.Tot.append pre post))
    (ensures sorted_kv pre /\ sorted_kv post /\
             (forall (x y : string*list a). List.Tot.memP x pre /\ List.Tot.memP y post ==>
                FStar.String.compare (fst x) (fst y) < 0))
    (decreases pre) =
  match pre with
  | [] -> ()
  | hd :: tl ->
    lemma_sorted_kv_append tl post;
    List.Tot.append_memP_forall tl post

// ===================================================================
// Stage 4b: `take_prefix`'s two identities the tree recursion needs --
// that it reconstitutes its input by append, and that its two halves'
// lengths add up. Neither exists in RDF.Indexed.fsti (only the memP
// form does, OWL.Semantics.MemLemmas's lemma_take_prefix_memP_forall).
// ===================================================================

let rec lemma_take_prefix_acc_append (#a:Type) (n:nat) (acc xs : list a)
  : Lemma
    (ensures (let (pre, suf) = take_prefix_acc n acc xs in
              List.Tot.append (List.Tot.rev acc) xs == List.Tot.append pre suf))
    (decreases xs) =
  if n = 0 then ()
  else match xs with
       | [] -> ()
       | hd :: tl ->
         lemma_take_prefix_acc_append (n - 1) (hd :: acc) tl;
         lemma_rev_cons hd acc;
         List.Tot.append_assoc (List.Tot.rev acc) [hd] tl;
         List.Tot.append_l_cons hd tl (List.Tot.rev acc)

let lemma_take_prefix_append (#a:Type) (n:nat) (xs : list a)
  : Lemma
    (ensures (let (pre, suf) = take_prefix n xs in xs == List.Tot.append pre suf)) =
  lemma_take_prefix_acc_append n [] xs;
  List.Tot.append_nil_l xs

let rec lemma_take_prefix_acc_length (#a:Type) (n:nat) (acc xs : list a)
  : Lemma
    (requires n <= List.Tot.length xs)
    (ensures (let (pre, suf) = take_prefix_acc n acc xs in
              List.Tot.length pre = List.Tot.length acc + n /\
              List.Tot.length suf = List.Tot.length xs - n))
    (decreases xs) =
  if n = 0 then List.Tot.rev_length acc
  else match xs with
       | [] -> ()
       | hd :: tl -> lemma_take_prefix_acc_length (n - 1) (hd :: acc) tl

let lemma_take_prefix_length (#a:Type) (n:nat) (xs : list a)
  : Lemma
    (requires n <= List.Tot.length xs)
    (ensures (let (pre, suf) = take_prefix n xs in
              List.Tot.length pre = n /\ List.Tot.length suf = List.Tot.length xs - n)) =
  lemma_take_prefix_acc_length n [] xs

// ===================================================================
// Stage 4c: sorted_list_to_tree_fuel's midpoint bisection, given
// sorted_kv, serves every element under its own key -- the direction
// the commented-out ATTEMPT block in OWL.Semantics.MemLemmas.fst could
// not close ("nothing ties the comparison direction to which half
// take_prefix put (k,v) in"). Now it does: sorted_kv (established via
// Stages 2-4a upstream) gives that direction directly, at each
// recursion level, from the LOCAL split's own cross-relation fact.
//
// Mirrors bucket_lookup's own three-way branch (k=k' / compare<0 /
// else) exactly, so each branch's target is bucket_lookup's actual
// reduct. Within each branch the recursive call's precondition (which
// half (k,v) is in) is established by contradiction: sorted_kv rules
// out the other two possibilities via zero_iff_eq (the k=k' case
// forces compare k k' = 0, excluding the strict cross-relations the
// other two branches would need) and antisym (translating the
// right-hand all_gt fact into the left-to-right comparison
// bucket_lookup actually tests).
let rec lemma_slt_lookup_complete (#a:Type)
    (xs : list (string * list a)) (fuel : nat) (k : string) (v : list a) (t : a)
  : Lemma
    (requires sorted_kv xs /\ List.Tot.memP (k, v) xs /\ List.Tot.memP t v /\
              fuel >= List.Tot.length xs)
    (ensures List.Tot.memP t (bucket_lookup (sorted_list_to_tree_fuel xs fuel) k))
    (decreases fuel) =
  match xs with
  | [] -> ()
  | _ ->
    if fuel = 0 then ()
    else begin
      let n = List.Tot.length xs in
      let mid = n / 2 in
      lemma_take_prefix_length mid xs;
      lemma_take_prefix_append mid xs;
      let (left_xs, rest) = take_prefix mid xs in
      match rest with
      | (k', v') :: right_xs ->
        lemma_sorted_kv_append left_xs rest;
        List.Tot.append_memP left_xs rest (k, v);
        string_compare_zero_iff_eq k k';
        string_compare_antisym k' k;
        // Cross-relation facts, each stated as an implication so Z3
        // can pick whichever side actually holds without an explicit
        // branch on a non-decidable memP proposition.
        assert (List.Tot.memP (k, v) left_xs ==> FStar.String.compare k k' < 0);
        assert (List.Tot.memP (k, v) rest ==>
                (k, v) == (k', v') \/ List.Tot.memP (k, v) right_xs);
        assert (List.Tot.memP (k, v) right_xs ==> FStar.String.compare k' k < 0);
        if k = k' then ()
        else if FStar.String.compare k k' < 0 then
          lemma_slt_lookup_complete left_xs (fuel - 1) k v t
        else
          lemma_slt_lookup_complete right_xs (fuel - 1) k v t
      | [] -> ()
    end

// ===================================================================
// Stage 5: compose. Generic over key_of so sp/subj/obj/po/so can
// reuse this by instantiating key_of, per the task brief -- only
// bucket_key_pred is exercised below (the pinned statement), but
// nothing here is predicate-specific.
// ===================================================================

let lemma_build_bucket_complete (#a:Type) (key_of : a -> option string) (ts : list a) (k : string) (t : a)
  : Lemma
    (requires key_of t == Some k /\ List.Tot.memP t ts)
    (ensures List.Tot.memP t (bucket_lookup (build_bucket key_of ts) k)) =
  let decorated = List.Tot.map (fun (x : a) -> (key_of x, x)) ts in
  let sorted = List.Tot.sortWith cmp_by_decorated_key decorated in
  let grouped = group_sorted_decorated_aux sorted None [] [] in
  let ascending = List.Tot.rev grouped in
  List.Tot.memP_map_intro (fun (x : a) -> (key_of x, x)) t ts;
  lemma_sortWith_memP_rev cmp_by_decorated_key decorated (Some k, t);
  lemma_sortWith_sorted_pairs decorated;
  lemma_group_exists sorted None [] [] k;
  lemma_group_sorted sorted None [] [];
  lemma_rev_desc_to_asc grouped;
  let aux (v : list a) : Lemma
    (requires List.Tot.memP (k, v) grouped /\ List.Tot.memP t v)
    (ensures List.Tot.memP t (bucket_lookup (build_bucket key_of ts) k)) =
    List.Tot.rev_memP grouped (k, v);
    lemma_slt_lookup_complete ascending (List.Tot.length ascending) k v t
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

// The pinned statement: every triple of g whose predicate is p IS
// served by `bucket_lookup ig.ig_pred` under p's key, for
// `ig = build_indexed g`. No side condition needed -- bucket_key_pred
// is total (always `Some t.p`, no separator/injectivity concern the
// way sp_key/po_key's STRONG forms need).
let lemma_build_indexed_complete_pred (g : rdf_graph)
  : Lemma
    (ensures (let ig = build_indexed g in
              forall (t : triple).
                List.Tot.memP t g ==>
                List.Tot.memP t (bucket_lookup ig.ig_pred t.p))) =
  let ig = build_indexed g in
  assert (ig.ig_pred == build_bucket bucket_key_pred g);
  let aux (t : triple) : Lemma
    (requires List.Tot.memP t g)
    (ensures List.Tot.memP t (bucket_lookup ig.ig_pred t.p)) =
    lemma_build_bucket_complete bucket_key_pred g t.p t
  in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
