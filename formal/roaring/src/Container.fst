module Container

// Phase D — Container sum type with promotions.
//
// This module unifies the three concrete container variants
// (Array, Bitmap, Run) under a single sum type so the top-level
// Roaring directory in Phase E can hold heterogeneous container
// types per high-16 chunk.
//
// Per `design_issues/roaring_fstar_plan.md` §3.3, Phase D scope:
//   - container sum type
//   - container_contains, container_cardinality
//   - denote_container_for_key (Spec bridge)
//   - denote_container_empty lemma
//   - promotion functions:
//       array_to_bitmap, bitmap_to_array,
//       array_to_run, run_to_array,
//       bitmap_to_run, run_to_bitmap
//     with at least one promotion's denotation-preservation lemma
//     fully proved.
//
// Constraints (CLAUDE.md iron rules):
//   - No assume val
//   - No --admit_smt_queries
//   - No --lax
//   - All recursion structural or fuel-bounded.
//
// Comment-syntax warning: F* block comments NEST and any `*)` inside
// silently terminates the comment. Always use `//` line comments
// when the prose must reference parens-star constructs.

open FStar.List.Tot
open FStar.Mul
open Spec

module CA = Container.Array
module CB = Container.Bitmap
module CR = Container.Run
module U64 = FStar.UInt64
module U32 = FStar.UInt32

// ---------------------------------------------------------------
// 1. The container sum type.
// ---------------------------------------------------------------

type container =
  | C_Array  : CA.array_container -> container
  | C_Bitmap : CB.wf_bitmap       -> container
  | C_Run    : CR.run_container   -> container

let container_contains (c : container) (v : u16_val) : Tot bool =
  match c with
  | C_Array  a  -> CA.array_contains  a  v
  | C_Bitmap bm -> CB.bitmap_contains bm v
  | C_Run    rc -> CR.run_contains    rc v

let container_cardinality (c : container) : Tot nat =
  match c with
  | C_Array  a  -> length a
  | C_Bitmap bm -> CB.bitmap_cardinality bm
  | C_Run    rc -> CR.run_cardinality    rc

let denote_container_for_key (c : container) (v : u16_val) : Tot bool =
  container_contains c v

// ---------------------------------------------------------------
// 2. Empty containers, one per variant.
// ---------------------------------------------------------------

let container_empty_array  : container = C_Array  CA.array_empty
let container_empty_bitmap : container = C_Bitmap CB.bitmap_empty
let container_empty_run    : container = C_Run    CR.run_empty

// denote_container_empty:
//   For each empty-container variant, the denotation is `false`
//   for every candidate value.
//
// The C_Array case is by definition (array_contains [] _ = false).
// The C_Bitmap case relies on CB.denote_bitmap_empty.
// The C_Run case relies on CR.denote_run_empty.

val denote_container_empty (v : u16_val) :
  Lemma (ensures
           denote_container_for_key container_empty_array  v = false /\
           denote_container_for_key container_empty_bitmap v = false /\
           denote_container_for_key container_empty_run    v = false)
let denote_container_empty v =
  CB.denote_bitmap_empty v;
  CR.denote_run_empty v

// ---------------------------------------------------------------
// 3. Word-list helpers reused across promotions.
//
// `set_bit_at_word` sets bit `bit_pos` in u64 `w`.
// `set_bit_in_words` sets bit index `i` in a list of 1024 u64s,
// preserving the list length. Used by array_to_bitmap and
// run_to_bitmap.
// ---------------------------------------------------------------

let set_bit_at_word (w : U64.t) (bit_pos : nat{bit_pos < 64}) : Tot U64.t =
  let s : U32.t = U32.uint_to_t bit_pos in
  let mask = U64.shift_left 1uL s in
  U64.logor w mask

// Update word at position idx in a list of length n; out-of-range
// idx is a no-op (defensive — callers always pass an in-range idx).
let rec list_update_u64
  (ws : list U64.t) (idx : nat) (new_w : U64.t)
  : Tot (result:list U64.t {length result = length ws}) (decreases ws) =
  match ws with
  | [] -> []
  | w :: rest ->
    if idx = 0 then new_w :: rest
    else w :: list_update_u64 rest (idx - 1) new_w

let set_bit_in_words
  (ws : CB.bitmap_words_t) (i : u16_val)
  : Tot CB.bitmap_words_t =
  let word_idx = i / 64 in
  let bit_pos  = i - word_idx `op_Multiply` 64 in
  // word_idx < 1024, bit_pos < 64; bounds carry from i < pow16.
  assert (word_idx < CB.bitmap_words);
  assert (bit_pos < 64);
  let w = CB.list_index_u64 ws word_idx in
  let w' = set_bit_at_word w bit_pos in
  list_update_u64 ws word_idx w'

// ---------------------------------------------------------------
// 4. array_to_bitmap.
//
// Build a wf_bitmap whose set bits are exactly the values in the
// sorted-array container. Cardinality is computed as the actual
// popcount of the resulting word list, so the wf_bitmap invariant
// `bm_card = popcount_sum bm_words` holds by construction.
//
// The runtime cost is one popcount_sum walk after the bit-setting
// pass. That's O(words) = O(1024) on top of the bit-setting pass —
// linear in the array size. A correctness-preserving optimisation
// would track cardinality incrementally; deferred to Phase D.5.
// ---------------------------------------------------------------

let rec set_bits_from_array
  (ws : CB.bitmap_words_t) (xs : list u16_val)
  : Tot CB.bitmap_words_t (decreases xs) =
  match xs with
  | [] -> ws
  | v :: rest ->
    let ws' = set_bit_in_words ws v in
    set_bits_from_array ws' rest

let array_to_bitmap (a : CA.array_container) : Tot CB.wf_bitmap =
  let ws = set_bits_from_array (CB.zero_words_n CB.bitmap_words) a in
  let card = CB.popcount_sum ws in
  { CB.bm_words = ws; CB.bm_card = card }

// Phase D.5: array_to_bitmap correctness lemma.
// Stated near the end of the file (after the shared bit-level
// helpers introduced for the run_to_bitmap proof).

// ---------------------------------------------------------------
// 5. bitmap_to_array.
//
// Walk the universe [0, pow16) high-to-low with an accumulator;
// prepending the current index at each level produces an ascending
// list. Returns `None` when the cardinality exceeds the array cap
// (4096) or when sortedness fails to be statically discharged.
//
// We use a runtime sortedness check rather than a static proof so
// the body stays small; the static proof is Phase D.5.
// ---------------------------------------------------------------

let rec collect_present
  (bm : CB.wf_bitmap) (i : nat{i <= pow16}) (acc : list u16_val)
  : Tot (list u16_val) (decreases i) =
  if i = 0 then acc
  else
    let i' : nat = i - 1 in
    // i' < pow16 since i <= pow16 and i > 0.
    assert (i' < pow16);
    let i'_u16 : u16_val = i' in
    if CB.bitmap_contains bm i'_u16 then
      collect_present bm i' (i'_u16 :: acc)
    else
      collect_present bm i' acc

let bitmap_to_array (bm : CB.wf_bitmap) : Tot (option CA.array_container) =
  let xs = collect_present bm pow16 [] in
  if length xs <= array_max_cardinality && CA.sorted_strict xs then
    Some xs
  else
    None

// Phase D.5: prove (for the Some case)
//   forall bm v. (Some? (bitmap_to_array bm)) ==>
//     (CA.array_contains (Some?.v (bitmap_to_array bm)) v
//      = CB.bitmap_contains bm v)
//
// Strategy: induct on i to show
//   mem y (collect_present bm i acc)
//     = mem y acc \/ (y < i /\ CB.bitmap_contains bm y).
// Since the wrapper threads acc = [] and i = pow16, and any
// y : u16_val automatically satisfies y < pow16, the equation
// collapses to mem y xs = CB.bitmap_contains bm y. Then
// array_contains_iff_mem (available because the Some case enforces
// sorted_strict xs) bridges array_contains to mem.

val mem_collect_present
  (bm : CB.wf_bitmap)
  (i : nat{i <= pow16})
  (acc : list u16_val)
  (y : u16_val) :
  Lemma (ensures
           mem y (collect_present bm i acc)
           = (mem y acc || (y < i && CB.bitmap_contains bm y)))
        (decreases i)
let rec mem_collect_present bm i acc y =
  if i = 0 then ()
  else
    let i' : nat = i - 1 in
    let i'_u16 : u16_val = i' in
    if CB.bitmap_contains bm i'_u16 then
      mem_collect_present bm i' (i'_u16 :: acc) y
    else
      mem_collect_present bm i' acc y

val bitmap_to_array_correct (bm : CB.wf_bitmap) (v : u16_val) :
  Lemma (requires Some? (bitmap_to_array bm))
        (ensures
          (let after = Some?.v (bitmap_to_array bm) in
           CA.array_contains after v = CB.bitmap_contains bm v))
let bitmap_to_array_correct bm v =
  let xs = collect_present bm pow16 [] in
  // The Some case enforces sorted_strict xs, so array_contains_iff_mem
  // applies to xs.
  CA.array_contains_iff_mem xs v;
  // mem v xs = (mem v [] || (v < pow16 && bitmap_contains bm v))
  //          = (false || (true && bitmap_contains bm v))   -- v < pow16 since v : u16_val
  //          = bitmap_contains bm v
  mem_collect_present bm pow16 [] v

// ---------------------------------------------------------------
// 6. array_to_run.
//
// Group consecutive values in the sorted array into runs. A run
// `(s, lmo)` represents the lmo+1 values [s, s+lmo]. We walk the
// array and either extend the current run or close it and open a
// new one. Returns an `option` to keep the bound surfaces simple
// when the canonical-form invariants need a runtime check.
// ---------------------------------------------------------------

// One-pass build: maintain (current_run_start, current_run_lmo,
// accumulator-of-finished-runs).
//
// A natural invariant of the recursion (for callers that hand in a
// sorted-strict array) is that every value extends-or-opens-fresh.
// We re-check at the end via `sorted_nonadjacent` rather than carry
// the proof through the body; that's the Phase D.5 strengthening.

let rec array_to_run_pairs
  (xs : list u16_val)
  : Tot (list (u16_val & nat)) (decreases xs) =
  match xs with
  | [] -> []
  | v :: rest ->
    match array_to_run_pairs rest with
    | [] -> [(v, 0)]
    | (s, lmo) :: tail ->
      // If v + 1 = s, extend the leading run downwards: new run
      // becomes (v, lmo + 1) provided v + lmo + 1 < pow16, which
      // follows from s = v + 1 and s + lmo < pow16. We assert that
      // bound rather than thread it as a refinement, accepting the
      // runtime check on the final wrapper below.
      if v + 1 = s && v + lmo + 1 < pow16 then
        (v, lmo + 1) :: tail
      else
        (v, 0) :: (s, lmo) :: tail

// Refine each candidate pair to a run_pair when in bounds.
let rec wrap_run_pairs
  (ps : list (u16_val & nat))
  : Tot (option (list CR.run_pair)) (decreases ps) =
  match ps with
  | [] -> Some []
  | (s, lmo) :: rest ->
    if s + lmo < pow16 then
      match wrap_run_pairs rest with
      | None -> None
      | Some rest' ->
        let p : CR.run_pair = (s, lmo) in
        Some (p :: rest')
    else None

let array_to_run (a : CA.array_container) : Tot (option CR.run_container) =
  let raw = array_to_run_pairs a in
  match wrap_run_pairs raw with
  | None -> None
  | Some rs ->
    if CR.sorted_nonadjacent rs then Some rs else None

// Phase D.5: array_to_run correctness.
//
// Strategy: factor through a `pairs_contains` predicate that doesn't
// require the run-pair refinement. Show
//   (i)  for every xs, mem v xs <==> pairs_contains (array_to_run_pairs xs) v
//   (ii) wrap_run_pairs ps = Some rs ==> pairs_contains ps v = CR.run_contains rs v
// Combine: if array_to_run a = Some rc, then array_contains a v = run_contains rc v.

let rec pairs_contains (ps : list (u16_val & nat)) (v : u16_val) : Tot bool =
  match ps with
  | [] -> false
  | (s, lmo) :: rest ->
    (s <= v && v <= s + lmo) || pairs_contains rest v

val mem_array_to_run_pairs (xs : list u16_val) (v : u16_val) :
  Lemma (ensures pairs_contains (array_to_run_pairs xs) v = mem v xs)
        (decreases xs)
let rec mem_array_to_run_pairs xs v =
  match xs with
  | [] -> ()
  | v0 :: rest ->
    mem_array_to_run_pairs rest v;
    match array_to_run_pairs rest with
    | [] -> ()
    | (s, lmo) :: tail ->
      // Two-branch case: extend leading run vs prepend a fresh
      // singleton run. Either way, pairs_contains over the result
      // assembles the IH plus the singleton fact (v = v0).
      ()

val pairs_contains_eq_run_contains (ps : list (u16_val & nat)) (rs : list CR.run_pair) (v : u16_val) :
  Lemma (requires wrap_run_pairs ps == Some rs)
        (ensures pairs_contains ps v = CR.run_contains rs v)
        (decreases ps)
let rec pairs_contains_eq_run_contains ps rs v =
  match ps with
  | [] -> ()
  | (s, lmo) :: rest ->
    // wrap_run_pairs (s, lmo) :: rest = Some ((s,lmo) :: rest') where
    // wrap_run_pairs rest = Some rest'.
    if s + lmo < pow16 then
      match wrap_run_pairs rest with
      | None -> ()
      | Some rest' ->
        // rs must be (s, lmo) :: rest'.
        pairs_contains_eq_run_contains rest rest' v
    else ()

val array_to_run_correct (a : CA.array_container) (v : u16_val) :
  Lemma (requires Some? (array_to_run a))
        (ensures
          (let after = Some?.v (array_to_run a) in
           CR.run_contains after v = CA.array_contains a v))
let array_to_run_correct a v =
  let raw = array_to_run_pairs a in
  // The Some path of array_to_run forces wrap_run_pairs raw = Some rs
  // for some rs satisfying sorted_nonadjacent. Recover rs:
  match wrap_run_pairs raw with
  | None -> ()  // vacuous: contradicts Some? (array_to_run a)
  | Some rs ->
    if CR.sorted_nonadjacent rs then begin
      mem_array_to_run_pairs a v;
      pairs_contains_eq_run_contains raw rs v;
      CA.array_contains_iff_mem a v
    end else ()

// ---------------------------------------------------------------
// 7. run_to_array — the fully-proved promotion.
//
// Expand each run pair into its inclusive value list, concatenated
// in run order. Membership of the expansion equals the disjunction
// over runs of "v is in the run" — which is the definition of
// run_contains.
//
// We expose the underlying expansion list (run_to_array_list) so
// the correctness lemma can talk about list membership; the
// option-returning wrapper run_to_array adds the canonical-form
// runtime check.
// ---------------------------------------------------------------

// Expand one run (s, lmo) into the descending list
// [s+lmo; s+lmo-1; ...; s+1; s]. We use a structural recursion on
// `lmo + 1` (an inclusive count). Returning descending order makes
// the recursion structural over the natural-number depth.

let rec range_desc
  (s : u16_val) (count : nat)
  : Tot (list u16_val) (decreases count) =
  if count = 0 then []
  else
    let k : nat = count - 1 in
    if s + k < pow16 then
      let v : u16_val = s + k in
      v :: range_desc s k
    else
      // Vacuous when called with valid inputs (pair_valid ensures
      // s + lmo < pow16, so s + k <= s + lmo < pow16). We return
      // [] defensively to keep the function total without a
      // refinement on count.
      []

// Membership of range_desc s count: y is in iff s <= y < s + count
// AND y < pow16. The second clause is implied by the first when
// s + count <= pow16, which run_pair_valid guarantees.

val mem_range_desc (s : u16_val) (count : nat) (y : u16_val) :
  Lemma (requires s + count <= pow16)
        (ensures mem y (range_desc s count)
                 <==> (s <= y /\ y < s + count))
        (decreases count)
let rec mem_range_desc s count y =
  if count = 0 then ()
  else
    let k : nat = count - 1 in
    // s + k < pow16 since s + count <= pow16 and k < count.
    mem_range_desc s k y

// Append-style concatenation of run expansions.
let rec run_to_array_list (rs : list CR.run_pair)
  : Tot (list u16_val) (decreases rs) =
  match rs with
  | [] -> []
  | r :: rest ->
    let s = CR.pair_start r in
    let lmo = CR.pair_lmo r in
    range_desc s (lmo + 1) @ run_to_array_list rest

// Membership of the expansion list <==> run_contains.
val mem_run_to_array_list (rs : list CR.run_pair) (y : u16_val) :
  Lemma (ensures mem y (run_to_array_list rs)
                 = CR.run_contains rs y)
        (decreases rs)
let rec mem_run_to_array_list rs y =
  match rs with
  | [] -> ()
  | r :: rest ->
    let s = CR.pair_start r in
    let lmo = CR.pair_lmo r in
    // s + (lmo + 1) <= pow16 because run_pair_valid says
    // s + lmo < pow16, hence s + lmo + 1 <= pow16.
    mem_range_desc s (lmo + 1) y;
    mem_run_to_array_list rest y;
    // mem y (a @ b) = mem y a || mem y b — pulled in from the
    // standard library; F* unfolds it automatically.
    FStar.List.Tot.Properties.append_mem (range_desc s (lmo + 1))
                                          (run_to_array_list rest) y

// Concrete promotion wrapper. Returns None if the expansion isn't
// sorted-strict or exceeds the array cap. The Some-case correctness
// lemma proves the denotation matches.

let run_to_array (rc : CR.run_container) : Tot (option CA.array_container) =
  let xs = run_to_array_list rc in
  if length xs <= array_max_cardinality && CA.sorted_strict xs then
    Some xs
  else
    None

// Correctness lemma — the proven denotation-preservation property.

val run_to_array_correct (rc : CR.run_container) (v : u16_val) :
  Lemma (requires Some? (run_to_array rc))
        (ensures
          (let after = Some?.v (run_to_array rc) in
           CA.array_contains after v = CR.run_contains rc v))
let run_to_array_correct rc v =
  let xs = run_to_array_list rc in
  // The check inside `run_to_array` enforces sorted_strict xs in the
  // Some case; the bridge array_contains_iff_mem then equates
  // array_contains with mem, which mem_run_to_array_list ties to
  // run_contains.
  CA.array_contains_iff_mem xs v;
  mem_run_to_array_list rc v

// ---------------------------------------------------------------
// 8. bitmap_to_run.
//
// Walk the universe [0, pow16) ascending, maintaining the
// "currently open run" state. On each transition (1 -> 0 or
// 0 -> 1) we either close the current run or open a new one.
// Phase D ships the body; the canonical-form lemma (paper §4
// "single run spans the whole chunk") is Phase D.5.
// ---------------------------------------------------------------

// Walk descending so `acc` ends up in ascending start order.
//
// State: (current_open_start, current_open_lmo, finished_runs).
// We supply None when no run is open. At each i' = i-1, check the
// bit; on 1, extend or open; on 0, close any open run.
//
// Return type: list of candidate (u16_val & nat) pairs; the wrapper
// re-validates and runtime-checks sorted_nonadjacent.

// We descend i from pow16 down to 0. At each step we look at the
// bit at index i'. The accumulator `acc` is the list of finished
// runs so far in ascending start order; `open_run` is None or
// Some (open_start, open_lmo).
//
// Note: walking high-to-low, an "open run" is a run we've started
// from the high end and may extend downward. When the bit at i'
// is set:
//   - If a run is open at start s (so s = i' + 1 currently), we
//     extend it: new start = i', new lmo = lmo + 1.
//   - Otherwise open a new run at (i', 0).
// When the bit at i' is unset:
//   - Close any open run (push to acc).

let rec bitmap_to_run_descend
  (bm : CB.wf_bitmap)
  (i : nat{i <= pow16})
  (open_run : option (u16_val & nat))
  (acc : list (u16_val & nat))
  : Tot (list (u16_val & nat)) (decreases i) =
  if i = 0 then
    match open_run with
    | None -> acc
    | Some p -> p :: acc
  else
    let i' : nat = i - 1 in
    assert (i' < pow16);
    let i'_u16 : u16_val = i' in
    let bit = CB.bitmap_contains bm i'_u16 in
    if bit then
      match open_run with
      | None ->
        bitmap_to_run_descend bm i' (Some (i'_u16, 0)) acc
      | Some (s, lmo) ->
        if s = i' + 1 then
          // Extend down. Bound: new start i', new lmo lmo+1; need
          // i' + (lmo + 1) < pow16, i.e. i' + lmo + 1 < pow16. From
          // the invariant s + lmo < pow16 and s = i' + 1, we get
          // i' + 1 + lmo < pow16, i.e. i' + lmo + 1 < pow16. We
          // assert it for clarity and to discharge any obligations
          // implied below.
          bitmap_to_run_descend bm i' (Some (i'_u16, lmo + 1)) acc
        else
          // Shouldn't happen if the descent is monotone, but is
          // structurally fine: close the old run and open a new
          // one at i'.
          bitmap_to_run_descend bm i' (Some (i'_u16, 0)) ((s, lmo) :: acc)
    else
      // Bit is 0; close any open run.
      match open_run with
      | None -> bitmap_to_run_descend bm i' None acc
      | Some p ->
        bitmap_to_run_descend bm i' None (p :: acc)

let bitmap_to_run (bm : CB.wf_bitmap) : Tot (option CR.run_container) =
  let raw = bitmap_to_run_descend bm pow16 None [] in
  match wrap_run_pairs raw with
  | None -> None
  | Some rs ->
    if CR.sorted_nonadjacent rs then Some rs else None

// TODO Phase D.5: prove correctness, including the spans_whole_chunk
// canonical-form predicate from CR for fully-saturated bitmaps.

// ---------------------------------------------------------------
// 9. run_to_bitmap.
//
// Walk the runs, setting a contiguous range of bits per run.
// We reuse set_bit_in_words one bit at a time, which is O(N) in
// the run length (paper §4 algorithm 3 is the optimised mask
// version; deferred to Phase G).
// ---------------------------------------------------------------

// Set bits [s, s+count-1] in ws. Structurally recursive on count.
let rec set_range_in_words
  (ws : CB.bitmap_words_t) (s : u16_val) (count : nat)
  : Tot CB.bitmap_words_t (decreases count) =
  if count = 0 then ws
  else
    let k : nat = count - 1 in
    if s + k < pow16 then
      let v : u16_val = s + k in
      let ws' = set_bit_in_words ws v in
      set_range_in_words ws' s k
    else
      // Vacuous for valid run pairs. Defensive.
      set_range_in_words ws s k

let rec set_bits_from_runs
  (ws : CB.bitmap_words_t) (rs : list CR.run_pair)
  : Tot CB.bitmap_words_t (decreases rs) =
  match rs with
  | [] -> ws
  | r :: rest ->
    let s = CR.pair_start r in
    let lmo = CR.pair_lmo r in
    let ws' = set_range_in_words ws s (lmo + 1) in
    set_bits_from_runs ws' rest

let run_to_bitmap (rc : CR.run_container) : Tot CB.wf_bitmap =
  let ws = set_bits_from_runs (CB.zero_words_n CB.bitmap_words) rc in
  let card = CB.popcount_sum ws in
  { CB.bm_words = ws; CB.bm_card = card }

// Phase D.5: prove
//   forall rc v. CB.bitmap_contains (run_to_bitmap rc) v
//              = CR.run_contains rc v
//
// Strategy. The proof factors through three lift levels:
//
//   (a) Bit-level: set_bit_at_word's effect on CB.bit_at_word.
//   (b) Word-list level: list_update_u64's effect on list_index_u64,
//       lifted to set_bit_in_words on words_contain.
//   (c) Range / run level: set_range_in_words mirrors run-membership
//       on a single pair; set_bits_from_runs mirrors the disjunction
//       across all runs.
//
// run_to_bitmap then builds a wf_bitmap from these final words; the
// cardinality field doesn't affect bitmap_contains.

// ---------- (a) Bit-level lemmas ----------
//
// `set_bit_at_word w p` ORs in (shift_left 1uL p), which sets bit p
// (value-position) and leaves all other bits of `w` unchanged.

val bit_at_word_set_same (w : U64.t) (p : nat{p < 64}) :
  Lemma (ensures CB.bit_at_word (set_bit_at_word w p) p = true)
let bit_at_word_set_same w p =
  let s : U32.t = U32.uint_to_t p in
  let mask = U64.shift_left 1uL s in
  // mask = 2^p; logand (logor w mask) mask = mask <> 0 since mask <> 0.
  // We reason via FStar.UInt.nth and the SMT patterns on logor / shift_left
  // / pow2_n. The body just establishes the right vector inequality:
  //   nth (logor w mask) (63 - p) = nth w (63 - p) || nth mask (63 - p)
  //                               = _ || true = true
  // and then (logor w mask) & mask is non-zero because they share the
  // high-bit at position 63 - p.
  let lor = U64.logor w mask in
  let masked = U64.logand lor mask in
  // mask's only set nth-position is 63 - p.
  // FStar.UInt.pow2_nth_lemma says nth (pow2_n p) i is true iff i = n-p-1.
  // shift_left 1 p has value 2^p (when p < n), and we use that fact via
  // FStar.UInt.shift_left_value_lemma; or directly: shift_left of (one n)
  // by p has nth-position n-1-p set.
  // The simplest path: appeal to nth_lemma after asserting equality at
  // position 63 - p only — but nth_lemma needs full equality. We instead
  // appeal to logand/logor's nth definitions plus shift_left's nth def.
  let i : nat = 63 - p in
  // nth (shift_left 1uL p) i: shift_left_lemma_2 says it equals nth #64 1 (i + p) if i + p < 64.
  // Here i + p = 63, and nth #64 1 63 = true (one_nth_lemma: nth (one n) (n-1) = true).
  FStar.UInt.shift_left_lemma_2 #64 (FStar.UInt.one 64) p i;
  FStar.UInt.one_nth_lemma #64 (i + p);
  FStar.UInt.logor_definition #64 (U64.v w) (U64.v mask) i;
  // Now nth (U64.v lor) i = nth w i || true = true.
  // CB.bit_at_word checks not (eq (logand lor mask) 0). We use logand's nth
  // definition at index i: nth (logand lor mask) i = nth lor i && nth mask i = true.
  FStar.UInt.logand_definition #64 (U64.v lor) (U64.v mask) i;
  // A nonzero u64 differs from zero by nth_lemma — but we don't even
  // need the full lemma; nth at i being true rules out the zero word
  // (zero_nth_lemma gives every nth = false for zero).
  FStar.UInt.zero_nth_lemma #64 i;
  // Suffices: U64.v masked <> 0. nth at i is true here, false in zero.
  // F* infers CB.bit_at_word's inner not (U64.eq masked 0uL) = not false = true
  // once we discharge masked <> 0.
  if U64.v masked = 0 then begin
    // contradiction: nth (zero 64) i = false but nth masked i = true.
    let _ : squash (FStar.UInt.nth (U64.v masked) i = true) = () in
    let _ : squash (FStar.UInt.nth (U64.v masked) i = false) = () in
    ()
  end

val bit_at_word_set_other (w : U64.t) (p q : nat) :
  Lemma (requires p < 64 /\ q < 64 /\ p <> q)
        (ensures CB.bit_at_word (set_bit_at_word w p) q = CB.bit_at_word w q)
let bit_at_word_set_other w p q =
  let sp : U32.t = U32.uint_to_t p in
  let mask = U64.shift_left 1uL sp in
  let lor = U64.logor w mask in
  // We must show, calling CB.bit_at_word with bit_pos = q on lor:
  //   not (eq (logand lor (shift_left 1uL q)) 0)
  // = not (eq (logand w (shift_left 1uL q)) 0)
  // Since the only differing nth-bit between lor and w is at position
  // 63 - p, and the q-mask has its only set bit at 63 - q, with p <> q
  // these positions are disjoint and the logand at the q-mask bit only
  // sees w.
  let sq : U32.t = U32.uint_to_t q in
  let mask_q = U64.shift_left 1uL sq in
  let bit_w  = U64.logand w mask_q in
  let bit_lor = U64.logand lor mask_q in
  // Show the values are equal by nth_lemma. We need nth bit_w i = nth bit_lor i
  // for every i in [0,64). We split into two cases using SMT.
  let aux (i : nat{i < 64}) :
    Lemma (FStar.UInt.nth (U64.v bit_w) i = FStar.UInt.nth (U64.v bit_lor) i)
  =
    // SMT patterns on shift_left / logor / logand suffice here once we
    // pin the relationship between `mask`, `mask_q` and i.
    FStar.UInt.logand_definition #64 (U64.v w) (U64.v mask_q) i;
    FStar.UInt.logand_definition #64 (U64.v lor) (U64.v mask_q) i;
    FStar.UInt.logor_definition #64 (U64.v w) (U64.v mask) i;
    // mask = pow2_n-style: shift_left 1 p sets only nth-position 63 - p.
    if i + p < 64 then
      FStar.UInt.shift_left_lemma_2 #64 (FStar.UInt.one 64) p i
    else
      FStar.UInt.shift_left_lemma_1 #64 (FStar.UInt.one 64) p i;
    FStar.UInt.one_nth_lemma #64 (if i + p < 64 then i + p else 0);
    if i + q < 64 then
      FStar.UInt.shift_left_lemma_2 #64 (FStar.UInt.one 64) q i
    else
      FStar.UInt.shift_left_lemma_1 #64 (FStar.UInt.one 64) q i;
    FStar.UInt.one_nth_lemma #64 (if i + q < 64 then i + q else 0)
  in
  FStar.Classical.forall_intro aux;
  FStar.UInt.nth_lemma #64 (U64.v bit_w) (U64.v bit_lor)

// ---------- (b) Word-list lemmas ----------
//
// `words_get` is the bit-probe equivalent of CB.bitmap_contains but
// at the bitmap_words_t level (no cardinality field, so no wf_bitmap
// invariant to maintain mid-construction).

let words_get (ws : CB.bitmap_words_t) (v : u16_val) : Tot bool =
  let word_idx = v / 64 in
  let bit_pos  = v - word_idx `op_Multiply` 64 in
  assert (word_idx < CB.bitmap_words);
  assert (bit_pos < 64);
  CB.bit_at_word (CB.list_index_u64 ws word_idx) bit_pos

// By definition CB.bitmap_contains agrees with words_get on bm_words.
val bitmap_contains_eq_words_get (bm : CB.wf_bitmap) (v : u16_val) :
  Lemma (ensures CB.bitmap_contains bm v = words_get bm.CB.bm_words v)
let bitmap_contains_eq_words_get _ _ = ()

// list_update_u64 is defensive at out-of-range idx (no-op). The
// in-range case gives a clean read-after-update bridge.

val list_index_update_same (ws : list U64.t) (idx : nat) (new_w : U64.t) :
  Lemma (requires idx < length ws)
        (ensures CB.list_index_u64 (list_update_u64 ws idx new_w) idx = new_w)
        (decreases ws)
let rec list_index_update_same ws idx new_w =
  match ws with
  | [] -> ()
  | _ :: rest ->
    if idx = 0 then ()
    else list_index_update_same rest (idx - 1) new_w

val list_index_update_other (ws : list U64.t) (idx : nat) (new_w : U64.t) (idx2 : nat) :
  Lemma (requires idx <> idx2)
        (ensures CB.list_index_u64 (list_update_u64 ws idx new_w) idx2
                 = CB.list_index_u64 ws idx2)
        (decreases ws)
let rec list_index_update_other ws idx new_w idx2 =
  match ws with
  | [] -> ()
  | _ :: rest ->
    if idx = 0 then begin
      // result = new_w :: rest, so list_index at idx2 (>0) reads rest at idx2-1.
      ()
    end else if idx2 = 0 then
      // result = w :: list_update rest (idx-1) new_w; idx2=0 reads w.
      ()
    else
      list_index_update_other rest (idx - 1) new_w (idx2 - 1)

// Lift to set_bit_in_words / words_get: setting bit at v0 leaves the
// probe at v unchanged when v <> v0, and forces the probe true when
// v = v0.

val words_get_set_same (ws : CB.bitmap_words_t) (v0 : u16_val) :
  Lemma (ensures words_get (set_bit_in_words ws v0) v0 = true)
let words_get_set_same ws v0 =
  let word_idx = v0 / 64 in
  let bit_pos  = v0 - word_idx `op_Multiply` 64 in
  assert (word_idx < CB.bitmap_words);
  assert (bit_pos < 64);
  let w = CB.list_index_u64 ws word_idx in
  let w' = set_bit_at_word w bit_pos in
  // Result of set_bit_in_words is list_update_u64 ws word_idx w'.
  list_index_update_same ws word_idx w';
  // After update, list_index at word_idx is w'; bit_at_word w' bit_pos = true.
  bit_at_word_set_same w bit_pos

val words_get_set_other (ws : CB.bitmap_words_t) (v0 : u16_val) (v : u16_val) :
  Lemma (requires v <> v0)
        (ensures words_get (set_bit_in_words ws v0) v = words_get ws v)
let words_get_set_other ws v0 v =
  let wi0 = v0 / 64 in
  let bp0 = v0 - wi0 `op_Multiply` 64 in
  let wi  = v  / 64 in
  let bp  = v  - wi  `op_Multiply` 64 in
  assert (wi0 < CB.bitmap_words);
  assert (bp0 < 64);
  assert (wi  < CB.bitmap_words);
  assert (bp  < 64);
  let w0  = CB.list_index_u64 ws wi0 in
  let w0' = set_bit_at_word w0 bp0 in
  // ws_after = list_update_u64 ws wi0 w0'.
  if wi = wi0 then begin
    // Same word: bit_pos must differ since v <> v0. Reason: v and v0
    // are uniquely encoded as (wi, bp) in [0,1024) x [0,64), so wi=wi0
    // and bp=bp0 would force v=v0.
    assert (bp <> bp0);
    list_index_update_same ws wi0 w0';
    // After update, the probe at v reads w0' at bp; before update,
    // it reads w0 at bp. Bit at bp is unchanged because bp <> bp0.
    bit_at_word_set_other w0 bp0 bp
  end else begin
    // Different word: list_index at wi is unaffected.
    list_index_update_other ws wi0 w0' wi
  end

// Probing words_get against the all-zeros words. Re-uses the lemmas
// supporting denote_bitmap_empty.

val words_get_zero (v : u16_val) :
  Lemma (ensures words_get (CB.zero_words_n CB.bitmap_words) v = false)
let words_get_zero v =
  let word_idx = v / 64 in
  let bit_pos  = v - word_idx `op_Multiply` 64 in
  CB.list_index_zero_words CB.bitmap_words word_idx;
  CB.bit_at_word_zero bit_pos

// ---------- (c) Range / run lemma chain ----------
//
// For a single run starting at s with length count, set_range_in_words
// matches "v in [s, s+count)" disjuncted with the prior probe.

val words_get_set_range (ws : CB.bitmap_words_t) (s : u16_val) (count : nat) (v : u16_val) :
  Lemma (requires s + count <= pow16)
        (ensures words_get (set_range_in_words ws s count) v
                 = ((s <= v && v < s + count) || words_get ws v))
        (decreases count)
let rec words_get_set_range ws s count v =
  if count = 0 then ()
  else
    let k : nat = count - 1 in
    // s + k < pow16 from s + count <= pow16.
    let v_top : u16_val = s + k in
    let ws' = set_bit_in_words ws v_top in
    // set_range_in_words ws s count = set_range_in_words ws' s k.
    words_get_set_range ws' s k v;
    // words_get ws' v = (v = v_top) || words_get ws v.
    if v = v_top then
      words_get_set_same ws v_top
    else
      words_get_set_other ws v_top v

// Run-list version: set_bits_from_runs threads through every run; the
// final probe equals the disjunction over runs (run_contains) plus the
// initial probe.

val words_get_set_bits_from_runs
  (ws : CB.bitmap_words_t) (rs : list CR.run_pair) (v : u16_val) :
  Lemma (ensures words_get (set_bits_from_runs ws rs) v
                 = (CR.run_contains rs v || words_get ws v))
        (decreases rs)
let rec words_get_set_bits_from_runs ws rs v =
  match rs with
  | [] -> ()
  | r :: rest ->
    let s = CR.pair_start r in
    let lmo = CR.pair_lmo r in
    // s + (lmo + 1) <= pow16 follows from run_pair_valid: s + lmo < pow16.
    let ws' = set_range_in_words ws s (lmo + 1) in
    words_get_set_range ws s (lmo + 1) v;
    words_get_set_bits_from_runs ws' rest v
    // run_contains (r :: rest) v = (s <= v <= s+lmo) || run_contains rest v
    //                           = (s <= v < s+lmo+1) || run_contains rest v.
    // The two recursive facts assemble exactly to the goal.

// Final lemma: bit-by-bit semantics of run_to_bitmap matches run_contains.

val run_to_bitmap_correct (rc : CR.run_container) (v : u16_val) :
  Lemma (ensures CB.bitmap_contains (run_to_bitmap rc) v
                 = CR.run_contains rc v)
let run_to_bitmap_correct rc v =
  let zero = CB.zero_words_n CB.bitmap_words in
  let final_words = set_bits_from_runs zero rc in
  // CB.bitmap_contains (run_to_bitmap rc) v = words_get final_words v.
  bitmap_contains_eq_words_get (run_to_bitmap rc) v;
  // = run_contains rc v || words_get zero v
  words_get_set_bits_from_runs zero rc v;
  // = run_contains rc v || false
  words_get_zero v

// array_to_bitmap correctness — same scaffolding as run_to_bitmap:
// set_bits_from_array threads single-bit sets across the array's
// values, so the probe at v on the resulting words equals
// "v is in the array" || prior probe.

val words_get_set_bits_from_array
  (ws : CB.bitmap_words_t) (xs : list u16_val) (v : u16_val) :
  Lemma (ensures words_get (set_bits_from_array ws xs) v
                 = (mem v xs || words_get ws v))
        (decreases xs)
let rec words_get_set_bits_from_array ws xs v =
  match xs with
  | [] -> ()
  | v0 :: rest ->
    let ws' = set_bit_in_words ws v0 in
    words_get_set_bits_from_array ws' rest v;
    if v = v0 then
      words_get_set_same ws v0
    else
      words_get_set_other ws v0 v

val array_to_bitmap_correct (a : CA.array_container) (v : u16_val) :
  Lemma (ensures CB.bitmap_contains (array_to_bitmap a) v
                 = CA.array_contains a v)
let array_to_bitmap_correct a v =
  let zero = CB.zero_words_n CB.bitmap_words in
  bitmap_contains_eq_words_get (array_to_bitmap a) v;
  words_get_set_bits_from_array zero a v;
  words_get_zero v;
  // Bridge mem to array_contains via sorted_strict (a is an array_container).
  CA.array_contains_iff_mem a v

// ---------- bitmap_to_run correctness ----------
//
// Strategy. The descent maintains three invariants on its state at
// each level i:
//   (1) shape:    open_run = None, OR open_run = Some(s, lmo) with
//                 s = i and s + lmo < pow16.
//   (2) match:    for every v with i <= v < pow16,
//                   open_contains open_run v || pairs_contains acc v
//                   = bitmap_contains bm v.
//   (3) acc-low:  for every v with v < i,
//                   pairs_contains acc v = false.
//
// Under these, the result of bitmap_to_run_descend bm i open_run acc
// satisfies pairs_contains result v = bitmap_contains bm v for every
// v in [0, pow16). The wrapper supplies the trivially-valid initial
// state (i = pow16, None, []), then re-wraps and validates the canonical
// form. The wrap step preserves underlying values so pairs_contains
// matches run_contains.

let open_contains (open_run : option (u16_val & nat)) (v : u16_val) : bool =
  match open_run with
  | None -> false
  | Some (s, lmo) -> s <= v && v <= s + lmo

let valid_descend_shape
  (i : nat{i <= pow16})
  (open_run : option (u16_val & nat))
  : prop =
  match open_run with
  | None -> True
  | Some (s, lmo) -> s == i /\ s + lmo < pow16

let valid_descend_match
  (bm : CB.wf_bitmap)
  (i : nat{i <= pow16})
  (open_run : option (u16_val & nat))
  (acc : list (u16_val & nat))
  : prop =
  forall (v : u16_val).
    i <= v ==>
    (open_contains open_run v || pairs_contains acc v) = CB.bitmap_contains bm v

let valid_descend_acc_low
  (i : nat{i <= pow16})
  (acc : list (u16_val & nat))
  : prop =
  forall (v : u16_val). v < i ==> pairs_contains acc v = false

// Per-step membership invariant: under the three preconditions, the
// final descent result agrees with bitmap_contains everywhere.

val descend_correct
  (bm : CB.wf_bitmap)
  (i : nat{i <= pow16})
  (open_run : option (u16_val & nat))
  (acc : list (u16_val & nat)) :
  Lemma
    (requires
      valid_descend_shape i open_run /\
      valid_descend_match bm i open_run acc /\
      valid_descend_acc_low i acc)
    (ensures
      (let r = bitmap_to_run_descend bm i open_run acc in
       forall (v : u16_val). pairs_contains r v = CB.bitmap_contains bm v))
    (decreases i)
let rec descend_correct bm i open_run acc =
  if i = 0 then begin
    match open_run with
    | None -> ()
    | Some _ -> ()
  end else begin
    assert (i > 0);
    let i' : nat = i - 1 in
    assert (i' < pow16);
    let i'_u16 : u16_val = i' in
    let bit = CB.bitmap_contains bm i'_u16 in
    if bit then begin
      match open_run with
      | None ->
        let new_open : option (u16_val & nat) = Some (i'_u16, 0) in
        // Discharge valid_descend_match bm i' new_open acc:
        // For v with i' <= v: open_contains new_open v = (v = i').
        //   At v = i': true; bitmap_contains bm i' = bit = true. ✓
        //   At v > i' (v >= i): old match gives pairs_contains acc v = bm v.
        descend_correct bm i' new_open acc
      | Some (s, lmo) ->
        if s = i' + 1 then begin
          let new_open : option (u16_val & nat) = Some (i'_u16, lmo + 1) in
          // Discharge valid_descend_match bm i' new_open acc:
          // open_contains new_open v = (i' <= v && v <= i' + lmo + 1).
          // Old shape: s = i so old open_contains v = (i <= v <= i + lmo).
          // For v >= i (= i'+1): both reduce to (v <= i + lmo).
          // For v = i': new gives true; bm i' = bit = true.
          assert (CB.bitmap_contains bm i'_u16 = true);
          assert (s = i);
          let aux (v : u16_val) :
            Lemma (i' <= v ==> ((open_contains new_open v || pairs_contains acc v)
                                = CB.bitmap_contains bm v)) =
            if i' <= v then begin
              if v = i'_u16 then ()
              else begin
                assert (v <> i'_u16);
                assert (v > i');
                assert (v >= i)
              end
            end
          in
          FStar.Classical.forall_intro aux;
          descend_correct bm i' new_open acc
        end else begin
          // Dead branch: shape invariant says s = i = i' + 1 when
          // open_run = Some _, so this else cannot fire.
          assert (s = i);
          assert (s = i' + 1);
          assert False
        end
    end else begin
      match open_run with
      | None ->
        descend_correct bm i' None acc
      | Some (s, lmo) ->
        let new_acc : list (u16_val & nat) = (s, lmo) :: acc in
        // Shape says s = i, hence s = i' + 1.
        assert (s = i);
        assert (CB.bitmap_contains bm i'_u16 = false);
        // Discharge valid_descend_match bm i' None new_acc:
        // open_contains None v = false.
        // pairs_contains new_acc v = (s <= v <= s+lmo) || pairs_contains acc v.
        let aux_match (v : u16_val) :
          Lemma (i' <= v ==> ((false || pairs_contains new_acc v)
                              = CB.bitmap_contains bm v)) =
          if i' <= v then begin
            if v = i'_u16 then begin
              assert (s > v);
              // pairs_contains acc i' = false from old acc_low (i' < i).
              ()
            end else begin
              assert (v <> i'_u16);
              assert (v > i');
              assert (v >= i)
            end
          end
        in
        FStar.Classical.forall_intro aux_match;
        // Discharge valid_descend_acc_low i' new_acc:
        // For v < i': (s <= v && v <= s+lmo) is false (s=i > v); pairs_contains acc v = false (old acc_low, v < i' < i).
        let aux_low (v : u16_val) :
          Lemma (v < i' ==> pairs_contains new_acc v = false) =
          if v < i' then begin
            assert (s > v);
            ()
          end
        in
        FStar.Classical.forall_intro aux_low;
        descend_correct bm i' None new_acc
    end
  end

val bitmap_to_run_correct (bm : CB.wf_bitmap) (v : u16_val) :
  Lemma (requires Some? (bitmap_to_run bm))
        (ensures
          (let after = Some?.v (bitmap_to_run bm) in
           CR.run_contains after v = CB.bitmap_contains bm v))
let bitmap_to_run_correct bm v =
  let raw = bitmap_to_run_descend bm pow16 None [] in
  // Initial state trivially satisfies all three preconditions:
  //   shape:   open_run = None.
  //   match:   forall v with pow16 <= v < pow16: vacuous.
  //   acc_low: forall v < pow16: pairs_contains [] v = false definitionally.
  descend_correct bm pow16 None [];
  // pairs_contains raw v = bitmap_contains bm v for every v : u16_val.
  // wrap_run_pairs and the sorted_nonadjacent gate preserve underlying values.
  match wrap_run_pairs raw with
  | None -> ()
  | Some rs ->
    if CR.sorted_nonadjacent rs then
      pairs_contains_eq_run_contains raw rs v
    else ()

// ---------------------------------------------------------------
// 10. Smoke tests via assert_norm.
//
// Concrete cases the F* normalizer can fully reduce. Empty
// containers exercise denote_container_empty's branches.
// ---------------------------------------------------------------

let _ = assert_norm (container_cardinality container_empty_array  = 0)
let _ = assert_norm (container_cardinality container_empty_run    = 0)
let _ = assert_norm (not (container_contains container_empty_array  0))
let _ = assert_norm (not (container_contains container_empty_array  65535))
let _ = assert_norm (not (container_contains container_empty_run    0))
let _ = assert_norm (not (container_contains container_empty_run    65535))
