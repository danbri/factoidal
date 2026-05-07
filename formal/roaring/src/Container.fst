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

// TODO Phase D.5: prove
//   forall a v. CB.bitmap_contains (array_to_bitmap a) v
//             = CA.array_contains  a v
// This requires bit-level equational reasoning about set_bit_at_word
// and a bridge from popcount_u64 / list_index_u64 to bit_at_word.

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

// TODO Phase D.5: prove (for the Some case)
//   forall bm v. (Some? (bitmap_to_array bm)) ==>
//     (CA.array_contains (Some?.v (bitmap_to_array bm)) v
//      = CB.bitmap_contains bm v)
// Requires showing collect_present returns sorted_strict ascending
// list whose membership matches bitmap_contains.

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

// TODO Phase D.5: prove
//   forall a v. (Some? (array_to_run a)) ==>
//     CR.run_contains (Some?.v (array_to_run a)) v
//     = CA.array_contains a v

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

// TODO Phase D.5: prove
//   forall rc v. CB.bitmap_contains (run_to_bitmap rc) v
//              = CR.run_contains rc v

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
