module Regex.Exec

// The fast path: normalized derivatives, a codepoint-class alphabet
// partition, unanchored search, and a fuel-bounded emptiness check.
// Phase 1 of issue #304. Design doc:
// docs/designissues/2026-07-15-verified-regex-engine.md
//
// TIER: this is the IMPLEMENTATION-PRAGMATICS layer (fstar-module-style).
// It is pure, total F* (Tot, explicit fuel, no effects), so it extracts to
// OCaml/JS/wasm/C like the rest of the tree, but it is the "unverified
// performance" layer in the sense of iron rule #11's project qualifier:
//
//   * `run_word` / `matches` here reuse the PROVEN Regex.Derivative.deriv, so
//     matching inherits `matches_correct`. Memoization of a deterministic
//     function is transparent, so a future memoized cache does not change the
//     result.
//   * `nderiv` (normalized derivative) additionally applies `smart_cat` /
//     `smart_star` to keep the derivative state set finite (needed for the DFA
//     closure and emptiness). Its language-equality to `deriv`
//     (`smart_cat_ok` / `smart_star_ok`) is a Phase-2 proof obligation; until
//     then `is_empty` below is SOUND-BY-CONSTRUCTION but not machine-checked
//     (precise guarantee stated at `is_empty`).
//
// EXTRACTION NOTE (fstar-module-style extraction traps): `run_word` is written
// in tail position so it extracts to an OCaml loop rather than deep recursion
// on the word length (F* Tot totality is NOT OCaml stack safety). Codepoints
// are `nat`, which extract to zarith `Z.t`; the Phase-1 goal is existence +
// correctness of the engine, and the perf-smoke measurement in the design doc
// records the order of magnitude. A byte/int32 codepoint representation is a
// Phase-3 optimization once a consumer needs the throughput.

open FStar.Mul
open Regex.Syntax
module D = Regex.Derivative
module L = FStar.List.Tot

// ----------------------------------------------------------------------------
// Full ACI normalization for Alt / And (Owens-Reppy-Turon similarity)
// ----------------------------------------------------------------------------
//
// smart_alt / smart_and in Regex.Syntax only canonicalize ONE binary node
// (kept deliberately shallow so their `*_ok` language lemmas — which the
// VERIFIED derivative depends on — stay cheap). The DFA state set is only
// finite once nested alternation is flattened into a sorted, deduplicated leaf
// set (associativity + commutativity + idempotence). Without this the classic
// `(a?)^n a^n` derivative chain grows exponentially. We do the full flatten
// here in the pragmatics layer, where correctness is a Phase-2 obligation.

let rec insert_regex (x:regex) (xs:list regex) : Tot (list regex) (decreases xs) =
  match xs with
  | [] -> [x]
  | y :: ys ->
    let c = regex_cmp x y in
    if c = 0 then xs
    else if c < 0 then x :: xs
    else y :: insert_regex x ys

// Flatten an Alt tree, dropping R_Empty (identity of union), into a sorted
// deduped leaf list.
let rec alt_flatten (r:regex) (acc:list regex) : Tot (list regex) (decreases r) =
  match r with
  | R_Empty -> acc
  | R_Alt a b -> alt_flatten a (alt_flatten b acc)
  | _ -> insert_regex r acc

// Flatten an And tree, dropping the universal language (identity of
// intersection), into a sorted deduped leaf list.
let rec and_flatten (r:regex) (acc:list regex) : Tot (list regex) (decreases r) =
  match r with
  | R_And a b -> and_flatten a (and_flatten b acc)
  | _ -> if r = r_universal then acc else insert_regex r acc

let rec has_universal (xs:list regex) : Tot bool (decreases xs) =
  match xs with [] -> false | y :: ys -> (y = r_universal) || has_universal ys

let rec has_empty (xs:list regex) : Tot bool (decreases xs) =
  match xs with [] -> false | y :: ys -> R_Empty? y || has_empty ys

let rec rebuild_alt (xs:list regex) : Tot regex (decreases xs) =
  match xs with
  | [] -> R_Empty
  | [x] -> x
  | x :: rest -> R_Alt x (rebuild_alt rest)

let rec rebuild_and (xs:list regex) : Tot regex (decreases xs) =
  match xs with
  | [] -> r_universal
  | [x] -> x
  | x :: rest -> R_And x (rebuild_and rest)

// Canonical union: flatten, dedup, sort; universal absorbs.
let ealt (a b:regex) : regex =
  let leaves = alt_flatten a (alt_flatten b []) in
  if has_universal leaves then r_universal else rebuild_alt leaves

// Canonical intersection: flatten, dedup, sort; R_Empty absorbs.
let eand (a b:regex) : regex =
  let leaves = and_flatten a (and_flatten b []) in
  if has_empty leaves then R_Empty else rebuild_and leaves

// ----------------------------------------------------------------------------
// Normalized derivative (ACI-flattened Alt/And, smart_cat/smart_star)
// ----------------------------------------------------------------------------

let rec nderiv (c:nat) (r:regex) : Tot regex (decreases r) =
  match r with
  | R_Empty -> R_Empty
  | R_Eps -> R_Empty
  | R_Ranges rs -> if in_ranges c rs then R_Eps else R_Empty
  | R_Alt a b -> ealt (nderiv c a) (nderiv c b)
  | R_And a b -> eand (nderiv c a) (nderiv c b)
  | R_Not a -> smart_not (nderiv c a)
  | R_Cat a b ->
    let left = smart_cat (nderiv c a) b in
    if nullable a then ealt left (nderiv c b) else left
  | R_Star a -> smart_cat (nderiv c a) (R_Star a)

// ----------------------------------------------------------------------------
// Anchored matching (reuses the PROVEN derivative, so inherits matches_correct)
// ----------------------------------------------------------------------------

// Tail-recursive fold of the proven derivative over the word. Extracts to an
// OCaml loop (tail call), so it is stack-safe on long inputs.
let rec run_word (r:regex) (w:list nat) : Tot regex (decreases w) =
  match w with
  | [] -> r
  | c :: rest -> run_word (D.deriv c r) rest

// `matches r w` is provably `mem r w` (Regex.Derivative.matches_correct):
// run_word uses the same deriv, so nullable (run_word r w) = matches r w.
let matches (r:regex) (w:list nat) : bool = nullable (run_word r w)

// Same shape but with the normalized derivative (state-finite fast variant).
let rec run_word_norm (r:regex) (w:list nat) : Tot regex (decreases w) =
  match w with
  | [] -> r
  | c :: rest -> run_word_norm (nderiv c r) rest

let matches_norm (r:regex) (w:list nat) : bool = nullable (run_word_norm r w)

// ----------------------------------------------------------------------------
// Unanchored search
// ----------------------------------------------------------------------------

// The class of all codepoints: one range [0, max_codepoint].
let any_char : regex = R_Ranges [(0, max_codepoint)]
let dot_star : regex = R_Star any_char

// `contains r` : does some substring of the word match r?  Built as .* r .*
// (the standard unanchored-search reduction). Uses the normalized derivative.
let contains (r:regex) : regex = R_Cat dot_star (R_Cat r dot_star)

let search (r:regex) (w:list nat) : bool = matches_norm (contains r) w

// `find_from` : leftmost start index at which `r` matches some prefix of the
// remaining word. Scans positions left to right; returns the first index whose
// suffix is accepted by (r .*) — i.e. r matches a prefix there. Total by
// recursion on the word.
let anchored_prefix (r:regex) : regex = R_Cat r dot_star

let rec find_from (r:regex) (w:list nat) (idx:nat) : Tot (option nat) (decreases w) =
  if matches_norm (anchored_prefix r) w then Some idx
  else match w with
       | [] -> None
       | _ :: rest -> find_from r rest (idx + 1)

let find_match (r:regex) (w:list nat) : option nat = find_from r w 0

// ----------------------------------------------------------------------------
// Codepoint-class alphabet partition
// ----------------------------------------------------------------------------
//
// Every derivative class of a regex is determined by the range endpoints
// appearing in it: two codepoints in the same maximal gap between endpoints
// have identical derivatives. `class_reps r` returns one representative
// codepoint per class (the endpoints themselves plus 0 and max_codepoint),
// which is the finite alphabet the DFA/emptiness closure iterates.

let rec insert_sorted (x:nat) (xs:list nat) : Tot (list nat) (decreases xs) =
  match xs with
  | [] -> [x]
  | y :: ys -> if x = y then xs
               else if x < y then x :: xs
               else y :: insert_sorted x ys

let rec collect_bounds (r:regex) (acc:list nat) : Tot (list nat) (decreases r) =
  match r with
  | R_Empty | R_Eps -> acc
  | R_Ranges rs -> collect_range_bounds rs acc
  | R_Cat a b | R_Alt a b | R_And a b -> collect_bounds b (collect_bounds a acc)
  | R_Not a | R_Star a -> collect_bounds a acc

and collect_range_bounds (rs:list (nat & nat)) (acc:list nat) : Tot (list nat) (decreases rs) =
  match rs with
  | [] -> acc
  | (lo, hi) :: tl ->
    let acc1 = insert_sorted lo acc in
    let acc2 = if hi + 1 <= max_codepoint then insert_sorted (hi + 1) acc1 else acc1 in
    collect_range_bounds tl acc2

// Representative codepoints: 0, every range endpoint, and max_codepoint.
let class_reps (r:regex) : list nat =
  insert_sorted 0 (insert_sorted max_codepoint (collect_bounds r []))

// ----------------------------------------------------------------------------
// Fuel-bounded emptiness over the normalized derivative closure
// ----------------------------------------------------------------------------
//
// GUARANTEE (precise): `is_empty r` explores the reachable normalized-
// derivative states over the class-representative alphabet, breadth-first,
// bounded by `fuel`. It returns:
//   * `false` as soon as it reaches ANY nullable state (a witnessed accepting
//     path exists), OR when `fuel` is exhausted before the closure is complete
//     (conservative "not proven empty" — never a false "empty" claim under the
//     class-partition assumption);
//   * `true` when the closure completes (worklist drains) with no nullable
//     state reached — i.e. no word is accepted.
// The class-partition covering all reachable derivatives, and hence full
// machine-checked soundness, is the Phase-2 obligation (smart_cat_ok /
// smart_star_ok + a class-coverage lemma). This is why is_empty lives in the
// pragmatics layer, not in Regex.Derivative. For the OWL facet-emptiness
// consumer (#299) it is applied to `R_And p (R_Not q)` shapes.

// Structural membership test for the visited/worklist state lists.
let rec mem_state (r:regex) (xs:list regex) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | y :: ys -> (r = y) || mem_state r ys

// Successors of a state over the class-representative alphabet.
let rec succ_states (r:regex) (reps:list nat) : Tot (list regex) (decreases reps) =
  match reps with
  | [] -> []
  | c :: cs -> nderiv c r :: succ_states r cs

// Add successors not already seen to the worklist and visited set.
let rec add_new (news:list regex) (visited worklist:list regex)
  : Tot (list regex & list regex) (decreases news) =
  match news with
  | [] -> (visited, worklist)
  | s :: rest ->
    if mem_state s visited then add_new rest visited worklist
    else add_new rest (s :: visited) (s :: worklist)

// Breadth-first exploration of the derivative closure. Returns true (empty)
// only when the worklist drains with no nullable state seen; false on the
// first nullable state OR on fuel exhaustion (conservative).
let rec bfs_empty (worklist visited:list regex) (reps:list nat) (fuel:nat)
  : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else match worklist with
       | [] -> true
       | s :: rest ->
         if nullable s then false
         else
           let succs = succ_states s reps in
           let visited', worklist' = add_new succs visited rest in
           bfs_empty worklist' visited' reps (fuel - 1)

// Fuel is tied to the regex size (fstar-module-style trap #3: never a bare
// constant that can silently truncate); exhaustion returns the conservative
// `false`. For the shapes the OWL facet check produces, the reachable state
// count is tiny and the closure drains well within this bound.
let is_empty (r:regex) : bool =
  let reps = class_reps r in
  let fuel = 1000 * (size r + 1) in
  bfs_empty [r] [r] reps fuel

// Emptiness of a language INTERSECTION — the operation the OWL facet
// pattern-restriction check needs (#299): are there NO strings matching both
// p and q?  (Applied e.g. to a pattern facet and the complement of an
// enumeration.)
let intersection_empty (p q:regex) : bool = is_empty (R_And p q)

// Does the language of `p` contain that of `q`?  q \ p is empty iff
// L(q) subseteq L(p).  (q AND NOT p) empty.
let subsumes (p q:regex) : bool = is_empty (R_And q (R_Not p))

// ----------------------------------------------------------------------------
// PHASE-2 EQUIVALENCE PROOFS: the ACI-normalized fast path is language-equal
// to the proven Regex.Derivative core.
// ----------------------------------------------------------------------------
//
// Phase 1 shipped `matches_norm` / `is_empty` as SOUND-BY-CONSTRUCTION: they
// re-normalize derivatives with the Exec ACI flatten (`ealt`/`eand`) and
// `smart_cat`, whose language-equality to the plain derivative was not yet
// machine-checked. This section discharges that obligation for the MATCHING
// path: `matches_norm r w <==> mem r w`, with no admit, no --lax, no assume
// val — so `matches_norm` is now as trusted as `Regex.Derivative.matches`.
//
// Structure (mirrors the proven `deriv_correct` in Regex.Derivative):
//   1. `ealt`/`eand` preserve language      (ACI flatten + sorted dedup)
//   2. generic split-shift lemmas relate `cat_try`/`star_try` on (c::w) to a
//      derivative on w, for ANY derivative function meeting the shift spec
//   3. `nderiv_correct : mem (nderiv c r) w <==> mem r (c::w)`  (full AST)
//   4. `matches_norm_correct`, and equality to the proven reference
//
// SCOPE NOTE — `is_empty`/`intersection_empty`/`subsumes` still carry residual
// proof debt: their per-step transition (`nderiv`) is now proven
// language-correct (nderiv_correct below), but full machine-checked emptiness
// SOUNDNESS additionally needs a derivative-CLASS-COVERAGE lemma (that
// `class_reps` and the BFS closure enumerate every reachable derivative up to
// language-equality — the Owens-Reppy-Turon finiteness argument). That
// coverage lemma is NOT proven here; `is_empty` remains sound-by-construction +
// test-cross-checked, its precise fuel/closure guarantee stated at its
// definition. Closing it is the remaining #304 phase-2 item.

// ---- 1a. Alt flatten preserves the union language ----

// Membership against a flattened Alt leaf list = OR over the leaves.
let rec mem_alt_list (xs:list regex) (w:list nat) : Tot bool (decreases xs) =
  match xs with
  | [] -> false
  | x :: rest -> mem x w || mem_alt_list rest w

// Sorted insertion preserves the OR (dedup is language-safe: regex_cmp = 0
// means structural equality, Regex.Syntax.regex_cmp_eq).
let rec insert_regex_ok (x:regex) (xs:list regex) (w:list nat)
  : Lemma (ensures (mem_alt_list (insert_regex x xs) w <==> (mem x w || mem_alt_list xs w)))
          (decreases xs) =
  match xs with
  | [] -> ()
  | y :: ys ->
    let c = regex_cmp x y in
    if c = 0 then regex_cmp_eq x y
    else if c < 0 then ()
    else insert_regex_ok x ys w

let rec alt_flatten_ok (r:regex) (acc:list regex) (w:list nat)
  : Lemma (ensures (mem_alt_list (alt_flatten r acc) w <==> (mem r w || mem_alt_list acc w)))
          (decreases r) =
  match r with
  | R_Empty -> ()
  | R_Alt a b -> alt_flatten_ok b acc w; alt_flatten_ok a (alt_flatten b acc) w
  | _ -> insert_regex_ok r acc w

let rec rebuild_alt_ok (xs:list regex) (w:list nat)
  : Lemma (ensures (mem (rebuild_alt xs) w <==> mem_alt_list xs w)) (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | _ :: rest -> rebuild_alt_ok rest w

// If a universal leaf is present, everything matches (r_universal accepts all).
let rec has_universal_ok (xs:list regex) (w:list nat)
  : Lemma (requires has_universal xs) (ensures mem_alt_list xs w) (decreases xs) =
  match xs with
  | [] -> ()
  | y :: ys -> if y = r_universal then () else has_universal_ok ys w

let ealt_ok (a b:regex) (w:list nat)
  : Lemma (ensures (mem (ealt a b) w <==> (mem a w || mem b w))) =
  let leaves = alt_flatten a (alt_flatten b []) in
  alt_flatten_ok b [] w;
  alt_flatten_ok a (alt_flatten b []) w;
  if has_universal leaves then has_universal_ok leaves w
  else rebuild_alt_ok leaves w

// ---- 1b. And flatten preserves the intersection language ----

let rec mem_and_list (xs:list regex) (w:list nat) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | x :: rest -> mem x w && mem_and_list rest w

let rec insert_regex_and_ok (x:regex) (xs:list regex) (w:list nat)
  : Lemma (ensures (mem_and_list (insert_regex x xs) w <==> (mem x w && mem_and_list xs w)))
          (decreases xs) =
  match xs with
  | [] -> ()
  | y :: ys ->
    let c = regex_cmp x y in
    if c = 0 then regex_cmp_eq x y
    else if c < 0 then ()
    else insert_regex_and_ok x ys w

let rec and_flatten_ok (r:regex) (acc:list regex) (w:list nat)
  : Lemma (ensures (mem_and_list (and_flatten r acc) w <==> (mem r w && mem_and_list acc w)))
          (decreases r) =
  match r with
  | R_And a b -> and_flatten_ok b acc w; and_flatten_ok a (and_flatten b acc) w
  | _ -> if r = r_universal then () else insert_regex_and_ok r acc w

let rec rebuild_and_ok (xs:list regex) (w:list nat)
  : Lemma (ensures (mem (rebuild_and xs) w <==> mem_and_list xs w)) (decreases xs) =
  match xs with
  | [] -> ()
  | [_] -> ()
  | _ :: rest -> rebuild_and_ok rest w

let rec has_empty_ok (xs:list regex) (w:list nat)
  : Lemma (requires has_empty xs) (ensures mem_and_list xs w == false) (decreases xs) =
  match xs with
  | [] -> ()
  | y :: ys -> if R_Empty? y then () else has_empty_ok ys w

let eand_ok (a b:regex) (w:list nat)
  : Lemma (ensures (mem (eand a b) w <==> (mem a w && mem b w))) =
  let leaves = and_flatten a (and_flatten b []) in
  and_flatten_ok b [] w;
  and_flatten_ok a (and_flatten b []) w;
  if has_empty leaves then has_empty_ok leaves w
  else rebuild_and_ok leaves w

// ---- 2. Generic split-shift lemmas (any derivative meeting the spec) ----
//
// These are the Regex.Derivative `cat_shift`/`star_shift`, but abstracted over
// the derivative regex `da` (given `mem da w' <==> mem a (c::w')`) so they work
// for `nderiv` as well as `deriv`. Proof: induction on the split index k,
// exactly as the proven originals.

let rec cat_shift_gen (a b da:regex) (c:nat) (w:list nat) (k:nat)
  : Lemma (requires (forall (w':list nat). mem da w' <==> mem a (c :: w')))
          (ensures (cat_try a b (c :: w) (k + 1) <==>
                    ((mem a [] && mem b (c :: w)) \/ cat_try da b w k)))
          (decreases k) =
  D.take_cons c w k;
  D.drop_cons c w k;
  if k = 0 then (D.take_zero (c :: w); D.drop_zero (c :: w); D.take_zero w; D.drop_zero w)
  else cat_shift_gen a b da c w (k - 1)

let rec star_shift_gen (a da:regex) (c:nat) (w:list nat) (k:nat)
  : Lemma (requires (forall (w':list nat). mem da w' <==> mem a (c :: w')))
          (ensures (star_try a (c :: w) (k + 1) <==> cat_try da (R_Star a) w k))
          (decreases k) =
  D.take_cons c w k;
  D.drop_cons c w k;
  if k = 0 then (D.take_zero w; D.drop_zero w)
  else star_shift_gen a da c w (k - 1)

// Per-word normalized-derivative correctness for Cat and Star, given the IHs.

let nderiv_cat_w (a b:regex) (c:nat) (w:list nat)
  : Lemma (requires (forall (w':list nat). mem (nderiv c a) w' <==> mem a (c :: w')) /\
                    (forall (w':list nat). mem (nderiv c b) w' <==> mem b (c :: w')))
          (ensures (mem (nderiv c (R_Cat a b)) w <==> mem (R_Cat a b) (c :: w))) =
  nullable_correct a;
  cat_shift_gen a b (nderiv c a) c w (L.length w);
  smart_cat_ok (nderiv c a) b w;
  if nullable a then ealt_ok (smart_cat (nderiv c a) b) (nderiv c b) w
  else ()

let nderiv_star_w (a:regex) (c:nat) (w:list nat)
  : Lemma (requires (forall (w':list nat). mem (nderiv c a) w' <==> mem a (c :: w')))
          (ensures (mem (nderiv c (R_Star a)) w <==> mem (R_Star a) (c :: w))) =
  star_shift_gen a (nderiv c a) c w (L.length w);
  smart_cat_ok (nderiv c a) (R_Star a) w

// ---- 3. Normalized-derivative correctness for the FULL AST ----

let rec nderiv_correct (c:nat) (r:regex)
  : Lemma (ensures (forall (w:list nat). mem (nderiv c r) w <==> mem r (c :: w)))
          (decreases r) =
  match r with
  | R_Empty -> ()
  | R_Eps -> ()
  | R_Ranges _ -> ()
  | R_Alt a b ->
    nderiv_correct c a; nderiv_correct c b;
    introduce forall (w:list nat). mem (nderiv c (R_Alt a b)) w <==> mem (R_Alt a b) (c :: w)
    with ealt_ok (nderiv c a) (nderiv c b) w
  | R_And a b ->
    nderiv_correct c a; nderiv_correct c b;
    introduce forall (w:list nat). mem (nderiv c (R_And a b)) w <==> mem (R_And a b) (c :: w)
    with eand_ok (nderiv c a) (nderiv c b) w
  | R_Not a ->
    nderiv_correct c a;
    introduce forall (w:list nat). mem (nderiv c (R_Not a)) w <==> mem (R_Not a) (c :: w)
    with smart_not_ok (nderiv c a) w
  | R_Cat a b ->
    nderiv_correct c a; nderiv_correct c b;
    introduce forall (w:list nat). mem (nderiv c (R_Cat a b)) w <==> mem (R_Cat a b) (c :: w)
    with nderiv_cat_w a b c w
  | R_Star a ->
    nderiv_correct c a;
    introduce forall (w:list nat). mem (nderiv c (R_Star a)) w <==> mem (R_Star a) (c :: w)
    with nderiv_star_w a c w

// ---- 4. matches_norm correctness ----

let rec run_word_norm_correct (r:regex) (w:list nat)
  : Lemma (ensures (mem (run_word_norm r w) [] <==> mem r w)) (decreases w) =
  match w with
  | [] -> ()
  | c :: rest ->
    run_word_norm_correct (nderiv c r) rest;
    nderiv_correct c r

// The Phase-2 theorem: the ACI-normalized fast path denotes exactly the
// reference language `mem`. No admit, no assume val.
let matches_norm_correct (r:regex) (w:list nat)
  : Lemma (ensures (matches_norm r w <==> mem r w)) =
  nullable_correct (run_word_norm r w);
  run_word_norm_correct r w

// Corollary: the fast path agrees with the machine-checked reference
// Regex.Derivative.matches (matches_correct) on every input.
let matches_norm_eq_proven (r:regex) (w:list nat)
  : Lemma (ensures (matches_norm r w <==> D.matches r w)) =
  matches_norm_correct r w;
  D.matches_correct r w
