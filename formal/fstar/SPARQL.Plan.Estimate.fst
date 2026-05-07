module SPARQL.Plan.Estimate

// Cardinality estimate for a triple pattern in a presence-bitmap-aware
// columnar store.
//
// Recovery plan Phase 4 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md). Retires codename Mem5 — the
// "estimate-from-presence-bitmap" fast path that landed as an OCaml
// shadow in `cottas_ondisk_runtime.sh` and lived for a while inline
// in `cottas_ondisk_estimate` inside `RDF.CottasStore.fst` (lines
// 1331-1371).
//
// What this module owns:
//   - `estimate_pattern_in_rgs` : given (n_candidate_rgs, total_rgs,
//     total_rows), produce the cheap-cardinality estimate that the
//     join-order optimiser consumes. Pure F*.
//   - `EstimateCount` : the result type — exact / approximate / unknown
//     to make the precision regime explicit at the API boundary.
//   - `estimate_unbound_pattern` : the unbound `COUNT(*)` fast path
//     (parquet num_rows is the truth).
//   - Lemma: `estimate_pattern_in_rgs_zero_when_no_candidates` — empty
//     candidates means estimate is exactly 0 (and the underlying truth
//     is also 0; this is exact, not approximate).
//
// What it deliberately does NOT own:
//   - The actual presence-bitmap reading (lives in `PresenceBitmap` /
//     `CompoundPresenceBitmap`).
//   - The candidate-RG construction (lives in `RDF.CottasStore.fst`,
//     deferred to `SPARQL.Plan.AccessPath.fst` in Phase 6).
//   - The store-handle plumbing (the COTTAS store calls this module
//     after it has already opened parquet metadata + run the prune).
//
// This split keeps the estimator pure-and-portable: the same
// `estimate_pattern_in_rgs` formula works for any store that exposes
// (rg-candidate count, total rgs, total rows). The COTTAS-specific
// path that *produces* those three numbers stays in `RDF.CottasStore.fst`
// for now and migrates to `SPARQL.Plan.AccessPath.fst` in Phase 6.
//
// Wiring status: same as the Pruning module — the API surface IS the
// final shape; `RDF.CottasStore.cottas_ondisk_estimate` will swap its
// inline `n_candidates * (total_rows / rg_count)` for a call to
// `estimate_pattern_in_rgs_nat` once the F* extraction toolchain
// version drift is resolved. Today the formula in CottasStore matches
// `estimate_pattern_in_rgs_nat` exactly modulo the `EC_Exact 0` early
// returns, so the swap is semantically a no-op.

module L = FStar.List.Tot

// ---------------------------------------------------------------------------
// EstimateCount — typed result.
//
// `EC_Exact n` : the count is precisely `n` (e.g. unbound pattern with a
// known num_rows).
// `EC_Approx n` : `n` is an order-of-magnitude estimate. The optimiser
// only needs this for join-order; off-by-2x is fine.
// `EC_Unknown` : no estimate was computable. Caller falls back to
// "treat as large".
// ---------------------------------------------------------------------------

type estimate_count =
  | EC_Exact   : nat -> estimate_count
  | EC_Approx  : nat -> estimate_count
  | EC_Unknown : estimate_count

// Project an estimate down to a `nat`. `EC_Unknown` is the sentinel for
// "no info"; we surface it as a large number in callers that only have
// a `nat` API. Pure helper; the typed shape above is the preferred
// surface for callers that handle the three regimes distinctly.
let estimate_count_value (ec : estimate_count) : Tot nat =
  match ec with
  | EC_Exact n  -> n
  | EC_Approx n -> n
  | EC_Unknown  -> 0

let estimate_count_is_exact (ec : estimate_count) : Tot bool =
  match ec with
  | EC_Exact _ -> true
  | _          -> false

// ---------------------------------------------------------------------------
// estimate_pattern_in_rgs — the Mem5 cheap-cardinality formula.
//
// Inputs:
//   - n_candidates : nat — number of rgs that survive the prune.
//   - total_rgs    : nat — total rgs in the corpus.
//   - total_rows   : nat — total rows in the corpus (from parquet
//                    metadata; never requires a data-page decode).
//
// Output:
//   - `EC_Exact 0` when n_candidates = 0 (no rg survives prune; the
//     pattern definitely returns no rows).
//   - `EC_Exact 0` when total_rgs = 0 or total_rows = 0 (empty corpus).
//   - `EC_Approx (n_candidates * (total_rows / total_rgs))` otherwise.
//     The integer-truncating division is intentional — we want a
//     non-negative `nat`, and the optimiser tolerates the rounding.
//
// This replaces the previous walk_candidate_rgs_estimate path which
// decoded all 4 columns of every candidate rg and counted matching
// rows — minutes for a 3.1M-row corpus, microseconds with this. The
// formula is the same one that lived inline in
// `RDF.CottasStore.fst:1349-1371`, lifted to a pure-F* module with a
// typed result.
// ---------------------------------------------------------------------------

let estimate_pattern_in_rgs
  (n_candidates : nat) (total_rgs : nat) (total_rows : nat)
  : Tot estimate_count =
  if n_candidates = 0 then
    EC_Exact 0
  else if total_rgs = 0 then
    EC_Exact 0
  else if total_rows = 0 then
    EC_Exact 0
  else
    let avg_rows_per_rg : nat = total_rows / total_rgs in
    let prod : int = FStar.Mul.op_Star n_candidates avg_rows_per_rg in
    if prod < 0 then
      // Cannot occur under the nonneg inputs above; defensive nat clamp.
      EC_Approx 0
    else
      EC_Approx prod

// ---------------------------------------------------------------------------
// estimate_unbound_pattern — when no column is bound, the count is
// exactly the total number of rows. The parquet metadata has it
// directly; no scan needed.
// ---------------------------------------------------------------------------

let estimate_unbound_pattern (total_rows : nat) : Tot estimate_count =
  EC_Exact total_rows

// ---------------------------------------------------------------------------
// estimate_aggregate — sum a list of per-rg estimates.
//
// Reserved shape for future expansion (e.g. when a store exposes
// per-rg row counts and the planner wants a sharper estimate than
// "n_candidates * avg"). For now, callers pass a list of per-rg
// estimates and we return the sum, as a `nat`.
//
// Pure F*; uses `FStar.List.Tot.fold_left`.
// ---------------------------------------------------------------------------

let rec sum_nats (xs : list nat) : Tot nat (decreases xs) =
  match xs with
  | []       -> 0
  | x :: tl -> x + sum_nats tl

let estimate_aggregate (per_rg : list nat) : Tot estimate_count =
  EC_Approx (sum_nats per_rg)

// ---------------------------------------------------------------------------
// Properties.
// ---------------------------------------------------------------------------

// When no candidate rg survived the prune, the estimate is exactly 0.
// This matters: empty-result patterns short-circuit cleanly through the
// optimiser, avoiding wasted plan time.
let estimate_pattern_in_rgs_zero_when_no_candidates
  (total_rgs : nat) (total_rows : nat)
  : Lemma
    (ensures
      estimate_pattern_in_rgs 0 total_rgs total_rows = EC_Exact 0)
  = ()

// When the corpus has no rgs, the estimate is exactly 0 regardless of
// candidate count (vacuously, no rg can match because none exist).
let estimate_pattern_in_rgs_zero_when_no_rgs
  (n_candidates : nat) (total_rows : nat)
  : Lemma
    (ensures
      estimate_pattern_in_rgs n_candidates 0 total_rows = EC_Exact 0)
  = ()

// When the corpus has no rows, the estimate is exactly 0.
let estimate_pattern_in_rgs_zero_when_no_rows
  (n_candidates : nat) (total_rgs : nat)
  : Lemma
    (ensures
      estimate_pattern_in_rgs n_candidates total_rgs 0 = EC_Exact 0)
  = ()

// ---------------------------------------------------------------------------
// Compatibility shim — flat-nat shape for existing call sites.
//
// `cottas_ondisk_estimate` in `RDF.CottasStore.fst` returns `nat` today.
// Until that call site is updated to thread `estimate_count`, expose a
// thin wrapper that drops the typed wrapper. Marked clearly so future
// migrations can grep for it.
// ---------------------------------------------------------------------------

let estimate_pattern_in_rgs_nat
  (n_candidates : nat) (total_rgs : nat) (total_rows : nat)
  : Tot nat =
  estimate_count_value (estimate_pattern_in_rgs n_candidates total_rgs total_rows)
