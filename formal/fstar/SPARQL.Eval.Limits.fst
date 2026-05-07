module SPARQL.Eval.Limits

// Row-cap circuit breaker for the SPARQL evaluator. Pure F*.
//
// Recovery plan Phase 5 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md). Retires codename Tav5 — the `--max-rows N`
// circuit breaker that lives in `factoidal_http.ml` as the
// `exceeds_cap` / `result_cap_response` pair. The OCaml-side decision
// "should this oversized result set become an HTTP 413?" is the
// rendering glue; the policy "stop after N rows" belongs in F*.
//
// This module exposes:
//   - `row_cap` : a tiny record describing the cap, with `0 = unlimited`.
//   - `cap_reached` : the predicate the caller polls between rows.
//   - `take_capped` : a pure list combinator that keeps at most
//     `c.max_rows` elements of its input list.
//   - `take_capped_length_le_cap` : the bound is honoured when the cap
//     is enabled.
//   - `take_capped_unlimited_id` : a disabled cap is the identity.
//
// The `take_capped` shape matches the existing OCaml call sites in
// `factoidal_http.ml`: `run_query` materialises the row list and then
// applies the cap policy. A streaming combinator (lazy or
// continuation-passing) is a future extension; the materialised-list
// shape is what the current evaluator returns and what we need to
// retire today.

module L = FStar.List.Tot

// ---------------------------------------------------------------------------
// Cap value.
//
// `max_rows = 0` is the "unlimited" sentinel. The convention matches
// the existing OCaml-side `cap <= 0` test: zero means "no cap".
// ---------------------------------------------------------------------------

type row_cap = { max_rows : nat }

let no_cap : row_cap = { max_rows = 0 }

let mk_cap (n : nat) : row_cap = { max_rows = n }

// True iff the cap is enabled.
let is_enabled (c : row_cap) : bool =
  c.max_rows <> 0

// True iff the cap is enabled and `n_rows` has reached or exceeded it.
// Mirrors the shape of `exceeds_cap` in factoidal_http.ml but lives
// here so the policy is a single F* predicate.
let cap_reached (c : row_cap) (n_rows : nat) : bool =
  is_enabled c && n_rows >= c.max_rows

// ---------------------------------------------------------------------------
// take_capped : keep only the first `c.max_rows` elements, or all of
// them if the cap is disabled.
//
// Pure, total, structurally recursive on `rows`. The `taken_so_far`
// accumulator threads how many we have already kept; this avoids
// recomputing `List.length` each step.
// ---------------------------------------------------------------------------

let rec take_capped_aux (#a : Type) (c : row_cap)
                        (rows : list a) (taken_so_far : nat)
  : Tot (list a) (decreases rows) =
  match rows with
  | [] -> []
  | x :: rest ->
    if is_enabled c && taken_so_far >= c.max_rows then []
    else x :: take_capped_aux c rest (taken_so_far + 1)

let take_capped (#a : Type) (c : row_cap) (rows : list a) : Tot (list a) =
  take_capped_aux c rows 0

// ---------------------------------------------------------------------------
// Properties.
// ---------------------------------------------------------------------------

// Helper lemma: if `take_capped_aux` is called with `taken_so_far`
// already at or past the cap (and the cap is enabled), it returns the
// empty list. Used in the length-bound proof below. Non-recursive —
// both list shapes evaluate the predicate guard the same way.
let take_capped_aux_at_cap (#a : Type) (c : row_cap)
                           (rows : list a) (taken : nat)
  : Lemma (requires is_enabled c /\ taken >= c.max_rows)
          (ensures  take_capped_aux c rows taken == []) =
  match rows with
  | [] -> ()
  | _ :: _ -> ()

// Helper lemma: bound on `take_capped_aux` when the cap is enabled.
// `length (take_capped_aux c rs taken) + taken <= max c.max_rows taken`.
// Proves that the result plus what was already taken cannot exceed
// the cap (or `taken` if `taken` already overshoots).
let rec take_capped_aux_length_le (#a : Type) (c : row_cap)
                                  (rows : list a) (taken : nat)
  : Lemma (requires is_enabled c)
          (ensures
            (let r = take_capped_aux c rows taken in
             if taken >= c.max_rows then L.length r = 0
             else L.length r + taken <= c.max_rows))
          (decreases rows) =
  match rows with
  | [] -> ()
  | _ :: rest ->
    if taken >= c.max_rows then
      take_capped_aux_at_cap c rows taken
    else
      take_capped_aux_length_le c rest (taken + 1)

// Top-level property: `length (take_capped c rs) <= c.max_rows` when
// the cap is enabled.
let take_capped_length_le_cap (#a : Type) (c : row_cap) (rows : list a)
  : Lemma (requires is_enabled c)
          (ensures  L.length (take_capped c rows) <= c.max_rows) =
  take_capped_aux_length_le c rows 0

// When the cap is disabled, `take_capped` is the identity.
let rec take_capped_aux_unlimited (#a : Type) (rows : list a) (taken : nat)
  : Lemma (requires True)
          (ensures  take_capped_aux no_cap rows taken == rows)
          (decreases rows) =
  match rows with
  | [] -> ()
  | _ :: rest -> take_capped_aux_unlimited rest (taken + 1)

let take_capped_unlimited_id (#a : Type) (rows : list a)
  : Lemma (ensures take_capped no_cap rows == rows) =
  take_capped_aux_unlimited rows 0
