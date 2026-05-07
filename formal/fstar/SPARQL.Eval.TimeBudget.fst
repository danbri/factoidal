module SPARQL.Eval.TimeBudget

open FStar.All

// Cooperative cancellation primitive for the SPARQL evaluator.
//
// Recovery plan Phase 5 (docs/designissues/2026-05-07-query-planning-
// fstar-recovery.md). Replaces the architecturally-wrong SIGALRM
// per-query timeout (codename Heth3) in factoidal_http.ml with a
// polling discipline: the evaluator checks the budget between yield
// boundaries and bails out cleanly. No process-global signal handlers,
// no surprise `raise Query_timeout` mid-traversal, safe under
// concurrent workers.
//
// Verification surface: a single `assume val now_ms` for a wallclock
// read. Everything else is pure F* — the deadline arithmetic, the
// `is_expired` predicate, the result type. The OCaml realisation of
// `now_ms` is rule-#11(a) acceptable: pure I/O. See issue #202 and
// `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/
// 202_now_ms.sh`.
//
// Heth3 retirement happens in a follow-up PR that consumes this module
// at the call sites in factoidal_http.ml.

// ---------------------------------------------------------------------------
// Wallclock read.
//
// THE ONLY thing OCaml realises in this module. Returns the current
// monotonic-ish millisecond reading. Realised by Unix.gettimeofday in
// the patch. Not strictly monotonic — wallclock jumps are tolerated.
// ---------------------------------------------------------------------------

assume val now_ms : unit -> ML int

// ---------------------------------------------------------------------------
// Budget: wallclock deadline expressed in milliseconds.
//
// `deadline_ms = 0` is the convention for "no budget set" and is
// always treated as "never expired". Any non-zero deadline is the
// absolute wallclock time at which the budget elapses; consumers
// compare the current clock against it.
// ---------------------------------------------------------------------------

type budget = { deadline_ms : int }

let no_budget : budget = { deadline_ms = 0 }

// Construct a budget that expires `secs` seconds from now.
//
// `secs = 0` returns `no_budget` rather than a deadline equal to the
// current clock — the disabled-budget sentinel must round-trip
// through `mk_budget_secs 0`.
let mk_budget_secs (secs : nat) : ML budget =
  if secs = 0 then no_budget
  else
    let now = now_ms () in
    { deadline_ms = now + FStar.Mul.op_Star secs 1000 }

// Same idea, but the caller provides the milliseconds directly. Useful
// for tests that want sub-second budgets without going through `secs`.
let mk_budget_ms (ms : nat) : ML budget =
  if ms = 0 then no_budget
  else
    let now = now_ms () in
    { deadline_ms = now + ms }

// ---------------------------------------------------------------------------
// Budget arithmetic — pure F*.
//
// `is_expired` is total in `(budget, int)`: given the current clock,
// it answers whether the budget has elapsed. Splitting it from `poll`
// keeps the pure logic verifiable and lets callers test it without
// needing to mock the clock.
// ---------------------------------------------------------------------------

let is_expired (b : budget) (now : int) : bool =
  b.deadline_ms <> 0 && now >= b.deadline_ms

// `is_disabled b` iff the budget is the disabled sentinel.
let is_disabled (b : budget) : bool =
  b.deadline_ms = 0

// Lemma: a disabled budget is never expired, regardless of the clock.
let disabled_never_expires (b : budget) (now : int)
  : Lemma (requires is_disabled b)
          (ensures  not (is_expired b now))
  = ()

// Lemma: an enabled budget is expired iff `now` has reached its
// deadline.
let enabled_expires_at_deadline (b : budget) (now : int)
  : Lemma (requires not (is_disabled b))
          (ensures  is_expired b now = (now >= b.deadline_ms))
  = ()

// ---------------------------------------------------------------------------
// ML-effect helper: read the clock + check.
//
// Call this between every yield boundary in the evaluator. Returns
// true iff the budget has expired and the caller should stop.
// ---------------------------------------------------------------------------

let poll (b : budget) : ML bool =
  if is_disabled b then false
  else is_expired b (now_ms ())

// ---------------------------------------------------------------------------
// Budgeted result type.
//
// Wrapper for operations that may bail out under a budget. Lets the
// evaluator return BudgetedExpired without constructing a partial
// result; the caller maps that to HTTP 503 / a 408-style envelope.
// ---------------------------------------------------------------------------

type budgeted (a : Type) =
  | BudgetedOk      : value:a -> budgeted a
  | BudgetedExpired : budgeted a

let bind_budgeted (#a #b : Type) (x : budgeted a) (f : a -> budgeted b)
  : budgeted b =
  match x with
  | BudgetedOk v -> f v
  | BudgetedExpired -> BudgetedExpired

let map_budgeted (#a #b : Type) (f : a -> b) (x : budgeted a) : budgeted b =
  match x with
  | BudgetedOk v -> BudgetedOk (f v)
  | BudgetedExpired -> BudgetedExpired

let is_ok (#a : Type) (x : budgeted a) : bool =
  match x with
  | BudgetedOk _ -> true
  | BudgetedExpired -> false
