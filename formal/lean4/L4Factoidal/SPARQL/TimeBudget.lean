/-
L4Factoidal.SPARQL.TimeBudget — cooperative cancellation.

Port of `formal/fstar/SPARQL.Eval.TimeBudget.fst` (133 lines).

Recovery-plan phase 5: it replaces the SIGALRM per-query timeout in
`factoidal_http.ml` with a polling discipline. The evaluator checks the
budget at yield boundaries and stops cleanly. No process-global signal
handlers, no `raise Query_timeout` in the middle of a traversal, safe
under concurrent workers.

`deadlineMs = 0` is the disabled sentinel and is never expired.

## The one difference, and it is the interesting one

The F\* module carries a single `assume val now_ms : unit -> ML int` —
its only OCaml realisation, acceptable under iron rule #11(a) as pure
I/O, with its own stub patch (`202_now_ms.sh`).

Lean has no `assume val`. The clock is `IO.monoMsNow`, and it is not
mentioned in this module at all: `mkBudgetMs` and `mkBudgetSecs` take
the current reading as an ARGUMENT, and `poll` takes it too. Reading
the clock happens at the caller's edge, once, and the budget logic
stays a total function of its inputs.

That is the same treatment `EvalEnv.now` already gets for §17.4.5.1
`NOW()` in `SPARQL/Expr.lean` — its header states the rule as "read
once, at the edge, and passed in; never an ambient clock call". This
module follows it, so the Lean tree's realisation surface here is
EMPTY where the F\* tree's is one `assume val`.

`ML`-effect `poll` therefore becomes `pollAt`, a pure function of the
budget and a clock reading. A caller writes
`pollAt b (← IO.monoMsNow)`.
-/

namespace L4Factoidal.SPARQL

/-- A wallclock deadline in milliseconds. Not strictly monotonic:
    wallclock jumps are tolerated, as in the F\* source. -/
structure Budget where
  deadlineMs : Int
  deriving Repr, DecidableEq, Inhabited

def noBudget : Budget := { deadlineMs := 0 }

/-- A budget expiring `secs` seconds after the clock reading `now`.

    `secs = 0` returns `noBudget` rather than a deadline equal to
    `now` — the disabled sentinel must round-trip through
    `mkBudgetSecs now 0`, which a deadline of `now` would not do. -/
def mkBudgetSecs (now : Int) (secs : Nat) : Budget :=
  if secs == 0 then noBudget else { deadlineMs := now + (secs : Int) * 1000 }

/-- The same in milliseconds, for sub-second budgets. -/
def mkBudgetMs (now : Int) (ms : Nat) : Budget :=
  if ms == 0 then noBudget else { deadlineMs := now + (ms : Int) }

def Budget.isDisabled (b : Budget) : Bool := b.deadlineMs == 0

/-- Total in `(budget, clock)`. Split from `pollAt` so the logic is
    testable without a clock. -/
def isExpired (b : Budget) (now : Int) : Bool :=
  b.deadlineMs != 0 && now ≥ b.deadlineMs

/-- Call this at every yield boundary. `true` means stop. -/
def pollAt (b : Budget) (now : Int) : Bool :=
  if b.isDisabled then false else isExpired b now

/-! ## The two properties -/

theorem disabled_never_expires (b : Budget) (now : Int) (h : b.isDisabled = true) :
    isExpired b now = false := by
  simp [Budget.isDisabled] at h
  simp [isExpired, h]

theorem enabled_expires_at_deadline (b : Budget) (now : Int)
    (h : b.isDisabled = false) :
    isExpired b now = decide (now ≥ b.deadlineMs) := by
  simp [Budget.isDisabled] at h
  simp [isExpired, h]

/-! ## The budgeted result

Lets the evaluator report expiry without constructing a partial result.
The caller maps `expired` to its own envelope. -/

inductive Budgeted (α : Type) where
  | ok (value : α)
  | expired
  deriving Repr, DecidableEq, Inhabited

def bindBudgeted {α β : Type} (x : Budgeted α) (f : α → Budgeted β) : Budgeted β :=
  match x with
  | .ok v    => f v
  | .expired => .expired

def mapBudgeted {α β : Type} (f : α → β) (x : Budgeted α) : Budgeted β :=
  match x with
  | .ok v    => .ok (f v)
  | .expired => .expired

def Budgeted.isOk {α : Type} : Budgeted α → Bool
  | .ok _    => true
  | .expired => false

/-! ## Build-time checks

### The disabled sentinel round-trips

`mkBudgetSecs now 0` must be `noBudget`, not a deadline equal to `now`.
A deadline equal to `now` is EXPIRED, so getting this backwards turns
"no timeout" into "already timed out". -/

#guard mkBudgetSecs 1000 0 == noBudget
#guard mkBudgetMs 1000 0 == noBudget
#guard noBudget.isDisabled
#guard !pollAt (mkBudgetSecs 1000 0) 999999999

/-! ### An enabled budget expires at its deadline, not before -/

#guard (mkBudgetSecs 1000 5).deadlineMs == 6000
#guard (mkBudgetMs 1000 500).deadlineMs == 1500
#guard !pollAt (mkBudgetSecs 1000 5) 5999
#guard pollAt (mkBudgetSecs 1000 5) 6000
#guard pollAt (mkBudgetSecs 1000 5) 6001

/-! ### A clock that jumps BACKWARD un-expires the budget rather than
    trapping it — the tolerated-jump behaviour the F\* header states. -/

#guard pollAt (mkBudgetSecs 1000 5) 7000
#guard !pollAt (mkBudgetSecs 1000 5) 3000

/-! ### The result type -/

#guard (Budgeted.ok 5).isOk
#guard !(Budgeted.expired : Budgeted Nat).isOk
#guard bindBudgeted (Budgeted.ok 5) (fun n => Budgeted.ok (n + 1)) == Budgeted.ok 6
#guard bindBudgeted (Budgeted.expired : Budgeted Nat)
        (fun n => Budgeted.ok (n + 1)) == Budgeted.expired
#guard mapBudgeted (· + 1) (Budgeted.ok 5) == Budgeted.ok 6
#guard mapBudgeted (· + 1) (Budgeted.expired : Budgeted Nat) == Budgeted.expired

/-! Expiry is absorbing: once expired, no later step can produce a
    value. That is what lets the evaluator stop without unwinding. -/

#guard !(bindBudgeted (Budgeted.expired : Budgeted Nat)
          (fun n => Budgeted.ok (n + 1))).isOk

#print axioms disabled_never_expires
#print axioms enabled_expires_at_deadline

end L4Factoidal.SPARQL
