open Prims
let now_ms (uu___ : unit) : Prims.int=
  (* Issue #202: rule-#11(a) pure-I/O realisation.
     Unix.gettimeofday returns seconds-as-float; multiply to ms,
     truncate, and lift to Prims.int (Z.t). Wallclock jumps are
     tolerated -- only affects polling cadence, not correctness. *)
  Z.of_int (int_of_float (Unix.gettimeofday () *. 1000.0))
type budget = {
  deadline_ms: Prims.int }
let __proj__Mkbudget__item__deadline_ms (projectee : budget) : Prims.int=
  match projectee with | { deadline_ms;_} -> deadline_ms
let no_budget : budget= { deadline_ms = Prims.int_zero }
let mk_budget_secs (secs : Prims.nat) : budget=
  if secs = Prims.int_zero
  then no_budget
  else
    (let now = now_ms () in
     { deadline_ms = (now + (secs * (Prims.of_int (1000)))) })
let mk_budget_ms (ms : Prims.nat) : budget=
  if ms = Prims.int_zero
  then no_budget
  else (let now = now_ms () in { deadline_ms = (now + ms) })
let is_expired (b : budget) (now : Prims.int) : Prims.bool=
  (b.deadline_ms <> Prims.int_zero) && (now >= b.deadline_ms)
let is_disabled (b : budget) : Prims.bool= b.deadline_ms = Prims.int_zero
let poll (b : budget) : Prims.bool=
  if is_disabled b
  then false
  else (let uu___1 = now_ms () in is_expired b uu___1)
type 'a budgeted =
  | BudgetedOk of 'a 
  | BudgetedExpired 
let uu___is_BudgetedOk (projectee : 'a budgeted) : Prims.bool=
  match projectee with | BudgetedOk value -> true | uu___ -> false
let __proj__BudgetedOk__item__value (projectee : 'a budgeted) : 'a=
  match projectee with | BudgetedOk value -> value
let uu___is_BudgetedExpired (projectee : 'a budgeted) : Prims.bool=
  match projectee with | BudgetedExpired -> true | uu___ -> false
let bind_budgeted (x : 'a budgeted) (f : 'a -> 'b budgeted) : 'b budgeted=
  match x with | BudgetedOk v -> f v | BudgetedExpired -> BudgetedExpired
let map_budgeted (f : 'a -> 'b) (x : 'a budgeted) : 'b budgeted=
  match x with
  | BudgetedOk v -> BudgetedOk (f v)
  | BudgetedExpired -> BudgetedExpired
let is_ok (x : 'a budgeted) : Prims.bool=
  match x with | BudgetedOk uu___ -> true | BudgetedExpired -> false
