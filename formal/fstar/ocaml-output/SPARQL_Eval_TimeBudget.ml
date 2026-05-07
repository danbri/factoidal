open Prims
let (now_ms : unit -> Prims.int) =
  (* Issue #202: rule-#11(a) pure-I/O realisation.
     Unix.gettimeofday returns seconds-as-float; multiply to ms,
     truncate, and lift to Prims.int (Z.t). Wallclock jumps are
     tolerated -- only affects polling cadence, not correctness. *)
  fun uu___ ->
    Z.of_int (int_of_float (Unix.gettimeofday () *. 1000.0))
type budget = {
  deadline_ms: Prims.int }
let (__proj__Mkbudget__item__deadline_ms : budget -> Prims.int) =
  fun projectee -> match projectee with | { deadline_ms;_} -> deadline_ms
let (no_budget : budget) = { deadline_ms = Prims.int_zero }
let (mk_budget_secs : Prims.nat -> budget) =
  fun secs ->
    if secs = Prims.int_zero
    then no_budget
    else
      (let now = now_ms () in
       { deadline_ms = (now + (secs * (Prims.of_int (1000)))) })
let (mk_budget_ms : Prims.nat -> budget) =
  fun ms ->
    if ms = Prims.int_zero
    then no_budget
    else (let now = now_ms () in { deadline_ms = (now + ms) })
let (is_expired : budget -> Prims.int -> Prims.bool) =
  fun b ->
    fun now -> (b.deadline_ms <> Prims.int_zero) && (now >= b.deadline_ms)
let (is_disabled : budget -> Prims.bool) =
  fun b -> b.deadline_ms = Prims.int_zero
let (poll : budget -> Prims.bool) =
  fun b ->
    if is_disabled b
    then false
    else (let uu___1 = now_ms () in is_expired b uu___1)
type 'a budgeted =
  | BudgetedOk of 'a 
  | BudgetedExpired 
let uu___is_BudgetedOk : 'a . 'a budgeted -> Prims.bool =
  fun projectee ->
    match projectee with | BudgetedOk value -> true | uu___ -> false
let __proj__BudgetedOk__item__value : 'a . 'a budgeted -> 'a =
  fun projectee -> match projectee with | BudgetedOk value -> value
let uu___is_BudgetedExpired : 'a . 'a budgeted -> Prims.bool =
  fun projectee ->
    match projectee with | BudgetedExpired -> true | uu___ -> false
let bind_budgeted : 'a 'b . 'a budgeted -> ('a -> 'b budgeted) -> 'b budgeted
  =
  fun x ->
    fun f ->
      match x with | BudgetedOk v -> f v | BudgetedExpired -> BudgetedExpired
let map_budgeted : 'a 'b . ('a -> 'b) -> 'a budgeted -> 'b budgeted =
  fun f ->
    fun x ->
      match x with
      | BudgetedOk v -> BudgetedOk (f v)
      | BudgetedExpired -> BudgetedExpired
let is_ok : 'a . 'a budgeted -> Prims.bool =
  fun x -> match x with | BudgetedOk uu___ -> true | BudgetedExpired -> false
