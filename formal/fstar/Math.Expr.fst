module Math.Expr

// Domain-neutral symbolic-math foundation, intended to be the shared
// CAS-agnostic core: a symbolic expression AST (numbers, symbols, and
// n-ary function-application nodes), an exact rational value type with
// its arithmetic, and a fuel-bounded numeric evaluator. This is an
// independent F* implementation of standard computer-algebra data
// structures -- no code, API, or algorithm is ported from SymPy or any
// other CAS. NOTHING in this module is MathML-specific; the Content
// MathML front-end (MathML.Content.fst) maps its xml_node trees into
// Math.Expr.expr and reuses `eval` here, and a future verified CAS
// (simplify / differentiate / substitute / expand) will pattern-match
// directly on `expr`.
//
// Design notes for symbolic manipulation (not just evaluation):
//   * Operators are NOT baked-in AST variants. `plus`, `times`,
//     `power`, `root`, `sin`, `ln`, ... are all E_App nodes carrying
//     their function name as data, so `differentiate` can pattern-match
//     the name later. Convenience constructors (e_add/e_mul/e_pow/e_neg)
//     build those E_App nodes but add no new variant.
//   * Constructors do NOT fold constants: e_add (E_Int 2) (E_Int 3) is
//     the tree E_App "plus" [E_Int 2; E_Int 3], NOT E_Int 5. Constant
//     folding is the job of `eval` (numeric) or a future `simplify`
//     (canonical form), kept as a separate step.
//   * Number leaves stay honest about exactness: integers and rationals
//     are represented exactly. Genuinely irrational results (sin 1,
//     ln 2, sqrt 2) are never fabricated as a float — `eval` returns
//     MV_Undef for them, so exactness is never silently lost.

open FStar.String
open FStar.List.Tot

(* ================================================================ *)
(* Exact value type                                                  *)
(* ================================================================ *)

type mvalue =
  // exact rational num/den; invariant maintained by mk_rat: den > 0
  // and gcd(|num|,den) = 1. Integers are den = 1.
  | MV_Rat  : num:int -> den:int -> mvalue
  | MV_Bool : b:bool -> mvalue
  // an explicit "cannot evaluate exactly" marker; reason is diagnostic
  | MV_Undef : reason:string -> mvalue

(* ================================================================ *)
(* Integer helpers                                                   *)
(* ================================================================ *)

let iabs (n:int) : nat = if n < 0 then 0 - n else n

let rec ipow (base:int) (e:nat) : Tot int (decreases e) =
  if e = 0 then 1 else op_Multiply base (ipow base (e - 1))

let rec pow10 (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 10 (pow10 (n - 1))

// Euclid's algorithm on naturals. Terminates because (a % b) < b for
// b > 0 (z3 discharges the decreases obligation from the modulo range
// axiom, since the b = 0 case is handled first).
let rec nat_gcd (a:nat) (b:nat) : Tot nat (decreases b) =
  if b = 0 then a else nat_gcd b (a % b)

let rec ifact (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply n (ifact (n - 1))

(* ================================================================ *)
(* Rational smart constructor + arithmetic                           *)
(* ================================================================ *)

// Normalise sign (denominator positive) and reduce to lowest terms.
// Division by zero denominator -> MV_Undef, never a bogus number.
let mk_rat (n:int) (d:int) : mvalue =
  if d = 0 then MV_Undef "division-by-zero"
  else
    let sgn = if d < 0 then (-1) else 1 in
    let n' = op_Multiply sgn n in
    let d' = op_Multiply sgn d in
    // d' > 0 here
    let g0 = nat_gcd (iabs n') (iabs d') in
    let g = if g0 = 0 then 1 else g0 in
    MV_Rat (n' / g) (d' / g)

let is_rat (v:mvalue) : bool = MV_Rat? v

// Binary rational arithmetic with error propagation. A non-rational
// operand yields a type error; MV_Undef inputs propagate their reason.
let rat_bin (f:(int -> int -> int -> int -> mvalue)) (a:mvalue) (b:mvalue) : mvalue =
  match a, b with
  | MV_Undef r, _ -> MV_Undef r
  | _, MV_Undef r -> MV_Undef r
  | MV_Rat n1 d1, MV_Rat n2 d2 -> f n1 d1 n2 d2
  | _ -> MV_Undef "type-error-expected-number"

let m_add (a:mvalue) (b:mvalue) : mvalue =
  rat_bin (fun n1 d1 n2 d2 ->
    mk_rat (op_Multiply n1 d2 + op_Multiply n2 d1) (op_Multiply d1 d2)) a b

let m_sub (a:mvalue) (b:mvalue) : mvalue =
  rat_bin (fun n1 d1 n2 d2 ->
    mk_rat (op_Multiply n1 d2 - op_Multiply n2 d1) (op_Multiply d1 d2)) a b

let m_mul (a:mvalue) (b:mvalue) : mvalue =
  rat_bin (fun n1 d1 n2 d2 ->
    mk_rat (op_Multiply n1 n2) (op_Multiply d1 d2)) a b

let m_div (a:mvalue) (b:mvalue) : mvalue =
  rat_bin (fun n1 d1 n2 d2 ->
    if n2 = 0 then MV_Undef "division-by-zero"
    else mk_rat (op_Multiply n1 d2) (op_Multiply d1 n2)) a b

let m_neg (a:mvalue) : mvalue =
  match a with
  | MV_Rat n d -> MV_Rat (0 - n) d
  | MV_Undef r -> MV_Undef r
  | _ -> MV_Undef "type-error-expected-number"

let m_abs (a:mvalue) : mvalue =
  match a with
  | MV_Rat n d -> MV_Rat (iabs n) d
  | MV_Undef r -> MV_Undef r
  | _ -> MV_Undef "type-error-expected-number"

// Integer test: rational with denominator 1.
let as_int (v:mvalue) : option int =
  match v with
  | MV_Rat n 1 -> Some n
  | _ -> None

(* ---------------------------------------------------------------- *)
(* Power (integer exponent only — exact), root (exact only)         *)
(* ---------------------------------------------------------------- *)

let m_pow (base:mvalue) (ex:mvalue) : mvalue =
  match base, ex with
  | MV_Undef r, _ -> MV_Undef r
  | _, MV_Undef r -> MV_Undef r
  | MV_Rat p q, _ ->
    (match as_int ex with
     | None -> MV_Undef "non-integer-exponent-not-exact"
     | Some e ->
       let ke = iabs e in
       let pk = ipow p ke in
       let qk = ipow q ke in
       if e >= 0 then mk_rat pk qk
       else if p = 0 then MV_Undef "zero-to-negative-power"
       else mk_rat qk pk)
  | _ -> MV_Undef "type-error-expected-number"

// Integer k-th root of a natural number m (k >= 1): the r with r^k = m,
// or None if m is not a perfect k-th power. Bounded search r in [0..m].
let rec find_int_root (m:nat) (k:nat) (r:nat) (fuel:nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else
    let p = ipow r k in
    if p = m then Some r
    else if p > m then None
    else find_int_root m k (r + 1) (fuel - 1)

// Exact k-th root of a reduced rational p/q. Both |p| and q must be
// perfect k-th powers; even degrees require p >= 0. Anything inexact
// (e.g. root 2 of 2) is MV_Undef, never approximated.
let m_root (deg:mvalue) (arg:mvalue) : mvalue =
  match deg, arg with
  | MV_Undef r, _ -> MV_Undef r
  | _, MV_Undef r -> MV_Undef r
  | _, MV_Rat p q ->
    (match as_int deg with
     | None -> MV_Undef "non-integer-root-degree"
     | Some k ->
       if k <= 0 then MV_Undef "nonpositive-root-degree"
       else
         let kn : nat = k in
         let neg = p < 0 in
         if neg && (kn % 2 = 0) then MV_Undef "even-root-of-negative"
         else
           let ap = iabs p in
           let aq = iabs q in
           (match find_int_root ap kn 0 (ap + 1), find_int_root aq kn 0 (aq + 1) with
            | Some rp, Some rq ->
              let rp' = if neg then 0 - rp else rp in
              mk_rat rp' rq
            | _ -> MV_Undef "root-not-exact")
     )
  | _ -> MV_Undef "type-error-expected-number"

(* ---------------------------------------------------------------- *)
(* Integer-only operators: quotient, rem, factorial, gcd            *)
(*                                                                   *)
(* quotient/rem use truncation toward zero (F* op_Division /         *)
(* op_Modulus). Callers that need floor semantics on mixed signs     *)
(* must adapt; on nonnegative operands the two conventions agree.    *)
(* ---------------------------------------------------------------- *)

let m_quotient (a:mvalue) (b:mvalue) : mvalue =
  match as_int a, as_int b, a, b with
  | _, _, MV_Undef r, _ -> MV_Undef r
  | _, _, _, MV_Undef r -> MV_Undef r
  | Some x, Some y, _, _ ->
    if y = 0 then MV_Undef "division-by-zero" else MV_Rat (x / y) 1
  | _ -> MV_Undef "quotient-requires-integers"

let m_rem (a:mvalue) (b:mvalue) : mvalue =
  match as_int a, as_int b, a, b with
  | _, _, MV_Undef r, _ -> MV_Undef r
  | _, _, _, MV_Undef r -> MV_Undef r
  | Some x, Some y, _, _ ->
    if y = 0 then MV_Undef "division-by-zero" else MV_Rat (x % y) 1
  | _ -> MV_Undef "rem-requires-integers"

let m_factorial (a:mvalue) : mvalue =
  match a with
  | MV_Undef r -> MV_Undef r
  | _ ->
    (match as_int a with
     | Some x -> if x < 0 then MV_Undef "factorial-of-negative"
                 else MV_Rat (ifact x) 1
     | None -> MV_Undef "factorial-requires-integer")

let m_gcd2 (a:mvalue) (b:mvalue) : mvalue =
  match as_int a, as_int b, a, b with
  | _, _, MV_Undef r, _ -> MV_Undef r
  | _, _, _, MV_Undef r -> MV_Undef r
  | Some x, Some y, _, _ -> MV_Rat (nat_gcd (iabs x) (iabs y)) 1
  | _ -> MV_Undef "gcd-requires-integers"

(* ---------------------------------------------------------------- *)
(* Comparison (cross-multiplication; denominators are positive)     *)
(* ---------------------------------------------------------------- *)

// Some (-1|0|1) for a<b|a=b|a>b, or None if not both rational.
let rat_cmp (a:mvalue) (b:mvalue) : option int =
  match a, b with
  | MV_Rat n1 d1, MV_Rat n2 d2 ->
    let lhs = op_Multiply n1 d2 in
    let rhs = op_Multiply n2 d1 in
    if lhs < rhs then Some (-1)
    else if lhs = rhs then Some 0
    else Some 1
  | _ -> None

let m_max (a:mvalue) (b:mvalue) : mvalue =
  match rat_cmp a b with
  | Some c -> if c < 0 then b else a
  | None -> (match a, b with
             | MV_Undef r, _ -> MV_Undef r
             | _, MV_Undef r -> MV_Undef r
             | _ -> MV_Undef "type-error-expected-number")

let m_min (a:mvalue) (b:mvalue) : mvalue =
  match rat_cmp a b with
  | Some c -> if c > 0 then b else a
  | None -> (match a, b with
             | MV_Undef r, _ -> MV_Undef r
             | _, MV_Undef r -> MV_Undef r
             | _ -> MV_Undef "type-error-expected-number")

(* ================================================================ *)
(* Exact decimal-literal parsing (domain-neutral)                    *)
(* ================================================================ *)

let is_ws_char (c:FStar.Char.char) : bool =
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

let rec drop_ws (l:list FStar.Char.char) : Tot (list FStar.Char.char) (decreases l) =
  match l with
  | c :: t -> if is_ws_char c then drop_ws t else l
  | [] -> []

let trim_chars (l:list FStar.Char.char) : list FStar.Char.char =
  List.Tot.rev (drop_ws (List.Tot.rev (drop_ws l)))

let trim_str (s:string) : string =
  String.string_of_list (trim_chars (String.list_of_string s))

let is_digit_char (c:FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  n >= 0x30 && n <= 0x39

let digit_val (c:FStar.Char.char) : int = FStar.Char.int_of_char c - 0x30

// Read a maximal run of decimal digits; returns (value, count, rest).
let rec read_digits (l:list FStar.Char.char) (acc:int) (cnt:nat)
  : Tot (int & nat & list FStar.Char.char) (decreases l) =
  match l with
  | c :: rest ->
    if is_digit_char c then read_digits rest (op_Multiply acc 10 + digit_val c) (cnt + 1)
    else (acc, cnt, l)
  | [] -> (acc, cnt, l)

// Parse a decimal literal (optional sign, integer/fraction, optional
// E-notation) into an exact rational. E-notation stays exact because
// 10^k is rational. Any leftover garbage -> MV_Undef.
let parse_decimal (s:string) : mvalue =
  let cs0 = trim_chars (String.list_of_string s) in
  match cs0 with
  | [] -> MV_Undef "empty-number"
  | _ ->
    let (neg, cs1) =
      match cs0 with
      | '-' :: t -> (true, t)
      | '+' :: t -> (false, t)
      | _ -> (false, cs0)
    in
    let (ip, ipc, cs2) = read_digits cs1 0 0 in
    let (fp, fpc, cs3) =
      match cs2 with
      | '.' :: t -> read_digits t 0 0
      | _ -> (0, 0, cs2)
    in
    if ipc + fpc = 0 then MV_Undef "not-a-number"
    else
      let (exp, cs4) =
        match cs3 with
        | 'e' :: t ->
          let (esgn, t1) = (match t with '-' :: u -> (-1, u) | '+' :: u -> (1, u) | _ -> (1, t)) in
          let (ev, evc, t2) = read_digits t1 0 0 in
          if evc = 0 then (0, cs3) else (op_Multiply esgn ev, t2)
        | 'E' :: t ->
          let (esgn, t1) = (match t with '-' :: u -> (-1, u) | '+' :: u -> (1, u) | _ -> (1, t)) in
          let (ev, evc, t2) = read_digits t1 0 0 in
          if evc = 0 then (0, cs3) else (op_Multiply esgn ev, t2)
        | _ -> (0, cs3)
      in
      (match cs4 with
       | [] ->
         let mant0 = op_Multiply ip (pow10 fpc) + fp in
         let mant = if neg then 0 - mant0 else mant0 in
         let net = exp - fpc in
         if net >= 0 then mk_rat (op_Multiply mant (pow10 net)) 1
         else mk_rat mant (pow10 (0 - net))
       | _ -> MV_Undef "trailing-garbage-in-number")

(* ================================================================ *)
(* Symbolic expression AST                                           *)
(* ================================================================ *)

type expr =
  | E_Int  : n:int -> expr                       // exact integer literal
  | E_Rat  : num:int -> den:int -> expr          // exact rational literal num/den
  | E_Bool : b:bool -> expr                      // boolean literal
  | E_Sym  : name:string -> expr                 // symbol / variable
  | E_App  : fn:string -> args:list expr -> expr // n-ary function application

// Convenience constructors. These build E_App nodes (operators are NOT
// baked-in variants) and DO NOT fold constants — that is `eval`'s or a
// future `simplify`'s job.
let e_add (a:expr) (b:expr) : expr = E_App "plus" [a; b]
let e_mul (a:expr) (b:expr) : expr = E_App "times" [a; b]
let e_pow (a:expr) (b:expr) : expr = E_App "power" [a; b]
let e_neg (a:expr) : expr = E_App "minus" [a]

// Lift an exact value into an expression literal (used when a
// front-end has already parsed a number). A non-exact / error value
// becomes a nullary function node that `eval` reports as undefined,
// so exactness is never silently faked.
let value_to_lit (v:mvalue) : expr =
  match v with
  | MV_Rat n 1 -> E_Int n
  | MV_Rat n d -> E_Rat n d
  | MV_Bool b -> E_Bool b
  | MV_Undef r -> E_App "number-parse-error" []

(* ================================================================ *)
(* n-ary folds over evaluated argument lists                         *)
(* ================================================================ *)

let rec fold_bin (f:(mvalue -> mvalue -> mvalue)) (acc:mvalue) (args:list mvalue)
  : Tot mvalue (decreases args) =
  match args with
  | [] -> acc
  | a :: rest -> fold_bin f (f acc a) rest

// Chained relation: op holds between every consecutive pair.
let rec relation_chain (ok:(int -> bool)) (args:list mvalue)
  : Tot mvalue (decreases args) =
  match args with
  | [] -> MV_Bool true
  | [_] -> MV_Bool true
  | a :: b :: rest ->
    (match rat_cmp a b with
     | Some c -> if ok c then relation_chain ok (b :: rest) else MV_Bool false
     | None ->
       (match a, b with
        | MV_Undef r, _ -> MV_Undef r
        | _, MV_Undef r -> MV_Undef r
        | _ -> MV_Undef "type-error-in-relation"))

(* ================================================================ *)
(* Function-name dispatch (pure: operates on evaluated arg values)   *)
(*                                                                   *)
(* Every operator is dispatched by its function name (the E_App fn    *)
(* field), matching the domain-neutral names a front-end maps onto.   *)
(* `root` takes [radicand] (default degree 2) or [degree; radicand].  *)
(* Irrational / unknown functions return an explicit MV_Undef,        *)
(* never an approximation.                                            *)
(* ================================================================ *)

let apply_fn (fn:string) (args:list mvalue) : mvalue =
  match fn with
  | "plus"  -> fold_bin m_add (MV_Rat 0 1) args
  | "times" -> fold_bin m_mul (MV_Rat 1 1) args
  | "minus" ->
    (match args with
     | [a] -> m_neg a
     | [a; b] -> m_sub a b
     | _ -> MV_Undef "minus-arity")
  | "divide" ->
    (match args with [a; b] -> m_div a b | _ -> MV_Undef "divide-arity")
  | "power" ->
    (match args with [a; b] -> m_pow a b | _ -> MV_Undef "power-arity")
  | "root" ->
    (match args with
     | [x] -> m_root (MV_Rat 2 1) x
     | [d; x] -> m_root d x
     | _ -> MV_Undef "root-arity")
  | "abs" ->
    (match args with [a] -> m_abs a | _ -> MV_Undef "abs-arity")
  | "quotient" ->
    (match args with [a; b] -> m_quotient a b | _ -> MV_Undef "quotient-arity")
  | "rem" ->
    (match args with [a; b] -> m_rem a b | _ -> MV_Undef "rem-arity")
  | "factorial" ->
    (match args with [a] -> m_factorial a | _ -> MV_Undef "factorial-arity")
  | "gcd" ->
    (match args with
     | [] -> MV_Rat 0 1
     | a :: rest -> fold_bin m_gcd2 a rest)
  | "max" ->
    (match args with [] -> MV_Undef "max-empty" | a :: rest -> fold_bin m_max a rest)
  | "min" ->
    (match args with [] -> MV_Undef "min-empty" | a :: rest -> fold_bin m_min a rest)
  | "eq"  -> relation_chain (fun c -> c = 0) args
  | "neq" ->
    (match args with
     | [a; b] -> (match rat_cmp a b with
                  | Some c -> MV_Bool (c <> 0)
                  | None -> (match a, b with
                             | MV_Undef r, _ -> MV_Undef r
                             | _, MV_Undef r -> MV_Undef r
                             | _ -> MV_Undef "type-error-in-relation"))
     | _ -> MV_Undef "neq-arity")
  | "lt"  -> relation_chain (fun c -> c < 0) args
  | "gt"  -> relation_chain (fun c -> c > 0) args
  | "leq" -> relation_chain (fun c -> c <= 0) args
  | "geq" -> relation_chain (fun c -> c >= 0) args
  | _ -> MV_Undef (String.concat "" ["unsupported-function:"; fn])

(* ================================================================ *)
(* Fuel-bounded numeric evaluator over expr                          *)
(*                                                                   *)
(* Lexicographic decreases: eval = %[fuel; 0],                       *)
(* eval_args = %[fuel; 1 + length es]. eval recurses into args with  *)
(* fuel-1; eval_args walks the arg list at the same fuel with a       *)
(* strictly smaller list measure.                                    *)
(* ================================================================ *)

let rec eval (env:list (string & mvalue)) (e:expr) (fuel:nat)
  : Tot mvalue (decreases %[fuel; 0])
=
  if fuel = 0 then MV_Undef "fuel-exhausted"
  else
    match e with
    | E_Int n -> MV_Rat n 1
    | E_Rat n d -> mk_rat n d
    | E_Bool b -> MV_Bool b
    | E_Sym name ->
      (match List.Tot.find (fun (kv:(string & mvalue)) -> fst kv = name) env with
       | Some (_, v) -> v
       | None -> MV_Undef (String.concat "" ["unbound-symbol:"; name]))
    | E_App fn args ->
      let vals = eval_args env args (fuel - 1) in
      apply_fn fn vals

and eval_args (env:list (string & mvalue)) (es:list expr) (fuel:nat)
  : Tot (list mvalue) (decreases %[fuel; 1 + List.Tot.length es])
=
  match es with
  | [] -> []
  | hd :: tl -> eval env hd fuel :: eval_args env tl fuel

// Depth budget. Expression trees are shallow in practice; this bounds
// recursion for totality without limiting any realistic input.
let eval_fuel : nat = 100000

let mk_env (pairs:list (string & string)) : list (string & mvalue) =
  List.Tot.map (fun (kv:(string & string)) -> (fst kv, parse_decimal (snd kv))) pairs

let eval_expr (env:list (string & mvalue)) (e:expr) : mvalue =
  eval env e eval_fuel

(* ================================================================ *)
(* Canonical string form (for exact comparison / display)            *)
(* ================================================================ *)

// Reduced rationals compare canonically as "num" (den = 1) or
// "num/den"; booleans as true/false; every MV_Undef collapses to the
// single token "undef" so expectation matching is reason-independent.
let value_to_string (v:mvalue) : string =
  match v with
  | MV_Rat n 1 -> string_of_int n
  | MV_Rat n d -> String.concat "" [string_of_int n; "/"; string_of_int d]
  | MV_Bool b -> if b then "true" else "false"
  | MV_Undef _ -> "undef"

// The diagnostic reason behind an MV_Undef (empty for defined values).
let value_reason (v:mvalue) : string =
  match v with
  | MV_Undef r -> r
  | _ -> ""
