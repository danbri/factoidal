module Math.Simplify

// A canonical normalizer for Math.Expr.expr — the "simplify" of the
// verified CAS layer. Total and structural (recursion on the strict
// subterm ordering). Bottom-up: children are simplified first, then a
// shallow combining pass normalizes the node.
//
// What it normalizes (sound subset):
//   * constant folding : any E_App whose arguments are all numeric
//     literals is folded through Math.Expr.apply_fn (so 2+3 -> 5,
//     6/2 -> 3, 2^3 -> 8). Folding that would be undefined (e.g. /0)
//     is left symbolic — never faked.
//   * plus  : flatten nested plus, drop +0 identities, sum numeric
//     literals into one constant, collect repeated summands into an
//     integer coefficient (x+x -> 2*x), deterministic ordering.
//   * times : flatten nested times, annihilate on any literal 0,
//     drop *1 identities, multiply numeric literals into one constant,
//     combine equal bases with integer exponents (x*x -> x^2,
//     x^a*x^b -> x^(a+b)), deterministic ordering.
//   * cheap always-sound identities: a^1 -> a, a/1 -> a, a-0 -> a.
//
// What it deliberately does NOT do (documented gaps, all sound to omit):
//   * distribute / expand products over sums (that is a separate
//     `expand`); no factoring.
//   * fold coefficient-carrying like-terms such as (2*x)+x -> 3*x
//     (only exact repeats of an identical subterm are collected).
//   * a^0 -> 1 for a symbolic base (unsound at a = 0), or any rule
//     that changes the domain of definition.
//   * trig/log simplification identities.
//
// simplify is idempotent (simplify (simplify e) = simplify e); this is
// asserted as a property test in the CAS harness, not proved here.

open Math.Expr
open FStar.List.Tot

(* ---------------------------------------------------------------- *)
(* Canonical ordering key (a total-ish string serialization used to  *)
(* deterministically order commutative operands).                    *)
(* ---------------------------------------------------------------- *)

let rec expr_key (e:expr) : Tot string (decreases e) =
  match e with
  | E_Int n -> String.concat "" ["0i:"; string_of_int n]
  | E_Rat n d -> String.concat "" ["1r:"; string_of_int n; "/"; string_of_int d]
  | E_Bool b -> String.concat "" ["2b:"; if b then "t" else "f"]
  | E_Sym s -> String.concat "" ["3s:"; s]
  | E_App fn args -> String.concat "" ["4a:"; fn; "("; expr_key_list args; ")"]

and expr_key_list (es:list expr) : Tot string (decreases es) =
  match es with
  | [] -> ""
  | h :: t -> String.concat "" [expr_key h; ","; expr_key_list t]

// Lexicographic comparison of two strings by codepoint. Returns
// negative / zero / positive, as an ordering on the char lists.
let rec charlist_cmp (a:list FStar.Char.char) (b:list FStar.Char.char)
  : Tot int (decreases a) =
  match a, b with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | ca :: ta, cb :: tb ->
    let na = FStar.Char.int_of_char ca in
    let nb = FStar.Char.int_of_char cb in
    if na < nb then -1
    else if na > nb then 1
    else charlist_cmp ta tb

let str_cmp (a:string) (b:string) : int =
  charlist_cmp (String.list_of_string a) (String.list_of_string b)

let expr_cmp (a:expr) (b:expr) : int = str_cmp (expr_key a) (expr_key b)

// Insertion sort by expr_cmp — total, no order-property proof needed.
let rec insert_sorted (x:expr) (l:list expr) : Tot (list expr) (decreases l) =
  match l with
  | [] -> [x]
  | h :: t -> if expr_cmp x h <= 0 then x :: l else h :: insert_sorted x t

let rec sort_exprs (l:list expr) : Tot (list expr) (decreases l) =
  match l with
  | [] -> []
  | h :: t -> insert_sorted h (sort_exprs t)

(* ---------------------------------------------------------------- *)
(* Numeric-literal helpers                                           *)
(* ---------------------------------------------------------------- *)

let is_num_lit (e:expr) : bool =
  match e with
  | E_Int _ -> true
  | E_Rat _ _ -> true
  | _ -> false

let lit_value (e:expr) : mvalue =
  match e with
  | E_Int n -> MV_Rat n 1
  | E_Rat n d -> mk_rat n d
  | _ -> MV_Undef "not-a-literal"

let is_zero_lit (e:expr) : bool =
  match e with
  | E_Int n -> n = 0
  | E_Rat n _ -> n = 0
  | _ -> false

(* ---------------------------------------------------------------- *)
(* Flatten one level of an associative operator's nested nodes. The   *)
(* children are already simplified, hence internally flat, so a       *)
(* single splice suffices.                                            *)
(* ---------------------------------------------------------------- *)

let rec flatten_op (fn:string) (args:list expr) : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | h :: t ->
    let rest = flatten_op fn t in
    (match h with
     | E_App fn2 inner -> if fn2 = fn then append inner rest else h :: rest
     | _ -> h :: rest)

(* ---------------------------------------------------------------- *)
(* Tally identical exprs into (expr, count) pairs, insertion-ordered. *)
(* ---------------------------------------------------------------- *)

let rec bump (t:expr) (acc:list (expr & nat)) : Tot (list (expr & nat)) (decreases acc) =
  match acc with
  | [] -> [(t, 1)]
  | (h, c) :: rest -> if h = t then (h, c + 1) :: rest else (h, c) :: bump t rest

let rec tally (l:list expr) (acc:list (expr & nat)) : Tot (list (expr & nat)) (decreases l) =
  match l with
  | [] -> acc
  | h :: t -> tally t (bump h acc)

(* ---------------------------------------------------------------- *)
(* Base/exponent view of a factor and integer-exponent combination.  *)
(* ---------------------------------------------------------------- *)

let base_exp (e:expr) : (expr & int) =
  match e with
  | E_App "power" [b; E_Int n] -> (b, n)
  | _ -> (e, 1)

let rec bump_exp (b:expr) (n:int) (acc:list (expr & int))
  : Tot (list (expr & int)) (decreases acc) =
  match acc with
  | [] -> [(b, n)]
  | (hb, hn) :: rest -> if hb = b then (hb, hn + n) :: rest else (hb, hn) :: bump_exp b n rest

let rec combine_powers (l:list (expr & int)) (acc:list (expr & int))
  : Tot (list (expr & int)) (decreases l) =
  match l with
  | [] -> acc
  | (b, n) :: t -> combine_powers t (bump_exp b n acc)

(* ---------------------------------------------------------------- *)
(* Splits of an argument list into (constant fold, other terms).     *)
(* ---------------------------------------------------------------- *)

let rec split_sum (args:list expr) (constv:mvalue) (terms:list expr)
  : Tot (mvalue & list expr) (decreases args) =
  match args with
  | [] -> (constv, terms)
  | h :: t ->
    if is_num_lit h then split_sum t (m_add constv (lit_value h)) terms
    else split_sum t constv (append terms [h])

let rec split_prod (args:list expr) (constv:mvalue) (factors:list expr)
  : Tot (mvalue & list expr) (decreases args) =
  match args with
  | [] -> (constv, factors)
  | h :: t ->
    if is_num_lit h then split_prod t (m_mul constv (lit_value h)) factors
    else split_prod t constv (append factors [h])

(* ---------------------------------------------------------------- *)
(* Emit summands / factors from the collected structures.            *)
(* ---------------------------------------------------------------- *)

let rec emit_summands (pairs:list (expr & nat)) : Tot (list expr) (decreases pairs) =
  match pairs with
  | [] -> []
  | (t, c) :: rest ->
    let head = if c <= 1 then t else E_App "times" [E_Int c; t] in
    head :: emit_summands rest

let rec emit_factors (pairs:list (expr & int)) : Tot (list expr) (decreases pairs) =
  match pairs with
  | [] -> []
  | (b, n) :: rest ->
    if n = 0 then emit_factors rest
    else
      let head = if n = 1 then b else E_App "power" [b; E_Int n] in
      head :: emit_factors rest

(* ---------------------------------------------------------------- *)
(* plus / times shallow normalizers (operate on simplified children). *)
(* ---------------------------------------------------------------- *)

let simplify_plus (args:list expr) : expr =
  let flat = flatten_op "plus" args in
  let (constv, terms) = split_sum flat (MV_Rat 0 1) [] in
  let pairs = tally terms [] in
  let summands = sort_exprs (emit_summands pairs) in
  let const_lit =
    (match constv with
     | MV_Rat 0 1 -> []
     | MV_Undef _ -> []
     | _ -> [value_to_lit constv]) in
  let all = append summands const_lit in
  (match all with
   | [] -> E_Int 0
   | [x] -> x
   | _ -> E_App "plus" all)

let simplify_times (args:list expr) : expr =
  let flat = flatten_op "times" args in
  if existsb is_zero_lit flat then E_Int 0
  else
    let (constv, factors) = split_prod flat (MV_Rat 1 1) [] in
    let pairs = combine_powers (map base_exp factors) [] in
    let facs = sort_exprs (emit_factors pairs) in
    let const_lit =
      (match constv with
       | MV_Rat 1 1 -> []
       | MV_Undef _ -> []
       | _ -> [value_to_lit constv]) in
    let all = append const_lit facs in
    (match all with
     | [] -> E_Int 1
     | [x] -> x
     | _ -> E_App "times" all)

// Shallow normalizer for a non-plus/times node whose args are already
// simplified: constant-fold if all literal & defined, else apply the
// cheap always-sound identities, else rebuild.
let simplify_other (fn:string) (args:list expr) : expr =
  if for_all is_num_lit args then
    (let v = apply_fn fn (map lit_value args) in
     match v with
     | MV_Undef _ -> E_App fn args
     | _ -> value_to_lit v)
  else
    (match fn, args with
     | "power", [a; E_Int 1] -> a
     | "divide", [a; E_Int 1] -> a
     | "minus", [a; E_Int 0] -> a
     | _ -> E_App fn args)

let simplify_app (fn:string) (args:list expr) : expr =
  if fn = "plus" then simplify_plus args
  else if fn = "times" then simplify_times args
  else simplify_other fn args

(* ---------------------------------------------------------------- *)
(* The recursive driver: simplify children, then combine.            *)
(* ---------------------------------------------------------------- *)

let rec simplify (e:expr) : Tot expr (decreases e) =
  match e with
  | E_Int _ -> e
  | E_Rat _ _ -> e
  | E_Bool _ -> e
  | E_Sym _ -> e
  | E_App fn args -> simplify_app fn (simplify_list args)

and simplify_list (es:list expr) : Tot (list expr) (decreases es) =
  match es with
  | [] -> []
  | h :: t -> simplify h :: simplify_list t
