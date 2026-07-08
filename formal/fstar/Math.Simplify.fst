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
//     literals into one constant, and merge like terms by summing their
//     rational coefficients over a canonical core key — so x+x -> 2*x
//     and y + 2*y + 3*y + 4*y -> 10*y. Deterministic ordering.
//   * times : flatten nested times, annihilate on any literal 0,
//     drop *1 identities, multiply numeric literals into one constant,
//     combine equal bases with integer exponents (x*x -> x^2,
//     x^a*x^b -> x^(a+b)), deterministic ordering.
//   * cheap always-sound identities: a^1 -> a, a/1 -> a, a-0 -> a.
//
// What it deliberately does NOT do (documented gaps, all sound to omit):
//   * distribute / expand products over sums (that is a separate
//     `expand`); no factoring.
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

(* ---------------------------------------------------------------- *)
(* Coefficient-carrying like-term merge for a sum.                    *)
(*                                                                    *)
(* Each non-numeric summand is split into a rational coefficient and  *)
(* a "core" — the list of its non-numeric factors (already sorted,    *)
(* because the child was simplified). Summands whose cores share a    *)
(* canonical key (expr_key of the core) have their coefficients       *)
(* SUMMED, so y + 2*y + 3*y + 4*y -> 10*y and x + x -> 2*x. Only      *)
(* genuinely like terms merge: distinct cores have distinct keys, so  *)
(* unlike terms are never combined (soundness > coverage).            *)
(* ---------------------------------------------------------------- *)

// Split a summand into (rational coefficient, core factor list). A
// times node contributes its numeric-literal factors to the coefficient
// and the rest to the core; anything else is coefficient 1 over itself.
let split_coeff (e:expr) : (mvalue & list expr) =
  match e with
  | E_App "times" factors -> split_prod factors (MV_Rat 1 1) []
  | _ -> (MV_Rat 1 1, [e])

// Canonical key for a core factor list (the empty core denotes a pure
// number, folded into the additive constant rather than keyed).
let core_key (cf:list expr) : string =
  match cf with
  | [] -> ""
  | [f] -> expr_key f
  | _ -> expr_key (E_App "times" cf)

// Add coefficient c for the core keyed by k (factors cf) into acc,
// summing into an existing group with the same key.
let rec bump_core (k:string) (cf:list expr) (c:mvalue)
                  (acc:list (string & list expr & mvalue))
  : Tot (list (string & list expr & mvalue)) (decreases acc) =
  match acc with
  | [] -> [(k, cf, c)]
  | (hk, hcf, hc) :: rest ->
    if hk = k then (hk, hcf, m_add hc c) :: rest
    else (hk, hcf, hc) :: bump_core k cf c rest

// Fold the non-numeric summands into (additive constant, keyed groups).
// A summand that reduces to a pure number (empty core) is added to the
// constant instead of forming a group.
let rec collect_coeffs (terms:list expr) (constv:mvalue)
                       (acc:list (string & list expr & mvalue))
  : Tot (mvalue & list (string & list expr & mvalue)) (decreases terms) =
  match terms with
  | [] -> (constv, acc)
  | t :: rest ->
    let (c, cf) = split_coeff t in
    (match cf with
     | [] -> collect_coeffs rest (m_add constv c) acc
     | _ -> collect_coeffs rest constv (bump_core (core_key cf) cf c acc))

// Rebuild one summand from its coefficient and core. Coefficient 0
// annihilates (empty), 1 drops (bare core), otherwise emit a flat
// times node coeff::core so a re-simplify is stable (idempotence).
let merged_term (cf:list expr) (c:mvalue) : list expr =
  match c with
  | MV_Rat 0 1 -> []
  | MV_Rat 1 1 -> [ (match cf with [f] -> f | _ -> E_App "times" cf) ]
  | _ -> [ E_App "times" (value_to_lit c :: cf) ]

let rec emit_merged (groups:list (string & list expr & mvalue))
  : Tot (list expr) (decreases groups) =
  match groups with
  | [] -> []
  | (_, cf, c) :: rest -> append (merged_term cf c) (emit_merged rest)

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
  let (constv0, terms) = split_sum flat (MV_Rat 0 1) [] in
  let (constv, groups) = collect_coeffs terms constv0 [] in
  let summands = sort_exprs (emit_merged groups) in
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
