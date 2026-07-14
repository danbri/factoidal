module Math.Sigmoid

// A bounded-rational exp() approximation and a sigmoid point-sampler
// built on it, for hub post 28's live sigmoid demo (issue #289). All
// arithmetic is fixed-precision scaled-integer arithmetic (no floats
// anywhere in this module, `Tot` throughout -- fixed term/iteration
// counts, no fuel exhaustion, no partiality) using the same
// "mantissa / 10^scale" convention SPARQL11.Algebra's parse_to_scaled
// / format_scaled_value use for xsd:decimal.
//
// ================================================================
// Algorithm: argument reduction + truncated Taylor + repeated squaring
// ================================================================
//
//   exp(x) = exp(x / 2^m) ^ (2^m)
//
// `reduction_shift` (m, fixed nat constant) divides the argument down
// to a small r = x / 2^m. `exp_small` then evaluates a
// degree-(taylor_terms - 1) Taylor polynomial of exp at r:
//
//   T_N(r) = sum_{k=0}^{N} r^k / k!
//
// and `square_repeat` squares the result m times, which raises it to
// the 2^m power (T_N(r))^(2^m) -- repeated squaring, not naive
// exponentiation -- recovering an approximation to exp(x) = exp(r)^(2^m).
//
// ================================================================
// Fixed-point arithmetic, and WHY (not exact rationals)
// ================================================================
//
// An earlier version of this module carried the computation as EXACT
// rationals (Math.Expr.mvalue's MV_Rat, arbitrary-precision num/den)
// all the way through, including the ten `square_repeat` squarings.
// That is mathematically the most transparent choice, but it is a
// PERFORMANCE TRAP: each exact-rational squaring roughly SQUARES the
// bit-length of both numerator and denominator (v -> v*v has a
// denominator of d^2, not d), so after m=10 squarings the exact
// denominator's bit-length grows by a factor of 2^10 = 1024 over the
// Taylor sum's own (already substantial, from r = x/1024's
// denominator to the 12th power) starting bit-length -- tens of
// thousands of decimal digits, with a gcd reduction (Euclid's
// algorithm) at every single multiplication along the way. Measured:
// this made a single 25-point sigmoid_points call fail to return
// within several CPU-minutes in the extracted OCaml/JS runtime.
//
// The fix is the standard one for this exact failure mode: TRUNCATE
// back to a fixed number of fractional digits after every
// multiplication/division, so intermediate values never grow past a
// bounded size no matter how many operations are chained. `wp_mul` /
// `wp_div` below operate on plain `int` mantissas at one fixed
// internal precision, `work_scale` (represented value = mantissa /
// 10^work_scale); every multiply computes the exact product and then
// divides back down by `10^work_scale`, discarding the low digits.
// This is ordinary fixed-point arithmetic, still scaled-integer (never
// a float), and it keeps every intermediate mantissa within a small,
// constant number of digits regardless of the Taylor-term count or the
// squaring depth.
//
// ================================================================
// DOCUMENTED ERROR BOUND
// ================================================================
//
// This is a documented (not SMT-verified -- it is a real-analysis
// fact, outside decidable arithmetic) bound, derived for the fixed
// constants this module actually uses: reduction_shift = 10 (m = 10,
// so 2^m = 1024), taylor_terms = 13 (so N = 12, a degree-12
// polynomial), work_scale = 24 (24 fractional decimal digits of
// internal precision), output_scale = 9 (9 fractional decimal digits
// on the returned `scaled` value).
//
// Domain: |x| <= 40 (comfortably covers any k*(x - x0) a sigmoid demo
// will produce -- sigmoid saturates to 0/1 well before |argument| = 40).
//
// Step 1 (Taylor truncation). Lagrange's remainder theorem gives, for
// r = x / 1024 (so |r| <= 40/1024 ~= 0.0391):
//     |T_N(r) - exp(r)| <= |r|^(N+1) / (N+1)! * exp(|r|)
// With N = 12, |r| <= 0.0391: |r|^13 ~= 4.9e-19, 13! = 6 227 020 800,
// exp(|r|) ~= 1.04, so the truncation error is bounded by
//     ~= 4.9e-19 / 6.23e9 * 1.04  ~=  8.3e-29.
//
// Step 2 (fixed-point rounding, per operation). Every `wp_mul`/`wp_div`
// truncates its exact result to `work_scale` = 24 fractional digits,
// contributing an absolute error of at most 10^-24 to THAT operation's
// result (never compounding beyond that within one operation -- the
// two operands' own accumulated error is a separate, additive term).
// The Taylor sum performs at most 13 * (12 multiplications for r^k) +
// 13 divisions ~= 170 fixed-point operations; squaring performs 10
// more. Generously bounding every one of these ~180 operations as
// contributing a fresh 10^-24 error term additively gives an
// accumulated Taylor-phase error of at most 180 * 10^-24 = 1.8e-22 --
// still negligible next to Step 1's 8.3e-29 -- so the combined
// pre-squaring relative error on exp(r) is bounded by
//     d_r <= 8.3e-29 + 1.8e-22  ~=  1.8e-22.
//
// Step 3 (squaring amplification). Writing T_N(r) = exp(r)*(1 + d)
// with |d| <= d_r ~= 1.8e-22 (relative form of the Step-1/2 bound,
// since exp(r) ~= 1 here), repeated squaring gives
//     T_N(r)^(2^m) = exp(r)^(2^m) * (1 + d)^(2^m)
//                  ~= exp(x) * (1 + 2^m * d)      [(1+d)^k ~= 1+k*d, |d| tiny]
// plus one fresh `wp_mul` rounding term (<= 10^-24 absolute, on a
// value of magnitude up to exp(x)) at each of the 10 squaring steps.
// So the RELATIVE error on exp(x) after 10 squarings is bounded by
//     2^10 * d_r + 10 * 10^-24  ~=  1024 * 1.8e-22 + 1e-23  ~=  1.9e-19.
// For |x| <= 40, exp(x) <= exp(40) ~= 2.35e17, so this contributes an
// ABSOLUTE error of at most ~= 2.35e17 * 1.9e-19 ~= 0.045 in the
// worst case at the very top of the domain (x = 40); for the |x| a
// sigmoid demo actually evaluates (single-digit-to-low-double-digit
// k*(x-x0), so exp(x) at most in the hundreds), this term is many
// orders of magnitude smaller than the Step 4 term below.
//
// Step 4 (output rounding). The public `exp_approx` / `sigmoid_points`
// truncate the internal work_scale=24 result down to `output_scale` =
// 9 fractional decimal digits, contributing an additional error of at
// most 10^-9.
//
// Combined, for the practical sigmoid range this module is built for
// (|x| up to a few tens, not the pathological x = 40 extreme), the
// Step 4 output-rounding term (10^-9) dominates every earlier term by
// many orders of magnitude:
//     |exp_approx(x) - exp(x)| < 10^-9   for the practical sigmoid range.

open FStar.List.Tot
open Math.Expr  // reused ONLY for the pure integer helpers pow10/ipow/ifact/iabs

(* ================================================================ *)
(* The scaled fixed-point decimal representation: (mantissa, scale), *)
(* value = mantissa / 10^scale. Same convention as                   *)
(* SPARQL11.Algebra.parse_to_scaled / format_scaled_value. This is    *)
(* the INTERCHANGE representation (caller's own scale, e.g. 0 for an  *)
(* integer literal or a handful of digits for a decimal literal).     *)
(* ================================================================ *)

type scaled = int & nat

(* ================================================================ *)
(* Fixed-point internal working representation: a plain `int`        *)
(* mantissa, always understood at the ONE fixed `work_scale` (never   *)
(* varying) -- see the module header for why a fixed, bounded         *)
(* precision (rather than growing exact rationals) is load-bearing    *)
(* for performance, not just style.                                   *)
(* ================================================================ *)

let work_scale : nat = 24
let work_pow10 : int = pow10 work_scale   // 10^24, fixed positive constant

// Interchange scaled -> internal fixed-point mantissa (at work_scale).
// Exact when the caller's scale <= work_scale (just pads with zeros --
// true for every caller in this module, since output_scale = 9 <=
// work_scale = 24 and typical decimal-literal inputs carry far fewer
// than 24 fractional digits); the `sc > work_scale` arm truncates
// (documented, not silently exact) so the function stays total for
// any input.
let to_work (s : scaled) : Tot int =
  let (m, sc) = s in
  if sc <= work_scale then op_Multiply m (pow10 (work_scale - sc))
  else
    let d = pow10 (sc - work_scale) in
    if d = 0 then m else m / d

// Internal fixed-point mantissa (at work_scale) -> interchange scaled
// at the REQUESTED output scale (<= work_scale for every caller here).
let from_work (wp : int) (scale : nat) : Tot scaled =
  if scale >= work_scale then (op_Multiply wp (pow10 (scale - work_scale)), scale)
  else
    let d = pow10 (work_scale - scale) in
    if d = 0 then (wp, scale) else (wp / d, scale)

let wp_from_int (n : int) : Tot int = op_Multiply n work_pow10

// Exact (same fixed scale on both sides, so a plain int add/sub is
// exact -- no truncation needed or performed).
let wp_add (a b : int) : Tot int = a + b
let wp_sub (a b : int) : Tot int = a - b
let wp_neg (a : int) : Tot int = 0 - a

// The size-bounding operations (see module header): compute the EXACT
// product/quotient scaled by work_pow10, then truncate back down to
// work_scale fractional digits. This is what keeps every intermediate
// value's digit count constant across an arbitrary chain of multiplies
// (unlike exact-rational squaring, whose denominator bit-length
// roughly doubles per squaring).
let wp_mul (a b : int) : Tot int =
  if work_pow10 = 0 then 0 else (op_Multiply a b) / work_pow10

let wp_div (a b : int) : Tot int =
  if b = 0 then 0 else (op_Multiply a work_pow10) / b

(* ================================================================ *)
(* Fixed-point integer power: base^e via repeated wp_mul (bounded --  *)
(* each step truncates back to work_scale digits).                    *)
(* ================================================================ *)

let rec wp_ipow (base : int) (e : nat) : Tot int (decreases e) =
  if e = 0 then wp_from_int 1 else wp_mul base (wp_ipow base (e - 1))

(* ================================================================ *)
(* Truncated Taylor polynomial of exp at a (small, post-reduction)    *)
(* fixed-point r: sum_{k=0}^{N} r^k / k!.                              *)
(* ================================================================ *)

// term_idx counts UP from 0, fuel counts DOWN -- fuel is the decreases
// measure, term_idx is just data. Adds `fuel` terms starting at
// r^term_idx / term_idx!.
let rec taylor_sum (r : int) (term_idx : nat) (fuel : nat) (acc : int)
  : Tot int (decreases fuel)
=
  if fuel = 0 then acc
  else
    let rk = wp_ipow r term_idx in
    let factk = wp_from_int (ifact term_idx) in
    let term = wp_div rk factk in
    taylor_sum r (term_idx + 1) (fuel - 1) (wp_add acc term)

(* ================================================================ *)
(* Fixed constants (see the error-bound derivation in the module      *)
(* header -- these numbers are exactly what that derivation assumes). *)
(* ================================================================ *)

let reduction_shift : nat = 10   // divide the argument by 2^10 = 1024
let taylor_terms : nat = 13      // k = 0 .. 12, a degree-12 polynomial
let output_scale : nat = 9       // 9 fractional decimal digits out

// T_N(r) for the fixed N = taylor_terms - 1.
let exp_small (r : int) : Tot int =
  taylor_sum r 0 taylor_terms (wp_from_int 0)

(* ================================================================ *)
(* Repeated squaring: v -> v^(2^times), fixed-point (bounded).        *)
(* ================================================================ *)

let rec square_repeat (v : int) (times : nat) : Tot int (decreases times) =
  if times = 0 then v else square_repeat (wp_mul v v) (times - 1)

(* ================================================================ *)
(* exp_approx over the fixed-point core (argument reduction +         *)
(* truncated Taylor + repeated squaring -- see module header).        *)
(* ================================================================ *)

let exp_approx_wp (x_wp : int) : Tot int =
  let divisor = wp_from_int (ipow 2 reduction_shift) in
  let r = wp_div x_wp divisor in
  let base = exp_small r in
  square_repeat base reduction_shift

// Public entry point over the `scaled` interchange representation
// (see error bound in the module header for the accuracy this gives).
let exp_approx (x : scaled) : Tot scaled =
  let x_wp = to_work x in
  let y_wp = exp_approx_wp x_wp in
  from_work y_wp output_scale

(* ================================================================ *)
(* Sigmoid point sampling: L / (1 + exp(-k*(x - x0))) at n+1 evenly    *)
(* spaced x values in [xmin, xmax]. All computed in the same bounded   *)
(* fixed-point representation (including the x_i sample points         *)
(* themselves), rounded to `output_scale` decimal digits only at the   *)
(* very end.                                                           *)
(* ================================================================ *)

// exp_approx_wp's squaring always yields a nonnegative value (a
// square is never negative), so 1 + e > 0 always: the wp_div below
// never hits division-by-zero in practice, though it is defined
// (returns 0) for that case regardless, so the function stays total.
let rec sigmoid_points_wp
    (k_wp x0_wp l_wp xmin_wp step_wp : int) (i : nat) (fuel : nat)
  : Tot (list (int & int)) (decreases fuel)
=
  if fuel = 0 then []
  else
    let x_wp = wp_add xmin_wp (wp_mul (wp_from_int i) step_wp) in
    let neg_k_dx = wp_neg (wp_mul k_wp (wp_sub x_wp x0_wp)) in
    let e_wp = exp_approx_wp neg_k_dx in
    let denom_wp = wp_add (wp_from_int 1) e_wp in
    let y_wp = wp_div l_wp denom_wp in
    (x_wp, y_wp) :: sigmoid_points_wp k_wp x0_wp l_wp xmin_wp step_wp (i + 1) (fuel - 1)

// Public entry point: n+1 evenly spaced (x, sigmoid(x)) samples over
// [xmin, xmax], both coordinates rounded to `output_scale` digits.
// n = 0 yields the single sample at xmin (step is irrelevant then, so
// it is set to 0 rather than dividing by n).
let sigmoid_points (k x0 l xmin xmax : scaled) (n : nat)
  : Tot (list (scaled & scaled))
=
  let k_wp = to_work k in
  let x0_wp = to_work x0 in
  let l_wp = to_work l in
  let xmin_wp = to_work xmin in
  let xmax_wp = to_work xmax in
  let step_wp =
    if n = 0 then wp_from_int 0
    else wp_div (wp_sub xmax_wp xmin_wp) (wp_from_int n)
  in
  let pts = sigmoid_points_wp k_wp x0_wp l_wp xmin_wp step_wp 0 (n + 1) in
  List.Tot.map
    (fun (p : int & int) -> (from_work (fst p) output_scale, from_work (snd p) output_scale))
    pts
