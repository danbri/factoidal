module Math.Series

// Finite summation and product over an integer index range, built on
// the CAS-agnostic core (Math.Expr) plus Math.Subst.subst and
// Math.Simplify.simplify. NO general binder / bound-variable machinery
// is introduced: the bounds are concrete integers, so each term is
// produced by numeric substitution of the index and the whole thing is
// combined with the existing n-ary "plus" / "times" nodes and then
// normalised by simplify.
//
//   summation body i lo hi  = simplify ( sum_{k=lo}^{hi} body[i:=k] )
//   finite_product body i lo hi = simplify ( prod_{k=lo}^{hi} body[i:=k] )
//
// Empty-range identities fall straight out of simplify:
//   * an empty "plus"  normalises to E_Int 0  (additive identity)
//   * an empty "times" normalises to E_Int 1  (multiplicative identity)
// so hi < lo yields 0 and 1 respectively with no special case.
//
// The product is LEFT FACTORED: we do not distribute / expand it (that
// is a separate `expand` step). simplify only applies its sound subset
// (annihilation on a literal 0, dropping *1, folding numeric literals),
// so e.g. the k=0 term (x + 0*y) collapses to x while (x + 1*y), ...
// stay as the factors of the product.
//
// Symbolic bounds (lo / hi not concrete integers) are OUT of scope here:
// this module is finite numeric expansion only. Closed forms for a
// symbolic upper bound (Gauss sums, geometric series, ...) require the
// bound-variable / closed-form layer, which is future work.

open Math.Expr
open Math.Subst
open Math.Simplify

// Number of terms in the inclusive integer range [lo, hi] (0 if empty).
// Kept as a nat so the term-builder can recurse on a decreasing fuel.
let series_count (lo:int) (hi:int) : nat =
  if hi < lo then 0 else hi - lo + 1

// The list [ body[idx := lo]; body[idx := lo+1]; ... ] of `fuel` terms,
// each obtained by substituting the running integer index into `body`.
let rec series_terms_fuel (body:expr) (idx:string) (lo:int) (fuel:nat)
  : Tot (list expr) (decreases fuel)
=
  if fuel = 0 then []
  else subst idx (E_Int lo) body :: series_terms_fuel body idx (lo + 1) (fuel - 1)

// The terms of the range [lo, hi] inclusive (empty when hi < lo).
let series_range_terms (body:expr) (idx:string) (lo:int) (hi:int) : list expr =
  series_terms_fuel body idx lo (series_count lo hi)

// Finite summation: fold the range terms into one "plus" node and
// normalise. simplify's like-term / coefficient merge turns e.g.
// summation (x + i*y) i 1 4 into 4*x + 10*y.
let summation (body:expr) (idx:string) (lo:int) (hi:int) : expr =
  simplify (E_App "plus" (series_range_terms body idx lo hi))

// Finite product: fold the range terms into one "times" node and
// normalise (LEFT FACTORED — no expansion). The k=0 term x + 0*y
// reduces to x via simplify's annihilator/identity laws.
let finite_product (body:expr) (idx:string) (lo:int) (hi:int) : expr =
  simplify (E_App "times" (series_range_terms body idx lo hi))
