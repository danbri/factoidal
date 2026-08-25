/-
L4Factoidal.Math.SigmoidTests — build-time checks for the fixed-point
`exp` and the sigmoid sampler.

The checks are stated as BOUNDS, not as exact equalities: this module
approximates on purpose (see its header), so a guard demanding an
exact digit string would be pinning the truncation rather than the
mathematics.
-/
import L4Factoidal.Math.Sigmoid

namespace L4Factoidal.Math.Sigmoid

/-- The mantissa at `outputScale`, i.e. the value times 10^9. -/
private def at9 (s : Scaled) : Int := s.1

private def near (got want tol : Int) : Bool :=
  (got - want).natAbs ≤ tol.natAbs

/-! ## `exp` at the points whose values are known exactly or well

`exp(0) = 1` is exact. `exp(1)` is 2.718281828…, and `exp(-1)` is
0.367879441…; the tolerance below is 10^-6 at the nine-digit output
scale, which is far inside what the degree-12 Taylor polynomial after
a 2^10 argument reduction gives. -/

#guard at9 (expApprox (0, 0)) == 1000000000
#guard near (at9 (expApprox (1, 0))) 2718281828 1000
#guard near (at9 (expApprox (-1, 0))) 367879441 1000
#guard near (at9 (expApprox (2, 0))) 7389056099 10000

/-! A DECIMAL argument goes through the same path: `exp(0.5)` is
    1.648721271…. -/
#guard near (at9 (expApprox (5, 1))) 1648721271 1000

/-! ## The sigmoid

The standard logistic (k = 1, x0 = 0, L = 1) is 1/2 at zero, and it
is symmetric: `σ(x) + σ(-x) = 1`. Symmetry is the property worth
checking, because an argument-reduction bug breaks it while leaving
each value individually plausible. -/

private def logistic (x : Scaled) : Int :=
  match sigmoidPoints (1, 0) (0, 0) (1, 0) x x 0 with
  | (_, y) :: _ => y.1
  | []          => 0

#guard near (logistic (0, 0)) 500000000 10
#guard near (logistic (1, 0) + logistic (-1, 0)) 1000000000 100
#guard near (logistic (4, 0) + logistic (-4, 0)) 1000000000 100

/-! `σ` is increasing, and it stays inside `(0, L)` — never at or past
    the asymptote, which a saturating fixed-point error would show up
    as. -/
#guard logistic (-4, 0) < logistic (0, 0)
#guard logistic (0, 0) < logistic (4, 0)
#guard 0 < logistic (-8, 0)
#guard logistic (8, 0) < 1000000000

/-! ## Sampling

`n` gives `n+1` points, and `n = 0` gives the single point at `xmin`
rather than dividing by zero. -/

#guard (sigmoidPoints (1, 0) (0, 0) (1, 0) (-2, 0) (2, 0) 4).length == 5
#guard (sigmoidPoints (1, 0) (0, 0) (1, 0) (-2, 0) (2, 0) 0).length == 1
#guard ((sigmoidPoints (1, 0) (0, 0) (1, 0) (-2, 0) (2, 0) 0).head?.map
          (fun p => p.1.1)) == some (-2000000000)

/-! The samples are evenly spaced across the whole range, first at
    `xmin` and last at `xmax`. -/
#guard ((sigmoidPoints (1, 0) (0, 0) (1, 0) (-2, 0) (2, 0) 4).getLast?.map
          (fun p => p.1.1)) == some 2000000000

end L4Factoidal.Math.Sigmoid
