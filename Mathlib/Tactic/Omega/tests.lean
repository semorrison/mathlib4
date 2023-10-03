import Mathlib.Tactic.Omega.tactic
import Mathlib.Util.Time
import Mathlib.Tactic.Conv

/-!
`n = 0` has no solutions if `n ≠ 0`, and `n ≥ 0` has no solutions if `n < 0`.
-/

example (h : (7 : Int) = 0) : False := by
  omega

example (h : (7 : Int) ≤ 0) : False := by
  omega

example (h : (-7 : Int) + 14 = 0) : False := by
  omega

example (h : (-7 : Int) + 14 ≤ 0) : False := by
  omega

example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
  omega

example (h : (7 : Int) - 14 = 0) : False := by
  omega

example (h : (14 : Int) - 7 ≤ 0) : False := by
  omega

example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
  omega

example (h : -(7 : Int) = 0) : False := by
  omega

example (h : -(-7 : Int) ≤ 0) : False := by
  omega

example (h : 2 * (7 : Int) = 0) : False := by
  omega

/-!
If the constant term of an equation is not divisible by the GCD of the coefficients,
there are no solutions.
-/
example {x : Int} (h : x + x + 1 = 0) : False := by
  omega

example {x : Int} (h : 2 * x + 1 = 0) : False := by
  omega

example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by
  omega

example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by
  omega

set_option trace.omega true

/-!
If we have two inequalities with opposite coefficients `a + ∑ cᵢ * xᵢ ≥ 0` and `b - ∑ cᵢ * xᵢ ≥ 0`
then `-a > b` gives a contradiction.
-/
example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by
  omega

set_option trace.profiler true
set_option trace.profiler.threshold 1
set_option trace.Kernel true

#time
#eval omega_algorithm₁ { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [-2]}] }
#time
#eval omega_algorithm' { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [-2]}] }
#time
#whnf omega_algorithm' { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [-2]}] }

/-! Even better, we can use this test after dividing through by the gcd and tightening: -/
#time
example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by
  omega

-- set_option maxHeartbeats 10000000

#time
#eval omega_algorithm₁ { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [0, -2]}], equalities := [{const := 0, coeffs := [1, -1]}] }
#time
#eval omega_algorithm' { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [0, -2]}], equalities := [{const := 0, coeffs := [1, -1]}] }


-- #time
-- example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by
--   omega

-- #time
-- example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) : False := by
--   omega



/--
error: omega algorithm is incomplete!
---
info:
[omega] trivial
[omega] trivial
-/
#guard_msgs in
example : False := by
  omega
