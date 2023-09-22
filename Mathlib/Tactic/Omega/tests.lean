import Mathlib.Tactic.Omega.tactic
import Mathlib.Util.Time

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

/-! Even better, we can use this test after dividing through by the gcd and tightening: -/
#time
example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₁ : 2 * x + 1 ≤ 0) : False := by
  omega

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
