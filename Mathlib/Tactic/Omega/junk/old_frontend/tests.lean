-- import Mathlib.Tactic.Omega.tactic
-- import Mathlib.Util.Time
-- import Mathlib.Tactic.Conv

-- /-!
-- `n = 0` has no solutions if `n ≠ 0`, and `n ≥ 0` has no solutions if `n < 0`.
-- -/

-- example (h : (7 : Int) = 0) : False := by
--   omega_int_core

-- example (h : (7 : Int) ≤ 0) : False := by
--   omega_int_core

-- example (h : (-7 : Int) + 14 = 0) : False := by
--   omega_int_core

-- example (h : (-7 : Int) + 14 ≤ 0) : False := by
--   omega_int_core

-- example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
--   omega_int_core

-- example (h : (7 : Int) - 14 = 0) : False := by
--   omega_int_core

-- example (h : (14 : Int) - 7 ≤ 0) : False := by
--   omega_int_core

-- example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
--   omega_int_core

-- example (h : -(7 : Int) = 0) : False := by
--   omega_int_core

-- example (h : -(-7 : Int) ≤ 0) : False := by
--   omega_int_core

-- example (h : 2 * (7 : Int) = 0) : False := by
--   omega_int_core

-- example (h : (7 : Int) < 0) : False := by omega_int_core

-- /-!
-- If the constant term of an equation is not divisible by the GCD of the coefficients,
-- there are no solutions.
-- -/
-- example {x : Int} (h : x + x + 1 = 0) : False := by
--   omega_int_core

-- example {x : Int} (h : 2 * x + 1 = 0) : False := by
--   omega_int_core

-- example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by
--   omega_int_core

-- example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by
--   omega_int_core

-- -- set_option trace.omega true

-- /-!
-- If we have two inequalities with opposite coefficients `a + ∑ cᵢ * xᵢ ≥ 0` and `b - ∑ cᵢ * xᵢ ≥ 0`
-- then `-a > b` gives a contradiction.
-- -/
-- example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by
--   omega_int_core

-- example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 < 4 - x) : False := by
--   omega_int_core

-- -- set_option trace.profiler true
-- -- set_option trace.profiler.threshold 1
-- -- set_option trace.Kernel true

-- #time
-- #eval omega_algorithm₁ { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [-2]}] }

-- /-! Even better, we can use this test after dividing through by the gcd and tightening: -/
-- #time
-- example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by
--   omega_int_core

-- example {x : Int} (h₁ : 0 < 2 * x + 2) (h₂ : 2 * x + 1 ≤ 0) : False := by
--   omega_int_core

-- #time
-- #eval omega_algorithm₁ { inequalities := [{const := 1, coeffs := [2]}, {const := -1, coeffs := [0, -2]}], equalities := [{const := 0, coeffs := [1, -1]}] }


-- #time
-- example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by
--   omega_int_core

-- #time
-- example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) : False := by
--   omega_int_core

-- #time
-- example {x1 x2 x3 x4 x5 x6 : Int} (h : 0 ≤ 2 * x1 + 1) (h : x1 = x2) (h : x2 = x3) (h : x3 = x4) (h : x4 = x5) (h : x5 = x6) (h : 2 * x6 + 1 ≤ 0) : False := by
--   omega_int_core

-- example {x : Int} (_ : 1 ≤ -3 * x) (_ : 1 ≤ 2 * x) : False := by
--   omega_int_core

-- def s : Omega.Problem := { inequalities := [{const := -1, coeffs := [1, 0]}, {const := -1, coeffs := [0, 1]}], equalities := [{const := 0, coeffs := [2, 3]}] }
-- #eval (Omega.Impl.Problem.of s).eliminateEqualities 100

-- #time
-- example {x y : Int} (_ : 2 * x + 3 * y = 0) (_ : 1 ≤ x) (_ : 1 ≤ y) : False := by omega_int_core

-- #time
-- example {x y z : Int} (_ : 2 * x + 3 * y + 4 * z = 0) (_ : 1 ≤ x + y) (_ : 1 ≤ y + z) (_ : 1 ≤ x + z) : False := by omega_int_core

-- -- This one has rational solutions, but tightening inequalities is enough to show there are no integer solutions.
-- #time
-- example {x y : Int} (_ : 1 ≤ 3 * x) (_ : y ≤ 2) (_ : 6 * x - 2 ≤ y) : False := by omega_int_core

-- -- example {x : Int} (_ : x / 2 = x) (_ : 1 ≤ x) : False := by omega
-- example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 1 ≤ x) : False := by omega_int_core
-- example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x ≥ 1) : False := by omega_int_core
-- example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 0 < x) : False := by omega_int_core
-- example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x > 0) : False := by omega_int_core

-- theorem omega_nightmare {x y : Int} (_ : 3 ≤ 11 * x + 13 * y) (_ : 11 * x + 13 * y ≤ 21)
--     (_ : -8 ≤ 7 * x - 9 * y) (_ : 7 * x - 9 * y ≤ 6) : False := by
--   -- omega_int_core -- need to implement the shadows before we can do this!
--   sorry

-- /--
-- error: omega did not find a contradiction
-- -/
-- #guard_msgs in
-- example : False := by
--   omega_int_core
