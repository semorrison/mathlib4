import Mathlib.Tactic.Omega.Frontend

example : True := by
  fail_if_success omega
  trivial

example (_ : (1 : Int) < (0 : Int)) : False := by omega

example (_ : (0 : Int) < (0 : Int)) : False := by omega
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega); trivial

example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega
example {x : Int} (_ : x % 2 > 5) : False := by omega

example {x : Int} (_ : 2 * (x / 2) > x) : False := by omega
example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by omega

example (_ : 7 < 3) : False := by omega
example (_ : 0 < 0) : False := by omega

example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by omega
example {x : Nat} (_ : x ≥ 7) (_ : x ≤ 3) : False := by omega
example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega

example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 5) (_ : y < 5) : False := by omega
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 5) (_ : y < 5) : False := by omega

example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by omega
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by omega

example {x y : Int} (_ : 6 * x + 7 * y = 5) : True := by (fail_if_success omega); trivial
example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by omega

example {x : Nat} (_ : x < 0) : False := by omega

example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by omega

example {x y : Nat} (_ : x - y = 0) (_ : x > y) : False := by omega

example {x y z : Int} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {a b c d e f : Nat} (_ : a - b - c - d - e - f = 0) (_ : a > b + c + d + e + f) : False := by
  omega

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by omega

example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega

example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by omega

example {x y : Nat} (h1 : x / 2 - y / 3 < x % 2) (h2 : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by omega

example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
  omega


example (h : (7 : Int) = 0) : False := by omega

example (h : (7 : Int) ≤ 0) : False := by omega

example (h : (-7 : Int) + 14 = 0) : False := by omega

example (h : (-7 : Int) + 14 ≤ 0) : False := by omega

example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
  omega

example (h : (7 : Int) - 14 = 0) : False := by omega

example (h : (14 : Int) - 7 ≤ 0) : False := by omega

example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
  omega

example (h : -(7 : Int) = 0) : False := by omega

example (h : -(-7 : Int) ≤ 0) : False := by omega

example (h : 2 * (7 : Int) = 0) : False := by omega

example (h : (7 : Int) < 0) : False := by omega

example {x : Int} (h : x + x + 1 = 0) : False := by omega

example {x : Int} (h : 2 * x + 1 = 0) : False := by omega

example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by omega

example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 < 4 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x : Int} (h₁ : 0 < 2 * x + 2) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by omega

example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) :
    False := by omega

example {x1 x2 x3 x4 x5 x6 : Int} (h : 0 ≤ 2 * x1 + 1) (h : x1 = x2) (h : x2 = x3) (h : x3 = x4)
    (h : x4 = x5) (h : x5 = x6) (h : 2 * x6 + 1 ≤ 0) : False := by omega

example {x : Int} (_ : 1 ≤ -3 * x) (_ : 1 ≤ 2 * x) : False := by omega

example {x y : Int} (_ : 2 * x + 3 * y = 0) (_ : 1 ≤ x) (_ : 1 ≤ y) : False := by omega

example {x y z : Int} (_ : 2 * x + 3 * y + 4 * z = 0) (_ : 1 ≤ x + y) (_ : 1 ≤ y + z)
    (_ : 1 ≤ x + z) : False := by omega

example {x y : Int} (_ : 1 ≤ 3 * x) (_ : y ≤ 2) (_ : 6 * x - 2 ≤ y) : False := by omega

example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 1 ≤ x) : False := by omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x ≥ 1) : False := by omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 0 < x) : False := by omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x > 0) : False := by omega

-- theorem omega_nightmare {x y : Int} (_ : 3 ≤ 11 * x + 13 * y) (_ : 11 * x + 13 * y ≤ 21)
--     (_ : -8 ≤ 7 * x - 9 * y) (_ : 7 * x - 9 * y ≤ 6) : False := by
--   -- omega -- need to implement the shadows before we can do this!
--   sorry

-- TODO: if the goal is an equality, allow the case split.
example {n : Nat} (_ : n > 0) : (2*n - 1) % 2 = 1 := by
  by_contra h
  rw [← ne_eq, Nat.ne_iff_lt_or_gt] at h
  cases h <;>
  omega
