import Mathlib.Tactic.Omega.tactic_div_mod

example {x : Int} (h₁ : x / 2 = x) (h₂ : 1 ≤ x) : False := by
  omega_int_div

example {x : Int} (h₁ : 7 < x % 3) : False := by
  omega_int_div
