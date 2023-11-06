import Mathlib.Tactic.Omega.tactic_div_mod


set_option trace.omega true

example {x : Int} (h₁ : x / 2 = x) (h₂ : 1 ≤ x) : False := by
  omega_int

example {x : Int} (h₁ : 7 < x % 3) : False := by
  omega_int
