import Mathlib.Tactic.Omega.Frontend

example (x : Nat) : x % 4 - x % 8 = 0 := by
  rw [Nat.eq_iff_le_and_ge]
  constructor <;> omega
