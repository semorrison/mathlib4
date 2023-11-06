import Mathlib.Tactic.Zify
import Mathlib.Data.Int.Basic
import Std.Tactic.GuardExpr

example (a b : ℕ) : a < 2 * b := by
  zify
  -- goal is: `↑a < ↑(2 * b)`
  push_cast
  -- goal is: `↑a < ↑(2 * b)`
  sorry
  -- I want to get to `↑a < 2 * ↑n`!
