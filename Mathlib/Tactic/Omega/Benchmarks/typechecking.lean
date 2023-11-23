import Mathlib.Tactic.Omega.Frontend

set_option profiler true
set_option profiler.threshold 1
-- set_option trace.omega true

def foo {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

-- #print foo
