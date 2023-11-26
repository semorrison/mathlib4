import Mathlib.Tactic.Omega.Frontend

/-
```
lake build Mathlib.Tactic.Omega.Benchmarks.b20231126 > /dev/null && \
date && git rev-parse HEAD && \
hyperfine "lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231126.lean"
```

-/

example {x y z : Int} (_ : 7 * x + 12 * y + 31 * z - 17 = 0) (_ : 3 * x + 5 * y + 24 * z - 7 = 0) (_ : 0 ≤ x + 1000) : True := by
  fail_if_success omega
  trivial

example {x y z : Int} (_ : 7 * x + 12 * y + 31 * z - 17 = 0) (_ : 3 * x + 5 * y + 24 * z - 7 = 0) (_ : 0 ≤ y + 1000) : True := by
  fail_if_success omega
  trivial

example {x y z : Int} (_ : 7 * x + 12 * y + 31 * z - 17 = 0) (_ : 3 * x + 5 * y + 24 * z - 7 = 0) (_ : 0 ≤ z - 8) : True := by
  fail_if_success omega
  trivial

example {x y z : Int} (_ : 7 * x + 12 * y + 31 * z - 17 = 0) (_ : 3 * x + 5 * y + 24 * z - 7 = 0) (_ : 0 ≤ x + 1000) (_ : 0 ≤ y + 1000) (_ : 0 ≤ z - 8) : False := by
  omega
