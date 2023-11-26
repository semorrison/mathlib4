import Mathlib.Tactic.Omega.Frontend

/-
```
lake build Mathlib.Tactic.Omega.Benchmarks.b20231126 > /dev/null && \
date && git rev-parse HEAD && \
hyperfine "lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231126.lean"
```

Use any2
Sun Nov 26 21:28:22 AEDT 2023
5520e81760522b8ecec02f157da1aca3e25a359e
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231126.lean
  Time (mean ± σ):     568.1 ms ±   4.5 ms    [User: 434.8 ms, System: 123.9 ms]
  Range (min … max):   563.4 ms … 578.4 ms    10 runs
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
