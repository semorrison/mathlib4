import Mathlib.Tactic.Omega.Impl2.Frontend

/-
```
lake build Mathlib.Tactic.Omega.Benchmarks.b20231120_coq > /dev/null && \
date && git rev-parse HEAD && \
hyperfine --warmup 3 "lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120_coq.lean"
hyperfine --warmup 3 "rm -f .lia.cache && rm -f Mathlib/Tactic/Omega/comparisons/b20231120.vo && rm -f Mathlib/Tactic/Omega/comparisons/b20231120.vo? && coqc Mathlib/Tactic/Omega/comparisons/b20231120.v"
```
Thu Nov 23 17:12:20 AEDT 2023
acdcf21bba393dbbec8d15db9129125120e311c4
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120_coq.lean
  Time (mean ± σ):      1.446 s ±  0.004 s    [User: 1.265 s, System: 0.170 s]
  Range (min … max):    1.440 s …  1.456 s    10 runs
Benchmark 1: coqc b20231120.v
  Time (mean ± σ):     180.9 ms ±   1.7 ms    [User: 126.0 ms, System: 51.2 ms]
  Range (min … max):   179.3 ms … 185.5 ms    16 runs

About 8x faster! Not as bad as I feared.

Tue Dec 12 00:52:43 AEDT 2023
fe17c00be5bb5e31e18f84e82400a82feab03cd3
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120_coq.lean
  Time (mean ± σ):     805.8 ms ±   5.2 ms    [User: 593.2 ms, System: 201.2 ms]
  Range (min … max):   798.6 ms … 815.0 ms    10 runs

Benchmark 1: rm -f .lia.cache && rm -f Mathlib/Tactic/Omega/comparisons/b20231120.vo && rm -f Mathlib/Tactic/Omega/comparisons/b20231120.vo? && coqc Mathlib/Tactic/Omega/comparisons/b20231120.v
  Time (mean ± σ):     371.7 ms ±   5.9 ms    [User: 291.1 ms, System: 74.6 ms]
  Range (min … max):   364.1 ms … 382.7 ms    10 runs

Now about 2.5x faster? Starting Lean takes 423.7 ms, starting Coq takes 258.5 ms
-/

example : True := by
  fail_if_success omega
  trivial

example (_ : (1 : Int) < (0 : Int)) : False := by omega

example (_ : (0 : Int) < (0 : Int)) : False := by omega
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega); trivial

-- example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega
-- example {x : Int} (_ : x % 2 > 5) : False := by omega

-- example {x : Int} (_ : 2 * (x / 2) > x) : False := by omega
-- example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by omega

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

-- example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

-- example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

-- example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

-- example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

-- example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega

example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by omega

-- example {x y : Nat} (h1 : x / 2 - y / 3 < x % 2) (h2 : 3 * x ≥ 2 * y + 4) : False := by omega

-- example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

-- example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by omega

-- example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
--   omega
