import Mathlib.Tactic.Omega.Frontend

/-
```
lake build Mathlib.Tactic.Omega.Benchmarks.b20231120 > /dev/null && \
date && git rev-parse HEAD && \
hyperfine "lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean"
```

Mon Nov 20 21:22:44 AEDT 2023
6cae784b3cd9028bd6e507a7b5bf4e2cd06c5d28
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.805 s ±  0.012 s    [User: 3.590 s, System: 0.207 s]
  Range (min … max):    3.788 s …  3.825 s    10 runs

Disable the expression cache:
Mon Nov 20 21:25:54 AEDT 2023
8987d291c41b59875de4000366a75605ca60c489
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.936 s ±  0.010 s    [User: 3.731 s, System: 0.197 s]
  Range (min … max):    3.923 s …  3.957 s    10 runs

introduce hasEquality / hasInequality redirections
Tue Nov 21 14:24:34 AEDT 2023
376ef7d181eb709c00920367b99043bdcf86039b
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.826 s ±  0.013 s    [User: 3.609 s, System: 0.209 s]
  Range (min … max):    3.815 s …  3.849 s    10 runs

Putting everything on one side
Thu Nov 23 18:23:22 AEDT 2023
8c0f95607201c1550b8c06acb5e2423a7da6d82c
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.782 s ±  0.005 s    [User: 3.591 s, System: 0.182 s]
  Range (min … max):    3.773 s …  3.788 s    10 runs

Using specialized coordinate_eval_i
Thu Nov 23 18:55:14 AEDT 2023
bb9af0b5e44cb55d36d7baae6062a53ff94c2134
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.754 s ±  0.006 s    [User: 3.569 s, System: 0.176 s]
  Range (min … max):    3.745 s …  3.765 s    10 runs

Before gcd_spec
Sun Nov 26 17:37:07 AEDT 2023
5562f7bac2590f0a7d6464cab98949bf04e5fb02
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.748 s ±  0.011 s    [User: 3.568 s, System: 0.172 s]
  Range (min … max):    3.730 s …  3.764 s    10 runs

gcd_spec but not taking advantage of it
Sun Nov 26 17:39:23 AEDT 2023
0852452e555aff5b4a1d61111e8eb37ba971dde9
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.845 s ±  0.007 s    [User: 3.622 s, System: 0.214 s]
  Range (min … max):    3.832 s …  3.855 s    10 runs

gcd_spec, at the cost of some new sorries
Sun Nov 26 17:49:58 AEDT 2023
0852452e555aff5b4a1d61111e8eb37ba971dde9
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.739 s ±  0.004 s    [User: 3.550 s, System: 0.180 s]
  Range (min … max):    3.735 s …  3.745 s    5 runs

Use List.any₂
Sun Nov 26 18:29:50 AEDT 2023
31871f94d5809dff7a6c24d1ece9355f0e7ae4ac
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/b20231120.lean
  Time (mean ± σ):      3.226 s ±  0.006 s    [User: 3.036 s, System: 0.180 s]
  Range (min … max):    3.217 s …  3.231 s    5 runs
-/

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
