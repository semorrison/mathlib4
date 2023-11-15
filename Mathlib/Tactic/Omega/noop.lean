import Mathlib.Tactic.Omega.tests_nat

example : True := by
  iterate 100 fail_if_success omega
  trivial


/-
* `lake build Mathlib.Tactic.Omega.noop > /dev/null && date && hyperfine "lake env lean Mathlib/Tactic/Omega/noop.lean"`

Fri Nov 10 17:08:19 AEDT 2023
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.841 s ±  0.005 s    [User: 1.446 s, System: 0.387 s]
  Range (min … max):    1.829 s …  1.848 s    10 runs

Skipping `simp only [Int.ofNat_ne_zero_iff_pos]`
Fri Nov 10 17:20:09 AEDT 2023
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.813 s ±  0.004 s    [User: 1.391 s, System: 0.414 s]
  Range (min … max):    1.806 s …  1.819 s    10 runs

Combing the `simp [Int.emod_def]` call into the main `simp` step.
Fri Nov 10 18:31:16 AEDT 2023
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.706 s ±  0.009 s    [User: 1.309 s, System: 0.387 s]
  Range (min … max):    1.695 s …  1.721 s    10 runs

Combine `zify` into the other simp step.
Fri Nov 10 18:50:27 AEDT 2023
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.407 s ±  0.007 s    [User: 1.101 s, System: 0.296 s]
  Range (min … max):    1.400 s …  1.425 s    10 runs

decide := true is worryingly much faster?
Fri Nov 10 19:17:20 AEDT 2023
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.146 s ±  0.004 s    [User: 0.870 s, System: 0.267 s]
  Range (min … max):    1.140 s …  1.153 s    10 runs

Update Mathlib
Wed Nov 15 17:21:39 AEDT 2023
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.145 s ±  0.005 s    [User: 0.870 s, System: 0.267 s]
  Range (min … max):    1.140 s …  1.157 s    10 runs

Don't use syntactical `simp`; build our own Simp.Context
Wed Nov 15 17:32:58 AEDT 2023
cb28e95da74b0d19717fb48bcc80b2c8631c3565
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.042 s ±  0.002 s    [User: 0.783 s, System: 0.251 s]
  Range (min … max):    1.039 s …  1.046 s    10 runs

 -/
