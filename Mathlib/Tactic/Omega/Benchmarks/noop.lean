import Mathlib.Tactic.Omega.Frontend

set_option maxRecDepth 5000
example : True := by
  iterate 1000 fail_if_success omega
  trivial


/-
```
lake build Mathlib.Tactic.Omega.Benchmarks.noop > /dev/null && \
date && git rev-parse HEAD && \
hyperfine "lake env lean Mathlib/Tactic/Omega/Benchmarks/noop.lean"
```

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

decide := false in the mystery simp
Wed Nov 15 18:39:27 AEDT 2023
90be93b2c59cb02dcc6e99db6273bd6b4d670822
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):      1.039 s ±  0.002 s    [User: 0.777 s, System: 0.254 s]
  Range (min … max):    1.036 s …  1.041 s    10 runs

Wed Nov 15 18:59:24 AEDT 2023
68c754db3ea96b6f52d5452b20fc489eeeae8c17
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):     857.7 ms ±   3.7 ms    [User: 636.7 ms, System: 212.1 ms]
  Range (min … max):   852.0 ms … 864.8 ms    10 runs

Wed Nov 15 19:22:25 AEDT 2023
3ecfc794e75897c9f2c0763ead1e5c4365c357bc
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):     739.1 ms ±   3.6 ms    [User: 554.2 ms, System: 176.0 ms]
  Range (min … max):   734.8 ms … 743.9 ms    10 runs

more de-syntactifying
Wed Nov 15 20:10:22 AEDT 2023
3ecfc794e75897c9f2c0763ead1e5c4365c357bc
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):     737.2 ms ±   3.4 ms    [User: 553.4 ms, System: 175.1 ms]
  Range (min … max):   732.3 ms … 742.3 ms    10 runs

v2; complete rewrite of front end:
Fri Nov 17 22:56:58 AEDT 2023
4ba03a339d641b729d6a8a4ccb9a55c56e3cc9ca
Benchmark 1: lake env lean Mathlib/Tactic/Omega/noop.lean
  Time (mean ± σ):     519.4 ms ±   1.8 ms    [User: 357.7 ms, System: 152.0 ms]
  Range (min … max):   517.4 ms … 522.9 ms    10 runs

Mon Nov 20 21:24:18 AEDT 2023
8987d291c41b59875de4000366a75605ca60c489
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/noop.lean
  Time (mean ± σ):     489.4 ms ±   7.6 ms    [User: 337.8 ms, System: 143.5 ms]
  Range (min … max):   482.3 ms … 506.2 ms    10 runs

Added more bells and whistles on the frontend and have lost some speed:

Mon Dec 11 16:13:46 AEDT 2023
fe17c00be5bb5e31e18f84e82400a82feab03cd3
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/noop.lean
  Time (mean ± σ):     559.3 ms ±   6.1 ms    [User: 361.0 ms, System: 186.2 ms]
  Range (min … max):   552.5 ms … 573.4 ms    10 runs

Change from 100 to 1000 loops so we're actually measuring something.

Mon Dec 11 16:15:01 AEDT 2023
fe17c00be5bb5e31e18f84e82400a82feab03cd3
Benchmark 1: lake env lean Mathlib/Tactic/Omega/Benchmarks/noop.lean
  Time (mean ± σ):      1.746 s ±  0.011 s    [User: 1.153 s, System: 0.581 s]
  Range (min … max):    1.733 s …  1.766 s    10 runs

 -/
