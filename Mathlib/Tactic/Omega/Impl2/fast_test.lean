import Mathlib.Tactic.Omega.Impl2.fast

/-
lake build Mathlib.Tactic.Omega.Impl2.fast_test > /dev/null && \
date && git rev-parse HEAD && \
hyperfine "lake env lean Mathlib/Tactic/Omega/Impl2/fast_test.lean"
-/

def ex1 : Problem := Problem.addInequalities {}
    [Inequality.of_eq [7, 12, 31] (-17), Inequality.of_eq [3, 5, 24] (-7)]

def ex1_1 : Problem := ex1.addInequalities [Inequality.of_le [1] 1000]
def ex1_2 : Problem := ex1.addInequalities [Inequality.of_le [0,1] 1000]
def ex1_3 : Problem := ex1.addInequalities [Inequality.of_le [0,0,1] (-8)]
def ex1_all : Problem := ex1.addInequalities [Inequality.of_le [1] 1000, Inequality.of_le [0,1] 1000, Inequality.of_le [0,0,1] (-8)]

-- example : ex1_1.solveEqualities = Problem.addInequalities {} [Inequality.of_le [0,0,-1] 7] := rfl
-- example : ex1_2.solveEqualities = Problem.addInequalities {} [Inequality.of_le [0,0,1] 13] := rfl
-- example : ex1_3.solveEqualities = Problem.addInequalities {} [Inequality.of_le [0,0,1] (-8)] := rfl
example : ex1_1.solveEqualities.possible = true := rfl
example : ex1_2.solveEqualities.possible = true := rfl
example : ex1_3.solveEqualities.possible = true := rfl

example : ex1_all.solveEqualities.possible = false := rfl
