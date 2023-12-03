-- import Mathlib.Tactic.Omega.Impl2.fast

-- /-
-- lake build Mathlib.Tactic.Omega.Impl2.fast_test > /dev/null && \
-- date && git rev-parse HEAD && \
-- hyperfine "lake env lean Mathlib/Tactic/Omega/Impl2/fast_test.lean"
-- -/

-- open Omega (OmegaM)
-- open Omega.ProofProducing

-- def ex1 : Problem := Problem.addEqualities {}
--     [([7, 12, 31], -17, none), ([3, 5, 24], -7, none)]

-- def ex1_1 : Problem := ex1.addInequalities [([1], 1000, none)]
-- def ex1_2 : Problem := ex1.addInequalities [([0,1], 1000, none)]
-- def ex1_3 : Problem := ex1.addInequalities [([0,0,1], -8, none)]
-- def ex1_all : Problem := ex1.addInequalities [([1], 1000, none), ([0,1], 1000, none), ([0,0,1], -8, none)]

-- -- example : ex1_1.solveEqualities = Problem.addInequalities {} [Inequality.of_le [0,0,-1] 7] := rfl
-- -- example : ex1_2.solveEqualities = Problem.addInequalities {} [Inequality.of_le [0,0,1] 13] := rfl
-- -- example : ex1_3.solveEqualities = Problem.addInequalities {} [Inequality.of_le [0,0,1] (-8)] := rfl
-- #eval ex1_1.solveEqualities.possible
-- #eval ex1_2.solveEqualities.possible
-- #eval ex1_3.solveEqualities.possible

-- #eval ex1_all.solveEqualities.possible
-- #eval ex1_all.solveEqualities

-- open Lean Meta
-- #eval show MetaM Expr from OmegaM.run do
--   let t ← ex1_all.solveEqualities.proveFalse?.get!
--   inferType t
