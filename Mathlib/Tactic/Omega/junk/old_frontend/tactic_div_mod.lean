-- import Mathlib.Tactic.Omega.junk.old_frontend.tactic


-- namespace Lean.Expr

-- def isIntDiv? (e : Expr) : Option (Expr × Expr) :=
--   match e.getAppFnArgs with
--   | (``HDiv.hDiv, #[.const ``Int _, .const ``Int _, .const ``Int _, _, n, d]) => some (n, d)
--   | _ => none

-- /-- Variant of `isIntDiv?` that checks that the denominator is a nonzero numeral. -/
-- def isIntDivNumeral? (e : Expr) : Option (Expr × Expr) :=
--   match e.isIntDiv? with
--   | some (n, d) => match d.nat? with
--     | none
--     | some 0 => none
--     | some _ => some (n, d)
--   | none => none

-- /-- Find a subexpressions `x / k`,
-- where `x` is an integer and `k` is an nonzero integer numeral. -/
-- def findIntDivNumeral (e : Expr) : Option (Expr × Expr) :=
--   (e.find? fun s => s.isIntDivNumeral?.isSome) |>.bind isIntDiv?

-- end Lean.Expr

-- open Lean Elab Meta
-- /--
-- Look through the local hypotheses for any expressions `x / k`,
-- where `x` is an integer and `k` is an nonzero integer numeral.
-- -/
-- def findIntDivNumeral : MetaM (Expr × Expr) := do
--   let hyps ← getLocalHyps
--   let r ← hyps.findSomeM? fun h => return (← inferType h).findIntDivNumeral
--   match r with
--   | some (n, d) => return (n, d)
--   | none => failure

-- open Tactic Term

-- open Parser.Tactic

-- /--
-- Looks through the local hypotheses for an expression `x / k`,
-- where `x` is an integer and `k` is an nonzero integer numeral.

-- If it finds one, replaces `x / k` with a new variable `y` and adds the inequalities
-- `k * y ≤ x` and `x < k * y + k`.

-- Fails it is does not find such an expression.

-- (There is currently no way to specify the new variable name, or the names of the new hypotheses.)
-- -/
-- def generalizeIntDivNumeral : TacticM Unit := withMainContext do
--   let (n, d) ← findIntDivNumeral
--   -- TODO we can speed this up, no need for syntax:
--   let n ← exprToSyntax n
--   let d ← exprToSyntax d
--   evalTactic (← `(tacticSeq|
--     have : $d * ($n / $d) ≤ $n := Int.mul_ediv_self_le (by decide)
--     have : $n + 1 ≤ $d * ($n / $d) + $d := Int.lt_mul_ediv_self_add (by decide)
--     generalize $n / $d = y at *))

-- @[inherit_doc generalizeIntDivNumeral]
-- syntax "generalize_int_div" : tactic

-- elab_rules : tactic
--   | `(tactic| generalize_int_div) => generalizeIntDivNumeral

-- syntax "omega_int_div" : tactic

-- macro_rules
--   | `(tactic| omega_int_div) => `(tacticSeq |
--       false_or_by_contra

--       simp (config := {decide := true, failIfUnchanged := false}) only [Int.lt_iff_add_one_le, Int.ge_iff_le, Int.gt_iff_lt, Int.not_lt, Int.not_le, Int.emod_def] at *


--       -- We could speed this up by writing an `Expr.findAll`?
--       repeat' generalize_int_div

--       omega_int_core)
