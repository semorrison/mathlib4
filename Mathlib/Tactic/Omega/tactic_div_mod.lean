import Mathlib.Tactic.Omega.tactic

theorem Int.mul_ediv_le {x k : Int} (h : k ≠ 0) : k * (x / k) ≤ x :=
  calc k * (x / k)
    _ ≤ k * (x / k) + x % k := Int.le_add_of_nonneg_right (emod_nonneg x h)
    _ = x                   := ediv_add_emod _ _

theorem Int.lt_mul_ediv_add {x k : Int} (h : 0 < k) : x < k * (x / k) + k :=
  calc x
    _ = k * (x / k) + x % k := (ediv_add_emod _ _).symm
    _ < k * (x / k) + k     := Int.add_lt_add_left (emod_lt_of_pos x h) _

namespace Lean.Expr

def isIntDiv? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HDiv.hDiv, #[.const ``Int [], .const ``Int [], .const ``Int [], _, n, d]) => some (n, d)
  | _ => none

/-- Variant of `isIntDiv?` that checks that the denominator is a nonzero numeral. -/
def isIntDivNumeral? (e : Expr) : Option (Expr × Expr) :=
  match e.isIntDiv? with
  | some (n, d) => match d.nat? with
    | none => none
    | some 0 => none
    | some _ => some (n, d)
  | none => none

/-- Find a subexpressions `x / k`,
where `x` is an integer and `k` is an nonzero integer numeral. -/
def findIntDivNumeral (e : Expr) : Option (Expr × Expr) :=
  (e.find? fun s => s.isIntDivNumeral?.isSome) |>.bind isIntDiv?

end Lean.Expr

open Lean Elab Meta
/--
Look through the local hypotheses for any expressions `x / k`,
where `x` is an integer and `k` is an nonzero integer numeral.
-/
def findIntDivNumeral : MetaM (Expr × Expr) := do
  let hyps ← getLocalHyps
  let r ← hyps.findSomeM? fun h => return (← inferType h).findIntDivNumeral
  match r with
  | some (n, d) => return (n, d)
  | none => failure

open Tactic Term

open Parser.Tactic

/--
Looks through the local hypotheses for an expression `x / k`,
where `x` is an integer and `k` is an nonzero integer numeral.

If it finds one, replaces `x / k` with a new variable `y` and adds the inequalities
`k * y ≤ x` and `x < k * y + k`.

Fails it is does not find such an expression.

(There is currently no way to specify the new variable name, or the names of the new hypotheses.)
-/
def generalizeIntDivNumeral : TacticM Unit := withMainContext do
  let (n, d) ← findIntDivNumeral
  let n ← exprToSyntax n
  let d ← exprToSyntax d
  evalTactic (← `(tacticSeq|
    have : $d * ($n / $d) ≤ $n := Int.mul_ediv_le (by decide)
    have : $n < $d * ($n / $d) + $d := Int.lt_mul_ediv_add (by decide)
    generalize $n / $d = y at *))

@[inherit_doc generalizeIntDivNumeral]
syntax "generalize_int_div" : tactic

elab_rules : tactic
  | `(tactic| generalize_int_div) => generalizeIntDivNumeral

syntax "omega_int" : tactic


macro_rules
  | `(tactic| omega_int) => `(tacticSeq |
      exfalso
      simp (config := {failIfUnchanged := false}) only [Int.emod_def] at *
      repeat' generalize_int_div
      omega_int_core)
