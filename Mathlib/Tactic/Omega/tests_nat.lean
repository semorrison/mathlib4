import Mathlib.Tactic.Omega.tactic_div_mod
import Mathlib.Util.Time
import Mathlib.Tactic.Zify
import Mathlib.Data.Int.Basic

-- set_option trace.omega.parsing true

syntax "omega_nat_core" : tactic

open Lean Parser.Tactic

macro_rules
  | `(tactic| omega_nat_core) => `(tacticSeq |
      exfalso
      try zify at *
      omega_int)

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by
  omega_nat_core

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by
  omega_nat_core

example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by
  omega_nat_core

namespace Lean.Expr

open Qq

#eval q((3 - 7 : Nat) : Int)

def isNatSubCast? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => match n.getAppFnArgs with
    | (``HSub.hSub, #[.const ``Nat [], .const ``Nat [], .const ``Nat [], _, n, d]) => some (n, d)
    | _ => none
  | _ => none

/-- Find a subexpressions `((a - b : Nat) : Int)`,
where `a` and `b` are natural numbers. -/
def findNatSubCast (e : Expr) : Option (Expr × Expr) :=
  (e.find? fun s => s.isNatSubCast?.isSome) |>.bind isNatSubCast?

end Lean.Expr

open Lean Elab Meta
/--
Look through the local hypotheses for any expressions `((a - b : Nat) : Int)`,
where `a` and `b` are natural numbers.
-/
def findNatSubCast : MetaM (Expr × Expr) := do
  let hyps ← getLocalHyps
  let r ← hyps.findSomeM? fun h => return (← inferType h).findNatSubCast
  match r with
  | some (n, d) => return (n, d)
  | none => failure

open Tactic Term

theorem Nat.cast_sub' (x y : Nat) :
    ((x - y : Nat) : Int) = if y ≤ x then (x : Int) - (y : Int) else 0 := by
  split <;> rename_i h
  · rw [Nat.cast_sub h]
  · rw [not_le] at h
    rw [Nat.sub_eq_zero_iff_le.mpr (Nat.le_of_lt h)]
    rfl

/--
Look through the local hypotheses for any expressions `((a - b : Nat) : Int)`,
where `a` and `b` are natural numbers.

If such an expression is found, rewrite it as
```
if b ≤ a then (a : Int) - (b : Int) else 0
```
and then split the if.

If no such expression is found, fail.
-/
def splitNatSubCast : TacticM Unit := withMainContext do
  let (a, b) ← findNatSubCast
  let a ← exprToSyntax a
  let b ← exprToSyntax b
  evalTactic (← `(tactic| simp only [Nat.cast_sub' $a $b] at *))
  evalTactic (← `(tactic| by_cases h : $b ≤ $a <;> [simp only [if_pos h] at *; simp only [if_neg h] at *]))

@[inherit_doc splitNatSubCast]
syntax "split_nat_sub_cast" : tactic

elab_rules : tactic
  | `(tactic| split_nat_sub_cast) => splitNatSubCast

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y + 1 ≤ x) : False := by
  zify at *
  split_nat_sub_cast
  omega_nat_core
  omega_nat_core

syntax "omega_nat" : tactic

macro_rules
  | `(tactic| omega_nat) => `(tacticSeq |
      exfalso
      try zify at *
      first | omega_nat_core | split_nat_sub_cast <;> omega_nat | fail "omega could not find a contradiction")

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by
  omega_nat

example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by
  omega_int

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by
  omega_nat

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by
  omega_nat

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by
  omega_nat

syntax "omega" : tactic

macro_rules
  | `(tactic| omega) => `(tactic| omega_nat)

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega
