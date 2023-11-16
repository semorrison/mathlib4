import Lean
import Mathlib.Tactic.Omega.Problem
import Mathlib.Tactic.Zify

open Lean Meta

theorem Int.ge_iff_le {x y : Int} : x ≥ y ↔ y ≤ x := Iff.rfl
theorem Int.gt_iff_lt {x y : Int} : x > y ↔ y < x := Iff.rfl
theorem Nat.ge_iff_le {x y : Nat} : x ≥ y ↔ y ≤ x := Iff.rfl
theorem Nat.gt_iff_lt {x y : Nat} : x > y ↔ y < x := Iff.rfl

namespace Omega

structure AtomM.State where
  atoms : Array Expr
  subs : List Nat

abbrev AtomM := StateRefT AtomM.State MetaM

structure MetaProblem where
  /-- Pending facts which have not been processed yet. -/
  facts : List Expr
  /-- An integer linear arithmetic problem. -/
  problem : Problem
  /-- A proof, in the `AtomM` monad, that `problem` is satisfiable at the atoms. -/
  sat : AtomM Expr

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : AtomM Expr := do
  mkListLit (.const ``Int []) (← get).atoms.toList

/-- The proof that the trivial `Problem` is satisfied at the atoms. -/
def trivialSat : AtomM Expr :=
  return .app (.const ``Problem.trivial_sat []) (← atomsList)

instance : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := match i with
    | .ofNat n => mkApp (.const ``Int.ofNat []) (toExpr n)
    | .negSucc n => mkApp (.const ``Int.negSucc []) (toExpr n)

instance : ToExpr LinearCombo where
  toExpr lc :=
    (Expr.const ``LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
  toTypeExpr := .const ``LinearCombo []

instance : ToExpr Problem where
  toExpr p := (Expr.const ``Problem.mk []).app (toExpr p.possible)
    |>.app (toExpr p.equalities) |>.app (toExpr p.inequalities)
  toTypeExpr := .const ``Problem []

/--
Translates an expression into a `LinearCombo`.
Also returns:
* a proof that this linear combo evaluated at the atoms is equal to the original expression
* a list of new facts which should be recorded:
  * for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
  * for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
    `k * a ≤ x < (k + 1) * a`
-/
def asLinearCombo (x : Expr) : AtomM (LinearCombo × AtomM Expr × List Expr) :=
  sorry

namespace MetaProblem

def trivial : MetaProblem where
  facts := []
  problem := .trivial
  sat := trivialSat

instance : Inhabited MetaProblem := ⟨trivial⟩

def satType (p : Problem) : AtomM Expr :=
  return .app (.app (.const ``Problem.sat []) (toExpr p)) (← atomsList)

def addIntEquality (p : MetaProblem) (h x y : Expr) : AtomM MetaProblem := do
  sorry

def addIntInequality (p : MetaProblem) (h x y : Expr) : AtomM MetaProblem := do
  sorry

/-- Given a fact `h` with type `¬ P`, return a more useful fact obtained by pushing the negation. -/
def pushNot (h P : Expr) : MetaM (Option Expr) := do
  match P.getAppFnArgs with
  | (``LT.lt, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_lt []) x y, h])
  | (``LE.le, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_le []) x y, h])
  | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_lt []) x y, h])
  | (``LE.le, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_le []) x y, h])
  | (``GT.gt, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_lt []) y x, h])
  | (``GE.ge, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_le []) y x, h])
  | (``GT.gt, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_lt []) y x, h])
  | (``GE.ge, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_le []) y x, h])
  -- TODO add support for `¬ a ∣ b`?
  | _ => return none

open Mathlib.Tactic.Zify

partial def addFact (p : MetaProblem) (h : Expr) : AtomM MetaProblem := do
  if ¬ p.problem.possible then
    return p
  else
    let t ← inferType h
    match t.getAppFnArgs with
    | (``False, #[]) => pure <|
      { facts := []
        problem := .impossible,
        sat := pure (.app (.app (.const ``False.elim []) (← satType p.problem)) h) }
    | (``Not, #[P]) => match ← pushNot h P with
      | none => return p
      | some h' => p.addFact h'
    | (``GT.gt, #[.const ``Int [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.gt_iff_lt []) x y, h])
    | (``GE.ge, #[.const ``Int [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.ge_iff_le []) x y, h])
    | (``GT.gt, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.gt_iff_lt []) x y, h])
    | (``GE.ge, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.ge_iff_le []) x y, h])
    | (``Eq, #[.const ``Nat [], x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``nat_cast_eq []) x y, h])
    | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``nat_cast_lt []) x y, h])
    | (``LE.le, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``nat_cast_le []) x y, h])
    | (``Eq, #[.const ``Int [], _, x, y]) =>
      p.addIntEquality h x y
    | (``LT.lt, #[.const ``Int [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.lt_iff_add_one_le []) x y, h])
    | (``LE.le, #[.const ``Int [], _, x, y]) =>
      p.addIntInequality h x y
    -- TODO Add support for `k ∣ b`?
    | _ => pure p



end MetaProblem
