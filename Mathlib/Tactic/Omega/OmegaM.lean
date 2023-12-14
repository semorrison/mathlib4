import Mathlib.Tactic.Omega.Int
import Mathlib.Tactic.Omega.LinearCombo

set_option autoImplicit true

open Lean Meta

instance [BEq α] [Hashable α] : Singleton α (HashSet α) := ⟨fun x => HashSet.empty.insert x⟩
instance [BEq α] [Hashable α] : Insert α (HashSet α) := ⟨fun a s => s.insert a⟩

instance name_collision : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := match i with
    | .ofNat n => mkApp (.const ``Int.ofNat []) (toExpr n)
    | .negSucc n => mkApp (.const ``Int.negSucc []) (toExpr n)

namespace Std.Tactic.Omega

structure State where
  /-- The atoms up-to-defeq encountered so far. -/
  atoms : Array Expr := #[]

abbrev OmegaM' := StateRefT State MetaM

/--
Cache of expressions that have been visited
-/
def Cache : Type := HashMap Expr (LinearCombo × OmegaM' Expr)

abbrev OmegaM := StateRefT Cache OmegaM'

/-- Run a computation in the `OmegaM` monad. -/
def OmegaM.run (m : OmegaM α) : MetaM α := m.run' HashMap.empty |>.run' {}

def atoms : OmegaM (List Expr) := return (← getThe State).atoms.toList

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : OmegaM Expr := do
  return .app (.const ``Coeffs.ofList []) (← mkListLit (.const ``Int []) (← atoms))

/--
Run an `OmegaM` computation, restoring the state afterwards.
-/
def savingState (t : OmegaM α) : OmegaM α := do
  let state ← getThe State
  let cache ← getThe Cache
  let r ← t
  modifyThe State fun _ => state
  modifyThe Cache fun _ => cache
  pure r

/-- Wrapper around `Expr.nat?` that also allows `Nat.cast`. -/
def nat? (n : Expr) : Option Nat :=
  match n.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => n.nat?
  | _ => n.nat?

/-- Wrapper around `Expr.int?` that also allows `Nat.cast`. -/
def int? (n : Expr) : Option Int :=
  match n.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => n.int?
  | _ => n.int?


/--
Analyzes a newly recorded atom,
returning a collection of interesting facts about it that should be added to the context.
-/
def analyzeAtom (e : Expr) : MetaM (HashSet Expr) := do
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, e']) =>
    let r := {Expr.app (.const ``Int.ofNat_nonneg []) e'}
    return match e'.getAppFnArgs with
    | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      r.insert (mkApp2 (.const ``Int.ofNat_sub_dichotomy []) a b)
    | _ => r
  | (`HDiv.hDiv, #[_, _, _, _, x, k]) => match nat? k with
    | none
    | some 0 => pure ∅
    | some _ =>
      let ne_zero := mkApp3 (.const ``Ne [.succ .zero]) (.const ``Int []) k (toExpr (0 : Int))
      let pos := mkApp4 (.const ``LT.lt [.zero]) (.const ``Int []) (.const ``Int.instLTInt [])
        (toExpr (0 : Int)) k
      pure <|
      {mkApp3 (.const ``Int.mul_ediv_self_le []) x k (← mkDecideProof ne_zero),
        mkApp3 (.const ``Int.lt_mul_ediv_self_add []) x k (← mkDecideProof pos)}
  | _ => pure ∅

/--
Look up an expression in the atoms, recording it if it has not previously appeared.

Return its index, and, if it is new, a collection of interesting facts about the atom.
* for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
* for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
  `k * a ≤ x < (k + 1) * a`
* for each new atom of the form `((a - b : Nat) : Int)`, the fact:
  `b ≤ a ∧ ((a - b : Nat) : Int) = a - b ∨ a < b ∧ ((a - b : Nat) : Int) = 0`
-/
def lookup (e : Expr) : OmegaM (Nat × Option (HashSet Expr)) := do
  let c ← getThe State
  for h : i in [:c.atoms.size] do
    have : i < c.atoms.size := h.2
    if ← isDefEq e c.atoms[i] then
      return (i, none)
  trace[omega] "New atom: {e}"
  let facts ← analyzeAtom e
  if ← isTracingEnabledFor `omega then
    unless facts.isEmpty do
      trace[omega] "New facts: {← facts.toList.mapM fun e => inferType e}"
  let i ← modifyGetThe State fun c ↦ (c.atoms.size,
    { c with
      atoms := c.atoms.push e })
  return (i, some facts)

end Omega
