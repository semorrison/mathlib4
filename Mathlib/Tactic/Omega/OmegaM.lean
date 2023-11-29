import Mathlib.Tactic.Omega.Problem

set_option autoImplicit true

open Lean Meta

instance [BEq α] [Hashable α] : Singleton α (HashSet α) := ⟨fun x => HashSet.empty.insert x⟩
instance [BEq α] [Hashable α] : Insert α (HashSet α) := ⟨fun a s => s.insert a⟩

instance name_collision : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := match i with
    | .ofNat n => mkApp (.const ``Int.ofNat []) (toExpr n)
    | .negSucc n => mkApp (.const ``Int.negSucc []) (toExpr n)

namespace Omega

structure State where
  /-- The atoms up-to-defeq encountered so far. -/
  atoms : Array Expr := #[]
  /--
  For each atom `((a - b : Nat) : Int)`, which has been encountered but not yet case split,
  the values of `a` and `b`.
  -/
  subs : List (Expr × Expr) := []

abbrev OmegaM' := StateRefT State MetaM

/--
Cache of expressions that have been visited
-/
def Cache : Type := HashMap Expr (LinearCombo × OmegaM' Expr)

abbrev OmegaM := StateRefT Cache OmegaM'

/-- Run a computation in the `OmegaM` monad. -/
def OmegaM.run (m : OmegaM α) : MetaM α := m.run' HashMap.empty |>.run' {}

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : OmegaM Expr := do
  mkListLit (.const ``Int []) (← getThe State).atoms.toList

/--
If a natural number subtraction `((a - b : Nat) : Int)` has been encountered,
return the pair `a` and `b`, and mark this subtraction as done.
-/
def popSub : OmegaM (Option (Expr × Expr)) := do
  modifyGetThe State fun s => match s.subs with
  | [] => (none, s)
  | p :: t => (some p, { s with subs := t })

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
returning a collection of interesting facts about it that should be added to the context,
and, if it is a coercion of a natural subtraction, the operands.
-/
def analyzeAtom (e : Expr) : MetaM (HashSet Expr × Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, e']) => pure ({Expr.app (.const ``Int.ofNat_nonneg []) e'},
    match e'.getAppFnArgs with
    | (``HSub.hSub, #[_, _, _, _, a, b]) => some (a, b)
    | _ => none)
  | (`HDiv.hDiv, #[_, _, _, _, x, k]) => match nat? k with
    | none
    | some 0 => pure (∅, none)
    | some _ =>
      let ne_zero := mkApp3 (.const ``Ne [.succ .zero]) (.const ``Int []) k (toExpr (0 : Int))
      let pos := mkApp4 (.const ``LT.lt [.zero]) (.const ``Int []) (.const ``Int.instLTInt [])
        (toExpr (0 : Int)) k
      pure <|
      ({mkApp3 (.const ``Int.mul_ediv_self_le []) x k (← mkDecideProof ne_zero),
        mkApp3 (.const ``Int.lt_mul_ediv_self_add []) x k (← mkDecideProof pos)}, none)
  | _ => pure (∅, none)

/--
Look up an expression in the atoms, recording it if it has not previously appeared.

Return its index, and, if it is new, a collection of interesting facts about the atom.
* for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
* for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
  `k * a ≤ x < (k + 1) * a`

If the atom is of the form `((a - b : Nat) : Int)`, also record its index and operands in `subs`,
for later case splitting.
-/
def lookup (e : Expr) : OmegaM (Nat × Option (HashSet Expr)) := do
  let c ← getThe State
  for h : i in [:c.atoms.size] do
    have : i < c.atoms.size := h.2
    if ← isDefEq e c.atoms[i] then
      return (i, none)
  trace[omega] "New atom: {e}"
  let (facts, sub) ← analyzeAtom e
  if ← isTracingEnabledFor `omega then
    unless facts.isEmpty do
      trace[omega] "New facts: {← facts.toList.mapM fun e => inferType e}"
  let i ← modifyGetThe State fun c ↦ (c.atoms.size,
    { c with
      atoms := c.atoms.push e,
      subs := if let some (a, b) := sub then (a, b) :: c.subs else c.subs })
  return (i, some facts)

/-- The proof that the trivial `Problem` is satisfied at the atoms. -/
def trivialSat : OmegaM Expr :=
  return .app (.const ``Problem.trivial_sat []) (← atomsList)

end Omega
