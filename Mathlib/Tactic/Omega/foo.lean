import Mathlib.Util.Time

import Lean

set_option autoImplicit true

open Lean Meta

namespace Lean.Expr

/-- If the expression is a constant, return that name. Otherwise return `Name.anonymous`. -/
def constName (e : Expr) : Name :=
  e.constName?.getD Name.anonymous

/-- Return the function (name) and arguments of an application. -/
def getAppFnArgs (e : Expr) : Name × Array Expr :=
  withApp e λ e a => (e.constName, a)

def nat? (e : Expr) : Option Nat := do
  guard <| e.isAppOfArity ``OfNat.ofNat 3
  let lit (.natVal n) := e.appFn!.appArg! | none
  n

end Lean.Expr

namespace Lean.Elab.Tactic

def liftMetaTactic' (tac : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => do pure [← tac g]

end Lean.Elab.Tactic

namespace Lean.Meta

def getLocalHyps [Monad m] [MonadLCtx m] : m (Array Expr) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push d.toExpr
  return hs

end Lean.Meta

/-
Let's say I have a type `α` and predicate `P : α → Prop`.

Say I have a function `start : MetaM (α × Expr)` which generates a term `a : α`,
along with an expression representing a proof of `P a`.

Further, I have non-meta functions `run : α → α` and `correct : P a → P (run a)`,
and `check (a : α) : Option (PLift (¬ P a))`.

What I would like to do now is attempt to prove false using these ingredients:
* `let (a, h₁) ← start`
* evaluate `check (run a)`
* if it matches `.some (.up h₂)`, return the expression `h₂ h₁`.
-/
--

def α : Type := Nat
def P : α → Prop := fun a => a = (0 : Nat)

def start : MetaM (α × Expr) := do
  for h in (← getLocalHyps) do
    let t ← inferType h
    match t.getAppFnArgs with
    | (``P, #[n]) => match n.nat? with
      | some n => return (n, h)
      | _ => pure ()
    | _ => pure ()
  throwError "Didn't find a hypothesis."

def run (a : α) : α := Nat.pred a
def correct {a : α} (h : P a) : P (run a) := by
  dsimp [P] at h; subst h; simp [P, run]

def check (a : α) : Option (PLift (¬ P a)) :=
  match a with
  | Nat.zero => none
  | Nat.succ _ => some (.up (by simp [P]))

instance : ToExpr α := inferInstanceAs <| ToExpr Nat

def algorithm (a : α) : Option (PLift (¬ P a)) :=
  match check (run a) with
  | some (.up h) => some (.up (fun w => h (correct w)))
  | none => none

def proveFalse' : MetaM Expr := do
  let (a, h₁) ← start
  let a_expr := toExpr a
  let s ← mkAppM ``algorithm #[a_expr]
  let r ← whnf s
  match r.getAppFnArgs with
    | (``Option.some, #[_, r']) =>
      match r'.getAppFnArgs with
      | (``PLift.up, #[_, h₂]) => return h₂.app h₁
      | _ => unreachable!
    | _ => throwError "failed to prove false"

open Elab Tactic

def proveFalse : TacticM Unit := do
  liftMetaTactic' MVarId.exfalso
  let proof_of_false ← proveFalse'
  closeMainGoal proof_of_false

syntax "proveFalse" : tactic

elab_rules : tactic
  | `(tactic| proveFalse) => proveFalse

example (h : P (16 : Nat)) : False := by
  proveFalse

example (h : P (1 : Nat)) : False := by
  proveFalse -- failed to prove false
