/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Std.Tactic.GuardMsgs

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta

syntax (name := reorder_hyps) "reorder_hyps" : tactic

def topologicalSortM {m} [Monad m] {α : Type _} (l : List α) (lt : α → α → m Bool) : m (List α) :=
  go l []
where
  insert : α → List α → m (List α)
  | a, [] => pure [a]
  | a, h :: t => return if ← lt a h then a :: h :: t else h :: (← insert a t)
  go : List α → List α → m (List α)
  | [], r => pure r
  | h :: t, r => do go t (← insert h r)

def reorderHyps (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut lctx ← getLCtx
  let decls := lctx.decls.toArray.filterMap id
  let ppDecls ← decls.mapM fun d => return (d, toString (← ppExpr d.type))
  let typeSortedDecls : Array LocalDecl :=
    (ppDecls.insertionSort fun ⟨_, t₁⟩ ⟨_, t₂⟩ => t₁ < t₂).map (·.1)
  let topSortedDecls ← topologicalSortM typeSortedDecls.toList fun d₁ d₂ =>
    localDeclDependsOn d₂ d₁.fvarId
  let reindexedDecls := topSortedDecls.enum.map fun ⟨i, d⟩ => d.setIndex i
  lctx := { lctx with
    fvarIdToDecl := reindexedDecls.foldl (init := {}) fun m d => m.insert d.fvarId d
    decls := (reindexedDecls.map Option.some).toPArray' }
  let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances)
    (← goal.getType) MetavarKind.syntheticOpaque (← goal.getTag)
  goal.assign mvarNew
  pure mvarNew.mvarId!

elab_rules : tactic
  | `(tactic| reorder_hyps) => do liftMetaTactic1 fun g => reorderHyps g
