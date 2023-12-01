/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Std.Tactic.GuardMsgs

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta

syntax (name := normalize_names) "normalize_names" : tactic

def normalizeNames (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut lctx ← getLCtx
  let mut i := 0
  for d? in lctx.decls do
    let some d := d? | continue
    lctx := lctx.setUserName d.fvarId s!"h{i}"
    i := i + 1
  let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances)
    (← goal.getType) MetavarKind.syntheticOpaque (← goal.getTag)
  goal.assign mvarNew
  pure mvarNew.mvarId!

elab_rules : tactic
  | `(tactic| normalize_names) => do liftMetaTactic1 fun g => normalizeNames g
