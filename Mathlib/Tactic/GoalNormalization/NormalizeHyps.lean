/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.GoalNormalization.NormalizeNames
import Mathlib.Tactic.GoalNormalization.ReorderHyps
namespace Mathlib.Tactic

open Lean Elab.Tactic Meta

syntax (name := normalize_hyps) "normalize_hyps" : tactic

def iterateUntilPPRepeats (t : MVarId → MetaM MVarId) (g : MVarId) : MetaM MVarId := do
  let mut g ← t g
  let mut results := [toString (← ppGoal g)]
  while results[0]? ≠ results[1]? do
    g ← t g
    results := toString (← ppGoal g) :: results
  return g

def normalizeHyps (goal : MVarId) : MetaM MVarId :=
  iterateUntilPPRepeats (fun g => do normalizeNames (← reorderHyps g)) goal

elab_rules : tactic
  | `(tactic| normalize_hyps) => do liftMetaTactic1 fun g => normalizeHyps g
