import Mathlib.Tactic.Omega.Problem
import Mathlib.Tactic.Omega.Int
import Mathlib.Tactic.Omega.Impl2.fast

set_option autoImplicit true

open Lean Meta



/--
Given `p : P ∨ Q`, split the goal into two subgoals: one containing the hypothesis `h : P` and another containing `h : Q`.
-/
def _root_.Lean.MVarId.cases2 (mvarId : MVarId) (p : Expr) (hName : Name := `h) : MetaM ((MVarId × FVarId) × (MVarId × FVarId)) := do
  let mvarId ← mvarId.assert `hByCases (← inferType p) p
  let (fvarId, mvarId) ← mvarId.intro1
  let #[s₁, s₂] ← mvarId.cases fvarId #[{ varNames := [hName] }, { varNames := [hName] }] |
    throwError "'cases' tactic failed, unexpected number of subgoals"
  let #[Expr.fvar f₁ ..] ← pure s₁.fields | throwError "'cases' tactic failed, unexpected new hypothesis"
  let #[Expr.fvar f₂ ..] ← pure s₂.fields | throwError "'cases' tactic failed, unexpected new hypothesis"
  return ((s₁.mvarId, f₁), (s₂.mvarId, f₂))

namespace Omega

/--
A partially processed `omega` context.

We have:
* a `ProofProducing.Problem` representing the integer linear constraints extracted so far,
  and their proofs
* the unprocessed `facts : List Expr` taken from the local context,
* the unprocessed `disjunctions : List Expr`,
  which will only be split one at a time if we can't otherwise find a contradiction.

We begin with `facts := ← getLocalHyps` and `problem := .trivial`,
and progressively process the facts.

As we process the facts, we may generate additional facts
(e.g. about coercions and integer divisions).
To avoid duplicates, we maintain a `HashSet` of previously processed facts.

TODO: we may want to solve equalities as we find them.
-/
structure MetaProblem where
  /-- An integer linear arithmetic problem. -/
  problem : ProofProducing.Problem := {}
  /-- Pending facts which have not been processed yet. -/
  facts : List Expr := []
  /-- Pending disjunctions, which we will case split one at a time if we can't get a contradiction. -/
  disjunctions : List Expr := []
  /-- Facts which have already been processed; we keep these to avoid duplicates. -/
  processedFacts : HashSet Expr := ∅

/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

instance : ToExpr LinearCombo where
  toExpr lc :=
    (Expr.const ``LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
  toTypeExpr := .const ``LinearCombo []

instance : ToExpr Problem where
  toExpr p := (Expr.const ``Problem.mk []).app (toExpr p.possible)
    |>.app (toExpr p.equalities) |>.app (toExpr p.inequalities)
  toTypeExpr := .const ``Problem []

/-- Construct the `rfl` proof that `lc.eval atoms = e`. -/
def mkEvalRflProof (e : Expr) (lc : LinearCombo) : OmegaM Expr := do
  mkEqReflWithExpectedType e (mkApp2 (.const ``LinearCombo.eval []) (toExpr lc) (← atomsList))

/-- If `e : Expr` is the `n`-th atom, construct the proof that
`e = (coordinate n).eval atoms`. -/
def mkCoordinateEvalAtomsEq (e : Expr) (n : Nat) : OmegaM Expr := do
  if n < 10 then
    let atoms := (← getThe State).atoms
    let tail ← mkListLit (.const ``Int []) atoms[n+1:].toArray.toList
    let lem := .str ``LinearCombo s!"coordinate_eval_{n}"
    mkEqSymm (mkAppN (.const lem []) (atoms[:n+1].toArray.push tail))
  else
    -- Construct the `rfl` proof that `e = (atoms.get? n).getD 0`
    let atoms ← atomsList
    let n := toExpr n
    let eq ← mkEqReflWithExpectedType e
      (mkApp3 (.const ``Option.getD [.zero]) (.const ``Int [])
        (mkApp3 (.const ``List.get? [.zero]) (.const ``Int []) atoms n) (toExpr (0 : Int)))
    mkEqTrans eq (← mkEqSymm (mkApp2 (.const ``LinearCombo.coordinate_eval []) n atoms))

/-- Construct the linear combination (and its associated proof and new facts) for an atom. -/
def mkAtomLinearCombo (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
  let (n, facts) ← lookup e
  return ⟨LinearCombo.coordinate n, mkCoordinateEvalAtomsEq e n, facts.getD ∅⟩

-- TODO this can be removed at `v4.4.0-rc1`, Kyle has PR'd it to Lean.
@[inherit_doc mkAppN]
macro_rules
  | `(mkAppN $f #[$xs,*]) => (xs.getElems.foldlM (fun x e => `(Expr.app $x $e)) f : MacroM Term)

mutual

/--
Wrapper for `asLinearComboImpl`,
using a cache for previously visited expressions.

Gives a small (10%) speedup in testing.
I tried using a pointer based cache,
but there was never enough subexpression sharing to make it effective.
-/
partial def asLinearCombo (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
  let cache ← get
  match cache.find? e with
  | some (lc, prf) =>
    trace[omega] "Found in cache: {e}"
    return (lc, prf, ∅)
  | none =>
    let r ← asLinearComboImpl e
    modifyThe Cache fun cache => (cache.insert e (r.1, r.2.1.run' cache))
    pure r

/--
Translates an expression into a `LinearCombo`.
Also returns:
* a proof that this linear combo evaluated at the atoms is equal to the original expression
* a list of new facts which should be recorded:
  * for each new atom `a` of the form `((x : Nat) : Int)`, the fact that `0 ≤ a`
  * for each new atom `a` of the form `x / k`, for `k` a positive numeral, the facts that
    `k * a ≤ x < (k + 1) * a`

We also transform the expression as we descend into it:
* pushing coercions: `↑(x + y)`, `↑(x * y)`, `↑(x / k)`, `↑(x % k)`, `↑k`
* unfolding `emod`: `x % k` → `x - x / k`

Finally, the `OmegaM` monad records appearances of `↑(x - y)` atoms, for later case splitting.
-/
partial def asLinearComboImpl (e : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
  trace[omega] "processing {e}"
  match e.int? with
  | some i =>
    let lc := {const := i}
    return ⟨lc, mkEvalRflProof e lc, ∅⟩
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : OmegaM Expr := do
      let add_eval := mkApp3 (.const ``LinearCombo.add_eval []) (toExpr l₁) (toExpr l₂) (← atomsList)
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁ + l₂, prf, facts₁.merge facts₂)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : OmegaM Expr := do
      let sub_eval := mkApp3 (.const ``LinearCombo.sub_eval []) (toExpr l₁) (toExpr l₂) (← atomsList)
      mkEqTrans
        (← mkAppM ``Int.sub_congr #[← prf₁, ← prf₂])
        (← mkEqSymm sub_eval)
    pure (l₁ - l₂, prf, facts₁.merge facts₂)
  | (``Neg.neg, #[_, _, e']) => do
    let (l, prf, facts) ← asLinearCombo e'
    let prf' : OmegaM Expr := do
      let neg_eval := mkApp2 (.const ``LinearCombo.neg_eval []) (toExpr l) (← atomsList)
      mkEqTrans
        (← mkAppM ``Int.neg_congr #[← prf])
        (← mkEqSymm neg_eval)
    pure (-l, prf', facts)
  | (``HMul.hMul, #[_, _, _, _, n, e']) =>
    match int? n with
    | some n' =>
      let (l, prf, facts) ← asLinearCombo e'
      let prf' : OmegaM Expr := do
        let smul_eval := mkApp3 (.const ``LinearCombo.smul_eval []) (toExpr l) n (← atomsList)
        mkEqTrans
          (← mkAppM ``Int.mul_congr_right #[n, ← prf])
          (← mkEqSymm smul_eval)
      pure (l.smul n', prf', facts)
    | none => mkAtomLinearCombo e
  | (``HMod.hMod, #[_, _, _, _, n, k]) => rewrite e (mkApp2 (.const ``Int.emod_def []) n k)
  | (``Nat.cast, #[_, _, n]) => match n.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_add []) a b)
    | (``HMul.hMul, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_mul []) a b)
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_ediv []) a b)
    | (``OfNat.ofNat, #[_, n, _]) => rewrite e (.app (.const ``Int.natCast_ofNat []) n)
    | (``HMod.hMod, #[_, _, _, _, a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_emod []) a b)
    | (``HSub.hSub, #[_, _, _, _, mkAppN (.const ``HSub.hSub _) #[_, _, _, _, a, b], c]) =>
      rewrite e (mkApp3 (.const ``Int.ofNat_sub_sub []) a b c)
    | _ => mkAtomLinearCombo e
  | _ => mkAtomLinearCombo e
where
  rewrite (lhs rw : Expr) : OmegaM (LinearCombo × OmegaM Expr × HashSet Expr) := do
    trace[omega] "rewriting {lhs} via {rw} : {← inferType rw}"
    match (← inferType rw).eq? with
    | some (_, _lhs', rhs) =>
      let (lc, prf, facts) ← asLinearCombo rhs
      let prf' : OmegaM Expr := do mkEqTrans rw (← prf)
      pure (lc, prf', facts)
    | none => panic! "Invalid rewrite rule in 'asLinearCombo'"

end

namespace MetaProblem

/-- The trivial `MetaProblem`, with no facts to processs and a trivial `Problem`. -/
def trivial : MetaProblem where
  problem := {}

instance : Inhabited MetaProblem := ⟨trivial⟩

/--
Add an integer equality to the `Problem`.
-/
-- TODO ambitiously, we could be solving easy equalities as we add them ...
def addIntEquality (p : MetaProblem) (h x : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo x
  let newFacts : HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} = 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := p.problem.addEquality lc.const lc.coeffs
      (some do mkEqTrans (← mkEqSymm (← prf)) h) }

/--
Add an integer inequality to the `Problem`.
-/
def addIntInequality (p : MetaProblem) (h y : Expr) : OmegaM MetaProblem := do
  let (lc, prf, facts) ← asLinearCombo y
  let newFacts : HashSet Expr := facts.fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  trace[omega] "Adding proof of {lc} ≥ 0"
  pure <|
  { p with
    facts := newFacts.toList ++ p.facts
    problem := p.problem.addInequality lc.const lc.coeffs
      (some do mkAppM ``le_of_le_of_eq #[h, (← prf)]) }

/-- Given a fact `h` with type `¬ P`, return a more useful fact obtained by pushing the negation. -/
def pushNot (h P : Expr) : Option Expr := do
  match P.getAppFnArgs with
  | (``LT.lt, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.le_of_not_lt []) x y h)
  | (``LE.le, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.lt_of_not_le []) x y h)
  | (``LT.lt, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.le_of_not_lt []) x y h)
  | (``LE.le, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.lt_of_not_le []) x y h)
  | (``GT.gt, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.le_of_not_lt []) y x h)
  | (``GE.ge, #[.const ``Int [], _, x, y]) => some (mkApp3 (.const ``Int.lt_of_not_le []) y x h)
  | (``GT.gt, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.le_of_not_lt []) y x h)
  | (``GE.ge, #[.const ``Nat [], _, x, y]) => some (mkApp3 (.const ``Nat.lt_of_not_le []) y x h)
  | (``Eq, #[.const ``Nat [], x, y]) => some (mkApp3 (.const ``Nat.lt_or_gt_of_ne []) x y h)
  | (``Eq, #[.const ``Int [], x, y]) => some (mkApp3 (.const ``Int.lt_or_gt_of_ne []) x y h)
  | (``Dvd.dvd, #[.const ``Nat [], _, k, x]) =>
    some (mkApp3 (.const ``Nat.emod_pos_of_not_dvd []) k x h)
  | (``Dvd.dvd, #[.const ``Int [], _, k, x]) =>
    -- This introduces a disjunction that could be avoided by checking `k ≠ 0`.
    some (mkApp3 (.const ``Int.emod_pos_of_not_dvd []) k x h)
  | (``Or, #[P₁, P₂]) => some (mkApp3 (.const ``and_not_not_of_not_or []) P₁ P₂ h)
  | (``And, #[P₁, P₂]) =>
    some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P₁ P₂
      (.app (.const ``Classical.propDecidable []) P₁)
      (.app (.const ``Classical.propDecidable []) P₂) h)
  | _ => none


partial def addFact (p : MetaProblem) (h : Expr) : OmegaM MetaProblem := do
  if ¬ p.problem.possible then
    return p
  else
    let t ← instantiateMVars (← inferType h)
    match t.getAppFnArgs with
    | (``Eq, #[.const ``Int [], x, y]) =>
      match y.int? with
      | some 0 => p.addIntEquality h x
      | _ => p.addFact (mkApp3 (.const ``Int.sub_eq_zero_of_eq []) x y h)
    | (``LE.le, #[.const ``Int [], _, x, y]) =>
      match x.int? with
      | some 0 => p.addIntInequality h y
      | _ => p.addFact (mkApp3 (.const ``Int.sub_nonneg_of_le []) y x h)
    | (``LT.lt, #[.const ``Int [], _, x, y]) =>
      p.addFact (mkApp3 (.const ``Int.add_one_le_of_lt []) x y h)
    | (``GT.gt, #[.const ``Int [], _, x, y]) => p.addFact (mkApp3 (.const ``Int.lt_of_gt []) x y h)
    | (``GE.ge, #[.const ``Int [], _, x, y]) => p.addFact (mkApp3 (.const ``Int.le_of_ge []) x y h)
    | (``GT.gt, #[.const ``Nat [], _, x, y]) => p.addFact (mkApp3 (.const ``Nat.lt_of_gt []) x y h)
    | (``GE.ge, #[.const ``Nat [], _, x, y]) => p.addFact (mkApp3 (.const ``Nat.le_of_ge []) x y h)
    | (``Not, #[P]) => match pushNot h P with
      | none => return p
      | some h' => p.addFact h'
    | (``Eq, #[.const ``Nat [], x, y]) => p.addFact (mkApp3 (.const ``Int.ofNat_congr []) x y h)
    | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
      p.addFact (mkApp3 (.const ``Int.ofNat_lt_of_lt []) x y h)
    | (``LE.le, #[.const ``Nat [], _, x, y]) =>
      p.addFact (mkApp3 (.const ``Int.ofNat_le_of_le []) x y h)
    | (``Dvd.dvd, #[.const ``Nat [], _, k, x]) =>
      p.addFact (mkApp3 (.const ``Nat.mod_eq_zero_of_dvd []) k x h)
    | (``Dvd.dvd, #[.const ``Int [], _, k, x]) =>
      p.addFact (mkApp3 (.const ``Int.mod_eq_zero_of_dvd []) k x h)
    | (``And, #[t₁, t₂]) => do
        (← p.addFact (mkApp3 (.const ``And.left []) t₁ t₂ h)).addFact
          (mkApp3 (.const ``And.right []) t₁ t₂ h)
    | (``Or, #[_, _]) => return { p with disjunctions := p.disjunctions.insert' h }
    | _ => pure p

/--
Process all the facts in a `MetaProblem`.

This is partial because new facts may be generated along the way.
-/
partial def processFacts (p : MetaProblem) : OmegaM MetaProblem := do
  match p.facts with
  | [] => pure p
  | h :: t =>
    if p.processedFacts.contains h then
      processFacts { p with facts := t }
    else
      (← MetaProblem.addFact { p with
        facts := t
        processedFacts := p.processedFacts.insert h } h).processFacts

end MetaProblem

partial def omegaImpl (m : MetaProblem) (g : MVarId) : OmegaM Unit := g.withContext do
  let m' ← m.processFacts
  guard m'.facts.isEmpty
  let p := m'.problem
  trace[omega] "Extracted linear arithmetic problem:\n{← atomsList}\n{p}"
  let p' := if p.possible then p.solveEqualities else p
  let p'' := if p'.possible then p'.run' else p'
  trace[omega] "After elimination:\n{← atomsList}\n{p''}"
  if p''.possible then
    match m'.disjunctions with
    | [] => throwError "omega did not find a contradiction:\n{p''}"
    | h :: t =>
      trace[omega] "Case splitting on {← inferType h}"
      let (⟨g₁, h₁⟩, ⟨g₂, h₂⟩) ← g.cases2 h
      trace[omega] "Adding facts:\n{← g₁.withContext <| inferType (.fvar h₁)}"
      let m₁ := { m' with
        problem := p -- I would really hope that we can use p' here (reuse already solved equations)
        facts := [.fvar h₁]
        disjunctions := t }
      -- Some way to check that the disjunction actually added something usable?
      savingState do omegaImpl m₁ g₁
      trace[omega] "Adding facts:\n{← g₂.withContext <| inferType (.fvar h₂)}"
      let m₂ := { m' with
        problem := p
        facts := [.fvar h₂]
        disjunctions := t }
      omegaImpl m₂ g₂
  else
    match p''.proveFalse? with
    | none => throwError "omega found a contradiction, but didn't produce a proof of False"
    | some prf =>
      trace[omega] "Justification:\n{p''.explanation?.get!}"
      let prf ← instantiateMVars (← prf)
      trace[omega] "omega found a contradiction, proving {← inferType prf}"
      trace[omega] "{prf}"
      g.assign prf

/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def omega (facts : List Expr) (g : MVarId) : MetaM Unit := OmegaM.run do
  omegaImpl { facts } g

/--
Changes the goal to `False`, retaining as much information as possible:

If the goal is `False`, do nothing.
If the goal is `¬ P`, introduce `P`.
If the goal is `x ≠ y`, introduce `x = y`.
Otherwise, for a goal `P`, replace it with `¬ ¬ P` and introduce `¬ P`.
-/
syntax (name := false_or_by_contra) "false_or_by_contra" : tactic

@[inherit_doc false_or_by_contra]
def falseOrByContra (g : MVarId) : MetaM (List MVarId) := do
  match ← g.getType with
  | .const ``False _ => pure [g]
  | .app (.const ``Not _) _
  | mkAppN (.const ``Ne _) #[_, _, _] => pure [(← g.intro1).2]
  | _ => (← g.applyConst ``Classical.byContradiction).mapM fun s => (·.2) <$> s.intro1

open Lean Elab Tactic

elab_rules : tactic
  | `(tactic| false_or_by_contra) => liftMetaTactic falseOrByContra

/--
The `omega` tactic, for resolving integer and natural linear arithmetic problems.

It is not yet a full decision procedure (no "dark" or "grey" shadows),
but should be effective on many problems.

We handle hypotheses of the form `x = y`, `x < y`, `x ≤ y` for `x y` in `Nat` or `Int`,
along with negations of inequalities.

We decompose the sides of the inequalities as linear combinations of atoms.

If we encounter `x / n` or `x % n` for literal integers `n` we introduce new auxiliary variables
and the relevant inequalities.

On the first pass, we do not perform case splits on natural subtraction.
If `omega` fails, we recursively perform a case split on
a natural subtraction appearing in a hypothesis, and try again.
-/
def omegaTactic : TacticM Unit := do
    liftMetaFinishingTactic fun g => do
      let gs ← falseOrByContra g
      _ ← gs.mapM fun g => g.withContext do
        let hyps := (← getLocalHyps).toList
        trace[omega] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
        omega hyps g

@[inherit_doc omegaTactic]
syntax "omega" : tactic

elab_rules : tactic
  | `(tactic| omega) => omegaTactic
