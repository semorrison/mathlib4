import Lean
import Mathlib.Tactic.Omega.Problem
import Mathlib.Tactic.Omega.Impl.Problem
import Mathlib.Util.AtomM
import Mathlib.Control.Basic
import Qq
/-!
We define the minimally scoped `omega` tactic here.

It does no preprocessing, and just looks for integer linear constraints amongst the hypotheses.
-/

-- Note to self:
-- When there is something usable, see if it helps with https://github.com/leanprover/lean4/issues/2353


set_option autoImplicit true
set_option relaxedAutoImplicit true

open Lean Elab Tactic Mathlib.Tactic Meta

theorem Int.add_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  subst h₁; subst h₂; rfl

theorem Int.mul_congr_right (a : Int) {c d : Int} (h₂ : c = d) : a * c = a * d := by
  subst h₂; rfl

theorem Int.sub_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a - c = b - d := by
  subst h₁; subst h₂; rfl

theorem Int.neg_congr {a b : Int} (h₁ : a = b) : -a = -b := by
  subst h₁; rfl

def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

open Qq

open Omega

-- def mkEqReflOptionNat (x : Option Nat) : Expr :=
--   mkApp2 (mkConst ``Eq.refl [.succ .zero])
--     (mkApp (mkConst ``Option [.zero]) (mkConst ``Nat [])) (toExpr x)

instance : ToExpr LinearCombo where
  toExpr lc :=
    (Expr.const ``LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
  toTypeExpr := .const ``LinearCombo []

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : AtomM Expr := do
  mkListLit (.const ``Int []) (← get).atoms.toList

def mkEvalRfl (e : Expr) (lc : LinearCombo) : AtomM Expr := do
  mkEqReflWithExpectedType e (← mkAppM ``LinearCombo.eval #[toExpr lc, ← atomsList])

/-- If `e : Expr` is the `n`-th atom, construct the proof that
`e = (coordinate n).eval atoms`. -/
def mkCoordinateEvalAtomsEq (e : Expr) (n : Nat) : AtomM Expr := do
  -- Construct the `rfl` proof that `e = (atoms.get? n).getD 0`
  let eq ← mkEqReflWithExpectedType
    e (← mkAppM ``Option.getD #[← mkAppM ``List.get? #[← atomsList, toExpr n], toExpr (0 : Int)])
  mkEqTrans eq (← mkEqSymm (← mkAppM ``LinearCombo.coordinate_eval #[toExpr n, ← atomsList]))

def mkAtomLinearCombo (e : Expr) : AtomM (LinearCombo × AtomM Expr) := do
  let n ← AtomM.addAtom e
  return ⟨LinearCombo.coordinate n, mkCoordinateEvalAtomsEq e n⟩

/--
Given an expression `e`, express it as a linear combination `lc : LinearCombo`
of the atoms seen so far,
and provide an `AtomM Expr` which can be evaluated later
(in particular, when further atoms have been identified)
providing a proof that `e = lc.eval atoms`.
-/
partial def asLinearCombo (e : Expr) : AtomM (LinearCombo × AtomM Expr) := do
  match e.int? with
  | some i =>
    let lc := {const := i}
    return ⟨lc, mkEvalRfl e lc⟩
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁) ← asLinearCombo e₁
    let (l₂, prf₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let add_eval ← mkAppM ``LinearCombo.add_eval #[toExpr l₁, toExpr l₂, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁ + l₂, prf)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁) ← asLinearCombo e₁
    let (l₂, prf₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let sub_eval ← mkAppM ``LinearCombo.sub_eval #[toExpr l₁, toExpr l₂, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.sub_congr #[← prf₁, ← prf₂])
        (← mkEqSymm sub_eval)
    pure (l₁ - l₂, prf)
  | (``Neg.neg, #[_, _, e']) => do
    let (l, prf) ← asLinearCombo e'
    let prf' : AtomM Expr := do
      let neg_eval ← mkAppM ``LinearCombo.neg_eval #[toExpr l, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.neg_congr #[← prf])
        (← mkEqSymm neg_eval)
    pure (-l, prf')
  | (``HMul.hMul, #[_, _, _, _, n, e']) =>
    match n.int? with
    | some n' =>
      let (l, prf) ← asLinearCombo e'
      let prf' : AtomM Expr := do
        let smul_eval ← mkAppM ``LinearCombo.smul_eval #[toExpr l, n, ← atomsList]
        mkEqTrans
          (← mkAppM ``Int.mul_congr_right #[n, ← prf])
          (← mkEqSymm smul_eval)
      pure (l.smul n', prf')
    | none => mkAtomLinearCombo e
  | _ => mkAtomLinearCombo e

attribute [simp] Int.sub_self

theorem Problem.singleEqualitySub_sat {a b : LinearCombo} (h : a.eval v = b.eval v) :
    Problem.sat { equalities := [b - a] } v where
  equalities := by simp_all
  inequalities := by simp

theorem Problem.singleInequalitySub_sat {a b : LinearCombo} (h : a.eval v ≤ b.eval v) :
    Problem.sat { inequalities := [b - a] } v where
  equalities := by simp
  inequalities := by simpa using Int.sub_nonneg_of_le h

theorem le_of_eq_of_le'' {a b c : α} [LE α] (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := by
  subst h₁
  exact h₂

theorem le_of_le_of_eq'' {a b c : α} [LE α] (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
  subst h₂
  exact h₁

/--
Given an expression `e`, working in the `AtomM` monad to progressively identify atoms,
expresses `e` as a linear programming constraint `p : Problem`
(with either exactly one equality, or exactly one inequality).

Additionally, returns an `AtomM Expr` which can be evaluated later
(in particular, when further atoms have been identified)
which will consist of a proof that `p` is satisfied when evaluated at the atoms.
-/
def ofExpr (e : Expr) : AtomM (Problem × AtomM Expr) := do
  let ty ← inferType e
  match ty.eq? with
  | some (.const ``Int [], lhs, rhs) =>
    trace[omega.parsing] m!"Integer equality: {e} : {ty}"
    let (lhs_lc, lhs_prf) ← asLinearCombo lhs
    let (rhs_lc, rhs_prf) ← asLinearCombo rhs
    let problem : Problem := { equalities := [rhs_lc.sub lhs_lc] }
    let prf : AtomM Expr := do
      let eq ← mkEqTrans (← mkEqSymm (← lhs_prf)) (← mkEqTrans e (← rhs_prf))
      mkAppM ``Problem.singleEqualitySub_sat #[eq]
    pure (problem, prf)
  | some _ =>
    -- Equalities in `Nat` will be handled by separate preprocessing.
    trace[omega.parsing] m!"Discarding non-integer equality: {e} : {ty}"
    throwError "We only handle equalities in `Int`."
  | none =>
    match ty.le? with
    | some (.const ``Int [], lhs, rhs) =>
      trace[omega.parsing] m!"Integer inequality: {e} : {ty}"
      let (lhs_lc, lhs_prf) ← asLinearCombo lhs
      let (rhs_lc, rhs_prf) ← asLinearCombo rhs
      let problem : Problem := { inequalities := [rhs_lc.sub lhs_lc] }
      let prf : AtomM Expr := do
        let ineq ← mkAppM ``le_of_le_of_eq''
          #[← mkAppM ``le_of_eq_of_le'' #[← mkEqSymm (← lhs_prf), e], (← rhs_prf)]
        mkAppM ``Problem.singleInequalitySub_sat #[ineq]
      pure (problem, prf)
    | some _ =>
      -- Inequalities in `Nat` will be handled by separate preprocessing.
      trace[omega.parsing] m!"Discarding non-integer inequality: {e} : {ty}"
      throwError "We only handle inequalities in `Int`."
    | none =>
      trace[omega.parsing] m!"Discarding hypothesis: {e} : {ty}"
      throwError "Expression was not an `=` or `≤`."

/-- The proof that the trivial `Problem` is satisfied by `[]`. -/
def trivial_sat : Expr :=
  .app (.const ``Problem.trivial_sat []) (.app (.const `List.nil [.zero]) (.const `Int []))

open Meta

/--
Given a list of expressions,
which should be the proofs of some integer linear constraints
(equalities and non-strict inequalities),
returns a `p : Problem`,
and an expression representing a proof of `p.sat values` for some `values`.
-/
def omega_problem (hyps : List Expr) : MetaM (Problem × Expr) := do
  let satProblems : List (Problem × Expr) ← AtomM.run .default do
    -- Prepare all the problems, accumulating atoms as we go.
    let problems ← hyps.filterMapM fun e => try? (ofExpr e)
    -- Once the atoms are fixed,
    -- prepare the proofs that the problems are all satisfied
    -- at the final list of atoms.
    problems.mapM fun ⟨p, delayedPrf⟩ => return (p, ← delayedPrf)
  -- Combine the problems using `Problem.and`, and the proofs using `Problem.and_sat`:
  trace[omega] m!"{satProblems.map (·.1)}"
  match satProblems with
  | [] =>
    return (.trivial, trivial_sat)
  | h :: t =>
    t.foldlM (fun ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ => return (p₁.and p₂, ← mkAppM ``Problem.and_sat #[s₁, s₂])) h

def omega_algorithm₁ (p : Problem) : Problem :=
  let p₀ := Impl.Problem.of p
  let p₁ := p₀.tidy
  let p₂ := p₁.eliminateEqualities 100
  let p₃ := p₂.eliminateInequalities 100
  p₃.to

def omega_algorithm₂ (p : Problem) : p → (omega_algorithm₁ p) :=
  let p₀ := Impl.Problem.of p
  let p₁ := p₀.tidy
  let p₂ := p₁.eliminateEqualities 100
  let p₃ := p₂.eliminateInequalities 100
  Impl.Problem.map_to p₃ ∘ p₂.eliminateInequalities_map 100 ∘ p₁.eliminateEqualities_equiv 100 ∘ p₀.tidy_equiv.mpr ∘ Impl.Problem.map_of p

def blah {p : Problem} (h : (omega_algorithm₁ p).possible = false) : p.unsat :=
  -- sorry
  (omega_algorithm₁ p).unsat_of_impossible h ∘ omega_algorithm₂ p

instance : ToExpr Problem where
  toExpr p := (Expr.const ``Problem.mk []).app (toExpr p.possible) |>.app (toExpr p.equalities) |>.app (toExpr p.inequalities)
  toTypeExpr := .const ``Problem []

def Problem.of {p : Problem} {v} (h : p.sat v) : p := ⟨v, h⟩

def evalProblem (e : Expr) : MetaM Problem := unsafe do
  evalExpr Problem (mkConst ``Problem) e

def mkEqFalse'' (e : Expr) : MetaM Expr := mkAppM ``Eq #[e, .const ``Bool.false []]

def omega (hyps : List Expr) : MetaM Expr := do
  let (p, sat) ← omega_problem hyps
  trace[omega] "{p}"
  if (omega_algorithm₁ p).possible then
    throwError "omega did not find a contradiction" -- TODO later, show a witness?
  else
    let p_expr := toExpr p
    let s ← mkAppM ``Problem.possible #[← mkAppM ``omega_algorithm₁ #[p_expr]]
    let r := (← mkFreshExprMVar (← mkAppM ``Eq #[s, .const ``Bool.false []])).mvarId!
    r.assign (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (.const ``Bool []) (.const ``Bool.false []))
    return (← mkAppM ``blah #[.mvar r]).app (← mkAppM ``Problem.of #[sat])

open Qq

theorem Int.ge_iff_le {x y : Int} : x ≥ y ↔ y ≤ x := Iff.rfl
theorem Int.gt_iff_lt {x y : Int} : x > y ↔ y < x := Iff.rfl

syntax "false_or_by_contra" : tactic

def falseOrByContra (g : MVarId) : MetaM (List MVarId) := do
  match ← g.getType with
  | .const ``False _ => pure [g]
  | .app (.const ``Not _) _ => pure [(← g.intro1).2]
  | _ => (← g.applyConst ``Classical.byContradiction).mapM fun s => (·.2) <$> s.intro1


elab_rules : tactic
  | `(tactic| false_or_by_contra) => liftMetaTactic falseOrByContra
  -- `(tactic| first | guard_target = False | by_contra)

/--
`omega` tactic over the integers, with no pre-processing.
-/
def omegaIntCore : TacticM Unit := do
  withMainContext do
    let hyps ← getLocalHyps
    let proof_of_false ← omega hyps.toList
    closeMainGoal proof_of_false

syntax "omega_int_core" : tactic

elab_rules : tactic
  | `(tactic| omega_int_core) => omegaIntCore

open Parser.Tactic

/--
`omega` tactic over the integers, with only minimal pre-processing:
* calls `by_contra`
* replaces `x < y` with `x + 1 ≤ y`
* replaces `x > y` with `y < x` and `x ≥ y` with `y ≤ x`
* replaces `¬ x < y` with `y ≤ x` and `¬ x ≤ y` with `y < x`
-/
def omega_int : TacticM Unit := do
  evalTactic (← `(tacticSeq|
    false_or_by_contra
    simp (config := {decide := true, failIfUnchanged := false}) only [Int.lt_iff_add_one_le, Int.ge_iff_le, Int.gt_iff_lt, Int.not_lt, Int.not_le, Int.emod_def] at *))
  omegaIntCore

syntax "omega_int" : tactic

elab_rules : tactic
  | `(tactic| omega_int) => omega_int