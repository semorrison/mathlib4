import Lean
import Mathlib.Tactic.Omega.Problem
import Mathlib.Tactic.Omega.Impl.Problem
import Mathlib.Util.AtomM
import Qq
/-!
We define the minimally scoped `omega` tactic here.

It does no preprocessing, and just looks for integer linear constraints amongst the hypotheses.
-/


set_option autoImplicit true
set_option relaxedAutoImplicit true

initialize Lean.registerTraceClass `omega

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

def mkEqReflOptionNat (x : Option Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [.succ .zero])
    (mkApp (mkConst ``Option [.zero]) (mkConst ``Nat [])) (toExpr x)

instance : ToExpr Impl.LinearCombo where
  toExpr lc :=
    (Expr.const ``Impl.LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
      -- |>.app (toExpr lc.smallCoeff) |>.app (mkEqReflOptionNat lc.smallCoeff)
  toTypeExpr := .const ``Impl.LinearCombo []

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : AtomM Expr := do
  mkListLit (.const ``Int []) (← get).atoms.toList

def mkEvalRfl (e : Expr) (lc : Impl.LinearCombo) : AtomM Expr := do
  mkEqReflWithExpectedType e (← mkAppM ``Impl.LinearCombo.eval #[toExpr lc, ← atomsList])

/-- If `e : Expr` is the `n`-th atom, construct the proof that
`e = (coordinate n).eval atoms`. -/
def mkCoordinateEvalAtomsEq (e : Expr) (n : Nat) : AtomM Expr := do
  -- Construct the `rfl` proof that `e = (atoms.get? n).getD 0`
  let eq ← mkEqReflWithExpectedType
    e (← mkAppM ``Option.getD #[← mkAppM ``List.get? #[← atomsList, toExpr n], toExpr (0 : Int)])
  mkEqTrans eq (← mkEqSymm (← mkAppM ``Impl.LinearCombo.coordinate_eval #[toExpr n, ← atomsList]))

def mkAtomLinearCombo (e : Expr) : AtomM (Impl.LinearCombo × AtomM Expr) := do
  let n ← AtomM.addAtom e
  return ⟨Impl.LinearCombo.coordinate n, mkCoordinateEvalAtomsEq e n⟩

/--
Given an expression `e`, express it as a linear combination `lc : LinearCombo`
of the atoms seen so far,
and provide an `AtomM Expr` which can be evaluated later
(in particular, when further atoms have been identified)
providing a proof that `e = lc.eval atoms`.
-/
partial def asLinearCombo (e : Expr) : AtomM (Impl.LinearCombo × AtomM Expr) := do
  match e.int? with
  | some i =>
    let lc := {const := i}
    return ⟨lc, mkEvalRfl e lc⟩
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁) ← asLinearCombo e₁
    let (l₂, prf₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let add_eval ← mkAppM ``Impl.LinearCombo.add_eval #[toExpr l₁, toExpr l₂, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁ + l₂, prf)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁) ← asLinearCombo e₁
    let (l₂, prf₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let sub_eval ← mkAppM ``Impl.LinearCombo.sub_eval #[toExpr l₁, toExpr l₂, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.sub_congr #[← prf₁, ← prf₂])
        (← mkEqSymm sub_eval)
    pure (l₁ - l₂, prf)
  | (``Neg.neg, #[_, _, e']) => do
    let (l, prf) ← asLinearCombo e'
    let prf' : AtomM Expr := do
      let neg_eval ← mkAppM ``Impl.LinearCombo.neg_eval #[toExpr l, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.neg_congr #[← prf])
        (← mkEqSymm neg_eval)
    pure (-l, prf')
  | (``HMul.hMul, #[_, _, _, _, n, e']) =>
    match n.int? with
    | some n' =>
      let (l, prf) ← asLinearCombo e'
      let prf' : AtomM Expr := do
        let smul_eval ← mkAppM ``Impl.LinearCombo.smul_eval #[toExpr l, n, ← atomsList]
        mkEqTrans
          (← mkAppM ``Int.mul_congr_right #[n, ← prf])
          (← mkEqSymm smul_eval)
      pure (l.smul n', prf')
    | none => mkAtomLinearCombo e
  | _ => mkAtomLinearCombo e

attribute [simp] Int.sub_self

theorem Impl.Problem.singleEqualitySub_sat {a b : Impl.LinearCombo} (h : a.eval v = b.eval v) :
    Impl.Problem.sat { equalities := [b - a] } v where
  equalities := by simp_all
  inequalities := by simp

theorem Impl.Problem.singleInequalitySub_sat {a b : Impl.LinearCombo} (h : a.eval v ≤ b.eval v) :
    Impl.Problem.sat { inequalities := [b - a] } v where
  equalities := by simp
  inequalities := by simpa using Int.sub_nonneg_of_le h

theorem le_of_eq_of_le {a b c : α} [LE α] (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := by
  subst h₁
  exact h₂

theorem le_of_le_of_eq {a b c : α} [LE α] (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
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
def ofExpr (e : Expr) : AtomM (Impl.Problem × AtomM Expr) := do
  let ty ← inferType e
  match ty.eq? with
  | some (.const ``Int [], lhs, rhs) =>
    let (lhs_lc, lhs_prf) ← asLinearCombo lhs
    let (rhs_lc, rhs_prf) ← asLinearCombo rhs
    let problem : Impl.Problem := { equalities := [rhs_lc.sub lhs_lc] }
    let prf : AtomM Expr := do
      let eq ← mkEqTrans (← mkEqSymm (← lhs_prf)) (← mkEqTrans e (← rhs_prf))
      mkAppM ``Impl.Problem.singleEqualitySub_sat #[eq]
    pure (problem, prf)
  | some _ =>
    -- Equalities in `Nat` will be handled by separate preprocessing.
    throwError "We only handle equalities in `Int`."
  | none =>
    match ty.le? with
    | some (.const ``Int [], lhs, rhs) =>
      let (lhs_lc, lhs_prf) ← asLinearCombo lhs
      let (rhs_lc, rhs_prf) ← asLinearCombo rhs
      let problem : Impl.Problem := { inequalities := [rhs_lc.sub lhs_lc] }
      let prf : AtomM Expr := do
        let ineq ← mkAppM ``le_of_le_of_eq
          #[← mkAppM ``le_of_eq_of_le #[← mkEqSymm (← lhs_prf), e], (← rhs_prf)]
        mkAppM ``Impl.Problem.singleInequalitySub_sat #[ineq]
      pure (problem, prf)
    | some _ =>
      -- Inequalities in `Nat` will be handled by separate preprocessing.
      throwError "We only handle inequalities in `Int`."
    | none =>
      throwError "Expression was not an `=` or `≤`."

/-- The proof that the trivial `Problem` is satisfied by `[]`. -/
def trivial_sat : Expr :=
  .app (.const `Impl.Problem.trivial_sat []) (.app (.const `List.nil [.zero]) (.const `Int []))

open Meta

/--
Given a list of expressions,
which should be the proofs of some integer linear constraints
(equalities and non-strict inequalities),
returns a `p : Problem`,
and an expression representing a proof of `p.sat values` for some `values`.
-/
def omega_problem (hyps : List Expr) : MetaM (Impl.Problem × Expr) := do
  let satProblems : List (Impl.Problem × Expr) ← AtomM.run .default do
    -- Prepare all the problems, accumulating atoms as we go.
    let problems ← hyps.filterMapM fun e => try? (ofExpr e)
    -- Once the atoms are fixed,
    -- prepare the proofs that the problems are all satisfied
    -- at the final list of atoms.
    problems.mapM fun ⟨p, delayedPrf⟩ => return (p, ← delayedPrf)
  -- Combine the problems using `Problem.and`, and the proofs using `Problem.and_sat`:
  match satProblems with
  | [] =>
    return (.trivial, trivial_sat)
  | h :: t =>
    t.foldlM (fun ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ => return (p₁.and p₂, ← mkAppM ``Impl.Problem.and_sat #[s₁, s₂])) h

def omega_algorithm (p : Impl.Problem) : (q : Impl.Problem) × (p → q) :=
  let p₁ := p.normalize
  let p₂ := p₁.processConstants
  let p₃ := p₂.checkContradictions
  let p₄ := p₃.eliminateEasyEqualities
  -- let f : p₀ → p₃ := /-p₃.eliminateEasyEqualities_equiv.mpr ∘ -/p₂.checkContradictions_equiv.mpr ∘ p₁.processConstants_equiv.mpr ∘ p₀.normalize_equiv.mpr
  -- let q := p₃.to
  ⟨p₄, p₃.eliminateEasyEqualities_equiv.mpr ∘ p₂.checkContradictions_equiv.mpr ∘ p₁.processConstants_equiv.mpr ∘ p.normalize_equiv.mpr⟩

-- Eventually we can remove the `Option` here. It's a decision procedure.
-- But for a while it will only be a partial implementation.
def omega_algorithm' (p : Impl.Problem) : Impl.Problem × Option p.Solution :=
  let ⟨q, f⟩ := omega_algorithm p
  if h : q.possible = false then
    (q, some (.unsat (q.unsat_of_impossible h ∘ f)))
  else
    (q, none)

instance : ToExpr Impl.Problem where
  toExpr p := (Expr.const ``Impl.Problem.mk []).app (toExpr p.possible) |>.app (toExpr p.equalities) |>.app (toExpr p.inequalities)
  toTypeExpr := .const ``Impl.Problem []

def Impl.Problem.of {p : Impl.Problem} {v} (h : p.sat v) : p := ⟨v, h⟩

def evalProblem (e : Expr) : MetaM Impl.Problem := unsafe do
  evalExpr Impl.Problem (mkConst ``Impl.Problem) e

def omega (hyps : List Expr) : MetaM Expr := do
  let (p, sat) ← omega_problem hyps
  trace[omega] "{p}"
  let p_expr := toExpr p
  let s ← mkAppM ``omega_algorithm' #[p_expr]
  let r ← profileitM Exception "omega" (← getOptions) do
    whnf s
  match r.getAppFnArgs with
  | (``Prod.mk, #[_, _, q, sol?]) =>
    trace[omega] "{← evalProblem q}"
    match sol?.getAppFnArgs with
    | (``Option.some, #[_, sol]) =>
      match sol.getAppFnArgs with
      | (``Impl.Problem.Solution.unsat, #[_, unsat]) =>
        return unsat.app (← mkAppM ``Impl.Problem.of #[sat])
      | _ => throwError "found satisfying values!"
    | _ => throwError m!"omega algorithm is incomplete!"
  | _ => throwError m!"omega algorithm did not reduce in the kernel: {r}"

open Qq

def omega' : TacticM Unit := do
  liftMetaTactic' MVarId.exfalso
  let hyps ← getLocalHyps
  let proof_of_false ← omega hyps.toList
  closeMainGoal proof_of_false

syntax "omega" : tactic

elab_rules : tactic
  | `(tactic| omega) => omega'
