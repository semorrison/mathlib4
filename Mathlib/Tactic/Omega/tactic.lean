import Lean
import Mathlib.Tactic.Omega.Problem
import Mathlib.Util.AtomM
import Qq
/-!
We define the minimally scoped `omega` tactic here.

It does no preprocessing, and just looks for integer linear constraints amongst the hypotheses.
-/


set_option autoImplicit true
set_option relaxedAutoImplicit true

open Lean Elab Tactic Mathlib.Tactic Meta

theorem Int.add_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  subst h₁; subst h₂; rfl

def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

open Qq

open Qq

instance : ToExpr LinearCombo where
  toExpr lc := (Expr.const ``LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
  toTypeExpr := .const ``LinearCombo []

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : AtomM Expr := do
  mkListLit (.const ``Int []) (← get).atoms.toList

def mkEvalRfl (e : Expr) (lc : LinearCombo) : AtomM Expr := do
  mkEqReflWithExpectedType e (← mkAppM ``LinearCombo.eval #[toExpr lc, ← atomsList])

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
    let lc := ⟨i, []⟩
    return ⟨lc, mkEvalRfl e lc⟩
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁) ← asLinearCombo e₁
    let (l₂, prf₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let (_, _, add_eval) ← Meta.forallMetaTelescope (← mkConst' ``LinearCombo.add_eval)
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁.add l₂, prf)
  -- | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
  --   let (l₁, prf₁) ← asLinearCombo e₁
  --   let (l₂, prf₂) ← asLinearCombo e₁
  --   sorry
  -- | (``Neg.neg, #[_, _, e]) => do
  --   let (l, prf) ← asLinearCombo e
  --   sorry
  | _ =>
    logInfo "We don't handle atoms yet."
    failure -- FIXME atoms

attribute [simp] Int.sub_self

theorem Problem.singleEqualitySub_sat {a b : LinearCombo} (h : a.eval v = b.eval v) :
    Problem.sat { equalities := [a.sub b] } v where
  equalities := by simp_all
  inequalities := by simp

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
    let (lhs_lc, lhs_prf) ← asLinearCombo lhs
    let (rhs_lc, rhs_prf) ← asLinearCombo rhs
    let problem : Problem := { equalities := [lhs_lc.sub rhs_lc] }
    let prf : AtomM Expr := do
      let eq ← mkEqTrans (← mkEqSymm (← lhs_prf)) (← mkEqTrans e (← rhs_prf))
      mkAppM ``Problem.singleEqualitySub_sat #[eq]
    pure (problem, prf)
  | _ =>
    logInfo "We don't handle inequalities yet."
    failure -- TODO handle inequalities

/-- The proof that the trivial `Problem` is satisfied by `[]`. -/
def trivial_sat : Expr :=
  .app (.const `Problem.trivial_sat []) (.app (.const `List.nil [.zero]) (.const `Int []))

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
  match satProblems with
  | [] =>
    return (.trivial, trivial_sat)
  | h :: t =>
    t.foldlM (fun ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ => return (p₁.and p₂, ← mkAppM ``Problem.and_sat #[s₁, s₂])) h

-- In fact we don't really need the `Option` here. It's a decision procedure.
-- But for a while it will only be a partial implementation.
def omega_algorithm (p : Problem) : Option p.Solution :=
  let p' := p.processConstants
  if h : p'.possible = false then
    some (.unsat (p'.unsat_of_impossible h ∘ p.processConstants_map))
  else
    none

instance : ToExpr Problem where
  toExpr p := (Expr.const ``Problem.mk []).app (toExpr p.possible) |>.app (toExpr p.equalities) |>.app (toExpr p.inequalities)
  toTypeExpr := .const ``Problem []

def foo {p : Problem} {v} (h : p.sat v) : p := ⟨v, h⟩

def omega (hyps : List Expr) : MetaM Expr := do
  let (p, sat) ← omega_problem hyps
  let p_expr := toExpr p
  let s ← mkAppM ``omega_algorithm #[p_expr]
  let r ← reduce s
  match r.getAppFnArgs with
  | (``Option.some, #[_, s]) =>
    match s.getAppFnArgs with
    | (``Problem.Solution.unsat, #[_, unsat]) => return unsat.app (← mkAppM ``foo #[sat])
    | _ => throwError "found satisfying values!"
  | _ => throwError m!"omega algorithm is incomplete! {r}"

open Qq

axiom a : (7 : Int) = 0

#eval show MetaM _ from do
  inferType (← omega [q(a)])

example : Nat := by
  exact 7

def omega' : TacticM Unit := do
  liftMetaTactic' MVarId.exfalso
  let hyps ← getLocalHyps
  let proof_of_false ← omega hyps.toList
  closeMainGoal proof_of_false

syntax "omega" : tactic

elab_rules : tactic
  | `(tactic| omega) => omega'

example (h : (7 : Int) = 0) : False := by
  omega
