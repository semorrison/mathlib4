import Lean
import Mathlib.Tactic.Omega.Problem
import Mathlib.Util.AtomM
import Qq
/-!
We define the minimally scoped `omega` tactic here.

It does no preprocessing, and just looks for integer linear constraints amongst the hypotheses.
-/

open Lean Elab Tactic Mathlib.Tactic Meta

/--
Given an expression `e`, express it as a linear combination `lc : LinearCombo`
of the atoms seen so far,
and provide an `AtomM Expr` which can be evaluated later
(in particular, when further atoms have been identified)
providing a proof that `e = lc.eval atoms`.
-/
partial def asLinearCombo (e : Expr) : AtomM (LinearCombo × AtomM Expr) := do
  match e.int? with
  | some i => return (⟨i, []⟩, mkEqRefl e)
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁) ← asLinearCombo e₁
    let (l₂, prf₂) ← asLinearCombo e₁
    sorry
  -- | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
  --   let (l₁, prf₁) ← asLinearCombo e₁
  --   let (l₂, prf₂) ← asLinearCombo e₁
  --   sorry
  -- | (``Neg.neg, #[_, _, e]) => do
  --   let (l, prf) ← asLinearCombo e
  --   sorry
  | _ => sorry

open Qq

axiom a : Int
axiom b : Int
#eval q(a * b)

/--
Given an expression `e`, working in the `AtomM` monad to progressively identify atoms,
expresses `e` as a linear programming constraint `p : Problem`
(with either exactly one equality, or exactly one inequality).

Additionally, returns an `AtomM Expr` which can be evaluated later
(in particular, when further atoms have been identified)
which will consist of a proof that `p` is satisfied when evaluated at the atoms.
-/
def ofExpr (e : Expr) : AtomM (Problem × AtomM Expr) := sorry

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
    let problems ← hyps.mapM ofExpr
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
