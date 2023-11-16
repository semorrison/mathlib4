import Lean
import Mathlib.Tactic.Omega.Problem
import Mathlib.Tactic.Omega.Impl.Problem
import Mathlib.Tactic.Zify
import Qq

set_option autoImplicit true

open Lean Meta

instance [BEq α] [Hashable α] : Singleton α (HashSet α) := ⟨fun x => HashSet.empty.insert x⟩
instance [BEq α] [Hashable α] : Insert α (HashSet α) := ⟨fun a s => s.insert a⟩

theorem Int.natCast_ofNat : @Nat.cast Int instNatCastInt (no_index (OfNat.ofNat x)) = OfNat.ofNat x := rfl

theorem Int.ge_iff_le {x y : Int} : x ≥ y ↔ y ≤ x := Iff.rfl
theorem Int.gt_iff_lt {x y : Int} : x > y ↔ y < x := Iff.rfl
theorem Nat.ge_iff_le {x y : Nat} : x ≥ y ↔ y ≤ x := Iff.rfl
theorem Nat.gt_iff_lt {x y : Nat} : x > y ↔ y < x := Iff.rfl

theorem le_of_eq_of_le'' {a b c : α} [LE α] (h₁ : a = b) (h₂ : b ≤ c) : a ≤ c := by
  subst h₁
  exact h₂

theorem le_of_le_of_eq'' {a b c : α} [LE α] (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
  subst h₂
  exact h₁

theorem Int.add_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  subst h₁; subst h₂; rfl

theorem Int.mul_congr_right (a : Int) {c d : Int} (h₂ : c = d) : a * c = a * d := by
  subst h₂; rfl

theorem Int.sub_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a - c = b - d := by
  subst h₁; subst h₂; rfl

theorem Int.neg_congr {a b : Int} (h₁ : a = b) : -a = -b := by
  subst h₁; rfl

namespace Omega

structure AtomM.State where
  /-- The atoms up-to-defeq encountered so far. -/
  atoms : Array Expr := #[]
  /--
  The indices of any atoms of the form `((a - b : Nat) : Int)`,
  along with the values of `a` and `b`,
  which have been encountered but not yet case split. -/
  subs : List (Nat × Expr × Expr) := []

abbrev AtomM := StateRefT AtomM.State MetaM

/-- Run a computation in the `AtomM` monad. -/
def AtomM.run (m : AtomM α) : MetaM α := m.run' {}

/-- Return the `Expr` representing the list of atoms. -/
def atomsList : AtomM Expr := do
  mkListLit (.const ``Int []) (← get).atoms.toList

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
  | (`HDiv.hDiv, #[_, _, _, _, x, k]) => match k.nat? with
    | none
    | some 0 => pure (∅, none)
    | some _ =>
      let ne_zero := mkApp3 (.const ``Ne [.succ .zero]) (.const ``Int []) k (toExpr (0 : Int))
      let pos := mkApp4 (.const ``LT.lt [.zero]) (.const ``Int []) (.const ``Int.instLTInt [])
        (toExpr (0 : Int)) k
      pure <|
      ({mkApp3 (.const ``Int.mul_ediv_le []) x k (← mkDecideProof ne_zero),
        mkApp3 (.const ``Int.lt_mul_ediv_add []) x k (← mkDecideProof pos)}, none)
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
def lookup (e : Expr) : AtomM (Nat × Option (HashSet Expr)) := do
  let c ← get
  for h : i in [:c.atoms.size] do
    have : i < c.atoms.size := h.2
    if ← isDefEq e c.atoms[i] then
      return (i, none)
  let (facts, sub) ← analyzeAtom e
  let i ← modifyGet fun c ↦ (c.atoms.size,
    { c with
      atoms := c.atoms.push e,
      subs := if let some (a, b) := sub then (c.atoms.size, a, b) :: c.subs else c.subs })
  return (i, some facts)

/-- The proof that the trivial `Problem` is satisfied at the atoms. -/
def trivialSat : AtomM Expr :=
  return .app (.const ``Problem.trivial_sat []) (← atomsList)

/--
A partially processed `omega` context.

We have:
* the unprocessed `facts : List Expr` taken from the local context,
* a `Problem` representing the integer linear constraints extracted so far, and
* a proof, wrapped in the `AtomM` monad, that this problem is satisfiable in the local context.

We begin with `facts := ← getLocalHyps` and `problem := .trivial`,
and progressively process the facts.

As we process the facts, we may generate additional facts
(e.g. about coercions and integer divisions).
To avoid duplicates, we maintain a `HashSet` of previously processed facts.

TODO: which should be running the "tidy" steps of the `omega` algorithm as we process facts,
so easy problems with contradictions can be solved quickly.

TODO: we may even want to solve easy equalities as we find them. This would require recording their
solutions and applying the substitutions to all later constraints as they are constructed.
-/
structure MetaProblem where
  /-- Pending facts which have not been processed yet. -/
  facts : List Expr := []
  /-- Facts which have already been processed; we keep these to avoid duplicates. -/
  processedFacts : HashSet Expr := ∅
  /-- An integer linear arithmetic problem. -/
  problem : Problem := .trivial
  /-- A proof, in the `AtomM` monad, that `problem` is satisfiable at the atoms. -/
  sat : AtomM Expr := trivialSat

instance : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := match i with
    | .ofNat n => mkApp (.const ``Int.ofNat []) (toExpr n)
    | .negSucc n => mkApp (.const ``Int.negSucc []) (toExpr n)

instance : ToExpr LinearCombo where
  toExpr lc :=
    (Expr.const ``LinearCombo.mk []).app (toExpr lc.const) |>.app (toExpr lc.coeffs)
  toTypeExpr := .const ``LinearCombo []

instance : ToExpr Problem where
  toExpr p := (Expr.const ``Problem.mk []).app (toExpr p.possible)
    |>.app (toExpr p.equalities) |>.app (toExpr p.inequalities)
  toTypeExpr := .const ``Problem []

/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

/-- Construct the `rfl` proof that `lc.eval atoms = e`. -/
def mkEvalRfl (e : Expr) (lc : LinearCombo) : AtomM Expr := do
  mkEqReflWithExpectedType e (← mkAppM ``LinearCombo.eval #[toExpr lc, ← atomsList])

/-- If `e : Expr` is the `n`-th atom, construct the proof that
`e = (coordinate n).eval atoms`. -/
def mkCoordinateEvalAtomsEq (e : Expr) (n : Nat) : AtomM Expr := do
  -- Construct the `rfl` proof that `e = (atoms.get? n).getD 0`
  let eq ← mkEqReflWithExpectedType
    e (← mkAppM ``Option.getD #[← mkAppM ``List.get? #[← atomsList, toExpr n], toExpr (0 : Int)])
  mkEqTrans eq (← mkEqSymm (← mkAppM ``LinearCombo.coordinate_eval #[toExpr n, ← atomsList]))

/-- Construct the linear combination (and its associated proof and new facts) for an atom. -/
def mkAtomLinearCombo (e : Expr) : AtomM (LinearCombo × AtomM Expr × HashSet Expr) := do
  let (n, facts) ← lookup e
  return ⟨LinearCombo.coordinate n, mkCoordinateEvalAtomsEq e n, facts.getD ∅⟩

def int? (n : Expr) : Option Int :=
  match n.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => n.int?
  | _ => n.int?

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

Finally, the `AtomM` monad records appearances of `↑(x - y)` atoms, for later case splitting.

TODO: Use an unsafe cache, like `Expr.find?`, to take advantage of sharing.
-/
partial def asLinearCombo (e : Expr) : AtomM (LinearCombo × AtomM Expr × HashSet Expr) := do
  trace[omega] "processing {e}"
  match e.int? with
  | some i =>
    let lc := {const := i}
    return ⟨lc, mkEvalRfl e lc, ∅⟩
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let add_eval ← mkAppM ``LinearCombo.add_eval #[toExpr l₁, toExpr l₂, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.add_congr #[← prf₁, ← prf₂])
        (← mkEqSymm add_eval)
    pure (l₁ + l₂, prf, facts₁.merge facts₂)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) => do
    let (l₁, prf₁, facts₁) ← asLinearCombo e₁
    let (l₂, prf₂, facts₂) ← asLinearCombo e₂
    let prf : AtomM Expr := do
      let sub_eval ← mkAppM ``LinearCombo.sub_eval #[toExpr l₁, toExpr l₂, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.sub_congr #[← prf₁, ← prf₂])
        (← mkEqSymm sub_eval)
    pure (l₁ - l₂, prf, facts₁.merge facts₂)
  | (``Neg.neg, #[_, _, e']) => do
    let (l, prf, facts) ← asLinearCombo e'
    let prf' : AtomM Expr := do
      let neg_eval ← mkAppM ``LinearCombo.neg_eval #[toExpr l, ← atomsList]
      mkEqTrans
        (← mkAppM ``Int.neg_congr #[← prf])
        (← mkEqSymm neg_eval)
    pure (-l, prf', facts)
  | (``HMul.hMul, #[_, _, _, _, n, e']) =>
    match int? n with
    | some n' =>
      let (l, prf, facts) ← asLinearCombo e'
      let prf' : AtomM Expr := do
        let smul_eval ← mkAppM ``LinearCombo.smul_eval #[toExpr l, n, ← atomsList]
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
    | (``Nat.mod, #[a, b]) => rewrite e (mkApp2 (.const ``Int.ofNat_emod []) a b)
    | _ => mkAtomLinearCombo e
  | _ => mkAtomLinearCombo e
where
  rewrite (lhs rw : Expr) : AtomM (LinearCombo × AtomM Expr × HashSet Expr) := do
    trace[omega] "rewriting {lhs} via ({rw} : {← inferType rw})"
    match (← inferType rw).eq? with
    | some (_, _lhs', rhs) =>
      -- guard (← isDefEq lhs _lhs')
      let (lc, prf, facts) ← asLinearCombo rhs
      let prf' : AtomM Expr := do
        mkEqTrans (← mkEqSymm rw) (← prf)
      pure (lc, prf', facts)
    | none => panic! "Invalid rewrite rule in 'asLinearCombo'"

namespace MetaProblem

/-- The trivial `MetaProblem`, with no facts to processs and a trivial `Problem`. -/
def trivial : MetaProblem where
  problem := .trivial
  sat := trivialSat

instance : Inhabited MetaProblem := ⟨trivial⟩

/-- The statement that a problem is satisfied at `atomsList`. -/
def satType (p : Problem) : AtomM Expr :=
  return .app (.app (.const ``Problem.sat []) (toExpr p)) (← atomsList)

theorem LinearCombo.sub_eval_zero {a b : LinearCombo} {v : List Int} (h : a.eval v = b.eval v) :
    (b - a).eval v = 0 := by
  simp_all

theorem LinearCombo.sub_eval_nonneg {a b : LinearCombo} {v : List Int} (h : a.eval v ≤ b.eval v) :
    0 ≤ (b - a).eval v := by
  simpa using Int.sub_nonneg_of_le h


/--
Add an integer equality to the `Problem`.
-/
-- TODO ambitiously, we could be solving easy equalities as we add them ...
def addIntEquality (p : MetaProblem) (h x y : Expr) : AtomM MetaProblem := do
  let (lc₁, prf₁, facts₁) ← asLinearCombo x
  let (lc₂, prf₂, facts₂) ← asLinearCombo y
  let newFacts : HashSet Expr := (facts₁.merge facts₂).fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  pure <|
  { facts := newFacts.toList ++ p.facts
    problem := p.problem.addEquality (lc₂ - lc₁)
    sat := do
      let eq ← mkEqTrans (← mkEqSymm (← prf₁)) (← mkEqTrans h (← prf₂))
      mkAppM ``Problem.addEquality_sat
        #[← p.sat, ← mkAppM ``LinearCombo.sub_eval_zero #[eq]] }

/--
Add an integer inequality to the `Problem`.
-/
-- TODO once we've got this working, we should run `tidy` at every step
def addIntInequality (p : MetaProblem) (h x y : Expr) : AtomM MetaProblem := do
  let (lc₁, prf₁, facts₁) ← asLinearCombo x
  let (lc₂, prf₂, facts₂) ← asLinearCombo y
  let newFacts : HashSet Expr := (facts₁.merge facts₂).fold (init := ∅) fun s e =>
    if p.processedFacts.contains e then s else s.insert e
  pure <|
  { facts := newFacts.toList ++ p.facts
    problem := p.problem.addInequality (lc₂ - lc₁)
    sat := do
      let ineq ← mkAppM ``le_of_le_of_eq''
        #[← mkAppM ``le_of_eq_of_le'' #[← mkEqSymm (← prf₁), h], (← prf₂)]
      mkAppM ``Problem.addInequality_sat
        #[← p.sat, ← mkAppM ``LinearCombo.sub_eval_nonneg #[ineq]] }

/-- Given a fact `h` with type `¬ P`, return a more useful fact obtained by pushing the negation. -/
def pushNot (h P : Expr) : MetaM (Option Expr) := do
  match P.getAppFnArgs with
  | (``LT.lt, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_lt []) x y, h])
  | (``LE.le, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_le []) x y, h])
  | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_lt []) x y, h])
  | (``LE.le, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_le []) x y, h])
  | (``GT.gt, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_lt []) y x, h])
  | (``GE.ge, #[.const ``Int [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.not_le []) y x, h])
  | (``GT.gt, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_lt []) y x, h])
  | (``GE.ge, #[.const ``Nat [], _, x, y]) =>
    return some (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.not_le []) y x, h])
  -- TODO add support for `¬ a ∣ b`?
  | _ => return none

open Mathlib.Tactic.Zify

partial def addFact (p : MetaProblem) (h : Expr) : AtomM MetaProblem := do
  if ¬ p.problem.possible then
    return p
  else
    let t ← inferType h
    match t.getAppFnArgs with
    | (``False, #[]) => pure <|
      { facts := []
        problem := .impossible,
        sat := pure (.app (.app (.const ``False.elim []) (← satType p.problem)) h) }
    | (``Not, #[P]) => match ← pushNot h P with
      | none => return p
      | some h' => p.addFact h'
    | (``GT.gt, #[.const ``Int [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.gt_iff_lt []) x y, h])
    | (``GE.ge, #[.const ``Int [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.ge_iff_le []) x y, h])
    | (``GT.gt, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.gt_iff_lt []) x y, h])
    | (``GE.ge, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Nat.ge_iff_le []) x y, h])
    | (``Eq, #[.const ``Nat [], x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``nat_cast_eq []) x y, h])
    | (``LT.lt, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``nat_cast_lt []) x y, h])
    | (``LE.le, #[.const ``Nat [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``nat_cast_le []) x y, h])
    | (``Eq, #[.const ``Int [], x, y]) =>
      p.addIntEquality h x y
    | (``LT.lt, #[.const ``Int [], _, x, y]) =>
      p.addFact (← mkAppM ``Iff.mp #[mkApp2 (.const ``Int.lt_iff_add_one_le []) x y, h])
    | (``LE.le, #[.const ``Int [], _, x, y]) =>
      p.addIntInequality h x y
    -- TODO Add support for `k ∣ b`?
    | _ => pure p

/--
Process all the facts in a `MetaProblem`.

This is partial because new facts may be generated along the way.
-/
partial def processFacts (p : MetaProblem) : AtomM MetaProblem := do
  match p.facts with
  | [] => pure p
  | h :: t =>
    if p.processedFacts.contains h then
      p.processFacts
    else
      (← MetaProblem.addFact { p with
        facts := t
        processedFacts := p.processedFacts.insert h } h).processFacts

end MetaProblem

def runOmega (p : Problem) : Problem :=
  let p₀ := Impl.Problem.of p
  let p₁ := p₀.tidy
  let p₂ := p₁.eliminateEqualities 100
  let p₃ := p₂.eliminateInequalities 100
  p₃.to

def runOmega_map (p : Problem) : p → (runOmega p) :=
  let p₀ := Impl.Problem.of p
  let p₁ := p₀.tidy
  let p₂ := p₁.eliminateEqualities 100
  let p₃ := p₂.eliminateInequalities 100
  Impl.Problem.map_to p₃ ∘ p₂.eliminateInequalities_map 100 ∘ p₁.eliminateEqualities_equiv 100 ∘ p₀.tidy_equiv.mpr ∘ Impl.Problem.map_of p

def unsat_of_impossible {p : Problem} (h : (runOmega p).possible = false) : p.unsat :=
  (runOmega p).unsat_of_impossible h ∘ runOmega_map p

def Problem.of {p : Problem} {v} (h : p.sat v) : p := ⟨v, h⟩

/-- Given a collection of facts, try to prove `False` using the omega algorithm. -/
def omega (facts : List Expr) : MetaM Expr := do
  let m : MetaProblem := { facts }
  let (p, sat) ← AtomM.run do
    let m' ← m.processFacts
    guard m'.facts.isEmpty
    pure (m'.problem, ← m'.sat)
  trace[omega] "{p}"
  if (runOmega p).possible then
    throwError "omega did not find a contradiction" -- TODO later, show a witness?
  else
    let p_expr := toExpr p
    let s ← mkAppM ``Problem.possible #[← mkAppM ``runOmega #[p_expr]]
    let r := (← mkFreshExprMVar (← mkAppM ``Eq #[s, .const ``Bool.false []])).mvarId!
    r.assign (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (.const ``Bool []) (.const ``Bool.false []))
    return (← mkAppM ``unsat_of_impossible #[.mvar r]).app (← mkAppM ``Problem.of #[sat])

syntax "false_or_by_contra" : tactic

def falseOrByContra (g : MVarId) : MetaM (List MVarId) := do
  match ← g.getType with
  | .const ``False _ => pure [g]
  | .app (.const ``Not _) _ => pure [(← g.intro1).2]
  | _ => (← g.applyConst ``Classical.byContradiction).mapM fun s => (·.2) <$> s.intro1

open Lean Elab Tactic

elab_rules : tactic
  | `(tactic| false_or_by_contra) => liftMetaTactic falseOrByContra

/--
`omega` tactic, without splitting natural subtraction.
-/
def omegaTacticCore : TacticM Unit := do
  withMainContext do
    liftMetaTactic falseOrByContra
    let hyps ← getLocalHyps
    let proof_of_false ← omega hyps.toList
    closeMainGoal proof_of_false

syntax "omega_core" : tactic

elab_rules : tactic
  | `(tactic| omega_core) => omegaTacticCore

set_option trace.omega true

example : True := by
  fail_if_success omega_core
  trivial

example (_ : (1 : Int) < (0 : Int)) : False := by omega_core

example (_ : (0 : Int) < (0 : Int)) : False := by omega_core
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega_core); trivial

-- set_option trace.aesop true in
example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega_core
example {x : Int} (_ : x % 2 > 5) : False := by omega_core

example {x : Int} (_ : 2 * (x / 2) > x) : False := by omega_core
example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by omega_core

example (_ : 7 < 3) : False := by omega_core
example (_ : 0 < 0) : False := by omega_core

example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by omega_core
example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega_core

example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 5) (_ : y < 5) : False := by omega_core
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 5) (_ : y < 5) : False := by omega_core

example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by omega_core
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by omega_core

example {x y : Int} (_ : 6 * x + 7 * y = 5) : True := by (fail_if_success omega_core); trivial
example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by omega_core

example {x : Nat} (_ : x < 0) : False := by omega_core

example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by omega_core
