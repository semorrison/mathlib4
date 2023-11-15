import Mathlib.Tactic.Omega.tactic_div_mod
import Mathlib.Util.Time
import Mathlib.Tactic.Zify
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Rewrites

set_option autoImplicit true
-- set_option trace.omega.parsing true


namespace Lean.Expr

-- TODO there's another one of these in linarith?
/-- If `e` is of the form `((n : Nat) : Int)`, `isNatCast e` returns `n`. -/
def isNatCast (e: Expr) : Option (Expr) :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => some n
  | _ => none

/--
Find all the atoms in a linear expression
which produce a result under `f : Expr → Option β`.
-/
partial def findInIntLinearExpr (e : Expr) (f : Expr → Option β) [BEq β] [Hashable β] : HashSet β :=
  match e.int? with
  | some _ => ∅
  | none => match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y])
  | (``HSub.hSub, #[_, _, _, _, x, y]) => (x.findInIntLinearExpr f).merge (y.findInIntLinearExpr f)
  | (``Neg.neg, #[_, _, x]) => x.findInIntLinearExpr f
  | (``HMul.hMul, #[_, _, _, _, n, x]) =>
    match n.int? with
    | some _ => x.findInIntLinearExpr f
    | none => match f e with | some b => HashSet.empty.insert b | none => ∅
  -- We look inside `x / n` and `x % n`; these will only be replaced in the `Int` layer of `omega`.
  | (``HDiv.hDiv, #[_, _, _, _, x, n])
  | (``HMod.hMod, #[_, _, _, _, x, n]) =>
    match n.nat? with
    | some _ => x.findInIntLinearExpr f
    | none => match f e with | some b => HashSet.empty.insert b | none => ∅
  | _ => match f e with | some b => HashSet.empty.insert b | none => ∅

/--
Find all the atoms in a comparison of linear expressions
which produce a result under `f : Expr → Option β`.
-/
partial def findInIntLinearComparison (e : Expr) (f : Expr → Option β) [BEq β] [Hashable β] : HashSet β :=
  match e.getAppFnArgs with
  | (``Not, #[p]) => p.findInIntLinearComparison f
  | (``Eq, #[.const ``Int [], x, y])
  | (``LT.lt, #[.const ``Int [], _, x, y])
  | (``LE.le, #[.const ``Int [], _, x, y])
  | (``GT.gt, #[.const ``Int [], _, x, y])
  | (``GE.ge, #[.const ``Int [], _, x, y]) => (x.findInIntLinearExpr f).merge (y.findInIntLinearExpr f)
  | _ => ∅

end Lean.Expr

open Lean Elab Meta

def findNatCasts : MetaM (HashSet Expr) := do
  let hyps ← getLocalHyps
  hyps.foldrM (init := ∅) fun h s => return s.merge <|
    (← inferType h).findInIntLinearComparison fun e => e.isNatCast

open Tactic Term

/--
Look through hypotheses for linear inequalities between integers,
locating casts of natural numbers.

For each such `x`, add the hypothesis `0 ≤ x` if it does not already exist.
-/
def assertNatCastsNonneg : TacticM Unit := withMainContext do
  let casts ← findNatCasts
  let hyps ← ((← getLocalHyps).mapM fun h => inferType h)
  let new := hyps.foldr (init := casts) fun h s => match h.getAppFnArgs with
  | (``LE.le, #[.const ``Int [], _, z, x]) => if z.nat? = some 0 then s.erase x else s
  | _ => s
  for n in new do
    let n ← exprToSyntax n
    evalTactic (← `(tactic| have := Int.ofNat_nonneg $n))

@[inherit_doc assertNatCastsNonneg]
syntax "assert_nat_casts_nonneg" : tactic

elab_rules : tactic
  | `(tactic| assert_nat_casts_nonneg) => assertNatCastsNonneg

open Lean Parser.Tactic

-- I have no idea why we can't just use `false_or_by_contra` here!!
syntax "false_or_by_contra'" : tactic
macro_rules | `(tactic| false_or_by_contra') => `(tactic| first | guard_target = False | by_contra)

-- /--
-- `omega_nat_core` is a simple enrichment of `omega_int`, with basic support for natural numbers.
-- As a pre-processing step, we run `zify` at all hypotheses,
-- and then assert `0 ≤ x` for each `x` a cast of a natural number to the integers
-- that appears in a hypothesis.
-- -/
-- syntax (name := omega_nat_core) "omega_nat_core" : tactic

-- @[inherit_doc omega_nat_core]
-- macro_rules
--   | `(tactic| omega_nat_core) => `(tacticSeq |
--       false_or_by_contra'
--       try zify at *
--       assert_nat_casts_nonneg
--       omega_int)


namespace Lean.Expr

def isNatSubCast? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => match n.getAppFnArgs with
    | (``HSub.hSub, #[_, _, _, _, n, d]) => some (n, d)
    | _ => none
  | _ => none

/-- Find a subexpressions `((a - b : Nat) : Int)`,
where `a` and `b` are natural numbers. -/
def findNatSubCast (e : Expr) : Option (Expr × Expr) :=
  (e.find? fun s => s.isNatSubCast?.isSome) |>.bind isNatSubCast?

end Lean.Expr

/--
Look through the local hypotheses for any expressions `((a - b : Nat) : Int)`,
where `a` and `b` are natural numbers.
-/
def findNatSubCast : MetaM (Expr × Expr) := do
  let hyps ← getLocalHyps
  let r ← hyps.findSomeM? fun h => return (← inferType h).findNatSubCast
  match r with
  | some (n, d) => return (n, d)
  | none => failure

open Tactic Term

theorem Nat.cast_sub' (x y : Nat) :
    ((x - y : Nat) : Int) = if y ≤ x then (x : Int) - (y : Int) else 0 := by
  split <;> rename_i h
  · rw [Nat.cast_sub h]
  · rw [not_le] at h
    rw [Nat.sub_eq_zero_iff_le.mpr (Nat.le_of_lt h)]
    rfl

/--
Look through the local hypotheses for any expressions `((a - b : Nat) : Int)`,
where `a` and `b` are natural numbers.

If such an expression is found, rewrite it as
```
if b ≤ a then (a : Int) - (b : Int) else 0
```
and then split the if.

If no such expression is found, fail.
-/
def splitNatSubCast : TacticM Unit := withMainContext do
  let (a, b) ← findNatSubCast
  let a ← exprToSyntax a
  let b ← exprToSyntax b
  evalTactic (← `(tacticSeq|
    simp only [Nat.cast_sub' $a $b] at *
    by_cases h : $b ≤ $a <;> [simp only [if_pos h] at *; simp only [if_neg h] at *]))

@[inherit_doc splitNatSubCast]
syntax "split_nat_sub_cast" : tactic

elab_rules : tactic
  | `(tactic| split_nat_sub_cast) => splitNatSubCast


-- theorem Nat.lt_iff_add_one_le {x y : Nat} : x < y ↔ x + 1 ≤ y := Iff.rfl
-- theorem Nat.ge_iff_le {x y : Nat} : x ≥ y ↔ y ≤ x := Iff.rfl
-- theorem Nat.gt_iff_lt {x y : Nat} : x ≥ y ↔ y ≤ x := Iff.rfl

theorem Int.ofNat_ne_zero_iff_pos {x : Nat} : ¬ (x : Int) = 0 ↔ 0 < (x : Int) := by
   have h := Int.ofNat_nonneg x
   generalize (x : Int) = x at *
   rcases Int.lt_trichotomy (x : Int) 0 with lt | rfl | gt
   · simpa using lt.not_le h
   · simp
   · simp only [gt, iff_true]
     exact gt.ne.symm


open Mathlib.Tactic.Zify

theorem Int.natCast_ofNat : @Nat.cast Int instNatCastInt (no_index (OfNat.ofNat x)) = OfNat.ofNat x := rfl

def omegaSimpLemmas : List Name := [
    -- zify lemmas:
    ``nat_cast_eq, ``nat_cast_le, ``nat_cast_lt, ``nat_cast_ne, ``nat_cast_dvd,
    -- push_cast lemmas:
    -- ``Nat.cast_zero, ``Nat.cast_one, ``Nat.cast_ofNat,
    ``Int.natCast_zero, ``Int.natCast_one, ``Int.natCast_ofNat,
    ``Int.ofNat_ediv, ``Int.ofNat_add,
    ``Int.ofNat_mul, ``Int.ofNat_emod,
    -- top level (shouldn't do these with simp?)
    ``Int.lt_iff_add_one_le, ``Int.ge_iff_le, ``Int.gt_iff_lt, ``Int.not_lt, ``Int.not_le,
    -- unfold `emod`:
    ``Int.emod_def]

def omegaSimpContext : MetaM Simp.Context := do
  pure <|
  { simpTheorems := #[← omegaSimpLemmas.foldlM (·.addConst ·) {}],
    congrTheorems := {},
    config := {decide := true, failIfUnchanged := false} }

syntax "omega_simp" : tactic

elab_rules : tactic
  | `(tactic| omega_simp) => withMainContext <|
    liftMetaTactic fun g => do
      let (r, _) ← simpGoal g (← omegaSimpContext) (fvarIdsToSimp := ← g.getNondepPropHyps)
      pure <| r.toList.map (·.2)

/--
`omega_int` with additional support for natural numbers.

We lift hypotheses about the natural numbers to the integers, using `zify`.
This will push cast inwards, but `((a - b : Nat) : Int)` will be treated as an atom unless
`b ≤ a` is already in the context.

We assert `0 ≤ x` for every cast of a natural number atom appearing in the hypotheses,
using `assert_nat_casts_nonneg`.

We then call `omega_int`.

If this *fails*, we look for an occurrence of `((a - b : Nat) : Int)`,
split into cases according to
* `b ≤ a` and `((a - b : Nat) : Int) = (a : Int) - (b : Int)` or
* `a < b` and `((a - b : Nat) : Int) = 0`
and then call `omega_nat` again on each of these new problems.

(Note the the processing steps via `zify` and `assert_nat_casts_nonneg` are wastefully repeated
during these case splits; if this is problematic we can make this more efficient.)
-/
syntax "omega_nat" : tactic

macro_rules
  | `(tactic| omega_nat) => `(tacticSeq |
      false_or_by_contra'

      -- simp (config := {decide := true, failIfUnchanged := false}) only
      --   [zify_simps,
      --     -- push_cast lemmas:
      --     push_cast,
      --     -- Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Int.ofNat_ediv, Int.ofNat_add, Int.ofNat_mul,
      --     -- Int.ofNat_emod,
      --     -- top level (shouldn't do these with simp?)
      --     Int.lt_iff_add_one_le, Int.ge_iff_le, Int.gt_iff_lt, Int.not_lt, Int.not_le,
      --     -- unfold `emod`:
      --     Int.emod_def] at *
      omega_simp

      -- Don't use Int.ofNat_ne_zero_iff_pos?

      assert_nat_casts_nonneg
      first
        |
          repeat' generalize_int_div
          -- Why do we need this step?!? Costs 0.4ms in a noop
          simp (config := {decide := false, failIfUnchanged := false}) only [] at *
          omega_int_core
        | split_nat_sub_cast <;> omega_nat
        | fail "omega could not find a contradiction")

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by
  omega_nat

example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by
  omega_int_div

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by
  omega_nat

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by
  omega_nat

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by
  omega_nat

/--
The `omega` tactic, for resolving integer and natural linear arithmetic problems.

It is not yet a full decision procedure (no "dark" or "grey" shadows),
but should be effective on many problems.

We handle hypotheses of the form `x = y`, `x < y`, `x ≤ y` for `x y` in `Nat` or `Int`,
along with negations of inequalities. (We do not do case splits on `h : x ≠ y`.)

We decompose the sides of the inequalities as linear combinations of atoms.

If we encounter `x / n` or `x % n` for literal integers `n` we introduce new auxilliary variables
and the relevant inequalities.

On the first pass, we do not perform case splits on natural subtraction.
If `omega` fails, we recursively perform a case split on
a natural subtraction appearing in a hypothesis, and try again.
-/
syntax "omega" : tactic

macro_rules
  | `(tactic| omega) => `(tactic| omega_nat)

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega

example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by omega

section
-- set_option profiler true
-- set_option profiler.threshold 10

-- #time
example {x y : Nat} (h1 : x / 2 - y / 3 < x % 2) (h2 : 3 * x ≥ 2 * y + 4) : False := by omega

-- #time
example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

-- #time
example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by omega

-- This is out of scope for `omega`, as it has a variable in a denominator.
-- example {x : Int} {m : Nat} (_ : 0 < m) (_ : x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m := by
--   omega

-- Happily `omega` can nevertheless cope with this one, treating `x % m` as at atom.
example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
  omega





-- We'd need to restore using `Int.ofNat_ne_zero_iff_pos`
-- #time
-- example {x : Nat} (h : ¬0 < ((x : Int) + 1) / 2) : (x : Int) = 0 := by omega

-- set_option profiler.threshold 1
-- #time
-- example : True := by
--   fail_if_success done
--   trivial

-- set_option profiler.threshold 1
-- example : True := by
--   fail_if_success omega
--   trivial

end


-- Profiling progress:
-- 1542ms: begin
-- #time
example : True := by
  iterate 100 fail_if_success omega
  trivial


theorem Int.ne_iff_lt_or_gt {a b : Int} : a ≠ b ↔ a < b ∨ b < a := by
  constructor
  · intro h
    simp only [or_iff_not_imp_left]
    intro
    by_contra
    simp_all
    apply h
    apply Int.le_antisymm <;> assumption
  · simp only [or_iff_not_imp_left]
    rintro h rfl
    simp_all

example {x : Int} : x % 2 = 0 ∨ x % 2 = 1 := by
  simp only [or_iff_not_imp_left]
  intro h
  rw [← ne_eq] at h
  rw [Int.ne_iff_lt_or_gt] at h
  cases h <;>
  -- omega should be willing to do one case split, if the goal is an equality!
  apply Int.le_antisymm <;> omega

example {x : Int} : x % 2 = 0 ∨ x % 2 = 1 := by
  by_contra h
  push_neg at h
  aesop_destruct_products
  simp only [Int.ne_iff_lt_or_gt] at *
  casesm* (_ ∨ _) <;> omega
