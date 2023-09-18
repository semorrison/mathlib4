import Std
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Have

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
# Abstract description of integer linear programming problems.

We define `LinearCombo`, `Problem`, and `DisjunctiveProblem`.
These are abstract descriptions of integer linear programming problems.

In particular, they are intended to be easy to reason about,
but need not be fast to compute with.

-/

structure LinearCombo where
  const : Int
  coeffs : List Int
deriving DecidableEq

namespace LinearCombo

def eval (lc : LinearCombo) (values : List Int) : Int :=
  (lc.coeffs.zip values).foldl (fun r ⟨c, v⟩ => r + c * v) lc.const

-- Prove some alternative formulas for `eval`? Which to use?
-- theorem eval_eq (lc : LinearCombo) (values : List Int) :
--   lc.eval values = lc.const + (List.zipWith (· * ·) lc.coeffs values).sum := sorry

end LinearCombo

structure Problem where
  possible : Bool := true
  equalities : List LinearCombo := []
  inequalities : List LinearCombo := []

namespace Problem

structure sat (p : Problem) (values : List Int) : Prop where
  possible : p.possible = true
  equalities : lc ∈ p.equalities → lc.eval values = 0
  inequalities : lc ∈ p.inequalities → lc.eval values ≥ 0

def solutions (p : Problem) : Type :=
  { values // p.sat values }

instance : CoeSort Problem Type where
  coe := solutions

def unsat (p : Problem) : Prop := p → False

inductive Solution (p : Problem)
| sat : p.solutions → Solution p
| unsat : p.unsat → Solution p

end Problem

structure DisjunctiveProblem where
  problems : List Problem

namespace DisjunctiveProblem

def sat (d : DisjunctiveProblem) (values : List Int) : Prop :=
  ∃ p ∈ d.problems, p.sat values

def solutions (p : DisjunctiveProblem) : Type :=
  { values // p.sat values }

instance : CoeSort DisjunctiveProblem Type where
  coe := solutions

def unsat (p : DisjunctiveProblem) : Prop := p → False

inductive Solution (d : DisjunctiveProblem)
| sat : d.sat values → Solution d
| unsat : d.unsat → Solution d

end DisjunctiveProblem

/-!
Erasing an inequality results in a larger solution space.
-/
namespace Problem

/-- Erase an inequality from a problem. -/
@[simps]
def eraseInequality (p : Problem) (lc : LinearCombo) : Problem :=
  { p with inequalities := p.inequalities.erase lc }

/-- Any solution gives a solution after erasing an inequality. -/
def eraseInequality_map (p : Problem) (lc : LinearCombo) : p → p.eraseInequality lc :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m => s.inequalities (by simp at m; apply List.mem_of_mem_erase m) }⟩

end Problem

/-!
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

If `a ≤ b`, then the non-negative set for `a` is a subset of the non-negative set for `b`.

(Note this is only a preorder, not even a partial order,
as we don't allow for rescaling when comparing coefficients.)

We show:
```
a < b → a ∈ p.inequalities → p.eraseInequality b → p
```
-/

namespace LinearCombo

def le (a b : LinearCombo) : Prop :=
  a.coeffs = b.coeffs ∧ a.const ≤ b.const

instance : LE LinearCombo := ⟨le⟩

@[simp]
theorem le_def (a b : LinearCombo) : a ≤ b ↔ a.coeffs = b.coeffs ∧ a.const ≤ b.const := Iff.rfl

theorem eval_le_of_le {a b : LinearCombo} (h : a ≤ b) (v : List Int) : a.eval v ≤ b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rcases h with ⟨rfl, h⟩
  simp_all
  generalize List.zip _ _ = p
  -- This should be some general fact, but we can just bash it out.
  -- Perhaps might be easier with alternative formulas for `eval`.
  induction p generalizing a b h with
  | nil => simpa
  | cons x p ih =>
    simp only [List.foldl_cons]
    apply ih
    apply Int.add_le_add_right h

theorem evalNonneg_of_le {a b : LinearCombo} (h : a ≤ b) : a.eval v ≥ 0 → b.eval v ≥ 0 :=
  fun w => Int.le_trans w (eval_le_of_le h v)

def lt (a b : LinearCombo) : Prop :=
  a ≤ b ∧ a ≠ b

instance instLinearComboLT : LT LinearCombo := ⟨lt⟩

@[simp]
theorem lt_def (a b : LinearCombo) : a < b ↔ a.coeffs = b.coeffs ∧ a.const < b.const := by
  dsimp [instLinearComboLT, lt]
  rw [le_def]
  rcases a with ⟨a, as⟩; rcases b with ⟨b, bs⟩
  simp only [mk.injEq]
  constructor
  · rintro ⟨⟨rfl, le⟩, h⟩
    simp_all only [and_true, true_and]
    exact Int.lt_iff_le_and_ne.mpr ⟨le, h⟩
  · rintro ⟨rfl, lt⟩
    simp only [true_and, and_true]
    exact ⟨Int.le_of_lt lt, Int.ne_of_lt lt⟩

theorem eval_lt_of_lt {a b : LinearCombo} (h : a < b) (v : List Int) : a.eval v < b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rw [lt_def] at h
  rcases h with ⟨rfl, h⟩
  simp_all
  generalize List.zip _ _ = p
  -- This should be some general fact, but we can just bash it out.
  -- Perhaps might be easier with alternative formulas for `eval`.
  induction p generalizing a b h with
  | nil => simpa
  | cons x p ih =>
    simp only [List.foldl_cons]
    apply ih
    apply Int.add_lt_add_right h

end LinearCombo

namespace Problem

-- TODO find a home
theorem List.mem_iff_mem_erase_or_eq [DecidableEq α] (l : List α) (a b : α) :
    a ∈ l ↔ (a ∈ l.erase b ∨ (a = b ∧ b ∈ l)) := by
  by_cases h : a = b
  · subst h
    simp [or_iff_right_of_imp List.mem_of_mem_erase]
  · simp_all

def eraseRedundantInequality
    (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) :
    p.eraseInequality b → p :=
  fun ⟨v, s⟩ => ⟨v, { s with
    inequalities := fun m' => by
      rw [List.mem_iff_mem_erase_or_eq _ _ b] at m'
      rcases m' with m' | ⟨rfl, m'⟩
      · apply s.inequalities
        exact m'
      · rcases lt with ⟨le, ne⟩
        apply LinearCombo.evalNonneg_of_le le
        apply s.inequalities
        simpa using (List.mem_erase_of_ne ne).mpr m }⟩

end Problem

theorem List.zip_map_left (l₁ : List α) (l₂ : List β) (f : α → γ) :
    List.zip (l₁.map f) l₂ = (List.zip l₁ l₂).map fun p => (f p.1, p.2) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

theorem List.zip_map_right (l₁ : List α) (l₂ : List β) (f : β → γ) :
    List.zip l₁ (l₂.map f) = (List.zip l₁ l₂).map fun p => (p.1, f p.2) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all

namespace LinearCombo

@[simps]
def neg (lc : LinearCombo) : LinearCombo where
  const := -lc.const
  coeffs := lc.coeffs.map (-·)

@[simp]
theorem neg_eval (lc : LinearCombo) (v : List Int) : lc.neg.eval v = - lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp only [eval, neg_const, neg_coeffs]
  rw [List.zip_map_left, List.foldl_map]
  generalize coeffs.zip v = ps
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp_all only [List.foldl_cons]
    rw [Int.neg_mul, ← Int.neg_add, ih]

theorem contradiction_of_neg_lt (p : Problem) {a b : LinearCombo}
    (ma : a ∈ p.inequalities) (mb : b ∈ p.inequalities) (w : a < b.neg) : p → False := by
  rintro ⟨v, s⟩
  have := LinearCombo.eval_lt_of_lt w v
  simp only [neg_eval] at this
  apply Int.lt_irrefl 0 (Int.lt_of_lt_of_le (Int.lt_of_le_of_lt (s.inequalities ma) this)
    (Int.neg_le_neg (s.inequalities mb)))

/--
We verify that `x - 1 ≥ 0` and `-x ≥ 0` have no solutions.
-/
example : let p : Problem := { inequalities := [⟨-1, [1]⟩, ⟨0, [-1]⟩] }; p → False := by
  apply contradiction_of_neg_lt (a := ⟨-1, [1]⟩) (b := ⟨0, [-1]⟩) <;> simp

end LinearCombo
