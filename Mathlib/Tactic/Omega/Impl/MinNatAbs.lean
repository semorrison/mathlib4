import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Change
import Mathlib.Tactic.Omega.ForStd

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Classical

namespace List

@[simp] theorem minimum?_nil [Min α] : ([] : List α).minimum? = none := rfl

-- We don't put `@[simp]` on `minimum?_cons`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem minimum?_cons [Min α] {xs : List α} : (x :: xs).minimum? = foldl min x xs := rfl

@[simp] theorem minimum?_eq_none_iff {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  cases xs <;> simp [minimum?]

-- This could be generalized away from `Nat`.
-- The standard library doesn't yet have the order typeclasses
-- that would be necessary for such a generalization.
theorem minimum?_eq_some_iff {xs : List Nat} :
    xs.minimum? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, a ≤ b) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [minimum?]
    simp only [Option.some.injEq, mem_cons, forall_eq_or_imp]
    induction xs generalizing x with
    | nil => constructor <;> simp_all
    | cons x' xs ih =>
      simp only [foldl_cons, mem_cons, forall_eq_or_imp]
      rw [ih]
      constructor
      · rintro ⟨rfl | h₁, h₂, h₃⟩
        · refine ⟨?_, Nat.min_le_left _ _, Nat.min_le_right _ _, h₃⟩
          · rw [Nat.min_def]
            split <;> simp
        · exact ⟨Or.inr (Or.inr h₁), Nat.le_trans h₂ (Nat.min_le_left x x'),
            Nat.le_trans h₂ (Nat.min_le_right x x'), h₃⟩
      · rintro ⟨rfl | rfl | h₁, h₂, h₃, h₄⟩
        · have : min a x' = a := by rw [Nat.min_def, if_pos h₃]
          exact ⟨Or.inl this.symm, by rw [this]; apply Nat.le_refl, h₄⟩
        · have : min x a = a := by
            rw [Nat.min_def]
            by_cases h : x = a
            · simp_all
            · rw [if_neg]
              simpa using Nat.lt_of_le_of_ne h₂ (Ne.symm h)
          exact ⟨Or.inl this.symm, by rw [this]; apply Nat.le_refl, h₄⟩
        · exact ⟨Or.inr h₁, by rw [Nat.min_def]; split <;> assumption, h₄⟩

/--
The minimum non-zero entry in a list of natural numbers, or zero if all entries are zero.

We completely characterize the function via
`nonzeroMinimum_eq_zero_iff` and `nonzeroMinimum_eq_nonzero_iff` below.
-/
def nonzeroMinimum (xs : List Nat) : Nat := xs.filter (· ≠ 0) |>.minimum? |>.getD 0

@[simp] theorem nonzeroMinimum_eq_zero_iff {xs : List Nat} :
    xs.nonzeroMinimum = 0 ↔ ∀ {x}, x ∈ xs → x = 0 := by
  simp [nonzeroMinimum, Option.getD_eq_iff, minimum?_eq_none_iff, minimum?_eq_some_iff,
    filter_eq_nil, mem_filter]

theorem nonzeroMinimum_mem {xs : List Nat} (w : xs.nonzeroMinimum ≠ 0) :
    xs.nonzeroMinimum ∈ xs := by
  dsimp [nonzeroMinimum] at *
  generalize h : (xs.filter (· ≠ 0) |>.minimum?) = m at *
  match m, w with
  | some (m+1), _ => simp_all [minimum?_eq_some_iff, mem_filter]

theorem nonzeroMinimum_pos {xs : List Nat} (m : a ∈ xs) (h : a ≠ 0) : 0 < xs.nonzeroMinimum :=
  Nat.pos_iff_ne_zero.mpr fun w => h (nonzeroMinimum_eq_zero_iff.mp w m)

theorem nonzeroMinimum_le {xs : List Nat} (m : a ∈ xs) (h : a ≠ 0) : xs.nonzeroMinimum ≤ a := by
  have : (xs.filter (· ≠ 0) |>.minimum?) = some xs.nonzeroMinimum := by
    have w := nonzeroMinimum_pos m h
    dsimp [nonzeroMinimum] at *
    generalize h : (xs.filter (· ≠ 0) |>.minimum?) = m? at *
    match m?, w with
    | some m?, _ => rfl
  rw [minimum?_eq_some_iff] at this
  apply this.2
  simp [List.mem_filter]
  exact ⟨m, h⟩

theorem nonzeroMinimum_eq_nonzero_iff {xs : List Nat} {x : Nat} (h : x ≠ 0) :
    xs.nonzeroMinimum = x ↔ x ∈ xs ∧ (∀ y ∈ xs, x ≤ y ∨ y = 0) := by
  constructor
  · rintro rfl
    constructor
    exact nonzeroMinimum_mem h
    intro y m
    by_cases w : y = 0
    · right; exact w
    · left; apply nonzeroMinimum_le m w
  · rintro ⟨m, w⟩
    apply Nat.le_antisymm
    · exact nonzeroMinimum_le m h
    · have nz : xs.nonzeroMinimum ≠ 0 := by
        apply Nat.pos_iff_ne_zero.mp
        apply nonzeroMinimum_pos m h
      specialize w (nonzeroMinimum xs) (nonzeroMinimum_mem nz)
      cases w with
      | inl h => exact h
      | inr h => exfalso; exact nz h

/--
The minimum absolute value of a nonzero entry, or zero if all entries are zero.

We completely characterize the function via
`minNatAbs_eq_zero_iff` and `minNatAbs_eq_nonzero_iff` below.
-/
def minNatAbs (xs : List Int) : Nat := xs.map Int.natAbs |>.nonzeroMinimum

@[simp] theorem minNatAbs_eq_zero_iff {xs : List Int} : xs.minNatAbs = 0 ↔ ∀ y ∈ xs, y = 0 := by
  simp [minNatAbs]

theorem minNatAbs_eq_nonzero_iff (xs : List Int) (w : z ≠ 0) :
    xs.minNatAbs = z ↔
      (∃ y ∈ xs, y.natAbs = z) ∧ (∀ y ∈ xs, z ≤ y.natAbs ∨ y = 0) := by
  simp [minNatAbs, nonzeroMinimum_eq_nonzero_iff w]
