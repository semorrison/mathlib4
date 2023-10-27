import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Change

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
-- that would be neccessary for such a generalization.
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

def minNatAbs? (xs : List Int) : Option Nat :=
  match xs with
  | [] => none
  | x :: xs => if x = 0 then
      xs.minNatAbs?
    else match xs.minNatAbs? with
      | none => some x.natAbs
      | some m => some (min x.natAbs m)

@[simp]
theorem minNatAbs?_eq_none_iff {xs : List Int} : xs.minNatAbs? = none ↔ ∀ y ∈ xs, y = 0 := by
  constructor
  · intro w
    induction xs with
    | nil => simp_all [minNatAbs?]
    | cons x xs ih =>
      simp only [minNatAbs?] at w
      split at w <;> rename_i h
      · intro y m
        simp only [mem_cons] at m
        rcases m with rfl | m
        · assumption
        · exact ih w y m
      · split at w <;> simp_all
  · induction xs <;> simp_all [minNatAbs?]

@[simp] theorem minNatAbs?_ne_some_zero {xs : List Int} : xs.minNatAbs? ≠ some 0 := by
  induction xs with
  | nil => simp_all [minNatAbs?]
  | cons x xs ih =>
    simp only [minNatAbs?]
    split
    · assumption
    · cases h : minNatAbs? xs
      · simp_all
      · simp
        intro h
        rw [Nat.min_def] at h
        split at h <;> simp_all

theorem minNatAbs?_exists_of_eq_some {xs : List Int} (w : xs.minNatAbs? = some z) :
    ∃ y ∈ xs, y.natAbs = z := by
  induction xs with
  | nil => simp_all [minNatAbs?]
  | cons x xs ih =>
    simp only [minNatAbs?] at w
    split at w
    · specialize ih w
      obtain ⟨x, m, rfl⟩ := ih
      exact ⟨x, mem_cons_of_mem _ m, rfl⟩
    · split at w
      · simp only [Option.some.injEq] at w
        refine ⟨x, mem_cons_self x xs, w⟩
      · simp only [Option.some.injEq] at w
        rename_i h'
        rw [Nat.min_def] at w
        split at w
        · refine ⟨x, mem_cons_self x xs, w⟩
        · subst w
          obtain ⟨x, m, rfl⟩ := ih h'
          refine ⟨x, mem_cons_of_mem _ m, rfl⟩

theorem minNatAbs?_forall_of_eq_some {xs : List Int} (w : xs.minNatAbs? = some z) :
    ∀ y ∈ xs, z ≤ y.natAbs ∨ y = 0 := by
  induction xs generalizing z with
  | nil => simp_all [minNatAbs?]
  | cons x xs ih =>
    simp only [minNatAbs?] at w
    split at w
    · specialize ih w
      intro y m
      simp only [mem_cons] at m
      rcases m with rfl | m
      · right; assumption
      · exact ih _ m
    · split at w
      · simp only [Option.some.injEq] at w
        intro y m
        simp only [mem_cons] at m
        rcases m with rfl | m
        · left; exact Nat.le_of_eq w.symm
        · rename_i h'
          simp only [minNatAbs?_eq_none_iff] at h'
          right
          exact h' _ m
      · simp only [Option.some.injEq] at w
        rename_i h₁
        rw [Nat.min_def] at w
        split at w <;> rename_i h₂
        · subst w
          intro y m
          simp only [mem_cons] at m
          rcases m with rfl | m
          · left; exact Nat.le_refl _
          · specialize ih h₁ _ m
            rcases ih with ih | rfl
            · left
              exact Nat.le_trans h₂ ih
            · simp
        · subst w
          intro y m
          simp only [mem_cons] at m
          rcases m with rfl | m
          · left
            exact Nat.le_of_not_le h₂
          · exact ih h₁ _ m

theorem minNatAbs?_eq_some_iff {xs : List Int} :
    xs.minNatAbs? = some z ↔
      (z ≠ 0 ∧ (∃ y ∈ xs, y.natAbs = z) ∧ (∀ y ∈ xs, z ≤ y.natAbs ∨ y = 0)) := by
  constructor
  · intro w
    exact ⟨by rintro rfl; simp_all, minNatAbs?_exists_of_eq_some w, minNatAbs?_forall_of_eq_some w⟩
  · rintro ⟨w₁, ⟨y, m, rfl⟩, w₃⟩
    cases h : minNatAbs? xs with
    | none =>
      simp only [minNatAbs?_eq_none_iff] at h
      specialize h _ m
      simp_all
    | some z' =>
      simp only [Option.some.injEq]
      apply Nat.le_antisymm
      · replace h := minNatAbs?_forall_of_eq_some h _ m
        rcases h with h | rfl
        · assumption
        · simp_all
      · obtain ⟨y', m', rfl⟩ := minNatAbs?_exists_of_eq_some h
        specialize w₃ _ m'
        rcases w₃ with w₂ | rfl
        · assumption
        · simp at h

/--
The minimum absolute value of a nonzero entry, or zero if all entries are zero.

We completely characterize the function via
`minNatAbs_eq_zero_iff` and `minNatAbs_eq_nonzero_iff` below.
-/
def minNatAbs (xs : List Int) : Nat := xs.minNatAbs?.getD 0

@[simp] theorem minNatAbs_eq_zero_iff {xs : List Int} : xs.minNatAbs = 0 ↔ ∀ y ∈ xs, y = 0 := by
  simp only [minNatAbs]
  cases h : xs.minNatAbs?
  · simp_all only [minNatAbs?_eq_none_iff, true_iff]
    assumption
  · simp
    constructor
    · rintro rfl
      simp_all
    · replace h := minNatAbs?_exists_of_eq_some h
      obtain ⟨y, m, rfl⟩ := h
      intro w
      specialize w _ m
      simp_all

theorem minNatAbs_eq_nonzero_iff (xs : List Int) (w : z ≠ 0) :
    xs.minNatAbs = z ↔
      (∃ y ∈ xs, y.natAbs = z) ∧ (∀ y ∈ xs, z ≤ y.natAbs ∨ y = 0) := by
  simp only [minNatAbs]
  cases h : xs.minNatAbs? with
  | none =>
    simp only [Option.getD_none]
    constructor
    · rintro rfl
      simp_all
    · intro w'
      have := minNatAbs?_eq_some_iff.mpr ⟨w, w'⟩
      simp_all
  | some z' =>
    simp
    constructor
    · rintro rfl
      exact (minNatAbs?_eq_some_iff.mp h).2
    · intro w'
      replace w' := minNatAbs?_eq_some_iff.mpr ⟨w, w'⟩
      simp_all

end List
