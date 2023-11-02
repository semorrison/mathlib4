import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Change

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Classical

namespace List

/--
The minimum non-zero entry in a list of natural numbers, or zero if all entries are zero.

We completely characterize the function via
`nonzeroMinimum_eq_zero_iff` and `nonzeroMinimum_eq_nonzero_iff` below.
-/
def nonzeroMinimum (xs : List Nat) : Nat := xs.filter (· ≠ 0) |>.minimum? |>.getD 0

@[simp] theorem nonzeroMinimum_eq_zero_iff {xs : List Nat} :
    xs.nonzeroMinimum = 0 ↔ ∀ {x}, x ∈ xs → x = 0 := by
  simp [nonzeroMinimum, Option.getD_eq_iff, minimum?_eq_none_iff, minimum?_eq_some_iff',
    filter_eq_nil, mem_filter]

theorem nonzeroMinimum_mem {xs : List Nat} (w : xs.nonzeroMinimum ≠ 0) :
    xs.nonzeroMinimum ∈ xs := by
  dsimp [nonzeroMinimum] at *
  generalize h : (xs.filter (· ≠ 0) |>.minimum?) = m at *
  match m, w with
  | some (m+1), _ => simp_all [minimum?_eq_some_iff', mem_filter]

theorem nonzeroMinimum_pos {xs : List Nat} (m : a ∈ xs) (h : a ≠ 0) : 0 < xs.nonzeroMinimum :=
  Nat.pos_iff_ne_zero.mpr fun w => h (nonzeroMinimum_eq_zero_iff.mp w m)

theorem nonzeroMinimum_le {xs : List Nat} (m : a ∈ xs) (h : a ≠ 0) : xs.nonzeroMinimum ≤ a := by
  have : (xs.filter (· ≠ 0) |>.minimum?) = some xs.nonzeroMinimum := by
    have w := nonzeroMinimum_pos m h
    dsimp [nonzeroMinimum] at *
    generalize h : (xs.filter (· ≠ 0) |>.minimum?) = m? at *
    match m?, w with
    | some m?, _ => rfl
  rw [minimum?_eq_some_iff'] at this
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
