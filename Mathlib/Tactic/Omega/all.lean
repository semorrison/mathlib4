import Mathlib
-- import Mathlib.Tactic.Omega.Problem

set_option autoImplicit true

#print List.map_id''

instance {α : Type _} [DecidableEq α] {l : List α} (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (∃ (a : α) (_ : a ∈ l), p a) := by
  simp
  infer_instance

instance {α : Type _} [DecidableEq α] {l : List α} (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (∃ (a : α), a ∈ l ∧ p a) :=
  inferInstance

instance {α : Type _} [DecidableEq α] {l : List α} (p : (a : α) → a ∈ l → Prop) [∀ a m, Decidable (p a m)] :
    Decidable (∃ (a : α) (m : a ∈ l), p a m) :=
  inferInstance

instance (x : Option α) : Decidable (x = none) := by
  cases x <;> (simp; infer_instance)

example (L : List (Option α)) : Decidable (∃ x ∈ L, x = none) := inferInstance

theorem List.mem_iff_exists_mem_eq {a : α} {L : List α} : a ∈ L ↔ ∃ x ∈ L, x = a := by
  simp

instance (L : List (Option α)) : Decidable (none ∈ L) := by
  rw [List.mem_iff_exists_mem_eq]
  infer_instance


@[simp] theorem Nat.dvd_one_iff : n ∣ 1 ↔ n = 1 := by simp only [Nat.dvd_one]
