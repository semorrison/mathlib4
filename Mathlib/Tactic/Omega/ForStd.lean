import Std

import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-- A type synonym to equip a type with its lexicographic order. -/
def Lex' (α : Type _) := α

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex' (Prod α β)

instance Prod.Lex.instLT' (α β : Type _) [LT α] [LT β] : LT (α ×ₗ β) where
  lt := Prod.Lex (· < ·) (· < ·)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite' [Decidable P] : (dite P (fun _ ↦ a) fun _ ↦ b) = ite P a b :=
  rfl

@[simp] theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  split <;> simp_all

@[simp] theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all

namespace Int

theorem le_iff_ge {a b : Int} : a ≤ b ↔ b ≥ a := Iff.rfl

theorem mul_ediv_self_le {x k : Int} (h : k ≠ 0) : k * (x / k) ≤ x :=
  calc k * (x / k)
    _ ≤ k * (x / k) + x % k := Int.le_add_of_nonneg_right (emod_nonneg x h)
    _ = x                   := ediv_add_emod _ _

theorem lt_mul_ediv_self_add {x k : Int} (h : 0 < k) : x < k * (x / k) + k :=
  calc x
    _ = k * (x / k) + x % k := (ediv_add_emod _ _).symm
    _ < k * (x / k) + k     := Int.add_lt_add_left (emod_lt_of_pos x h) _

protected theorem mul_le_mul_of_nonpos_left {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
  rw [Int.mul_comm a b, Int.mul_comm a c]
  apply Int.mul_le_mul_of_nonpos_right h ha

theorem pow_two {x : Int} : x^2 = x * x := by
  change Int.pow _ _ = _
  simp [Int.pow]

theorem mul_self_nonneg {x : Int} : 0 ≤ x * x := by
  match x with
  | .ofNat n =>
    simpa only [ofNat_eq_coe, ← Int.ofNat_mul] using Int.ofNat_nonneg _
  | .negSucc n =>
    simpa only [negSucc_mul_negSucc, ge_iff_le, ← Int.ofNat_mul] using Int.ofNat_nonneg _

attribute [simp] sign_eq_zero_iff_zero

@[simp] theorem sign_sign : sign (sign x) = sign x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

@[simp] theorem sign_nonneg : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := {decide := true}) [sign]

end Int

namespace List

@[simp] theorem reverse_eq_nil_iff {xs : List α} : xs.reverse = [] ↔ xs = [] := by
  induction xs <;> simp

@[simp] theorem isEmpty_nil : ([] : List α).isEmpty = true := rfl
@[simp] theorem isEmpty_cons : (x :: xs : List α).isEmpty = false := rfl

instance {xs : List α} : Decidable (xs = []) :=
  decidable_of_decidable_of_iff (by induction xs <;> simp : xs.isEmpty ↔ xs = [])

@[simp] theorem dropWhile_nil : ([] : List α).dropWhile p = [] := rfl

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]

theorem dropWhile_append {xs ys : List α} :
    (xs ++ ys).dropWhile p =
      if xs.dropWhile p = [] then ys.dropWhile p else xs.dropWhile p ++ ys := by
  induction xs with
  | nil => simp
  | cons h t ih =>
    simp only [cons_append, dropWhile_cons]
    split <;> simp_all

theorem filter_cons :
    (x :: xs : List α).filter p = if p x then x :: (xs.filter p) else xs.filter p := by
  split <;> rename_i h
  · rw [filter_cons_of_pos _ h]
  · rw [filter_cons_of_neg _ h]

@[simp]
theorem get?_coe {xs : List α} {i : Fin xs.length} : xs.get? i = some (xs.get i) :=
   get?_eq_some.mpr ⟨i.2, rfl⟩

/--
Return an index for an element in a list, given that the element is a member of the list.
This function is `O(xs.length)`, as it just traverses the list looking the element.
-/
def idx_of_mem [DecidableEq α] {xs : List α} (h : y ∈ xs) : Fin xs.length :=
  ⟨xs.findIdx (· = y), xs.findIdx_lt_length_of_exists ⟨y, h, by simp⟩⟩

theorem idx_of_mem_spec [DecidableEq α] {xs : List α} (w : y ∈ xs) :
    xs.get (xs.idx_of_mem w) = y :=
  decide_eq_true_eq.mp (List.findIdx_get (p := (· = y)) (xs := xs))

@[simp]
theorem map_id''' (l : List α) : l.map (fun a => a) = l := l.map_id

theorem mem_of_mem_filter' {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  (mem_filter.mp h).1

theorem mem_iff_mem_erase_or_eq [DecidableEq α] (l : List α) (a b : α) :
    a ∈ l ↔ a ∈ l.erase b ∨ (a = b ∧ b ∈ l) := by
  by_cases h : a = b
  · subst h
    simp [or_iff_right_of_imp List.mem_of_mem_erase]
  · simp_all

-- These `findIdx?` lemmas are in https://github.com/leanprover/std4/pull/293

@[simp] theorem findIdx?_nil : ([] : List α).findIdx? p i = none := rfl
@[simp] theorem findIdx?_cons :
    (x :: xs).findIdx? p i = if p x then some i else findIdx? p xs (i + 1) := rfl
@[simp] theorem findIdx?_succ :
    (xs : List α).findIdx? p (i+1) = (xs.findIdx? p i).map fun i => i + 1 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons]
    split <;> simp_all

theorem findIdx?_eq_some_iff (xs : List α) (p : α → Bool) :
    xs.findIdx? p = some i ↔ (xs.take (i + 1)).map p = List.replicate i false ++ [true] := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [findIdx?_cons, Nat.zero_add, findIdx?_succ, take_succ_cons, map_cons]
    split
    · cases i <;> simp_all
    · cases i <;> simp_all

theorem findIdx?_of_eq_some {xs : List α} {p : α → Bool} (w : xs.findIdx? p = some i) :
    match xs.get? i with | some a => p a | none => false := by
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [findIdx?_cons, Nat.zero_add, findIdx?_succ]
    split at w
    · cases i <;> simp_all
    · cases i <;> simp_all

theorem findIdx?_of_eq_none {xs : List α} {p : α → Bool} (w : xs.findIdx? p = none) :
    ∀ i, match xs.get? i with | some a => ¬ p a | none => true := by
  intro i
  induction xs generalizing i with
  | nil => simp_all
  | cons x xs ih =>
    simp_all only [Bool.not_eq_true, findIdx?_cons, Nat.zero_add, findIdx?_succ]
    cases i with
    | zero =>
      split at w <;>
      simp_all
    | succ i =>
      simp only [get?_cons_succ]
      apply ih
      split at w <;>
      simp_all

@[simp] theorem findIdx?_append :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p <|> (ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [cons_append, findIdx?_cons, Nat.zero_add, findIdx?_succ]
    split
    · simp
    · simp_all only [Bool.not_eq_true, Option.map_orElse, Option.map_map, length_cons]
      rfl

@[simp] theorem findIdx?_replicate :
    (List.replicate n a).findIdx? p = if 0 < n ∧ p a then some 0 else none := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate, findIdx?_cons, Nat.zero_add, findIdx?_succ, Nat.zero_lt_succ, true_and]
    split <;> simp_all

end List

-- Currently not even using
namespace UInt64

attribute [ext] UInt64

protected theorem min_def {a b : UInt64} : min a b = if a ≤ b then a else b := rfl
protected theorem le_def {a b : UInt64} : a ≤ b ↔ a.val.val ≤ b.val.val := Iff.rfl
protected theorem lt_def {a b : UInt64} : a < b ↔ a.val.val < b.val.val := Iff.rfl

@[simp] protected theorem not_le {a b : UInt64} : ¬ (a ≤ b) ↔ b < a := by
  rw [UInt64.le_def, UInt64.lt_def]
  exact Fin.not_le

protected theorem min_comm {a b : UInt64} : min a b = min b a := by
  ext
  have min_val_val : ∀ a b : UInt64, (min a b).val.val = min a.val.val b.val.val := by
    intros
    simp only [UInt64.min_def, UInt64.le_def, Nat.min_def]
    split <;> rfl
  simp [min_val_val, Nat.min_comm]

protected theorem min_eq_left {a b : UInt64} (h : a ≤ b) : min a b = a := by
  simp [UInt64.min_def, h]

protected theorem min_eq_right {a b : UInt64} (h : b ≤ a) : min a b = b := by
  rw [UInt64.min_comm]; exact UInt64.min_eq_left h

end UInt64
